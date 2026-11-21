import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_6
noncomputable section
open scoped nonZeroDivisors
theorem finite_quotient {F B : Type} [Field F] [CommRing B] [IsDedekindDomain B]
    [Algebra F B] [Algebra.FiniteType F B] (J : Ideal B) (hJ : J ≠ ⊥) :
    Module.Finite F (B ⧸ J) := by
  apply (Module.finite_iff_krullDimLE_zero F (B ⧸ J)).2
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.2
  intro P hP
  exact hP.1.1.isMaximal (ne_bot_of_le_ne_bot hJ hP.1.2)
private theorem rank_quot_map {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (g : M →ₗ[F] N) (hg : Function.Injective g)
    (U : Submodule F M) :
    Module.rank F (N ⧸ U.map g) = Module.rank F (N ⧸ g.range) + Module.rank F (M ⧸ U) := by
  let e : M ≃ₗ[F] g.range := LinearEquiv.ofInjective g hg
  let eq : (M ⧸ U) ≃ₗ[F] (↥g.range ⧸ U.map g.rangeRestrict) :=
    Submodule.Quotient.equiv U _ e rfl
  rw [LinearMap.rank_quot_submodule_map_eq, ← eq.rank_eq]
variable {F A : Type} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
local notation "K" => FractionRing A
local notation "B" => integralClosure A (FractionRing A)
private theorem range_mul_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (b : S) : (Algebra.lmul R S b).range = (Ideal.span {b} : Ideal S).restrictScalars R := by
  ext x
  change (∃ y, b * y = x) ↔ x ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  exact exists_congr fun _ => eq_comm
private theorem conductor [Module.Finite A B] :
    ∃ d : A, d ≠ 0 ∧ ∀ b : B, d • b ∈ (Algebra.linearMap A B).range := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := B))
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) s
    (algebraMap B K)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  let m : B →ₗ[A] B := d.val • LinearMap.id
  have hle : Submodule.span A (↑s : Set B) ≤ (Algebra.linearMap A B).range.comap m := by
    apply Submodule.span_le.2
    intro b hb
    obtain ⟨a, ha⟩ := hd b hb
    refine ⟨a, Subtype.ext ?_⟩
    change algebraMap A K a = algebraMap B K (d.val • b)
    simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B K] using ha
  rw [hs] at hle
  exact fun b => hle (Submodule.mem_top (x := b))
set_option maxHeartbeats 1000000 in
theorem compare_normalization [Algebra.FiniteType F A] [Module.Finite A B]
    [IsDedekindDomain B] (a : A) (ha : a ≠ 0) :
    Module.Finite F (A ⧸ Ideal.span {a}) ∧
      Module.finrank F (A ⧸ Ideal.span {a}) =
        Module.finrank F (B ⧸ Ideal.span {algebraMap A B a}) := by
  let : Algebra.FiniteType F B := Algebra.FiniteType.trans ‹Algebra.FiniteType F A› inferInstance
  let i : A →ₗ[F] B := (Algebra.algHom F A B).toLinearMap
  have hi : Function.Injective i := by
    intro x y h
    exact IsFractionRing.injective A K (congrArg Subtype.val h)
  let U := i.range
  let b := algebraMap A B a
  have hb : b ≠ 0 := fun he => ha (hi (he.trans (map_zero _).symm))
  let g := Algebra.lmul F B b
  have hg : Function.Injective g := fun x y h => mul_left_cancel₀ hb h
  let P := (Ideal.span {a} : Ideal A).restrictScalars F
  have hmap : P.map i = U.map g := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp (show y ∈ Ideal.span {a} from hy)
      exact ⟨i z, ⟨z, rfl⟩, (map_mul (algebraMap A B) a z).symm⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨a * z, Ideal.mem_span_singleton.mpr ⟨z, rfl⟩, map_mul (algebraMap A B) a z⟩
  obtain ⟨d, hd, hdcon⟩ := conductor (A := A)
  let u := Algebra.lmul F B (algebraMap A B d)
  have hu : u.range ≤ U := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hdcon x
    exact ⟨y, hy.trans (Algebra.smul_def d x)⟩
  have hdB : algebraMap A B d ≠ 0 := fun he => hd (hi (he.trans (map_zero _).symm))
  have hfd : Module.Finite F (B ⧸ Ideal.span {algebraMap A B d}) :=
    finite_quotient _ (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hdB)
  have : Module.Finite F (B ⧸ u.range) := by
    rw [show u.range = (Ideal.span {algebraMap A B d} : Ideal B).restrictScalars F
      from range_mul_span _]
    exact hfd
  have : Module.Finite F (B ⧸ U) :=
    Module.Finite.of_surjective (Submodule.factor hu) (Submodule.factor_surjective hu)
  have hfb : Module.Finite F (B ⧸ Ideal.span {b}) :=
    finite_quotient _ (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hb)
  have : Module.Finite F (B ⧸ g.range) := by
    rw [show g.range = (Ideal.span {b} : Ideal B).restrictScalars F from range_mul_span _]
    exact hfb
  have h₁ := rank_quot_map i hi P
  have h₂ := rank_quot_map g hg U
  rw [hmap, h₂] at h₁
  have : Module.Finite F (A ⧸ P) := by
    apply (Module.rank_lt_aleph0_iff).mp
    apply (Cardinal.add_lt_aleph0_iff.mp (_ :
      Module.rank F (B ⧸ U) + Module.rank F (A ⧸ P) < Cardinal.aleph0)).2
    rw [← h₁]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 F _) (Module.rank_lt_aleph0 F _)
  refine ⟨‹Module.Finite F (A ⧸ P)›, ?_⟩
  have he := congrArg Cardinal.toNat h₁
  rw [Cardinal.toNat_add (Module.rank_lt_aleph0 F _) (Module.rank_lt_aleph0 F _),
    Cardinal.toNat_add (Module.rank_lt_aleph0 F _) (Module.rank_lt_aleph0 F _)] at he
  have he' : Module.finrank F (B ⧸ g.range) + Module.finrank F (B ⧸ U) =
      Module.finrank F (B ⧸ U) + Module.finrank F (A ⧸ P) := he
  have hr : Module.finrank F (A ⧸ P) = Module.finrank F (B ⧸ g.range) := by omega
  rw [show g.range = (Ideal.span {b} : Ideal B).restrictScalars F from range_mul_span _] at hr
  exact hr
end
end K1_14_2_2_7_4_4_6
end
section
namespace K1_13_7_5_3_3_1
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u v
section Local
variable {k : Type v} [Field k] [Infinite k]
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra k R]
include k in
omit [IsLocalRing R] in
private theorem regular_add_mem {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (J : Ideal R)
    (h : ∀ P ∈ associatedPrimes R M, a ∈ P → ¬ J ≤ P) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  let A := {P ∈ associatedPrimes R M | a ∈ P}
  have hA : A.Finite := (associatedPrimes.finite R M).subset fun _ hP => hP.1
  have hav : ¬ ((J : Set R) ⊆ ⋃ P ∈ A, (P : Set R)) := by
    intro hall
    obtain ⟨P, hP, hJP⟩ :=
      (J.subset_union_prime_finite hA (f := id) ⊥ ⊥
        (fun P hP _ _ => (show IsAssociatedPrime P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b, hb, hbA⟩ := Set.not_subset.mp hav
  have hb' (P : Ideal R) (hP : P ∈ associatedPrimes R M) (haP : a ∈ P) :
      b ∉ P := fun hbP => hbA (Set.mem_iUnion₂.mpr ⟨P, ⟨hP, haP⟩, hbP⟩)
  let bad (P : Ideal R) := {t : k | a + algebraMap k R t * b ∈ P}
  have hbad (P : Ideal R) (hP : P ∈ associatedPrimes R M) : (bad P).Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    by_contra hst
    have hp : P.IsPrime := (show IsAssociatedPrime P M from hP).isPrime
    have hd : algebraMap k R (s - t) * b ∈ P := by
      rw [map_sub, sub_mul]
      simpa only [add_sub_add_left_eq_sub] using P.sub_mem hs ht
    have hbP : b ∈ P := (hp.mem_or_mem hd).resolve_left fun hz =>
      hp.ne_top (P.eq_top_of_isUnit_mem hz ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hst)).map
        (algebraMap k R)))
    have haP : a ∈ P := by
      simpa only [add_sub_cancel_right] using P.sub_mem hs (P.mul_mem_left (algebraMap k R s) hbP)
    exact hb' P hP haP hbP
  have hfinite := (associatedPrimes.finite R M).biUnion hbad
  obtain ⟨t, ht⟩ := hfinite.exists_notMem
  refine ⟨algebraMap k R t * b, J.mul_mem_left _ hb, ?_⟩
  by_contra hreg
  have hh : a + algebraMap k R t * b ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    rwa [biUnion_associatedPrimes_eq_compl_regular R M]
  obtain ⟨P, hP, hhP⟩ := Set.mem_iUnion₂.mp hh
  exact ht (Set.mem_iUnion₂.mpr ⟨P, hP, hhP⟩)
private abbrev ResidueModule (R : Type u) [CommRing R] [IsLocalRing R] :=
  ModuleCat.of R (R ⧸ maximalIdeal R)
omit [IsNoetherianRing R] [IsLocalRing R] in
private theorem ext_after_regular (N M : ModuleCat.{u} R) {a : R}
    (ha : IsSMulRegular M a) {n : ℕ} (h : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop a M)) i) := by
  intro i hi
  have h₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have h₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i + 1) rfl)
    (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
include k in
private theorem weaklyRegular_of_ext (rs : List R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hm : ∀ a ∈ rs, a ∈ maximalIdeal R)
    (hI : maximalIdeal R ≤ (Ideal.ofList rs ⊔ Module.annihilator R M).radical)
    (hext : ∀ i < rs.length, Subsingleton (Ext (ResidueModule R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom : Subsingleton (ResidueModule R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r, hr, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn : Module.annihilator R (ResidueModule R) = maximalIdeal R :=
      Ideal.annihilator_quotient
    have hrm : r ∈ maximalIdeal R := hAnn ▸ hr
    let J := Ideal.ofList rs
    have hJm : J ≤ maximalIdeal R := Ideal.span_le.mpr
      (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨b, hb, hab⟩ := regular_add_mem (k := k) (M := M) a J (by
      intro P hP haP hJP
      have hassoc : IsAssociatedPrime P M := hP
      have hprime := hassoc.isPrime
      have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤ P := by
        rw [Ideal.ofList_cons]
        exact sup_le (sup_le ((Ideal.span_singleton_le_iff_mem P).mpr haP) hJP)
          (by simpa only [Submodule.annihilator_top] using hassoc.annihilator_le)
      have hrP := hprime.radical_le_iff.mpr hle (hI hrm)
      have hru : r ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) :=
        Set.mem_iUnion₂.mpr ⟨P, hP, hrP⟩
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hru
      exact hru hreg)
    let M' := ModuleCat.of R (QuotSMulTop (a + b) M)
    have habann : a + b ∈ Module.annihilator R M' := QuotSMulTop.mem_annihilator M (a + b)
    have hann : Module.annihilator R M ≤ Module.annihilator R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
    have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤
        J ⊔ Module.annihilator R M' := by
      rw [Ideal.ofList_cons]
      refine sup_le (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_left)
        (hann.trans le_sup_right)
      have hsum : a + b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_right habann
      have hb' : b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_left hb
      simpa only [add_sub_cancel_right] using (J ⊔ Module.annihilator R M').sub_mem hsum hb'
    have htail := ih M' (fun z hz => hm z (List.mem_cons_of_mem _ hz))
      (hI.trans (Ideal.radical_mono hle)) (ext_after_regular _ M hab hext)
    have hcons : IsWeaklyRegular M ((a + b) :: rs) := IsWeaklyRegular.cons hab htail
    have happ : IsWeaklyRegular M (rs ++ [a + b]) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hcons
        (show List.Perm ([a + b] ++ rs) (rs ++ [a + b]) from List.perm_append_comm) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a List.mem_cons_self) (hJm hb)
        · exact hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨hrs, hlast⟩ := (isWeaklyRegular_append_iff M rs [a + b]).mp happ
    let T : Submodule R M := J • ⊤
    have hlast' : IsSMulRegular (M ⧸ T) (a + b) := (isWeaklyRegular_singleton_iff _ _).mp hlast
    have ha : IsSMulRegular (M ⧸ T) a := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT : b • x ∈ T := by
        apply (Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).mpr hb) :
          Ideal.span {b} • (⊤ : Submodule R M) ≤ T)
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew : IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hrs, (isWeaklyRegular_singleton_iff _ _).mpr ha⟩
    have hp : List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from List.perm_append_comm
    exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hnew hp.symm
      (fun z hz => hm z (hp.mem_iff.mpr hz))
include k in
theorem weaklyRegular_of_parameters (ref rs : List R) (hlen : ref.length = rs.length)
    (hmem : ∀ a ∈ ref, a ∈ maximalIdeal R) (href : IsRegular R ref)
    (hrad : (Ideal.ofList rs).radical = maximalIdeal R) :
    IsWeaklyRegular R rs := by
  let N := ResidueModule R
  have hAnn : Module.annihilator R N = maximalIdeal R := Ideal.annihilator_quotient
  have hSupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus, hAnn]
  have hlt : maximalIdeal R • (⊤ : Submodule R R) < ⊤ := by
    change maximalIdeal R • (⊤ : Ideal R) < ⊤
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp
    (ModuleCat.of R R) hlt ref hmem href
  exact weaklyRegular_of_ext (k := k) rs (ModuleCat.of R R)
    (fun a ha => hrad ▸ (Ideal.ofList rs).le_radical (Ideal.subset_span ha))
    (hrad ▸ Ideal.radical_mono le_sup_left) (fun i hi => hext i (hlen ▸ hi))
end Local
end K1_13_7_5_3_3_1
end
section
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
def weight (x : ι → F) (i : ι) : F :=
  (∏ j ∈ (Finset.univ : Finset ι).erase i, (x i - x j))⁻¹
def syndrome (x : ι → F) (u : ι → F) (j : ℕ) : F :=
  ∑ i, weight x i * u i * x i ^ j
theorem weighted_eval_sum_zero (x : ι → F) (hx : Function.Injective x)
    (q : F[X]) (hq : q.degree < (Fintype.card ι - 1 : ℕ)) :
    ∑ i, weight x i * q.eval (x i) = 0 := by
  have hlt : q.degree < (Fintype.card ι : ℕ) :=
    hq.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x)
    (fun a _ b _ hab => hx hab) (by simpa using hlt)
  rw [Finset.card_univ, Polynomial.coeff_eq_zero_of_degree_lt hq] at h
  simpa [weight, div_eq_mul_inv, mul_comm] using h.symm
def hankel (x : ι → F) (u v : ι → F) (L t : ℕ) :
    Matrix (Fin L) (Fin (t + 1)) F[X] :=
  fun i j => C (syndrome x u (i.val + j.val)) +
    X * C (syndrome x v (i.val + j.val))
def locator (x : ι → F) (S : Finset ι) : F[X] :=
  ∏ i ∈ S, (X - C (x i))
theorem locator_monic (x : ι → F) (S : Finset ι) : (locator x S).Monic :=
  Polynomial.monic_prod_of_monic S _ (fun _ _ => monic_X_sub_C _)
theorem locator_natDegree (x : ι → F) (S : Finset ι) :
    (locator x S).natDegree = S.card := by
  rw [locator, Polynomial.natDegree_prod_of_monic S _ (fun _ _ => monic_X_sub_C _)]
  simp
theorem locator_eval_zero (x : ι → F) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    (locator x S).eval (x i) = 0 := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero hi (sub_self _)
theorem sum_coeff_eval (E : F[X]) (t : ℕ) (hE : E.natDegree ≤ t) (a : F) :
    (∑ j : Fin (t + 1), E.coeff j.val * a ^ j.val) = E.eval a := by
  rw [Fin.sum_univ_eq_sum_range (fun j => E.coeff j * a ^ j) (t + 1)]
  exact (Polynomial.eval_eq_sum_range' (by omega) a).symm
theorem hankel_annihilates (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (γ : F) (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (P E : F[X]) (hP : P.degree < k) (hE : E.natDegree ≤ t)
    (hagree : ∀ a, E.eval (x a) * (u a + γ * v a) = E.eval (x a) * P.eval (x a)) :
    (fun i j => ((hankel x u v L t) i j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => E.coeff j.val) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, hankel, eval_add, eval_mul, eval_C, eval_X,
    Pi.zero_apply]
  change (∑ j : Fin (t + 1),
    ((syndrome x u (i.val + j.val)) + γ * syndrome x v (i.val + j.val)) *
      E.coeff j.val) = 0
  have hsum : (∑ j : Fin (t + 1),
      ((syndrome x u (i.val + j.val)) + γ * syndrome x v (i.val + j.val)) *
        E.coeff j.val) =
      ∑ a, weight x a * (E.eval (x a) * (u a + γ * v a)) * x a ^ i.val := by
    simp only [syndrome, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← sum_coeff_eval E t hE (x a)]
    simp only [Finset.sum_mul, Finset.mul_sum, pow_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  simp_rw [hagree]
  have hq : (E * P * X ^ i.val).degree < (↑(Fintype.card ι - 1) : WithBot ℕ) := by
    by_cases hp0 : P = 0
    · simp [hp0]
    have hpn : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hP
    have hn : (E * P * X ^ i.val).natDegree ≤ t + P.natDegree + i.val := by
      calc
        _ ≤ (E * P).natDegree + (X ^ i.val : F[X]).natDegree := natDegree_mul_le
        _ ≤ (E.natDegree + P.natDegree) + i.val := by
          simpa using Nat.add_le_add_right (natDegree_mul_le (p := E) (q := P)) i.val
        _ ≤ t + P.natDegree + i.val := by omega
    have hb : (E * P * X ^ i.val).natDegree < Fintype.card ι - 1 := by
      have := i.isLt
      omega
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hb)
  have hz := weighted_eval_sum_zero x hx (E * P * X ^ i.val) hq
  simpa only [eval_mul, eval_pow, eval_X, mul_assoc] using hz
variable (p : ℕ) [ExpChar F p]
theorem weight_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i) (i : ι) :
    frobenius F p (weight x i) = weight x i := by
  simp only [weight, map_inv₀, map_prod, map_sub, frobenius_def, hfixed]
theorem syndrome_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i)
    (u : ι → F) (j : ℕ) :
    syndrome x (fun i => u i ^ p) j = (syndrome x u j) ^ p := by
  change (∑ i, weight x i * u i ^ p * x i ^ j) =
    frobenius F p (∑ i, weight x i * u i * x i ^ j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, map_pow, weight_frobenius p x hfixed i]
  simp only [frobenius_def, hfixed]
theorem locator_map {B : Type*} [Field B] (φ : B →+* F) (x : ι → B) (S : Finset ι) :
    (locator x S).map φ = locator (fun i => φ (x i)) S := by
  simp [locator, Polynomial.map_prod]
theorem locator_map_frobenius (x : ι → F) (hfixed : ∀ i, x i ^ p = x i)
    (S : Finset ι) : (locator x S).map (frobenius F p) = locator x S := by
  simp [locator, Polynomial.map_prod, hfixed, frobenius_def]
def stacked (x : ι → F) (u v : ι → F) (L t : ℕ) :
    Matrix (Fin 2 × Fin L) (Fin (t + 1)) F[X] :=
  fun i j => if i.1 = 0 then hankel x u v L t i.2 j else
    C ((syndrome x u (i.2.val + j.val)) ^ p) +
      X ^ p * C ((syndrome x v (i.2.val + j.val)) ^ p)
theorem locator_annihilates_stacked (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F) (γ : F)
    (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (P : F[X]) (hP : P.degree < k) (S : Finset ι) (hS : S.card ≤ t)
    (hagree : ∀ a, a ∉ S → u a + γ * v a = P.eval (x a)) :
    (fun i j => ((stacked p x u v L t) i j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => (locator x S).coeff j.val) = 0 := by
  have hE : (locator x S).natDegree ≤ t := (locator_natDegree x S).trans_le hS
  have ha : ∀ a, (locator x S).eval (x a) * (u a + γ * v a) =
      (locator x S).eval (x a) * P.eval (x a) := by
    intro a
    by_cases h : a ∈ S
    · simp [locator_eval_zero x S a h]
    · rw [hagree a h]
  have hfirst := hankel_annihilates x hx u v γ k L t hsize P (locator x S) hP hE ha
  have hcoeff : ∀ j, frobenius F p ((locator x S).coeff j) = (locator x S).coeff j := by
    intro j
    have hc := congrArg (fun q : F[X] => q.coeff j) (locator_map_frobenius p x hfixed S)
    simpa only [Polynomial.coeff_map] using hc
  funext i
  rcases i with ⟨b, i⟩
  fin_cases b
  · simpa [stacked, Matrix.mulVec, dotProduct, hankel] using congrFun hfirst i
  · have hh := congrArg (frobenius F p) (congrFun hfirst i)
    simp only [Matrix.mulVec, dotProduct, hankel, eval_add, eval_mul, eval_C, eval_X,
      Pi.zero_apply, map_sum, map_mul, map_add, map_zero, hcoeff] at hh
    simpa [stacked, Matrix.mulVec, dotProduct, frobenius_def, mul_comm] using hh
end
end FrobeniusLocator
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
local instance decidableFullRank (P : Prop) : Decidable P := Classical.propDecidable P
def Decodable (x : ι → F) (u v : ι → F) (k t : ℕ) (γ : F) : Prop :=
  ∃ P : F[X], P.degree < k ∧
    (Finset.univ.filter (fun i => u i + γ * v i ≠ P.eval (x i))).card ≤ t
def minorPolynomial {row col : Type*} [Fintype col] [DecidableEq col]
    (M : Matrix row col F[X]) (rows : col → row) : F[X] :=
  Matrix.det (fun i j => M (rows i) j)
theorem det_eval_eq {col : Type*} [Fintype col] [DecidableEq col]
    (M : Matrix col col F[X]) (γ : F) :
    M.det.eval γ = Matrix.det (fun i j => (M i j).eval γ) :=
  (Polynomial.evalRingHom γ).map_det M
variable (p : ℕ) [ExpChar F p]
theorem decodable_implies_minor_root (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ p = x i) (u v : ι → F)
    (k L t : ℕ) (hsize : k + L + t ≤ Fintype.card ι)
    (rows : Fin (t + 1) → Fin 2 × Fin L) (γ : F)
    (hγ : Decodable x u v k t γ) :
    (minorPolynomial (stacked p x u v L t) rows).eval γ = 0 := by
  classical
  obtain ⟨P, hP, hcard⟩ := hγ
  let S := Finset.univ.filter (fun i => u i + γ * v i ≠ P.eval (x i))
  have hS : S.card ≤ t := hcard
  have hagree : ∀ i, i ∉ S → u i + γ * v i = P.eval (x i) := by
    intro i hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have hk := locator_annihilates_stacked p x hx hfixed u v γ k L t hsize P hP S hS hagree
  have hkm : (fun i j => ((stacked p x u v L t) (rows i) j).eval γ) *ᵥ
      (fun j : Fin (t + 1) => (locator x S).coeff j.val) = 0 := by
    funext i
    exact congrFun hk (rows i)
  have hc : (locator x S).coeff S.card = 1 := by
    rw [← locator_natDegree x S]
    exact (locator_monic x S).coeff_natDegree
  rw [minorPolynomial, det_eval_eq (fun i j : Fin (t + 1) => stacked p x u v L t (rows i) j) γ]
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hkm
    (i := ⟨S.card, by omega⟩) (by simpa only [hc] using (one_mem (nonZeroDivisors F)))
end
end FrobeniusLocator
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F : Type*} [Field F]
local instance decidableMinorDegree (P : Prop) : Decidable P := Classical.propDecidable P
theorem natDegree_det_le_row_sum {c : Type*} [Fintype c] [DecidableEq c]
    (M : Matrix c c F[X]) (d : c → ℕ) (hM : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hs : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree =
      (∏ i, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, natDegree_neg]
  rw [hs]
  calc
    _ ≤ ∑ i, (M (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (σ i) := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = ∑ i, d i := Equiv.sum_comp σ d
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem hankel_entry_natDegree (x : ι → F) (u v : ι → F) (L t : ℕ)
    (i : Fin L) (j : Fin (t + 1)) : (hankel x u v L t i j).natDegree ≤ 1 := by
  unfold hankel
  compute_degree
theorem stacked_entry_natDegree (p : ℕ) [ExpChar F p] (x : ι → F) (u v : ι → F)
    (L t : ℕ) (i : Fin 2 × Fin L) (j : Fin (t + 1)) :
    (stacked p x u v L t i j).natDegree ≤ if i.1 = 0 then 1 else p := by
  unfold stacked
  split_ifs with h
  · exact hankel_entry_natDegree x u v L t i.2 j
  · compute_degree
end
end FrobeniusLocator
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.CofactorLine
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {R c : Type*} [CommRing R] [Fintype c] [DecidableEq c]
def bordered (A : Matrix c c R) (b : c → R) : Matrix c (Option c) R :=
  fun i j => match j with | none => b i | some j => A i j
def vector (A : Matrix c c R) (b : c → R) : Option c → R :=
  fun j => match j with | none => A.det | some j => -(A.cramer b j)
theorem mulVec_border (A : Matrix c c R) (b : c → R) (E : Option c → R) :
    (bordered A b).mulVec E = A.mulVec (fun j => E (some j)) + E none • b := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, bordered,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem annihilates (A : Matrix c c R) (b : c → R) :
    (bordered A b).mulVec (vector A b) = 0 := by
  rw [mulVec_border]
  change A.mulVec (-(A.cramer b)) + A.det • b = 0
  rw [Matrix.mulVec_neg, Matrix.mulVec_cramer]
  exact neg_add_cancel _
theorem map_vector {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix c c R) (b : c → R) (j : Option c) :
    vector (A.map φ) (φ ∘ b) j = φ (vector A b j) := by
  cases j with
  | none => exact (φ.map_det A).symm
  | some j =>
    change -((A.map φ).cramer (φ ∘ b) j) = φ (-(A.cramer b j))
    rw [map_neg, Matrix.cramer_apply, Matrix.cramer_apply]
    congr 1
    rw [← Matrix.map_updateCol]
    exact (φ.map_det _).symm
theorem cramer_mulVec (A : Matrix c c R) (v : c → R) :
    A.cramer (A.mulVec v) = A.det • v := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
theorem map_cramer {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix c c R) (b : c → R) (j : c) :
    (A.map φ).cramer (φ ∘ b) j = φ (A.cramer b j) := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, ← Matrix.map_updateCol]
  exact (φ.map_det _).symm
section Field
variable {K : Type*} [Field K]
theorem kernel_zero_of_free_zero (A : Matrix c c K) (b : c → K) (hA : A.det ≠ 0)
    (E : Option c → K) (hE : (bordered A b).mulVec E = 0) (hfree : E none = 0) :
    E = 0 := by
  rw [mulVec_border, hfree, zero_smul, add_zero] at hE
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hA hE
  funext j
  cases j with
  | none => exact hfree
  | some j => exact congrFun hz j
theorem kernel_line (A : Matrix c c K) (b : c → K) (hA : A.det ≠ 0)
    (E : Option c → K) (hE : (bordered A b).mulVec E = 0) :
    E = (E none / A.det) • vector A b := by
  have hz : (bordered A b).mulVec (E - (E none / A.det) • vector A b) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hE, annihilates, smul_zero, sub_zero]
  have hfree : (E - (E none / A.det) • vector A b) none = 0 := by
    change E none - (E none / A.det) * A.det = 0
    rw [div_mul_cancel₀ _ hA, sub_self]
  have heq := kernel_zero_of_free_zero A b hA _ hz hfree
  exact sub_eq_zero.mp heq
variable {row : Type*}
def pivot (M : Matrix row (Option c) K) (rows : c → row) : Matrix c c K :=
  fun i j => M (rows i) (some j)
end Field
section Polynomial
variable {F : Type*} [Field F]
theorem vector_natDegree_le (A : Matrix c c F[X]) (b : c → F[X])
    (d : c → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d i)
    (hb : ∀ i, (b i).natDegree ≤ d i) (j : Option c) :
    (vector A b j).natDegree ≤ ∑ i, d i := by
  cases j with
  | none => exact FrobeniusLocator.natDegree_det_le_row_sum A d hA
  | some j =>
    change (-(A.cramer b j)).natDegree ≤ _
    rw [natDegree_neg, Matrix.cramer_apply]
    apply FrobeniusLocator.natDegree_det_le_row_sum _ d
    intro i k
    by_cases hkj : k = j
    · subst k
      simpa only [Matrix.updateCol_self] using hb i
    · simpa only [Matrix.updateCol_ne hkj] using hA i k
end Polynomial
end
end FrobeniusLocator.CofactorLine
end
section
namespace FrobeniusLocator.GenericRank
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K : Type*} [Field K]
theorem exists_rows_det_ne_zero {row : Type*} [Fintype row] {m : ℕ} (A : Matrix row (Fin m) K)
    (hker : ∀ v, A.mulVec v = 0 → v = 0) :
    ∃ rows : Fin m → row, (A.submatrix rows id).det ≠ 0 := by
  have hk : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hker v (by simpa only [Matrix.mulVecLin_apply] using hv)
  have hr : A.rank = m := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hk, finrank_bot, add_zero, Module.finrank_fin_fun] at h
    exact h
  rw [Matrix.rank_eq_finrank_span_row] at hr
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = m := by
    rw [← finrank_span_eq_card hli, hsp, hr]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent K (A.submatrix (a ∘ e) id).row := by
    have heq : (A.submatrix (a ∘ e) id).row = (A.row ∘ a) ∘ e := by
      funext i j
      rfl
    rw [heq]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero
theorem exists_pivot_of_kernel_line {row : Type*} [Fintype row] {m : ℕ} (M : Matrix row (Option (Fin m)) K)
    (E : Option (Fin m) → K) (hfree : E none ≠ 0)
    (hline : ∀ v, M.mulVec v = 0 → ∃ a : K, v = a • E) :
    ∃ rows : Fin m → row, (CofactorLine.pivot M rows).det ≠ 0 := by
  let A : Matrix row (Fin m) K := fun i j => M i (some j)
  obtain ⟨rows, hrows⟩ := exists_rows_det_ne_zero A (by
    intro v hv
    let v' : Option (Fin m) → K := fun j => match j with | none => 0 | some j => v j
    have hv' : M.mulVec v' = 0 := by
      funext i
      change (∑ j : Option (Fin m), M i j * v' j) = 0
      rw [Fintype.sum_option]
      simpa only [v', mul_zero, add_zero, zero_add, A, Matrix.mulVec, dotProduct,
        Pi.zero_apply] using congrFun hv i
    obtain ⟨a, ha⟩ := hline v' hv'
    have hscalar : a = 0 := by
      have h := congrFun ha none
      change 0 = a * E none at h
      exact (mul_eq_zero.mp h.symm).resolve_right hfree
    funext j
    have h := congrFun ha (some j)
    simpa only [v', hscalar, zero_smul, Pi.zero_apply] using h)
  exact ⟨rows, hrows⟩
theorem kernel_line_of_finrank {row col : Type*} [Fintype col]
    (M : Matrix row col K) (hnull : Module.finrank K (LinearMap.ker M.mulVecLin) = 1)
    (E : col → K) (hE : E ≠ 0) (hME : M.mulVec E = 0) :
    ∀ v, M.mulVec v = 0 → ∃ a : K, v = a • E := by
  have hspan : K ∙ E = LinearMap.ker M.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact hME
    · rw [finrank_span_singleton hE, hnull]
  intro v hv
  have hmem : v ∈ K ∙ E := by rw [hspan]; exact hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨a, ha.symm⟩
theorem nullity_one_of_rank {row col : Type*} [Fintype col]
    (M : Matrix row col K) (hr : M.rank + 1 = Fintype.card col) :
    Module.finrank K (LinearMap.ker M.mulVecLin) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  change M.rank + _ = _ at h
  omega
end
end FrobeniusLocator.GenericRank
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
structure RowBasis (φ : F[X] →+* K) (M : Matrix row col F[X]) (r : ℕ) where
  rows : Fin r → row
  cols : Fin r → col
  minor_ne : (M.submatrix rows cols).det ≠ 0
  spans : ∀ i, ∃ a : Fin r → K, ∀ j,
    φ (M i j) = ∑ q, a q * φ (M (rows q) j)
def pivot {r : ℕ} {φ : F[X] →+* K} {M : Matrix row col F[X]}
    (B : RowBasis φ M r) : Matrix (Fin r) (Fin r) F[X] := M.submatrix B.rows B.cols
def rowCoefficients {r : ℕ} {φ : F[X] →+* K} {M : Matrix row col F[X]}
    (B : RowBasis φ M r) (i : row) : Fin r → F[X] :=
  (pivot B).transpose.cramer (fun q => M i (B.cols q))
theorem row_relation (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r) (i : row) (j : col) :
    (pivot B).det * M i j = ∑ q, rowCoefficients B i q * M (B.rows q) j := by
  obtain ⟨a, ha⟩ := B.spans i
  let A := (pivot B).map φ
  have hsolve : A.transpose.mulVec a = fun q => φ (M i (B.cols q)) := by
    funext q
    change (∑ l, φ (M (B.rows l) (B.cols q)) * a l) = _
    simpa only [mul_comm] using (ha (B.cols q)).symm
  have hc : ∀ q, φ (rowCoefficients B i q) = φ (pivot B).det * a q := by
    intro q
    have hm := CofactorLine.map_cramer φ (pivot B).transpose
      (fun q => M i (B.cols q)) q
    have hcr := congrFun (CofactorLine.cramer_mulVec A.transpose a) q
    rw [hsolve, Matrix.det_transpose] at hcr
    have hd := φ.map_det (pivot B)
    rw [RingHom.mapMatrix_apply] at hd
    change φ (rowCoefficients B i q) = _
    calc
      _ = ((pivot B).transpose.map φ).cramer (fun q => φ (M i (B.cols q))) q := hm.symm
      _ = A.det * a q := hcr
      _ = _ := by rw [← hd]
  apply hφ
  rw [map_mul, map_sum]
  simp only [map_mul, hc]
  rw [ha j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring
theorem kernel_eq_selected (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) (v : col → F) :
    (M.map (evalRingHom γ)).mulVec v = 0 ↔
      ((M.submatrix B.rows id).map (evalRingHom γ)).mulVec v = 0 := by
  constructor
  · intro h
    funext i
    exact congrFun h (B.rows i)
  · intro h
    funext i
    apply (mul_eq_zero.mp (show (pivot B).det.eval γ *
      ((M.map (evalRingHom γ)).mulVec v) i = 0 from ?_)).resolve_left hγ
    have heval : ∀ j, (pivot B).det.eval γ * (M i j).eval γ =
        ∑ q, (rowCoefficients B i q).eval γ * (M (B.rows q) j).eval γ := by
      intro j
      have hrel := congrArg (evalRingHom γ) (row_relation φ hφ M r B i j)
      simp only [map_mul, map_sum] at hrel
      exact hrel
    change (pivot B).det.eval γ * (∑ j, (M i j).eval γ * v j) = 0
    rw [Finset.mul_sum]
    simp_rw [← mul_assoc, heval, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q hq
    have hz := congrFun h q
    change (∑ j, (M (B.rows q) j).eval γ * v j) = 0 at hz
    calc
      _ = (rowCoefficients B i q).eval γ * (∑ j, (M (B.rows q) j).eval γ * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hz, mul_zero]
theorem exists_rowBasis [Fintype row] (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) : Nonempty (RowBasis φ M r) := by
  classical
  let N := M.map φ
  have hr' : Module.finrank K (Submodule.span K (Set.range N.row)) = r := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hr
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K N.row
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hsp, hr']
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  let rows := a ∘ e
  have hli' : LinearIndependent K (fun q : Fin r => N.row (rows q)) :=
    hli.comp e e.injective
  have hspace : Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) =
      Submodule.span K (Set.range N.row) := by
    rw [← hsp]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      exact ⟨e q, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨l, hl⟩ := e.surjective q
      exact ⟨l, by simp only [rows, Function.comp_apply, hl]⟩
  let T := N.submatrix rows id
  obtain ⟨cols, hcols⟩ := GenericRank.exists_rows_det_ne_zero T.transpose (by
    intro v hv
    have hsum : (∑ q, v q • N.row (rows q)) = 0 := by
      funext j
      have h := congrFun hv j
      change (∑ q, N (rows q) j * v q) = 0 at h
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.row, Pi.zero_apply] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK : (N.submatrix rows cols).det ≠ 0 := by
    have heq : T.transpose.submatrix cols id = (N.submatrix rows cols).transpose := by
      ext i j
      rfl
    rw [heq, Matrix.det_transpose] at hcols
    exact hcols
  refine ⟨⟨rows, cols, ?_, ?_⟩⟩
  · intro hzero
    apply hminorK
    have hmap := φ.map_det (M.submatrix rows cols)
    rw [RingHom.mapMatrix_apply, hzero, map_zero] at hmap
    exact hmap.symm
  · intro i
    have hmem : N.row i ∈ Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) := by
      rw [hspace]
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    refine ⟨v, ?_⟩
    intro j
    have h := congrFun hv j
    simpa only [N, Matrix.row, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
theorem rank_specializes [Fintype row] (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) :
    (M.map (evalRingHom γ)).rank = r := by
  let N := M.map (evalRingHom γ)
  let T := (M.submatrix B.rows id).map (evalRingHom γ)
  change N.rank = r
  have hminor : (N.submatrix B.rows B.cols).det ≠ 0 := by
    have hmap := (evalRingHom γ).map_det (pivot B)
    rw [RingHom.mapMatrix_apply] at hmap
    intro h0
    apply hγ
    have heq : N.submatrix B.rows B.cols = (pivot B).map (evalRingHom γ) := rfl
    rw [heq, ← hmap] at h0
    exact h0
  have hTrank : T.rank = r := by
    have hminorRank := Matrix.rank_of_det_ne_zero hminor
    have hlo := Matrix.rank_submatrix_le T id B.cols
    have hhi := Matrix.rank_le_card_height T
    change (N.submatrix B.rows B.cols).rank ≤ T.rank at hlo
    rw [hminorRank, Fintype.card_fin] at hlo
    rw [Fintype.card_fin] at hhi
    omega
  have hker : LinearMap.ker N.mulVecLin = LinearMap.ker T.mulVecLin := by
    ext v
    exact kernel_eq_selected φ hφ M r B γ hγ v
  have hN := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have hT := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  change N.rank + Module.finrank F (LinearMap.ker N.mulVecLin) = _ at hN
  change T.rank + Module.finrank F (LinearMap.ker T.mulVecLin) = _ at hT
  rw [hker] at hN
  rw [hTrank] at hT
  omega
theorem constant_kernel_eq_normal [Fintype row] (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : RowBasis φ M r)
    (V : Submodule F (col → F)) (hV : Module.finrank F V = Fintype.card col - r)
    (hsub : ∀ γ v, v ∈ V → (M.map (evalRingHom γ)).mulVec v = 0)
    (γ : F) (hγ : (pivot B).det.eval γ ≠ 0) :
    LinearMap.ker (M.map (evalRingHom γ)).mulVecLin = V := by
  have hrank := rank_specializes φ hφ M r B γ hγ
  have hn := LinearMap.finrank_range_add_finrank_ker (M.map (evalRingHom γ)).mulVecLin
  change (M.map (evalRingHom γ)).rank + _ = _ at hn
  rw [hrank, Module.finrank_fintype_fun_eq_card] at hn
  have hdim : Module.finrank F (LinearMap.ker (M.map (evalRingHom γ)).mulVecLin) = Fintype.card col - r := by omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv
    exact hsub γ v hv
  · rw [hV, hdim]
theorem minor_degree_le (φ : F[X] →+* K) (M : Matrix row col F[X]) (r : ℕ)
    (B : RowBasis φ M r) (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    (pivot B).det.natDegree ≤ ∑ q, d (B.rows q) := by
  exact FrobeniusLocator.natDegree_det_le_row_sum _ _
    (fun i j => hdeg (B.rows i) (B.cols j))
end
end FrobeniusLocator.NormalFiber
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
section Ring
variable {R row col : Type*} [CommRing R] [Fintype col] [DecidableEq col]
variable {r : ℕ}
def inclusion (cols : Fin r → col) : Matrix col (Fin r) R :=
  fun j q => (Pi.single (cols q) (1 : R) : col → R) j
theorem selected_mul_inclusion (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) :
    M.submatrix rows id * inclusion cols = M.submatrix rows cols := by
  ext i q
  change (M.submatrix rows id).mulVec (Pi.single (cols q) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl
def cofactorMap (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col) :
    (col → R) →ₗ[R] (col → R) :=
  (M.submatrix rows cols).det • LinearMap.id -
    (inclusion cols).mulVecLin.comp
      ((M.submatrix rows cols).cramer.comp (M.submatrix rows id).mulVecLin)
def rawVector (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col)
    (j : col) : col → R := cofactorMap M rows cols (Pi.single j 1)
theorem cofactorMap_apply (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    cofactorMap M rows cols v = (M.submatrix rows cols).det • v -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        ((M.submatrix rows id).mulVec v)) := rfl
theorem rawVector_apply (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (j : col) :
    rawVector M rows cols j = (M.submatrix rows cols).det • Pi.single j 1 -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        (fun q => M (rows q) j)) := by
  rw [rawVector, cofactorMap_apply, Matrix.mulVec_single_one]
  rfl
theorem selected_annihilates_map (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    (M.submatrix rows id).mulVec (cofactorMap M rows cols v) = 0 := by
  rw [cofactorMap_apply, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, selected_mul_inclusion, Matrix.mulVec_cramer, sub_self]
theorem selected_annihilates (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (j : col) :
    (M.submatrix rows id).mulVec (rawVector M rows cols j) = 0 :=
  selected_annihilates_map M rows cols _
theorem cofactorMap_of_kernel (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R)
    (hv : (M.submatrix rows id).mulVec v = 0) :
    cofactorMap M rows cols v = (M.submatrix rows cols).det • v := by
  rw [cofactorMap_apply, hv, map_zero, Matrix.mulVec_zero, sub_zero]
theorem sum_rawVector (M : Matrix row col R) (rows : Fin r → row)
    (cols : Fin r → col) (v : col → R) :
    ∑ j, v j • rawVector M rows cols j = cofactorMap M rows cols v := by
  simp only [rawVector, ← map_smul, ← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]
theorem map_rawVector {S : Type*} [CommRing S] (ψ : R →+* S)
    (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col) (j c : col) :
    rawVector (M.map ψ) rows cols j c = ψ (rawVector M rows cols j c) := by
  have hsub : (M.map ψ).submatrix rows cols = (M.submatrix rows cols).map ψ := rfl
  have hd := ψ.map_det (M.submatrix rows cols)
  rw [RingHom.mapMatrix_apply] at hd
  have hc : ((M.submatrix rows cols).map ψ).cramer
      (fun q => ψ (M (rows q) j)) =
      fun q => ψ ((M.submatrix rows cols).cramer (fun q => M (rows q) j) q) := by
    funext q
    exact CofactorLine.map_cramer ψ _ _ q
  have hs : ∀ a : col, ψ ((Pi.single a (1 : R) : col → R) c) =
      (Pi.single a (1 : S) : col → S) c := by
    intro a
    by_cases h : a = c <;> simp [h]
  simp only [rawVector_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsub, ← hd, map_sub, map_mul, hs]
  congr 1
  change (∑ q, (Pi.single (cols q) (1 : S) : col → S) c *
      ((M.submatrix rows cols).map ψ).cramer (fun q => ψ (M (rows q) j)) q) = _
  rw [hc]
  simp only [Matrix.mulVec, dotProduct, inclusion, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hs]
end Ring
section Field
variable {K row col : Type*} [Field K] [Fintype col] [DecidableEq col]
variable {r : ℕ}
theorem raw_spans (M : Matrix row col K) (rows : Fin r → row) (cols : Fin r → col)
    (hdet : (M.submatrix rows cols).det ≠ 0) (v : col → K)
    (hv : (M.submatrix rows id).mulVec v = 0) :
    v = ∑ j, (v j / (M.submatrix rows cols).det) • rawVector M rows cols j := by
  have heq := sum_rawVector M rows cols v
  rw [cofactorMap_of_kernel _ _ _ _ hv] at heq
  calc
    v = (M.submatrix rows cols).det⁻¹ • ((M.submatrix rows cols).det • v) := by
      rw [smul_smul, inv_mul_cancel₀ hdet, one_smul]
    _ = _ := by
      rw [← heq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul, div_eq_mul_inv, mul_comm]
end Field
section Polynomial
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}
def vector (B : NormalFiber.RowBasis φ M r) (j : col) : col → F[X] :=
  rawVector M B.rows B.cols j
theorem generic_kernel_eq_selected (B : NormalFiber.RowBasis φ M r) (v : col → K) :
    (M.map φ).mulVec v = 0 ↔ ((M.submatrix B.rows id).map φ).mulVec v = 0 := by
  constructor
  · intro h
    funext q
    exact congrFun h (B.rows q)
  · intro h
    funext i
    obtain ⟨a, ha⟩ := B.spans i
    change (∑ j, φ (M i j) * v j) = 0
    simp_rw [ha, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q hq
    have hz := congrFun h q
    change (∑ j, φ (M (B.rows q) j) * v j) = 0 at hz
    calc
      _ = a q * (∑ j, φ (M (B.rows q) j) * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hz, mul_zero]
theorem annihilates (B : NormalFiber.RowBasis φ M r) (hφ : Function.Injective φ)
    (j : col) : M.mulVec (vector B j) = 0 := by
  have hsel := selected_annihilates (M.map φ) B.rows B.cols j
  have hfull := (generic_kernel_eq_selected B _).mpr hsel
  funext i
  apply hφ
  have h := congrFun hfull i
  simpa only [vector, Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
    Matrix.map_apply, map_rawVector, Pi.zero_apply] using h
theorem generic_spans (B : NormalFiber.RowBasis φ M r) (hφ : Function.Injective φ)
    (v : col → K) (hv : (M.map φ).mulVec v = 0) :
    v = ∑ j, (v j / φ (NormalFiber.pivot B).det) •
      (fun c => φ (vector B j c)) := by
  have hd := φ.map_det (NormalFiber.pivot B)
  rw [RingHom.mapMatrix_apply] at hd
  have hd' : φ (NormalFiber.pivot B).det =
      ((M.map φ).submatrix B.rows B.cols).det := hd
  have hdet : ((M.map φ).submatrix B.rows B.cols).det ≠ 0 := by
    rw [← hd']
    exact fun h => B.minor_ne (hφ (h.trans (map_zero φ).symm))
  have hsel := (generic_kernel_eq_selected B v).mp hv
  have heq := raw_spans (M.map φ) B.rows B.cols hdet v hsel
  have hmap : ∀ j, rawVector (M.map φ) B.rows B.cols j =
      fun c => φ (vector B j c) := fun j => funext (map_rawVector φ M B.rows B.cols j)
  simpa only [← hd', hmap] using heq
theorem vector_natDegree_le (B : NormalFiber.RowBasis φ M r)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) (j c : col) :
    (vector B j c).natDegree ≤ ∑ q, d (B.rows q) := by
  classical
  rw [vector, rawVector_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · by_cases hj : j = c
    · subst c
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one,
        NormalFiber.pivot] using
        NormalFiber.minor_degree_le φ M r B d hdeg
    · simp [Pi.smul_apply, Pi.single_apply, hj]
  · change (∑ q, inclusion B.cols c q *
      (M.submatrix B.rows B.cols).cramer (fun q => M (B.rows q) j) q).natDegree ≤ _
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    by_cases hq : B.cols q = c
    · simp only [inclusion, hq, Pi.single_eq_same, one_mul, Matrix.cramer_apply]
      apply FrobeniusLocator.natDegree_det_le_row_sum _ (fun q => d (B.rows q))
      intro i k
      by_cases hk : k = q
      · subst k
        simpa only [Matrix.updateCol_self] using hdeg (B.rows i) j
      · simpa only [Matrix.updateCol_ne hk, Matrix.submatrix_apply] using
          hdeg (B.rows i) (B.cols k)
    · simp [inclusion, Pi.single_apply, hq]
end Polynomial
end
end FrobeniusLocator.GenericCofactor
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.AppendConstants
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F row extra col : Type*} [Field F] [Fintype col] [DecidableEq col]
def appendOver {K : Type*} [Field K] (M : Matrix row col K) (E : Matrix extra col K) :
    Matrix (row ⊕ extra) col K := Sum.elim M E
theorem appendOver_kernel {K : Type*} [Field K]
    (M : Matrix row col K) (E : Matrix extra col K) (v : col → K) :
    (appendOver M E).mulVec v = 0 ↔ M.mulVec v = 0 ∧ E.mulVec v = 0 := by
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (Sum.inl i)),
      funext (fun i => congrFun h (Sum.inr i))⟩
  · rintro ⟨hM, hE⟩
    funext i
    cases i with
    | inl i => exact congrFun hM i
    | inr i => exact congrFun hE i
end
end FrobeniusLocator.AppendConstants
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}
theorem rows_injective (B : RowBasis φ M r) : Function.Injective B.rows := by
  intro i j hij
  by_contra hne
  apply B.minor_ne
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp only [Matrix.submatrix_apply, hij]
end
end FrobeniusLocator.NormalFiber
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K]
  [Fintype row] [Fintype col] [DecidableEq col]
theorem exists_rowBasis_containing (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) (S : Set row)
    (hS : LinearIndepOn K (M.map φ).row S) :
    ∃ B : RowBasis φ M r, S ⊆ Set.range B.rows := by
  classical
  let N := M.map φ
  let T := hS.extend (Set.subset_univ S)
  have hST : S ⊆ T := hS.subset_extend (Set.subset_univ S)
  have hli : LinearIndependent K (fun i : T => N.row i.val) :=
    (hS.linearIndepOn_extend (Set.subset_univ S)).linearIndependent_restrict
  have hspace : Submodule.span K (Set.range (fun i : T => N.row i.val)) =
      Submodule.span K (Set.range N.row) := by
    have heq := hS.span_image_extend_eq_span_image (Set.subset_univ S)
    have hl : Set.range (fun i : T => N.row i.val) = N.row '' T := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [hl]
    simpa only [Set.image_univ] using heq
  have hcard : Fintype.card T = r := by
    rw [← finrank_span_eq_card hli, hspace, ← Matrix.rank_eq_finrank_span_row]
    exact hr
  let e : Fin r ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin r → row := fun q => (e q).val
  have hli' : LinearIndependent K (fun q : Fin r => N.row (rows q)) :=
    hli.comp e e.injective
  let A := N.submatrix rows id
  obtain ⟨cols, hcols⟩ := GenericRank.exists_rows_det_ne_zero A.transpose (by
    intro v hv
    have hsum : (∑ q, v q • N.row (rows q)) = 0 := by
      funext j
      have h := congrFun hv j
      change (∑ q, N (rows q) j * v q) = 0 at h
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.row, Pi.zero_apply] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK : (N.submatrix rows cols).det ≠ 0 := by
    have heq : A.transpose.submatrix cols id = (N.submatrix rows cols).transpose := by
      funext i j
      rfl
    rw [heq, Matrix.det_transpose] at hcols
    exact hcols
  have hminor : (M.submatrix rows cols).det ≠ 0 := by
    intro hzero
    apply hminorK
    have hmap := φ.map_det (M.submatrix rows cols)
    rw [RingHom.mapMatrix_apply, hzero, map_zero] at hmap
    exact hmap.symm
  have hspace' : Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) =
      Submodule.span K (Set.range N.row) := by
    rw [← hspace]
    congr 1
    ext v
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨e q, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨l, hl⟩ := e.surjective q
      exact ⟨l, by simp only [rows, hl]⟩
  refine ⟨⟨rows, cols, hminor, ?_⟩, ?_⟩
  · intro i
    have hm : N.row i ∈ Submodule.span K (Set.range (fun q : Fin r => N.row (rows q))) := by
      rw [hspace']
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    refine ⟨a, ?_⟩
    intro j
    have h := congrFun ha j
    simpa only [N, Matrix.row, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  · intro i hi
    obtain ⟨q, hq⟩ := e.surjective ⟨i, hST hi⟩
    exact ⟨q, congrArg Subtype.val hq⟩
end
end FrobeniusLocator.NormalFiber
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.AppendConstants
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K row col : Type*} [Field K] [Fintype col] [DecidableEq col]
def functional (a : col → K) : (col → K) →ₗ[K] K where
  toFun v := ∑ j, a j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm, mul_assoc]
def appendOne (M : Matrix row col K) (a : col → K) : Matrix (row ⊕ Unit) col K :=
  appendOver M (fun _ => a)
theorem appendOne_kernel (M : Matrix row col K) (a v : col → K) :
    (appendOne M a).mulVec v = 0 ↔ M.mulVec v = 0 ∧ functional a v = 0 := by
  rw [appendOne, appendOver_kernel]
  constructor
  · rintro ⟨hM, ha⟩
    exact ⟨hM, congrFun ha ()⟩
  · rintro ⟨hM, ha⟩
    exact ⟨hM, funext (fun _ => ha)⟩
def restriction (M : Matrix row col K) (a : col → K) :
    LinearMap.ker M.mulVecLin →ₗ[K] K :=
  (functional a).comp (LinearMap.ker M.mulVecLin).subtype
def restrictionKernelEquiv (M : Matrix row col K) (a : col → K) :
    LinearMap.ker (restriction M a) ≃ₗ[K]
      LinearMap.ker (appendOne M a).mulVecLin where
  toFun v := ⟨v.val.val, (appendOne_kernel M a _).mpr ⟨v.val.property, v.property⟩⟩
  invFun v := ⟨⟨v.val, ((appendOne_kernel M a _).mp v.property).1⟩,
    ((appendOne_kernel M a _).mp v.property).2⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl
theorem nullity_drop_one (M : Matrix row col K) (a : col → K)
    (hactive : ∃ v : col → K, M.mulVec v = 0 ∧ functional a v ≠ 0) :
    Module.finrank K (LinearMap.ker (appendOne M a).mulVecLin) + 1 =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have hne : restriction M a ≠ 0 := by
    intro hzero
    obtain ⟨v, hv, ha⟩ := hactive
    apply ha
    exact LinearMap.congr_fun hzero ⟨v, hv⟩
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [(restrictionKernelEquiv M a).finrank_eq] at h
  exact h
end
end FrobeniusLocator.AppendConstants
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K]
  [Fintype row] [DecidableEq row] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}
theorem selected_two_level_sum (B : RowBasis φ M r) (S : Finset row)
    (hS : (S : Set row) ⊆ Set.range B.rows) (p : ℕ) :
    (∑ q, if B.rows q ∈ S then 1 else p) = S.card + p * (r - S.card) := by
  classical
  have hc : (Finset.univ.filter (fun q => B.rows q ∈ S)).card = S.card := by
    apply Finset.card_bij (fun q _ => B.rows q)
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro i hi j hj hij
      exact rows_injective B hij
    · intro i hi
      obtain ⟨q, hq⟩ := hS hi
      exact ⟨q, by simp [hq, hi], hq⟩
  have hn : (Finset.univ.filter (fun q => B.rows q ∉ S)).card = r - S.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (fun q => B.rows q ∈ S)
    rw [hc, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one, hc, hn]
  simp [Nat.mul_comm]
theorem exists_rowBasis_two_level (φ : F[X] →+* K) (M : Matrix row col F[X])
    (r : ℕ) (hr : (M.map φ).rank = r) (S : Finset row)
    (hS : LinearIndepOn K (M.map φ).row (S : Set row)) (p : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ if i ∈ S then 1 else p) :
    ∃ B : RowBasis φ M r,
      (∑ q, if B.rows q ∈ S then 1 else p) = S.card + p * (r - S.card) ∧
      (pivot B).det.natDegree ≤ S.card + p * (r - S.card) := by
  obtain ⟨B, hcontains⟩ := exists_rowBasis_containing φ M r hr (S : Set row) hS
  have heq := selected_two_level_sum B S hcontains p
  refine ⟨B, heq, ?_⟩
  rw [← heq]
  exact minor_degree_le φ M r B (fun i => if i ∈ S then 1 else p) hdeg
end
end FrobeniusLocator.NormalFiber
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.NormalFiber
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
def ordinaryRows (L : ℕ) : Fin L → Fin 2 × Fin L := fun i => (0, i)
def ordinarySet (L : ℕ) : Finset (Fin 2 × Fin L) :=
  Finset.univ.filter (fun i => i.1 = 0)
theorem ordinarySet_coe (L : ℕ) :
    (ordinarySet L : Set (Fin 2 × Fin L)) = Set.range (ordinaryRows L) := by
  ext i
  constructor
  · intro hi
    have h0 : i.1 = 0 := (Finset.mem_filter.mp hi).2
    exact ⟨i.2, by ext <;> simp [ordinaryRows, h0]⟩
  · rintro ⟨i, rfl⟩
    simp [ordinarySet, ordinaryRows]
theorem ordinarySet_card (L : ℕ) : (ordinarySet L).card = L := by
  classical
  have heq : (ordinarySet L).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun i _ => i.2)
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      have hi0 := (Finset.mem_filter.mp hi).2
      have hj0 := (Finset.mem_filter.mp hj).2
      exact Prod.ext (hi0.trans hj0.symm) hij
    · intro j hj
      exact ⟨(0,j), by simp [ordinarySet], rfl⟩
  simpa using heq
theorem exists_stacked_basis (φ : F[X] →+* K) (L s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) col F[X]) (hr : (M.map φ).rank = s)
    (hfirst : LinearIndependent K (fun i => (M.map φ).row (ordinaryRows L i)))
    (hdeg : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p) :
    ∃ B : RowBasis φ M s,
      (∑ q, if (B.rows q).1 = 0 then 1 else p) = L + p * (s-L) ∧
      (pivot B).det.natDegree ≤ L + p * (s-L) := by
  classical
  have hinj : Function.Injective (ordinaryRows L) := by
    intro i j hij
    exact congrArg Prod.snd hij
  have hS : LinearIndepOn K (M.map φ).row (ordinarySet L : Set (Fin 2 × Fin L)) := by
    rw [ordinarySet_coe]
    exact (linearIndepOn_range_iff hinj _).mpr hfirst
  have hdeg' : ∀ i j, (M i j).natDegree ≤ if i ∈ ordinarySet L then 1 else p := by
    intro i j
    simpa only [ordinarySet, Finset.mem_filter, Finset.mem_univ, true_and] using hdeg i j
  obtain ⟨B, hledger, hminor⟩ := exists_rowBasis_two_level φ M s hr (ordinarySet L) hS p hdeg'
  rw [ordinarySet_card] at hledger hminor
  refine ⟨B, ?_, ?_⟩
  · simpa only [ordinarySet, Finset.mem_filter, Finset.mem_univ, true_and,
      ordinarySet_card] using hledger
  · exact hminor
theorem first_rows_independent_of_rank (φ : F[X] →+* K) (L : ℕ)
    (M : Matrix (Fin 2 × Fin L) col F[X])
    (hfirst : ((M.map φ).submatrix (ordinaryRows L) id).rank = L) :
    LinearIndependent K (fun i => (M.map φ).row (ordinaryRows L i)) := by
  have hli : LinearIndependent K ((M.map φ).submatrix (ordinaryRows L) id).row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, Fintype.card_fin, hfirst]
  exact hli
end
end FrobeniusLocator.NormalFiber
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance decidablePrincipal (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
def specialize {d : ℕ} (v : Fin (d + 1) → F[X]) (γ : F) : F[X] :=
  ∑ j, C ((v j).eval γ) * X ^ j.val
def nodePolynomial {d : ℕ} (v : Fin (d + 1) → F[X]) (x : F) : F[X] :=
  ∑ j, C (x ^ j.val) * v j
theorem nodePolynomial_eval {d : ℕ} (v : Fin (d + 1) → F[X]) (x γ : F) :
    (nodePolynomial v x).eval γ = (specialize v γ).eval x := by
  simp only [nodePolynomial, specialize, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem nodePolynomial_natDegree_le {d B : ℕ} (v : Fin (d + 1) → F[X])
    (hv : ∀ j, (v j).natDegree ≤ B) (x : F) :
    (nodePolynomial v x).natDegree ≤ B := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hv j)
theorem specialize_natDegree_le {d : ℕ} (v : Fin (d+1) → F[X]) (γ : F) :
    (specialize v γ).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have h := Polynomial.natDegree_C_mul_le ((v j).eval γ) (X ^ j.val : F[X])
  simp only [natDegree_X_pow] at h
  exact h.trans (by omega)
theorem principal_incidence_count (x : ι → F) (V : F → F[X])
    (q : ι → F[X]) (p d : ℕ) (hd : 0 < d)
    (hq : ∀ i, q i ≠ 0) (hdeg : ∀ i, (q i).natDegree ≤ p * d)
    (heval : ∀ i γ, (q i).eval γ = (V γ).eval (x i))
    (Γ : Finset F)
    (hroots : ∀ γ ∈ Γ, d ≤ (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) :
    Γ.card ≤ p * Fintype.card ι := by
  classical
  have hnode (i : ι) :
      (Γ.filter (fun γ => (V γ).eval (x i) = 0)).card ≤ p * d := by
    apply le_trans (b := (q i).natDegree)
    · apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      apply (Polynomial.mem_roots (hq i)).mpr
      change (q i).eval γ = 0
      rw [heval]
      exact (Finset.mem_filter.mp hγ).2
    · exact hdeg i
  have hswap : (∑ γ ∈ Γ, (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) =
      ∑ i : ι, (Γ.filter (fun γ => (V γ).eval (x i) = 0)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hleft : Γ.card * d ≤ ∑ γ ∈ Γ, (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card := by
    calc
      Γ.card * d = ∑ _γ ∈ Γ, d := by simp
      _ ≤ _ := Finset.sum_le_sum hroots
  have hright : (∑ i : ι, (Γ.filter
      (fun γ => (V γ).eval (x i) = 0)).card) ≤ Fintype.card ι * (p * d) := by
    calc
      _ ≤ ∑ _i : ι, p * d := Finset.sum_le_sum (fun i _ => hnode i)
      _ = _ := by simp
  rw [hswap] at hleft
  nlinarith
theorem principal_kernel_count (x : ι → F) (V : F → F[X])
    (q : ι → F[X]) (p d δ : ℕ) (hd : 0 < d)
    (hq : ∀ i, q i ≠ 0) (hdeg : ∀ i, (q i).natDegree ≤ p * d)
    (heval : ∀ i γ, (q i).eval γ = (V γ).eval (x i))
    (Δ : F[X]) (hΔ : Δ ≠ 0) (hΔdeg : Δ.natDegree ≤ δ)
    (Γ : Finset F)
    (hroots : ∀ γ ∈ Γ, Δ.eval γ ≠ 0 → d ≤ (Finset.univ.filter
      (fun i => (V γ).eval (x i) = 0)).card) :
    Γ.card ≤ δ + p * Fintype.card ι := by
  classical
  let E := Γ.filter (fun γ => Δ.eval γ = 0)
  let R := Γ.filter (fun γ => Δ.eval γ ≠ 0)
  have hE : E.card ≤ δ := by
    apply le_trans (b := Δ.natDegree)
    · apply Polynomial.card_le_degree_of_subset_roots
      intro γ hγ
      exact (Polynomial.mem_roots hΔ).mpr (Finset.mem_filter.mp hγ).2
    · exact hΔdeg
  have hR : R.card ≤ p * Fintype.card ι := by
    apply principal_incidence_count x V q p d hd hq hdeg heval R
    intro γ hγ
    obtain ⟨hγΓ, hγΔ⟩ := Finset.mem_filter.mp hγ
    exact hroots γ hγΓ hγΔ
  have hsum : E.card + R.card = Γ.card := by
    exact Finset.card_filter_add_card_filter_not _
  omega
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.PrimitiveVector
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F col : Type*} [Field F] [Fintype col]
def IsPrimitive (P : col → F[X]) : Prop := Ideal.span (Set.range P) = ⊤
theorem primitive_iff_bezout (P : col → F[X]) :
    IsPrimitive P ↔ ∃ a : col → F[X], ∑ i, a i * P i = 1 := by
  rw [IsPrimitive, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
theorem exists_normalization (P : col → F[X]) (hP : P ≠ 0) :
    ∃ (g : F[X]) (Q : col → F[X]), g ≠ 0 ∧
      (∀ i, P i = g * Q i) ∧ IsPrimitive Q := by
  classical
  let I := Ideal.span (Set.range P)
  let g := Submodule.IsPrincipal.generator I
  have hg : g ≠ 0 := by
    intro hg
    have hI : I = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hg
    apply hP
    funext i
    have hm : P i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    rw [hI] at hm
    exact hm
  have hdiv : ∀ i, ∃ q : F[X], P i = g * q := by
    intro i
    have hm : P i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hm
    exact ⟨q, by simpa only [smul_eq_mul, mul_comm] using hq⟩
  choose Q hQ using hdiv
  refine ⟨g, Q, hg, hQ, (primitive_iff_bezout Q).mpr ?_⟩
  have hgm : g ∈ I := Submodule.IsPrincipal.generator_mem I
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgm
  refine ⟨a, ?_⟩
  have heq : g * (∑ i, a i * Q i) = g * 1 := by
    rw [Finset.mul_sum, mul_one]
    calc
      _ = ∑ i, a i * P i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hQ i]
        ring
      _ = g := ha
  exact mul_left_cancel₀ hg heq
theorem eval_ne_zero (P : col → F[X]) (hP : IsPrimitive P) (γ : F) :
    (fun i => (P i).eval γ) ≠ 0 := by
  obtain ⟨a, ha⟩ := (primitive_iff_bezout P).mp hP
  intro hzero
  have heval := congrArg (evalRingHom γ) ha
  simp only [map_sum, map_mul, map_one, Polynomial.coe_evalRingHom] at heval
  have hz : ∀ i, (P i).eval γ = 0 := fun i => congrFun hzero i
  simp only [hz, mul_zero, Finset.sum_const_zero] at heval
  exact zero_ne_one heval
theorem exists_eval_ne_zero (P : col → F[X]) (hP : IsPrimitive P) (γ : F) :
    ∃ i, (P i).eval γ ≠ 0 := by
  by_contra h
  push_neg at h
  exact eval_ne_zero P hP γ (funext h)
theorem normalization_natDegree_le (P Q : col → F[X]) (g : F[X]) (hg : g ≠ 0)
    (hPQ : ∀ i, P i = g * Q i) (i : col) :
    (Q i).natDegree ≤ (P i).natDegree := by
  by_cases hQ : Q i = 0
  · simp [hQ]
  · rw [hPQ i, Polynomial.natDegree_mul hg hQ]
    omega
theorem normalization_preserves_kernel {row : Type*} [DecidableEq col]
    (M : Matrix row col F[X]) (P Q : col → F[X]) (g : F[X]) (hg : g ≠ 0)
    (hPQ : ∀ i, P i = g * Q i) (hM : M.mulVec P = 0) :
    M.mulVec Q = 0 := by
  have heq : P = g • Q := by
    funext i
    exact hPQ i
  rw [heq, Matrix.mulVec_smul] at hM
  funext i
  have hi := congrFun hM i
  change g * (M.mulVec Q) i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hg
end
end FrobeniusLocator.PrimitiveVector
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}
theorem vector_free_coordinate (B : NormalFiber.RowBasis φ M r) (j c : col)
    (hc : c ∉ Set.range B.cols) :
    vector B j c = if j = c then (NormalFiber.pivot B).det else 0 := by
  rw [vector, rawVector_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hzero : ∀ q, inclusion B.cols c q = (0 : F[X]) := by
    intro q
    have hq : B.cols q ≠ c := fun h => hc ⟨q, h⟩
    simp [inclusion, hq]
  simp only [hzero, zero_mul, Finset.sum_const_zero, sub_zero]
  by_cases hj : j = c <;> simp [hj, NormalFiber.pivot]
end
end FrobeniusLocator.GenericCofactor
end
section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericLayer
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F row col : Type*} [Field F] [Fintype row] [Fintype col] [DecidableEq col]
abbrev GenericField (F : Type*) [Field F] := FractionRing F[X]
def genericRank (M : Matrix row col F[X]) : ℕ :=
  (M.map (algebraMap F[X] (GenericField F))).rank
def genericNullity (M : Matrix row col F[X]) : ℕ :=
  Module.finrank (GenericField F)
    (LinearMap.ker (M.map (algebraMap F[X] (GenericField F))).mulVecLin)
theorem rank_add_nullity (M : Matrix row col F[X]) :
    genericRank M + genericNullity M = Fintype.card col := by
  simpa only [genericRank, genericNullity, Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker
      (M.map (algebraMap F[X] (GenericField F))).mulVecLin
theorem exists_generic_basis (M : Matrix row col F[X]) :
    Nonempty (NormalFiber.RowBasis (algebraMap F[X] (GenericField F)) M (genericRank M)) :=
  NormalFiber.exists_rowBasis _ M _ rfl
end
end FrobeniusLocator.GenericLayer
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance decidableDivisor (P : Prop) : Decidable P := Classical.propDecidable P
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
theorem locator_eval_zero_iff (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (i : ι) : (locator x S).eval (x i) = 0 ↔ i ∈ S := by
  simp only [locator, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, sub_eq_zero, hx.eq_iff]
  simp
theorem locator_mul_sdiff (x : ι → F) (H S : Finset ι) (hHS : H ⊆ S) :
    locator x H * locator x (S \ H) = locator x S := by
  simpa only [locator, mul_comm] using
    (Finset.prod_sdiff (f := fun i => (X-C (x i) : F[X])) hHS)
theorem remove_fixed_factor (x : ι → F) (hx : Function.Injective x)
    (H S : Finset ι) (V Q : F[X])
    (hfactor : locator x S = locator x H * V * Q) :
    V ∣ locator x (S \ H) ∧ ∀ i, V.eval (x i) = 0 → i ∉ H := by
  have hHS : H ⊆ S := by
    intro i hi
    apply (locator_eval_zero_iff x hx S i).mp
    rw [hfactor, eval_mul, eval_mul, locator_eval_zero x H i hi, zero_mul, zero_mul]
  have hcancel : locator x (S \ H) = V*Q := by
    apply mul_left_cancel₀ (locator_monic x H).ne_zero
    rw [locator_mul_sdiff x H S hHS, hfactor]
    ring
  refine ⟨⟨Q,hcancel⟩,?_⟩
  intro i hi
  have hz : (locator x (S \ H)).eval (x i) = 0 := by
    rw [hcancel, eval_mul, hi, zero_mul]
  exact (Finset.mem_sdiff.mp ((locator_eval_zero_iff x hx _ i).mp hz)).2
theorem roots_outside_fixed_card (x : ι → F) (H : Finset ι) (V : F[X])
    (havoid : ∀ i, V.eval (x i) = 0 → i ∉ H) :
    (Finset.univ.filter (fun i : {i // i ∉ H} => V.eval (x i.val) = 0)).card =
      (Finset.univ.filter (fun i => V.eval (x i) = 0)).card := by
  classical
  let D := Finset.univ.filter (fun i : {i // i ∉ H} => V.eval (x i.val) = 0)
  have himage : D.image Subtype.val =
      Finset.univ.filter (fun i => V.eval (x i) = 0) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      exact ⟨⟨i,havoid i hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
theorem locator_roots (x : ι → F) (S : Finset ι) :
    (locator x S).roots = S.val.map x := by
  rw [locator, Polynomial.roots_prod _ _ (locator_monic x S).ne_zero]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
theorem locator_splits (x : ι → F) (S : Finset ι) : (locator x S).Splits := by
  exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C (x i))
theorem divisor_domain_roots (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (V : F[X]) (hV : V ∣ locator x S) :
    V.natDegree = (Finset.univ.filter (fun i => V.eval (x i) = 0)).card := by
  classical
  have hE0 := (locator_monic x S).ne_zero
  have hV0 : V ≠ 0 := ne_zero_of_dvd_ne_zero hE0 hV
  have hsplits := (locator_splits x S).of_dvd hE0 hV
  have hle := Polynomial.roots.le_of_dvd hE0 hV
  rw [locator_roots] at hle
  have hnodup : V.roots.Nodup := Multiset.nodup_of_le hle (S.nodup.map hx)
  have himage : (Finset.univ.filter (fun i => V.eval (x i) = 0)).image x =
      V.roots.toFinset := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Polynomial.mem_roots hV0).mpr hi
    · intro ha
      have hEa := Multiset.mem_of_le hle ha
      obtain ⟨i, hiS, hia⟩ := Multiset.mem_map.mp hEa
      refine ⟨i, ?_, hia⟩
      change V.eval (x i) = 0
      rw [hia]
      exact (Polynomial.mem_roots hV0).mp ha
  calc
    V.natDegree = V.roots.card := hsplits.natDegree_eq_card_roots
    _ = V.roots.toFinset.card := (Multiset.toFinset_card_of_nodup hnodup).symm
    _ = ((Finset.univ.filter (fun i => V.eval (x i) = 0)).image x).card :=
      congrArg Finset.card himage.symm
    _ = _ := Finset.card_image_of_injective _ hx
theorem full_degree_of_factorization (H V Q : F[X]) (h d q : ℕ)
    (hH : H.natDegree = h) (hV : V.natDegree ≤ d) (hQ : Q.natDegree ≤ q)
    (htotal : (H * V * Q).natDegree = h + d + q) : V.natDegree = d := by
  have htotal_le : (H * V * Q).natDegree ≤ h + V.natDegree + q := by
    calc
      _ ≤ (H * V).natDegree + Q.natDegree := Polynomial.natDegree_mul_le
      _ ≤ H.natDegree + V.natDegree + Q.natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ _ := by omega
  omega
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericLayer
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
theorem stacked_ordinary (p : ℕ) [ExpChar F p] (x u v : ι → F) (L t : ℕ) :
    (stacked p x u v L t).submatrix (NormalFiber.ordinaryRows L) id =
      hankel x u v L t := by
  funext i j
  simp [stacked, NormalFiber.ordinaryRows]
theorem exists_frobenius_basis (p : ℕ) [ExpChar F p] (x u v : ι → F)
    (L t r : ℕ)
    (hr : genericRank (stacked p x u v L t) = t+1-r)
    (hfirst : genericRank (hankel x u v L t) = L) :
    ∃ B : NormalFiber.RowBasis (algebraMap F[X] (GenericField F))
        (stacked p x u v L t) (t+1-r),
      (∑ q, if (B.rows q).1 = 0 then 1 else p) = L + p * (t+1-r-L) ∧
      (NormalFiber.pivot B).det.natDegree ≤ L + p * (t+1-r-L) := by
  let φ := algebraMap F[X] (GenericField F)
  have hfirst' : (((stacked p x u v L t).map φ).submatrix
      (NormalFiber.ordinaryRows L) id).rank = L := by
    have heq : ((stacked p x u v L t).map φ).submatrix
        (NormalFiber.ordinaryRows L) id = (hankel x u v L t).map φ := by
      funext i j
      exact congrArg φ (congrFun (congrFun (stacked_ordinary p x u v L t) i) j)
    rw [heq]
    exact hfirst
  exact NormalFiber.exists_stacked_basis φ L (t+1-r) p _ hr
    (NormalFiber.first_rows_independent_of_rank φ L _ hfirst')
    (stacked_entry_natDegree p x u v L t)
end
end FrobeniusLocator.GenericLayer
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.GenericCofactor
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype row]
  [Fintype col] [DecidableEq col]
variable {φ : F[X] →+* K} {M : Matrix row col F[X]} {r : ℕ}
theorem exists_primitive_line (B : NormalFiber.RowBasis φ M r)
    (hφ : Function.Injective φ) (hnull : r + 1 = Fintype.card col)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i) :
    ∃ Q : col → F[X], PrimitiveVector.IsPrimitive Q ∧ M.mulVec Q = 0 ∧
      (∀ c, (Q c).natDegree ≤ ∑ q, d (B.rows q)) ∧
      ∀ (γ : F), (NormalFiber.pivot B).det.eval γ ≠ 0 →
        ∀ v : col → F, (M.map (evalRingHom γ)).mulVec v = 0 →
          ∃ a : F, v = a • (fun c => (Q c).eval γ) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : col, j ∉ Set.range B.cols := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective B.cols := fun j => h j
    have hc := Fintype.card_le_of_surjective B.cols hsurj
    rw [Fintype.card_fin] at hc
    omega
  have hP : vector B j ≠ 0 := by
    intro hzero
    have h := vector_free_coordinate B j j hj
    rw [if_pos rfl] at h
    apply B.minor_ne
    simpa only [NormalFiber.pivot, Pi.zero_apply] using
      h.symm.trans (congrFun hzero j)
  obtain ⟨g, Q, hg, hPQ, hprim⟩ := PrimitiveVector.exists_normalization (vector B j) hP
  have hQ : M.mulVec Q = 0 := PrimitiveVector.normalization_preserves_kernel
    M (vector B j) Q g hg hPQ (annihilates B hφ j)
  refine ⟨Q, hprim, hQ, ?_, ?_⟩
  · intro c
    exact (PrimitiveVector.normalization_natDegree_le _ _ _ hg hPQ c).trans
      (vector_natDegree_le B d hdeg j c)
  · intro γ hγ v hv
    have hR := NormalFiber.rank_specializes φ hφ M r B γ hγ
    have hdim : Module.finrank F
        (LinearMap.ker (M.map (evalRingHom γ)).mulVecLin) = 1 := by
      have hh := LinearMap.finrank_range_add_finrank_ker (M.map (evalRingHom γ)).mulVecLin
      change (M.map (evalRingHom γ)).rank + _ = _ at hh
      rw [hR, Module.finrank_fintype_fun_eq_card] at hh
      omega
    have hQγ : (M.map (evalRingHom γ)).mulVec (fun c => (Q c).eval γ) = 0 := by
      funext i
      have h := congrArg (evalRingHom γ) (congrFun hQ i)
      simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
        Matrix.map_apply, Polynomial.coe_evalRingHom, Pi.zero_apply] using h
    exact GenericRank.kernel_line_of_finrank _ hdim _
      (PrimitiveVector.eval_ne_zero Q hprim γ) hQγ v hv
end
end FrobeniusLocator.GenericCofactor
end
section
namespace FrobeniusLocator
noncomputable section
open Polynomial Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
def ExtendsOn (x : ι → F) (w : ι → F) (k : ℕ) (S : Finset ι) : Prop :=
  ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S, P.eval (x i) = w i
theorem trim_nonextendable (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (hbad : ¬ ExtendsOn x w k S) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧ ¬ ExtendsOn x w k T := by
  classical
  obtain ⟨B, hBS, hBcard⟩ := Finset.exists_subset_card_eq (show k ≤ S.card by omega)
  have hBinj : Set.InjOn x (B : Set ι) := fun a _ b _ h => hx h
  let q := Lagrange.interpolate B x w
  have hqdeg : q.degree < (k : WithBot ℕ) := by
    simpa only [q, hBcard] using Lagrange.degree_interpolate_lt w hBinj
  have hqval : ∀ i ∈ B, q.eval (x i) = w i :=
    fun i hi => Lagrange.eval_interpolate_at_node w hBinj hi
  obtain ⟨a, haS, ha⟩ : ∃ a ∈ S, q.eval (x a) ≠ w a := by
    by_contra hh
    push Not at hh
    exact hbad ⟨q, hqdeg, hh⟩
  have haB : a ∉ B := fun hh => ha (hqval a hh)
  have hins : insert a B ⊆ S := Finset.insert_subset_iff.mpr ⟨haS, hBS⟩
  have hsmall : (insert a B).card ≤ A := by
    rw [Finset.card_insert_of_notMem haB, hBcard]
    omega
  obtain ⟨T, hBT, hTS, hTcard⟩ := Finset.exists_subsuperset_card_eq hins hsmall hAS
  refine ⟨T, hTS, hTcard, ?_⟩
  rintro ⟨P, hP, hPv⟩
  have hpq : P = q := Polynomial.eq_of_degrees_lt_of_eval_index_eq B hBinj
    (by simpa only [hBcard] using hP) (by simpa only [hBcard] using hqdeg)
    (fun i hi => (hPv i (hBT (Finset.mem_insert_of_mem hi))).trans (hqval i hi).symm)
  exact ha (hpq ▸ hPv a (hBT (Finset.mem_insert_self a B)))
theorem trim_nonjoint (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (hbad : ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧
      ¬ (ExtendsOn x u k T ∧ ExtendsOn x v k T) := by
  classical
  by_cases hu : ExtendsOn x u k S
  · obtain ⟨T, hTS, hTcard, hTbad⟩ := trim_nonextendable x hx v k A hkA S hAS
      (fun hv => hbad ⟨hu, hv⟩)
    exact ⟨T, hTS, hTcard, fun h => hTbad h.2⟩
  · obtain ⟨T, hTS, hTcard, hTbad⟩ := trim_nonextendable x hx u k A hkA S hAS hu
    exact ⟨T, hTS, hTcard, fun h => hTbad h.1⟩
theorem exact_A_bad_witness (x : ι → F) (hx : Function.Injective x)
    (u v : ι → F) (γ : F) (k A : ℕ) (hkA : k < A) (S : Finset ι)
    (hAS : A ≤ S.card) (P : F[X]) (hP : P.degree < k)
    (hfold : ∀ i ∈ S, P.eval (x i) = u i + γ * v i)
    (hbad : ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = A ∧ P.degree < k ∧
      (∀ i ∈ T, P.eval (x i) = u i + γ * v i) ∧
      ¬ (ExtendsOn x u k T ∧ ExtendsOn x v k T) := by
  obtain ⟨T, hTS, hcard, hbadT⟩ := trim_nonjoint x hx u v k A hkA S hAS hbad
  exact ⟨T, hTS, hcard, hP, fun i hi => hfold i (hTS hi), hbadT⟩
end
end FrobeniusLocator
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
def LocatorMoments (x : ι → F) (w : ι → F) (E : F[X]) (L : ℕ) : Prop :=
  ∀ j < L, ∑ i, weight x i * (E.eval (x i) * w i) * x i ^ j = 0
theorem extendsOn_of_locator_moments (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k L : ℕ) (S : Finset ι)
    (hsize : k + L + S.card = Fintype.card ι)
    (hmom : LocatorMoments x w (locator x S) L) :
    ExtendsOn x w k (Finset.univ \ S) := by
  classical
  let T := Finset.univ \ S
  let P := Lagrange.interpolate T x w
  have hTcard : T.card = Fintype.card ι - S.card := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  have hPinj : Set.InjOn x (T : Set ι) := hx.injOn
  have hPval : ∀ i ∈ T, P.eval (x i) = w i :=
    fun i hi => Lagrange.eval_interpolate_at_node w hPinj hi
  refine ⟨P, ?_, hPval⟩
  by_contra hP
  have hp0 : P ≠ 0 := by
    intro hz
    simp [hz] at hP
  have hPnat : k ≤ P.natDegree := by
    have hnot := not_lt.mp hP
    exact_mod_cast hnot.trans Polynomial.degree_le_natDegree
  have hPbound : P.natDegree < Fintype.card ι - S.card := by
    apply (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr
    simpa only [P, hTcard] using Lagrange.degree_interpolate_lt w hPinj
  let j := Fintype.card ι - 1 - S.card - P.natDegree
  have hj : j < L := by omega
  have htop : S.card + P.natDegree + j = Fintype.card ι - 1 := by omega
  let Q := locator x S * P * X ^ j
  have hE0 : locator x S ≠ 0 := (locator_monic x S).ne_zero
  have hQdeg : Q.natDegree = Fintype.card ι - 1 := by
    dsimp [Q]
    rw [natDegree_mul (mul_ne_zero hE0 hp0) (pow_ne_zero _ X_ne_zero),
      natDegree_mul hE0 hp0, locator_natDegree, natDegree_X_pow, htop]
  have hQlt : Q.degree < (Fintype.card ι : WithBot ℕ) := by
    apply Polynomial.degree_le_natDegree.trans_lt
    rw [hQdeg]
    exact_mod_cast (show Fintype.card ι - 1 < Fintype.card ι by omega)
  have hcoeff := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x)
    (fun a _ b _ hab => hx hab) (by simpa using hQlt)
  have hpoint (i : ι) :
      (locator x S).eval (x i) * P.eval (x i) =
      (locator x S).eval (x i) * w i := by
    by_cases hi : i ∈ S
    · simp [locator_eval_zero x S i hi]
    · rw [hPval i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)]
  have hsum : ∑ i, weight x i * Q.eval (x i) = 0 := by
    dsimp [Q]
    simp only [eval_mul, eval_pow, eval_X]
    simp_rw [hpoint]
    simpa only [mul_assoc] using hmom j hj
  have hz : Q.coeff (Fintype.card ι - 1) = 0 := by
    have hc : Q.coeff (Fintype.card ι - 1) =
        ∑ i, weight x i * Q.eval (x i) := by
      simpa only [Finset.card_univ, weight, div_eq_mul_inv, mul_comm] using hcoeff
    exact hc.trans hsum
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero hE0 hp0) (pow_ne_zero _ X_ne_zero)
  apply (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
  simpa only [Polynomial.leadingCoeff, hQdeg] using hz
theorem hankel_word_moments (x : ι → F) (w : ι → F) (E : F[X]) (L t : ℕ)
    (hE : E.natDegree ≤ t)
    (hrec : ∀ i : Fin L, ∑ j : Fin (t+1),
      syndrome x w (i.val+j.val) * E.coeff j.val = 0) :
    LocatorMoments x w E L := by
  intro i hi
  have hh := hrec ⟨i, hi⟩
  have hsum : (∑ j : Fin (t+1), syndrome x w (i+j.val) * E.coeff j.val) =
      ∑ a, weight x a * (E.eval (x a) * w a) * x a ^ i := by
    simp only [syndrome, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← sum_coeff_eval E t hE (x a)]
    simp only [Finset.sum_mul, Finset.mul_sum, pow_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact hsum.symm.trans hh
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {K : Type*} [Field K]
def hankelWindow (s : Fin 2 → ℕ → K) (rows cols : ℕ) :
    Matrix (Fin 2 × Fin rows) (Fin cols) K :=
  fun b j => s b.1 (b.2.val+j.val)
def relationMatrix (s : Fin 2 → ℕ → K) (m H : ℕ) :
    Matrix (Fin (m-H)) (Fin 2 × Fin (H+1)) K :=
  (hankelWindow s (H+1) (m-H)).transpose
theorem relation_equations (s : Fin 2 → ℕ → K) (m H : ℕ)
    (v : Fin 2 × Fin (H+1) → K) :
    (relationMatrix s m H).mulVec v=0 ↔
      ∀ j : Fin (m-H), ∑ b : Fin 2, ∑ i : Fin (H+1),
        v (b,i)*s b (i.val+j.val)=0 := by
  simp only [funext_iff, Matrix.mulVec, dotProduct, relationMatrix, hankelWindow,
    Matrix.transpose_apply, Pi.zero_apply, Fintype.sum_prod_type, mul_comm]
theorem complementary_nullities (s : Fin 2 → ℕ → K) (m H : ℕ) :
    Module.finrank K (LinearMap.ker (relationMatrix s m H).mulVecLin)+(m-H) =
      2*(H+1)+Module.finrank K
        (LinearMap.ker (hankelWindow s (H+1) (m-H)).mulVecLin) := by
  have hr := LinearMap.finrank_range_add_finrank_ker (relationMatrix s m H).mulVecLin
  have hk := LinearMap.finrank_range_add_finrank_ker
    (hankelWindow s (H+1) (m-H)).mulVecLin
  change (relationMatrix s m H).rank + _ = _ at hr
  change (hankelWindow s (H+1) (m-H)).rank + _ = _ at hk
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hr
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk
  have he : (relationMatrix s m H).rank=(hankelWindow s (H+1) (m-H)).rank :=
    Matrix.rank_transpose _
  omega
def HasLevelHilbertFunction (s : Fin 2 → ℕ → K) (m a b c : ℕ) : Prop :=
  ∀ H<m, Module.finrank K
    (LinearMap.ker (hankelWindow s (H+1) (m-H)).mulVecLin) =
      (m-H-a)+(m-H-b)+(m-H-c)
theorem relation_nullity_on_two_active (s : Fin 2 → ℕ → K)
    (m a b c H : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b≤m-H) (hH : m+1-c≤H) (hHm : H<m)
    (hHF : HasLevelHilbertFunction s m a b c) :
    Module.finrank K (LinearMap.ker (relationMatrix s m H).mulVecLin) =
      H-(m+1-c)+1 := by
  have hd := complementary_nullities s m H
  rw [hHF H hHm] at hd
  omega
theorem minimal_relation_line (s : Fin 2 → ℕ → K)
    (m a b c : ℕ) (hc : c≤m) (hsum : a+b+c=2*m+2)
    (ha : a≤b) (hb : b<c) (hc2 : 1<c)
    (hHF : HasLevelHilbertFunction s m a b c) :
    Module.finrank K (LinearMap.ker (relationMatrix s m (m+1-c)).mulVecLin)=1 := by
  have h := relation_nullity_on_two_active s m a b c (m+1-c) hc hsum ha
    (by omega) (by omega) (by omega) hHF
  simpa using h
end
end FrobeniusLocator.Strata
end
section
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
theorem extendsOn_of_syndrome_zero (x : ι → F) (hx : Function.Injective x)
    (w : ι → F) (k : ℕ) (hk : k ≤ Fintype.card ι)
    (hzero : ∀ j < Fintype.card ι-k, syndrome x w j = 0) :
    ExtendsOn x w k Finset.univ := by
  have hmom : LocatorMoments x w (locator x ∅) (Fintype.card ι-k) := by
    intro j hj
    simpa [syndrome, locator] using hzero j hj
  simpa using extendsOn_of_locator_moments x hx w k (Fintype.card ι-k) ∅
    (by simp; omega) hmom
theorem syndrome_linear (x u v : ι → F) (a b : F) (j : ℕ) :
    syndrome x (fun i => a*u i+b*v i) j = a*syndrome x u j+b*syndrome x v j := by
  simp only [syndrome, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
end
end FrobeniusLocator.Principal
end
section
namespace Sol1.C52
open scoped BigOperators Matrix
noncomputable section
theorem rank_le_col_representatives
    {F R C C' : Type*} [Field F] [Fintype C] [Fintype C']
    (M : Matrix R C F) (rep : C' → C)
    (h : ∀ c, M.col c = 0 ∨ ∃ j, M.col c = M.col (rep j)) :
    M.rank ≤ (M.submatrix id rep).rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (M.submatrix id rep).col)
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  rcases h c with hz | ⟨j,hj⟩
  · rw [hz]
    exact Submodule.zero_mem _
  · rw [hj]
    exact Submodule.subset_span ⟨j,rfl⟩
end
end Sol1.C52
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
open Finset
def V (D w B s t : ℕ) : ℕ :=
  ∑ i ∈ range (B+1), ∑ j ∈ range (B+1-i),
    (D+1-w*(i+j))*(s+1-i)*(t+1-j)
def J (m s t : ℕ) : ℕ :=
  ∑ i ∈ range m, ∑ j ∈ range (m-i),
    (m-i-j)*(s+1-i)*(t+1-j)
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Polynomial Finset
def clearedEval {R : Type*} [CommRing R] (B : ℕ) (Q : R[X]) (a b : R) : R :=
  ∑ j∈range (B+1),Q.coeff j*a^j*b^(B-j)
theorem clearedEval_at_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R) (hy : b*y=a) :
    clearedEval B Q a b=b^B*Q.eval y := by
  rw [eval_eq_sum_range' (show Q.natDegree<B+1 by omega),mul_sum]
  unfold clearedEval
  apply sum_congr rfl
  intro j hj
  have hjB : j≤B := by have := mem_range.mp hj; omega
  rw [← hy,mul_pow]
  have hb : b^j*b^(B-j)=b^B := by rw [← pow_add,Nat.add_sub_of_le hjB]
  calc
    Q.coeff j*(b^j*y^j)*b^(B-j) = Q.coeff j*y^j*(b^j*b^(B-j)) := by ring
    _ = b^B*(Q.coeff j*y^j) := by rw [hb]; ring
theorem clearedEval_zero_of_root {R : Type*} [CommRing R]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b y : R)
    (hy : b*y=a) (hroot : Q.eval y=0) : clearedEval B Q a b=0 := by
  rw [clearedEval_at_root B Q hQ a b y hy,hroot,mul_zero]
theorem clearedEval_ne_zero_field {K : Type*} [Field K]
    (B : ℕ) (Q : K[X]) (hQ : Q.natDegree≤B) (a b : K) (hb : b≠0)
    (hnot : ¬ (C b*X-C a) ∣ Q) : clearedEval B Q a b≠0 := by
  have heq : C b*X-C a=C b*(X-C (a/b)) := by
    rw [mul_sub,← C_mul]
    have hba : b*(a/b)=a := by field_simp
    rw [hba]
  have hroot : Q.eval (a/b)≠0 := by
    intro hz
    apply hnot
    rw [heq]
    have hd : (X-C (a/b))∣Q := (dvd_iff_isRoot).mpr hz
    have hu : C b ∣ (1 : K[X]) := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)).dvd
    simpa using mul_dvd_mul hu hd
  rw [clearedEval_at_root B Q hQ a b (a/b) (by field_simp)]
  exact mul_ne_zero (pow_ne_zero B hb) hroot
theorem map_clearedEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B : ℕ) (Q : R[X]) (a b : R) :
    f (clearedEval B Q a b)=clearedEval B (Q.map f) (f a) (f b) := by
  simp [clearedEval]
theorem clearedEval_ne_zero {R K : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : ℕ) (Q : R[X]) (hQ : Q.natDegree≤B) (a b : R) (hb : b≠0)
    (hprimitive : (C b*X-C a).IsPrimitive) (hnot : ¬ (C b*X-C a)∣Q) :
    clearedEval B Q a b≠0 := by
  have hmap : ¬ (C (algebraMap R K b)*X-C (algebraMap R K a))∣Q.map (algebraMap R K) := by
    simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X] using
      (not_congr (hprimitive.dvd_iff_fraction_map_dvd_fraction_map K)).mp hnot
  have hdeg : (Q.map (algebraMap R K)).natDegree≤B := (natDegree_map_le).trans hQ
  have hb' : algebraMap R K b≠0 := by simpa using (IsFractionRing.injective R K).ne hb
  have hn := clearedEval_ne_zero_field B (Q.map (algebraMap R K)) hdeg
    (algebraMap R K a) (algebraMap R K b) hb' hmap
  rw [← map_clearedEval] at hn
  exact fun hz => hn (by rw [hz,map_zero])
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11_3
noncomputable section
open Polynomial
theorem exists_simple_derivative_at_root {R : Type*} [CommRing R] [IsDomain R]
    (p B : ℕ) [CharP R p] (f : R[X]) (hf : f≠0) (hdegree : f.natDegree≤B)
    (hsmall : B<p) (y : R) (hroot : f.IsRoot y) :
    ∃ j<B,(derivative^[j] f).IsRoot y ∧ ¬(derivative (derivative^[j] f)).IsRoot y := by
  let μ := f.rootMultiplicity y
  have hμpos : 0<μ := (rootMultiplicity_pos hf).mpr hroot
  have hμle : μ≤B := by
    have hd := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd y) hf
    have hle : μ≤f.natDegree := by simpa [μ,natDegree_pow] using hd
    exact hle.trans hdegree
  have hnzd : ∀ m≤μ,m≠0 → (m : R)∈nonZeroDivisors R := by
    intro m hm hmn
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hd : p∣m := (CharP.cast_eq_zero_iff R p m).mp hz
    have hp : p≤m := Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hd
    omega
  have hnext : ¬(derivative^[μ] f).IsRoot y := by
    intro hnext
    have hall : ∀ m≤μ,(derivative^[m] f).IsRoot y := by
      intro m hm
      rcases lt_or_eq_of_le hm with hh | rfl
      · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hh
      · exact hnext
    have hc := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd
    exact (Nat.lt_irrefl μ) hc
  refine ⟨μ-1,by omega,isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega),?_⟩
  have he : derivative (derivative^[μ-1] f)=derivative^[μ] f := by
    simpa only [Nat.succ_eq_add_one,Nat.sub_add_cancel hμpos] using (Function.iterate_succ_apply' derivative (μ-1) f).symm
  rwa [he]
end
end K1_11_3
end
