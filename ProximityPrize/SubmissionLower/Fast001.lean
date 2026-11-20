import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
set_option Elab.async false

section PackSource_K1_14_2_2_7_4_4_6Normalization
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_2_2_7_4_4_6

noncomputable section

open scoped nonZeroDivisors

/-- Every nonzero ideal of a finite-type Dedekind algebra cuts a finite-dimensional algebra. -/
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
/-- Compare the cut before and after the finite birational normalization. -/
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
end PackSource_K1_14_2_2_7_4_4_6Normalization

section PackSource_K1_13_7_5_3_3_1Aux
set_option autoImplicit true
namespace K1_13_7_5_3_3_1

open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise

universe u v

section Local

variable {k : Type v} [Field k] [Infinite k]
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra k R]

include k in
omit [IsLocalRing R] in
/-- A coset of a subideal contains a regular element if the subideal and the
coset representative together avoid containment in every associated prime. -/
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
/-- A list generating an ideal with maximal radical is weakly regular if it
has the same length as a regular sequence in the maximal ideal. -/
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
end PackSource_K1_13_7_5_3_3_1Aux
