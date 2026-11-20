import ProximityPrize.SubmissionLower.Fast000
import ProximityPrize.SubmissionLower.Fast001
import ProximityPrize.SubmissionLower.Fast002
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast060
import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast066
import ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast035
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast059
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast067
set_option Elab.async false

section PackSource_K1_13_5_4_2_2_1Filtration
set_option autoImplicit true
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace K1_13_5_4_2_2_1

noncomputable section

open K1_13_5_4_2_2 K1_13_6_3_4 MvPolynomial

variable {k σ : Type} [Field k] [Finite σ]

/-- A bounded filtration piece generates the coordinate ring over the parameter. -/
theorem projection_finite_of_reduction (I : Ideal (MvPolynomial σ k)) (a : σ → k)
    (hred : ValueReduction I (linearForm a)) : (projection I a).Finite := by
  classical
  obtain ⟨N, hN⟩ := hred
  let A := MvPolynomial σ k ⧸ I
  let g := projection I a
  letI : Algebra (Polynomial k) A := g.toRingHom.toAlgebra
  change Module.Finite (Polynomial k) A
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (R := k)).mp
    (inferInstance : Module.Finite k (quotientDegreeLE I N))
  let T : Submodule (Polynomial k) A := Submodule.span _ (s : Set A)
  have hbase : ∀ x ∈ quotientDegreeLE I N, x ∈ T := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact T.zero_mem
    | add x y _ _ hx hy => exact T.add_mem hx hy
    | smul c x _ hx =>
      have hc : (Polynomial.C c : Polynomial k) • x = c • x := by
        change g (Polynomial.C c) * x = c • x
        rw [← Polynomial.algebraMap_eq, g.commutes]
        exact (Algebra.smul_def c x).symm
      rw [← hc]
      exact T.smul_mem _ hx
  have hmul (x : A) : (Polynomial.X : Polynomial k) • x =
      Ideal.Quotient.mk I (linearForm a) * x := by
    change g Polynomial.X * x = _
    rw [show g Polynomial.X = Ideal.Quotient.mk I (linearForm a) from Polynomial.aeval_X _]
  have hall (n : ℕ) : ∀ x ∈ quotientDegreeLE I n, x ∈ T := by
    induction n with
    | zero => exact fun x hx => hbase x (quotientDegreeLE_mono I (Nat.zero_le N) hx)
    | succ n ih =>
      intro x hx
      by_cases hn : N ≤ n
      · obtain ⟨y, hy, z, hz, rfl⟩ := hN n hn x hx
        rw [← hmul]
        exact T.add_mem (ih y hy) (T.smul_mem _ (ih z hz))
      · exact hbase x (quotientDegreeLE_mono I (by omega) hx)
  apply Module.Finite.of_fg_top
  refine ⟨s, top_unique fun x _ => ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_quotientDegreeLE I x
  exact hall n x hn

theorem translated_reduction (I : Ideal (MvPolynomial σ k)) (a : σ → k) (t : k)
    (hred : ValueReduction I (linearForm a)) : ValueReduction I (linearForm a - C t) := by
  obtain ⟨N, hN⟩ := hred
  refine ⟨N, fun n hn x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := hN n hn x hx
  refine ⟨y + t • z, (quotientDegreeLE I n).add_mem hy ((quotientDegreeLE I n).smul_mem t hz),
    z, hz, ?_⟩
  have ht : t • z = Ideal.Quotient.mk I (C t) * z := Algebra.smul_def t z
  rw [ht, map_sub]
  ring

private theorem eventually_growth (I : Ideal (MvPolynomial σ k))
    (hI : (affineHilbertPolynomial I).natDegree = 1) :
    ∃ N : ℕ, ∀ n ≥ N, (affineHilbertFunction I (n + 1) : ℚ) =
      (affineHilbertFunction I n : ℚ) + affineDegree I := by
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  refine ⟨N, fun n hn => ?_⟩
  have hD : affineDegree I = (affineHilbertPolynomial I).coeff 1 := by
    simp [affineDegree, Polynomial.leadingCoeff, hI]
  rw [hD, ← hN (n + 1) (by omega), ← hN n hn]
  have hP := Polynomial.eq_X_add_C_of_natDegree_le_one hI.le
  conv_lhs => rw [hP]
  conv_rhs => enter [1]; rw [hP]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Nat.cast_add, Nat.cast_one]
  ring

omit [Finite σ] in
private theorem degreeLE_step (I : Ideal (MvPolynomial σ k)) {f : MvPolynomial σ k}
    (hf : f.totalDegree ≤ 1) {n : ℕ}
    (hred : ∀ x ∈ quotientDegreeLE I (n + 1),
      ∃ y ∈ quotientDegreeLE I n, ∃ z ∈ quotientDegreeLE I n,
        x = y + Ideal.Quotient.mk I f * z) :
    quotientDegreeLE I (n + 1) =
      quotientDegreeLE I n ⊔ (quotientDegreeLE I n).map (LinearMap.mulLeft k (Ideal.Quotient.mk I f)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hred x hx
    exact Submodule.mem_sup.mpr ⟨y, hy, _, Submodule.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩
  · apply sup_le (quotientDegreeLE_mono I (Nat.le_succ n))
    rintro x ⟨y, hy, rfl⟩
    simpa only [LinearMap.mulLeft_apply, Nat.add_comm] using
      mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE hf) hy

/-- Once the Hilbert function grows by a constant, the filtration recurrence and
regularity of the parameter imply that multiplication raises all high degrees by one. -/
private theorem strict_at_high_degree (I : Ideal (MvPolynomial σ k))
    (hI : I.IsPrime) (hdeg : (affineHilbertPolynomial I).natDegree = 1)
    {f : MvPolynomial σ k} (hf : f.totalDegree ≤ 1) (hred : ValueReduction I f) :
    Function.Injective (LinearMap.mulLeft k (Ideal.Quotient.mk I f)) ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ x : MvPolynomial σ k ⧸ I,
        Ideal.Quotient.mk I f * x ∈ quotientDegreeLE I (n + 1) → x ∈ quotientDegreeLE I n := by
  obtain ⟨N₁, hN₁⟩ := hred
  obtain ⟨N₂, hN₂⟩ := eventually_growth I hdeg
  let N := max N₁ N₂
  let F := quotientDegreeLE I
  let H := affineHilbertFunction I
  let v := Ideal.Quotient.mk I f
  let m := LinearMap.mulLeft k v
  have hstep (n : ℕ) (hn : N ≤ n) : F (n + 1) = F n ⊔ (F n).map m :=
    degreeLE_step I hf (hN₁ n ((le_max_left _ _).trans hn))
  have hv : v ≠ 0 := by
    intro hz
    have he : F (N + 1) ≤ F N := by
      intro x hx
      obtain ⟨y, hy, z, _, he⟩ := hN₁ N (le_max_left _ _) x hx
      have hxy : x = y := by simpa only [v, hz, zero_mul, add_zero] using he
      exact hxy.symm ▸ hy
    have hd : H (N + 1) ≤ H N := Submodule.finrank_mono he
    have hle : (H (N + 1) : ℚ) ≤ (H N : ℚ) := by exact_mod_cast hd
    have hg : (H (N + 1) : ℚ) = (H N : ℚ) + affineDegree I := hN₂ N (le_max_right _ _)
    linarith [affineDegree_pos hI.ne_top]
  letI : I.IsPrime := hI
  have hm : Function.Injective m := fun _ _ h => mul_left_cancel₀ hv h
  have hdim (n : ℕ) : Module.finrank k ((F n).map m) = H n :=
    (Submodule.equivMapOfInjective m hm (F n)).finrank_eq.symm
  have hinter (n : ℕ) (hn : N ≤ n) :
      (F n).map m = F (n + 1) ⊓ (F (n + 1)).map m := by
    have hn' : N₂ ≤ n := (le_max_right _ _).trans hn
    have hle : (F n).map m ≤ F (n + 1) ⊓ (F (n + 1)).map m := by
      refine le_inf ?_ (Submodule.map_mono (quotientDegreeLE_mono I (Nat.le_succ n)))
      rw [hstep n hn]
      exact le_sup_right
    have hrank := Submodule.finrank_sup_add_finrank_inf_eq (F (n + 1)) ((F (n + 1)).map m)
    rw [← hstep (n + 1) (by omega), hdim] at hrank
    change H (n + 2) + _ = H (n + 1) + H (n + 1) at hrank
    have hbalance : H (n + 2) + H n = H (n + 1) + H (n + 1) := by
      have h₁ : (H (n + 1) : ℚ) = (H n : ℚ) + affineDegree I := hN₂ n hn'
      have h₂ : (H (n + 2) : ℚ) = (H (n + 1) : ℚ) + affineDegree I := hN₂ (n + 1) (by omega)
      exact_mod_cast (show (H (n + 2) : ℚ) + (H n : ℚ) = (H (n + 1) : ℚ) + (H (n + 1) : ℚ) by
        linarith)
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hdim]
    omega
  refine ⟨hm, N, fun n hn x hx => ?_⟩
  obtain ⟨d, hd⟩ := exists_mem_quotientDegreeLE I x
  induction d with
  | zero => exact quotientDegreeLE_mono I (Nat.zero_le n) hd
  | succ d ih =>
    by_cases hdn : d < n
    · exact quotientDegreeLE_mono I (by omega) hd
    · have hx' : m x ∈ F (d + 1) ⊓ (F (d + 1)).map m :=
        ⟨quotientDegreeLE_mono I (by omega) hx, Submodule.mem_map.mpr ⟨x, hd, rfl⟩⟩
      rw [← hinter d (by omega)] at hx'
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
      exact ih ((hm hyx) ▸ hy)

/-- Rank-nullity on the large filtration pieces computes the length of the
scheme fiber, including any multiplicities. -/
theorem fiber_degree_of_reduction (I : Ideal (MvPolynomial σ k))
    (hI : I.IsPrime) (hdeg : (affineHilbertPolynomial I).natDegree = 1)
    {f : MvPolynomial σ k} (hf : f.totalDegree ≤ 1) (hred : ValueReduction I f) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = 0 ∧
      affineDegree (I ⊔ Ideal.span {f}) = affineDegree I := by
  let J := I ⊔ Ideal.span {f}
  let F := quotientDegreeLE I
  let v := Ideal.Quotient.mk I f
  let q := Ideal.Quotient.factorₐ k (show I ≤ J from le_sup_left)
  obtain ⟨hm, N₁, hN₁⟩ := strict_at_high_degree I hI hdeg hf hred
  obtain ⟨N₂, hN₂⟩ := eventually_growth I hdeg
  have hker {x : MvPolynomial σ k ⧸ I} (hx : q x = 0) :
      ∃ y : MvPolynomial σ k ⧸ I, v * y = x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J p = 0 at hx
    obtain ⟨r, hr, s, hs, he⟩ := Submodule.mem_sup.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    refine ⟨Ideal.Quotient.mk I u, ?_⟩
    rw [← map_mul, ← he, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_add, mul_comm]
  have hqv : q v = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hfun (n : ℕ) (hn : max N₁ N₂ ≤ n) :
      (affineHilbertFunction J (n + 1) : ℚ) = affineDegree I := by
    let cut : F (n + 1) →ₗ[k] quotientDegreeLE J (n + 1) :=
      (q.toLinearMap.domRestrict (F (n + 1))).codRestrict _ fun x => by
        obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp x.property
        rw [LinearMap.domRestrict_apply, ← he]
        exact mk_mem_quotientDegreeLE hp
    have hcut : Function.Surjective cut := by
      intro y
      obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp y.property
      exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext he⟩
    let mul : F n →ₗ[k] F (n + 1) :=
      ((LinearMap.mulLeft k v).domRestrict (F n)).codRestrict _ fun x => by
        change v * x.val ∈ F (n + 1)
        simpa only [Nat.add_comm] using mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE hf) x.property
    have hmul : Function.Injective mul := fun _ _ h => Subtype.ext (hm (congrArg Subtype.val h))
    have hkm : LinearMap.ker cut = LinearMap.range mul := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx
        obtain ⟨y, hy⟩ := hker (congrArg Subtype.val hx)
        have hy' : y ∈ F n := hN₁ n ((le_max_left _ _).trans hn) y (hy.symm ▸ x.property)
        exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        change q (v * y.val) = 0
        rw [map_mul, hqv, zero_mul]
    have hrank := cut.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hcut, finrank_top, hkm, LinearMap.finrank_range_of_inj hmul] at hrank
    change affineHilbertFunction J (n + 1) + affineHilbertFunction I n =
      affineHilbertFunction I (n + 1) at hrank
    have hc : (affineHilbertFunction J (n + 1) : ℚ) + (affineHilbertFunction I n : ℚ) =
        (affineHilbertFunction I (n + 1) : ℚ) := by exact_mod_cast hrank
    linarith only [hc, hN₂ n ((le_max_right _ _).trans hn)]
  have hpoly : Polynomial.C (affineDegree I) = affineHilbertPolynomial J := by
    apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max N₁ N₂ + 1)
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      rw [Polynomial.eval_C]
      exact (hfun n (by omega)).symm
  change (affineHilbertPolynomial J).natDegree = 0 ∧ affineDegree J = affineDegree I
  refine ⟨by rw [← hpoly, Polynomial.natDegree_C], ?_⟩
  change ((affineHilbertPolynomial J).natDegree.factorial : ℚ) *
    (affineHilbertPolynomial J).leadingCoeff = affineDegree I
  rw [← hpoly, Polynomial.natDegree_C, Nat.factorial_zero, Nat.cast_one, one_mul,
    Polynomial.leadingCoeff_C]

end
end K1_13_5_4_2_2_1
end PackSource_K1_13_5_4_2_2_1Filtration

section PackSource_K1_13_5_4_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_2_1

open K1_13_5_4_2_2 K1_13_5_4_4_2

theorem proof : K1_13_5_4_2_2.c1 := by
  intro k σ _ _ _ I hI hdim
  obtain ⟨bad, hproper, hbad⟩ := exists_boundary_exclusions I hdim
  refine ⟨bad, hproper, fun a ha => ?_⟩
  have hred := valueReduction_of_geometric (K := k) I (linearForm_homogeneous a) (hbad a ha)
  exact ⟨projection_finite_of_reduction I a hred, fun t =>
    fiber_degree_of_reduction I hI hdim (totalDegree_hyperplane_le_one a t)
      (translated_reduction I a t hred)⟩

end K1_13_5_4_2_2_1
end PackSource_K1_13_5_4_2_2_1Proof

section PackSource_K1_13_7_5_3_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_5_3_1_1

theorem proof : K1_13_7_5_3_1.c1 :=
  K1_13_7_5_3_1.degree_of_shared K1_13_5_4_2_2_1.proof

end K1_13_7_5_3_1_1
end PackSource_K1_13_7_5_3_1_1Proof

section PackSource_K1_13_5_4_2_4_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_4_1_2

noncomputable section

open K1_13_5_4_2_4_1
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open scoped Pointwise

variable {L : Type} [Field L]

private abbrev FiveVariables (L : Type) [Field L] := MvPolynomial (Fin 5) L

private theorem variable_cancel {d : ℕ} {s : Set (Fin d)} {i : Fin d} (hi : i ∉ s)
    (p : MvPolynomial (Fin d) L) (hp : MvPolynomial.X i * p ∈ span (MvPolynomial.X '' s)) :
    p ∈ span (MvPolynomial.X '' s) := by
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff := coeff_X_mul m i p
  have hmem : Finsupp.single i 1 + m ∈ (MvPolynomial.X i * p).support :=
    mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
  obtain ⟨j, hj, hne⟩ := hp _ hmem
  have hij : i ≠ j := fun e => hi (e.symm ▸ hj)
  exact ⟨j, hj, by simpa [Finsupp.add_apply, Finsupp.single_apply, hij] using hne⟩

private theorem ofList_take_variables {d n : ℕ} (hn : n ≤ d) :
    Ideal.ofList ((List.ofFn (MvPolynomial.X : Fin d → MvPolynomial (Fin d) L)).take n) =
      span (MvPolynomial.X '' {j : Fin d | j.val < n}) := by
  rw [← Fin.ofFn_take_eq_take_ofFn hn]
  apply congrArg (Ideal.span : Set (MvPolynomial (Fin d) L) → Ideal (MvPolynomial (Fin d) L))
  ext p
  change p ∈ List.ofFn (Fin.take n hn MvPolynomial.X) ↔
    p ∈ MvPolynomial.X '' {j : Fin d | j.val < n}
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hn j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, hj⟩, rfl⟩

private theorem variables_weaklyRegular (d : ℕ) :
    IsWeaklyRegular (MvPolynomial (Fin d) L)
      (List.ofFn (MvPolynomial.X : Fin d → MvPolynomial (Fin d) L)) := by
  classical
  refine ⟨?_⟩
  intro n hn
  have hn' : n < d := by simpa only [List.length_ofFn] using hn
  rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_variables hn'.le, List.getElem_ofFn]
  let s : Set (Fin d) := {j | j.val < n}
  exact (isSMulRegular_quotient_iff_mem_of_smul_mem
    (span ((MvPolynomial.X : Fin d → MvPolynomial (Fin d) L) '' s))
    (MvPolynomial.X ⟨n, hn'⟩)).mpr
    (variable_cancel (s := s) (i := ⟨n, hn'⟩) (Nat.lt_irrefl n))

private def translation (z : Fin 5 → L) : FiveVariables L ≃ₐ[L] FiveVariables L :=
  AlgEquiv.ofAlgHom (aeval (fun i => MvPolynomial.X i - C (z i))) (aeval (fun i => MvPolynomial.X i + C (z i)))
    (MvPolynomial.algHom_ext (fun i => by simp))
    (MvPolynomial.algHom_ext (fun i => by simp))

private def totalEquiv (L : Type) [Field L] : FiveVariables L ≃ₐ[L] Total L :=
  (renameEquiv L (_root_.finSuccEquiv 4)).trans (optionEquivRight L (Fin 4))

private theorem totalEquiv_zero : totalEquiv L (MvPolynomial.X 0) = C Polynomial.X := by
  rw [totalEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    _root_.finSuccEquiv_zero, optionEquivRight_X_none]

private theorem totalEquiv_succ (i : Fin 4) : totalEquiv L (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  rw [totalEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    _root_.finSuccEquiv_succ, optionEquivRight_X_some]

private theorem totalEquiv_C (c : L) : totalEquiv L (C c) = C (Polynomial.C c) := by
  rw [totalEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_C, optionEquivRight_C]

/-- The five coordinates translated to the closed point remain regular in the local ring. -/
private theorem reference_sequence (y : Fin 4 → L) :
    ∃ rs : List (TotalLocal y), rs.length = 5 ∧
      (∀ a ∈ rs, a ∈ maximalIdeal (TotalLocal y)) ∧ IsRegular (TotalLocal y) rs := by
  let z : Fin 5 → L := Fin.cases 0 y
  let e := ((translation z).trans (totalEquiv L)).toRingEquiv
  let rs := List.ofFn (MvPolynomial.X : Fin 5 → FiveVariables L)
  have hcongr : List.Forall₂ (fun (r : FiveVariables L) (s : Total L) =>
      ∀ x : FiveVariables L, e (r • x) = s • e x) rs (rs.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => e.map_mul r x)
  have hwr : IsWeaklyRegular (Total L) (rs.map e) :=
    (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp (variables_weaklyRegular 5)
  have hm (p : Total L) (hp : p ∈ rs.map e) : p ∈ totalPrime y := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    change reduce (totalEquiv L (aeval (fun j => MvPolynomial.X j - C (z j)) (MvPolynomial.X i))) ∈ rationalIdeal y
    rw [mem_vanishingIdeal_singleton_iff, aeval_X, map_sub]
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [z, reduce, totalEquiv_zero, totalEquiv_succ, totalEquiv_C]
  refine ⟨(rs.map e).map (algebraMap (Total L) (TotalLocal y)), by simp [rs], ?_,
    hwr.isRegular_of_isLocalization_of_mem (TotalLocal y) (totalPrime y) hm⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (TotalLocal y) (totalPrime y) w).mpr (hm w hw)

/-- Reduction identifies the ideal of the special fibre with the total equations plus the parameter. -/
private theorem total_minimal (g : Fin 4 → Total L) (y : Fin 4 → L)
    (hy : rationalIdeal y ∈ (equationsIdeal fun i => reduce (g i)).minimalPrimes) :
    totalPrime y ∈ (equationsIdeal g ⊔ span {C Polynomial.X}).minimalPrimes := by
  have hsurj : Function.Surjective (reduce (L := L)) := by
    apply MvPolynomial.map_surjective
    intro a
    exact ⟨Polynomial.C a, Polynomial.eval_C⟩
  have hmap : (equationsIdeal g).map reduce = equationsIdeal (fun i => reduce (g i)) := by
    rw [equationsIdeal, Ideal.map_span, ← Set.range_comp']
    rfl
  have hker : RingHom.ker (reduce (L := L)) = span {C Polynomial.X} := by
    rw [reduce, MvPolynomial.ker_map, Polynomial.ker_evalRingHom, Polynomial.C_0, sub_zero,
      Ideal.map_span, Set.image_singleton]
  have h := Ideal.minimalPrimes_comap_of_surjective hsurj (hmap ▸ hy)
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, hker] at h

theorem proof : K1_13_5_4_2_4_1.c2 := by
  classical
  intro L _ _ g y hy
  let R := TotalLocal y
  let a := algebraMap (Total L) R
  let _ : Algebra L R := (a.comp (algebraMap L (Total L))).toAlgebra
  let front := List.ofFn fun i => a (g i)
  let t := a (C Polynomial.X)
  have hfront : Ideal.ofList front = (equationsIdeal g).map a := by
    rw [equationsIdeal, Ideal.map_span, ← Set.range_comp']
    exact congrArg span (Set.ext (List.mem_ofFn' (fun i => a (g i))))
  have hrad : (Ideal.ofList (front ++ [t])).radical = maximalIdeal R := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton, hfront, show span {t} =
      (span {C Polynomial.X}).map a by rw [Ideal.map_span, Set.image_singleton]]
    rw [← Ideal.map_sup, IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      R (totalPrime y) _ (total_minimal g y hy), IsLocalization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨rs, hlen, hmem, hreg⟩ := reference_sequence y
  have hparams := K1_13_7_5_3_3_1.weaklyRegular_of_parameters (k := L) rs (front ++ [t])
    (by simpa [front] using hlen) hmem hreg hrad
  have hlast := ((isWeaklyRegular_append_iff R front [t]).mp hparams).2
  have hc := (isWeaklyRegular_singleton_iff _ _).mp hlast
  rw [Ideal.smul_eq_mul, Ideal.mul_top, hfront] at hc
  exact hc

end

end K1_13_5_4_2_4_1_2
end PackSource_K1_13_5_4_2_4_1_2Proof

section PackSource_K1_13_4_3_3Coefficients
set_option autoImplicit true
namespace K1_13_4_3_3

noncomputable section

open Polynomial K1 K1_13 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

set_option maxRecDepth 12000

/-- Substitute the raw jets along a line of polynomial paths. -/
def line (Q : Row 3) (T U : Geom[X]) : Polynomial Geom[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q

private def Bounded (F : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 49196 * j

private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega

private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]

private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf

private theorem line_degree (Q : Row 3) (T U : Geom[X]) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 180267)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 49196 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial Geom[X] :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 49196 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 180267 - i.val ≤ (131071 - i.val) + 49196
      omega
    change ((F i).coeff k).natDegree ≤ b i + 49196 * k
    rw [show F i = _ from rfl, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using ht
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm := bounded_mul (bounded_C (Q.coeff a) le_rfl)
    (bounded_prod a.support (fun i => F i ^ a i) (fun i => b i * a i)
      (fun i _ => bounded_pow (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)

private theorem eval_line (Q : Row 3) (T U : Geom[X]) (c : Geom) :
    (line Q T U).eval (Polynomial.C c) = atJet Q (T + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id Geom[X] := RingHom.ext fun p => by simp
  rw [hC]
  change MvPolynomial.eval _ Q = MvPolynomial.eval (jet (T + c • U)) Q
  have heq : (fun i : Fin 3 => (evalRingHom (C c))
      (Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (T + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]

private theorem swapped_coeff (F : Polynomial Geom[X]) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

/-- Taylor coefficients below the contact order vanish as parameter polynomials. -/
private theorem coeff_contact (F : Polynomial Geom[X]) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ F.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ F.coeff j := by
  let f : Geom[X] →+* Geom[X] := (taylorAlgHom x).toRingHom
  let A := F.map f
  have heval (c : Geom) : A.eval (C c) = taylor x (F.eval (C c)) := by
    change (F.map f).eval (C c) = f (F.eval (C c))
    have hC : f (C c) = C c := taylor_C _ _
    rw [← hC, eval_map, eval₂_at_apply]
    rw [hC]
  have hzero (i : ℕ) (hi : i < r) : (Bivariate.swap A).coeff i = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hz (c : Geom) : ((Bivariate.swap A).coeff i).eval c = 0 := by
      have hs : (Bivariate.swap A).map (evalRingHom c) = A.eval (C c) := by
        simpa [Polynomial.aeval_def] using (Bivariate.aveal_eq_map_swap c A).symm
      change evalRingHom c ((Bivariate.swap A).coeff i) = 0
      rw [← Polynomial.coeff_map, hs, heval]
      exact X_pow_dvd_iff.mp ((X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set Geom).Infinite)
  apply (X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (F.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]

/-- Each surviving parameter coefficient must vanish by contact at the selected hits. -/
theorem line_coeff_zero (w : I → K) (H res T : Geom[X]) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 180265)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 49196 * j < r * 180265) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 180267 :=
    natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  have hc (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ r ∣ (line Q T U).eval (C c) := by
    rw [eval_line]
    apply hcontact i
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    have ht : (T + c • U).eval (x i) = T.eval (x i) := by simp [eval_smul, hU0]
    change (H * (T + c • U) + res).eval (x i) = _
    rw [eval_add, eval_mul, ht, ← eval_mul, ← eval_add]
    exact hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply K1_11.eq_zero_of_many_contacts A x hx r
  · exact fun i hi => coeff_contact _ _ _ (hc i hi) j
  · rw [hA]
    exact (line_degree Q T U t hQ hT hU j).trans_lt hj

end
end K1_13_4_3_3
end PackSource_K1_13_4_3_3Coefficients

section PackSource_K1_13_4_3_3Proof
set_option autoImplicit true
namespace K1_13_4_3_3

noncomputable section

open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator
open scoped BigOperators

set_option maxRecDepth 12000

/-- Multiplication by the locator is invertible in the local three-jet ring
away from its roots. Reduce the inverse times the target to degree at most two. -/
private theorem exists_direction (L : Geom[X]) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 3 → Geom) :
    ∃ V : Geom[X], V.natDegree ≤ 2 ∧ ∀ i : Fin 3, (jet (L * V) i).eval x = v i := by
  classical
  let B := (Polynomial.X - C x) ^ 3
  have hB : B.Monic := (monic_X_sub_C x).pow _
  have hdeg : B.natDegree = 3 := by simp [B, natDegree_pow]
  have hcop : IsCoprime L B := by
    apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
    simpa [dvd_iff_isRoot, IsRoot] using hx
  obtain ⟨a, b, hab⟩ := hcop
  let F := taylor (-x) (ofFn 3 v)
  let V := (a * F) %ₘ B
  have hdiv : B ∣ L * V - F := by
    refine ⟨-(b * F + L * ((a * F) /ₘ B)), ?_⟩
    dsimp only [V]
    rw [modByMonic_eq_sub_mul_div]
    linear_combination F * hab
  have hjet := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L * V - F) x 3).mp hdiv
  refine ⟨V, ?_, fun i => ?_⟩
  · have hne : B ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hdeg
      omega
    have hsmall := natDegree_modByMonic_lt (a * F) hB hne
    rw [hdeg] at hsmall
    exact Nat.le_of_lt_succ hsmall
  · have h := hjet i.val i.isLt
    rw [map_sub, eval_sub, sub_eq_zero] at h
    change (hasseDeriv i.val (L * V)).eval x = v i
    rw [h, ← taylor_coeff, show F = taylor (-x) (ofFn 3 v) from rfl, taylor_taylor,
      add_neg_cancel, taylor_zero, ofFn_coeff_eq_val_of_lt v i.isLt]

/-- Along a scalar line through the origin, the coefficient at degree j
is the degree-j homogeneous component evaluated at the direction. -/
private theorem coeff_line_through_zero (P : MvPolynomial (Fin 3) Geom) (v : Fin 3 → Geom) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) := by
  classical
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  change _ = MvPolynomial.eval₂Hom (RingHom.id _) v _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow Polynomial.C,
    ← map_prod Polynomial.C, ← map_mul Polynomial.C, ← mul_assoc, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all

private theorem line_at_abscissa (P : Row 3) (S U : Geom[X]) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 3 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (MvPolynomial.map (evalRingHom x) (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 3) : Geom[X] := Polynomial.C (f (jet U i)) * Polynomial.X
  change (mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 3 => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
    MvPolynomial.eval₂Hom Polynomial.C g
      (MvPolynomial.map f (MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂Hom_map_hom]
  change _ = MvPolynomial.eval₂Hom (Polynomial.C.comp f) g
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl : (mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := RingHom.ext fun p => by simp
  have hr : (MvPolynomial.eval₂Hom (Polynomial.C.comp f) g).comp MvPolynomial.C =
      Polynomial.C.comp f := RingHom.ext fun p => by simp
  rw [hl, hr]
  congr 1
  funext i
  simp [g, add_comm]

private theorem order_of_locator_lines (P : Row 3) (S L : Geom[X]) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : Geom[X]), V.natDegree ≤ 2 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  change d ≤ m.degree
  by_contra! hlt
  have hz (x : Geom) (hx : L.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := MvPolynomial.map (evalRingHom x) (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V, hV, hv⟩ := exists_direction L x hx v
      have heval := congrArg (evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin 3 → Geom) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : MvPolynomial (Fin 3) Geom => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero

private theorem translate_map (Q : Row 3) (T : Geom[X]) :
    K1_13_4.translate (trajectory T) (MvPolynomial.map inclX Q) =
      MvPolynomial.map inclX (shiftJet Q T) := by
  let left := (K1_13_4.translate (trajectory T)).comp (MvPolynomial.map inclX)
  let right := (MvPolynomial.map inclX).comp (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin 3 => MvPolynomial.X i + MvPolynomial.C (jet T i)))
  have h : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, K1_13_4.translate]
    · intro i
      simp [left, right, K1_13_4.translate, trajectory]
  exact DFunLike.congr_fun h Q

theorem proof : K1_13_4_3.c3 := by
  intro w H res T t k Q hT hhits hc hQ hcut
  obtain ⟨B, hB, hhits⟩ := hhits
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
  let x (i : I) := embed (node i)
  have ho : OrderAt Q T (k + 1) := by
    apply order_of_locator_lines Q T (locator x A) (locator_monic x A).ne_zero
    intro V hV j hj
    exact line_coeff_zero w H res T t 5000 Q hT hQ hc A hA
      (fun i hi => hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [translate_map]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)

end
end K1_13_4_3_3
end PackSource_K1_13_4_3_3Proof

section PackSource_K1_13_4_2_2_2AuxCount
set_option autoImplicit true
namespace K1_13_4_2_2_2

noncomputable section

open K1_13 K1_13_4_2_2 MvPolynomial

abbrev degreeWeight : Fin 3 → ℕ := fun _ => 1
abbrev ordinaryWeight : Fin 3 → ℕ := ![1, 0, 1]
abbrev tangentWeight : Fin 3 → ℕ := ![2, 0, 1]

theorem degree_weight (e : PlaneExp) : e.weight degreeWeight = e 0 + e 1 + e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, add_assoc]

theorem ordinary_weight (e : PlaneExp) : e.weight ordinaryWeight = e 0 + e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul]

theorem tangent_weight (e : PlaneExp) : e.weight tangentWeight = 2 * e 0 + e 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, Nat.mul_comm]

abbrev DegreeExponents (d : ℕ) := ↥{e : PlaneExp | e.weight degreeWeight = d}
abbrev DegreeSpace (d : ℕ) := restrictSupport Geom {e : PlaneExp | e.weight degreeWeight = d}
abbrev BadExponents (d : ℕ) (F : Flag) :=
  {e : DegreeExponents d //
    (e.val.weight ordinaryWeight : ℤ) < F.ordinary ∨
    (e.val.weight tangentWeight : ℤ) < F.weighted}

/-- Pairs of total degree less than `n`, indexed by total degree and one exponent. -/
private abbrev Triangle (n : ℕ) := Σ s : Fin n, Fin (s.val + 1)

private theorem triangle_card (n : ℕ) : (Fintype.card (Triangle n) : ℤ) = triangular n := by
  have hs : (∑ s : Fin n, (s.val + 1)) = (n + 1).choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) n]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [Nat.choose_succ_succ, Nat.choose_one_right]
      omega
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, hs, Nat.choose_two_right, Nat.add_sub_cancel,
    Int.natCast_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one, triangular, mul_comm]
  rfl

private def degreeEquiv (d : ℕ) : DegreeExponents d ≃ Triangle (d + 1) where
  toFun e := ⟨⟨e.val 0 + e.val 2, by
    have h := e.property
    simp only [Set.mem_ofPred_eq, degree_weight] at h
    omega⟩, ⟨e.val 0, by
      change e.val 0 < e.val 0 + e.val 2 + 1
      omega⟩⟩
  invFun s := ⟨Finsupp.equivFunOnFinite.symm ![s.2.val, d - s.1.val, s.1.val - s.2.val], by
    have h := s.1.isLt
    have h' := s.2.isLt
    simp only [Set.mem_ofPred_eq, degree_weight]
    change s.2.val + (d - s.1.val) + (s.1.val - s.2.val) = d
    omega⟩
  left_inv e := by
    have h := e.property
    simp only [Set.mem_ofPred_eq, degree_weight] at h
    apply Subtype.ext
    ext i : 1
    fin_cases i
    · rfl
    · change d - (e.val 0 + e.val 2) = e.val 1
      omega
    · change e.val 0 + e.val 2 - e.val 0 = e.val 2
      omega
  right_inv s := by
    have h := s.2.isLt
    have ht : s.2.val + (s.1.val - s.2.val) = s.1.val := by omega
    exact Sigma.ext (Fin.ext ht) ((Fin.heq_ext_iff (congrArg (· + 1) ht)).mpr rfl)

noncomputable instance degreeExponentsFintype (d : ℕ) :
    Fintype (DegreeExponents d) :=
  Fintype.ofEquiv (Triangle (d + 1)) (degreeEquiv d).symm

noncomputable instance badExponentsFintype (d : ℕ) (F : Flag) : Fintype (BadExponents d F) :=
  @Fintype.ofFinite _ (Finite.of_injective Subtype.val Subtype.val_injective)

instance degreeSpaceFinite (d : ℕ) : Module.Finite Geom (DegreeSpace d) :=
  Module.Finite.of_basis (basisRestrictSupport Geom {e : PlaneExp | e.weight degreeWeight = d})

theorem degreeSpace_finrank (d : ℕ) :
    (Module.finrank Geom (DegreeSpace d) : ℤ) = triangular ((d : ℤ) + 1) := by
  rw [Module.finrank_eq_card_basis (basisRestrictSupport Geom
    {e : PlaneExp | e.weight degreeWeight = d})]
  change (Fintype.card (DegreeExponents d) : ℤ) = _
  rw [Fintype.card_congr (degreeEquiv d)]
  simpa using triangle_card (d + 1)

private def ordinaryCut (F : Flag) : ℤ := max 0 (max F.ordinary ((F.weighted + 1) / 2))
private def tangentCut (F : Flag) : ℤ := max (ordinaryCut F) F.weighted

/-- Above ordinary order `u`, translate the pair `(s, b)` to `(s-u, b)`,
where `s` is the ordinary order and `b` is the doubled coordinate exponent. -/
private def badToTriangles (d : ℕ) (F : Flag) (e : BadExponents d F) :
    Triangle (ordinaryCut F).toNat ⊕ Triangle (tangentCut F - ordinaryCut F).toNat :=
  if h : (e.val.val 0 + e.val.val 2 : ℕ) < (ordinaryCut F).toNat then
    .inl ⟨⟨e.val.val 0 + e.val.val 2, h⟩, ⟨e.val.val 0, by
      change e.val.val 0 < e.val.val 0 + e.val.val 2 + 1
      omega⟩⟩
  else
    .inr ⟨⟨e.val.val 0 + e.val.val 2 - (ordinaryCut F).toNat + e.val.val 0, by
      have hu : 0 ≤ ordinaryCut F := le_max_left _ _
      have ho : F.ordinary ≤ ordinaryCut F := (le_max_left _ _).trans (le_max_right _ _)
      have hw : F.weighted ≤ tangentCut F := le_max_right _ _
      have he := e.property
      rw [ordinary_weight, tangent_weight] at he
      omega⟩, ⟨e.val.val 0, by
        change e.val.val 0 <
          e.val.val 0 + e.val.val 2 - (ordinaryCut F).toNat + e.val.val 0 + 1
        omega⟩⟩

private theorem badToTriangles_injective (d : ℕ) (F : Flag) :
    Function.Injective (badToTriangles d F) := by
  intro e f h
  have hd := e.val.property
  have hd' := f.val.property
  simp only [Set.mem_ofPred_eq, degree_weight] at hd hd'
  let coords : Triangle (ordinaryCut F).toNat ⊕ Triangle (tangentCut F - ordinaryCut F).toNat →
      ℕ × ℕ := Sum.elim (fun s => (s.1.val, s.2.val))
        (fun s => (s.1.val - s.2.val + (ordinaryCut F).toNat, s.2.val))
  have project (a : BadExponents d F) :
      coords (badToTriangles d F a) = (a.val.val 0 + a.val.val 2, a.val.val 0) := by
    unfold badToTriangles
    split
    · rfl
    · change (a.val.val 0 + a.val.val 2 - (ordinaryCut F).toNat + a.val.val 0 -
        a.val.val 0 + (ordinaryCut F).toNat, a.val.val 0) = _
      rw [Nat.add_sub_cancel, Nat.sub_add_cancel (by omega)]
  have hc := congrArg coords h
  rw [project, project] at hc
  obtain ⟨ht, hb⟩ := Prod.mk.inj hc
  apply Subtype.ext
  apply Subtype.ext
  ext i : 1
  fin_cases i
  · exact hb
  · change e.val.val 1 = f.val.val 1
    omega
  · change e.val.val 2 = f.val.val 2
    omega

theorem bad_card_le (d : ℕ) (F : Flag) : (Fintype.card (BadExponents d F) : ℤ) ≤ colength F := by
  have h := Fintype.card_le_of_injective _ (badToTriangles_injective d F)
  have hu : 0 ≤ ordinaryCut F := le_max_left _ _
  have hv : ordinaryCut F ≤ tangentCut F := le_max_left _ _
  have hz : 0 ≤ tangentCut F - ordinaryCut F := sub_nonneg.mpr hv
  have hcast : (Fintype.card (BadExponents d F) : ℤ) ≤
      (Fintype.card (Triangle (ordinaryCut F).toNat ⊕
        Triangle (tangentCut F - ordinaryCut F).toNat) : ℤ) := by exact_mod_cast h
  rwa [Fintype.card_sum, Nat.cast_add, triangle_card, triangle_card, Int.toNat_of_nonneg hu,
    Int.toNat_of_nonneg hz] at hcast

end

end K1_13_4_2_2_2
end PackSource_K1_13_4_2_2_2AuxCount

section PackSource_K1_13_4_2_2_2AuxFlags
set_option autoImplicit true
namespace K1_13_4_2_2_2

noncomputable section

open K1_13 K1_13_4_2_2 MvPolynomial

local notation "V" => (MvPolynomial.X : Fin 3 → Plane)

/-- In each chart, variable 1 homogenizes and variable 0 has double weight. -/
def chartImage : Fin 3 → Fin 3 → Plane :=
  ![![V 1, V 2, V 0], ![V 0, V 2, V 1], planeImage]

def chart (i : Fin 3) : Plane →ₐ[Geom] Plane := bind₁ (chartImage i)

theorem var_homogeneous (j : Fin 3) : (V j).IsWeightedHomogeneous degreeWeight 1 :=
  isWeightedHomogeneous_X Geom degreeWeight j

private theorem chart_homogeneous (i : Fin 3) {d : ℕ} {f : Plane}
    (hf : f.IsWeightedHomogeneous degreeWeight d) :
    (chart i f).IsWeightedHomogeneous degreeWeight d := by
  apply hf.bind₁
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [chartImage, planeImage, var_homogeneous]
  exact ((var_homogeneous 0).add (var_homogeneous 1)).sub (var_homogeneous 2)

def Meets (F : Fin 3 → Flag) (f : Plane) : Prop :=
  ∀ i : Fin 3,
    chart i f ∈ restrictWeightedOrder ordinaryWeight (F i).ordinary.toNat ∧
    chart i f ∈ restrictWeightedOrder tangentWeight (F i).weighted.toNat

private abbrev Forbidden (d : ℕ) (F : Fin 3 → Flag) := Σ i : Fin 3, BadExponents d (F i)

/-- Extract every forbidden coefficient in its respective homogeneous chart. -/
def flagMap (d : ℕ) (F : Fin 3 → Flag) : DegreeSpace d →ₗ[Geom] (Forbidden d F → Geom) :=
  LinearMap.pi fun t =>
    ((lcoeff Geom t.2.val.val).comp (chart t.1).toLinearMap).domRestrict (DegreeSpace d)

theorem degree_homogeneous {d : ℕ} (f : DegreeSpace d) :
    (f : Plane).IsWeightedHomogeneous degreeWeight d := by
  intro e he
  exact (mem_restrictSupport_iff Geom).mp f.property (mem_support_iff.mpr he)

theorem meets_of_ker {d : ℕ} {F : Fin 3 → Flag} (f : LinearMap.ker (flagMap d F)) :
    Meets F (f.val : Plane) := by
  intro i
  have ok (e : PlaneExp) (he : e ∈ (chart i (f.val : Plane)).support) :
      ¬ ((e.weight ordinaryWeight : ℤ) < (F i).ordinary ∨
        (e.weight tangentWeight : ℤ) < (F i).weighted) := by
    intro hbad
    have hne := mem_support_iff.mp he
    have hd := chart_homogeneous i (degree_homogeneous f.val) hne
    exact hne (congrFun (LinearMap.mem_ker.mp f.property) ⟨i, ⟨⟨e, hd⟩, hbad⟩⟩)
  constructor
  · apply mem_restrictWeightedOrder.mpr
    intro e he
    have h := not_or.mp (ok e he)
    omega
  · apply mem_restrictWeightedOrder.mpr
    intro e he
    have h := not_or.mp (ok e he)
    omega

theorem flag_kernel_bound (d : ℕ) (F : Fin 3 → Flag) :
    triangular ((d : ℤ) + 1) - ∑ i, colength (F i) ≤
      (Module.finrank Geom (LinearMap.ker (flagMap d F)) : ℤ) := by
  let L := flagMap d F
  have hd := L.finrank_range_add_finrank_ker
  have hr : (Module.finrank Geom (LinearMap.range L) : ℤ) ≤
      Fintype.card (Forbidden d F) := by
    have h := Submodule.finrank_le (LinearMap.range L)
    rw [Module.finrank_pi] at h
    exact_mod_cast h
  have hc : (Fintype.card (Forbidden d F) : ℤ) ≤ ∑ i, colength (F i) := by
    rw [Fintype.card_sigma, Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => bad_card_le d (F i)
  rw [← degreeSpace_finrank d]
  change _ ≤ (Module.finrank Geom (LinearMap.ker L) : ℤ)
  omega

private def inverseP : Fin 3 → Plane := ![V 2, V 0, V 1]

private theorem undo_P (f : Plane) : bind₁ inverseP (chart 0 f) = f := by
  rw [chart, bind₁_bind₁]
  have him : (fun i => bind₁ inverseP (chartImage 0 i)) = V := by
    funext i
    fin_cases i <;> simp [inverseP, chartImage]
  rw [him, bind₁_X_left]
  rfl

private theorem undo_Q (f : Plane) : chart 1 (chart 1 f) = f := by
  simp only [chart, bind₁_bind₁]
  have him : (fun i => bind₁ (chartImage 1) (chartImage 1 i)) = V := by
    funext i
    fin_cases i <;> simp [chartImage]
  rw [him, bind₁_X_left]
  rfl

private abbrev qOrdinary : Fin 3 → ℕ := ![1, 1, 0]
private abbrev qTangent : Fin 3 → ℕ := ![2, 1, 0]

theorem original_kernel {q : ℕ} {g : ℤ} {f : Plane}
    (hd : f.IsWeightedHomogeneous degreeWeight (residualDegree q))
    (hf : Meets (initialFlag q g) f) :
    ∃ hsrc : f ∈ PlaneSource q g, (⟨f, hsrc⟩ : PlaneSource q g) ∈
      LinearMap.ker (planeContact q g) := by
  have hP : f ∈ restrictWeightedOrder Fin.val (-g).toNat := by
    rw [← undo_P f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 0).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQo : f ∈ restrictWeightedOrder qOrdinary ((residualDegree q : ℤ) - 1150).toNat := by
    rw [← undo_Q f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).1
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQw : f ∈ restrictWeightedOrder qTangent (2 * (residualDegree q : ℤ) - 2300).toNat := by
    rw [← undo_Q f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hsrc : f ∈ PlaneSource q g := by
    apply (mem_restrictSupport_iff Geom).mpr
    intro e he
    have hdeg := hd (mem_support_iff.mp he)
    have hn := mem_restrictWeightedOrder.mp hP e he
    have ho := mem_restrictWeightedOrder.mp hQo e he
    have hw := mem_restrictWeightedOrder.mp hQw e he
    change e.weight degreeWeight = residualDegree q ∧ -g ≤ (e.weight Fin.val : ℤ) ∧
      e.weight Fin.val ≤ 2300 ∧ e 2 ≤ 1150
    rw [degree_weight] at hdeg
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, smul_eq_mul, Nat.mul_comm] at hn ho hw ⊢
    omega
  refine ⟨hsrc, LinearMap.mem_ker.mpr ?_⟩
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  exact (hf 2).2

end

end K1_13_4_2_2_2
end PackSource_K1_13_4_2_2_2AuxFlags

section PackSource_K1_13_4_2_2_2Proof
set_option autoImplicit true
namespace K1_13_4_2_2_2

noncomputable section

open K1_13 K1_13_4_2_2 MvPolynomial
open scoped BigOperators

local notation "V" => (MvPolynomial.X : Fin 3 → Plane)

private def factor : Fin 6 → Plane :=
  let x := V 0 - V 1
  let y := V 1
  let z := V 2
  ![z, y, x, x + y, x + z, x * y + x * z + y * z]

private def product (p : Powers) : Plane := ∏ j, factor j ^ p j

private theorem factor_ne_zero (j : Fin 6) : factor j ≠ 0 := by
  let point : Fin 6 → Fin 3 → Geom :=
    ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![1, 0, 0], ![1, 0, 0], ![1, 1, 1]]
  intro h
  have he := congrArg (fun f : Plane => eval (point j) f) h
  fin_cases j <;> simp [point, factor] at he

private theorem factor_homogeneous (j : Fin 6) :
    (factor j).IsWeightedHomogeneous degreeWeight (factorDegree j).toNat := by
  have hx := (var_homogeneous 0).sub (var_homogeneous 1)
  have hy := var_homogeneous 1
  have hz := var_homogeneous 2
  fin_cases j
  · exact hz
  · exact hy
  · exact hx
  · exact hx.add hy
  · exact hx.add hz
  · exact ((hx.mul hy).add (hx.mul hz)).add (hy.mul hz)

private def chartFactor (i : Fin 3) (j : Fin 6) : Plane :=
  let a := V 0
  let b := V 1
  let c := V 2
  (![![a, c, b - c, b, b - c + a, b * c - c * c + b * a],
    ![b, c, a - c, a, a - c + b, a * c - c * c + a * b],
    ![c, b, a - c, a - c + b, a, a * b - c * c + a * c]] : Fin 3 → Fin 6 → Plane) i j

private theorem chart_factor (i : Fin 3) (j : Fin 6) :
    chart i (factor j) = chartFactor i j := by
  fin_cases i <;> fin_cases j <;> simp [chart, chartImage, planeImage, factor, chartFactor] <;> ring

private def HasOrders (f : Plane) (a b : ℕ) : Prop :=
  f ∈ restrictWeightedOrder ordinaryWeight a ∧ f ∈ restrictWeightedOrder tangentWeight b

private theorem orders_zero (f : Plane) : HasOrders f 0 0 := by simp [HasOrders]

private theorem orders_var (i : Fin 3) (a b : ℕ) (ha : a ≤ ordinaryWeight i)
    (hb : b ≤ tangentWeight i) : HasOrders (V i) a b :=
  ⟨X_mem_restrictWeightedOrder _ i ha, X_mem_restrictWeightedOrder _ i hb⟩

private theorem orders_pair (i j : Fin 3) (a b : ℕ) (ha : a ≤ ordinaryWeight i + ordinaryWeight j)
    (hb : b ≤ tangentWeight i + tangentWeight j) : HasOrders (V i * V j) a b :=
  ⟨restrictWeightedOrder_anti _ ha
      (mul_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ i le_rfl)
        (X_mem_restrictWeightedOrder _ j le_rfl)),
    restrictWeightedOrder_anti _ hb
      (mul_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ i le_rfl)
        (X_mem_restrictWeightedOrder _ j le_rfl))⟩

private theorem orders_sub {f g : Plane} {a b : ℕ}
    (hf : HasOrders f a b) (hg : HasOrders g a b) : HasOrders (f - g) a b :=
  ⟨Submodule.sub_mem _ hf.1 hg.1, Submodule.sub_mem _ hf.2 hg.2⟩

private theorem orders_sub_add {f g h : Plane} {a b : ℕ}
    (hf : HasOrders f a b) (hg : HasOrders g a b) (hh : HasOrders h a b) :
    HasOrders (f - g + h) a b :=
  ⟨Submodule.add_mem _ (orders_sub hf hg).1 hh.1,
    Submodule.add_mem _ (orders_sub hf hg).2 hh.2⟩

private theorem factor_orders (j : Fin 6) (i : Fin 3) :
    chart i (factor j) ∈ restrictWeightedOrder ordinaryWeight (factorFlag j i).ordinary.toNat ∧
    chart i (factor j) ∈ restrictWeightedOrder tangentWeight (factorFlag j i).weighted.toNat := by
  rw [chart_factor]
  change HasOrders (chartFactor i j) (factorFlag j i).ordinary.toNat (factorFlag j i).weighted.toNat
  have a₁₁ := orders_var 0 1 1 (by decide) (by decide)
  have a₁₂ := orders_var 0 1 2 (by decide) (by decide)
  have c₁₁ := orders_var 2 1 1 (by decide) (by decide)
  have ac := orders_pair 0 2 1 2 (by decide) (by decide)
  have ab := orders_pair 0 1 1 2 (by decide) (by decide)
  have cc := orders_pair 2 2 1 2 (by decide) (by decide)
  fin_cases i <;> fin_cases j
  · exact a₁₂
  · exact c₁₁
  · exact orders_zero _
  · exact orders_zero _
  · exact orders_zero _
  · exact orders_sub_add (orders_pair 1 2 1 1 (by decide) (by decide))
      (orders_pair 2 2 1 1 (by decide) (by decide)) (orders_pair 1 0 1 1 (by decide) (by decide))
  · exact orders_zero _
  · exact c₁₁
  · exact orders_sub a₁₁ c₁₁
  · exact a₁₂
  · exact orders_zero _
  · exact orders_sub_add ac cc ab
  · exact c₁₁
  · exact orders_zero _
  · exact orders_sub a₁₁ c₁₁
  · exact orders_zero _
  · exact a₁₂
  · exact orders_sub_add ab cc ac

private theorem cast_power_sum (p : Powers) (v : Fin 6 → ℤ) (hv : ∀ j, 0 ≤ v j) :
    ((∑ j, p j * (v j).toNat : ℕ) : ℤ) = ∑ j, (p j : ℤ) * v j := by
  simp [Nat.cast_sum, hv]

private theorem product_lift_degree (q : ℕ) (p : Powers) {f : Plane}
    (hn : 0 ≤ remainingDegree q p)
    (hf : f.IsWeightedHomogeneous degreeWeight (remainingDegree q p).toNat) :
    (product p * f).IsWeightedHomogeneous degreeWeight (residualDegree q) := by
  have hp : (product p).IsWeightedHomogeneous degreeWeight (∑ j, p j * (factorDegree j).toNat) := by
    apply IsWeightedHomogeneous.prod
    intro j _
    simpa only [Nat.nsmul_eq_mul] using (factor_homogeneous j).pow (p j)
  have hc := cast_power_sum p factorDegree (by intro j; unfold factorDegree; split <;> decide)
  have hsum : (∑ j, p j * (factorDegree j).toNat) + (remainingDegree q p).toNat =
      residualDegree q := by
    unfold remainingDegree at hn ⊢
    omega
  rw [← hsum]
  exact hp.mul hf

private theorem lift_order (p : Powers) (i : Fin 3) (w : Fin 3 → ℕ) (a : ℤ) (v : Fin 6 → ℤ)
    (hv : ∀ j, 0 ≤ v j)
    (hfactor : ∀ j, chart i (factor j) ∈ restrictWeightedOrder w (v j).toNat)
    {f : Plane}
    (hf : chart i f ∈ restrictWeightedOrder w (a - ∑ j, (p j : ℤ) * v j).toNat) :
    chart i (product p * f) ∈ restrictWeightedOrder w a.toNat := by
  have hp : chart i (product p) ∈ restrictWeightedOrder w (∑ j, p j * (v j).toNat) := by
    simp only [product, map_prod, map_pow]
    exact prod_mem_restrictWeightedOrder _ fun j _ => pow_mem_restrictWeightedOrder (hfactor j) (p j)
  rw [map_mul]
  refine restrictWeightedOrder_anti w ?_ (mul_mem_restrictWeightedOrder hp hf)
  have hc := cast_power_sum p v hv
  omega

private theorem product_lift_flags (q : ℕ) (g : ℤ) (p : Powers) {f : Plane}
    (hf : Meets (remainingFlag q g p) f) : Meets (initialFlag q g) (product p * f) := by
  intro i
  exact ⟨lift_order p i ordinaryWeight (initialFlag q g i).ordinary
      (fun j => (factorFlag j i).ordinary)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j => (factor_orders j i).1) (hf i).1,
    lift_order p i tangentWeight (initialFlag q g i).weighted
      (fun j => (factorFlag j i).weighted)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j => (factor_orders j i).2) (hf i).2⟩

private theorem lift_finrank (q : ℕ) (g : ℤ) (p : Powers) (hn : 0 ≤ remainingDegree q p) :
    Module.finrank Geom (LinearMap.ker (flagMap (remainingDegree q p).toNat (remainingFlag q g p))) ≤
      Module.finrank Geom (LinearMap.ker (planeContact q g)) := by
  let S := LinearMap.ker (flagMap (remainingDegree q p).toNat (remainingFlag q g p))
  have h (f : S) := original_kernel (q := q) (g := g)
    (product_lift_degree q p hn (degree_homogeneous f.val))
    (product_lift_flags q g p (meets_of_ker f))
  let L : S →ₗ[Geom] Plane :=
    (LinearMap.mulLeft Geom (product p)).comp
      (((DegreeSpace (remainingDegree q p).toNat).subtype).comp S.subtype)
  let M := L.codRestrict (PlaneSource q g) (fun f => (h f).choose)
  let N := M.codRestrict (LinearMap.ker (planeContact q g)) (fun f => (h f).choose_spec)
  apply LinearMap.finrank_le_finrank_of_injective (f := N)
  intro f f' hff'
  apply Subtype.ext
  apply Subtype.ext
  have hp : product p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (factor_ne_zero j)
  exact mul_left_cancel₀ hp (congrArg (fun a => (a.val : Plane)) hff')

theorem proof : K1_13_4_2_2.c2 := by
  intro q _ k _ p
  let d := remainingDegree q p
  by_cases hn : remainingDegree q p < 0
  · simp [kernelLower, hn]
  have hnonneg : 0 ≤ d := le_of_not_gt hn
  have hres := flag_kernel_bound d.toNat (remainingFlag q (offset k) p)
  rw [Int.toNat_of_nonneg hnonneg] at hres
  have hl := lift_finrank q (offset k) p hnonneg
  simp only [kernelLower, hn, ite_false]
  exact hres.trans (by exact_mod_cast hl)

end

end K1_13_4_2_2_2
end PackSource_K1_13_4_2_2_2Proof

section PackSource_K1_13_7_5_3_3_3_2Model
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_5_3_3_3_2

noncomputable section

open K1_13_5_4_2_4 K1_13_5_4_2_4_2 K1_13_7_5_3_3_3 MvPolynomial
open scoped Pointwise

variable {A : Fin 4 → Finset Exponent}

abbrev Ambient (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (Row A)

abbrev stamp (d : Degree) : Exponent := Finsupp.equivFunOnFinite.symm d

theorem stamp_shift (d : Degree) (i : Fin 4) :
    stamp (shift d i 1) = stamp d + Finsupp.single i 1 := by
  ext j
  simp [shift, Finsupp.add_apply, Finsupp.single_eq_pi_single]

theorem exponentSet_add (d e : Degree) :
    exponentSet A (d + e) = exponentSet A d + exponentSet A e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]

theorem exponentSet_single (i : Fin 4) : exponentSet A (Pi.single i 1) = A i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp

private theorem mono_piece {d : Degree} {e : Exponent} (he : e ∈ exponentSet A d)
    (c : CoefficientField A) : monomial e c ∈ piece A d := by
  have h : monomial e (1 : CoefficientField A) ∈ piece A d :=
    Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (piece A d).smul_mem c h

private theorem mul_piece {d e : Degree} {p q : Row A}
    (hp : p ∈ piece A d) (hq : q ∈ piece A e) : p * q ∈ piece A (d + e) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨b, rfl⟩ := hq
      rw [monomial_mul_monomial]
      apply mono_piece
      rw [exponentSet_add]
      exact Set.mem_add.mpr ⟨a, a.2, b, b.2, rfl⟩
    | zero => simp
    | add q r _ _ hq hr => simpa only [mul_add] using (piece A _).add_mem hq hr
    | smul c q _ hq => simpa only [mul_smul_comm] using (piece A _).smul_mem c hq
  | zero => simp
  | add p r _ _ hp hr => simpa only [add_mul] using (piece A _).add_mem hp hr
  | smul c p _ hp => simpa only [smul_mul_assoc] using (piece A _).smul_mem c hp

def generator (t : Σ i : Fin 4, ↥(A i)) : Ambient A :=
  monomial (Finsupp.single t.1 1) (monomial t.2.val 1)

/-- The multigraded monomial algebra, with the spatial polynomials as coefficients. -/
def model (A : Fin 4 → Finset Exponent) : Subalgebra (CoefficientField A) (Ambient A) :=
  Algebra.adjoin _ (Set.range (generator (A := A)))

instance modelCommRing : CommRing (model A) :=
  Subalgebra.toCommRing (R := CoefficientField A) (A := Ambient A) (model A)

instance : IsNoetherianRing (model A) := by
  classical
  let : Algebra.FiniteType (CoefficientField A) (model A) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range generator)
  exact Algebra.FiniteType.isNoetherianRing (CoefficientField A) (model A)

def gen (i : Fin 4) (a : ↥(A i)) : model A :=
  ⟨generator ⟨i, a⟩, Algebra.subset_adjoin ⟨⟨i, a⟩, rfl⟩⟩

/-- The product of one monomial variable from each factor. -/
def chart (a : Chart A) : model A := ∏ i, gen i (a i)

private theorem mono_sum {ι : Type*} (s : Finset ι) (d e : ι → Exponent) :
    (monomial (∑ x ∈ s, d x) (monomial (∑ x ∈ s, e x) 1) : Ambient A) =
      ∏ x ∈ s, monomial (d x) (monomial (e x) 1) := by
  rw [monomial_sum_one, monomial_sum_prod]

private theorem sum_single (d : Degree) : (∑ i, Finsupp.single i (d i)) = stamp d := by
  classical
  ext j
  simp [Finset.sum_apply', Finsupp.single_apply]

theorem chart_pow_val (a : Chart A) (m : ℕ) :
    ((chart a ^ m : model A) : Ambient A) = monomial (stamp (fun _ => m)) (chartPower a m) := by
  have h : ((chart a : model A) : Ambient A) =
      monomial (stamp (fun _ => 1)) (monomial (∑ i, (a i).val) 1) := by
    rw [← sum_single, mono_sum]
    exact SubmonoidClass.coe_finsetProd _ _
  rw [Subalgebra.coe_pow, h, monomial_pow, monomial_pow, one_pow, chartPower]
  congr
  ext i
  simp

private theorem factors {d : Degree} {e : Exponent} (he : e ∈ exponentSet A d) :
    ∃ f : ∀ i, Fin (d i) → ↥(A i), ∑ i, ∑ x, (f i x).val = e := by
  classical
  obtain ⟨u, hu, rfl⟩ := (Set.mem_fintype_sum _ _).mp he
  have hf (i : Fin 4) : ∃ f : Fin (d i) → ↥(A i), ∑ x, (f x).val = u i := by
    obtain ⟨v, hv, heq⟩ := Set.mem_nsmul_iff_sum.mp (hu i)
    exact ⟨fun x => ⟨v x, hv x⟩, heq⟩
  choose f hf using hf
  exact ⟨f, Finset.sum_congr rfl fun i _ => hf i⟩

private theorem factors_val {d : Degree} (f : ∀ i, Fin (d i) → ↥(A i)) :
    ((∏ i, ∏ x, gen i (f i x) : model A) : Ambient A) =
      monomial (stamp d) (monomial (∑ i, ∑ x, (f i x).val) 1) := by
  classical
  rw [← sum_single, mono_sum, SubmonoidClass.coe_finsetProd]
  apply Finset.prod_congr rfl
  intro i _
  rw [SubmonoidClass.coe_finsetProd]
  have h : (∑ _ : Fin (d i), Finsupp.single i (1 : ℕ)) = Finsupp.single i (d i) := by
    ext j
    simp [Finsupp.single_apply]
  rw [← h, mono_sum]
  rfl

private theorem monomial_mem_model {d e : Exponent} (he : e ∈ exponentSet A d) :
    monomial d (monomial e 1) ∈ model A := by
  obtain ⟨f, hf⟩ := factors he
  have hp := (∏ i, ∏ x, gen i (f i x)).property
  rw [factors_val, hf] at hp
  simpa only [stamp, Finsupp.equivFunOnFinite_symm_coe] using hp

/-- Homogenize one filtered polynomial in the indicated multidegree. -/
def tag (d : Exponent) {p : Row A} (hp : p ∈ piece A d) : model A := by
  refine ⟨monomial d p, ?_⟩
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨e, rfl⟩ := hp; exact monomial_mem_model e.2
  | zero => rw [map_zero]; exact (model A).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (model A).add_mem hp hq
  | smul c p _ hp => simpa only [smul_monomial] using (model A).smul_mem hp c

private def pieceAlgebra (A : Fin 4 → Finset Exponent) :
    Subalgebra (CoefficientField A) (Ambient A) where
  carrier := {p | ∀ d : Exponent, p.coeff d ∈ piece A d}
  zero_mem' := by simp
  one_mem' := by
    intro d
    by_cases h : d = 0
    · subst d
      simpa [exponentSet] using (mono_piece (A := A) (d := 0) (e := 0) (by simp [exponentSet]) 1)
    · simp [coeff_one, Ne.symm h]
  add_mem' := by
    intro p q hp hq d
    exact (piece A d).add_mem (hp d) (hq d)
  mul_mem' := by
    classical
    intro p q hp hq d
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun e he => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp he
    exact h ▸ mul_piece (hp e.1) (hq e.2)
  algebraMap_mem' := by
    intro c d
    rw [IsScalarTower.algebraMap_eq (CoefficientField A) (Row A) (Ambient A)]
    change (C (C c) : Ambient A).coeff d ∈ piece A d
    by_cases h : d = 0
    · subst d
      rw [coeff_zero_C]
      exact mono_piece (A := A) (d := 0) (e := 0) (by simp [exponentSet]) c
    · simp [coeff_C, Ne.symm h]

theorem coeff_mem (f : model A) (d : Exponent) : (f : Ambient A).coeff d ∈ piece A d := by
  have h : model A ≤ pieceAlgebra A := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨i, a⟩, rfl⟩ d
    by_cases hd : d = Finsupp.single i 1
    · subst d
      simp only [generator, coeff_monomial]
      apply mono_piece
      rw [Finsupp.single_eq_pi_single, exponentSet_single]
      exact Finset.mem_coe.mpr a.2
    · simp [generator, coeff_monomial, Ne.symm hd]
  exact (h f.property : ∀ d : Exponent, (f : Ambient A).coeff d ∈ piece A d) d

/-- Extract the homogeneous component in degree `d`. -/
def proj (d : Exponent) (f : model A) : model A := tag d (coeff_mem f d)

/-- The span of the chosen common powers of all chart products. -/
def chartIdeal (A : Fin 4 → Finset Exponent) (m : ℕ) : Ideal (model A) :=
  Ideal.span (Set.range fun a : Chart A => chart a ^ m)

private theorem factors_dvd (hz : ∀ i, 0 ∈ A i) {d : Degree} {m : ℕ}
    (hd : ∀ i, (A i).card * m ≤ d i) (f : ∀ i, Fin (d i) → ↥(A i)) :
    ∃ a : Chart A, chart a ^ m ∣ ∏ i, ∏ x, gen i (f i x) := by
  classical
  have h (i : Fin 4) : ∃ a : ↥(A i), (gen i a) ^ m ∣ ∏ x, gen i (f i x) := by
    let : Nonempty ↥(A i) := ⟨⟨0, hz i⟩⟩
    obtain ⟨a, _, ha⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (f := f i) (n := m)
      (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by simpa using hd i)
    obtain ⟨s, hs, hsCard⟩ := Finset.exists_subset_card_eq ha
    refine ⟨a, ∏ x ∈ Finset.univ \ s, gen i (f i x), ?_⟩
    have he : (∏ x ∈ s, gen i (f i x)) = gen i a ^ m := by
      calc
        _ = ∏ _x ∈ s, gen i a :=
          Finset.prod_congr rfl fun x hx => congrArg (gen i) (Finset.mem_filter.mp (hs hx)).2
        _ = _ := by rw [Finset.prod_const, hsCard]
    rw [← he, mul_comm, Finset.prod_sdiff (Finset.subset_univ s)]
  choose a ha using h
  refine ⟨a, ?_⟩
  unfold chart
  rw [← Finset.prod_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ha i

theorem tag_mem_chartIdeal (hz : ∀ i, 0 ∈ A i) {d : Exponent} {m : ℕ}
    (hd : ∀ i, (A i).card * m ≤ d i) {p : Row A} (hp : p ∈ piece A d) :
    tag d hp ∈ chartIdeal A m := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨e, rfl⟩ := hp
    obtain ⟨f, hf⟩ := factors e.2
    have he : (∏ i, ∏ x, gen i (f i x)) = tag d (Submodule.subset_span ⟨e, rfl⟩) := by
      apply Subtype.ext
      simp only [factors_val, hf, tag, stamp, Finsupp.equivFunOnFinite_symm_coe]
    obtain ⟨a, q, hq⟩ := factors_dvd hz hd f
    rw [← he, hq, mul_comm]
    exact (chartIdeal A m).mul_mem_left q (Ideal.subset_span ⟨a, rfl⟩)
  | zero =>
    have h : tag d ((piece A d).zero_mem) = 0 := Subtype.ext (map_zero (monomial d))
    rw [h]
    exact (chartIdeal A m).zero_mem
  | add p q hp hq ihp ihq =>
    have h : tag d ((piece A d).add_mem hp hq) = tag d hp + tag d hq :=
      Subtype.ext (map_add (monomial d) p q)
    rw [h]
    exact (chartIdeal A m).add_mem ihp ihq
  | smul c p hp ih =>
    have h : tag d ((piece A d).smul_mem c hp) = algebraMap _ (model A) c * tag d hp := by
      apply Subtype.ext
      change monomial d (c • p) = (algebraMap (CoefficientField A) (Ambient A) c) * monomial d p
      rw [← Algebra.smul_def, smul_monomial]
    rw [h]
    exact (chartIdeal A m).mul_mem_left _ ih

end
end K1_13_7_5_3_3_3_2
end PackSource_K1_13_7_5_3_3_3_2Model

section PackSource_K1_13_6_3_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_1_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_1
open scoped BigOperators TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

private def coeffMap : Row 4 →+ Row 4 :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom
      (Polynomial.derivative : Polynomial Geom →ₗ[Geom] Polynomial Geom).toAddMonoidHom).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

private theorem coeff_coeffMap (U : Row 4) (m : Fin 4 →₀ ℕ) :
    (coeffMap U).coeff m = Polynomial.derivative (U.coeff m) := rfl

private theorem coeffMap_eq (U : Row 4) : coeffMap U = coefficientDerivative U := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffMap, coefficientDerivative, MvPolynomial.coeff_sum]
  by_cases hm : m ∈ U.support
  · rw [Finset.sum_eq_single_of_mem m hm]
    · simp
    · intro n _ hnm
      simp [MvPolynomial.coeff_monomial, hnm]
  · have hzero : U.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
    rw [hzero, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hnm : n ≠ m := fun e => hm (e ▸ hn)
    simp [MvPolynomial.coeff_monomial, hnm]

private def coeffDer : Derivation ℤ (Row 4) (Row 4) :=
  Derivation.mk' coeffMap.toIntLinearMap (by
    intro U V
    classical
    change coeffMap (U * V) = U * coeffMap V + V * coeffMap U
    rw [mul_comm V (coeffMap U), add_comm (U * coeffMap V)]
    apply MvPolynomial.ext
    intro m
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_mul,
      coeff_coeffMap, map_sum, Polynomial.derivative_mul, Finset.sum_add_distrib])

private def shiftDer (i : Fin 3) : Derivation ℤ (Row 4) (Row 4) :=
  (MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ) •
    (MvPolynomial.pderiv i.castSucc : Derivation (Polynomial Geom) (Row 4) (Row 4)).restrictScalars ℤ

private def partialDer : Derivation ℤ (Row 4) (Row 4) :=
  coeffDer + ∑ i : Fin 3, shiftDer i

private theorem partialDer_apply (U : Row 4) : partialDer U = partialFlow U := by
  have hsum : (∑ i : Fin 3, shiftDer i) U = ∑ i : Fin 3, shiftDer i U := by
    change Derivation.coeFnAddMonoidHom (∑ i : Fin 3, shiftDer i) U = _
    rw [map_sum, Finset.sum_apply]
    rfl
  rw [partialDer, Derivation.add_apply, hsum, partialFlow]
  change coeffMap U + _ = _
  rw [coeffMap_eq]
  simp only [shiftDer, Derivation.smul_apply, Derivation.restrictScalars_apply, smul_eq_mul]

private def rawDer (g : Row 4) : Derivation ℤ (Row 4) (Row 4) :=
  separant g • partialDer -
    partialFlow g •
      (MvPolynomial.pderiv 3 : Derivation (Polynomial Geom) (Row 4) (Row 4)).restrictScalars ℤ

private theorem rawDer_apply (g U : Row 4) : rawDer g U = flowNumerator g U := by
  simp only [rawDer, flowNumerator, Derivation.sub_apply, Derivation.smul_apply, partialDer_apply,
    Derivation.restrictScalars_apply, smul_eq_mul, separant]

/-- Extend a derivation using base change of the module of differentials. -/
private theorem lift_derivation {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallyEtale A B] (d : Derivation ℤ A A) :
    ∃ e : Derivation ℤ B B, ∀ a, e (algebraMap A B a) = algebraMap A B (d a) := by
  let f := (Algebra.linearMap A B).comp d.liftKaehlerDifferential
  let l := (f.liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B).symm.toLinearMap
  refine ⟨l.compDer (KaehlerDifferential.D ℤ B), ?_⟩
  intro a
  change l (KaehlerDifferential.D ℤ B (algebraMap A B a)) = _
  simp [l, f, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

private abbrev RatJets := MvPolynomial (Fin 4) GenericField
private abbrev Denoms : Submonoid (Row 4) :=
  (nonZeroDivisors (Polynomial Geom)).map MvPolynomial.C

private theorem rowToSep_eq (U : Row 4) :
    rowToSep U = algebraMap RatJets SepJets (algebraMap (Row 4) RatJets U) := by
  simpa only [rowToSep, MvPolynomial.algebraMap_def] using
    (MvPolynomial.map_map (algebraMap (Polynomial Geom) GenericField)
      (algebraMap GenericField SepField) U).symm

private theorem formallyEtale_mvPolynomial {k L σ : Type*} [CommRing k] [CommRing L]
    [Algebra k L] [Algebra.FormallyEtale k L] :
    Algebra.FormallyEtale (MvPolynomial σ k) (MvPolynomial σ L) := by
  let A := MvPolynomial σ k
  let B := MvPolynomial σ L
  exact Algebra.FormallyEtale.of_equiv (A := A ⊗[k] L)
    (Algebra.IsPushout.equiv k A L B)

/-- A separable algebraic coefficient extension keeps a domain reduced. -/
private theorem reduced_tensor {k L T : Type*} [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] [CommRing T] [IsDomain T] [Algebra k T] :
    IsReduced (T ⊗[k] L) := by
  let F := FractionRing T
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : Algebra.IsSeparable k B :=
    Subalgebra.isSeparable_iff.mpr (fun x _ => Algebra.IsSeparable.isSeparable k x)
  have : Algebra.IsIntegral k B :=
    ⟨fun x => (Algebra.IsSeparable.isSeparable k x).isIntegral⟩
  let : Field B := (isField_of_isIntegral_of_isField' (S := B) (Field.toIsField k)).toField
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : Algebra.FormallyUnramified k B := Algebra.FormallyUnramified.of_isSeparable k B
  have : IsReduced (F ⊗[k] B) := Algebra.FormallyUnramified.isReduced_of_field F _
  let f := IsScalarTower.toAlgHom k T F
  exact isReduced_of_injective (Algebra.TensorProduct.map f (AlgHom.id k B))
    (Module.Flat.rTensor_preserves_injective_linearMap (M := B) f.toLinearMap
      (IsFractionRing.injective T F))

private theorem radical_extended_prime {k L A B : Type*} [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra L B] [Algebra A B] [IsScalarTower k L B] [IsScalarTower k A B]
    [Algebra.IsPushout k L A B] (p : Ideal A) [p.IsPrime] :
    (p.map (algebraMap A B)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let T := A ⧸ p
  have : IsReduced (T ⊗[k] L) := reduced_tensor (k := k) (L := L) (T := T)
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).toRingEquiv.trans
    ((Algebra.IsPushout.cancelBaseChangeAlg k L A B T).toRingEquiv.trans
      (Algebra.TensorProduct.comm k L T).toRingEquiv)
  exact isReduced_of_injective e e.injective

private theorem stable_extended_ideal {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (d : Derivation ℤ A A) (D : Derivation ℤ B B)
    (hd : ∀ a, D (algebraMap A B a) = algebraMap A B (d a))
    (p : Ideal A) (hp : ∀ x ∈ p, d x ∈ p) :
    ∀ x ∈ p.map (algebraMap A B), D x ∈ p.map (algebraMap A B) := by
  let J := p.map (algebraMap A B)
  intro x hx
  refine Submodule.span_induction (p := fun x _ => D x ∈ J) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    rw [hd]
    exact Ideal.mem_map_of_mem _ (hp a ha)
  · simp [J]
  · intro a b _ _ ha hb
    rw [map_add]
    exact J.add_mem ha hb
  · intro b a ha hDa
    rw [smul_eq_mul, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact J.add_mem (J.mul_mem_left b hDa) (J.mul_mem_right (D b) ha)

private theorem stable_integral_prime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (d : Derivation ℤ A A) (D : Derivation ℤ B B)
    (hd : ∀ a, D (algebraMap A B a) = algebraMap A B (d a))
    (q : Ideal B) [q.IsPrime] (hrad : ((q.under A).map (algebraMap A B)).IsRadical)
    (hp : ∀ x ∈ q.under A, d x ∈ q.under A) : ∀ x ∈ q, D x ∈ q := by
  let J := (q.under A).map (algebraMap A B)
  have hmin : q ∈ J.minimalPrimes := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := A) q
  let C := Localization.AtPrime q
  have hloc : J.map (algebraMap B C) = q.map (algebraMap B C) := by
    calc
      _ = J.radical.map (algebraMap B C) :=
        congrArg (Ideal.map (algebraMap B C)) hrad.radical.symm
      _ = (J.map (algebraMap B C)).radical := IsLocalization.map_radical q.primeCompl C J
      _ = _ := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := C) q J hmin
  intro u hu
  have hm : algebraMap B C u ∈ J.map (algebraMap B C) := by
    rw [hloc]
    exact Ideal.mem_map_of_mem _ hu
  obtain ⟨s, hs, hsu⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl C J u).mp hm
  have hDsu := stable_extended_ideal d D hd _ hp _ hsu
  have hmem : D (s * u) ∈ q := Ideal.map_comap_le hDsu
  rw [D.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  exact (‹q.IsPrime›.mem_or_mem
    ((q.add_mem_iff_left (q.mul_mem_right (D s) hu)).mp hmem)).resolve_left hs

private theorem stable_localized_ideal {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (d : Derivation ℤ B B) (p : Ideal B)
    (h : ∀ a, algebraMap A B a ∈ p → d (algebraMap A B a) ∈ p) :
    ∀ x ∈ p, d x ∈ p := by
  intro x hx
  obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj M x
  have hs : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
  have ha : algebraMap A B a ∈ p := he ▸ p.mul_mem_right _ hx
  have hdxs : d (x * algebraMap A B s) ∈ p := he.symm ▸ h a ha
  rw [d.leibniz, smul_eq_mul, smul_eq_mul] at hdxs
  exact (p.unit_mul_mem_iff_mem hs).mp ((p.add_mem_iff_right (p.mul_mem_right _ hx)).mp hdxs)

set_option maxHeartbeats 500000 in
theorem proof : K1_13_6_3_1.c2 := by
  intro g surface hprime hI
  have : Algebra.FormallyEtale (Row 4) RatJets :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatJets) Denoms
  have : Algebra.FormallyEtale GenericField SepField :=
    Algebra.FormallyEtale.of_isSeparable GenericField SepField
  have : Algebra.FormallyEtale RatJets SepJets := formallyEtale_mvPolynomial
  obtain ⟨d, hd⟩ := lift_derivation (B := RatJets) (rawDer g)
  obtain ⟨D, hD⟩ := lift_derivation (B := SepJets) d
  let q := surface.comap sepToGeo
  have : q.IsPrime := hprime.comap sepToGeo
  have hraw (U : Row 4) : D (rowToSep U) = rowToSep (flowNumerator g U) := by
    rw [rowToSep_eq, hD, hd]
    exact (congrArg (fun a : Row 4 => algebraMap RatJets SepJets
      (algebraMap (Row 4) RatJets a)) (rawDer_apply g U)).trans (rowToSep_eq _).symm
  let p := q.under RatJets
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hrad : (p.map (algebraMap RatJets SepJets)).IsRadical :=
    radical_extended_prime (k := GenericField) (L := SepField) p
  refine ⟨D, hraw, stable_integral_prime (A := RatJets) (B := SepJets) d D hD q hrad ?_⟩
  apply stable_localized_ideal Denoms d p
  intro U hU
  have hUgeo : toGeneric U ∈ surface := by
    rw [← sepToGeo_rowToSep, rowToSep_eq]
    exact hU
  have hflow : algebraMap (Row 4) RatJets (flowNumerator g U) ∈ p := by
    change sepToGeo (algebraMap RatJets SepJets
      (algebraMap (Row 4) RatJets (flowNumerator g U))) ∈ surface
    rw [← rowToSep_eq, sepToGeo_rowToSep]
    exact hI U hUgeo
  rw [hd]
  exact (congrArg (algebraMap (Row 4) RatJets) (rawDer_apply g U)).symm ▸ hflow

end
end K1_13_6_3_1_2
end PackSource_K1_13_6_3_1_2Proof

section PackSource_K1_13_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2000

namespace K1_13_1_2

open K1_13 K1_13_1 PolynomialDifferential
open scoped BigOperators

private abbrev Exponent := JetVariable 3 →₀ ℕ

private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c

/-- Largest total jet degree for derivative exponents a, b, c. -/
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))

private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)

private def firstWidth (a b c : ℕ) : ℕ :=
  90 * 180265 - 133671 * gradeCeiling a b c + indexWeight a b c

/-- The grade falls by j from its ceiling, so each step adds 133671 abscissa slots. -/
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133671 * j

private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x

@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]

@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]

private theorem exponent_coordinates (u : Exponent) :
    exponent (u none) (u (some 0)) (u (some 1)) (u (some 2)) (u (some 3)) = u := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem true_weight (x v a b c : ℕ) :
    (exponent x v a b c).weight (differentialWeight 133671) =
      x + (v * 133671 + a * 133670 + b * 133669 + c * 133668) := by
  have hw : differentialWeight (d := 3) 133671 = fun i =>
      i.elim 1 (fun k => 133671 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, exponent, Finsupp.weight_optionElim, jet_weight]
  simp

private theorem eligible_exponent (x v a b c : ℕ) :
    AnchorEligible (exponent x v a b c) ↔
      c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133671 * (v + (a + b + c)) < 90 * 180265 + indexWeight a b c := by
  unfold AnchorEligible gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, true_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  change (v + a + b + c ≤ 120 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 48 ∧
    c ≤ 10 ∧ a + b + c ≤ 48 - (v + a + b + c - 113 + 1) / 2 ∧
    x + (v * 133671 + a * 133670 + b * 133669 + c * 133668) ≤ 90 * 180265 - 1) ↔ _
  by_cases h : a + b + c = 0 <;> omega

private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133671 * (gradeCeiling a b c - j) < 90 * 180265 + indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 120 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega

/-- The coordinates in order are the third, second, and first derivative exponents,
the drop from the grade ceiling, and the abscissa exponent. -/
private abbrev Slot :=
  Σ c : Fin 11, Σ b : Fin ((48 - 3 * c.val) / 2 + 1),
    Σ a : Fin (48 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)

private abbrev Eligible := {u : Exponent // AnchorEligible u}

private theorem slot_bounds (c b a j x : ℕ) :
    (c < 11 ∧ b < (48 - 3 * c) / 2 + 1 ∧ a < 48 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega

private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
  obtain ⟨hc, hi, hj, hx⟩ := (slot_bounds c b a j x).mp
    ⟨c.isLt, b.isLt, a.isLt, j.isLt, x.isLt⟩
  have hg : gradeCeiling a b c - j - (a.val + b.val + c.val) + (a.val + b.val + c.val) =
      gradeCeiling a b c - j := by omega
  rw [eligible_exponent, hg]
  exact ⟨hc, hi, by omega, (width_iff a b c j x (by omega)).mp hx⟩

private theorem slotExponent_injective : Function.Injective slotExponent := by
  rintro ⟨⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩, ⟨j, hj⟩, ⟨x, hx⟩⟩
    ⟨⟨c', hc'⟩, ⟨b', hb'⟩, ⟨a', ha'⟩, ⟨j', hj'⟩, ⟨x', hx'⟩⟩ h
  have ec : c = c' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 0)) h
  have ej : j = j' := by
    change j < gradeSlots a b c at hj
    change j' < gradeSlots a b c at hj'
    unfold gradeSlots at hj hj'
    omega
  subst j'
  rfl

private theorem slotExponent_surjective : Function.Surjective slotExponent := by
  intro u
  let x := u.val none
  let v := u.val (some 0)
  let a := u.val (some 1)
  let b := u.val (some 2)
  let c := u.val (some 3)
  have he : exponent x v a b c = u.val := exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]

private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]

private theorem sumRange_eq_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range, sumRange_eq]

private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133671 * (n * (n - 1) / 2)

private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]

private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => sumRange (fun a => tripleCount a b c) (48 - 3 * c - 2 * b + 1))
    ((48 - 3 * c) / 2 + 1)

private theorem slot_card : Fintype.card Slot = sumRange sliceCount 11 := by
  simp only [Slot, sliceCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem totalCount : sumRange sliceCount 11 = 2412427366214 := by
  decide +kernel

/-- Exact dimension of the order-90 anchor bank. -/
theorem anchor_finrank : Module.finrank Geom anchorSpace = 2412427366214 := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  let b := MvPolynomial.basisRestrictSupport Geom {u : Exponent | AnchorEligible u}
  exact (Module.finrank_eq_card_basis (b.reindex e.symm)).trans (slot_card.trans totalCount)

theorem proof : K1_13_1.c2 := by
  unfold K1_13_1.c2
  rw [anchor_finrank]
  decide

end K1_13_1_2
end PackSource_K1_13_1_2Proof

section PackSource_K1_13_5_4_3_2Jets
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 1500

namespace K1_13_5_4_3_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial

theorem natCast_geom_ne_zero {j : ℕ} (hj : 0 < j) (hp : j < K1.p) : (j : Geom) ≠ 0 := by
  intro h
  have hk : (j : K1.K) = 0 := embed.injective (by simpa only [map_natCast, map_zero] using h)
  exact (Nat.not_dvd_of_pos_of_lt hj hp) ((CharP.cast_eq_zero_iff K1.K K1.p _).mp hk)

section
variable {f : Row 3} {P : Ideal (GeoRow 3)} (h : TangentStable f P)

local notation "e" => chartEval f P
local notation "r" => invSep f P
local notation "s" => e (separant f)
local notation "d" => delta h

theorem delta_constants (a : Geom) : d (constants e a) = 0 := by
  change d (e (MvPolynomial.C (Polynomial.C a))) = 0
  rw [delta_coeff, derivative_C, map_zero, map_zero]

private theorem delta_natCast (n : ℕ) : d (n : Chart f P) = 0 := by
  rw [← map_natCast (constants e)]
  exact delta_constants h _

theorem delta_centre : d (e (MvPolynomial.C Polynomial.X)) = 1 := by
  rw [delta_coeff, derivative_X, map_one, map_one]

private theorem delta_inv : d r = -(r * r * d s) := by
  have hh := delta_mul h s r
  have hd1 : d (1 : Chart f P) = 0 := by
    simpa only [Nat.cast_one] using delta_natCast h 1
  rw [sep_mul_inv, hd1] at hh
  linear_combination r * hh.symm - d r * sep_mul_inv f P

private theorem delta_inv_pow (n : ℕ) : d (r ^ n) = -(n : Chart f P) * (r ^ (n + 1)) * d s := by
  induction n with
  | zero => simpa using (delta_natCast h 1)
  | succ n ih =>
    rw [pow_succ r n, delta_mul, delta_inv, ih, pow_succ r (n+1), pow_succ r n]
    push_cast
    ring

private theorem delta_scaled (b : Row 3) (n : ℕ) :
    d (e b * r ^ n) =
      e (separant f * tangentNumerator f b -
        (n : Row 3) * b * tangentNumerator f (separant f)) * r ^ (n + 2) := by
  rw [delta_mul, delta_inv_pow, delta_eval h (separant f), delta_eval h b,
    map_sub, map_mul, map_mul, map_mul, map_natCast, pow_succ r (n+1), pow_succ r n]
  have hsr : s * r = 1 := sep_mul_inv f P
  linear_combination
    - (e (tangentNumerator f b) * r ^ n * r) * hsr

private theorem inverse_factorial_step {n : ℕ} (hn : n + 1 < K1.p) :
    (n + 1 : Geom) * (((n + 1).factorial : Geom)⁻¹) = (n.factorial : Geom)⁻¹ := by
  have hs : (n + 1 : Geom) ≠ 0 := by
    exact_mod_cast natCast_geom_ne_zero (Nat.succ_pos n) hn
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv_rev]
  rw [mul_rotate', inv_mul_cancel₀ hs, mul_one]

theorem jet_step (n : ℕ) (hn : n < taylorLength) :
    d (localJet f P n) = (n + 1 : ℕ) * localJet f P (n + 1) := by
  rcases n with _ | _ | _ | k
  · simp [localJet, delta_eval, tangentNumerator, lowerTangent,
      coeffDerivative_X, MvPolynomial.pderiv_X, ← mul_assoc,
      mul_comm r s, sep_mul_inv]
  · simp [localJet, delta_eval, tangentNumerator, lowerTangent,
      coeffDerivative_X, MvPolynomial.pderiv_X, map_ofNat]
    have hsr : r * s = 1 := (mul_comm s r).symm.trans (sep_mul_inv f P)
    linear_combination (2 * e (MvPolynomial.X 2)) * hsr
  · have hsc : (3 : Geom) * (2 * ((6 : Geom)⁻¹)) = 1 := by
      have hn : (6 : Geom) ≠ 0 := natCast_geom_ne_zero (j := 6) (by decide) (by decide)
      rw [← mul_assoc, show (3 : Geom) * 2 = 6 by norm_num, mul_inv_cancel₀ hn]
    have hc := congrArg (constants e) hsc
    simp only [map_mul, map_ofNat, map_one] at hc
    have ht : tangentNumerator f (MvPolynomial.X 2) = -lowerTangent f := by
      simp [tangentNumerator, lowerTangent, MvPolynomial.pderiv_X]
    change d (localJet f P 2) = ((3 : ℕ) : Chart f P) * localJet f P 3
    simp only [localJet, delta_eval, ht, compatibilityNumerator, map_neg, Nat.cast_ofNat]
    norm_num [Nat.factorial]
    linear_combination -(e (lowerTangent f) * r) * hc
  · have hn' : k + 3 + 1 < K1.p := by
      change k + 3 < 133672 at hn
      change k + 3 + 1 < 2130706433
      omega
    have hc := congrArg (constants e) (inverse_factorial_step hn')
    simp only [map_mul, map_add, map_natCast, map_one] at hc
    change d (2 * e (compatibilityNumerator f k) *
        constants e (((k + 3).factorial : Geom)⁻¹) * r ^ (2*k+1)) =
      (k + 3 + 1 : ℕ) * (2 * e (compatibilityNumerator f (k+1)) *
        constants e (((k + 3 + 1).factorial : Geom)⁻¹) * r ^ (2*(k+1)+1))
    have hconst : d (2 * constants e (((k + 3).factorial : Geom)⁻¹)) = 0 := by
      have hd2 : d (2 : Chart f P) = 0 := delta_natCast h 2
      rw [delta_mul, delta_constants, hd2, mul_zero, zero_mul, add_zero]
    rw [show 2 * e (compatibilityNumerator f k) *
        constants e (((k + 3).factorial : Geom)⁻¹) * r ^ (2*k+1) =
        (2 * constants e (((k + 3).factorial : Geom)⁻¹)) *
          (e (compatibilityNumerator f k) * r ^ (2*k+1)) by ring,
      delta_mul, hconst, zero_mul, add_zero, delta_scaled]
    rw [show 2*k+1+2 = 2*(k+1)+1 by omega]
    change _ * (e (compatibilityNumerator f (k+1)) * _) = _
    push_cast at hc ⊢
    linear_combination - (2 * e (compatibilityNumerator f (k+1)) * r ^ (2*(k+1)+1)) * hc

theorem cut_jet_zero (hc : oldCutIdeal f ≤ P) : localJet f P taylorLength = 0 := by
  have hcut : genericRow (oldCut f) ∈ P := hc (Ideal.subset_span (by simp))
  have hz : e (oldCut f) = 0 := chart_zero f P hcut
  change 2 * e (oldCut f) * _ * _ = 0
  rw [hz, mul_zero, zero_mul, zero_mul]

theorem coeff_jetPolynomial {A : Type*} [Semiring A] (M : ℕ) (a : ℕ → A)
    (n : ℕ) : (jetPolynomial M a).coeff n = if n < M then a n else 0 := by
  classical
  rw [jetPolynomial, finsetSum_coeff]
  split_ifs with hn
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin M)]
    · exact coeff_monomial_same _ _
    · intro i _ hi
      exact coeff_monomial_of_ne _ (fun he => hi (Fin.ext he.symm))
    · simp
  · exact Finset.sum_eq_zero fun i _ =>
      coeff_monomial_of_ne _ (fun he => hn (he.symm ▸ i.isLt))

theorem degree_jetPolynomial {A : Type*} [Semiring A] {M D : ℕ} (a : ℕ → A)
    (hM : M ≤ D + 1) : (jetPolynomial M a).natDegree ≤ D := by
  rw [jetPolynomial]
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (i.isLt.trans_le hM))

theorem centred_step (hc : oldCutIdeal f ≤ P) (n : ℕ) :
    d ((centred f P).coeff n) = (centred f P).derivative.coeff n := by
  rw [coeff_derivative, centred, coeff_jetPolynomial, coeff_jetPolynomial]
  by_cases hn : n + 1 < taylorLength
  · rw [ite_eq_left (by omega), ite_eq_left hn, jet_step h n (by omega), mul_comm, Nat.cast_add, Nat.cast_one]
  · rw [ite_eq_right hn, zero_mul]
    split_ifs with hlt
    · rw [jet_step h n hlt, show n + 1 = taylorLength by omega, cut_jet_zero hc, mul_zero]
    · exact map_zero _

end
end
end K1_13_5_4_3_2
end PackSource_K1_13_5_4_3_2Jets

section PackSource_K1_13_5_4_3_2Continuation
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 1500

namespace K1_13_5_4_3_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial

private theorem hasse_comm {A : Type*} [CommRing A] (i j : ℕ) (U : A[X]) :
    hasseDeriv i (hasseDeriv j U) = hasseDeriv j (hasseDeriv i U) := by
  have hi := LinearMap.congr_fun (hasseDeriv_comp (R := A) i j) U
  have hj := LinearMap.congr_fun (hasseDeriv_comp (R := A) j i) U
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hi hj
  rw [hi, hj, Nat.add_comm j i, Nat.choose_symm_add (a := i) (b := j)]

private theorem trajectory_degree {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3)
    (U : A[X]) (hU : U.natDegree ≤ 133671) {D : ℕ} (hf : TrueWeightLE f D) :
    (trajectory k f U).natDegree ≤ D := by
  classical
  rw [trajectory, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_mul_le).trans ?_
  apply le_trans _ (hf m hm)
  apply Nat.add_le_add natDegree_map_le
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans
    (Nat.sub_le_sub_right hU _)) |>.trans_eq (Nat.mul_comm _ _)

section DifferentialPolynomials

variable {A : Type*} [CommRing A]
variable (D : A →+ A) (hOne : D 1 = 0)
  (hMul : ∀ a b, D (a * b) = a * D b + D a * b)

/-- Polynomials whose derivative in the fresh variable equals the coefficient
derivation at the original centre. -/
private def horizontal : Subsemiring A[X] where
  carrier := {U | ∀ n, D (U.coeff n) = U.derivative.coeff n}
  zero_mem' n := by simp
  one_mem' n := by
    rw [derivative_one, coeff_zero, coeff_one]
    split_ifs
    · exact hOne
    · exact map_zero _
  add_mem' {U V} hU hV n := by
    simp only [coeff_add, map_add, hU n, hV n]
  mul_mem' {U V} hU hV n := by
    change D ((U * V).coeff n) = (U * V).derivative.coeff n
    simp only [coeff_mul, map_sum, hMul, hU _, hV _, derivative_mul, coeff_add,
      Finset.sum_add_distrib]
    abel

local notation "H" => horizontal D hOne hMul

private theorem hasse_horizontal {U : A[X]} (hU : U ∈ H) (i : ℕ) :
    hasseDeriv i U ∈ H := by
  have hNat (n : ℕ) : D (n : A) = 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, map_add, ih, hOne, add_zero]
  intro n
  rw [← hasseDeriv_one', hasse_comm 1 i, hasseDeriv_one', hasseDeriv_coeff,
    hasseDeriv_coeff, hMul, hNat, hU (n+i), zero_mul, add_zero]

private theorem shifted_horizontal (k : Geom →+* A) (hk : ∀ z, D (k z) = 0)
    (x₀ : A) (hx : D x₀ = 1) (b : Geom[X]) : taylor x₀ (b.map k) ∈ H := by
  have hX : ((Polynomial.X : A[X]) + Polynomial.C x₀) ∈ H := by
    intro n
    simp only [coeff_add, derivative_X_add_C, coeff_X, coeff_C, coeff_one]
    split_ifs with hn hn' <;> simp_all
  induction b using Polynomial.induction_on' with
  | add a b ha hb => simpa only [Polynomial.map_add, map_add] using (H).add_mem ha hb
  | monomial n a =>
    rw [Polynomial.map_monomial, taylor_monomial]
    refine (H).mul_mem (fun j => ?_) ((H).pow_mem hX n)
    simp only [coeff_C, derivative_C, coeff_zero]
    split_ifs <;> simp [hk]

private theorem horizontal_zero {R : A[X]} (hR : R ∈ H)
    (h0 : R.coeff 0 = 0) (hdeg : R.natDegree < K1.p)
    (hUnit : ∀ n : ℕ, 0 < n → n < K1.p → IsUnit (n : A)) : R = 0 := by
  have hz : ∀ n < K1.p, R.coeff n = 0 := by
    intro n
    induction n with
    | zero => exact fun _ => h0
    | succ n ih =>
      intro hn
      have hstep := hR n
      rw [coeff_derivative, ih (Nat.lt_of_succ_lt hn), map_zero] at hstep
      have hu : IsUnit ((n : A) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hUnit (n + 1) (Nat.succ_pos n) hn
      exact hu.mul_left_inj.mp (hstep.symm.trans (zero_mul _).symm)
  ext n
  rw [coeff_zero]
  by_cases hn : n < K1.p
  · exact hz n hn
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_lt hn))

include hOne hMul in
private theorem fresh_identity (k : Geom →+* A) (hk : ∀ z, D (k z) = 0)
    (x₀ : A) (hx : D x₀ = 1) (f : Row 3) (U W : A[X]) (hShift : taylor x₀ U = W)
    (hW : ∀ n, D (W.coeff n) = W.derivative.coeff n)
    (hEval : (trajectory k f U).eval x₀ = 0) (hDeg : (trajectory k f U).natDegree < K1.p)
    (hUnit : ∀ n : ℕ, 0 < n → n < K1.p → IsUnit (n : A)) :
    trajectory k f U = 0 := by
  let t := (taylorAlgHom x₀).toRingHom
  let g := t.comp (Polynomial.mapRingHom k)
  let a : Fin 3 → A[X] := fun i => hasseDeriv i.val W
  have hArg (i : Fin 3) : t (hasseDeriv i.val U) = a i := by
    change taylor x₀ (hasseDeriv i.val U) = hasseDeriv i.val W
    rw [← hasseDeriv_taylor, hShift]
  have hT : t (trajectory k f U) = MvPolynomial.eval₂ g a f := by
    rw [trajectory, MvPolynomial.hom_eval₂]
    simp only [hArg]
    rfl
  have hR : t (trajectory k f U) ∈ H := by
    rw [hT]
    let g' : Geom[X] →+* H := g.codRestrict _ (shifted_horizontal D hOne hMul k hk x₀ hx)
    let v : Fin 3 → H := fun i => ⟨a i, hasse_horizontal D hOne hMul hW i.val⟩
    let R' : H := MvPolynomial.eval₂ g' v f
    have hm : (R' : A[X]) = MvPolynomial.eval₂ g a f :=
      MvPolynomial.hom_eval₂ f g' (H).subtype v
    rw [← hm]
    exact R'.2
  apply (taylor_eq_zero x₀ _).mp
  apply horizontal_zero D hOne hMul hR _ _ hUnit
  · change (taylor x₀ (trajectory k f U)).coeff 0 = 0
    rwa [taylor_coeff_zero]
  · change (taylor x₀ (trajectory k f U)).natDegree < K1.p
    rwa [natDegree_taylor]

end DifferentialPolynomials

section
variable {f : Row 3} {P : Ideal (GeoRow 3)}

local notation "A" => Chart f P
local notation "e" => chartEval f P
local notation "k" => constants e
local notation "x₀" => e (MvPolynomial.C Polynomial.X)

private theorem initial_jet (i : Fin 3) :
    (hasseDeriv i.val (localTaylor f P)).eval x₀ = e (MvPolynomial.X i) := by
  have hi : i.val < taylorLength := i.isLt.trans (by decide)
  rw [← taylor_coeff, localTaylor, taylor_taylor, add_neg_cancel, taylor_zero, centred,
    coeff_jetPolynomial, ite_eq_left hi]
  fin_cases i <;> rfl

private theorem initial_residual (hc : oldCutIdeal f ≤ P) :
    (trajectory k f (localTaylor f P)).eval x₀ = 0 := by
  unfold trajectory
  change (evalRingHom x₀) (MvPolynomial.eval₂ _ _ f) = _
  have hCoeff : (evalRingHom x₀).comp (Polynomial.mapRingHom k) = (e).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro z
      change ((Polynomial.C z).map k).eval x₀ = k z
      rw [Polynomial.map_C, eval_C]
    · change ((Polynomial.X : Geom[X]).map k).eval x₀ = x₀
      rw [Polynomial.map_X, eval_X]
  rw [MvPolynomial.hom_eval₂, hCoeff]
  simp only [coe_evalRingHom, initial_jet]
  have he := (MvPolynomial.hom_eval₂ f MvPolynomial.C e MvPolynomial.X).symm
  rw [MvPolynomial.eval₂_eta] at he
  rw [he]
  exact chart_zero f P (hc (Ideal.subset_span (by simp)))

theorem continuation (h : TangentStable f P) (hf : TrueWeightLE f (90 * 180265 - 1))
    (hc : oldCutIdeal f ≤ P) : trajectory k f (localTaylor f P) = 0 := by
  have hOne : delta h (1 : A) = 0 := by
    simpa only [map_one] using delta_constants h (1 : Geom)
  have hU : (localTaylor f P).natDegree ≤ 133671 := by
    rw [localTaylor, natDegree_taylor, centred]
    exact degree_jetPolynomial _ (by decide)
  have hShift : taylor x₀ (localTaylor f P) = centred f P := by
    rw [localTaylor, taylor_taylor, add_neg_cancel, taylor_zero]
  refine fresh_identity (delta h) hOne (delta_mul h) k (delta_constants h) x₀ (delta_centre h)
    f (localTaylor f P) (centred f P) hShift (centred_step h hc) (initial_residual hc) ?_ ?_
  · exact (trajectory_degree k f _ hU hf).trans_lt (by decide)
  · intro n hn hp
    rw [← map_natCast k]
    exact (natCast_geom_ne_zero hn hp).isUnit.map k

end
end
end K1_13_5_4_3_2
end PackSource_K1_13_5_4_3_2Continuation

section PackSource_K1_13_5_4_3_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_5_4_3_2

noncomputable section

open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial

section
variable {f : Row 3} {P : Ideal (GeoRow 3)} {y : Fin 3 → GeometricX}

private def specialize (hy : y ∈ regularLocus f P) : Chart f P →+* GeometricX :=
  chartLift (pointEval y) (fun b hb => hy.1 (genericRow b) hb) (isUnit_iff_ne_zero.mpr hy.2)

private theorem specialize_eval (hy : y ∈ regularLocus f P) (b : Row 3) :
    specialize hy (chartEval f P b) = pointEval y b :=
  chartLift_eval _ _ _ b

private theorem specialize_inv (hy : y ∈ regularLocus f P) :
    specialize hy (invSep f P) = (pointEval y (separant f))⁻¹ := by
  have hh := congrArg (specialize hy) (sep_mul_inv f P)
  simp only [map_mul, map_one, specialize_eval] at hh
  exact ((mul_eq_one_iff_inv_eq₀ hy.2).mp hh).symm

private theorem specialize_constants (hy : y ∈ regularLocus f P) :
    (specialize hy).comp (constants (chartEval f P)) = algebraMap Geom GeometricX := by
  apply RingHom.ext
  intro a
  change specialize hy (chartEval f P (MvPolynomial.C (Polynomial.C a))) = _
  rw [specialize_eval]
  change MvPolynomial.eval y (MvPolynomial.map genericCoeff (MvPolynomial.C (Polynomial.C a))) = _
  rw [MvPolynomial.map_C, MvPolynomial.eval_C, ← Polynomial.algebraMap_eq]
  rfl

private theorem specialize_jet (hy : y ∈ regularLocus f P) (j : ℕ) :
    specialize hy (localJet f P j) = centredJet f (pointEval y) j := by
  rcases j with _ | _ | _ | n
  all_goals simp only [localJet, centredJet, specialize_eval, map_mul, map_ofNat, map_pow,
    specialize_inv]
  change 2 * pointEval y (compatibilityNumerator f n) *
      ((specialize hy).comp (constants (chartEval f P))) (((n+3).factorial : Geom)⁻¹) *
        (pointEval y (separant f))⁻¹ ^ (2*n+1) = _
  rw [specialize_constants hy, map_inv₀, map_natCast, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

private theorem specialize_taylor (hy : y ∈ regularLocus f P) :
    (localTaylor f P).map (specialize hy) = taylorAt f (pointEval y) := by
  simp only [localTaylor, taylorAt, map_taylor, map_neg, specialize_eval, centre, centred, jetPolynomial,
    Polynomial.map_sum, Polynomial.map_monomial, specialize_jet]

private theorem specialize_trajectory (hy : y ∈ regularLocus f P) :
    (trajectory (constants (chartEval f P)) f (localTaylor f P)).map (specialize hy) =
      extendedAtJet f (taylorAt f (pointEval y)) := by
  unfold trajectory
  change Polynomial.mapRingHom (specialize hy) (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp, specialize_constants]
  simp only [Polynomial.coe_mapRingHom, ← Polynomial.hasseDeriv_map, specialize_taylor]
  unfold extendedAtJet
  rw [MvPolynomial.eval_map]

end

theorem proof : K1_13_5_4_3.c2 := by
  intro f P hf _ hc _ h y hy
  rw [← specialize_trajectory hy, continuation h hf hc, Polynomial.map_zero]

end
end K1_13_5_4_3_2
end PackSource_K1_13_5_4_3_2Proof

section PackSource_K1_13_5_4_2_3_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_3_1

noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_3 MvPolynomial

private theorem graphPoint_kills {f : Row 3} (T : LiftedChart f)
    {P : Ideal (GeoRow 3)} (hP : oldCutIdeal f ≤ P)
    {x : Fin 3 → GeometricX} (hx : x ∈ regularLocus f P) :
    threeCut f T ≤ RingHom.ker (eval (graphPoint f x)) := by
  have hf : eval x (genericRow f) = 0 :=
    hx.1 _ (hP (Ideal.subset_span (by simp)))
  refine sup_le (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    apply RingHom.mem_ker.mpr
    rcases hb with rfl | rfl
    · rwa [eval_liftRow_graphPoint]
    · exact eval_graph_graphPoint hx.2
  · exact RingHom.mem_ker.mpr ((eval_represents_iff T.cut_represents hf hx.2).mpr
      (hx.1 _ (hP (Ideal.subset_span (by simp)))))

/-- Clear the separant denominator after moving a graph polynomial to the old chart. -/
private theorem clear_denominator (f : Row 3) (T : LiftedChart f)
    (e : OldOpen f ≃+* GraphOpen f T)
    (he : ∀ a, e (oldMap f a) = graphMap f T (liftRow a)) (b : GeoRow 4) :
    ∃ (n : ℕ) (a : GeoRow 3),
      graphMap f T b * graphMap f T (liftedSep f) ^ n = graphMap f T (liftRow a) := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (oldCutIdeal f) (sep f)) (e.symm (graphMap f T b))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e.symm (graphMap f T b) * oldMap f (sep f) ^ n = oldMap f a at hc
  exact ⟨n, a, by simpa only [map_mul, map_pow, RingEquiv.apply_symm_apply, he]
    using congrArg e hc⟩

/-- A prime that avoids the separant is determined by its regular points. -/
private theorem mem_iff_vanishes_regular {f : Row 3} {P : Ideal (GeoRow 3)} [P.IsPrime]
    (hsep : sep f ∉ P) (a : GeoRow 3) :
    a ∈ P ↔ ∀ x ∈ regularLocus f P, eval x a = 0 := by
  refine ⟨fun ha _ hx => hx.1 a ha, fun ha => ?_⟩
  have hz : sep f * a ∈ vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
    intro x hx
    change eval x (sep f * a) = 0
    rw [map_mul]
    by_cases hs : eval x (sep f) = 0
    · rw [hs, zero_mul]
    · rw [ha x ⟨hx, hs⟩, mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hz
  exact (‹P.IsPrime›.mem_or_mem hz).resolve_left hsep

theorem proof : K1_13_5_4_2_3.c1 := by
  intro f T e he Q hQ hcut hsep
  letI : Q.IsPrime := hQ
  let P := Q.comap (rename Fin.castSucc).toRingHom
  letI : P.IsPrime := hQ.comap _
  change oldCutIdeal f ≤ P ∧ graphCurve f P = Q
  let F := FractionRing (GeoRow 4 ⧸ Q)
  let q : GeoRow 4 →+* F := (algebraMap (GeoRow 4 ⧸ Q) F).comp (Ideal.Quotient.mk Q)
  have hq (b : GeoRow 4) : q b = 0 ↔ b ∈ Q := by
    change algebraMap (GeoRow 4 ⧸ Q) F (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hsq : q (liftedSep f) ≠ 0 := fun h => hsep ((hq _).mp h)
  let qOpen := openLift (threeCut f T) (liftedSep f) q
    (fun b hb => RingHom.mem_ker.mpr ((hq b).mpr (hcut hb))) (isUnit_iff_ne_zero.mpr hsq)
  have hqOpen (b : GeoRow 4) : qOpen (graphMap f T b) = q b := openLift_onOpen _ _ _ _ _ b
  have hP : oldCutIdeal f ≤ P := by
    intro a ha
    change liftRow a ∈ Q
    apply (hq _).mp
    rw [← hqOpen, ← he, onOpen_kills ha, map_zero, map_zero]
  refine ⟨hP, ?_⟩
  apply SetLike.ext
  intro b
  obtain ⟨n, a, hab⟩ := clear_denominator f T e he b
  have hfrac := congrArg qOpen hab
  simp only [map_mul, map_pow, hqOpen] at hfrac
  have hQmem : b ∈ Q ↔ a ∈ P := by
    change b ∈ Q ↔ liftRow a ∈ Q
    rw [← hq b, ← hq (liftRow a), ← hfrac, mul_eq_zero]
    simp only [pow_ne_zero n hsq, or_false]
  have hpoint (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval (graphPoint f x) b * eval x (sep f) ^ n = eval x a := by
    have hs : eval (graphPoint f x) (liftedSep f) ≠ 0 := by
      rw [eval_liftRow_graphPoint]
      exact hx.2
    let w := openLift (threeCut f T) (liftedSep f) (eval (graphPoint f x))
      (graphPoint_kills T hP hx) (isUnit_iff_ne_zero.mpr hs)
    have hw (g : GeoRow 4) : w (graphMap f T g) = eval (graphPoint f x) g :=
      openLift_onOpen _ _ _ _ _ g
    simpa only [map_mul, map_pow, hw, eval_liftRow_graphPoint] using congrArg w hab
  rw [hQmem, mem_iff_vanishes_regular (show sep f ∉ P from hsep)]
  constructor
  · intro hb x hx
    have hz : eval (graphPoint f x) b = 0 := hb _ ⟨x, hx, rfl⟩
    rw [← hpoint x hx, hz, zero_mul]
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (mul_eq_zero.mp ((hpoint x hx).trans (ha x hx))).resolve_right (pow_ne_zero n hx.2)

end

end K1_13_5_4_2_3_1
end PackSource_K1_13_5_4_2_3_1Proof

section PackSource_K1_13_6_2_4_4Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_2_4_4

noncomputable section

open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
open scoped Polynomial TensorProduct

/-- Regard the last jet as the polynomial variable over the old jet ring. -/
private def fifthEquiv : GeoJets5 ≃+* GeoJets[X] :=
  ((MvPolynomial.renameEquiv GeoField finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft GeoField (Fin 4))).toRingEquiv

private theorem fifthEquiv_comp :
    fifthEquiv.toRingHom.comp oldEmbedding = Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [fifthEquiv, oldEmbedding, MvPolynomial.optionEquivLeft_C]
  · intro i
    simp [fifthEquiv, oldEmbedding, MvPolynomial.optionEquivLeft_X_some]

@[simp] private theorem fifthEquiv_old (D : GeoJets) :
    fifthEquiv (oldEmbedding D) = Polynomial.C D :=
  DFunLike.congr_fun fifthEquiv_comp D

private theorem map_cylinder (P : Ideal GeoJets) :
    (cylinder P).map (fifthEquiv : GeoJets5 →+* GeoJets[X]) = P.map Polynomial.C := by
  rw [← RingEquiv.toRingHom_eq_coe, cylinder, Ideal.map_map, fifthEquiv_comp]

private def cylinderQuotient (P : Ideal GeoJets) :
    (GeoJets5 ⧸ cylinder P) ≃+* (GeoJets ⧸ P)[X] :=
  (Ideal.quotientEquiv (cylinder P) (P.map Polynomial.C) fifthEquiv (map_cylinder P).symm).trans
    P.polynomialQuotientEquivQuotientPolynomial.symm

@[simp] private theorem cylinderQuotient_old (P : Ideal GeoJets) (D : GeoJets) :
    cylinderQuotient P (Ideal.Quotient.mk (cylinder P) (oldEmbedding D)) =
      Polynomial.C (Ideal.Quotient.mk P D) := by
  rw [cylinderQuotient, RingEquiv.trans_apply, Ideal.quotientEquiv_mk, fifthEquiv_old,
    Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]

private theorem cylinder_regular {P : Ideal GeoJets} {D : GeoJets}
    (h : IsLeftRegular (Ideal.Quotient.mk P D)) :
    IsLeftRegular (Ideal.Quotient.mk (cylinder P) (oldEmbedding D)) := by
  intro x y he
  apply (cylinderQuotient P).injective
  have he' := congrArg (cylinderQuotient P) he
  simp only [map_mul, cylinderQuotient_old] at he'
  ext n
  have hn := congrArg (fun p : (GeoJets ⧸ P)[X] => p.coeff n) he'
  exact h (by simpa only [Polynomial.coeff_C_mul] using hn)

private theorem mem_cylinder_old {P : Ideal GeoJets} {D : GeoJets} :
    oldEmbedding D ∈ cylinder P ↔ D ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← (cylinderQuotient P).map_eq_zero_iff,
    cylinderQuotient_old, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]

private theorem cylinder_prime {P : Ideal GeoJets} (hP : P.IsPrime) : (cylinder P).IsPrime := by
  let := hP
  let h : IsDomain (GeoJets5 ⧸ cylinder P) :=
    MulEquiv.isDomain (GeoJets ⧸ P)[X] (cylinderQuotient P).toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime (cylinder P)).mp h

private theorem cylinder_minimal {I P : Ideal GeoJets} (hP : I.IsMinimalPrime P) :
    (cylinder I).IsMinimalPrime (cylinder P) := by
  refine ⟨⟨cylinder_prime hP.isPrime, Ideal.map_mono hP.le⟩, ?_⟩
  intro T hT hTP
  let := hT.1
  have hle : T.comap oldEmbedding ≤ P := fun _ hx =>
    mem_cylinder_old.mp (hTP hx)
  have hPT : P ≤ T.comap oldEmbedding :=
    hP.2 ⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp hT.2⟩ hle
  exact Ideal.map_le_iff_le_comap.mpr hPT

private theorem cylinder_dimension {P : Ideal GeoJets}
    (h : ringKrullDim (GeoJets ⧸ P) = 2) : OfDim (cylinder P) 3 := by
  unfold OfDim
  have he : ringKrullDim (GeoJets5 ⧸ cylinder P) = ringKrullDim ((GeoJets ⧸ P)[X]) :=
    ringKrullDim_eq_of_ringEquiv (cylinderQuotient P)
  rw [he, Polynomial.ringKrullDim_of_isNoetherianRing, h]
  norm_num

private theorem relPrime_of_regular {F G : GeoJets} (hF : F ≠ 0)
    (hG : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G)) :
    IsRelPrime F G := by
  rintro a ⟨b, hab⟩ ⟨c, hac⟩
  have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hF)
  have hmul : G * b ∈ (Ideal.span {F} : Ideal GeoJets) := by
    apply Ideal.mem_span_singleton.mpr
    exact ⟨c, by rw [hab, hac]; ring⟩
  have hz : Ideal.Quotient.mk (Ideal.span {F}) b = 0 :=
    (isLeftRegular_iff_right_eq_zero_of_mul.mp hG) _ (by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmul)
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  apply isUnit_iff_dvd_one.mpr
  apply (mul_dvd_mul_iff_left hb).mp
  simpa only [mul_one, hab, mul_comm b a] using hd

local instance : Algebra GeoJets GeoJets5 := oldEmbedding.toAlgebra

local instance : Module.Flat GeoJets GeoJets5 := by
  let e : GeoJets5 ≃ₐ[GeoJets] GeoJets[X] :=
    { fifthEquiv with
      commutes' := by
        intro b
        exact fifthEquiv_old b }
  let := Module.Free.of_basis (Polynomial.basisMonomials GeoJets)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- At the cylinder prime the maximal ideal comes from the old local ring.
The local length formula therefore has fibre factor one. -/
private theorem cylinder_length (I P : Ideal GeoJets) (hP : P.IsPrime) :
    cycleLength I P hP = LengthAt (cylinder I) (cylinder P) (cylinder_prime hP) := by
  let := hP
  let := cylinder_prime hP
  let : (cylinder P).LiesOver P := ⟨by
    ext D
    exact mem_cylinder_old.symm⟩
  let A := Localization.AtPrime P
  let B := Localization.AtPrime (cylinder P)
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver P (cylinder P)
  have : IsScalarTower GeoJets A B := inferInstance
  have : IsLocalHom (algebraMap A B) := by
    rw [Localization.AtPrime.algebraMap_eq P (cylinder P)]
    infer_instance
  have hmap (L : Ideal GeoJets) :
      (L.map (algebraMap GeoJets A)).map (algebraMap A B) =
        (cylinder L).map (algebraMap GeoJets5 B) := by
    change (_ : Ideal B) = (L.map (algebraMap GeoJets GeoJets5)).map (algebraMap GeoJets5 B)
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P), hmap,
      Localization.AtPrime.map_eq_maximalIdeal]
  let L := I.map (algebraMap GeoJets A)
  have hsimple : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal B).1
  have hlen := IsLocalRing.length_baseChange A B (A ⧸ L)
  rw [hmax, Module.length_eq_one B (B ⧸ IsLocalRing.maximalIdeal B), mul_one] at hlen
  change Module.length A (A ⧸ L) =
    Module.length B (B ⧸ (cylinder I).map (algebraMap GeoJets5 B))
  rw [← hmap I]
  exact hlen.symm.trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B L).toLinearEquiv.length_eq.symm

theorem proof : K1_13_6_2_4.c4 := by
  intro f Q hf hQ
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have hA : sectionIdeal ⊥ (oldEmbedding (toGeneric f)) = cylinder F := by
    simp [sectionIdeal, cylinder, F, Ideal.map_span]
  have hJ : sectionIdeal (sectionIdeal ⊥ (oldEmbedding (toGeneric f))) (oldEmbedding (toGeneric Q)) =
      cylinder (intersectionIdeal f Q) := by
    rw [hA, intersectionIdeal, Ideal.span_insert]
    simp [sectionIdeal, cylinder, F, Ideal.map_sup, Ideal.map_span]
  have hreg := K1_13_6_3_6.geometric_regular hf hQ
  have hF := K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero
  dsimp only
  constructor
  · exact (congrArg (fun I : Ideal GeoJets5 =>
      IsLeftRegular (Ideal.Quotient.mk I (oldEmbedding (toGeneric Q)))) hA).mpr
      (cylinder_regular hreg)
  · intro P hP
    refine ⟨cylinder_dimension (K1_13_6_1_4.pair_dimension hF (relPrime_of_regular hF hreg) hP),
      ?_⟩
    apply (congrArg (fun I : Ideal GeoJets5 => ∃ hc : I.IsMinimalPrime (cylinder P),
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≤ LengthAt I (cylinder P) hc.isPrime) hJ).mpr
    exact ⟨cylinder_minimal hP, (cylinder_length (intersectionIdeal f Q) P hP.isPrime).le⟩

end

end K1_13_6_2_4_4
end PackSource_K1_13_6_2_4_4Proof

section PackSource_K1_13_6_2_4_1Shift
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_2_4_1

noncomputable section

open MvPolynomial

/-- Translate one grading variable by minus one. -/
def previous (i : Fin 5) : Form →+* Form :=
  eval₂Hom C (fun j => MvPolynomial.X j + C (if j = i then -1 else 0))

def backwardDiff (i : Fin 5) : Form →+ Form :=
  AddMonoidHom.id Form - (previous i).toAddMonoidHom

theorem backwardDiff_apply (i : Fin 5) (p : Form) :
    backwardDiff i p = p - previous i p := rfl

theorem previous_eval (i : Fin 5) (p : Form) (t : Grade) :
    eval (fun j => ((t + unitGrade i) j : ℚ)) (previous i p) =
      eval (fun j => (t j : ℚ)) p := by
  let R := eval (fun j => (t j : ℚ))
  let L := (eval (fun j => ((t + unitGrade i) j : ℚ))).comp (previous i)
  have h : L = R := by
    ext j
    · simp [L, R, previous]
    · by_cases hij : i = j
      · subst j
        simp [L, R, previous, unitGrade]
      · simp [L, R, previous, unitGrade, Finsupp.single_apply, hij, Ne.symm hij]
  exact DFunLike.congr_fun h p

/-- The exact sequence in successor grades becomes a polynomial identity. -/
theorem eq_sub_previous (i : Fin 5) {f g h : Grade → ℕ} {p q r : Form}
    (hp : Represents p (fun t => f t)) (hq : Represents q (fun t => g t))
    (hr : Represents r (fun t => h t))
    (hex : ∀ t, f (t + unitGrade i) + h t = g (t + unitGrade i)) :
    p = q - previous i r := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hq
  obtain ⟨L, hL⟩ := hr
  refine eq_of_grid (N := max (max N M) L + 1) fun u hu => ?_
  have he (j : Fin 5) : unitGrade i j ≤ 1 := by
    simp only [unitGrade, Finsupp.single_apply]
    split <;> omega
  let t : Grade := Finsupp.equivFunOnFinite.symm fun j => u j - unitGrade i j
  have hut : t + unitGrade i = u := by
    ext j
    have h := hu j
    have h' := he j
    change u j - unitGrade i j + unitGrade i j = u j
    omega
  have hprev : eval (fun j => (u j : ℚ)) (previous i r) = eval (fun j => (t j : ℚ)) r := by
    rw [← hut, previous_eval]
  have hNu : ∀ j, N ≤ u j := fun j => by have := hu j; omega
  have hMu : ∀ j, M ≤ u j := fun j => by have := hu j; omega
  have hLt (j : Fin 5) : L ≤ t j := by
    have h := hu j
    have h' := he j
    change L ≤ u j - unitGrade i j
    omega
  rw [map_sub, hprev, hN _ hNu, hM _ hMu, hL _ hLt, eq_sub_iff_add_eq]
  change (f u : ℚ) + (h t : ℚ) = (g u : ℚ)
  exact_mod_cast (hut ▸ hex t)

private theorem previous_erase (i : Fin 5) (a : Grade) (r : ℚ) :
    previous i (monomial (a.erase i) r) = monomial (a.erase i) r := by
  rw [previous, eval₂Hom_monomial, monomial_eq]
  congr 1
  apply Finsupp.prod_congr
  intro j hj
  have hij : j ≠ i := fun h => (Finsupp.mem_support_iff.mp hj) (by simp [h])
  simp [hij]

private theorem shiftedPower (i : Fin 5) (a : Grade) (r : ℚ) :
    previous i (monomial a r) =
      ∑ k ∈ Finset.range (a i + 1),
        monomial (a.erase i + Finsupp.single i k)
          (r * ((-1 : ℚ) ^ (a i - k) * ((a i).choose k : ℚ))) := by
  have hm : monomial a r = MvPolynomial.X i ^ a i * monomial (a.erase i) r := by
    conv_lhs => rw [← Finsupp.erase_add_single i a, add_comm]
    exact monomial_single_add
  rw [hm, map_mul, map_pow, previous_erase]
  have hx : previous i (MvPolynomial.X i) = MvPolynomial.X i + C (-1) := by simp [previous]
  rw [hx, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, ← map_natCast (MvPolynomial.C : ℚ →+* Form) ((a i).choose k)]
  calc
    _ = (C ((-1 : ℚ) ^ (a i - k)) * C ((a i).choose k : ℚ)) *
        (MvPolynomial.X i ^ k * monomial (a.erase i) r) := by ring
    _ = _ := by
      rw [← map_mul, ← monomial_single_add, C_mul_monomial,
        add_comm (Finsupp.single i k) (a.erase i), mul_comm _ r]

private theorem backward_monomial (i : Fin 5) (a : Grade) (r : ℚ) :
    backwardDiff i (monomial a r) =
      ∑ k ∈ Finset.range (a i),
        monomial (a.erase i + Finsupp.single i k)
          (-(r * ((-1 : ℚ) ^ (a i - k) * ((a i).choose k : ℚ)))) := by
  rw [backwardDiff_apply, shiftedPower, Finset.sum_range_succ]
  simp [Finsupp.erase_add_single, ← Finset.sum_neg_distrib]

private theorem erase_degree (i : Fin 5) (a : Grade) :
    (a.erase i).degree + a i = a.degree := by
  simpa using congrArg Finsupp.degree (Finsupp.erase_add_single i a)

theorem backwardDiff_coeff_eq_zero (i : Fin 5) {p : Form} (a : Grade)
    (h : p.totalDegree ≤ a.degree) : (backwardDiff i p).coeff a = 0 := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hb' : b.degree ≤ a.degree := (le_totalDegree hb).trans h
  rw [backward_monomial, coeff_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  apply coeff_eq_zero_of_totalDegree_lt
  have hd := erase_degree i b
  have hk' := Finset.mem_range.mp hk
  have hb'' : (b.erase i + Finsupp.single i k).degree < a.degree := by
    rw [map_add, Finsupp.degree_single]
    omega
  exact (totalDegree_monomial_le _ _).trans_lt hb''

theorem backwardDiff_degree_le (i : Fin 5) {p : Form} {d : ℕ}
    (h : p.totalDegree ≤ d + 1) : (backwardDiff i p).totalDegree ≤ d := by
  refine Finset.sup_le fun a ha => ?_
  by_contra! hda
  exact (mem_support_iff.mp ha) (backwardDiff_coeff_eq_zero i a (h.trans hda))

theorem previous_coeff (i : Fin 5) {p : Form} (a : Grade)
    (h : p.totalDegree ≤ a.degree) : (previous i p).coeff a = p.coeff a := by
  have hz := backwardDiff_coeff_eq_zero i a h
  rw [backwardDiff_apply, coeff_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem previous_degree_le (i : Fin 5) {p : Form} {d : ℕ}
    (h : p.totalDegree ≤ d) : (previous i p).totalDegree ≤ d := by
  refine Finset.sup_le fun a ha => ?_
  by_contra! hda
  have h' := h.trans hda.le
  exact (mem_support_iff.mp ha)
    ((previous_coeff i a h').trans (coeff_eq_zero_of_totalDegree_lt (h.trans_lt hda)))

private theorem backward_monomial_coeff (i : Fin 5) {a b : Grade}
    (ha : a i = 0) (hb : b.degree ≤ a.degree + 1) (r : ℚ) :
    (backwardDiff i (monomial b r)).coeff a = (monomial b r).coeff (a + unitGrade i) := by
  classical
  rw [backward_monomial, coeff_sum]
  by_cases he : b = a + unitGrade i
  · subst b
    have hv : (a + unitGrade i) i = 1 := by simp [unitGrade, ha]
    have herr : (a + unitGrade i).erase i + Finsupp.single i 0 = a := by
      ext j
      by_cases hj : j = i <;> simp [unitGrade, hj, ha]
    rw [hv, Finset.sum_range_one, herr]
    norm_num
  · rw [coeff_monomial, ite_eq_right he]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [coeff_monomial, ite_eq_right]
    intro heq
    have hk0 : k = 0 := by
      have hp := congrArg (fun t : Grade => t i) heq
      simpa [ha] using hp
    subst k
    have heq' : a = b.erase i := by simpa using heq.symm
    have hd := erase_degree i b
    have hk' := Finset.mem_range.mp hk
    rw [← heq'] at hd
    have hb' : b i = 1 := by omega
    exact he (by rw [heq', unitGrade, ← hb', Finsupp.erase_add_single])

theorem backwardDiff_coeff_squarefree (i : Fin 5) {I : Finset (Fin 5)} (hi : i ∉ I)
    {p : Form} (h : p.totalDegree ≤ I.card + 1) :
    (backwardDiff i p).coeff (squarefree I) = p.coeff (squarefree (insert i I)) := by
  have ha : squarefree I i = 0 := by simp [squarefree_apply, hi]
  rw [squarefree_insert hi, ← p.support_sum_monomial_coeff, map_sum, coeff_sum, coeff_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact backward_monomial_coeff i ha
    (by rw [squarefree_degree]; exact (le_totalDegree hb).trans h) (p.coeff b)

end

end K1_13_6_2_4_1
end PackSource_K1_13_6_2_4_1Shift

section PackSource_K1_13_7_1_1_1_1Differences
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_1_1_1_1

noncomputable section

open K1_13_6 K1_13_7_1_1_1 MvPolynomial
open K1_13_6_2_4_1 (Grade Form Represents squarefree squarefree_degree TopNonnegative
  unitGrade previous previous_eval backwardDiff backwardDiff_apply backwardDiff_degree_le
  backwardDiff_coeff_squarefree)

private theorem grade_shift (b : ℕ) (w : Grades) (i : Fin 4) :
    grade b (w + Pi.single i 1) = grade b w + unitGrade i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [Finsupp.add_apply, grade_last, grade_last, unitGrade,
      Finsupp.single_eq_of_ne' (Fin.castSucc_ne_last i), add_zero]
  · by_cases h : i = k
    · subst k
      simp [unitGrade]
    · simp [unitGrade, Ne.symm h]

private theorem large_add {N : ℕ} {w : Grades} (hw : ∀ j, N ≤ w j)
    (i : Fin 4) (s : ℕ) : ∀ j, N ≤ (w + Pi.single i s : Grades) j :=
  fun j => (hw j).trans (Nat.le_add_right _ _)

private theorem unit_differences_eval (b N : ℕ) (dirs : List (Fin 4))
    (H : Grades → ℝ) (p : Form) (u : Grade)
    (h : ∀ w, (∀ j, N ≤ w j) →
      H w = (eval (fun j => ((grade b w + u) j : ℚ)) p : ℝ)) :
    ∃ v : Grade, ∀ w, (∀ j, N ≤ w j) →
      gradeDifferences dirs 1 H w = (eval (fun j => ((grade b w + v) j : ℚ))
        ((dirs.map Fin.castSucc).foldl (fun q j => backwardDiff j q) p) : ℝ) := by
  induction dirs generalizing H p u with
  | nil => exact ⟨u, h⟩
  | cons i dirs ih =>
    simp only [gradeDifferences, List.foldl_cons, List.map_cons]
    apply ih (gradeDifference H i 1) (backwardDiff i.castSucc p) (u + unitGrade i.castSucc)
    intro w hw
    have hs : grade b (w + Pi.single i 1) + u = (grade b w + u) + unitGrade i.castSucc := by
      rw [grade_shift]
      abel
    have hu : grade b w + (u + unitGrade i.castSucc) =
        (grade b w + u) + unitGrade i.castSucc := (add_assoc _ _ _).symm
    rw [gradeDifference, h _ (large_add hw i 1), h _ hw, hs, hu,
      backwardDiff_apply, map_sub, Rat.cast_sub, previous_eval]

private theorem fold_backward_eq_const (dirs : List (Fin 5)) (hn : dirs.Nodup)
    (p : Form) (hp : p.totalDegree ≤ dirs.length) :
    dirs.foldl (fun q j => backwardDiff j q) p = C (p.coeff (squarefree dirs.toFinset)) := by
  induction dirs generalizing p with
  | nil =>
    have hz : p.totalDegree = 0 := Nat.eq_zero_of_le_zero hp
    simpa only [List.foldl_nil, List.toFinset_nil, squarefree, Finset.sum_empty] using
      (totalDegree_eq_zero_iff_eq_C.mp hz)
  | cons i dirs ih =>
    have hd := (List.nodup_cons.mp hn)
    have hp' : p.totalDegree ≤ dirs.toFinset.card + 1 := by
      rw [List.toFinset_card_of_nodup hd.2]
      exact hp
    have hnot : i ∉ dirs.toFinset := by simpa using hd.1
    rw [List.foldl_cons, ih hd.2 _ (backwardDiff_degree_le i hp),
      backwardDiff_coeff_squarefree i hnot hp', List.toFinset_cons]

private def window (i : Fin 4) (s : ℕ) (H : Grades → ℝ) (w : Grades) : ℝ :=
  ∑ n ∈ Finset.range s, H (w + Pi.single i n)

private theorem difference_window (F : Grades → ℝ) (i j : Fin 4) (s t : ℕ) :
    gradeDifference (window i s F) j t = window i s (gradeDifference F j t) := by
  funext w
  simp only [gradeDifference, window, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  abel

private theorem difference_telescope (H : Grades → ℝ) (i : Fin 4) (s : ℕ) :
    gradeDifference H i s = window i s (gradeDifference H i 1) := by
  funext w
  induction s with
  | zero => simp [gradeDifference, window]
  | succ s ih =>
    have hs : (w + Pi.single i s) + Pi.single i 1 = w + Pi.single i (s + 1) := by
      rw [add_assoc, ← Pi.single_add]
    rw [window, Finset.sum_range_succ]
    change gradeDifference H i (s + 1) w =
      window i s (gradeDifference H i 1) w + gradeDifference H i 1 (w + Pi.single i s)
    rw [← ih]
    simp only [gradeDifference, hs]
    ring

private theorem differences_window (dirs : List (Fin 4)) (F : Grades → ℝ)
    (i : Fin 4) (s t : ℕ) :
    gradeDifferences dirs t (window i s F) = window i s (gradeDifferences dirs t F) := by
  induction dirs generalizing F with
  | nil => rfl
  | cons j dirs ih =>
    change gradeDifferences dirs t (gradeDifference (window i s F) j t) =
      window i s (gradeDifferences dirs t (gradeDifference F j t))
    rw [difference_window, ih]

private theorem scale_differences (dirs : List (Fin 4)) (N s : ℕ) (F : Grades → ℝ) (d : ℝ)
    (h : ∀ w, (∀ j, N ≤ w j) → gradeDifferences dirs 1 F w = d)
    (w : Grades) (hw : ∀ j, N ≤ w j) :
    gradeDifferences dirs s F w = (s : ℝ) ^ dirs.length * d := by
  induction dirs generalizing F w with
  | nil => simpa [gradeDifferences] using h w hw
  | cons i dirs ih =>
    change ∀ v, (∀ j, N ≤ v j) →
      gradeDifferences dirs 1 (gradeDifference F i 1) v = d at h
    change gradeDifferences dirs s (gradeDifference F i s) w =
      (s : ℝ) ^ (dirs.length + 1) * d
    rw [difference_telescope, differences_window]
    unfold window
    rw [Finset.sum_congr rfl (fun n _ => ih (gradeDifference F i 1) h _
      (large_add hw i n))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
    ring

/-- The indicated squarefree coefficient gives rectangular differences at any common step. -/
theorem mixed_of_polynomial {A : Fin 4 → Set Exponent} {B : Set Exponent} {P : Ideal GeoJets}
    {p : Form}
    (hp : Represents p (fun t => (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℚ)))
    (i : Fin 5) (hd : p.totalDegree ≤ 4 - i.val) (hn : TopNonnegative p) :
    ∃ d : ℝ, 0 ≤ d ∧ IsMixedDegree A B P i.val d := by
  let dirs := remainingDirections i.val
  let inds := dirs.map Fin.castSucc
  let d := p.coeff (squarefree inds.toFinset)
  have hdlen : dirs.length = 4 - i.val := by simp [dirs, remainingDirections]
  have hnDirs : dirs.Nodup := (List.nodup_finRange 4).sublist (List.drop_sublist _ _)
  have hnInds : inds.Nodup := hnDirs.map (Fin.castSucc_injective 4)
  have hdInds : p.totalDegree ≤ inds.length := by simpa [inds, hdlen] using hd
  have hnonneg : 0 ≤ d := by
    apply hn
    rw [squarefree_degree, List.toFinset_card_of_nodup hnInds]
    exact hdInds
  refine ⟨d, by exact_mod_cast hnonneg, ?_⟩
  obtain ⟨N, hN⟩ := hp
  refine ⟨N, fun b w s hb hw => ?_⟩
  have he (v : Grades) (hv : ∀ j, N ≤ v j) :
      hilbert A B P b v =
        (eval (fun j => ((grade b v + 0) j : ℚ)) p : ℝ) := by
    have hlarge (j : Fin 5) : N ≤ grade b v j := by
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using hb
      · simpa using hv k
    have h := hN (grade b v) hlarge
    change eval (fun j => (grade b v j : ℚ)) p =
      (hilbertRank A B P (grade b v (Fin.last 4)) (fun j => grade b v j.castSucc) : ℚ) at h
    simpa only [add_zero, grade_last, grade_cut, Rat.cast_natCast, hilbert] using
      congrArg (fun x : ℚ => (x : ℝ)) h.symm
  obtain ⟨u, hu⟩ := unit_differences_eval b N dirs (hilbert A B P b) p 0 he
  have hc (v : Grades) (hv : ∀ j, N ≤ v j) :
      gradeDifferences dirs 1 (hilbert A B P b) v = (d : ℝ) := by
    rw [hu v hv, fold_backward_eq_const inds hnInds p hdInds, eval_C]
  simpa only [hdlen] using scale_differences dirs N s (hilbert A B P b) (d : ℝ) hc w hw

end
end K1_13_7_1_1_1_1
end PackSource_K1_13_7_1_1_1_1Differences

section PackSource_K1_13_4_3_2Proof
set_option autoImplicit true
namespace K1_13_4_3_2

noncomputable section

open K1 K1_13 K1_13_4 K1_13_4_3
open scoped Polynomial BigOperators

/-- The forward affine substitution over a chosen seed coefficient ring. -/
private def restoreVars {R : Type*} [CommRing R] (z : R) (H res : R[X]) :
    SeedVar → MvPolynomial (Fin 3) R[X] :=
  fun i => i.elim (MvPolynomial.C (Polynomial.C z)) (fun j =>
    MvPolynomial.C (Polynomial.hasseDeriv j.val res) +
      ∑ k : Fin 3, if k.val ≤ j.val then
        MvPolynomial.C (Polynomial.hasseDeriv (j.val - k.val) H) * MvPolynomial.X k
      else 0)

private def restoreWith {R : Type*} [CommRing R] (f : Geom →+* R)
    (z : R) (H res : R[X]) : PhysicalRow →+* MvPolynomial (Fin 3) R[X] :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Polynomial.mapRingHom f))
    (restoreVars z H res)

private theorem map_restoreWith {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (f : Geom →+* R) (z : R) (H res : R[X]) (F : PhysicalRow) :
    MvPolynomial.map (Polynomial.mapRingHom g) (restoreWith f z H res F) =
      restoreWith (g.comp f) (g z) (H.map g) (res.map g) F := by
  have he : (MvPolynomial.map (Polynomial.mapRingHom g)).comp (restoreWith f z H res) =
      restoreWith (g.comp f) (g z) (H.map g) (res.map g) := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [restoreWith, Polynomial.map_map]
    · intro i
      cases i <;> simp [restoreWith, restoreVars, Polynomial.hasseDeriv_map, apply_ite]
  exact DFunLike.congr_fun he F

private theorem restoreAt_eq (H res : Geom[X]) (z : Geom) (F : PhysicalRow) :
    restoreAt H res z F = restoreWith (RingHom.id Geom) z H res F := by
  have he : (restoreJets H res).comp (atSeed (Polynomial.C z)) =
      restoreWith (RingHom.id Geom) z H res := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [restoreWith, atSeed, restoreJets]
    · intro i
      cases i <;> simp [restoreWith, restoreVars, atSeed, restoreJets, jet]
  exact DFunLike.congr_fun he F

private abbrev LocalSeed (d : Geom[X]) := Localization.Away d

private abbrev seedMap (d : Geom[X]) : Geom[X] →+* LocalSeed d := algebraMap _ _

private def seedLift {S : Type*} [Field S] {d : Geom[X]} (g : Geom[X] →+* S)
    (hg : g d ≠ 0) : LocalSeed d →+* S :=
  IsLocalization.Away.lift d (isUnit_iff_ne_zero.mpr hg)

@[simp] private theorem seedLift_comp {S : Type*} [Field S] {d : Geom[X]}
    (g : Geom[X] →+* S) (hg : g d ≠ 0) :
    (seedLift g hg).comp (seedMap d) = g :=
  IsLocalization.Away.lift_comp d _

@[simp] private theorem seedLift_apply {S : Type*} [Field S] {d : Geom[X]}
    (g : Geom[X] →+* S) (hg : g d ≠ 0) (a : Geom[X]) :
    seedLift g hg (seedMap d a) = g a :=
  IsLocalization.Away.lift_eq d _ a

private theorem seedLift_injective {S : Type*} [Field S] {d : Geom[X]}
    (g : Geom[X] →+* S) (hg : g d ≠ 0) (hi : Function.Injective g) :
    Function.Injective (seedLift g hg) := by
  have hd : d ≠ 0 := fun h => hg (by simp [h])
  have ha : Function.Injective (seedMap d) :=
    IsLocalization.injective (LocalSeed d) (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  unfold seedLift IsLocalization.Away.lift
  exact (IsLocalization.lift_injective_iff _).mpr fun x y => ha.eq_iff.trans hi.eq_iff.symm

private def localResidue (n : Geom[X][X]) (d : Geom[X]) : (LocalSeed d)[X] :=
  Polynomial.C (IsLocalization.Away.invSelf d) * n.map (seedMap d)

private theorem map_localResidue {S : Type*} [Field S] {d : Geom[X]}
    (g : Geom[X] →+* S) (hg : g d ≠ 0) (n : Geom[X][X]) :
    (localResidue n d).map (seedLift g hg) = Polynomial.C ((g d)⁻¹) * n.map g := by
  have h := congrArg (seedLift g hg) (IsLocalization.Away.mul_invSelf (S := LocalSeed d) d)
  change seedLift g hg (seedMap d d * IsLocalization.Away.invSelf d) = seedLift g hg 1 at h
  rw [map_mul, map_one, seedLift_apply] at h
  simp [localResidue, Polynomial.map_map, eq_inv_of_mul_eq_one_right h]

/-- Monic remainders descend through the injective map to the generic seed
field. Then the full pole power divides after evaluation at a regular seed. -/
private theorem specialized_dvd {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (r : ℕ) (F : PhysicalRow) (z : Geom) (hz : L.denominator.eval z ≠ 0)
    (hF : (MvPolynomial.C (liftX P.H)) ^ r ∣ restore P L F) :
    MvPolynomial.C (P.H ^ r) ∣
      restoreAt P.H (residueAt L.numerator L.denominator z) z F := by
  let d := L.denominator
  let f := (seedMap d).comp (Polynomial.C : Geom →+* Geom[X])
  let HH := P.H.map f
  let D := HH ^ r
  let A := restoreWith f (seedMap d Polynomial.X) HH (localResidue L.numerator d) F
  let gf : Geom[X] →+* GenericSeed := algebraMap _ _
  let ev := Polynomial.evalRingHom z
  let hg : gf d ≠ 0 := by
    intro h
    have hd : d = 0 :=
      (IsFractionRing.injective Geom[X] GenericSeed) (h.trans (map_zero _).symm)
    apply hz
    change d.eval z = 0
    simp [hd]
  let he : ev d ≠ 0 := hz
  let g := seedLift gf hg
  let e := seedLift ev he
  have hgf : g.comp f = algebraMap Geom GenericSeed := by
    dsimp only [g, f]
    rw [← RingHom.comp_assoc, seedLift_comp]
    exact (IsScalarTower.algebraMap_eq Geom Geom[X] GenericSeed).symm
  have hef : e.comp f = RingHom.id Geom := by
    dsimp only [e, f]
    rw [← RingHom.comp_assoc, seedLift_comp]
    apply RingHom.ext
    intro c
    change (Polynomial.C c).eval z = c
    simp
  have hgH : HH.map g = liftX P.H := by
    dsimp only [HH]
    rw [Polynomial.map_map, hgf, K1_13_4.liftX]
  have heH : HH.map e = P.H := by
    dsimp only [HH]
    rw [Polynomial.map_map, hef, Polynomial.map_id]
  have hgA : MvPolynomial.map (Polynomial.mapRingHom g) A = restore P L F := by
    dsimp only [A]
    rw [map_restoreWith, hgf, hgH]
    dsimp only [g]
    rw [seedLift_apply, map_localResidue]
    rfl
  have heA : MvPolynomial.map (Polynomial.mapRingHom e) A =
      restoreAt P.H (residueAt L.numerator d z) z F := by
    dsimp only [A]
    rw [map_restoreWith, hef, heH]
    dsimp only [e]
    rw [seedLift_apply, map_localResidue, restoreAt_eq]
    simp [ev, residueAt]
  have hD : D.Monic := ((P.monic.map f).pow r)
  have hgD : D.map g = (liftX P.H) ^ r := by
    dsimp only [D]
    rw [Polynomial.map_pow, hgH]
  have heD : D.map e = P.H ^ r := by
    dsimp only [D]
    rw [Polynomial.map_pow, heH]
  have hdvd : MvPolynomial.C D ∣ A := by
    apply (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro m
    have hm := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mp
      (show MvPolynomial.C (D.map g) ∣
          MvPolynomial.map (Polynomial.mapRingHom g) A by
        rw [hgA, hgD, map_pow]
        exact hF) m
    rw [MvPolynomial.coeff_map] at hm
    apply (Polynomial.modByMonic_eq_zero_iff_dvd hD).mp
    apply Polynomial.map_injective g (seedLift_injective gf hg (IsFractionRing.injective _ _))
    rw [Polynomial.map_modByMonic g hD, Polynomial.map_zero]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (hD.map g)).mpr hm
  have h := map_dvd (MvPolynomial.map (Polynomial.mapRingHom e)) hdvd
  rw [MvPolynomial.map_C, heA] at h
  change MvPolynomial.C (D.map e) ∣ _ at h
  rwa [heD] at h

private def rawWeight (i : Fin 3) : ℕ := 131071 - i.val

private def trueWeight (h : ℕ) (i : SeedVar) : ℕ :=
  i.elim 0 (fun j => 131071 + h - j.val)

private theorem weight_eq_sum {σ : Type*} (m : σ →₀ ℕ) (w : σ → ℕ) :
    m.weight w = m.sum (fun i e => w i * e) := by
  rw [Finsupp.weight_apply]
  congr 1
  funext i e
  exact Nat.mul_comm _ _

private theorem restore_degree {H res : Geom[X]} (z : Geom) {B : ℕ} {F : PhysicalRow}
    (hres : res.natDegree ≤ H.natDegree) (hF : TrueCut H.natDegree B F) :
    restoreAt H res z F ∈ MvPolynomial.restrictJointDegree rawWeight B := by
  have hf : F ∈ MvPolynomial.restrictJointDegree (trueWeight H.natDegree) B :=
    MvPolynomial.mem_restrictJointDegree.mpr fun m hm => by
      have hw : m.weight (trueWeight H.natDegree) =
          m.sum (fun i e => i.elim 0 (fun j => (131071 + H.natDegree - j.val) * e)) := by
        rw [weight_eq_sum]
        congr 1
        funext i e
        cases i <;> simp [trueWeight]
      rw [hw]
      exact hF m (MvPolynomial.mem_support_iff.mpr hm)
  have hv (i : SeedVar) :
      restoreVars z H res i ∈
        MvPolynomial.restrictJointDegree rawWeight (trueWeight H.natDegree i) := by
    cases i with
    | none =>
      exact MvPolynomial.C_mem_restrictJointDegree _ (by simp)
    | some j =>
      change _ + _ ∈ MvPolynomial.restrictJointDegree rawWeight (131071 + H.natDegree - j.val)
      apply Submodule.add_mem
      · apply MvPolynomial.C_mem_restrictJointDegree
        have hj := j.isLt
        have hd := Polynomial.natDegree_hasseDeriv_le res j.val
        omega
      · apply Submodule.sum_mem
        intro k _
        by_cases hk : k.val ≤ j.val
        · rw [ite_eq_left hk]
          by_cases hd : j.val - k.val ≤ H.natDegree
          · apply MvPolynomial.restrictJointDegree_mono rawWeight _
              (MvPolynomial.mul_mem_restrictJointDegree
                (MvPolynomial.C_mem_restrictJointDegree rawWeight
                  (Polynomial.natDegree_hasseDeriv_le H (j.val - k.val)))
                (MvPolynomial.X_mem_restrictJointDegree rawWeight k le_rfl))
            have hj := j.isLt
            have hk' := k.isLt
            unfold rawWeight
            omega
          · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ (Nat.lt_of_not_ge hd),
              map_zero, zero_mul]
            exact Submodule.zero_mem _
        · rw [ite_eq_right hk]
          exact Submodule.zero_mem _
  rw [restoreAt_eq, restoreWith]
  have he : (MvPolynomial.C.comp (Polynomial.mapRingHom (RingHom.id Geom))) =
      (MvPolynomial.C : Geom[X] →+* Row 3) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.C (p.map (RingHom.id Geom)) = MvPolynomial.C p
    rw [Polynomial.map_id]
  rw [he, MvPolynomial.eval₂Hom_C_eq_bind₁]
  exact MvPolynomial.bind₁_mem_restrictJointDegree hv hf

theorem proof : K1_13_4_3.c2 := by
  intro w Γ s P L box t F hF γ hγ
  let z := P.z γ
  let res := residueAt L.numerator L.denominator z
  let r := box.b + box.j
  obtain ⟨Q, hQ⟩ := specialized_dvd P L r F z (L.regular γ hγ) hF.2.2.2
  refine ⟨Q, ?_, hQ⟩
  have hres : res.natDegree ≤ P.H.natDegree := by
    unfold res residueAt
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans L.small.le)
  have hbound := restore_degree z hres hF.2.1
  rw [hQ] at hbound
  intro m hm
  have hn : Q.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hp : (P.H ^ r) ≠ 0 := pow_ne_zero _ P.monic.ne_zero
  have hc : (MvPolynomial.C (P.H ^ r) * Q).coeff m ≠ 0 := by
    rw [MvPolynomial.coeff_C_mul]
    exact mul_ne_zero hp hn
  have hb := MvPolynomial.mem_restrictJointDegree.mp hbound m hc
  rw [MvPolynomial.coeff_C_mul, Polynomial.natDegree_mul hp hn, Polynomial.natDegree_pow] at hb
  simp only [weight_eq_sum, rawWeight] at hb
  change _ ≤ t + r * P.H.natDegree at hb
  omega

end
end K1_13_4_3_2
end PackSource_K1_13_4_3_2Proof

section PackSource_K1_13_6_3_6Hilbert
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_6

noncomputable section

open K1_13_6 K1_13_6_3 MvPolynomial Filter
open scoped BigOperators

private theorem hilbert_step (I : JetIdeal) (g : GeoJets) (N : ℕ) (hN : g.totalDegree ≤ N) :
    affineHilbertFunction (I ⊔ Ideal.span {g}) N +
      affineHilbertFunction (I.colon {g}) (N - g.totalDegree) ≤ affineHilbertFunction I N := by
  let J : JetIdeal := I ⊔ Ideal.span {g}
  let A : JetIdeal := I.colon {g}
  let q := Ideal.Quotient.factorₐ GeoField (show I ≤ J from le_sup_left)
  let cut : quotientDegreeLE I N →ₗ[GeoField] quotientDegreeLE J N :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change q y.val ∈ _
      rw [← hpy]
      exact mk_mem_quotientDegreeLE hp
  have hcut : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let mul := (quotientMul I g).restrictScalars GeoField
  let emb : quotientDegreeLE A (N - g.totalDegree) →ₗ[GeoField] quotientDegreeLE I N :=
    (mul.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change quotientMul I g y.val ∈ _
      rw [← hpy, quotientMul_mk]
      exact mk_mem_quotientDegreeLE ((totalDegree_mul p g).trans (by omega))
  have hemb (y : quotientDegreeLE A (N - g.totalDegree)) : emb y ∈ LinearMap.ker cut := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change q (quotientMul I g y.val) = 0
    have hex := (LinearMap.exact_iff.mp (quotientMul_exact I g))
    have hm : quotientMul I g y.val ∈
        LinearMap.range (quotientMul I g) := LinearMap.mem_range_self _ _
    rw [← hex] at hm
    exact hm
  have hinj : Function.Injective (emb.codRestrict (LinearMap.ker cut) hemb) := by
    intro x y he
    exact Subtype.ext (quotientMul_injective I g
      (congrArg (fun z => z.val.val) he))
  have hker := LinearMap.finrank_le_finrank_of_injective hinj
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut, finrank_top] at hrank
  change affineHilbertFunction J N + affineHilbertFunction A (N - g.totalDegree) ≤ _
  unfold affineHilbertFunction
  omega

theorem hilbert_coeff_step (I : JetIdeal) (g : GeoJets) (hI : dimension I ≤ 2) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {g})).coeff 2 +
      (affineHilbertPolynomial (I.colon {g})).coeff 2 ≤ (affineHilbertPolynomial I).coeff 2 := by
  let J : JetIdeal := I ⊔ Ideal.span {g}
  let A : JetIdeal := I.colon {g}
  let b := g.totalDegree
  let S := affineHilbertPolynomial J + Polynomial.taylor (-(b : ℚ)) (affineHilbertPolynomial A)
  have hA : dimension A ≤ 2 :=
    (natDegree_affineHilbertPolynomial_le_of_le Ideal.le_colon).trans hI
  have hJ : dimension J ≤ 2 :=
    (natDegree_affineHilbertPolynomial_le_of_le le_sup_left).trans hI
  have hS : S.natDegree ≤ 2 :=
    Polynomial.natDegree_add_le_of_degree_le hJ (by rwa [Polynomial.natDegree_taylor])
  have hc : S.coeff 2 ≤ (affineHilbertPolynomial I).coeff 2 := by
    refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hS hI ?_
    obtain ⟨N₀, h₀⟩ := exists_eval_affineHilbertPolynomial A
    filter_upwards [eventually_eval_affineHilbertPolynomial J, eventually_eval_affineHilbertPolynomial I,
      eventually_ge_atTop (N₀ + b)] with N h₁ h₂ hN
    have hb : b ≤ N := by omega
    simp only [S, Polynomial.eval_add, Polynomial.taylor_eval, h₁, h₂, ← sub_eq_add_neg,
      ← Nat.cast_sub hb, h₀ (N - b) (by omega : N₀ ≤ N - b)]
    exact_mod_cast hilbert_step I g N hb
  simpa only [S, Polynomial.coeff_add, Polynomial.coeff_taylor_of_natDegree_le _ hA] using hc

theorem coeff_two_nonneg (P : JetIdeal) (hP : dimension P ≤ 2) :
    0 ≤ (affineHilbertPolynomial P).coeff 2 :=
  Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
    hP (eventually_eval_affineHilbertPolynomial_nonneg P)

theorem degree_at_least_one (P : JetIdeal) (hP : P ≠ ⊤) (hd : dimension P = 2) :
    1 ≤ affineDegree P := by
  let H := affineHilbertPolynomial P
  change H.natDegree = 2 at hd
  have he (x : ℚ) : H.eval x = H.coeff 0 + H.coeff 1 * x + H.coeff 2 * x ^ 2 := by
    rw [Polynomial.eval_eq_sum_range, hd]
    norm_num [Finset.sum_range_succ]
  obtain ⟨n, hn⟩ := exists_eval_affineHilbertPolynomial P
  have h (j : ℕ) : H.eval ((n + j : ℕ) : ℚ) = affineHilbertFunction P (n + j) :=
    hn _ (Nat.le_add_right ..)
  have hdiff : 2 * H.coeff 2 =
      (affineHilbertFunction P (n + 2) : ℚ) - 2 * (affineHilbertFunction P (n + 1) : ℚ) +
        (affineHilbertFunction P (n + 0) : ℚ) := by
    rw [← h 0, ← h 1, ← h 2, he, he, he]
    push_cast
    ring
  have hdeg : affineDegree P = 2 * H.coeff 2 := by
    change (H.natDegree.factorial : ℚ) * H.leadingCoeff = 2 * H.coeff 2
    rw [Polynomial.leadingCoeff, hd]
    norm_num
  let z : ℤ := (affineHilbertFunction P (n + 2) : ℤ) -
    2 * (affineHilbertFunction P (n + 1) : ℤ) + (affineHilbertFunction P (n + 0) : ℤ)
  have hz : (z : ℚ) = affineDegree P := by
    rw [hdeg, hdiff]
    push_cast [z]
    rfl
  have hp : (0 : ℤ) < z := by
    have hpos : (0 : ℚ) < (z : ℚ) := by rw [hz]; exact affineDegree_pos hP
    exact_mod_cast hpos
  rw [← hz]
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

end

end K1_13_6_3_6
end PackSource_K1_13_6_3_6Hilbert

section PackSource_K1_13_6_1_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_2_1

noncomputable section

open K1_13_6 K1_13_6_3 K1_13_6_3_6 MvPolynomial

private theorem pair_regular {F G : GeoJets} (hrel : IsRelPrime F G) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))

/-- Each minimal prime is obtained by a proper cut of a hypersurface component. -/
private theorem surface_dimension {F G : GeoJets} (hF : F ≠ 0) (hrel : IsRelPrime F G)
    {p : JetIdeal} (hp : (Ideal.span {F} ⊔ Ideal.span {G}).IsMinimalPrime p) :
    dimension p = 2 := by
  let _ : p.IsPrime := hp.isPrime
  let A : JetIdeal := Ideal.span {F}
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
    (show A ≤ p from le_sup_left.trans hp.le)
  let _ : q.IsPrime := hq.isPrime
  have hG : G ∉ q := by
    intro h
    obtain ⟨y, hy, hGy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hq h
    apply hy
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply pair_regular hrel
    change Ideal.Quotient.mk A G * Ideal.Quotient.mk A y = Ideal.Quotient.mk A G * 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hGy, mul_zero]
  have hp' : (q ⊔ Ideal.span {G}).IsMinimalPrime p := by
    refine ⟨⟨hp.isPrime, sup_le hqp (le_sup_right.trans hp.le)⟩, fun r hr hrp => ?_⟩
    exact hp.2 ⟨hr.1, sup_le (hq.le.trans (le_sup_left.trans hr.2))
      (le_sup_right.trans hr.2)⟩ hrp
  have hqdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hq
  rw [Nat.card_fin] at hqdeg
  have hpdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hG hp'
  change dimension q + 1 = 4 at hqdeg
  change dimension p + 1 = dimension q at hpdeg
  omega

/-- The total-degree filtration bounds the quadratic coefficient of the whole intersection. -/
private theorem pair_hilbert {F G : GeoJets} (hF : F ≠ 0) (hrel : IsRelPrime F G)
    (hproper : (Ideal.span {F} : JetIdeal) ≠ ⊤) :
    dimension (Ideal.span {F} ⊔ Ideal.span {G}) ≤ 2 ∧
      2 * (affineHilbertPolynomial (Ideal.span {F} ⊔ Ideal.span {G})).coeff 2 ≤
        (F.totalDegree : ℚ) * (G.totalDegree : ℚ) := by
  let A : JetIdeal := Ideal.span {F}
  have hAdeg := natDegree_affineHilbertPolynomial_span_singleton_add_one hF hproper
  rw [Nat.card_fin] at hAdeg
  have hthree : dimension A = 3 := by
    change dimension A + 1 = 4 at hAdeg
    omega
  have hcoeff : 6 * (affineHilbertPolynomial A).leadingCoeff = (F.totalDegree : ℚ) := by
    have hd : affineDegree A = (F.totalDegree : ℚ) := affineDegree_span_singleton hF
    unfold affineDegree at hd
    rw [show (affineHilbertPolynomial A).natDegree = 3 from hthree] at hd
    norm_num at hd
    exact hd
  have hc := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (I := A) (pair_regular hrel) (b := G.totalDegree) le_rfl
  change (affineHilbertPolynomial A).natDegree = 3 at hthree
  rw [hthree] at hc
  norm_num at hc
  refine ⟨hc.1, ?_⟩
  nlinarith only [hc.2, congrArg (fun x : ℚ => x * G.totalDegree) hcoeff]

/-- At a fixed minimal prime, only cyclic factors with that annihilator survive. -/
private theorem local_hilbert {J p : JetIdeal} (hp : J.IsMinimalPrime p) (hJ : dimension J ≤ 2) :
    ∃ n : ℕ, cycleLength J p hp.isPrime = (n : ℕ∞) ∧
      (n : ℚ) * (affineHilbertPolynomial p).coeff 2 ≤ (affineHilbertPolynomial J).coeff 2 := by
  suffices aux : ∀ I : JetIdeal, J ≤ I →
      ∃ n : ℕ, cycleLength I p hp.isPrime = (n : ℕ∞) ∧
        (n : ℚ) * (affineHilbertPolynomial p).coeff 2 ≤ (affineHilbertPolynomial I).coeff 2
    from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := JetIdeal)) with
  | h I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      exact ⟨0, by simpa using length_eq_zero_of_not_le hp.isPrime (by simpa using hp.isPrime.ne_top),
        by simp [affineHilbertPolynomial_top]⟩
    obtain ⟨g, hg, hprime⟩ := exists_prime_colon I hI
    let A : JetIdeal := I.colon {g}
    let B : JetIdeal := I ⊔ Ideal.span {g}
    have hIA : I ≤ A := Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨n, hn, hbound⟩ := ih B hIB (hJI.trans hIB.le)
    have hdI := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hJ
    have hc : (affineHilbertPolynomial B).coeff 2 + (affineHilbertPolynomial A).coeff 2 ≤
        (affineHilbertPolynomial I).coeff 2 := hilbert_coeff_step I g hdI
    have hlen : cycleLength I p hp.isPrime = cycleLength A p hp.isPrime + cycleLength B p hp.isPrime :=
      length_step I p hp.isPrime g
    rw [hn] at hlen
    by_cases heq : A = p
    · have hA : cycleLength A p hp.isPrime = 1 := by
        rw [heq]
        exact length_self p hp.isPrime
      refine ⟨n + 1, by simpa [hA, add_comm] using hlen, ?_⟩
      rw [heq] at hc
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [hbound, hc]
    · have hA : cycleLength A p hp.isPrime = 0 := length_eq_zero_of_not_le hp.isPrime
        (fun hAp => heq (le_antisymm hAp (hp.2 ⟨hprime, hJI.trans hIA⟩ hAp)))
      refine ⟨n, by simpa [hA] using hlen, ?_⟩
      have hnonneg := coeff_two_nonneg A
        ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdI)
      linarith only [hbound, hc, hnonneg]

theorem proof : K1_13_6_1_2.c1 := by
  intro F G p hp hF hrel
  have hspan : (Ideal.span {F, G} : JetIdeal) = Ideal.span {F} ⊔ Ideal.span {G} := by
    rw [← Ideal.span_union]
    rfl
  rw [hspan] at hp ⊢
  have hproper : (Ideal.span {F} : JetIdeal) ≠ ⊤ :=
    ne_top_of_le_ne_top hp.isPrime.ne_top (le_sup_left.trans hp.le)
  obtain ⟨hJ, hupper⟩ := pair_hilbert hF hrel hproper
  obtain ⟨n, hn, hlocal⟩ := local_hilbert hp hJ
  have hd := surface_dimension hF hrel hp
  have hdeg : 1 ≤ 2 * (affineHilbertPolynomial p).coeff 2 := by
    have h := degree_at_least_one p hp.isPrime.ne_top hd
    unfold affineDegree at h
    rw [Polynomial.leadingCoeff, show (affineHilbertPolynomial p).natDegree = 2 from hd] at h
    norm_num at h
    exact h
  have hlower : (n : ℚ) ≤ (n : ℚ) * (2 * (affineHilbertPolynomial p).coeff 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hdeg
  have hnat : n ≤ F.totalDegree * G.totalDegree := by
    exact_mod_cast (show (n : ℚ) ≤ (F.totalDegree : ℚ) * (G.totalDegree : ℚ) by
      linarith only [hlower, hlocal, hupper])
  rw [hn]
  exact_mod_cast hnat

end

end K1_13_6_1_2_1
end PackSource_K1_13_6_1_2_1Proof

section PackSource_K1_13_6_1_3_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_3_1

noncomputable section

open K1_13 K1_13_6

/-- A prime minimal over the auxiliary pair has height two, so it cannot lie
strictly below the original component, whose height is at most two. -/
private theorem auxiliary_minimal {F G Q : GeoJets} {S : Ideal GeoJets}
    (hF : F ≠ 0) (hrel : IsRelPrime F G) (hS : (Ideal.span {F, Q}).IsMinimalPrime S)
    (hG : G ∈ S) : (Ideal.span {F, G}).IsMinimalPrime S := by
  let _ : S.IsPrime := hS.isPrime
  have hpair : Ideal.span {F, G} ≤ S := by
    apply Ideal.span_le.mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hS.le (Ideal.subset_span (by simp)), hG⟩
  obtain ⟨T, hT, hTS⟩ := Ideal.exists_minimalPrimes_le hpair
  let _ : T.IsPrime := hT.isPrime
  have hTheight := K1_13_6_1_2.pair_height hF hrel hT
  have hcard : ({F, Q} : Set GeoJets).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hSheight : S.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hS).trans
      (by exact_mod_cast hcard)
  have heq : T = S := by
    apply eq_of_le_of_not_lt hTS
    intro hstrict
    have h := (Ideal.height_add_one_le_of_lt_of_isPrime hstrict).trans hSheight
    norm_num [hTheight] at h
  change (Ideal.span {F, G}).IsMinimalPrime T at hT
  rwa [heq] at hT

theorem proof : K1_13_6_1_3.c1 := by
  intro f P Q S hrel hS hP
  have hf : toGeneric f ≠ 0 := by
    intro hz
    have hunit := hrel (show toGeneric P ∣ toGeneric f by simp [hz]) (dvd_refl _)
    exact hS.isPrime.ne_top (S.eq_top_of_isUnit_mem hP hunit)
  have hZ : (intersectionIdeal f P).IsMinimalPrime S := auxiliary_minimal hf hrel hS hP
  have hup := K1_13_6_1_2_1.proof _ _ S hZ hf hrel
  have hdeg (g : Row 4) : (toGeneric g).totalDegree ≤ (shape g).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hupper : cycleLength (intersectionIdeal f P) S hZ.isPrime ≤
      (↑((shape f).b * (shape P).b) : ℕ∞) :=
    hup.trans (by exact_mod_cast Nat.mul_le_mul (hdeg f) (hdeg P))
  have hfin := ne_of_lt (hupper.trans_lt (ENat.natCast_lt_top _))
  let w := (cycleLength (intersectionIdeal f P) S hZ.isPrime).toNat
  have hw : cycleLength (intersectionIdeal f P) S hZ.isPrime = (w : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hpos := K1_13_6_1_2.cycleLength_pos hZ.isPrime hZ.le
  rw [hw] at hpos hupper
  exact ⟨hZ, w, by exact_mod_cast hpos, by exact_mod_cast hupper, hw⟩

end
end K1_13_6_1_3_1
end PackSource_K1_13_6_1_3_1Proof

section PackSource_K1_13_6_3_6Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_6

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped BigOperators

/-- Ascend through cyclic prime factors. At a fixed minimal prime only the
factors with that same annihilator survive localization. -/
private theorem coefficient_budget (J : JetIdeal) (hd : dimension J ≤ 2) : by
    classical
    exact (∀ P (hp : J.IsMinimalPrime P), cycleLength J P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ J.minimalPrimesFinset,
        (cycleWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial J).coeff 2 := by
  classical
  let T := J.minimalPrimesFinset
  suffices aux : ∀ I : JetIdeal, J ≤ I →
      (∀ P (hp : J.IsMinimalPrime P), cycleLength I P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ T, (cycleWeight I P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial I).coeff 2 from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := JetIdeal)) with
  | h I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      have hz (P : JetIdeal) (hp : P.IsPrime) : cycleLength ⊤ P hp = 0 :=
        length_eq_zero_of_not_le hp (by simpa using hp.ne_top)
      exact ⟨fun P hp => by simp [hz P hp.isPrime], by
        refine le_of_eq ?_
        simp only [cycleWeight, affineHilbertPolynomial_top, Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro P hP
        have hp := (Ideal.mem_minimalPrimesFinset.mp hP).isPrime
        simp [dite_eq_left hp, hz P hp]⟩
    obtain ⟨g, hg, hprime⟩ := exists_prime_colon I hI
    let A : JetIdeal := I.colon {g}
    let B : JetIdeal := I ⊔ Ideal.span {g}
    have hIA : I ≤ A := Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨hfin, hbudget⟩ := ih B hIB (hJI.trans hIB.le)
    have hstep (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength I P hp.isPrime =
          cycleLength A P hp.isPrime + cycleLength B P hp.isPrime :=
      length_step I P hp.isPrime g
    have hterm (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime = if P = A then 1 else 0 := by
      split_ifs with h
      · subst P
        exact length_self A hp.isPrime
      · exact length_eq_zero_of_not_le hp.isPrime
          (fun hAP => h (le_antisymm (hp.2 ⟨hprime, hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P : JetIdeal) (hP : P ∈ T) :
        (cycleWeight I P : ℚ) = (cycleWeight B P : ℚ) + (if P = A then 1 else 0) := by
      have hp := Ideal.mem_minimalPrimesFinset.mp hP
      simp only [cycleWeight, dite_eq_left hp.isPrime]
      rw [hstep P hp, ENat.toNat_add (hfinite P hp) (hfin P hp), hterm P hp, Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp => by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp, hfin P hp⟩, ?_⟩
    calc
      _ = (∑ P ∈ T, (cycleWeight B P : ℚ) * (affineHilbertPolynomial P).coeff 2) +
          (if A ∈ T then (affineHilbertPolynomial A).coeff 2 else 0) := by
        rw [← Finset.sum_ite_eq' T A (fun P => (affineHilbertPolynomial P).coeff 2),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP, add_mul, ite_mul, one_mul, zero_mul]
      _ ≤ (affineHilbertPolynomial B).coeff 2 + (affineHilbertPolynomial A).coeff 2 := by
        apply add_le_add hbudget
        split_ifs
        · exact le_rfl
        · exact coeff_two_nonneg A ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdim)
      _ ≤ _ := hilbert_coeff_step I g hdim

theorem proof : K1_13_6_3.c6 := by
  classical
  intro f Q hf hQ hbox
  let J := intersectionIdeal f Q
  obtain ⟨hj, hd⟩ := intersection_hilbert hf hQ
  obtain ⟨hfin, hcoeff⟩ := coefficient_budget J hj
  have hdim (P : JetIdeal) (hp : J.IsMinimalPrime P) : dimension P = 2 :=
    surface_dimension hf hQ hp
  have hb : (shape Q).b ≤ cutterBox.b := hbox.1.trans (by decide)
  have hw : ∑ P ∈ J.minimalPrimesFinset, (cycleWeight J P : ℚ) * affineDegree P ≤
      ((shape f).b * cutterBox.b : ℕ) := by
    calc
      _ = 2 * ∑ P ∈ J.minimalPrimesFinset,
          (cycleWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have hp := hdim P (Ideal.mem_minimalPrimesFinset.mp hP)
        simp only [affineDegree, Polynomial.leadingCoeff, hp]
        norm_num
        ring
      _ ≤ (shape f).b * (shape Q).b := (mul_le_mul_of_nonneg_left hcoeff (by norm_num)).trans hd
      _ ≤ ((shape f).b * cutterBox.b : ℕ) := by
        push_cast
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb) (by positivity)
  refine ⟨?_, hw⟩
  intro P hp
  refine ⟨hdim P hp, length_pos hp.isPrime hp.le, ?_⟩
  have hsingle := Finset.single_le_sum
    (f := fun P => (cycleWeight J P : ℚ) * affineDegree P)
    (fun P _ => mul_nonneg (by positivity) (affineDegree_nonneg P))
    (Ideal.mem_minimalPrimesFinset.mpr hp)
  have hnat : cycleWeight J P ≤ (shape f).b * cutterBox.b := by
    exact_mod_cast (le_mul_of_one_le_right (by positivity : 0 ≤ (cycleWeight J P : ℚ))
      (degree_at_least_one P hp.isPrime.ne_top (hdim P hp))).trans (hsingle.trans hw)
  have hen : (cycleWeight J P : ℕ∞) = cycleLength J P hp.isPrime := by
    simp only [cycleWeight, dite_eq_left hp.isPrime]
    exact ENat.natCast_toNat (hfin P hp)
  rw [← hen]
  exact_mod_cast hnat

end

end K1_13_6_3_6
end PackSource_K1_13_6_3_6Proof

section PackSource_K1_13_7_2_5_4_1Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_2_5_4_1

noncomputable section

open K1_13 K1_13_6_3 K1_13_6_3_4 K1_13_7_2_5_4 MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Associated primes supported at the cone vertex can only obstruct
injectivity in finitely many homogeneous degrees. -/
def c1 : Prop :=
  ∀ {k σ : Type} [Field k] [Finite σ] (B : Ideal (MvPolynomial σ k))
    (ℓ : MvPolynomial σ k),
    B.IsHomogeneous (homogeneousSubmodule σ k) → ℓ.IsHomogeneous 1 →
    (∀ P ∈ associatedPrimes (MvPolynomial σ k) (MvPolynomial σ k ⧸ B),
      (∃ i : σ, MvPolynomial.X i ∉ P) → ℓ ∉ P) →
    EventuallyRegularHomogeneous B ℓ

/-- An affine regular cut with filter-regular slope yields the exact
first difference of the affine Hilbert polynomial. -/
def c2 : Prop :=
  ∀ {k σ : Type} [Field k] [Finite σ] (I : Ideal (MvPolynomial σ k))
    (a : k) (ℓ : MvPolynomial σ k),
    ℓ.IsHomogeneous 1 → IsLeftRegular (Ideal.Quotient.mk I (C a + ℓ)) →
    EventuallyRegularHomogeneous (boundaryIdeal I) ℓ →
    affineHilbertPolynomial (cut I (C a + ℓ)) =
      Polynomial.backwardDifference 1 (affineHilbertPolynomial I)

private theorem backwardDifference_degree {k σ : Type} [Field k] [Finite σ]
    (I J : Ideal (MvPolynomial σ k)) (hI : 0 < dimension I)
    (h : affineHilbertPolynomial J = Polynomial.backwardDifference 1 (affineHilbertPolynomial I)) :
    dimension J = dimension I - 1 ∧ affineDegree J = affineDegree I := by
  obtain ⟨hd, hc⟩ := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (one_ne_zero : (1 : ℚ) ≠ 0) hI
  refine ⟨by simp only [dimension, h, hd], ?_⟩
  have hsucc : dimension I - 1 + 1 = dimension I := by omega
  have hfact := congrArg Nat.factorial hsucc
  rw [Nat.factorial_succ, hsucc] at hfact
  rw [affineDegree, affineDegree, h, hd, hc, one_mul]
  change _ = ((dimension I).factorial : ℚ) * _
  rw [← hfact, Nat.cast_mul]
  ring

private theorem next_slice (h1 : c1) (h2 : c2) (A : CoeffIdeal)
    (d : FreshCoeffRing) (hd : IsLeftRegular (Ideal.Quotient.mk (extendIdeal A) d))
    (hA : 0 < dimension A) :
    ∃ H : CoeffHyperplane,
      IsLeftRegular (Ideal.Quotient.mk (extendIdeal A) H.freshForm) ∧
      IsLeftRegular (Ideal.Quotient.mk (extendIdeal (coefficientSurface A H)) d) ∧
      dimension (coefficientSurface A H) = dimension A - 1 ∧
      affineDegree (extendIdeal (coefficientSurface A H)) = affineDegree (extendIdeal A) := by
  let I := extendIdeal A
  obtain ⟨H, hp, hq, hb⟩ := exists_slice I (cut I d) (boundaryIdeal I)
  have hf := regular_of_avoids_associated I H.freshForm hp
  have hfd := regular_of_avoids_associated (cut I d) H.freshForm hq
  have he : extendIdeal (coefficientSurface A H) = cut I H.freshForm := extend_cut A H
  have hm := h1 (boundaryIdeal I) (freshSlope H) (boundary_homogeneous I)
    (freshSlope_homogeneous H) hb
  have hform : IsLeftRegular (Ideal.Quotient.mk I (C (geomConstants H.offset) + freshSlope H)) := by
    rwa [← freshForm_eq H]
  have hpoly := h2 I _ _ (freshSlope_homogeneous H) hform hm
  rw [← freshForm_eq H, ← he] at hpoly
  have hAext : 0 < dimension I := by
    change 0 < (affineHilbertPolynomial (extendIdeal A)).natDegree
    rw [K1_13_6_3_4_1.proof A]
    exact hA
  obtain ⟨hdim, hdeg⟩ := backwardDifference_degree I _ hAext hpoly
  refine ⟨H, hf, he.symm ▸ denominator_regular_after_cut I d H.freshForm hd hfd, ?_, hdeg⟩
  change (affineHilbertPolynomial (extendIdeal (coefficientSurface A H))).natDegree =
    (affineHilbertPolynomial (extendIdeal A)).natDegree - 1 at hdim
  rw [K1_13_6_3_4_1.proof, K1_13_6_3_4_1.proof] at hdim
  exact hdim

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_2_5_4.c1 := by
  intro A _ hprime hdim d hd
  let : (extendIdeal A).IsPrime := hprime
  have hreg : IsLeftRegular (Ideal.Quotient.mk (extendIdeal A) d) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hd)
  obtain ⟨H, hH, hdH, hdimH, hdegH⟩ := next_slice h1 h2 A d hreg (by omega)
  let U := coefficientSurface A H
  have hU : dimension U = 2 := by dsimp [U]; omega
  obtain ⟨G, hG, hdG, hdimG, hdegG⟩ := next_slice h1 h2 U d hdH (by omega)
  let V := coefficientCurve A H G
  have hV : dimension V = 1 := by
    change dimension (coefficientSurface U G) = 1
    omega
  have hs : retainedSurface A d H = extendIdeal U := saturate_eq_of_regular _ _ hdH
  have ht : retainedCurve A d H G = extendIdeal V := saturate_eq_of_regular _ _ hdG
  refine ⟨⟨H, G, ?_, hs.symm ▸ hG, ?_, ?_, boundary_charts_of_curve V hV⟩⟩
  · intro hh
    have hz : Ideal.Quotient.mk (extendIdeal A) H.freshForm = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hh
    rw [hz] at hH
    have heq : (0 : FreshCoeffRing ⧸ extendIdeal A) * 0 = 0 * 1 := by simp
    exact zero_ne_one (hH heq)
  · rw [ht]
    change (affineHilbertPolynomial (extendIdeal V)).natDegree = 1
    rwa [K1_13_6_3_4_1.proof]
  · rw [ht]
    calc
      affineDegree (extendIdeal V) = affineDegree (extendIdeal U) := hdegG
      _ = affineDegree (extendIdeal A) := hdegH
      _ = affineDegree A := by rw [affineDegree, affineDegree, K1_13_6_3_4_1.proof]

end
end K1_13_7_2_5_4_1
end PackSource_K1_13_7_2_5_4_1Split

section PackSource_K1_13_7_2_5_4_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_2_5_4_1_1

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type} [Field k]

/-- The kernel of multiplication by the slope is killed by a power of
the ideal generated by the variables. -/
private theorem exists_vertex_power_annihilates [Finite σ]
    (B : Ideal (MvPolynomial σ k)) (ℓ : MvPolynomial σ k)
    (hAvoid : ∀ P ∈ associatedPrimes (MvPolynomial σ k) (MvPolynomial σ k ⧸ B),
      (∃ i : σ, MvPolynomial.X i ∉ P) → ℓ ∉ P) :
    ∃ t : ℕ, ∀ a ∈ idealOfVars σ k ^ t, ∀ g, ℓ * g ∈ B → a * g ∈ B := by
  let R := MvPolynomial σ k
  let K := LinearMap.ker (LinearMap.lsmul R (R ⧸ B) ℓ)
  have hℓ : ℓ ∈ Module.annihilator R K := Module.mem_annihilator.mpr fun x ↦
    Subtype.ext (LinearMap.mem_ker.mp x.property)
  have hrad : idealOfVars σ k ≤ (Module.annihilator R K).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    have hPK := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R K hP
    have hPQ : P ∈ associatedPrimes R (R ⧸ B) :=
      associatedPrimes.subset_of_injective K.subtype_injective hPK
    have hle : Module.annihilator R K ≤ P := by
      simpa only [Submodule.annihilator_top] using hPK.annihilator_le
    by_contra hi
    exact hAvoid P hPQ ⟨i, hi⟩ (hle hℓ)
  obtain ⟨t, ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ k)
  refine ⟨t, fun a ha g hg ↦ ?_⟩
  have hgK : Ideal.Quotient.mk B g ∈ K := by
    change Ideal.Quotient.mk B (ℓ * g) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
  have haK := Module.mem_annihilator.mp (ht ha) (⟨Ideal.Quotient.mk B g, hgK⟩ : K)
  have hzero : Ideal.Quotient.mk B (a * g) = 0 := congrArg Subtype.val haK
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- High-degree monomials in a multiplier already send the generator into
`B`. Low-degree monomials cannot reach degree `n`. -/
private theorem component_mul_mem_of_vertex_power
    {B : Ideal (MvPolynomial σ k)} (hB : B.IsHomogeneous (homogeneousSubmodule σ k))
    {t n : ℕ} (a g : MvPolynomial σ k) (hn : t + g.totalDegree ≤ n)
    (hann : ∀ b ∈ idealOfVars σ k ^ t, b * g ∈ B) :
    homogeneousComponent n (a * g) ∈ B := by
  classical
  nth_rw 1 [← a.support_sum_monomial_coeff]
  rw [Finset.sum_mul, map_sum]
  apply B.sum_mem
  intro d hd
  by_cases h : t ≤ d.degree
  · exact homogeneousComponent_mem_of_mem hB
      (hann _ ((monomial_mem_pow_idealOfVars_iff t d (mem_support_iff.mp hd)).mpr h)) n
  · have hdeg : (monomial d (a.coeff d) * g).totalDegree < n :=
      (totalDegree_mul _ _).trans_lt
        ((Nat.add_lt_add_right ((totalDegree_monomial_le d _).trans_lt (Nat.lt_of_not_ge h))
          _).trans_le hn)
    rw [homogeneousComponent_eq_zero n _ hdeg]
    exact B.zero_mem

theorem proof : K1_13_7_2_5_4_1.c1 := by
  classical
  intro k σ _ _ B ℓ hB _ hAvoid
  let R := MvPolynomial σ k
  let J : Ideal R := B.colon {ℓ}
  have hJ (g : R) : g ∈ J ↔ ℓ * g ∈ B := by
    change g ∈ B.colon {ℓ} ↔ _
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  obtain ⟨t, ht⟩ := exists_vertex_power_annihilates B ℓ hAvoid
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  have hgen (i : Fin m) : ℓ * g i ∈ B :=
    (hJ _).mp (hg ▸ Submodule.subset_span (Set.mem_range_self i))
  let D := Finset.univ.sup fun i : Fin m ↦ (g i).totalDegree
  refine ⟨t + D, fun n hn q hq hℓq ↦ ?_⟩
  have hqJ : q ∈ Submodule.span R (Set.range g) := hg.symm ▸ (hJ _).mpr hℓq
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hqJ
  rw [← homogeneousComponent_eq_self hq, ← ha, map_sum]
  apply B.sum_mem
  intro i _
  have hdeg : (g i).totalDegree ≤ D :=
    Finset.le_sup (f := fun j ↦ (g j).totalDegree) (Finset.mem_univ i)
  exact component_mul_mem_of_vertex_power hB (a i) (g i)
    ((Nat.add_le_add_left hdeg t).trans hn) (fun b hb ↦ ht b hb _ (hgen i))

end K1_13_7_2_5_4_1_1
end PackSource_K1_13_7_2_5_4_1_1Proof

section PackSource_K1_13_7_2_5_4_1_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_2_5_4_1_2

noncomputable section

open MvPolynomial K1_13_6_3_4 K1_13_7_2_5_4 K1_13_7_2_5_4_1

variable {k σ : Type} [Field k]

private theorem degree_le_of_component_zero {p : MvPolynomial σ k} {m : ℕ}
    (hp : p.totalDegree ≤ m + 1) (hz : homogeneousComponent (m + 1) p = 0) :
    p.totalDegree ≤ m := by
  unfold totalDegree
  refine Finset.sup_le fun d hd ↦ ?_
  have hle := (le_totalDegree hd).trans hp
  have hne : d.degree ≠ m + 1 := by
    intro he
    apply mem_support_iff.mp hd
    simpa [coeff_homogeneousComponent, he] using
      congrArg (fun q : MvPolynomial σ k ↦ q.coeff d) hz
  change d.degree ≤ m
  exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)

private theorem affine_form_degree_le (a : k) {ℓ : MvPolynomial σ k}
    (hℓ : ℓ.IsHomogeneous 1) : (C a + ℓ).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le ((totalDegree_C a).trans_le (by decide)) hℓ.totalDegree_le)

/-- A multiple of the cutting form in filtration degree `n+1` has a
multiplier in filtration degree `n` once the slope is injective at infinity. -/
private theorem reduce_multiplier (I : Ideal (MvPolynomial σ k)) (a : k)
    {ℓ p q : MvPolynomial σ k} (hℓ : ℓ.IsHomogeneous 1) {T n : ℕ}
    (hT : ∀ m ≥ T, ∀ r : MvPolynomial σ k, r.IsHomogeneous m →
      ℓ * r ∈ boundaryIdeal I → r ∈ boundaryIdeal I)
    (hn : T ≤ n + 1) (hp : p.totalDegree ≤ n + 1)
    (hq : p - (C a + ℓ) * q ∈ I) :
    ∃ r : MvPolynomial σ k, r.totalDegree ≤ n ∧ p - (C a + ℓ) * r ∈ I := by
  let g : MvPolynomial σ k := C a + ℓ
  have hg : g.totalDegree ≤ 1 := affine_form_degree_le a hℓ
  suffices lower : ∀ m (q : MvPolynomial σ k), q.totalDegree ≤ m → p - g * q ∈ I →
      ∃ r : MvPolynomial σ k, r.totalDegree ≤ n ∧ p - g * r ∈ I from
    lower q.totalDegree q le_rfl hq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro q hqm hq
    by_cases hmn : m ≤ n
    · exact ⟨q, hqm.trans hmn, hq⟩
    have hhigh : n + 1 ≤ m := by omega
    have hprod : (g * q).totalDegree ≤ m + 1 :=
      (totalDegree_mul _ _).trans (by omega)
    have hdiff : (p - g * q).totalDegree ≤ m + 1 :=
      (totalDegree_sub _ _).trans (max_le (by omega) hprod)
    have hboundary : homogeneousComponent (m + 1) (p - g * q) ∈ boundaryIdeal I :=
      Ideal.subset_span ⟨p - g * q, m + 1, hq, hdiff, rfl⟩
    have hconst : (C a * q).totalDegree < m + 1 :=
      (totalDegree_mul _ _).trans_lt (by rw [totalDegree_C, zero_add]; omega)
    rw [map_sub, homogeneousComponent_eq_zero _ _ (show p.totalDegree < m + 1 by omega),
      show g * q = C a * q + ℓ * q from add_mul _ _ _, map_add,
      homogeneousComponent_eq_zero _ _ hconst, zero_add, component_mul_linear hℓ,
      zero_sub] at hboundary
    have hhom := homogeneousComponent_isHomogeneous m q
    have hlead := hT m (hn.trans hhigh) (homogeneousComponent m q) hhom
      ((boundaryIdeal I).neg_mem_iff.mp hboundary)
    obtain ⟨v, hv, hvm, htop⟩ :=
      K1_13_5_4_4_2.lift_boundary_component I hlead m
    have hbound : (q - v).totalDegree ≤ m :=
      (totalDegree_sub _ _).trans (max_le hqm hvm)
    have hzero : homogeneousComponent m (q - v) = 0 := by
      rw [map_sub, htop, homogeneousComponent_eq_self hhom, sub_self]
    have hm : m - 1 + 1 = m := by omega
    have hsmaller : (q - v).totalDegree ≤ m - 1 := by
      apply degree_le_of_component_zero
      · rwa [hm]
      · rwa [hm]
    apply ih (m - 1) (by omega) (q - v) hsmaller
    convert I.add_mem hq (I.mul_mem_left g hv) using 1
    ring

/-- Rank-nullity for the surjection of filtered pieces, with its kernel
identified by multiplication by the cutting form. -/
private theorem hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k)) (a : k)
    {ℓ : MvPolynomial σ k} (hℓ : ℓ.IsHomogeneous 1)
    (hreg : IsLeftRegular (Ideal.Quotient.mk I (C a + ℓ))) {T n : ℕ}
    (hT : ∀ m ≥ T, ∀ r : MvPolynomial σ k, r.IsHomogeneous m →
      ℓ * r ∈ boundaryIdeal I → r ∈ boundaryIdeal I) (hn : T ≤ n + 1) :
    affineHilbertFunction (cut I (C a + ℓ)) (n + 1) + affineHilbertFunction I n =
      affineHilbertFunction I (n + 1) := by
  let g : MvPolynomial σ k := C a + ℓ
  let J := cut I g
  have hIJ : I ≤ J := le_sup_left
  let factor := Ideal.Quotient.factorₐ k hIJ
  let proj : quotientDegreeLE I (n + 1) →ₗ[k] quotientDegreeLE J (n + 1) :=
    (factor.toLinearMap.domRestrict _).codRestrict _ fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      change factor x.val ∈ _
      rw [← hpx]
      exact mk_mem_quotientDegreeLE hp
  have hsurj : Function.Surjective proj := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  have hg : g.totalDegree ≤ 1 := affine_form_degree_le a hℓ
  let mul : quotientDegreeLE I n →ₗ[k] quotientDegreeLE I (n + 1) :=
    ((LinearMap.mulLeft k (Ideal.Quotient.mk I g)).domRestrict _).codRestrict _ fun x ↦ by
      change Ideal.Quotient.mk I g * x.val ∈ _
      rw [Nat.add_comm n 1]
      exact mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE hg) x.property
  have hmul (x : quotientDegreeLE I n) : mul x ∈ LinearMap.ker proj := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.factor hIJ (Ideal.Quotient.mk I g * x.val) = 0
    have hgJ : g ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hgJ, zero_mul]
  let emb := mul.codRestrict (LinearMap.ker proj) hmul
  have hemb : Function.Bijective emb := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hreg
        (congrArg (fun z : LinearMap.ker proj ↦ (z.val : MvPolynomial σ k ⧸ I)) hxy))
    · intro y
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.val.property
      have hy : factor y.val.val = 0 := congrArg Subtype.val y.property
      rw [← hpy] at hy
      have hpJ : p ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨b, hb, t, ht, hsum⟩ := Submodule.mem_sup.mp hpJ
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ht
      have hq : p - g * q ∈ I := by rwa [← hsum, add_sub_cancel_right]
      obtain ⟨r, hr, hrI⟩ := reduce_multiplier I a hℓ hT hn hp hq
      refine ⟨⟨Ideal.Quotient.mk I r, mk_mem_quotientDegreeLE hr⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change Ideal.Quotient.mk I g * Ideal.Quotient.mk I r = y.val.val
      rw [← map_mul, ← hpy, Ideal.Quotient.eq]
      simpa only [neg_sub] using I.neg_mem hrI
  have hrank := proj.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    ← (LinearEquiv.ofBijective emb hemb).finrank_eq] at hrank
  exact hrank

theorem proof : K1_13_7_2_5_4_1.c2 := by
  intro k σ _ _ I a ℓ hℓ hreg hboundary
  obtain ⟨T, hT⟩ := hboundary
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial I
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max T (M + 1))
  intro N hN
  have hTn : T ≤ N := (le_max_left T (M + 1)).trans hN
  have hMn : M + 1 ≤ N := (le_max_right T (M + 1)).trans hN
  have hsucc : N - 1 + 1 = N := by omega
  have hstep := hilbert_step I a hℓ hreg hT (n := N - 1) (by rwa [hsucc])
  rw [hsucc] at hstep
  have hcast : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
  rw [Polynomial.eval_backwardDifference, ← hcast, hM N (by omega), hM (N - 1) (by omega)]
  apply sub_eq_iff_eq_add.mpr
  exact_mod_cast hstep.symm

end

end K1_13_7_2_5_4_1_2
end PackSource_K1_13_7_2_5_4_1_2Proof

section PackSource_K1_13_6_3_5_5_1Cone
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_5_1

noncomputable section

open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_5

variable {k σ τ C E : Type} [Field k] [CommRing C] [Algebra k C]
  [CommRing E] [Algebra k E]

/-- Evaluate with every chart coordinate multiplied by the homogenizing variable. -/
def scaleEval (g : MvPolynomial σ k →ₐ[k] C) : MvPolynomial σ k →ₐ[k] Polynomial C :=
  aeval (fun i => Polynomial.C (g (MvPolynomial.X i)) * Polynomial.X)

theorem scaleEval_homogeneous (g : MvPolynomial σ k →ₐ[k] C)
    {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n) :
    scaleEval g p = Polynomial.C (g p) * Polynomial.X ^ n := by
  classical
  have hm (d : σ →₀ ℕ) (hd : d.degree = n) (a : k) :
      scaleEval g (monomial d a) = Polynomial.C (g (monomial d a)) * Polynomial.X ^ n := by
    have hg : g (monomial d a) = algebraMap k C a * d.prod (fun i j => g (MvPolynomial.X i) ^ j) := by
      rw [DFunLike.congr_fun (aeval_unique g) (monomial d a), aeval_monomial]
      rfl
    rw [scaleEval, aeval_monomial, hg, Polynomial.algebraMap_apply, map_mul, mul_assoc]
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow,
      Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hd, map_prod]
  calc
    scaleEval g p = ∑ d ∈ p.support, scaleEval g (monomial d (p.coeff d)) := by
      rw [← map_sum, ← p.as_sum]
    _ = ∑ d ∈ p.support, Polynomial.C (g (monomial d (p.coeff d))) * Polynomial.X ^ n := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hm d (by simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hd).symm) (p.coeff d)
    _ = Polynomial.C (g p) * Polynomial.X ^ n := by
      rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← p.as_sum]

theorem scaleEval_coeff (g : MvPolynomial σ k →ₐ[k] C) (p : MvPolynomial σ k) (n : ℕ) :
    (scaleEval g p).coeff n = g (homogeneousComponent n p) := by
  classical
  have h : scaleEval g p =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        Polynomial.C (g (homogeneousComponent i p)) * Polynomial.X ^ i := by
    calc
      scaleEval g p = ∑ i ∈ Finset.range (p.totalDegree + 1),
          scaleEval g (homogeneousComponent i p) := by
        rw [← map_sum, sum_homogeneousComponent]
      _ = _ := Finset.sum_congr rfl fun i _ =>
        scaleEval_homogeneous g (homogeneousComponent_isHomogeneous i p)
  rw [h, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n ≤ p.totalDegree
  · rw [Finset.sum_eq_single n]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · intro hnot
      exact (hnot (Finset.mem_range_succ_iff.mpr hn)).elim
  · rw [homogeneousComponent_eq_zero n p (lt_of_not_ge hn), map_zero]
    exact Finset.sum_eq_zero fun i hi => by
      have hi' := Finset.mem_range_succ_iff.mp hi
      simp [show n ≠ i by omega]

/-- Sending the homogenizing variable to one dehomogenizes a cone equation. -/
def dehom : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval (fun i => i.elim 1 MvPolynomial.X)

theorem dehom_totalDegree_le (p : MvPolynomial (Option σ) k) :
    (dehom p).totalDegree ≤ p.totalDegree := by
  let T := restrictTotalDegree σ k
  have hT : Monotone T := fun _ _ h _ hp =>
    (mem_restrictTotalDegree _ _ _).2 (((mem_restrictTotalDegree _ _ _).1 hp).trans h)
  have h1 : (1 : MvPolynomial σ k) ∈ T 0 := (mem_restrictTotalDegree _ _ _).2 (by simp)
  have hm : ∀ i : Option σ, ∀ n t, t ∈ T n → i.elim 1 MvPolynomial.X * t ∈ T (n + 1) := by
    intro i n t ht
    cases i with
    | none => simpa using hT (Nat.le_succ n) ht
    | some i =>
      refine (mem_restrictTotalDegree _ _ _).2 ((totalDegree_mul _ _).trans ?_)
      simpa [totalDegree_X, Nat.add_comm] using Nat.add_le_add_left
        ((mem_restrictTotalDegree _ _ _).1 ht) 1
  have h := aeval_mem_of_forall_mul_mem (fun i : Option σ => i.elim 1 MvPolynomial.X)
    hT h1 hm (q := p) le_rfl
  exact (mem_restrictTotalDegree _ _ _).1 (by simpa [dehom] using h)

/-- Affine cone parametrization using the shared homogenizing variable. -/
def coneEval (e : Polynomial C →ₐ[k] E) (g : MvPolynomial σ k →ₐ[k] C) :
    MvPolynomial (Option σ) k →ₐ[k] E :=
  e.comp (scaleEval (g.comp dehom))

abbrev Cone (e : Polynomial C →ₐ[k] E) (g : MvPolynomial σ k →ₐ[k] C) :=
  (coneEval e g).range

variable (e : Polynomial C →ₐ[k] E) (g : MvPolynomial σ k →ₐ[k] C)

@[simp] theorem coneEval_X_none : coneEval e g (MvPolynomial.X none) = e Polynomial.X := by
  simp [coneEval, dehom, scaleEval]

@[simp] theorem coneEval_X_some (i : σ) :
    coneEval e g (MvPolynomial.X (some i)) = e (Polynomial.C (g (MvPolynomial.X i)) * Polynomial.X) := by
  simp [coneEval, dehom, scaleEval]

/-- The common linear coordinate on the cone. -/
def w : Cone e g := ⟨e Polynomial.X, ⟨MvPolynomial.X none, coneEval_X_none e g⟩⟩

@[simp] theorem coe_w : (w e g : E) = e Polynomial.X := rfl

/-- Homomorphism obtained by scaling just the original chart generators. -/
def scaled : MvPolynomial σ k →ₐ[k] Cone e g :=
  (coneEval e g).rangeRestrict.comp (rename some)

theorem coe_scaled (p : MvPolynomial σ k) : (scaled e g p : E) = e (scaleEval g p) := by
  have h : (coneEval e g).comp (rename some) = e.comp (scaleEval g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [scaleEval]
  exact DFunLike.congr_fun h p

/-- Every possible coefficient on the cone lifts to a chart polynomial of bounded degree. -/
theorem coneCoeff (a : Cone e g) (n : ℕ) :
    ∃ b : Polynomial C, e b = (a : E) ∧
      ∃ p : MvPolynomial σ k, p.totalDegree ≤ n ∧ g p = b.coeff n := by
  obtain ⟨q, hq⟩ := a.property
  refine ⟨scaleEval (g.comp dehom) q, hq, dehom (homogeneousComponent n q), ?_, ?_⟩
  · exact (dehom_totalDegree_le (homogeneousComponent n q)).trans
      (homogeneousComponent_isHomogeneous n q).totalDegree_le
  · exact (scaleEval_coeff (g.comp dehom) q n).symm

/-- A chart polynomial of degree at most n gives a pure cone term of degree n. -/
theorem coneTerm {p : MvPolynomial σ k} {n : ℕ} (hp : p.totalDegree ≤ n) :
    e (Polynomial.C (g p) * Polynomial.X ^ n) ∈ Cone e g := by
  classical
  rw [← sum_homogeneousComponent p, map_sum, map_sum, Finset.sum_mul, map_sum]
  refine (Cone e g).sum_mem fun i hi => ?_
  have hin : i ≤ n := (Finset.mem_range_succ_iff.mp hi).trans hp
  rw [← Nat.add_sub_of_le hin, pow_add, ← mul_assoc, map_mul]
  exact (Cone e g).mul_mem
    (by
      rw [← scaleEval_homogeneous g (homogeneousComponent_isHomogeneous i p), ← coe_scaled]
      exact (scaled e g _).property)
    (by rw [map_pow, ← coe_w e g]; exact (Cone e g).pow_mem (w e g).property _)

theorem cone_noetherian [Finite σ] : IsNoetherianRing (Cone e g) :=
  isNoetherianRing_of_surjective _ _ (coneEval e g).rangeRestrict.toRingHom
    (coneEval e g).rangeRestrict_surjective

end

end K1_13_6_3_5_5_1
end PackSource_K1_13_6_3_5_5_1Cone

section PackSource_K1_13_6_3_5_5_1Section
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_5_1

noncomputable section

open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_5

variable {k σ C E : Type} [Field k] [CommRing C] [Algebra k C]
  [CommRing E] [Algebra k E]

variable (e : Polynomial C →ₐ[k] E) (g : MvPolynomial σ k →ₐ[k] C)

abbrev sectionIdeal := Ideal.span ({w e g} : Set (Cone e g))

/-- The original variables map to the scaled variables modulo the homogenizing coordinate. -/
def sectionMk : MvPolynomial σ k →ₐ[k] Cone e g ⧸ sectionIdeal e g :=
  (Ideal.Quotient.mkₐ k _).comp (scaled e g)

theorem sectionMk_surjective : Function.Surjective (sectionMk e g) := by
  let drop : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
    aeval (fun i => i.elim 0 MvPolynomial.X)
  let q : Cone e g →ₐ[k] Cone e g ⧸ sectionIdeal e g := Ideal.Quotient.mkₐ k _
  have h : (sectionMk e g).comp drop = q.comp (coneEval e g).rangeRestrict := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      have hw : (coneEval e g).rangeRestrict (MvPolynomial.X none) = w e g :=
        Subtype.ext (coneEval_X_none e g)
      change sectionMk e g (drop (MvPolynomial.X none)) = q ((coneEval e g).rangeRestrict (MvPolynomial.X none))
      rw [show drop (MvPolynomial.X none) = 0 by simp [drop], map_zero, hw]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
    | some i => simp [sectionMk, drop, scaled, q]
  have hsurj : Function.Surjective (q.comp (coneEval e g).rangeRestrict) :=
    (Ideal.Quotient.mk_surjective.comp (coneEval e g).rangeRestrict_surjective)
  rw [← h] at hsurj
  intro z
  obtain ⟨f, hf⟩ := hsurj z
  exact ⟨drop f, hf⟩

private theorem topForm_mem_ker (f : MvPolynomial σ k) (hf : g f = 0) :
    homogeneousComponent f.totalDegree f ∈ RingHom.ker (sectionMk e g) := by
  classical
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (sectionIdeal e g) (scaled e g (homogeneousComponent f.totalDegree f)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  generalize hd : f.totalDegree = d
  cases d with
  | zero =>
    have h : homogeneousComponent 0 f = f :=
      homogeneousComponent_eq_self (isHomogeneous_of_totalDegree_zero σ hd)
    refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [zero_mul, Subalgebra.coe_zero, coe_scaled,
      scaleEval_homogeneous g (homogeneousComponent_isHomogeneous _ _), h, hf]
    simp
  | succ n =>
    let b := ∑ i ∈ Finset.range (n + 1), homogeneousComponent i f
    have hsum : b + homogeneousComponent (n + 1) f = f := by
      have h := sum_homogeneousComponent f
      rw [hd, Finset.sum_range_succ] at h
      exact h
    have hb : b.totalDegree ≤ n := by
      apply (mem_restrictTotalDegree _ _ _).mp
      exact (restrictTotalDegree σ k n).sum_mem fun i hi =>
        (mem_restrictTotalDegree _ _ _).mpr
          ((homogeneousComponent_isHomogeneous i f).totalDegree_le.trans
            (Finset.mem_range_succ_iff.mp hi))
    have heq : g (homogeneousComponent (n + 1) f) = g (-b) := by
      have hh := congrArg g hsum
      rw [map_add, hf] at hh
      rw [map_neg, eq_neg_iff_add_eq_zero, add_comm]
      exact hh
    have hnb : (-b).totalDegree ≤ n := by simpa using hb
    refine ⟨⟨_, coneTerm e g hnb⟩, Subtype.ext ?_⟩
    change e (Polynomial.C (g (-b)) * Polynomial.X ^ n) * (w e g : E) =
      (scaled e g (homogeneousComponent (n + 1) f) : E)
    rw [coe_w, ← map_mul, mul_assoc, ← pow_succ, coe_scaled,
      scaleEval_homogeneous g (homogeneousComponent_isHomogeneous _ _), heq]

theorem sectionMk_ker (he : Function.Injective e) :
    RingHom.ker (sectionMk e g) = boundaryIdeal (RingHom.ker g.toRingHom) := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · intro f hf
    have hw : scaled e g f ∈ sectionIdeal e g :=
      Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hf)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hw
    have hc (i : ℕ) (b : Polynomial C) (hb : e b = (a : E)) :
        (b * Polynomial.X).coeff i = g (homogeneousComponent i f) := by
      have h : e (b * Polynomial.X) = e (scaleEval g f) := by
        rw [map_mul, hb, ← coe_w e g, ← coe_scaled]
        exact congrArg Subtype.val ha
      rw [he h, scaleEval_coeff]
    rw [← sum_homogeneousComponent f]
    refine Ideal.sum_mem _ fun i _ => ?_
    let h := homogeneousComponent i f
    have hh : h.IsHomogeneous i := homogeneousComponent_isHomogeneous i f
    change h ∈ boundaryIdeal (RingHom.ker g.toRingHom)
    by_cases hz : h = 0
    · simp [hz]
    cases i with
    | zero =>
      obtain ⟨b, hb, _⟩ := coneCoeff e g a 0
      have hhA : h ∈ RingHom.ker g.toRingHom := by
        rw [RingHom.mem_ker]
        exact (hc 0 b hb).symm.trans (Polynomial.coeff_mul_X_zero b)
      exact Ideal.subset_span ⟨h, hhA, by rw [hh.totalDegree hz, homogeneousComponent_eq_self hh]⟩
    | succ i =>
      obtain ⟨b, hb, p, hp, hpcoef⟩ := coneCoeff e g a i
      have hp' : p.totalDegree < i + 1 := Nat.lt_succ_of_le hp
      have hsub : h - p ∈ RingHom.ker g.toRingHom := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        exact (hc (i + 1) b hb).symm.trans ((Polynomial.coeff_mul_X b i).trans hpcoef.symm)
      have hdeg : (h - p).totalDegree = i + 1 := by
        rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt, hh.totalDegree hz]
        simpa [hh.totalDegree hz] using hp'
      exact Ideal.subset_span ⟨h - p, hsub, by
        rw [hdeg, map_sub, homogeneousComponent_eq_self hh, homogeneousComponent_eq_zero _ _ hp',
          sub_zero]⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact topForm_mem_ker e g f (RingHom.mem_ker.mp hf)

variable {g} {A : Ideal (MvPolynomial σ k)}

/-- The scheme-theoretic boundary is the quotient cone by the common coordinate. -/
def sectionEquiv (he : Function.Injective e) (hA : RingHom.ker g.toRingHom = A) :
    (MvPolynomial σ k ⧸ boundaryIdeal A) ≃ₐ[k] (Cone e g ⧸ sectionIdeal e g) :=
  (Ideal.quotientEquivAlgOfEq k ((sectionMk_ker e g he).trans (congrArg boundaryIdeal hA)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (sectionMk_surjective e g))

theorem sectionEquiv_mk (he : Function.Injective e) (hA : RingHom.ker g.toRingHom = A)
    (f : MvPolynomial σ k) :
    sectionEquiv e he hA (Ideal.Quotient.mk (boundaryIdeal A) f) = sectionMk e g f := by
  rfl

def presentation (he : Function.Injective e) (hA : RingHom.ker g.toRingHom = A) :
    SectionPresentation (boundaryIdeal A) (w e g) where
  toQuotient := (sectionEquiv e he hA).symm.toRingHom.comp (Ideal.Quotient.mk _)
  surjective := (sectionEquiv e he hA).symm.surjective.comp Ideal.Quotient.mk_surjective
  ker_eq := by
    rw [RingHom.ker_comp_of_injective _ (sectionEquiv e he hA).symm.injective,
      Ideal.mk_ker]

end

end K1_13_6_3_5_5_1
end PackSource_K1_13_6_3_5_5_1Section

section PackSource_K1_13_6_3_5_5_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_5_1

noncomputable section

open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_5

variable {k σ τ C E : Type} [Field k] [CommRing C] [Algebra k C]
  [CommRing E] [Algebra k E]

variable (e : Polynomial C →ₐ[k] E) (g : MvPolynomial σ k →ₐ[k] C)
  (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (hφ : IsLinearProjection φ)

include hφ in
theorem scaleEval_comp (p : MvPolynomial τ k) :
    scaleEval (g.comp φ) p = scaleEval g (φ p) := by
  suffices scaleEval (g.comp φ) = (scaleEval g).comp φ from DFunLike.congr_fun this p
  apply MvPolynomial.algHom_ext
  intro i
  change scaleEval (g.comp φ) (MvPolynomial.X i) = scaleEval g (φ (MvPolynomial.X i))
  rw [scaleEval_homogeneous g (hφ i), pow_one]
  simp [scaleEval]

include hφ in
theorem cone_le : Cone e (g.comp φ) ≤ Cone e g := by
  let lift : MvPolynomial (Option τ) k →ₐ[k] MvPolynomial (Option σ) k :=
    aeval (fun i => i.elim (MvPolynomial.X none) (fun j => rename some (φ (MvPolynomial.X j))))
  have h : (coneEval e g).comp lift = coneEval e (g.comp φ) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simp [lift]
    | some i =>
      change coneEval e g (lift (MvPolynomial.X (some i))) = _
      rw [show lift (MvPolynomial.X (some i)) = rename some (φ (MvPolynomial.X i)) by simp [lift]]
      change (scaled e g (φ (MvPolynomial.X i)) : E) = _
      simp only [coe_scaled, coneEval_X_some, scaleEval_homogeneous g (hφ i),
        pow_one, AlgHom.comp_apply]
  rintro _ ⟨p, rfl⟩
  exact ⟨lift p, DFunLike.congr_fun h p⟩

variable {g} {A : Ideal (MvPolynomial σ k)} {B : Ideal (MvPolynomial τ k)}

include hφ in
theorem presentation_compatible (he : Function.Injective e)
    (hA : RingHom.ker g.toRingHom = A) (hB : RingHom.ker (g.comp φ).toRingHom = B) :
    Compatible φ.toRingHom (Subalgebra.inclusion (cone_le e g φ hφ)).toRingHom
      (presentation e he hB) (presentation e he hA) := by
  let f := (Subalgebra.inclusion (cone_le e g φ hφ)).toRingHom
  let qT := Ideal.Quotient.mk (sectionIdeal e (g.comp φ))
  let qS := Ideal.Quotient.mk (sectionIdeal e g)
  let ET := sectionEquiv e he hB
  let ES := sectionEquiv e he hA
  have hf : ∀ x ∈ sectionIdeal e (g.comp φ), qS (f x) = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_mul]
    have hw : qS (f (w e (g.comp φ))) = 0 := by
      change qS (w e g) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [hw, mul_zero]
  let n := Ideal.Quotient.lift (sectionIdeal e (g.comp φ)) (qS.comp f) hf
  let m := ES.symm.toRingHom.comp (n.comp ET.toRingHom)
  refine ⟨m, ?_, ?_⟩
  · apply RingHom.ext
    intro p
    change ES.symm (n (ET (Ideal.Quotient.mk (boundaryIdeal B) p))) =
      Ideal.Quotient.mk (boundaryIdeal A) (φ p)
    apply ES.injective
    rw [AlgEquiv.apply_symm_apply, sectionEquiv_mk e he hB, sectionEquiv_mk e he hA]
    change qS (f (scaled e (g.comp φ) p)) = qS (scaled e g (φ p))
    congr 1
    apply Subtype.ext
    change (scaled e (g.comp φ) p : E) = (scaled e g (φ p) : E)
    rw [coe_scaled, coe_scaled, scaleEval_comp g φ hφ]
  · apply RingHom.ext
    intro p
    change ES.symm (n (ET (ET.symm (qT p)))) = ES.symm (qS (f p))
    simp only [AlgEquiv.apply_symm_apply, n, qT, Ideal.Quotient.lift_mk,
      RingHom.comp_apply]

theorem cone_fraction {F : Type} [IsDomain C] [Field F] [Algebra k F]
    [Algebra (Polynomial C) F]
    [IsFractionRing (Polynomial C) F]
    (eF : Polynomial C →ₐ[k] F) (hee : ∀ p, eF p = algebraMap (Polynomial C) F p)
    (hg : Function.Surjective g)
    (hbir : ∀ p : MvPolynomial σ k, ∃ u v : MvPolynomial τ k,
      g (φ v) ≠ 0 ∧ g p * g (φ v) = g (φ u)) :
    IsFractionRing (Cone eF (g.comp φ)) F := by
  let T := Cone eF (g.comp φ)
  let D := Subfield.closure (T : Set F)
  have he : Function.Injective eF := fun a b hab =>
    IsFractionRing.injective (Polynomial C) F ((hee a).symm.trans (hab.trans (hee b)))
  have hx : eF Polynomial.X ∈ D := Subfield.subset_closure (w eF (g.comp φ)).property
  have hC (a : C) : eF (Polynomial.C a) ∈ D := by
    obtain ⟨p, rfl⟩ := hg a
    obtain ⟨u, v, hv, huv⟩ := hbir p
    let d := max u.totalDegree v.totalDegree
    let U := Polynomial.C (g (φ u)) * Polynomial.X ^ d
    let V := Polynomial.C (g (φ v)) * Polynomial.X ^ d
    have hU : eF U ∈ D := Subfield.subset_closure
      (coneTerm eF (g.comp φ) (le_max_left u.totalDegree v.totalDegree))
    have hV : eF V ∈ D := Subfield.subset_closure
      (coneTerm eF (g.comp φ) (le_max_right u.totalDegree v.totalDegree))
    have hV0 : eF V ≠ 0 := by
      rw [← map_zero eF]
      exact he.ne (mul_ne_zero (by simpa using hv) (pow_ne_zero _ Polynomial.X_ne_zero))
    have h : eF (Polynomial.C (g p)) = eF U / eF V := by
      apply (eq_div_iff hV0).mpr
      rw [← map_mul]
      apply congrArg eF
      dsimp [U, V]
      rw [← mul_assoc, ← map_mul, huv]
    rw [h]
    exact D.div_mem hU hV
  have hpol (p : Polynomial C) : eF p ∈ D := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact D.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact D.mul_mem (hC a) (D.pow_mem hx n)
  have hmem (z : F) : z ∈ D := by
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial C) z
    rw [← hee, ← hee]
    exact D.div_mem (hpol p) (hpol q)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, hx', y, hy', hxy⟩ := Subfield.mem_closure_iff.mp (hmem z)
  have hclosure : Subring.closure (T : Set F) = T.toSubring :=
    Subring.closure_eq T.toSubring
  rw [hclosure] at hx' hy'
  exact ⟨⟨x, hx'⟩, ⟨y, hy'⟩, hxy.symm⟩

private theorem modelIn {k σ τ : Type} [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (hφ : IsLinearProjection φ)
    (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) (hbir : IsBirationalOn φ A)
    (F : Type) [Field F] [Algebra (Polynomial (MvPolynomial σ k ⧸ A)) F]
    [IsFractionRing (Polynomial (MvPolynomial σ k ⧸ A)) F] :
    Nonempty (ConeModel φ A) := by
  let _ : A.IsPrime := hA
  let C := MvPolynomial σ k ⧸ A
  let P := Polynomial C
  let _ : Algebra k F := Algebra.compHom (R := P) F (algebraMap k P)
  let _ : IsScalarTower k P F :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := P) (A := F) (fun _ => rfl)
  let e := IsScalarTower.toAlgHom k P F
  let g := Ideal.Quotient.mkₐ k A
  have he : Function.Injective e := IsFractionRing.injective P F
  have hker : RingHom.ker g.toRingHom = A := Ideal.mk_ker
  have hkerφ : RingHom.ker (g.comp φ).toRingHom = A.comap φ := by
    change RingHom.ker (g.toRingHom.comp φ.toRingHom) = A.comap φ.toRingHom
    rw [← RingHom.comap_ker, hker]
  refine ⟨{
    F := F
    target := Cone e (g.comp φ)
    source := Cone e g
    le := cone_le e g φ hφ
    targetNoetherian := cone_noetherian e (g.comp φ)
    sourceNoetherian := cone_noetherian e g
    fraction := cone_fraction (g := g) φ e (fun _ => rfl) Ideal.Quotient.mk_surjective ?_
    w := w e (g.comp φ)
    w_ne := ?_
    targetSection := presentation e he hkerφ
    sourceSection := presentation e he hker
    compatible := presentation_compatible e φ hφ he hker hkerφ
  }⟩
  · intro p
    obtain ⟨u, v, hv, huv⟩ := hbir p
    refine ⟨u, v, ?_, ?_⟩
    · exact fun h => hv (Ideal.Quotient.eq_zero_iff_mem.mp h)
    · have hh : Ideal.Quotient.mk A (p * φ v - φ u) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr huv
      rw [map_sub, map_mul, sub_eq_zero] at hh
      exact hh
  · intro hw
    have h : e Polynomial.X = e 0 := by simpa using congrArg Subtype.val hw
    exact Polynomial.X_ne_zero (he h)

theorem proof : K1_13_6_3_5_5.c1 := by
  intro k σ τ _ _ _ φ hφ A hA hbir
  let _ : A.IsPrime := hA
  exact modelIn φ hφ A hA hbir (FractionRing (Polynomial (MvPolynomial σ k ⧸ A)))

end

end K1_13_6_3_5_5_1
end PackSource_K1_13_6_3_5_5_1Proof

section PackSource_K1_13_4_2_2_3Proof
set_option autoImplicit true
namespace K1_13_4_2_2_3

open K1_13_4_2_2
open scoped BigOperators

set_option maxHeartbeats 600000

private def quarterSquare (w : ℤ) : ℤ := w ^ 2 / 4
private def weightCost (w : ℤ) : ℤ := quarterSquare (w + 1)

private theorem double_triangular (w : ℤ) : 2 * triangular w = w * (w + 1) := by
  unfold triangular
  apply Int.mul_ediv_cancel_of_dvd
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    exact dvd_mul_of_dvd_left (by rw [hw]; exact dvd_mul_right _ _) _
  · have hw : w + 1 = 2 * (w / 2 + 1) := by omega
    exact dvd_mul_of_dvd_right (by rw [hw]; exact dvd_mul_right _ _) _

private theorem quarterSquare_spec (w : ℤ) :
    4 * quarterSquare w = w ^ 2 - w % 2 := by
  unfold quarterSquare
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with h | h
  · have hw : w = 2 * (w / 2) := by omega
    have he : w ^ 2 = 4 * (w / 2) ^ 2 := by
      calc _ = (2 * (w / 2)) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega
  · have hw : w = 2 * (w / 2) + 1 := by omega
    have he : w ^ 2 = 4 * ((w / 2) ^ 2 + w / 2) + 1 := by
      calc _ = (2 * (w / 2) + 1) ^ 2 := congrArg (· ^ 2) hw
           _ = _ := by ring
    rw [he, h]
    omega

private theorem weightCost_spec (w : ℤ) :
    4 * weightCost w = w ^ 2 + 2 * w + w % 2 := by
  unfold weightCost
  rw [quarterSquare_spec]
  have h : (w + 1) % 2 + w % 2 = 1 := by omega
  nlinarith only [h]

private theorem weightCost_nonneg (w : ℤ) : 0 ≤ weightCost w := by
  unfold weightCost quarterSquare
  positivity

private theorem weightCost_mono {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) :
    weightCost a ≤ weightCost b := by
  unfold weightCost quarterSquare
  have hs : (a + 1) ^ 2 ≤ (b + 1) ^ 2 := by gcongr
  omega

private theorem triangular_eq_costs (d : ℤ) :
    triangular (d + 1) = weightCost d + weightCost (d + 1) := by
  have hp : d % 2 + (d + 1) % 2 = 1 := by omega
  nlinarith only [double_triangular (d + 1), weightCost_spec d, weightCost_spec (d + 1), hp]

private theorem colength_zero {a w : ℤ} (ha : a ≤ 0) (hw : w ≤ 0) :
    colength ⟨a, w⟩ = 0 := by
  have hu : (w + 1) / 2 ≤ 0 := by omega
  simp [colength, max_eq_left (max_le ha hu), max_eq_left hw, triangular]

private theorem colength_cost {a w : ℤ} (ha : a ≤ 0) (hw : 0 ≤ w) :
    colength ⟨a, w⟩ = weightCost w := by
  have hu : 0 ≤ (w + 1) / 2 := by omega
  have haw : a ≤ (w + 1) / 2 := ha.trans hu
  have huv : (w + 1) / 2 ≤ w := by omega
  have h : (w + 1) / 2 = w / 2 + w % 2 := by omega
  have h' : w - (w + 1) / 2 = w / 2 := by omega
  unfold colength
  simp only [max_eq_right haw, max_eq_right hu, max_eq_right huv]
  rw [h', h]
  have h₁ := double_triangular (w / 2 + w % 2)
  have h₂ := double_triangular (w / 2)
  have h₃ := weightCost_spec w
  rcases (show w % 2 = 0 ∨ w % 2 = 1 by omega) with he | he
  · have hw' : w = 2 * (w / 2) := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw']
    nlinarith only [h₁, h₂, h₃]
  · have hw' : w = 2 * (w / 2) + 1 := by omega
    rw [he] at h₁ h₃ ⊢
    conv at h₃ => rhs; rw [hw']
    nlinarith only [h₁, h₂, h₃]

private theorem cumulative_small {d w : ℤ} (hw : 0 ≤ w) (hwd : w ≤ d) :
    cumulative d w = weightCost (w + 1) := by
  have hcap : w ≤ 2 * d := by omega
  simp only [cumulative, not_lt.mpr hw, ite_false, min_eq_left hcap,
    max_eq_left (sub_nonpos.mpr hwd)]
  norm_num [weightCost, quarterSquare, triangular, add_assoc]

/-- Reflecting the index exchanges the two ends of the full homogeneous grade. -/
private theorem cumulative_middle {d w : ℤ} (hd : 0 ≤ d) (hdw : d ≤ w) (hw : w ≤ 2 * d) :
    cumulative d w = triangular (d + 1) - weightCost (2 * d - w) := by
  simp only [cumulative, not_lt.mpr (hd.trans hdw), ite_false, min_eq_left hw,
    max_eq_right (sub_nonneg.mpr hdw)]
  rw [show (w + 2) ^ 2 / 4 = weightCost (w + 1) by
    rw [show w + 2 = w + 1 + 1 by ring]
    rfl]
  have hp : (w + 1) % 2 + (2 * d - w) % 2 = 1 := by omega
  nlinarith only [weightCost_spec (w + 1), weightCost_spec (2 * d - w),
    double_triangular (w - d), double_triangular (d + 1), hp]

private theorem cumulative_full {d w : ℤ} (hd : 0 ≤ d) (hw : 2 * d ≤ w) :
    cumulative d w = triangular (d + 1) := by
  have h : cumulative d w = cumulative d (2 * d) := by
    simp [cumulative, not_lt.mpr (show 0 ≤ 2 * d by omega),
      not_lt.mpr (show 0 ≤ w by omega), min_eq_right hw]
  rw [h, cumulative_middle hd (by omega) le_rfl]
  simp [weightCost, quarterSquare]

private theorem cumulative_bounds {d : ℤ} (hd : 0 ≤ d) (w : ℤ) :
    0 ≤ cumulative d w ∧ cumulative d w ≤ triangular (d + 1) := by
  by_cases hw : w < 0
  · simp [cumulative, hw, triangular_eq_costs, add_nonneg (weightCost_nonneg _) (weightCost_nonneg _)]
  by_cases hwd : w ≤ d
  · rw [cumulative_small (by omega) hwd, triangular_eq_costs]
    have h := weightCost_mono (a := w + 1) (b := d + 1) (by omega) (by omega)
    exact ⟨weightCost_nonneg _, by linarith [weightCost_nonneg d]⟩
  by_cases hcap : w ≤ 2 * d
  · rw [cumulative_middle hd (by omega) hcap, triangular_eq_costs]
    have h := weightCost_mono (a := 2 * d - w) (b := d) (by omega) (by omega)
    exact ⟨by linarith [weightCost_nonneg (d + 1)], by linarith [weightCost_nonneg (2 * d - w)]⟩
  · rw [cumulative_full hd (by omega), triangular_eq_costs]
    exact ⟨add_nonneg (weightCost_nonneg _) (weightCost_nonneg _), le_rfl⟩

private def factorPowers (n : ℕ) : Powers := fun i => if i = 4 then n else 0

private def fullPowers (q k : ℕ) : Powers :=
  factorPowers (planeOrder q (offset k) - (q : ℤ)).toNat

private theorem sum_powers (n : ℕ) (f : Fin 6 → ℤ) :
    (∑ i, (factorPowers n i : ℤ) * f i) = (n : ℤ) * f 4 := by
  simp [factorPowers]

private theorem shifted_kernel (q n : ℕ) (g : ℤ) (hq : q < 1151) (hg : 0 ≤ g)
    (hn : n ≤ q) (ht : 0 ≤ planeOrder q g - 2 * (n : ℤ)) :
    kernelLower (remainingDegree q (factorPowers n)) (remainingFlag q g (factorPowers n)) =
      triangular ((q : ℤ) - n + 1) - weightCost (planeOrder q g - 2 * (n : ℤ)) := by
  have hd : residualDegree q = q := min_eq_left (by omega)
  have hd' : remainingDegree q (factorPowers n) = (q : ℤ) - n := by
    rw [remainingDegree, hd, sum_powers]
    simp [factorDegree]
  have hP : remainingFlag q g (factorPowers n) 0 = ⟨0, -g⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag]
  have hQ : remainingFlag q g (factorPowers n) 1 = ⟨(q : ℤ) - 1150, 2 * (q : ℤ) - 2300⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, hd]
  have hO : remainingFlag q g (factorPowers n) 2 = ⟨-(n : ℤ), planeOrder q g - 2 * (n : ℤ)⟩ := by
    simp [remainingFlag, sum_powers, initialFlag, factorFlag, mul_comm]
  rw [kernelLower, hd']
  simp only [show ¬ ((q : ℤ) - n) < 0 by omega, ite_false, Fin.sum_univ_three, hP, hQ, hO,
    colength_zero (a := 0) (w := -g) (by omega) (by omega),
    colength_zero (a := (q : ℤ) - 1150) (w := 2 * (q : ℤ) - 2300) (by omega) (by omega),
    colength_cost (a := -(n : ℤ)) (by omega) ht, zero_add]

private theorem cast_toNat_le {a b : ℤ} (hab : a ≤ b) (hb : 0 ≤ b) :
    (a.toNat : ℤ) ≤ b := by
  have h := Int.toNat_le_toNat hab
  omega

private theorem block_le_columns (q : ℕ) (g : ℤ) (p : Powers) (h : 0 ≤ columnCount q g) :
    (blockBound q g p : ℤ) ≤ columnCount q g := by
  by_cases ht : planeOrder q g ≤ 0
  · simpa only [blockBound, ht, ite_true, Nat.cast_zero] using h
  simp only [blockBound, ht, ite_false]
  apply cast_toNat_le _ h
  exact sub_le_self _ (le_max_left _ _)

private theorem block_le_of_shifted (q : ℕ) (g : ℤ) (p : Powers) (r : ℤ) (hr : 0 ≤ r)
    (h : columnCount q g -
        kernelLower (remainingDegree q p) (remainingFlag q g p) ≤ r) :
    (blockBound q g p : ℤ) ≤ r := by
  by_cases ht : planeOrder q g ≤ 0
  · simpa only [blockBound, ht, ite_true, Nat.cast_zero] using hr
  simp only [blockBound, ht, ite_false]
  apply cast_toNat_le _ hr
  exact (sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _).trans h

private theorem block_le_cumulative (q k : ℕ) (hq : q < 1151) :
    (blockBound q (offset k) (fullPowers q k) : ℤ) ≤
      cumulative q (planeOrder q (offset k) - 1) - cumulative q (-offset k - 1) := by
  let g := offset k
  let t := planeOrder q g
  change (blockBound q g (factorPowers (t - (q : ℤ)).toNat) : ℤ) ≤
    cumulative q (t - 1) - cumulative q (-g - 1)
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hc : columnCount q g = triangular ((q : ℤ) + 1) - cumulative q (-g - 1) := by
    have hd : residualDegree q = q := min_eq_left (by omega)
    have hg : -g - 1 ≤ 2300 := by dsimp [g, offset]; omega
    unfold columnCount
    rw [hd, min_eq_right hg]
    change cumulative (q : ℤ) 2300 - cumulative q (-g - 1) = _
    rw [cumulative_full hq0 (by omega : 2 * (q : ℤ) ≤ 2300)]
  by_cases hhigh : 2 * (q : ℤ) < t
  · rw [cumulative_full hq0 (by omega), ← hc]
    exact block_le_columns _ _ _ (by rw [hc]; exact sub_nonneg.mpr (cumulative_bounds hq0 _).2)
  have hg : 0 ≤ g := by unfold t planeOrder at hhigh; omega
  have hz : cumulative q (-g - 1) = 0 := by simp [cumulative, show -g - 1 < 0 by omega]
  rw [hz, sub_zero]
  by_cases ht : t ≤ 0
  · simp [blockBound, show planeOrder q g ≤ 0 from ht, cumulative, show t - 1 < 0 by omega]
  apply block_le_of_shifted _ _ _ _ (cumulative_bounds hq0 _).1
  rw [hc, hz, sub_zero]
  by_cases hlo : t ≤ (q : ℤ)
  · have hn : (t - (q : ℤ)).toNat = 0 := by omega
    rw [hn, shifted_kernel q 0 g hq hg (by omega) (by simpa [t] using le_of_lt (lt_of_not_ge ht)),
      cumulative_small (by omega) (by omega)]
    push_cast
    simp only [sub_zero]
    rw [show t - 1 + 1 = t by ring]
    change triangular ((q : ℤ) + 1) - (triangular ((q : ℤ) + 1) - weightCost t) ≤ weightCost t
    linarith
  have hn : ((t - (q : ℤ)).toNat : ℤ) = t - (q : ℤ) := Int.toNat_of_nonneg (by omega)
  rw [shifted_kernel q _ g hq hg (by omega) (by change 0 ≤ t - _; omega),
    hn, cumulative_middle hq0 (by omega) (by omega)]
  change triangular ((q : ℤ) + 1) -
    (triangular ((q : ℤ) - (t - (q : ℤ)) + 1) - weightCost (t - 2 * (t - (q : ℤ)))) ≤ _
  rw [show (q : ℤ) - (t - (q : ℤ)) + 1 = 2 * (q : ℤ) - t + 1 by ring,
    show t - 2 * (t - (q : ℤ)) = 2 * (q : ℤ) - t by ring,
    triangular_eq_costs (2 * (q : ℤ) - t),
    show 2 * (q : ℤ) - (t - 1) = 2 * (q : ℤ) - t + 1 by ring]
  linarith

/-- Reverse the active part of a signed cumulative count. -/
private theorem sum_reverse (d : ℤ) (n N : ℕ) (hn : n ≤ N) :
    (∑ k ∈ Finset.range N, cumulative d ((n : ℤ) - 1 - (k : ℤ))) =
      ∑ k ∈ Finset.range n, cumulative d (k : ℤ) := by
  calc
    _ = ∑ k ∈ Finset.range n, cumulative d ((n : ℤ) - 1 - (k : ℤ)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro k _ hk
      have hneg : (n : ℤ) - 1 - (k : ℤ) < 0 := by
        simp only [Finset.mem_range] at hk
        omega
      simp [cumulative, hneg]
    _ = _ := by
      rw [← Finset.sum_range_reflect (fun k : ℕ => cumulative d (k : ℤ)) n]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      congr 1
      omega

private def gradeLimit (q : ℕ) : ℤ := (5000 - (q : ℤ)) * triangular ((q : ℤ) + 1)

private theorem grade_le_limit (q : ℕ) (hq : q < 1151) :
    (gradeBound fullPowers q : ℤ) ≤ gradeLimit q := by
  rw [gradeBound, Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range 7300,
        (cumulative (q : ℤ) (planeOrder q (offset k) - 1) - cumulative (q : ℤ) (-offset k - 1)) :=
      Finset.sum_le_sum fun k _ => block_le_cumulative q k hq
    _ = gradeLimit q := by
      have hp (k : ℕ) : planeOrder q (offset k) - 1 = ((7300 - q : ℕ) : ℤ) - 1 - k := by
        unfold planeOrder offset
        omega
      have hm (k : ℕ) : -offset k - 1 = ((2300 : ℕ) : ℤ) - 1 - k := by
        unfold offset
        omega
      simp_rw [hp, hm]
      rw [Finset.sum_sub_distrib, sum_reverse _ _ _ (Nat.sub_le _ _),
        sum_reverse _ _ _ (by omega : 2300 ≤ 7300),
        show 7300 - q = 2300 + (5000 - q) by omega, Finset.sum_range_add, add_sub_cancel_left]
      have hfull (k : ℕ) : cumulative (q : ℤ) ((2300 + k : ℕ) : ℤ) =
          triangular ((q : ℤ) + 1) := cumulative_full (by omega) (by omega)
      simp_rw [hfull]
      simp [gradeLimit, Nat.cast_sub (show q ≤ 5000 by omega)]

private theorem sum_grade_limit (n : ℕ) :
    24 * (∑ q ∈ Finset.range n, gradeLimit q) =
      (n : ℤ) * (n + 1) * (n + 2) * (20003 - 3 * (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, gradeLimit, Nat.cast_succ]
    have ht := double_triangular ((n : ℤ) + 1)
    linear_combination 12 * (5000 - (n : ℤ)) * ht

theorem proof : K1_13_4_2_2.c3 := by
  refine ⟨fullPowers, ?_⟩
  have h : (∑ q ∈ Finset.range 1151, gradeLimit q) = 1054250623200 := by
    have hs := sum_grade_limit 1151
    norm_num only [Nat.cast_ofNat, Int.reduceAdd, Int.reduceMul, Int.reduceSub] at hs
    omega
  have hsum := Finset.sum_le_sum (s := Finset.range 1151)
    (fun q hq => grade_le_limit q (Finset.mem_range.mp hq))
  rw [← Nat.cast_sum, h] at hsum
  exact_mod_cast hsum

end K1_13_4_2_2_3
end PackSource_K1_13_4_2_2_3Proof

section PackSource_K1_13_5_4_4_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

namespace K1_13_5_4_4_2

noncomputable section

open K1_13 K1_13_5_4 K1_13_5_4_4 K1_13_6_3_4 MvPolynomial

private def jetQuot (Q : CoefficientIdeal) :
    (FreshJetRing ⧸ freshImage Q) →ₐ[FreshField] (FreshCoeffRing ⧸ extendIdeal Q) :=
  Ideal.quotientMapₐ (extendIdeal Q) freshProjection (fun _ h => h)

private theorem jetQuot_mk (Q : CoefficientIdeal) (p : FreshJetRing) :
    jetQuot Q (Ideal.Quotient.mk (freshImage Q) p) =
      Ideal.Quotient.mk (extendIdeal Q) (freshProjection p) := rfl

private theorem jetQuot_X (Q : CoefficientIdeal) (j : Fin 3) :
    jetQuot Q (Ideal.Quotient.mk (freshImage Q) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (extendIdeal Q) (K1_13_5_5.jetForm freshArgument j.val) := by
  rw [jetQuot_mk, freshProjection, aeval_X]

private theorem jetQuot_injective (Q : CoefficientIdeal) : Function.Injective (jetQuot Q) := by
  apply (injective_iff_map_eq_zero (jetQuot Q)).mpr
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [jetQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hz

/-- Clearing denominators on the variables suffices on the whole quotient. -/
private theorem recover_quotient {Q : CoefficientIdeal} (hP : (extendIdeal Q).IsPrime)
    (hb : FreshBirational Q) (x : FreshCoeffRing ⧸ extendIdeal Q) :
    ∃ a b, jetQuot Q b ≠ 0 ∧ jetQuot Q b * x = jetQuot Q a := by
  letI := hP
  let g := jetQuot Q
  have hX (i : Fin taylorLength) :
      ∃ a b, g b ≠ 0 ∧ g b * Ideal.Quotient.mk (extendIdeal Q) (MvPolynomial.X i) = g a := by
    obtain ⟨u, v, hv, huv⟩ := hb i
    refine ⟨Ideal.Quotient.mk _ u, Ideal.Quotient.mk _ v, ?_, ?_⟩
    · rwa [show g = jetQuot Q from rfl, jetQuot_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [show g = jetQuot Q from rfl, jetQuot_mk, jetQuot_mk, ← map_mul, ← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr huv
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ∃ a b, g b ≠ 0 ∧ g b * Ideal.Quotient.mk (extendIdeal Q) p = g a
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨algebraMap FreshField _ c, 1, by simp, ?_⟩
    rw [map_one, one_mul, AlgHom.commutes]
    rfl
  | add p q hp hq =>
    obtain ⟨a, b, hb₀, ha⟩ := hp
    obtain ⟨c, d, hd₀, hc⟩ := hq
    refine ⟨a * d + b * c, b * d, by simpa only [map_mul] using mul_ne_zero hb₀ hd₀, ?_⟩
    simp only [map_mul, map_add]
    rw [show g b * g d * (Ideal.Quotient.mk (extendIdeal Q) p +
      Ideal.Quotient.mk (extendIdeal Q) q) =
      (g b * Ideal.Quotient.mk (extendIdeal Q) p) * g d +
      g b * (g d * Ideal.Quotient.mk (extendIdeal Q) q) by ring, ha, hc]
  | mul_X p i hp =>
    obtain ⟨a, b, hb₀, ha⟩ := hp
    obtain ⟨c, d, hd₀, hc⟩ := hX i
    refine ⟨a * c, b * d, by simpa only [map_mul] using mul_ne_zero hb₀ hd₀, ?_⟩
    simp only [map_mul]
    rw [show g b * g d * (Ideal.Quotient.mk (extendIdeal Q) p *
      Ideal.Quotient.mk (extendIdeal Q) (MvPolynomial.X i)) =
      (g b * Ideal.Quotient.mk (extendIdeal Q) p) *
      (g d * Ideal.Quotient.mk (extendIdeal Q) (MvPolynomial.X i)) by ring, ha, hc]

theorem proof : K1_13_5_4_4.c2 := by
  intro Q _ hd hp hb
  letI := hp
  let g := jetQuot Q
  have hrec := recover_quotient hp hb
  have hg := jetQuot_injective Q
  have hbase : affineHilbertPolynomial (extendIdeal Q) = affineHilbertPolynomial Q :=
    K1_13_5_5_2.hilbertPolynomial_map Q
  have hdim_ext : (affineHilbertPolynomial (extendIdeal Q)).natDegree = 1 := by
    rwa [hbase]
  have hlin (j : Fin 3) :
      g (Ideal.Quotient.mk (freshImage Q) (MvPolynomial.X j)) ∈
        quotientDegreeLE (extendIdeal Q) 1 := by
    change jetQuot Q _ ∈ _
    rw [jetQuot_X]
    exact mk_mem_quotientDegreeLE (jetForm_homogeneous j.val).totalDegree_le
  have hdim_le := (natDegree_affineHilbertPolynomial_le_of_injective g hg).trans_eq hdim_ext
  have hdim : (affineHilbertPolynomial (freshImage Q)).natDegree = 1 := by
    by_contra hd'
    have hz : (affineHilbertPolynomial (freshImage Q)).natDegree = 0 := by omega
    letI : (freshImage Q).IsPrime := hp.comap freshProjection
    letI := moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hz
    have hsurj : Function.Surjective g := by
      intro x
      obtain ⟨a, b, hb₀, he⟩ := hrec x
      obtain ⟨c, hc⟩ := FiniteDimensional.exists_mul_eq_one FreshField
        (show b ≠ 0 from fun h => hb₀ (by simp [h]))
      refine ⟨c * a, ?_⟩
      rw [map_mul, ← he, ← mul_assoc, ← map_mul, mul_comm c b, hc, map_one, one_mul]
    have h := natDegree_affineHilbertPolynomial_le_of_surjective g hsurj
    rw [hdim_ext, hz] at h
    omega
  have hdeg := degree_eq_of_valueReduction g hg (0 : Fin 3) (jetQuot_X Q 0) hlin
    hrec (freshValueReduction Q hd)
  refine ⟨hdim, ?_⟩
  rw [← hdeg, affineDegree, affineDegree, hbase]

end
end K1_13_5_4_4_2
end PackSource_K1_13_5_4_4_2Proof

section PackSource_K1_13_6_2_3_2_3Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_2_3_2_3

noncomputable section

open K1_13 K1_13_6 K1_13_6_2_3_2 MvPolynomial

private def gradeExponent {ι : Type} [Fintype ι] :
    (ι → ℕ) ≃+ (ι →₀ ℕ) :=
  Finsupp.addEquivFunOnFinite.symm

private theorem gradeExponent_step {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    gradeExponent (step i) = Finsupp.single i 1 :=
  Finsupp.equivFunOnFinite_symm_single i 1

private theorem capMap_X {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets)
    (v : CapVar shapes) :
    capMap shapes J (MvPolynomial.X v) = monomial (Finsupp.single v.1 1)
      (Ideal.Quotient.mk J (monomial v.2.val 1)) :=
  aeval_X _ _

/-- A presentation monomial contributes at one grading exponent. Its coefficient is the
corresponding affine monomial in the original quotient. -/
private theorem capMap_monomial_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (shapes : ι → Shape) (J : Ideal GeoJets) (e : CapVar shapes →₀ ℕ) :
    capMap shapes J (monomial e 1) =
      monomial (gradeExponent (Finsupp.weight (step ∘ capSlot shapes) e))
        (Ideal.Quotient.mk J (monomial (Finsupp.weight (fun v : CapVar shapes => v.2.val) e) 1)) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add e f he hf =>
      rw [← one_mul (1 : GeoField), ← monomial_mul_monomial, map_mul, he, hf,
        monomial_mul_monomial, ← map_mul, monomial_mul_monomial, one_mul,
        map_add, map_add, map_add]
  | single v n =>
      rw [← X_pow_eq_monomial, map_pow, capMap_X, monomial_pow, ← map_pow,
        monomial_pow, one_pow, Finsupp.weight_single, Finsupp.weight_single, map_nsmul]
      change monomial (n • Finsupp.single v.1 1)
        (Ideal.Quotient.mk J (monomial (n • v.2.val) 1)) =
        monomial (n • gradeExponent (step v.1))
          (Ideal.Quotient.mk J (monomial (n • v.2.val) 1))
      rw [gradeExponent_step]

private theorem capIdeal_graded {ι : Type} [Fintype ι] [DecidableEq ι]
    (shapes : ι → Shape) (J : Ideal GeoJets) :
    Graded (capSlot shapes) (capIdeal shapes J) := by
  intro f hf a
  classical
  let proj : MvPolynomial ι (GeoJets ⧸ J) →ₗ[GeoField] MvPolynomial ι (GeoJets ⧸ J) :=
    ((monomial (gradeExponent a)).comp (lcoeff (GeoJets ⧸ J) (gradeExponent a))).restrictScalars
      GeoField
  have hcomm :
      (capMap shapes J).toLinearMap.comp
          (weightedHomogeneousComponent (step ∘ capSlot shapes) a) =
        proj.comp (capMap shapes J).toLinearMap := by
    apply (basisMonomials (CapVar shapes) GeoField).ext
    intro e
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial
      (step ∘ capSlot shapes) e 1 rfl)]
    by_cases he : Finsupp.weight (step ∘ capSlot shapes) e = a
    · simp [he, proj, capMap_monomial_one]
    · simp [he, Ne.symm he, proj, capMap_monomial_one]
  change capMap shapes J f = 0 at hf
  change capMap shapes J (weightedHomogeneousComponent (step ∘ capSlot shapes) a f) = 0
  have hf' := DFunLike.congr_fun hcomm f
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hf, map_zero] using hf'

private theorem cap_hilbert_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (shapes : ι → Shape) (J : Ideal GeoJets) (a : ι → ℕ) :
    hilbert (capSlot shapes) (capIdeal shapes J) a =
      (supportRank J (productExponents shapes a) : ℚ) := by
  let S := weightedHomogeneousSubmodule GeoField (step ∘ capSlot shapes) a
  let V := S.map (Ideal.Quotient.mkₐ GeoField (RingHom.ker (capMap shapes J))).toLinearMap
  let T := restrictSupport GeoField (productExponents shapes a)
  let U := T.map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let lift := (Ideal.kerLiftAlg (capMap shapes J)).toLinearMap
  let tag : (GeoJets ⧸ J) →ₗ[GeoField] MvPolynomial ι (GeoJets ⧸ J) :=
    (monomial (gradeExponent a)).restrictScalars GeoField
  have hlift : V.map lift = S.map (capMap shapes J).toLinearMap := by
    change (S.map _).map _ = _
    rw [← Submodule.map_comp]
    rfl
  have htag : Function.Injective tag := by
    intro x y h
    have hc := congrArg (fun p : MvPolynomial ι (GeoJets ⧸ J) => p.coeff (gradeExponent a)) h
    simpa [tag] using hc
  have himage : S.map (capMap shapes J).toLinearMap = U.map tag := by
    have hS : S = restrictSupport GeoField
        {e | Finsupp.weight (step ∘ capSlot shapes) e = a} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    change S.map _ = (T.map _).map _
    rw [hS, show T = restrictSupport GeoField (productExponents shapes a) from rfl,
      restrictSupport_eq_span, restrictSupport_eq_span, Submodule.map_span,
      Submodule.map_span, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      change Finsupp.weight (step ∘ capSlot shapes) e = a at he
      refine ⟨_, ⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      simp only [AlgHom.toLinearMap_apply, capMap_monomial_one, he]
      rfl
    · rintro ⟨_, ⟨_, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨e, he, rfl⟩ := hm
      refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
      simp only [AlgHom.toLinearMap_apply, capMap_monomial_one, he]
      rfl
  have hrank : Module.finrank GeoField V = Module.finrank GeoField U :=
    calc
      _ = Module.finrank GeoField (V.map lift) :=
        (Submodule.equivMapOfInjective lift (Ideal.kerLiftAlg_injective (capMap shapes J))
          V).finrank_eq
      _ = Module.finrank GeoField (U.map tag) := by rw [hlift, himage]
      _ = _ := (Submodule.equivMapOfInjective tag htag U).finrank_eq.symm
  exact congrArg (fun n : ℕ => (n : ℚ)) hrank

/-- The slot grading descends to the cap algebra, with affine support ranks in its pieces. -/
theorem proof : K1_13_6_2_3_2.c3 := by
  intro ι _ _ shapes J
  exact ⟨capIdeal_graded shapes J, cap_hilbert_eq shapes J⟩

end

end K1_13_6_2_3_2_3
end PackSource_K1_13_6_2_3_2_3Proof

section PackSource_K1_13_4_5_1Proof
set_option autoImplicit true
namespace K1_13_4_5_1

noncomputable section

open K1_13 K1_13_4 MvPolynomial
open scoped Polynomial BigOperators

private theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX

/-- Use one common denominator without changing the support of the row. -/
private theorem clear_denominators (f : GenericRow) :
    ∃ (d : Geom[X]) (P : PhysicalRow), d ≠ 0 ∧ P.support = f.support ∧
      MvPolynomial.map inclX P = C (inclX d) * f := by
  classical
  let M := nonZeroDivisors (Geom[X])
  let d := IsLocalization.commonDenom M f.support f.coeff
  let num := IsLocalization.integerMultiple M f.support f.coeff
  let P : PhysicalRow := ∑ a : ↥f.support, monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : inclX (d : Geom[X]) ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  have hP : MvPolynomial.map inclX P = C (inclX d) * f := by
    ext m
    simp only [coeff_map, coeff_C_mul, P, coeff_sum]
    by_cases hm : m ∈ f.support
    · let a : ↥f.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M f.support f.coeff a
        change inclX (num a) = (d : Geom[X]) • f.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [coeff_monomial, hb]
    · have hz : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥f.support, (monomial a.val (num a) : PhysicalRow).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, P, hd, ?_, hP⟩
  rw [← support_map_of_injective P inclX_injective, hP]
  ext m
  simp [MvPolynomial.mem_support_iff, coeff_C_mul, hi]

private def coefficientDerivative (P : PhysicalRow) : PhysicalRow :=
  ∑ m ∈ P.support, monomial m (Polynomial.derivative (P.coeff m))

@[simp] private theorem coeff_coefficientDerivative (P : PhysicalRow) (m : SeedVar →₀ ℕ) :
    (coefficientDerivative P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero]

private theorem coefficientDerivative_C (c : Geom[X]) :
    coefficientDerivative (C c) = C (Polynomial.derivative c) := by
  ext m
  by_cases hm : 0 = m <;> simp [coeff_C, hm]

private theorem coefficientDerivative_add (P Q : PhysicalRow) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp

private theorem coefficientDerivative_mul_X (P : PhysicalRow) (j : SeedVar) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  ext m
  rw [coeff_coefficientDerivative, coeff_mul_X', coeff_mul_X']
  split_ifs <;> simp

/-- The chain rule differentiates both the coefficients and the substituted variables. -/
private theorem eval_chain (P : PhysicalRow) (a : SeedVar → Geom[X]) :
    Polynomial.derivative (eval a P) = eval a (coefficientDerivative P) +
      ∑ i, Polynomial.derivative (a i) * eval a (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [coefficientDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, eval_X, Polynomial.derivative_mul, ih, coefficientDerivative_mul_X,
      map_mul, eval_X]
    simp only [pderiv_mul, map_add, map_mul, eval_X, mul_add, Finset.sum_add_distrib]
    have left : (∑ i, Polynomial.derivative (a i) * (eval a (pderiv i P) * a j)) =
        (∑ i, Polynomial.derivative (a i) * eval a (pderiv i P)) * a j := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, Polynomial.derivative (a i) * (eval a P * eval a (pderiv i (MvPolynomial.X j)))) =
        Polynomial.derivative (a j) * eval a P := by
      simp [pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring

/-- The dotted row, with the coefficient derivative supplied separately. -/
private def dotted {R : Type*} [CommRing R] (r P : SeedRow R) : SeedRow R :=
  r + MvPolynomial.X (some 1) * pderiv (some 0) P +
    C (2 : R) * (MvPolynomial.X (some 2) * pderiv (some 1) P)

private def polynomialPoint (z : Geom) (S : Geom[X]) : SeedVar → Geom[X] :=
  fun i => i.elim (Polynomial.C z) (jet S)

private theorem derivative_hasse (S : Geom[X]) (k : ℕ) :
    Polynomial.derivative (Polynomial.hasseDeriv k S) =
      Polynomial.C ((k + 1 : ℕ) : Geom) * Polynomial.hasseDeriv (k + 1) S := by
  have h := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := Geom) 1 k) S
  simpa [Polynomial.hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul,
    Polynomial.C_eq_natCast, Nat.add_comm, add_mul] using h

private theorem eval_dotted (P : PhysicalRow) (z : Geom) (S : Geom[X])
    (htop : P.degreeOf (some 2) = 0) :
    eval (polynomialPoint z S) (dotted (coefficientDerivative P) P) =
      Polynomial.derivative (eval (polynomialPoint z S) P) := by
  have hzero := pderiv_eq_zero_of_degreeOf_eq_zero htop
  have h₀ : Polynomial.derivative (polynomialPoint z S (some 0)) =
      polynomialPoint z S (some 1) := by
    simp [polynomialPoint, jet]
  have h₁ : Polynomial.derivative (polynomialPoint z S (some 1)) =
      Polynomial.C (2 : Geom) * polynomialPoint z S (some 2) := by
    simpa [polynomialPoint, jet] using derivative_hasse S 1
  have hz : Polynomial.derivative (polynomialPoint z S none) = 0 :=
    Polynomial.derivative_C
  rw [eval_chain, Fintype.sum_option, Fin.sum_univ_three]
  simp only [dotted, map_add, map_mul, eval_X, eval_C, h₀, h₁, hzero, hz, map_zero, mul_zero,
    add_zero, zero_mul]
  rw [map_ofNat (Polynomial.C : Geom →+* Geom[X])]
  ring

private theorem eval_map_point (z : Geom) (S : Geom[X]) (P : PhysicalRow) :
    eval (atPoint (inclConst z) (trajectory S)) (MvPolynomial.map inclX P) =
      inclX (eval (polynomialPoint z S) P) := by
  have hpoint : atPoint (inclConst z) (trajectory S) = inclX ∘ polynomialPoint z S := by
    funext i
    cases i with
    | none => exact RingHom.congr_fun (IsScalarTower.algebraMap_eq Geom Geom[X] GenericX) z
    | some i => rfl
  rw [hpoint, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp inclX (polynomialPoint z S) P).symm

private theorem degreeOf_le_of_support_subset {P Q : GenericRow} (h : P.support ⊆ Q.support)
    (i : SeedVar) : P.degreeOf i ≤ Q.degreeOf i := by
  apply degreeOf_le_iff.mpr
  intro m hm
  exact le_degreeOf_of_mem_support i (h hm)

/-- Moving one power from variable i to variable j increases the weight by at most d. -/
private theorem moved_weight (w : SeedVar → ℕ) (i j : SeedVar) (P : GenericRow) (d : ℕ)
    (h : w j ≤ w i + d) :
    (MvPolynomial.X j * pderiv i P).weightedTotalDegree w ≤ P.weightedTotalDegree w + d := by
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_X_mul'] at hm
  split_ifs at hm with hj
  · have hn : m - Finsupp.single j 1 + Finsupp.single i 1 ∈ P.support := by
      rw [coeff_pderiv] at hm
      exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hw := le_weightedTotalDegree w hn
    have he := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hj)
    rw [map_add, Finsupp.weight_single, one_smul] at hw
    omega
  · exact (hm rfl).elim

private theorem dotted_weight (w : SeedVar → ℕ) (r P : GenericRow) (d : ℕ)
    (hr : r.support ⊆ P.support)
    (h₀ : w (some 1) ≤ w (some 0) + d) (h₁ : w (some 2) ≤ w (some 1) + d) :
    (dotted r P).weightedTotalDegree w ≤ P.weightedTotalDegree w + d := by
  rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  have hr' : r ∈ restrictWeightedDegree w (P.weightedTotalDegree w + d) := by
    apply mem_restrictWeightedDegree.mpr
    intro m hm
    exact (le_weightedTotalDegree w (hr hm)).trans (Nat.le_add_right _ _)
  have h₀' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (moved_weight w _ _ P d h₀)
  have h₁' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (moved_weight w _ _ P d h₁)
  unfold dotted
  rw [MvPolynomial.C_mul']
  exact (restrictWeightedDegree w _).add_mem ((restrictWeightedDegree w _).add_mem hr' h₀')
    ((restrictWeightedDegree w _).smul_mem (2 : GenericX) h₁')

private theorem seed_weight (P : GenericRow) :
    P.weightedTotalDegree (Pi.single none 1) = seedDegree P := by
  rw [seedDegree, degreeOf_eq_sup, weightedTotalDegree]
  simp only [Finsupp.weight_single_one_apply]

private theorem small_cast_ne_zero (n : ℕ) (hpos : 0 < n) (hsmall : n ≤ 10) :
    (n : GenericX) ≠ 0 := by
  let : CharP GenericX K1.p := charP_of_injective_ringHom (inclConst.comp embed).injective K1.p
  intro hz
  have hlarge : 10 < K1.p := by decide
  exact (not_le_of_gt (hsmall.trans_lt hlarge))
    (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff GenericX K1.p n).mp hz))

private theorem pderiv_moved {P : GenericRow} {i j k : SeedVar} (h : P.degreeOf k = 0) :
    pderiv k (MvPolynomial.X j * pderiv i P) = pderiv k (MvPolynomial.X j : GenericRow) * pderiv i P := by
  have hzero : pderiv k (pderiv i P) = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero ((degreeOf_pderiv_le i k P).trans_eq h))
  rw [pderiv_mul, hzero, mul_zero, add_zero]

/-- If k is absent from f, divisibility by f survives the k partial. -/
private theorem partial_not_dvd {f g : GenericRow} (i k : SeedVar) (a : GenericX)
    (hi : 0 < f.degreeOf i) (hsmall : f.degreeOf i ≤ 10) (hk : f.degreeOf k = 0)
    (ha : a ≠ 0) (hg : pderiv k g = C a * pderiv i f) : ¬ f ∣ g := by
  have hpartial : pderiv i f ≠ 0 :=
    pderiv_ne_zero_of_natCast_ne_zero i f (small_cast_ne_zero _ hi hsmall)
  have hnonzero : C a * pderiv i f ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha) hpartial
  have hdegree : (C a * pderiv i f).degreeOf i ≤ f.degreeOf i - 1 :=
    (degreeOf_C_mul_le _ _ _).trans (degreeOf_pderiv_le_sub_one i f)
  rintro ⟨q, hq⟩
  rw [hq, pderiv_mul, pderiv_eq_zero_of_degreeOf_eq_zero hk, zero_mul, zero_add] at hg
  have hq' : pderiv k q ≠ 0 := by
    intro hz
    exact hnonzero (by rw [← hg, hz, mul_zero])
  rw [← hg, degreeOf_mul_eq (ne_zero_of_degreeOf_ne_zero hi.ne') hq'] at hdegree
  omega

private theorem dotted_relPrime {f r : GenericRow} (hf : Irreducible f)
    (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 10) (htop : f.degreeOf (some 2) = 0)
    (hr : r.support ⊆ f.support) (a : GenericX) (ha : a ≠ 0) :
    IsRelPrime f (dotted r (C a * f)) := by
  have hd (i : SeedVar) : (C a * f).degreeOf i = f.degreeOf i := by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) hf.ne_zero, degreeOf_C, zero_add]
  have hsmall (i : Fin 3) : f.degreeOf (some i) ≤ 10 :=
    (degreeOf_le_weightedTotalDegree (fun j : SeedVar => j.elim 0 (fun _ => 1))
      (some i) (show 0 < (1 : ℕ) by decide) f).trans ht
  have hzero (i : SeedVar) (hi : f.degreeOf i = 0) : pderiv i r = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero
      ((degreeOf_le_of_support_subset hr i).trans_eq hi))
  have htop' : (C a * f).degreeOf (some 2) = 0 := (hd _).trans htop
  apply hf.isRelPrime_iff_not_dvd.mpr
  by_cases h₁ : f.degreeOf (some 1) = 0
  · have h₀ : 0 < f.degreeOf (some 0) := by
      by_contra! h₀
      have hz : jetTotal f ≤ 0 := by
        apply Finset.sup_le
        intro m hm
        have hm₀ := (le_degreeOf_of_mem_support (some 0) hm).trans h₀
        have hm₁ := (le_degreeOf_of_mem_support (some 1) hm).trans_eq h₁
        have hm₂ := (le_degreeOf_of_mem_support (some 2) hm).trans_eq htop
        rw [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_three]
        simp [Nat.eq_zero_of_le_zero hm₀, Nat.eq_zero_of_le_zero hm₁, Nat.eq_zero_of_le_zero hm₂]
      omega
    have h₁' : (C a * f).degreeOf (some 1) = 0 := (hd _).trans h₁
    refine partial_not_dvd (some 0) (some 1) a h₀ (hsmall 0) h₁ ha ?_
    unfold dotted
    rw [pderiv_eq_zero_of_degreeOf_eq_zero h₁']
    simp only [mul_zero, add_zero, map_add, hzero _ h₁, zero_add, pderiv_moved h₁',
      pderiv_X_self, one_mul]
    rw [pderiv_C_mul]
  · refine partial_not_dvd (some 1) (some 2) ((2 : GenericX) * a) (Nat.pos_of_ne_zero h₁)
      (hsmall 1) htop (mul_ne_zero (small_cast_ne_zero 2 (by decide) (by decide)) ha) ?_
    unfold dotted
    rw [map_add, map_add, hzero _ htop, pderiv_moved (i := some 0) (j := some 1) htop',
      pderiv_X_of_ne (by decide : (some 1 : SeedVar) ≠ some 2), zero_mul, add_zero,
      pderiv_C_mul, pderiv_moved htop', pderiv_X_self, one_mul, pderiv_C_mul]
    simp only [zero_add, map_mul, mul_assoc]

theorem proof : K1_13_4_5.c1 := by
  intro f hf hb ht _ htop
  obtain ⟨d, P, hd, hs, hP⟩ := clear_denominators f
  let r := MvPolynomial.map inclX (coefficientDerivative P)
  let A := MvPolynomial.map inclX P
  have hA : A.support = f.support := (support_map_of_injective P inclX_injective).trans hs
  have hr : r.support ⊆ f.support := by
    intro m hm
    rw [← hs, MvPolynomial.mem_support_iff]
    rw [MvPolynomial.mem_support_iff, coeff_map, coeff_coefficientDerivative] at hm
    intro hz
    exact hm (by rw [hz, map_zero, map_zero])
  have htopP : P.degreeOf (some 2) = 0 := by rwa [degreeOf_eq_sup, hs, ← degreeOf_eq_sup]
  have ha : inclX d ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  refine ⟨dotted r A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show A = C (inclX d) * f from hP]
    exact dotted_relPrime hf hb ht htop hr _ ha
  · rw [← seed_weight, ← seed_weight]
    simpa [weightedTotalDegree, hA] using
      dotted_weight (Pi.single none 1) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [jetTotal, weightedTotalDegree, hA] using
      dotted_weight (fun i => i.elim 0 (fun _ => 1)) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [jetIndex, weightedTotalDegree, hA] using
      dotted_weight (fun i => i.elim 0 Fin.val) r A 1 (hA.symm ▸ hr) (by decide) (by decide)
  · intro z S hz
    have hzP : eval (polynomialPoint z S) P = 0 := by
      apply inclX_injective
      rw [map_zero, ← eval_map_point, hP, map_mul, hz, mul_zero]
    have hmap : dotted r A = MvPolynomial.map inclX (dotted (coefficientDerivative P) P) := by
      simp only [dotted, A, r, map_add, map_mul, map_X, pderiv_map, map_ofNat]
    rw [hmap, eval_map_point, eval_dotted P z S htopP, hzP, map_zero, map_zero]

end

end K1_13_4_5_1
end PackSource_K1_13_4_5_1Proof

section PackSource_K1_13_6_3_5_3_6Aux
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_3_6

open Polynomial K1_13_6_3_5_3
open scoped Polynomial WithZero

noncomputable section

variable {F L : Type} [Field F] [Field L]

def jetRatio (e : F[X] →+* L) (i : ℕ) (g : F[X]) : L :=
  e (hasseDeriv i g) / e g

theorem jetRatio_zero (e : F[X] →+* L) {g : F[X]} (hg : e g ≠ 0) :
    jetRatio e 0 g = 1 := by
  simp [jetRatio, hg]

theorem jetRatio_mul (e : F[X] →+* L) {g h : F[X]} (hg : e g ≠ 0) (hh : e h ≠ 0) :
    jetRatio e 1 (g * h) = jetRatio e 1 g + jetRatio e 1 h ∧
    jetRatio e 2 (g * h) =
      jetRatio e 2 g + jetRatio e 1 g * jetRatio e 1 h + jetRatio e 2 h := by
  have h₁ : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  have h₂ : Finset.HasAntidiagonal.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  constructor
  · unfold jetRatio
    rw [hasseDeriv_mul, h₁]
    simp
    field_simp
    ring
  · unfold jetRatio
    rw [hasseDeriv_mul, h₂]
    simp
    field_simp
    ring

theorem jetRatio_pow (e : F[X] →+* L) {g : F[X]} (hg : e g ≠ 0) (m : ℕ) :
    jetRatio e 1 (g ^ m) = (m : L) * jetRatio e 1 g ∧
    jetRatio e 2 (g ^ m) =
      (m : L) * jetRatio e 2 g + (m.choose 2 : L) * jetRatio e 1 g ^ 2 := by
  induction m with
  | zero =>
    simp [jetRatio, hasseDeriv_apply_one]
  | succ m ih =>
    have hm : e (g ^ m) ≠ 0 := by simpa using pow_ne_zero m hg
    obtain ⟨h₁, h₂⟩ := jetRatio_mul e hm hg
    have hc : ((m + 1).choose 2 : L) = (m : L) + (m.choose 2 : L) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add]
    constructor
    · rw [pow_succ, h₁, ih.1, Nat.cast_succ]
      ring
    · rw [pow_succ, h₂, ih.1, ih.2, hc, Nat.cast_succ]
      ring

theorem eval_hasse_le (j : F →+* L) (a : L) (v : Valuation L ℤᵐ⁰) (ha : v a = 1)
    (g : F[X]) (i : ℕ) {w : ℤᵐ⁰} (hw : ∀ n ∈ g.support, v (j (g.coeff n)) ≤ w) :
    v ((hasseDeriv i g).eval₂ j a) ≤ w := by
  rw [hasseDeriv_apply, Polynomial.sum, eval₂_finsetSum]
  apply v.map_sum_le
  intro n hn
  simp only [eval₂_monomial, map_mul, map_pow, ha, one_pow, mul_one]
  have hcast : v (j (n.choose i : F)) ≤ 1 := by
    have hn : ∀ m : ℕ, v (m : L) ≤ 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m hm =>
        rw [Nat.cast_succ]
        exact v.map_add_le hm (by simp)
    simpa only [map_natCast] using hn (n.choose i)
  simpa only [one_mul] using mul_le_mul_of_nonneg hcast (hw n hn) zero_le zero_le

theorem eval_coprime_unit (e : F[X] →+* L) (v : Valuation L ℤᵐ⁰)
    {g h : F[X]} (hint : ∀ p, v (e p) ≤ 1) (hcop : IsCoprime g h)
    (hg : v (e g) < 1) : v (e h) = 1 := by
  obtain ⟨p, q, hpq⟩ := hcop
  refine (hint h).antisymm (le_of_not_gt fun hh => ?_)
  have hmul {p g : F[X]} (hg : v (e g) < 1) : v (e p * e g) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left zero_le (hint p)).trans_lt hg
  have h₀ : v (e p * e g + e q * e h) < 1 :=
    v.map_add_lt (hmul hg) (hmul hh)
  rw [← map_mul, ← map_mul, ← map_add, hpq, map_one, map_one] at h₀
  exact (lt_irrefl _ h₀)

end
end K1_13_6_3_5_3_6
end PackSource_K1_13_6_3_5_3_6Aux

section PackSource_K1_13_6_3_5_3_6Local
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_3_6

open Polynomial K1_13_6_3_5_3
open scoped Polynomial WithZero

noncomputable section

variable {F L : Type} [Field F] [Field L]

private theorem poleOrder_le_log (v : Valuation L ℤᵐ⁰) {x : L}
    {w : ℤᵐ⁰} (hw : w ≠ 0) (h : v x ≤ w) : poleOrder v x ≤ (WithZero.log w).toNat := by
  unfold poleOrder
  by_cases hx : v x = 0
  · simp [hx]
  exact Int.toNat_le_toNat ((WithZero.log_le_log hx hw).2 h)

theorem poleOrder_eq_zero (v : Valuation L ℤᵐ⁰) {x : L} (h : v x ≤ 1) :
    poleOrder v x = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using poleOrder_le_log v one_ne_zero h)

private theorem tuplePole_le_log {σ : Type} [Fintype σ] (v : Valuation L ℤᵐ⁰)
    (u : σ → L) {w : ℤᵐ⁰} (hw : w ≠ 0) (h : ∀ i, v (u i) ≤ w) :
    tuplePole v u ≤ (WithZero.log w).toNat :=
  Finset.sup_le (fun i _ => poleOrder_le_log v hw (h i))

theorem tuplePole_eq_log {σ : Type} [Fintype σ] (v : Valuation L ℤᵐ⁰)
    (u : σ → L) {w : ℤᵐ⁰} (hw : w ≠ 0) (h : ∀ i, v (u i) ≤ w)
    (he : ∃ i, v (u i) = w) : tuplePole v u = (WithZero.log w).toNat := by
  refine (tuplePole_le_log v u hw h).antisymm ?_
  obtain ⟨i, hi⟩ := he
  rw [← hi]
  exact Finset.le_sup (s := Finset.univ) (f := fun j => poleOrder v (u j)) (Finset.mem_univ i)

theorem tuplePole_eq_zero {σ : Type} [Fintype σ] (v : Valuation L ℤᵐ⁰)
    (u : σ → L) (h : ∀ i, v (u i) ≤ 1) : tuplePole v u = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using tuplePole_le_log v u one_ne_zero h)

theorem zeroOrder_eq_zero (v : Valuation L ℤᵐ⁰) {x : L} (h : 1 ≤ v x) :
    zeroOrder v x = 0 := by
  have hlog : 0 ≤ WithZero.log (v x) := WithZero.le_log_of_exp_le (by simpa using h)
  unfold zeroOrder
  omega

theorem log_prod_toNat {ι : Type} (s : Finset ι) (w : ι → ℤᵐ⁰)
    (h : ∀ i ∈ s, 1 ≤ w i) :
    (WithZero.log (∏ i ∈ s, w i)).toNat = ∑ i ∈ s, (WithZero.log (w i)).toNat := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hw : 1 ≤ w i := h i (Finset.mem_insert_self i s)
    have hs k (hk : k ∈ s) : 1 ≤ w k := h k (Finset.mem_insert_of_mem hk)
    have hp : 1 ≤ ∏ k ∈ s, w k := Finset.one_le_prod₀ hs
    have h₁ : 0 ≤ WithZero.log (w i) := WithZero.le_log_of_exp_le (by simpa using hw)
    have h₂ : 0 ≤ WithZero.log (∏ k ∈ s, w k) :=
      WithZero.le_log_of_exp_le (by simpa using hp)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ← ih hs,
      WithZero.log_mul (zero_lt_one.trans_le hw).ne' (zero_lt_one.trans_le hp).ne']
    omega

theorem log_pow_toNat (w : ℤᵐ⁰) (m : ℕ) (h : 1 ≤ w) :
    (WithZero.log (w ^ m)).toNat = m * (WithZero.log w).toNat := by
  have hlog : 0 ≤ WithZero.log w := WithZero.le_log_of_exp_le (by simpa using h)
  rw [WithZero.log_pow, nsmul_eq_mul]
  have hm : 0 ≤ (m : ℤ) * WithZero.log w := mul_nonneg (Int.natCast_nonneg _) hlog
  exact_mod_cast (show (((m : ℤ) * WithZero.log w).toNat : ℤ) =
      ↑(m * (WithZero.log w).toNat) by simp [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg hlog])

/-- When one factor vanishes and its linear Hasse coefficient is a unit,
the largest normalized jet value is the inverse factor value to order one or two. -/
theorem local_jet_max (e : F[X] →+* L) (v : Valuation L ℤᵐ⁰) (g h : F[X]) (m : ℕ)
    (hm : 0 < m) (hg : e g ≠ 0) (hz : v (e g) < 1)
    (hd : v (e (hasseDeriv 1 g)) = 1) (hh : v (e h) = 1)
    (hint : ∀ p i, v (e (hasseDeriv i p)) ≤ 1)
    (hc₁ : v (m : L) = 1) (hc₂ : 2 ≤ m → v (m.choose 2 : L) = 1) :
    (∀ i : Fin 3, v (jetRatio e i.val (g ^ m * h)) ≤ (v (e g))⁻¹ ^ min m 2) ∧
      ∃ i : Fin 3, v (jetRatio e i.val (g ^ m * h)) = (v (e g))⁻¹ ^ min m 2 := by
  let T := (v (e g))⁻¹
  have hT : 1 < T := (one_lt_inv₀ ((v.ne_zero_iff.2 hg).bot_lt)).2 hz
  have hhn : e h ≠ 0 := v.ne_zero_iff.1 (hh.trans_ne one_ne_zero)
  have hgn : e (g ^ m) ≠ 0 := by simpa using pow_ne_zero m hg
  have hfn : e (g ^ m * h) ≠ 0 := by simpa only [map_mul] using mul_ne_zero hgn hhn
  have hr₀ : v (jetRatio e 0 (g ^ m * h)) = 1 := by rw [jetRatio_zero e hfn, map_one]
  have hG₁ : v (jetRatio e 1 g) = T := by rw [jetRatio, v.map_div, hd, one_div]
  have hG₂ : v (jetRatio e 2 g) ≤ T := by
    rw [jetRatio, v.map_div, div_eq_mul_inv]
    exact mul_le_of_le_one_left zero_le (hint g 2)
  have hH (i : ℕ) : v (jetRatio e i h) ≤ 1 := by
    rw [jetRatio, v.map_div, hh, div_one]
    exact hint h i
  have hmul {x y : L} (hx : v x ≤ 1) (hy : v y ≤ T) : v (x * y) ≤ T := by
    rw [map_mul]
    exact (mul_le_of_le_one_left zero_le hx).trans hy
  obtain ⟨hp₁, hp₂⟩ := jetRatio_pow e hg m
  obtain ⟨hf₁, hf₂⟩ := jetRatio_mul e hgn hhn
  rw [hp₁] at hf₁
  have hleft : v ((m : L) * jetRatio e 1 g) = T := by rw [map_mul, hc₁, hG₁, one_mul]
  have hR₁ : v (jetRatio e 1 (g ^ m * h)) = T := by
    rw [hf₁, v.map_add_eq_of_lt_left ((hH 1).trans_lt (hT.trans_eq hleft.symm)), hleft]
  have hR₂ : jetRatio e 2 (g ^ m * h) = (m.choose 2 : L) * jetRatio e 1 g ^ 2 +
      ((m : L) * jetRatio e 2 g + jetRatio e 2 h +
        jetRatio e 1 h * ((m : L) * jetRatio e 1 g)) := by
    rw [hf₂, hp₁, hp₂]
    ring
  have hsmall : v ((m : L) * jetRatio e 2 g + jetRatio e 2 h +
        jetRatio e 1 h * ((m : L) * jetRatio e 1 g)) ≤ T :=
    v.map_add_le (v.map_add_le (hmul hc₁.le hG₂) ((hH 2).trans hT.le))
      (hmul (hH 1) hleft.le)
  by_cases h₂ : 2 ≤ m
  · have hTT : T < T ^ 2 := by
      rw [pow_two]
      exact lt_mul_of_one_lt_right (zero_lt_one.trans hT) hT
    have hmain : v ((m.choose 2 : L) * jetRatio e 1 g ^ 2) = T ^ 2 := by
      rw [map_mul, map_pow, hc₂ h₂, hG₁, one_mul]
    have hR₂' : v (jetRatio e 2 (g ^ m * h)) = T ^ 2 := by
      rw [hR₂, v.map_add_eq_of_lt_left (hsmall.trans_lt (hTT.trans_eq hmain.symm)), hmain]
    rw [min_eq_right h₂]
    refine ⟨fun i => ?_, ⟨2, hR₂'⟩⟩
    fin_cases i
    · exact hr₀.trans_le (hT.le.trans hTT.le)
    · exact hR₁.trans_le hTT.le
    · exact hR₂'.le
  · have hmin : min m 2 = 1 := by omega
    have hz₂ : m.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hmin, pow_one]
    refine ⟨fun i => ?_, ⟨1, hR₁⟩⟩
    fin_cases i
    · exact hr₀.trans_le hT.le
    · exact hR₁.le
    · rw [hR₂, hz₂, Nat.cast_zero, zero_mul, zero_add]
      exact hsmall

end
end K1_13_6_3_5_3_6
end PackSource_K1_13_6_3_5_3_6Local

section PackSource_K1_13_6_3_5_3_6Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_3_6

open Polynomial K1_13_6_3_5_3
open scoped Polynomial WithZero

noncomputable section

variable {F L : Type} [Field F] [Field L]

private theorem factor_value_prod (e : F[X] →+* L) (v : Valuation L ℤᵐ⁰)
    {f : F[X]} (B : JetFactors f) :
    v (e f) = ∏ i, v (e (B.factor i)) ^ B.multiplicity i := by
  rw [congrArg e B.product_eq, map_prod, map_prod]
  simp only [map_pow]

/-- If the valuation is trivial on the old field, coprimality and separability
give a unique possible vanishing factor and a unit first derivative there. -/
private theorem trivial_branch (j : F →+* L) (a : L) (v : Valuation L ℤᵐ⁰)
    (ha : v a = 1) (hj : ∀ x : F, x ≠ 0 → v (j x) = 1)
    (he : Function.Injective (eval₂RingHom j a)) {f : F[X]} (B : JetFactors f) {N : ℕ} :
    tuplePole v (coefficientTuple (N := N) j f) =
        ∑ i, B.multiplicity i * poleOrder v ((B.factor i).eval₂ j a) ∧
      tuplePole v (fun i : Fin 3 => jetRatio (eval₂RingHom j a) i.val f) =
        ∑ i, min (B.multiplicity i) 2 * zeroOrder v ((B.factor i).eval₂ j a) := by
  classical
  let e := eval₂RingHom j a
  change _ ∧ tuplePole v (fun i : Fin 3 => jetRatio e i.val f) =
    ∑ i, min (B.multiplicity i) 2 * zeroOrder v (e (B.factor i))
  have hj' (x : F) : v (j x) ≤ 1 := by
    by_cases hx : x = 0 <;> simp [hx, hj]
  have hcast' (n : ℕ) (hn : (n : F) ≠ 0) : v (n : L) = 1 := by
    simpa only [map_natCast] using hj (n : F) hn
  have hint (p : F[X]) (i : ℕ) : v (e (hasseDeriv i p)) ≤ 1 :=
    eval_hasse_le j a v ha p i (fun n _ => hj' (p.coeff n))
  have heint (p : F[X]) : v (e p) ≤ 1 := by
    simpa using hint p 0
  constructor
  · rw [tuplePole_eq_zero v (coefficientTuple (N := N) j f) (fun i => hj' (f.coeff i.val))]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hi := poleOrder_eq_zero v (heint (B.factor i))
    change B.multiplicity i * poleOrder v (e (B.factor i)) = 0
    rw [hi, mul_zero]
  · by_cases hz : ∃ r, v (e (B.factor r)) < 1
    · obtain ⟨r, hr⟩ := hz
      have hu (i : Fin B.count) (hi : i ≠ r) : v (e (B.factor i)) = 1 :=
        eval_coprime_unit e v heint (B.coprime r i hi.symm) hr
      have hd : v (e (hasseDeriv 1 (B.factor r))) = 1 := by
        rw [hasseDeriv_one']
        exact eval_coprime_unit e v heint (B.separable r) hr
      let rest := ∏ i ∈ Finset.univ.erase r, B.factor i ^ B.multiplicity i
      have hf : f = B.factor r ^ B.multiplicity r * rest :=
        B.product_eq.trans
          (Finset.mul_prod_erase _ (fun i => B.factor i ^ B.multiplicity i)
            (Finset.mem_univ r)).symm
      have hrest : v (e rest) = 1 := by
        unfold rest
        rw [map_prod, map_prod]
        simp only [map_pow]
        apply Finset.prod_eq_one
        intro i hi
        rw [hu i (Finset.ne_of_mem_erase hi), one_pow]
      have hne : e (B.factor r) ≠ 0 := by
        intro h
        apply (B.monic r).ne_zero
        exact he (h.trans (map_zero e).symm)
      obtain ⟨hmax, hattain⟩ := local_jet_max e v (B.factor r) rest (B.multiplicity r)
        (B.positive r) hne hr hd hrest hint
        (hcast' _ (B.first_scalar r)) (fun hm => hcast' _ (B.second_scalar r hm))
      have hmax_ne : (v (e (B.factor r)))⁻¹ ^ min (B.multiplicity r) 2 ≠ 0 :=
        pow_ne_zero _ (inv_ne_zero (v.ne_zero_iff.mpr hne))
      rw [show tuplePole v (fun i : Fin 3 => jetRatio e i.val f) =
          tuplePole v (fun i : Fin 3 => jetRatio e i.val (B.factor r ^ B.multiplicity r * rest))
          from congrArg (fun g => tuplePole v (fun i : Fin 3 => jetRatio e i.val g)) hf,
        tuplePole_eq_log v _ hmax_ne hmax hattain,
        Finset.sum_eq_single_of_mem r (Finset.mem_univ r) (fun i _ hi => by
          rw [zeroOrder_eq_zero v (hu i hi).ge, mul_zero])]
      have hinv : 1 ≤ (v (e (B.factor r)))⁻¹ :=
        ((one_lt_inv₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hne))).2 hr).le
      rw [log_pow_toNat _ _ hinv, WithZero.log_inv, zeroOrder]
    · have hu (i : Fin B.count) : v (e (B.factor i)) = 1 :=
        (heint _).antisymm (le_of_not_gt fun hi => hz ⟨i, hi⟩)
      have hf : v (e f) = 1 := by simp [factor_value_prod e v B, hu]
      rw [tuplePole_eq_zero v _ (fun i => by
        rw [jetRatio, v.map_div, hf, div_one]
        exact hint _ _)]
      have hz₀ (i : Fin B.count) : zeroOrder v (e (B.factor i)) = 0 :=
        zeroOrder_eq_zero v (hu i).ge
      simp [hz₀]

/-- The monic factors have Gauss value at least one. Their values multiply,
and all Hasse evaluations are bounded by the original Gauss value. -/
private theorem gauss_branch (j : F →+* L) (a : L) (v : Valuation L ℤᵐ⁰)
    (ha : v a = 1)
    (hG : ∀ g : F[X], v (g.eval₂ j a) = g.support.sup (fun i => v (j (g.coeff i))))
    {f : F[X]} (B : JetFactors f) {N : ℕ} (hN : f.natDegree < N) :
    tuplePole v (coefficientTuple (N := N) j f) =
        ∑ i, B.multiplicity i * poleOrder v ((B.factor i).eval₂ j a) ∧
      tuplePole v (fun i : Fin 3 => jetRatio (eval₂RingHom j a) i.val f) =
        ∑ i, min (B.multiplicity i) 2 * zeroOrder v ((B.factor i).eval₂ j a) := by
  let e := eval₂RingHom j a
  have hbound (g : F[X]) (n : ℕ) : v (j (g.coeff n)) ≤ v (e g) := by
    by_cases hn : g.coeff n = 0
    · simp [hn]
    · change _ ≤ v (g.eval₂ j a)
      rw [hG]
      exact Finset.le_sup (s := g.support) (f := fun i => v (j (g.coeff i))) (mem_support_iff.mpr hn)
  have hfactor (i : Fin B.count) : 1 ≤ v (e (B.factor i)) := by
    have hi := hbound (B.factor i) (B.factor i).natDegree
    simpa [(B.monic i).coeff_natDegree] using hi
  have hf : 1 ≤ v (e f) := by
    rw [factor_value_prod e v B]
    exact Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (hfactor i))
  have hfv : v (e f) ≠ 0 := (zero_lt_one.trans_le hf).ne'
  have hfn : f ≠ 0 := by
    intro h
    exact hfv (by rw [h, map_zero, map_zero])
  obtain ⟨n, hn, hmax⟩ :=
    f.support.exists_mem_eq_sup (support_nonempty.mpr hfn) (fun i => v (j (f.coeff i)))
  have hFin : n < N := (le_natDegree_of_ne_zero (mem_support_iff.mp hn)).trans_lt hN
  constructor
  · rw [tuplePole_eq_log v (coefficientTuple (N := N) j f) hfv (fun i => hbound f i.val)
        ⟨⟨n, hFin⟩, hmax.symm.trans (hG f).symm⟩, factor_value_prod e v B,
      log_prod_toNat _ _ (fun i _ => one_le_pow₀ (hfactor i))]
    apply Finset.sum_congr rfl
    intro i _
    exact log_pow_toNat _ _ (hfactor i)
  · rw [tuplePole_eq_zero v (fun i : Fin 3 => jetRatio e i.val f) (fun i => by
      rw [jetRatio, v.map_div]
      apply (div_le_one₀ (zero_lt_one.trans_le hf)).2
      exact eval_hasse_le j a v ha f i.val (fun n _ => hbound f n))]
    have hz (i : Fin B.count) : zeroOrder v ((B.factor i).eval₂ j a) = 0 :=
      zeroOrder_eq_zero v (hfactor i)
    simp [hz]

theorem proof : K1_13_6_3_5_3.c6 := by
  intro F L _ _ j a f B v N hN ha he hG
  have hjet : ratios (jetTuple (n := 3) j a f) 0 =
      fun i : Fin 3 => jetRatio (eval₂RingHom j a) i.val f := by
    funext i
    simp [ratios, jetTuple, jetRatio]
  rw [hjet]
  rcases hG with hj | hG
  · exact trivial_branch j a v ha hj he B
  · exact gauss_branch j a v ha hG B hN

end
end K1_13_6_3_5_3_6
end PackSource_K1_13_6_3_5_3_6Proof

section PackSource_K1_13_7_3Transfer
set_option autoImplicit true
namespace K1_13_7_3
noncomputable section

open K1_13 K1_13_4 Polynomial

theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX

theorem support_toGeneric (P : Row 3) :
    (MvPolynomial.map inclX P).support = P.support :=
  MvPolynomial.support_map_of_injective P inclX_injective

private theorem support_scalar (u : GenericX) (hu : u ≠ 0) (P : Lower) :
    (MvPolynomial.C u * P).support = P.support := by
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hu]

/-- Clear one common denominator, which changes neither of the two jet
degree caps. -/
theorem clear_denominators (R : Lower) :
    ∃ (d : Geom[X]) (Q : Row 3), d ≠ 0 ∧ Q.support = R.support ∧
      MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R := by
  classical
  let M := nonZeroDivisors Geom[X]
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 3 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : inclX (d : Geom[X]) ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  have hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R := by
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change inclX (num a) = (d : Geom[X]) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 3).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  exact ⟨d, Q, hd, (support_toGeneric Q).symm.trans
    (congrArg MvPolynomial.support hQ |>.trans (support_scalar _ hi _)), hQ⟩

theorem eval_toGeneric (Q : Row 3) (S : Geom[X]) :
    MvPolynomial.eval (trajectory S) (MvPolynomial.map inclX Q) = inclX (atJet Q S) := by
  rw [atJet, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp inclX (jet S) Q).symm

private theorem map_shift (Q : Row 3) (S : Geom[X]) :
    MvPolynomial.map inclX (shiftJet Q S) =
      K1_13_4.translate (trajectory S) (MvPolynomial.map inclX Q) := by
  have hc : (MvPolynomial.map (σ := Fin 3) inclX).comp MvPolynomial.C =
      MvPolynomial.C.comp inclX := by
    apply RingHom.ext
    intro x
    simp
  unfold K1_13.shiftJet
  rw [MvPolynomial.eval₂_comp_left]
  change _ = MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (trajectory S i)) (MvPolynomial.map inclX Q)
  rw [MvPolynomial.eval₂_map, hc]
  congr 1
  funext i
  simp [trajectory]

theorem order_toGeneric (Q : Row 3) (S : Geom[X]) (m : ℕ) :
    LowerOrder (MvPolynomial.map inclX Q) (trajectory S) m ↔ OrderAt Q S m := by
  unfold LowerOrder OrderAt
  rw [← map_shift, support_toGeneric]

theorem order_clear {Q : Row 3} {R : Lower} {d : Geom[X]} (hd : d ≠ 0)
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R)
    (S : Geom[X]) {m : ℕ} (hR : LowerOrder R (trajectory S) m) : OrderAt Q S m := by
  apply (order_toGeneric Q S m).mp
  unfold LowerOrder at hR ⊢
  rw [hQ, map_mul, show K1_13_4.translate (trajectory S) (MvPolynomial.C (inclX d)) =
    MvPolynomial.C (inclX d) by simp [K1_13_4.translate],
    support_scalar _ ((map_ne_zero_iff inclX inclX_injective).mpr hd)]
  exact hR

private theorem constantCoeff_translate (A : Lower) (y : Fin 3 → GenericX) :
    (K1_13_4.translate y A).coeff 0 = MvPolynomial.eval y A := by
  have h : (MvPolynomial.constantCoeff.comp (K1_13_4.translate y) : Lower →+* GenericX) =
      MvPolynomial.eval y := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [K1_13_4.translate]
    · intro i
      simp [K1_13_4.translate]
  exact RingHom.congr_fun h A

/-- A factor whose value is nonzero at the centre has no effect on the
least total degree of a shifted row. -/
theorem order_cancel {A P : Lower} {y : Fin 3 → GenericX} {d : ℕ}
    (hA : MvPolynomial.eval y A ≠ 0) (h : LowerOrder (A * P) y d) : LowerOrder P y d := by
  classical
  intro a ha
  by_contra! hlt
  let U := K1_13_4.translate y A
  let V := K1_13_4.translate y P
  obtain ⟨m, hm, hmin⟩ := V.support.exists_min_image (fun e => e.degree) ⟨a, ha⟩
  have hsmall : m.degree < d := lt_of_le_of_lt (hmin a ha) hlt
  have hcoeff : (U * V).coeff m = U.coeff 0 * V.coeff m := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_single (0, m)
    · intro z hz hne
      have hzsum : z.1 + z.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      have hz₁ : z.1 ≠ 0 := by
        intro hzero
        apply hne
        exact Prod.ext hzero (by simpa [hzero] using hzsum)
      have hpos : 0 < z.1.degree :=
        Nat.pos_of_ne_zero (fun hh => hz₁ ((Finsupp.degree_eq_zero_iff _).mp hh))
      have hsum : z.1.degree + z.2.degree = m.degree := by
        rw [← map_add, hzsum]
      have hzero : V.coeff z.2 = 0 := by
        by_contra hn
        have hle := hmin z.2 (MvPolynomial.mem_support_iff.mpr hn)
        omega
      rw [hzero, mul_zero]
    · intro hn
      exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add m))).elim
  have hu : U.coeff 0 ≠ 0 := by rwa [show U = K1_13_4.translate y A by rfl, constantCoeff_translate]
  have hout : m ∈ (U * V).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero hu (MvPolynomial.mem_support_iff.mp hm)
  have hmem : m ∈ (K1_13_4.translate y (A * P)).support := by simpa only [map_mul] using hout
  exact (not_le_of_gt hsmall) (h m hmem)

end
end K1_13_7_3
end PackSource_K1_13_7_3Transfer

section PackSource_K1_13_7_3Split
set_option autoImplicit true
namespace K1_13_7_3
noncomputable section

open K1_13 K1_13_7 Polynomial
open K1_13_4 (inclX lowerIndex LowerOrder trajectory)

/-- Pay once for each high-exponent irreducible factor, and remove its
full power. The removed product divides a power of the purchased product. -/
def c1 : Prop :=
  ∀ R : K1_13_4.Lower, R ≠ 0 → ∀ b j τ : ℕ, 0 < τ →
    R.totalDegree ≤ b → lowerIndex R ≤ j →
    ∃ H A P : K1_13_4.Lower,
      H ≠ 0 ∧ P ≠ 0 ∧ R = A * P ∧ A ∣ H ^ b ∧
      H.totalDegree ≤ b / τ ∧ lowerIndex H ≤ j / τ ∧
      P.totalDegree ≤ b ∧ lowerIndex P ≤ j ∧ LowPowers P τ

/-- A combination of Hasse partials for the remaining factors. A partial
of order at most 33183 loses at most that much at any lower-jet point. -/
def c2 : Prop :=
  ∀ P : K1_13_4.Lower, P ≠ 0 → P.totalDegree ≤ 952630000 →
    lowerIndex P ≤ 322000000 → LowPowers P 33184 →
    ∃ Q : K1_13_4.Lower, Q ≠ 0 ∧ Q.totalDegree ≤ 952630000 ∧
      lowerIndex Q ≤ 322000000 ∧ IsRelPrime P Q ∧
      ∀ y, LowerOrder P y 41481 → LowerOrder Q y 8298

private theorem caps_of_support {Q : Row 3} {R : K1_13_4.Lower} {b j : ℕ}
    (hs : Q.support = R.support) (hb : R.totalDegree ≤ b) (hj : lowerIndex R ≤ j) :
    LowerCaps Q b j := by
  simpa only [LowerCaps, MvPolynomial.totalDegree, indexDegree, lowerIndex, hs] using And.intro hb hj

private theorem ne_of_support {Q : Row 3} {R : K1_13_4.Lower}
    (hs : Q.support = R.support) (hR : R ≠ 0) : Q ≠ 0 :=
  MvPolynomial.support_nonempty.mp (hs ▸ MvPolynomial.support_nonempty.mpr hR)

private theorem index_eq_weighted (P : Row 3) :
    indexDegree P = MvPolynomial.weightedTotalDegree Fin.val P := by
  unfold indexDegree MvPolynomial.weightedTotalDegree
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]

private theorem caps_mul {P Q : Row 3} {b₁ j₁ b₂ j₂ : ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hp : LowerCaps P b₁ j₁) (hq : LowerCaps Q b₂ j₂) :
    LowerCaps (P * Q) (b₁ + b₂) (j₁ + j₂) := by
  refine ⟨(MvPolynomial.totalDegree_mul P Q).trans (Nat.add_le_add hp.1 hq.1), ?_⟩
  rw [index_eq_weighted, MvPolynomial.weightedTotalDegree_mul _ _ _ hP hQ,
    ← index_eq_weighted, ← index_eq_weighted]
  exact Nat.add_le_add hp.2 hq.2

private theorem proper_clear {P Q : K1_13_4.Lower} {P' Q' : Row 3} {dP dQ : Geom[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hrel : IsRelPrime P Q)
    (hdP : dP ≠ 0) (hdQ : dQ ≠ 0)
    (hmP : MvPolynomial.map inclX P' = MvPolynomial.C (inclX dP) * P)
    (hmQ : MvPolynomial.map inclX Q' = MvPolynomial.C (inclX dQ) * Q) :
    IsRelPrime (genericRow P') (genericRow Q') := by
  let i := algebraMap GenericX GeometricX
  have hu (x : Geom[X]) (hx : x ≠ 0) : IsUnit (MvPolynomial.C (σ := Fin 3) (i (inclX x))) :=
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff i i.injective).mpr
      ((map_ne_zero_iff inclX inclX_injective).mpr hx))).map MvPolynomial.C
  have hg (A : Row 3) (B : K1_13_4.Lower) (d : Geom[X])
      (h : MvPolynomial.map inclX A = MvPolynomial.C (inclX d) * B) :
      genericRow A = MvPolynomial.C (i (inclX d)) * MvPolynomial.map i B := by
    unfold genericRow
    change MvPolynomial.map (i.comp inclX) A = _
    rw [← MvPolynomial.map_map, h, map_mul, MvPolynomial.map_C]
  rw [hg P' P dP hmP, hg Q' Q dQ hmQ,
    isRelPrime_mul_unit_left_left (hu dP hdP), isRelPrime_mul_unit_left_right (hu dQ hdQ)]
  exact relPrime_map_field P Q hP hQ hrel

theorem of_children (h1 : c1) (h2 : c2) : K1_13_7.c3 := by
  intro E
  let R := MvPolynomial.map inclX E.residual
  have hsR : E.residual.support = R.support := (support_toGeneric _).symm
  have hnR : R ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.map_injective _ inclX_injective)).mpr E.residual_ne
  have hbR : R.totalDegree ≤ 952630000 := by
    simpa only [MvPolynomial.totalDegree, hsR] using E.residual_total
  have hjR : lowerIndex R ≤ 322000000 := by
    simpa only [lowerIndex, indexDegree, hsR] using E.residual_index
  obtain ⟨H, A, P, hnH, hnP, heq, hdiv, hbH, hjH, hbP, hjP, hlow⟩ :=
    h1 R hnR 952630000 322000000 33184 (by decide) hbR hjR
  obtain ⟨Q, hnQ, hbQ, hjQ, hrel, horderQ⟩ := h2 P hnP hbP hjP hlow
  obtain ⟨dH, H', _, hsH, hmH⟩ := clear_denominators H
  obtain ⟨dP, P', hdP, hsP, hmP⟩ := clear_denominators P
  obtain ⟨dQ, Q', hdQ, hsQ, hmQ⟩ := clear_denominators Q
  have hnH' := ne_of_support hsH hnH
  have hcH : LowerCaps H' 28707 9703 := caps_of_support hsH hbH hjH
  have hcap : LowerCaps (E.common * H') 35007 12106 :=
    caps_mul E.common_ne hnH' ⟨E.common_total, E.common_index⟩ hcH
  refine ⟨E.common * H', P', Q', mul_ne_zero E.common_ne hnH', hcap,
    caps_of_support hsP hbP hjP, caps_of_support hsQ hbQ hjQ,
    ⟨ne_of_support hsP hnP, ne_of_support hsQ hnQ, proper_clear hnP hnQ hrel hdP hdQ hmP hmQ⟩, ?_⟩
  intro S hS
  by_cases hd : atJet (E.common * H') S = 0
  · exact Or.inl hd
  right
  have hc : atJet E.common S ≠ 0 := fun h => hd (by
    simp [atJet, show MvPolynomial.eval (jet S) E.common = 0 from h])
  have hHval : MvPolynomial.eval (trajectory S) H ≠ 0 := by
    intro hz
    have hh := eval_toGeneric H' S
    rw [hmH, map_mul, hz, mul_zero] at hh
    have hz' : atJet H' S = 0 := inclX_injective (hh.symm.trans (map_zero _).symm)
    exact hd (by simp [atJet, show MvPolynomial.eval (jet S) H' = 0 from hz'])
  have hAval : MvPolynomial.eval (trajectory S) A ≠ 0 := by
    have hh := map_dvd (MvPolynomial.eval (trajectory S)) hdiv
    rw [map_pow] at hh
    intro hz
    exact pow_ne_zero _ hHval (zero_dvd_iff.mp (hz ▸ hh))
  have hRord : LowerOrder R (trajectory S) 41481 :=
    (order_toGeneric E.residual S _).mpr (hS.resolve_left hc)
  rw [heq] at hRord
  have hPord := order_cancel hAval hRord
  exact ⟨order_clear hdP hmP S hPord, order_clear hdQ hmQ S (horderQ _ hPord)⟩

end
end K1_13_7_3
end PackSource_K1_13_7_3Split

section PackSource_K1_13_7_3_2Proof
set_option autoImplicit true
namespace K1_13_7_3_2
noncomputable section

open K1_13 K1_13_4 MvPolynomial UniqueFactorizationMonoid

private abbrev Exponent := Fin 3 →₀ ℕ

private abbrev iterPartial (i : Fin 3) (a : ℕ) (P : Lower) : Lower :=
  (pderiv (R := GenericX) i)^[a] P

private theorem natCast_ne_zero {n : ℕ} (hpos : 0 < n) (hn : n < K1.p) :
    (n : GenericX) ≠ 0 := by
  let _ : CharP GenericX K1.p :=
    charP_of_injective_ringHom (inclConst.comp embed).injective K1.p
  intro hz
  exact (not_le_of_gt hn) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff _ _ _).mp hz))

private theorem source_support (i : Fin 3) (a : ℕ) (P : Lower)
    {m : Exponent} (hm : m ∈ (iterPartial i a P).support) :
    m + Finsupp.single i a ∈ P.support := by
  induction a generalizing m with
  | zero => simpa [iterPartial] using hm
  | succ a ih =>
    have hs : m + Finsupp.single i 1 ∈ (iterPartial i a P).support := by
      rw [MvPolynomial.mem_support_iff] at hm ⊢
      intro hz
      apply hm
      change ((pderiv (R := GenericX) i)^[a + 1] P).coeff m = 0
      rw [Function.iterate_succ_apply', coeff_pderiv, hz, zero_mul]
    simpa only [add_assoc, ← Finsupp.single_add, Nat.add_comm 1 a] using ih hs

private theorem translate_pderiv (i : Fin 3) (P : Lower) (y : Fin 3 → GenericX) :
    translate y (pderiv i P) = pderiv i (translate y P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [K1_13_4.translate]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P j hP =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hP, map_mul, pderiv_mul]
    by_cases hj : j = i
    · subst j
      simp [K1_13_4.translate, map_add]
    · simp [K1_13_4.translate, map_add, pderiv_X_of_ne hj]

private theorem translate_iter (i : Fin 3) (P : Lower) (y : Fin 3 → GenericX) (a : ℕ) :
    translate y (iterPartial i a P) = iterPartial i a (translate y P) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [iterPartial, Function.iterate_succ_apply'] at ih ⊢
    rw [translate_pderiv, ih]

/-- Below the characteristic, ordinary iterated partials give the same
factor avoidance as Hasse partials. Each Leibniz step reduces the extracted
power by one and leaves a nonzero residual modulo the prime. -/
private theorem exact_iter_not_dvd (i : Fin 3) {f : Lower} (hf : Prime f)
    (hsep : ¬ f ∣ pderiv i f) (a : ℕ) (ha : a < K1.p) {U : Lower} (hU : ¬ f ∣ U) :
    ¬ f ∣ iterPartial i a (f ^ a * U) := by
  induction a generalizing U with
  | zero => simpa [iterPartial] using hU
  | succ a ih =>
    let V := ((a + 1 : ℕ) : Lower) * (pderiv i f * U) + f * pderiv i U
    have hstep : pderiv i (f ^ (a + 1) * U) = f ^ a * V := by
      rw [pderiv_mul, pderiv_pow, Nat.add_sub_cancel, pow_succ f a]
      dsimp only [V]
      ring
    have hu : IsUnit ((a + 1 : ℕ) : Lower) := by
      rw [← map_natCast (C : GenericX →+* Lower)]
      exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero (Nat.succ_pos a) ha)).map C
    have hV : ¬ f ∣ V := by
      intro hd
      have h := (dvd_add_left (dvd_mul_right f (pderiv i U))).mp hd
      exact (hf.dvd_or_dvd (hu.dvd_mul_left.mp h)).elim hsep hU
    change ¬ f ∣ (pderiv (R := GenericX) i)^[a + 1] (f ^ (a + 1) * U)
    rw [Function.iterate_succ_apply, hstep]
    exact ih (Nat.lt_of_succ_lt ha) hV

private theorem exists_separant {f : Lower} (hf : Prime f) (hb : f.totalDegree < K1.p) :
    ∃ i : Fin 3, ¬ f ∣ pderiv i f := by
  have hv : f.vars.Nonempty := by
    by_contra! he
    have heq := vars_eq_empty_iff_eq_C.mp he
    have hn : f.coeff 0 ≠ 0 := by
      intro hz
      exact hf.ne_zero (by rw [heq, hz, map_zero])
    exact hf.not_isUnit (heq ▸ (isUnit_iff_ne_zero.mpr hn).map C)
  obtain ⟨i, hi⟩ := hv
  have hpos := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hc := natCast_ne_zero hpos ((degreeOf_le_totalDegree f i).trans_lt hb)
  have hn := pderiv_ne_zero_of_natCast_ne_zero i f hc
  have hdeg := degreeOf_pderiv_le_sub_one i f
  refine ⟨i, ?_⟩
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hn (by rw [hg, h, mul_zero])
  rw [hg, degreeOf_mul_eq hf.ne_zero hg0] at hdeg
  omega

private theorem exact_exponent {P f : Lower} (hf : Prime f)
    (hlow : K1_13_7_3.LowPowers P 33184) :
    ∃ a < 33184, f ^ a ∣ P ∧ ¬ f ^ (a + 1) ∣ P := by
  classical
  have hex : ∃ n : ℕ, ¬ f ^ n ∣ P := ⟨33184, hlow f hf⟩
  have hpos : 0 < Nat.find hex := by
    by_contra! h
    have hz : Nat.find hex = 0 := by omega
    exact Nat.find_spec hex (by simp [hz])
  have hle := Nat.find_min' hex (hlow f hf)
  let a := Nat.find hex - 1
  have ha : a + 1 = Nat.find hex := Nat.sub_add_cancel hpos
  refine ⟨a, by omega, not_not.mp (Nat.find_min hex (by omega : a < Nat.find hex)), ?_⟩
  rw [ha]
  exact Nat.find_spec hex

private theorem index_weight (m : Exponent) :
    Finsupp.weight (R := ℕ) (Fin.val : Fin 3 → ℕ) m = m.sum (fun i e => i.val * e) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]

/-- The two degree caps and the simultaneous order conditions are linear
constraints on the prospective cutter. -/
private def admissible (P : Lower) : Submodule GenericX Lower where
  carrier := {Q |
    (∀ m ∈ Q.support, m.degree ≤ 952630000 ∧
      Finsupp.weight (R := ℕ) (Fin.val : Fin 3 → ℕ) m ≤ 322000000) ∧
    ∀ y, LowerOrder P y 41481 → LowerOrder Q y 8298}
  zero_mem' := by
    simp [LowerOrder]
  add_mem' := by
    intro Q R hQ hR
    change (_ ∧ _) at hQ hR ⊢
    refine ⟨fun m hm => ?_, fun y hy m hm => ?_⟩
    · exact (Finset.mem_union.mp (support_add hm)).elim (hQ.1 m) (hR.1 m)
    · rw [map_add] at hm
      exact (Finset.mem_union.mp (support_add hm)).elim (hQ.2 y hy m) (hR.2 y hy m)
  smul_mem' := by
    intro c Q hQ
    change (_ ∧ _) at hQ ⊢
    rw [Algebra.smul_def]
    change (_ ∧ ∀ y, LowerOrder P y 41481 → LowerOrder (C c * Q) y 8298)
    refine ⟨fun m hm => hQ.1 m (support_C_mul_le Q c hm), fun y hy m hm => ?_⟩
    rw [map_mul, show translate y (C c) = C c by simp [K1_13_4.translate]] at hm
    exact hQ.2 y hy m (support_C_mul_le (translate y Q) c hm)

private theorem iter_mem_admissible {P : Lower} (hb : P.totalDegree ≤ 952630000)
    (hj : lowerIndex P ≤ 322000000) (i : Fin 3) {a : ℕ} (ha : a < 33184) :
    iterPartial i a P ∈ admissible P := by
  refine ⟨fun m hm => ?_, fun y hy m hm => ?_⟩
  · have hs := source_support i a P hm
    have htotal := (le_totalDegree hs).trans hb
    change (m + Finsupp.single i a).degree ≤ _ at htotal
    rw [map_add, Finsupp.degree_single] at htotal
    have hindex := (Finset.le_sup (f := fun x : Exponent => x.sum (fun j e => j.val * e)) hs).trans hj
    rw [← index_weight, map_add] at hindex
    exact ⟨(Nat.le_add_right _ _).trans htotal, (Nat.le_add_right _ _).trans hindex⟩
  · rw [translate_iter] at hm
    have hord := hy _ (source_support i a (translate y P) hm)
    change 41481 ≤ (m + Finsupp.single i a).degree at hord
    change 8298 ≤ m.degree
    rw [map_add, Finsupp.degree_single] at hord
    omega

theorem proof : K1_13_7_3.c2 := by
  classical
  intro P hP hb hj hlow
  let partials : Set Lower := {Q | ∃ (i : Fin 3) (a : ℕ), a < 33184 ∧ Q = iterPartial i a P}
  let N := Submodule.span GenericX partials
  have hN : N ≤ admissible P := Submodule.span_le.mpr (by
    rintro _ ⟨i, a, ha, rfl⟩
    exact iter_mem_admissible hb hj i ha)
  have hPN : P ∈ N := Submodule.subset_span ⟨0, 0, by decide, rfl⟩
  let _ : StrongNormalizationMonoid Lower := UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  let factors := (normalizedFactors P).toFinset
  let forbidden : Option ↥factors → Submodule GenericX N
    | none => ⊥
    | some f => ((Ideal.span {f.val}).restrictScalars GenericX).comap N.subtype
  have hproper (k : Option ↥factors) : forbidden k ≠ ⊤ := by
    cases k with
    | none =>
      intro he
      have hm : (⟨P, hPN⟩ : N) ∈ forbidden none := he ▸ Submodule.mem_top
      exact hP (congrArg Subtype.val ((Submodule.mem_bot GenericX).mp hm))
    | some f =>
      have hm : f.val ∈ normalizedFactors P := Multiset.mem_toFinset.mp f.property
      have hf := prime_of_normalized_factor f.val hm
      have hfp := dvd_of_mem_normalizedFactors hm
      obtain ⟨i, hi⟩ := exists_separant hf
        (((totalDegree_le_of_dvd_of_isDomain hfp hP).trans hb).trans_lt (by decide))
      obtain ⟨a, ha, hdiv, hnext⟩ := exact_exponent hf hlow
      obtain ⟨U, hU⟩ := hdiv
      have hnd : ¬ f.val ∣ U := by
        rintro ⟨V, hv⟩
        exact hnext ⟨V, by rw [hU, hv, pow_succ, mul_assoc]⟩
      have hc : ¬ f.val ∣ iterPartial i a P := by
        rw [hU]
        exact exact_iter_not_dvd i hf hi a (ha.trans (by decide)) hnd
      let G : N := ⟨iterPartial i a P, Submodule.subset_span ⟨i, a, ha, rfl⟩⟩
      intro he
      have hg : G ∈ forbidden (some f) := he ▸ Submodule.mem_top
      exact hc (Ideal.mem_span_singleton.mp hg)
  obtain ⟨Q, hQ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥factors) (K := GenericX) (M := N) forbidden hproper
  have hgood := hN Q.property
  refine ⟨Q.val, ?_, ?_, ?_, ?_, hgood.2⟩
  · exact fun hz => hQ none ((Submodule.mem_bot GenericX).mpr (Subtype.ext hz))
  · exact Finset.sup_le (fun m hm => (hgood.1 m hm).1)
  · exact Finset.sup_le (fun m hm => (index_weight m) ▸ (hgood.1 m hm).2)
  · apply (isRelPrime_iff_no_prime_factors hP).mpr
    intro d hdP hdQ hd
    obtain ⟨f, hf, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hP hd.irreducible hdP
    exact hQ (some ⟨f, Multiset.mem_toFinset.mpr hf⟩)
      (Ideal.mem_span_singleton.mpr (hassoc.dvd_iff_dvd_left.mp hdQ))

end
end K1_13_7_3_2
end PackSource_K1_13_7_3_2Proof

section PackSource_K1_13_7_3_1Proof
set_option autoImplicit true
namespace K1_13_7_3_1

noncomputable section

open K1_13_4 (Lower lowerIndex)
open MvPolynomial (weightedTotalDegree weightedTotalDegree_mul weightedTotalDegree_le_of_dvd
  weightedTotalDegree_one)
open UniqueFactorizationMonoid

local instance : StrongNormalizationMonoid Lower :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

private theorem lowerIndex_eq_weighted (F : Lower) :
    lowerIndex F = weightedTotalDegree Fin.val F := by
  unfold lowerIndex weightedTotalDegree
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]

private theorem weightedDegree_pow (w : Fin 3 → ℕ) {F : Lower} (hF : F ≠ 0) (n : ℕ) :
    weightedTotalDegree w (F ^ n) = n * weightedTotalDegree w F := by
  induction n with
  | zero => rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C, zero_mul]
  | succ n ih =>
      rw [pow_succ, weightedTotalDegree_mul w _ _ (pow_ne_zero _ hF) hF, ih, Nat.succ_mul]

private theorem degree_pos_of_prime {f : Lower} (hf : Prime f) : 0 < f.totalDegree := by
  by_contra! h
  have he : f = MvPolynomial.C (f.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  have hc : f.coeff 0 ≠ 0 := fun hz => hf.ne_zero (by rw [he, hz, map_zero])
  exact hf.not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)

private theorem factors_of_subproduct {R : Lower} {s : Multiset Lower}
    (hs : s ≤ normalizedFactors R) : normalizedFactors s.prod = s := by
  calc
    normalizedFactors s.prod = s.map normalize :=
      normalizedFactors_prod_eq s fun f hf => irreducible_of_normalized_factor f
        (Multiset.mem_of_le hs hf)
    _ = s.map id := Multiset.map_congr rfl fun f hf =>
      normalize_normalized_factor f (Multiset.mem_of_le hs hf)
    _ = s := Multiset.map_id' s

/-- Purchase a single copy of each factor whose multiplicity reaches the threshold. -/
theorem proof : K1_13_7_3.c1 := by
  classical
  intro R hR b j τ hτ hb hj
  let factors := normalizedFactors R
  let high := factors.filter (fun f => τ ≤ factors.count f)
  let low := factors.filter (fun f => ¬ τ ≤ factors.count f)
  let H := high.dedup.prod
  let A := high.prod
  obtain ⟨u, hu⟩ := prod_normalizedFactors hR
  let P := low.prod * (u : Lower)
  have hpart : high + low = factors := Multiset.filter_add_not _ _
  have hRAP : R = A * P := by
    change R = high.prod * (low.prod * (u : Lower))
    rw [← mul_assoc, ← Multiset.prod_add, hpart]
    exact hu.symm
  have hhigh : high ≤ factors := Multiset.filter_le _ _
  have hlow : low ≤ factors := Multiset.filter_le _ _
  have hdedup : high.dedup ≤ factors := (Multiset.dedup_le _).trans hhigh
  have hH : H ≠ 0 := Multiset.prod_ne_zero fun hz =>
    zero_notMem_normalizedFactors R (Multiset.mem_of_le hdedup hz)
  have hA : A ≠ 0 := left_ne_zero_of_mul (hRAP ▸ hR)
  have hP : P ≠ 0 := right_ne_zero_of_mul (hRAP ▸ hR)
  have hnfH : normalizedFactors H = high.dedup := factors_of_subproduct hdedup
  have hnfA : normalizedFactors A = high := factors_of_subproduct hhigh
  have hnfP : normalizedFactors P = low :=
    (Associated.normalizedFactors_eq (show Associated low.prod P from ⟨u, rfl⟩)).symm.trans
      (factors_of_subproduct hlow)

  -- The purchased product raised to the threshold divides the removed product.
  have hpurchase : H ^ τ ∣ A := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hH) hA,
      normalizedFactors_pow, hnfH, hnfA, Multiset.le_iff_count]
    intro f
    rw [Multiset.count_nsmul, Multiset.count_dedup]
    by_cases hf : f ∈ high
    · have ht : τ ≤ factors.count f := (Multiset.mem_filter.mp hf).2
      have hc : high.count f = factors.count f :=
        Multiset.count_filter_of_pos (p := fun g => τ ≤ factors.count g) ht
      simpa only [hf, if_true, mul_one, hc] using ht
    · simp [hf]

  -- Each normalized prime has positive total degree, so its exponent is at most b.
  have hexponent (f : Lower) (hf : f ∈ factors) : factors.count f ≤ b := by
    have hp := prime_of_normalized_factor f hf
    have hdiv : f ^ factors.count f ∣ R := by
      rw [Multiset.pow_count]
      exact (Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)).trans
        (prod_normalizedFactors hR).dvd
    have hdegree := weightedTotalDegree_le_of_dvd (1 : Fin 3 → ℕ) hdiv hR
    rw [weightedDegree_pow _ hp.ne_zero, weightedTotalDegree_one, weightedTotalDegree_one]
      at hdegree
    exact (Nat.le_mul_of_pos_right _ (degree_pos_of_prime hp)).trans (hdegree.trans hb)
  have hremoved : A ∣ H ^ b := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hA (pow_ne_zero _ hH),
      normalizedFactors_pow, hnfH, hnfA, Multiset.le_iff_count]
    intro f
    rw [Multiset.count_nsmul, Multiset.count_dedup]
    by_cases hf : f ∈ high
    · simp only [hf, if_true, mul_one]
      exact (Multiset.count_le_of_le f hhigh).trans (hexponent f (Multiset.mem_of_le hhigh hf))
    · simp [hf]

  have hAdiv : A ∣ R := ⟨P, hRAP⟩
  have hPdiv : P ∣ R := ⟨A, hRAP.trans (mul_comm A P)⟩
  have hbudget (w : Fin 3 → ℕ) (B : ℕ) (hB : weightedTotalDegree w R ≤ B) :
      weightedTotalDegree w H ≤ B / τ := by
    have hd := weightedTotalDegree_le_of_dvd w (hpurchase.trans hAdiv) hR
    rw [weightedDegree_pow w hH, Nat.mul_comm τ] at hd
    exact (Nat.le_div_iff_mul_le hτ).mpr (hd.trans hB)

  refine ⟨H, A, P, hH, hP, hRAP, hremoved, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [weightedTotalDegree_one] using
      (hbudget 1 b (by simpa only [weightedTotalDegree_one] using hb))
  · simpa only [← lowerIndex_eq_weighted] using
      (hbudget Fin.val j (by simpa only [← lowerIndex_eq_weighted] using hj))
  · exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hPdiv hR).trans hb
  · rw [lowerIndex_eq_weighted] at hj ⊢
    exact (weightedTotalDegree_le_of_dvd Fin.val hPdiv hR).trans hj
  · intro f hf hdiv
    have hle := (dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero _ hf.ne_zero) hP).mp hdiv
    rw [hf.irreducible.normalizedFactors_pow, hnfP, Multiset.le_iff_count] at hle
    have hc := hle (normalize f)
    rw [Multiset.count_replicate_self, Multiset.count_filter] at hc
    split at hc <;> omega

end

end K1_13_7_3_1
end PackSource_K1_13_7_3_1Proof

