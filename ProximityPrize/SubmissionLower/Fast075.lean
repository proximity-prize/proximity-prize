import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast060
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast066
import ProximityPrize.SubmissionLower.Fast071
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast073
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast064
import ProximityPrize.SubmissionLower.Fast070
set_option Elab.async false

section PackSource_K1_13_7_5_3_3_3_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_5_3_3_3_2

noncomputable section

open K1_13_5_4_2_4 K1_13_5_4_2_4_2 K1_13_7_5_3_3_3 MvPolynomial
open scoped Pointwise

variable {A : Fin 4 → Finset Exponent}

private def relIdeal (I : Ideal (Row A)) : Ideal (model A) where
  carrier := {f | ∀ d, (f : Ambient A).coeff d ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg d
    exact I.add_mem (hf d) (hg d)
  smul_mem' := by
    classical
    intro f g hg d
    change ((f : Ambient A) * (g : Ambient A)).coeff d ∈ I
    rw [coeff_mul]
    exact I.sum_mem fun e _ => I.mul_mem_left _ (hg e.2)

private theorem mem_relIdeal_of_val {I : Ideal (Row A)} {f : model A} {d : Exponent}
    {p : Row A} (h : (f : Ambient A) = monomial d p) (hp : p ∈ I) : f ∈ relIdeal I := by
  classical
  intro k
  rw [h, coeff_monomial]
  split_ifs
  · exact hp
  · exact I.zero_mem

private def cut (i : Fin 4) : model A :=
  tag (Finsupp.single i 1) (p := genericEquation A i) (by
    have h : (1 : Row A) ∈ piece A 0 := by
      have h0 : (0 : Exponent) ∈ exponentSet A 0 := by simp [exponentSet]
      exact Submodule.subset_span ⟨⟨0, h0⟩, rfl⟩
    simpa [shift, Finsupp.single_eq_pi_single] using equation_mul_mem_piece i h)

private def target (A : Fin 4 → Finset Exponent) (i : Fin 4) : Ideal (model A) :=
  Ideal.span {cut i} ⊔ relIdeal (prefixIdeal A i.val)

private theorem mem_target {i : Fin 4} {f : model A} :
    f ∈ target A i ↔ ∃ r : model A, f - cut i * r ∈ relIdeal (prefixIdeal A i.val) := by
  rw [target, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨r, b, hb, rfl⟩
    exact ⟨r, by simpa [mul_comm r (cut i)] using hb⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, _, hr, by rw [mul_comm r, add_sub_cancel]⟩

private theorem extract {i : Fin 4} {d : Degree} {p : Row A}
    (hp : p ∈ piece A (shift d i 1))
    (h : tag (stamp (shift d i 1)) hp ∈ target A i) :
    ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val := by
  obtain ⟨r, hr⟩ := mem_target.mp h
  refine ⟨(r : Ambient A).coeff (stamp d), coeff_mem r (stamp d), ?_⟩
  have H := hr (stamp (shift d i 1))
  change (monomial (stamp (shift d i 1)) p -
    monomial (Finsupp.single i 1) (genericEquation A i) * (r : Ambient A)).coeff
      (stamp (shift d i 1)) ∈ prefixIdeal A i.val at H
  rw [MvPolynomial.coeff_sub, coeff_monomial, ite_eq_left rfl, stamp_shift,
    add_comm (stamp d), coeff_monomial_mul] at H
  exact H

private theorem chart_degree (d : Degree) (i : Fin 4) (m : ℕ) :
    stamp (fun _ => m) + stamp (shift d i 1) =
      Finsupp.single i 1 + stamp (d + fun _ => m) := by
  rw [stamp_shift]
  ext j
  change m + (d j + (Finsupp.single i 1 : Exponent) j) = (Finsupp.single i 1 : Exponent) j + (d j + m)
  omega

private theorem monomial_mul_sub {R : Type*} [CommRing R] (a b c d : Exponent)
    (h : a + b = c + d) (p q r s : R) :
    (monomial a p : MvPolynomial (Fin 4) R) * monomial b q - monomial c r * monomial d s =
      monomial (c + d) (p * q - r * s) := by
  simp only [monomial_mul_monomial, h, map_sub]

private theorem chart_lift (h : ChartLifting A) (i : Fin 4) (d : Degree) {p : Row A}
    (hp : p ∈ piece A (shift d i 1)) (hrel : p ∈ prefixIdeal A (i.val + 1)) (a : Chart A) :
    ∃ m : ℕ, chart a ^ m * tag (stamp (shift d i 1)) hp ∈ target A i := by
  obtain ⟨m, r, hr, hrel'⟩ := h i d p hp hrel a
  let dm : Degree := d + (fun _ : Fin 4 => m)
  have hr' : r ∈ piece A (stamp dm) := by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact hr
  let t : model A := tag (A := A) (p := r) (stamp dm) hr'
  let g : model A := tag (A := A) (p := p) (stamp (shift d i 1)) hp
  let f : model A := chart a ^ m * g - cut i * t
  refine ⟨m, (mem_target (A := A) (i := i) (f := chart a ^ m * g)).mpr ⟨t, ?_⟩⟩
  change f ∈ relIdeal (prefixIdeal A i.val)
  refine mem_relIdeal_of_val (A := A) (I := prefixIdeal A i.val) (f := f)
    (d := Finsupp.single i 1 + stamp dm)
    (p := chartPower a m * p - genericEquation A i * r) ?_ hrel'
  calc
    (f : Ambient A) =
        ((chart a ^ m : model A) : Ambient A) * monomial (stamp (shift d i 1)) p -
          monomial (Finsupp.single i 1) (genericEquation A i) * monomial (stamp dm) r := rfl
    _ = _ := by
      rw [chart_pow_val]
      exact monomial_mul_sub _ _ _ _ (chart_degree d i m) (chartPower a m) p (genericEquation A i) r

private theorem pow_mul_mem_of_le {R : Type*} [CommRing R] (J : Ideal R) (x f : R)
    {l m : ℕ} (h : l ≤ m) (hl : x ^ l * f ∈ J) : x ^ m * f ∈ J := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm l k, pow_add, mul_assoc]
  exact J.mul_mem_left _ hl

private theorem uniform_power {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) (x : R) : ∃ M : ℕ, ∀ f : R,
      (∃ m : ℕ, x ^ m * f ∈ J) → x ^ M * f ∈ J := by
  let C : ℕ →o Submodule R R :=
    ⟨fun m => J.colon {x ^ m}, fun l m hlm f hf => by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] at hf ⊢
      exact pow_mul_mem_of_le J x f hlm hf⟩
  obtain ⟨M, hM⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) C
  refine ⟨M, fun f ⟨m, hm⟩ => ?_⟩
  have hle : C m ≤ C M := by
    rcases le_total m M with hl | hl
    · exact C.monotone hl
    · exact (hM m hl).ge
  have hmem : f ∈ C m := by
    change f ∈ J.colon {x ^ m}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] using hm
  have hmem' : f ∈ J.colon {x ^ M} := hle hmem
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] using hmem'

private def gens (A : Fin 4 → Finset Exponent) (i : Fin 4) (b : ℕ) : Set (model A) :=
  {f | ∃ (d : Degree) (p : Row A) (hp : p ∈ piece A (shift d i 1)),
    (∀ j, d j ≤ b) ∧ p ∈ prefixIdeal A (i.val + 1) ∧ f = tag (stamp (shift d i 1)) hp}

private theorem bounded_gens (i : Fin 4) : ∃ B : ℕ, ∀ (d : Degree) {p : Row A}
    (hp : p ∈ piece A (shift d i 1)), p ∈ prefixIdeal A (i.val + 1) →
      tag (stamp (shift d i 1)) hp ∈ Ideal.span (gens A i B) := by
  classical
  let C : ℕ →o Submodule (model A) (model A) :=
    ⟨fun b => Ideal.span (gens A i b), fun _ _ hn => Ideal.span_mono (by
      rintro _ ⟨d, p, hp, hd, hrel, rfl⟩
      exact ⟨d, p, hp, fun j => (hd j).trans hn, hrel, rfl⟩)⟩
  obtain ⟨B, hB⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance C
  refine ⟨B, fun d p hp hrel => ?_⟩
  have h : tag (stamp (shift d i 1)) hp ∈ C (max B (Finset.univ.sup d)) :=
    Ideal.subset_span ⟨d, p, hp, fun j => (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _),
      hrel, rfl⟩
  rwa [← hB _ (le_max_left _ _)] at h

private theorem proj_mul_tag {f : model A} {d e : Exponent} {p : Row A}
    (hp : p ∈ piece A e) : proj (d + e) (f * tag e hp) = proj d f * tag e hp := by
  apply Subtype.ext
  change monomial (d + e) (((f : Ambient A) * monomial e p).coeff (d + e)) =
    monomial d ((f : Ambient A).coeff d) * monomial e p
  rw [monomial_mul_monomial, coeff_mul_monomial]

private theorem proj_add (d : Exponent) (f g : model A) :
    proj d (f + g) = proj d f + proj d g := by
  apply Subtype.ext
  change monomial d (((f : Ambient A) + (g : Ambient A)).coeff d) =
    monomial d ((f : Ambient A).coeff d) + monomial d ((g : Ambient A).coeff d)
  change monomial d ((f : Ambient A).coeff d + (g : Ambient A).coeff d) = _
  exact map_add (monomial d) _ _

private theorem stable_cut (hz : ∀ i, 0 ∈ A i) (h : ChartLifting A) (i : Fin 4) :
    ∃ b : ℕ, ∀ (d : Degree), (∀ j, b ≤ d j) →
      ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
        ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val := by
  classical
  obtain ⟨B, hB⟩ := bounded_gens (A := A) i
  choose M hM using fun a : Chart A => uniform_power (target A i) (chart a)
  let m := Finset.univ.sup M
  let N := Finset.univ.sup fun j => (A j).card * m
  have hkill (g : model A) (hg : g ∈ gens A i B) :
      chartIdeal A m ≤ (target A i).colon {g} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change chart a ^ m ∈ (target A i).colon {g}
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    obtain ⟨d, p, hp, _, hrel, rfl⟩ := hg
    apply pow_mul_mem_of_le _ _ _ (show M a ≤ m from Finset.le_sup (Finset.mem_univ a))
    exact hM a _ (chart_lift h i d hp hrel a)
  have hhigh (f : model A) (hf : f ∈ Ideal.span (gens A i B)) :
      ∀ (q : model A) (e : Exponent), (∀ j, B + 1 + N ≤ e j) → proj e (q * f) ∈ target A i := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      intro q e he
      obtain ⟨d, p, hp, hd, hrel, rfl⟩ := hg
      let k := stamp (shift d i 1)
      have hk (j : Fin 4) : k j ≤ B + 1 := by
        change d j + (Pi.single i 1 : Degree) j ≤ B + 1
        by_cases hij : j = i
        · subst j
          simpa only [Pi.single_eq_same] using Nat.succ_le_succ (hd i)
        · rw [Pi.single_eq_of_ne hij, add_zero]
          exact (hd j).trans (Nat.le_succ B)
      have hle : k ≤ e := fun j => (hk j).trans ((Nat.le_add_right _ _).trans (he j))
      have hsub : e - k + k = e := tsub_add_cancel_of_le hle
      have hs (j : Fin 4) : (A j).card * m ≤ (e - k) j := by
        have hN : (A j).card * m ≤ N :=
          Finset.le_sup (f := fun j => (A j).card * m) (Finset.mem_univ j)
        change (A j).card * m ≤ e j - k j
        have := hk j
        have := he j
        omega
      have hm := Submodule.mem_colon_singleton.mp (hkill _ ⟨d, p, hp, hd, hrel, rfl⟩
        (tag_mem_chartIdeal hz hs (coeff_mem q (e - k))))
      rw [← hsub]
      exact (proj_mul_tag (f := q) (d := e - k) (e := k) (show p ∈ piece A k from hp)).symm ▸ hm
    | zero =>
      intro q e he
      rw [mul_zero]
      have hz' : proj e (0 : model A) = 0 := by
        apply Subtype.ext
        change monomial e ((0 : Ambient A).coeff e) = 0
        simp
      rw [hz']
      exact (target A i).zero_mem
    | add f g _ _ hf hg =>
      intro q e he
      rw [mul_add, proj_add]
      exact (target A i).add_mem (hf q e he) (hg q e he)
    | smul r f _ hf =>
      intro q e he
      simpa only [smul_eq_mul, mul_assoc] using hf (q * r) e he
  refine ⟨B + 1 + N, fun d hd p hp hrel => extract hp ?_⟩
  have H := hhigh _ (hB d hp hrel) 1 (stamp (shift d i 1)) (fun j =>
    (hd j).trans (Nat.le_add_right _ _))
  rw [one_mul] at H
  convert H using 1
  apply Subtype.ext
  change monomial (stamp (shift d i 1)) p =
    monomial (stamp (shift d i 1)) ((monomial (stamp (shift d i 1)) p).coeff (stamp (shift d i 1)))
  rw [coeff_monomial, ite_eq_left rfl]

theorem proof : K1_13_7_5_3_3_3.c2 := by
  classical
  intro A hz h
  choose b hb using stable_cut hz h
  exact ⟨Finset.univ.sup b, fun i d hd => hb i d (fun j =>
    (Finset.le_sup (Finset.mem_univ i)).trans (hd j))⟩

end
end K1_13_7_5_3_3_3_2
end PackSource_K1_13_7_5_3_3_3_2Proof

section PackSource_K1_13_7_1_2_2_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 2000

namespace K1_13_7_1_2_2_1_1

noncomputable section

open K1_13_6_3_4 K1_13_7_1 K1_13_7_1_2_2_1 K1_13_7_2_5_4_1 MvPolynomial

variable {k E σ : Type} [Field k] [Field E] [Algebra k E]

private theorem map_component (p : MvPolynomial σ k) (n : ℕ) :
    MvPolynomial.map (algebraMap k E) (homogeneousComponent n p) =
      homogeneousComponent n (MvPolynomial.map (algebraMap k E) p) := by
  ext d
  by_cases hd : d.degree = n <;>
    simp only [MvPolynomial.coeff_map, coeff_homogeneousComponent, hd, ite_true, ite_false, map_zero]

/-- An inclusion of ideals with equal affine Hilbert polynomials is an equality. -/
private theorem ideal_eq_of_le_of_hilbert_eq [Finite σ]
    {A B : Ideal (MvPolynomial σ E)} (hAB : A ≤ B)
    (h : affineHilbertPolynomial A = affineHilbertPolynomial B) : A = B := by
  obtain ⟨a, ha⟩ := exists_eval_affineHilbertPolynomial A
  obtain ⟨b, hb⟩ := exists_eval_affineHilbertPolynomial B
  refine le_antisymm hAB ?_
  intro p hp
  let n := max p.totalDegree (max a b)
  let V := quotientDegreeLE A n
  let W := quotientDegreeLE B n
  let q := (Ideal.Quotient.factorₐ E hAB).toLinearMap
  have hq (x : V) : q x ∈ W := by
    obtain ⟨r, hr, he⟩ := mem_quotientDegreeLE.mp x.property
    rw [← he]
    exact mk_mem_quotientDegreeLE hr
  let f : V →ₗ[E] W := (q.domRestrict V).codRestrict W hq
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, he⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk A r, mk_mem_quotientDegreeLE hr⟩, Subtype.ext he⟩
  have he : Module.finrank E V = Module.finrank E W := by
    have hna : a ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have hnb : b ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    have he := (ha n hna).symm.trans ((congrArg (Polynomial.eval (n : ℚ)) h).trans (hb n hnb))
    change ((Module.finrank E V : ℕ) : ℚ) = (Module.finrank E W : ℚ) at he
    exact_mod_cast he
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he (f := f)).mpr hsurj
  let x : V := ⟨Ideal.Quotient.mk A p, mk_mem_quotientDegreeLE (le_max_left _ _)⟩
  have hx : f x = f 0 := by
    rw [map_zero]
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val (hinj hx))

private theorem boundary_map (I : Ideal (MvPolynomial TaylorIndex k)) :
    boundaryIdeal (I.map (MvPolynomial.map (algebraMap k E))) =
      (boundaryIdeal I).map (MvPolynomial.map (algebraMap k E)) := by
  let f : MvPolynomial TaylorIndex k →+* MvPolynomial TaylorIndex E :=
    MvPolynomial.map (algebraMap k E)
  symm
  apply ideal_eq_of_le_of_hilbert_eq
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    change f (homogeneousComponent n p) ∈ boundaryIdeal (I.map f)
    rw [map_component]
    apply Ideal.subset_span
    exact ⟨f p, n, Ideal.mem_map_of_mem _ hp,
      (Finset.sup_mono (support_map_subset (algebraMap k E) p)).trans hn, rfl⟩
  · rw [K1_13_5_5_2.hilbertPolynomial_map, K1_13_5_4_4_2.hilbertPolynomial_boundary,
      K1_13_5_4_4_2.hilbertPolynomial_boundary, K1_13_5_5_2.hilbertPolynomial_map]

private theorem affine_regular {t : Option TaylorIndex → E} (ht : AlgebraicIndependent k t)
    (I : Ideal (MvPolynomial TaylorIndex k)) :
    IsLeftRegular (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k E)))
      (affinePolynomial t)) := by
  classical
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  let a : Option TaylorIndex → MvPolynomial TaylorIndex k :=
    fun i => i.elim 1 MvPolynomial.X
  have he : (∑ i, C (t i) * MvPolynomial.map (algebraMap k E) (a i)) = affinePolynomial t := by
    simp [Fintype.sum_option, a, affinePolynomial]
  obtain ⟨m, hm⟩ := generic_torsion ht I a none p (he.symm ▸ hx)
  simpa [a] using hm

private def slope (t : Option TaylorIndex → E) : MvPolynomial TaylorIndex E :=
  ∑ i, C (t (some i)) * MvPolynomial.X i

private theorem linear_sum_homogeneous {σ F : Type} [Fintype σ] [Field F] (a : σ → F) :
    (∑ i, C (a i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ F 1).sum_mem fun i _ => isHomogeneous_C_mul_X _ i

private theorem slope_homogeneous (t : Option TaylorIndex → E) : (slope t).IsHomogeneous 1 :=
  linear_sum_homogeneous (fun i : TaylorIndex => t (some i))

private theorem generic_slope_eventually_regular {t : Option TaylorIndex → E}
    (ht : AlgebraicIndependent k t) (I : Ideal (MvPolynomial TaylorIndex k)) :
    EventuallyRegularHomogeneous
      (boundaryIdeal (I.map (MvPolynomial.map (algebraMap k E)))) (slope t) := by
  let J := I.map (MvPolynomial.map (algebraMap k E))
  let B := boundaryIdeal J
  apply K1_13_7_2_5_4_1_1.proof B (slope t) (boundary_homogeneous J) (slope_homogeneous t)
  intro P hP hi hℓ
  obtain ⟨i, hi⟩ := hi
  obtain ⟨x, he⟩ := (isAssociatedPrime_iff.mp hP).2
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmul : slope t * p ∈ B := by
    rw [he, Submodule.mem_colon_singleton, Submodule.mem_bot] at hℓ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hℓ
  have hgen := generic_torsion (ht.comp some (Option.some_injective TaylorIndex))
    (boundaryIdeal I) MvPolynomial.X i p
  simp only [MvPolynomial.map_X, Function.comp_apply, ← boundary_map] at hgen
  obtain ⟨m, hm⟩ := hgen hmul
  have hpow : MvPolynomial.X i ^ m ∈ P := by
    rw [he, Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk B (MvPolynomial.X i ^ m) * Ideal.Quotient.mk B p = 0
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  exact hi (hP.isPrime.mem_of_pow_mem _ hpow)

private theorem degree_drop {p : MvPolynomial σ E} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) (h : homogeneousComponent (n + 1) p = 0) :
    p.totalDegree ≤ n := by
  apply Finset.sup_le
  intro d hd
  have hle := (le_totalDegree hd).trans hp
  have hne : d.degree ≠ n + 1 := by
    intro he
    apply mem_support_iff.mp hd
    simpa [coeff_homogeneousComponent, he] using congrArg (fun q : MvPolynomial σ E => q.coeff d) h
  exact Nat.le_of_lt_succ (lt_of_le_of_ne (show d.degree ≤ n + 1 from hle) hne)

private theorem strict_filtered {t : Option TaylorIndex → E}
    {J : Ideal (MvPolynomial TaylorIndex E)}
    (h : EventuallyRegularHomogeneous (boundaryIdeal J) (slope t)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ quotientDegreeLE J (n + 1),
      Ideal.Quotient.mk J (affinePolynomial t) * x ∈ quotientDegreeLE J (n + 1) →
      x ∈ quotientDegreeLE J n := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn x hx hfx => ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hx
  obtain ⟨q, hq, hqeq⟩ := mem_quotientDegreeLE.mp hfx
  have hrel : affinePolynomial t * p - q ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqeq, sub_self]
  have hform : affinePolynomial t = C (t none) + slope t := rfl
  have hlin := (slope_homogeneous t).totalDegree_le
  have hdeg : (affinePolynomial t * p - q).totalDegree ≤ n + 2 := by
    have hfd : (affinePolynomial t).totalDegree ≤ 1 := by
      rw [hform]
      exact (totalDegree_add _ _).trans (max_le (by simp) hlin)
    exact (totalDegree_sub _ _).trans (max_le
      ((totalDegree_mul _ _).trans (by omega)) (by omega))
  have hcomp : homogeneousComponent (n + 2) (affinePolynomial t * p - q) =
      slope t * homogeneousComponent (n + 1) p := by
    rw [hform, add_mul, map_sub, map_add,
      homogeneousComponent_eq_zero _ q (by omega), sub_zero,
      homogeneousComponent_eq_zero _ (C (t none) * p) (by
        apply (totalDegree_mul _ _).trans_lt
        simp only [totalDegree_C, zero_add]
        omega), zero_add, component_mul_linear (slope_homogeneous t)]
  have hlead : slope t * homogeneousComponent (n + 1) p ∈ boundaryIdeal J := by
    rw [← hcomp]
    exact Ideal.subset_span ⟨_, n + 2, hrel, hdeg, rfl⟩
  have hmem := hN (n + 1) (by omega) _ (homogeneousComponent_isHomogeneous _ _) hlead
  obtain ⟨r, hr, hrd, htop⟩ := K1_13_5_4_4_2.lift_boundary_component J hmem (n + 1)
  have hd : (p - r).totalDegree ≤ n :=
    degree_drop ((totalDegree_sub _ _).trans (max_le hp hrd)) (by
      rw [map_sub, htop, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
        sub_self])
  have hq' : Ideal.Quotient.mk J (p - r) = Ideal.Quotient.mk J p := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hr, sub_zero]
  rw [← hq']
  exact mk_mem_quotientDegreeLE hd

/-- A tuple of independent coefficients gives an affine non-zero-divisor
whose slope acts injectively on all sufficiently high degree quotients. -/
theorem proof : K1_13_7_1_2_2_1.c1 := by
  intro k E _ _ _ t ht I
  exact ⟨affine_regular ht I, strict_filtered (generic_slope_eventually_regular ht I)⟩

end

end K1_13_7_1_2_2_1_1
end PackSource_K1_13_7_1_2_2_1_1Proof
