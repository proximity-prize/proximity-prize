import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast010
set_option Elab.async false

section PackSource_ReciprocalCore
set_option autoImplicit true
/-! Generic polynomial core of the reciprocal/base-list family reduction.
No universal list bound or protocol claim is asserted here. -/
namespace Sol1.Reciprocal
open Polynomial

variable {F K : Type*} [Field F] [Field K]

/-- More than the polynomial degree many base-valued evaluations force
descent along a field embedding. No Frobenius-specific fact is needed. -/
theorem descends_of_many_values (phi : F →+* K) (S : Finset F)
    (f : Polynomial K) (w : F → F) (k : ℕ)
    (hf : f.natDegree ≤ k) (hcard : k < S.card)
    (heval : ∀ x ∈ S, f.eval (phi x) = phi (w x)) :
    ∃ P : Polynomial F, P.map phi = f ∧ P.natDegree ≤ k ∧
      ∀ x ∈ S, P.eval x = w x := by
  classical
  let P : Polynomial F := Lagrange.interpolate S id w
  have hnodes : Set.InjOn (id : F → F) S := fun _ _ _ _ h => h
  have hP : P.degree < (S.card : WithBot ℕ) :=
    Lagrange.degree_interpolate_lt w hnodes
  have hmap : (P.map phi).degree < (S.card : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le hP
  have hdeg : f.degree < (S.card : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast lt_of_le_of_lt hf hcard
  have hphi : Set.InjOn (fun x : F => phi x) S :=
    fun _ _ _ _ h => phi.injective h
  have heq : P.map phi = f := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hphi hmap hdeg
    intro x hx
    rw [Polynomial.eval_map_apply, heval x hx]
    congr 1
    exact Lagrange.eval_interpolate_at_node w hnodes hx
  refine ⟨P, heq, ?_, ?_⟩
  · have hnat := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_map_eq_of_injective phi.injective] at hnat
    omega
  · intro x hx
    exact Lagrange.eval_interpolate_at_node w hnodes hx

theorem coefficient_fixed_of_many_fixed_values (sigma : K →+* K)
    (S : Finset K) (f : Polynomial K)
    (hcard : f.natDegree < S.card)
    (hnodes : ∀ x ∈ S, sigma x = x)
    (hvalues : ∀ x ∈ S, sigma (f.eval x) = f.eval x) :
    ∀ i, sigma (f.coeff i) = f.coeff i := by
  have heq : f.map sigma = f := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ S
    · intro x hx
      calc
        (f.map sigma).eval x = (f.map sigma).eval (sigma x) := by rw [hnodes x hx]
        _ = sigma (f.eval x) := Polynomial.eval_map_apply _ _
        _ = f.eval x := hvalues x hx
    · exact lt_of_le_of_lt (max_le Polynomial.natDegree_map_le le_rfl) hcard
  intro i
  simpa only [Polynomial.coeff_map] using congrArg (fun q : Polynomial K => q.coeff i) heq

theorem eq_of_eval_on_base (phi : F →+* K) (S : Finset F)
    (f g : Polynomial K)
    (heval : ∀ x ∈ S, f.eval (phi x) = g.eval (phi x))
    (hcard : max f.natDegree g.natDegree < S.card) : f = g := by
  classical
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (S.image phi)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact heval x hx
  · simpa only [Finset.card_image_of_injective S phi.injective] using hcard

theorem linear_mul_add_const_degree (h : Polynomial K) (alpha gamma : K)
    (k : ℕ) (hh : h.natDegree < k) :
    ((X-C alpha)*h+C gamma).natDegree ≤ k := by
  have hm := Polynomial.natDegree_mul_le (p := X-C alpha) (q := h)
  have ha := Polynomial.natDegree_add_le ((X-C alpha)*h) (C gamma)
  simp only [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_C] at hm ha
  omega

/-- The pole direction cannot extend on the same large support. -/
theorem pole_direction_never_extends (phi : F →+* K) (S : Finset F)
    (alpha : K) (k : ℕ) (hcard : k < S.card)
    (halpha : ∀ x ∈ S, phi x ≠ alpha) :
    ¬ ∃ g : Polynomial K, g.natDegree < k ∧
      ∀ x ∈ S, g.eval (phi x) = -1/(phi x-alpha) := by
  rintro ⟨g, hg, heval⟩
  let f : Polynomial K := (X-C alpha)*g+C 1
  have hdegree : f.natDegree ≤ k := linear_mul_add_const_degree g alpha 1 k hg
  have hzero : f = 0 := by
    apply eq_of_eval_on_base phi S f 0
    · intro x hx
      have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero, heval x hx]
      field_simp
      ring
    · simpa only [Polynomial.natDegree_zero, max_eq_left (Nat.zero_le _)] using
        lt_of_le_of_lt hdegree hcard
  have hbad := congrArg (fun q : Polynomial K => q.eval alpha) hzero
  have : (1 : K) = 0 := by simpa [f] using hbad
  exact one_ne_zero this

/-- Exact supportwise reciprocal decoder / ordinary base-list equivalence. -/
theorem pole_decoder_iff_base_polynomial (phi : F →+* K) (S : Finset F)
    (w : F → F) (alpha gamma : K) (k : ℕ) (hk : 0 < k)
    (hcard : k < S.card) (halpha : ∀ x ∈ S, phi x ≠ alpha) :
    (∃ h : Polynomial K, h.natDegree < k ∧
      ∀ x ∈ S, h.eval (phi x) = (phi (w x)-gamma)/(phi x-alpha)) ↔
    ∃ P : Polynomial F, P.natDegree ≤ k ∧
      (∀ x ∈ S, P.eval x = w x) ∧ (P.map phi).eval alpha = gamma := by
  constructor
  · rintro ⟨h, hh, heval⟩
    let f : Polynomial K := (X-C alpha)*h+C gamma
    have hf : f.natDegree ≤ k := linear_mul_add_const_degree h alpha gamma k hh
    have he : ∀ x ∈ S, f.eval (phi x) = phi (w x) := by
      intro x hx
      have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, heval x hx]
      field_simp
      ring
    obtain ⟨P, hmap, hP, hvalues⟩ := descends_of_many_values phi S f w k hf hcard he
    refine ⟨P, hP, hvalues, ?_⟩
    rw [hmap]
    simp [f]
  · rintro ⟨P, hP, hvalues, hgamma⟩
    have hroot : Polynomial.IsRoot (P.map phi-C gamma) alpha := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
        hgamma, sub_self]
    obtain ⟨h, hfactor⟩ := (Polynomial.dvd_iff_isRoot.mpr hroot)
    have hdegree : (P.map phi-C gamma).natDegree ≤ k := by
      apply le_trans (Polynomial.natDegree_sub_le _ _)
      apply max_le
      · exact le_trans Polynomial.natDegree_map_le hP
      · simp
    have hh : h.natDegree < k := by
      by_cases hz : h = 0
      · simpa [hz] using hk
      · rw [hfactor, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero alpha) hz,
          Polynomial.natDegree_X_sub_C] at hdegree
        omega
    refine ⟨h, hh, ?_⟩
    intro x hx
    have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
    have he := congrArg (fun q : Polynomial K => q.eval (phi x)) hfactor
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_map_apply, hvalues x hx] at he
    apply (eq_div_iff hden).mpr
    simpa only [mul_comm] using he.symm

open Classical in
/-- The ordinary base list has degree at most k, hence dimension k+1. -/
def baseCloseSet (D : Finset F) (w : F → F) (k A : ℕ) : Set (Polynomial F) :=
  {P | P.natDegree ≤ k ∧ A ≤ (D.filter fun x => P.eval x = w x).card}

/-- Explicit common-support MCA predicate for the scalar reciprocal pair.
The nonalignment clause excludes simultaneous extension of both inputs
on exactly the support used for decoding. -/
def poleMCASet (phi : F →+* K) (D : Finset F) (w : F → F)
    (alpha : K) (k A : ℕ) : Set K :=
  {gamma | ∃ S : Finset F, S ⊆ D ∧ A ≤ S.card ∧
    (∃ h : Polynomial K, h.natDegree < k ∧
      ∀ x ∈ S, h.eval (phi x) = (phi (w x)-gamma)/(phi x-alpha)) ∧
    ¬ ∃ u v : Polynomial K, u.natDegree < k ∧ v.natDegree < k ∧
      ∀ x ∈ S, u.eval (phi x) = phi (w x)/(phi x-alpha) ∧
        v.eval (phi x) = -1/(phi x-alpha)}

/-- Exact evaluation-IMAGE identity, including the SAME-support
nonalignment predicate. Evaluation need not be injective. -/
theorem pole_MCA_set_eq_evaluation_image (phi : F →+* K) (D : Finset F)
    (w : F → F) (alpha : K) (k A : ℕ) (hk : 0 < k) (hkA : k < A)
    (halpha : ∀ x ∈ D, phi x ≠ alpha) :
    poleMCASet phi D w alpha k A =
      (fun P : Polynomial F => (P.map phi).eval alpha) '' baseCloseSet D w k A := by
  classical
  ext gamma
  constructor
  · rintro ⟨S, hSD, hAS, hdecode, _hnonaligned⟩
    obtain ⟨P, hP, hvalues, hgamma⟩ :=
      (pole_decoder_iff_base_polynomial phi S w alpha gamma k hk
        (lt_of_lt_of_le hkA hAS) (fun x hx => halpha x (hSD hx))).mp hdecode
    refine ⟨P, ⟨hP, ?_⟩, hgamma⟩
    apply le_trans hAS
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSD hx, hvalues x hx⟩
  · rintro ⟨P, ⟨hP, hcount⟩, hgamma⟩
    let S : Finset F := D.filter fun x => P.eval x = w x
    have hSD : S ⊆ D := Finset.filter_subset _ _
    have hAS : A ≤ S.card := hcount
    have hcard : k < S.card := lt_of_lt_of_le hkA hAS
    have halphaS : ∀ x ∈ S, phi x ≠ alpha := fun x hx => halpha x (hSD hx)
    have hvalues : ∀ x ∈ S, P.eval x = w x :=
      fun x hx => (Finset.mem_filter.mp hx).2
    have hdecode := (pole_decoder_iff_base_polynomial phi S w alpha gamma k hk
      hcard halphaS).mpr ⟨P, hP, hvalues, hgamma⟩
    refine ⟨S, hSD, hAS, hdecode, ?_⟩
    rintro ⟨u, v, _hu, hv, hboth⟩
    apply pole_direction_never_extends phi S alpha k hcard halphaS
    exact ⟨v, hv, fun x hx => (hboth x hx).2⟩

theorem native_support_gap : (131072 : ℕ) < 177505 := by norm_num

/-- A finite family of bounded-degree polynomials has an injective
evaluation on any candidate set larger than its pairwise collision budget.
Ordered pairs give a deliberately coarse square-size bound. -/
theorem exists_injective_evaluation (S : Finset (Polynomial K))
    (T : Finset K) (k : ℕ) (hdegree : ∀ f ∈ S, f.natDegree ≤ k)
    (hsize : k*S.card^2 < T.card) :
    ∃ alpha ∈ T, Set.InjOn (fun f : Polynomial K => f.eval alpha) S := by
  classical
  let J : Finset (Polynomial K × Polynomial K) :=
    (S.product S).filter fun fg => fg.1 ≠ fg.2
  let Q : Polynomial K := ∏ fg ∈ J, (fg.1-fg.2)
  have hfactor : ∀ fg ∈ J, fg.1-fg.2 ≠ 0 := by
    intro fg hfg
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hfg).2
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hJ : J.card ≤ S.card*S.card := by
    exact le_trans (Finset.card_filter_le _ _)
      (by rw [Finset.product_eq_sprod, Finset.card_product])
  have hQdegree : Q.natDegree ≤ k*S.card^2 := by
    apply le_trans (Polynomial.natDegree_prod_le J (fun fg => fg.1-fg.2))
    calc
      (∑ fg ∈ J, (fg.1-fg.2).natDegree) ≤ ∑ _fg ∈ J, k := by
        apply Finset.sum_le_sum
        intro fg hfg
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp hfg).1
        exact le_trans (Polynomial.natDegree_sub_le _ _)
          (max_le (hdegree _ hm.1) (hdegree _ hm.2))
      _ = J.card*k := by simp
      _ ≤ (S.card*S.card)*k := Nat.mul_le_mul_right k hJ
      _ = k*S.card^2 := by ring
  obtain ⟨alpha, hT, hnonzero⟩ : ∃ alpha ∈ T, Q.eval alpha ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hQ (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q T
      hnone (lt_of_le_of_lt hQdegree hsize))
  refine ⟨alpha, hT, ?_⟩
  intro f hf g hg heval
  by_contra hne
  have hfg : (f,g) ∈ J := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hf,hg⟩, hne⟩
  have hprod : (∏ fg ∈ J, (fg.1-fg.2).eval alpha) ≠ 0 := by
    simpa only [Q, Polynomial.eval_prod] using hnonzero
  have hdiff := Finset.prod_ne_zero_iff.mp hprod (f,g) hfg
  exact hdiff (by simp only [Polynomial.eval_sub, heval, sub_self])

/-- There is ample native room to separate C0+1 base-list polynomials
while excluding all n domain nodes. No degree-six alpha assertion is
needed for this necessary-subproblem argument. -/
theorem native_evaluation_separation_budget :
    262144 + 131072*(7*262144^3+1)^2 < (2130706433 : ℕ)^6 := by norm_num

end Sol1.Reciprocal
end PackSource_ReciprocalCore

section PackSource_ReciprocalCardinality
set_option autoImplicit true
/-! Typed finite-field count consequences of the frozen reciprocal core.
The pole-cap premise is explicit; no universal MCA bound is proved here. -/

namespace Sol1.Reciprocal

open Polynomial

variable {F K : Type*} [Field F] [Field K] [Fintype K]

open Classical in
/-- A finite base-list family separates at a pole outside all domain nodes.
A uniform cap on the actual scalar pole-MCA sets then bounds its cardinality. -/
theorem finset_card_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (P : Finset (Polynomial F)) (hP : (P : Set (Polynomial F)) ⊆ baseCloseSet D w k A)
    (hroom : D.card + k * P.card ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B) :
    P.card ≤ B := by
  classical
  let mapped : Finset (Polynomial K) := P.image (Polynomial.map phi)
  let candidates : Finset K := Finset.univ \ D.image phi
  have hmapinj : Function.Injective (Polynomial.map phi) :=
    Polynomial.map_injective phi phi.injective
  have hmapped : mapped.card = P.card := Finset.card_image_of_injective P hmapinj
  have hcandidates : candidates.card = Fintype.card K - D.card := by
    dsimp [candidates]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_image_of_injective D phi.injective]
  have hdegree : ∀ f ∈ mapped, f.natDegree ≤ k := by
    intro f hf
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    exact Polynomial.natDegree_map_le.trans (hP hq).1
  have hsize : k * mapped.card ^ 2 < candidates.card := by
    rw [hmapped, hcandidates]
    omega
  obtain ⟨alpha, halpha, hinj⟩ :=
    exists_injective_evaluation mapped candidates k hdegree hsize
  have houtside : ∀ x ∈ D, phi x ≠ alpha := by
    intro x hx heq
    have hnot : alpha ∉ D.image phi := (Finset.mem_sdiff.mp halpha).2
    exact hnot (Finset.mem_image.mpr ⟨x, hx, heq⟩)
  have hinjP : Set.InjOn (fun q : Polynomial F ↦ (q.map phi).eval alpha) P := by
    intro q hq r hr heq
    apply hmapinj
    exact hinj (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩) heq
  have hmaps : ∀ q ∈ (P : Set (Polynomial F)),
      (q.map phi).eval alpha ∈ poleMCASet phi D w alpha k A := by
    intro q hq
    rw [pole_MCA_set_eq_evaluation_image phi D w alpha k A hk hkA houtside]
    exact ⟨q, hP hq, rfl⟩
  have hcount := Set.ncard_le_ncard_of_injOn
    (fun q : Polynomial F ↦ (q.map phi).eval alpha) hmaps hinjP
  have hcount' : P.card ≤ (poleMCASet phi D w alpha k A).ncard := by
    simpa only [Set.ncard_coe_finset] using hcount
  exact hcount'.trans (hcap alpha houtside)

open Classical in
/-- Room for a B+1 counterexample family bounds every finite subfamily. -/
theorem every_finset_card_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (hroom : D.card + k * (B + 1) ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B)
    (P : Finset (Polynomial F)) (hP : (P : Set (Polynomial F)) ⊆ baseCloseSet D w k A) :
    P.card ≤ B := by
  by_contra hlarge
  have hsize : B + 1 ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hsize
  have hQ := finset_card_le_of_pole_cap phi D w k A B hk hkA Q
    (fun q hq ↦ hP (hQP hq)) (by simpa only [hQcard] using hroom) hcap
  omega

open Classical in
/-- The complete ordinary base list is finite and bounded, conditionally on
the uniform scalar pole-MCA cap and the finite extension-field room. -/
theorem base_list_finite_ncard_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (hroom : D.card + k * (B + 1) ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B) :
    (baseCloseSet D w k A).Finite ∧ (baseCloseSet D w k A).ncard ≤ B := by
  have hfinsets := every_finset_card_le_of_pole_cap phi D w k A B hk hkA hroom hcap
  have hfinite : (baseCloseSet D w k A).Finite := by
    by_contra hinfinite
    obtain ⟨P, hP, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (B + 1)
    have h := hfinsets P hP
    omega
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply hfinsets hfinite.toFinset
  intro q hq
  exact hfinite.mem_toFinset.mp hq


end Sol1.Reciprocal
end PackSource_ReciprocalCardinality

section PackSource_HyperplaneAvoidance
set_option autoImplicit true
namespace Sol1
open Finset Module

/-- At most `|K|` proper central subspaces cannot cover a finite vector space.
The non-strict cardinality hypothesis is needed for affine-line MCA scalarization. -/
theorem exists_avoiding_subspaces_card_le
    {K V I : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] [FiniteDimensional K V]
    (s : Finset I) (p : I → Submodule K V)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ v : V, ∀ i ∈ s, v ∉ p i := by
  classical
  by_cases he : s = ∅
  · subst s
    exact ⟨0, by simp⟩
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let q := Fintype.card K
  let d := Module.finrank K V
  let N := q ^ (d - 1)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (Submodule.finrank_lt (hp i₀ hi₀))
  have hN : 0 < N := pow_pos (by omega : 0 < q) _
  have hfull : q * N = Fintype.card V := by
    rw [Module.card_eq_pow_finrank (K := K)]
    exact (mul_comm _ _).trans (Nat.pow_pred_mul hd)
  let A : I → Finset V := fun i => Finset.univ.filter fun x => x ∈ p i
  have hz : ∀ i, (0 : V) ∈ A i := by intro i; simp [A]
  have hA : ∀ i ∈ s, (A i).card ≤ N := by
    intro i hi
    change (Finset.univ.filter fun x : V => x ∈ p i).card ≤ N
    rw [← Fintype.card_subtype (fun x : V => x ∈ p i)]
    rw [Module.card_eq_pow_finrank (K := K)]
    change q ^ Module.finrank K (p i) ≤ q ^ (d - 1)
    have hr := Submodule.finrank_lt (hp i hi)
    gcongr
    omega
  let U := s.biUnion fun i => (A i).erase 0
  have hU : U.card ≤ q * (N - 1) := by
    apply (Finset.card_biUnion_le_card_mul s (fun i => (A i).erase 0) (N - 1) ?_).trans
    · exact Nat.mul_le_mul_right _ hs
    · intro i hi
      have hzero := Finset.card_erase_add_one (hz i)
      have hbound := hA i hi
      omega
  have hcomp : (Finset.univ.erase (0 : V)).card + 1 = Fintype.card V := by
    simpa using (Finset.card_erase_add_one (Finset.mem_univ (0 : V)))
  have hstrict : U.card < (Finset.univ.erase (0 : V)).card := by
    have hprod : q * (N - 1) = q * N - q := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hprod, hfull] at hU
    have hV : q ≤ Fintype.card V := by
      rw [← hfull]
      nlinarith
    omega
  obtain ⟨v, hv, hvU⟩ := Finset.exists_mem_notMem_of_card_lt_card hstrict
  refine ⟨v, ?_⟩
  intro i hi hvp
  apply hvU
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hv).1, by simpa [A] using hvp⟩⟩


/-- One row projection simultaneously detects at most `|K|` nonzero row residuals. -/
theorem exists_row_projection
    {K I R : Type*} [Field K] [Fintype K] [Fintype R]
    (s : Finset I) (v : I → R → K)
    (hv : ∀ i ∈ s, v i ≠ 0) (hs : s.card ≤ Fintype.card K) :
    ∃ lambda : R → K, ∀ i ∈ s, (∑ j, lambda j * v i j) ≠ 0 := by
  classical
  let f : I → ((R → K) →ₗ[K] K) := fun i =>
    { toFun := fun lambda => ∑ j, lambda j * v i j
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.mul_sum, mul_assoc] }
  have hp : ∀ i ∈ s, LinearMap.ker (f i) ≠ ⊤ := by
    intro i hi htop
    obtain ⟨j, hj⟩ : ∃ j, v i j ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hv i hi (funext hn)
    have heval : f i (Pi.single j 1) = v i j := by simp [f, Pi.single_apply]
    have hz : (Pi.single j 1 : R → K) ∈ LinearMap.ker (f i) := by rw [htop]; trivial
    change f i (Pi.single j 1) = 0 at hz
    exact hj (heval.symm.trans hz)
  obtain ⟨lambda, hlambda⟩ := exists_avoiding_subspaces_card_le s
    (fun i => LinearMap.ker (f i)) hp hs
  exact ⟨lambda, by simpa [f] using hlambda⟩

end Sol1
end PackSource_HyperplaneAvoidance

section PackSource_FiniteRowProjection
set_option autoImplicit true
/-! Finite-set row projection and integer-agreement list transfer.
No scalar list bound is asserted: it is an explicit hypothesis. -/

namespace Sol1.FiniteRowProjection

noncomputable section
open scoped BigOperators

variable {K I R : Type*} [Field K] [Fintype K] [Fintype R]

def project (lambda : R → K) (f : I → R → K) : I → K :=
  fun i ↦ ∑ r, lambda r * f i r

omit [Field K] [Fintype K] [Fintype R] in
private theorem exists_coordinate_ne {f g : I → R → K} (hne : f ≠ g) :
    ∃ i, f i ≠ g i := by
  by_contra h
  push Not at h
  exact hne (funext h)

/-- One scalar row functional separates a finite vector-word family when the
ordered-pair count is at most the field size. -/
theorem exists_project_injective (P : Finset (I → R → K))
    (hroom : P.card ^ 2 ≤ Fintype.card K) :
    ∃ lambda : R → K, Set.InjOn (project (I := I) lambda) (P : Set (I → R → K)) := by
  classical
  let pairs := (P.product P).filter fun fg ↦ fg.1 ≠ fg.2
  let coordinate : pairs → I := fun fg ↦
    Classical.choose (exists_coordinate_ne (Finset.mem_filter.mp fg.property).2)
  let residual : pairs → R → K := fun fg ↦ fg.val.1 (coordinate fg) - fg.val.2 (coordinate fg)
  have hresidual : ∀ fg : pairs, residual fg ≠ 0 := by
    intro fg
    exact sub_ne_zero.mpr (Classical.choose_spec
      (exists_coordinate_ne (Finset.mem_filter.mp fg.property).2))
  have hpairs : (Finset.univ : Finset pairs).card ≤ Fintype.card K := by
    rw [Finset.card_univ, Fintype.card_coe]
    calc
      pairs.card ≤ (P.product P).card := Finset.card_filter_le _ _
      _ = P.card ^ 2 := by simp [pow_two]
      _ ≤ Fintype.card K := hroom
  obtain ⟨lambda, hlambda⟩ := Sol1.exists_row_projection
    (Finset.univ : Finset pairs) residual (fun fg _ ↦ hresidual fg) hpairs
  refine ⟨lambda, ?_⟩
  intro f hf g hg heq
  by_contra hne
  let fg : pairs := ⟨(f,g), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf,hg⟩, hne⟩⟩
  apply hlambda fg (Finset.mem_univ _)
  have he := congrFun heq (coordinate fg)
  change (∑ r, lambda r * f (coordinate fg) r) =
    ∑ r, lambda r * g (coordinate fg) r at he
  change (∑ r, lambda r * (f (coordinate fg) r - g (coordinate fg) r)) = 0
  simpa only [mul_sub, Finset.sum_sub_distrib] using sub_eq_zero.mpr he

omit [Fintype K] in
theorem project_mem (C : Submodule K (I → K)) (lambda : R → K)
    (f : I → R → K) (hf : ∀ r, (fun i ↦ f i r) ∈ C) : project lambda f ∈ C := by
  classical
  have hm : (∑ r, lambda r • (fun i ↦ f i r)) ∈ C :=
    C.sum_mem (fun r _ ↦ C.smul_mem (lambda r) (hf r))
  have heq : project lambda f = ∑ r, lambda r • (fun i ↦ f i r) := by
    ext i
    simp [project]
  rw [heq]
  exact hm

open Classical in
def agreementCard [Fintype I] {A : Type*} (f w : I → A) : ℕ :=
  (Finset.univ.filter fun i ↦ f i = w i).card

omit [Field K] [Fintype K] [Fintype R] in
theorem agreementCard_mono [Fintype I] {A B : Type*}
    (f w : I → A) (g z : I → B) (h : ∀ i, f i = w i → g i = z i) :
    agreementCard f w ≤ agreementCard g z := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i (Finset.mem_filter.mp hi).2⟩

omit [Fintype K] in
theorem agreementCard_le_project [Fintype I] (lambda : R → K) (f w : I → R → K) :
    agreementCard f w ≤ agreementCard (project lambda f) (project lambda w) := by
  classical
  apply agreementCard_mono
  intro i he
  simp only [project, he]

/-- A scalar integer-agreement list cap transfers to every finite vector list
under the finite B+1 projection-separation budget. -/
theorem finset_vector_list_card_le [Fintype I]
    (C : Submodule K (I → K)) (A B : ℕ)
    (hroom : (B + 1) ^ 2 ≤ Fintype.card K)
    (hscalar : ∀ w : I → K, ∀ P : Finset (I → K),
      (∀ f ∈ P, f ∈ C ∧ A ≤ agreementCard f w) → P.card ≤ B)
    (w : I → R → K) (P : Finset (I → R → K))
    (hP : ∀ f ∈ P, (∀ r, (fun i ↦ f i r) ∈ C) ∧ A ≤ agreementCard f w) :
    P.card ≤ B := by
  classical
  by_contra hlarge
  have hsize : B + 1 ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hsize
  obtain ⟨lambda, hinj⟩ := exists_project_injective Q (by simpa only [hQcard] using hroom)
  have hprojected : ∀ f ∈ Q.image (project lambda),
      f ∈ C ∧ A ≤ agreementCard f (project lambda w) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode, hagree⟩ := hP g (hQP hg)
    exact ⟨project_mem C lambda g hcode,
      hagree.trans (agreementCard_le_project lambda g w)⟩
  have hbound := hscalar (project lambda w) (Q.image (project lambda)) hprojected
  rw [Finset.card_image_of_injOn hinj, hQcard] at hbound
  omega


end
end Sol1.FiniteRowProjection
end PackSource_FiniteRowProjection

section PackSource_K1_2PruningCount
set_option autoImplicit true
/-!+# Locator-root pruning: finite counting and nullity induction

This module is independent of a matrix representation. The only hypotheses
in `PruningSystem` are the terminal counts and the generic-rank behavior of
constant evaluation rows. No rank assumption is imposed at an individual slope.+-/

namespace K1_2.Pruning
open Finset
noncomputable section

variable {Slope Node State : Type*} [DecidableEq Slope] [DecidableEq Node]

/-- Count all root incidences, including those at exceptional specializations. -/
theorem root_incidence (Γ : Finset Slope) (D H : Finset Node)
    (T : Slope → Finset Node) (t : ℕ)
    (hT : ∀ γ ∈ Γ, T γ ⊆ D) (hcard : ∀ γ ∈ Γ, (T γ).card = t) :
    (t - H.card) * Γ.card ≤
      ∑ a ∈ D \ H, (Γ.filter fun γ => a ∈ T γ).card := by
  have hsum : ∑ γ ∈ Γ, ((T γ) \ H).card =
      ∑ a ∈ D \ H, (Γ.filter fun γ => a ∈ T γ).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨fun ha => ⟨⟨hT γ hγ ha.1, ha.2⟩, ha.1⟩,
      fun ha => ⟨ha.2, ha.1.2⟩⟩
  calc
    (t - H.card) * Γ.card = ∑ _γ ∈ Γ, (t - H.card) := by simp [Nat.mul_comm]
    _ ≤ ∑ γ ∈ Γ, ((T γ) \ H).card := by
      apply Finset.sum_le_sum
      intro γ hγ
      simpa only [hcard γ hγ] using Finset.le_card_sdiff H (T γ)
    _ = _ := hsum

/-- Rational version with a uniform bound on the node fibers. -/
theorem root_incidence_bound (Γ : Finset Slope) (D H : Finset Node)
    (T : Slope → Finset Node) (t : ℕ) (U : ℚ)
    (hT : ∀ γ ∈ Γ, T γ ⊆ D) (hcard : ∀ γ ∈ Γ, (T γ).card = t)
    (hfiber : ∀ a ∈ D \ H, ((Γ.filter fun γ => a ∈ T γ).card : ℚ) ≤ U) :
    ((t - H.card : ℕ) : ℚ) * Γ.card ≤ ((D \ H).card : ℚ) * U := by
  have hcount := root_incidence Γ D H T t hT hcard
  have hcast : ((t - H.card : ℕ) : ℚ) * Γ.card ≤
      ∑ a ∈ D \ H, ((Γ.filter fun γ => a ∈ T γ).card : ℚ) := by
    exact_mod_cast hcount
  exact hcast.trans (by simpa using Finset.sum_le_sum hfiber)

/-- The exact recurrence; terminal determinant charges occur only at leaves. -/
def bound (δ K : ℕ) (C : ℚ) : ℕ → ℚ
  | 0 => δ
  | r + 1 => max ((δ : ℚ) + K) (C * bound δ K C r)

@[simp] theorem bound_zero (δ K : ℕ) (C : ℚ) : bound δ K C 0 = δ := rfl
@[simp] theorem bound_succ (δ K r : ℕ) (C : ℚ) :
    bound δ K C (r+1) = max ((δ : ℚ) + K) (C * bound δ K C r) := rfl

theorem bound_nonneg (δ K : ℕ) (C : ℚ) (hC : 0 ≤ C) (r : ℕ) :
    0 ≤ bound δ K C r := by
  induction r with
  | zero => exact Nat.cast_nonneg δ
  | succ r ih => exact le_max_of_le_left (by positivity)

/-- Matrix facts and the punctured-core cap needed by the counting induction.

`common q` is the set of common domain roots of the generic kernel;
`child q a` appends the constant evaluation row at `a`. The fixed budget
`δ` is valid for the original row basis plus any number of constant rows.
`core_cap` is the sum of a minor-root exceptional set and the punctured cap.
-/
structure PruningSystem (State Slope Node : Type*) [DecidableEq Slope] [DecidableEq Node]
    (t s0 δ K : ℕ) where
  domain : Finset Node
  nullity : State → ℕ
  slopes : State → Finset Slope
  roots : State → Slope → Finset Node
  common : State → Finset Node
  child : State → Node → State
  roots_subset : ∀ q γ, γ ∈ slopes q → roots q γ ⊆ domain
  roots_card : ∀ q γ, γ ∈ slopes q → (roots q γ).card = t
  common_subset : ∀ q, common q ⊆ domain
  common_card : ∀ q, 0 < nullity q → (common q).card ≤ t
  zero_cap : ∀ q, nullity q = 0 → (slopes q).card ≤ δ
  core_cap : ∀ q, 0 < nullity q → t - (common q).card ≤ s0 →
    (slopes q).card ≤ δ + K
  child_nullity : ∀ q a, a ∈ domain \ common q →
    nullity (child q a) + 1 = nullity q
  child_slopes : ∀ q a, a ∈ domain \ common q →
    (slopes q).filter (fun γ => a ∈ roots q γ) ⊆ slopes (child q a)

/-- Complete pruning induction with no intermediate exceptional-set charge. -/
theorem pruning_system_count {t s0 δ K : ℕ}
    (P : PruningSystem State Slope Node t s0 δ K)
    (ht : t ≤ P.domain.card) (q : State) :
    ((P.slopes q).card : ℚ) ≤
      bound δ K (1 + (P.domain.card - t : ℕ) / ((s0 : ℚ) + 1)) (P.nullity q) := by
  let C : ℚ := 1 + (P.domain.card - t : ℕ) / ((s0 : ℚ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  suffices h : ∀ r q, P.nullity q = r → ((P.slopes q).card : ℚ) ≤ bound δ K C r by
    exact h (P.nullity q) q rfl
  intro r
  induction r with
  | zero =>
    intro q hq
    simpa only [bound_zero] using (show ((P.slopes q).card : ℚ) ≤ δ by
      exact_mod_cast P.zero_cap q hq)
  | succ r ih =>
    intro q hq
    have hpos : 0 < P.nullity q := by omega
    by_cases hcore : t - (P.common q).card ≤ s0
    · apply le_trans (b := (δ : ℚ) + K) ?_ (le_max_left _ _)
      exact_mod_cast P.core_cap q hpos hcore
    · have hfiber : ∀ a ∈ P.domain \ P.common q,
          (((P.slopes q).filter fun γ => a ∈ P.roots q γ).card : ℚ) ≤ bound δ K C r := by
        intro a ha
        have hsub : (((P.slopes q).filter fun γ => a ∈ P.roots q γ).card : ℚ) ≤
            ((P.slopes (P.child q a)).card : ℚ) := by
          exact_mod_cast Finset.card_le_card (P.child_slopes q a ha)
        exact hsub.trans (ih (P.child q a) (by have := P.child_nullity q a ha; omega))
      have hinc := root_incidence_bound (P.slopes q) P.domain (P.common q)
        (P.roots q) t (bound δ K C r) (P.roots_subset q) (P.roots_card q) hfiber
      have hH := P.common_card q hpos
      have hHD : (P.common q).card ≤ P.domain.card := Finset.card_le_card (P.common_subset q)
      have hd : (P.domain \ P.common q).card = P.domain.card - (P.common q).card :=
        Finset.card_sdiff_of_subset (P.common_subset q)
      have hs : 0 < ((t - (P.common q).card : ℕ) : ℚ) := by exact_mod_cast (show 0 < t - (P.common q).card by omega)
      have hden : 0 < (s0 : ℚ) + 1 := by positivity
      have hs0 : (s0 : ℚ) + 1 ≤ ((t - (P.common q).card : ℕ) : ℚ) := by exact_mod_cast (show s0+1 ≤ t - (P.common q).card by omega)
      have hratio : (((P.domain \ P.common q).card : ℚ) /
            ((t - (P.common q).card : ℕ) : ℚ)) ≤ C := by
        rw [hd, Nat.cast_sub hHD, Nat.cast_sub hH]
        have hn : 0 ≤ (P.domain.card : ℚ) - t := sub_nonneg.mpr (by exact_mod_cast ht)
        have hs' : 0 < (t : ℚ) - (P.common q).card := by simpa [Nat.cast_sub hH] using hs
        have hs0' : (s0 : ℚ) + 1 ≤ (t : ℚ) - (P.common q).card := by simpa [Nat.cast_sub hH] using hs0
        dsimp [C]
        rw [Nat.cast_sub ht]
        calc
          ((P.domain.card : ℚ) - (P.common q).card) / (t - (P.common q).card) =
              1 + ((P.domain.card : ℚ) - t) / (t - (P.common q).card) := by
            field_simp
            ring
          _ ≤ 1 + ((P.domain.card : ℚ) - t) / ((s0 : ℚ) + 1) :=
            add_le_add_right (div_le_div_of_nonneg_left hn hden hs0') 1
      have hb : ((P.slopes q).card : ℚ) ≤
          (((P.domain \ P.common q).card : ℚ) /
            ((t - (P.common q).card : ℕ) : ℚ)) * bound δ K C r := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hs).mpr
        simpa [mul_comm] using hinc
      exact hb.trans ((mul_le_mul_of_nonneg_right hratio (bound_nonneg δ K C hC r)).trans
        (le_max_right _ _))

end
end K1_2.Pruning
end PackSource_K1_2PruningCount

section PackSource_K1_2PruningArithmetic
set_option autoImplicit true
namespace K1_2.Pruning

def coreK : ℕ := 42657721657869
def productionC : ℚ := 247437 / 67201
def degreeBudget (r : ℕ) : ℕ := 49164 + 2130706433 * (32745 - r)
def nullitySixCap : ℕ := 173829092174484954

theorem productionC_eq :
    (1 + (262144 - 81908 : ℕ) / ((67200 : ℚ) + 1)) = productionC := by
  norm_num [productionC]

theorem degreeBudget_six : degreeBudget 6 = 69757197959151 := by decide

/-- A finite exact-rational certificate. The right endpoint is strict so
natural cardinalities may be rounded down without a floor API. -/
theorem production_bound_lt (r : ℕ) (hr : r ≤ 6) :
    bound (degreeBudget r) coreK productionC r < (nullitySixCap : ℚ) + 1 := by
  interval_cases r <;> norm_num [bound, degreeBudget, coreK, productionC, nullitySixCap]

theorem production_count_le (r N : ℕ) (hr : r ≤ 6)
    (hN : (N : ℚ) ≤ bound (degreeBudget r) coreK productionC r) :
    N ≤ nullitySixCap := by
  have hh := hN.trans_lt (production_bound_lt r hr)
  have : N < nullitySixCap + 1 := by exact_mod_cast hh
  omega

/-- The requested number is the exact floor at nullity six. -/
theorem production_six_floor :
    (nullitySixCap : ℚ) ≤ bound (degreeBudget 6) coreK productionC 6 ∧
    bound (degreeBudget 6) coreK productionC 6 < (nullitySixCap : ℚ) + 1 := by
  norm_num [bound, degreeBudget, coreK, productionC, nullitySixCap]

theorem production_budget_margin :
    nullitySixCap + 29984033161052090 = 203813125335537044 ∧
    274980728111395087 - (nullitySixCap + 29984033161052090) = 71167602775858043 ∧
    nullitySixCap ≤ 244996694950342997 := by decide

/-- An instantiated pruning system on the production-size domain has the
advertised count. Its rank/specialization/core premises remain explicit. -/
theorem production_pruning_count {State Slope Node : Type*}
    [DecidableEq Slope] [DecidableEq Node]
    (r : ℕ) (hr : r ≤ 6)
    (P : PruningSystem State Slope Node 81908 67200 (degreeBudget r) coreK)
    (hn : P.domain.card = 262144) (q : State) (hq : P.nullity q = r) :
    (P.slopes q).card ≤ nullitySixCap := by
  apply production_count_le r _ hr
  have h := pruning_system_count P (by omega) q
  rw [hn, hq] at h
  norm_num [productionC] at h ⊢
  exact h

end K1_2.Pruning
end PackSource_K1_2PruningArithmetic

section PackSource_WeightedIncidence
set_option autoImplicit true
namespace Astra7
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000

variable {F σ ι : Type*} [Field F] [IsAlgClosed F] [Fintype σ] [Fintype ι]

/-- Weighted hypersurface incidence, obtained from a finite coordinate power
cover. The factor on the left is the exact covering degree. -/
theorem weighted_hypersurface_count
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hchar : ∀ i, (w i : F) ≠ 0)
    {g : MvPolynomial σ F} (hg : g ≠ 0) (s : MvPolynomial σ F)
    {v b A m : ℕ} (hv : g.weightedTotalDegree w ≤ v)
    (cuts : ι → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).weightedTotalDegree w ≤ b)
    (hb : 0 < b) (hmA : m ≤ A)
    (hfinite : ∀ T : Finset ι, T.card = m →
      {x : σ → F | aeval x g = 0 ∧ aeval x s ≠ 0 ∧
        ∀ i ∈ T, aeval x (cuts i) = 0}.Finite)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    ((S.card * ∏ i, w i : ℕ) : ℚ) ≤ v *
      ((((Fintype.card ι - m + 1) * b : ℕ) : ℚ) / ((A-m+1 : ℕ) : ℚ)) ^
        (Nat.card σ - 1) := by
  classical
  obtain ⟨theta,htheta⟩ := exists_avoiding_shift S
  let G := powerSubst w theta g
  let Sep := powerSubst w theta s
  let C := fun i => powerSubst w theta (cuts i)
  have hG : G ≠ 0 := by
    intro hz
    apply hg
    apply powerSubst_injective w theta hw
    simpa [G] using hz
  have hGdeg : G.totalDegree ≤ v := (degree_powerSubst w theta g).trans hv
  have hCdeg : ∀ i, (C i).totalDegree ≤ b := fun i =>
    (degree_powerSubst w theta (cuts i)).trans (hdeg i)
  have hfinite' : ∀ T : Finset ι, T.card = m →
      {x : σ → F | aeval x G = 0 ∧ aeval x Sep ≠ 0 ∧
        ∀ i ∈ T, aeval x (C i) = 0}.Finite := by
    intro T hT
    have hh := finite_powerPoint_preimage w theta hw (hfinite T hT)
    simpa [G,Sep,C,Set.preimage_setOf_eq,eval_powerSubst] using hh
  have hLS : ∀ x ∈ liftFinset w theta S, aeval x G = 0 ∧ aeval x Sep ≠ 0 := by
    intro x hx
    have hh := hS _ ((mem_liftFinset w theta x S hw).mp hx)
    simpa [G,Sep,eval_powerSubst] using hh
  have hLA : ∀ x ∈ liftFinset w theta S, A ≤ {i | aeval x (C i) = 0}.ncard := by
    intro x hx
    have hh := hA _ ((mem_liftFinset w theta x S hw).mp hx)
    simpa [C,eval_powerSubst] using hh
  have hh := hypersurface_card_le_of_finite_fibers hG Sep hGdeg C hCdeg hb hmA
    hfinite' (liftFinset w theta S) hLS hLA
  rwa [card_liftFinset w theta S hw hchar htheta] at hh

end
end Astra7
end PackSource_WeightedIncidence
