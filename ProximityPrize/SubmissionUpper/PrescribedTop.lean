/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.IRSHalfRadius

/-!
# A prescribed-top-coefficient collision family below half radius

The included baseline attacks at radius `1/2` using the word `X^m` together with
*every* `m`-subset of the domain as an interpolation set.  This file generalises
that construction: it uses `t`-subsets with `t = m + r`, restricted to those whose
vanishing polynomial shares its top `r` coefficients with a fixed one.  Each such
subset still yields a genuine codeword agreeing with a single fixed word on all `t`
points, so the attack survives at radius `(n - t)/n = 1/2 - r/n`.

With `r = 8431` this certifies the unsafe suffix from grid index `122641` onward.
-/

namespace ProximityPrize.SubmissionUpper.PrescribedTop

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open scoped NNReal


open ProximityPrize.Benchmark

abbrev K := _root_.KoalaBear.Field
abbrev FF := IRSProfile.Field
abbrev Idx := IRSProfile.Index

/-- Agreement-set size: `m + r = 131072 + 8431`. -/
abbrev tt : ℕ := 139503
/-- Number of prescribed top coefficients. -/
abbrev rr : ℕ := 8431

noncomputable def nodes (j : Idx) : K := IRSProfile.baseNttDomain.node j

theorem domain_eq (j : Idx) : IRSProfile.domain j = algebraMap K FF (nodes j) := rfl

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  apply IRSProfile.domain.injective
  rw [domain_eq, domain_eq, h]

noncomputable def g (J : Finset Idx) : Polynomial K :=
  ∏ j ∈ J, (Polynomial.X - Polynomial.C (nodes j))

/-- The prescribed top-coefficient signature: coefficients in degrees `tt-1 … tt-rr`. -/
noncomputable def key (J : Finset Idx) : Fin rr → K :=
  fun i => (g J).coeff (tt - 1 - i.val)

theorem card_Idx : Fintype.card Idx = 262144 := by
  simp

theorem card_K : Fintype.card K = 2 ^ 31 - 2 ^ 24 + 1 :=
  ZMod.card _root_.KoalaBear.fieldSize

theorem card_FF : Fintype.card FF = (2 ^ 31 - 2 ^ 24 + 1) ^ 6 :=
  _root_.KoalaBear.card_ext6

theorem card_keys : Fintype.card (Fin rr → K) = (2 ^ 31 - 2 ^ 24 + 1) ^ 8431 := by
  rw [Fintype.card_fun, card_K, Fintype.card_fin]

theorem card_powerset :
    (Finset.powersetCard tt (Finset.univ : Finset Idx)).card = Nat.choose 262144 139503 := by
  rw [Finset.card_powersetCard, Finset.card_univ, card_Idx]




/-- `4ab <= (a+b)^2`. -/
theorem four_mul_le_sq (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := by
  have h : 2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_sq a b
  nlinarith [h]

/-- Along a segment of constant sum, the product is smallest at the ends. -/
theorem pair_lower (A k i : ℕ) (hik : i ≤ k) :
    (A + k) * A ≤ (A + (k - i)) * (A + i) := by
  obtain ⟨d, hd⟩ := Nat.le.dest hik
  subst hd
  simp only [Nat.add_sub_cancel_left]
  nlinarith

/-- Squared upper bound on the ascending factorial, via pairing. -/
theorem prod_sq_up :
    4 ^ 8431 * (∏ i ∈ Finset.range 8431, (131072 + 1 + i)) ^ 2 ≤ 270576 ^ 16862 := by
  have hrefl : (∏ i ∈ Finset.range 8431, (131072 + 1 + (8431 - 1 - i)))
      = ∏ i ∈ Finset.range 8431, (131072 + 1 + i) :=
    Finset.prod_range_reflect (fun i => 131072 + 1 + i) 8431
  have hsq : (∏ i ∈ Finset.range 8431,
        ((131072 + 1 + i) * (131072 + 1 + (8431 - 1 - i))))
      = (∏ i ∈ Finset.range 8431, (131072 + 1 + i)) ^ 2 := by
    rw [Finset.prod_mul_distrib, hrefl, ← pow_two]
  have h4 : (4 : ℕ) ^ 8431 = ∏ _i ∈ Finset.range 8431, (4 : ℕ) := by
    rw [Finset.prod_const, Finset.card_range]
  have hR : (270576 : ℕ) ^ 16862 = ∏ _i ∈ Finset.range 8431, ((270576 : ℕ) ^ 2) := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul]
  rw [← hsq, h4, hR, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' ?_
  intro i hi
  have hik := Finset.mem_range.mp hi
  have hsum : (131072 + 1 + i) + (131072 + 1 + (8431 - 1 - i)) = 270576 := by omega
  calc 4 * ((131072 + 1 + i) * (131072 + 1 + (8431 - 1 - i)))
      ≤ ((131072 + 1 + i) + (131072 + 1 + (8431 - 1 - i))) ^ 2 := four_mul_le_sq _ _
    _ = 270576 ^ 2 := by rw [hsum]

/-- Squared lower bound on the descending factorial, via pairing. -/
theorem prod_sq_lo :
    ((131072 : ℕ) * 122642) ^ 8431
      ≤ (∏ i ∈ Finset.range 8431, (262144 - 131072 - i)) ^ 2 := by
  have hrefl : (∏ i ∈ Finset.range 8431, (262144 - 131072 - (8431 - 1 - i)))
      = ∏ i ∈ Finset.range 8431, (262144 - 131072 - i) :=
    Finset.prod_range_reflect (fun i => 262144 - 131072 - i) 8431
  have hsq : (∏ i ∈ Finset.range 8431,
        ((262144 - 131072 - i) * (262144 - 131072 - (8431 - 1 - i))))
      = (∏ i ∈ Finset.range 8431, (262144 - 131072 - i)) ^ 2 := by
    rw [Finset.prod_mul_distrib, hrefl, ← pow_two]
  have hL : ((131072 : ℕ) * 122642) ^ 8431
      = ∏ _i ∈ Finset.range 8431, ((131072 : ℕ) * 122642) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← hsq, hL]
  refine Finset.prod_le_prod' ?_
  intro i hi
  have hik := Finset.mem_range.mp hi
  have e1 : 262144 - 131072 - i = 122642 + (8430 - i) := by omega
  have e2 : 262144 - 131072 - (8431 - 1 - i) = 122642 + i := by omega
  have e3 : (131072 : ℕ) * 122642 = (122642 + 8430) * 122642 := by norm_num
  rw [e1, e2, e3]
  exact pair_lower 122642 8430 i (by omega)


theorem choose_shift (N a : ℕ) : ∀ b : ℕ,
    N.choose (a + b) * (∏ i ∈ Finset.range b, (a + 1 + i))
      = N.choose a * (∏ i ∈ Finset.range b, (N - a - i)) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hstep : N.choose (a + b + 1) * (a + b + 1) = N.choose (a + b) * (N - (a + b)) :=
        Nat.choose_succ_right_eq N (a + b)
      calc
        N.choose (a + (b + 1)) * ((∏ i ∈ Finset.range b, (a + 1 + i)) * (a + 1 + b))
            = (N.choose (a + b + 1) * (a + b + 1)) * (∏ i ∈ Finset.range b, (a + 1 + i)) := by
              rw [show a + (b + 1) = a + b + 1 by omega, show a + 1 + b = a + b + 1 by omega]
              ring
        _ = (N.choose (a + b) * (N - (a + b))) * (∏ i ∈ Finset.range b, (a + 1 + i)) := by
              rw [hstep]
        _ = (N.choose (a + b) * (∏ i ∈ Finset.range b, (a + 1 + i))) * (N - (a + b)) := by ring
        _ = (N.choose a * (∏ i ∈ Finset.range b, (N - a - i))) * (N - (a + b)) := by rw [ih]
        _ = N.choose a * ((∏ i ∈ Finset.range b, (N - a - i)) * (N - a - b)) := by
              rw [show N - (a + b) = N - a - b by omega]; ring

theorem abstract_contradiction2 {Ca Cb U L P W V F four c : ℕ}
    (hF : 0 < F) (hV : 0 < V)
    (hshift : Cb * U = Ca * L)
    (hup : F * U ^ 2 ≤ W)
    (hlo : V ≤ L ^ 2)
    (hcb : four < c * Ca)
    (hcon : Cb ≤ P)
    (hnum : c ^ 2 * P ^ 2 * W ≤ F * four ^ 2 * V) : False := by
  have hFV : 0 < F * V := Nat.mul_pos hF hV
  have hsq : four ^ 2 < (c * Ca) ^ 2 := Nat.pow_lt_pow_left hcb (by norm_num)
  have hstep : F * four ^ 2 * V < F * (c * Ca) ^ 2 * V := by
    calc F * four ^ 2 * V = four ^ 2 * (F * V) := by ring
      _ < (c * Ca) ^ 2 * (F * V) := Nat.mul_lt_mul_of_lt_of_le hsq (le_refl (F * V)) hFV
      _ = F * (c * Ca) ^ 2 * V := by ring
  have hstrict : F * four ^ 2 * V < c ^ 2 * P ^ 2 * W := by
    calc F * four ^ 2 * V
        < F * (c * Ca) ^ 2 * V := hstep
      _ ≤ F * (c * Ca) ^ 2 * L ^ 2 := Nat.mul_le_mul_left _ hlo
      _ = c ^ 2 * (F * (Ca * L) ^ 2) := by ring
      _ = c ^ 2 * (F * (Cb * U) ^ 2) := by rw [hshift]
      _ = c ^ 2 * Cb ^ 2 * (F * U ^ 2) := by ring
      _ ≤ c ^ 2 * Cb ^ 2 * W := Nat.mul_le_mul_left _ hup
      _ ≤ c ^ 2 * P ^ 2 * W :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcon 2))
  exact absurd hnum (not_le.mpr hstrict)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 900000 in
theorem numeric_fact2 :
    131072 ^ 2 * (((2 ^ 31 - 2 ^ 24 + 1) ^ 8431 * 2 ^ 59) ^ 2) * 270576 ^ 16862
      ≤ 4 ^ 8431 * (4 ^ 131072) ^ 2 * ((131072 : ℕ) * 122642) ^ 8431 := by decide

theorem key_counting :
    (2 ^ 31 - 2 ^ 24 + 1) ^ 8431 * 2 ^ 59 < Nat.choose 262144 139503 := by
  by_contra hcon
  push Not at hcon
  have hshift : Nat.choose 262144 139503 * (∏ i ∈ Finset.range 8431, (131072 + 1 + i))
      = Nat.choose 262144 131072 * (∏ i ∈ Finset.range 8431, (262144 - 131072 - i)) := by
    have h := choose_shift 262144 131072 8431
    rwa [show (131072 + 8431 : ℕ) = 139503 by norm_num] at h
  have hcb : (4 : ℕ) ^ 131072 < 131072 * Nat.choose 262144 131072 := by
    have h := Nat.four_pow_lt_mul_centralBinom 131072 (by norm_num)
    rw [Nat.centralBinom_eq_two_mul_choose,
      show (2 * 131072 : ℕ) = 262144 by norm_num] at h
    exact h
  exact abstract_contradiction2 (by positivity) (by positivity) hshift
    prod_sq_up prod_sq_lo hcb hcon numeric_fact2

/-- Pigeonhole over a `Fintype` codomain: some fibre beats the average.
`Finset.univ` on the codomain appears only inside this proof, where the codomain
is still a variable, so no giant instance is ever unfolded at a use site. -/
theorem pigeonhole {α β : Type} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) (n : ℕ)
    (hn : Fintype.card β * n < s.card) :
    ∃ y : β, n < (s.filter (fun x => f x = y)).card := by
  by_contra hcon
  push Not at hcon
  have hsum : s.card
      = ∑ y ∈ (Finset.univ : Finset β), (s.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ _)
  have hle : ∑ y ∈ (Finset.univ : Finset β), (s.filter (fun x => f x = y)).card
      ≤ ∑ _y ∈ (Finset.univ : Finset β), n :=
    Finset.sum_le_sum (fun y _ => hcon y)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at hle
  omega

set_option maxRecDepth 40000 in
theorem exists_big_fiber :
    ∃ σ : Fin rr → K,
      2 ^ 59 <
        ((Finset.powersetCard tt (Finset.univ : Finset Idx)).filter
          (fun J => key J = σ)).card := by
  refine pigeonhole (Finset.powersetCard tt (Finset.univ : Finset Idx)) key _ ?_
  rw [card_keys, card_powerset]
  exact key_counting

theorem g_monic (J : Finset Idx) : (g J).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (nodes j)

theorem g_natDegree (J : Finset Idx) : (g J).natDegree = J.card := by
  classical
  rw [g, Polynomial.natDegree_prod_of_monic _ _
    (fun j (_ : j ∈ J) => Polynomial.monic_X_sub_C (nodes j))]
  simp

theorem g_eval (J : Finset Idx) (j : Idx) :
    (g J).eval (nodes j) = 0 ↔ j ∈ J := by
  classical
  constructor
  · intro h
    rw [g, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨a, ha, hva⟩ := h
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hva
    rwa [nodes_injective hva]
  · intro h
    rw [g, Polynomial.eval_prod]
    refine Finset.prod_eq_zero h ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

theorem g_coeff_top {J : Finset Idx} (hJ : J.card = tt) : (g J).coeff tt = 1 := by
  have hm := g_monic J
  rw [Polynomial.Monic, Polynomial.leadingCoeff, g_natDegree, hJ] at hm
  exact hm

theorem g_coeff_gt {J : Finset Idx} (hJ : J.card = tt) {d : ℕ} (hd : tt < d) :
    (g J).coeff d = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [g_natDegree, hJ]; exact hd

theorem coeff_eq_of_key {J J' : Finset Idx} (hkey : key J = key J')
    {d : ℕ} (hd1 : 131072 ≤ d) (hd2 : d ≤ 139502) :
    (g J).coeff d = (g J').coeff d := by
  have hi : 139502 - d < 8431 := by omega
  have h := congrFun hkey ⟨139502 - d, hi⟩
  simp only [key] at h
  rwa [show (139503 : ℕ) - 1 - (139502 - d) = d by omega] at h

/-- Two members of the same fibre differ by a polynomial of degree `< 131072`,
which is exactly the row-degree budget of the code. -/
theorem sub_degree_lt {J J' : Finset Idx}
    (hJ : J.card = tt) (hJ' : J'.card = tt) (hkey : key J = key J') :
    (g J' - g J).degree < (131072 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro d hd
  have hdn : (131072 : ℕ) ≤ d := by exact_mod_cast hd
  rw [Polynomial.coeff_sub]
  rcases lt_trichotomy d 139503 with hlt | heq | hgt
  · have hle : d ≤ 139502 := by omega
    rw [coeff_eq_of_key (J := J') (J' := J) hkey.symm hdn hle, sub_self]
  · have : d = tt := heq
    subst this
    rw [g_coeff_top hJ', g_coeff_top hJ, sub_self]
  · have hgt' : tt < d := hgt
    rw [g_coeff_gt hJ' hgt', g_coeff_gt hJ hgt', sub_self]


abbrev kk := IRSProfile.totalDimension
abbrev ss := IRSProfile.interleaving
abbrev mm : ℕ := 131072

local instance : NeZero ss := ⟨by norm_num [ss, IRSProfile.interleaving]⟩

theorem rowDimension_eq : kk / ss = mm :=
  IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [mm, IRSProfile.baseDimension])

/-- Every polynomial below the row-degree budget is realised by a message whose
encoding puts its evaluations in row `0` and zero in every other row. -/
theorem exists_message (c : Polynomial FF) (hdeg : c.degree < (kk / ss : ℕ)) :
    ∃ u : Fin kk → FF, ∀ j : Idx, ∀ row : Fin ss,
      IRSProfile.encoder u j row =
        if row = 0 then c.eval (IRSProfile.domain j) else 0 := by
  classical
  have hpmem : c ∈ Polynomial.degreeLT FF (kk / ss) := Polynomial.mem_degreeLT.mpr hdeg
  let coeff : Fin (kk / ss) → FF := Polynomial.degreeLTEquiv FF (kk / ss) ⟨c, hpmem⟩
  let rows : Fin ss → Fin (kk / ss) → FF := fun row => if row = 0 then coeff else 0
  let u : Fin kk → FF := flatten kk ss IRSProfile.interleaving_dvd_totalDimension rows
  have hpoly : ToyProblem.Spec.rsPolynomial (kk / ss) coeff = c := by
    exact congrArg Subtype.val
      ((Polynomial.degreeLTEquiv FF (kk / ss)).symm_apply_apply ⟨c, hpmem⟩)
  refine ⟨u, ?_⟩
  intro j row
  rw [IRSProfile.encoder, encoder_apply]
  change ToyProblem.Spec.rsEncoder (kk / ss) IRSProfile.domain
      (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension
        (flatten kk ss IRSProfile.interleaving_dvd_totalDimension rows) row) j = _
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows 0 = coeff by simp [rows], ToyProblem.Spec.rsEncoder_apply, hpoly]
    simp
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (kk / ss) IRSProfile.domain)) j
    simp only [rows, hrow, if_false]
    simpa [hrow] using hz



/-! ## The chosen fibre -/

noncomputable def sigma0 : Fin rr → K := Classical.choose exists_big_fiber

noncomputable def Fam : Finset (Finset Idx) :=
  (Finset.powersetCard tt (Finset.univ : Finset Idx)).filter (fun J => key J = sigma0)

theorem Fam_card_gt : 2 ^ 59 < Fam.card :=
  Classical.choose_spec exists_big_fiber

theorem Fam_card_eq {J : Finset Idx} (h : J ∈ Fam) : J.card = tt :=
  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h).1).2

theorem Fam_key {J : Finset Idx} (h : J ∈ Fam) : key J = sigma0 :=
  (Finset.mem_filter.mp h).2

theorem Fam_nonempty : Fam.Nonempty := by
  rw [← Finset.card_pos]
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) Fam_card_gt

noncomputable def J0 : Finset Idx := Fam_nonempty.choose

theorem J0_mem : J0 ∈ Fam := Fam_nonempty.choose_spec

/-! ## Transporting the vanishing polynomials to the extension field -/

noncomputable def gF (J : Finset Idx) : Polynomial FF := (g J).map (algebraMap K FF)

theorem algebraMap_injective : Function.Injective (algebraMap K FF) :=
  (algebraMap K FF).injective

theorem gF_eval (J : Finset Idx) (j : Idx) :
    (gF J).eval (IRSProfile.domain j) = algebraMap K FF ((g J).eval (nodes j)) := by
  rw [gF, Polynomial.eval_map, domain_eq]
  exact Polynomial.eval₂_at_apply _ _

theorem gF_eval_zero_iff (J : Finset Idx) (j : Idx) :
    (gF J).eval (IRSProfile.domain j) = 0 ↔ j ∈ J := by
  rw [gF_eval, map_eq_zero_iff _ algebraMap_injective]
  exact g_eval J j

theorem gF_natDegree {J : Finset Idx} (hJ : J.card = tt) : (gF J).natDegree = tt := by
  rw [gF, Polynomial.natDegree_map_eq_of_injective algebraMap_injective, g_natDegree, hJ]

/-! ## The codeword polynomials -/

noncomputable def cpoly (J : Finset Idx) : Polynomial FF := gF J0 - gF J

theorem cpoly_degree {J : Finset Idx} (hJ : J ∈ Fam) : (cpoly J).degree < (131072 : ℕ) := by
  have hk : key J = key J0 := (Fam_key hJ).trans (Fam_key J0_mem).symm
  have h := sub_degree_lt (Fam_card_eq hJ) (Fam_card_eq J0_mem) hk
  calc (cpoly J).degree
      = ((g J0 - g J).map (algebraMap K FF)).degree := by
        rw [cpoly, gF, gF, Polynomial.map_sub]
    _ ≤ (g J0 - g J).degree := Polynomial.degree_map_le
    _ < (131072 : ℕ) := h

/-! ## The fixed word and its messages -/

noncomputable def word : Idx → Fin ss → FF :=
  fun j row => if row = 0 then (gF J0).eval (IRSProfile.domain j) else 0

abbrev Carrier := {J : Finset Idx // J ∈ Fam}

theorem cpoly_degree' (a : Carrier) : (cpoly a.val).degree < (kk / ss : ℕ) := by
  rw [rowDimension_eq]
  exact cpoly_degree a.prop

noncomputable def pmsg (a : Carrier) : Fin kk → FF :=
  Classical.choose (exists_message (cpoly a.val) (cpoly_degree' a))

theorem pmsg_spec (a : Carrier) (j : Idx) (row : Fin ss) :
    IRSProfile.encoder (pmsg a) j row =
      if row = 0 then (cpoly a.val).eval (IRSProfile.domain j) else 0 :=
  Classical.choose_spec (exists_message (cpoly a.val) (cpoly_degree' a)) j row

/-- On its own subset, the fixed word agrees with the codeword of that subset. -/
theorem word_agree (a : Carrier) (j : Idx) (hj : j ∈ a.val) :
    word j = IRSProfile.encoder (pmsg a) j := by
  funext row
  rw [word, pmsg_spec]
  by_cases hrow : row = 0
  · subst hrow
    simp only
    rw [cpoly, Polynomial.eval_sub, (gF_eval_zero_iff a.val j).mpr hj, sub_zero]
  · simp only [if_neg hrow]

/-- No message agrees with the fixed word on more than `t` points. -/
theorem word_far (u : Fin kk → FF) (S : Finset Idx) (hcard : tt < S.card)
    (hagree : ∀ j ∈ S, word j = IRSProfile.encoder u j) : False := by
  classical
  have hSbig : 139503 < S.card := hcard
  let q : Polynomial FF := ToyProblem.Spec.rsPolynomial (kk / ss)
    (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg0 : q.degree < ((kk / ss : ℕ) : WithBot ℕ) :=
    ToyProblem.Spec.rsPolynomial_degree_lt _ _
  have hcast : ((kk / ss : ℕ) : WithBot ℕ) = ((131072 : ℕ) : WithBot ℕ) := by
    rw [rowDimension_eq]
  have hqdeg : q.degree < ((131072 : ℕ) : WithBot ℕ) := by rwa [hcast] at hqdeg0
  have hle : (131072 : ℕ) ≤ S.card := by omega
  have hqdegS : q.degree < ((S.card : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hqdeg (by exact_mod_cast hle)
  have hnd : (gF J0).natDegree = tt := gF_natDegree (Fam_card_eq J0_mem)
  have hne : gF J0 ≠ 0 := by
    intro h0
    rw [h0] at hnd
    simp at hnd
  have hPdegS : (gF J0).degree < ((S.card : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hne, hnd]
    exact_mod_cast hSbig
  have heval : ∀ j ∈ S, (gF J0).eval (IRSProfile.domain j) = q.eval (IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin ss)
    rw [word] at h
    simp only [if_pos] at h
    rw [IRSProfile.encoder, encoder_apply, ToyProblem.Spec.rsEncoder_apply] at h
    exact h
  have heq : gF J0 = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq S IRSProfile.domain.injective.injOn
      hPdegS hqdegS heval
  rw [heq] at hnd
  have hnd' : q.natDegree = 139503 := hnd
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0] at hnd'
    simp at hnd'
  have hlt : q.natDegree < 131072 := (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hqdeg
  omega

/-- Distinct subsets in the family give distinct messages. -/
theorem pmsg_injective : Function.Injective pmsg := by
  intro a b hab
  have hcard : (131072 : ℕ) ≤ (Finset.univ : Finset Idx).card := by
    rw [Finset.card_univ, card_Idx]; norm_num
  have hcp : cpoly a.val = cpoly b.val := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset Idx)
      IRSProfile.domain.injective.injOn ?_ ?_ ?_
    · exact lt_of_lt_of_le (cpoly_degree a.prop) (by exact_mod_cast hcard)
    · exact lt_of_lt_of_le (cpoly_degree b.prop) (by exact_mod_cast hcard)
    · intro j _
      have ha := pmsg_spec a j 0
      have hb := pmsg_spec b j 0
      rw [hab] at ha
      simp only [if_pos] at ha hb
      rw [← ha, hb]
  have hgF : gF a.val = gF b.val := by
    have hsub : gF J0 - gF a.val = gF J0 - gF b.val := hcp
    exact sub_right_injective hsub
  apply Subtype.ext
  ext j
  rw [← gF_eval_zero_iff a.val j, ← gF_eval_zero_iff b.val j, hgF]


/-! ## The unsafe suffix from grid index `122641` -/

theorem card_Carrier : Fintype.card Carrier = Fam.card := Fintype.card_coe _

theorem carrier_large : 2 ^ 59 < Fintype.card Carrier := by
  rw [card_Carrier]
  exact Fam_card_gt

theorem card_FF_lt : Fintype.card FF < 2 ^ 186 := by
  rw [card_FF]
  norm_num

theorem carrier_density_nat :
    Fintype.card FF + Fintype.card Carrier - 1 <
      Fintype.card Carrier * 2 ^ 128 := by
  have hq := card_FF_lt
  have hN := carrier_large
  omega

theorem nnreal_cast_add_sub_one (q N : ℕ) :
    (q : ℝ≥0) + (N : ℝ≥0) - 1 = ((q + N - 1 : ℕ) : ℝ≥0) := by
  apply NNReal.eq
  norm_num

theorem nnreal_fraction_lt (q N k : ℕ) (hk : 0 < k) (hd : 0 < q + N - 1)
    (h : q + N - 1 < N * k) :
    (1 : ℝ≥0) / (k : ℝ≥0) <
      (N : ℝ≥0) / ((q + N - 1 : ℕ) : ℝ≥0) := by
  have hk' : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  have hd' : (0 : ℝ≥0) < ((q + N - 1 : ℕ) : ℝ≥0) := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hk' hd']
  norm_num
  exact_mod_cast h

theorem epsilon_lt_carrier_fraction :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      (Fintype.card Carrier : ℝ≥0) /
        ((Fintype.card FF + Fintype.card Carrier - 1 : ℕ) : ℝ≥0) := by
  unfold ProximityPrize.Benchmark.Upper.epsilonStar ProximityGap.prizeThreshold
  push_cast
  change (1 : ℝ≥0) / 2 ^ (128 : ℕ) <
    (Fintype.card Carrier : ℝ≥0) /
      ((Fintype.card FF : ℝ≥0) + (Fintype.card Carrier : ℝ≥0) - 1)
  rw [nnreal_cast_add_sub_one]
  have hdenNat : 0 < Fintype.card FF + Fintype.card Carrier - 1 := by
    have hq : 0 < Fintype.card FF := Fintype.card_pos
    have hN : 0 < Fintype.card Carrier := lt_trans (by positivity) carrier_large
    omega
  have h := nnreal_fraction_lt _ _ _ (by positivity) hdenNat carrier_density_nat
  rw [Nat.cast_pow] at h
  exact h

/-- For every radius in the certified band, the quantitative collision image
already has density strictly above `2^-128`. -/
theorem winningSetDensity_gt_epsilon (δ : ℝ≥0)
    (hlo : (122641 / 262144 : ℝ≥0) ≤ δ)
    (hhi : δ < IRSProfile.minRelativeDistance) :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      winningSetDensity IRSProfile.encoder δ := by
  classical
  have hcardI : Fintype.card Idx = 262144 := card_Idx
  have hd_lo : (122641 / 262144 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hlo
  have hd_hi : (δ : ℝ) < 131073 / 262144 := by
    have h : (δ : ℝ) < (IRSProfile.minRelativeDistance : ℝ) := by exact_mod_cast hhi
    rwa [show ((IRSProfile.minRelativeDistance : ℝ≥0) : ℝ) = 131073 / 262144 by
      unfold IRSProfile.minRelativeDistance; norm_num] at h
  have hx_lo : (131071 : ℝ) < (1 - (δ : ℝ)) * 262144 := by nlinarith
  have hx_hi : (1 - (δ : ℝ)) * 262144 ≤ 139503 := by nlinarith
  have hx_pos : (0 : ℝ) ≤ (1 - (δ : ℝ)) * 262144 := by linarith
  have ht'_lo : 131072 ≤ Nat.ceil ((1 - (δ : ℝ)) * 262144) := by
    have h : 131071 < Nat.ceil ((1 - (δ : ℝ)) * 262144) :=
      Nat.lt_ceil.mpr (by exact_mod_cast hx_lo)
    omega
  have ht'_hi : Nat.ceil ((1 - (δ : ℝ)) * 262144) ≤ 139503 :=
    Nat.ceil_le.mpr (by exact_mod_cast hx_hi)
  have hsub : ∀ a : Carrier, ∃ T ⊆ a.val, T.card = Nat.ceil ((1 - (δ : ℝ)) * 262144) := by
    intro a
    exact Finset.exists_subset_card_eq (by rw [Fam_card_eq a.prop]; exact ht'_hi)
  choose T hTsub hTcard using hsub
  refine lt_of_lt_of_le epsilon_lt_carrier_fraction ?_
  refine HalfRadiusCollision.winningSetDensity_ge_of_fixed_word_list
    (F := FF) (m := Nat.ceil ((1 - (δ : ℝ)) * 262144))
    IRSProfile.encoder δ ?_ ?_ pmsg T word pmsg_injective ?_ hTcard ?_ ?_
  · rw [hcardI]
    have hceil : ((Nat.ceil ((1 - (δ : ℝ)) * 262144) : ℕ) : ℝ) < (1 - (δ : ℝ)) * 262144 + 1 :=
      Nat.ceil_lt_add_one hx_pos
    have hone : (1 : ℕ) ≤ Nat.ceil ((1 - (δ : ℝ)) * 262144) := by omega
    rw [Nat.cast_sub hone]
    push_cast
    linarith
  · rw [hcardI]
    have h := Nat.le_ceil ((1 - (δ : ℝ)) * 262144)
    push_cast
    exact h
  · exact lt_trans (by positivity) carrier_large
  · intro a j hj
    exact word_agree a j (hTsub a hj)
  · intro u S hS hzero
    refine IRSHalfRadius.IRSProfile.message_eq_zero_of_zero_on_many u S ?_ hzero
    have hm : IRSHalfRadius.m = 131072 := rfl
    omega

end ProximityPrize.SubmissionUpper.PrescribedTop
