/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

namespace ProximityPrize.SubmissionUpper.FixedDomainBridge

open ToyProblem
open scoped NNReal

variable {F : Type} [Field F]

/-- A union bound chooses a point outside a forbidden set at which all members
of a bounded-degree polynomial family take distinct values.  The count uses
ordered pairs; replacing `L * (L - 1)` by `choose L 2` is a possible refinement
but is unnecessary for the benchmark numerics. -/
theorem exists_eval_injective_off_domain
    [Fintype F] [DecidableEq F]
    {J : Type} [Fintype J] [DecidableEq J]
    (domain : Finset F) (H : J → Polynomial F) (d : ℕ)
    (hH : Function.Injective H)
    (hdegree : ∀ j, (H j).natDegree ≤ d)
    (hcount : domain.card + Fintype.card J * (Fintype.card J - 1) * d <
      Fintype.card F) :
    ∃ α : F, α ∉ domain ∧ Function.Injective (fun j ↦ (H j).eval α) := by
  classical
  let collisionRoots (jk : J × J) : Finset F :=
    (H jk.1 - H jk.2).roots.toFinset
  have hcollision (jk : J × J) (hjk : jk ∈ (Finset.univ : Finset J).offDiag) :
      (collisionRoots jk).card ≤ d := by
    have hmem := Finset.mem_offDiag.mp hjk
    have hdeg : (H jk.1 - H jk.2).natDegree ≤ d :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le (hdegree jk.1) (hdegree jk.2))
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' (H jk.1 - H jk.2)).trans hdeg)
  let bad : Finset F := domain ∪ (Finset.univ : Finset J).offDiag.biUnion collisionRoots
  have hbad : bad.card < Fintype.card F := by
    have hcoll : ((Finset.univ : Finset J).offDiag.biUnion collisionRoots).card ≤
        (Finset.univ : Finset J).offDiag.card * d :=
      Finset.card_biUnion_le_card_mul _ _ d hcollision
    have hoff : (Finset.univ : Finset J).offDiag.card =
        Fintype.card J * (Fintype.card J - 1) := by
      rw [Finset.offDiag_card, Finset.card_univ, Nat.mul_sub_left_distrib]
      simp
    calc
      bad.card ≤ domain.card +
          ((Finset.univ : Finset J).offDiag.biUnion collisionRoots).card := by
        exact Finset.card_union_le _ _
      _ ≤ domain.card + (Finset.univ : Finset J).offDiag.card * d :=
        Nat.add_le_add_left hcoll _
      _ = domain.card + Fintype.card J * (Fintype.card J - 1) * d := by rw [hoff]
      _ < Fintype.card F := hcount
  have hex : ∃ α : F, α ∉ bad := by
    by_contra h
    push Not at h
    have hbaduniv : bad = Finset.univ := by ext α; simp [h α]
    rw [hbaduniv, Finset.card_univ] at hbad
    exact (lt_irrefl _) hbad
  obtain ⟨α, hα⟩ := hex
  refine ⟨α, ?_, ?_⟩
  · intro hαdomain
    apply hα
    exact Finset.mem_union_left _ hαdomain
  · intro j k heval
    by_contra hjk
    apply hα
    have hroot : α ∈ collisionRoots (j, k) := by
      dsimp only [collisionRoots]
      rw [Multiset.mem_toFinset,
        Polynomial.mem_roots (sub_ne_zero.mpr (fun heq ↦ hjk (hH heq)))]
      simpa [Polynomial.eval_sub] using sub_eq_zero.mpr heval
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(j, k), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩, hroot⟩)

/-- Divide off the forced root at `α`. -/
noncomputable def quotientAt (H : Polynomial F) (α : F) : Polynomial F :=
  (H - Polynomial.C (H.eval α)) /ₘ (Polynomial.X - Polynomial.C α)

theorem factor_mul_quotientAt (H : Polynomial F) (α : F) :
    (Polynomial.X - Polynomial.C α) * quotientAt H α =
      H - Polynomial.C (H.eval α) := by
  apply Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
  simp [Polynomial.IsRoot]

theorem quotientAt_natDegree_lt {H : Polynomial F} {α : F} {k : ℕ}
    (hk : 0 < k) (hdegree : H.natDegree ≤ k) :
    (quotientAt H α).natDegree < k := by
  rw [quotientAt, Polynomial.natDegree_divByMonic _
    (Polynomial.monic_X_sub_C α), Polynomial.natDegree_X_sub_C]
  have hnum : (H - Polynomial.C (H.eval α)).natDegree ≤ H.natDegree := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  omega

theorem eval_quotientAt {H : Polynomial F} {α x : F} (hx : x ≠ α) :
    (quotientAt H α).eval x = (H.eval x - H.eval α) / (x - α) := by
  have h := congrArg (Polynomial.eval x) (factor_mul_quotientAt H α)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at h
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  rw [mul_comm]
  exact h

theorem quotientAt_agrees_on_close_points
    {I : Type} (domain : I → F) (c : I → F)
    {H : Polynomial F} {α : F} {z : F} {i : I}
    (hα : domain i ≠ α) (hz : H.eval α = z) (hag : H.eval (domain i) = c i) :
    c i / (domain i - α) + z * (-1 / (domain i - α)) =
      (quotientAt H α).eval (domain i) := by
  rw [eval_quotientAt hα, hag, hz]
  field_simp
  ring

/-- Rank-one remainder form of the same transfer.  If every family member has
the decomposition `H = A * P + λ * R`, then agreement with a fixed word becomes
an affine line after pointwise division by `A`. -/
theorem rankOneRemainder_agrees
    {A P R H : Polynomial F} {lam x y : F}
    (hA : A.eval x ≠ 0)
    (hdecomp : H = A * P + Polynomial.C lam * R)
    (hag : H.eval x = y) :
    y / A.eval x + lam * (-R.eval x / A.eval x) = P.eval x := by
  rw [hdecomp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C] at hag
  field_simp [hA]
  rw [← hag]
  ring

/-! The exact benchmark-scale union bound. -/

def targetListSize : ℕ := 274980728111395088

theorem benchmark_field_card :
    Fintype.card ProximityPrize.Benchmark.IRSProfile.Field =
      93571093019388561295270373781649880353786165192103559169 := by
  change Fintype.card KoalaBear.Ext6 = _
  rw [KoalaBear.card_ext6]
  norm_num [KoalaBear.fieldSize]

theorem targetListSize_eq_threshold :
    targetListSize =
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field / 2 ^ 128 + 1 := by
  rw [benchmark_field_card]
  norm_num [targetListSize]

set_option maxRecDepth 100000 in
theorem benchmark_ordered_collision_count :
    262144 + targetListSize * (targetListSize - 1) * 131072 <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
  rw [benchmark_field_card]
  norm_num [targetListSize]

set_option maxRecDepth 100000 in
theorem benchmark_unordered_collision_count :
    262144 + Nat.choose targetListSize 2 * 131072 <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
  rw [benchmark_field_card, Nat.choose_two_right]
  norm_num [targetListSize]

theorem target_density_gt_epsilon :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      (targetListSize : ℝ≥0) /
        (Fintype.card ProximityPrize.Benchmark.IRSProfile.Field : ℝ≥0) := by
  unfold ProximityPrize.Benchmark.Upper.epsilonStar ProximityGap.prizeThreshold
  push_cast
  change (1 : ℝ≥0) / 2 ^ (128 : ℕ) <
    (targetListSize : ℝ≥0) /
      (Fintype.card ProximityPrize.Benchmark.IRSProfile.Field : ℝ≥0)
  rw [div_lt_div_iff₀ (by positivity) (by exact_mod_cast Fintype.card_pos)]
  rw [benchmark_field_card]
  norm_num [targetListSize]

namespace IRS

open Polynomial
open ToyProblem.Impl.IRS
open ProximityPrize.Benchmark

abbrev FF := IRSProfile.Field
abbrev Idx := IRSProfile.Index
abbrev kk := IRSProfile.totalDimension
abbrev ss := IRSProfile.interleaving
abbrev rowK : ℕ := 131072

local instance : NeZero ss := ⟨by norm_num [ss, IRSProfile.interleaving]⟩

theorem rowDimension_eq : kk / ss = rowK :=
  IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [rowK, IRSProfile.baseDimension])

def rowZeroWord (h : Idx → FF) : Idx → Fin ss → FF :=
  fun j row ↦ if row = 0 then h j else 0

/-- Every quotient polynomial of degree below `rowK` has a corresponding
interleaved message supported in row zero. -/
theorem exists_message (c : Polynomial FF) (hdeg : c.degree < (rowK : ℕ)) :
    ∃ u : Fin kk → FF, ∀ j : Idx,
      IRSProfile.encoder u j = rowZeroWord (fun i ↦ c.eval (IRSProfile.domain i)) j := by
  classical
  have hdeg' : c.degree < (kk / ss : ℕ) := by rwa [rowDimension_eq]
  have hpmem : c ∈ Polynomial.degreeLT FF (kk / ss) :=
    Polynomial.mem_degreeLT.mpr hdeg'
  let coeff : Fin (kk / ss) → FF :=
    Polynomial.degreeLTEquiv FF (kk / ss) ⟨c, hpmem⟩
  let rows : Fin ss → Fin (kk / ss) → FF :=
    fun row ↦ if row = 0 then coeff else 0
  let u : Fin kk → FF :=
    flatten kk ss IRSProfile.interleaving_dvd_totalDimension rows
  have hpoly : ToyProblem.Spec.rsPolynomial (kk / ss) coeff = c := by
    exact congrArg Subtype.val
      ((Polynomial.degreeLTEquiv FF (kk / ss)).symm_apply_apply ⟨c, hpmem⟩)
  refine ⟨u, ?_⟩
  intro j
  funext row
  rw [IRSProfile.encoder, encoder_apply]
  change ToyProblem.Spec.rsEncoder (kk / ss) IRSProfile.domain
      (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension
        (flatten kk ss IRSProfile.interleaving_dvd_totalDimension rows) row) j = _
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows 0 = coeff by simp [rows], ToyProblem.Spec.rsEncoder_apply, hpoly]
    simp [rowZeroWord]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (kk / ss) IRSProfile.domain)) j
    simp only [rows, hrow, if_false]
    simpa [rowZeroWord, hrow] using hz

def inverseWord (α : FF) : Idx → Fin ss → FF :=
  rowZeroWord (fun j ↦ -1 / (IRSProfile.domain j - α))

def quotientCenterWord (c : Idx → FF) (α : FF) : Idx → Fin ss → FF :=
  rowZeroWord (fun j ↦ c j / (IRSProfile.domain j - α))

/-- The reciprocal direction is farther than every radius whose required
agreement is strictly above the row dimension. -/
theorem inverseWord_far (α : FF) (hα : ∀ j : Idx, IRSProfile.domain j ≠ α)
    (u : Fin kk → FF) (S : Finset Idx) (hcard : rowK < S.card)
    (hagree : ∀ j ∈ S, inverseWord α j = IRSProfile.encoder u j) : False := by
  classical
  let q : Polynomial FF := ToyProblem.Spec.rsPolynomial (kk / ss)
    (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (rowK : ℕ) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (kk / ss)
      (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hqnat : q.natDegree < rowK := by
    by_cases hqzero : q = 0
    · simp [hqzero, rowK]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  let witness : Polynomial FF :=
    (Polynomial.X - Polynomial.C α) * q + 1
  have hwitness_natDegree : witness.natDegree ≤ rowK := by
    have hmul : ((Polynomial.X - Polynomial.C α) * q).natDegree ≤
        (Polynomial.X - Polynomial.C α).natDegree + q.natDegree :=
      Polynomial.natDegree_mul_le
    have hadd := Polynomial.natDegree_add_le
      ((Polynomial.X - Polynomial.C α) * q) 1
    rw [Polynomial.natDegree_X_sub_C] at hmul
    dsimp only [witness]
    calc
      (((Polynomial.X - Polynomial.C α) * q) + 1).natDegree ≤
          ((Polynomial.X - Polynomial.C α) * q).natDegree := by
        simpa using hadd
      _ ≤ rowK := by omega
  have hwitness_ne : witness ≠ 0 := by
    intro hzero
    have h := congrArg (Polynomial.eval α) hzero
    simp [witness] at h
  have heval : ∀ j ∈ S, witness.eval (IRSProfile.domain j) = 0 := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin ss)
    rw [inverseWord, rowZeroWord] at h
    simp only [if_pos] at h
    rw [IRSProfile.encoder, encoder_apply, ToyProblem.Spec.rsEncoder_apply] at h
    change -1 / (IRSProfile.domain j - α) = q.eval (IRSProfile.domain j) at h
    dsimp only [witness]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, ← h]
    field_simp [hα j]
    rw [div_self (sub_ne_zero.mpr (hα j))]
    ring
  apply hwitness_ne
  let nodes : Finset FF := S.image IRSProfile.domain
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' witness nodes
  · intro x hx
    simp only [nodes, Finset.mem_image] at hx
    rcases hx with ⟨j, hj, rfl⟩
    exact heval j hj
  · have hnodes : nodes.card = S.card := by
      dsimp only [nodes]
      exact Finset.card_image_of_injective S IRSProfile.domain.injective
    rw [hnodes]
    exact hwitness_natDegree.trans_lt hcard

end IRS

/-- A fixed affine word line with distinct close points directly lower-bounds the
winning-set density.  The second direction being far supplies the violating
two-row instance, so no auxiliary collision functional is needed. -/
theorem winningSetDensity_ge_of_injective_close_line
    [Fintype F] [DecidableEq F]
    {ι B : Type} [Fintype ι] [Fintype B] [DecidableEq B]
    [AddCommGroup B] [Module F B]
    {k m : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → B)) (δ : ℝ≥0)
    (hupper : (1 - (δ : ℝ)) * Fintype.card ι ≤ (m : ℝ))
    {J : Type} [Fintype J] [DecidableEq J]
    (z : J → F) (p : J → Fin k → F) (T : J → Finset ι)
    (f g : ι → B) (hz : Function.Injective z)
    (hTcard : ∀ a, (T a).card = m)
    (hag : ∀ a i, i ∈ T a → f i + z a • g i = enc (p a) i)
    (hfar : ∀ (u : Fin k → F) (S : Finset ι),
      (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card →
      (∀ i ∈ S, g i = enc u i) → False) :
    (Fintype.card J : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
      winningSetDensity enc δ := by
  classical
  let x : ViolatingInstance enc δ :=
    { v := 0
      μ₁ := 0
      μ₂ := 0
      f₁ := f
      f₂ := g
      violates := by
        rintro ⟨W, ⟨M, hW, _hconstraint⟩, S, hS, hA⟩
        apply hfar (M 1) S hS
        intro i hi
        have h := hA 1 i hi
        rw [hW 1] at h
        simpa using h }
  let zs : Finset F := Finset.univ.image z
  have hZcard : zs.card = Fintype.card J := by
    simp only [zs, Finset.card_image_of_injective Finset.univ hz, Finset.card_univ]
  have hZsub : (zs : Set F) ⊆ winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ := by
    intro γ hγ
    have hγ' : γ ∈ zs := hγ
    simp only [zs, Finset.mem_image, Finset.mem_univ, true_and] at hγ'
    rcases hγ' with ⟨a, rfl⟩
    simp only [winningSetFor, Set.mem_setOf_eq]
    refine ⟨![enc (p a)], ?_, T a, ?_, ?_⟩
    · refine ⟨![p a], ?_, ?_⟩
      · intro row
        fin_cases row
        rfl
      · intro row
        fin_cases row
        simp [x]
    · rw [hTcard]
      exact hupper
    · intro row i hi
      fin_cases row
      simpa [x] using hag a i hi
  have hZle : zs.card ≤
      (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard := by
    rw [← Set.ncard_coe_finset zs]
    exact Set.ncard_le_ncard hZsub (Set.toFinite _)
  refine le_trans ?_ (winningSetRatio_le_winningSetDensity x)
  rw [winningSetRatio, ← hZcard]
  have hZle' : (zs.card : ℝ≥0) ≤
      ((winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) := by
    exact_mod_cast hZle
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).mpr hZle'

namespace IRS

open ProximityPrize.Benchmark

local instance : NeZero ss := ⟨by norm_num [ss, IRSProfile.interleaving]⟩

/-- Exact fixed-domain large-list-to-upper bridge for the benchmark encoder.
The input family consists of distinct degree-at-most-`rowK` polynomials that
all agree with one fixed scalar word on `mAgree` benchmark-domain points. -/
theorem winningSetDensity_ge_of_fixed_domain_list
    {J : Type} [Fintype J] [DecidableEq J]
    (H : J → Polynomial FF) (T : J → Finset Idx) (center : Idx → FF)
    (mAgree : ℕ) (δ : ℝ≥0)
    (hH : Function.Injective H)
    (hdegree : ∀ j, (H j).natDegree ≤ rowK)
    (hTcard : ∀ j, (T j).card = mAgree)
    (hag : ∀ j i, i ∈ T j → (H j).eval (IRSProfile.domain i) = center i)
    (hcount : 262144 + Fintype.card J * (Fintype.card J - 1) * rowK <
      Fintype.card FF)
    (hthreshold : (rowK : ℝ) < (1 - (δ : ℝ)) * Fintype.card Idx)
    (hupper : (1 - (δ : ℝ)) * Fintype.card Idx ≤ (mAgree : ℝ)) :
    (Fintype.card J : ℝ≥0) / (Fintype.card FF : ℝ≥0) ≤
      winningSetDensity IRSProfile.encoder δ := by
  classical
  let domainSet : Finset FF := Finset.univ.image IRSProfile.domain
  have hdomainCard : domainSet.card = 262144 := by
    dsimp only [domainSet]
    rw [Finset.card_image_of_injective Finset.univ IRSProfile.domain.injective,
      Finset.card_univ]
    norm_num [Idx, IRSProfile.Index]
  obtain ⟨α, hαdomain, hz⟩ := exists_eval_injective_off_domain
    domainSet H rowK hH hdegree (by simpa only [hdomainCard] using hcount)
  have hα : ∀ i : Idx, IRSProfile.domain i ≠ α := by
    intro i heq
    apply hαdomain
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  have hquotDegreeNat (j : J) : (quotientAt (H j) α).natDegree < rowK :=
    quotientAt_natDegree_lt (by norm_num [rowK]) (hdegree j)
  have hquotDegree (j : J) : (quotientAt (H j) α).degree < (rowK : ℕ) := by
    by_cases hzero : quotientAt (H j) α = 0
    · rw [hzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp (hquotDegreeNat j)
  have hexMessage (j : J) : ∃ u : Fin kk → FF, ∀ i : Idx,
      IRSProfile.encoder u i =
        rowZeroWord (fun x ↦ (quotientAt (H j) α).eval (IRSProfile.domain x)) i :=
    exists_message (quotientAt (H j) α) (hquotDegree j)
  choose p hp using hexMessage
  have hagLine : ∀ j i, i ∈ T j →
      quotientCenterWord center α i + (H j).eval α • inverseWord α i =
        IRSProfile.encoder (p j) i := by
    intro j i hi
    rw [hp j i]
    funext row
    by_cases hrow : row = 0
    · subst row
      have hscalar := quotientAt_agrees_on_close_points IRSProfile.domain center
        (H := H j) (i := i) (hα i) rfl (hag j i hi)
      simpa [quotientCenterWord, inverseWord, rowZeroWord] using hscalar
    · simp [quotientCenterWord, inverseWord, rowZeroWord, hrow]
  refine winningSetDensity_ge_of_injective_close_line IRSProfile.encoder δ hupper
    (fun j ↦ (H j).eval α) p T (quotientCenterWord center α) (inverseWord α)
    hz hTcard hagLine ?_
  intro u S hS hagree
  have hcardReal : (rowK : ℝ) < (S.card : ℝ) := hthreshold.trans_le hS
  have hcard : rowK < S.card := by exact_mod_cast hcardReal
  exact inverseWord_far α hα u S hcard hagree

/-- Benchmark-ready corollary: a fixed-domain list of exactly the first integer
above `|FF| / 2^128` already makes the winning density exceed the prize target. -/
theorem epsilon_lt_winningSetDensity_of_target_list
    {J : Type} [Fintype J] [DecidableEq J]
    (H : J → Polynomial FF) (T : J → Finset Idx) (center : Idx → FF)
    (mAgree : ℕ) (δ : ℝ≥0)
    (hJcard : Fintype.card J = targetListSize)
    (hH : Function.Injective H)
    (hdegree : ∀ j, (H j).natDegree ≤ rowK)
    (hTcard : ∀ j, (T j).card = mAgree)
    (hag : ∀ j i, i ∈ T j → (H j).eval (IRSProfile.domain i) = center i)
    (hthreshold : (rowK : ℝ) < (1 - (δ : ℝ)) * Fintype.card Idx)
    (hupper : (1 - (δ : ℝ)) * Fintype.card Idx ≤ (mAgree : ℝ)) :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      winningSetDensity IRSProfile.encoder δ := by
  have hcount : 262144 + Fintype.card J * (Fintype.card J - 1) * rowK <
      Fintype.card FF := by
    rw [hJcard]
    exact benchmark_ordered_collision_count
  have hge := winningSetDensity_ge_of_fixed_domain_list H T center mAgree δ hH
    hdegree hTcard hag hcount hthreshold hupper
  calc
    ProximityPrize.Benchmark.Upper.epsilonStar <
        (targetListSize : ℝ≥0) / (Fintype.card FF : ℝ≥0) :=
      target_density_gt_epsilon
    _ = (Fintype.card J : ℝ≥0) / (Fintype.card FF : ℝ≥0) := by rw [hJcard]
    _ ≤ winningSetDensity IRSProfile.encoder δ := hge

end IRS

end ProximityPrize.SubmissionUpper.FixedDomainBridge
