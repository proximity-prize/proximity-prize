/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Inertia
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Ramification
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Ideal_Norm_AbsNorm

/-!
Permitted flat proof port of Mathlib.NumberTheory.RamificationInertia.Basic.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: e69ad497b25828fac8c3379b12513fde24f2a6fd34cc181689d1fe52c572a715.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .






























 -/

section ProximityFlatProofPort


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section FinrankQuotientMap

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [Algebra R K]
variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]
variable {V V' V'' : Type*}
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']
variable [AddCommGroup V''] [Module R V'']
variable (K)

open scoped Matrix

variable {K} in
/-- .








 -/
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [Module.Finite R S]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Algebra.IsAlgebraic R S]
    [IsTorsionFree R K] (hp : p ≠ ⊤) (b : Set S)
    (hb' : Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective R K)
  --
  let M : Submodule R S := Submodule.span R b
  --
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin R (S ⧸ M) _ _ _ _
  --
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkQ (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkQ]
      _ = ⊤ := by rw [Ideal.smul_top_eq_map, (Submodule.map_mkQ_eq_top M _).mpr hb']
  --
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x := by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1
      (by { rw [ha, smul_top_eq]; exact Submodule.mem_top } :
        x ∈ p • Submodule.span R (Set.range a))
    · refine ⟨fun i => a'' i, fun i => ha'' _, ?_⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
  choose A' hA'p hA' using fun i => exists_sum (a i)
  --
  let A : Matrix (Fin n) (Fin n) R := Matrix.of A' - 1
  let B := A.adjugate
  have A_smul : ∀ i, ∑ j, A i j • a j = 0 := by
    intros
    simp [A, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, sub_smul,
      Finset.sum_sub_distrib, hA', sub_self]
  --
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B * A) i j • a j := ?_
      _ = ∑ k, B i k • ∑ j, A k j • a j := ?_
      _ = 0 := Finset.sum_eq_zero fun k _ => ?_
    · simp only [B, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    · rw [A_smul, smul_zero]
  --
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx ⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    rw [← quot_x_eq, Finset.smul_sum]
    conv =>
      lhs; congr; next => skip
      intro x; rw [smul_comm A.det, d_smul, smul_zero]
    exact Finset.sum_const_zero
  refine top_le_iff.mp
      (calc
        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := ?_
        _ ≤ Submodule.span K (algebraMap S L '' b) := ?_)
  --
  · rw [eq_comm, Submodule.restrictScalars_eq_top_iff, Ideal.span_singleton_eq_top]
    refine IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr ?_)
    refine ne_zero_of_map («f» := Ideal.Quotient.mk p) ?_
    have := Ideal.Quotient.nontrivial_iff.mpr hp
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (Matrix.of A' - 1)) := rfl
      _ = Matrix.det fun i j =>
          (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Fin n) (Fin n) (R ⧸ p)) i j := ?_
      _ = Matrix.det (-1 : Matrix (Fin n) (Fin n) (R ⧸ p)) := ?_
      _ = (-1 : R ⧸ p) ^ n := by rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      _ ≠ 0 := IsUnit.ne_zero (isUnit_one.neg.pow _)
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [map_sub, RingHom.mapMatrix_apply, map_one]
      simp
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub, Matrix.neg_apply]
  --
  · intro x hx
    rw [Submodule.restrictScalars_mem, IsScalarTower.algebraMap_apply R S L] at hx
    exact IsFractionRing.ideal_span_singleton_map_subset R hRL span_d hx

variable [hRK : IsFractionRing R K]

/-- .






 -/
theorem FinrankQuotientMap.linearIndependent_of_nontrivial [IsDedekindDomain R]
    (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (F : V'' →ₗ[R] V) (hf : Function.Injective F)
    (f' : V'' →ₗ[R] V') {ι : Type*} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (F ∘ b) := by
  contrapose hb' with hb
  --
  --
  --
  --
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
  choose g'' hg'' using hag
  letI := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  --
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  have eq : F (∑ i ∈ s, g' i • b i) = 0 := by
    rw [map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← map_smul, ← map_sum,
    (F.map_eq_zero_iff hf).mp eq, map_zero, (· ∘ ·)]

variable (L)

/-- .
 -/
theorem finrank_quotient_map [IsDomain S] [IsDedekindDomain R] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [hp : p.IsMaximal] [Module.Finite R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L := by
  --
  --
  let ι := Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  let b : Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p) := Module.Free.chooseBasis _ _
  --
  let b' : ι → S := fun i => (Ideal.Quotient.mk_surjective (b i)).choose
  have b_eq_b' : ⇑b = (Submodule.mkQ (map (algebraMap R S) p)).restrictScalars R ∘ b' :=
    funext fun i => (Ideal.Quotient.mk_surjective (b i)).choose_spec.symm
  --
  --
  let b'' : ι → L := algebraMap S L ∘ b'
  have b''_li : LinearIndependent K b'' := ?_
  · have b''_sp : Submodule.span K (Set.range b'') = ⊤ := ?_
    --
    · let c : Basis ι K L := Basis.mk b''_li b''_sp.ge
      rw [finrank_eq_card_basis b, finrank_eq_card_basis c]
    --
    · rw [Set.range_comp]
      refine FinrankQuotientMap.span_eq_top p hp.ne_top _ (top_le_iff.mp ?_)
      --
      --
      --
      --
      intro x _
      have mem_span_b : ((Submodule.mkQ (map (algebraMap R S) p)) x : S ⧸ map (algebraMap R S) p) ∈
          Submodule.span (R ⧸ p) (Set.range b) := b.mem_span _
      rw [← @Submodule.restrictScalars_mem R,
        Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective, b_eq_b',
        Set.range_comp, ← Submodule.map_span] at mem_span_b
      obtain ⟨y, y_mem, y_eq⟩ := Submodule.mem_map.mp mem_span_b
      suffices y + -(y - x) ∈ _ by simpa
      rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at y_eq
      exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
  · have := b.linearIndependent; rw [b_eq_b'] at this
    convert!
      FinrankQuotientMap.linearIndependent_of_nontrivial K _
        ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkQ _).restrictScalars R) this
    · rw [Quotient.algebraMap_eq, Ideal.mk_ker]
      exact hp.ne_top
    · exact IsFractionRing.injective S L

end FinrankQuotientMap

section FactLeComap

local notation "e" => ramificationIdx' p P

/-- .
 -/
noncomputable instance Quotient.algebraQuotientPowRamificationIdx : Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx')

@[simp]
theorem Quotient.algebraMap_quotient_pow_ramificationIdx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk (P ^ e) (f x) := rfl

/-- .


 -/
@[instance_reducible]
def Quotient.algebraQuotientOfRamificationIdxNeZero [hfp : NeZero e] :
    Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLEComap (le_comap_of_ramificationIdx'_ne_zero hfp.out)

attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem Quotient.algebraMap_quotient_of_ramificationIdx_neZero
    [NeZero e] (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (f x) := rfl

/-- . -/
@[simps]
noncomputable def powQuotSuccInclusion (i : ℕ) :
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)) →ₗ[R ⧸ p]
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where
  toFun x := ⟨x, Ideal.map_mono (Ideal.pow_le_pow_right i.le_succ) x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem powQuotSuccInclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion p P i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ hx0
  rw [Subtype.ext_iff] at hx0 ⊢
  rwa [powQuotSuccInclusion_apply_coe] at hx0

/-- .


 -/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) :=
  Quotient.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩)
    fun x y h => by
    rw [Submodule.quotientRel_def] at h ⊢
    simp only [map_mul, LinearMap.mem_range]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul a_mem h)⟩, ?_⟩
    ext
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk,
      Subtype.coe_mk, map_mul, map_sub, mul_sub]

theorem quotientToQuotientRangePowQuotSuccAux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ := by
  apply Quotient.map'_mk''

section
variable [hfp : NeZero (ramificationIdx' p P)]

/-- . -/
noncomputable def quotientToQuotientRangePowQuotSucc
    {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p]
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) where
  toFun := quotientToQuotientRangePowQuotSuccAux p P a_mem
  map_add' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      quotientToQuotientRangePowQuotSuccAux_mk, mul_add, map_add, map_mul, AddMemClass.mk_add_mk]
  map_smul' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, RingHom.id_apply,
      quotientToQuotientRangePowQuotSuccAux_mk]
    refine congr_arg Submodule.Quotient.mk ?_
    ext
    simp only [map_mul, Quotient.mk_eq_mk, Submodule.coe_smul_of_tower,
      Algebra.smul_def, Quotient.algebraMap_quotient_pow_ramificationIdx]
    ring

theorem quotientToQuotientRangePowQuotSucc_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ :=
  quotientToQuotientRangePowQuotSuccAux_mk p P a_mem x

theorem quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPrime]
    {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem) := fun x =>
  Quotient.inductionOn' x fun x y =>
    Quotient.inductionOn' y fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow_right hi
      simp only [Submodule.Quotient.mk''_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
        Submodule.coe_sub] at h ⊢
      rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩
      rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
        sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.Quotient.quot_mk_eq_mk,
        Ideal.Quotient.mk_eq_mk, ← map_sub, Ideal.Quotient.eq, ← mul_sub] at h
      exact
        (Ideal.IsPrime.mem_pow_mul _
              ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_left
          a_notMem

theorem quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S]
    (hP0 : P ≠ ⊥) [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow_right hi.le
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a} ⊔ P ^ (i + 1) by
    obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
      Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
      Submodule.coe_sub]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, ?_⟩
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add,
      sub_add_cancel_left, map_neg]
  rw [← Submodule.span_singleton_le_iff_mem, submodule_span_eq] at a_mem a_notMem
  have hspan0 : span {a} ≠ ⊥ := fun ha ↦ a_notMem (ha ▸ bot_le)
  rwa [sup_comm, irreducible_pow_sup hspan0 ((prime_iff_isPrime hP0).mpr hP).irreducible,
    count_normalizedFactors_eq a_mem a_notMem, min_eq_left i.le_succ]

/-- .
 -/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S]
    [P.IsPrime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i))
      ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_notMem using
    SetLike.exists_of_lt
      (Ideal.pow_right_strictAnti P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  refine (LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩).symm
  · exact quotientToQuotientRangePowQuotSucc p P a_mem
  · exact quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem
  · exact quotientToQuotientRangePowQuotSucc_surjective p P hP hi a_mem a_notMem

/-- .
 -/
theorem rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    {i : ℕ} (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) +
        Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1))) := by
  rw [← rank_range_of_injective _ (powQuotSuccInclusion_injective p P i),
    (quotientRangePowQuotSuccInclusionEquiv p P hP0 hi).symm.rank_eq]
  exact (Submodule.rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion p P i))).symm

theorem rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
  let Q : ℕ → Prop :=
    fun i => Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ i) }
      = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
  refine Nat.decreasingInduction' (P := Q) (fun j lt_e _le_j ih => ?_) hi ?_
  · dsimp only [Q]
    rw [rank_pow_quot_aux p P _ lt_e, ih, ← succ_nsmul', Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
    assumption
  · dsimp only [Q]
    rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    exact rank_bot (R ⧸ p) (S ⧸ P ^ e)

end

/-- .
 -/
theorem rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
    (hP0 : P ≠ ⊥) (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  have := rank_pow_quot p P hP0 0 (Nat.zero_le e)
  rw [pow_zero, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  exact (rank_top (R ⧸ p) _).symm.trans this

/-- .
 -/
theorem finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [p.IsMaximal] [P.IsPrime] (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfRamificationIdxNeZero p P
  have hdim := rank_prime_pow_ramificationIdx _ _ hP0 he
  by_cases hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  · have := (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    apply @Nat.cast_injective Cardinal
    rw [finrank_eq_rank', Nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul]
  have hPe := mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe,
    mul_zero]

end FactLeComap

section FactorsMap

/-! . -/


variable [IsDedekindDomain S]

theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero

instance Factors.isPrime (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsPrime (P : Ideal S) :=
  Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))

theorem Factors.ramificationIdx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx' p P.1 ≠ 0 :=
  IsDedekindDomain.ramificationIdx'_ne_zero (ne_zero_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2)))

instance Factors.fact_ramificationIdx_neZero (P : (factors (map (algebraMap R S) p)).toFinset) :
    NeZero (ramificationIdx' p P.1) :=
  ⟨Factors.ramificationIdx_ne_zero p P⟩

attribute [local instance] Quotient.algebraQuotientOfRamificationIdxNeZero

instance Factors.isScalarTower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance Factors.liesOver [p.IsMaximal] (P : (factors (map (algebraMap R S) p)).toFinset) :
    P.1.LiesOver p :=
  ⟨(comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P.1)).injective).symm⟩

theorem Factors.finrank_pow_ramificationIdx [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) =
      ramificationIdx' p P.1 * inertiaDeg' p (P : Ideal S) := by
  rw [finrank_prime_pow_ramificationIdx, inertiaDeg'_algebraMap]
  exacts [Factors.ne_bot p P, NeZero.ne _]

instance Factors.finiteDimensional_quotient_pow [Module.Finite R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) := by
  refine .of_finrank_pos ?_
  rw [pos_iff_ne_zero, Factors.finrank_pow_ramificationIdx]
  exact mul_ne_zero (Factors.ramificationIdx_ne_zero p P) (inertiaDeg'_pos p P.1).ne'

universe w

/-- .
 -/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1 :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count (P : Ideal S))
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [IsDedekindDomain.ramificationIdx'_eq_factors_count hp (Factors.isPrime p P)
            (Factors.ne_bot p P)]

@[simp]
theorem Factors.piQuotientEquiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun _ => Ideal.Quotient.mk _ x := rfl

@[simp]
theorem Factors.piQuotientEquiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun _ =>
      Ideal.Quotient.mk _ (algebraMap _ _ x) := rfl

variable (S)

/-- .

 -/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1 :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩; ext P
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, Algebra.smul_def,
        Quotient.algebraMap_quotient_map_quotient, Quotient.mk_algebraMap,
        RingHomCompTriple.comp_apply, Pi.mul_apply, Pi.algebraMap_apply]
      congr }

variable (K L : Type*) [Field K] [Field L] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite R S]

/-- .


 -/
theorem sum_ramification_inertia {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
        ramificationIdx' p P * inertiaDeg' p P = finrank K L := by
  set e := ramificationIdx' p (S := S)
  calc
    ∑ P ∈ (factors (map (algebraMap R S) p)).toFinset, e P * inertiaDeg' p P =
        ∑ P ∈ (factors (map (algebraMap R S) p)).toFinset.attach,
          finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) := ?_
    _ = finrank (R ⧸ p)
          (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := ?_
    _ = finrank K L := ?_
  · rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Factors.finrank_pow_ramificationIdx]
  · refine LinearEquiv.finrank_eq (Factors.piQuotientLinearEquiv S p ?_).symm
    rwa [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp <|
      algebraMap_injective_of_field_isFractionRing R S K L, le_bot_iff]
  · exact finrank_quotient_map p K L

theorem inertiaDeg_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] (hp0 : p ≠ ⊥) :
    p.inertiaDeg' P ≤ Module.finrank K L := by
  classical
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁, hP₂⟩
  rw [← sum_ramification_inertia S K L hp0, ← Finset.add_sum_erase _ _ hP]
  refine le_trans (Nat.le_mul_of_pos_left _ ?_) (Nat.le_add_right _ _)
  exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0

theorem ramificationIdx_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] :
    p.ramificationIdx' P ≤ Module.finrank K L := by
  classical
  by_cases hp0 : p = ⊥
  · simp [hp0]
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁, hP₂⟩
  rw [← sum_ramification_inertia S K L hp0, ← Finset.add_sum_erase _ _ hP]
  refine le_trans (Nat.le_mul_of_pos_right _ ?_) (Nat.le_add_right _ _)
  exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P

theorem card_primesOverFinset_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (hp0 : p ≠ ⊥) : Finset.card (IsDedekindDomain.primesOverFinset p S) ≤ Module.finrank K L := by
  rw [← sum_ramification_inertia S K L hp0, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun P hP ↦ ?_
  have : P.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).1
  have : P.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).2
  refine Right.one_le_mul ?_ ?_
  · exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0
  · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P

/-- . -/
lemma ramificationIdx_mul_inertiaDeg_of_isLocalRing [IsLocalRing S] {p : Ideal R} [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    ramificationIdx' p (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg' (IsLocalRing.maximalIdeal S) = Module.finrank K L := by
  have := FaithfulSMul.of_field_isFractionRing R S K L
  simp_rw [← sum_ramification_inertia S K L hp0, IsLocalRing.primesOverFinset_eq S hp0,
    Finset.sum_singleton]

end FactorsMap

end Ideal
