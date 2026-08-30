import ProximityPrize.SubmissionLower.AlignmentMomentCurveProjection

namespace ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section DraftProofs

section RadiusCell

variable {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [DecidableEq A]

omit [DecidableEq ι] in
theorem agreement_card_ge_of_closeCodewordsRel
    (C : Set (ι → A)) (y c : ι → A) (δ : ℝ) (e : ℕ)
    (hcell : δ * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ))
    (hc : c ∈ Code.closeCodewordsRel C y δ) :
    Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => c i = y i)).card := by
  classical
  have hball := (Code.mem_closeCodewordsRel_iff.mp hc).2
  simp only [Code.relHammingDist_coe] at hball
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdistR : (hammingDist y c : ℝ) < ((e + 1 : ℕ) : ℝ) :=
    ((div_le_iff₀ hn).mp hball).trans_lt hcell
  have hdist : hammingDist y c ≤ e := by
    have hlt : hammingDist y c < e + 1 := by exact_mod_cast hdistR
    omega
  have hagree : Code.agree c y + hammingDist y c = Fintype.card ι := by
    rw [hammingDist_comm]
    exact Code.agree_add_hammingDist (u := c) (v := y)
  change Fintype.card ι - e ≤ Code.agree c y
  omega

end RadiusCell

section GenericCode

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

def sixteenIndexEquiv : Fin 2 × Fin 8 ≃ Fin 16 := finProdFinEquiv

def flattenSymbol (v : Fin 2 → Fin 8 → F) (j : Fin 16) : F :=
  v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2

def unflattenSymbol (v : Fin 16 → F) (a : Fin 2) (b : Fin 8) : F :=
  v (sixteenIndexEquiv (a, b))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem unflatten_flattenSymbol (v : Fin 2 → Fin 8 → F) :
    unflattenSymbol (flattenSymbol v) = v := by
  funext a b
  simp only [unflattenSymbol, flattenSymbol, Equiv.symm_apply_apply]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem flatten_unflattenSymbol (v : Fin 16 → F) :
    flattenSymbol (unflattenSymbol v) = v := by
  funext j
  change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j)) = v j
  rw [Equiv.apply_symm_apply]

def squaredEightSymbolEquiv : (Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
  toFun := flattenSymbol
  invFun := unflattenSymbol
  left_inv := unflatten_flattenSymbol
  right_inv := flatten_unflattenSymbol

def flattenWord (v : ι → Fin 2 → Fin 8 → F) : ι → Fin 16 → F :=
  fun i => squaredEightSymbolEquiv (v i)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
omit [Field F] [Fintype F] [DecidableEq F] in
theorem flattenWord_injective :
    Function.Injective (flattenWord : (ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F) := by
  intro v u h
  funext i
  exact squaredEightSymbolEquiv.injective (congrFun h i)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
omit [Field F] [Fintype F] [DecidableEq F] in
theorem flattenWord_agreement_iff
    (v u : ι → Fin 2 → Fin 8 → F) (i : ι) :
    flattenWord v i = flattenWord u i ↔ v i = u i := by
  constructor
  · intro hh
    change (squaredEightSymbolEquiv (F := F)) (v i) =
      (squaredEightSymbolEquiv (F := F)) (u i) at hh
    exact (squaredEightSymbolEquiv (F := F)).injective hh
  · intro hh
    change (squaredEightSymbolEquiv (F := F)) (v i) =
      (squaredEightSymbolEquiv (F := F)) (u i)
    exact congrArg (squaredEightSymbolEquiv (F := F)) hh

omit [Nonempty ι] [DecidableEq ι] in
omit [Field F] [Fintype F] in
theorem flattenWord_agreement_card (v u : ι → Fin 2 → Fin 8 → F) :
    (Finset.univ.filter (fun i => flattenWord v i = flattenWord u i)).card =
      (Finset.univ.filter (fun i => v i = u i)).card := by
  classical
  congr 1
  ext i
  simp only [Finset.mem_filter, flattenWord_agreement_iff]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
theorem squared_eight_rows
    (C : LinearCode ι F) (v : ι → Fin 2 → Fin 8 → F)
    (hv : v ∈ ((C ^⋈ (Fin 8)) ^⋈ (Fin 2) :
      ModuleCode ι F (Fin 2 → Fin 8 → F))) :
    ∀ a : Fin 2, ∀ b : Fin 8, (fun i => v i a b) ∈ C := by
  intro a b
  have houter :=
    (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
      (C ^⋈ (Fin 8)) v).mp hv a
  exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b

end GenericCode

theorem irs_code_mem_iff_rows
    (v : IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field) :
    v ∈ IRSProfile.code ↔
      ∀ b : Fin IRSProfile.interleaving, (fun i => v i b) ∈ IRSProfile.baseCode := by
  change (∀ b : Fin IRSProfile.interleaving,
    (fun i => v i b) ∈ ReedSolomon.code IRSProfile.domain
      (IRSProfile.totalDimension / IRSProfile.interleaving)) ↔ _
  rw [IRSProfile.totalDimension_div_interleaving]
  rfl

theorem irs_squared_carrier_eq :
    (((IRSProfile.code ^⋈ (Fin 2) :
      ModuleCode IRSProfile.Index IRSProfile.Field
        (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
      Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))) =
    ((((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
      ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)) :
      Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))) := by
  ext v
  change (∀ a : Fin 2, (fun i => v i a) ∈ IRSProfile.code) ↔
    ∀ a : Fin 2, ∀ b : Fin 8, (fun i => v i a b) ∈ IRSProfile.baseCode
  constructor
  · intro hv a b
    exact (irs_code_mem_iff_rows _).mp (hv a) b
  · intro hv a
    exact (irs_code_mem_iff_rows _).mpr (hv a)

end DraftProofs

end ProximityPrize.SubmissionLower.AlignmentInterleavedLambda
