import ProximityPrize.SubmissionBinaryLower.P64Resultant
import ProximityPrize.Benchmark.BinaryTargetLower
import ArkLib.Data.CodingTheory.JohnsonBound.Pairwise

/-!
# Radius, score and the list term at 64.00 (PROOF.md 1.1, 1.4)

`δ = 78622925 / 2^28`. Lemma J: the code interleaved twice has at most
`⌊n(A - D)/(A² - nD)⌋ = 235031` codewords within relative distance `δ` of any word, by ArkLib's
integral pairwise Johnson bound `Code.finset_card_le_pairwiseJohnson` (restated at radius `δ`,
whose Hamming ball is the ball of radius `614241 = ⌊δn⌋`). The affine-line bridge
`AffineLineGivenSetsBound` is copied from `BCHKSBridge.lean` lines 1-75 (63.99 submission).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64List

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open CoreDefinitions ProximityGap
open scoped NNReal ProbabilityTheory

/-- The radius `δ = 78622925 / 2^28`. -/
noncomputable def radius : ℝ≥0 := (78622925 : ℝ≥0) / 268435456

/-- The list bound of Lemma J. -/
def listBound : ℕ := 235031

/-- The MCA numerator: the whole remaining room. -/
def numerator : ℕ := 2 ^ 64 - 235031

/-- Score: `(1 - δ)^2 ≤ 1/2`, so `(1 - δ)^128 ≤ 2^-64`. -/
theorem radius_score : (1 - radius) ^ (128 : ℕ) ≤ claimedError 6400 := by
  have hsq : (1 - radius) ^ 2 ≤ (1 / 2 : ℝ≥0) := by
    have hr : radius ≤ 1 := by
      unfold radius
      rw [div_le_one (by norm_num)]
      norm_num
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hr]
    norm_num [radius]
  have hE : claimedError 6400 = (1 / 2 : ℝ≥0) ^ (64 : ℕ) := by
    unfold claimedError
    rw [show -(((6400 : ℕ) : ℝ) / 100) = ((-64 : ℤ) : ℝ) by norm_num, NNReal.rpow_intCast]
    norm_num
  rw [hE, show (128 : ℕ) = 2 * 64 from rfl, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hsq 64

/-- The code interleaved twice. -/
noncomputable abbrev SquaredCode :
    Set (BinaryIRSProfile.Index → Fin 2 → Fin BinaryIRSProfile.interleaving →
      BinaryIRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
      Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))

set_option maxRecDepth 20000 in
theorem squaredCode_minDist : Code.minDist SquaredCode = 1048577 := by
  calc
    Code.minDist SquaredCode =
        Code.minDist (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
          Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) :=
      Code.minDist_interleavedCodeSet (κ := Fin 2) _
    _ = 1048577 := BinaryIRSProfile.minDistance

/-- **Lemma J** at radius `δ`. -/
theorem lambda_le : Code.Lambda SquaredCode (radius : ℝ) ≤ (listBound : ℕ∞) := by
  have hn : Fintype.card BinaryIRSProfile.Index = 2097152 := BinaryIRSProfile.card_index
  have hbound : Code.pairwiseJohnsonListBound 2097152 1048575 1482911 = listBound := by
    norm_num [Code.pairwiseJohnsonListBound, listBound]
  rw [← hbound]
  apply Code.Lambda_le_of_forall_finset_card_le
  intro received T hT
  rw [← hn]
  apply Code.finset_card_le_pairwiseJohnson SquaredCode received 1048575 1482911 (by norm_num)
    (by rw [hn]; norm_num)
  · intro c hc c' hc' hne
    have hd := Code.minDist_le_dist hc hc' hne
    rw [squaredCode_minDist] at hd
    have hsum := Code.agree_add_hammingDist (u := c) (v := c')
    rw [hn] at hsum
    omega
  · intro c hc
    have hmem := Code.mem_closeCodewordsRel_iff.mp (hT c hc)
    refine ⟨hmem.1, ?_⟩
    have hdist := hmem.2
    rw [Code.relHammingDist_coe, hn] at hdist
    have hrad : ((radius : ℝ≥0) : ℝ) = 78622925 / 268435456 := by
      simp [radius]
    have hd : (hammingDist received c : ℝ) ≤ 78622925 / 128 := by
      rw [hrad] at hdist
      generalize (hammingDist received c : ℝ) = x at hdist ⊢
      push_cast at hdist
      rw [div_le_iff₀ (by norm_num)] at hdist
      linarith
    have hdN : hammingDist c received ≤ 614241 := by
      rw [hammingDist_comm]
      have : (hammingDist received c : ℝ) < 614242 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have hsum := Code.agree_add_hammingDist (u := c) (v := received)
    rw [hn] at hsum
    omega

/-- The chosen-agreement-set conclusion needed by the affine-line MCA argument. -/
def AffineLineGivenSetsBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (C : LinearCode ι F) (δ : ℝ) (a : ℕ) : Prop :=
  ∀ (U : Fin 2 → ι → F) (S : Finset F) (T : F → Finset ι),
    a < S.card →
    (∀ z ∈ S, (T z).card ≥ (Fintype.card ι : ℝ) * (1 - δ)) →
    (∀ z ∈ S,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (T z) ∈
        LinearCode.projectedCodeSubmod C (T z)) →
    ∃ z ∈ S, ∀ j : Fin 2,
      LinearCode.projectedWord (U j) (T z) ∈ LinearCode.projectedCodeSubmod C (T z)

/-- A chosen-agreement-set theorem with numerator `a` implies the corresponding MCA bound. -/
theorem mcaError_affineLine_le_of_givenSetsBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (C : LinearCode ι F) (δ : ℝ) (a : ℕ)
    (hgiven : AffineLineGivenSetsBound C δ a) :
    mcaError (AffineLineGenerator F) C δ ≤
      ENNReal.ofReal ((a : ℝ) / Fintype.card F) := by
  classical
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample,
    show ENNReal.ofReal ((a : ℝ) / Fintype.card F)
        = (a : ENNReal) / (Fintype.card F : ENNReal) from by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
  refine ENNReal.div_le_div_right ?_ _
  · exact_mod_cast (show
      (Finset.univ.filter (fun z : F =>
        IsMCA (AffineLineGenerator F) C z U δ)).card ≤ a by
      by_contra hnot
      have hlarge : a < (Finset.univ.filter (fun z : F =>
          IsMCA (AffineLineGenerator F) C z U δ)).card := by omega
      let S : Finset F := Finset.univ.filter (fun z : F =>
        IsMCA (AffineLineGenerator F) C z U δ)
      have hmem (z : F) (hz : z ∈ S) :
          IsMCA (AffineLineGenerator F) C z U δ := by
        simpa [S] using hz
      let T : F → Finset ι := fun z =>
        if hz : z ∈ S then Classical.choose (hmem z hz) else ∅
      have hTspec (z : F) (hz : z ∈ S) :
          (T z).card ≥ (Fintype.card ι : ℝ) * (1 - δ) ∧
          LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (T z) ∈
            LinearCode.projectedCodeSubmod C (T z) ∧
          ∃ j : Fin 2, LinearCode.projectedWord (U j) (T z) ∉
            LinearCode.projectedCodeSubmod C (T z) := by
        rcases Classical.choose_spec (hmem z hz) with ⟨hcard, hcomb, hbad⟩
        have hTz : T z = Classical.choose (hmem z hz) := by
          simp only [T, dif_pos hz]
        rw [hTz]
        refine ⟨hcard, ?_, hbad⟩
        simpa [AffineLineGenerator, Fin.sum_univ_two] using hcomb
      obtain ⟨z, hzS, hall⟩ := hgiven U S T (by simpa [S] using hlarge)
        (fun z hz => (hTspec z hz).1) (fun z hz => (hTspec z hz).2.1)
      obtain ⟨j, hj⟩ := (hTspec z hzS).2.2
      exact hj (hall j))

end P64List
end ProximityPrize.SubmissionBinaryLower
