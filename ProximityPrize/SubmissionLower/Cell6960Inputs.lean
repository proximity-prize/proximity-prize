import ProximityPrize.SubmissionLower.PortFoundation
import ProximityPrize.SubmissionLower.Cell82Intermediate

set_option Elab.async false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false

namespace Cell6960Inputs

noncomputable section
open Code LinearCode CoreDefinitions ToyProblem FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount (squaredCode A16)
open Sol1.FiniteRowProjection (agreementCard)
open scoped NNReal
open private score_ratio_iff from ProximityPrize.SubmissionLower.Cell82Intermediate

inductive Target | s55 | s56 | s57 | s58 | s59 | s60

def score : Target → ℕ
  | .s55 => 6955
  | .s56 => 6956
  | .s57 => 6957
  | .s58 => 6958
  | .s59 => 6959
  | .s60 => 6960

def errors : Target → ℕ
  | .s55 => 82268
  | .s56 => 82278
  | .s57 => 82287
  | .s58 => 82297
  | .s59 => 82307
  | .s60 => 82317

def agreement (t : Target) := 262144 - errors t
def numerator (t : Target) := (errors t + 1) * 4096 - 1
abbrev denominator : ℕ := 1073741824
def radius (t : Target) : ℝ≥0 := claimedRadius (numerator t) denominator

theorem radius_admissible (t : Target) :
    radius t ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  cases t <;> norm_num [radius, numerator, errors, claimedRadius, IRSProfile.minRelativeDistance]

theorem radius_score (t : Target) :
    (1 - radius t)^IRSProfile.repetitions ≤ claimedError (score t) := by
  apply (score_ratio_iff _ _ _ (by decide) (by cases t <;> decide)).mpr
  cases t <;> decide +kernel

abbrev I := P0.I
abbrev K := P0.K
abbrev Words := P0.Words
abbrev node := P0.node
abbrev k := P0.k

def realRadius (t : Target) : ℝ := radius t
def BadFamily (t : Target) (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u (realRadius t)

theorem agreement_of_threshold (t : Target) {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1-realRadius t) ≤ s) : agreement t ≤ s := by
  rw [IRSProfile.card_index] at hs
  have p : ((agreement t - 1 : ℕ) : ℝ) < 262144*(1-realRadius t) := by
    cases t <;> norm_num [realRadius, radius, claimedRadius, numerator, errors, agreement]
  have h : agreement t - 1 < s := by exact_mod_cast p.trans_le hs
  omega

variable {t : Target}

theorem close_agreement_ge (t : Target) (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ realRadius t) : agreement t ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : realRadius t =
      1 - ((Fintype.card I : ℝ) * (1 - realRadius t)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - realRadius t)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold t hagree).trans hcard
def nativeBadSlopes (t : Target) (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U (realRadius t)

end
end Cell6960Inputs
