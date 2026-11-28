import ProximityPrize.SubmissionLower.Z6969Pack0836

-- Source: ProximityPrize.SubmissionLower.Low6969RetainedCount
section Z6969Source2398
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969RetainedBank
section Merged_R6960Low6969RetainedBank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6969RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox atJet extend OrderAt embed indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low6969Prices (Messages SmallFactor ActiveFits primaryBox primaryCutoff layerWidth layerNeed
  TrueWeightLE LayerBudget)
open scoped Polynomial BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
def levelOrder (T : ℕ) : ℕ := (primaryCutoff-T)/layerWidth+1
structure Bank (Γ : Finset K) (s : K → (Polynomial K)) where
  row : ℕ → Row 4 → Prop
  bounds : ∀ T ≤ primaryCutoff, ∀ P, row T P →
    InBox (shape P) primaryBox ∧ TrueWeightLE P primaryCutoff ∧ ActiveFits P 5192
  order : ∀ T ≤ primaryCutoff, ∀ P, row T P → ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (levelOrder T)
variable {Γ : Finset K} {s : K → (Polynomial K)}
def Bank.Ranked (D : Bank Γ s) : Prop :=
  ∀ x : Geom, (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, layerWidth*(layerNeed-1) < ∑ T ∈ Finset.range (primaryCutoff+1), r T ∧
      ∀ T ≤ primaryCutoff, r T ≤ Low6969Prices.symbolCount ∧ ∃ e : Fin (r T) → Row 4,
        (∀ i, D.row T (e i)) ∧ LinearIndependent Geom (fun i => symbolAt x (e i))
def Bank.Admissible (D : Bank Γ s) (f : Row 4) (l : ℕ) : Prop :=
  ∀ T ≤ primaryCutoff, ∀ P, D.row T P → f^(levelOrder T-l) ∣ P
private theorem some_admissible (D : Bank Γ s) (f : Row 4) : ∃ l, D.Admissible f l := by
  refine ⟨primaryCutoff/layerWidth+1, fun T _ P _ => ?_⟩
  have hle : levelOrder T ≤ primaryCutoff/layerWidth+1 :=
    Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
  rw [Nat.sub_eq_zero_of_le hle,pow_zero]
  exact one_dvd P
def Bank.availability (D : Bank Γ s) (f : Row 4) : ℕ := by
  classical
  exact Nat.find (some_admissible D f)
theorem Bank.available (D : Bank Γ s) (f : Row 4) : D.Admissible f (D.availability f) := by
  classical
  exact Nat.find_spec (some_admissible D f)
theorem Bank.extremal (D : Bank Γ s) (f : Row 4) (hp : 0 < D.availability f) :
    ∃ T ≤ primaryCutoff, ∃ P, D.row T P ∧ D.availability f ≤ levelOrder T ∧
      f^(levelOrder T - D.availability f) ∣ P ∧ ¬ f^(levelOrder T - D.availability f+1) ∣ P := by
  classical
  let l := D.availability f
  have hbad : ¬ D.Admissible f (l-1) := Nat.find_min (some_admissible D f) (by
    change l-1 < l
    dsimp only [l]
    omega)
  dsimp only [Bank.Admissible] at hbad
  push Not at hbad
  obtain ⟨T,hT,P,hP,hn⟩ := hbad
  have hl : l ≤ levelOrder T := by
    by_contra! hh
    have heq : levelOrder T-(l-1)=0 := by omega
    exact hn (by rw [heq,pow_zero]; exact one_dvd P)
  have heq : levelOrder T-(l-1)=levelOrder T-l+1 := by dsimp only [l] at *; omega
  exact ⟨T,hT,P,hP,hl,D.available f T hT P hP,by rwa [heq] at hn⟩
end
end Low6969RetainedCut
end Merged_R6960Low6969RetainedBank
end Z6969Source2398
