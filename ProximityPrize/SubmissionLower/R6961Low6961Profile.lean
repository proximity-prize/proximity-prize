import ProximityPrize.SubmissionLower.R6961Low6961Primary

set_option Elab.async false

namespace Lower6961.Low
open P3 (I K node)
open K1_13 (Row Shape InBox shape OrderAt extend)
open scoped Polynomial BigOperators

abbrev layerWidth : ℕ := agreement-physicalDegree+3
abbrev layerCount : ℕ := 1+primaryCutoff/layerWidth
abbrev TrueWeightLE {n : ℕ} (P : Row n) (T : ℕ) := PrimaryTaper.TrueWeightLE physicalDegree P T

structure Messages (w : I→K) (Γ : Finset K) (s : K→(Polynomial K)) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ∈Γ,(s γ).natDegree≤physicalDegree
  hits : ∀ γ∈Γ,∃ T : Finset I,agreement≤T.card ∧ ∀ i∈T,(s γ).eval (node i)=w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ⊆Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ,fun γ mem=>h.degree γ (hΔ mem),fun γ mem=>h.hits γ (hΔ mem)⟩

def ProperCut (f : Row 4) (Γ : Finset K) (s : K→(Polynomial K)) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬f∣Q) ∧ InBox (shape Q) PrimaryTaper.primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    Final50Price.ActiveFits Q 5164 ∧ ∀ γ∈Γ,OrderAt Q (extend (s γ)) l

def LayerBudget {n : ℕ} (a : Fin n→Shape) (l : Fin n→ℕ) : Prop :=
  need ≤ ∑ r∈Finset.range layerCount,
    Final50Price.remaining (∑ i,(r+1-l i)*(a i).b) (∑ i,(r+1-l i)*(a i).j)
end Lower6961.Low
