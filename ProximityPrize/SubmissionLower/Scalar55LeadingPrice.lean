import ProximityPrize.SubmissionLower.PortLow5

namespace Scalar55LeadingPrice
open K1 (I K node)
open K1_13 (Row indexDegree atJet extend)
open scoped Polynomial

abbrev agreement : ℕ := 179876
abbrev physicalDegree : ℕ := 131071
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev anchorCutoff : ℕ := 55 * agreement - 1

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D

def lowerWidth (_ : ℕ) : ℕ := 75
def lowerIndex (_ : ℕ) : ℕ := 22
def lowerTop (_ : ℕ) : ℕ := 10
def lowerCap (_ : ℕ) : ℕ := 2616730184958484

def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 75 ∧ indexDegree g ≤ 22 ∧ g.degreeOf 2 ≤ 10 ∧
    TrueWeightLE g anchorCutoff

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top

end Scalar55LeadingPrice
