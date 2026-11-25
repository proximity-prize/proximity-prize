import ProximityPrize.SubmissionLower.Fast017

set_option Elab.async false

namespace Scalar6963Price
open K1 (I K node)
open K1_13 (Row indexDegree atJet extend)
open scoped Polynomial

abbrev agreement : ℕ := 179798
abbrev physicalDegree : ℕ := 131071
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev anchorCutoff : ℕ := 10608082

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D

def lowerWidth (top : Fin 1) : ℕ := ![80] top
def lowerIndex (top : Fin 1) : ℕ := ![24] top
def lowerTop (top : Fin 1) : ℕ := ![10] top
def lowerCap (top : Fin 1) : ℕ := ![2648776989850163] top

def LowerRow (top : Fin 1) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧
    g.degreeOf 2 ≤ lowerTop top ∧ TrueWeightLE g anchorCutoff

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

def c5 (top : Fin 1) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top

end Scalar6963Price
