import ProximityPrize.SubmissionLower.PortLow5

namespace Scalar50Wide55Price
open K1 (I K node)
open K1_13 (Row indexDegree atJet extend)
open scoped Polynomial

abbrev agreement : ℕ := 179905
abbrev physicalDegree : ℕ := 131071
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev anchorCutoff : ℕ := 16373174

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D

def lowerWidth (top : Fin 4) : ℕ := ![60,64,68,74] top
def lowerIndex (top : Fin 4) : ℕ := ![22,21,20,19] top
def lowerTop (top : Fin 4) : ℕ := ![10,10,10,9] top
def lowerCap (top : Fin 4) : ℕ := ![1998214939673133,2000435286055873,1978421264831724,1998378207868762] top

def LowerRow (top : Fin 4) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧
    g.degreeOf 2 ≤ lowerTop top ∧ TrueWeightLE g anchorCutoff

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

def c5 (top : Fin 4) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top

end Scalar50Wide55Price
