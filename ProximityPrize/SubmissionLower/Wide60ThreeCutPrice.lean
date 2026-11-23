/- Full-support adaptation of PR656 (8d1d82a4df2fd3cd347a881c91088431dded323d)
   and the PR658 coupled-chart and sequential-cut proof (fbfa288e5fe2252d30dde0b0b8a065e0df712acb). -/
import ProximityPrize.SubmissionLower.PortLow5

namespace Wide60ThreeCutPrice
open K1 (I K node)
open K1_13 (Row indexDegree atJet extend)
open scoped Polynomial

abbrev agreement:ℕ:=179827
abbrev physicalDegree:ℕ:=131071
abbrev taylorLength:ℕ:=physicalDegree+1
abbrev anchorCutoff:ℕ:=16373174

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val)*a)≤D

def lowerWidth (top:Fin 5):ℕ := ![57,63,67,69,78] top
def lowerIndex (top:Fin 5):ℕ := ![23,22,21,20,19] top
def lowerTop (top:Fin 5):ℕ := ![10,10,10,10,9] top
def lowerCap (top:Fin 5):ℕ := ![1636126182550072,1717600839844781,1700283485206119,1709344005401308,1665714221994368] top

def LowerRow (top : Fin 5) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧
    g.degreeOf 2≤lowerTop top ∧ TrueWeightLE g anchorCutoff

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct:Set.InjOn s (Γ:Set K)
  degree : ∀ γ ∈ Γ,(s γ).natDegree≤physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T:Finset I,agreement≤T.card ∧ ∀ i ∈ T,(s γ).eval (node i)=w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ,fun γ hγ => h.degree γ (hΔ hγ),fun γ hγ => h.hits γ (hΔ hγ)⟩

def c5 (top : Fin 5) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ,atJet g (extend (s γ))=0)→Γ.card≤lowerCap top

end Wide60ThreeCutPrice
