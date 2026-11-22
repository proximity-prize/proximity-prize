import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price -- serialize candidate build

namespace Euler50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179895
abbrev errors : ℕ := 82249
abbrev physicalDegree : ℕ := 133438
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev evaluatedAnchorCutoff : ℕ := 91 * agreement - 1
abbrev anchorCutoff : ℕ := evaluatedAnchorCutoff + 50

def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
def fullCap (top : ℕ) : Shape := ⟨122, 50, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 122 ∧ (∑ i, (a i).j) ≤ 50 ∧
    (∑ i, (a i).t) ≤ top
def lowerWidth (top : ℕ) : ℕ := 122 - top
def lowerIndex (top : ℕ) : ℕ := 50 - 3 * top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧
    TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) (fullCap 13) ∧ TrueWeightLE f anchorCutoff
def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K

abbrev FatEquations := P3_6.FatEquations
abbrev fatOrder : ℕ := 56282
def lowerCap : ℕ → ℕ
  | 0 => 20191258188519948
  | 1 => 17982643821040339
  | 2 => 15891021751610123
  | 3 => 13918175243762510
  | 4 => 12066589566482795
  | 5 => 10338137787613356
  | 6 => 8735220537434730
  | 7 => 7259789031503614
  | 8 => 5914171121896265
  | 9 => 4700384107477598
  | 10 => 3620695330431312
  | 11 => 2677175700713190
  | 12 => 1872044726737353
  | 13 => 1207414049521846
  | _ => 0
def Holds (E : FatEquations) (S : Geom[X]) : Prop :=
  atJet E.common S = 0 ∨ OrderAt E.residual S fatOrder

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

abbrev BentCap := Shape × ℕ

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
end
end Euler50Price
