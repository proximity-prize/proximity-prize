import ProximityPrize.SubmissionLower.Z6969Pack0836

namespace Height2307Leading
open K1_13 (Row extend atJet indexDegree)
open Low6969Prices (Messages TrueWeightLE anchorCutoff)

def lowerWidth (top : ℕ) : ℕ := 143 - top
def lowerIndex (top : ℕ) : ℕ := 60 - 3 * top
def lowerTop (top : ℕ) : ℕ := lowerIndex top / 2

def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧ TrueWeightLE g anchorCutoff

def lowerCap : ℕ → ℕ
  | 0 => 32366760449246328
  | 1 => 29327847625153443
  | 2 => 26425863949989591
  | 3 => 23662310668877784
  | 4 => 21039929228222417
  | 5 => 18560350637172986
  | 6 => 16226192633808788
  | 7 => 14039202548103346
  | 8 => 12001888057905658
  | 9 => 10116098961026135
  | 10 => 8384246932962957
  | 11 => 6808269976591597
  | 12 => 5390498232723584
  | 13 => 4132943236742945
  | 14 => 3037868472223412
  | 15 => 2107343924716369
  | 16 => 1343581707791287
  | _ => 0

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top

end Height2307Leading

