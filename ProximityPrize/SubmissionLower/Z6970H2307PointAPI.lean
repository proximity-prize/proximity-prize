import ProximityPrize.SubmissionLower.Z6970H2307Bands
import ProximityPrize.SubmissionLower.Z6970H2307PriceDefs

set_option Elab.async false

namespace Height2307Allocation
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Prices (fullCap)
open Low6969RetainedCut (contractedPrice)
open Height2307Bands
open P3_6_8 (shapeSum)
open scoped BigOperators

abbrev Order := Band → Shape → ℕ

def residual (k : Band) (x : Shape) : Shape :=
  ⟨143-(start k).b-x.b,60-(start k).j-x.j,16-(start k).t-x.t⟩

def Companion (order : Order) (book : Band → Shape → Option ℕ) : Prop :=
  ∀ {k rest debt}, book k rest = some debt → ∀ {n : ℕ} (a : Fin n → Shape)
    (cost : Fin n → ℕ) (partners : Finset (Fin n)),
    (∀ v∈partners, Valid (a v) ∧ (a v).j≤2*(a v).b+(a v).t) →
    InBox (shapeSum a partners) rest →
    (∀ v∈partners, cost v≤contractedPrice (a v) (start k) (order k (a v)) 179) →
    (∑ v∈partners,cost v)≤debt

def Quote (G : Shape → ℕ) (Gated : ℕ → Shape → Prop) (k : Band)
    (x : Shape) (l fee : ℕ) : Prop :=
  contractedPrice x (start k) l 179 ≤ fee ∨
    (∃ u, Low6969SharedPrice.RateFits x u ∧ Low6969SharedPrice.price x l 179 u ≤ fee) ∨
    (Gated k.val x ∧ Height2307Count6970.gatePrice G x l ≤ fee)

def PointTable (order : Order) (book : Band → Shape → Option ℕ)
    (G : Shape → ℕ) (Gated : ℕ → Shape → Prop) : Prop :=
  ∀ k x, Valid x → x.j≤2*x.b+x.t → InBox ((start k).plus x) (fullCap 16) →
    ∃ m fee, 0<m ∧ m≤order k x ∧ Quote G Gated k x m fee ∧
      (fee ≤ allowance k ((start k).t+x.t) x.b x.j x.t ∨
        ∃ debt, book k (residual k x) = some debt ∧
          fee+debt+reserve k+Low6969Prices.lowerCap ((start k).t+x.t)≤budget)

end Height2307Allocation
