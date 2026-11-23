import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option Elab.async false

namespace KoalaWeightedRate
open K1_13 (Shape)
open Final50SharedPrice (Rate weights)

abbrev unit : ℕ := 1000000000
abbrev split : ℕ := 10

def boxFee (w x : Shape) : ℕ := w.b * max x.b x.j + w.j * x.j + w.t * min x.t (x.j / 3)
def sepBox (x : Shape) : Shape := ⟨x.b - 1, x.j - 3, x.t - 1⟩

structure Envelope where
  widthLow : ℕ
  indexLow : ℕ
  topLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
  taperLow : ℕ
  taperHigh : ℕ
  coeff : Shape
  sep : ℕ

def Fits (p : Envelope) (x : Shape) : Prop :=
  p.widthLow ≤ x.b ∧ x.b ≤ p.widthHigh ∧ p.indexLow ≤ x.j ∧ x.j ≤ p.indexHigh ∧
    p.topLow ≤ x.t ∧ p.taperLow ≤ 26*x.b ∧ min (26*x.b+25*x.j) (x.b+25*165) ≤ p.taperHigh

def RayBounds (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weights .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

def Pays (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = split ∧ 0 < u.amount ∧ Final50Price.tiltedFits x ∧
    RayBounds p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (Pays p x u) := by
  unfold Pays Fits RayBounds
  infer_instance

def first : Envelope := ⟨106,48,4,132,53,2756,4257,⟨4886433,26118015,6676780⟩,1966580209⟩
def second : Envelope := ⟨113,53,2,132,55,2938,4257,⟨5348865,28495660,6413088⟩,2254748075⟩

def Allowed (x : Shape) (u : Rate) : Prop :=
  Final50SharedPrice.RateFits x u ∨ Pays first x u ∨ Pays second x u

instance (x : Shape) (u : Rate) : Decidable (Allowed x u) := by unfold Allowed; infer_instance




end KoalaWeightedRate
