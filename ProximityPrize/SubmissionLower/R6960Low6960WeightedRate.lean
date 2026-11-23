import ProximityPrize.SubmissionLower.R6960Low6960SharedPrice

set_option Elab.async false

namespace Low6960WeightedRate
open K1_13 (Shape)
open Low6960SharedPrice (Rate weights)

abbrev unit : ℕ := 1000000000
abbrev split : ℕ := 10

def boxFee (w x : Shape) : ℕ := w.b * max x.b x.j + w.j * x.j + w.t * min x.t (x.j / 3)
def sepBox (x : Shape) : Shape := ⟨x.b - 1, x.j - 3, x.t - 1⟩
def charge (r a d e : ℕ) : ℕ := e * (24 * (r - e*a) + d * (e - 1))

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
  Fits p x ∧ u.kind = .tilted ∧ u.split = split ∧ 0 < u.amount ∧ Low6960Prices.tiltedFits x ∧
    RayBounds p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (Pays p x u) := by
  unfold Pays Fits RayBounds
  infer_instance

def first : Envelope := ⟨106,48,4,132,53,2756,4257,⟨4886433,26118015,6676780⟩,1966580209⟩
def second : Envelope := ⟨113,53,2,132,55,2938,4257,⟨5348865,28495660,6413088⟩,2254748075⟩

def Allowed (x : Shape) (u : Rate) : Prop :=
  Low6960SharedPrice.RateFits x u ∨ Pays first x u ∨ Pays second x u

instance (x : Shape) (u : Rate) : Decidable (Allowed x u) := by unfold Allowed; infer_instance

private theorem ray_expansion (w : Shape) (b j t : ℕ) (hb : j ≤ b) (ht : 3*t ≤ j) :
    w.b*b+w.j*j+w.t*t = w.b*(b-j)+(w.b+w.j)*(j-3*t)+(3*(w.b+w.j)+w.t)*t := by
  let B := b-j
  let J := j-3*t
  change w.b*b+w.j*j+w.t*t = w.b*B+(w.b+w.j)*J+(3*(w.b+w.j)+w.t)*t
  have hB : b = B+J+3*t := by dsimp [B,J]; omega
  have hJ : j = J+3*t := by dsimp [J]; omega
  rw [hB, hJ]
  ring

theorem fee_le {p : Envelope} {x : Shape} {amount : ℕ} (h : RayBounds p x amount) (y : Shape) :
    unit * boxFee (weights .tilted x) y ≤ (1920 * amount) * boxFee p.coeff y := by
  let b := max y.b y.j
  let j := y.j
  let t := min y.t (y.j/3)
  let w := weights .tilted x
  have hb : j ≤ b := le_max_right _ _
  have ht : 3*t ≤ j := by
    have hd : t ≤ y.j/3 := min_le_right _ _
    dsimp only [j]
    omega
  change unit*(w.b*b+w.j*j+w.t*t) ≤ (1920*amount)*(p.coeff.b*b+p.coeff.j*j+p.coeff.t*t)
  rw [ray_expansion w b j t hb ht, ray_expansion p.coeff b j t hb ht]
  calc
    _ = (unit*w.b)*(b-j) + (unit*(w.b+w.j))*(j-3*t) + (unit*(3*(w.b+w.j)+w.t))*t := by ring
    _ ≤ _ := by
      rw [show (1920*amount)*(p.coeff.b*(b-j)+(p.coeff.b+p.coeff.j)*(j-3*t)+
          (3*(p.coeff.b+p.coeff.j)+p.coeff.t)*t) =
          ((1920*amount)*p.coeff.b)*(b-j) + ((1920*amount)*(p.coeff.b+p.coeff.j))*(j-3*t) +
          ((1920*amount)*(3*(p.coeff.b+p.coeff.j)+p.coeff.t))*t by ring]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (Nat.mul_le_mul_right _ h.2.1))
        (Nat.mul_le_mul_right _ h.2.2.1)

theorem transfer {p : Envelope} {x : Shape} {u : Rate} (h : Pays p x u) (y : Shape) (r a d e : ℕ)
    (hp : (split+1-e)*(24*boxFee p.coeff y+d*p.sep) ≤ split*unit*charge r a d e) :
    (u.split+1-e)*(24*boxFee (weights u.kind x) y+d*boxFee (weights u.kind x) (sepBox x)) ≤
      (Low6960SharedPrice.surfaceScale u.kind*(u.split*u.amount))*charge r a d e := by
  obtain ⟨_, hk, hs, _, _, hw⟩ := h
  rw [hk, hs]
  let w := weights .tilted x
  let z := 24*boxFee w y+d*boxFee w (sepBox x)
  let cap := 1920*u.amount
  let bound := 24*boxFee p.coeff y+d*p.sep
  have hz : unit*z ≤ cap*bound := by
    calc
      _ = 24*(unit*boxFee w y)+d*(unit*boxFee w (sepBox x)) := by dsimp [z]; ring
      _ ≤ 24*(cap*boxFee p.coeff y)+d*(cap*p.sep) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (fee_le hw y)) (Nat.mul_le_mul_left _ hw.2.2.2)
      _ = _ := by dsimp [bound]; ring
  change (split+1-e)*z ≤ (1920*(split*u.amount))*charge r a d e
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < unit)
  calc
    unit*((split+1-e)*z) = (split+1-e)*(unit*z) := by ring
    _ ≤ (split+1-e)*(cap*bound) := Nat.mul_le_mul_left _ hz
    _ = cap*((split+1-e)*bound) := by ring
    _ ≤ cap*(split*unit*charge r a d e) := Nat.mul_le_mul_left _ hp
    _ = _ := by dsimp [cap]; ring

#print axioms transfer
end Low6960WeightedRate
