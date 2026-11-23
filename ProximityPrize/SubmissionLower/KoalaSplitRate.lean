import ProximityPrize.SubmissionLower.KoalaWeightedRate

set_option Elab.async false

namespace KoalaSplitRate
open K1_13 (Shape)
open Final50SharedPrice (Rate weights)
open KoalaWeightedRate (Envelope Fits boxFee sepBox charge)

def RayBounds (p : Envelope) (U : ℕ) (x : Shape) (amount : ℕ) : Prop :=
  let w:=weights .tilted x
  let scale:=1920*amount
  U*w.b ≤ scale*p.coeff.b ∧
    U*(w.b+w.j)≤scale*(p.coeff.b+p.coeff.j) ∧
    U*(3*(w.b+w.j)+w.t)≤scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    U*boxFee w (sepBox x)≤scale*p.sep

def Pays (p : Envelope) (k U : ℕ) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = k ∧ 0 < k ∧ 0 < U ∧ 0 < u.amount ∧
    Final50Price.tiltedFits x ∧ RayBounds p U x u.amount

instance (p : Envelope) (k U : ℕ) (x : Shape) (u : Rate) : Decidable (Pays p k U x u) := by
  unfold Pays Fits RayBounds
  infer_instance

private theorem ray_expansion (w : Shape) (b j t : ℕ) (hb : j ≤ b) (ht : 3*t ≤ j) :
    w.b*b+w.j*j+w.t*t=w.b*(b-j)+(w.b+w.j)*(j-3*t)+(3*(w.b+w.j)+w.t)*t:=by
  let B:=b-j
  let J:=j-3*t
  change w.b*b+w.j*j+w.t*t=w.b*B+(w.b+w.j)*J+(3*(w.b+w.j)+w.t)*t
  have hB:b=B+J+3*t:=by dsimp [B,J]; omega
  have hJ:j=J+3*t:=by dsimp [J]; omega
  rw [hB,hJ]
  ring

theorem fee_le {p : Envelope} {U : ℕ} {x : Shape} {amount : ℕ} (h : RayBounds p U x amount) (y : Shape) :
    U*boxFee (weights .tilted x) y≤(1920*amount)*boxFee p.coeff y:=by
  let b:=max y.b y.j
  let j:=y.j
  let t:=min y.t (y.j/3)
  let w:=weights .tilted x
  have hb:j≤b:=le_max_right _ _
  have ht : 3*t ≤ j := by
    have hd:t≤y.j/3:=min_le_right _ _
    dsimp only [j]
    omega
  change U*(w.b*b+w.j*j+w.t*t)≤(1920*amount)*(p.coeff.b*b+p.coeff.j*j+p.coeff.t*t)
  rw [ray_expansion w b j t hb ht,ray_expansion p.coeff b j t hb ht]
  calc
    _=(U*w.b)*(b-j)+(U*(w.b+w.j))*(j-3*t)+(U*(3*(w.b+w.j)+w.t))*t:=by ring
    _ ≤ _ := by
      rw [show (1920*amount)*(p.coeff.b*(b-j)+(p.coeff.b+p.coeff.j)*(j-3*t)+
          (3*(p.coeff.b+p.coeff.j)+p.coeff.t)*t) =
          ((1920*amount)*p.coeff.b)*(b-j)+((1920*amount)*(p.coeff.b+p.coeff.j))*(j-3*t) +
          ((1920*amount)*(3*(p.coeff.b+p.coeff.j)+p.coeff.t))*t by ring]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (Nat.mul_le_mul_right _ h.2.1))
        (Nat.mul_le_mul_right _ h.2.2.1)

theorem transfer {p : Envelope} {k U : ℕ} {x : Shape} {u : Rate} (h : Pays p k U x u) (y : Shape) (r a d e : ℕ)
    (hp:(k+1-e)*(24*boxFee p.coeff y+d*p.sep)≤k*U*charge r a d e) :
    (u.split+1-e)*(24*boxFee (weights u.kind x) y+d*boxFee (weights u.kind x) (sepBox x)) ≤
      (Final50SharedPrice.surfaceScale u.kind*(u.split*u.amount))*charge r a d e:=by
  obtain ⟨_,hk,hs,_,hU,_,_,hw⟩:=h
  rw [hk,hs]
  let w:=weights .tilted x
  let z:=24*boxFee w y+d*boxFee w (sepBox x)
  let cap:=1920*u.amount
  let bound:=24*boxFee p.coeff y+d*p.sep
  have hz : U*z ≤ cap*bound := by
    calc
      _=24*(U*boxFee w y)+d*(U*boxFee w (sepBox x)):=by dsimp [z]; ring
      _ ≤ 24*(cap*boxFee p.coeff y)+d*(cap*p.sep) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (fee_le hw y)) (Nat.mul_le_mul_left _ hw.2.2.2)
      _=_:=by dsimp [bound]; ring
  change (k+1-e)*z≤(1920*(k*u.amount))*charge r a d e
  apply Nat.le_of_mul_le_mul_left _ hU
  calc
    U*((k+1-e)*z)=(k+1-e)*(U*z):=by ring
    _≤(k+1-e)*(cap*bound):=Nat.mul_le_mul_left _ hz
    _=cap*((k+1-e)*bound):=by ring
    _≤cap*(k*U*charge r a d e):=Nat.mul_le_mul_left _ hp
    _=_:=by dsimp [cap]; ring

#print axioms transfer
end KoalaSplitRate
