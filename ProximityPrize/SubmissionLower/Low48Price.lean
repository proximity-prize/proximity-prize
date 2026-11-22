import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Low48BentSupport -- serialize candidate build

namespace Low48Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179944
abbrev errors : ℕ := 82200
abbrev physicalDegree : ℕ := 133437
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
def fullCap (top : ℕ) : Shape := ⟨121, 49, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 121 ∧ (∑ i, (a i).j) ≤ 49 ∧
    (∑ i, (a i).t) ≤ top
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) (fullCap 13) ∧ TrueWeightLE f anchorCutoff
def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (tiltedSurface p q) (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  if 3 * x.t + 3 ≤ x.j then min (physicalPriceOld x l) (physicalPriceTilted x l)
  else physicalPriceOld x l

def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l
end
end Low48Price
