import ProximityPrize.SubmissionLower.GoldBranch6N8

set_option Elab.async false
namespace Euler50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179925
abbrev errors : ℕ := 82219
abbrev physicalDegree : ℕ := 133438
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev evaluatedAnchorCutoff : ℕ := 91 * agreement - 1
abbrev anchorCutoff : ℕ := evaluatedAnchorCutoff + 50

theorem anchorCutoff_lt_char : anchorCutoff < K1.p := by decide
theorem anchorCutoff_double_lt_char : 2 * anchorCutoff + 3 < K1.p := by decide
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
abbrev layerNeed : ℕ := 22449423186794
abbrev layerWidth : ℕ := agreement - physicalDegree + 3
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
def fullCap (top : ℕ) : Shape := ⟨122, 50, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 122 ∧ (∑ i, (a i).j) ≤ 50 ∧
    (∑ i, (a i).t) ≤ top
def lowerWidth (top : ℕ) : ℕ := 122 - top
def lowerIndex (top : ℕ) : ℕ := 50 - 3 * top
def lowerTop (top : ℕ) : ℕ := lowerIndex top / 2
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ lowerWidth top ∧ indexDegree g ≤ lowerIndex top ∧
    TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) (fullCap 13) ∧ TrueWeightLE f anchorCutoff
def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K

def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ActiveFits Q 5164 ∧ ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
abbrev symbolCount : ℕ := 406807694511

/-- Bound a layer by the tapered ambient count and the residual rectangular count. -/
def remaining (b j : ℕ) : ℕ := min symbolCount (K1_13.remaining b j)

def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤ ∑ r ∈ Finset.range (1 + primaryCutoff / layerWidth),
    remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)
abbrev FatEquations := P3_6.FatEquations
abbrev fatOrder : ℕ := 56282
abbrev divisorOrder : ℕ := 51775
abbrev isolatedOrder : ℕ := 617
abbrev commonBox := P3_6.commonBox
abbrev resultantBox := P3_6.resultantBox
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

def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
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

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end
end Euler50Price
