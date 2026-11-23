import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch4
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_3
noncomputable section
open Polynomial
open P3 (HighBand K p agreement blockLength AnchorModel AnchoredFamily)
open P3_7 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
export P1_7_4 (Mass massQ dotQ capMin pairMinSeed cornerBound pairedCap PairedMass
  degreeVector introWeight introJump envelope running weightedBill ODEGuard)
def stageAt (b : HighBand) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
def laterCount (b : HighBand) := (stages b).length - 1
def introIndices : HighBand → List ℕ
  | .h2274 | .h2294 => List.range' 1 11
  | .h7773 => []
def stopIndex (_ : HighBand) : ℕ := 0
def introAccount (b : HighBand) (k : Fin 4) :
    List ℕ → (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ
  | [], cap, old =>
    introJump cap old (stageAt b 0).moving.shape k +
      (![cap 0, cap 2, 2*cap 0*cap 2, cap 2 * cap 2] : Fin 4 → ℕ) k
  | i :: is, cap, old =>
    let s := stageAt b i
    let c := s.free.shape
    introJump cap old c k + introAccount b k is
      (fun j => min (cap j) (degreeVector c j / (s.reserve+1)))
      (fun j => max (old j) (introWeight c k j))
def initialCap (b : HighBand) (k : Fin 4) : ℕ :=
  let s := stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : HighBand) : ℕ :=
  if (introIndices b).isEmpty then
    let s := stageAt b 0
    s.free.shape.U * s.moving.shape.U + (pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def stageCap (b : HighBand) (i : ℕ) (square : Bool) : Mass :=
  let s := stageAt b i
  pairedCap s.free.shape s.moving.shape s.reserve square
def history (b : HighBand) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)))
def cutShape (b : HighBand) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : HighBand) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def lossWeight (b : HighBand) (a h : ℕ → ℚ) (i : ℕ) : Mass :=
  fun k => a i * cutWeight b 0 i k + h i * cutWeight b 1 i k
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
structure BankGuard (hi reserve : ℕ) (s : Shape) : Prop where
  ode : ODEGuard s.B s.J
  seed_small : s.U < p
  pos : 0 < s.m * agreement
  buffer : 2*hi*reserve ≤ fullCutoff s
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  mass_bound : Fits parents (initialCap b)
  seed : K1_14_3.SeedCover
  seed_le : seed.curve.totalDegree ≤ initialCap b 2
  seed_points : seed.points.card ≤ initialE b
  ordinates : Finset FX
  ordinate_le : ordinates.card ≤ initialCap b 0
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, seed.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    graphEval (M.label γ) content = 0 ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P3_7_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace P3_7_3
noncomputable section
open Polynomial
open P3 (HighBand K p AnchorModel AnchoredFamily)
open P3_7 ( stages terminal   PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
end
end P3_7_3
end
section
namespace P3_7_3_3
open P3 (HighBand p agreement)
open P3_7 (Stage stages terminal fullCutoff fees)
open P3_7_3 (stageAt laterCount stopIndex introIndices BankGuard)
open K1_14 (Shape)
private theorem bank {hi r : ℕ} {s : Shape}
    (hb : 2 ≤ s.B) (hj : 0 < s.J) (hjb : s.J ≤ s.B) (hbp : s.B < p)
    (hu : s.U < p) (hm : 0 < s.m) (hr : 2 * hi * r ≤ fullCutoff s) :
    BankGuard hi r s :=
  ⟨⟨hb, hj, hjb, hbp⟩, hu, Nat.mul_pos hm (by decide), hr⟩
local notation "bank!" => bank (by decide) (by decide) (by decide)
  (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) (by decide) (Nat.le_of_ble_eq_true rfl)
private def StageChecks (hi : ℕ) (s : Stage) : Prop :=
  s.reserve < p ∧ BankGuard hi s.reserve s.free.shape ∧ BankGuard hi s.reserve s.moving.shape
private theorem checked {hi r : ℕ} {s : Stage} (he : s.reserve = r) (hs : r < p)
    (hf : BankGuard hi s.reserve s.free.shape) (hm : BankGuard hi s.reserve s.moving.shape) :
    StageChecks hi s := ⟨he ▸ hs, hf, hm⟩
private def TailChecks (hi : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, 0 < s.reserve ∧ StageChecks hi s
private theorem cons {hi r : ℕ} {s : Stage} {ss : List Stage}
    (he : s.reserve = r) (hp : 0 < r) (hs : StageChecks hi s) (ht : TailChecks hi ss) :
    TailChecks hi (s :: ss) :=
  (List.forall_mem_cons).mpr ⟨⟨he ▸ hp, hs⟩, ht⟩
local notation "row!" rr => cons (r := rr) rfl (by decide)
  (checked (r := rr) rfl (Nat.le_of_ble_eq_true rfl) bank! bank!)
end P3_7_3_3
end
section
namespace P3_7_3_3
open P3 (HighBand p)
open P3_7 (fees)
open P3_7_3 (stageAt initialCap initialE introIndices introAccount degreeVector  
   stopIndex history ODEGuard)
open P1_7_4 (cornerBound sharedBound pairMinSeed pairMinOrdinate)
open K1_14 (Shape)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
end P3_7_3_3
end
section
namespace P3_7_3_3
open P3 (HighBand agreement blockLength)
open P3_7 (stages fees degreeAt gap scale muNum lambdaNum ceilRatio)
open P3_7_3 (  initialCap  )
open scoped BigOperators
end P3_7_3_3
end
section
namespace P3_7_3_4
open P3 (p blockLength agreement)
open P3_7 (degreeAt gap curveUnit)
abbrev Q : ℚ := ((p+1 : ℕ) : ℚ)
private def alpha (hi : ℕ) : ℚ := 1 + 2 * ((blockLength : ℚ) / agreement) * degreeAt hi
private def mu (hi : ℕ) : ℚ := ((blockLength - degreeAt hi : ℕ) : ℚ) / gap hi
private def drop (a : ℚ) := a / Q
private def quad (hi : ℕ) (a : ℚ) := 2 * alpha hi * drop a
private def slope (hi : ℕ) (a : ℚ) := 2 * alpha hi - (mu hi - alpha hi) * drop a
def raw (hi : ℕ) (a : ℚ) (g : ℕ) :=
  (1 - a * g / Q) * curveUnit hi g
def rateCheck (hi : ℕ) (a h : ℚ) (m : ℕ) : Bool :=
  decide (Q/81 ≤ a) && decide (0 ≤ h) && decide (0 ≤ quad hi a) &&
    (decide (m = 1) || decide (quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)) &&
    decide (slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) && decide (raw hi a m ≤ h)
end P3_7_3_4
end
section
namespace P3_7_3_4
open P3 (HighBand p)
open P3_7 (fees)
open P3_7_3
open P1_7_4 (dotQ_mono_mass)
private def corner (b : HighBand) (i r : ℕ) (k : Fin 4) : ℚ :=
  let s := stageAt b i
  cornerBound s.free.shape s.moving.shape r (s.reserve+1) (decide (stopIndex b ≤ i)) k
abbrev Receipt := List ℕ
def entry (xs : Receipt) (i : ℕ) : ℕ := xs[i]?.getD 0
def lossUnits (xs : Receipt) (i : ℕ) : ℕ := entry xs i / 0x100000000000000
def byte (xs : Receipt) (i j : ℕ) : ℕ := entry xs i / 256^j % 256
def cap (b : HighBand) (xs : Receipt) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => fun k =>
    let r := byte xs (i+1) k
    if r = 0 then cap b xs i k else corner b (i+1) r k
def dot4 (v c : Mass) : ℚ := v 0*c 0 + (v 1*c 1 + (v 2*c 2 + (v 3*c 3 + 0)))
def localDegree (b : HighBand) (xs : Receipt) (i : ℕ) : ℚ :=
  dot4 (cutWeight b 0 i) (cap b xs i)
def degreeRate (b : HighBand) (xs : Receipt) (i : ℕ) : ℚ :=
  let d := byte xs i 4
  if d = 0 then localDegree b xs i else Q / d
def heightRate (b : HighBand) (xs : Receipt) (i : ℕ) : ℚ :=
  max 0 (raw b.row.hi (degreeRate b xs i) (byte xs i 5))
def discounted (b : HighBand) : Prop := b.row.lo < 7773
instance (b : HighBand) : Decidable (discounted b) := inferInstanceAs (Decidable (_ < _))
def rates (b : HighBand) (xs : Receipt) : ℕ → Mass :=
  if discounted b then lossWeight b (degreeRate b xs) (heightRate b xs) else fun _ _ => 0
def multiplier (b : HighBand) : ℚ := if discounted b then 1 else Q
def jump (v : ℕ → Mass) (i : ℕ) (c : Mass) : ℚ :=
  dot4 (fun k => running v (i+1) k - running v i k) c
def seedPrice (xs : Receipt) (i : ℕ) : ℚ := (0x400000 * byte xs i 6 : ℕ)
def capCheck (b : HighBand) (xs : Receipt) (i : ℕ) (k : Fin 4) : Bool :=
  decide (byte xs i k ≤ (stageAt b i).reserve + 1)
def rateRow (b : HighBand) (xs : Receipt) (i : ℕ) : Bool :=
  if discounted b then
    rateCheck b.row.hi (degreeRate b xs i) (heightRate b xs i) (byte xs i 5) &&
      decide (localDegree b xs i ≤ degreeRate b xs i)
  else true
structure RowOK (b : HighBand) (xs : Receipt) (i : ℕ) : Prop where
  cap0 : capCheck b xs i 0 = true
  cap1 : capCheck b xs i 1 = true
  cap2 : capCheck b xs i 2 = true
  cap3 : capCheck b xs i 3 = true
  rate : rateRow b xs i = true
  seed : decide (jump (cutWeight b 0) i (cap b xs i) ≤ seedPrice xs i) = true
  loss : decide (multiplier b * jump (cutWeight b 0) i (cap b xs i) +
    jump (rates b xs) i (cap b xs i) ≤ (lossUnits xs i : ℚ) / 256) = true
def RowsOK (b : HighBand) (xs : Receipt) (n : ℕ) : Prop :=
  ∀ i : Fin n, RowOK b xs i
private theorem RowsOK.prev {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs (n+1)) :
    RowsOK b xs n := fun i => h i.castSucc
end P3_7_3_4
end
section
namespace P3_7_3_4
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
local notation "r!" => (RowOK.mk (by decide) (by decide) (by decide) (by decide)
  (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl))
end P3_7_3_4
end
