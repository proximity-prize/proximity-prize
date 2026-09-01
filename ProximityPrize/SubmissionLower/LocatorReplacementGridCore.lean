import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.N5

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

open RCN095 RCN260 LocatorFactorAggregate LocatorLowQuotient

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private abbrev prime : ℕ := 2130706433
abbrev bound : ℕ := 271584249856321201
abbrev totalCap : ℕ := 2774
private abbrev ysCap : ℕ := 85
private abbrev slopeCap : ℕ := 18
private abbrev sourceLength : ℕ := 56863
private abbrev delta : ℕ := 50578

/-- A rectangular cumulative-degree box for one irreducible factor. -/
structure Box where
  r : ℕ
  ylo : ℕ
  yhi : ℕ
  tlo : ℕ
  thi : ℕ
  deriving DecidableEq

def Box.valid (b : Box) : Prop :=
  1 ≤ b.r ∧ b.r ≤ b.ylo ∧ b.ylo ≤ b.yhi ∧ b.yhi ≤ ysCap ∧
    b.ylo ≤ b.thi ∧ b.tlo ≤ b.thi ∧ b.thi ≤ totalCap

instance (b : Box) : Decidable b.valid := by unfold Box.valid; infer_instance

def Box.factorY (b : Box) : ℕ := min b.yhi b.thi
def Box.factorT (b : Box) : ℕ := max b.tlo b.ylo
def Box.ordinaryCap (b : Box) : FlagDegree := cap b.thi b.factorY b.r
def Box.ordinaryCost (b : Box) : ℕ :=
  paddedCost 131072 131073 b.ordinaryCap
def Box.ordinaryFits (b : Box) : Prop :=
  totalCap * b.ordinaryCost ≤ bound * b.factorT

instance (b : Box) : Decidable b.ordinaryFits := by
  unfold Box.ordinaryFits; infer_instance

/-- Arithmetic data for a kernel source embedded in the common ambient box. -/
structure Source where
  y : ℕ
  r : ℕ
  gap : ℕ
  deriving DecidableEq

def sourceA : Source := ⟨87, 18, 14369494135⟩
def sourceAux : Source := ⟨99, 21, 818464256093⟩
def sourceC : Source := ⟨243, 52, 55614698193593⟩

def stageT (b : Box) (j : ℕ) : ℕ := sourceLength - j * b.factorT
def stageY (src : Source) (b : Box) (j : ℕ) : ℕ := src.y - j * b.ylo
def stageR (src : Source) (b : Box) (j : ℕ) : ℕ := src.r - j * b.r

def stageBand (src : Source) (b : Box) (j : ℕ) : ℕ :=
  delta * channelCount (stageT b j) (stageY src b j) (stageR src b j)

def bandSum (src : Source) (b : Box) : ℕ → ℕ
  | 0 => 0
  | 1 => stageBand src b 1
  | 2 => stageBand src b 1 + stageBand src b 2
  | 3 => stageBand src b 1 + stageBand src b 2 + stageBand src b 3
  | 4 => stageBand src b 1 + stageBand src b 2 + stageBand src b 3 +
      stageBand src b 4
  | 5 => stageBand src b 1 + stageBand src b 2 + stageBand src b 3 +
      stageBand src b 4 + stageBand src b 5
  | 6 => stageBand src b 1 + stageBand src b 2 + stageBand src b 3 +
      stageBand src b 4 + stageBand src b 5 + stageBand src b 6
  | _ => 0

def stagePair (src : Source) (b : Box) (j : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181648, b.factorY, b.r, b.thi,
    stageY src b j, stageR src b j, stageT b j⟩

def PairGates (P : UnequalParameters) : Prop :=
  1 ≤ P.leftR ∧ P.leftY < prime ∧ P.leftR < prime ∧ P.leftZ < prime ∧
    P.mixedCost.y < prime ∧ P.mixedCost.r < prime ∧ P.mixedCost.z < prime

instance (P : UnequalParameters) : Decidable (PairGates P) := by
  unfold PairGates; infer_instance

def stageCost (src : Source) (b : Box) (j : ℕ) : ℕ :=
  (stagePair src b j).regularCountCap

def routeCost (src : Source) (b : Box) : ℕ → ℕ
  | 0 => 0
  | 1 => stageCost src b 1
  | 2 => max (stageCost src b 1) (stageCost src b 2)
  | 3 => max (max (stageCost src b 1) (stageCost src b 2))
      (stageCost src b 3)
  | 4 => max (max (max (stageCost src b 1) (stageCost src b 2))
      (stageCost src b 3)) (stageCost src b 4)
  | 5 => max (max (max (max (stageCost src b 1) (stageCost src b 2))
      (stageCost src b 3)) (stageCost src b 4)) (stageCost src b 5)
  | 6 => max (max (max (max (max (stageCost src b 1) (stageCost src b 2))
      (stageCost src b 3)) (stageCost src b 4)) (stageCost src b 5))
      (stageCost src b 6)
  | _ => 0

def pairGatesThrough (src : Source) (b : Box) : ℕ → Prop
  | 0 => True
  | 1 => PairGates (stagePair src b 1)
  | 2 => PairGates (stagePair src b 1) ∧ PairGates (stagePair src b 2)
  | 3 => PairGates (stagePair src b 1) ∧ PairGates (stagePair src b 2) ∧
      PairGates (stagePair src b 3)
  | 4 => PairGates (stagePair src b 1) ∧ PairGates (stagePair src b 2) ∧
      PairGates (stagePair src b 3) ∧ PairGates (stagePair src b 4)
  | 5 => PairGates (stagePair src b 1) ∧ PairGates (stagePair src b 2) ∧
      PairGates (stagePair src b 3) ∧ PairGates (stagePair src b 4) ∧
      PairGates (stagePair src b 5)
  | 6 => PairGates (stagePair src b 1) ∧ PairGates (stagePair src b 2) ∧
      PairGates (stagePair src b 3) ∧ PairGates (stagePair src b 4) ∧
      PairGates (stagePair src b 5) ∧ PairGates (stagePair src b 6)
  | _ => False

instance (src : Source) (b : Box) (k : ℕ) : Decidable (pairGatesThrough src b k) := by
  rcases k with _ | k
  · simp only [pairGatesThrough]; infer_instance
  · rcases k with _ | k
    · simp only [pairGatesThrough]; infer_instance
    · rcases k with _ | k
      · simp only [pairGatesThrough]; infer_instance
      · rcases k with _ | k
        · simp only [pairGatesThrough]; infer_instance
        · rcases k with _ | k
          · simp only [pairGatesThrough]; infer_instance
          · rcases k with _ | k
            · simp only [pairGatesThrough]; infer_instance
            · rcases k with _ | k
              · simp only [pairGatesThrough]; infer_instance
              · simp only [pairGatesThrough]; infer_instance

def terminalCoprime (src : Source) (b : Box) (k : ℕ) : Prop :=
  stageT b k < b.factorT ∨ stageY src b k < b.ylo ∨ stageR src b k < b.r

instance (src : Source) (b : Box) (k : ℕ) :
    Decidable (terminalCoprime src b k) := by
  unfold terminalCoprime; infer_instance

def RouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ 6 ∧
    k * b.ylo ≤ src.y ∧ k * b.r ≤ src.r ∧
    k * b.factorT + stageY src b k ≤ sourceLength ∧
    bandSum src b k < src.gap ∧ terminalCoprime src b k ∧
    pairGatesThrough src b k ∧
    totalCap * routeCost src b k ≤ bound * b.factorT

instance (src : Source) (k : ℕ) (b : Box) : Decidable (RouteFits src k b) := by
  unfold RouteFits; infer_instance

/-- A receipt-local propositionally equivalent presentation of `RouteFits`. -/
def FastRouteFits (src : Source) (k : ℕ) (b : Box) : Prop :=
  1 ≤ k ∧ k ≤ 6 ∧
    k * b.ylo ≤ src.y ∧ k * b.r ≤ src.r ∧
    k * b.factorT + stageY src b k ≤ sourceLength ∧
    terminalCoprime src b k ∧ bandSum src b k < src.gap ∧
    pairGatesThrough src b k ∧
    totalCap * routeCost src b k ≤ bound * b.factorT

instance (src : Source) (k : ℕ) (b : Box) : Decidable (FastRouteFits src k b) := by
  unfold FastRouteFits; infer_instance

theorem fastRouteFits_iff (src : Source) (k : ℕ) (b : Box) :
    FastRouteFits src k b ↔ RouteFits src k b := by
  constructor
  · rintro ⟨hkpos, hkcap, hy, hr, hlen, hterminal, hband, hgates, hcost⟩
    exact ⟨hkpos, hkcap, hy, hr, hlen, hband, hterminal, hgates, hcost⟩
  · rintro ⟨hkpos, hkcap, hy, hr, hlen, hband, hterminal, hgates, hcost⟩
    exact ⟨hkpos, hkcap, hy, hr, hlen, hterminal, hband, hgates, hcost⟩

def Fits (b : Box) : Prop :=
  b.ordinaryFits ∨ RouteFits sourceA 1 b ∨ RouteFits sourceAux 1 b ∨
    RouteFits sourceC 2 b ∨ RouteFits sourceC 3 b ∨
    RouteFits sourceC 4 b ∨ RouteFits sourceC 5 b ∨ RouteFits sourceC 6 b

instance (b : Box) : Decidable (Fits b) := by unfold Fits; infer_instance

def FastFits (b : Box) : Prop :=
  b.ordinaryFits ∨ FastRouteFits sourceA 1 b ∨ FastRouteFits sourceAux 1 b ∨
    FastRouteFits sourceC 2 b ∨ FastRouteFits sourceC 3 b ∨
    FastRouteFits sourceC 4 b ∨ FastRouteFits sourceC 5 b ∨
    FastRouteFits sourceC 6 b

instance (b : Box) : Decidable (FastFits b) := by unfold FastFits; infer_instance

theorem fastFits_to_fits (b : Box) : FastFits b → Fits b := by
  intro h
  simpa only [FastFits, Fits, fastRouteFits_iff] using h

abbrev CoarseCell := Fin 18 × Fin 22 × Fin 22
def coarseR (c : CoarseCell) : ℕ := c.1.val + 1
def coarseYlo (c : CoarseCell) : ℕ := coarseR c + 4 * c.2.1.val
def coarseYhi (c : CoarseCell) : ℕ := min ysCap (coarseYlo c + 3)
def coarseTlo (c : CoarseCell) : ℕ := 128 * c.2.2.val
def coarseThi (c : CoarseCell) : ℕ := min totalCap (coarseTlo c + 127)
def coarseBox (c : CoarseCell) : Box :=
  ⟨coarseR c, coarseYlo c, coarseYhi c, coarseTlo c, coarseThi c⟩
def HardCoarse (c : CoarseCell) : Prop := (coarseBox c).valid ∧ ¬ Fits (coarseBox c)
instance (c : CoarseCell) : Decidable (HardCoarse c) := by
  unfold HardCoarse; infer_instance

def FastHardCoarse (c : CoarseCell) : Prop :=
  (coarseBox c).valid ∧ ¬ FastFits (coarseBox c)
instance (c : CoarseCell) : Decidable (FastHardCoarse c) := by
  unfold FastHardCoarse; infer_instance

structure FineCell where
  parent : {c : CoarseCell // HardCoarse c}
  yi : Fin 4
  ti : Fin 4
  deriving DecidableEq, Fintype

def fineR (c : FineCell) : ℕ := coarseR c.parent.1
def fineY (c : FineCell) : ℕ := coarseYlo c.parent.1 + c.yi.val
def fineTlo (c : FineCell) : ℕ := coarseTlo c.parent.1 + 32 * c.ti.val
def fineThi (c : FineCell) : ℕ := min (coarseThi c.parent.1) (fineTlo c + 31)
def fineBox (c : FineCell) : Box := ⟨fineR c, fineY c, fineY c, fineTlo c, fineThi c⟩
def HardFine (c : FineCell) : Prop := (fineBox c).valid ∧ ¬ Fits (fineBox c)
instance (c : FineCell) : Decidable (HardFine c) := by
  unfold HardFine; infer_instance

structure UnitCell where
  parent : {c : FineCell // HardFine c}
  ti : Fin 4
  deriving DecidableEq, Fintype

def unitR (c : UnitCell) : ℕ := fineR c.parent.1
def unitY (c : UnitCell) : ℕ := fineY c.parent.1
def unitTlo (c : UnitCell) : ℕ := fineTlo c.parent.1 + 8 * c.ti.val
def unitThi (c : UnitCell) : ℕ := min (fineThi c.parent.1) (unitTlo c + 7)
def unitBox (c : UnitCell) : Box :=
  ⟨unitR c, unitY c, unitY c, unitTlo c, unitThi c⟩

/-- Proof-irrelevant presentation of a fine box, used to split the finite
receipt into independent rows without repeatedly enumerating nested
subtypes. -/
def fineBoxAt (c : CoarseCell) (yi ti : Fin 4) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    coarseTlo c + 32 * ti.val,
    min (coarseThi c) (coarseTlo c + 32 * ti.val + 31)⟩

/-- Proof-irrelevant presentation of a width-eight terminal box below a fine box. -/
def unitBoxAt (c : CoarseCell) (yi ti ui : Fin 4) : Box :=
  ⟨coarseR c, coarseYlo c + yi.val, coarseYlo c + yi.val,
    (coarseTlo c + 32 * ti.val) + 8 * ui.val,
    min (min (coarseThi c) (coarseTlo c + 32 * ti.val + 31))
      ((coarseTlo c + 32 * ti.val) + 8 * ui.val + 7)⟩

theorem fineBox_eq_fineBoxAt (c : FineCell) :
    fineBox c = fineBoxAt c.parent.1 c.yi c.ti := rfl

theorem unitBox_eq_unitBoxAt (c : UnitCell) :
    unitBox c = unitBoxAt c.parent.1.parent.1
      c.parent.1.yi c.parent.1.ti c.ti := rfl

abbrev Cell := CoarseCell ⊕ (FineCell ⊕ UnitCell)

def box : Cell → Box
  | .inl c => coarseBox c
  | .inr (.inl c) => fineBox c
  | .inr (.inr c) => unitBox c

def Leaf : Cell → Prop
  | .inl c => ¬ HardCoarse c
  | .inr (.inl c) => ¬ HardFine c
  | .inr (.inr _) => True

instance (c : Cell) : Decidable (Leaf c) := by
  rcases c with c | c
  · simp only [Leaf]; infer_instance
  · rcases c with c | c
    · simp only [Leaf]; infer_instance
    · simp only [Leaf]; infer_instance

def Valid (c : Cell) : Prop := (box c).valid ∧ Leaf c
instance (c : Cell) : Decidable (Valid c) := by unfold Valid; infer_instance

structure InCell (p : FlagDegree) (c : Cell) : Prop where
  all_eq : p.all = (box c).r
  ylo_le : (box c).ylo ≤ middle p
  middle_le_yhi : middle p ≤ (box c).yhi
  tlo_le : (box c).tlo ≤ total p
  total_le_thi : total p ≤ (box c).thi
  leaf : Leaf c

def coarseCellOf (p : FlagDegree) (hslo : 1 ≤ p.all) (hshi : p.all ≤ slopeCap)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) : CoarseCell :=
  (⟨p.all - 1, by
      change p.all ≤ 18 at hshi
      omega⟩,
    ⟨(middle p - p.all) / 4, by
      change middle p ≤ 85 at hy
      omega⟩,
    ⟨total p / 128, by
      change total p ≤ 2774 at ht
      omega⟩)

theorem coarseCellOf_bounds (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ slopeCap) (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) :
    p.all = coarseR (coarseCellOf p hslo hshi hy ht) ∧
      coarseYlo (coarseCellOf p hslo hshi hy ht) ≤ middle p ∧
      middle p ≤ coarseYhi (coarseCellOf p hslo hshi hy ht) ∧
      coarseTlo (coarseCellOf p hslo hshi hy ht) ≤ total p ∧
      total p ≤ coarseThi (coarseCellOf p hslo hshi hy ht) := by
  have hmy := all_le_middle p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change p.all = p.all - 1 + 1; omega
  · change (p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) ≤ middle p; omega
  · change middle p ≤ min ysCap
      ((p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) + 3)
    exact le_min hy (by omega)
  · change 128 * (total p / 128) ≤ total p; omega
  · change total p ≤ min totalCap (128 * (total p / 128) + 127)
    exact le_min ht (by omega)

def fineCellOf (p : FlagDegree) (c : CoarseCell) (hc : HardCoarse c)
    (hylo : coarseYlo c ≤ middle p) (hyhi : middle p ≤ coarseYhi c)
    (htlo : coarseTlo c ≤ total p) (hthi : total p ≤ coarseThi c) : FineCell :=
  ⟨⟨c, hc⟩, ⟨middle p - coarseYlo c, by
      have hcap : coarseYhi c ≤ coarseYlo c + 3 := Nat.min_le_right _ _
      omega⟩,
    ⟨(total p - coarseTlo c) / 32, by
      have hcap : coarseThi c ≤ coarseTlo c + 127 := Nat.min_le_right _ _
      omega⟩⟩

theorem fineCellOf_bounds (p : FlagDegree) (c : CoarseCell) (hc : HardCoarse c)
    (hylo : coarseYlo c ≤ middle p) (hyhi : middle p ≤ coarseYhi c)
    (htlo : coarseTlo c ≤ total p) (hthi : total p ≤ coarseThi c)
    (hr : p.all = fineR (fineCellOf p c hc hylo hyhi htlo hthi)) :
    p.all = fineR (fineCellOf p c hc hylo hyhi htlo hthi) ∧
      fineY (fineCellOf p c hc hylo hyhi htlo hthi) = middle p ∧
      fineTlo (fineCellOf p c hc hylo hyhi htlo hthi) ≤ total p ∧
      total p ≤ fineThi (fineCellOf p c hc hylo hyhi htlo hthi) := by
  refine ⟨hr, ?_, ?_, ?_⟩
  · simp only [fineY, fineCellOf]; omega
  · simp only [fineTlo, fineCellOf]; omega
  · simp only [fineThi]
    apply le_min hthi
    simp only [fineTlo, fineCellOf]
    omega

def unitCellOf (p : FlagDegree) (c : FineCell) (hc : HardFine c)
    (htlo : fineTlo c ≤ total p) (hthi : total p ≤ fineThi c) : UnitCell :=
  ⟨⟨c, hc⟩, ⟨(total p - fineTlo c) / 8, by
      have hcap : fineThi c ≤ fineTlo c + 31 := Nat.min_le_right _ _
      omega⟩⟩

theorem unitCellOf_bounds (p : FlagDegree) (c : FineCell) (hc : HardFine c)
    (htlo : fineTlo c ≤ total p) (hthi : total p ≤ fineThi c) :
    unitTlo (unitCellOf p c hc htlo hthi) ≤ total p ∧
      total p ≤ unitThi (unitCellOf p c hc htlo hthi) := by
  constructor
  · simp only [unitTlo, unitCellOf]
    omega
  · simp only [unitThi]
    apply le_min hthi
    simp only [unitTlo, unitCellOf]
    omega

def cellOf (p : FlagDegree) (hslo : 1 ≤ p.all) (hshi : p.all ≤ slopeCap)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) : Cell :=
  let c := coarseCellOf p hslo hshi hy ht
  if hc : HardCoarse c then
    let hb := coarseCellOf_bounds p hslo hshi hy ht
    let f := fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    if hf : HardFine f then
      let hfb := fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2 hb.1
      .inr (.inr (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2))
    else .inr (.inl f)
  else .inl c

theorem cellOf_bounds (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ slopeCap) (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) :
    InCell p (cellOf p hslo hshi hy ht) := by
  let c := coarseCellOf p hslo hshi hy ht
  have hb := coarseCellOf_bounds p hslo hshi hy ht
  by_cases hc : HardCoarse c
  · let f := fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    have hfb := fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2 hb.1
    by_cases hf : HardFine f
    · have hu := unitCellOf_bounds p f hf hfb.2.2.1 hfb.2.2.2
      simp only [cellOf, c, hc, dite_true, f, hf]
      refine ⟨hfb.1, hfb.2.1.le, hfb.2.1.symm.le, ?_, ?_, trivial⟩
      · change unitTlo (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2) ≤ total p
        exact hu.1
      · change total p ≤ unitThi (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2)
        exact hu.2
    · simp only [cellOf, c, hc, dite_true, f, hf]
      exact ⟨hfb.1, hfb.2.1.le, hfb.2.1.symm.le, hfb.2.2.1,
        hfb.2.2.2, by simpa only [Leaf]⟩
  · simp only [cellOf, c, hc, dite_false]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
      by simpa only [Leaf]⟩

theorem valid_of_inCell (p : FlagDegree) (c : Cell)
    (hy : middle p ≤ ysCap) (ht : total p ≤ totalCap) (h : InCell p c) : Valid c := by
  have hall := all_le_middle p
  have hmid := middle_le_total p
  have hrpos : 1 ≤ (box c).r := by
    rcases c with c | c
    · simp [box, coarseBox, coarseR]
    · rcases c with c | c
      · simp [box, fineBox, fineR, coarseR]
      · simp [box, unitBox, unitR, fineR, coarseR]
  have hry : (box c).r ≤ (box c).ylo := by
    rcases c with c | c
    · simp [box, coarseBox, coarseR, coarseYlo]
    · rcases c with c | c
      · simp [box, fineBox, fineR, fineY, coarseR, coarseYlo] <;> omega
      · simp [box, unitBox, unitR, unitY, fineR, fineY, coarseR, coarseYlo] <;> omega
  have hycap : (box c).yhi ≤ ysCap := by
    rcases c with c | c
    · simp [box, coarseBox, coarseYhi]
    · rcases c with c | c
      · have hlo := h.ylo_le
        have hhi := h.middle_le_yhi
        change fineY c ≤ middle p at hlo
        change middle p ≤ fineY c at hhi
        change fineY c ≤ ysCap
        omega
      · have hlo := h.ylo_le
        have hhi := h.middle_le_yhi
        change unitY c ≤ middle p at hlo
        change middle p ≤ unitY c at hhi
        change unitY c ≤ ysCap
        omega
  have htcap : (box c).thi ≤ totalCap := by
    rcases c with c | c
    · simp [box, coarseBox, coarseThi]
    · rcases c with c | c
      · exact (Nat.min_le_left _ _).trans (by simp [coarseThi])
      · change unitThi c ≤ totalCap
        exact (Nat.min_le_left _ _).trans
          ((Nat.min_le_left _ _).trans (by simp [coarseThi]))
  refine ⟨?_, h.leaf⟩
  exact ⟨hrpos, hry, h.ylo_le.trans h.middle_le_yhi, hycap,
    h.ylo_le.trans (hmid.trans h.total_le_thi),
    h.tlo_le.trans h.total_le_thi, htcap⟩

/-- The part of a slope-row receipt in a half-open coarse-Y interval. -/
def RowBandReceipt (ri : Fin 18) (lo hi : ℕ) : Prop :=
  ∀ (cy : Fin 22), lo ≤ cy.val → cy.val < hi → ∀ (ct : Fin 22),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) (lo hi : ℕ) : Decidable (RowBandReceipt ri lo hi) := by
  unfold RowBandReceipt
  infer_instance

/-- A rectangular coarse-Y/coarse-T part of a slope-row receipt. -/
def RowTileReceipt (ri : Fin 18) (ylo yhi tlo thi : ℕ) : Prop :=
  ∀ (cy : Fin 22), ylo ≤ cy.val → cy.val < yhi →
    ∀ (ct : Fin 22), tlo ≤ ct.val → ct.val < thi →
      let coarse : CoarseCell := (ri, cy, ct)
      FastHardCoarse coarse →
        ∀ (yi ti : Fin 4),
          ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
            ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
              (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) (ylo yhi tlo thi : ℕ) :
    Decidable (RowTileReceipt ri ylo yhi tlo thi) := by
  unfold RowTileReceipt
  infer_instance

/-- A receipt for one fixed coarse-Y cell and a half-open range of coarse-T
cells.  Unlike `RowTileReceipt`, its decision procedure does not enumerate
the other twenty-one values of `Fin 22`. -/
def FixedYReceipt (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ) : Prop :=
  ∀ (ct : Fin 22), tlo ≤ ct.val → ct.val < thi →
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ) :
    Decidable (FixedYReceipt ri cy tlo thi) := by
  unfold FixedYReceipt
  infer_instance

/-- Adapt a fixed-Y receipt to the existing singleton-Y tile interface. -/
theorem fixedYReceipt_to_rowTile (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ)
    (h : FixedYReceipt ri cy tlo thi) :
    RowTileReceipt ri cy.val (cy.val + 1) tlo thi := by
  intro cy' hylo hyhi ct htlo hthi
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct htlo hthi

/-- Adapt a full-total-range fixed-Y receipt to the existing singleton-Y band
interface. -/
theorem fixedYReceipt_to_rowBand (ri : Fin 18) (cy : Fin 22)
    (h : FixedYReceipt ri cy 0 22) :
    RowBandReceipt ri cy.val (cy.val + 1) := by
  intro cy' hylo hyhi ct
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct (Nat.zero_le _) ct.isLt

/-- A closed slope-row receipt.  Kernel reduction is deliberately split at
this level: each auxiliary lemma evaluates one eighteenth of the adaptive
grid and is cached before the next row starts. -/
def RowReceipt (ri : Fin 18) : Prop :=
  ∀ (cy : Fin 22) (ct : Fin 22),
    let coarse : CoarseCell := (ri, cy, ct)
    HardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) : Decidable (RowReceipt ri) := by
  unfold RowReceipt
  infer_instance

/-- A receipt-local propositionally equivalent row presentation. -/
def FastRowReceipt (ri : Fin 18) : Prop :=
  ∀ (cy : Fin 22) (ct : Fin 22),
    let coarse : CoarseCell := (ri, cy, ct)
    FastHardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ FastFits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits

instance (ri : Fin 18) : Decidable (FastRowReceipt ri) := by
  unfold FastRowReceipt
  infer_instance

theorem fastRowReceipt_to_rowReceipt (ri : Fin 18)
    (h : FastRowReceipt ri) : RowReceipt ri := by
  intro cy ct
  dsimp only
  intro hcoarse yi ti hfine ui hunit
  exact h cy ct
    ⟨hcoarse.1, fun hfast => hcoarse.2 (fastFits_to_fits _ hfast)⟩ yi ti
    ⟨hfine.1, fun hfast => hfine.2 (fastFits_to_fits _ hfast)⟩ ui hunit

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
