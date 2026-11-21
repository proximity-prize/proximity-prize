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
def rankMass (b : HighBand) : Mass :=
  if stopIndex b = 0 then history b 0
  else capMin (history b (stopIndex b - 1)) (stageCap b (stopIndex b) false)
def rankB (b : HighBand) : ℕ := (rankMass b 2).floor.toNat
def rankJ (b : HighBand) : ℕ := (rankMass b 1).floor.toNat
def cutShape (b : HighBand) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : HighBand) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def seedLimit (b : HighBand) : ℚ :=
  weightedBill (laterCount b+1) (cutWeight b 0) (history b)
def pointLimit (b : HighBand) : ℚ :=
  dotQ (running (cutWeight b 2) (laterCount b + 1))
    ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
def lossWeight (b : HighBand) (a h : ℕ → ℚ) (i : ℕ) : Mass :=
  fun k => a i * cutWeight b 0 i k + h i * cutWeight b 1 i k
def fixedFee (hi B J : ℕ) : ℕ :=
  let d := degreeAt hi
  let q := gap hi
  let lam : ℚ := (blockLength : ℚ) / agreement
  let mu : ℚ := ((blockLength-d : ℕ) : ℚ) / q
  let ap := mu + 2*lam*d*(B-1 : ℕ)
  let vp := min ap (lam*d*(2*J-1 : ℕ))
  (((B-J : ℕ) : ℚ)*vp + J*ap).ceil.toNat+B^2
def fixedBudget (b : HighBand) : ℕ :=
  let price (s : Shape) := fixedFee b.row.hi s.B s.J
  ∑ i ∈ Finset.range (stages b).length,
    (price (stageAt b i).free.shape + price (stageAt b i).moving.shape)
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
structure BankGuard (hi reserve : ℕ) (s : Shape) : Prop where
  ode : ODEGuard s.B s.J
  seed_small : s.U < p
  pos : 0 < s.m * agreement
  buffer : 2*hi*reserve ≤ fullCutoff s
structure ScheduleOK (b : HighBand) : Prop where
  stages_pos : 0 < (stages b).length
  zero : (stageAt b 0).reserve = 0
  later_pos : ∀ i < laterCount b, 0 < (stageAt b (i+1)).reserve
  small_reserve : ∀ i < (stages b).length, (stageAt b i).reserve < p
  stop_le : stopIndex b ≤ laterCount b
  intro_pos : ∀ i ∈ introIndices b, 0 < i ∧ i < (stages b).length
  intro_asc : (introIndices b).Pairwise (· < ·)
  stage_guard : ∀ i < (stages b).length,
    let s := stageAt b i
    BankGuard b.row.hi s.reserve s.free.shape ∧ BankGuard b.row.hi s.reserve s.moving.shape
  terminal_guard : BankGuard b.row.hi 0 (terminal b).shape
  initial_small : ∀ k, initialCap b k < p
  initial_e_ge : initialCap b 3 ≤ initialE b
  content_small : (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U < p
  rank_guard : ODEGuard (rankB b) (rankJ b)
  low_seed : (p+1)*initialCap b 2 + initialE b ≤ (fees b).lowSeed
  low_jet : initialCap b 0 + fixedFee b.row.hi (rankB b) (rankJ b) ≤ (fees b).lowJet
  fixed : fixedBudget b ≤ (fees b).fixedODE
  content : (p+1)*((stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U) ≤ (fees b).content
structure RateOK (hi : ℕ) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ) / 81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1 - a*g/((p+1 : ℕ) : ℚ)) * curveUnit hi g ≤ h
structure LossLedger (b : HighBand) : Prop where
  seed_small : seedLimit b < (p : ℚ)
  points : pointLimit b ≤ ((fees b).point : ℚ)
  discount : b.row.lo < 7773 →
    ∃ a h : ℕ → ℚ,
      (∀ i ≤ laterCount b, RateOK b.row.hi (a i) (h i) ∧
        min (seedLimit b) (dotQ (cutWeight b 0 i) (history b i)) ≤ a i) ∧
      weightedBill (laterCount b+1) (lossWeight b a h) (history b) + seedLimit b ≤
        ((fees b).loss : ℚ)
  direct : 7773 ≤ b.row.lo → ((p+1 : ℕ) : ℚ) * seedLimit b ≤ ((fees b).loss : ℚ)
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
open P3_7 (InBand stages terminal Source CurveTariff PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c4 : Prop := ∀ b : HighBand, LossLedger b
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
open P3_7_3 (stageAt initialCap initialE introIndices introAccount degreeVector rankB rankJ
  rankMass stopIndex history ODEGuard)
open P1_7_4 (cornerBound sharedBound pairMinSeed pairMinOrdinate)
open K1_14 (Shape)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
private def floorN (x : ℚ) : ℕ := x.floor.toNat
private theorem floorN_mono : Monotone floorN := by
  intro a b h
  exact Int.toNat_le_toNat (Int.floor_mono h)
private theorem floorN_cast (n : ℕ) : floorN (n : ℚ) = n := by
  change ⌊(n : ℚ)⌋.toNat = n
  rw [Int.floor_natCast, Int.toNat_natCast]
private theorem floorN_max (a b : ℚ) :
    floorN (max a b) = max (floorN a) (floorN b) :=
  floorN_mono.map_max
private theorem floorN_fold_max (xs : List ℚ) (a : ℚ) :
    floorN (xs.foldl max a) = (xs.map floorN).foldl max (floorN a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, floorN_max]
private theorem floorN_add_div (x y d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) :
    floorN ((x : ℚ)/d + (y : ℚ)/e) = (x*e+y*d)/(d*e) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have heq : (x : ℚ)/d + (y : ℚ)/e = ((x*e+y*d : ℕ) : ℚ)/(d*e : ℕ) := by
    push_cast
    field_simp
  rw [heq]
  change ⌊((x*e+y*d : ℕ) : ℚ)/(d*e : ℕ)⌋.toNat = _
  rw [Rat.floor_natCast_div_natCast]
  exact Int.toNat_natCast _
private def sharedNat (s t : Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) : ℕ :=
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  let a := highScale r k
  (highCap x z k*d + pairCap (residualShape s x z) (residualShape t x z) k*a)/(a*d)
private theorem floorN_shared (s t : Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4)
    (hr : 0 < r) (hm : r ≤ m) :
    floorN (sharedBound s t x z r m square k) = sharedNat s t x z r m square k := by
  have hn : 0 < m+1-r := by omega
  unfold sharedBound sharedNat
  apply floorN_add_div
  · fin_cases k <;> exact (by first | exact hr.ne' | exact pow_ne_zero 2 hr.ne')
  · split <;> first | exact hn.ne' | exact pow_ne_zero 2 hn.ne'
private def cornerNat (s t : Shape) (r m : ℕ) (square : Bool) (k : Fin 4) : ℕ :=
  let xs := [0, pairMinSeed s t]
  let zMax := pairMinOrdinate s t
  let zs := [0, zMax, min zMax (s.B-s.J), min zMax (t.B-t.J)]
  (xs.flatMap fun x => zs.map fun z => sharedNat s t x z r m square k).foldl max 0
private theorem floorN_corner (s t : Shape) (r m : ℕ) (square : Bool) (k : Fin 4)
    (hr : 0 < r) (hm : r ≤ m) :
    floorN (cornerBound s t r m square k) = cornerNat s t r m square k := by
  unfold cornerBound cornerNat
  rw [floorN_fold_max, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, floorN_shared _ _ _ _ _ _ _ _ hr hm]
  rfl
private theorem rank_at_zero (b : HighBand) :
    rankB b = initialCap b 2 ∧ rankJ b = initialCap b 1 := by
  change floorN (initialCap b 2 : ℚ) = _ ∧ floorN (initialCap b 1 : ℚ) = _
  exact ⟨floorN_cast _, floorN_cast _⟩
private theorem initial_eval (b : HighBand) (k : Fin 4) :
    initialCap b k =
      if (introIndices b).isEmpty then
        cornerNat (stageAt b 0).free.shape (stageAt b 0).moving.shape 1 1 false k
      else
        introAccount b k (introIndices b) (degreeVector (stageAt b 0).free.shape) (fun _ => 0) := by
  unfold initialCap
  split
  · exact floorN_corner _ _ _ _ _ _ (by decide) (by decide)
  · rfl
def initialNumbers : HighBand → Fin 4 → ℕ
  | .h2274 => ![6993, 82300, 395992, 2047524]
  | .h2294 => ![6465, 79363, 381243, 2044393]
  | .h7773 => ![132, 1268, 7340, 32000]
theorem initial_eq (b : HighBand) (k : Fin 4) : initialCap b k = initialNumbers b k := by
  rw [initial_eval]
  cases b <;> fin_cases k <;> rfl
theorem rank_eq (b : HighBand) :
    rankB b = initialNumbers b 2 ∧ rankJ b = initialNumbers b 1 :=
  ⟨(rank_at_zero b).1.trans (initial_eq b 2), (rank_at_zero b).2.trans (initial_eq b 1)⟩
end P3_7_3_3
end
section
namespace P3_7_3_3
open P3 (HighBand agreement blockLength)
open P3_7 (stages fees degreeAt gap scale muNum lambdaNum ceilRatio)
open P3_7_3 (fixedFee fixedBudget initialCap rankB rankJ)
open scoped BigOperators
private theorem sum_stages (s : List P3_7.Stage) (fallback : P3_7.Stage) (f : P3_7.Stage → ℕ) :
    (∑ i ∈ Finset.range s.length, f ((s[i]?).getD fallback)) = (s.map f).sum := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Nat.add_comm]
end P3_7_3_3
end
section
namespace P3_7_3_4
open P3 (p blockLength agreement)
open P3_7 (degreeAt gap curveUnit)
open P3_7_3 (RateOK)
abbrev Q : ℚ := ((p+1 : ℕ) : ℚ)
private def alpha (hi : ℕ) : ℚ := 1 + 2 * ((blockLength : ℚ) / agreement) * degreeAt hi
private def mu (hi : ℕ) : ℚ := ((blockLength - degreeAt hi : ℕ) : ℚ) / gap hi
private def drop (a : ℚ) := a / Q
private def quad (hi : ℕ) (a : ℚ) := 2 * alpha hi * drop a
private def slope (hi : ℕ) (a : ℚ) := 2 * alpha hi - (mu hi - alpha hi) * drop a
def raw (hi : ℕ) (a : ℚ) (g : ℕ) :=
  (1 - a * g / Q) * curveUnit hi g
private theorem raw_eq (hi : ℕ) (a : ℚ) (g : ℕ) :
    raw hi a g = -(quad hi a) * (g : ℚ)^2 + slope hi a * g + (mu hi - alpha hi) := by
  unfold raw curveUnit quad slope drop mu alpha
  ring
private theorem raw_le_peak (hi : ℕ) (a : ℚ) (g m : ℕ) (hg : 0 < g)
    (hquad : 0 ≤ quad hi a)
    (hleft : m = 1 ∨ quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)
    (hright : slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) :
    raw hi a g ≤ raw hi a m := by
  rw [raw_eq, raw_eq]
  rcases lt_trichotomy g m with h | rfl | h
  · have he : 0 ≤ (m : ℚ) - g := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : (g : ℚ) + m ≤ 2 * (m : ℚ) - 1 := by
      have hh : (g : ℚ) + 1 ≤ m := by exact_mod_cast h
      linarith only [hh]
    have hb : quad hi a * ((g : ℚ) + m) ≤ slope hi a := by
      rcases hleft with hm | hm
      · omega
      · exact (mul_le_mul_of_nonneg_left hgm hquad).trans hm
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
  · exact le_rfl
  · have he : 0 ≤ (g : ℚ) - m := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : 2 * (m : ℚ) + 1 ≤ (g : ℚ) + m := by
      have hh : (m : ℚ) + 1 ≤ g := by exact_mod_cast h
      linarith only [hh]
    have hb : slope hi a ≤ quad hi a * ((g : ℚ) + m) :=
      hright.trans (mul_le_mul_of_nonneg_left hgm hquad)
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
def rateCheck (hi : ℕ) (a h : ℚ) (m : ℕ) : Bool :=
  decide (Q/81 ≤ a) && decide (0 ≤ h) && decide (0 ≤ quad hi a) &&
    (decide (m = 1) || decide (quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)) &&
    decide (slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) && decide (raw hi a m ≤ h)
theorem rate_of_check {hi : ℕ} {a h : ℚ} {m : ℕ}
    (hc : rateCheck hi a h m = true) : RateOK hi a h := by
  simp only [rateCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨ha, hh⟩, hquad⟩, hl⟩, hr⟩, hp⟩
  refine ⟨ha, hh, fun g hg _ => ?_⟩
  by_cases hz : 0 ≤ 1 - a * g / Q
  · rw [max_eq_right hz]
    exact (raw_le_peak hi a g m hg hquad hl hr).trans hp
  · rw [max_eq_left (le_of_not_ge hz), zero_mul]
    exact hh
end P3_7_3_4
end
section
namespace P3_7_3_4
open P3 (HighBand p)
open P3_7 (fees)
open P3_7_3
open P1_7_4 (dotQ_mono_mass)
private theorem foldl_le_entry (f : ℕ → ℚ) (xs : List ℕ) (a : ℚ) {j : ℕ}
    (hj : j ∈ xs) : xs.foldl (fun z i => min z (f i)) a ≤ f j := by
  have floor (xs : List ℕ) (a : ℚ) : xs.foldl (fun z i => min z (f i)) a ≤ a := by
    induction xs generalizing a with
    | nil => exact le_rfl
    | cons i xs ih => exact (ih _).trans (min_le_left _ _)
  induction xs generalizing a with
  | nil => simp at hj
  | cons i xs ih =>
    rcases List.mem_cons.mp hj with rfl | hm
    · exact (floor xs _).trans (min_le_right _ _)
    · exact ih _ hm
private def corner (b : HighBand) (i r : ℕ) (k : Fin 4) : ℚ :=
  let s := stageAt b i
  cornerBound s.free.shape s.moving.shape r (s.reserve+1) (decide (stopIndex b ≤ i)) k
private theorem stage_le_corner (b : HighBand) (i r : ℕ) (k : Fin 4)
    (hp : 0 < r) (hr : r ≤ (stageAt b i).reserve + 1) :
    stageCap b i (decide (stopIndex b ≤ i)) k ≤ corner b i r k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  change ((List.range ((stageAt b i).reserve + 1)).foldl
    (fun a j => min a (corner b i (j+1) k)) (corner b i 1 k)) ≤ corner b i (j+1) k
  exact foldl_le_entry _ _ _ (List.mem_range.mpr (by omega))
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
theorem dot4_eq (v c : Mass) : dot4 v c = dotQ v c := by
  simp only [dotQ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl
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
private theorem multiplier_nonneg (b : HighBand) : 0 ≤ multiplier b := by
  unfold multiplier
  split
  · exact zero_le_one
  · exact Nat.cast_nonneg _
def jump (v : ℕ → Mass) (i : ℕ) (c : Mass) : ℚ :=
  dot4 (fun k => running v (i+1) k - running v i k) c
private theorem jump_bound (v : ℕ → Mass) (i : ℕ) {c d : Mass} (h : ∀ k, c k ≤ d k) :
    dotQ (fun k => running v (i+1) k - running v i k) c ≤ jump v i d := by
  rw [jump, dot4_eq]
  exact dotQ_mono_mass (fun _ => sub_nonneg.mpr (le_max_left _ _)) h
def seedPrice (xs : Receipt) (i : ℕ) : ℚ := (0x400000 * byte xs i 6 : ℕ)
def seedTotal (xs : Receipt) : ℕ → ℕ
  | 0 => 0
  | i+1 => seedTotal xs i + 0x400000 * byte xs i 6
def lossTotal (xs : Receipt) : ℕ → ℕ
  | 0 => 0
  | i+1 => lossTotal xs i + lossUnits xs i
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
private theorem RowsOK.at {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs n)
    {i : ℕ} (hi : i < n) : RowOK b xs i := h ⟨i, hi⟩
private theorem RowsOK.prev {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs (n+1)) :
    RowsOK b xs n := fun i => h i.castSucc
private theorem RowOK.threshold {b : HighBand} {xs : Receipt} {i : ℕ}
    (h : RowOK b xs i) (k : Fin 4) : byte xs i k ≤ (stageAt b i).reserve + 1 := by
  apply of_decide_eq_true
  fin_cases k
  · exact h.cap0
  · exact h.cap1
  · exact h.cap2
  · exact h.cap3
private theorem history_le {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs n)
    {i : ℕ} (hi : i < n) (k : Fin 4) : history b i k ≤ cap b xs i k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    change min (history b i k) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)) k) ≤
      (if byte xs (i+1) k = 0 then cap b xs i k else corner b (i+1) (byte xs (i+1) k) k)
    by_cases hr : byte xs (i+1) k = 0
    · rw [ite_eq_left hr]
      exact (min_le_left _ _).trans (ih (by omega))
    · rw [ite_eq_right hr]
      exact (min_le_right _ _).trans
        (stage_le_corner b (i+1) _ k (Nat.pos_of_ne_zero hr) ((h.at hi).threshold k))
private theorem seed_le {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs n) :
    weightedBill n (cutWeight b 0) (history b) ≤ (seedTotal xs n : ℚ) := by
  induction n with
  | zero => simp [weightedBill, seedTotal]
  | succ n ih =>
    have hn : n < n+1 := Nat.lt_succ_self n
    have hrow := h.at hn
    have hstep := (jump_bound (cutWeight b 0) n (history_le h hn)).trans
      (of_decide_eq_true hrow.seed)
    rw [weightedBill, Finset.sum_range_succ, ← weightedBill, seedTotal, Nat.cast_add]
    exact add_le_add (ih h.prev) hstep
private theorem loss_le {b : HighBand} {xs : Receipt} {n : ℕ} (h : RowsOK b xs n) :
    multiplier b * weightedBill n (cutWeight b 0) (history b) +
      weightedBill n (rates b xs) (history b) ≤ (lossTotal xs n : ℚ) / 256 := by
  induction n with
  | zero => simp [weightedBill, lossTotal]
  | succ n ih =>
    have hn : n < n+1 := Nat.lt_succ_self n
    have hs := jump_bound (cutWeight b 0) n (history_le h hn)
    have hr := jump_bound (rates b xs) n (history_le h hn)
    have hstep := (add_le_add (mul_le_mul_of_nonneg_left hs (multiplier_nonneg b)) hr).trans
      (of_decide_eq_true (h.at hn).loss)
    have hprev := ih h.prev
    simp only [weightedBill, Finset.sum_range_succ, mul_add] at hprev ⊢
    rw [lossTotal, Nat.cast_add, add_div]
    linarith only [hprev, hstep]
private theorem zero_bill (n : ℕ) (m : ℕ → Mass) :
    weightedBill n (fun _ _ => 0) m = 0 := by
  have zero_running (i : ℕ) (k : Fin 4) : running (fun _ _ => 0) i k = 0 := by
    induction i with
    | zero => rfl
    | succ i ih => change max (running (fun _ _ => 0) i k) 0 = 0; rw [ih, max_self]
  simp [weightedBill, dotQ, zero_running]
def pointCap (b : HighBand) : Mass :=
  ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
theorem ledger_of_band {b : HighBand} {xs : Receipt} (s l pt : ℕ)
    (rows : RowsOK b xs (laterCount b+1))
    (hsn : seedTotal xs (laterCount b+1) = s)
    (hln : lossTotal xs (laterCount b+1) = l)
    (hpt : dot4 (running (cutWeight b 2) (laterCount b+1)) (pointCap b) = (pt : ℚ))
    (hs : s < p) (hl : l ≤ 256 * (fees b).loss) (hp : pt ≤ (fees b).point) :
    LossLedger b := by
  let n := laterCount b+1
  have hseed := seed_le rows
  rw [hsn] at hseed
  change seedLimit b ≤ (s : ℚ) at hseed
  have hpoint : pointLimit b ≤ ((fees b).point : ℚ) := by
    exact ((dot4_eq _ _).symm.trans hpt).le.trans (by exact_mod_cast hp)
  have hfee : multiplier b * seedLimit b + weightedBill n (rates b xs) (history b) ≤
      ((fees b).loss : ℚ) := by
    refine (loss_le rows).trans ((div_le_iff₀ (by norm_num)).mpr ?_)
    rw [hln, mul_comm]
    exact_mod_cast hl
  refine ⟨hseed.trans_lt (by exact_mod_cast hs), hpoint, ?_, ?_⟩
  · intro hb
    have hb' : discounted b := hb
    refine ⟨degreeRate b xs, heightRate b xs, ?_, ?_⟩
    · intro i hi
      have hin : i < n := by dsimp [n]; omega
      have hr := (rows.at hin).rate
      simp only [rateRow, ite_eq_left hb', Bool.and_eq_true, decide_eq_true_eq] at hr
      refine ⟨rate_of_check hr.1, (min_le_right _ _).trans ?_⟩
      exact (dotQ_mono_mass (fun _ => Nat.cast_nonneg _) (history_le rows hin)).trans
        (dot4_eq _ _ ▸ hr.2)
    · rw [multiplier, ite_eq_left hb', one_mul, rates, ite_eq_left hb', add_comm] at hfee
      exact hfee
  · intro hb
    have hb' : ¬ discounted b := not_lt.mpr hb
    rwa [multiplier, ite_eq_right hb', rates, ite_eq_right hb', zero_bill, add_zero] at hfee
end P3_7_3_4
end
section
namespace P3_7_3_4
open P3_7_3 (LossLedger)
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
local notation "r!" => (RowOK.mk (by decide) (by decide) (by decide) (by decide)
  (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl))
private def r1 : Receipt := [
  0x76be718fde453fdd2a060000000000, 0x2986abace0f480b04070000000001, 0x1784cb1e19d0f9802081001010101, 0x1716f398614599902091201000101,
  0xf4baacc2976f8902091200020101, 0x15bbf8da55a5650020b1602020101, 0x28362d195ab56d5030b1602020101, 0x3bc0bedb05a94fc030e1c03030101,
  0x1770395dcd86fb5020e1c04050101, 0x316e191f1676b7603122404050100, 0x2f8f27306eeb1cc02122400070202, 0x72496b7fac209b503122400090202,
  0x31ec348fad9716704130000000003, 0x9178b400700abf2050e1c0c0e0400, 0x14fbe05d0470f8be090b0011140500, 0x14561aa3f90dbe9e07090000220900]
private theorem b1 : LossLedger .h2274 :=
  ledger_of_band (xs := r1) 0x17c00000 0xc904390c91470e24 0x17d3980110
    (by intro i; fin_cases i <;> exact r!) rfl rfl (by with_unfolding_all rfl)
    (by decide) (by decide) (by decide)
private def r2 : Receipt := [
  0x5ee5c43a66e55e6425070000000000, 0x3a5c07e79bdd5ce03080000000001, 0x184f70634e9000202081001010101, 0x13afe294a0faf9c02091201000101,
  0x1c402bb5a349151020b1602020101, 0xc043cd74670fa5010b1602020101, 0x36e746bddd0d225030e1c02020101, 0x32eb5181b8562e1030e1c03030101,
  0x13cb1a19455d747010e1c00050101, 0x2dd72da2a7c8b6102122404050100, 0x3299782c939c4f303122400070202, 0x7892245669720bc021a0000090202,
  0x577f64c8ad174db030e1c00000003, 0x37f9efc3f3b69b2040e1c00000004, 0x3ae34f4aa7feff30510000c0e0300, 0x46107a89c5daa8f030f0000150500,
  0xb232845952d10f5050c00001a0600, 0x1f45e2ebb519ff6f0a09001e220900]
private theorem b2 : LossLedger .h2294 :=
  ledger_of_band (xs := r2) 0x16c00000 0xb8a9a55071628b96 0x19d622fd92
    (by intro i; fin_cases i <;> exact r!) rfl rfl (by with_unfolding_all rfl)
    (by decide) (by decide) (by decide)
private def r3 : Receipt := [
  0x14c0ea8053ab00001000000000000, 0x6626ebac467e0001000002020101, 0x777e40e01aa00b01000003030101, 0x358afafcdf619801000005050202]
private theorem b3 : LossLedger .h7773 :=
  ledger_of_band (xs := r3) 16777216 0x25f3ecf8e7b2fa3 15469025
    (by intro i; fin_cases i <;> exact r!) rfl rfl (by with_unfolding_all rfl)
    (by decide) (by decide) (by decide)
theorem proof : P3_7_3.c4 := by
  intro b
  cases b with
  | h2274 => exact b1
  | h2294 => exact b2
  | h7773 => exact b3
end P3_7_3_4
end
