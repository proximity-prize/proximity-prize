import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.UpperBranch8
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
abbrev Mass := Fin 4 → ℚ
def massQ (S : Finset (Ideal Ambient)) : Mass := fun k => mass S k
def dotQ (a c : Mass) : ℚ := ∑ k, a k * c k
def capMin (a c : Mass) : Mass := fun k => min (a k) (c k)
def pairMinSeed (s t : Shape) : ℕ := min s.U t.U
def pairMinOrdinate (s t : Shape) : ℕ := min s.B t.B
def sharedBound (s t : Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
def cornerBound (s t : Shape) (r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let xs := [0, pairMinSeed s t]
  let zMax := pairMinOrdinate s t
  let zs := [0, zMax, min zMax (s.B-s.J), min zMax (t.B-t.J)]
  (xs.flatMap fun x => zs.map fun z => sharedBound s t x z r m square k).foldl max 0
def pairedCap (s t : Shape) (reserve : ℕ) (square : Bool) : Mass :=
  fun k =>
    let m := reserve+1
    (List.range m).foldl
      (fun a r => min a (cornerBound s t (r+1) m square k))
      (cornerBound s t 1 m square k)
def PairedMass : Prop :=
  ∀ (s t : Shape) (r : ℕ) (square : Bool) (P Q : Jet),
    0 < r → r < p → s.B < p → t.B < p → s.U < p → t.U < p →
    s.J ≤ s.B → t.J ≤ t.B → P ≠ 0 → Q ≠ 0 →
    K1_14_3.RowCaps P s → K1_14_3.RowCaps Q t → K1_14_3.NoMovingCommon P Q →
    ∀ (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient)),
    (square = true → ∀ I ∈ S, K1_14_2_2.dual I) →
    (∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      K1_14_2_2.orderOn I P (r+1) ∧ K1_14_2_2.orderOn I Q (r+1)) →
    ∀ k, massQ S k ≤ pairedCap s t r square k
def stageAt (b : HighBand) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
theorem stage_mem {b : HighBand} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b := by
  rw [stageAt, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def laterCount (b : HighBand) := (stages b).length - 1
def introIndices : HighBand → List ℕ
  | .h2370 | .h2390 | .h2420 | .h2440 => List.range' 1 11
  | .h2410 => List.range' 1 9 ++ [11]
  | .h2460 | .h2480 | .h2500 | .h2520 | .h2530 | .h2540 |
    .h2550 | .h2560 | .h2570 | .h2585 | .h2590 | .h2600 | .h2601 | .h2611 |
    .h2621 | .h2640 | .h2670 | .h2700 | .h2750 | .h2800 | .h2900 | .h2950 |
    .h2980 | .h3000 | .h3050 | .h3100 | .h3200 | .h3400 | .h3555 => List.range' 1 8
  | _ => []
def stopIndex : HighBand → ℕ
  | .h4000 => 2
  | .h4800 => 1
  | _ => 0
def degreeVector (s : Shape) : Fin 3 → ℕ := ![s.B, s.J, s.U]
def introWeight (s : Shape) (k : Fin 4) : Fin 3 → ℕ :=
  ![![s.J, s.B-s.J, 0], ![0, s.U, s.J], ![s.U, 0, s.B], ![0, 0, s.U]] k
def introJump (cap old : Fin 3 → ℕ) (s : Shape) (k : Fin 4) : ℕ :=
  ∑ j, (max (old j) (introWeight s k j) - old j) * cap j
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
def envelope (s : Stage) : Shape :=
  let a := s.free.shape
  let b := s.moving.shape
  let j := max a.J b.J
  ⟨0, max (a.B-a.J) (b.B-b.J) + j, j, max a.U b.U⟩
def cutShape (b : HighBand) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : HighBand) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def running (v : ℕ → Mass) : ℕ → Mass
  | 0 => fun _ => 0
  | i+1 => fun k => max (running v i k) (v i k)
def weightedBill (n : ℕ) (v : ℕ → Mass) (hist : ℕ → Mass) : ℚ :=
  ∑ i ∈ Finset.range n, dotQ (fun k => running v (i+1) k - running v i k) (hist i)
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
  let a := 1 + (2*d-3)*(B-1)
  let v := min a ((2*d-3)*(J-1)+d)
  let published := ((blockLength-agreement)*((B-J)*v+J*a)+(q-1))/q+B^2
  let lam : ℚ := (blockLength : ℚ) / agreement
  let mu : ℚ := ((blockLength-d : ℕ) : ℚ) / q
  let ap := mu + 2*lam*d*(B-1 : ℕ)
  let vp := min ap (lam*d*(2*J-1 : ℕ))
  let persistent := (((B-J : ℕ) : ℚ)*vp + J*ap).ceil.toNat+B^2
  min published persistent
def fixedBudget (b : HighBand) : ℕ :=
  let price (s : Shape) := fixedFee b.row.hi s.B s.J
  ∑ i ∈ Finset.range (stages b).length,
    (price (stageAt b i).free.shape + price (stageAt b i).moving.shape)
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), K1_14_2.toJet P ∈ I
def PairPass {h rows s} (pair : P1_7.BufferedPair h rows s) (I : Ideal Ambient) : Prop :=
  BankPass rows s.free.shape I ∧ BankPass rows s.moving.shape I ∧
    K1_14_2_2R.chainCompatible pair.free pair.moving I
structure ODEGuard (B J : ℕ) : Prop where
  bmin : 2 ≤ B
  jpos : 0 < J
  jb : J ≤ B
  small : B < p
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
  degree : ((p+1 : ℕ) : ℚ) / 80 ≤ a
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
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace P1_7_4
noncomputable section
open P1 (HighBand)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
open scoped BigOperators Classical
theorem massQ_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    massQ S k ≤ massQ T k := by
  exact (Nat.cast_le (α := ℚ)).mpr (K1_14_2_2.mass_mono h k)
theorem massQ_nonneg (S : Finset (Ideal Ambient)) (k : Fin 4) : 0 ≤ massQ S k :=
  Nat.cast_nonneg _
theorem massQ_split {S T : Finset (Ideal Ambient)} (h : T ⊆ S) (k : Fin 4) :
    massQ (S \ T) k + massQ T k = massQ S k := by
  unfold massQ
  exact_mod_cast (Finset.sum_sdiff h :
    mass (S \ T) k + mass T k = mass S k)
theorem dotQ_nonneg {v c : Mass} (hv : ∀ k, 0 ≤ v k) (hc : ∀ k, 0 ≤ c k) :
    0 ≤ dotQ v c :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (hc k)
theorem dotQ_mono_mass {v c d : Mass} (hv : ∀ k, 0 ≤ v k) (h : ∀ k, c k ≤ d k) :
    dotQ v c ≤ dotQ v d :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hv k)
theorem dotQ_mono_weight {v w c : Mass} (hc : ∀ k, 0 ≤ c k) (h : ∀ k, v k ≤ w k) :
    dotQ v c ≤ dotQ w c :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (hc k)
theorem dotQ_scale_add (a h : ℚ) (v w x : Mass) :
    a * dotQ v x + h * dotQ w x = dotQ (fun k => a*v k + h*w k) x := by
  simp only [dotQ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
theorem cutWeight_nonneg (b : HighBand) (fee : Fin 3) (i : ℕ) (k : Fin 4) :
    0 ≤ cutWeight b fee i k := Nat.cast_nonneg _
theorem dot_cast (b : HighBand) (fee : Fin 3) (i : ℕ) (S : Finset (Ideal Ambient)) :
    ((K1_14_2_2.dot (K1_14_2_2.weight (cutShape b i) fee) (mass S) : ℕ) : ℚ) =
      dotQ (cutWeight b fee i) (massQ S) := by
  simp only [dotQ, K1_14_2_2.dot, cutWeight, massQ, Nat.cast_sum, Nat.cast_mul]
theorem history_le_initial (b : HighBand) (i : ℕ) (k : Fin 4) :
    history b i k ≤ initialCap b k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (min_le_left _ _).trans ih
private theorem running_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v i k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact ih.trans (le_max_left _ _)
private theorem jump_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v (i+1) k - running v i k :=
  sub_nonneg.mpr (le_max_left _ _)
private theorem running_succ_dot (v : ℕ → Mass) (i : ℕ) (c : Mass) :
    dotQ (running v (i+1)) c = dotQ (running v i) c +
      dotQ (fun k => running v (i+1) k - running v i k) c := by
  unfold dotQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private theorem pay_one (v : ℕ → Mass) (hist : ℕ → Mass) (i : ℕ)
    {S T U : Finset (Ideal Ambient)} (hT : T ⊆ S) (hU : U ⊆ S \ T)
    (hcap : ∀ k, massQ S k ≤ hist i k) :
    dotQ (v i) (massQ U) + dotQ (running v (i+1)) (massQ T) ≤
      dotQ (running v i) (massQ S) +
        dotQ (fun k => running v (i+1) k - running v i k) (hist i) := by
  have hleft : dotQ (v i) (massQ U) ≤ dotQ (running v (i+1)) (massQ (S \ T)) :=
    (dotQ_mono_weight (massQ_nonneg U) (fun k => le_max_right _ _)).trans
      (dotQ_mono_mass (running_nonneg v (i+1)) (massQ_mono hU))
  have hsplit :
      dotQ (running v (i+1)) (massQ (S \ T)) + dotQ (running v (i+1)) (massQ T) =
        dotQ (running v (i+1)) (massQ S) := by
    unfold dotQ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_add, massQ_split hT]
  calc
    _ ≤ _ := add_le_add hleft le_rfl
    _ = _ := hsplit
    _ = _ := running_succ_dot v i _
    _ ≤ _ := add_le_add le_rfl (dotQ_mono_mass (jump_nonneg v i) hcap)
theorem bill_bound (n : ℕ) (v hist : ℕ → Mass)
    (live lost : ℕ → Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ hist i k) :
    (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) ≤ weightedBill n v hist := by
  have h :
      (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) +
        dotQ (running v n) (massQ (live n)) ≤ weightedBill n v hist := by
    induction n with
    | zero => simp [running, dotQ, weightedBill]
    | succ n ih =>
      have old := ih (fun i hi => next i (by omega)) (fun i hi => fail i (by omega))
        (fun i hi => cap i (by omega))
      have step := pay_one v hist n (next n (by omega)) (fail n (by omega)) (cap n (by omega))
      unfold weightedBill at old ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  exact (le_add_of_nonneg_right (dotQ_nonneg (running_nonneg v n) (massQ_nonneg _))).trans h
theorem flat_bill (n : ℕ) (v : ℕ → Mass) (c : Mass) :
    weightedBill n v (fun _ => c) = dotQ (running v n) c := by
  induction n with
  | zero => simp [weightedBill, running, dotQ]
  | succ n ih =>
    rw [weightedBill, Finset.sum_range_succ, ← weightedBill, ih, running_succ_dot]
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p agreement)
open P1_7 (Stage Listed Source InBand stages terminal fullCutoff buffered window_nat)
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052
open private seed_value_eq from ProximityPrize.SubmissionLower.Fast052
open private parent_caps from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical
abbrev StageIndex (b : HighBand) := Fin (stages b).length
def pairAt {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) :
    P1_7.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
theorem free_listed {b : HighBand} (i : StageIndex b) : Listed b (stageAt b i).free :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inl rfl⟩)
theorem moving_listed {b : HighBand} (i : StageIndex b) : Listed b (stageAt b i).moving :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inr rfl⟩)
theorem bank_zero {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) {t : P1_7.Bank} (ht : Listed b t)
    (hpos : 0 < t.shape.m * agreement) {P : Jet} {W : ℕ}
    (hW : W ≤ fullCutoff t.shape) (hP : P ∈ rows t.shape W) :
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 :=
  src.necessary t ht W (by unfold fullCutoff at hW; omega) P hP
private theorem buffer_spend {b w} (hw : InBand b w) {r : ℕ} {s : Shape}
    (guard : BankGuard b.row.hi r s) :
    buffered w.toNat r s + 2*w.toNat*r ≤ fullCutoff s := by
  have h := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 (window_nat hw).2)
  have h' := h.trans guard.buffer
  unfold buffered
  omega
theorem intro_zero {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead) {t : P1_7.Bank}
    (ht : Listed b t) {r : ℕ} (guard : BankGuard b.row.hi r t.shape)
    {P : Jet} (hP : P ∈ rows t.shape (buffered M.overhead.toNat r t.shape))
    (i : Fin 2) (a : ℕ) (ha : a ≤ r) :
    ∀ γ ∈ Γ, jetAt (seedHasse i a P) (M.label γ) (F.scalar γ) = 0 := by
  apply bank_zero src ht guard.pos _ (src.shift t ht _ _ hP i a)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ ha) _).trans (buffer_spend hw guard)
structure FixedRows {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
def fixedRows {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (pairs : P1_7.Pairs b M.overhead.toNat rows)
    (i : StageIndex b) : FixedRows pairs i :=
  let pair := pairAt pairs i
  ⟨Classical.choice (K1_14_2_2_1.proof _ _ pair.free_ne
      (src.shape _ (free_listed i) _ _ pair.free_mem)),
    Classical.choice (K1_14_2_2_1.proof _ _ pair.moving_ne
      (src.shape _ (moving_listed i) _ _ pair.moving_mem))⟩
theorem fixed_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (hm : OnParent F I γ) (hG : fixedOn G I) :
    K1_14_2.fixedAt G (F.scalar γ) = 0 := by
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (hm hG)
theorem on_surface {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} (hI : I.IsPrime) {γ : K} (hm : OnParent F I γ) :
    P1_7.MarkOn M F (P0_10R.Bridge.surfaceOf I hI) γ := by
  intro P hP
  apply RingHom.mem_ker.mpr
  change jetAt P (M.label γ) (F.scalar γ) = 0
  rw [← eval_toJet]
  exact RingHom.mem_ker.mp (hm hP)
theorem surface_pass {h rows s} {pair : P1_7.BufferedPair h rows s}
    {I : Ideal Ambient} (hI : I.IsPrime) (hp : PairPass pair I) :
    P1_7.PairPass pair (P0_10R.Bridge.surfaceOf I hI) :=
  ⟨hp.1, hp.2.1, hp.2.2⟩
theorem rank_equation (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ ¬ dual I) {B J : ℕ}
    (hord : mass S 1 ≤ J) (hmix : mass S 2 ≤ B) :
    ∃ G : ODE, ODECaps G B J ∧ ∀ I ∈ S, fixedOn G I := by
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps K1_14_2_2_5_1.proof K1_14_2_2_5_2.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hp := K1_14_2_2_5.product_caps S G (fun I => sectionDegree I 2)
    (fun I => sectionDegree I 1) (fun I hI => (hG I hI).1)
  exact ⟨∏ I ∈ S, G I, ⟨hp.1, hp.2.1.trans hord, fun j i h => (hp.2.2 j i h).trans hmix⟩,
    fun I hI => K1_14_2_2_5.product_fixedOn hI G (hG I hI).2⟩
private theorem shifted_contact {A : Type*} [CommRing A] (a : K1_14.Seeds →+* A)
    {rows : Banks} {s : Shape} {I : Ideal Ambient} {h W r : ℕ} {P : Jet}
    (hn : ∀ W W', W ≤ W' → rows s W ≤ rows s W')
    (hs : K1_14_3.SeedShift h rows s) (hv : BankPass rows s I)
    (hcut : W + 2*h*r ≤ fullCutoff s) (hP : P ∈ rows s W) :
    fibreContact (I.map (specializeJets a)) (specializeJets a (toJet P)) r := by
  intro t ht
  rw [← specialize_shiftedWord]
  apply Ideal.mem_map_of_mem
  exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
    (shift_word hs hP t))
theorem buffered_order {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    {t : P1_7.Bank} (ht : Listed b t) {r : ℕ}
    (guard : BankGuard b.row.hi r t.shape) (hr : r < p)
    {I : Ideal Ambient} (hactive : Active I) (hv : BankPass rows t.shape I)
    {P : Jet} (hP : P ∈ rows t.shape (buffered M.overhead.toNat r t.shape)) :
    orderOn I P (r+1) := by
  classical
  have hn := src.nested t ht t ht rfl rfl rfl le_rfl
  have hcut := buffer_spend hw guard
  by_cases hd : dual I
  · have hc := shifted_contact (algebraMap K1_14.Seeds SeedField) hn
      (src.shift t ht) hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (K1_14_2_2_3_1.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ r hr hc)
  · obtain ⟨g, hg, hdeg, he⟩ := K1_14_2_2_3_2.proof I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP K1_14.FX p := charP_of_injective_ringHom seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc := shifted_contact (jetImageMap I) hn (src.shift t ht) hv hcut hP
    change fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) r at hc
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg hr hc
private theorem envelope_caps {s : Stage} {P : Jet}
    (hb : s.free.shape.J ≤ s.free.shape.B) (hc : s.moving.shape.J ≤ s.moving.shape.B)
    (hP : RowCaps P s.free.shape ∨ RowCaps P s.moving.shape) : RowCaps P (envelope s) := by
  have ha : s.free.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hb).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hd : s.moving.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hc).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i h
  rcases hP with hp | hp
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans ha, hj.trans (le_max_left _ _), hu.trans (le_max_left _ _)⟩
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans hd, hj.trans (le_max_right _ _), hu.trans (le_max_right _ _)⟩
theorem failed_bank {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) {t : P1_7.Bank} (ht : Listed b t)
    (hpos : 0 < t.shape.m * agreement) {I : Ideal Ambient} (hf : ¬ BankPass rows t.shape I) :
    ∃ P : Jet, RowCaps P t.shape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  unfold BankPass at hf
  push Not at hf
  obtain ⟨P, hP, hprop⟩ := hf
  exact ⟨P, src.shape t ht _ P hP, hprop, bank_zero src ht hpos le_rfl hP⟩
theorem failed_pair {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (sched : ScheduleOK b)
    (pairs : P1_7.Pairs b M.overhead.toNat rows) (i : StageIndex b) {I : Ideal Ambient}
    (hf : ¬ PairPass (pairAt pairs i) I) :
    ∃ P : Jet, RowCaps P (envelope (stageAt b i)) ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  let s := stageAt b i
  let pair := pairAt pairs i
  obtain ⟨ga, gc⟩ := sched.stage_guard i i.isLt
  have liftCaps {P : Jet} (h : RowCaps P s.free.shape ∨ RowCaps P s.moving.shape) :
      RowCaps P (envelope s) := envelope_caps ga.ode.jb gc.ode.jb h
  by_cases hP : BankPass rows s.free.shape I
  · by_cases hQ : BankPass rows s.moving.shape I
    · have htest : ¬ K1_14_2_2R.chainCompatible pair.free pair.moving I :=
        fun h => hf ⟨hP, hQ, h⟩
      unfold K1_14_2_2R.chainCompatible at htest
      push Not at htest
      obtain ⟨f, _, _, _, hdiv, hmem, g, a, hclear, hproper⟩ := htest
      have hcaps := src.shape _ (moving_listed i) _ _ pair.moving_mem
      have hG := K1_14_3R.chainCutter_caps_of_dvd pair.moving_ne hcaps gc.ode.jpos hdiv hclear
      refine ⟨K1_14_3R.chainCutter g, liftCaps (Or.inr hG), hproper, ?_⟩
      intro γ _ hγ
      apply K1_14_3R.chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hγ hmem)
      simpa only [eval_toJet, jetAt, eval₂_C, coe_eval₂RingHom, K1_14.atMark] using hz
    · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (moving_listed i) gc.pos hQ
      exact ⟨P, liftCaps (Or.inr hcaps), hproper, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (free_listed i) ga.pos hP
    exact ⟨P, liftCaps (Or.inl hcaps), hproper, fun γ hγ _ => hzero γ hγ⟩
private theorem mark_on_cut {I : Ideal Ambient} {P : Jet} {z : K} {S : K[X]}
    (hI : OnJet I z S) (hzero : jetAt P z S = 0) :
    ∃ Q ∈ cutComponents I P, OnJet Q z S := by
  let e := jetMarkHom z S
  have hle : I ⊔ Ideal.span {toJet P} ≤ RingHom.ker e := by
    apply sup_le hI
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans hzero))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, hQ, hmark⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr hQ, hmark⟩
theorem proper_cut {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) {I : Ideal Ambient} {P : Jet} (hs : s.J ≤ s.B) (hI : Active I)
    (hcaps : RowCaps P s) (hprop : toJet P ∉ I) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 →
        γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnParent F Q)
  let direct := (constantComponents I P).biUnion marked
  have hcard : direct.card ≤ (constantComponents I P).card := by
    have hsingle (Q : Ideal Ambient) (hQ : Q ∈ constantComponents I P) :
        (marked Q).card ≤ 1 := by
      obtain ⟨hcomp, hconst⟩ := Finset.mem_filter.mp hQ
      let _ : Q.IsPrime := (cutComponent_curve hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq hconst (Finset.mem_filter.mp hγ).2).trans
        (seed_value_eq hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q ∈ constantComponents I P, (marked Q).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ constantComponents I P, 1 := Finset.sum_le_sum hsingle
      _ = _ := by simp
  let C : CutCover :=
    ⟨direct, movingComponents I P, by
      intro Q hQ
      obtain ⟨hcomp, hmov⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hdim⟩ := cutComponent_curve hI hprop hcomp
      exact ⟨hp, hdim, K1_14_2_2_7_1.proof Q hp hdim hmov⟩⟩
  refine ⟨C, ?_, ?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s I P hs hI hcaps hprop
    · exact P0_10R.Bridge.cut_ordinate_mass s I P hs hI hcaps hprop
    · exact hcard.trans (P0_10R.Bridge.cut_constant_count s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    obtain ⟨Q, hQ, hQmark⟩ := mark_on_cut hmark hzero
    by_cases ht : ConstantSeed Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, Finset.mem_filter.mpr ⟨hγ, hQmark⟩⟩)
    · exact Or.inr ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, hQmark⟩
theorem combined_cuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape) (hs : s.J ≤ s.B)
    (ha : ∀ I ∈ A, Active I)
    (hcut : ∀ I ∈ A, ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent F I γ) → γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have hex (I : Ideal Ambient) (hI : I ∈ A) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
        ∀ γ ∈ Γ, OnParent F I γ → γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
    obtain ⟨P, hp, hprop, hzero⟩ := hcut I hI
    obtain ⟨C, hc, hmarks⟩ := proper_cut F s hs (ha I hI) hp hprop
    exact ⟨C, hc, fun γ hγ hm => hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I : Ideal Ambient) : CutCover :=
    if hI : I ∈ A then Classical.choose (hex I hI) else emptyCut
  have hC (I : Ideal Ambient) (hI : I ∈ A) :
      (∀ fee, (C I).cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → γ ∈ (C I).direct ∨ ∃ Q ∈ (C I).curves, OnParent F Q γ := by
    simpa only [C, dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨joinCuts A C, ?_, ?_⟩
  · intro fee
    calc
      _ ≤ ∑ I ∈ A, (C I).cost fee := joinCuts_cost A C fee
      _ ≤ ∑ I ∈ A, dot (weight s fee) (sectionDegree I) :=
        Finset.sum_le_sum (fun I hI => (hC I hI).1 fee)
      _ = _ := sum_dot _ _
  · rintro γ hγ ⟨I, hI, hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q, hQ, hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I, hI, hd⟩)
    · exact Or.inr ⟨Q, Finset.mem_biUnion.mpr ⟨I, hI, hQ⟩, hmark⟩
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p)
open P1_7 (CurveTariff curveUnit)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open private on_root on_seed moving_graph_count seed_graph_count equal_image_degree
  union_card_le from ProximityPrize.SubmissionLower.Fast062
open scoped BigOperators Classical
private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
def curveMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) (C : CutCover) :
    Finset K := C.curves.biUnion fun I => Γ.filter (OnParent F I)
theorem mem_curveMarks {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {C : CutCover} {γ : K} (hγ : γ ∈ Γ) {I : Ideal Ambient} (hI : I ∈ C.curves)
    (hm : OnParent F I γ) : γ ∈ curveMarks F C :=
  Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnParent F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : AnchorModel u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnParent F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnParent F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
theorem direct_curve_count {u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (C : CutCover) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(C.cost 0 : ℚ) := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      (Γ.filter (OnParent F I)).card ≤ (p+1)*seedLength I := by
    obtain ⟨f, hf, he, _, hd⟩ := K1_14_2_3_1.proof I (seed_slice (C.geometric I hI))
    have hle : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    exact (direct_count F hf.ne_zero he ((hd.trans hle).trans_lt hp)).trans
      (Nat.mul_le_mul_left _ hd)
  have h : (curveMarks F C).card ≤ (p+1)*C.cost 0 := calc
    _ ≤ ∑ I ∈ C.curves, (Γ.filter (OnParent F I)).card := Finset.card_biUnion_le
    _ ≤ ∑ I ∈ C.curves, (p+1)*seedLength I := Finset.sum_le_sum hcount
    _ = _ := by rw [← Finset.mul_sum, hsum]
  exact_mod_cast h
private theorem interpolate (hi g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK hi a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit hi g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/80 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hg80 : g ≤ 80 := by
      by_contra! h
      have hgQ : (80 : ℚ) ≤ g := by exact_mod_cast h.le
      have he : q/80*80 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit hi g ≤ h := by
      have hf := hu.interpolation g hg hg80
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit hi g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hg80) hc)
      _ = a*(d*g)+((1-θ)*curveUnit hi g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (tariff : CurveTariff b M F) {a h globalCap localCap : ℚ} (hu : RateOK b.row.hi a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnParent F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnParent F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/80 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit b.row.hi g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate b.row.hi g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (tariff : CurveTariff b M F)
    {a h globalCap : ℚ} (hu : RateOK b.row.hi a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnParent F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnParent F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
namespace P1_7_4
noncomputable section
open P1 (HighBand AnchorModel AnchoredFamily)
open P1_7 (stages terminal Source InBand)
open K1_14 (Banks)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active Fits dual fixedOn mass)
open scoped Classical
def nextIndex {b : HighBand} (i : ℕ) (hi : i < laterCount b) : StageIndex b :=
  ⟨i+1, by unfold laterCount at hi; omega⟩
structure Process {b h rows} (pairs : P1_7.Pairs b h rows) where
  sched : ScheduleOK b
  parents : Finset (Ideal Ambient)
  fixed : ∀ i : StageIndex b, FixedRows pairs i
  geometry : ∀ I ∈ parents, Active I ∧ I.height = 2
  init_mass : Fits parents (initialCap b)
def Process.Clean {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    (I : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixed i).free.equation I ∧ ¬ fixedOn (R.fixed i).moving.equation I
def PassedThrough {b h rows} (pairs : P1_7.Pairs b h rows) (i : ℕ) (I : Ideal Ambient) : Prop :=
  ∀ j : StageIndex b, 0 < j.val → j.val ≤ i → PairPass (pairAt pairs j) I
def Process.tested {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => R.Clean I ∧ PassedThrough pairs i I
def Process.kept {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  (R.tested i).filter fun I => stopIndex b ≤ i → dual I
def Process.rankExit {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.tested (stopIndex b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.kept (laterCount b)).filter (BankPass rows (terminal b).shape)
def Process.live {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if i ≤ laterCount b then R.kept i else R.final
def Process.lost {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if hi : i < laterCount b then
    (R.kept i).filter fun I => ¬ PairPass (pairAt pairs (nextIndex i hi)) I
  else
    (R.kept i).filter fun I => ¬ BankPass rows (terminal b).shape I
theorem Process.tested_sub {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.tested i ⊆ R.parents :=
  Finset.filter_subset _ _
theorem Process.kept_sub {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.kept i ⊆ R.tested i :=
  Finset.filter_subset _ _
theorem Process.final_sub {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs) :
    R.final ⊆ R.kept (laterCount b) :=
  Finset.filter_subset _ _
theorem Process.lost_sub {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.lost i ⊆ R.kept i := by
  unfold Process.lost
  split <;> exact Finset.filter_subset _ _
private theorem Process.tested_anti {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.tested j ⊆ R.tested i := by
  intro I hI
  obtain ⟨hm, hc, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨hm, hc, fun k hpos hk => hp k hpos (hk.trans hij)⟩
private theorem Process.kept_anti {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.kept j ⊆ R.kept i := by
  intro I hI
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨R.tested_anti hij hm, fun h => hp (h.trans hij)⟩
theorem Process.next_sub {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i ≤ laterCount b) : R.live (i+1) ⊆ R.live i := by
  rcases hi.lt_or_eq with ht | he
  · simp only [Process.live, ite_eq_left hi, ite_eq_left (Nat.succ_le_of_lt ht)]
    exact R.kept_anti (Nat.le_succ _)
  · subst i
    simpa [Process.live] using R.final_sub
theorem Process.lost_diff {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i ≤ laterCount b) : R.lost i ⊆ R.live i \ R.live (i+1) := by
  intro I hm
  refine Finset.mem_sdiff.mpr ⟨by simpa only [Process.live, ite_eq_left hi] using R.lost_sub i hm, ?_⟩
  intro hn
  rcases hi.lt_or_eq with ht | he
  · have hf := (Finset.mem_filter.mp
        (show I ∈ (R.kept i).filter _ from by simpa only [Process.lost, dite_eq_left ht] using hm)).2
    have hk : I ∈ R.kept (i+1) := by
      simpa only [Process.live, ite_eq_left (Nat.succ_le_of_lt ht)] using hn
    have hpasses := (Finset.mem_filter.mp (R.kept_sub _ hk)).2.2
    exact hf (hpasses (nextIndex i ht) (by change 0 < i+1; omega) le_rfl)
  · subst i
    have hf := (Finset.mem_filter.mp
        (show I ∈ (R.kept (laterCount b)).filter _ from by
          simpa only [Process.lost, dite_eq_right (Nat.lt_irrefl _)] using hm)).2
    have hf' : I ∈ R.final := by simpa [Process.live] using hn
    exact hf (Finset.mem_filter.mp hf').2
private theorem Process.local_cap {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (i : StageIndex b) (hi : 0 < i.val) (square : Bool)
    {A : Finset (Ideal Ambient)} (hA : A ⊆ R.tested i)
    (hdual : square = true → ∀ I ∈ A, dual I) (k : Fin 4) :
    massQ A k ≤ stageCap b i square k := by
  let s := stageAt b i
  let pair := pairAt pairs i
  obtain ⟨ga, gb⟩ := R.sched.stage_guard i i.isLt
  have hr := R.sched.small_reserve _ i.isLt
  have hrpos := R.sched.later_pos (i.val-1) (by unfold laterCount; omega)
  have hidx : i.val-1+1 = i.val := by omega
  rw [hidx] at hrpos
  exact estimate s.free.shape s.moving.shape s.reserve square pair.free pair.moving
    hrpos hr ga.ode.small gb.ode.small ga.seed_small gb.seed_small ga.ode.jb gb.ode.jb
    pair.free_ne pair.moving_ne
    (src.shape _ (free_listed i) _ _ pair.free_mem)
    (src.shape _ (moving_listed i) _ _ pair.moving_mem) pair.no_moving
    (R.fixed i).free (R.fixed i).moving A hdual (fun I hI => by
      obtain ⟨hp, hc, hpass⟩ := Finset.mem_filter.mp (hA hI)
      have hactive := (R.geometry I hp).1
      have htest := hpass i hi le_rfl
      exact ⟨hactive, htest.2.2, (hc i).1, (hc i).2,
        buffered_order src hw (free_listed i) ga hr hactive htest.1 pair.free_mem,
        buffered_order src hw (moving_listed i) gb hr hactive htest.2.1 pair.moving_mem⟩) k
theorem Process.cap_kept {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    {i : ℕ} (hi : i ≤ laterCount b) (k : Fin 4) : massQ (R.kept i) k ≤ history b i k := by
  induction i with
  | zero =>
    exact (Nat.cast_le (α := ℚ)).mpr
      ((K1_14_2_2.mass_mono ((R.kept_sub 0).trans (R.tested_sub 0)) k).trans (R.init_mass k))
  | succ i ih =>
    refine le_min ((massQ_mono (R.kept_anti (Nat.le_succ i)) k).trans (ih (by omega))) ?_
    let j := nextIndex i (by omega : i < laterCount b)
    exact R.local_cap estimate src hw j (Nat.succ_pos _) _ (R.kept_sub (i+1))
      (fun h I hI => (Finset.mem_filter.mp hI).2 (of_decide_eq_true h)) k
theorem Process.cap_live {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    {i : ℕ} (hi : i ≤ laterCount b) (k : Fin 4) : massQ (R.live i) k ≤ history b i k := by
  rw [Process.live, ite_eq_left hi]
  exact R.cap_kept estimate src hw hi k
theorem Process.rank_geometry {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.rankExit) : Active I ∧ ¬ dual I :=
  let hm := Finset.mem_filter.mp hI
  ⟨(R.geometry I (R.tested_sub _ hm.1)).1, hm.2⟩
theorem Process.rank_cap {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (k : Fin 4) : massQ R.rankExit k ≤ rankMass b k := by
  unfold rankMass
  by_cases hz : stopIndex b = 0
  · rw [ite_eq_left hz]
    exact (Nat.cast_le (α := ℚ)).mpr ((K1_14_2_2.mass_mono
      ((Finset.filter_subset _ _ : R.rankExit ⊆ R.tested (stopIndex b)).trans
        (R.tested_sub _)) k).trans (R.init_mass k))
  · rw [ite_eq_right hz]
    have hprev : stopIndex b-1 < stopIndex b := by omega
    have hsub : R.rankExit ⊆ R.tested (stopIndex b) := Finset.filter_subset _ _
    have hkeep : R.rankExit ⊆ R.kept (stopIndex b-1) := by
      intro I hI
      exact Finset.mem_filter.mpr ⟨R.tested_anti hprev.le (hsub hI), fun h => (hprev.not_ge h).elim⟩
    have h1 := (massQ_mono hkeep k).trans
      (R.cap_kept estimate src hw (hprev.le.trans R.sched.stop_le) k)
    have hj : stopIndex b < (stages b).length := by
      have := R.sched.stop_le
      have := R.sched.stages_pos
      unfold laterCount at *
      omega
    have h2 := R.local_cap estimate src hw ⟨stopIndex b, hj⟩ (Nat.pos_of_ne_zero hz)
      false hsub (by simp) k
    exact le_min h1 h2
theorem Process.retains {b h rows} {pairs : P1_7.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.parents) (hc : R.Clean I)
    (hrank : I ∉ R.rankExit) (hlost : ∀ i ≤ laterCount b, I ∉ R.lost i) :
    I ∈ R.final := by
  have keep : ∀ i ≤ laterCount b, I ∈ R.kept i := by
    intro i hi
    induction i with
    | zero =>
      have ht : I ∈ R.tested 0 :=
        Finset.mem_filter.mpr ⟨hI, hc, fun j hp hj => (Nat.not_lt_of_ge hj hp).elim⟩
      refine Finset.mem_filter.mpr ⟨ht, ?_⟩
      intro hs
      by_contra hd
      exact hrank (Finset.mem_filter.mpr ⟨by simpa [Nat.eq_zero_of_le_zero hs] using ht, hd⟩)
    | succ i ih =>
      have ht : i < laterCount b := hi
      have hprev := ih (Nat.le_of_lt ht)
      have hp : PairPass (pairAt pairs (nextIndex i ht)) I := by
        by_contra hfail
        apply hlost i ht.le
        simpa only [Process.lost, dite_eq_left ht] using Finset.mem_filter.mpr ⟨hprev, hfail⟩
      have htest : I ∈ R.tested (i+1) := by
        refine Finset.mem_filter.mpr ⟨hI, hc, ?_⟩
        intro j hj hji
        rcases hji.lt_or_eq with hj' | he
        · exact (Finset.mem_filter.mp (R.kept_sub i hprev)).2.2 j hj (Nat.le_of_lt_succ hj')
        · rw [show j = nextIndex i ht from Fin.ext he]
          exact hp
      refine Finset.mem_filter.mpr ⟨htest, ?_⟩
      intro hs
      by_cases hh : stopIndex b ≤ i
      · exact (Finset.mem_filter.mp hprev).2 hh
      · have he : stopIndex b = i+1 := by omega
        by_contra hd
        exact hrank (Finset.mem_filter.mpr ⟨by simpa [he] using htest, hd⟩)
  have hk := keep (laterCount b) le_rfl
  refine Finset.mem_filter.mpr ⟨hk, ?_⟩
  by_contra hf
  apply hlost (laterCount b) le_rfl
  simpa only [Process.lost, dite_eq_right (Nat.lt_irrefl _)] using Finset.mem_filter.mpr ⟨hk, hf⟩
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
namespace P1_7_4
noncomputable section
open P1 (HighBand AnchorModel AnchoredFamily K p)
open P1_7 (terminal Source InBand fees CurveTariff)
open K1_14 (Banks Jet jetAt)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover emptyCut RowCaps)
open scoped Classical BigOperators
structure FailureBooks {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs) where
  loss : Finset K
  point : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  covers : ∀ i ≤ laterCount b, ∀ γ ∈ Γ, ∀ I ∈ R.lost i,
    OnParent F I γ → γ ∈ point ∨ γ ∈ loss
private theorem properBin {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (src : Source b M F rows) (i : ℕ) :
    ∃ C : CutCover, (∀ fee, (C.cost fee : ℚ) ≤ dotQ (cutWeight b fee i) (massQ (R.lost i))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ R.lost i, OnParent F I γ) →
        γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have geom (I : Ideal Ambient) (hI : I ∈ R.lost i) :=
    (R.geometry I (R.tested_sub i (R.kept_sub i (R.lost_sub i hI)))).1
  have hj : (cutShape b i).J ≤ (cutShape b i).B := by
    by_cases hi : i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      exact Nat.le_add_left _ _
    · rw [cutShape, ite_eq_right hi]
      exact R.sched.terminal_guard.ode.jb
  have cutter (I : Ideal Ambient) (hI : I ∈ R.lost i) :
      ∃ P : Jet, RowCaps P (cutShape b i) ∧ toJet P ∉ I ∧
        ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
    by_cases hi : i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      rw [Process.lost, dite_eq_left hi] at hI
      exact failed_pair src R.sched pairs (nextIndex i hi) (Finset.mem_filter.mp hI).2
    · rw [cutShape, ite_eq_right hi]
      rw [Process.lost, dite_eq_right hi] at hI
      obtain ⟨P, hP, hproper, hzero⟩ := failed_bank src (Or.inl rfl) R.sched.terminal_guard.pos
        (Finset.mem_filter.mp hI).2
      exact ⟨P, hP, hproper, fun γ hγ _ => hzero γ hγ⟩
  obtain ⟨C, hC, hcover⟩ := combined_cuts (R.lost i) (cutShape b i) hj geom cutter
  refine ⟨C, fun fee => ?_, hcover⟩
  rw [← dot_cast]
  exact (Nat.cast_le (α := ℚ)).mpr (hC fee)
theorem failure_books {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (src : Source b M F rows) (hw : InBand b M.overhead) (est : PairedMass)
    (ledger : LossLedger b) (tariff : b.row.lo < 7773 → CurveTariff b M F) :
    Nonempty (FailureBooks F R) := by
  let n := laterCount b+1
  choose C hcost hcover using properBin R src
  let points := (Finset.range n).biUnion fun i => (C i).direct
  let lost := (Finset.range n).biUnion fun i => curveMarks F (C i)
  have next : ∀ i < n, R.live (i+1) ⊆ R.live i :=
    fun _ hi => R.next_sub (Nat.le_of_lt_succ hi)
  have fail : ∀ i < n, R.lost i ⊆ R.live i \ R.live (i+1) :=
    fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)
  have caps : ∀ i < n, ∀ k, massQ (R.live i) k ≤ history b i k :=
    fun _ hi => R.cap_live est src hw (Nat.le_of_lt_succ hi)
  have sumD : (∑ i ∈ Finset.range n, ((C i).cost 0 : ℚ)) ≤ seedLimit b :=
    (Finset.sum_le_sum fun i _ => hcost i 0).trans
      (bill_bound n (cutWeight b 0) (history b) R.live R.lost next fail caps)
  have hD (i : ℕ) (hi : i ≤ laterCount b) : ((C i).cost 0 : ℚ) ≤ seedLimit b :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (α := ℚ) ((C j).cost 0))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans sumD
  have hp (i : ℕ) (hi : i ≤ laterCount b) : (C i).cost 0 < p :=
    (Nat.cast_lt (α := ℚ)).mp ((hD i hi).trans_lt ledger.seed_small)
  have points_paid : (points.card : ℚ) ≤ (fees b).point := by
    let start : Mass :=
      ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
    have flat : ∀ i < n, ∀ k, massQ (R.live i) k ≤ start k := by
      intro i hi k
      have hc := (caps i hi k).trans (history_le_initial b i k)
      fin_cases k
      · exact hc
      · exact hc
      · exact hc
      · exact hc.trans ((Nat.cast_le (α := ℚ)).mpr R.sched.initial_e_ge)
    calc
      _ ≤ ∑ i ∈ Finset.range n, ((C i).cost 2 : ℚ) := by
        exact_mod_cast (Finset.card_biUnion_le : points.card ≤
          ∑ i ∈ Finset.range n, (C i).direct.card)
      _ ≤ ∑ i ∈ Finset.range n, dotQ (cutWeight b 2 i) (massQ (R.lost i)) :=
        Finset.sum_le_sum fun i _ => hcost i 2
      _ ≤ weightedBill n (cutWeight b 2) (fun _ => start) :=
        bill_bound n (cutWeight b 2) (fun _ => start) R.live R.lost next fail flat
      _ = pointLimit b := flat_bill _ _ _
      _ ≤ _ := ledger.points
  have hsum : (lost.card : ℚ) ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := by
    exact_mod_cast (Finset.card_biUnion_le : lost.card ≤
      ∑ i ∈ Finset.range n, (curveMarks F (C i)).card)
  have loss_paid : (lost.card : ℚ) ≤ (fees b).loss := by
    by_cases hd : b.row.lo < 7773
    · obtain ⟨a, h, hrate, hpay⟩ := ledger.discount hd
      have per_bin (i : ℕ) (hi : i ∈ Finset.range n) :
          ((curveMarks F (C i)).card : ℚ) ≤
            dotQ (lossWeight b a h i) (massQ (R.lost i)) + (C i).cost 0 := by
        have hi' : i ≤ laterCount b := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        obtain ⟨rate, ha⟩ := hrate i hi'
        have hloc : (C i).cost 0 ≤ dotQ (cutWeight b 0 i) (history b i) :=
          (hcost i 0).trans (dotQ_mono_mass (cutWeight_nonneg b 0 i)
            (fun k => (massQ_mono
              (fun _ hI => (Finset.mem_sdiff.mp (fail i (Finset.mem_range.mp hi) hI)).1) k).trans
                (caps i (Finset.mem_range.mp hi) k)))
        have hr := rated_curve_count F (tariff hd) rate (C i) (hD i hi')
          ((min_le_min le_rfl hloc).trans ha) (hp i hi')
        have a0 : 0 ≤ a i := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/80 by positivity).trans rate.degree
        calc
          _ ≤ a i*((C i).cost 0 : ℚ) + h i*((C i).cost 1 : ℚ) + (C i).cost 0 := hr
          _ ≤ a i*dotQ (cutWeight b 0 i) (massQ (R.lost i)) +
                h i*dotQ (cutWeight b 1 i) (massQ (R.lost i)) + (C i).cost 0 :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost i 0) a0)
              (mul_le_mul_of_nonneg_left (hcost i 1) rate.height)) le_rfl
          _ = _ := by rw [dotQ_scale_add]; rfl
      calc
        _ ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := hsum
        _ ≤ ∑ i ∈ Finset.range n, (dotQ (lossWeight b a h i) (massQ (R.lost i)) +
            ((C i).cost 0 : ℚ)) := Finset.sum_le_sum per_bin
        _ ≤ weightedBill n (lossWeight b a h) (history b) + seedLimit b := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (bill_bound n (lossWeight b a h) (history b) R.live R.lost next fail caps) sumD
        _ ≤ _ := hpay
    · calc
        _ ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := hsum
        _ ≤ ∑ i ∈ Finset.range n, ((p+1 : ℕ) : ℚ)*((C i).cost 0 : ℚ) :=
          Finset.sum_le_sum fun i hi => direct_curve_count F (C i)
            (hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
        _ ≤ ((p+1 : ℕ) : ℚ)*seedLimit b := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left sumD (Nat.cast_nonneg _)
        _ ≤ _ := ledger.direct (Nat.le_of_not_gt hd)
  refine ⟨⟨lost, points, (Nat.cast_le (α := ℚ)).mp loss_paid,
    (Nat.cast_le (α := ℚ)).mp points_paid, ?_⟩⟩
  intro i hi γ hγ I hI hm
  have hr := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  rcases hcover i γ hγ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hj⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hr, hd⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hr, mem_curveMarks hγ hJ hj⟩)
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7 (InBand stages terminal Source CurveTariff PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ScheduleOK b →
    ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 → NoMovingCommon P Q →
    RowCaps P (stageAt b 0).free.shape → RowCaps Q (stageAt b 0).moving.shape →
    ∀ (A : FixedPart P (stageAt b 0).free.shape) (B : FixedPart Q (stageAt b 0).moving.shape),
    (∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧ jetAt Q (M.label γ) (F.scalar γ) = 0) →
    ∀ later : ℕ → Jet,
    (∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j a, a ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ, jetAt (seedHasse j a (later i)) (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover M F b A.equation B.equation)
def c2 : Prop := PairedMass
def c3 : Prop :=
  ∀ (b : HighBand) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead →
    ∀ B J : ℕ, ODEGuard B J →
    ∀ G : ODE, ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ fixedFee b.row.hi B J
def c4 : Prop := ∀ b : HighBand, ScheduleOK b
def c5 : Prop := ∀ b : HighBand, LossLedger b
private def fixedMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (G : ODE) : Finset K := Γ.filter fun γ => fixedAt G (F.scalar γ) = 0
private theorem fixed_paid (hcount : c3) {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (hw : InBand b M.overhead) {B J : ℕ}
    (guard : ODEGuard B J) {G : ODE} (cap : ODECaps G B J) :
    (fixedMarks F G).card ≤ fixedFee b.row.hi B J :=
  hcount b u del M Γ F hw B J guard G cap _ (Finset.filter_subset _ _)
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
private def fixedBook {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs) : Finset K :=
  Finset.univ.biUnion fun i : StageIndex b =>
    fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation
private theorem fixed_book_paid (hcount : c3) {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (hw : InBand b M.overhead) {rows : Banks}
    {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs) :
    (fixedBook F R).card ≤ (fees b).fixedODE := by
  let price (i : ℕ) :=
    fixedFee b.row.hi (stageAt b i).free.shape.B (stageAt b i).free.shape.J +
      fixedFee b.row.hi (stageAt b i).moving.shape.B (stageAt b i).moving.shape.J
  calc
    _ ≤ ∑ i : StageIndex b,
        (fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : StageIndex b, price i := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨ga, gb⟩ := R.sched.stage_guard i i.isLt
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add
        (fixed_paid hcount F hw ga.ode (R.fixed i).free.equation_caps)
        (fixed_paid hcount F hw gb.ode (R.fixed i).moving.equation_caps))
    _ = fixedBudget b := Fin.sum_univ_eq_sum_range price (stages b).length
    _ ≤ _ := R.sched.fixed
private theorem mem_fixed_left {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (i : StageIndex b) {γ : K} (hγ : γ ∈ Γ) (hz : fixedAt (R.fixed i).free.equation (F.scalar γ) = 0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hz⟩)⟩
private theorem mem_fixed_right {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : P1_7.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (i : StageIndex b) {γ : K} (hγ : γ ∈ Γ) (hz : fixedAt (R.fixed i).moving.equation (F.scalar γ) = 0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hz⟩)⟩
private theorem floor_bound {n : ℕ} {r : ℚ} (h : (n : ℚ) ≤ r) : n ≤ r.floor.toNat := by
  have hi : (n : ℤ) ≤ r.floor := Rat.le_floor_iff.mpr (by exact_mod_cast h)
  simpa using Int.toNat_le_toNat hi
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) : P1_7.c4 := by
  classical
  intro b u del M Γ F hw _ _ _ tariff rows src pairs
  let sched := h4 b
  let zero : StageIndex b := ⟨0, sched.stages_pos⟩
  let P := pairAt pairs zero
  let fixed := fixedRows src pairs
  obtain ⟨ga, gb⟩ := sched.stage_guard 0 sched.stages_pos
  have hf := src.shape _ (free_listed zero) _ _ P.free_mem
  have hg := src.shape _ (moving_listed zero) _ _ P.moving_mem
  let later (i : ℕ) : Jet := if hi : i < (stages b).length then (pairAt pairs ⟨i, hi⟩).free else 0
  obtain ⟨initial⟩ := h1 b u del M Γ F sched P.free P.moving P.free_ne P.moving_ne
    P.no_moving hf hg (fixed zero).free (fixed zero).moving (fun γ hγ =>
      ⟨bank_zero src (free_listed zero) ga.pos (Nat.sub_le _ _) P.free_mem γ hγ,
        bank_zero src (moving_listed zero) gb.pos (Nat.sub_le _ _) P.moving_mem γ hγ⟩) later (by
      intro i hi
      obtain ⟨_, hsize⟩ := sched.intro_pos i hi
      let j : StageIndex b := ⟨i, hsize⟩
      let pair := pairAt pairs j
      simp only [later, dite_eq_left hsize]
      exact ⟨pair.free_ne, src.shape _ (free_listed j) _ _ pair.free_mem,
        fun k a ha => intro_zero src hw (free_listed j) (sched.stage_guard i hsize).1 pair.free_mem k a ha⟩)
  let R : Process pairs :=
    ⟨sched, initial.parents, fixed, fun I hI => ⟨initial.active I hI, initial.height_two I hI⟩,
      initial.mass_bound⟩
  obtain ⟨losses⟩ := failure_books R src hw h2 (h5 b) tariff
  obtain ⟨G, hgcap, hG⟩ := rank_equation R.rankExit (fun _ hI => R.rank_geometry hI)
    (B := rankB b) (J := rankJ b) (floor_bound (R.rank_cap h2 src hw 1))
    (floor_bound (R.rank_cap h2 src hw 2))
  let seed := Γ.filter fun γ => initial.seed.Covers (M.label γ)
  let contents := Γ.filter fun γ => graphEval (M.label γ) initial.content = 0
  let ords := Γ.filter fun γ => atX (F.scalar γ) ∈ initial.ordinates
  let rank := fixedMarks F G
  have label_inj : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  have hseed : seed.card ≤ (fees b).lowSeed := by
    have h := K1_14_3.seed_count (T := seed) label_inj.injOn initial.seed
      (initial.seed_le.trans_lt (sched.initial_small 2)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
    exact (h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ initial.seed_le) initial.seed_points)).trans
      sched.low_seed
  have hcontents : contents.card ≤ (fees b).content := by
    let C : SeedCover := ⟨initial.content, initial.content_ne, ∅⟩
    have h := K1_14_3.seed_count (T := contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.content_small)
      (fun _ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    have h' : contents.card ≤ (p+1)*initial.content.totalDegree := by
      simpa only [C, Finset.card_empty, Nat.add_zero] using h
    exact (h'.trans (Nat.mul_le_mul_left _ initial.content_le)).trans sched.content
  have hords : ords.card ≤ initialCap b 0 :=
    (Finset.card_le_card_of_injOn (fun γ => atX (F.scalar γ))
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
      (fun _ hγ _ hδ h => F.distinct (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
        (K1_14_3.scalar_atX_injective h))).trans initial.ordinate_le
  let books : PrefixBooks b :=
    ⟨losses.loss, losses.point, seed, ords ∪ rank, fixedBook F R, contents,
      losses.loss_le, losses.point_le, hseed,
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hords
        (fixed_paid h3 F hw sched.rank_guard hgcap))).trans sched.low_jet,
      fixed_book_paid h3 F hw R, hcontents⟩
  have initial_mem (I : ↥R.final) : I.1 ∈ R.parents :=
    R.tested_sub _ (R.kept_sub _ (R.final_sub I.2))
  let toSurface (I : ↥R.final) : Surface := surfaceOf I.1 (R.geometry _ (initial_mem I)).1.prime
  refine ⟨{
    books := books
    parents := R.final.attach.image toSurface
    geometric := ?_
    stage_pass := ?_
    terminal_pass := ?_
    covers := ?_ }⟩
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    have hgeom := R.geometry _ (initial_mem I)
    exact parent_of_dual hgeom.1 hgeom.2
      ((Finset.mem_filter.mp (R.final_sub I.2)).2 sched.stop_le)
  · intro q hq s hs hpositive
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hs
    let j : StageIndex b := ⟨i, hi⟩
    have ht : stageAt b j = s := by
      simpa [j, stageAt, List.getElem?_eq_getElem hi] using he
    clear he
    subst s
    have htest := (Finset.mem_filter.mp (R.kept_sub _ (R.final_sub I.2))).2.2
    have hj : 0 < j.val := by
      by_contra! hbad
      have hz : j.val = 0 := Nat.eq_zero_of_le_zero hbad
      have hr : (stageAt b j).reserve = 0 := by rw [hz, sched.zero]
      omega
    exact surface_pass (R.geometry _ (initial_mem I)).1.prime
      (htest j hj (by unfold laterCount; dsimp [j]; omega))
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  · intro γ hγ
    by_cases hpaid : γ ∈ books.union
    · exact Or.inl hpaid
    right
    have forbid_seed (h : γ ∈ seed) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_contents (h : γ ∈ contents) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_ords (h : γ ∈ ords) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_rank (h : γ ∈ rank) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_fixed (h : γ ∈ fixedBook F R) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_loss (h : γ ∈ losses.point ∨ γ ∈ losses.loss) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    rcases initial.covers γ hγ with hz | ho | hc | ha | hb | ⟨I, hI, hm⟩
    · exact (forbid_seed (Finset.mem_filter.mpr ⟨hγ, hz⟩)).elim
    · exact (forbid_ords (Finset.mem_filter.mpr ⟨hγ, ho⟩)).elim
    · exact (forbid_contents (Finset.mem_filter.mpr ⟨hγ, hc⟩)).elim
    · exact (forbid_fixed (mem_fixed_left F R zero hγ ha)).elim
    · exact (forbid_fixed (mem_fixed_right F R zero hγ hb)).elim
    · have hclean : R.Clean I := fun j =>
        ⟨fun hj => forbid_fixed (mem_fixed_left F R j hγ (fixed_zero hm hj)),
          fun hj => forbid_fixed (mem_fixed_right F R j hγ (fixed_zero hm hj))⟩
      have hnotRank : I ∉ R.rankExit := fun h => forbid_rank
        (Finset.mem_filter.mpr ⟨hγ, fixed_zero hm (hG I h)⟩)
      have hnotLost : ∀ i ≤ laterCount b, I ∉ R.lost i := fun i hi h =>
        forbid_loss (losses.covers i hi γ hγ I h hm)
      let J : ↥R.final := ⟨I, R.retains hI hclean hnotRank hnotLost⟩
      exact ⟨toSurface J, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), on_surface _ hm⟩
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1 (p)
open P1_7_4 (massQ sharedBound)
open K1_14 (Jet Shape)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
open private cancel_fixed from ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
open private factor_caps from ProximityPrize.SubmissionLower.Fast071
private theorem cancellation : K1_14_2_2_4.c3 :=
  K1_14_2_2_4_3.of_children K1_14_2_2_4_3_1.proof K1_14_2_2_4_3_2.proof
private theorem sections : K1_14_2_2_4.c5 :=
  K1_14_2_2_4_5.of_children K1_14_2_2_4_5_1.proof K1_14_2_2_4_5_2.proof
    K1_14_2_2_4_5_3.proof K1_14_2_2_4_5_4.proof K1_14_2_2_4_5_5.proof
private theorem scaled_le_div {d m c : ℕ} (hd : 0 < d) (h : d * m ≤ c) :
    (m : ℚ) ≤ (c : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).mpr
  rw [mul_comm]
  exact_mod_cast h
private theorem paired_stage {s t : Shape} {P Q : Jet} {A : FixedPart P s} {B : FixedPart Q t}
    (G : P0_10R_2.SharedGcd A B) (S : Finset (Ideal Ambient)) (square : Bool)
    (m r : ℕ) (k : Fin 4) (hr : 0 < r) (hrm : r ≤ m)
    (hx : seedDegree G.ordinary < p) (hz : G.ordinary.natDegree < p)
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    massQ S k ≤ sharedBound s t (seedDegree G.ordinary) G.ordinary.natDegree r m square k := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hg : 0 < highScale r k := by
    fin_cases k <;> first | exact hr | exact Nat.pow_pos hr
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply K1_14_2_2R.high_graph_mass K1_14_2_2_4_4.proof sections G.ordinary P Q
      _ r G.ordinary_ne hz hr
    · refine ⟨fixedIncl A.equation * G.left, G.left_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl B.equation * G.right, G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1, (hpass I hm).2.1, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤
      pairCap (residualShape s x z) (residualShape t x z) k := by
    apply sections G.left G.right _ _ _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, _, hA, hB, hP, hQ⟩ := hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP := cancellation G.ordinary G.left I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hA hP)
    have hlQ := cancellation G.ordinary G.right I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hB hQ)
    have hlen := K1_14_2_2_4_4.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha, fun hdegree => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square = false := Bool.eq_false_iff.mpr fun he => hIdual (hdual he I hm)
      have hk : k ≠ 3 := fun he => hIdual (show 0 < sectionDegree I 3 by
        rw [← he]
        exact Nat.pos_of_ne_zero hdegree)
      simpa [d, hs, hk, hIdual] using hlen
  have hadd : mass (S.filter (HighOn G.ordinary r)) k +
      mass (S.filter fun I => ¬ HighOn G.ordinary r I) k = mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (mass S k : ℚ) ≤ (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
  rw [← hadd, Nat.cast_add]
  exact add_le_add (scaled_le_div hg hh) (scaled_le_div hd hl)
theorem paired_thresholds (s t : Shape) (m : ℕ) (square : Bool) (P Q : Jet)
    (hsB : s.B < p) (hsU : s.U < p) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPs : RowCaps P s) (hQt : RowCaps Q t) (hno : K1_14_3.NoMovingCommon P Q)
    (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient))
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    ∃ x ≤ P1_7_4.pairMinSeed s t, ∃ z ≤ P1_7_4.pairMinOrdinate s t,
      ∀ r, 0 < r → r ≤ m → ∀ k, massQ S k ≤ sharedBound s t x z r m square k := by
  obtain ⟨G⟩ := P0_10R_2.sharedGcd A B hP hQ hPs hQt hno
  obtain ⟨hU, hB, _⟩ := factor_caps hQ G.ordinary_ne hQt G.right_factor
  refine ⟨seedDegree G.ordinary, le_min G.seed_le hU, G.ordinary.natDegree,
    le_min G.ordinate_le hB, ?_⟩
  intro r hr hrm k
  exact paired_stage G S square m r k hr hrm (G.seed_le.trans_lt hsU)
    (G.ordinate_le.trans_lt hsB) hdual hpass
end
end P1_7_4_2
end
section
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1_7_4 (pairMinSeed pairMinOrdinate cornerBound sharedBound)
open K1_14 (Shape)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
private theorem at_endpoints {F : ℕ → ℚ} {l x u : ℕ} {a b c M : ℚ}
    (hl : l ≤ x) (hu : x ≤ u) (ha : 0 ≤ a)
    (hF : ∀ y, l ≤ y → y ≤ u → F y = a * (y : ℚ)^2 + b * (y : ℚ) + c)
    (hL : F l ≤ M) (hU : F u ≤ M) : F x ≤ M := by
  have hl' : (l : ℚ) ≤ x := by exact_mod_cast hl
  have hu' : (x : ℚ) ≤ u := by exact_mod_cast hu
  have hchord := mul_nonneg ha (mul_nonneg (sub_nonneg.mpr hl') (sub_nonneg.mpr hu'))
  rw [hF x hl hu]
  rw [hF l le_rfl (hl.trans hu)] at hL
  rw [hF u (hl.trans hu) le_rfl] at hU
  by_cases hs : 0 ≤ a * ((l : ℚ) + u) + b
  · have h := mul_nonneg hs (sub_nonneg.mpr hu')
    linarith only [hU, hchord, h]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hl')
    linarith only [hL, hchord, h]
private def sectionBound (s t : Shape) (a b : ℚ) (k : Fin 4) (x z : ℕ) : ℚ :=
  a * (highCap x z k : ℚ) + b * (pairCap (residualShape s x z) (residualShape t x z) k : ℚ)
private theorem cast_trapezoid (B C J E : ℕ) (hJ : J ≤ B) :
    ((B * E + C * J - J * E : ℕ) : ℚ) =
      (B : ℚ) * E + (C : ℚ) * J - (J : ℚ) * E := by
  have h := (Nat.mul_le_mul_right E hJ).trans (Nat.le_add_right (B * E) (C * J))
  simp only [Nat.cast_sub h, Nat.cast_add, Nat.cast_mul]
private theorem seed_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hz : z ≤ pairMinOrdinate s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 0 0 0 ≤ M)
    (hZ : sectionBound s t a b 0 0 (pairMinOrdinate s t) ≤ M)
    (hC : sectionBound s t a b 0 0 (min (s.B-s.J) (t.B-t.J)) ≤ M) :
    sectionBound s t a b 0 x z ≤ M := by
  let C := min (s.B-s.J) (t.B-t.J)
  let limit := pairMinOrdinate s t
  let F (y : ℕ) := sectionBound s t a b 0 0 y
  have hcS : C ≤ s.B-s.J := min_le_left _ _
  have hcT : C ≤ t.B-t.J := min_le_right _ _
  change F z ≤ M
  by_cases hlow : z ≤ C
  · refine at_endpoints (F := F) (l := 0) (u := C) (a := 0)
      (b := a - b * ((s.J : ℚ) + t.J))
      (c := b * ((s.B : ℚ) * t.J + (t.B : ℚ) * s.J - (s.J : ℚ) * t.J))
      (Nat.zero_le z) hlow le_rfl ?_ h0 hC
    intro y _ hy
    have hsj : s.J ≤ s.B-y := by omega
    have htj : t.J ≤ t.B-y := by omega
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [min_eq_left hsj, min_eq_left htj, cast_trapezoid _ _ _ _ hsj,
      Nat.cast_sub (show y ≤ s.B by omega), Nat.cast_sub (show y ≤ t.B by omega)]
    ring
  · refine at_endpoints (F := F) (l := C) (u := limit) (a := b)
      (b := a - b * ((s.B : ℚ) + t.B)) (c := b * (s.B : ℚ) * t.B)
      (by omega) hz hb ?_ hC hZ
    intro y hy hyZ
    have hyS := hyZ.trans (min_le_left s.B t.B)
    have hyT := hyZ.trans (min_le_right s.B t.B)
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [cast_trapezoid _ _ _ _ (min_le_right _ _)]
    rcases min_choice (s.B-s.J) (t.B-t.J) with hc | hc
    · have hj : s.B-y ≤ s.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
    · have hj : t.B-y ≤ t.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
private theorem ordinate_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 1 0 0 ≤ M)
    (hX : sectionBound s t a b 1 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 1 x z ≤ M := by
  have hmono : sectionBound s t a b 1 x z ≤ sectionBound s t a b 1 x 0 := by
    change a * (x : ℚ) + b * (((s.U-x) * min t.J (t.B-z) +
      (t.U-x) * min s.J (s.B-z) : ℕ) : ℚ) ≤ a * (x : ℚ) +
      b * (((s.U-x) * min t.J (t.B-0) + (t.U-x) * min s.J (s.B-0) : ℕ) : ℚ)
    simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ]
    apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb)
    exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_left _ (min_le_left _ _))
      (Nat.mul_le_mul_left _ (min_le_left _ _))
  apply hmono.trans
  refine at_endpoints (F := fun y => sectionBound s t a b 1 y 0)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := a - b * ((t.J : ℚ) + s.J)) (c := b * ((s.U : ℚ) * t.J + (t.U : ℚ) * s.J))
    (Nat.zero_le x) hx le_rfl ?_ h0 hX
  intro y _ hy
  change a * (y : ℚ) + b * (((s.U-y) * min t.J (t.B-0) +
    (t.U-y) * min s.J (s.B-0) : ℕ) : ℚ) = _
  simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem mixed_endpoints (s t : Shape) {a b M : ℚ} {x z : ℕ}
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hC : ∀ y, (y = 0 ∨ y = pairMinSeed s t) → ∀ w,
      (w = 0 ∨ w = pairMinOrdinate s t) → sectionBound s t a b 2 y w ≤ M) :
    sectionBound s t a b 2 x z ≤ M := by
  have hform (y w : ℕ) (hy : y ≤ pairMinSeed s t) (hw : w ≤ pairMinOrdinate s t) :
      sectionBound s t a b 2 y w =
        a * (2 * (y : ℚ) * (w : ℚ)) +
          b * (((s.U : ℚ)-y) * ((t.B : ℚ)-w) + ((t.U : ℚ)-y) * ((s.B : ℚ)-w)) := by
    change a * ((2*y*w : ℕ) : ℚ) +
      b * (((s.U-y) * (t.B-w) + (t.U-y) * (s.B-w) : ℕ) : ℚ) = _
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
      Nat.cast_sub (hy.trans (min_le_right s.U t.U)),
      Nat.cast_sub (hw.trans (min_le_left s.B t.B)),
      Nat.cast_sub (hw.trans (min_le_right s.B t.B))]
  have hxCorner (y : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) :
      sectionBound s t a b 2 y z ≤ M := by
    have hy' : y ≤ pairMinSeed s t := hy.elim (fun h => h ▸ Nat.zero_le _) (fun h => h ▸ le_rfl)
    refine at_endpoints (F := sectionBound s t a b 2 y)
      (l := 0) (u := pairMinOrdinate s t) (a := 0)
      (b := 2 * a * y - b * (((s.U : ℚ)-y) + ((t.U : ℚ)-y)))
      (c := b * (((s.U : ℚ)-y) * t.B + ((t.U : ℚ)-y) * s.B))
      (Nat.zero_le z) hz le_rfl ?_ (hC y hy 0 (Or.inl rfl)) (hC y hy _ (Or.inr rfl))
    intro w _ hw
    rw [hform y w hy' hw]
    ring
  refine at_endpoints (F := fun y => sectionBound s t a b 2 y z)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := 2 * a * z - b * (((t.B : ℚ)-z) + ((s.B : ℚ)-z)))
    (c := b * ((s.U : ℚ) * ((t.B : ℚ)-z) + (t.U : ℚ) * ((s.B : ℚ)-z)))
    (Nat.zero_le x) hx le_rfl ?_ (hxCorner 0 (Or.inl rfl)) (hxCorner _ (Or.inr rfl))
  intro y _ hy
  rw [hform y z hy hz]
  ring
private theorem jet_endpoints (s t : Shape) {a b M : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t)
    (h0 : sectionBound s t a b 3 0 0 ≤ M)
    (hX : sectionBound s t a b 3 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 3 x z ≤ M := by
  change sectionBound s t a b 3 x 0 ≤ M
  refine at_endpoints (F := fun y => sectionBound s t a b 3 y 0)
    (l := 0) (u := pairMinSeed s t) (a := a+b)
    (b := -b * ((s.U : ℚ) + t.U)) (c := b * (s.U : ℚ) * t.U)
    (Nat.zero_le x) hx (add_nonneg ha hb) ?_ h0 hX
  intro y _ hy
  change a * ((y*y : ℕ) : ℚ) + b * (((s.U-y) * (t.U-y) : ℕ) : ℚ) = _
  simp only [Nat.cast_mul, Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem foldMax_ge {w : ℚ} (L : List ℚ) (init : ℚ)
    (h : w ≤ init ∨ w ∈ L) : w ≤ L.foldl max init := by
  induction L generalizing init with
  | nil => exact h.resolve_right List.not_mem_nil
  | cons v L ih =>
    apply ih
    rcases h with h | h
    · exact Or.inl (h.trans (le_max_left _ _))
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (le_max_right _ _)
      · exact Or.inr h
private def ordinateCorners (s t : Shape) : List ℕ :=
  [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B-s.J),
    min (pairMinOrdinate s t) (t.B-t.J)]
private theorem first_break_mem (s t : Shape) :
    min (s.B-s.J) (t.B-t.J) ∈ ordinateCorners s t := by
  let c := min (s.B-s.J) (t.B-t.J)
  have hc : c ≤ pairMinOrdinate s t :=
    le_min ((min_le_left _ _).trans (Nat.sub_le ..)) ((min_le_right _ _).trans (Nat.sub_le ..))
  rcases min_choice (s.B-s.J) (t.B-t.J) with h | h
  · have he := min_eq_right (show s.B-s.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
  · have he := min_eq_right (show t.B-t.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
theorem shared_le_corner (s t : Shape) {x z r m : ℕ} (square : Bool) (k : Fin 4)
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B) :
    sharedBound s t x z r m square k ≤ cornerBound s t r m square k := by
  let a : ℚ := (highScale r k : ℚ)⁻¹
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  let b : ℚ := (d : ℚ)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb : 0 ≤ b := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hEq (y w : ℕ) : sharedBound s t y w r m square k = sectionBound s t a b k y w := by
    simp only [sharedBound, sectionBound, a, b, d, n, div_eq_mul_inv, mul_comm]
  have hcorner (y w : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) (hw : w ∈ ordinateCorners s t) :
      sectionBound s t a b k y w ≤ cornerBound s t r m square k := by
    rw [← hEq]
    apply foldMax_ge
    refine Or.inr (List.mem_flatMap.mpr ⟨y, ?_, List.mem_map.mpr ⟨w, hw, rfl⟩⟩)
    exact hy.elim (fun h => by simp [h]) (fun h => by simp [h])
  rw [hEq]
  have h0 : 0 ∈ ordinateCorners s t := by simp [ordinateCorners]
  have hZ : pairMinOrdinate s t ∈ ordinateCorners s t := by simp [ordinateCorners]
  fin_cases k
  · exact seed_endpoints s t hb hz hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner 0 _ (Or.inl rfl) hZ) (hcorner 0 _ (Or.inl rfl) (first_break_mem s t))
  · exact ordinate_endpoints s t hb hx hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
  · exact mixed_endpoints s t hx hz (fun y hy w hw =>
      hcorner y w hy (hw.elim (fun h => h ▸ h0) (fun h => h ▸ hZ)))
  · exact jet_endpoints s t ha hb hx (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
end
end P1_7_4_2
end
section
namespace P1_7_4_2
open P1_7_4 (pairedCap cornerBound)
private theorem le_foldMin (v : ℚ) (f : ℕ → ℚ) (L : List ℕ) (init : ℚ)
    (hi : v ≤ init) (h : ∀ j ∈ L, v ≤ f j) :
    v ≤ L.foldl (fun a j => min a (f j)) init := by
  induction L generalizing init with
  | nil => exact hi
  | cons j L ih =>
    exact ih _ (le_min hi (h j (List.mem_cons_self ..)))
      (fun i hii => h i (List.mem_cons_of_mem _ hii))
theorem proof : P1_7_4.c2 := by
  intro s t r square P Q _ _ hsB _ hsU _ hsJ htJ hP hQ hPs hQt hno A B S hdual hpass k
  let m := r + 1
  obtain ⟨x, hx, z, hz, ht⟩ :=
    paired_thresholds s t m square P Q hsB hsU hP hQ hPs hQt hno A B S hdual hpass
  have bound (j : ℕ) (hj : j < m) :
      P1_7_4.massQ S k ≤ cornerBound s t (j+1) m square k :=
    (ht (j+1) (Nat.succ_pos _) hj k).trans (shared_le_corner s t square k hx hz hsJ htJ)
  change _ ≤ pairedCap s t r square k
  unfold pairedCap
  exact le_foldMin _ _ _ _ (bound 0 (Nat.succ_pos _))
    (fun j hj => bound j (List.mem_range.mp hj))
end P1_7_4_2
end
section
namespace P1_7_4_1
noncomputable section
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap OnParent)
open K1_14 (Jet Shape Seeds FX graphEval seedHasse)
open K1_14_2 (Ambient CoordinateRing ODE OnJet fixedAt)
open K1_14_2_2 (Fits RowCaps)
open K1_14_2_2_2 (FiniteSections residualBudget afterGcd ordinaryBudget)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open scoped BigOperators
def SectionGeometry (S : Finset (Ideal Ambient)) : Prop :=
  ∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧ FiniteSections I
structure AffineCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (G H : ODE) where
  components : Finset (Ideal Ambient)
  geometry : SectionGeometry components
  fits : Fits components (initialCap b)
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, graphEval (M.label γ) content = 0 ∨
    fixedAt G (F.scalar γ) = 0 ∨ fixedAt H (F.scalar γ) = 0 ∨
      ∃ I ∈ components, OnParent F I γ
def factorDegree (D : Jet) : Fin 3 → ℕ :=
  ![jetDegree D, D.natDegree, seedDegree D]
def factorMass (D : Finset Jet) (j : Fin 3) : ℕ :=
  ∑ f ∈ D, factorDegree f j
def ZeroLedger : Prop :=
  ∀ b : HighBand, (introIndices b).isEmpty = true →
    let s := (stageAt b 0).free.shape
    let t := (stageAt b 0).moving.shape
    s.J ≤ s.B → t.J ≤ t.B →
    ∀ x z : ℕ, x ≤ min s.U t.U → z ≤ min s.B t.B → ∀ k,
      residualBudget (afterGcd s x z) (afterGcd t x z) k + ordinaryBudget x z k ≤ initialCap b k
def IntroHasse : Prop :=
  ∀ (s : Shape) (P : Jet), RowCaps P s →
    ∀ j a, RowCaps (seedHasse j a P) s
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt initialCap initialE ScheduleOK InitialCover OnParent)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover joinCovers joinCovers_degree joinCovers_points joinCovers_covers)
open scoped BigOperators Classical
open private section_bound seed_projection component_height ordinary_cover from ProximityPrize.SubmissionLower.PortHighFinish
theorem proper_cover {P Q : Jet} (hp : ProperPair P Q) {s t : Shape}
    (hs : s.J ≤ s.B) (ht : t.J ≤ t.B) (hP : RowCaps P s) (hQ : RowCaps Q t) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (residualBudget s t) ∧
      ∀ z R, jetAt P z R = 0 → jetAt Q z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hp
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hp s t hs ht hP hQ S hS
  refine ⟨S, ?_, hfits, hcover⟩
  intro I hI
  obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
  exact ⟨hprime, hdim, component_height hp hprime hdim hrow hcut, hfinite I hI⟩
theorem ordinary_component_cover (f : Equation) (hi : Irreducible f)
    (hd : 0 < f.natDegree) (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hf, hc⟩ := ordinary_cover f hi hd hp
  exact ⟨S, fun I hI => ⟨(hS I hI).1, (hS I hI).2.1, (hS I hI).2.2.1,
    (hS I hI).2.2.2.1⟩, hf, hc⟩
theorem collect {α : Type*} (D : Finset α)
    (budget : α → Fin 4 → ℕ) (T : α → K → K[X] → Prop)
    (h : ∀ d ∈ D, ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (fun k => ∑ d ∈ D, budget d k) ∧
      ∀ d ∈ D, ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R := by
  classical
  let C (d : α) := if hd : d ∈ D then Classical.choose (h d hd) else ∅
  have hC (d : α) (hd : d ∈ D) :
      SectionGeometry (C d) ∧ Fits (C d) (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ C d, OnJet I z R := by
    simpa only [C, dite_eq_left hd] using Classical.choose_spec (h d hd)
  refine ⟨D.biUnion C, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨d, hd, hi⟩ := Finset.mem_biUnion.mp hI
    exact (hC d hd).1 I hi
  · intro k
    exact (sum_biUnion_le D C (fun I => sectionDegree I k)).trans
      (Finset.sum_le_sum fun d hd => (hC d hd).2.1 k)
  · intro d hd z R hr
    obtain ⟨I, hI, hone⟩ := (hC d hd).2.2 z R hr
    exact ⟨I, Finset.mem_biUnion.mpr ⟨d, hd, hI⟩, hone⟩
theorem finish {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {b : HighBand} {G H : ODE} (sched : ScheduleOK b) (C : AffineCover F b G H) :
    Nonempty (InitialCover M F b G H) := by
  classical
  let S := C.components
  let noSeeds := S.filter (fun I => sectionDegree I 0 = 0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hf⟩ := C.geometry I hI
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((C.fits k).trans_lt (sched.initial_small k))
    exact ⟨hprime, hdim, hf.seeds, hf.ordinate, hf.mixed, hf.jets,
      ⟨ha, hsmall 0⟩, hsmall 2, hsmall 3, hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ D : SeedCover, D.curve.totalDegree ≤ sectionDegree I 2 ∧
        D.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → D.Covers z := by
    obtain ⟨hI, hz⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hf⟩ := C.geometry I hI
    exact seed_projection I hprime hdim hf hz
  let seedImage (I : Ideal Ambient) : SeedCover :=
    if hi : I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1, one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree ≤ sectionDegree I 2 ∧
      (seedImage I).points.card ≤ sectionDegree I 3 ∧
      ∀ z R, OnJet I z R → (seedImage I).Covers z := by
    simpa only [seedImage, dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover := joinCovers noSeeds seedImage
  let onY (I : Ideal Ambient) := (Γ.filter (OnParent F I)).image (fun γ => atX (F.scalar γ))
  let ordinates := constY.biUnion onY
  have hy (I : Ideal Ambient) (hi : I ∈ constY) : (onY I).card ≤ sectionDegree I 0 := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    apply le_trans (b := 1) _ ha
    apply Finset.card_le_one.mpr
    intro x hx y hy'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hy'
    exact ordinate_eq (C.geometry I hI).1 hy
      (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
  refine ⟨{
    parents := parents
    active := hparents
    height_two := fun I hi => (C.geometry I (Finset.mem_filter.mp hi).1).2.2.1
    mass_bound := fits_mono (Finset.filter_subset _ _) C.fits
    seed := imageCover
    seed_le := ?_
    seed_points := ?_
    ordinates := ordinates
    ordinate_le := ?_
    content := C.content
    content_ne := C.content_ne
    content_le := C.content_le
    covers := ?_ }⟩
  · calc
      _ ≤ ∑ I ∈ noSeeds, (seedImage I).curve.totalDegree := joinCovers_degree _ _
      _ ≤ mass noSeeds 2 := Finset.sum_le_sum fun I hi => (hseedImage I hi).1
      _ ≤ mass S 2 := mass_mono (Finset.filter_subset _ _) 2
      _ ≤ _ := C.fits 2
  · calc
      _ ≤ ∑ I ∈ noSeeds, (seedImage I).points.card := joinCovers_points _ _
      _ ≤ mass noSeeds 3 := Finset.sum_le_sum fun I hi => (hseedImage I hi).2.1
      _ ≤ mass S 3 := mass_mono (Finset.filter_subset _ _) 3
      _ ≤ initialCap b 3 := C.fits 3
      _ ≤ _ := sched.initial_e_ge
  · calc
      _ ≤ ∑ I ∈ constY, (onY I).card := Finset.card_biUnion_le
      _ ≤ mass constY 0 := Finset.sum_le_sum hy
      _ ≤ mass S 0 := mass_mono (Finset.filter_subset _ _) 0
      _ ≤ _ := C.fits 0
  · intro γ hγ
    rcases C.covers γ hγ with h | h | h | ⟨I, hI, hon⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ha : sectionDegree I 0 = 0
      · have hmem : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hI, ha⟩
        exact Or.inl (joinCovers_covers hmem ((hseedImage I hmem).2.2 _ _ hon))
      · have hpos := Nat.pos_of_ne_zero ha
        by_cases hy : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨I, Finset.mem_filter.mpr ⟨hI, hpos, hy⟩, hon⟩))))
        · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
            ⟨I, Finset.mem_filter.mpr ⟨hI, hpos, hy⟩,
              Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγ, hon⟩, rfl⟩⟩))
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p)
open P1_7_4 (degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open K1_14_2_2_2_1 (extractSeed rowCaps_iff jetDegree seedDegree seedDegree_le
  jetDegree_mul seedDegree_mul seedDegree_seed jetDegree_C)
open K1_14_2_1_1 (view exists_view_degree_pos view_seedHasse view_degree_le OtherSeed)
open K1_14_3_2_1 (seedToJet markEval_fixed markEval_seed)
open K1_14_3 (fixedEmbedding)
open scoped BigOperators Classical
open private seedContent_cap divisor_caps from ProximityPrize.SubmissionLower.Fast051
open private exists_fixedIncl from ProximityPrize.SubmissionLower.Fast051
open private dvd_pow_of_dvd_hasse derivative_not_dvd from ProximityPrize.SubmissionLower.Fast076
structure Stripped {P : Jet} {s : Shape} (A : FixedPart P s) where
  content : Seeds
  row : Jet
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ s.U
  row_ne : row ≠ 0
  row_dvd : row ∣ P
  row_caps : RowCaps row s
  residual_eq : A.residual = C (C content) * row
  primitive : ∀ b : Seeds, C (C b) ∣ row → IsUnit b
  no_fixed : ∀ g : ODE, Irreducible (fixedIncl g) → ¬ fixedIncl g ∣ row
  covers : ∀ z S, jetAt P z S = 0 →
    graphEval z content = 0 ∨ fixedAt A.equation S = 0 ∨ jetAt row z S = 0
theorem strip {P : Jet} {s : Shape} (hP : P ≠ 0) (hc : RowCaps P s) (A : FixedPart P s) :
    Nonempty (Stripped A) := by
  have hr : A.residual ≠ 0 := fun hz => hP (by rw [A.factorization, hz, mul_zero])
  have hd : A.residual ∣ P := ⟨_, A.factorization.trans (mul_comm _ _)⟩
  obtain ⟨a, R, he, hprim⟩ := extractSeed A.residual hr
  have hm : (C (C a) * R : Jet) ≠ 0 := he ▸ hr
  have hR := (show R ∣ A.residual from ⟨_, he.trans (mul_comm _ _)⟩)
  refine ⟨⟨a, R, by simpa using left_ne_zero_of_mul hm,
    seedContent_cap hP hc ((show C (C a) ∣ A.residual from ⟨R, he⟩).trans hd),
    right_ne_zero_of_mul hm, hR.trans hd, divisor_caps hP hc (hR.trans hd),
    he, hprim, fun g hg hgR => A.stripped g hg (hgR.trans hR), ?_⟩⟩
  intro z S h
  have H := congrArg (markEval z S) (A.factorization.trans (congrArg (fixedIncl A.equation * ·) he))
  change markEval z S P = 0 at h
  rw [h, map_mul, map_mul] at H
  change 0 = markEval z S (fixedEmbedding A.equation) *
    (markEval z S (seedToJet a) * markEval z S R) at H
  rw [markEval_fixed, markEval_seed, eq_comm, mul_eq_zero, mul_eq_zero] at H
  rcases H with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
theorem factorDegree_add {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) (j : Fin 3) :
    factorDegree (P * Q) j = factorDegree P j + factorDegree Q j := by
  fin_cases j
  · exact jetDegree_mul hP hQ
  · exact natDegree_mul hP hQ
  · exact seedDegree_mul hP hQ
private theorem factorDegree_one (j : Fin 3) : factorDegree 1 j = 0 := by
  fin_cases j
  · exact jetDegree_C (1 : Equation) |>.trans natDegree_one
  · exact natDegree_one
  · exact seedDegree_seed (1 : Seeds) |>.trans MvPolynomial.totalDegree_one
theorem factorDegree_pow {P : Jet} (hP : P ≠ 0) (r : ℕ) (j : Fin 3) :
    factorDegree (P ^ r) j = r * factorDegree P j := by
  induction r with
  | zero => simp [factorDegree_one]
  | succ r ih =>
    rw [pow_succ, factorDegree_add (pow_ne_zero _ hP) hP, ih, Nat.succ_mul]
theorem factorDegree_prod {S : Finset Jet} {f : Jet → Jet} (hf : ∀ d ∈ S, f d ≠ 0) (j : Fin 3) :
    factorDegree (∏ d ∈ S, f d) j = ∑ d ∈ S, factorDegree (f d) j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [factorDegree_one]
  | insert d S hd ih =>
    have hS : ∀ e ∈ S, f e ≠ 0 := fun e he => hf e (Finset.mem_insert_of_mem he)
    rw [Finset.prod_insert hd, Finset.sum_insert hd,
      factorDegree_add (hf d (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hS), ih hS]
theorem factorDegree_dvd {P Q : Jet} (hQ : Q ≠ 0) (hd : P ∣ Q) (j : Fin 3) :
    factorDegree P j ≤ factorDegree Q j := by
  obtain ⟨T, rfl⟩ := hd
  rw [factorDegree_add (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)]
  exact Nat.le_add_right _ _
theorem caps_iff (P : Jet) (s : Shape) :
    RowCaps P s ↔ ∀ j, factorDegree P j ≤ degreeVector s j := by
  rw [rowCaps_iff]
  constructor
  · rintro ⟨hB, hJ, hU⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩
def ownShape (P : Jet) : Shape :=
  ⟨0, factorDegree P 0, factorDegree P 1, factorDegree P 2⟩
theorem own_caps (P : Jet) : RowCaps P (ownShape P) := by
  apply (caps_iff _ _).mpr
  intro j
  fin_cases j <;> exact le_rfl
theorem own_J_le_B {P : Jet} (hP : P ≠ 0) : (ownShape P).J ≤ (ownShape P).B := by
  have hc : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  exact (Nat.le_add_left _ _).trans ((own_caps P) _ _ hc).1
theorem factorMass_mono {D E : Finset Jet} (h : D ⊆ E) (j : Fin 3) :
    factorMass D j ≤ factorMass E j :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
structure IntroFactors (P : Jet) (D : Finset Jet) : Prop where
  factors : ∀ f ∈ D, Irreducible f ∧ f ∣ P ∧ UsesSeed f ∧
    f ∉ Set.range seedToJet ∧ f ∉ Set.range fixedEmbedding
  pairwise : (D : Set Jet).Pairwise IsRelPrime
theorem IntroFactors.mono {P : Jet} {D E : Finset Jet} (h : IntroFactors P E) (he : D ⊆ E) :
    IntroFactors P D :=
  ⟨fun f hf => h.factors f (he hf), h.pairwise.mono he⟩
theorem initial_factors {P : Jet} {s : Shape} {A : FixedPart P s} (R : Stripped A) :
    ∃ D : Finset Jet, IntroFactors P D ∧ (∀ j, factorMass D j ≤ degreeVector s j) ∧
      ∀ z S, jetAt R.row z S = 0 → ∃ f ∈ D, jetAt f z S = 0 := by
  classical
  let _ : StrongNormalizationMonoid Jet := UniqueFactorizationMonoid.strongNormalizationMonoid
  let N := normalizedFactors R.row
  let D := N.toFinset
  have hmem (f : Jet) (hf : f ∈ D) : f ∈ N := Multiset.mem_toFinset.mp hf
  have hirr (f : Jet) (hf : f ∈ D) : Irreducible f :=
    irreducible_of_normalized_factor f (hmem f hf)
  have hdvd (f : Jet) (hf : f ∈ D) : f ∣ R.row := dvd_of_mem_normalizedFactors (hmem f hf)
  have hprod : (∏ f ∈ D, f) ∣ R.row :=
    (Multiset.toFinset_prod_dvd_prod N).trans (prod_normalizedFactors R.row_ne).dvd
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    have hfix : f ∉ Set.range fixedEmbedding := by
      rintro ⟨g, rfl⟩
      exact R.no_fixed g (hirr _ hf) (hdvd _ hf)
    have hseed : f ∉ Set.range seedToJet := by
      rintro ⟨a, rfl⟩
      exact (hirr _ hf).not_isUnit (isUnit_C.mpr (isUnit_C.mpr (R.primitive a (hdvd _ hf))))
    exact ⟨hirr f hf, (hdvd f hf).trans R.row_dvd,
      by_contra (fun h => hfix (by
        obtain ⟨g, hg⟩ := exists_fixedIncl f h
        exact ⟨g, hg.symm⟩)), hseed, hfix⟩
  · intro f hf g hg hne
    exact (hirr f hf).isRelPrime_iff_not_dvd.mpr fun hd =>
      hne (normalizedFactors_eq_of_dvd R.row f (hmem _ hf) g (hmem _ hg) hd)
  · intro j
    calc
      _ = factorDegree (∏ f ∈ D, id f) j :=
        (factorDegree_prod (f := id) (fun f hf => (hirr f hf).ne_zero) j).symm
      _ ≤ factorDegree R.row j := factorDegree_dvd R.row_ne hprod j
      _ ≤ _ := (caps_iff _ _).mp R.row_caps j
  · intro z S hz
    change markEval z S R.row = 0 at hz
    have hm := map_dvd (markEval z S) (prod_normalizedFactors R.row_ne).symm.dvd
    change markEval z S R.row ∣ markEval z S N.prod at hm
    rw [hz, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hm
    obtain ⟨f, hf, he⟩ := hm
    exact ⟨f, Multiset.mem_toFinset.mpr hf, he⟩
theorem hasse_power {D R : Jet} {s : Shape} (hi : Irreducible D) (hseed : UsesSeed D)
    (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p) {e : ℕ}
    (hall : ∀ i a, a ≤ e → D ∣ seedHasse i a R) : D^(e+1) ∣ R := by
  obtain ⟨i, hpos⟩ := exists_view_degree_pos D hseed
  have hD : D ∣ R := by
    apply (map_dvd_iff (view i)).mp
    simpa only [view_seedHasse, hasseDeriv_zero'] using
      (map_dvd_iff (view i)).mpr (hall i 0 (Nat.zero_le _))
  have hbound : (view i D).natDegree < p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hD)
      ((view i).map_ne_zero_iff.mpr hR)).trans
        (view_degree_le i R s.U ((seedDegree_le _ _).mp ((rowCaps_iff _ _).mp hcap).2.2))).trans_lt hsmall
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP OtherSeed p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr : Irreducible (view i D) := (MulEquiv.irreducible_iff (view i)).mpr hi
  have hprime : Prime (view i D) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply dvd_pow_of_dvd_hasse hprime (derivative_not_dvd _ hpos hbound)
  intro a ha
  rw [← view_seedHasse]
  exact (map_dvd_iff (view i)).mpr (hall i a (Nat.le_of_lt_succ ha))
theorem retained_mass {P R : Jet} {D : Finset Jet} (hD : IntroFactors P D)
    {s : Shape} (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p)
    (e : ℕ) (hall : ∀ f ∈ D, ∀ i a, a ≤ e → f ∣ seedHasse i a R) (j : Fin 3) :
    factorMass D j ≤ degreeVector s j / (e+1) := by
  have hprod : (∏ f ∈ D, f^(e+1)) ∣ R := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro f hf g hg hne
      exact (hD.pairwise hf hg hne).pow_left.pow_right
    · intro f hf
      exact hasse_power (hD.factors f hf).1 (hD.factors f hf).2.2.1 hR hcap hsmall (hall f hf)
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos e)).mpr
  rw [Nat.mul_comm, factorMass, Finset.mul_sum]
  calc
    _ = factorDegree (∏ f ∈ D, f^(e+1)) j := by
      rw [factorDegree_prod (fun f hf => pow_ne_zero _ (hD.factors f hf).1.ne_zero)]
      exact Finset.sum_congr rfl fun f hf =>
        (factorDegree_pow (hD.factors f hf).1.ne_zero _ j).symm
    _ ≤ factorDegree R j := factorDegree_dvd hR hprod j
    _ ≤ _ := (caps_iff _ _).mp hcap j
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p AnchorModel AnchoredFamily HighBand)
open P1_7_4 (ScheduleOK stageAt introIndices initialCap)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (extractOrdinary)
open scoped BigOperators Classical
open private gcd_caps multiset_prod_ne_zero distinct_le_degree seed_degree_mul
  atMark_prod_eq_zero jetAt_mul jetAt_ordinary from ProximityPrize.SubmissionLower.Fast051
theorem zero_cover (ledger : ZeroLedger) {b : HighBand} (sched : ScheduleOK b)
    (empty : (introIndices b).isEmpty = true)
    {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {P Q : Jet} (hnc : NoMovingCommon P Q)
    {A : FixedPart P (stageAt b 0).free.shape} {B : FixedPart Q (stageAt b 0).moving.shape}
    (a : Stripped A) (b' : Stripped B)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0) :
    Nonempty (AffineCover F b A.equation B.equation) := by
  classical
  let s := (stageAt b 0).free.shape
  let t := (stageAt b 0).moving.shape
  obtain ⟨gs, gt⟩ := sched.stage_guard 0 sched.stages_pos
  have hord (D : Jet) (hD : Irreducible D) (hda : D ∣ a.row) (hdb : D ∣ b'.row) :
      D.natDegree = 0 := by
    by_contra hp
    obtain ⟨G, rfl⟩ := hnc D hD (hda.trans a.row_dvd) (hdb.trans b'.row_dvd)
      (Nat.pos_of_ne_zero hp)
    exact a.no_fixed G hD hda
  obtain ⟨N, L, T, hL, hT, hproper, hN⟩ :=
    extractOrdinary a.row b'.row a.row_ne b'.row_ne a.primitive hord
  let x := ordinarySeedDegree N.prod
  let z := N.prod.natDegree
  have hN0 : ∀ f ∈ N, f ≠ 0 := fun f hf => (hN f hf).1.ne_zero
  have hF := multiset_prod_ne_zero N hN0
  have hAc : RowCaps (C N.prod * L) s := hL ▸ a.row_caps
  have hBc : RowCaps (C N.prod * T) t := hT ▸ b'.row_caps
  obtain ⟨hx, hz, hcL⟩ := gcd_caps hF hproper.left_ne hAc
  obtain ⟨hx', hz', hcT⟩ := gcd_caps hF hproper.right_ne hBc
  obtain ⟨S, hgeom, hS, hcover⟩ :=
    proper_cover hproper (min_le_right _ _) (min_le_right _ _) hcL hcT
  have hs1 : ordinarySeedDegree (1 : Equation) = 0 := by
    rw [← K1_14_2_2_2_1.seedDegree_C]
    simpa only [C_1, MvPolynomial.totalDegree_one] using K1_14_2_2_2_1.seedDegree_seed (1 : Seeds)
  have hseed : (∑ f ∈ N.toFinset, ordinarySeedDegree f) ≤ x :=
    distinct_le_degree ordinarySeedDegree hs1 (fun hf hg => seed_degree_mul hf hg) N hN0
  have hy : (∑ f ∈ N.toFinset, f.natDegree) ≤ z :=
    distinct_le_degree natDegree natDegree_one (fun hf hg => natDegree_mul hf hg) N hN0
  obtain ⟨U, hUgeom, hU, hUcover⟩ := collect N.toFinset
    (fun f => ordinaryBudget (ordinarySeedDegree f) f.natDegree) (fun f z R => atMark f z R = 0)
    (fun f hf => ordinary_component_cover f (hN f (Multiset.mem_toFinset.mp hf)).1
      (hN f (Multiset.mem_toFinset.mp hf)).2
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans hy).trans_lt
        (hz.trans_lt gs.ode.small)))
  refine ⟨{
    components := S ∪ U
    geometry := ?_
    fits := ?_
    content := a.content * b'.content
    content_ne := mul_ne_zero a.content_ne b'.content_ne
    content_le := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add a.content_le b'.content_le)
    covers := ?_ }⟩
  · intro I hI
    exact (Finset.mem_union.mp hI).elim (hgeom I) (hUgeom I)
  · intro k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hS k) ((hU k).trans (ordinary_sum _ _ _ hseed hy k))).trans
        (ledger b empty gs.ode.jb gt.ode.jb x z (le_min hx hx') (le_min hz hz') k))
  · intro γ hγ
    obtain ⟨hp, hq⟩ := hrows γ hγ
    rcases a.covers _ _ hp with h | h | ha
    · exact Or.inl (by rw [map_mul, h, zero_mul])
    · exact Or.inr (Or.inl h)
    rcases b'.covers _ _ hq with h | h | hb
    · exact Or.inl (by rw [map_mul, h, mul_zero])
    · exact Or.inr (Or.inr (Or.inl h))
    apply Or.inr ∘ Or.inr ∘ Or.inr
    by_cases hzero : atMark N.prod (M.label γ) (F.scalar γ) = 0
    · obtain ⟨f, hf, hmark⟩ := atMark_prod_eq_zero hzero
      obtain ⟨I, hI, hon⟩ := hUcover f (Multiset.mem_toFinset.mpr hf) _ _ hmark
      exact ⟨I, Finset.mem_union_right _ hI, hon⟩
    · rw [hL, jetAt_mul, jetAt_ordinary, mul_eq_zero] at ha
      rw [hT, jetAt_mul, jetAt_ordinary, mul_eq_zero] at hb
      obtain ⟨I, hI, hon⟩ := hcover _ _ (ha.resolve_left hzero) (hb.resolve_left hzero)
      exact ⟨I, Finset.mem_union_left _ hI, hon⟩
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4_1
noncomputable section
open P1_7_4 (introWeight introJump)
open K1_14 (Jet Shape)
open K1_14_2_2_2 (residualBudget ordinaryBudget)
open scoped BigOperators Classical
def factorTariff (s : Shape) (k : Fin 4) (f : Jet) : ℕ :=
  ∑ j, introWeight s k j * factorDegree f j
def weightedDegree (w : Fin 3 → ℕ) (D : Finset Jet) : ℕ :=
  ∑ j, w j * factorMass D j
theorem weighted_factors (w : Fin 3 → ℕ) (D : Finset Jet) :
    weightedDegree w D = ∑ f ∈ D, ∑ j, w j * factorDegree f j := by
  unfold weightedDegree factorMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
theorem residual_tariff (f : Jet) (s : Shape) (hs : s.J ≤ s.B) (k : Fin 4) :
    residualBudget (ownShape f) s k = factorTariff s k f := by
  fin_cases k
  · simp only [residualBudget, factorTariff, Fin.sum_univ_three, introWeight, ownShape]
    change factorDegree f 0*s.J + s.B*factorDegree f 1 - factorDegree f 1*s.J =
      s.J*factorDegree f 0 + (s.B-s.J)*factorDegree f 1 + 0*factorDegree f 2
    have hm := Nat.mul_le_mul_right (factorDegree f 1) hs
    rw [Nat.mul_comm (factorDegree f 1) s.J, Nat.add_sub_assoc hm, ← Nat.sub_mul]
    ring
  · change _ = ∑ j, introWeight s 1 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.J + s.U*factorDegree f 1 =
      0*factorDegree f 0 + s.U*factorDegree f 1 + s.J*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 2 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.B + s.U*factorDegree f 0 =
      s.U*factorDegree f 0 + 0*factorDegree f 1 + s.B*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 3 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.U = 0*factorDegree f 0 + 0*factorDegree f 1 + s.U*factorDegree f 2
    ring
theorem tariff_step {D T : Finset Jet} (hT : T ⊆ D) (cap old : Fin 3 → ℕ)
    (s : Shape) (k : Fin 4) (hcap : ∀ j, factorMass D j ≤ cap j) :
    (∑ f ∈ D \ T, factorTariff s k f) +
      weightedDegree (fun j => max (old j) (introWeight s k j)) T ≤
      weightedDegree old D + introJump cap old s k := by
  classical
  let w := fun j => max (old j) (introWeight s k j)
  have hadd (j : Fin 3) : old j + (w j-old j) = w j :=
    Nat.add_sub_of_le (le_max_left _ _)
  calc
    _ ≤ weightedDegree w (D \ T) + weightedDegree w T := by
      apply Nat.add_le_add_right
      rw [weighted_factors]
      exact Finset.sum_le_sum fun f _ =>
        Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (le_max_right _ _)
    _ = weightedDegree w D := by
      simp only [weighted_factors]
      exact Finset.sum_sdiff hT
    _ = weightedDegree old D + ∑ j, (w j-old j) * factorMass D j := by
      unfold weightedDegree
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← Nat.add_mul, hadd]
    _ ≤ _ := Nat.add_le_add_left
      (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hcap j)) _
theorem ordinary_charge (D : Finset Jet) (cap : Fin 3 → ℕ)
    (hcap : ∀ j, factorMass D j ≤ cap j) (k : Fin 4) :
    (∑ f ∈ D, ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ≤
      ordinaryBudget (cap 2) (cap 0) k := by
  fin_cases k
  · exact hcap 0
  · exact hcap 2
  · change (∑ f ∈ D, 2 * factorDegree f 2 * factorDegree f 0) ≤ 2 * cap 2 * cap 0
    calc
      _ ≤ ∑ f ∈ D, 2 * factorDegree f 2 * cap 0 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 0))
      _ = (2 * factorMass D 2) * cap 0 := by rw [factorMass, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hcap 2))
  · change (∑ f ∈ D, factorDegree f 2 * factorDegree f 2) ≤ cap 2 * cap 2
    calc
      _ ≤ ∑ f ∈ D, factorDegree f 2 * cap 2 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 2))
      _ = factorMass D 2 * cap 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (hcap 2)
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap ScheduleOK introAccount introJump introWeight degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (jetDegree_C seedDegree_C)
open scoped BigOperators Classical
open private ordinary_factor from ProximityPrize.SubmissionLower.Fast067
private theorem irreducible_cut {f C : Jet} (hf : Irreducible f) (hd : ¬ f ∣ C) :
    ProperPair f C :=
  ⟨hf.ne_zero, fun h => hd (h ▸ dvd_zero _), fun _ hD hDf hDC =>
    hd ((hD.associated_of_dvd hf hDf).dvd'.trans hDC)⟩
private theorem terminal_piece {P Q : Jet} {t : Shape} {D : Finset Jet}
    (hD : IntroFactors P D) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q t) (hJB : t.J ≤ t.B) (hB : t.B < p) (hQ : Q ≠ 0)
    (f : Jet) (hf : f ∈ D) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (fun k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ∧
      ∀ z R, (jetAt f z R = 0 ∧ jetAt Q z R = 0) → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨hi, hPf, _, hs, hfix⟩ := hD.factors f hf
  by_cases hd : f ∣ Q
  · have hv : f.natDegree = 0 := by
      by_contra h
      exact hfix (hnc f hi hPf hd (Nat.pos_of_ne_zero h))
    obtain ⟨hc, hirr, hpos⟩ := ordinary_factor hi hv hs
    have hdegrees : factorDegree f 0 = (f.coeff 0).natDegree ∧
        factorDegree f 2 = ordinarySeedDegree (f.coeff 0) :=
      ⟨(congrArg K1_14_2_2_2_1.jetDegree hc).symm.trans (jetDegree_C _),
       (congrArg K1_14_2_2_2_1.seedDegree hc).symm.trans (seedDegree_C _)⟩
    have hsmall : (f.coeff 0).natDegree < p := by
      rw [← hdegrees.1]
      exact ((factorDegree_dvd hQ hd 0).trans ((caps_iff _ _).mp hQc 0)).trans_lt hB
    obtain ⟨S, hG, hF, hC⟩ := ordinary_component_cover _ hirr hpos hsmall
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R ?_⟩
    · rw [hdegrees.1, hdegrees.2]
      exact Nat.le_add_left _ _
    · have hz := h.1
      rw [← hc] at hz
      simpa [jetAt, atMark] using hz
  · obtain ⟨S, hG, hF, hC⟩ :=
      proper_cover (irreducible_cut hi hd) (own_J_le_B hi.ne_zero) hJB (own_caps f) hQc
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R h.1 h.2⟩
    rw [residual_tariff f t hJB]
    exact Nat.le_add_right _ _
private theorem intro_components (shape : IntroHasse) {b : HighBand} (sched : ScheduleOK b)
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (stageAt b 0).moving.shape) (later : ℕ → Jet)
    (rows : ∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape) :
    ∀ (is : List ℕ), (∀ i ∈ is, i ∈ introIndices b) →
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount b k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ (stageAt b i).reserve →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro _ D cap hD hcap
    let t := (stageAt b 0).moving.shape
    have gt := (sched.stage_guard 0 sched.stages_pos).2
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.ode.jb gt.ode.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hord : (![cap 0, cap 2, 2*cap 0*cap 2, cap 2*cap 2] : Fin 4 → ℕ) k =
          ordinaryBudget (cap 2) (cap 0) k := by
        fin_cases k <;> try rfl
        change 2*cap 0*cap 2 = 2*cap 2*cap 0
        ring
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount, hord]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro his D cap hD hcap
    have hi := his i (List.mem_cons_self ..)
    have hrest : ∀ l ∈ is, l ∈ introIndices b := fun l hl => his l (List.mem_cons_of_mem _ hl)
    let s := (stageAt b i).free.shape
    let r := (stageAt b i).reserve
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := (sched.stage_guard i (sched.intro_pos i hi).2).1
    obtain ⟨hrow, hc⟩ := rows i hi
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc gt.seed_small r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih hrest T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.ode.jb (own_caps f) (shape s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.ode.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount b k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount b k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount b k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount b k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩
theorem intro_cover (shape : IntroHasse) {b : HighBand} (sched : ScheduleOK b)
    (hne : ¬ (introIndices b).isEmpty = true)
    {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (stageAt b 0).moving.shape)
    {A : FixedPart P (stageAt b 0).free.shape} {B : FixedPart Q (stageAt b 0).moving.shape}
    (a : Stripped A)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0)
    (later : ℕ → Jet)
    (hlater : ∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j r, r ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ, jetAt (seedHasse j r (later i)) (M.label γ) (F.scalar γ) = 0) :
    Nonempty (AffineCover F b A.equation B.equation) := by
  obtain ⟨D, hD, hcap, hroot⟩ := initial_factors a
  obtain ⟨S, hG, hFit, hC⟩ := intro_components shape sched hQ hnc hQc later
    (fun i hi => ⟨(hlater i hi).1, (hlater i hi).2.1⟩)
    (introIndices b) (fun _ hi => hi) D _ hD hcap
  refine ⟨{
    components := S
    geometry := hG
    fits := fun k => ?_
    content := a.content
    content_ne := a.content_ne
    content_le := a.content_le.trans (Nat.le_add_right _ _)
    covers := ?_ }⟩
  · rw [initialCap, ite_eq_right hne]
    simpa only [weightedDegree, zero_mul, Finset.sum_const_zero, Nat.add_zero] using hFit k (fun _ => 0)
  · intro γ hγ
    obtain ⟨hp, hq⟩ := hrows γ hγ
    rcases a.covers _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (hC _ _
        (fun i hi j r hr => (hlater i hi).2.2 j r hr γ hγ) hq (hroot _ _ h))))
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1
def c1 : Prop := ZeroLedger
def c2 : Prop := IntroHasse
theorem of_children (h1 : c1) (h2 : c2) : P1_7_4.c1 := by
  intro b u del M Γ F sched P Q hP hQ hnc hPc hQc A B hrows later hlater
  obtain ⟨a⟩ := strip hP hPc A
  by_cases hempty : (P1_7_4.introIndices b).isEmpty = true
  · obtain ⟨tail⟩ := strip hQ hQc B
    obtain ⟨C⟩ := zero_cover h1 sched hempty F hnc a tail hrows
    exact finish sched C
  · obtain ⟨C⟩ := intro_cover (B := B) h2 sched hempty F hQ hnc hQc a hrows later hlater
    exact finish sched C
end P1_7_4_1
end
section
namespace P1_7_4_1_1
open K1_14 (Shape)
open K1_14_2_2_2 (afterGcd residualBudget ordinaryBudget)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
open P1_7_4 (sharedBound stageAt initialCap)
private theorem sharedBound_zero (s t : Shape) (x z : ℕ) (k : Fin 4) :
    sharedBound s t x z 1 1 false k =
      ((residualBudget (afterGcd s x z) (afterGcd t x z) k + ordinaryBudget x z k : ℕ) : ℚ) := by
  have hscale : highScale 1 k = 1 := by fin_cases k <;> rfl
  have hdenom : (if false || (k == 3) then (1 + 1 - 1 : ℕ)^2 else 1 + 1 - 1) = 1 := by
    split <;> rfl
  simp only [sharedBound, hscale, hdenom, Nat.cast_one, div_one, Nat.cast_add]
  exact add_comm _ _
private theorem floor_bound {n : ℕ} {r : ℚ} (h : (n : ℚ) ≤ r) : n ≤ r.floor.toNat := by
  have hi : (n : ℤ) ≤ r.floor := Rat.le_floor_iff.mpr (by exact_mod_cast h)
  simpa using Int.toNat_le_toNat hi
theorem proof : P1_7_4_1.c1 := by
  unfold P1_7_4_1.c1 P1_7_4_1.ZeroLedger
  intro b hempty
  dsimp only
  intro hsJ htJ x z hx hz k
  have h := P1_7_4_2.shared_le_corner (stageAt b 0).free.shape (stageAt b 0).moving.shape
    (r := 1) (m := 1) false k hx hz hsJ htJ
  rw [sharedBound_zero] at h
  simpa only [initialCap, hempty, ite_true] using floor_bound h
end P1_7_4_1_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1_2
open K1_14 (FX Seeds Jet seedHasse)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff)
private theorem seedCoeff_totalDegree (i : Fin 2) (r : ℕ) (P : Seeds) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) FX :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : Seeds →ₐ[FX] MvPolynomial (Option (Fin 2)) FX := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft FX (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) FX)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le FX (Fin 2) (f P) r).trans hf
private theorem seedHasse_coeff (i : Fin 2) (r : ℕ) (P : Jet) (j k : ℕ) :
    ((seedHasse i r P).coeff j).coeff k = seedCoeff i r ((P.coeff j).coeff k) := by
  change ((mapCoeffs (mapCoeffs (seedCoeff i r)) P).coeff j).coeff k = _
  rw [mapCoeffs_coeff, mapCoeffs_coeff]
theorem proof : P1_7_4_1.c2 := by
  intro s P hP i r j k hc
  rw [seedHasse_coeff] at hc ⊢
  have hsource : (P.coeff j).coeff k ≠ 0 := by
    intro hz
    exact hc (by rw [hz, map_zero])
  obtain ⟨hB, hJ, hU⟩ := hP j k hsource
  exact ⟨hB, hJ, (seedCoeff_totalDegree i r _).trans hU⟩
end P1_7_4_1_2
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node agreement)
open P1_7_8 (FixedWord section_capacity)
open K1_13 (Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_3_6 (totalCap topCap)
def mix (b j : ℕ) (a v : ℚ) : ℚ := (↑(b-j : ℕ) : ℚ) * v + j * a
theorem mix_eq {b j : ℕ} (h : j ≤ b) (a v : ℚ) :
    mix b j a v = (b : ℚ) * v + j * (a-v) := by
  unfold mix
  rw [Nat.cast_sub h]
  ring
theorem cast_mixed {b j a v : ℕ} (h : j ≤ b) (hv : v ≤ a) :
    (MvPolynomial.cappedDegreeMixedVolume b j a v : ℚ) = mix b j a v := by
  rw [MvPolynomial.cappedDegreeMixedVolume_eq h hv, mix]
  push_cast
  rfl
theorem section_bound {w : I → K} {T : Finset K} {s : K → K[X]} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc
theorem published_regular {w T s d B J} (hw : FixedWord w T s d)
    (hd₀ : 2 ≤ d) (hd : d < agreement) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      ((P1.t : ℚ) / (agreement - d : ℕ)) *
        mix f.totalDegree (f.degreeOf 1) (totalCap d B) (topCap d B J) + 1 := by
  classical
  have hchart := K1_14_3_6_2.proof
  obtain ⟨C⟩ := hchart f d B J hd₀ (hd.trans (by decide : agreement < 180265)) hJ hb hj
  have hcount := section_capacity hw hd
    (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap d B) (topCap d B J))
    (fun i hi =>
      section_bound hw f hf hfpos hreg (by simp [totalCap])
        (lt_min (by simp [totalCap]) (by omega)) i hi (C.cut (node i) (w i))
        (mem_capped _ (C.total_bound _ _) (C.top_bound _ _))
        (fun γ hγ => C.agrees _ (hw.degree γ hγ) (hreg γ hγ) _ _))
  have hgap : (0 : ℚ) < ((agreement-d : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt hd
  have hc := (le_div_iff₀ hgap).mpr (by exact_mod_cast (mul_comm _ _).trans_le hcount :
    (T.card : ℚ) * (↑(agreement-d : ℕ) : ℚ) ≤
      P1.t * MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1)
        (totalCap d B) (topCap d B J) + (↑(agreement-d : ℕ) : ℚ))
  have hv : topCap d B J ≤ totalCap d B := min_le_left _ _
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hv] at hc
  refine hc.trans_eq ?_
  field_simp
end
end P1_7_4_3
end
section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_3
noncomputable section
open Polynomial PolynomialDifferential
open P1 (K I node p agreement)
open K1_13 (Row Geom extend embed atJet)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14 (seedEmbedding)
open K1_14_3_6 (power totalCap topCap)
open scoped BigOperators
open private specialization_flatten eval_at_center from ProximityPrize.SubmissionLower.Fast073
private theorem solution_taylor {f : Row 2} {S : K[X]} {d : ℕ}
    (hd : d < p) (hS : RegularAt 1 f (extend S)) :
    MvPolynomial.aeval (marked (extend S)) (initialJetSeparant center (chart f)) ≠ 0 ∧
    ∀ j ≤ d, rationalTaylorCoefficient center (chart f) (marked (extend S)) j =
      (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  let P := (extend S).map constants
  have hsol : differentialSpecialization (chart f) P = 0 := by
    change differentialSpecialization (chart f) ((extend S).map constants) = 0
    rw [chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) (extend S) ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) _ ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) _).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked (extend S)) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked (extend S)) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  refine ⟨by rwa [aeval_initialJetSeparant], ?_⟩
  have hcharG : CharP Geom p := charP_of_injective_ringHom embed.injective p
  have : CharP CenterField p := charP_of_injective_ringHom constants.injective p
  have hP : P = S.map seedEmbedding := by
    change (extend S).map constants = _
    rw [Polynomial.map_map]
    rfl
  intro j hj
  rw [← hP]
  refine rationalTaylorCoefficient_eq_solution center (chart f) P hsol hsep j (fun i hi ht => ?_)
  rw [Nat.choose_one_right]
  intro hz
  exact (not_le_of_gt ((ht.trans hj).trans_lt hd))
    (Nat.le_of_dvd (by omega : 0 < i) ((CharP.cast_eq_zero_iff CenterField p i).mp hz))
private theorem short_numerator_bound (f : Row 2) {B J t : ℕ} (hJ : 0 < J)
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) (j : Fin (t+1)) :
    commonTaylorNumerator center (chart f) (power t) j ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let N := commonTaylorNumerator center Q (power t) j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  have htot : N.totalDegree ≤ totalCap t B :=
    (totalDegree_commonTaylorNumerator_le center Q (hτ j)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1)
  exact mem_capped _ htot (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htot)
    ((degreeOf_commonTaylorNumerator_firstOrder_le center Q J (t+1) (power t) hτ hJ
      ((chart_top f).trans hj) j).trans (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) _)))
private theorem short_denominator_bound (f : Row 2) {B J t : ℕ}
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) :
    initialJetSeparant center (chart f) ^ power t ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  have hD₀ : D.totalDegree ≤ totalCap t B :=
    (MvPolynomial.totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _
      ((totalDegree_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1))).trans (Nat.le_add_left _ _))
  have hD₁ : D.degreeOf 1 ≤ power t * (J-1) :=
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _
      ((degreeOf_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_top f).trans hj) 1)))
  exact mem_capped D hD₀ (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hD₀) (hD₁.trans (Nat.le_add_right _ _)))
theorem short_cut (f : Row 2) {d t B J : ℕ} (hd : d < p) (ht : t ≤ d)
    (hJ : 0 < J) (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (sites : Finset I) (hs : d ≤ sites.card + t) (w : I → K) (i : I) :
    ∃ cut : MvPolynomial (Fin 2) CenterField,
      cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) ∧
      ∀ S : K[X], S.natDegree ≤ d → RegularAt 1 f (extend S) →
        (∀ j ∈ sites, S.eval (node j) = w j) →
        (MvPolynomial.aeval (marked (extend S)) cut = 0 ↔ S.eval (node i) = w i) := by
  classical
  obtain ⟨c, a, ha⟩ := P1_7_3.interpolation_weights sites d t hs w (node i)
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  let N (j : Fin (t+1)) := commonTaylorNumerator center Q (power t) j
  let cut := MvPolynomial.C (c - seedEmbedding (w i)) * D + ∑ j, MvPolynomial.C (a j) * N j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  refine ⟨cut, ?_, ?_⟩
  · dsimp only [cut]
    apply Submodule.add_mem
    · rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_denominator_bound f hB hj)
    · apply Submodule.sum_mem
      intro j _
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_numerator_bound f hJ hB hj j)
  · intro S hS hreg hnodes
    obtain ⟨hsep, hcoef⟩ := solution_taylor hd hreg
    have hval := ha (S.map seedEmbedding) (Polynomial.natDegree_map_le.trans hS)
      (fun j hj => by rw [Polynomial.eval_map_apply, hnodes j hj])
    change (S.map seedEmbedding).eval (seedEmbedding (node i)) = _ at hval
    rw [Polynomial.eval_map_apply] at hval
    let x := marked (extend S)
    have he (j : Fin (t+1)) : MvPolynomial.aeval x (N j) =
        MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
      dsimp only [N, D]
      rw [aeval_commonTaylorNumerator center Q x (hτ j) hsep, map_pow,
        hcoef _ ((Nat.le_of_lt_succ j.isLt).trans ht)]
    have hdne : MvPolynomial.aeval x D ≠ 0 := by
      dsimp only [D]
      rw [map_pow]
      exact pow_ne_zero _ hsep
    have hc : MvPolynomial.aeval x cut =
        MvPolynomial.aeval x D * (seedEmbedding (S.eval (node i)) - seedEmbedding (w i)) := by
      dsimp only [cut]
      rw [hval, map_add, map_mul, map_sum, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
        mul_sub, mul_add, Finset.mul_sum]
      simp only [map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, he]
      have hsum : (∑ j : Fin (t+1), a j *
          (MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j)) =
          ∑ j : Fin (t+1), MvPolynomial.aeval x D *
            (a j * (Polynomial.taylor center (S.map seedEmbedding)).coeff j) :=
        Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum]
      ring
    change MvPolynomial.aeval x cut = 0 ↔ _
    rw [hc, mul_eq_zero, or_iff_right hdne, sub_eq_zero, seedEmbedding.injective.eq_iff]
end
end P1_7_4_3
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node agreement blockLength p)
open P1_7_8 (FixedWord)
open P1_7_3 (persistentNodes persistent_card_le hits_persistent section_incidence)
open K1_13 (Row extend)
open K1_13_5 (RegularAt)
open K1_14_3_6 (power totalCap topCap)
open private weights rho_at_endpoint from ProximityPrize.SubmissionLower.UpperBranch3
private def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
private abbrev density : ℚ := (blockLength : ℚ) / agreement
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164398)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 164398) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let w' : P1_7_3.FixedWord w T s d := ⟨hw.distinct, hw.degree, hw.hits⟩
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le w' (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence w' D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)
end
end P1_7_4_3
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node p agreement blockLength HighBand AnchorModel AnchoredFamily)
open P1_7 (degreeAt gap)
open P1_7_4 (ODEGuard fixedFee)
open P1_7_8 (FixedWord)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (totalCap topCap)
open scoped BigOperators
private theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]
theorem proof : P1_7_4.c3 := by
  classical
  intro b u del M Γ F hband B J guard G hG T hT hroot
  let d := degreeAt b.row.hi
  have hdl : 131071 ≤ d := Nat.le_add_right _ _
  have hdu : d ≤ 164398 := Nat.add_le_add_left (P1_7.terminal_guards b).2.1 131071
  have hd : d < agreement := hdu.trans_lt (by decide)
  have hw : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hn
      · simp [hz]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hn
        have hb := hband.2
        change (F.scalar γ).natDegree ≤ 131071 + b.row.hi
        omega
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  let q := agreement - d
  let a := totalCap d B
  let v := topCap d B J
  let β : ℚ := (P1.t : ℚ) / q
  let m := (B-J)*v + J*a
  have hv : v ≤ a := min_le_left _ _
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hq : 0 < q := Nat.sub_pos_of_lt hd
  have hqR : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  unfold fixedFee
  apply le_min
  · have h := fixed_bound hw guard G hG hroot (β*a) (β*v) (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hβ) (fun U hU f hf hp hB hJ hreg => by
        have hc := published_regular (hw.mono hU) (by omega) hd guard.jpos f hf hp hB hJ hreg
        refine hc.trans_eq ?_
        change β * mix f.totalDegree (f.degreeOf 1) a v + 1 = _
        unfold mix
        ring)
    have he : mix B J (β*a) (β*v) = β * m := by unfold mix m; push_cast; ring
    rw [he] at h
    let num := P1.t * m
    let pay := (num + (q-1)) / q
    have hr := Nat.mod_add_div (num + (q-1)) q
    have hlt := Nat.mod_lt (num + (q-1)) hq
    have hn : num ≤ q * pay := by dsimp only [pay]; omega
    have hpay : β * m ≤ (pay : ℚ) := by
      dsimp only [β]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hqR).mpr
      rw [mul_comm (pay : ℚ)]
      exact_mod_cast hn
    change T.card ≤ pay + B^2
    have hfinal : (T.card : ℚ) ≤ (pay : ℚ) + (B^2 : ℕ) :=
      h.trans (add_le_add hpay le_rfl)
    exact_mod_cast hfinal
  · let ap := persistentTotal d B
    let vp := persistentTop d B J
    have ha : 0 ≤ ap := persistentTotal_nonneg d B
    have hvp : 0 ≤ vp := le_min ha (by positivity)
    have h := fixed_bound hw guard G hG hroot ap vp hvp (min_le_left _ _)
      (fun U hU => persistent_regular (hw.mono hU) hdl hdu guard.jpos)
    let r := mix B J ap vp
    have hceil : r ≤ (r.ceil.toNat : ℕ) := by
      have hz : r.ceil ≤ (r.ceil.toNat : ℤ) := Int.self_le_toNat _
      have hcast : (r.ceil : ℚ) ≤ (r.ceil.toNat : ℚ) := by exact_mod_cast hz
      exact Rat.le_ceil.trans hcast
    change T.card ≤ r.ceil.toNat + B^2
    have hfinal : (T.card : ℚ) ≤ (r.ceil.toNat : ℚ) + (B^2 : ℕ) :=
      h.trans (add_le_add hceil le_rfl)
    exact_mod_cast hfinal
end
end P1_7_4_3
end
