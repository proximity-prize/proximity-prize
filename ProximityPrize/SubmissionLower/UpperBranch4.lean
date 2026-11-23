import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.UpperBranch8
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (Stage stages terminal fullCutoff degreeAt  fees )
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
def envelope (s : Stage) : Shape :=
  let a := s.free.shape
  let b := s.moving.shape
  let j := max a.J b.J
  ⟨0, max (a.B-a.J) (b.B-b.J) + j, j, max a.U b.U⟩
def running (v : ℕ → Mass) : ℕ → Mass
  | 0 => fun _ => 0
  | i+1 => fun k => max (running v i k) (v i k)
def weightedBill (n : ℕ) (v : ℕ → Mass) (hist : ℕ → Mass) : ℚ :=
  ∑ i ∈ Finset.range n, dotQ (fun k => running v (i+1) k - running v i k) (hist i)
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
structure ODEGuard (B J : ℕ) : Prop where
  bmin : 2 ≤ B
  jpos : 0 < J
  jb : J ≤ B
  small : B < p
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
open P1_7 (Stage    stages terminal fullCutoff buffered )
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
structure FixedRows {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
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
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open private on_root on_seed moving_graph_count seed_graph_count equal_image_degree
  union_card_le from ProximityPrize.SubmissionLower.Fast062
open scoped BigOperators Classical
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
open P1_7 ( stages terminal   PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c2 : Prop := PairedMass
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
open P1_7_4 (stageAt initialCap initialE  InitialCover OnParent)
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
open P1_7_4 (stageAt introIndices initialCap  introAccount introJump introWeight degreeVector)
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
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1
def c2 : Prop := IntroHasse
end P1_7_4_1
end
section
namespace P1_7_4_1_1
open K1_14 (Shape)
open K1_14_2_2_2 (afterGcd residualBudget ordinaryBudget)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
open P1_7_4 (sharedBound stageAt initialCap)
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
open P1 (K I node p agreement blockLength HighBand AnchorModel AnchoredFamily)
open P1_7 (degreeAt )
open P1_7_4 (ODEGuard )
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (totalCap topCap)
open scoped BigOperators
end
end P1_7_4_3
end
