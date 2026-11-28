import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0561
import ProximityPrize.SubmissionLower.R6966ProofPhysicalHelperTariff
import ProximityPrize.SubmissionLower.Z6969Pack0559

set_option Elab.async false

-- Source: Research6969.PrefixRescueRegular
section Z6969Source0636
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

namespace Lower6960.Prefix6969Rescue

noncomputable section

open Polynomial Finset ProximityPrize.Benchmark
open K1 (K I p)
open K1_14 (Jet FX Shape atX graphEval jetAt)
open K1_14_2 (OnJet)
open K1_14_2_2 (CutCover RowCaps)
open K1_14_2_2_2_1 (jetDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective)
open Research6966
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open Research6969
open scoped Classical Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds

abbrev graphShape (a u : ℕ) : Shape := ⟨0, a, 1, u⟩

abbrev denominator (G : Jet) : Eqn (Fin 2) FX := G.coeff 1
abbrev numerator (G : Jet) : Eqn (Fin 2) FX := -G.coeff 0

def regular (G : Jet) (z : K) (S : Polynomial K) : Prop :=
  evaluate (NativeLostCurve.seed z) (atX S) (denominator G) ≠ 0

private theorem evaluation_eq (P : Eqn (Fin 2) FX) (z : K) (S : Polynomial K) :
    evaluate (NativeLostCurve.seed z) (atX S) P = P.eval₂ (graphEval z) (atX S) := rfl

theorem graph_law {G : Jet} (slope : G.natDegree = 1) {z : K} {S : Polynomial K}
    (root : jetAt G z S = 0) :
    evaluate (NativeLostCurve.seed z) (atX S) (denominator G) * atX S.derivative =
      evaluate (NativeLostCurve.seed z) (atX S) (numerator G) := by
  simp only [evaluation_eq]
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change ev G = 0 at root
  have id := congrArg ev (eq_X_add_C_of_natDegree_le_one slope.le)
  simp only [ev, map_add, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X] at id
  unfold numerator denominator
  rw [eval₂_neg]
  apply eq_neg_of_add_eq_zero_left
  exact id.symm.trans root

private theorem seed_cap {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u))
    (j i : ℕ) : ((G.coeff j).coeff i).totalDegree ≤ u := by
  by_cases hz : (G.coeff j).coeff i = 0
  · simp [hz]
  · exact (caps j i hz).2.2

theorem coefficient_cap {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) (j : ℕ) :
    cap (fun _ => 1) u (G.coeff j) := by
  intro i
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  change m.weight (fun _ => 1) ≤ u
  rw [← Finsupp.degree_eq_weight_one]
  exact (MvPolynomial.le_totalDegree hm).trans (seed_cap caps j i)

private theorem denominator_degree {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) :
    (denominator G).natDegree ≤ a - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_contra hn
  have hb := (caps 1 i hn).1
  change i + 1 ≤ a at hb
  omega

private theorem numerator_degree {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) :
    (numerator G).natDegree ≤ a := by
  rw [show numerator G = -G.coeff 0 from rfl, natDegree_neg]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_contra hn
  have hb := (caps 0 i hn).1
  change i + 0 ≤ a at hb
  omega

theorem regular_cut_count {u₀ deleted} {M : Model u₀ deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T ⊆ Γ) (C : CutCover)
    (inside : ∀ z∈T, ∃ Q∈C.curves, OnMark F Q z)
    {G : Jet} {a u d : ℕ} (ha : 2 ≤ a) (hu : 0 < u) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u))
    (roots : ∀ z∈T, jetAt G (M.label z) (F.scalar z) = 0)
    (good : ∀ z∈T, regular G (M.label z) (F.scalar z))
    (dp : 0 < d) (gap : d < 179730) (deg : ∀ z∈T, (F.scalar z).natDegree ≤ d) :
    (T.card : ℚ) ≤ ((u * C.cost 0 + (a-1) * C.cost 1 : ℕ) : ℚ) *
      MarkedAdaptive.price 262144 d 179730 := by
  have bcap : cap (fun _ => 1) u (numerator G) := by
    intro i
    rw [show numerator G = -G.coeff 0 from rfl, coeff_neg]
    exact Submodule.neg_mem _ (coefficient_cap caps 0 i)
  have possible : 179730 ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have tame : d < p := gap.trans (by decide)
  have numDegree : (numerator G).natDegree ≤ a - 1 + 1 :=
    (numerator_degree caps).trans (by omega)
  have bound := NativeLostCurve.cut_count F sub C inside
    (show 1 ≤ a - 1 by omega) hu dp gap possible tame
    (denominator G) (numerator G) (denominator_degree caps) numDegree (coefficient_cap caps 1)
    bcap deg (fun z hz => graph_law slope (roots z hz)) good
  simpa only [IRSProfile.card_index] using bound

theorem singular_count {u₀ deleted} {M : Model u₀ deleted} {Γ T : Finset K}
    (F : Family M Γ) {G : Jet} {a u : ℕ} (prime : Prime G) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u)) (small : (2 * a - 1) * u < p)
    (roots : ∀ z∈T, jetAt G (M.label z) (F.scalar z) = 0)
    (bad : ∀ z∈T, ¬ regular G (M.label z) (F.scalar z)) :
    T.card ≤ (2 * a - 1) * ((p + 1) * u) := by
  let H := PhysicalHelperTariff.graphOf G
  let N := PhysicalHelperTariff.realization prime slope
  have prim := PhysicalHelperTariff.primitive prime slope
  have graph : H.graphDegree ≤ a := by
    rw [← HelperWeightCap.native_degree N prim]
    apply (K1_14_2_2_2_1.jetDegree_le G a).mpr
    intro j i nz
    exact (caps j i nz).1
  have char : (2 * H.graphDegree - 1) * u < p := by
    exact (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ graph) _)).trans_lt small
  have coeff (j i : ℕ) (z : Fin 2) : ((G.coeff j).coeff i).degreeOf z ≤ u :=
    (((G.coeff j).coeff i).degreeOf_le_totalDegree z).trans (seed_cap caps j i)
  have zeros (z : K) (hz : z∈T) :
      (G.coeff 1).eval₂ (graphEval (M.label z)) (atX (F.scalar z)) = 0 := by
    have hb := not_ne_iff.mp (bad z hz)
    simpa only [regular, denominator, evaluation_eq] using hb
  have other (z : K) (hz : z∈T) :
      (-G.coeff 0).eval₂ (graphEval (M.label z)) (atX (F.scalar z)) = 0 := by
    have law := graph_law slope (roots z hz)
    rw [evaluation_eq, evaluation_eq, zeros z hz, zero_mul] at law
    exact law.symm
  have bound := NativeGraphExceptional.singular_count N prim (fun _ => u) coeff char
    T M.label (label_injective M).injOn (fun z => atX (F.scalar z)) zeros other
  exact bound.trans (by
    have rate : 2 * H.graphDegree - 1 ≤ 2 * a - 1 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left _ graph) _
    calc
      _ ≤ (2 * a - 1) * (u + p * u) := Nat.mul_le_mul_right _ rate
      _ = _ := by ring)


end
end Lower6960.Prefix6969Rescue
end Z6969Source0636

-- Source: Research6969.PrefixRescueInvoice
section Z6969Source0637
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient fixedAt ODE)
open K1_14_2_2 (ODECaps RowCaps mass mass_mono weight dot)
open K1_14_3 (seed_count scalar_atX_injective)
open P1_7_4 (Mass massQ dotQ dotQ_scale_add weightedBill bill_bound ODEGuard)
open HighCore82268JointRank (fixed_fee_linear)
open Prefix6969Wide (lambda mu fixedFee_eq)
open Prefix6969Rates (fixedFee fixed_count fixed_word endpointDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Research6969
open scoped BigOperators Classical

private theorem ceil_up (q : ℚ) : q ≤ (q.ceil.toNat : ℚ) := by
  have hn : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact Rat.le_ceil.trans hn

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  exact_mod_cast bound.trans (ceil_up q)

def incidence : ℚ := MarkedAdaptive.price 262144 endpointDegree 179730
def seedRate (u : ℕ) : ℕ := (incidence * u).ceil.toNat + 4
def ordRate (a : ℕ) : ℕ := (incidence * (a - 1 : ℕ) + mu).ceil.toNat + 4

theorem seed_le (u : ℕ) : incidence * u ≤ (seedRate u : ℚ) :=
  (ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4)

theorem ord_le (a : ℕ) : incidence * (a - 1 : ℕ) ≤ (ordRate a : ℚ) := by
  have h : incidence * (a - 1 : ℕ) ≤ incidence * (a - 1 : ℕ) + mu :=
    le_add_of_nonneg_right (by decide +kernel)
  exact h.trans ((ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4))

def rankB (plan : Plan) : ℕ := plan.initialCap 2 + 2
def rankJ (plan : Plan) : ℕ := plan.initialCap 1 + 1
def pivot (plan : Plan) (τ scale : ℚ) : ℚ := min (scale * rankJ plan) (τ * rankB plan)
def rankWeight (plan : Plan) (τ scale : ℚ) : Mass :=
  ![0, 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale,
    4*lambda*rankJ plan*(1-τ) + rankB plan, 0]
def rankRound (plan : Plan) (τ scale : ℚ) : ℚ :=
  rankWeight plan τ scale 1 + 2*rankWeight plan τ scale 2 + 2*lambda*(pivot plan τ scale)^2 + 1

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

def rankMarks : Finset K :=
  Γ.filter (fun γ => ∃ J∈R.initial.rankExit, OnMark F J γ)
def seedMarks : Finset K :=
  Γ.filter (fun γ => R.initial.seeds.Covers (M.label γ))
def ordinateMarks : Finset K :=
  Γ.filter (fun γ => atX (F.scalar γ) ∈ R.initial.ordinates)
def singularMarks (G : Jet) : Finset K :=
  Γ.filter (fun γ => ¬ regular G (M.label γ) (F.scalar γ))

theorem seed_count : (seedMarks R).card ≤ (p+1) * plan.initialCap 2 + plan.initialCap 3 := by
  have h := K1_14_3.seed_count (T := seedMarks R) (label_injective M).injOn R.initial.seeds
    (R.initial.seed_degree.trans_lt (plan.initial_small 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ R.initial.seed_degree) R.initial.seed_points)

theorem ordinate_count : (ordinateMarks R).card ≤ plan.initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ => atX (F.scalar γ))
    (fun _ hγ => (mem_filter.mp hγ).2) ?_).trans R.initial.ordinate_card
  intro γ hγ δ hδ same
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (scalar_atX_injective same)

theorem rank_count (hi : M.overhead.toNat ≤ 2411) {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1)
    (small : rankB plan < p) :
    ((rankMarks R).card : ℚ) ≤ dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) +
      rankRound plan τ scale := by
  let S := R.initial.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E, caps, roots⟩ := R.initial.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ plan.initialCap k :=
    (mass_mono (subset_union_left : S ⊆ R.initial.rankExit ∪ R.initial.parents) k).trans
      (R.initial.fits k)
  have hBm : B ≤ mass S 2 + 2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1 + 1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B ≤ rankB plan := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J ≤ rankJ plan := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree ≤ B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1, (le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), hJB, hB.trans_lt small⟩
  have count : (rankMarks R).card ≤ fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ hγ => roots γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have lin := fixed_fee_linear lambda mu τ (pivot plan τ scale)
    (by decide +kernel) (by decide +kernel) htau htau' hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight plan τ scale 1 * J +
      rankWeight plan τ scale 2 * B + 2*lambda*(pivot plan τ scale)^2 + 1 := by
    rw [fixedFee_eq]
    exact lin
  have pmax : pivot plan τ scale ≤ τ * rankB plan := min_le_right _ _
  have hlambda : (0 : ℚ) ≤ 4 * lambda := by decide +kernel
  have hmu : (0 : ℚ) ≤ mu := by decide +kernel
  have cj : 0 ≤ rankWeight plan τ scale 1 := by
    change 0 ≤ 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale
    have key := mul_le_mul_of_nonneg_left pmax hlambda
    linarith only [hmu, show 4*lambda*pivot plan τ scale ≤ 4*lambda*rankB plan*τ by
      calc _ ≤ _ := key
           _ = _ := by ring]
  have cB : 0 ≤ rankWeight plan τ scale 2 := by
    change 0 ≤ 4*lambda*rankJ plan*(1-τ) + rankB plan
    exact add_nonneg (mul_nonneg (mul_nonneg hlambda (Nat.cast_nonneg _)) (sub_nonneg.mpr htau'))
      (Nat.cast_nonneg _)
  have hJq : (J : ℚ) ≤ (mass S 1 : ℚ) + 1 := by exact_mod_cast hJm
  have hBq : (B : ℚ) ≤ (mass S 2 : ℚ) + 2 := by exact_mod_cast hBm
  have advanceJ := mul_le_mul_of_nonneg_left hJq cj
  have advanceB := mul_le_mul_of_nonneg_left hBq cB
  have expand : dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) =
      rankWeight plan τ scale 1 * (mass S 1 : ℚ) + rankWeight plan τ scale 2 * (mass S 2 : ℚ) := by
    simp [dotQ, rankWeight, massQ, Fin.sum_univ_succ, S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [expand, rankRound]
  linarith only [advanceJ, advanceB]

variable {R} (B : Book R)

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k => weight (B.shape i) fee k
def seedLimit : ℚ := weightedBill B.steps (cutWeight B 0) B.capacity
def pointLimit : ℚ := weightedBill B.steps (cutWeight B 2) (fun _ k => plan.initialCap k)

theorem costQ {i : ℕ} (hi : i < B.steps) (fee : Fin 3) :
    ((B.cut i).cost fee : ℚ) ≤ dotQ (cutWeight B fee i) (massQ (B.lost i)) := by
  exact (by simpa only [cutWeight,dotQ,dot,massQ,Book.lost,Nat.cast_sum,Nat.cast_mul] using
    ((Nat.cast_le (α := ℚ)).mpr (B.cut_cost i hi fee)))

theorem seed_bill : (∑ i∈range B.steps, ((B.cut i).cost 0 : ℚ)) ≤ seedLimit B :=
  (sum_le_sum fun _ hi => costQ B (mem_range.mp hi) 0).trans
    (bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.bound i hi))

def pointMarks : Finset K := (range B.steps).biUnion (fun i => (B.cut i).direct)

theorem point_bill : ((pointMarks B).card : ℚ) ≤ pointLimit B := by
  calc
    _ ≤ ∑ i∈range B.steps, ((B.cut i).cost 2 : ℚ) := by
      exact_mod_cast (show (pointMarks B).card ≤ ∑ i∈range B.steps,(B.cut i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range B.steps, dotQ (cutWeight B 2 i) (massQ (B.lost i)) :=
      sum_le_sum fun i hi => costQ B (mem_range.mp hi) 2
    _ ≤ _ := bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.initial_bound i hi)

def regularCutMarks (i : ℕ) : Finset K :=
  Γ.filter (fun γ => regular G (M.label γ) (F.scalar γ) ∧
    ∃ Q∈(B.cut i).curves, OnMark F Q γ)

def lossWeight (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * cutWeight B 0 i k + (ordRate a : ℚ) * cutWeight B 1 i k

theorem curve_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (hiM : M.overhead.toNat ≤ 2411)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {i : ℕ} (hi : i < B.steps) :
    ((regularCutMarks B i).card : ℚ) ≤ dotQ (lossWeight B a u i) (massQ (B.lost i)) := by
  let T := regularCutMarks B i
  have sub : T ⊆ Γ := filter_subset _ _
  have deg := fixed_word F hiM sub
  have cut := regular_cut_count F sub (B.cut i)
    (fun γ hγ => (mem_filter.mp hγ).2.2) ha hu slope caps
    (fun γ hγ => roots γ (sub hγ)) (fun γ hγ => (mem_filter.mp hγ).2.1)
    (by decide : 0 < endpointDegree) (by decide) deg.degree
  have shape : (T.card : ℚ) ≤ incidence * (u : ℚ) * (B.cut i).cost 0 +
      incidence * (a - 1 : ℕ) * (B.cut i).cost 1 := by
    push_cast at cut
    unfold incidence
    linarith only [cut]
  calc
    _ ≤ (seedRate u : ℚ) * (B.cut i).cost 0 + (ordRate a : ℚ) * (B.cut i).cost 1 :=
      shape.trans (add_le_add (mul_le_mul_of_nonneg_right (seed_le _) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (ord_le _) (Nat.cast_nonneg _)))
    _ ≤ (seedRate u : ℚ) * dotQ (cutWeight B 0 i) (massQ (B.lost i)) +
        (ordRate a : ℚ) * dotQ (cutWeight B 1 i) (massQ (B.lost i)) :=
      add_le_add (mul_le_mul_of_nonneg_left (costQ B hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (costQ B hi 1) (Nat.cast_nonneg _))
    _ = _ := by rw [dotQ_scale_add]; rfl

def lossMarks : Finset K := rankMarks R ∪ (range B.steps).biUnion (regularCutMarks B)
def paid : Finset K :=
  ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R)) ∪ singularMarks (M := M) (F := F) G

def eventCut (shape : ℕ → K1_14.Shape) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (shape i) fee k

def eventLossWeight (shape : ℕ → K1_14.Shape) (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * eventCut shape 0 i k + (ordRate a : ℚ) * eventCut shape 1 i k

def eventRunning (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (a u : ℕ) (τ scale : ℚ) : Mass :=
  P1_7_4.running (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u)) (steps + 1)

def eventLossLimit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℚ :=
  weightedBill (steps + 1) (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u))
    (beforeCuts (fun k => plan.initialCap k) capacity) +
    weightedBill steps (eventCut shape 0) capacity + rankRound plan τ scale

def eventFee (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℕ :=
  (eventLossLimit plan steps shape capacity a u τ scale).ceil.toNat +
    (weightedBill steps (eventCut shape 2) (fun _ k => plan.initialCap k)).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)

def lossLimit (a u : ℕ) (τ scale : ℚ) : ℚ :=
  eventLossLimit plan B.steps B.shape B.capacity a u τ scale

def fee (a u : ℕ) (τ scale : ℚ) : ℕ :=
  eventFee plan B.steps B.shape B.capacity a u τ scale

theorem eventFee_eq (a u : ℕ) (τ scale : ℚ) :
    fee B a u τ scale = eventFee plan B.steps B.shape B.capacity a u τ scale := rfl

theorem eventRunning_eq (a u : ℕ) (τ scale : ℚ) :
    P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) =
      eventRunning plan B.steps B.shape a u τ scale := rfl

def charge (credit : Fin 4 → ℕ) : ℕ := ∑ k, credit k * mass B.final k

theorem paid_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (small : (2*a-1)*u < p) (hiM : M.overhead.toNat ≤ 2411)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ) (retained : ∀ k, (credit k : ℚ) ≤
      P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) k) :
    (paid B).card + charge B credit ≤ fee B a u τ scale := by
  have cuts := sum_le_sum (fun i (mem : i ∈ range B.steps) =>
    curve_count B ha hu slope caps hiM roots (mem_range.mp mem))
  have lossRail : ((lossMarks B).card : ℚ) ≤ ((rankMarks R).card : ℚ) +
      ∑ i∈range B.steps, ((regularCutMarks B i).card : ℚ) := by
    exact_mod_cast (show (lossMarks B).card ≤ (rankMarks R).card +
      ∑ i∈range B.steps, (regularCutMarks B i).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have subtotal := lossRail.trans (add_le_add (rank_count R hiM (scale := scale) htau htau' rankSmall) cuts)
  have joint := B.joint_bill (rankWeight plan τ scale) (lossWeight B a u)
  have creditBill : (charge B credit : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
        (B.steps+1)) (massQ B.final) := by
    unfold charge dotQ massQ
    push_cast
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (retained k) (Nat.cast_nonneg _)
  have seedNonneg : 0 ≤ seedLimit B := le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (seed_bill B)
  have loss : (lossMarks B).card + charge B credit ≤ (lossLimit B a u τ scale).ceil.toNat := by
    apply card_round
    push_cast
    change _ ≤ weightedBill (B.steps + 1)
      (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
      (beforeCuts (fun k => plan.initialCap k) B.capacity) + seedLimit B + rankRound plan τ scale
    linarith only [subtotal, joint, creditBill, seedNonneg]
  have point := card_round (point_bill B)
  have singular : (singularMarks (M:=M) (F:=F) G).card ≤ (2*a-1)*((p+1)*u) :=
    singular_count F prime slope caps small (fun γ hγ => roots γ (mem_filter.mp hγ).1)
      (fun _ hγ => (mem_filter.mp hγ).2)
  have union₀ := card_union_le ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R))
    (singularMarks (M:=M) (F:=F) G)
  have union₁ := card_union_le (lossMarks B ∪ pointMarks B) (seedMarks R ∪ ordinateMarks R)
  have union₂ := card_union_le (lossMarks B) (pointMarks B)
  have union₃ := card_union_le (seedMarks R) (ordinateMarks R)
  have seed := seed_count R
  have ord := ordinate_count R
  unfold paid
  change _ ≤ (lossLimit B a u τ scale).ceil.toNat + (pointLimit B).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 + (2*a-1)*((p+1)*u)
  omega

/-- Every graph mark is paid by this actual book or lies on a surviving parent. -/
theorem paid_cover {γ : K} (mem : γ ∈ Γ) (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ ∈ paid B ∨ ∃ J∈B.final, OnMark F J γ := by
  by_cases bad : ¬ regular G (M.label γ) (F.scalar γ)
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, bad⟩))
  have good := not_not.mp bad
  rcases B.cut_marks mem root with seed | ord | rank | lost | final
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,rank⟩)))))
  · obtain ⟨i, hi, hit | hit⟩ := lost
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,hit⟩))))
    · have mark : γ ∈ (range B.steps).biUnion (regularCutMarks B) := mem_biUnion.mpr ⟨i,mem_range.mpr hi,
        mem_filter.mpr ⟨mem,good,hit⟩⟩
      exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
  · exact Or.inr final


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0637

-- Source: Research6969.PrefixRescueEvent
section Z6969Source0638
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (RowCaps)
open Far6969RescueGeometry (Model Family OnMark)

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Event (R : Run F Crt G plan) (survivors : Finset (Ideal Ambient))
    (feeBound : ℕ) (credit : Fin 4 → ℕ) where
  book : Book R
  final : book.final = survivors
  count : (paid book).card + charge book credit ≤ feeBound
  cover : ∀ γ∈Γ, γ ∈ paid book ∨ ∃ J∈survivors, OnMark F J γ

variable (R : Run F Crt G plan) {a u : ℕ}
variable (ha : 2 ≤ a) (hu : 0 < u)
variable (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
variable (small : (2*a-1)*u < p) (hi : M.overhead.toNat ≤ 2411)
variable (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
variable {τ scale : ℚ} (t0 : 0 ≤ τ) (t1 : τ ≤ 1) (rankSmall : rankB plan < p)
variable {bound : ℕ} (credit : Fin 4 → ℕ)

include ha hu prime slope caps small hi roots t0 t1 rankSmall

private theorem event_of_book (B : Book R) {survivors : Finset (Ideal Ambient)}
    (final : B.final = survivors)
    (checkFee : eventFee plan B.steps B.shape B.capacity a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan B.steps B.shape a u τ scale k) :
    Nonempty (Event R survivors bound credit) := by
  refine ⟨B, final, ?_, ?_⟩
  · exact (paid_count B ha hu prime slope caps small hi roots t0 t1 rankSmall credit
      (fun k => by rw [eventRunning_eq B a u τ scale]; exact checkCredit k)).trans checkFee
  · intro γ mem
    rw [← final]
    exact paid_cover B mem (roots γ mem)

/-- A certificate at a real early stop prices precisely the rows preceding that stop. -/
theorem early_event {stop : ℕ} (fits : stop < plan.count)
    (checkFee : eventFee plan stop plan.cutShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan stop plan.cutShape a u τ scale k) :
    Nonempty (Event R (R.live stop) bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.early R stop fits
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]

/-- The normal event adds the last cut from the production terminal bank. -/
theorem normal_event
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (checkFee : eventFee plan plan.count plan.normalShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤
      eventRunning plan plan.count plan.normalShape a u τ scale k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0638

-- Source: Research6969.PrefixRescueMiddleInvoice
section Z6969Source0639
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.MiddleInvoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient fixedAt ODE)
open K1_14_2_2 (ODECaps RowCaps mass mass_mono weight dot)
open K1_14_3 (seed_count scalar_atX_injective)
open P1_7_4 (Mass massQ dotQ dotQ_scale_add weightedBill bill_bound ODEGuard)
open HighCore82268JointRank (fixed_fee_linear)
open Prefix6969Middle (lambda mu fixedFee_eq)
open Prefix6969MiddleRates (fixedFee fixed_count fixed_word endpointDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Research6969
open scoped BigOperators Classical

private theorem ceil_up (q : ℚ) : q ≤ (q.ceil.toNat : ℚ) := by
  have hn : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact Rat.le_ceil.trans hn

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  exact_mod_cast bound.trans (ceil_up q)

def incidence : ℚ := MarkedAdaptive.price 262144 endpointDegree 179730
def seedRate (u : ℕ) : ℕ := (incidence * u).ceil.toNat + 4
def ordRate (a : ℕ) : ℕ := (incidence * (a - 1 : ℕ) + mu).ceil.toNat + 4

theorem seed_le (u : ℕ) : incidence * u ≤ (seedRate u : ℚ) :=
  (ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4)

theorem ord_le (a : ℕ) : incidence * (a - 1 : ℕ) ≤ (ordRate a : ℚ) := by
  have h : incidence * (a - 1 : ℕ) ≤ incidence * (a - 1 : ℕ) + mu :=
    le_add_of_nonneg_right (by decide +kernel)
  exact h.trans ((ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4))

def rankB (plan : Plan) : ℕ := plan.initialCap 2 + 2
def rankJ (plan : Plan) : ℕ := plan.initialCap 1 + 1
def pivot (plan : Plan) (τ scale : ℚ) : ℚ := min (scale * rankJ plan) (τ * rankB plan)
def rankWeight (plan : Plan) (τ scale : ℚ) : Mass :=
  ![0, 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale,
    4*lambda*rankJ plan*(1-τ) + rankB plan, 0]
def rankRound (plan : Plan) (τ scale : ℚ) : ℚ :=
  rankWeight plan τ scale 1 + 2*rankWeight plan τ scale 2 + 2*lambda*(pivot plan τ scale)^2 + 1

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

def rankMarks : Finset K :=
  Γ.filter (fun γ => ∃ J∈R.initial.rankExit, OnMark F J γ)
def seedMarks : Finset K :=
  Γ.filter (fun γ => R.initial.seeds.Covers (M.label γ))
def ordinateMarks : Finset K :=
  Γ.filter (fun γ => atX (F.scalar γ) ∈ R.initial.ordinates)
def singularMarks (G : Jet) : Finset K :=
  Γ.filter (fun γ => ¬ regular G (M.label γ) (F.scalar γ))

theorem seed_count : (seedMarks R).card ≤ (p+1) * plan.initialCap 2 + plan.initialCap 3 := by
  have h := K1_14_3.seed_count (T := seedMarks R) (label_injective M).injOn R.initial.seeds
    (R.initial.seed_degree.trans_lt (plan.initial_small 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ R.initial.seed_degree) R.initial.seed_points)

theorem ordinate_count : (ordinateMarks R).card ≤ plan.initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ => atX (F.scalar γ))
    (fun _ hγ => (mem_filter.mp hγ).2) ?_).trans R.initial.ordinate_card
  intro γ hγ δ hδ same
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (scalar_atX_injective same)

theorem rank_count (hi : M.overhead.toNat ≤ 2557) {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1)
    (small : rankB plan < p) :
    ((rankMarks R).card : ℚ) ≤ dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) +
      rankRound plan τ scale := by
  let S := R.initial.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E, caps, roots⟩ := R.initial.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ plan.initialCap k :=
    (mass_mono (subset_union_left : S ⊆ R.initial.rankExit ∪ R.initial.parents) k).trans
      (R.initial.fits k)
  have hBm : B ≤ mass S 2 + 2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1 + 1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B ≤ rankB plan := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J ≤ rankJ plan := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree ≤ B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1, (le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), hJB, hB.trans_lt small⟩
  have count : (rankMarks R).card ≤ fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ hγ => roots γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have lin := fixed_fee_linear lambda mu τ (pivot plan τ scale)
    (by decide +kernel) (by decide +kernel) htau htau' hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight plan τ scale 1 * J +
      rankWeight plan τ scale 2 * B + 2*lambda*(pivot plan τ scale)^2 + 1 := by
    rw [fixedFee_eq]
    exact lin
  have pmax : pivot plan τ scale ≤ τ * rankB plan := min_le_right _ _
  have hlambda : (0 : ℚ) ≤ 4 * lambda := by decide +kernel
  have hmu : (0 : ℚ) ≤ mu := by decide +kernel
  have cj : 0 ≤ rankWeight plan τ scale 1 := by
    change 0 ≤ 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale
    have key := mul_le_mul_of_nonneg_left pmax hlambda
    linarith only [hmu, show 4*lambda*pivot plan τ scale ≤ 4*lambda*rankB plan*τ by
      calc _ ≤ _ := key
           _ = _ := by ring]
  have cB : 0 ≤ rankWeight plan τ scale 2 := by
    change 0 ≤ 4*lambda*rankJ plan*(1-τ) + rankB plan
    exact add_nonneg (mul_nonneg (mul_nonneg hlambda (Nat.cast_nonneg _)) (sub_nonneg.mpr htau'))
      (Nat.cast_nonneg _)
  have hJq : (J : ℚ) ≤ (mass S 1 : ℚ) + 1 := by exact_mod_cast hJm
  have hBq : (B : ℚ) ≤ (mass S 2 : ℚ) + 2 := by exact_mod_cast hBm
  have advanceJ := mul_le_mul_of_nonneg_left hJq cj
  have advanceB := mul_le_mul_of_nonneg_left hBq cB
  have expand : dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) =
      rankWeight plan τ scale 1 * (mass S 1 : ℚ) + rankWeight plan τ scale 2 * (mass S 2 : ℚ) := by
    simp [dotQ, rankWeight, massQ, Fin.sum_univ_succ, S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [expand, rankRound]
  linarith only [advanceJ, advanceB]

variable {R} (B : Book R)

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k => weight (B.shape i) fee k
def seedLimit : ℚ := weightedBill B.steps (cutWeight B 0) B.capacity
def pointLimit : ℚ := weightedBill B.steps (cutWeight B 2) (fun _ k => plan.initialCap k)

theorem costQ {i : ℕ} (hi : i < B.steps) (fee : Fin 3) :
    ((B.cut i).cost fee : ℚ) ≤ dotQ (cutWeight B fee i) (massQ (B.lost i)) := by
  exact (by simpa only [cutWeight,dotQ,dot,massQ,Book.lost,Nat.cast_sum,Nat.cast_mul] using
    ((Nat.cast_le (α := ℚ)).mpr (B.cut_cost i hi fee)))

theorem seed_bill : (∑ i∈range B.steps, ((B.cut i).cost 0 : ℚ)) ≤ seedLimit B :=
  (sum_le_sum fun _ hi => costQ B (mem_range.mp hi) 0).trans
    (bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.bound i hi))

def pointMarks : Finset K := (range B.steps).biUnion (fun i => (B.cut i).direct)

theorem point_bill : ((pointMarks B).card : ℚ) ≤ pointLimit B := by
  calc
    _ ≤ ∑ i∈range B.steps, ((B.cut i).cost 2 : ℚ) := by
      exact_mod_cast (show (pointMarks B).card ≤ ∑ i∈range B.steps,(B.cut i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range B.steps, dotQ (cutWeight B 2 i) (massQ (B.lost i)) :=
      sum_le_sum fun i hi => costQ B (mem_range.mp hi) 2
    _ ≤ _ := bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.initial_bound i hi)

def regularCutMarks (i : ℕ) : Finset K :=
  Γ.filter (fun γ => regular G (M.label γ) (F.scalar γ) ∧
    ∃ Q∈(B.cut i).curves, OnMark F Q γ)

def lossWeight (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * cutWeight B 0 i k + (ordRate a : ℚ) * cutWeight B 1 i k

theorem curve_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (hiM : M.overhead.toNat ≤ 2557)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {i : ℕ} (hi : i < B.steps) :
    ((regularCutMarks B i).card : ℚ) ≤ dotQ (lossWeight B a u i) (massQ (B.lost i)) := by
  let T := regularCutMarks B i
  have sub : T ⊆ Γ := filter_subset _ _
  have deg := fixed_word F hiM sub
  have cut := regular_cut_count F sub (B.cut i)
    (fun γ hγ => (mem_filter.mp hγ).2.2) ha hu slope caps
    (fun γ hγ => roots γ (sub hγ)) (fun γ hγ => (mem_filter.mp hγ).2.1)
    (by decide : 0 < endpointDegree) (by decide) deg.degree
  have shape : (T.card : ℚ) ≤ incidence * (u : ℚ) * (B.cut i).cost 0 +
      incidence * (a - 1 : ℕ) * (B.cut i).cost 1 := by
    push_cast at cut
    unfold incidence
    linarith only [cut]
  calc
    _ ≤ (seedRate u : ℚ) * (B.cut i).cost 0 + (ordRate a : ℚ) * (B.cut i).cost 1 :=
      shape.trans (add_le_add (mul_le_mul_of_nonneg_right (seed_le _) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (ord_le _) (Nat.cast_nonneg _)))
    _ ≤ (seedRate u : ℚ) * dotQ (cutWeight B 0 i) (massQ (B.lost i)) +
        (ordRate a : ℚ) * dotQ (cutWeight B 1 i) (massQ (B.lost i)) :=
      add_le_add (mul_le_mul_of_nonneg_left (costQ B hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (costQ B hi 1) (Nat.cast_nonneg _))
    _ = _ := by rw [dotQ_scale_add]; rfl

def lossMarks : Finset K := rankMarks R ∪ (range B.steps).biUnion (regularCutMarks B)
def paid : Finset K :=
  ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R)) ∪ singularMarks (M := M) (F := F) G

def eventCut (shape : ℕ → K1_14.Shape) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (shape i) fee k

def eventLossWeight (shape : ℕ → K1_14.Shape) (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * eventCut shape 0 i k + (ordRate a : ℚ) * eventCut shape 1 i k

def eventRunning (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (a u : ℕ) (τ scale : ℚ) : Mass :=
  P1_7_4.running (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u)) (steps + 1)

def eventLossLimit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℚ :=
  weightedBill (steps + 1) (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u))
    (beforeCuts (fun k => plan.initialCap k) capacity) +
    weightedBill steps (eventCut shape 0) capacity + rankRound plan τ scale

def eventFee (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℕ :=
  (eventLossLimit plan steps shape capacity a u τ scale).ceil.toNat +
    (weightedBill steps (eventCut shape 2) (fun _ k => plan.initialCap k)).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)

def lossLimit (a u : ℕ) (τ scale : ℚ) : ℚ :=
  eventLossLimit plan B.steps B.shape B.capacity a u τ scale

def fee (a u : ℕ) (τ scale : ℚ) : ℕ :=
  eventFee plan B.steps B.shape B.capacity a u τ scale

theorem eventFee_eq (a u : ℕ) (τ scale : ℚ) :
    fee B a u τ scale = eventFee plan B.steps B.shape B.capacity a u τ scale := rfl

theorem eventRunning_eq (a u : ℕ) (τ scale : ℚ) :
    P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) =
      eventRunning plan B.steps B.shape a u τ scale := rfl

def charge (credit : Fin 4 → ℕ) : ℕ := ∑ k, credit k * mass B.final k

theorem paid_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (small : (2*a-1)*u < p) (hiM : M.overhead.toNat ≤ 2557)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ) (retained : ∀ k, (credit k : ℚ) ≤
      P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) k) :
    (paid B).card + charge B credit ≤ fee B a u τ scale := by
  have cuts := sum_le_sum (fun i (mem : i ∈ range B.steps) =>
    curve_count B ha hu slope caps hiM roots (mem_range.mp mem))
  have lossRail : ((lossMarks B).card : ℚ) ≤ ((rankMarks R).card : ℚ) +
      ∑ i∈range B.steps, ((regularCutMarks B i).card : ℚ) := by
    exact_mod_cast (show (lossMarks B).card ≤ (rankMarks R).card +
      ∑ i∈range B.steps, (regularCutMarks B i).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have subtotal := lossRail.trans (add_le_add (rank_count R hiM (scale := scale) htau htau' rankSmall) cuts)
  have joint := B.joint_bill (rankWeight plan τ scale) (lossWeight B a u)
  have creditBill : (charge B credit : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
        (B.steps+1)) (massQ B.final) := by
    unfold charge dotQ massQ
    push_cast
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (retained k) (Nat.cast_nonneg _)
  have seedNonneg : 0 ≤ seedLimit B := le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (seed_bill B)
  have loss : (lossMarks B).card + charge B credit ≤ (lossLimit B a u τ scale).ceil.toNat := by
    apply card_round
    push_cast
    change _ ≤ weightedBill (B.steps + 1)
      (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
      (beforeCuts (fun k => plan.initialCap k) B.capacity) + seedLimit B + rankRound plan τ scale
    linarith only [subtotal, joint, creditBill, seedNonneg]
  have point := card_round (point_bill B)
  have singular : (singularMarks (M:=M) (F:=F) G).card ≤ (2*a-1)*((p+1)*u) :=
    singular_count F prime slope caps small (fun γ hγ => roots γ (mem_filter.mp hγ).1)
      (fun _ hγ => (mem_filter.mp hγ).2)
  have union₀ := card_union_le ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R))
    (singularMarks (M:=M) (F:=F) G)
  have union₁ := card_union_le (lossMarks B ∪ pointMarks B) (seedMarks R ∪ ordinateMarks R)
  have union₂ := card_union_le (lossMarks B) (pointMarks B)
  have union₃ := card_union_le (seedMarks R) (ordinateMarks R)
  have seed := seed_count R
  have ord := ordinate_count R
  unfold paid
  change _ ≤ (lossLimit B a u τ scale).ceil.toNat + (pointLimit B).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 + (2*a-1)*((p+1)*u)
  omega

/-- Every graph mark is paid by this actual book or lies on a surviving parent. -/
theorem paid_cover {γ : K} (mem : γ ∈ Γ) (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ ∈ paid B ∨ ∃ J∈B.final, OnMark F J γ := by
  by_cases bad : ¬ regular G (M.label γ) (F.scalar γ)
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, bad⟩))
  have good := not_not.mp bad
  rcases B.cut_marks mem root with seed | ord | rank | lost | final
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,rank⟩)))))
  · obtain ⟨i, hi, hit | hit⟩ := lost
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,hit⟩))))
    · have mark : γ ∈ (range B.steps).biUnion (regularCutMarks B) := mem_biUnion.mpr ⟨i,mem_range.mpr hi,
        mem_filter.mpr ⟨mem,good,hit⟩⟩
      exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
  · exact Or.inr final


end
end Lower6960.Prefix6969Rescue.MiddleInvoice
end Z6969Source0639

-- Source: Research6969.PrefixRescueMiddleEvent
section Z6969Source0640
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.MiddleInvoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (RowCaps)
open Far6969RescueGeometry (Model Family OnMark)

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Event (R : Run F Crt G plan) (survivors : Finset (Ideal Ambient))
    (feeBound : ℕ) (credit : Fin 4 → ℕ) where
  book : Book R
  final : book.final = survivors
  count : (paid book).card + charge book credit ≤ feeBound
  cover : ∀ γ∈Γ, γ ∈ paid book ∨ ∃ J∈survivors, OnMark F J γ

variable (R : Run F Crt G plan) {a u : ℕ}
variable (ha : 2 ≤ a) (hu : 0 < u)
variable (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
variable (small : (2*a-1)*u < p) (hi : M.overhead.toNat ≤ 2557)
variable (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
variable {τ scale : ℚ} (t0 : 0 ≤ τ) (t1 : τ ≤ 1) (rankSmall : rankB plan < p)
variable {bound : ℕ} (credit : Fin 4 → ℕ)

include ha hu prime slope caps small hi roots t0 t1 rankSmall

private theorem event_of_book (B : Book R) {survivors : Finset (Ideal Ambient)}
    (final : B.final = survivors)
    (checkFee : eventFee plan B.steps B.shape B.capacity a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan B.steps B.shape a u τ scale k) :
    Nonempty (Event R survivors bound credit) := by
  refine ⟨B, final, ?_, ?_⟩
  · exact (paid_count B ha hu prime slope caps small hi roots t0 t1 rankSmall credit
      (fun k => by rw [eventRunning_eq B a u τ scale]; exact checkCredit k)).trans checkFee
  · intro γ mem
    rw [← final]
    exact paid_cover B mem (roots γ mem)

/-- A certificate at a real early stop prices precisely the rows preceding that stop. -/
theorem early_event {stop : ℕ} (fits : stop < plan.count)
    (checkFee : eventFee plan stop plan.cutShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan stop plan.cutShape a u τ scale k) :
    Nonempty (Event R (R.live stop) bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.early R stop fits
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]

/-- The normal event adds the last cut from the production terminal bank. -/
theorem normal_event
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (checkFee : eventFee plan plan.count plan.normalShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤
      eventRunning plan plan.count plan.normalShape a u τ scale k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]


end
end Lower6960.Prefix6969Rescue.MiddleInvoice
end Z6969Source0640

-- Source: Research6969.PrefixRescueSurfaceHandoff
section Z6969Source0641
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (toJet)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ massQ_mono)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open Far6969RescueGeometry (Model Family OnMark OnSurface word)
open scoped Classical

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable {R : Run F Crt G plan}

theorem Book.final_initial (B : Book R) : B.final ⊆ R.live 0 := by
  have sub (n : ℕ) (hn : n ≤ B.steps) : B.live n ⊆ B.live 0 := by
    induction n with
    | zero => exact subset_rfl
    | succ n ih => exact (B.next n (by omega)).trans (ih (by omega))
  rw [R.live_start, ← B.start]
  exact sub B.steps le_rfl

theorem Book.paid_or_regular {γ : K1.K} (B : Book R) (mem : γ∈Γ)
    (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ∈paid B ∨ regular G (M.label γ) (F.scalar γ) ∧
      ∃ J∈B.final, OnMark F J γ := by
  by_cases good : regular G (M.label γ) (F.scalar γ)
  · rcases paid_cover B mem root with hit | survivor
    · exact Or.inl hit
    · exact Or.inr ⟨good, survivor⟩
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, good⟩))

/-- Both terminal modes yield genuine parent surfaces for all unpaid graph marks. -/
theorem Book.surfaces (B : Book R) :
    ∃ S : Finset Surface,
      (∀ q∈S, Parent q ∧ ∃ J∈B.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈Γ, (∃ J∈B.final, OnMark F J γ) → ∃ q∈S, OnSurface F q γ := by
  let getGeom (J : B.final) := R.parent_geom (Book.final_initial B J.property)
  let surface (J : B.final) := surfaceOf J.val (getGeom J).1.prime
  let S := B.final.attach.image surface
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    obtain ⟨J, _, rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1, J.val, J.property, rfl⟩
  · rintro γ _ ⟨J, hJ, on⟩
    let q : B.final := ⟨J, hJ⟩
    refine ⟨surface q, mem_image.mpr ⟨q, mem_attach _ _, rfl⟩, ?_⟩
    intro P mem
    rw [← K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Book.terminal_parent (B : Book R) (final : B.final = R.terminal)
    {q : Surface} {J : Ideal K1_14_2.Ambient} (mem : J∈B.final)
    (origin : q.asIdeal = J.comap toJet) :
    Prefix6969Wide.SurfacePass Crt (word M) q ∧ G∈q.asIdeal := by
  have pass := (mem_filter.mp (final ▸ mem)).2
  have zero := (R.parent_geom (Book.final_initial B mem)).2.2.2.1
  refine ⟨?_, ?_⟩
  · intro s fit P inside
    rw [origin]
    exact pass s fit P inside
  · rw [origin]
    exact zero

theorem Run.mass_terminal (R : Run F Crt G plan) (k : Fin 4) :
    massQ R.terminal k ≤ plan.history (plan.count - 1) k := by
  have fits : plan.count - 1 < plan.count := by have := plan.positive; omega
  exact (massQ_mono (filter_subset _ _) k).trans (R.live_mass (plan.count-1) fits k)


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0641

-- Source: Research6969.PrefixRescueProducer
section Z6969Source0642
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ Mass)
open Far6969RescueGeometry (Model Family OnMark OnSurface)
open Prefix6969Main (Band)
open Research6966

structure EarlyPrice where
  degree : ℕ
  seed : ℕ
  stop : ℕ
  tau : ℚ
  scale : ℚ
  credit : Fin 4 → ℕ
  fee : ℕ

namespace EarlyPrice

def calculatedFee (x : EarlyPrice) (plan : Plan) : Band → ℕ
  | .near => Invoice.eventFee plan x.stop plan.cutShape plan.history x.degree x.seed x.tau x.scale
  | .middle => MiddleInvoice.eventFee plan x.stop plan.cutShape plan.history x.degree x.seed x.tau x.scale

def running (x : EarlyPrice) (plan : Plan) : Band → Mass
  | .near => Invoice.eventRunning plan x.stop plan.cutShape x.degree x.seed x.tau x.scale
  | .middle => MiddleInvoice.eventRunning plan x.stop plan.cutShape x.degree x.seed x.tau x.scale

structure Valid (x : EarlyPrice) (plan : Plan) (band : Band) : Prop where
  fits : x.stop < plan.count
  degree_min : 2 ≤ x.degree
  seed_pos : 0 < x.seed
  char : (2*x.degree-1)*x.seed < p
  graph_shape : plan.primeShape = graphShape x.degree x.seed
  slope_floor : plan.slopeFloor = 1
  tau_nonneg : 0 ≤ x.tau
  tau_le_one : x.tau ≤ 1
  rank_small : Invoice.rankB plan < p
  exact_fee : x.calculatedFee plan band ≤ x.fee
  retained : ∀ k, (x.credit k : ℚ) ≤ x.running plan band k

end EarlyPrice

/-- The same early rescue producer supplies a full-credit invoice at either height band. -/
theorem early_prefix {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {plan : Plan} {first : ℕ} {band : Band} {x : EarlyPrice}
    (S : plan.Sources first band.last) (cert : x.Valid plan band)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ (R : Run F Crt G plan) (B : Book R) (Q : Finset Surface),
      B.final = R.live x.stop ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee ∧
      (∀ k, massQ B.final k ≤ plan.history x.stop k) ∧
      (∀ q∈Q, Parent q ∧ G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈Invoice.paid B ∨
        (regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈Q, OnSurface F q γ) := by
  obtain ⟨R⟩ := S.run F Crt lo hi noPole residues phys prime
    (le_of_eq (cert.slope_floor.trans slope.symm)) seeded caps degree seed physical
  have geomCaps : RowCaps G (graphShape x.degree x.seed) := cert.graph_shape ▸ caps
  have bill : ∃ B : Book R, B.final = R.live x.stop ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee := by
    cases band
    · obtain ⟨event⟩ := Invoice.early_event R cert.degree_min cert.seed_pos prime slope geomCaps
        cert.char hi roots cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit cert.fits
        cert.exact_fee cert.retained
      exact ⟨event.book, event.final, event.count⟩
    · obtain ⟨event⟩ := MiddleInvoice.early_event R cert.degree_min cert.seed_pos prime slope geomCaps
        cert.char hi roots cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit cert.fits
        cert.exact_fee cert.retained
      exact ⟨event.book, event.final, event.count⟩
  obtain ⟨B, bend, count⟩ := bill
  obtain ⟨surfaces, geom, marked⟩ := Invoice.Book.surfaces B
  refine ⟨R, B, surfaces, bend, count, ?_, ?_, ?_⟩
  · intro k
    rw [bend]
    exact R.live_mass _ cert.fits k
  · intro q mem
    obtain ⟨parent, J, live, origin⟩ := geom q mem
    have inIdeal : G∈q.asIdeal := by
      rw [origin]
      exact (R.parent_geom (Invoice.Book.final_initial B live)).2.2.2.1
    exact ⟨parent, inIdeal, J, live, origin⟩
  · intro γ mem
    rcases Invoice.Book.paid_or_regular B mem (roots γ mem) with paid | ⟨reg, survivor⟩
    · exact Or.inl paid
    · exact Or.inr ⟨reg, marked γ mem survivor⟩

end
end Lower6960.Prefix6969Rescue
end Z6969Source0642

-- Source: Research6969.PrefixPairedProducer
section Z6969Source0643
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Pair
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ)
open Far6969RescueGeometry (Model Family OnSurface word)
open Prefix6969Main (Band)
open PrefixRows (Common)
open Research6966
open scoped Classical

def zeros {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) : Finset K :=
  Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ) = 0)

def zeros_family {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) :
    Family M (zeros F G) :=
  ⟨F.scalar, fun γ hγ => F.mark γ (mem_filter.mp hγ).1, F.distinct.mono (filter_subset _ _)⟩

/-- One paired production theorem for every saved early rescue event. -/
theorem produce {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {first extra a low floor : ℕ} {outer : P1_7.Bank} {band : Band}
    {main : Prefix6969Main.Plan} {mp : Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main band)
    (mainSource : main.Sources first band.last outer extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : Prefix6969Rescue.EarlyPrice}
    (rescueSource : rescue.Sources first band.last) (rescuePrice : rp.Valid rescue band)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Prefix6969Main.Rows main F Crt) (I : Prefix6969Main.Initial R)
      (Q : Prefix6969Rescue.Run (zeros_family F G) Crt G rescue)
      (B : Prefix6969Rescue.Book Q) (paid : Finset K) (A S : Finset Surface),
      B.final=Q.live rp.stop ∧
      paid.card + mp.charge I.final + Prefix6969Rescue.Invoice.charge B rp.credit ≤ mp.fee+rp.fee ∧
      (∀ k, massQ I.final k ≤ main.history main.last k) ∧
      (∀ k, massQ B.final k ≤ rescue.history rp.stop k) ∧
      (∀ q∈A, Parent q ∧ Prefix6969Main.SurfacePass Crt (word M) q) ∧
      (∀ q∈A, ∃ J∈I.final, q.asIdeal=J.comap toJet) ∧
      (∀ q∈S, Parent q ∧ G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈paid ∨ (jetAt G (M.label γ) (F.scalar γ) ≠ 0 ∧ ∃ q∈A, OnSurface F q γ) ∨
        (jetAt G (M.label γ) (F.scalar γ) = 0 ∧ Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧
          ∃ q∈S, OnSurface F q γ) := by
  obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
    Prefix6969Main.main_prefix F Crt main mainValid band mp mainPrice mainSource firstPos lo hi
      noPole residues phys known mainDegree mainSeed mainFloor
  have subRes : ∀ γ∈zeros F G, MarkResidues D (M.label γ) ((zeros_family F G).scalar γ) :=
    fun γ hγ => residues γ (mem_filter.mp hγ).1
  have roots : ∀ γ∈zeros F G, jetAt G (M.label γ) ((zeros_family F G).scalar γ) = 0 :=
    fun γ hγ => (mem_filter.mp hγ).2
  obtain ⟨Q, B, S, bend, rescueCount, rescueMass, rescueGeom, rescueCover⟩ :=
    Prefix6969Rescue.early_prefix (zeros_family F G) (Crt := Crt) rescueSource rescuePrice lo hi noPole subRes
      phys prime slope seeded caps rescueDegree rescueSeed rescueFloor roots
  refine ⟨R, I, Q, B, C.paid ∪ Prefix6969Rescue.Invoice.paid B, A, S, bend,
    ?_, mainMass, rescueMass, mainGeom, mainOrigin, rescueGeom, ?_⟩
  · have union := card_union_le C.paid (Prefix6969Rescue.Invoice.paid B)
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
    · rcases rescueCover γ (mem_filter.mpr ⟨hγ, root⟩) with paid | ⟨reg, on⟩
      · exact Or.inl (mem_union_right _ paid)
      · exact Or.inr (Or.inr ⟨root, reg, on⟩)
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
      rcases mainCover γ inMain with paid | on
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr (Or.inl ⟨root, on⟩)

end
end Lower6960.Prefix6969Pair
end Z6969Source0643
