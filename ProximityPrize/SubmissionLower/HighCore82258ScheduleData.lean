import ProximityPrize.SubmissionLower.UpperBranch4
import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.GoldBranch7

-- merged module HighCore82268JointRankBase
section Merged_HighCore82268JointRankBase

namespace HighCore82268JointRank

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ weightedBill bill_bound)

/-- Insert an additional charge immediately before the old charge at `stop`. -/
def splice {α : Type*} (stop : ℕ) (extra : α) (old : ℕ → α) (i : ℕ) : α :=
  if i < stop then old i else if i = stop then extra else old (i-1)

private theorem sum_splice (old : ℕ → ℚ) (extra : ℚ) {n stop : ℕ} (hstop : stop ≤ n) :
    ∑ i ∈ range (n+1), splice stop extra old i = (∑ i ∈ range n, old i) + extra := by
  induction n with
  | zero =>
    have : stop = 0 := by omega
    subst stop
    simp [splice]
  | succ n ih =>
    rw [sum_range_succ]
    rcases hstop.lt_or_eq with hlt | rfl
    · rw [ih (by omega), sum_range_succ]
      have hs : ¬ n+1 < stop := by omega
      have he : n+1 ≠ stop := by omega
      simp only [splice, ite_eq_right hs, ite_eq_right he, Nat.add_sub_cancel]
      ring
    · have hcong : (∑ i ∈ range (n+1), splice (n+1) extra old i) =
          ∑ i ∈ range (n+1), old i := by
        apply sum_congr rfl
        intro i hi
        simp [splice, mem_range.mp hi]
      rw [hcong]
      simp [splice]

/-- Two exits can use one bill if the nested live sets account for both exits. -/
theorem bill_with_exit (n stop : ℕ) (hstop : stop ≤ n) (w bound : ℕ → Mass)
    (exitWeight exitBound : Mass) (live lost : ℕ → Finset (Ideal Ambient))
    (entry exit : Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ bound i k)
    (entry_next : live stop ⊆ entry) (exit_diff : exit ⊆ entry \ live stop)
    (entry_prev : ∀ i, i+1 = stop → entry ⊆ live i)
    (prev_diff : ∀ i, i+1 = stop → lost i ⊆ live i \ entry)
    (entry_cap : ∀ k, massQ entry k ≤ exitBound k) :
    (∑ i ∈ range n, dotQ (w i) (massQ (lost i))) + dotQ exitWeight (massQ exit) ≤
      weightedBill (n+1) (splice stop exitWeight w) (splice stop exitBound bound) := by
  let l := splice stop entry live
  let f := splice stop exit lost
  have hnext : ∀ i < n+1, l (i+1) ⊆ l i := by
    intro i hi
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · by_cases hs : i+1 = stop
      · simpa [l, splice, hlt, hs] using entry_prev i hs
      · have hs' : i+1 < stop := by omega
        simpa [l, splice, hlt, hs'] using next i (by omega)
    · have hs : ¬ i+1 < i := by omega
      have he : i+1 ≠ i := by omega
      simpa [l, splice, hs, he] using entry_next
    · have hl : ¬ i < stop := by omega
      have he : i ≠ stop := by omega
      have hs : ¬ i+1 < stop := by omega
      have he' : i+1 ≠ stop := by omega
      have hx := next (i-1) (by omega)
      rw [show i-1+1 = i by omega] at hx
      simpa [l, splice, hl, he, hs, he'] using hx
  have hfail : ∀ i < n+1, f i ⊆ l i \ l (i+1) := by
    intro i hi
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · by_cases hs : i+1 = stop
      · simpa [l, f, splice, hlt, hs] using prev_diff i hs
      · have hs' : i+1 < stop := by omega
        simpa [l, f, splice, hlt, hs'] using fail i (by omega)
    · have hs : ¬ i+1 < i := by omega
      have he : i+1 ≠ i := by omega
      simpa [l, f, splice, hs, he] using exit_diff
    · have hl : ¬ i < stop := by omega
      have he : i ≠ stop := by omega
      have hs : ¬ i+1 < stop := by omega
      have he' : i+1 ≠ stop := by omega
      have hx := fail (i-1) (by omega)
      rw [show i-1+1 = i by omega] at hx
      simpa [l, f, splice, hl, he, hs, he'] using hx
  have hcap : ∀ i < n+1, ∀ k, massQ (l i) k ≤ splice stop exitBound bound i k := by
    intro i hi k
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · simpa [l, splice, hlt] using cap i (by omega) k
    · simpa [l, splice] using entry_cap k
    · have hl : ¬ i < stop := by omega
      have he : i ≠ stop := by omega
      simpa [l, splice, hl, he] using cap (i-1) (by omega) k
  have h := bill_bound (n+1) (splice stop exitWeight w) (splice stop exitBound bound)
    l f hnext hfail hcap
  convert h using 1
  rw [← sum_splice (fun i => dotQ (w i) (massQ (lost i))) (dotQ exitWeight (massQ exit)) hstop]
  apply sum_congr rfl
  intro i _
  by_cases hlt : i < stop
  · simp [f, splice, hlt]
  · by_cases heq : i = stop <;> simp [f, splice, hlt, heq]

/-- Linear bound for the nonlinear fixed-jet fee. -/
theorem fixed_fee_linear (L mu tau pivot : ℚ) (hL : 0 ≤ L) (hmu : 0 ≤ mu)
    (htau : 0 ≤ tau) (htau' : tau ≤ 1) {B J Bmax Jmax : ℕ}
    (hJB : J ≤ B) (hB : B ≤ Bmax) (hJ : J ≤ Jmax) :
    let a := mu + 2*L*(B-1 : ℕ)
    let v := min a (L*(2*J-1 : ℕ))
    ((((B-J : ℕ) : ℚ)*v + J*a).ceil.toNat + B^2 : ℕ) ≤
      ((4*L*Bmax*tau+mu-4*L*pivot)*J + (4*L*Jmax*(1-tau)+Bmax)*B+2*L*pivot^2+1 : ℚ) := by
  dsimp only
  let a := mu + 2*L*(B-1 : ℕ)
  let v := min a (L*(2*J-1 : ℕ))
  let q : ℚ := ((B-J : ℕ) : ℚ)*v + J*a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hv : 0 ≤ v := le_min ha (by positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb0 : (0 : ℚ) ≤ B := Nat.cast_nonneg _
  have hj0 : (0 : ℚ) ≤ J := Nat.cast_nonneg _
  have hb : (B : ℚ) ≤ Bmax := by exact_mod_cast hB
  have hj : (J : ℚ) ≤ Jmax := by exact_mod_cast hJ
  have hqceil : 0 ≤ q.ceil := by
    have h : (0 : ℚ) ≤ (q.ceil : ℚ) := hq.trans Rat.le_ceil
    exact_mod_cast h
  have hc : ((q.ceil.toNat : ℕ) : ℚ) ≤ q + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hqceil]
    exact Rat.ceil_lt.le
  have hva : v ≤ 2*L*J := by
    have hd : ((2*J-1 : ℕ) : ℚ) ≤ 2*J := by exact_mod_cast Nat.sub_le (2*J) 1
    exact (min_le_right _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hL])
  have haa : a ≤ mu + 2*L*B := by
    have hd : ((B-1 : ℕ) : ℚ) ≤ B := by exact_mod_cast Nat.sub_le B 1
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left hd hL]
  have hfirst : ((B-J : ℕ) : ℚ)*v ≤ ((B : ℚ)-J)*(2*L*J) := by
    rw [Nat.cast_sub hJB]
    exact mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr (by exact_mod_cast hJB))
  have hsecond := mul_le_mul_of_nonneg_left haa hj0
  have hq' : q ≤ 4*L*B*J + mu*J - 2*L*J^2 := by
    dsimp [q]
    linarith only [hfirst,hsecond]
  have hleft := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*L*tau*J by positivity)
  have hright := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ 4*L*(1-tau)*B by positivity)
  have hsq := mul_le_mul_of_nonneg_left hb hb0
  have htan : -2*L*(J : ℚ)^2 ≤ -4*L*pivot*J + 2*L*pivot^2 := by
    nlinarith only [mul_nonneg hL (sq_nonneg ((J : ℚ)-pivot))]
  change ((q.ceil.toNat + B^2 : ℕ) : ℚ) ≤ _
  push_cast
  nlinarith only [hq', hc, hleft, hright, hsq, htan]

#print axioms bill_with_exit
#print axioms fixed_fee_linear

end HighCore82268JointRank
end Merged_HighCore82268JointRankBase

set_option autoImplicit true
set_option maxRecDepth 18000

set_option autoImplicit true
open HighCore82258 (start finish prefixFee retainedCap)
set_option maxHeartbeats 2000000

section
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (Band K p agreement blockLength AnchorModel AnchoredFamily)
open HighCore82258 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
export P1_7_4 (Mass massQ dotQ capMin pairMinSeed cornerBound pairedCap PairedMass
  degreeVector introWeight introJump envelope running weightedBill ODEGuard)
def stageAt (b : Band) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
theorem stage_mem {b : Band} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b := by
  rw [stageAt, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def laterCount (b : Band) := (stages b).length - 1
def introIndices : Band → List ℕ
  | .h2367 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | .h2395 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  | .h7773 => []
def stopIndex (_ : Band) : ℕ := 0
def introAccount (b : Band) (k : Fin 4) :
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
def initialCap (b : Band) (k : Fin 4) : ℕ :=
  let s := stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : Band) : ℕ :=
  if (introIndices b).isEmpty then
    let s := stageAt b 0
    s.free.shape.U * s.moving.shape.U + (pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def stageCap (b : Band) (i : ℕ) (square : Bool) : Mass :=
  let s := stageAt b i
  pairedCap s.free.shape s.moving.shape s.reserve square
def history (b : Band) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)))
def rankMass (b : Band) : Mass :=
  if stopIndex b = 0 then history b 0
  else capMin (history b (stopIndex b - 1)) (stageCap b (stopIndex b) false)
def rankB (b : Band) : ℕ := (rankMass b 2).floor.toNat
def rankJ (b : Band) : ℕ := (rankMass b 1).floor.toNat
def cutShape (b : Band) (i : ℕ) : Shape :=
  if i < laterCount b then envelope (stageAt b (i+1)) else (terminal b).shape
def cutWeight (b : Band) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape b i) fee k
def seedLimit (b : Band) : ℚ :=
  weightedBill (laterCount b+1) (cutWeight b 0) (history b)
def pointLimit (b : Band) : ℚ :=
  dotQ (running (cutWeight b 2) (laterCount b + 1))
    ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
def lossWeight (b : Band) (a h : ℕ → ℚ) (i : ℕ) : Mass :=
  fun k => a i * cutWeight b 0 i k + h i * cutWeight b 1 i k
def fixedFee (hi B J : ℕ) : ℕ :=
  let d := degreeAt hi
  let q := gap hi
  let lam : ℚ := (blockLength : ℚ) / agreement
  let mu : ℚ := ((blockLength-d : ℕ) : ℚ) / q
  let ap := mu + 2*lam*d*(B-1 : ℕ)
  let vp := min ap (lam*d*(2*J-1 : ℕ))
  (((B-J : ℕ) : ℚ)*vp + J*ap).ceil.toNat+B^2
def jointRank : Band → Bool
  | .h2367 => true
  | _ => false

theorem jointRank_start (b : Band) (h : jointRank b = true) : start b < 7773 := by
  cases b <;> simp [jointRank] at h
  decide

def rankTau (_ : Band) : ℚ := (49/100)
def rankPivot (_ : Band) : ℚ := (47843/5)

end
end HighCore82258_3
end

namespace HighCore82258JointRank
open HighCore82258 (Band agreement blockLength degreeAt finish gap)
open HighCore82258_3 (rankMass)
open P1_7_4 (Mass)
def lambdaDegree (b : Band) : ℚ := (blockLength : ℚ) / agreement * degreeAt (finish b)
def mu (b : Band) : ℚ := ((blockLength-degreeAt (finish b) : ℕ) : ℚ) / gap (finish b)
def capB (b : Band) : ℕ := (rankMass b 2).floor.toNat+2
def capJ (b : Band) : ℕ := (rankMass b 1).floor.toNat+1

def rankCharge (b : Band) (tau pivot : ℚ) : Mass :=
  ![0, 4*lambdaDegree b*capB b*tau+mu b-4*lambdaDegree b*pivot,
    4*lambdaDegree b*capJ b*(1-tau)+capB b, 0]

def rankRounding (b : Band) (tau pivot : ℚ) : ℚ :=
  rankCharge b tau pivot 1 + 2*rankCharge b tau pivot 2 + 2*lambdaDegree b*pivot^2 + 1

end HighCore82258JointRank

section
namespace HighCore82258_3
noncomputable section
open HighCore82258 (Band K p agreement AnchorModel AnchoredFamily InBand degreeAt stages fees fullCutoff terminal curveUnit)
open K1_14 (Shape)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open HighCore82268JointRank (splice)
open HighCore82258JointRank (rankCharge rankRounding)

def lossCount (b : Band) : ℕ := laterCount b + 1 + (if jointRank b then 1 else 0)

def lossWeights (b : Band) (a h : ℕ → ℚ) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankCharge b (rankTau b) (rankPivot b)) (lossWeight b a h)
  else lossWeight b a h

def lossHistory (b : Band) : ℕ → Mass :=
  if jointRank b then splice (stopIndex b) (rankMass b) (history b) else history b

def lossOffset (b : Band) : ℚ :=
  if jointRank b then rankRounding b (rankTau b) (rankPivot b) else 0

def FixedCount : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → ∀ B J : ℕ, ODEGuard B J →
    ∀ G : ODE, ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ fixedFee (finish b) B J

def fixedBudget (b : Band) : ℕ :=
  let price (s : Shape) := fixedFee (finish b) s.B s.J
  ∑ i ∈ Finset.range (stages b).length,
    (price (stageAt b i).free.shape + price (stageAt b i).moving.shape)
structure BankGuard (hi reserve : ℕ) (s : Shape) : Prop where
  ode : ODEGuard s.B s.J
  seed_small : s.U < p
  pos : 0 < s.m * agreement
  buffer : 2*hi*reserve ≤ fullCutoff s
structure ScheduleOK (b : Band) : Prop where
  stages_pos : 0 < (stages b).length
  zero : (stageAt b 0).reserve = 0
  later_pos : ∀ i < laterCount b, 0 < (stageAt b (i+1)).reserve
  small_reserve : ∀ i < (stages b).length, (stageAt b i).reserve < p
  stop_le : stopIndex b ≤ laterCount b
  intro_pos : ∀ i ∈ introIndices b, 0 < i ∧ i < (stages b).length
  intro_asc : (introIndices b).Pairwise (· < ·)
  stage_guard : ∀ i < (stages b).length,
    let s := stageAt b i
    BankGuard (finish b) s.reserve s.free.shape ∧ BankGuard (finish b) s.reserve s.moving.shape
  terminal_guard : BankGuard (finish b) 0 (terminal b).shape
  initial_small : ∀ k, initialCap b k < p
  initial_e_ge : initialCap b 3 ≤ initialE b
  content_small : (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U < p
  rank_guard : ODEGuard (rankB b) (rankJ b)
  low_seed : (p+1)*initialCap b 2 + initialE b ≤ (fees b).lowSeed
  low_jet : initialCap b 0 + (if jointRank b then 0 else fixedFee (finish b) (rankB b) (rankJ b)) ≤ (fees b).lowJet
  fixed : fixedBudget b ≤ (fees b).fixedODE
  content : (p+1)*((stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U) ≤ (fees b).content
structure RateOK (hi : ℕ) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ) / 81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1 - a*g/((p+1 : ℕ) : ℚ)) * curveUnit hi g ≤ h
structure LossLedger (b : Band) : Prop where
  seed_small : seedLimit b < (p : ℚ)
  points : pointLimit b ≤ ((fees b).point : ℚ)
  discount : (start b) < 7773 →
    ∃ a h : ℕ → ℚ,
      (∀ i ≤ laterCount b, RateOK (finish b) (a i) (h i) ∧
        min (seedLimit b) (dotQ (cutWeight b 0 i) (history b i)) ≤ a i) ∧
      weightedBill (lossCount b) (lossWeights b a h) (lossHistory b) + seedLimit b + lossOffset b ≤
        ((fees b).loss : ℚ)
  rank_guard : jointRank b = true →
    0 ≤ rankTau b ∧ rankTau b ≤ 1 ∧ 0 ≤ rankCharge b (rankTau b) (rankPivot b) 1 ∧
      (rankMass b 2).floor.toNat + 2 < p
  direct : 7773 ≤ (start b) → ((p+1 : ℕ) : ℚ) * seedLimit b ≤ ((fees b).loss : ℚ)

end
end HighCore82258_3
end