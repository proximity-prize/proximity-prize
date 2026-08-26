import ProximityPrize.SubmissionLower.BCHKSResidualFlatBasisCount6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusHighSupportMaxRank6401

/-!
# Multi-pin rank accumulation at score 64.01

The older residual-flat count keeps only tuples whose every prefix is
independent.  Sampling more pins is stronger.  If a prefix of length `j` has
rank `s`, at most `F_s` row coordinates lie in its closure, so among the
`a-j` unused coordinates at least `a-F_s` increase the rank.

This file records the division-free backward recurrence for that process and
the exact score-6401 integer certificate.  It does **not** assert the missing
upstream claim that all benchmark owners live in one fixed normal space.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSMultiPinRankAccumulation6401

open BCHKSResidualFlatBasisCount6401
open BCHKSFrobeniusHighSupportMaxRank6401
open BCHKSTwoFrobeniusWeakCurveSeed6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

def multiPinAmbient6401 : Nat := 262144
def multiPinRow6401 : Nat := 185354
def multiPinDegreeCap6401 : Nat := 131071
def multiPinFinalFlatCap6401 : Nat := 153578
def multiPinOwnerMass6401 : Nat := 273591190752810939

/-- Flat cap for a residual parameter `rho`, whose normal-space dimension is
`R=rho+1`.  The state `s=rho` uses the rational final-flat cap. -/
def multiPinFlatCap6401 (rho s : Nat) : Nat :=
  if s < rho then multiPinDegreeCap6401 - rho + s + 1
  else multiPinFinalFlatCap6401

/-- One backward coupling step.  `low` is the number of certified successful
continuations after a rank-preserving choice and `high` after a rank-increasing
choice. -/
def multiPinStepWeight
    (a cap j low high : Nat) : Nat :=
  (a - cap) * high + (cap - j) * low

/-- Incidence averaging with an arbitrary owner-fibre cap.  This is the
form needed by multi-pin accumulation: a spanning injective tuple need not
determine one owner, but under failure of the weak affine-curve conclusion it
belongs to at most `1182` owner rows. -/
theorem ownerCard_mul_tupleMass_le_descFactorial_mul_fiberCap6401
    {U Owner : Type*} [DecidableEq U] [DecidableEq Owner]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (P : (t : Nat) → (Fin t → U) → Prop) [∀ t, DecidablePred (P t)]
    (t mass fiberCap : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, mass ≤ (goodTuples (A z) P t).card)
    (hfiber : ∀ f ∈ goodTuples Uset P t,
      (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card ≤ fiberCap)
    (hinj : ∀ f ∈ goodTuples Uset P t, Function.Injective f) :
    S.card * mass ≤ Uset.card.descFactorial t * fiberCap := by
  classical
  have hlower : S.card * mass ≤
      ∑ z ∈ S, (goodTuples (A z) P t).card := by
    calc
      S.card * mass = ∑ _z ∈ S, mass := by simp
      _ ≤ ∑ z ∈ S, (goodTuples (A z) P t).card :=
        Finset.sum_le_sum hrow
  have hswap : (∑ z ∈ S, (goodTuples (A z) P t).card) =
      ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
    calc
      (∑ z ∈ S, (goodTuples (A z) P t).card) =
          ∑ z ∈ S, ∑ f ∈ goodTuples Uset P t,
            if f ∈ goodTuples (A z) P t then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.card_filter]
        congr 1
        ext f
        simp only [Finset.mem_filter]
        constructor
        · intro hf
          refine ⟨?_, hf⟩
          rw [mem_goodTuples_iff] at hf ⊢
          exact ⟨fun i ↦ hsub z hz (hf.1 i), hf.2⟩
        · exact And.right
      _ = ∑ f ∈ goodTuples Uset P t, ∑ z ∈ S,
          if f ∈ goodTuples (A z) P t then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ f ∈ goodTuples Uset P t,
          (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := by
        apply Finset.sum_congr rfl
        intro f hf
        simp
  have hgood := goodTuples_card_le_descFactorial Uset P t hinj
  calc
    S.card * mass ≤ ∑ z ∈ S, (goodTuples (A z) P t).card := hlower
    _ = ∑ f ∈ goodTuples Uset P t,
        (S.filter fun z ↦ f ∈ goodTuples (A z) P t).card := hswap
    _ ≤ ∑ _f ∈ goodTuples Uset P t, fiberCap :=
      Finset.sum_le_sum hfiber
    _ = (goodTuples Uset P t).card * fiberCap := by simp
    _ ≤ Uset.card.descFactorial t * fiberCap :=
      Nat.mul_le_mul_right fiberCap hgood

/-- Linear-flat specialization of the capped incidence swap. -/
theorem ownerCard_mul_linearFlatGaps_le_descFactorial_mul_fiberCap6401
    {U Owner F V : Type*} [DecidableEq U] [DecidableEq Owner]
    [Field F] [AddCommGroup V] [Module F V]
    (Uset : Finset U) (S : Finset Owner) (A : Owner → Finset U)
    (normal : U → V) (flatCap : Nat → Nat) (a t fiberCap : Nat)
    (hsub : ∀ z ∈ S, A z ⊆ Uset)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hflat : ∀ z ∈ S, ∀ s < t,
      ∀ f ∈ goodTuples (A z)
          (independentNormalTuples (F := F) normal) s,
        (normalSpanFlat (F := F) (A z) normal f).card ≤ flatCap s)
    (hfiber : ∀ f ∈ goodTuples Uset
        (independentNormalTuples (F := F) normal) t,
      (S.filter fun z ↦ f ∈ goodTuples (A z)
        (independentNormalTuples (F := F) normal) t).card ≤ fiberCap) :
    S.card * (∏ s ∈ Finset.range t, (a - flatCap s)) ≤
      Uset.card.descFactorial t * fiberCap := by
  apply ownerCard_mul_tupleMass_le_descFactorial_mul_fiberCap6401
    Uset S A (independentNormalTuples (F := F) normal) t
      (∏ s ∈ Finset.range t, (a - flatCap s)) fiberCap hsub
  · intro z hz
    exact prod_gaps_le_goodTuples_card (A z)
      (independentNormalTuples (F := F) normal)
      (fun s ↦ a - flatCap s) t
      (independentNormalTuples_zero normal)
      (fun _s f x hs ↦
        (independentNormalTuples_snoc_iff normal f x).mp hs |>.1)
      (fun s hs f hf ↦ independent_tupleExtensions_card_gap
        (A z) normal f hf (hrow z hz) (hflat z hz s hs f hf))
  · exact hfiber
  · intro f hf
    have hli := (mem_goodTuples_iff Uset
      (independentNormalTuples (F := F) normal)).mp hf |>.2
    intro i j hij
    exact hli.injective (congrArg normal hij)

/-- The exact algebra behind the stochastic coupling.  If successful-tail
weight is monotone in the rank, replacing the true number of rank increases
by its lower bound `a-cap` can only decrease the successful count. -/
theorem multiPinStepWeight_le_actual
    (a cap j low high raises stays : Nat)
    (hjcap : j ≤ cap) (hcapa : cap ≤ a)
    (hmono : low ≤ high)
    (hpartition : raises + stays = a - j)
    (hraise : a - cap ≤ raises) :
    multiPinStepWeight a cap j low high ≤
      raises * high + stays * low := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmono
  have hsplit : (a - cap) + (cap - j) = a - j := by omega
  calc
    multiPinStepWeight a cap j low (low + d) =
        (a - j) * low + (a - cap) * d := by
      simp only [multiPinStepWeight]
      rw [← hsplit]
      ring
    _ ≤ (a - j) * low + raises * d := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right d hraise) _
    _ = raises * (low + d) + stays * low := by
      rw [← hpartition]
      ring

/-! ## Executable backward dynamic program

The array has entries for states `0,...,R`.  The terminal array is one only
at the spanning state `R`.  Starting at time `t`, the fold runs backwards
through `j=t-1,...,0`.  At state `R` every unused coordinate is harmless;
below `R` it uses `multiPinStepWeight`.
-/

def multiPinTerminalLayer (rho : Nat) : Array Nat :=
  Array.ofFn fun s : Fin (rho + 2) =>
    if rho + 1 ≤ s.1 then 1 else 0

def multiPinBackwardStep6401
    (rho j : Nat) (next : Array Nat) : Array Nat :=
  Array.ofFn fun s : Fin (rho + 2) =>
    if rho + 1 ≤ s.1 then
      (multiPinRow6401 - j) * next[s.1]!
    else
      multiPinStepWeight multiPinRow6401
        (multiPinFlatCap6401 rho s.1) j
        next[s.1]! next[s.1 + 1]!

/-- Check the monotonic-tail premise at one dynamic-program layer. -/
def multiPinLayerMonotone (rho : Nat) (layer : Array Nat) : Bool :=
  (List.range (rho + 1)).all fun s => layer[s]! ≤ layer[s + 1]!

/-- The first component is the final backward layer.  The second component
checks tail monotonicity at every layer used by the coupling. -/
def multiPinRun6401 (rho t : Nat) : Array Nat × Bool :=
  (List.range t).foldl
    (fun state q =>
      let current := multiPinBackwardStep6401 rho (t - q - 1) state.1
      (current, state.2 && multiPinLayerMonotone rho current))
    (multiPinTerminalLayer rho, multiPinLayerMonotone rho
      (multiPinTerminalLayer rho))

/-- Certified number of ordered distinct row tuples whose normals span the
`rho+1` dimensional normal space in the pessimistic coupling. -/
def multiPinSpanningMass6401 (rho t : Nat) : Nat :=
  (multiPinRun6401 rho t).1[0]!

/-! ## Pure polynomial-evaluation normals

For the global affine-residual coefficient span, every proper flat is cut out
by a nonzero degree-at-most-`131071` polynomial.  Thus the same cap applies at
every state below full rank; no special rational final flat is needed.
-/

def pureEvalBackwardStep6401
    (rho j : Nat) (next : Array Nat) : Array Nat :=
  Array.ofFn fun s : Fin (rho + 2) =>
    if rho + 1 ≤ s.1 then
      (multiPinRow6401 - j) * next[s.1]!
    else
      multiPinStepWeight multiPinRow6401 multiPinDegreeCap6401 j
        next[s.1]! next[s.1 + 1]!

def pureEvalMultiPinRun6401 (rho t : Nat) : Array Nat × Bool :=
  (List.range t).foldl
    (fun state q =>
      let current := pureEvalBackwardStep6401 rho (t - q - 1) state.1
      (current, state.2 && multiPinLayerMonotone rho current))
    (multiPinTerminalLayer rho, multiPinLayerMonotone rho
      (multiPinTerminalLayer rho))

def pureEvalMultiPinSpanningMass6401 (rho t : Nat) : Nat :=
  (pureEvalMultiPinRun6401 rho t).1[0]!

/-- Exact cap and time-window validity for the closing `rho=34,t=71`
instance. -/
theorem rho34_flatCaps_valid6401
    (s j : Nat) (hs : s ≤ 34) (hj : j ≤ 71) :
    j ≤ multiPinFlatCap6401 34 s ∧
      multiPinFlatCap6401 34 s ≤ multiPinRow6401 := by
  simp only [multiPinFlatCap6401]
  split_ifs <;>
    norm_num [multiPinDegreeCap6401, multiPinFinalFlatCap6401,
      multiPinRow6401] at * <;> omega

/-- The monotone-tail premise needed by the one-step coupling holds at every
layer of the concrete closing recurrence. -/
theorem rho34_t71_tailMonotonicity6401 :
    (multiPinRun6401 34 71).2 = true := by
  native_decide

/-- Exact integer certificate for the claimed improvement from residual
dimension `<25` to parameter `rho=34` (normal dimension `35`).  Division by
the ambient falling factorial leaves more than `1183` owners. -/
theorem rho34_t71_retains_1183_exact6401 :
    weakCurveOutput6401 * multiPinAmbient6401.descFactorial 71 ≤
      multiPinOwnerMass6401 * multiPinSpanningMass6401 34 71 := by
  native_decide

/-- The adjacent parameter genuinely misses, even with its scanned choice
`t=73`; hence the arithmetic extension stops at `rho=34`. -/
theorem rho35_t73_misses_1183_exact6401 :
    multiPinOwnerMass6401 * multiPinSpanningMass6401 35 73 <
      weakCurveOutput6401 * multiPinAmbient6401.descFactorial 73 := by
  native_decide

/-- With pure evaluation normals, the stronger `131071` cap at every proper
flat gives a comfortable closing margin at dimension `35`. -/
theorem pureEval_rho34_t71_retains_1183_exact6401 :
    weakCurveOutput6401 * multiPinAmbient6401.descFactorial 71 ≤
      multiPinOwnerMass6401 * pureEvalMultiPinSpanningMass6401 34 71 := by
  native_decide

theorem pureEval_rho34_t71_tailMonotonicity6401 :
    (pureEvalMultiPinRun6401 34 71).2 = true := by
  native_decide

/-- Dimension `36` is again the first miss. -/
theorem pureEval_rho35_t73_misses_1183_exact6401 :
    multiPinOwnerMass6401 * pureEvalMultiPinSpanningMass6401 35 73 <
      weakCurveOutput6401 * multiPinAmbient6401.descFactorial 73 := by
  native_decide

theorem pureEval_retained_ratio_floors6401 :
    (multiPinOwnerMass6401 * pureEvalMultiPinSpanningMass6401 34 71) /
        multiPinAmbient6401.descFactorial 71 = 1703 ∧
      (multiPinOwnerMass6401 * pureEvalMultiPinSpanningMass6401 35 73) /
        multiPinAmbient6401.descFactorial 73 = 696 := by
  native_decide

/-- The ordinary independent-basis count already forces a pure evaluation
normal space to have dimension at least `22` under weak-curve failure.  The
multi-pin recurrence is needed only for the improvement from `22` to `36`. -/
theorem pureEval_greedyBasis_all_dimensions_lt22_exact6401 (D : Fin 22) :
    weakCurveOutput6401 * multiPinAmbient6401.descFactorial D.val ≤
      multiPinOwnerMass6401 *
        (multiPinRow6401 - multiPinDegreeCap6401) ^ D.val := by
  fin_cases D <;> native_decide

/-- Human-readable floors of the two exact ratios.  These are consequences
of the same integer recurrence, not floating-point estimates. -/
theorem multiPin_retained_ratio_floors6401 :
    (multiPinOwnerMass6401 * multiPinSpanningMass6401 34 71) /
        multiPinAmbient6401.descFactorial 71 = 1200 ∧
      (multiPinOwnerMass6401 * multiPinSpanningMass6401 35 73) /
        multiPinAmbient6401.descFactorial 73 = 491 := by
  native_decide

/-- Parameter ledger, including the normal dimensions and pin counts used by
the two adjacent certificates. -/
theorem multiPin_parameter_ledger6401 :
    34 + 1 = 35 ∧ 2 * 35 + 1 = 71 ∧
      35 + 1 = 36 ∧ 2 * 36 + 1 = 73 ∧
      multiPinOwnerMass6401 = retainedHighSupportOwnerFloor6401 ∧
      multiPinAmbient6401 = flatAmbient6401 ∧
      multiPinRow6401 = flatAgreement6401 := by
  native_decide

end BCHKSMultiPinRankAccumulation6401
end ProximityPrize.SubmissionLower
