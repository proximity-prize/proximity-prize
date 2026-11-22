import ProximityPrize.SubmissionLower.FadicDegree
import ProximityPrize.SubmissionLower.Shared50ShapeRank
import ProximityPrize.SubmissionLower.KoalaWeightedRate

/-!
# Selecting a contact row from a variable f-adic gate

The variable-gate counterpart of `KoalaFadicSelect.select`.  The anchor factor is described by a
weighted envelope `p` (`KoalaWeightedRate.Fits`) and the accepted pointwise active bound
`ActiveFits f 165`; the gate is any terminal level, plain table and depth table whose finite loss
is below the layer need.  The selected contact row `v` has one of the three row forms of
`FadicGate.exists_varGateSpace`, and always lies in the accepted ambient source.
-/

set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

namespace KoalaVariableSelect
noncomputable section

open K1_13 (Row shape)
open K1_13_2_2 (gradeWeight oldWeight)
open K1_13_6 (GenericField GeoJets)
open K1_13_6_1_2 (hassePartial multiOrder)
open TaperColumns (jetExponents jetColumns)
open Shared50Rational
open Shared50Persistent (Persistent)
open Shared50ShapeRank (ambient ambient_dim contactSpace)
open FadicGate (Entry varGateDim varΘ BoxOK taperBox exists_varGateSpace topWeight taperWeight)
open Final50Price (layerNeed primaryCutoff layerWidth ActiveFits)
open MvPolynomial Finset
open scoped BigOperators

theorem wdeg_fraction (f : Row 4) (w : Fin 4 → ℕ) :
    (toFraction f).weightedTotalDegree w = f.weightedTotalDegree w := by
  unfold weightedTotalDegree
  rw [support_fraction]

theorem grade_of_fraction (f : Row 4) :
    (toFraction f).weightedTotalDegree gradeWeight = (shape f).b := by
  have hw : gradeWeight = (1 : Fin 4 → ℕ) := rfl
  rw [hw, weightedTotalDegree_one, totalDegree, support_fraction]
  rfl

theorem index_of_fraction (f : Row 4) :
    (toFraction f).weightedTotalDegree oldWeight = (shape f).j := by
  change (toFraction f).weightedTotalDegree Fin.val = K1_13.indexDegree f
  rw [K1_13_1.indexDegree_eq, weightedTotalDegree, support_fraction, weightedTotalDegree]

theorem top_of_fraction (f : Row 4) :
    (toFraction f).weightedTotalDegree topWeight = (shape f).t := by
  rw [FadicGate.wdeg_top_eq_degreeOf, degreeOf_eq_sup, support_fraction, ← degreeOf_eq_sup]
  rfl

/-- The envelope and the active bound give every hypothesis of the variable gate. -/
theorem envelope_bounds (f : Row 4) (p : KoalaWeightedRate.Envelope)
    (hfit : KoalaWeightedRate.Fits p (shape f)) (hact : ActiveFits f 165) :
    p.widthLow ≤ (toFraction f).weightedTotalDegree gradeWeight ∧
      (toFraction f).weightedTotalDegree gradeWeight ≤ p.widthHigh ∧
      p.indexLow ≤ (toFraction f).weightedTotalDegree oldWeight ∧
      (toFraction f).weightedTotalDegree oldWeight ≤ p.indexHigh ∧
      p.topLow ≤ (toFraction f).weightedTotalDegree topWeight ∧
      p.taperLow ≤ (toFraction f).weightedTotalDegree taperWeight ∧
      (toFraction f).weightedTotalDegree taperWeight ≤ p.taperHigh := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hfit
  rw [grade_of_fraction, index_of_fraction, top_of_fraction]
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · have hg := FadicGate.taper_ge_grade (toFraction f)
    rw [grade_of_fraction] at hg
    exact h6.trans hg
  · refine (FadicGate.taper_le (toFraction f) (shape f).b (shape f).j 165 ?_ ?_ ?_).trans h7
    · intro m hm
      have := le_weightedTotalDegree gradeWeight hm
      rwa [grade_of_fraction] at this
    · intro m hm
      have := le_weightedTotalDegree oldWeight hm
      rwa [index_of_fraction] at this
    · intro m hm
      rw [support_fraction] at hm
      exact hact m hm

/-- **Selection from a variable gate.**  `Rt`, `plainT` and `boxes` are the tables of a
certificate (for example `FadicGate.Final54W0`), `hcheck` its `loss` theorem. -/
theorem select {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P)
    (f : Row 4) (hf : f ≠ 0) (p : KoalaWeightedRate.Envelope)
    (hfit : KoalaWeightedRate.Fits p (shape f)) (hact : ActiveFits f 165)
    (Rt : ℕ) (plainT : ℕ → ℕ × ℕ × ℕ) (boxes : ℕ → List Entry) (loss : ℕ)
    (hcheck : ∀ N, ∑ i ∈ range N,
      max 0 ((Final50Price.symbolCount : ℤ) - varGateDim Final50Price.symbolCount
        p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow p.taperHigh
        Rt plainT (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i+1)) ≤ (loss : ℤ))
    (hloss : loss < layerNeed) :
    ∃ r : ℕ, 0 < r ∧ ∃ v : FractionJet, v ≠ 0 ∧ v ∈ ambient ∧
      (∀ P ∈ surfaces, ∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric v) ∈ P) ∧
      (Rt ≤ r ∨
        v ∈ restrictSupport GenericField
          (taperBox (min (plainT r).1 4012) (min (plainT r).2.1 1650) (plainT r).2.2 131312) ∨
        ∃ (a B J T : ℕ) (c h : FractionJet),
          a < (boxes r).length ∧ (boxes r).getD a none = some (B, J, T) ∧
          BoxOK p.widthHigh p.indexHigh p.taperHigh a B J ∧
          v = (toFraction f)^a * (c + toFraction f * h) ∧ c ≠ 0 ∧ ¬ toFraction f ∣ c ∧
          c ∈ restrictSupport GenericField (taperBox B J T (varΘ p.taperHigh a))) := by
  classical
  have hF : toFraction f ≠ 0 := by
    intro h
    apply hf (fraction_injective ?_)
    simpa only [show toFraction 0 = 0 by simp [toFraction]] using h
  obtain ⟨hbl, hbh, hjl, hjh, htl, hL, hH⟩ := envelope_bounds f p hfit hact
  choose U hu hd hs using fun i : ℕ => exists_varGateSpace (toFraction f) hF
    p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow p.taperHigh
    hbl hbh hjl hjh htl hL hH Rt plainT (fun r => (boxes r).length)
    (fun r a => (boxes r).getD a none) (i+1)
  let V (i : ℕ) := (U i).comap ambient.subtype
  have hcard : jetColumns.card = Final50Price.symbolCount := by
    have he : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
    have eq := ambient_dim
    rw [ambient, ← he, finrank_restrictSupport_finset] at eq
    exact eq
  have hv (i : ℕ) : Module.finrank GenericField (V i) = Module.finrank GenericField (U i) :=
    (Submodule.comapSubtypeEquivOfLe (show U i ≤ ambient from hu i)).finrank_eq
  have hlimits (i : ℕ) :
      ((Module.finrank GenericField ambient - Module.finrank GenericField (V i) : ℕ) : ℤ) ≤
        max 0 ((Final50Price.symbolCount : ℤ) - varGateDim Final50Price.symbolCount
          p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow p.taperHigh
          Rt plainT (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i+1)) := by
    have hle : Module.finrank GenericField (V i) ≤ Module.finrank GenericField ambient := by
      rw [hv]
      exact Submodule.finrank_mono (show U i ≤ ambient from hu i)
    rw [Nat.cast_sub hle, ambient_dim, hv]
    apply le_max_of_le_right
    have hh := hd i
    rw [hcard] at hh
    omega
  let N := 1+primaryCutoff/layerWidth
  have hsum : (∑ i∈range N,
      (Module.finrank GenericField ambient - Module.finrank GenericField (V i))) ≤ loss := by
    have hZ : ((∑ i∈range N,
        (Module.finrank GenericField ambient - Module.finrank GenericField (V i)) : ℕ) : ℤ) ≤ loss := by
      rw [Nat.cast_sum]
      exact (Finset.sum_le_sum (fun i (_ : i ∈ range N) => hlimits i)).trans (hcheck N)
    exact_mod_cast hZ
  let contacts (i : ℕ) : Submodule GenericField ambient := contactSpace surfaces (i+1)
  have h : (∑ i∈range N, (Module.finrank GenericField ambient - Module.finrank GenericField (V i))) <
      ∑ i∈range N, Module.finrank GenericField (contacts i) :=
    hsum.trans_lt (hloss.trans_le (Shared50ShapeRank.bank_layers hm surfaces hp))
  obtain ⟨i,_,Q,hq,hcontact,hv0⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N) contacts V h
  have uq : Q.val ∈ U i := hv0
  have nq : Q.val ≠ 0 := fun hz => hq (Subtype.ext hz)
  exact ⟨i+1, by omega, Q.val, nq, Q.2, hcontact, hs i _ uq nq⟩

#print axioms select
end
end KoalaVariableSelect
