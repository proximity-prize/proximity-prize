import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.FadicChunk
import ProximityPrize.SubmissionLower.R6960ExceptionalStage
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Low6960AllocWeight
import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960Low6960FractionContact
set_option Elab.async false







set_option Elab.async false

-- merged module R6960Low6960VariableSelect
section Merged_R6960Low6960VariableSelect

-- merged module R6960Low6960SharedShapeRank
section Merged_R6960Low6960SharedShapeRank

set_option Elab.async false
set_option maxRecDepth 40000
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000
namespace Low6960SharedShapeRank
noncomputable section

open K1_13 (Geom Row extend shape InBox OrderAt)
open K1_13_6 (GenericField GeoField GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder taylorHom taylor_coeff)
open Low6960SharedRational
open Low6960SharedPersistent (Persistent derivative_mem)
open TaperColumns (jetExponents jetColumns jet_card_eq)
open MvPolynomial Finset

def ambient : Submodule GenericField FractionJet :=
  restrictSupport GenericField jetExponents

instance : Module.Finite GenericField ambient :=
  restrictSupport_finite TaperColumns.jetExponents_finite

theorem ambient_dim : Module.finrank GenericField ambient = Low6960Prices.symbolCount := by
  have h : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
  rw [ambient,← h,finrank_restrictSupport_finset]
  have hc := jet_card_eq
  rw [TaperColumns.sourceCount_eq] at hc
  exact_mod_cast hc

def cutoff (r : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (Low6960ShapeGate.fits r)))).comap ambient.subtype

theorem cutoff_dim (r : ℕ) : Module.finrank GenericField (cutoff r) = Low6960ShapeGate.width r := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (Low6960ShapeGate.fits r))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact TaperColumns.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (Low6960ShapeGate.fits r)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,finrank_restrictSupport_finset]
  rfl

private theorem hasse_add (a : Fin 4 →₀ ℕ) (P Q : GeoJets) :
    hassePartial a (P+Q) = hassePartial a P + hassePartial a Q := by
  rw [← taylor_coeff, map_add, MvPolynomial.coeff_add, taylor_coeff,taylor_coeff]

private theorem hasse_zero (a : Fin 4 →₀ ℕ) :
    hassePartial a (0 : GeoJets) = 0 := by
  rw [← taylor_coeff, map_zero]
  simp

theorem hasse_C_mul (a : Fin 4 →₀ ℕ) (c : GeoField) (P : GeoJets) :
    hassePartial a (MvPolynomial.C c * P) = MvPolynomial.C c * hassePartial a P := by
  rw [← taylor_coeff, map_mul]
  have h : taylorHom (MvPolynomial.C c : GeoJets) = MvPolynomial.C (MvPolynomial.C c) := by
    simp [taylorHom]
  rw [h,coeff_C_mul,taylor_coeff]

def contactSpace (surfaces : Finset (Ideal GeoJets)) (r : ℕ) :
    Submodule GenericField ambient where
  carrier := {Q | ∀ P ∈ surfaces, ∀ a : Fin 4 →₀ ℕ, multiOrder a < r →
    hassePartial a (toGeometric Q.val) ∈ P}
  zero_mem' := by
    intro P _ a _
    change hassePartial a (toGeometric 0) ∈ P
    rw [map_zero,hasse_zero]
    exact P.zero_mem
  add_mem' := by
    intro a b ha hb P hP j hj
    change hassePartial j (toGeometric (a.val+b.val)) ∈ P
    rw [map_add,hasse_add]
    exact P.add_mem (ha P hP j hj) (hb P hP j hj)
  smul_mem' := by
    intro c a ha P hP j hj
    change hassePartial j (toGeometric (c • a.val)) ∈ P
    rw [← MvPolynomial.C_mul', map_mul, toGeometric, MvPolynomial.map_C, hasse_C_mul]
    exact P.mul_mem_left _ (ha P hP j hj)

open P3 (I K node)
open K1_13 (embed)
open Low6960Order (primaryCutoff layerWidth sourceRank layerNeed requiredOrder)
open scoped BigOperators
open P0_9_3 (exists_fresh sum_by_layer)

theorem bank_layers {w Γ s} (hm : Low6960Prices.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    layerNeed ≤ ∑ i ∈ range (1+primaryCutoff/layerWidth),
      Module.finrank GenericField (contactSpace surfaces (i+1)) := by
  obtain ⟨x,hx,_⟩ := exists_fresh (fun _ : Fin 0 => (0 : Row 4))
  obtain ⟨r,hr,hbank⟩ := Low6960Order.symbol_families w x (Low6960Order.primary_rank w) hx
  let cost (i : ℕ) := Module.finrank GenericField (contactSpace surfaces (i+1))
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    intro T hT
    obtain ⟨e,he,hli⟩ := hbank T hT
    let V := contactSpace surfaces (requiredOrder T)
    letI : Module.Finite GenericField V :=
      @FiniteDimensional.finiteDimensional_submodule GenericField ↥ambient
        inferInstance inferInstance inferInstance inferInstance V
    let u (i : Fin (r T)) : V := ⟨
      ⟨toFraction (e i),fun m hm => (he i).2.2.1 m (support_fraction (e i) ▸ hm)⟩,
      fun P hP a ha => by
        rw [fraction_geometric]
        apply derivative_mem (hp P hP) (he i).1 _ a ha
        intro γ hγ
        obtain ⟨H,hH,hhits⟩ := hm.hits γ hγ
        exact Low6960Order.order_of_contact w (e i) hT (he i).2.1 (he i).2.2.2
          (Polynomial.natDegree_map_le.trans (hm.degree γ hγ)) hH
          (fun i hi => by rw [Polynomial.eval_map,Polynomial.eval₂_hom,hhits i hi])⟩
    have hu : LinearIndependent GenericField u :=
      (independent_fraction x e hli).of_comp (ambient.subtype.comp V.subtype)
    have hcard := hu.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    exact hcard
  have hsum : sourceRank ≤ layerWidth * ∑ i ∈ range (1+primaryCutoff/layerWidth),cost i :=
    hr.trans ((sum_le_sum fun i hi => hcost i (Nat.le_of_lt_succ (mem_range.mp hi))).trans
      (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  have hceil : layerWidth * (layerNeed-1) < sourceRank := by decide
  by_contra! hsmall
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left _ (by
    dsimp only [cost]
    omega)))

/-- Select a small rational-function row of positive order on every persistent surface. -/
theorem exists_small {w Γ s} (hm : Low6960Prices.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : FractionJet, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low6960ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric Q) ∈ P := by
  have hbank := bank_layers hm surfaces hp
  let N := 1+primaryCutoff/layerWidth
  have hgate := Low6960ShapeGate.loss_bound N
  have h : (∑ i ∈ range N, (Module.finrank GenericField ambient -
      Module.finrank GenericField (cutoff (i+1)))) <
      ∑ i ∈ range N, Module.finrank GenericField (contactSpace surfaces (i+1)) := by
    simp only [ambient_dim,cutoff_dim]
    exact hgate.trans_lt ((by decide : Low6960SharedPrice.slopeLoss < layerNeed).trans_le hbank)
  obtain ⟨i,_,Q,hQ,hm,ht⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N)
      (fun i => contactSpace surfaces (i+1)) (fun i => cutoff (i+1)) h
  refine ⟨i+1,by omega,Q.val,fun hz => hQ (Subtype.ext hz),?_,hm⟩
  intro m hmem
  exact (Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp ht hmem)).2

theorem exists_polynomial {w Γ s} (hm : Low6960Prices.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low6960ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeneric Q) ∈ P := by
  obtain ⟨r,hr,U,hU,hs,ho⟩ := exists_small hm surfaces hp
  obtain ⟨d,Q,_,hS,hQ⟩ := clear_denominators U
  refine ⟨r,hr,Q,?_,fun m hm => hs m (hS ▸ hm),?_⟩
  · intro hz
    apply hU
    rw [hz,MvPolynomial.support_zero] at hS
    exact MvPolynomial.support_eq_empty.mp hS.symm
  · intro P hP a ha
    rw [← fraction_geometric,hQ,map_mul,toGeometric,MvPolynomial.map_C,hasse_C_mul]
    exact P.mul_mem_left _ (ho P hP a ha)

#print axioms bank_layers
#print axioms exists_polynomial
end
end Low6960SharedShapeRank

end Merged_R6960Low6960SharedShapeRank

-- merged module R6960Low6960VariableSelect
section Merged_R6960Low6960VariableSelect
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
namespace Low6960VariableSelect
noncomputable section
open K1_13 (Row shape)
open K1_13_2_2 (gradeWeight oldWeight)
open K1_13_6 (GenericField GeoJets)
open K1_13_6_1_2 (hassePartial multiOrder)
open TaperColumns (jetExponents jetColumns)
open Low6960SharedRational
open Low6960SharedPersistent (Persistent)
open Low6960SharedShapeRank (ambient ambient_dim contactSpace)
open FadicGate (Entry varGateDim varΘ BoxOK taperBox exists_varGateSpace topWeight taperWeight)
open Low6960Prices (layerNeed primaryCutoff layerWidth ActiveFits)
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
theorem envelope_bounds (f : Row 4) (p : Low6960WeightedRate.Envelope)
    (hfit : Low6960WeightedRate.Fits p (shape f)) (hact : ActiveFits f 169) :
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
  · refine (FadicGate.taper_le (toFraction f) (shape f).b (shape f).j 169 ?_ ?_ ?_).trans h7
    · intro m hm
      have := le_weightedTotalDegree gradeWeight hm
      rwa [grade_of_fraction] at this
    · intro m hm
      have := le_weightedTotalDegree oldWeight hm
      rwa [index_of_fraction] at this
    · intro m hm
      rw [support_fraction] at hm
      exact hact m hm
theorem select {w Γ s} (hm : Low6960Prices.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P)
    (f : Row 4) (hf : f ≠ 0) (p : Low6960WeightedRate.Envelope)
    (hfit : Low6960WeightedRate.Fits p (shape f)) (hact : ActiveFits f 169)
    (Rt : ℕ) (plainT : ℕ → ℕ × ℕ × ℕ) (boxes : ℕ → List Entry) (loss : ℕ)
    (hcheck : ∀ N, ∑ i ∈ range N,
      max 0 ((Low6960Prices.symbolCount : ℤ) - varGateDim Low6960Prices.symbolCount
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
  have hcard : jetColumns.card = Low6960Prices.symbolCount := by
    have he : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
    have eq := ambient_dim
    rw [ambient, ← he, finrank_restrictSupport_finset] at eq
    exact eq
  have hv (i : ℕ) : Module.finrank GenericField (V i) = Module.finrank GenericField (U i) :=
    (Submodule.comapSubtypeEquivOfLe (show U i ≤ ambient from hu i)).finrank_eq
  have hlimits (i : ℕ) :
      ((Module.finrank GenericField ambient - Module.finrank GenericField (V i) : ℕ) : ℤ) ≤
        max 0 ((Low6960Prices.symbolCount : ℤ) - varGateDim Low6960Prices.symbolCount
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
    hsum.trans_lt (hloss.trans_le (Low6960SharedShapeRank.bank_layers hm surfaces hp))
  obtain ⟨i,_,Q,hq,hcontact,hv0⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N) contacts V h
  have uq : Q.val ∈ U i := hv0
  have nq : Q.val ≠ 0 := fun hz => hq (Subtype.ext hz)
  exact ⟨i+1, by omega, Q.val, nq, Q.2, hcontact, hs i _ uq nq⟩
#print axioms select
end
end Low6960VariableSelect

end Merged_R6960Low6960VariableSelect

end Merged_R6960Low6960VariableSelect

-- merged module R6960Low6960FractionContact
section Merged_R6960Low6960FractionContact

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace Low6960FractionContact
noncomputable section

open K1_13 (Row Geom shape)
open K1_13_2_2 (gradeWeight oldWeight)
open K1_13_6 (GenericField GeoJets cycleLength intersectionIdeal toGeneric genericCoeffs)
open K1_13_6_1_2 (VanishesTo hassePartial multiOrder cycleLength_ge_order)
open K1_13_6_1_2_2 (vanishesTo_of_hasse)
open Low6960SharedRational
open Low6960SharedShapeRank (hasse_C_mul)
open scoped Polynomial
open MvPolynomial

theorem frac_map (Q : Row 4) :
    toFraction Q = MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) Q := rfl

theorem contact_clear {Q : Row 4} {v : FractionJet} {k : GenericField} {r : ℕ}
    {P : Ideal GeoJets} [P.IsPrime]
    (hd : toFraction Q = MvPolynomial.C k * v)
    (hc : ∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric v) ∈ P) :
    VanishesTo P (toGeneric Q) r := by
  apply vanishesTo_of_hasse _ P r
  intro a ha
  rw [← fraction_geometric Q, hd, map_mul, toGeometric, MvPolynomial.map_C, hasse_C_mul]
  exact P.mul_mem_left _ (hc a ha)

theorem proper_after_clear {f C : Row 4} {c : FractionJet} {k : GenericField}
    (hk : k ≠ 0) (hC : toFraction C = MvPolynomial.C k * c) (hc : ¬ toFraction f ∣ c) :
    ¬ f ∣ C := by
  intro hh
  apply hc
  obtain ⟨d, hd⟩ := map_dvd (MvPolynomial.map (algebraMap (Polynomial Geom) GenericField)) hh
  have he : MvPolynomial.C k * c = toFraction f * d := hC.symm.trans hd
  refine ⟨MvPolynomial.C k⁻¹ * d, ?_⟩
  calc
    c = MvPolynomial.C k⁻¹ * (MvPolynomial.C k * c) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
    _ = _ := by rw [he]; ring

end
end Low6960FractionContact

end Merged_R6960Low6960FractionContact

end Merged6967_R6960Low6960FractionContact

section Merged6967_R6960Low6960RetainedCount
set_option Elab.async false






set_option Elab.async false

-- merged module R6960Low6960AllocTotal
section Merged_R6960Low6960AllocTotal

-- merged module R6960Low6960GateShapes
section Merged_R6960Low6960GateShapes
set_option Elab.async false
namespace Low6960Gate
open K1_13 (Shape)
open Low6960SharedPrice (additiveBase nonsharedFee)
def floorShape (id : ℕ) : Shape := if id = 0 then ⟨0,0,0⟩ else ⟨id,3,1⟩
def gateList : ℕ → ℕ → List (ℕ × ℕ)
  | 0,2 => [(119,57), (120,52), (120,57), (121,51), (121,52), (121,54), (121,57), (122,51), (122,52), (122,54), (122,56), (122,57), (123,51), (123,52), (123,54), (123,56), (123,57), (124,51), (124,52), (124,53), (124,54), (124,56), (124,57), (125,50), (125,51), (125,53), (125,54), (125,56), (125,57), (126,50), (126,51), (126,53), (126,54), (126,55), (126,56), (126,57), (127,50), (127,51), (127,53), (127,54), (127,55), (127,56), (127,57), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,3 => [(115,57), (116,54), (116,57), (117,54), (117,57), (118,54), (118,57), (119,53), (119,54), (119,56), (119,57), (120,53), (120,54), (120,56), (120,57), (121,53), (121,54), (121,56), (121,57), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,4 => [(111,54), (112,54), (112,57), (113,53), (113,54), (113,57), (114,52), (114,53), (114,54), (114,57), (115,52), (115,53), (115,54), (115,57), (116,52), (116,53), (116,54), (116,56), (116,57), (117,52), (117,53), (117,54), (117,56), (117,57), (118,51), (118,52), (118,53), (118,54), (118,56), (118,57), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,5 => [(103,54), (104,54), (105,54), (106,54), (107,54), (108,54), (109,54), (110,54), (110,57), (111,54), (111,57), (112,54), (112,57), (113,53), (113,54), (113,56), (113,57), (114,52), (114,53), (114,54), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,56), (115,57), (116,51), (116,52), (116,53), (116,54), (116,56), (116,57), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,6 => [(99,54), (100,54), (101,54), (102,53), (102,54), (103,53), (103,54), (104,53), (104,54), (105,52), (105,53), (105,54), (106,54), (107,54), (107,57), (108,54), (108,57), (109,54), (109,57), (110,54), (110,57), (111,54), (111,56), (111,57), (112,54), (112,56), (112,57), (113,53), (113,54), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,7 => [(95,54), (96,54), (97,54), (98,54), (99,53), (99,54), (100,53), (100,54), (101,53), (101,54), (102,52), (102,53), (102,54), (103,52), (103,53), (103,54), (104,52), (104,53), (104,54), (105,52), (105,53), (105,54), (105,57), (106,54), (106,57), (107,54), (107,57), (108,54), (108,57), (109,54), (109,56), (109,57), (110,54), (110,56), (110,57), (111,54), (111,56), (111,57), (112,54), (112,56), (112,57), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,8 => [(93,54), (94,54), (95,54), (96,53), (96,54), (97,53), (97,54), (98,53), (98,54), (99,52), (99,53), (99,54), (100,52), (100,53), (100,54), (101,52), (101,53), (101,54), (102,52), (102,53), (102,54), (103,51), (103,52), (103,53), (103,54), (104,51), (104,52), (104,53), (104,54), (104,57), (105,51), (105,52), (105,53), (105,54), (105,57), (106,54), (106,57), (107,54), (107,56), (107,57), (108,54), (108,56), (108,57), (109,54), (109,56), (109,57), (110,54), (110,56), (110,57), (111,54), (111,55), (111,56), (111,57), (112,54), (112,55), (112,56), (112,57), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,9 => [(90,54), (91,54), (92,54), (93,54), (94,53), (94,54), (95,53), (95,54), (96,53), (96,54), (97,52), (97,53), (97,54), (98,52), (98,53), (98,54), (99,52), (99,53), (99,54), (99,57), (100,52), (100,53), (100,54), (100,57), (101,51), (101,52), (101,53), (101,54), (101,57), (102,51), (102,52), (102,53), (102,54), (102,56), (103,51), (103,52), (103,53), (103,54), (103,56), (103,57), (104,51), (104,52), (104,53), (104,54), (104,56), (104,57), (105,51), (105,52), (105,53), (105,54), (105,57), (106,54), (106,55), (106,56), (106,57), (107,54), (107,55), (107,56), (107,57), (108,54), (108,55), (108,56), (108,57), (109,54), (109,56), (109,57), (110,54), (110,55), (110,56), (110,57), (111,54), (111,55), (111,56), (111,57), (112,54), (112,55), (112,56), (112,57), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,47), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,46), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,46), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,45), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,10 => [(18,54), (19,54), (20,54), (89,54), (90,54), (91,54), (92,53), (92,54), (93,53), (93,54), (94,53), (94,54), (95,53), (95,54), (96,52), (96,53), (96,54), (97,52), (97,53), (97,54), (97,57), (98,52), (98,53), (98,54), (98,57), (99,52), (99,53), (99,54), (99,57), (100,51), (100,52), (100,53), (100,54), (100,57), (101,51), (101,52), (101,53), (101,54), (101,56), (101,57), (102,51), (102,52), (102,53), (102,54), (102,56), (102,57), (103,51), (103,52), (103,53), (103,54), (103,56), (103,57), (104,50), (104,51), (104,52), (104,53), (104,54), (104,56), (104,57), (105,50), (105,51), (105,52), (105,53), (105,54), (105,55), (105,56), (105,57), (106,53), (106,54), (106,55), (106,56), (106,57), (107,53), (107,54), (107,55), (107,56), (107,57), (108,53), (108,54), (108,55), (108,56), (108,57), (109,53), (109,54), (109,55), (109,56), (109,57), (110,53), (110,54), (110,55), (110,56), (110,57), (111,53), (111,54), (111,55), (111,56), (111,57), (112,53), (112,54), (112,55), (112,56), (112,57), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,47), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,47), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,46), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,46), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,46), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,45), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,45), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,11 => [(18,53), (18,54), (19,53), (19,54), (20,54), (21,54), (22,54), (23,54), (88,54), (89,54), (90,54), (91,53), (91,54), (92,53), (92,54), (93,53), (93,54), (94,53), (94,54), (95,52), (95,53), (95,54), (96,52), (96,53), (96,54), (96,57), (97,52), (97,53), (97,54), (97,57), (98,52), (98,53), (98,54), (98,57), (99,51), (99,52), (99,53), (99,54), (99,57), (100,51), (100,52), (100,53), (100,54), (100,56), (100,57), (101,51), (101,52), (101,53), (101,54), (101,56), (101,57), (102,51), (102,52), (102,53), (102,54), (102,56), (102,57), (103,50), (103,51), (103,52), (103,53), (103,54), (103,56), (103,57), (104,50), (104,51), (104,52), (104,53), (104,54), (104,55), (104,56), (104,57), (105,50), (105,51), (105,52), (105,53), (105,54), (105,55), (105,56), (105,57), (106,52), (106,53), (106,54), (106,55), (106,56), (106,57), (107,52), (107,53), (107,54), (107,55), (107,56), (107,57), (108,52), (108,53), (108,54), (108,55), (108,56), (108,57), (109,52), (109,53), (109,54), (109,55), (109,56), (109,57), (110,52), (110,53), (110,54), (110,55), (110,56), (110,57), (111,52), (111,53), (111,54), (111,55), (111,56), (111,57), (112,52), (112,53), (112,54), (112,55), (112,56), (112,57), (113,52), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,47), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,47), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,47), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,46), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,46), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,46), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,45), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,45), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,12 => [(18,53), (18,54), (19,53), (19,54), (20,53), (20,54), (21,54), (22,54), (23,54), (24,54), (87,54), (88,54), (89,54), (90,53), (90,54), (91,53), (91,54), (92,53), (92,54), (93,53), (93,54), (94,52), (94,53), (94,54), (95,52), (95,53), (95,54), (96,52), (96,53), (96,54), (96,57), (97,52), (97,53), (97,54), (97,57), (98,51), (98,52), (98,53), (98,54), (98,57), (99,51), (99,52), (99,53), (99,54), (99,56), (99,57), (100,51), (100,52), (100,53), (100,54), (100,56), (100,57), (101,51), (101,52), (101,53), (101,54), (101,56), (101,57), (102,51), (102,52), (102,53), (102,54), (102,56), (102,57), (103,50), (103,51), (103,52), (103,53), (103,54), (103,55), (103,56), (103,57), (104,50), (104,51), (104,52), (104,53), (104,54), (104,55), (104,56), (104,57), (105,50), (105,51), (105,52), (105,53), (105,54), (105,55), (105,56), (105,57), (106,52), (106,53), (106,54), (106,55), (106,56), (106,57), (107,52), (107,53), (107,54), (107,55), (107,56), (107,57), (108,52), (108,53), (108,54), (108,55), (108,56), (108,57), (109,52), (109,53), (109,54), (109,55), (109,56), (109,57), (110,52), (110,53), (110,54), (110,55), (110,56), (110,57), (111,52), (111,53), (111,54), (111,55), (111,56), (111,57), (112,52), (112,53), (112,54), (112,55), (112,56), (112,57), (113,52), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,47), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,47), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,47), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,46), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,46), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,46), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,45), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,45), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,13 => [(18,52), (18,53), (18,54), (19,53), (19,54), (20,53), (20,54), (21,53), (21,54), (22,54), (23,54), (24,54), (25,54), (86,54), (87,54), (88,54), (89,54), (90,53), (90,54), (91,53), (91,54), (92,53), (92,54), (93,53), (93,54), (94,52), (94,53), (94,54), (95,52), (95,53), (95,54), (95,57), (96,52), (96,53), (96,54), (96,57), (97,52), (97,53), (97,54), (97,57), (98,51), (98,52), (98,53), (98,54), (98,57), (99,51), (99,52), (99,53), (99,54), (99,56), (99,57), (100,51), (100,52), (100,53), (100,54), (100,56), (100,57), (101,51), (101,52), (101,53), (101,54), (101,56), (101,57), (102,51), (102,52), (102,53), (102,54), (102,56), (102,57), (103,50), (103,51), (103,52), (103,53), (103,54), (103,55), (103,56), (103,57), (104,50), (104,51), (104,52), (104,53), (104,54), (104,55), (104,56), (104,57), (105,50), (105,51), (105,52), (105,53), (105,54), (105,55), (105,56), (105,57), (106,52), (106,53), (106,54), (106,55), (106,56), (106,57), (107,52), (107,53), (107,54), (107,55), (107,56), (107,57), (108,52), (108,53), (108,54), (108,55), (108,56), (108,57), (109,52), (109,53), (109,54), (109,55), (109,56), (109,57), (110,52), (110,53), (110,54), (110,55), (110,56), (110,57), (111,52), (111,53), (111,54), (111,55), (111,56), (111,57), (112,52), (112,53), (112,54), (112,55), (112,56), (112,57), (113,52), (113,53), (113,54), (113,55), (113,56), (113,57), (114,52), (114,53), (114,54), (114,55), (114,56), (114,57), (115,51), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,50), (116,51), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,49), (117,50), (117,51), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,48), (118,49), (118,50), (118,51), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,48), (119,49), (119,50), (119,51), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,47), (120,48), (120,49), (120,50), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,47), (121,48), (121,49), (121,50), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,47), (122,48), (122,49), (122,50), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,47), (123,48), (123,49), (123,50), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,47), (124,48), (124,49), (124,50), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,47), (125,48), (125,49), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,47), (126,48), (126,49), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,46), (127,47), (127,48), (127,49), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,41), (128,46), (128,47), (128,48), (128,49), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,41), (129,46), (129,47), (129,48), (129,49), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,41), (130,46), (130,47), (130,48), (130,49), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,41), (131,46), (131,47), (131,48), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,41), (132,46), (132,47), (132,48), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,41), (133,46), (133,47), (133,48), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,41), (134,46), (134,47), (134,48), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,41), (135,45), (135,46), (135,47), (135,48), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,41), (136,45), (136,46), (136,47), (136,48), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 0,14 => [(95,57), (96,57), (97,57), (98,57), (99,56), (99,57), (100,56), (100,57), (101,56), (101,57), (102,56), (102,57), (103,55), (103,56), (103,57), (104,55), (104,56), (104,57), (105,55), (105,56), (105,57), (106,55), (106,56), (106,57), (107,54), (107,55), (107,56), (107,57), (108,54), (108,55), (108,56), (108,57), (109,54), (109,55), (109,56), (109,57), (110,54), (110,55), (110,56), (110,57), (111,54), (111,55), (111,56), (111,57), (112,54), (112,55), (112,56), (112,57), (113,53), (113,54), (113,55), (113,56), (113,57), (114,53), (114,54), (114,55), (114,56), (114,57), (115,52), (115,53), (115,54), (115,55), (115,56), (115,57), (116,52), (116,53), (116,54), (116,55), (116,56), (116,57), (117,52), (117,53), (117,54), (117,55), (117,56), (117,57), (118,52), (118,53), (118,54), (118,55), (118,56), (118,57), (119,52), (119,53), (119,54), (119,55), (119,56), (119,57), (120,51), (120,52), (120,53), (120,54), (120,55), (120,56), (120,57), (121,51), (121,52), (121,53), (121,54), (121,55), (121,56), (121,57), (122,51), (122,52), (122,53), (122,54), (122,55), (122,56), (122,57), (123,51), (123,52), (123,53), (123,54), (123,55), (123,56), (123,57), (124,51), (124,52), (124,53), (124,54), (124,55), (124,56), (124,57), (125,50), (125,51), (125,52), (125,53), (125,54), (125,55), (125,56), (125,57), (126,50), (126,51), (126,52), (126,53), (126,54), (126,55), (126,56), (126,57), (127,50), (127,51), (127,52), (127,53), (127,54), (127,55), (127,56), (127,57), (128,50), (128,51), (128,52), (128,53), (128,54), (128,55), (128,56), (128,57), (129,50), (129,51), (129,52), (129,53), (129,54), (129,55), (129,56), (129,57), (130,50), (130,51), (130,52), (130,53), (130,54), (130,55), (130,56), (130,57), (131,49), (131,50), (131,51), (131,52), (131,53), (131,54), (131,55), (131,56), (131,57), (132,49), (132,50), (132,51), (132,52), (132,53), (132,54), (132,55), (132,56), (132,57), (133,49), (133,50), (133,51), (133,52), (133,53), (133,54), (133,55), (133,56), (133,57), (134,49), (134,50), (134,51), (134,52), (134,53), (134,54), (134,55), (134,56), (134,57), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54), (135,55), (135,56), (135,57), (136,49), (136,50), (136,51), (136,52), (136,53), (136,54), (136,55), (136,56), (136,57)]
  | 1,3 => [(135,54)]
  | 1,4 => [(132,54), (133,54), (134,53), (134,54), (135,53), (135,54)]
  | 1,5 => [(129,54), (130,54), (131,53), (131,54), (132,53), (132,54), (133,52), (133,53), (133,54), (134,52), (134,53), (134,54), (135,52), (135,53), (135,54)]
  | 1,6 => [(126,54), (127,54), (128,53), (128,54), (129,53), (129,54), (130,53), (130,54), (131,52), (131,53), (131,54), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54), (135,51), (135,52), (135,53), (135,54)]
  | 1,7 => [(124,54), (125,54), (126,54), (127,53), (127,54), (128,53), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,8 => [(123,54), (124,54), (125,53), (125,54), (126,53), (126,54), (127,53), (127,54), (128,52), (128,53), (128,54), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,51), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,9 => [(121,54), (122,54), (123,54), (124,53), (124,54), (125,53), (125,54), (126,53), (126,54), (127,52), (127,53), (127,54), (128,52), (128,53), (128,54), (129,51), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,51), (131,52), (131,53), (131,54), (132,50), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,10 => [(121,54), (122,54), (123,53), (123,54), (124,53), (124,54), (125,53), (125,54), (126,52), (126,53), (126,54), (127,52), (127,53), (127,54), (128,52), (128,53), (128,54), (129,51), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,51), (131,52), (131,53), (131,54), (132,50), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,11 => [(120,54), (121,54), (122,54), (123,53), (123,54), (124,53), (124,54), (125,52), (125,53), (125,54), (126,52), (126,53), (126,54), (127,52), (127,53), (127,54), (128,51), (128,52), (128,53), (128,54), (129,51), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,50), (131,51), (131,52), (131,53), (131,54), (132,50), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,12 => [(120,54), (121,54), (122,53), (122,54), (123,53), (123,54), (124,53), (124,54), (125,52), (125,53), (125,54), (126,52), (126,53), (126,54), (127,52), (127,53), (127,54), (128,51), (128,52), (128,53), (128,54), (129,51), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,50), (131,51), (131,52), (131,53), (131,54), (132,50), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 1,13 => [(119,54), (120,54), (121,54), (122,53), (122,54), (123,53), (123,54), (124,53), (124,54), (125,52), (125,53), (125,54), (126,52), (126,53), (126,54), (127,52), (127,53), (127,54), (128,51), (128,52), (128,53), (128,54), (129,51), (129,52), (129,53), (129,54), (130,51), (130,52), (130,53), (130,54), (131,50), (131,51), (131,52), (131,53), (131,54), (132,50), (132,51), (132,52), (132,53), (132,54), (133,50), (133,51), (133,52), (133,53), (133,54), (134,50), (134,51), (134,52), (134,53), (134,54), (135,49), (135,50), (135,51), (135,52), (135,53), (135,54)]
  | 2,4 => [(134,54)]
  | 2,5 => [(132,54), (133,54), (134,53), (134,54)]
  | 2,6 => [(129,54), (130,54), (131,53), (131,54), (132,53), (132,54), (133,53), (133,54), (134,52), (134,53), (134,54)]
  | 2,7 => [(127,54), (128,54), (129,54), (130,53), (130,54), (131,53), (131,54), (132,52), (132,53), (132,54), (133,52), (133,53), (133,54), (134,52), (134,53), (134,54)]
  | 2,8 => [(126,54), (127,54), (128,53), (128,54), (129,53), (129,54), (130,53), (130,54), (131,52), (131,53), (131,54), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 2,9 => [(125,54), (126,54), (127,53), (127,54), (128,53), (128,54), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 2,10 => [(124,54), (125,54), (126,53), (126,54), (127,53), (127,54), (128,53), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 2,11 => [(123,54), (124,54), (125,54), (126,53), (126,54), (127,53), (127,54), (128,53), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 2,12 => [(123,54), (124,54), (125,54), (126,53), (126,54), (127,53), (127,54), (128,52), (128,53), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 2,13 => [(123,54), (124,54), (125,53), (125,54), (126,53), (126,54), (127,53), (127,54), (128,52), (128,53), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,52), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54), (134,51), (134,52), (134,53), (134,54)]
  | 3,6 => [(132,54), (133,54)]
  | 3,7 => [(130,54), (131,54), (132,54), (133,53), (133,54)]
  | 3,8 => [(129,54), (130,54), (131,53), (131,54), (132,53), (132,54), (133,53), (133,54)]
  | 3,9 => [(128,54), (129,54), (130,52), (130,53), (130,54), (131,53), (131,54), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54)]
  | 3,10 => [(127,54), (128,54), (129,54), (130,52), (130,53), (130,54), (131,53), (131,54), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54)]
  | 3,11 => [(126,54), (127,54), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54)]
  | 3,12 => [(126,54), (127,54), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54)]
  | 3,13 => [(126,54), (127,54), (128,54), (129,52), (129,53), (129,54), (130,52), (130,53), (130,54), (131,53), (131,54), (132,51), (132,52), (132,53), (132,54), (133,51), (133,52), (133,53), (133,54)]
  | 4,6 => [(132,54)]
  | 4,7 => [(131,54), (132,54)]
  | 4,8 => [(129,54), (130,54), (131,54), (132,53), (132,54)]
  | 4,9 => [(128,54), (129,54), (130,54), (131,53), (131,54), (132,53), (132,54)]
  | 4,10 => [(127,54), (128,54), (129,54), (130,53), (130,54), (131,53), (131,54), (132,53), (132,54)]
  | 4,11 => [(127,54), (128,54), (129,53), (129,54), (130,53), (130,54), (131,53), (131,54), (132,52), (132,53), (132,54)]
  | 4,12 => [(126,54), (127,54), (128,54), (129,53), (129,54), (130,53), (130,54), (131,53), (131,54), (132,52), (132,53), (132,54)]
  | 4,13 => [(126,54), (127,54), (128,54), (129,53), (129,54), (130,53), (130,54), (131,53), (131,54), (132,52), (132,53), (132,54)]
  | 5,9 => [(131,54)]
  | 5,10 => [(130,54), (131,54)]
  | 5,11 => [(130,54), (131,54)]
  | 5,12 => [(130,54), (131,54)]
  | 5,13 => [(129,54), (130,54), (131,54)]
  | _,_ => []
def Gated (id : ℕ) (x : Shape) : Prop := id < 6 ∧ (x.b,x.j) ∈ gateList id x.t
instance (id : ℕ) (x : Shape) : Decidable (Gated id x) := by unfold Gated; infer_instance
def gatePrice (G : Shape → ℕ) (x : Shape) (l : ℕ) : ℕ := additiveBase x l + nonsharedFee x l + G x
end Low6960Gate

end Merged_R6960Low6960GateShapes

-- merged module R6960Low6960AllocTiles
section Merged_R6960Low6960AllocTiles
set_option Elab.async false
set_option maxHeartbeats 2800000
set_option maxRecDepth 18000
namespace Low6960Allocation
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (Tile checks)
open Low6960Prices (physicalPrice physicalPriceOld tiltedFits activeFitsPrice)
open Low6960RetainedCut (contractedPrice)
open Low6960WeightedRate (Allowed)
open Low6960Gate (Gated gatePrice)
open Low6960Monotone (physicalPrice_le_old physical_mono)
open Compact50Cover (InRectangle fold_cover step)
def actualRate (u : Final50SharedPrice.Rate) : Low6960SharedPrice.Rate :=
  ⟨(match u.kind with | .ordinary=>.ordinary | .tilted=>.tilted),
    u.pivot,u.split,u.topIndex,u.amount⟩
def Covered {k : Band} (cells : List (MassCell k)) (x : Shape) : Prop :=
  (∃ l,0<l ∧ l≤order cells x ∧ contractedPrice x (start k) l 169 ≤
    allowance k ((start k).t+x.t) x.b x.j x.t) ∨
  ∃ u l,k=empty ∧ 0<l ∧ l≤order cells x ∧ Allowed x u ∧
    Low6960SharedPrice.price x l 169 u ≤ allowance k x.t x.b x.j x.t
def decode (word : ℕ) : List Tile :=
  if word % 4 = 3 then
    let z := word / 4
    let b := z % 256
    let j := z / 256 % 64
    let l := z / 16384 % 256
    let q := z / 4194304
    let marker := if 65536≤q then 512 else 256
    [.rectangle b j (b+q%256) (j+q%65536/256) (marker+l)]
  else Compact54Packed.decode word
def unpack (words : List ℕ) : List Tile := words.flatMap decode
def Paid {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6960Rectangle.PaidTilted cells t b j B (l-512)
      else if 256≤l then Low6960Rectangle.PaidFour cells t b j B J (l-256)
      else 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => (l=0 ∧ Gated k.val ⟨b,j,t⟩) ∨ (0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      contractedPrice ⟨b,j,t⟩ (start k) l 169 ≤ allowance k ((start k).t+t) b j t)
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Allowed ⟨b,j,t⟩ (actualRate u) ∧
      Low6960SharedPrice.price ⟨b,j,t⟩ l 169 (actualRate u) ≤ allowance k t b j t
instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (Paid cells t tile) := by cases tile <;> unfold Paid <;> infer_instance
def PaidF {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6960FastPrice.PaidTiltedF cells t b j B (l-512)
      else if 256≤l then Low6960FastPrice.PaidFourF cells t b j B J (l-256)
      else 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        Low6960FastPrice.physicalPriceOldF ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => (l=0 ∧ Gated k.val ⟨b,j,t⟩) ∨ (0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Low6960FastPrice.contractedPriceF ⟨b,j,t⟩ (start k) l 169 ≤ allowance k ((start k).t+t) b j t)
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Low6960FastPrice.AllowedF ⟨b,j,t⟩ (actualRate u) ∧
      Low6960FastPrice.priceF ⟨b,j,t⟩ l 169 (actualRate u) ≤ allowance k t b j t
instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (PaidF cells t tile) := by cases tile <;> unfold PaidF <;> infer_instance
theorem paidF_iff {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    PaidF cells t tile ↔ Paid cells t tile := by
  cases tile <;> simp only [PaidF, Paid, Low6960FastPrice.paidTiltedF_iff,
    Low6960FastPrice.paidFourF_iff, Low6960FastPrice.physicalPriceOldF_eq,
    Low6960FastPrice.contractedPriceF_eq, Low6960FastPrice.allowedF_iff, Low6960FastPrice.priceF_eq]
def pays {k : Band} (cells : List (MassCell k)) (t : ℕ) (tiles : List Tile) : Bool :=
  tiles.all (fun tile=>decide (PaidF cells t tile))
abbrev PaidBatch {k : Band} (cells : List (MassCell k)) (t : ℕ) :=
  {tiles : List Tile // pays cells t tiles=true}
def tilesOf {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) : List Tile :=
  batches.flatMap Subtype.val
private theorem batches_pay {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) :
    pays cells t (tilesOf batches)=true := by
  induction batches with
  | nil => rfl
  | cons head tail ih =>
    change pays cells t (head.val ++ tilesOf tail)=true
    rw [show pays cells t (head.val ++ tilesOf tail)=
      (pays cells t head.val && pays cells t (tilesOf tail)) by simp [pays,List.all_append]]
    rw [head.property,ih]
    rfl
private theorem contracted_le (x h : Shape) (l : ℕ) :
    contractedPrice x h l 169 ≤ physicalPrice x l 169 := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl
private theorem tile_cover {tile : Tile} {k : Band} {cells : List (MassCell k)} {t : ℕ} {a : Shape}
    (paid : Paid cells t tile) (bounds : InRectangle tile.bounds a.b a.j)
    (ht : a.t=t) (hi : 3*a.t≤a.j) : Covered cells a ∨ Gated k.val a := by
  rcases tile with ⟨b,j,B,J,l⟩ | ⟨b,j,l⟩ | ⟨b,j,l,u⟩
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    by_cases tilted : 512 ≤ l
    · have receipt : J=j ∧ Low6960Rectangle.PaidTilted cells t b j B (l-512) := by
        simpa only [Paid,ite_eq_left tilted] using paid
      have hja : a.j≤J := hJ
      exact Or.inl (Or.inl (Low6960Rectangle.tilted receipt.2 hb hB
        (Nat.le_antisymm (hja.trans_eq receipt.1) hj) ht))
    by_cases h : 256 ≤ l
    · have receipt : Low6960Rectangle.PaidFour cells t b j B J (l-256) := by
        simpa only [Paid, ite_eq_right tilted, ite_eq_left h] using paid
      exact Or.inl (Or.inl (Low6960Rectangle.four receipt hb hj hB hJ ht hi))
    have receipt : 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t := by
      simpa only [Paid, ite_eq_right tilted, ite_eq_right h] using paid
    obtain ⟨lp,lo,fee⟩ := receipt
    have ord := lo.trans (order_mono cells hb hj)
    have box : InBox a ⟨B,J,t⟩ := ⟨hB,hJ,ht.le⟩
    have charge : allowance k ((start k).t+t) b j t≤allowance k ((start k).t+t) a.b a.j a.t :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hb hj ht.ge))
    exact Or.inl (Or.inl ⟨l,lp,ord,
      ((contracted_le _ _ _).trans (physicalPrice_le_old _ _ _)).trans
        ((physical_mono box hi (ht ▸ hi.trans hJ) l).trans (fee.trans (by simpa only [ht] using charge)))⟩)
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    rcases paid with ⟨-,hg⟩ | paid
    · exact Or.inr hg
    · exact Or.inl (Or.inl ⟨l,paid⟩)
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    exact Or.inl (Or.inr ⟨actualRate u,l,paid⟩)
theorem cover_at {k : Band} {cells : List (MassCell k)} {t maxWidth maxIndex : ℕ}
    {batches : List (PaidBatch cells t)}
    (hcover : Compact50Cover.checks (tilesOf batches) maxWidth (3*t) (maxIndex+1-3*t) = true)
    (a : Shape) (ha : Valid a) (ht : a.t=t) (hb : a.b≤maxWidth) (hj : a.j≤maxIndex) :
    Covered cells a ∨ Gated k.val a := by
  let i := a.j-3*t
  have hleft : 3*t≤a.j := ht ▸ ha.2.1
  have hi : i∈List.range (maxIndex+1-3*t) := List.mem_range.mpr (by dsimp [i]; omega)
  have eq : 3*t+i=a.j := by dsimp [i]; omega
  have row := List.all_eq_true.mp hcover i hi
  change decide (maxWidth < (tilesOf batches).foldl (step (3*t+i)) ((3*t+i+2)/3))=true at row
  rw [eq] at row
  obtain ⟨tile,mem,bounds⟩ := fold_cover (tilesOf batches) a.j ((a.j+2)/3) a.b
    (by have := ha.2.2; omega) (hb.trans_lt (of_decide_eq_true row))
  have proof := (List.all_eq_true.mp (batches_pay batches)) tile mem
  exact tile_cover ((paidF_iff cells t tile).mp (of_decide_eq_true proof)) bounds ht ha.2.1
structure Receipt (k : Band) where
  orders : List (MassCell k)
  covers : ∀ a : Shape,Valid a → InBox ((start k).plus a) (Low6960Prices.fullCap 14) →
    Covered orders a ∨ Gated k.val a
def GateTable (orders : ∀ k : Band, List (MassCell k)) (G : Shape → ℕ) : Prop :=
  ∀ k : Band, ∀ x : Shape, Valid x → InBox ((start k).plus x) (Low6960Prices.fullCap 14) →
    Gated k.val x → ∃ l, 0<l ∧ l≤order (orders k) x ∧
      gatePrice G x l ≤ allowance k ((start k).t+x.t) x.b x.j x.t
#print axioms cover_at
end Low6960Allocation

end Merged_R6960Low6960AllocTiles

-- merged module R6960Low6960AllocTotal
section Merged_R6960Low6960AllocTotal

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Low6960AllocTotal
open K1_13 (Shape InBox FatEligible)
open Low6960RetainedCut (contractedPrice)
open K1_13_8 (Valid zeroShape)
open Final50PriceLayer (availableMass)
open Low6960Prices (physicalPrice fatPrice)
open Low6960Prices (layerNeed LayerBudget fullCap Fits)
open Low6960Allocation
open Low6960Retained (Box)
open Low6960Gate (Gated gatePrice)
open Low6960Monotone (physicalPrice_anti)
open Lower6960.Low (retained_family_fee)
open Lower6960.Low (degree_bound)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_insert shapeSum_union shapeSum_mono inBox_trans inBox_shapeSum shapeSum_valid_or_empty)

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i = 0)

private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} {k : Band} (ha : ∀ i, Valid (a i)) (hr : Valid (P3_6_8.shapeSum a z))
    (hbox : Box (P3_6_8.shapeSum a z)) (hk : Admits k (P3_6_8.shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ reserve k := by
  let r := P3_6_8.shapeSum a z
  let er := z.equivFin.symm
  let ar : Fin z.card → Shape := fun i => a (er i).val
  have sums (g : Shape → ℕ) : (∑ i, g (ar i)) = ∑ i ∈ z, g (a i) := by
    rw [← Finset.sum_attach z (fun i => g (a i))]
    exact Fintype.sum_equiv er _ _ fun _ => rfl
  have hj : (∑ i, (ar i).j) ≤ 8 := by rw [sums]; exact hbox.2.1
  have hb : (∑ i, (ar i).b) ≤ Lower6960.Low.lowDegreeCap (∑ i, (ar i).j) := by
    rw [sums, sums]
    exact degree_bound hr hbox
  have hp := retained_family_fee z.card ar (fun i => ha (er i).val) hj hb
  rw [sums, sums, sums, sums] at hp
  have hp' : (∑ i ∈ z, fatPrice (a i)) ≤
      Lower6960.Low.retainedTariff r.b r.j r.t := hp
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans (hp'.trans (admits_fee hk))
  have h := P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide), (h.2.1.trans hbox.2.1).trans (by decide)⟩

/-- Total cost of all factors in the low-height cover. -/
theorem total (receipts : ∀ k : Band, Receipt k) (G : Shape → ℕ)
    (htab : GateTable (fun k => (receipts k).orders) G) (top : ℕ) (htop : top ≤ 14) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits : Fits top a) (hlayers : LayerBudget a l)
    (hphys : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) →
      cost i ≤ contractedPrice (a i) (start k) m 169)
    (hshared : ∀ i m u, 0 < m → m ≤ l i → Low6960WeightedRate.Allowed (a i) u →
      cost i ≤ Low6960SharedPrice.price (a i) m 169 u)
    (hgate : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) → Gated k.val (a i) →
      cost i ≤ gatePrice G (a i) m)
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i, cost i) ≤ factorCap top := by
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := P3_6_8.shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ k : Band, Admits k r ∧
      (∑ i ∈ z, cost i) ≤ reserve k := by
    rcases Low6960Retained.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret, htr, _⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨empty,hr0.symm ▸ empty_admits,?_⟩
      rw [hempty,Finset.sum_empty]
      omega
    · have hr : Valid r := (P3_6_8.shapeSum_valid_or_empty ha z).resolve_left (by
        intro he
        have heq : P3_6_8.shapeSum a z = zeroShape := he ▸ P3_6_8.shapeSum_empty a
        have hpos : 1 ≤ (P3_6_8.shapeSum a z).t := htr
        rw [heq] at hpos
        exact (by decide : ¬ (1 ≤ zeroShape.t)) hpos)
      obtain ⟨k,hk⟩ := choose_band r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := admits_floor hk
  have massKind : q = zeroShape ∨ 0 < q.j := start_flat k
  have hreserve : reserve k ≤ factorCap top := reserve_fits top htop k
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _, Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_fee (i : Fin n) (hi : i ∈ pos) :
      cost i ≤ allowance k top (a i).b (a i).j (a i).t := by
    have hone : P3_6_8.shapeSum a {i} = a i := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
        P3_6_8.shapeSum_insert a (by simp),P3_6_8.shapeSum_empty]
      cases a i
      simp [zeroShape, Shape.plus]
    have hsingle : ({i} : Finset (Fin n)) ⊆ pos := Finset.singleton_subset_iff.mpr hi
    have hL : 0 < l i := hpos i hi
    have hj0 : 0 < (a i).j := by
      obtain ⟨ht, hj, _⟩ := ha i
      omega
    have hj : 0 < q.j + (a i).j := by omega
    have hmass0 := Low6960Retained.mass_le hlayers hz
      (s := {i}) (L := l i) (by simp) (hdisj hsingle) hqr
    rw [hone] at hmass0
    have hmass := hmass0.trans (layer_le_available massKind hj)
    have horder : order (receipts k).orders (a i) ≤ l i := by
      rcases order_valid (receipts k).orders (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono massKind hj
          (show l i ≤ order (receipts k).orders (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc := member_cap hsingle
    rw [hone] at hc
    have goal : InBox ((start k).plus (a i)) (fullCap 14) :=
      ⟨hc.1,hc.2.1,hc.2.2.trans htop⟩
    have ht : (start k).t+(a i).t≤top := hc.2.2
    rcases (receipts k).covers (a i) (ha i) goal with (⟨m,hm,hmo,hfee⟩ | ⟨u,m,he,hm,hmo,hu,hfee⟩) | hg
    · exact (hphys i m hm (hmo.trans horder) k hk).trans
        (hfee.trans (allowance_mono k ht htop))
    · exact (hshared i m u hm (hmo.trans horder) hu).trans
        (hfee.trans (allowance_mono k (ht.trans' (Nat.le_add_left _ _)) htop))
    · obtain ⟨m,hm,hmo,hfee⟩ := htab k (a i) (ha i) goal hg
      exact (hgate i m hm (hmo.trans horder) k hk hg).trans
        (hfee.trans (allowance_mono k ht htop))
  have hfits_pos := member_cap (s := pos) (Finset.Subset.rfl)
  have hwidth : (∑ i ∈ pos, (a i).b) ≤ 136 - q.b := by
    have hh := hfits_pos.1
    change q.b + (∑ i ∈ pos, (a i).b) ≤ 136 at hh
    omega
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 57 - q.j := by
    have hh := hfits_pos.2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 57 at hh
    omega
  have hDen : 0 < pricingDenom k := denom_pos k
  have hweights : (∑ i ∈ pos, pricingWeight k (a i).b (a i).j (a i).t) ≤ pricingDenom k := by
    by_cases he : k = empty
    · subst k
      change (∑ i∈pos,Low6960AllocWeight.weight (a i).b (a i).j (a i).t) ≤ 364
      exact Low6960AllocWeight.sum_le htop a hfits pos
    · simpa only [q, pricingWeight, pricingDenom, ite_eq_right he] using hindex
  let C := factorCap top - reserve k
  let M := pricingDenom k
  have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * pricingWeight k (a i).b (a i).j (a i).t := by
    have h := Nat.mul_le_mul_left M (positive_fee i hi)
    change M*cost i ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) at h
    calc
      _ ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) := h
      _ = (C*pricingWeight k (a i).b (a i).j (a i).t / M)*M := Nat.mul_comm _ _
      _ ≤ _ := Nat.div_mul_le_self _ _
  have hweighted : M * (∑ i ∈ pos, cost i) ≤ M*C := by
    rw [Finset.mul_sum, mul_comm M C]
    refine (Finset.sum_le_sum fees).trans ?_
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ hweights
  have hp : (∑ i ∈ pos, cost i) ≤ C := Nat.le_of_mul_le_mul_left hweighted hDen
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap top
  dsimp [C] at hp
  omega

#print axioms total
end Low6960AllocTotal

end Merged_R6960Low6960AllocTotal

end Merged_R6960Low6960AllocTotal

-- merged module R6960Low6960RetainedCount
section Merged_R6960Low6960RetainedCount

-- merged module R6960Low6960RetainedBank
section Merged_R6960Low6960RetainedBank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6960RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox atJet extend OrderAt embed indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low6960Prices (Messages SmallFactor ActiveFits primaryBox primaryCutoff layerWidth layerNeed
  TrueWeightLE LayerBudget)
open scoped Polynomial BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
def levelOrder (T : ℕ) : ℕ := (primaryCutoff-T)/layerWidth+1
structure Bank (Γ : Finset K) (s : K → (Polynomial K)) where
  row : ℕ → Row 4 → Prop
  bounds : ∀ T ≤ primaryCutoff, ∀ P, row T P →
    InBox (shape P) primaryBox ∧ TrueWeightLE P primaryCutoff ∧ ActiveFits P 5164
  order : ∀ T ≤ primaryCutoff, ∀ P, row T P → ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (levelOrder T)
variable {Γ : Finset K} {s : K → (Polynomial K)}
def Bank.Ranked (D : Bank Γ s) : Prop :=
  ∀ x : Geom, (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, layerWidth*(layerNeed-1) < ∑ T ∈ Finset.range (primaryCutoff+1), r T ∧
      ∀ T ≤ primaryCutoff, r T ≤ Low6960Prices.symbolCount ∧ ∃ e : Fin (r T) → Row 4,
        (∀ i, D.row T (e i)) ∧ LinearIndependent Geom (fun i => symbolAt x (e i))
def Bank.Admissible (D : Bank Γ s) (f : Row 4) (l : ℕ) : Prop :=
  ∀ T ≤ primaryCutoff, ∀ P, D.row T P → f^(levelOrder T-l) ∣ P
private theorem some_admissible (D : Bank Γ s) (f : Row 4) : ∃ l, D.Admissible f l := by
  refine ⟨primaryCutoff/layerWidth+1, fun T _ P _ => ?_⟩
  have hle : levelOrder T ≤ primaryCutoff/layerWidth+1 :=
    Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
  rw [Nat.sub_eq_zero_of_le hle,pow_zero]
  exact one_dvd P
def Bank.availability (D : Bank Γ s) (f : Row 4) : ℕ := by
  classical
  exact Nat.find (some_admissible D f)
theorem Bank.available (D : Bank Γ s) (f : Row 4) : D.Admissible f (D.availability f) := by
  classical
  exact Nat.find_spec (some_admissible D f)
theorem Bank.extremal (D : Bank Γ s) (f : Row 4) (hp : 0 < D.availability f) :
    ∃ T ≤ primaryCutoff, ∃ P, D.row T P ∧ D.availability f ≤ levelOrder T ∧
      f^(levelOrder T - D.availability f) ∣ P ∧ ¬ f^(levelOrder T - D.availability f+1) ∣ P := by
  classical
  let l := D.availability f
  have hbad : ¬ D.Admissible f (l-1) := Nat.find_min (some_admissible D f) (by
    change l-1 < l
    dsimp only [l]
    omega)
  dsimp only [Bank.Admissible] at hbad
  push Not at hbad
  obtain ⟨T,hT,P,hP,hn⟩ := hbad
  have hl : l ≤ levelOrder T := by
    by_contra! hh
    have heq : levelOrder T-(l-1)=0 := by omega
    exact hn (by rw [heq,pow_zero]; exact one_dvd P)
  have heq : levelOrder T-(l-1)=levelOrder T-l+1 := by dsimp only [l] at *; omega
  exact ⟨T,hT,P,hP,hl,D.available f T hT P hP,by rwa [heq] at hn⟩
theorem Bank.layer_budget {n : ℕ} (D : Bank Γ s) (ranked : D.Ranked) (f : Fin n → Row 4)
    (hirr : ∀ i, Irreducible (f i)) (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    LayerBudget (fun i => shape (f i)) (fun i => D.availability (f i)) := by
  classical
  let l (i : Fin n) := D.availability (f i)
  obtain ⟨x,hx,hsup⟩ := exists_fresh f
  obtain ⟨r,hrank,hfamilies⟩ := ranked x hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz,MvPolynomial.support_zero,eq_comm,MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) := Low6960Prices.remaining (∑ i, (k+1-l i)*(shape (f i)).b)
    (∑ i, (k+1-l i)*(shape (f i)).j)
  have hcost (T) (hT : T ≤ primaryCutoff) : r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    obtain ⟨hs,e,he,hei⟩ := hfamilies T hT
    let a (i : Fin n) := levelOrder T-l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        exact ((hirr j).isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk ((hirr j).associated_of_dvd (hirr k) h))).pow
      · intro j
        exact D.available (f j) T hT _ (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb,hj⟩ := specialization_bounds x (e i) (D.bounds T hT _ (he i)).1
        exact ⟨hb,hj,by simpa only [map_prod,map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    exact le_min hs (by simpa only [a,levelOrder,hb,hj] using hbound)
  have hsum := hrank.trans_le ((Finset.sum_le_sum fun T hT =>
    hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
    (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  change layerNeed ≤ ∑ k ∈ Finset.range (1+primaryCutoff/layerWidth), cost k
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1+primaryCutoff/layerWidth), cost k) ≤ layerNeed-1 := by omega
  exact (not_le_of_gt hsum) (Nat.mul_le_mul_left layerWidth hpred)
theorem Bank.proper_cut (D : Bank Γ s) {f : Row 4} (hf : SmallFactor f)
    (hchar : f.degreeOf 3 < K1.p) {l : ℕ} (hp : 0 < l) (hl : l ≤ D.availability f) :
    Low6960Prices.ProperCut f Γ s l := by
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal f (hp.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  obtain ⟨Q,hproper,hbQ,hwQ,haQ,hord⟩ := exists_divided_cut (H := 1) (k := levelOrder T) (l := l) hP one_ne_zero
    hf.1 hf.2.1 hchar isRelPrime_one_right (by omega) hb hw ht (by simp) divF exactF
  refine ⟨Q,hproper,⟨hbQ.1.trans (Nat.sub_le _ _),hbQ.2.1.trans (Nat.sub_le _ _),
    hbQ.2.2.trans (Nat.sub_le _ _)⟩,hwQ,haQ,?_⟩
  intro γ hγ
  exact hord _ (by simp [atJet]) (D.order T hT _ hrow γ hγ)
def sumShape {ι : Type*} (z : Finset ι) (x : ι → Shape) : Shape :=
  ⟨∑ i∈z, (x i).b, ∑ i∈z, (x i).j, ∑ i∈z, (x i).t⟩
theorem shape_of_product {ι : Type*} (z : Finset ι) (f : ι → Row 4) (hn : ∀ i∈z, f i ≠ 0) :
    shape (∏ i∈z, f i) = sumShape z (fun i => shape (f i)) := by
  have hb := MvPolynomial.weightedTotalDegree_prod (1 : Fin 4 → ℕ) z f hn
  have hj := MvPolynomial.weightedTotalDegree_prod Fin.val z f hn
  have ht := MvPolynomial.weightedTotalDegree_prod (Pi.single (3 : Fin 4) 1) z f hn
  simp only [MvPolynomial.weightedTotalDegree_one] at hb
  simp only [← K1_13_1.indexDegree_eq] at hj
  simp only [MvPolynomial.weightedTotalDegree_piSingle] at ht
  change Shape.mk _ _ _ = Shape.mk _ _ _
  rw [hb,hj,ht]
  rfl
theorem Bank.companion_price_floor {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    ∀ h : Shape, InBox h (shape (∏ j∈z, f j)) → Δ.card ≤ contractedPrice (shape (f i)) h l active := by
  classical
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal (f i) (hpos.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  have hH : (∏ j∈z, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hf j).1.ne_zero
  have divH := retained_power_dvd z f (fun j => (hf j).1) hdiff (k := levelOrder T) (P := P) (by
    intro j hj
    have hd := D.available (f j) T hT P hrow
    simpa only [hz j hj,Nat.sub_zero] using hd)
  exact price_of_witness_floor (hm.mono hsub) (hf i) ha hchar hon hoff hP hH
    (prime_off_product z f (fun j => (hf j).1) hdiff hi) hpos (by omega) hb hw ht
    (fun γ hγ => D.order T hT P hrow γ (hsub hγ)) divH divF exactF
theorem Bank.companion_price {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    Δ.card ≤ contractedPrice (shape (f i)) (shape (∏ j∈z, f j)) l active :=
  D.companion_price_floor hm f hf hdiff z hz hi hpos hl ha hchar Δ hsub hon hoff
    _ ⟨le_rfl,le_rfl,le_rfl⟩
#print axioms Bank.proper_cut
#print axioms shape_of_product
#print axioms Bank.layer_budget
#print axioms Bank.companion_price_floor
#print axioms Bank.companion_price
end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedBank

-- merged module R6960Low6960RetainedCount
section Merged_R6960Low6960RetainedCount
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6960RetainedCut
noncomputable section
open P3 (I K)
open K1_13 (Geom Row Shape shape InBox extend atJet OnFactor)
open Low6960Prices (Messages activeFitsPrice ActiveFits SmallFactor Fits Holds FatEquations
  ProperCut LayerBudget lowerCap fullCap TrueWeightLE anchorCutoff)
open Final50GeoCover (activeDegree)
open K1_13_1 (anchorLead indexDegree_eq)
open Lower6960.Low (factor_small lower_of_anchor)
open KoalaRetainedCut (anchor_factors priority_pieces)
open K1_13_1 (index_bounds)
open MvPolynomial
open scoped Polynomial BigOperators
def GateBank (G : Shape → ℕ) : Prop :=
  ∀ {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {n : ℕ} (D : Bank Γ s) (_ : Messages w Γ s)
    (f : Fin n → Row 4) (_ : ∀ i, SmallFactor (f i))
    (_ : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (_ : ∀ j ∈ z, D.availability (f j) = 0) {i : Fin n} (_ : i ∉ z)
    {l active : ℕ} (_ : 0 < l) (_ : l ≤ D.availability (f i))
    (_ : ActiveFits (f i) active) (_ : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (_ : Δ ⊆ Γ) (_ : ∀ γ ∈ Δ, OnFactor (f i) (extend (s γ)))
    (_ : ∀ γ ∈ Δ, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) (id : ℕ),
    InBox (Low6960Gate.floorShape id) (shape (∏ j ∈ z, f j)) →
    Low6960Gate.Gated id (shape (f i)) → Δ.card ≤ Low6960Gate.gatePrice G (shape (f i)) l
structure AllocationData (Γ : Finset K) (s : K → (Polynomial K)) (E : FatEquations) (top anchorK : ℕ)
    (G : Shape → ℕ) where
  n : ℕ
  f : Fin n → Row 4
  pieces : Fin n → Finset K
  orders : Fin n → ℕ
  zeros : Finset (Fin n)
  zero_iff : ∀ i, i∈zeros ↔ orders i=0
  small : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits top (fun i => shape (f i))
  active_budget : (∑ i, activeDegree (f i)) ≤ anchorK
  layers : LayerBudget (fun i => shape (f i)) orders
  subset : ∀ i, pieces i ⊆ Γ
  on_factor : ∀ i γ, γ ∈ pieces i → OnFactor (f i) (extend (s γ))
  fat : ∀ i γ, γ ∈ pieces i → Holds E (extend (s γ))
  proper : ∀ i, 0 < orders i → ProperCut (f i) Γ s (orders i)
  contracted : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ h, InBox h (sumShape zeros (fun j => shape (f j))) →
      (pieces i).card ≤ contractedPrice (shape (f i)) h l active
  gated : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ id, InBox (Low6960Gate.floorShape id) (sumShape zeros (fun j => shape (f j))) →
      Low6960Gate.Gated id (shape (f i)) →
      (pieces i).card ≤ Low6960Gate.gatePrice G (shape (f i)) l
def Allocation (budget anchorK : ℕ) (G : Shape → ℕ) : Prop :=
  ∀ {w Γ s}, Messages w Γ s → ∀ top, top ≤ 14 → ∀ E,
    ∀ d : AllocationData Γ s E top anchorK G, lowerCap top + (∑ i, (d.pieces i).card) ≤ budget
theorem count_of_data {budget anchorK : ℕ} {G : Shape → ℕ} (gate : GateBank G)
    (allocate : Allocation budget anchorK G)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    (bank : Bank Γ s) (rank : bank.Ranked) (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) (fullCap 14)) (hw : TrueWeightLE P anchorCutoff)
    (ha : ActiveFits P anchorK) (hz : ∀ γ∈Γ, atJet P (extend (s γ))=0)
    (lower : ∀ top ≤ 14, Low6960Prices.c5 top)
    (book : Finset K) (E : FatEquations) (booked : book.card ≤ 140000)
    (hE : ∀ γ∈Γ, γ∉book → Holds E (extend (s γ))) : Γ.card ≤ 140000+budget := by
  classical
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := anchor_factors hP
  let top := (shape P).t
  have htop : top ≤ 14 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ anchorK :=
    (sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ) Finset.univ f hP prodDvd).trans
      ((Final50GeoCover.activeFits_iff P anchorK).mp ha)
  let orders i := bank.availability (f i)
  let z := Finset.univ.filter fun i => orders i=0
  have hzero (i) : i∈z ↔ orders i=0 := by simp [z]
  obtain ⟨low,pieces,lowSub,lowOn,sub,on,off,total⟩ := priority_pieces
    (fun i => (factors i).2.2) s book z (fun γ hγ => covers _ (hz γ hγ))
  have lbound := lower top htop _ _ _ (hm.mono lowSub) _ (lower_of_anchor P hP hbox hw) lowOn
  have hchar (i) : (f i).degreeOf 3 < K1.p := (small i).2.2.1.2.2.trans_lt (by decide : 14<K1.p)
  let data : AllocationData Γ s E top anchorK G := {
    n := n, f := f, pieces := pieces, orders := orders, zeros := z, zero_iff := hzero
    small := small, different := different, fits := fits, active_budget := active
    layers := bank.layer_budget rank f (fun i => (factors i).1) different, subset := sub
    on_factor := fun i γ h => (on i γ h).2
    fat := fun i γ h => hE γ (sub i h) (on i γ h).1
    proper := fun i hp => bank.proper_cut (small i) (hchar i) hp le_rfl
    contracted := by
      intro i hi l hp hl K hK h hfloor
      apply bank.companion_price_floor hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) h
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
    gated := by
      intro i hi l hp hl K hK id hfloor hg
      refine gate bank hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) id ?_ hg
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
  }
  have counts := allocate hm top htop E data
  change lowerCap top + (∑ i, (pieces i).card) ≤ budget at counts
  exact total.trans (by omega)
#print axioms count_of_data
end
end Low6960RetainedCut

end Merged_R6960Low6960RetainedCount

end Merged_R6960Low6960RetainedCount

end Merged6967_R6960Low6960RetainedCount

section Merged6967_R6960MainGeometryUnion
set_option Elab.async false


set_option Elab.async false

-- merged module R6960MainGeometryFee
section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open RescueGeometry (Model Family OnMark OnSurface SurfacePass word curveMarks mem_curveMarks
  curve_tariff rated_curve_count fixedFee lambda mu tau)
open Lower6960.RescueGeometry (fixedFee_eq)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤33579) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    RescueGeometry.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤33579) {i : ℕ} (hi : i<17) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks R.family (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33579) : C.lossMarks.card ≤ (lossLimit).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 17,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤33579) : C.paid.card≤mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤33579) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card≤116835760512599839 ∧ (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S,geom,surface⟩ := ini.terminal_surfaces
  refine ⟨C.paid,S,(C.paid_count hi).trans main_fee_bound,geom,?_⟩
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range 17).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
#print axioms Rows.main_prefix
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryFee

-- merged module R6960MainGeometryUnion
section Merged_R6960MainGeometryUnion
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.MainGeometry
open Finset
open K1 (K)
open K1_14 (jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_3 (Surface Parent ProjectedProduct)
open RescueGeometry (Model Family OnSurface SurfacePass word exceptional_prefix)
open scoped Classical
def prefixCap : ℕ := 235296504696168815
theorem Rows.combined_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨main,left,fee,passing,cover⟩ := R.main_prefix hi noPole residues
  rcases R.out.kind with unit | common
  · refine ⟨main,left,fee.trans (by decide +kernel),passing,?_⟩
    intro γ hγ
    apply cover
    exact mem_filter.mpr ⟨hγ,by simp [unit,jetAt]⟩
  · obtain ⟨rescue,right,cost,retains,rescue_cover⟩ :=
      exceptional_prefix F Crt lo hi noPole residues common
    refine ⟨main∪rescue,left∪right,
      (card_union_le _ _).trans ((Nat.add_le_add fee cost).trans (by decide +kernel)),?_,?_⟩
    · intro q hq
      exact (mem_union.mp hq).elim (passing q) (retains q)
    · intro γ hγ
      let lift (paid' : Finset K) (S' : Finset Surface)
          (hp : paid'⊆main∪rescue) (hs : S'⊆left∪right)
          (on : γ∈paid' ∨ ∃ q∈S',OnSurface F q γ) :
          γ∈main∪rescue ∨ ∃ q∈left∪right,OnSurface F q γ := by
        rcases on with mark | ⟨q,hq,hmark⟩
        · exact Or.inl (hp mark)
        · exact Or.inr ⟨q,hs hq,hmark⟩
      by_cases e : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
      · exact lift rescue right subset_union_right subset_union_right (rescue_cover γ hγ e)
      · exact lift main left subset_union_left subset_union_left
          (cover γ (mem_filter.mpr ⟨hγ,e⟩))
theorem combined_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (S.Nonempty → ∃ f,ProjectedProduct S f) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨paid,S,fee,geom,cover⟩ := R.combined_prefix lo hi noPole residues
  exact ⟨paid,S,fee,geom,fun hs=>K1_14_3_7.proof S hs (fun q hq=>(geom q hq).1),cover⟩
#print axioms Rows.combined_prefix
#print axioms combined_prefix
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryUnion

end Merged6967_R6960MainGeometryUnion

section Merged6967_R6966ProofHelperPhysicalModel
set_option Elab.async false



set_option Elab.async false

namespace Research6966.HelperPhysicalModel
open Polynomial
open K1_14 (Jet Seeds)
open K1_14_1 (PoleData CRTLift RawSource jetConstant centerEval)
open K1_14_1_4 (doubleMap specialized evalRaw)
open K1_14_3 (SeedField)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

private theorem other_unit {R:Type*} [CommRing R] [IsDomain R] {H P Q:R}
    (hn:H≠0) (eq:H=P*Q) (dv:H∣P) : IsUnit Q := by
  obtain ⟨t,id⟩:=dv
  have pn:=left_ne_zero_of_mul (eq ▸ hn)
  have cancel:P*1=P*(Q*t):=by rw [mul_one,←mul_assoc,←eq];exact id
  exact IsUnit.of_mul_eq_one t (mul_left_cancel₀ pn cancel).symm

/-- Localizing the seed coefficients of a positive-slope prime preserves
irreducibility. A factorization after localization would clear to two native
polynomial factors, one of which must contain the original prime. -/
theorem generic_prime {R:Type*} [CommRing R] [IsDomain R] {N:R[X][X]}
    (pr:Prime N) (slope:0<N.natDegree) :
    Irreducible (doubleMap (algebraMap R (FractionRing R)) N) := by
  classical
  let f:=algebraMap R (FractionRing R)
  let φ:=doubleMap f
  have fi:=IsFractionRing.injective R (FractionRing R)
  have inject:Function.Injective φ:=map_injective _ (map_injective _ fi)
  have hn:φ N≠0:=(map_ne_zero_iff φ inject).mpr pr.ne_zero
  have positive:0<(φ N).natDegree := by
    change 0<(N.map (mapRingHom f)).natDegree
    rwa [natDegree_map_eq_of_injective (map_injective f fi)]
  refine ⟨fun unit=>positive.ne' (natDegree_eq_zero_of_isUnit unit),?_⟩
  intro P Q eq
  change φ N=P*Q at eq
  obtain ⟨A,a,an,hA⟩:=PadeIntegralGraph.clear_two (R:=R) P
  obtain ⟨B,b,bn,hB⟩:=PadeIntegralGraph.clear_two (R:=R) Q
  have prod:A*B=jetConstant (a*b)*N := by
    apply inject
    have c (x:R):φ (jetConstant x)=jetConstant (f x) := by
      simp only [φ,doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,Polynomial.map_C]
    calc
      φ (A*B) = φ A*φ B := map_mul _ _ _
      _ = (jetConstant (f a)*P)*(jetConstant (f b)*Q) := by rw [←hA,←hB]
      _ = jetConstant (f (a*b))*φ N := by rw [map_mul f,map_mul jetConstant,eq];ring
      _ = φ (jetConstant (a*b)*N) := by rw [map_mul φ,c]
  have dv:N∣A*B:=prod ▸ dvd_mul_left _ _
  have descend {D:R[X][X]} {t:R} {T:(FractionRing R)[X][X]} (nz:t≠0)
      (cleared:φ D=jetConstant (f t)*T) (div:N∣D) : φ N∣T := by
    have h:=map_dvd φ div
    rw [cleared] at h
    have unit:IsUnit (jetConstant (f t):(FractionRing R)[X][X]):=
      isUnit_C.mpr (isUnit_C.mpr ((map_ne_zero_iff f fi).mpr nz).isUnit)
    exact (associated_unit_mul_left _ _ unit).dvd_iff_dvd_right.mp h
  rcases pr.dvd_or_dvd dv with left|right
  · exact Or.inr (other_unit hn eq (descend an hA left))
  · exact Or.inl (other_unit hn (eq.trans (mul_comm ..)) (descend bn hB right))

structure Model {h} {D:PoleData h} (Crt:CRTLift D) (N:Jet) where
  raw : RawSource
  primitive : raw.IsPrimitive
  c : SeedField
  unit_c : c≠0
  eq : doubleMap evalRaw raw=jetConstant c*specialized Crt N

theorem exists_model {h} {D:PoleData h} (Crt:CRTLift D) {N:Jet} (irr:Irreducible N)
    (slope:0<N.natDegree) : Nonempty (Model Crt N) := by
  let f:=algebraMap Seeds SeedField
  obtain ⟨a,b,u,d,an,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let T:=PadeChart.chart a b u d
  let eqv:=AlgEquiv.ofBijective T (PadeChart.chart_equiv a b u d an)
  have chart:specialized Crt N=T (doubleMap f N) := by
    have id:=RingHom.congr_fun form N
    change specialized Crt N=_ at id
    rw [id]
    change _ = (K1_14_1_4.substitute (RingHom.id SeedField) _ _).comp (doubleMap f) N
    rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  have generic:Irreducible (doubleMap f N):=generic_prime (R:=Seeds) (N:=N) irr.prime slope
  have image:Irreducible (specialized Crt N) := by rw [chart];exact (MulEquiv.irreducible_iff eqv).mpr generic
  have pos:(specialized Crt N).natDegree≠0:=by rw [(K1_14_1_4.specialized_leading Crt irr.ne_zero).1];exact slope.ne'
  obtain ⟨G,c,prim,unit,id⟩:=PadeIntegralGraph.raw_model _ (image.isPrimitive pos)
  exact ⟨⟨G,prim,c,unit,id⟩⟩

theorem Model.physical_support {h W t:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} {Crt:CRTLift D}
    {N:Jet} (M:Model Crt N) (word:K1.I→K1_14.L) {s:K1_14.Shape} {P:K1_14_1.Source} {Q:Jet}
    (member:P∈K1_14_1.complete Crt word s W) (div:centerEval P=N^t*Q) (j i:ℕ)
    (nz:((specialized Crt Q).coeff j).coeff i≠0) :
    (131071-h)*i+(131071-h-1)*j+t*RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw≤W := by
  obtain ⟨R,rawEq,bounded⟩:=P0_10_1.complete_raw_bounded hp hl Crt word member
  let block:=evalRaw ((K1_14_1.rawBlock D)^(s.B+s.J))
  have blockUnit:IsUnit (jetConstant block:SeedField[X][X]) :=
    isUnit_C.mpr (isUnit_C.mpr (by
      dsimp only [block];rw [map_pow];exact (pow_ne_zero _ (K1_14_1_4.evalRaw_block_ne_zero D)).isUnit))
  have val:=K1_14_1_4.specialized_center Crt P
  rw [div,map_mul,map_pow,rawEq,map_mul] at val
  have pole:doubleMap evalRaw (jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)))=jetConstant block := by
    simp only [doubleMap,jetConstant,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply];rfl
  rw [pole] at val
  have unit:IsUnit (jetConstant M.c:SeedField[X][X]) := isUnit_C.mpr (isUnit_C.mpr M.unit_c.isUnit)
  have gv:(doubleMap evalRaw M.raw)^t∣doubleMap evalRaw R := by
    rw [M.eq,mul_pow]
    apply (associated_unit_mul_left _ _ blockUnit).dvd_iff_dvd_right.mp
    exact (associated_unit_mul_left _ _ (unit.pow t)).dvd.trans ⟨_,val.symm⟩
  obtain ⟨S,id⟩:=PadeRawField.integral_power evalRaw PadeRawField.eval_injective M.primitive t gv
  have mapped:doubleMap evalRaw M.raw≠0:=(map_ne_zero_iff (doubleMap evalRaw)
    (map_injective _ (map_injective _ PadeRawField.eval_injective))).mpr M.primitive.ne_zero
  have sn:specialized Crt N≠0:=by intro z;apply mapped;rw [M.eq,z,mul_zero]
  rw [id,map_mul,map_pow,M.eq,mul_pow] at val
  have same:specialized Crt Q=jetConstant (block*M.c^t)*doubleMap evalRaw S := by
    apply mul_left_cancel₀ (pow_ne_zero t sn)
    calc
      _ = _ := val
      _ = _ := by rw [map_mul jetConstant,map_pow jetConstant];ring
  have nonzero:(S.coeff j).coeff i≠0 := by
    intro z;apply nz
    rw [same]
    simp only [jetConstant,RingHom.comp_apply,coeff_C_mul,doubleMap,coe_mapRingHom,coeff_map,z,map_zero,mul_zero]
  have nonS:S≠0:=by intro z;exact nonzero (by simp [z])
  have paid:=(RawPhysicalDegree.bounded_iff ..).mp bounded
  rw [id,RawPhysicalDegree.weight_product _ _ (pow_ne_zero t M.primitive.ne_zero) nonS] at paid
  have pw:RawPhysicalDegree.weight (131071-h) (131071-h-1) (M.raw^t)=
      t*RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw := by simp [RawPhysicalDegree.weight,natDegree_pow]
  rw [pw] at paid
  have own:=(RawPhysicalDegree.bounded_iff (131071-h) (131071-h-1) _ S).mpr le_rfl
  have last:=own j i ((S.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr nonzero)
  omega

#print axioms generic_prime
#print axioms exists_model
#print axioms Model.physical_support

def Model.mul {h} {D:PoleData h} {Crt:CRTLift D} {A B:Jet} (left:Model Crt A) (right:Model Crt B) :
    Model Crt (A*B) where
  raw:=left.raw*right.raw
  primitive:=by
    let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=K1_14_1.SeedField[X][X])
    let := UniqueFactorizationMonoid.toNormalizedGCDMonoid K1_14_1.SeedField[X][X]
    exact left.primitive.mul right.primitive
  c:=left.c*right.c
  unit_c:=mul_ne_zero left.unit_c right.unit_c
  eq:=by rw [map_mul,left.eq,right.eq,map_mul jetConstant,map_mul];ring
end
end Research6966.HelperPhysicalModel

end Merged6967_R6966ProofHelperPhysicalModel

section Merged6967_R6966ProofPadeConcentration
set_option Elab.async false


set_option Elab.async false

namespace Research6966.PadeConcentration
open Polynomial Finset
open K1_14 (Jet L Shape)
open K1_14_1 (PoleData CRTLift RawSource jetConstant centerEval)
open K1_14_1_4 (doubleMap specialized)
open K1_14_3 (SeedClosure SeedField Parent Surface fibreRow)
open PadeRank (Plane)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure
private abbrev extField:=algebraMap SeedField E

/-- One primitive integral physical polynomial for the descended graph
at this CRT chart. Its choice precedes the choice of bank, row and cutoff. -/
structure Model {h} {D:PoleData h} (Crt:CRTLift D) (G:Pade.Row SeedField) where
  raw : RawSource
  primitive : raw.IsPrimitive
  transform : Plane E →ₐ[E] Plane E
  scalar : E
  nonzero : scalar≠0
  equation : doubleMap PadeRawField.rawField raw = jetConstant scalar*transform ((G.map extField).polynomial)
  onRows : ∀ P:Jet, transform (fibreRow P)=doubleMap extField (specialized Crt P)
  leading : ∀ {P:Plane E},P≠0 → (transform P).natDegree=P.natDegree ∧
    (transform P).leadingCoeff.natDegree=P.leadingCoeff.natDegree ∧ transform P≠0

theorem exists_model {h} {D:PoleData h} (Crt:CRTLift D) {G:Pade.Row SeedField} (gp:G.primitive) :
    Nonempty (Model Crt G) := by
  obtain ⟨a,b,u,d,ne,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let f:=extField
  let T:=PadeChart.chart (f a) (f b) (f u) (f d)
  let T₀:=PadeChart.chart a b u d
  obtain ⟨g,c,prim,cn,eq⟩:=PadeIntegralGraph.raw_model (T₀ G.polynomial)
    (PadeChart.chart_graph_primitive a b u d ne gp)
  refine ⟨⟨g,prim,T,f c,(map_ne_zero f).mpr cn,?_,?_,?_⟩⟩
  · have mapped:=congrArg (doubleMap f) eq
    rw [map_mul] at mapped
    have lhs:doubleMap f (doubleMap K1_14_1_4.evalRaw g)=doubleMap PadeRawField.rawField g := by
      ext j i;simp only [doubleMap,coe_mapRingHom,coeff_map,PadeRawField.rawField,RingHom.comp_apply];rfl
    have unit:doubleMap f (jetConstant c)=jetConstant (f c) := by
      simp only [jetConstant,doubleMap,RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C]
    have mappedGraph : doubleMap f G.polynomial=(G.map f).polynomial:=by
      simp only [Pade.Row.polynomial,Pade.Row.map,doubleMap,coe_mapRingHom,Polynomial.map_C,
        Polynomial.map_X,map_sub,map_mul]
    have natural:=PadeFiltered.base_change (RingHom.id SeedField) f a b u d
    rw [RingHom.comp_id] at natural
    have commute:=RingHom.congr_fun natural G.polynomial
    change T (doubleMap f G.polynomial)=doubleMap f (T₀ G.polynomial) at commute
    rw [mappedGraph] at commute
    rwa [lhs,unit,←commute] at mapped
  · intro P
    change T.toRingHom.comp (doubleMap (f.comp (algebraMap K1_14.Seeds SeedField))) P =
      (doubleMap f).comp (specialized Crt).toRingHom P
    rw [form,PadeFiltered.base_change]
  · intro P pn
    exact K1_14_1_4.affine_leading (RingHom.id E) Function.injective_id ((map_ne_zero f).mpr ne)
      (b:=f b) (C (f u)*Polynomial.X+C (f d)) pn

/-- Every actual complete source has an integral quotient with the raw
physical weight reduced by the full rounded number of forced powers. -/
theorem Model.quotient {h A W r:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    {Crt:CRTLift D} {G:Pade.Row SeedField} (m:Model Crt G) (gp:G.primitive)
    (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ (G.map extField).err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (bound:min s.B ((W+s.J)/(131071-h))≤b)
    {P:K1_14_1.Source} (member:P∈KoalaRect.rectComplete Crt word s W U) :
    let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
    ∃ Q:RawSource,K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J))*(m.raw^t*Q) ∧
      K1_14_1_4.Bounded (131071-h) (131071-h-1) (W-t*RawPhysicalDegree.weight (131071-h) (131071-h-1) m.raw) Q := by
  classical
  let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
  have cMem:centerEval P∈KoalaRect.rectEvaluated Crt word s W U:=Submodule.subset_span ⟨P,member,rfl⟩
  have inBank:fibreRow (centerEval P)∈PadeBankRank.rows Crt word s W U:=
    Submodule.subset_span ⟨centerEval P,cMem,rfl⟩
  have fieldPow:=PadeFiltered.forced_bank_layers hp hl Crt word U fits small cut geo pass ys v
    ((G.primitive_map extField).mpr gp) sheets (by rwa [Pade.Row.degree_map]) b bound inBank
  rw [Pade.Row.degree_map] at fieldPow
  change (G.map extField).polynomial^t ∣ fibreRow (centerEval P) at fieldPow
  have transformed:=map_dvd m.transform fieldPow
  rw [map_pow,m.onRows] at transformed
  apply PadeRawField.quotient_of_fibre_power hp hl Crt word member.1 m.primitive t
  have unit:IsUnit (jetConstant m.scalar:Plane E):=isUnit_C.mpr (isUnit_C.mpr m.nonzero.isUnit)
  rw [m.equation,mul_pow]
  exact (associated_unit_mul_left _ _ (unit.pow t)).dvd.trans transformed

#print axioms exists_model
#print axioms Model.quotient
end
end Research6966.PadeConcentration

end Merged6967_R6966ProofPadeConcentration

section Merged6967_R6966ProofSpreadWindow
set_option Elab.async false


set_option Elab.async false

namespace Research6966.SpreadWindow
open Finset
open K1_14 (Shape shapeSum)
open K1_14_4 (gradeWidth gradeWidth_card shapeSum_swap)
open PadeFiltered (physicalWindow)
open KoalaRect (area rectCapacity rectPower rectGrade)
set_option maxHeartbeats 1000000

def size (B J : ℕ) : ℕ :=
  let j := min B J
  (j+1)*(B+1)-j*(j+1)/2

def boundary (B J step W : ℕ) : ℕ :=
  let q := min B (W/step)
  size q J + if q < B then min J (q+1)+1-((q+1)*step-W) else 0

def lex (B J e k : ℕ) : ℕ :=
  size B J-SpreadLines.minSum (B+1) 1 (k*e) e (min k (min (J+1) (B+1)))

theorem size_eq (B J : ℕ) : size B J = ∑ j ∈ range (J+1), (B+1-j) := by
  let t := min B J
  have tj : t≤J := min_le_right _ _
  have cut : (∑ j ∈ range (t+1), (B+1-j)) = ∑ j ∈ range (J+1), (B+1-j) := by
    apply sum_subset (range_mono (Nat.succ_le_succ tj))
    intro j mem out
    simp only [mem_range] at mem out
    dsimp only [t] at out
    omega
  rw [← cut]
  have eq : (∑ j ∈ range (t+1), (B+1-j)) + ∑ j ∈ range (t+1), j = (t+1)*(B+1) := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _j ∈ range (t+1), (B+1) := by
        apply sum_congr rfl
        intro j hj
        have bound := (mem_range.mp hj).le.trans (Nat.succ_le_succ (min_le_left B J))
        exact Nat.sub_add_cancel bound
      _ = _ := by simp
  rw [sum_range_id,Nat.add_sub_cancel,Nat.mul_comm (t+1) t] at eq
  unfold size
  change (t+1)*(B+1)-t*(t+1)/2 = _
  omega

private theorem shape_size (B J : ℕ) :
    (∑ q ∈ range (B+1), (min q J+1)) = size B J := by
  let s : Shape := ⟨0,B,J,0⟩
  have e := shapeSum_swap s (fun _ _ => 1)
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.mul_one, card_range, shapeSum, s] at e
  exact e.symm.trans (size_eq B J).symm

theorem weight_iff (step j i W : ℕ) (pos : 0 < step) :
    step*i+(step-1)*j≤W ↔ (j+i)*step≤W+j := by
  have v := congrArg (fun t => t*j) (Nat.sub_add_cancel pos : step-1+1=step)
  rw [Nat.add_mul,Nat.one_mul] at v
  rw [Nat.add_mul, Nat.mul_comm j step, Nat.mul_comm i step]
  omega

private theorem card_slope (B J step W : ℕ) (wp : 0 < step) :
    (physicalWindow B J step W).card = ∑ j ∈ range (J+1), gradeWidth step B W j := by
  classical
  rw [physicalWindow,PadeRank.positions,filter_filter,card_filter,sum_product]
  apply sum_congr rfl
  intro j _
  rw [← card_filter]
  have row : ((range (B+1)).filter (fun i =>
      j+i<B+1 ∧ step*i+(step-1)*j≤W)) = range (gradeWidth step B W j) := by
    ext i
    simp only [mem_filter,mem_range,weight_iff step j i W wp,gradeWidth,
      ← Nat.le_div_iff_mul_le wp]
    omega
  rw [row,card_range]

private theorem card_grade (B J step W : ℕ) (wp : 0 < step) :
    (physicalWindow B J step W).card =
      ∑ q ∈ range (B+1), ∑ j ∈ range (min q J+1), if q*step≤W+j then 1 else 0 := by
  let s : Shape := ⟨0,B,J,0⟩
  rw [card_slope B J step W wp]
  simp_rw [gradeWidth_card step B W _ wp]
  exact shapeSum_swap s (fun q j => if q*step≤W+j then 1 else 0)

theorem boundary_eq (B J step W : ℕ) (small : J < step) :
    boundary B J step W = (physicalWindow B J step W).card := by
  classical
  have wp : 0 < step := by omega
  rw [card_grade B J step W wp]
  let q := min B (W/step)
  let slots (i : ℕ) := ∑ j ∈ range (min i J+1), if i*step≤W+j then 1 else 0
  change size q J+(if q < B then min J (q+1)+1-((q+1)*step-W) else 0) =
    ∑ i ∈ range (B+1), slots i
  have qb : q≤B := min_le_left _ _
  have full : q*step≤W := (Nat.le_div_iff_mul_le wp).mp (min_le_right ..)
  have complete : (∑ i ∈ range (q+1), slots i) = size q J := by
    rw [← shape_size]
    apply sum_congr rfl
    intro i hi
    unfold slots
    have ready := (Nat.mul_le_mul_right step (Nat.lt_succ_iff.mp (mem_range.mp hi))).trans full
    have ready' (j : ℕ) : i*step≤W+j := ready.trans (Nat.le_add_right _ _)
    simp [ready']
  rw [← sum_range_add_sum_Ico slots (Nat.succ_le_succ qb),complete]
  congr 1
  by_cases next : q < B
  · rw [ite_eq_left next, sum_eq_single (q+1)]
    · have test (j : ℕ) : (q+1)*step≤W+j ↔ (q+1)*step-W≤j := by omega
      unfold slots
      simp only [test]
      rw [← card_filter]
      have eq : ((range (min (q+1) J+1)).filter (fun j => (q+1)*step-W≤j)) =
          Ico ((q+1)*step-W) (min (q+1) J+1) := by
        ext j
        simp [and_comm]
      rw [eq,Nat.card_Ico,min_comm]
    · intro i hi ne
      have qi : q+2 ≤ i := by have hh := (mem_Ico.mp hi).1; omega
      have exactQ : q=W/step := by dsimp only [q] at next ⊢; omega
      have strong : W<(q+1)*step := (Nat.div_lt_iff_lt_mul wp).mp (by omega)
      have width := Nat.mul_le_mul_right step qi
      rw [show q+2=(q+1)+1 by omega,Nat.add_mul,Nat.one_mul] at width
      apply sum_eq_zero
      intro j hj
      have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_right i J)
      rw [ite_eq_right (by omega)]
    · intro bad
      exact (bad (mem_Ico.mpr ⟨le_rfl,Nat.succ_lt_succ next⟩)).elim
  · rw [ite_eq_right next, show q=B by omega, Ico_self,sum_empty]

private theorem lex_loss_le (B J e k : ℕ) :
    SpreadLines.minSum (B+1) 1 (k*e) e (min k (min (J+1) (B+1))) ≤
      ∑ j ∈ range (J+1), min (B+1-j) ((k-j)*e) := by
  let m := min k (min (J+1) (B+1))
  have mj : m≤J+1 := (min_le_right _ _).trans (min_le_left _ _)
  refine (SpreadLines.minSum_le ..).trans ?_
  have eq (j : ℕ) : k*e-e*j=(k-j)*e := by
    rw [Nat.mul_comm k e,← Nat.mul_sub_left_distrib,Nat.mul_comm e (k-j)]
  simp only [Nat.one_mul,eq]
  exact sum_le_sum_of_subset_of_nonneg (range_mono mj) (by intros; exact Nat.zero_le _)

theorem lex_ge (B J e k : ℕ) :
    (∑ j ∈ range (J+1), ((B+1-j)-(k-j)*e)) ≤ lex B J e k := by
  have whole : (∑ j ∈ range (J+1), ((B+1-j)-(k-j)*e)) +
      (∑ j ∈ range (J+1), min (B+1-j) ((k-j)*e)) = size B J := by
    rw [size_eq,← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by omega)
  have paid := lex_loss_le B J e k
  unfold lex
  omega

theorem rect_lex (A h e k W B : ℕ) (s : Shape) (U : Fin 2 → ℕ)
    (wp : 0 < 131071-h) (ep : 0 < e) (layer : rectPower A h s W = k)
    (cap : ∀ j ≤ s.J, gradeWidth (131071-h) s.B W j ≤ B+1-j) :
    rectCapacity A h s e U (fun _ => 0) W ≤ lex B s.J e k*area U := by
  rw [← KoalaRect.rectCapacity_eq A h s e U (fun _ => 0) W wp ep]
  have slots (r : ℕ) : KoalaRect.rectSlots U (fun _ => 0) r = area U := by
    simp [KoalaRect.rectSlots,area]
  simp only [rectGrade,layer,slots]
  rw [← sum_mul]
  refine Nat.mul_le_mul_right _ ((sum_le_sum (fun j hj =>
    Nat.sub_le_sub_right (cap j (Nat.lt_succ_iff.mp (mem_range.mp hj))) _)).trans (lex_ge ..))

theorem rect_zero (A h e W : ℕ) (s : Shape) (U : Fin 2 → ℕ)
    (wp : 0 < 131071-h) (ep : 0 < e)
    (far : s.J+s.B/e+1 < rectPower A h s W) :
    rectCapacity A h s e U (fun _ => 0) W = 0 := by
  rw [← KoalaRect.rectCapacity_eq A h s e U (fun _ => 0) W wp ep]
  apply sum_eq_zero
  intro j hj
  have jle := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have r : s.B/e < rectPower A h s W-j := by omega
  have gone := (Nat.div_lt_iff_lt_mul ep).mp r
  have cap : gradeWidth (131071-h) s.B W j ≤ s.B+1 := by unfold gradeWidth; omega
  unfold rectGrade
  dsimp only
  rw [Nat.sub_eq_zero_of_le (cap.trans (Nat.succ_le_of_lt gone)),Nat.zero_mul]

#print axioms boundary_eq
#print axioms rect_lex
#print axioms rect_zero
end Research6966.SpreadWindow

end Merged6967_R6966ProofSpreadWindow
