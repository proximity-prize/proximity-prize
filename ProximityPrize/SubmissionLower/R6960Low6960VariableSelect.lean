import ProximityPrize.SubmissionLower.R6960Low6960SharedRational
import ProximityPrize.SubmissionLower.R6960Low6960SharedPersistent
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.R6960Low6960ShapeGate
import ProximityPrize.SubmissionLower.FadicDegree
import ProximityPrize.SubmissionLower.R6960Low6960FastPrice

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
    (hfit : Low6960WeightedRate.Fits p (shape f)) (hact : ActiveFits f 177) :
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
  · refine (FadicGate.taper_le (toFraction f) (shape f).b (shape f).j 177 ?_ ?_ ?_).trans h7
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
    (hfit : Low6960WeightedRate.Fits p (shape f)) (hact : ActiveFits f 177)
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
