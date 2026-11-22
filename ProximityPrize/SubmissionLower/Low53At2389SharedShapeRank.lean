import ProximityPrize.SubmissionLower.Shared50ShapeRank
import ProximityPrize.SubmissionLower.Low53At2389Order
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Low53At2389ShapeGate

set_option Elab.async false
set_option maxRecDepth 40000
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000
namespace Low53At2389SharedShapeRank
noncomputable section

open K1_13 (Geom Row extend shape InBox OrderAt)
open K1_13_6 (GenericField GeoField GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder taylorHom taylor_coeff)
open Shared50Rational
open Shared50ShapeRank (ambient ambient_dim contactSpace)
open private hasse_C_mul from ProximityPrize.SubmissionLower.Shared50ShapeRank
open Shared50Persistent (Persistent derivative_mem)
open TaperColumns (jetExponents jetColumns jet_card_eq)
open MvPolynomial Finset

def cutoff (r : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (Low53At2389ShapeGate.fits r)))).comap ambient.subtype

theorem cutoff_dim (r : ℕ) : Module.finrank GenericField (cutoff r) = Low53At2389ShapeGate.width r := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (Low53At2389ShapeGate.fits r))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact TaperColumns.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (Low53At2389ShapeGate.fits r)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,finrank_restrictSupport_finset]
  rfl

open P3 (I K node)
open K1_13 (embed)
open Low53At2389Order (PrimaryRank primaryCutoff layerWidth sourceRank layerNeed requiredOrder)
open scoped BigOperators
open private exists_fresh sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase

theorem bank_layers {w Γ s} (hm : Low53At2389Price.Messages w Γ s) (hprimary : PrimaryRank w)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    layerNeed ≤ ∑ i ∈ range (1+primaryCutoff/layerWidth),
      Module.finrank GenericField (contactSpace surfaces (i+1)) := by
  obtain ⟨x,hx,_⟩ := exists_fresh (fun _ : Fin 0 => (0 : Row 4))
  obtain ⟨r,hr,hbank⟩ := Low53At2389Order.symbol_families w x hprimary hx
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
        exact Low53At2389Order.order_of_contact w (e i) hT (he i).2.1 (he i).2.2.2
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
theorem exists_small {w Γ s} (hm : Low53At2389Price.Messages w Γ s) (hprimary : PrimaryRank w)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : FractionJet, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low53At2389ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric Q) ∈ P := by
  have hbank := bank_layers hm hprimary surfaces hp
  let N := 1+primaryCutoff/layerWidth
  have h : (∑ i ∈ range N, (Module.finrank GenericField ambient -
      Module.finrank GenericField (cutoff (i+1)))) <
      ∑ i ∈ range N, Module.finrank GenericField (contactSpace surfaces (i+1)) := by
    simp only [ambient_dim,cutoff_dim]
    exact (Low53At2389ShapeGate.loss_bound N).trans_lt
      ((by decide : Low53At2389ShapeGate.slopeLoss < layerNeed).trans_le hbank)
  obtain ⟨i,_,Q,hQ,hm,ht⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N)
      (fun i => contactSpace surfaces (i+1)) (fun i => cutoff (i+1)) h
  refine ⟨i+1,by omega,Q.val,fun hz => hQ (Subtype.ext hz),?_,hm⟩
  intro m hmem
  exact (Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp ht hmem)).2

theorem exists_polynomial {w Γ s} (hm : Low53At2389Price.Messages w Γ s) (hprimary : PrimaryRank w)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low53At2389ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeneric Q) ∈ P := by
  obtain ⟨r,hr,U,hU,hs,ho⟩ := exists_small hm hprimary surfaces hp
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
end Low53At2389SharedShapeRank
