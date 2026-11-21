import ProximityPrize.SubmissionLower.Shared50Rational
import ProximityPrize.SubmissionLower.Shared50Persistent
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Final50ShapeGate

set_option Elab.async false
set_option maxRecDepth 40000
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000
namespace Shared50ShapeRank
noncomputable section

open K1_13 (Geom Row extend shape InBox OrderAt)
open K1_13_6 (GenericField GeoField GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder taylorHom taylor_coeff)
open Shared50Rational
open Shared50Persistent (Persistent derivative_mem)
open TaperColumns (jetExponents jetColumns jet_card_eq)
open MvPolynomial Finset

def ambient : Submodule GenericField FractionJet :=
  restrictSupport GenericField jetExponents

instance : Module.Finite GenericField ambient :=
  restrictSupport_finite TaperColumns.jetExponents_finite

theorem ambient_dim : Module.finrank GenericField ambient = Final50Price.symbolCount := by
  have h : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
  rw [ambient,← h,finrank_restrictSupport_finset]
  have hc := jet_card_eq
  rw [TaperColumns.sourceCount_eq] at hc
  exact_mod_cast hc

def cutoff (r : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r)))).comap ambient.subtype

theorem cutoff_dim (r : ℕ) : Module.finrank GenericField (cutoff r) = Final50ShapeGate.width r := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact TaperColumns.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,finrank_restrictSupport_finset]
  rfl

theorem hasse_add (a : Fin 4 →₀ ℕ) (P Q : GeoJets) :
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
open Final50Order (primaryCutoff layerWidth sourceRank layerNeed requiredOrder)
open scoped BigOperators
open private exists_fresh sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase

theorem bank_layers {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    layerNeed ≤ ∑ i ∈ range (1+primaryCutoff/layerWidth),
      Module.finrank GenericField (contactSpace surfaces (i+1)) := by
  obtain ⟨x,hx,_⟩ := exists_fresh (fun _ : Fin 0 => (0 : Row 4))
  obtain ⟨r,hr,hbank⟩ := Final50Order.symbol_families w x (Final50Order.primary_rank w) hx
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
        exact Final50Order.order_of_contact w (e i) hT (he i).2.1 (he i).2.2.2
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
theorem exists_small {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : FractionJet, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Final50ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric Q) ∈ P := by
  have hbank := bank_layers hm surfaces hp
  let N := 1+primaryCutoff/layerWidth
  have hgate := Final50ShapeGate.loss_bound N
  have h : (∑ i ∈ range N, (Module.finrank GenericField ambient -
      Module.finrank GenericField (cutoff (i+1)))) <
      ∑ i ∈ range N, Module.finrank GenericField (contactSpace surfaces (i+1)) := by
    simp only [ambient_dim,cutoff_dim]
    exact hgate.trans_lt ((by decide : Final50SharedPrice.slopeLoss < layerNeed).trans_le hbank)
  obtain ⟨i,_,Q,hQ,hm,ht⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N)
      (fun i => contactSpace surfaces (i+1)) (fun i => cutoff (i+1)) h
  refine ⟨i+1,by omega,Q.val,fun hz => hQ (Subtype.ext hz),?_,hm⟩
  intro m hmem
  exact (Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp ht hmem)).2

theorem exists_polynomial {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Final50ShapeGate.fits r m) ∧
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
end Shared50ShapeRank
