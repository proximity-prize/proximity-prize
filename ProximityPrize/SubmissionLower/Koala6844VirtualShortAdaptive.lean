import ProximityPrize.SubmissionLower.Koala6844VirtualShortFirstJet
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSource
import ProximityPrize.SubmissionLower.Koala6844ReceiptsStageExit


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetGlobalSupport
open RCN095 RCN130 RCN266 LocatorFactorAggregate LocatorLowQuotient LocatorBatchProductRoute
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6844Receipts (ClearedForm geometricGate)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 50000

variable {K I : Type} [Field K] [Fintype I]
local instance : DecidableEq K := Classical.decEq K

theorem exists_firstJet_adaptive_exit
    (D : ℕ → ℕ) (w wQ m L B U q a C gain : ℕ) (hw : 1 ≤ w)
    (hUL : U ≤ L) (hqU : q ≤ U) (hcut : D 0 ≤ C) (hcaps : U ≤ (D 0+B-1)/w)
    (A₀ A₁ d C₁ : Polynomial K) (ha : A₁ ≠ 0) (hd : d ≠ 0)
    (h₀ : A₀.natDegree ≤ a) (h₁ : A₁.natDegree ≤ a)
    (hdw : d.natDegree+w ≤ a+wQ) (hC : C₁.natDegree ≤ a+wQ)
    (x u0 u1 : I → K) (v : I → K)
    (h0 : ∀ i, d.eval (x i)*u0 i = v i*A₀.eval (x i))
    (h1 : ∀ i, d.eval (x i)*u1 i+C₁.eval (x i) = v i*A₁.eval (x i))
    (hLead : ∀ i, A₁.eval (x i) ≠ 0)
    (gap : ℕ) (hgap : gap ≤ Fintype.card (NormalizedIndex D w wQ L B 0 U q) -
      Fintype.card I * normalizedRankBudget D w m L B 0 U q)
    (H : MvPolynomial (Fin 4) K) (factors : Finset (RegularIndex H))
    (hFactors : factors.Nonempty) (hField : factors.card < ENat.card K)
    (hSlope : 0 < (originalCumulativeFlag (regularProduct H factors)).all)
    (hFuel : 0 < (⟨L+q,U,B,gap⟩ : SourceNumbers).fuel (originalCumulativeFlag (regularProduct H factors)))
    (hGate : geometricGate gain ⟨L+q,U,B,gap⟩ (originalCumulativeFlag (regularProduct H factors))) :
    let A := normalizedDenominator A₀ A₁
    let N := normalizedNumerator d C₁
    let V := (jointContactMap D w wQ L B 0 U q m A N x u0 u1).ker
    let F := firstJetClearedLinear D w wQ L B U q A N
    ∃ remaining ⊂ factors, ∃ c : V, ∃ j : ℕ,
      j ≤ (⟨L+q,U,B,gap⟩ : SourceNumbers).fuel (originalCumulativeFlag (regularProduct H factors)) ∧
      F c.val ≠ 0 ∧ F c.val ∈ nestedCoefficientBox K (C+q*a-j*gain) w (L+q) U B ∧
      ClearedForm (toFirstJet A) (toFirstJet N) q (F c.val) ∧
      ∀ f ∈ factors \ remaining, ∃ J : MvPolynomial (Fin 4) K,
        F c.val = f.val^j*J ∧ ¬ f.val ∣ J := by
  classical
  dsimp only
  let A := normalizedDenominator A₀ A₁
  let N := normalizedNumerator d C₁
  let V := (jointContactMap D w wQ L B 0 U q m A N x u0 u1).ker
  let F := firstJetClearedLinear D w wQ L B U q A N
  let f : V →ₗ[K] MvPolynomial (Fin 4) K := F.comp (Submodule.subtype V)
  have hf : Function.Injective f :=
    (firstJetClearedLinear_injective D w wQ L B U q hUL hqU A₀ A₁ d C₁ ha hd).comp Subtype.val_injective
  have hbox (c : V) := firstJetClearedLinear_mem_nestedCoefficientBox D w wQ L B U q a C
    hUL hqU hcut A₀ A₁ d C₁ h₀ h₁ hdw hC c.val
  have hlocal (i : I) : Module.finrank K
      (normalizedContactMap D w wQ L B 0 U q m A N (x i) (u0 i) (u1 i)).range ≤
      normalizedRankBudget D w m L B 0 U q := by
    obtain ⟨data⟩ := exists_nodePoleData (x i) (u0 i) (u1 i) (v i) m A₀ A₁ d C₁ (h0 i) (h1 i) (hLead i)
    exact normalized_local_rank_bound D w wQ L B 0 U q m (by omega) hUL hqU
      (fun h => (D h+B-1)/w) (fun h hh => by simpa [Nat.eq_zero_of_le_zero hh] using hcaps)
      A N (x i) (u0 i) (u1 i) data
  have hdim : gap ≤ Module.finrank K V := hgap.trans
    (normalizedContactKernel_finrank D w wQ L B 0 U q m (normalizedRankBudget D w m L B 0 U q)
      A N x u0 u1 hlocal)
  obtain ⟨S,hS,c,j,hj,hc,hbound,hfactor⟩ := Koala6844Receipts.exists_adaptive_source_exit
    ⟨L+q,U,B,gap⟩ (C+q*a) w gain hw f hf hbox hdim H factors hFactors hField hSlope hFuel hGate
  exact ⟨S,hS,c,j,hj,hc,hbound,firstJetClearedLinear_clearedForm D w wQ L B U q A N c.val,hfactor⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
