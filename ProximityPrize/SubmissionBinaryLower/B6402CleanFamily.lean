import ProximityPrize.SubmissionBinaryLower.B6402CarriedFactor
import ProximityPrize.SubmissionBinaryLower.B6402SpecialRouting
import ProximityPrize.SubmissionBinaryLower.B6402GroupCharge

namespace ProximityPrize.SubmissionBinaryLower.B6402CleanFamily
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A BadOn6402)
open B6401ContactKerD B6401QuotInterp B6402HardFactor B6402BucketBudget B6402GridProfile
open B6402GridRouting B6402Table4Common B6402SpecialRouting Native6402Grid
open B6401FactorBound (G_val std5Slot std5Slot_spec)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

def Bank : Prop := ∀ (i : Fin 237) (q : ℕ),q=1 ∨ q=2 → Ordinary (key i) q ∨ Replacement (key i) q

theorem limits : ∀ i : Fin 237, hi (key i)≤28/5 ∧ 0<(key i).gap.2.2.2 ∧ (key i).gap.2.2.1≤(key i).gap.2.2.2 := by decide +kernel

theorem gap_for_slot (k : Key) (r : Fin 5) (eid : k.gap=B6401T4Grid.std5Bounds r) (WF : ℕ) (ord : I → ℕ) (Az : Finset I)
    (nonneg : 0≤G_val WF ord Az) (eq : std5Slot (G_val WF ord Az)=r) : Upper k WF ord Az := by
  intro lim
  have h := std5Slot_spec nonneg
  dsimp only at h
  rw [eq] at h
  rw [eid] at lim
  have hu := h.2.2.2 lim
  unfold gapHi; rw [eid,div_mul_eq_mul_div]
  apply (le_div_iff₀ (by exact_mod_cast h.2.1 : (0:ℚ)<(B6401T4Grid.std5Bounds r).2.2.2)).mpr
  rw [mul_comm] at hu
  exact_mod_cast hu

theorem count (bank : Bank) {u₀ u₁ : I → K} {q : ℕ} (hq : q=1 ∨ q=2) (f : Model u₀ u₁ q)
    (S : Finset K) (P : K → K[X]) (Az : K → Finset I)
    (hP : ∀ z∈S,(P z).natDegree≤wY) (hA : ∀ z∈S,A≤(Az z).card)
    (matchP : ∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i)
    (onF : ∀ z∈S,evalContact (evalZContact f.F z) (P z)=0) (badP : ∀ z∈S,BadOn6402 u₀ u₁ (Az z))
    (mk : ∀ z∈S,KerD45Data)
    (hw : ∀ z (h:z∈S),(mk z h).W_F=f.WF) (hk : ∀ z (h:z∈S),(mk z h).k=f.k)
    (ha : ∀ z (h:z∈S),(mk z h).Az=Az z)
    (route : ∀ z (h:z∈S), Assigned (mk z h) (std5Slot (G_val f.WF f.k (Az z)))) :
    S.card≤singleBudget q+(∑ r : Fin 5,groupBudget r q)+5*(N*1813) := by
  classical
  let slot z := std5Slot (G_val f.WF f.k (Az z))
  have hg (z:K) (h:z∈S) : 0≤G_val f.WF f.k (Az z) := by
    have n := B6402ProfileMatch.nonneg (mk z h)
    rwa [hw,hk,ha] at n
  apply B6402GroupCharge.group_sum S slot
  intro z hz
  let D := mk z hz
  obtain ⟨j,covers,cl,ch,feas⟩ := route z hz
  let tag := key j
  have wD : D.W_F=f.WF := hw _ _
  have kD : D.k=f.k := hk _ _
  rw [hw] at cl ch
  have pay (U : Finset K) (inc : U⊆S) (upper : ∀ t∈U,Upper tag f.WF f.k (Az t)) :
      U.card≤budget tag q+N*1813 := by
    have l := limits j
    rcases bank j q hq with orig|new
    · apply Nat.le_trans _ (Nat.le_add_right _ _)
      exact B6402CarriedFactor.estimate hq f D wD kD tag feas cl ch l.2.2 orig U P Az
        (fun t h => hP t (inc h)) (fun t h => hA t (inc h)) (fun t h => matchP t (inc h))
        (fun t h => onF t (inc h)) (fun t h => badP t (inc h)) upper
    · exact replacement hq f D wD kD tag feas cl ch l.1 l.2.1 new U P Az
        (fun t h => hP t (inc h)) (fun t h => hA t (inc h)) (fun t h => matchP t (inc h))
        (fun t h => onF t (inc h)) (fun t h => badP t (inc h)) upper
  rcases covers with std|full
  · right
    let U := S.filter fun t => slot t=slot z
    have h := pay U (Finset.filter_subset _ _) (fun t ht => gap_for_slot tag (slot z) std f.WF f.k (Az t)
      (hg t (Finset.mem_filter.mp ht).1) (Finset.mem_filter.mp ht).2)
    rwa [standard tag (slot z) q std] at h
  · left
    have h := pay S (fun _ h => h) (fun _ _ hi => False.elim (by rw [full] at hi; exact (by decide : ¬(1:ℕ)<1) hi))
    have hf : tag.gap=single := full
    have ee : budget tag q=singleBudget q := by unfold budget; rw [ite_eq_left hf]
    rwa [ee] at h

#print axioms count
end ProximityPrize.SubmissionBinaryLower.B6402CleanFamily
