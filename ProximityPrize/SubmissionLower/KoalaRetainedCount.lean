import ProximityPrize.SubmissionLower.KoalaWeightedLayer2428
import ProximityPrize.SubmissionLower.KoalaRetainedBank
import ProximityPrize.SubmissionLower.KoalaRetainedCover

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace KoalaRetainedCut
noncomputable section

open P3 (I K)
open K1_13 (Geom Row Shape shape InBox extend atJet OnFactor)
open Final50Price (Messages activeFitsPrice ActiveFits SmallFactor Fits Holds FatEquations
  ProperCut LayerBudget lowerCap fullCap TrueWeightLE anchorCutoff)
open Final50GeoCover (activeDegree)
open K1_13_1 (anchorLead indexDegree_eq)
open private Final50GeoCover.factor_small Final50GeoCover.lower_of_anchor from ProximityPrize.SubmissionLower.Final50GeoCover
open private index_bounds from ProximityPrize.SubmissionLower.Fast040
open MvPolynomial
open scoped Polynomial BigOperators

/-- All inputs to the owner's index- or width-weighted arithmetic allocation, on a single bank. -/
structure AllocationData (Γ : Finset K) (s : K → K[X]) (E : FatEquations) (top anchorK : ℕ) where
  n:ℕ
  f:Fin n→Row 4
  pieces:Fin n→Finset K
  orders:Fin n→ℕ
  zeros:Finset (Fin n)
  zero_iff : ∀ i,i∈zeros↔orders i=0
  small : ∀ i,SmallFactor (f i)
  different : ∀ i j,i≠j → ¬ Associated (f i) (f j)
  fits:Fits top (fun i => shape (f i))
  active_budget:(∑ i,activeDegree (f i))≤anchorK
  layers:LayerBudget (fun i => shape (f i)) orders
  weightedLayers:KoalaWeightedLayer2428.WeightedLayerBudget (fun i => shape (f i)) orders
  subset : ∀ i,pieces i ⊆ Γ
  on_factor : ∀ i γ,γ ∈ pieces i→OnFactor (f i) (extend (s γ))
  fat : ∀ i γ,γ ∈ pieces i→Holds E (extend (s γ))
  proper : ∀ i,0 < orders i→ProperCut (f i) Γ s (orders i)
  contracted : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active,ActiveFits (f i) active →
    ∀ h, InBox h (sumShape zeros (fun j => shape (f j))) →
      (pieces i).card≤contractedPrice (shape (f i)) h l active

/-- Numeric tables discharge this callback. The budget excludes the separately booked points. -/
def Allocation (budget anchorK : ℕ) : Prop :=
  ∀ {w Γ s}, Messages w Γ s → ∀ top, top ≤ 14 → ∀ E,
    ∀ d:AllocationData Γ s E top anchorK,lowerCap top+(∑ i,(d.pieces i).card)≤budget

/-- Direct replacement for Final50Geo.count_of_data with the contracted price and the original
    proper cut both available to the same numerical allocation. -/
theorem count_of_data {budget anchorK : ℕ} (allocate : Allocation budget anchorK)
    {w:I→K} {Γ:Finset K} {s:K→K[X]} (hm:Messages w Γ s)
    (bank:Bank Γ s) (rank:bank.Ranked)
    (hjets : ∀ T P,bank.row T P→PrimaryTaper.JetsBounded P) (P:Row 4) (hP:P≠0)
    (hbox:InBox (shape P) (fullCap 14)) (hw:TrueWeightLE P anchorCutoff)
    (ha:ActiveFits P anchorK) (hz : ∀ γ∈Γ,atJet P (extend (s γ))=0)
    (lower : ∀ top≤14,Final50Price.c5 top)
    (book:Finset K) (E:FatEquations) (booked:book.card≤140000)
    (hE : ∀ γ∈Γ,γ∉book→Holds E (extend (s γ))):Γ.card≤140000+budget:=by
  classical
  obtain ⟨n,f,factors,different,prodDvd,covers⟩:=anchor_factors hP
  let top:=(shape P).t
  have htop:top≤14:=hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := Final50GeoCover.factor_small hP hbox hw
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
      change (∑ i,(f i).degreeOf 3)≤P.degreeOf 3
      simpa only [weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ anchorK :=
    (sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ) Finset.univ f hP prodDvd).trans
      ((Final50GeoCover.activeFits_iff P anchorK).mp ha)
  let orders i:=bank.availability (f i)
  let z:=Finset.univ.filter fun i => orders i=0
  have hzero (i):i∈z↔orders i=0:=by simp [z]
  obtain ⟨low,pieces,lowSub,lowOn,sub,on,off,total⟩ := priority_pieces
    (fun i => (factors i).2.2) s book z (fun γ hγ => covers _ (hz γ hγ))
  have lbound:=lower top htop _ _ _ (hm.mono lowSub) _ (Final50GeoCover.lower_of_anchor P hP hbox hw) lowOn
  have hchar (i):(f i).degreeOf 3 < K1.p:=(small i).2.2.1.2.2.trans_lt (by decide:14<K1.p)
  let data : AllocationData Γ s E top anchorK := {
    n:=n,f:=f,pieces:=pieces,orders:=orders,zeros:=z,zero_iff:=hzero
    small:=small,different:=different,fits:=fits,active_budget:=active
    layers:=bank.layer_budget rank f (fun i => (factors i).1) different
    weightedLayers := KoalaWeightedLayer2428.bank_budget bank rank hjets f
      (fun i => (factors i).1) different
    subset:=sub
    on_factor:=fun i γ h => (on i γ h).2
    fat:=fun i γ h => hE γ (sub i h) (on i γ h).1
    proper:=fun i hp => bank.proper_cut (small i) (hchar i) hp le_rfl
    contracted := by
      intro i hi l hp hl K hK h hfloor
      apply bank.companion_price_floor hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) h
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
  }
  have counts:=allocate hm top htop E data
  change lowerCap top+(∑ i,(pieces i).card)≤budget at counts
  exact total.trans (by omega)

#print axioms count_of_data
end
end KoalaRetainedCut
