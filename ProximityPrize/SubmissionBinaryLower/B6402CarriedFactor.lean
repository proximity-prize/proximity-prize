import ProximityPrize.SubmissionBinaryLower.B6402HardFactor

namespace ProximityPrize.SubmissionBinaryLower.B6402CarriedFactor
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A linePow BadOn6402)
open B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402Table4Common
open B6402GridProfile B6402GridRouting B6402IntFarkas B6402QuotBridge B6402BucketBudget B6402HardFactor
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

theorem estimate {u₀ u₁ : I → K} {q : ℕ} (hq : q=1 ∨ q=2) (f : Model u₀ u₁ q)
    (D : KerD45Data) (wD : D.W_F=f.WF) (kD : D.k=f.k) (key : Key) (route : Feasible D key)
    (cl : lo key≤(f.WF:ℚ)/wY) (ch : (f.WF:ℚ)/wY≤hi key)
    (ratio : key.gap.2.2.1≤key.gap.2.2.2) (ordinary : Ordinary key q)
    (S : Finset K) (P : K → K[X]) (Az : K → Finset I)
    (hP : ∀ z∈S,(P z).natDegree≤wY) (hA : ∀ z∈S,A≤(Az z).card)
    (matchP : ∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i)
    (onF : ∀ z∈S,evalContact (evalZContact f.F z) (P z)=0) (badP : ∀ z∈S,BadOn6402 u₀ u₁ (Az z))
    (gap : ∀ z∈S,Upper key f.WF f.k (Az z)) : S.card≤budget key q := by
  obtain ⟨b,ok,g,price⟩ := ordinary
  obtain ⟨hn,x,nn,a0,a1,a2,a3,at',ac,ub,eq⟩ := route
  obtain ⟨hm,hs,hd,deltaPos,denPos,gden,surplus,c1,c2⟩ := B6402RowTransport.table4_surplus_from_bucket D hn
    (rows key) key.cLoNum key.cLoDen key.cHiNum key.cHiDen b ok (wD ▸ cl) (wD ▸ ch) x nn a0 a1 a2 a3 at' ac ub eq
  rw [wD,kD] at surplus
  rcases price with zero|⟨_,_,price,noP64⟩
  · omega
  let w := if q=1 then b.cap1 else b.cap2
  have hc : checkCapWitness 1 b.m b.s key.cHiNum key.cHiDen b.δNum b.δDen b.hiGNum b.hiGDen q w=true := by
    rcases hq with rfl|rfl
    · exact c1
    · exact c2
  have hiN : b.hiGNum=key.gap.2.2.1 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.1) g
  have hiD : b.hiGDen=key.gap.2.2.2 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.2) g
  have p64 (use : w.useP64=true) (z : K) (hz : z∈S) :
      (b.hiGDen:ℤ)*((f.WF:ℤ)-(wY-1:ℕ)-(∑ i∈Az z,(2*(f.k i:ℤ)-1)))≤(b.hiGNum:ℤ)*N := by
    have ne : b.hiGNum≠b.hiGDen := by intro e; have h := noP64 e; change w.useP64=false at h; rw [use] at h; contradiction
    have lt : key.gap.2.2.1<key.gap.2.2.2 := by omega
    have up := gap z hz lt
    unfold gapHi at up
    rw [←hiN,←hiD] at up
    have den : (0:ℚ)<b.hiGDen := by exact_mod_cast gden
    rw [div_mul_eq_mul_div] at up
    have u := (le_div_iff₀ den).mp up
    have gmax : (b.hiGDen:ℤ)*B6401FactorBound.G_val f.WF f.k (Az z)≤(b.hiGNum:ℤ)*N := by
      rw [mul_comm (b.hiGDen:ℤ)]; exact_mod_cast u
    exact (mul_le_mul_of_nonneg_left (B6401FactorBound.sum_2k_sub_1_le_G_val f.WF f.k (Az z))
      (Int.natCast_nonneg _)).trans gmax
  have card := card_le_of_quotient_surplus u₀ u₁ w hc hq le_rfl hs hm hd deltaPos denPos gden (by simpa using f.lower)
    ch f.fc (f.eq ▸ f.lifted) (f.eq ▸ f.slope) (f.eq ▸ f.fw) (f.eq ▸ f.qz) f.k
    (fun i => ⟨f.ord i,fun _ => f.exactOrd i⟩) surplus S P Az hP (f.eq ▸ onF) hA matchP badP (fun h => ⟨rfl,p64 h⟩)
  have hcost : (w.c1Bkt:ℚ)*1811+w.c0Bkt≤budget key q := by exact_mod_cast price
  exact_mod_cast card.trans hcost

#print axioms estimate
end ProximityPrize.SubmissionBinaryLower.B6402CarriedFactor
