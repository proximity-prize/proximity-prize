import ProximityPrize.SubmissionBinaryLower.B6402FactorPlan
import ProximityPrize.SubmissionBinaryLower.B6402HardScalar
import ProximityPrize.SubmissionBinaryLower.B6402CleanFamily

namespace ProximityPrize.SubmissionBinaryLower.B6402ScalarPoint
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A linePow)
open B6401ContactKerD B6401QuotInterp B6402MixedDegree B6402Table4Common
open B6402GridProfile B6402GridRouting B6402SpecialRouting B6402BucketBudget B6402PricedCell
open B6402HardFactor B6402HardAuxiliary B6402OrderProfile B6402CleanFamily B6402IntFarkas
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

private theorem height_le_budget {m B W d q H price : ℕ} {w : CapWitness}
    (h : Binary6402NativeCaps.allowance m B W d q H price w=true) : H≤price := by
  unfold Binary6402NativeCaps.allowance at h
  split at h
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    have a := Nat.mul_le_mul_right H (show 1≤w.Cd+max (4*W/1048575) (4*B)+B+1 by omega)
    rw [one_mul] at a; omega
  · simp only [decide_eq_true_eq] at h
    let den := 1482750-1048575
    let num := 2097152-1048575
    let psi := 1+(2*1048575-1)*(2*B-1)+2*(B-(2*1048575+1))
    have h0 : 1≤2*B-1 := by omega
    have a := Nat.mul_le_mul_right den h0
    rw [one_mul] at a
    have h1 : den≤(2*B-1)*den+num*psi := a.trans (Nat.le_add_right _ _)
    have h2 := Nat.mul_le_mul_right H h1
    have h3 : ((2*B-1)*den+num*psi)*H+num*q*B+q*(2097152-1048575-1)*B*den≤price*den := h.2
    have h4 : den*H≤price*den := by omega
    rw [Nat.mul_comm den H] at h4
    exact Nat.le_of_mul_le_mul_right h4 (by decide : 0<den)

theorem count_at (bank : Bank) (u : I → K) (f : Model u (fun _=>0) 1)
    (fc : KerDIdx wY f.WF 1 → K) (cf : f.fc=fun e => C (fc e)) (wfmax : f.WF≤26689499)
    (D : KerD45Data) (wD : D.W_F=f.WF) (kD : D.k=f.k) (r : Fin 5) (routed : Assigned D r)
    (T : Finset (K[X])) (degrees : ∀ P∈T,P.natDegree≤wY)
    (fits : ∀ P∈T,A≤(Finset.univ.filter fun i : I => P.eval (BinaryIRSProfile.domain i)=u i).card)
    (root : ∀ P∈T,evalContact (∑ e,cC (fc e)*kerDBasisPoly e.1) P=0)
    (seedRoot : ∀ z (P : K[X]),P∈T → evalContact (evalZContact f.F z) P=0) : T.card≤100000 := by
  classical
  obtain ⟨j,gap,lo,hi,feasible⟩ := routed
  let k := Native6402Grid.key j
  rw [wD] at lo hi
  have eqF : (∑ e : KerDIdx wY f.WF 1,cC (C (fc e))*kerDBasisPoly e.1)=f.F := by rw [f.eq,cf]
  have ey (i : I) : linePow u (fun _ => 0) 1 i=C (u i) := by simp [B6402HybridP64.linePow]
  have ord (i : I) : twOrdGE (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (C (u i)) f.fc) (f.k i) := by
    rw [←ey]; exact f.ord i
  have exactOrd (i : I) : ∃ a b,a+b=f.k i ∧ twCoeff (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (C (u i)) f.fc) a b≠0 := by
    rw [←ey]; exact f.exactOrd i
  rcases bank j 1 (Or.inl rfl) with ordinary|repl
  · obtain ⟨b,ok,_,cost⟩ := ordinary
    obtain ⟨hn,x,nn,a0,a1,a2,a3,at',ac,hu,he⟩ := feasible
    obtain ⟨hm,hs,_,dz,dd,_,surplus,_,_⟩ := B6402RowTransport.table4_surplus_from_bucket D hn (rows k)
      k.cLoNum k.cLoDen k.cHiNum k.cHiDen b ok (wD ▸ lo) (wD ▸ hi) x nn a0 a1 a2 a3 at' ac hu he
    rw [wD,kD] at surplus
    rcases cost with zero|⟨bm,bs,_⟩
    · omega
    have positive : (0:ℚ)<(b.δNum:ℚ)/b.δDen := div_pos (by exact_mod_cast dz) (by exact_mod_cast dd)
    have hc := B6402QuotBridge.card_le_of_degZ_zero_surplus u le_rfl hs hm (by simpa using f.lower) fc
      (eqF ▸ f.lifted) (eqF ▸ f.slope) (eqF ▸ f.fw) f.k
      (fun i => ⟨by simpa only [cf,B6402PrimarySystem.localized] using ord i,
        fun _ => by simpa only [cf,B6402PrimarySystem.localized] using exactOrd i⟩)
      (positive.trans surplus) T (fun P h => ⟨degrees P h,fits P h,root P h⟩)
    have t1 := Nat.mul_le_mul_left (2*A) bm
    have t2 := Nat.mul_le_mul bs ((Nat.sub_le f.WF (1*(wY-1))).trans wfmax)
    have t3 : 1*(2*A*b.m-1)+b.s*(f.WF-1*(wY-1))≤2*A*3000+300*26689499 := by omega
    exact hc.trans ((Nat.div_le_div_right t3).trans (by decide))
  · let good := regular f.k BinaryIRSProfile.domain f.F
    let bad := exceptional f.k BinaryIRSProfile.domain f.F
    let H := mixed 1 f.F
    obtain ⟨p,a,cap,paid⟩ := B6402FactorPlan.select (Or.inl rfl) f D wD kD k feasible lo hi (limits j).1 (limits j).2.1 repl
    have gN : good.card≤N := (Finset.card_le_univ _).trans (by rw [BinaryIRSProfile.card_index]; rfl)
    have hh : H≤1812 := (at_most_input 1 f.F).trans (by rw [f.slope]; have h:=f.qz; omega)
    have large : budget k 1≤3200000000000000000 := by unfold budget; split_ifs <;> decide +kernel
    have cost := (height_le_budget cap).trans large
    have room : good.card*H+(p.plan.cap-p.plan.s*H+p.plan.s*H)<Fintype.card K := by
      rw [a.total,show Fintype.card K=2^(192:ℕ) from BF64.card_ext3]
      have hh' := Nat.mul_le_mul gN hh
      exact (Nat.add_le_add hh' cost).trans_lt (by decide)
    have hs := B6402HardScalar.scalar u a.positive_slope a.height a.degree a.ordinate a.layers a.multiplicity
      a.globalCap a.localCap f.k f.fc f.F f.eq f.fw f.lower rfl f.slope f.invariant f.irreducible f.lifted f.degree f.quartic ord exactOrd
      (by simpa only [primaryOrder,mi,B6402ProfileCosts.fee] using paid)
      (by simpa only [B6402SelectedPlan.order_two_card] using a.load) room T
      (fun P => Finset.univ.filter fun i : I => P.eval (BinaryIRSProfile.domain i)=u i) degrees fits
      (fun _ _ i => by simp) seedRoot
    exact hs.trans (a.scalar.trans (by decide))

#print axioms count_at
end ProximityPrize.SubmissionBinaryLower.B6402ScalarPoint
