import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.ZzqFt4d
import ProximityPrize.SubmissionLower.ZqXQOta
import ProximityPrize.SubmissionLower.ZnhmZEa
import ProximityPrize.SubmissionLower.ZiBpxuc
import ProximityPrize.SubmissionLower.ZgLUh9d
import ProximityPrize.SubmissionLower.ZVHUUZd
import ProximityPrize.SubmissionLower.ZQGI7be
import ProximityPrize.SubmissionLower.Z9HmSkb
import ProximityPrize.SubmissionLower.ZS1sWBc
import ProximityPrize.SubmissionLower.Zb3VwYd
import ProximityPrize.SubmissionLower.ZJ86yqc
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.ZIBb1mb
set_option Elab.async false
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2550 12=0x27618291b5e0 :=
  r! 0x34e633d18e0,r! 0x34d3f975100,r! 0x34c1b321e90,r! 0x34af7f0acb0,
  r! 0x349d3f70210,r! 0x348b1121fb0,r! 0x3478d7c2e80,r! 0x3466a2f5a80,
  r! 0x34547c9bcb0,r! 0x34424e0ffb0,r! 0x34302dfd5b0,r! 0x341e05b43f0,
  rfl
private theorem r2 :total 2562 12=0x26be65b184d0 :=
  r! 0x340becc7870,r! 0x33f9c9e5d70,r! 0x33e7b73eb20,r! 0x33d59aa74b0,
  r! 0x33c38e45ec0,r! 0x33b178546c0,r! 0x339f71dffc0,r! 0x338d6238710,
  r! 0x337b6349680,r! 0x336958b3c30,r! 0x3357600bf70,r! 0x33455bc90b0,
  rfl
private theorem r3:total 2574 11=0x22f5b302f440 :=
  r! 0x33335d68160,r! 0x33216c2c520,r! 0x330f736d1f0,r! 0x32fd8877060,
  r! 0x32eb963ea30,r! 0x32d9b163150,r! 0x32c7c581550,r! 0x32b5e7ffd80,
  r! 0x32a40169ac0,r! 0x32922a2f570,r! 0x328049facf0,rfl
theorem agi:total 2550 35=0x71159b462ef0 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qeUg7Fa
set_option maxRecDepth 8192
theorem proof :qwbsesc.c4 := by
  refine ⟨powers,?_⟩
  have s2 :total 2550 70=0xdcd556ffd740 :=
    total_append (q:=2550) (m:=35) (n:=35) agi aec
  have s3 :total 2550 105=0x14360965ef900 :=
    total_append (q:=2550) (m:=70) (n:=35) s2 acE
  have s4 :total 2550 140=0x1a4d9153f3ef0 :=
    total_append (q:=2550) (m:=105) (n:=35) s3 YE
  have s5:total 2550 175=0x20160d899c360 :=
    total_append (q:=2550) (m:=140) (n:=35) s4 apj
  have s6:total 2550 210=0x2591a2b27bc30 :=
    total_append (q:=2550) (m:=175) (n:=35) s5 amH
  have s7:total 2550 245=0x2ac278e09fbc0 :=
    total_append (q:=2550) (m:=210) (n:=35) s6 apk
  have s8:total 2550 280=0x2faabb4195000 :=
    total_append (q:=2550) (m:=245) (n:=35) s7 asc
  have s9:total 2550 315=0x344c985a4bd10 :=
    total_append (q:=2550) (m:=280) (n:=35) s8 rows9
  have s10 :total 2550 350=0x38aa419f88980 :=
    total_append (q:=2550) (m:=315) (n:=35) s9 fZA
  have h:=dyl (q:=2550) (n:=350) (by decide) (by decide)
  rw [s10] at h
  have hn: (0x38aa419f88980:ℤ)≤48*0x12e3a5fb6b7a :=
    Int.ofNat_le.mpr (by decide :0x38aa419f88980≤48*0x12e3a5fb6b7a)
  change 48*(P6_6_2.rankBand powers 2550 2900:ℤ)≤_ at h
  apply Int.ofNat_le.mp
  omega
end qeUg7Fa
end
section
set_option autoImplicit true
namespace P6_6_5
noncomputable section
open P6_6 (Messages)
open oR (ang Rr)
open Finset
open scoped BigOperators
open private Wq from ProximityPrize.SubmissionLower.ZJ86yqc
theorem bv5 {w Γ s} (h:Messages w Γ s) (d:ℕ)
    (bound : ∀ i,(∃ γ∈Γ,(s γ).eval (P6.node i)≠w i) →
      (Γ.filter fun γ=>(s γ).eval (P6.node i)=w i).card≤d) :
    46402*Γ.card≤82317*d+46402 :=
  Wq (A:=179827) (d:=133425) (err :=82317)
    rfl (by decide) (by decide) h.distinct h.degree h.lg d bound
theorem bfL {w Γ s d} (h:Messages w Γ s) (hc:ang w Γ s d) :
    46402*Γ.card≤82317*d+46402 := by
  obtain ⟨persistent,hp,hcap⟩:=hc
  exact bv5 h d fun i ⟨γ,hγ,hmiss⟩=>hcap i (fun hi=>hmiss (hp i hi γ hγ))
theorem bJG {w Γ s} (C:Rr w Γ s) (h:Messages w Γ s) :
    46402*C.CF.card≤82317*C.BJ+46402*C.n:= by
  classical
  calc
    46402*C.CF.card≤46402 * ∑ i,(C.part i).card :=
      Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i,46402*(C.part i).card:= by rw [Finset.mul_sum]
    _ ≤ ∑ i,(82317*C.cap i+46402) :=
      sum_le_sum fun i _=>bfL (h.mono (C.sub i)) (C.localCapacity i)
    _=82317*C.BJ+46402*C.n:= by
      simp [Rr.BJ,sum_add_distrib,Finset.mul_sum,Nat.mul_comm]
end
end P6_6_5
end
section
set_option autoImplicit true
namespace qZqYIua
open P6_6 P6_6_7 q90NBie
open aR (af Shape shape aO)
open dN (GeoJets)

open Dr
open lB (bF)
open private eME from ProximityPrize.SubmissionLower.BI
open private aWr b9i from ProximityPrize.SubmissionLower.J
private theorem residual_chamber (a v :Shape) :bF (residualBody a v) := by
  apply nZ.Jg
  let p:=rawResidual a v
  let j:=min p.j (3*p.b)
  change 3*min p.t (min p.b (j/3))≤j
  have ht:=(min_le_right p.t (min p.b (j/3))).trans (min_le_right p.b (j/3))
  omega
private theorem join_chamber {a b:Shape} (ha :bF a) (hb:bF b) :
    bF (joinBody a b) := by
  refine ⟨max_le_max ha.1 hb.1,?_⟩
  rcases le_total a.t b.t with h | h
  · rw [show (joinBody a b).t=b.t from max_eq_right h]
    exact hb.2.trans (le_max_right _ _)
  · rw [show (joinBody a b).t=a.t from max_eq_left h]
    exact ha.2.trans (le_max_left _ _)
theorem body_chambers {C:Context} {R G ell cs} (hp:PairInput C R G ell cs)
    {h:Shape} (hh:h=chartBody C R cs∨h=weightedChart bf (chartBody C R cs)) :
    bF (cutterBody C ell)∧bF (commonBody C R ell cs)∧ChamberBox h:= by
  let p:=chartBody C R cs
  have hchart:bF p:= by
    cases cs with
    | union l=>exact residual_chamber m6 C.v
    | own i=>exact lB.Tn R
  have hp0:0<p.t:= by
    obtain ⟨i,hi⟩: (chartIndices C cs).Nonempty := by
      cases cs with
      | own i=>exact ⟨i,Finset.mem_singleton_self _⟩
      | union l =>
        obtain ⟨γ,hγ⟩:=C.nonempty
        obtain ⟨i,hi,_⟩:=C.marks.Eh γ hγ
        exact ⟨i,hi⟩
    exact ((C.marks.factors i (P6_6_7_3.charter hp hi)).2.1).trans_le
      ((P6_6_7_3.bW2 hp).2 i hi).2.2
  have hq' : bF (cutterBody C ell) :=residual_chamber Wk (C.v.scale ell)
  have hR:bF (firstBody C R cs) := by
    cases cs with
    | union l=>exact residual_chamber Wk (C.v.scale l)
    | own i=>exact lB.Tn R
  refine ⟨hq',join_chamber hR hq',?_⟩
  rcases hh with rfl | rfl
  · exact ⟨hchart.1,hchart.2,hp0⟩
  · change ChamberBox (weightedChart bf p)
    unfold weightedChart
    split
    · let j:=3+(bf-4)*(p.j - 2)
      change j≤ max _ j∧3*min (bf-3) (j/3)≤j ∧
        0< min (bf-3) (j/3)
      have hj:3≤j:=Nat.le_add_right _ _
      have hm:=min_le_right (bf-3) (j/3)
      exact ⟨le_max_right _ _,by omega,
        lt_min (by decide) (Nat.div_pos hj (by decide))⟩
    · exact aGY _ _ (by decide)
theorem first_fits {C:Context} {R G ell cs} (hp:PairInput C R G ell cs) :
    aO (shape R) (firstSlot C R cs) := by
  cases cs with
  | union l=>exact ⟨le_rfl,le_rfl,le_rfl⟩
  | own i=>exact akM.a1n R
theorem common_fits {C:Context} {R:af 4} {ell cs} :
    aO (cutterBody C ell) (commonBody C R ell cs) :=
  ⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩
theorem retain_cycle (J:Ideal GeoJets) (boxes :List Shape)
    (hboxes : ∀ q∈boxes,bF q) (hsmall:boxes.length≤2)
    (hdim:dimension J≤boxes.length)
    (S:Finset (Ideal GeoJets)) (hS : ∀ P∈S,J.IsMinimalPrime P) :
    (∑ P∈S,(AN J P:ℚ)*tW P boxes)≤tW J boxes := by
  classical
  have hcycle :=bar.proof J boxes.length hdim
  have hb:ChamberBox ⟨3, 3,1⟩:=⟨by decide,by decide,by decide⟩
  have heq :tW J boxes =
      ∑ P∈J.minimalPrimesFinset,(AN J P:ℚ)*tW P boxes := by
    unfold tW
    rw [aWr hcycle hboxes hb,eME,Finset.sum_div]
    simp only [mul_div_assoc]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg (fun P hP=>Ideal.mem_minimalPrimesFinset.mpr (hS P hP))
  intro P hP _
  have hmin:=Ideal.mem_minimalPrimesFinset.mp hP
  exact mul_nonneg (Nat.cast_nonneg _)
    (b9i bav.proof hmin.isPrime hboxes hsmall
      ((MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hmin.le).trans hdim))
end qZqYIua
end
