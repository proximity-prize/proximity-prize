import ProximityPrize.SubmissionLower.RecoveryCore01
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
section InitialGeometry
namespace Lower80899.CUK
open RCN130 RCN238 RCN275


end Lower80899.CUK
namespace Lower80899.FCR

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open Selection DY KZ

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4



def initialAMap (u0 u1:I→K):Caps.AKernel u0 u1→ₗ[K] P4:=
  LZ (K:=K) 24285490 131071 104142 40 134
    IRSProfile.domain u0 u1

def ADN (u0 u1:I→K) (H:P4):
    Finset (RegularIndex H):=
  AKV H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem DXO
    (u0 u1:I→K) (H:P4) (F:RegularIndex H):
    F ∈ ADN u0 u1 H ↔
      ∀v:Caps.AKernel u0 u1,
        F.1 ∣ reconstruct K 24285490 131071 104142 40 v.1:=by
  simp only [ADN,ASD,Finset.mem_univ,
    true_and,initialAMap,SE]













end
end Lower80899.FCR

namespace Lower80899.Initial
open RCN095 RCN260 DY Lower80899.FCR Lower80899.FactorSwitch
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end Lower80899.Initial

end InitialGeometry
end MergedPart0
section MergedPart1
namespace Lower80899.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open UA NG ADZ ABE GB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
local instance:StrongNormalizationMonoid P4:=UniqueFactorizationMonoid.strongNormalizationMonoid

structure Input (u0 u1:I→K) (selected:K→Polynomial K) (Gamma:Finset K):Prop where
  degree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071
  agreement: ∀gamma ∈ Gamma,181235≤((Finset.univ:Finset I).filter (fun i=>
    (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card
  noPencil:BL selected Gamma 131071 80909

variable {u0 u1:I→K} {selected:K→Polynomial K} {Gamma:Finset K}

theorem Input.restrict (inp:Input u0 u1 selected Gamma) (Delta:Finset K) (h:Delta ⊆ Gamma):
    Input u0 u1 selected Delta:=
  ⟨fun g hg=>inp.degree g (h hg),fun g hg=>inp.agreement g (h hg),
    KX selected Gamma Delta 131071 80909 h inp.noPencil⟩

def BBJ:GH:=⟨262144,131071,181235,30085010,17230,1⟩

theorem DZK (inp:Input u0 u1 selected Gamma)
    (J:P4) (hJ:J ≠ 0) (hbox:J ∈ RCN174.BA K 30085010 131071 17230 1)
    (hR:J.degreeOf 2=0) (hsol: ∀g ∈ Gamma,BM K (selected g) g J=0):
    Gamma.card≤8110000000000+0:=by
  have h:=FHV BBJ J hJ 2130706433 hbox hR (by rfl)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (by norm_num [BBJ,GH.kappa])
    (by norm_num [BBJ,GH.algebraicCap,GH.kappa])
    (by norm_num [BBJ,GH.implicitYCap,GH.kappa])
    (by norm_num [BBJ,GH.algebraicCap,GH.kappa])
    (by norm_num [BBJ,GH.implicitYCap,GH.algebraicCap,GH.kappa])
    (by decide+kernel) (by decide+kernel) selected Gamma Finset.univ IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn (by rw [Finset.card_univ];exact Fintype.card_fin _)
    inp.degree hsol inp.agreement (by
      simpa only [BBJ,GH.errors,(show (262144-181235:ℕ)=80909 by decide+kernel)] using inp.noPencil)
  have ht:BBJ.countCap≤8110000000000+0:=by
    norm_num [BBJ,GH.countCap,GH.gap,
      GH.errors,GH.kappa,GH.algebraicCap,
      GH.implicitYCap,GH.CRI,
      GH.COO,GH.agreement,
      GH.DUN,RCN294.dot]
  exact h.trans ht

theorem FQY (inp:Input u0 u1 selected Gamma)
    (F:P4) (hF:F ≠ 0) (hbox:F ∈ RCN174.BA K 30085010 131071 17230 50):
    (tailSeeds F selected Gamma).card≤8110000000000+0:=by
  have hsmall:F.degreeOf 2<2130706433:=
    (UY F 30085010 131071 17230 50 hbox).trans_lt (by decide+kernel)
  have hJ:=dR_ne_zero F hF 2130706433 hsmall (chainLength F) le_rfl
  have hb:=EUD (dR (chainLength F) F) 30085010 131071 17230 50
    (dR_mem_box _ F 30085010 131071 17230 50 hbox) (EDK F)
  exact DZK (inp.restrict _ (GCE F selected Gamma)) _ hJ hb
    (EDK F) (fun _ hg=>(Finset.mem_filter.mp hg).2)

theorem FJZ (inp:Input u0 u1 selected Gamma)
    (Q:P4) (hQ:Q ≠ 0) (hbox:Q ∈ RCN174.BA K 30085010 131071 17230 50):
    (rfreeSeeds Q selected Gamma).card≤8110000000000+0:=by
  have hb:=EUD (rfreeProduct Q) 30085010 131071 17230 50
    (QS _ Q 30085010 131071 17230 50 hQ
      (EZM Q hQ) hbox) (DWN Q)
  exact DZK (inp.restrict _ (FXI Q selected Gamma)) _
    (FEQ Q hQ) hb (DWN Q)
    (fun _ hg=>(Finset.mem_filter.mp hg).2)

end
end Lower80899.Counting

namespace Lower80899.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 KZ
open DY MM FV Counting NG ADZ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _

theorem degreeY_le (F:P4):F.degreeOf 1≤wt BC F:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BC hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0≤wt BC F at h
  omega

theorem degreeZ_le (F:P4):F.degreeOf 3≤wt AT F:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree AT hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1≤wt AT F at h
  omega

theorem DNC (H:P4) (A:Finset (RegularIndex H)) (F:RegularIndex H) (hF:F ∈ A):
    F.1.degreeOf 1≤middle (BF H A)∧
    F.1.degreeOf 2≤(BF H A).all∧
    F.1.degreeOf 3≤total (BF H A):=by
  have hm:=LY H (Finset.singleton_subset_iff.mpr hF)
  have hc:=GX F.1
  have hy:F.1.degreeOf 1≤middle (BG H F):=by
    rw [BG,middle,hc.2.1]
    exact degreeY_le F.1
  have hz:F.1.degreeOf 3≤total (BG H F):=by
    rw [BG,total,hc.2.2]
    exact degreeZ_le F.1
  have hr:F.1.degreeOf 2=(BG H F).all:=by
    rw [BG,ARS]
  simpa only [BF,sumFlag,Finset.sum_singleton] using
    And.intro (hy.trans hm.2.1) (And.intro (hr.le.trans hm.1) (hz.trans hm.2.2))

theorem COU (H Q:P4) (hH:H ≠ 0) (hQ:Q ≠ 0) (weights:Fin 4→ℕ):
    wt weights (CK H Finset.univ)+wt weights (CK Q Finset.univ)≤
      wt weights (H*Q):=by
  simp only [wt]
  rw [UP weights H Q hH hQ]
  exact Nat.add_le_add
    (IQ weights _ H (ZQ H _) hH)
    (IQ weights _ Q (ZQ Q _) hQ)

theorem FIF (H Q:P4) (hH:H ≠ 0) (hQ:Q ≠ 0)
    (hbox:H*Q ∈ RCN100.BA K 30085010 131071 17230 50):
    (BF H Finset.univ).all+(BF Q Finset.univ).all≤50∧
    middle (BF H Finset.univ)+middle (BF Q Finset.univ)≤229∧
    total (BF H Finset.univ)+total (BF Q Finset.univ)≤17230:=by
  have hc:=(JT (H*Q) 30085010 131071 17230 50 (by decide+kernel)).mp hbox
  have hw:=XV (H*Q) 131071 (by decide+kernel)
  have hy:wt BC (H*Q)≤229:=by omega
  rw [JM,JM,
    IF,IF,
    KH,KH]
  exact ⟨(COU H Q hH hQ _).trans hc.2.1,
    (COU H Q hH hQ _).trans hy,
    (COU H Q hH hQ _).trans hc.1⟩

theorem GFL (H:P4) (U:Finset (RegularIndex H)):
    let N:=(Finset.univ:Finset (RegularIndex H)) \ U
    (BF H U).all+(BF H N).all=(BF H Finset.univ).all∧
    middle (BF H U)+middle (BF H N)=middle (BF H Finset.univ)∧
    total (BF H U)+total (BF H N)=total (BF H Finset.univ):=by
  simp only [BF,sumFlag_all,AQT,AXF]
  exact ⟨by rw [Nat.add_comm];exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm];exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm];exact Finset.sum_sdiff (Finset.subset_univ _)⟩

end
end Lower80899.Budgets
end MergedPart1
section MergedPart2
namespace Lower80899.FoldCounting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open UA NG ADZ ABE GB FAD AFK Counting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
local instance:StrongNormalizationMonoid P4:=UniqueFactorizationMonoid.strongNormalizationMonoid

variable {u0 u1:I→K} {selected:K→Polynomial K} {Gamma:Finset K}

def factorCharge' (F:P4) (selected:K→Polynomial K) (Gamma:Finset K):ℕ:=
  (foldSeeds F selected Gamma).card+(tailSeeds F selected Gamma).card

theorem factorCharge'_le_unit' (inp:Input u0 u1 selected Gamma)
    (F:P4) (hF:Irreducible F) (hpos:0<F.degreeOf 2)
    (hbox:F ∈ RCN174.BA K 30085010 131071 17230 50)
    (y z r:ℕ) (hy:y≤229) (hz:z≤17230) (hr:r≤50)
    (hFY:F.degreeOf 1≤y) (hFZ:F.degreeOf 3≤z) (hFR:F.degreeOf 2≤r):
    factorCharge' F selected Gamma≤F.degreeOf 2*(foldUnit y z r+0):=by
  have htail:=FQY inp F hF.ne_zero hbox
  have hT:=GEI y z r
  by_cases h1:F.degreeOf 2=1
  · rw [factorCharge',DKY F h1,Finset.card_empty,h1]
    omega
  have hd:2≤F.degreeOf 2:=by omega
  have hd40:F.degreeOf 2≤50:=hFR.trans hr
  have hleft:F.degreeOf 2-1≤50:=by omega
  have hfold:=EVR (stage y z (F.degreeOf 2) 1) F hF 2130706433
    hpos (hd40.trans_lt (by decide+kernel))
    hFY (by dsimp [stage];omega) hFZ hFY (by dsimp [stage];omega) hFZ
    (by dsimp [stage];omega)
    ((hy.trans_lt (by decide+kernel):y<2130706433))
    ((hd40.trans_lt (by decide+kernel):F.degreeOf 2<2130706433))
    ((hz.trans_lt (by decide+kernel):z<2130706433))
    (by
      dsimp [stage,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hleft hz) (Nat.mul_le_mul hz hd40)).trans_lt
        (by decide+kernel))
    (by
      dsimp [stage,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hy hz) (Nat.mul_le_mul hz hy)).trans_lt
        (by decide+kernel))
    (by
      dsimp [stage,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hy hd40) (Nat.mul_le_mul hleft hy)).trans_lt
        (by decide+kernel))
    selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by rw [Finset.card_univ];exact Fintype.card_fin _)
    (by norm_num [stage]) (by norm_num [stage]) (by norm_num [stage]) (by norm_num [stage])
    inp.degree inp.agreement
    (by simpa only [stage,DG.errors,
      (show (262144-181235:ℕ)=80909 by decide+kernel)] using inp.noPencil)
  have hgap:(stage y z (F.degreeOf 2) 1).gap=50164:=by
    simp [stage,DG.gap]
  have hdot:dot ⟨(stage y z (F.degreeOf 2) 1).leftY,(stage y z (F.degreeOf 2) 1).leftR,
      (stage y z (F.degreeOf 2) 1).leftZ⟩ (stage y z (F.degreeOf 2) 1).mixedCost=
        y*z*(6*F.degreeOf 2-4):=stageDot y z (F.degreeOf 2) (by omega)
  rw [hgap,hdot] at hfold
  have hnum:=FAS y z (F.degreeOf 2) r hd hFR
  unfold AAF at hnum
  have hs:0≤F.degreeOf 2*0:=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmul:factorCharge' F selected Gamma*50164≤
      F.degreeOf 2*(foldUnit y z r+0)*50164:=by
    unfold factorCharge'
    nlinarith
  exact Nat.le_of_mul_le_mul_right hmul (by decide)

end
end Lower80899.FoldCounting

namespace Lower80899.FoldBudgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 KZ
open DY MM FV Counting Budgets NG AFK FoldCounting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _

theorem joint_charge' (H Q:P4) (hH:H ≠ 0) (hQ:Q ≠ 0)
    (hbox:H*Q ∈ RCN100.BA K 30085010 131071 17230 50)
    (hHbox:H ∈ RCN174.BA K 30085010 131071 17230 50)
    (hQbox:Q ∈ RCN174.BA K 30085010 131071 17230 50)
    (U:Finset (RegularIndex H)) (u0 u1:I→K) (selected:K→Polynomial K)
    (Gamma Delta:Finset K) (inpH:Input u0 u1 selected Gamma) (inpQ:Input u0 u1 selected Delta)
    (hr:(BF H U).all≤40)
    (hy:middle (BF H U)≤181)
    (ht:total (BF H U)≤11784):
    let p:=BF H U
    (∑ F:RegularIndex H,factorCharge' F.1 selected Gamma)+
      (∑ F:RegularIndex Q,factorCharge' F.1 selected Delta)≤
      p.all*foldUnit (middle p) (total p) p.all+
      (50-p.all)*foldUnit (229-middle p) (17230-total p) (50-p.all)+50*0:=by
  let p:=BF H U
  let N:=(Finset.univ:Finset (RegularIndex H)) \ U
  have hb:=FIF H Q hH hQ hbox
  have hs:=GFL H U
  have hnR:(BF H N).all≤50-p.all:=by dsimp only [p,N];omega
  have hnY:middle (BF H N)≤229-middle p:=by dsimp only [p,N];omega
  have hnT:total (BF H N)≤17230-total p:=by dsimp only [p,N];omega
  have hqR:(BF Q Finset.univ).all≤50-p.all:=by dsimp only [p];omega
  have hqY:middle (BF Q Finset.univ)≤229-middle p:=by dsimp only [p];omega
  have hqT:total (BF Q Finset.univ)≤17230-total p:=by dsimp only [p];omega
  have hsum:(∑ F ∈ U,F.1.degreeOf 2)=p.all:=by
    simp only [p,BF,sumFlag_all,BG,ARS]
  have hprodBox:=RCN101.DZF K 30085010 131071 17230 50 (H*Q) hbox
  have hc:=FND (Finset.univ:Finset (RegularIndex H)) U
    (Finset.univ:Finset (RegularIndex Q)) (Finset.subset_univ _) (fun F=>F.1) (fun F=>F.1)
    H Q hH hQ (ZQ H _) (ZQ Q _)
    50 (foldUnit (middle p) (total p) p.all+0)
    (foldUnit (229-middle p) (17230-total p) (50-p.all)+0)
    (UY (H*Q) 30085010 131071 17230 50 hprodBox)
    (fun F=>factorCharge' F.1 selected Gamma) (fun F=>factorCharge' F.1 selected Delta)
    (fun F hF=>by
      have hf:=ALY H F.1 hH 30085010 131071 17230 50 hHbox F.2
      have hd:=DNC H U F hF
      exact factorCharge'_le_unit' inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (hy.trans (by decide+kernel)) (ht.trans (by decide+kernel))
        (hr.trans (by decide+kernel)) hd.1 hd.2.2 hd.2.1)
    (fun F hF=>by
      have hf:=ALY H F.1 hH 30085010 131071 17230 50 hHbox F.2
      have hd:=DNC H N F hF
      exact factorCharge'_le_unit' inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hnY) (hd.2.2.trans hnT) (hd.2.1.trans hnR))
    (fun F _=>by
      have hf:=ALY Q F.1 hQ 30085010 131071 17230 50 hQbox F.2
      have hd:=DNC Q Finset.univ F (Finset.mem_univ _)
      exact factorCharge'_le_unit' inpQ F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hqY) (hd.2.2.trans hqT) (hd.2.1.trans hqR))
  rw [hsum] at hc
  have hp:p.all+(50-p.all)=50:=by dsimp only [p];omega
  calc
    _≤_:=hc
    _=p.all*foldUnit (middle p) (total p) p.all+
        (50-p.all)*foldUnit (229-middle p) (17230-total p) (50-p.all)+
          (p.all+(50-p.all))*0:=by ring
    _=_:=by rw [hp]

end
end Lower80899.FoldBudgets

namespace Lower80899.FoldGeometry
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open UA Counting NG FAD FoldCounting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=UniqueFactorizationMonoid.strongNormalizationMonoid

theorem cover_count' (Q T:P4) (hQ:Q ≠ 0)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hQsolution: ∀g ∈ Gamma,BM K (selected g) g Q=0)
    (hTsolution: ∀g ∈ Gamma,BM K (selected g) g T=0):
    Gamma.card≤(∑ F:RegularIndex Q,(NQ Q T selected Gamma F).card)+
      (∑ F:RegularIndex Q,factorCharge' F.1 selected Gamma)+
      (rfreeSeeds Q selected Gamma).card:=by
  have hcover:=cover_fold Q T hQ selected Gamma hQsolution hTsolution
  have hB:((FW Q).biUnion fun F=>foldSeeds F selected Gamma).card≤
      ∑ F ∈ FW Q,(foldSeeds F selected Gamma).card:=Finset.card_biUnion_le
  have hC:((FW Q).biUnion fun F=>tailSeeds F selected Gamma).card≤
      ∑ F ∈ FW Q,(tailSeeds F selected Gamma).card:=Finset.card_biUnion_le
  have hA:=Finset.card_biUnion_le (s:=(Finset.univ:Finset (RegularIndex Q)))
    (t:=fun F=>NQ Q T selected Gamma F)
  have hcard:=Finset.card_le_card hcover
  have h1:=Finset.card_union_le
    ((Finset.univ.biUnion fun F:RegularIndex Q=>NQ Q T selected Gamma F) ∪
      ((FW Q).biUnion fun F=>foldSeeds F selected Gamma) ∪
      ((FW Q).biUnion fun F=>tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2:=Finset.card_union_le
    ((Finset.univ.biUnion fun F:RegularIndex Q=>NQ Q T selected Gamma F) ∪
      ((FW Q).biUnion fun F=>foldSeeds F selected Gamma))
    ((FW Q).biUnion fun F=>tailSeeds F selected Gamma)
  have h3:=Finset.card_union_le
    (Finset.univ.biUnion fun F:RegularIndex Q=>NQ Q T selected Gamma F)
    ((FW Q).biUnion fun F=>foldSeeds F selected Gamma)
  have he:(∑ F:RegularIndex Q,factorCharge' F.1 selected Gamma)=
      (∑ F ∈ FW Q,(foldSeeds F selected Gamma).card)+
      (∑ F ∈ FW Q,(tailSeeds F selected Gamma).card):=by
    rw [← Finset.sum_subtype (FW Q) (fun _=>Iff.rfl)
      (f:=fun F=>factorCharge' F selected Gamma)]
    simp only [factorCharge',Finset.sum_add_distrib]
  omega

end
end Lower80899.FoldGeometry
end MergedPart2

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace Lower80899.Geometry
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open UA Counting NG
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
local instance:StrongNormalizationMonoid P4:=UniqueFactorizationMonoid.strongNormalizationMonoid

end
end Lower80899.Geometry

namespace Lower80899.PairCell
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN156 RCN167 RCN180 RCN234 RCN260 RCN294
open DY KZ MM
open Counting NG ABE GB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ

theorem degreeR_le (F:P4):F.degreeOf 2≤wt BE F:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree BE hd
  rw [weight_fin4] at h
  change d 0*0+d 1*0+d 2*1+d 3*0≤wt BE F at h
  omega

theorem DTL (H G:P4) (hH:H ≠ 0) (hG:G ≠ 0)
    (U:Finset (RCN266.RegularIndex H)) (weights:Fin 4→ℕ):
    wt weights (CK H U)+wt weights G≤wt weights (H*G):=by
  simp only [wt]
  rw [UP weights H G hH hG]
  exact Nat.add_le_add_right
    (IQ weights _ H (ZQ H U) hH) _

theorem DLY (H G:P4) (hH:H ≠ 0) (hG:G ≠ 0)
    (U:Finset (RCN266.RegularIndex H)) (D w L s:ℕ) (hD:0<D) (hw:1≤w)
    (hbox:H*G ∈ RCN100.BA K D w L s):
    G.degreeOf 1≤(D-1+s)/w-middle (BF H U)∧
    G.degreeOf 2≤s-(BF H U).all∧
    G.degreeOf 3≤L-total (BF H U):=by
  have hc:=(JT (H*G) D w L s hD).mp hbox
  have hyw:=XV (H*G) w hw
  have hy:wt BC (H*G)≤(D-1+s)/w:=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm];omega)
  have e1:=DTL H G hH hG U BC
  have e2:=DTL H G hH hG U BE
  have e3:=DTL H G hH hG U AT
  rw [← IF] at e1
  rw [← JM] at e2
  rw [← KH] at e3
  have d1:=Budgets.degreeY_le G
  have d2:=degreeR_le G
  have d3:=Budgets.degreeZ_le G
  omega

theorem GIL {u0 u1:I→K} {selected:K→Polynomial K} {Gamma:Finset K}
    (inp:Input u0 u1 selected Gamma) (H Q T:P4) (hH:H ≠ 0) (hQ:Q ≠ 0) (hT:T ≠ 0)
    (hrel:IsRelPrime Q T)
    (hQbox:H*Q ∈ RCN100.BA K 30085010 131071 17230 50)
    (hTbox:H*T ∈ RCN100.BA K 45671220 131071 11785 78)
    (U:Finset (RCN266.RegularIndex H)) (hr:(BF H U).all<50):
    (∑ F:RCN052.RegularIndex Q,(NQ Q T selected Gamma F).card)≤
      PairCell6815.cap (BF H U).all (middle (BF H U))
        (total (BF H U)):=by
  obtain ⟨qY,qR,qZ⟩:=DLY H Q hH hQ U 30085010 131071 17230 50
    (by norm_num) (by norm_num) hQbox
  obtain ⟨tY,tR,tZ⟩:=DLY H T hH hT U 45671220 131071 11785 78
    (by norm_num) (by norm_num) hTbox
  norm_num only at qY tY
  let P:=PairCell6815.parameters (BF H U).all
    (middle (BF H U)) (total (BF H U))
  have hly:229-middle (BF H U)≤229:=Nat.sub_le _ _
  have hlr:50-(BF H U).all≤50:=Nat.sub_le _ _
  have hlz:17230-total (BF H U)≤17230:=Nat.sub_le _ _
  have hry:348-middle (BF H U)≤348:=Nat.sub_le _ _
  have hrr:78-(BF H U).all≤78:=Nat.sub_le _ _
  have hrz:11785-total (BF H U)≤11785:=Nat.sub_le _ _
  have hcount (F:RCN052.RegularIndex Q):=CKD P Q T hrel F 2130706433
    ((OI 1 F.1 Q (KR _ _ F.2).2.1 hQ).trans qY)
    ((OI 2 F.1 Q (KR _ _ F.2).2.1 hQ).trans qR)
    ((OI 3 F.1 Q (KR _ _ F.2).2.1 hQ).trans qZ)
    tY tR tZ (by dsimp only [P,PairCell6815.parameters];omega)
    (by dsimp only [P,PairCell6815.parameters];omega)
    (by dsimp only [P,PairCell6815.parameters];omega)
    (by dsimp only [P,PairCell6815.parameters];omega)
    (by
      dsimp only [P,PairCell6815.parameters,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hlr hrz) (Nat.mul_le_mul hlz hrr)).trans_lt
        (by norm_num))
    (by
      dsimp only [P,PairCell6815.parameters,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hly hrz) (Nat.mul_le_mul hlz hry)).trans_lt
        (by norm_num))
    (by
      dsimp only [P,PairCell6815.parameters,DG.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hly hrr) (Nat.mul_le_mul hlr hry)).trans_lt
        (by norm_num))
    selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by rw [Finset.card_univ];exact Fintype.card_fin _)
    (by norm_num [P,PairCell6815.parameters]) (by norm_num [P,PairCell6815.parameters])
    (by norm_num [P,PairCell6815.parameters]) (by norm_num [P,PairCell6815.parameters])
    inp.degree inp.agreement
    (by simpa only [P,PairCell6815.parameters,DG.errors,
      (show (262144-181235:ℕ)=80909 by decide+kernel)] using inp.noPencil)
  have hsum:=DVN P Q T selected Gamma
    (DYI P Q hQ qY qR qZ) hcount
  exact (Nat.le_div_iff_mul_le (by norm_num [P,PairCell6815.parameters,DG.gap])).mpr hsum

end
end Lower80899.PairCell

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace QQ
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN095 RCN100 RCN140 RCN156 RCN167 RCN180 RCN234 RCN266
open DY KZ MM
open Lower80899 Lower80899.PairCell
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
def cap (r y t:ℕ):ℕ:=if r<50 then PairCell6815.cap r y t else 0

theorem pair_count {u0 u1:I→K} {selected:K→Polynomial K} {Gamma:Finset K}
    (inp:Counting.Input u0 u1 selected Gamma) (H Q T:P4)
    (hH:H≠0) (hQ:Q≠0) (hT:T≠0) (hrel:IsRelPrime Q T)
    (hQbox:H*Q∈RCN100.BA K 30085010 131071 17230 50)
    (hTbox:H*T∈RCN100.BA K 45671220 131071 11785 78)
    (U:Finset (RCN266.RegularIndex H)):
    (∑ F:RCN052.RegularIndex Q,(NQ Q T selected Gamma F).card)≤
      cap (BF H U).all (middle (BF H U))
        (total (BF H U)):=by
  by_cases hr:(BF H U).all<50
  · simpa only [cap,if_pos hr] using GIL inp H Q T hH hQ hT hrel hQbox hTbox U hr
  · have hq:=(DLY H Q hH hQ U 30085010 131071 17230 50
      (by decide) (by decide) hQbox).2.1
    have hz:Q.degreeOf 2=0:=by omega
    have hempty:IsEmpty (RCN052.RegularIndex Q):=by
      refine ⟨fun F=> ?_⟩
      obtain ⟨_,hd,hpos⟩:=RCN167.KR Q F.val F.property
      have hle:=RCN081.OI 2 F.val Q hd hQ
      omega
    letI:=hempty
    simp [cap,hr]

end
end QQ

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace CY
open scoped BigOperators
open RCN260 GB
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

def num (L U S r y t:ℕ):ℕ:=
  KP (PI.pair L U S r y t)
def cost (L U S r y t:ℕ):ℕ:=
  FU (PI.pair L U S r y t)

theorem num_formula (L U S r y t:ℕ):
    num L U S r y t=
      131073*((1+2*131071*y)*(r*L+t*S)+131071*(2*r-1)*(y*L+t*U)+
        (1+2*131071*t)*(y*S+r*U))+80910*50164*(y*S+r*U):=by
  simp only [num,KP,PI.pair,
    DG.errors,DG.gap,DG.KO,
    DG.mixedCost,RCN294.dot]
  norm_num only [Nat.reduceSub,Nat.reduceAdd,Nat.reduceMul]
  ring

theorem cost_eq (L U S r y t:ℕ):cost L U S r y t=num L U S r y t/50164:=by
  simp only [cost,num,FU,PI.pair,DG.gap,Nat.reduceSub]

theorem num_mono (L U S r y t capR capY capT:ℕ) (hr:r≤capR) (hy:y≤capY) (ht:t≤capT):
    num L U S r y t≤num L U S capR capY capT:=by
  rw [num_formula,num_formula]
  gcongr

theorem cost_mono (L U S r y t capR capY capT:ℕ) (hr:r≤capR) (hy:y≤capY) (ht:t≤capT):
    cost L U S r y t≤cost L U S capR capY capT:=by
  rw [cost_eq,cost_eq]
  exact Nat.div_le_div_right (num_mono L U S r y t capR capY capT hr hy ht)

theorem sum_num_le {ι:Type*} [DecidableEq ι] (s:Finset ι)
    (L U S:ℕ) (r y t:ι→ℕ):
    (∑ i∈s,num L U S (r i) (y i) (t i))≤
      num L U S (∑ i∈s,r i) (∑ i∈s,y i) (∑ i∈s,t i):=by
  have hterm (i:ι) (hi:i∈s):
      num L U S (r i) (y i) (t i)≤
        131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80910*50164*(y i*S+r i*U):=by
    have hr:=Finset.single_le_sum (fun j (_:j∈s)=>Nat.zero_le (r j)) hi
    have hy:=Finset.single_le_sum (fun j (_:j∈s)=>Nat.zero_le (y j)) hi
    have ht:=Finset.single_le_sum (fun j (_:j∈s)=>Nat.zero_le (t j)) hi
    rw [num_formula]
    gcongr
  calc
    _≤∑ i∈s,(131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80910*50164*(y i*S+r i*U)):=Finset.sum_le_sum hterm
    _=_:=by
      rw [num_formula]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]

theorem sum_cost_le {ι:Type*} [DecidableEq ι] (s:Finset ι)
    (L U S:ℕ) (r y t:ι→ℕ):
    (∑ i∈s,cost L U S (r i) (y i) (t i))≤
      cost L U S (∑ i∈s,r i) (∑ i∈s,y i) (∑ i∈s,t i):=by
  conv_rhs=>rw [cost_eq]
  apply (Nat.le_div_iff_mul_le (by decide:0<50164)).mpr
  calc
    _=∑ i∈s,cost L U S (r i) (y i) (t i)*50164:=by rw [Finset.sum_mul]
    _≤∑ i∈s,num L U S (r i) (y i) (t i):=by
      apply Finset.sum_le_sum
      intro i hi
      rw [cost_eq]
      exact Nat.div_mul_le_self _ _
    _≤_:=sum_num_le s L U S r y t





end CY
end MergedPart0
section MergedPart1
namespace DMK
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem GHN {ι:Type*} [DecidableEq ι]
    (count charge:ι→ℕ) (routeable:Finset ι→Prop) (ambient:Finset ι)
    (hroute: ∀B,B ⊆ ambient→ routeable B→
      ∃U,U ⊂ B∧ ∀i ∈ B \ U,count i≤charge i):
    ∃U,U ⊆ ambient∧ ¬routeable U∧
      ∀i ∈ ambient \ U,count i≤charge i:=by
  classical
  have aux: ∀B:Finset ι,B ⊆ ambient→
      ∃U,U ⊆ B∧ ¬routeable U∧
        ∀i ∈ B \ U,count i≤charge i:=by
    intro B
    induction B using Finset.strongInduction with
    | H B ih=>
      intro hB
      by_cases hr:routeable B
      · obtain ⟨V,hV,hexit⟩:=hroute B hB hr
        obtain ⟨U,hU,hstop,hrest⟩:=ih V hV (hV.subset.trans hB)
        refine ⟨U,hU.trans hV.subset,hstop,?_⟩
        intro i hi
        obtain ⟨hiB,hiU⟩:=Finset.mem_sdiff.mp hi
        by_cases hiV:i ∈ V
        · exact hrest i (Finset.mem_sdiff.mpr ⟨hiV,hiU⟩)
        · exact hexit i (Finset.mem_sdiff.mpr ⟨hiB,hiV⟩)
      · exact ⟨B,Finset.Subset.refl _,hr,by simp⟩
  exact aux ambient (Finset.Subset.refl _)

end DMK
end MergedPart1
section MergedPart2
namespace BND
open scoped BigOperators
open CY DMK
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tSlope (_L U S r y:ℕ):ℕ:=
  131073*((1+2*131071*y)*S+131071*(2*r-1)*U+2*131071*(y*S+r*U))

theorem num_shift (L U S r y z:ℕ):
    num L U S r y (y+z)=num L U S r y y+tSlope L U S r y*z:=by
  rw [num_formula,num_formula]
  unfold tSlope
  ring

end BND
end MergedPart2
section MergedPart3
namespace Lower80899.EAK

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open DY CS KZ Lower80899.AGR Lower80899.FactorSwitch Lower80899.Oracle

open FV (Potential sumFlag sumFlag_all AQT AXF RawBelow AVS)
open MM (BF JM
  IF KH LY
  AAN AML BCO)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

private theorem DJI (s:EA) (p:FlagDegree)
    (hr:1≤p.all) (ht:total p≤s.totalCap)
    (hy:middle p≤s.middleCap) (hs:p.all≤s.slopeCap):
    1≤s.fuel p:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem BHW (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.fuel p*total p≤s.totalCap∧
      s.fuel p*middle p≤s.middleCap∧
      s.fuel p*p.all≤s.slopeCap:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  refine ⟨?_,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem AIN (a b:ℕ) (hb:0<b):
    a-(a/b)*b<b:=by
  have hm:=Nat.mod_lt a hb
  have heq:=Nat.mod_add_div' a b
  omega

private theorem BKF (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.totalCap-s.fuel p*total p<total p∨
      s.middleCap-s.fuel p*middle p<middle p∨
      s.slopeCap-s.fuel p*p.all<p.all:=by
  have hall:0<p.all:=by omega
  have hmiddle:0<middle p:=hall.trans_le (ATD p)
  have htotal:0<total p:=hmiddle.trans_le (AIS p)
  unfold EA.fuel
  by_cases hT:s.totalCap/total p≤
      min (s.middleCap/middle p) (s.slopeCap/p.all)
  · left
    rw [min_eq_left hT]
    exact AIN s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY:s.middleCap/middle p≤s.slopeCap/p.all
    · right;left
      rw [min_eq_left hY]
      exact AIN s.middleCap (middle p) hmiddle
    · right;right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact AIN s.slopeCap p.all hr

theorem EKV
    (sound:YF) (charge:FlagDegree→ℕ)
    (hpay: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤40→middle p≤181→total p≤11784→j≤sound.source.fuel p→
      PowerRoute.stageCost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
        (Oracle.LP p) j≤charge p)
    (D m:ℕ)
    (hweighted:D≤m*181235∧m*50165<D)
    (hshape:D+sound.source.slopeCap≤
      131071*(sound.source.middleCap+1))
    (hslopeM:sound.source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:sound.source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hroute:sound.source.Routeable (BF H A))
    (hnarrowS:(BF H A).all≤40)
    (hnarrowY:middle (BF H A)≤181)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤
        charge (BG H F):=by
  classical
  let p:=BF H A
  have hr:1≤p.all:=hroute.1
  have hA:A.Nonempty:=by
    by_contra hzero
    have hAe:A= ∅ :=Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p,BF,sumFlag] at hr
  have hfuel:1≤sound.source.fuel p:=
    DJI sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP:=BHW sound.source p hr
  have hterminalP:=BKF sound.source p hr
  have hfuelSlope:sound.source.fuel p≤sound.source.slopeCap:=by
    calc
      sound.source.fuel p≤sound.source.slopeCap/p.all:=
        (min_le_right _ _).trans (min_le_right _ _)
      _≤sound.source.slopeCap:=Nat.div_le_self _ _
  have hfuelM:sound.source.fuel p≤m:=hfuelSlope.trans hslopeM
  have hfuelChar:sound.source.fuel p<2130706433:=
    hfuelM.trans_lt hmChar
  have hlowpos: ∀j,1≤j→j≤sound.source.fuel p→
      0<D-j*50165:=by
    intro j hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    rcases hweighted with ⟨hw0,hw1⟩
    omega
  have hcapacity: ∀j,1≤j→j≤sound.source.fuel p→
      D-j*50165≤
        (m-j)*181235+j*(131071-1):=by
    intro j _hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    rcases hweighted with ⟨hw0,hw1⟩
    omega
  have hfield:A.card<ENat.card K:=by
    have hcard:A.card≤p.all:=by
      calc
        A.card= ∑ F ∈ A,1:=by simp
        _≤ ∑ F ∈ A,(BG H F).all:=
          Finset.sum_le_sum (fun F _=>Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (JH H F)))
        _=p.all:=by simp only [p,BF,sumFlag_all]
    calc
      (A.card:ENat)≤(40:ℕ):=by
        exact_mod_cast hcard.trans hnarrowS
      _<ENat.card K:=by
        rw [ENat.card_eq_coe_fintype_card,RCN183.BIS]
        norm_num
  have factor_le_aggregate (F:RegularIndex H) (hFA:F ∈ A):
      (BG H F).all≤p.all∧
      middle (BG H F)≤middle p∧
      total (BG H F)≤total p:=by
    have hsub:({F}:Finset (RegularIndex H)) ⊆ A:=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p,BF,sumFlag,middle,total] using
      LY H hsub
  have factorFuel (F:RegularIndex H) (hFA:F ∈ A) (j:ℕ)
      (hj:j≤sound.source.fuel p):
      j≤sound.source.fuel (BG H F):=by
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hFm:1≤middle (BG H F):=
      hFr.trans (ATD _)
    have hFt:1≤total (BG H F):=
      hFm.trans (AIS _)
    have hjT:j*total (BG H F)≤
        sound.source.totalCap:=by
      calc
        j*total (BG H F)≤j*total p:=
          Nat.mul_le_mul_left j hle.2.2
        _≤sound.source.fuel p*total p:=
          Nat.mul_le_mul_right (total p) hj
        _≤sound.source.totalCap:=hfeasibleP.1
    have hjY:j*middle (BG H F)≤
        sound.source.middleCap:=by
      calc
        j*middle (BG H F)≤j*middle p:=
          Nat.mul_le_mul_left j hle.2.1
        _≤sound.source.fuel p*middle p:=
          Nat.mul_le_mul_right (middle p) hj
        _≤sound.source.middleCap:=hfeasibleP.2.1
    have hjS:j*(BG H F).all≤
        sound.source.slopeCap:=by
      calc
        j*(BG H F).all≤j*p.all:=
          Nat.mul_le_mul_left j hle.1
        _≤sound.source.fuel p*p.all:=
          Nat.mul_le_mul_right p.all hj
        _≤sound.source.slopeCap:=hfeasibleP.2.2
    unfold EA.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates: ∀F ∈ A,∀j,j≤sound.source.fuel p→
      LX
        (sound.source.totalCap-j*wt AT F.1)
        (sound.source.middleCap-j*wt BC F.1)
        (sound.source.slopeCap-j*wt BE F.1)
        (wt BC F.1) (wt BE F.1)
        (wt AT F.1):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=sound.stageGates (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [hR,hY,hT] using hs
  have hcharge: ∀F ∈ A,∀j,j≤sound.source.fuel p→
      Lower80899.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80899.AGR.LP F) j≤
          charge (BG H F):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=hpay (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [Lower80899.AGR.LP,
      Lower80899.Oracle.LP,hR,hY,hT] using hs
  have hmpos:0<m:=by omega
  have hDpos:0<D:=by omega
  have hDa:D≤m*181235:=hweighted.1
  have hP:CK H A ≠ 0:=AHD H A
  have hcP:contactDec p≤wt (BV 131071) (CK H A):=by
    have h:=CS.FAK 131071 (by decide)
      (CK H A) hP
    simpa only [contactDec,p,IF,
      JM] using h
  have hDcap:D-wt (BV 131071) (CK H A)≤
      sound.source.contactCap p:=by
    unfold EA.contactCap
    omega
  have hbandThin:CS.HN 131071
      (D-wt (BV 131071) (CK H A)) 50165
      (wt (BV 131071) (CK H A))
      (wt AT (CK H A))
      (wt BC (CK H A))
      (wt BE (CK H A))
      (sound.source.totalCap-wt AT (CK H A))
      (sound.source.middleCap-wt BC (CK H A))
      (sound.source.slopeCap-wt BE (CK H A))
      (sound.source.fuel p)<sound.source.gap:=by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' :LH 50165
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (sound.source.totalCap-wt AT (CK H A))
          (sound.source.middleCap-wt BC (CK H A))
          (sound.source.slopeCap-wt BE (CK H A))
          (sound.source.fuel p)<sound.source.gap:=by
        simpa only [EA.band,p,KH,
          IF,JM] using hold
      exact (CS.CCZ
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' :CS.HN 131071
          (sound.source.contactCap p) 50165 (contactDec p)
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (sound.source.totalCap-wt AT (CK H A))
          (sound.source.middleCap-wt BC (CK H A))
          (sound.source.slopeCap-wt BE (CK H A))
          (sound.source.fuel p)<sound.source.gap:=by
        simpa only [EA.bandThin,p,KH,
          IF,JM] using hthin
      exact (CS.AZD 131071 50165
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply AAA D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50165 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p,KH,
      IF,JM] using hterminalP
  · simpa only [p,KH,
      IF,JM] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

theorem exact_split
    (sound:YF) (D m:ℕ)
    (hweighted:D≤m*181235∧m*50165<D)
    (hshape:D+sound.source.slopeCap≤
      131071*(sound.source.middleCap+1))
    (hslopeM:sound.source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:sound.source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hroute:sound.source.Routeable (BF H A))
    (hnarrowS:(BF H A).all≤40)
    (hnarrowY:middle (BF H A)≤181)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤
        CY.cost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
          (BG H F).all (middle (BG H F)) (total (BG H F)):=by
  apply EKV sound
    (fun p=>CY.cost sound.source.totalCap sound.source.middleCap sound.source.slopeCap
      p.all (middle p) (total p)) _ D m hweighted hshape hslopeM hmChar u0 u1 H selected Gamma
    hdegree hagreement hno hgap A hroute hnarrowS hnarrowY hnarrowT
  intro p j _hr _hs _hy _ht _hj
  simpa only [PowerRoute.stageCost,PowerRoute.stagePair,Oracle.LP,
    FactorSwitch.helperPair,CY.cost,PI.pair] using
    PI.GEK
      (sound.source.totalCap-j*total p) (sound.source.middleCap-j*middle p) (sound.source.slopeCap-j*p.all)
      sound.source.totalCap sound.source.middleCap sound.source.slopeCap p.all (middle p) (total p)
      (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)

end
end Lower80899.EAK
end MergedPart3
section MergedPart4
namespace ANB
open MZ PI RCN260 GB
theorem count0 (r y t:ℕ) (hr:1≤r) (hR:r≤40) (hY:y≤181) (hT:t≤11784):
    FU (pair 88902 1382 308 r y t)≤0*t+4941578463932*y+44352901270546*r:=by
  simpa only [Nat.zero_mul,Nat.zero_add] using EZQ r y t hr hY hT
theorem count1 (r y t:ℕ) (hr:1≤r) (hR:r≤29) (hY:y≤130) (hT:t≤8684):
    FU (pair 88902 1382 308 r y t)≤54403376517*t+3567494416161*y+16136495626660*r:=by
  exact count_le 88902 1382 308 29 130 8684 54403376517 3567494416161 16136495626660 r y t (by decide+kernel) hr hR hY hT
theorem count2 (r y t:ℕ) (hr:1≤r) (hR:r≤27) (hY:y≤123) (hT:t≤8284):
    FU (pair 88902 1382 308 r y t)≤51033431681*t+3361322287002*y+15331603481093*r:=by
  exact count_le 88902 1382 308 27 123 8284 51033431681 3361322287002 15331603481093 r y t (by decide+kernel) hr hR hY hT
theorem count3 (r y t:ℕ) (hr:1≤r) (hR:r≤26) (hY:y≤116) (hT:t≤8284):
    FU (pair 88902 1382 308 r y t)≤48610085170*t+3300429027688*y+14905350665897*r:=by
  exact count_le 88902 1382 308 26 116 8284 48610085170 3300429027688 14905350665897 r y t (by decide+kernel) hr hR hY hT
theorem count4 (r y t:ℕ) (hr:1≤r) (hR:r≤25) (hY:y≤113) (hT:t≤8284):
    FU (pair 88902 1382 308 r y t)≤47030594766*t+3239535768375*y+14722670887955*r:=by
  exact count_le 88902 1382 308 25 113 8284 47030594766 3239535768375 14722670887955 r y t (by decide+kernel) hr hR hY hT
end ANB
end MergedPart4
section MergedPart5
namespace Lower80899.TenPhase
open ProximityPrize.Benchmark RCN095 RCN140 RCN156 RCN234 RCN238 RCN266 RCN319
open Lower80899.Oracle Lower80899.BatchPhase
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _

def sound:ℕ→YF
  | 0=>SourceSound.Phase00.sound
  | 1=>SourceSound.Phase01.sound
  | 2=>SourceSound.Phase02.sound
  | 3=>SourceSound.Phase03.sound
  | 4=>SourceSound.Phase04.sound
  | 5=>SourceSound.Phase05.sound
  | 6=>SourceSound.Phase06.sound
  | 7=>SourceSound.Phase03.sound
  | 8=>SourceSound.Phase04.sound
  | _+9=>SourceSound.PhaseFinal.sound

def kernel (u0 u1:I→K) (j:ℕ):WZ (sound j) u0 u1:=
  match j with
  | 0=>SourceSound.Phase00.kernel u0 u1
  | 1=>SourceSound.Phase01.kernel u0 u1
  | 2=>SourceSound.Phase02.kernel u0 u1
  | 3=>SourceSound.Phase03.kernel u0 u1
  | 4=>SourceSound.Phase04.kernel u0 u1
  | 5=>SourceSound.Phase05.kernel u0 u1
  | 6=>SourceSound.Phase06.kernel u0 u1
  | 7=>SourceSound.Phase03.kernel u0 u1
  | 8=>SourceSound.Phase04.kernel u0 u1
  | _+9=>SourceSound.PhaseFinal.kernel u0 u1

end
end Lower80899.TenPhase
end MergedPart5
section MergedPart6
namespace LD
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem DIG
    (p q L0 L1 T0 T1 L T a b c:ℤ)
    (hp:0≤p) (hq:0≤q) (hn:0<p+q)
    (hT:(p+q)*T=p*T0+q*T1)
    (hlo:p*L0+q*L1≤(p+q)*L)
    (hhi:(p+q)*L≤p*L0+q*L1+(p+q))
    (h0:max 0 (-a)<a*L0+b*T0+c)
    (h1:max 0 (-a)<a*L1+b*T1+c):
    0<a*L+b*T+c:=by
  let e:=(p+q)*L-(p*L0+q*L1)
  let d:=max 0 (-a)
  have he0:0≤e:=by dsimp [e];omega
  have he1:e≤p+q:=by dsimp [e];omega
  have h0' :d+1≤a*L0+b*T0+c:=by dsimp [d];omega
  have h1' :d+1≤a*L1+b*T1+c:=by dsimp [d];omega
  have hsum:=add_le_add (mul_le_mul_of_nonneg_left h0' hp) (mul_le_mul_of_nonneg_left h1' hq)
  have hround: -(p+q)*d≤a*e:=by
    by_cases ha:0≤a
    · have hd:d=0:=by dsimp [d];omega
      rw [hd,mul_zero]
      exact mul_nonneg ha he0
    · have hd:d= -a:=by dsimp [d];omega
      have hh:=mul_le_mul_of_nonpos_left he1 (show a≤0 by omega)
      rw [hd]
      nlinarith only [hh]
  have hidentity:(p+q)*(a*L+b*T+c)=
      p*(a*L0+b*T0+c)+q*(a*L1+b*T1+c)+a*e:=by
    dsimp [e]
    have hh:=congrArg (fun x:ℤ=>b*x) hT
    nlinarith only [hh]
  have hpositive:0<(p+q)*(a*L+b*T+c):=by
    nlinarith only [hsum,hround,hidentity,hn]
  exact pos_of_mul_pos_right hpositive (le_of_lt hn)

def ceilBlend (T0 T1 L0 L1 T:ℕ):ℕ:=
  ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1)/(T1-T0)

theorem CKO (T0 T1 L0 L1 T:ℕ)
    (h01:T0<T1) (h0:T0≤T) (h1:T≤T1):
    (T1-T)*L0+(T-T0)*L1≤(T1-T0)*ceilBlend T0 T1 L0 L1 T∧
    (T1-T0)*ceilBlend T0 T1 L0 L1 T<
      (T1-T)*L0+(T-T0)*L1+(T1-T0):=by
  have hn:0<T1-T0:=by omega
  have hq:=Nat.div_add_mod ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) (T1-T0)
  have hm:=Nat.mod_lt ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1) hn
  unfold ceilBlend
  omega

theorem CUO (T0 T1 T:ℕ) (h0:T0≤T) (h1:T≤T1):
    (T1-T0)*T=(T1-T)*T0+(T-T0)*T1:=by
  have h01:T0≤T1:=by omega
  have ha:=Nat.sub_add_cancel h0
  have hb:=Nat.sub_add_cancel h1
  have hc:=Nat.sub_add_cancel h01
  nlinarith

theorem CDI (T0 T1 L0 L1 T k:ℕ)
    (h01:T0<T1) (h0:T0≤T) (h1:T≤T1)
    (hL0:T0+k≤L0) (hL1:T1+k≤L1):
    T+k≤ceilBlend T0 T1 L0 L1 T:=by
  have hn:0<T1-T0:=by omega
  have hsum:(T1-T)+(T-T0)=T1-T0:=by omega
  have hT:=CUO T0 T1 T h0 h1
  have hL:=(CKO T0 T1 L0 L1 T h01 h0 h1).1
  have hscale:=Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hk:=congrArg (fun n:ℕ=>n*k) hsum
  have hp:(T1-T0)*(T+k)≤(T1-T0)*ceilBlend T0 T1 L0 L1 T:=by
    nlinarith only [hT,hL,hscale,hk]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem DRS (T0 T1 L0 L1 T k:ℕ)
    (h01:T0<T1) (h0:T0≤T) (h1:T≤T1) (hL0:k≤L0) (hL1:k≤L1):
    k≤ceilBlend T0 T1 L0 L1 T:=by
  have hn:0<T1-T0:=by omega
  have hsum:(T1-T)+(T-T0)=T1-T0:=by omega
  have hL:=(CKO T0 T1 L0 L1 T h01 h0 h1).1
  have hscale:=Nat.add_le_add (Nat.mul_le_mul_left (T1-T) hL0) (Nat.mul_le_mul_left (T-T0) hL1)
  have hp:(T1-T0)*k≤(T1-T0)*ceilBlend T0 T1 L0 L1 T:=by
    nlinarith only [hL,hscale,congrArg (fun n:ℕ=>n*k) hsum]
  exact Nat.le_of_mul_le_mul_left hp hn

theorem GGM (T0 T1 L0 L1 T:ℕ)
    (h01:T0<T1) (h0:T0≤T) (h1:T≤T1):
    ceilBlend T0 T1 L0 L1 T≤max L0 L1:=by
  have hn:0<T1-T0:=by omega
  have hsum:(T1-T)+(T-T0)=T1-T0:=by omega
  have hL:=(CKO T0 T1 L0 L1 T h01 h0 h1).2
  have hscale:=Nat.add_le_add (Nat.mul_le_mul_left (T1-T) (le_max_left L0 L1))
    (Nat.mul_le_mul_left (T-T0) (le_max_right L0 L1))
  have hp:(T1-T0)*ceilBlend T0 T1 L0 L1 T<(T1-T0)*(max L0 L1+1):=by
    nlinarith only [hL,hscale,congrArg (fun n:ℕ=>n*max L0 L1) hsum]
  have hh:=Nat.lt_of_mul_lt_mul_left hp
  omega

end LD
end MergedPart6
section MergedPart7
namespace LD
open scoped BigOperators
open RCN100 RZ
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000

theorem DYD (D w L s h:ℕ)
    (hh:0<h) (hs:h≤s) (hL:h≤L):
    AW D w L s=
      AW D w L (h-1)+AW (D-(w-1)*h) w (L-h) (s-h):=by
  have hc (D L s:ℕ):AW D w L s=
      ∑ j∈Finset.range (s+1),∑ i∈Finset.range (L+1),(L+1-i-j)*(D-w*i-(w-1)*j):=by
    unfold AW
    exact Finset.sum_comm
  rw [hc D L s,hc D L (h-1),hc (D-(w-1)*h) (L-h) (s-h)]
  have he:s+1=h+(s-h+1):=by omega
  conv_lhs=>rw [he,Finset.sum_range_add]
  rw [show h-1+1=h by omega]
  apply congrArg₂ (fun a b:ℕ=>a+b)
  · rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have htrim:
        (∑ i∈Finset.range (L-h+1),(L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)))=
        ∑ i∈Finset.range (L+1),(L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)):=by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hn
      have hi' :=Finset.mem_range.mp hi
      have hn' :L-h+1≤ i:=by simpa using hn
      have hz:L+1-i-(h+j)=0:=by omega
      simp only [hz,zero_mul]
    rw [←htrim]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    · omega
    · rw [Nat.mul_add]
      omega

def BJR (q r w L s:ℕ):ℕ:=
  if r+s≤w then OM q r w L s else
    OM q r w L (w-r-1)+
    OM (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))

theorem DQG (q r w L s:ℕ)
    (hw:2≤w) (hr:r<w) (hs:s<w) (hsq:s≤q) (hL:q+1≤L):
    AW (q*w+r) w L s=BJR q r w L s:=by
  unfold BJR
  split_ifs with hfirst
  · exact GQ q r w L s hw hsq (by omega) hfirst
  · have hh:0<w-r:=by omega
    have hhs:w-r≤s:=by omega
    have hhq:w-r≤q:=by omega
    have hprod:(w-1)*(w-r)≤q*w+r:=by
      have h:=Nat.mul_le_mul (show w-1≤w by omega) hhq
      nlinarith
    have hcut:q*w+r-(w-1)*(w-r)=(q+1-(w-r))*w:=by
      have h1:=Nat.sub_add_cancel hprod
      have h2:=Nat.sub_add_cancel (show w-r≤q+1 by omega)
      have h3:=Nat.sub_add_cancel (show r≤w by omega)
      have h4:w-1+1=w:=by omega
      nlinarith
    rw [DYD (q*w+r) w L s (w-r) hh hhs (by omega),hcut]
    rw [GQ q r w L (w-r-1) hw (by omega) (by omega) (by omega)]
    simpa only [Nat.add_zero] using congrArg
      (fun x=>OM q r w L (w-r-1)+x)
      (GQ (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))
        hw (by omega) (by omega) (by omega))

end LD
end MergedPart7
section MergedPart8
namespace LD
open RZ RCN100
set_option autoImplicit false
set_option maxHeartbeats 700000

def oneSlope (q r w s:ℕ):ℕ:=
  (r+q)*(smallChoose (q+2) 2-smallChoose (q+1-s) 2)+
    (w-2)*(smallChoose (q+2) 3-smallChoose (q+1-s) 3)

def oneIntercept (q r w s:ℕ):ℤ:=
  (OM q r w q s:ℤ)-(oneSlope q r w s:ℤ)*q

theorem FAU (q r w L s:ℕ) (hL:q≤L):
    OM q r w L s+oneSlope q r w s*q=
      OM q r w q s+oneSlope q r w s*L:=by
  have hU:=Nat.sub_add_cancel (show q≤L+1 by omega)
  have hh:=congrArg (fun x:ℕ=>oneSlope q r w s*x) hU
  unfold OM oneSlope at*
  simp only [show q+1-q=1 by omega,one_mul] at*
  nlinarith only [hh]

theorem DVC (q r w L s:ℕ) (hL:q≤L):
    (OM q r w L s:ℤ)=
      (oneSlope q r w s:ℤ)*L+oneIntercept q r w s:=by
  have hh:(OM q r w L s:ℤ)+(oneSlope q r w s:ℤ)*q=
      (OM q r w q s:ℤ)+(oneSlope q r w s:ℤ)*L:=by
    exact_mod_cast FAU q r w L s hL
  unfold oneIntercept
  omega

def ECJ (q r w s:ℕ):ℕ:=
  if r+s≤w then oneSlope q r w s else
    oneSlope q r w (w-r-1)+oneSlope (q+1-(w-r)) 0 w (s-(w-r))

def CSW (q r w s:ℕ):ℤ:=
  if r+s≤w then oneIntercept q r w s else
    oneIntercept q r w (w-r-1)+oneIntercept (q+1-(w-r)) 0 w (s-(w-r))-
      (oneSlope (q+1-(w-r)) 0 w (s-(w-r)):ℤ)*(w-r)

theorem ERG (q r w L s:ℕ)
    (hw:2≤w) (hr:r<w) (hs:s<w) (hsq:s≤q) (hL:q+1≤L):
    (AW (q*w+r) w L s:ℤ)=
      (ECJ q r w s:ℤ)*L+CSW q r w s:=by
  rw [DQG q r w L s hw hr hs hsq hL]
  unfold BJR ECJ CSW
  split_ifs with hfirst
  · exact DVC q r w L s (by omega)
  · rw [Nat.cast_add,DVC q r w L (w-r-1) (by omega),
      DVC (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r)) (by omega),
      Nat.cast_sub (show w-r≤L by omega),Nat.cast_sub (show r≤w by omega),Nat.cast_add]
    ring

end LD
end MergedPart8

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace FI
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def num (L U S r y t:ℤ):ℤ:=
 131073*((1+2*131071*y)*(r*L+t*S)+131071*(2*r-1)*(y*L+t*U)+
   (1+2*131071*t)*(y*S+r*U))+80910*50164*(y*S+r*U)
def pair (r y t:ℤ):ℤ:=num (11785-t) (348-y) (78-r) (50-r) (229-y) (17230-t)

theorem DJM (f:ℤ→ℤ)
 (hf: ∀x,f x=(f 1-f 0)*x+f 0) (lo hi x:ℤ)
 (hlo:lo≤x) (hhi:x≤hi) (hl:0≤f lo) (hh:0≤f hi):0≤f x:=by
 rw [hf x]
 by_cases ha:0≤f 1-f 0
 · rw [hf lo] at hl
   have hm:=mul_le_mul_of_nonneg_left hlo ha
   linarith only [hl,hm]
 · have ha' :f 1-f 0≤0:=by omega
   rw [hf hi] at hh
   have hm:=mul_le_mul_of_nonpos_left hhi ha'
   linarith only [hh,hm]

def AffineEach (f:ℤ→ℤ→ℤ→ℤ):Prop:=
 (∀r y t,f r y t=(f 1 y t-f 0 y t)*r+f 0 y t)∧
 (∀r y t,f r y t=(f r 1 t-f r 0 t)*y+f r 0 t)∧
 (∀r y t,f r y t=(f r y 1-f r y 0)*t+f r y 0)

theorem box_nonneg (f:ℤ→ℤ→ℤ→ℤ) (hf:AffineEach f)
 (rl rh yl yh tl th r y t:ℤ) (hrl:rl≤r) (hrh:r≤rh)
 (hyl:yl≤y) (hyh:y≤yh) (htl:tl≤t) (hth:t≤th)
 (hc: ∀rr yy tt,(rr=rl∨rr=rh)→(yy=yl∨yy=yh)→(tt=tl∨tt=th)→0≤f rr yy tt):
 0≤f r y t:=by
 have hyf (rr:ℤ) (hr:rr=rl∨rr=rh):0≤f rr y t:=by
  apply DJM (fun yy=>f rr yy t) (fun yy=>hf.2.1 rr yy t) yl yh y hyl hyh
  · exact DJM (fun tt=>f rr yl tt) (fun tt=>hf.2.2 rr yl tt)
      tl th t htl hth (hc rr yl tl hr (Or.inl rfl) (Or.inl rfl))
      (hc rr yl th hr (Or.inl rfl) (Or.inr rfl))
  · exact DJM (fun tt=>f rr yh tt) (fun tt=>hf.2.2 rr yh tt)
      tl th t htl hth (hc rr yh tl hr (Or.inr rfl) (Or.inl rfl))
      (hc rr yh th hr (Or.inr rfl) (Or.inr rfl))
 exact DJM (fun rr=>f rr y t) (fun rr=>hf.1 rr y t)
   rl rh r hrl hrh (hyf rl (Or.inl rfl)) (hyf rh (Or.inr rfl))

/-- Margin after choosing endpoints for V's and the whole carrier's total flags. -/
def fixedMargin (rv yv wr wy av bv aw bw pw r y t:ℤ):ℤ:=
 let tv:=av*t+bv
 let tw:=aw*tv+bw
 pair r y t-num 88902 1382 308 (rv-r) (yv-y) (tv-t)-
  num 18000 348 78 (wr-rv) (wy-yv) (tw-tv)-pw*pair wr wy tw

theorem fixed_affine (rv yv wr wy av bv aw bw pw:ℤ):
 AffineEach (fixedMargin rv yv wr wy av bv aw bw pw):=by
 constructor
 · intro r y t
   unfold fixedMargin pair num
   ring
 constructor
 · intro r y t
   unfold fixedMargin pair num
   ring
 · intro r y t
   unfold fixedMargin pair num
   ring

/-- Margin over the whole carrier's three independent flag coordinates. -/
def wholeMargin (r y t rv yv tv pw wr wy wt:ℤ):ℤ:=
 pair r y t-num 88902 1382 308 (rv-r) (yv-y) (tv-t)-
  num 18000 348 78 (wr-rv) (wy-yv) (wt-tv)-pw*pair wr wy wt

theorem whole_affine (r y t rv yv tv pw:ℤ):
 AffineEach (wholeMargin r y t rv yv tv pw):=by
 constructor
 · intro wr wy wt
   unfold wholeMargin pair num
   ring
 constructor
 · intro wr wy wt
   unfold wholeMargin pair num
   ring
 · intro wr wy wt
   unfold wholeMargin pair num
   ring

def emptyMargin (ar br ay by' at' bt pw r y t:ℤ):ℤ:=
 let wr:=ar*r+br
 let wy:=ay*y+by'
 let wt:=at'*t+bt
 pair r y t-num 18000 348 78 (wr-r) (wy-y) (wt-t)-pw*pair wr wy wt

theorem empty_affine (ar br ay by' at' bt pw:ℤ):
 AffineEach (emptyMargin ar br ay by' at' bt pw):=by
 constructor
 · intro r y t
   unfold emptyMargin pair num
   ring
 constructor
 · intro r y t
   unfold emptyMargin pair num
   ring
 · intro r y t
   unfold emptyMargin pair num
   ring
theorem tv_affine (r y t rv yv wr wy aw bw pw tv:ℤ):
 wholeMargin r y t rv yv tv pw wr wy (aw*tv+bw)=
  (wholeMargin r y t rv yv 1 pw wr wy (aw+bw)-
    wholeMargin r y t rv yv 0 pw wr wy bw)*tv+
    wholeMargin r y t rv yv 0 pw wr wy bw:=by
 unfold wholeMargin pair num
 ring




end FI

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace DRM
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN302
open RZ IL
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

theorem OS:AW 45671220 131071 18000 78=8931777318780375:=by
  rw [show 45671220=348*131071+58512 by decide+kernel]
  rw [GQ 348 58512 131071 18000 78
    (by decide+kernel) (by decide+kernel) (by decide+kernel) (by decide+kernel)]
  decide+kernel

theorem rank_exact:ES 252 18000 78=34044741742:=by
  rw [ClosedRank.RU _ _ _ (by decide+kernel) (by decide+kernel)]
  decide+kernel

theorem AJG:7152539565527≤AW 45671220 131071 18000 78-
    262144*ES 252 18000 78:=by
  rw [OS,rank_exact]

theorem finrank_gap (u0 u1:IRSProfile.Index→IRSProfile.Field):
    7152539565527≤Module.finrank IRSProfile.Field (IJ (K:=IRSProfile.Field)
      45671220 131071 18000 78 252 IRSProfile.domain u0 u1):=
  KJ 45671220 18000 78 252 7152539565527 u0 u1 AJG

end DRM

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace CMQ
open RCN095 DY CS
open Lower80899.Oracle
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def terminal:EA:=⟨88902,1382,308,7897858914422491⟩

theorem EIN (delta dT dY dS T yCap S k l:ℕ) (h:k≤l):
    LH delta dT dY dS T yCap S k≤LH delta dT dY dS T yCap S l:=by
  induction k generalizing l T yCap S with
  | zero=>simp [LH]
  | succ k ih=>
    cases l with
    | zero=>omega
    | succ l=>
      simp only [LH]
      exact Nat.add_le_add_left (ih _ _ _ _ (by omega)) _

private theorem FNQ:
    LH 50165 29 29 29 88873 1353 279 10<7897858914422491:=by
  decide+kernel
private theorem FHZ:
    LH 50165 118 118 1 88784 1264 307 11<7897858914422491:=by
  decide+kernel

theorem high_route (p:FlagDegree) (hr:1≤p.all) (hR:p.all≤50)
    (hY:middle p≤229) (hT:total p≤11784)
    (hh:29≤p.all∨118≤middle p):terminal.Routeable p:=by
  have hry:p.all≤middle p:=by simp [middle]
  have hyt:middle p≤total p:=by simp [middle,total]
  refine ⟨hr,by dsimp [terminal];omega,by dsimp [terminal];omega,
    by dsimp [terminal];omega,Or.inl ?_⟩
  change LH 50165 (total p) (middle p) p.all
    (88902-total p) (1382-middle p) (308-p.all) (terminal.fuel p)<7897858914422491
  rcases hh with hh | hh
  · have hd:308/p.all≤308/29:=Nat.div_le_div_left hh (by omega)
    have hf:terminal.fuel p≤10:=by
      have hm:terminal.fuel p≤308/p.all:=by
        dsimp [EA.fuel,terminal]
        exact (min_le_right _ _).trans (min_le_right _ _)
      omega
    have hm:=BRL 50165 (total p) (middle p) p.all
      (88902-total p) (1382-middle p) (308-p.all) 29 29 29 88873 1353 279
      (terminal.fuel p) (by omega) (by omega) (by omega) (by omega) (by omega) hh
    exact hm.trans_lt ((EIN _ _ _ _ _ _ _ _ _ hf).trans_lt FNQ)
  · have hd:1382/middle p≤1382/118:=Nat.div_le_div_left hh (by omega)
    have hf:terminal.fuel p≤11:=by
      have hm:terminal.fuel p≤1382/middle p:=by
        dsimp [EA.fuel,terminal]
        exact (min_le_right _ _).trans (min_le_left _ _)
      omega
    have hm:=BRL 50165 (total p) (middle p) p.all
      (88902-total p) (1382-middle p) (308-p.all) 118 118 1 88784 1264 307
      (terminal.fuel p) (by omega) (by omega) (by omega) (by omega) hh hr
    exact hm.trans_lt ((EIN _ _ _ _ _ _ _ _ _ hf).trans_lt FHZ)

private theorem FNX:
    LH 50165 8500 1 1 80402 1381 307 10<7897858914422491:=by
  decide+kernel

theorem GDL (p:FlagDegree) (hr:1≤p.all) (hR:p.all≤50)
    (hY:middle p≤229) (hT:total p≤11784) (hh:8500≤total p):terminal.Routeable p:=by
  have hry:p.all≤middle p:=by simp [middle]
  refine ⟨hr,by dsimp [terminal];omega,by dsimp [terminal];omega,
    by dsimp [terminal];omega,Or.inl ?_⟩
  change LH 50165 (total p) (middle p) p.all
    (88902-total p) (1382-middle p) (308-p.all) (terminal.fuel p)<7897858914422491
  have hd:88902/total p≤88902/8500:=Nat.div_le_div_left hh (by omega)
  have hf:terminal.fuel p≤10:=by
    have hm:terminal.fuel p≤88902/total p:=by
      dsimp [EA.fuel,terminal]
      exact min_le_left _ _
    omega
  have hm:=BRL 50165 (total p) (middle p) p.all
    (88902-total p) (1382-middle p) (308-p.all) 8500 1 1 80402 1381 307
    (terminal.fuel p) (by omega) (by omega) (by omega) hh (by omega) hr
  exact hm.trans_lt ((EIN _ _ _ _ _ _ _ _ _ hf).trans_lt FNX)

theorem stopped_caps (p:FlagDegree) (hr:1≤p.all) (hR:p.all≤50)
    (hY:middle p≤229) (hT:total p≤11784) (hstop: ¬terminal.Routeable p):
    p.all≤28∧middle p≤117∧total p≤8499:=by
  have hh: ¬(29≤p.all∨118≤middle p):=fun h=>hstop (high_route p hr hR hY hT h)
  have ht: ¬8500≤total p:=fun h=>hstop (GDL p hr hR hY hT h)
  omega

end CMQ


end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace TG
open ProximityPrize.Benchmark Lower80899.Oracle Lower80899.SourceSound
open DY Lower80899.FactorSwitch RCN095 RCN223 RCN234 RCN260
set_option autoImplicit false
set_option maxHeartbeats 3000000

def cheap:EA:=⟨18000,348,78,7152539565527⟩
def terminal:EA:=⟨88902,1382,308,7897858914422491⟩

theorem cheap_gates (p:FlagDegree) (j:ℕ)
    (hr:1≤p.all) (hR:p.all≤50) (hY:middle p≤229) (hT:total p≤11784):
    LX (cheap.totalCap-j*total p) (cheap.middleCap-j*middle p)
      (cheap.slopeCap-j*p.all) (middle p) p.all (total p):=by
  apply VW
  unfold cheap LX helperPair DG.mixedCost
  norm_num
  omega

theorem FKR (p:FlagDegree) (j:ℕ)
    (hr:1≤p.all) (hR:p.all≤50) (hY:middle p≤229) (hT:total p≤11784):
    LX (terminal.totalCap-j*total p) (terminal.middleCap-j*middle p)
      (terminal.slopeCap-j*p.all) (middle p) p.all (total p):=by
  apply VW
  unfold terminal LX helperPair DG.mixedCost
  norm_num
  omega


end TG

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace BU
open FV Lower80899.AMY
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def num (L U S r y t:ℕ):ℕ:=
 131073*((1+2*131071*y)*(r*L+t*S)+131071*(2*r-1)*(y*L+t*U)+
   (1+2*131071*t)*(y*S+r*U))+80910*50164*(y*S+r*U)
def pair (r y t:ℕ):ℕ:=
 if r<50 then num (11785-t) (348-y) (78-r) (50-r) (229-y) (17230-t) else 0

def allN (f:ℕ→Bool):ℕ→Bool
 | 0=>true
 | n+1=>allN f n && f n
theorem allN_sound (f:ℕ→Bool) (n:ℕ) (h:allN f n=true) (i:ℕ) (hi:i<n):f i=true:=by
 induction n with
 | zero=>omega
 | succ n ih=>
   simp only [allN,Bool.and_eq_true] at h
   by_cases he:i=n
   · simpa only [he] using h.2
   · exact ih h.1 (by omega)

def core (rv yv ct i:ℕ):ℕ × ℕ × ℕ:=
 (if i%2=0 then 13 else min 17 (rv-1),
  if i/2%2=0 then 59 else min 76 yv,
  if i/4%2=0 then 3611 else min 4879 ct)
def corner (rv yv ct i j k:ℕ):Bool:=
 let (r,y,t):=core rv yv ct i
 let tv:=if j=0 then t else ct
 let branch:=k/4
 let wr:=if branch=0 then rv else if branch=1 then rv+1 else if branch=2 then 49 else 50
 let wy:=if k/2%2=0 then yv else 229
 let wt:=if k%2=0 then tv else 11784
 if 50<wr∨wr<rv∨(branch≠0∧wr=rv)∨(branch=0∧(k/2%2≠0∨k%2≠0)) then true
 else Nat.ble (num 88902 1382 308 (rv-r) (yv-y) (tv-t)+
    num 18000 348 78 (wr-rv) (wy-yv) (wt-tv)+pair wr wy wt) (pair r y t)
def corners (rv yv ct:ℕ):Bool:=
 if min 17 (rv-1)<13∨min 76 yv<59∨min 4879 ct<3611 then true
 else allN (fun i=>allN (fun j=>allN (corner rv yv ct i j) 16) 2) 8

def emptyCorner (i k:ℕ):Bool:=
 let r:=if i%2=0 then 13 else 17
 let y:=if i/2%2=0 then 59 else 76
 let t:=if i/4%2=0 then 3611 else 4879
 let wr:=if k/4=0 then r+1 else if k/4=1 then 49 else 50
 let wy:=if k/2%2=0 then y else 229
 let wt:=if k%2=0 then t else 11784
 Nat.ble (num 18000 348 78 (wr-r) (wy-y) (wt-t)+pair wr wy wt) (pair r y t)
theorem GWO:allN (fun i=>allN (emptyCorner i) 12) 8=true:=by decide+kernel
def c14:Array ℕ:= #[9339,9306,9273,9240,9207,9173,9139,9105,9071,9036,9001,8968,8943,8922,8904,8887,8869,8852,8834,8816,8797,8779,8760,8740,8720,8700,8680,8659,8638,8616,8594,8572,8549,8526,8502,8478,8453,8428,8402,8376,8349,8322,8294,8266,8237,8207,8177,8146,8115,8082,8050,8016,7981,7946,7910,7873,7835,7796,7756,7716,7674,7631,7587,7542,7496,7448,7399,7349,7297,7244,7190,7134,7076,7017,6955,6892,6827,6760,6690,6618,6544,6468,6389,6307,6222,6134,6042,5948,5849,5747,5641,5531,5419,5304,5187,5068,4947,4824,4700,4574,4447,4318,4189,4059,3929,3798,3668,3538,3409,3281,3155,3031,2909,2790,2673,2561,2452,2343,2232,2120,2006,1891,1773,1654,1534,1411,1287,1160,1032,902,769,635,498,360,219,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c15:Array ℕ:= #[9223,9190,9156,9123,9089,9055,9021,8987,8958,8934,8915,8897,8880,8863,8846,8828,8810,8792,8774,8755,8736,8717,8697,8677,8656,8636,8614,8593,8571,8549,8526,8503,8479,8455,8431,8406,8380,8354,8328,8301,8273,8245,8217,8187,8158,8127,8096,8064,8032,7999,7965,7930,7895,7858,7821,7783,7744,7705,7664,7622,7579,7535,7490,7444,7397,7348,7298,7247,7195,7140,7085,7028,6969,6908,6846,6781,6715,6647,6576,6503,6428,6351,6270,6187,6101,6012,5920,5825,5726,5623,5516,5404,5289,5172,5052,4931,4807,4681,4554,4425,4295,4164,4031,3899,3766,3633,3500,3367,3236,3106,2978,2852,2728,2607,2489,2376,2266,2156,2044,1931,1816,1700,1581,1462,1340,1216,1091,963,834,703,569,434,296,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c16:Array ℕ:= #[9103,9070,9036,9002,8970,8945,8924,8905,8888,8872,8855,8838,8821,8803,8785,8767,8748,8729,8710,8691,8671,8651,8631,8610,8589,8567,8545,8523,8500,8477,8454,8430,8406,8381,8355,8330,8303,8277,8249,8222,8193,8164,8135,8105,8074,8043,8011,7978,7945,7910,7876,7840,7803,7766,7728,7689,7649,7608,7567,7524,7480,7435,7389,7342,7293,7244,7193,7140,7086,7031,6974,6916,6856,6794,6731,6665,6598,6528,6457,6383,6307,6228,6147,6063,5976,5886,5792,5696,5596,5492,5385,5273,5156,5036,4914,4789,4662,4533,4403,4271,4138,4004,3869,3733,3597,3462,3326,3191,3057,2925,2795,2666,2541,2418,2299,2184,2073,1962,1850,1736,1620,1502,1383,1262,1139,1015,888,760,630,497,363,226,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c17:Array ℕ:= #[8980,8953,8931,8912,8894,8878,8861,8845,8828,8811,8793,8775,8757,8739,8721,8702,8682,8663,8643,8623,8603,8582,8561,8539,8517,8495,8472,8449,8426,8402,8378,8353,8328,8302,8276,8249,8222,8195,8167,8138,8109,8079,8048,8017,7986,7953,7920,7887,7852,7817,7781,7745,7707,7669,7630,7590,7549,7507,7464,7420,7375,7329,7282,7234,7184,7133,7081,7028,6973,6916,6858,6799,6738,6675,6610,6544,6475,6404,6332,6256,6179,6099,6017,5932,5844,5753,5659,5561,5460,5356,5247,5135,5018,4896,4771,4643,4513,4381,4248,4113,3977,3839,3701,3563,3424,3285,3147,3009,2873,2738,2605,2475,2347,2223,2103,1986,1874,1762,1649,1534,1417,1298,1178,1056,932,806,679,549,418,284,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c18:Array ℕ:= #[8898,8881,8865,8849,8832,8816,8798,8781,8763,8746,8727,8709,8690,8671,8652,8632,8613,8592,8572,8551,8530,8508,8486,8464,8441,8418,8395,8371,8347,8322,8297,8271,8245,8219,8192,8164,8136,8108,8079,8049,8019,7988,7957,7925,7892,7859,7825,7790,7755,7719,7682,7644,7606,7567,7526,7485,7443,7400,7356,7311,7265,7218,7170,7120,7069,7017,6964,6909,6853,6796,6736,6676,6613,6549,6483,6415,6346,6274,6200,6124,6045,5964,5880,5794,5705,5613,5518,5420,5318,5212,5103,4990,4872,4750,4623,4492,4359,4224,4088,3949,3810,3669,3528,3386,3244,3102,2961,2821,2682,2545,2410,2277,2147,2021,1899,1781,1668,1555,1441,1324,1207,1087,966,842,718,591,462,331,199,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c19:Array ℕ:= #[8834,8818,8801,8784,8767,8749,8731,8713,8695,8676,8658,8638,8619,8599,8579,8559,8538,8517,8496,8474,8452,8430,8407,8384,8361,8337,8313,8288,8263,8237,8211,8185,8158,8130,8103,8074,8045,8016,7986,7955,7924,7892,7860,7827,7793,7759,7724,7688,7652,7615,7577,7538,7498,7458,7417,7374,7331,7287,7242,7196,7148,7100,7051,7000,6948,6895,6840,6784,6727,6668,6608,6546,6482,6417,6349,6280,6209,6136,6061,5984,5904,5822,5737,5650,5559,5466,5370,5271,5168,5062,4952,4838,4719,4597,4470,4337,4201,4062,3922,3781,3638,3494,3349,3204,3059,2914,2770,2626,2484,2345,2207,2072,1940,1812,1689,1569,1455,1341,1225,1108,989,868,746,621,495,367,237,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c20:Array ℕ:= #[8767,8750,8732,8714,8696,8678,8660,8641,8622,8603,8583,8563,8543,8523,8502,8481,8459,8437,8415,8393,8370,8347,8323,8299,8275,8250,8225,8199,8173,8147,8120,8093,8065,8037,8008,7978,7948,7918,7887,7855,7823,7790,7757,7723,7688,7653,7617,7580,7543,7504,7465,7425,7385,7343,7300,7257,7213,7167,7121,7074,7025,6975,6925,6873,6819,6765,6709,6652,6593,6533,6472,6408,6343,6277,6208,6138,6066,5991,5915,5836,5755,5672,5586,5497,5406,5312,5214,5114,5010,4903,4792,4677,4558,4435,4308,4175,4037,3895,3752,3606,3460,3312,3164,3016,2867,2719,2571,2425,2280,2137,1997,1860,1726,1596,1470,1350,1234,1119,1002,884,763,642,518,392,265,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c21:Array ℕ:= #[8695,8677,8659,8640,8621,8602,8583,8564,8544,8524,8503,8483,8462,8440,8419,8397,8375,8352,8329,8306,8282,8258,8233,8209,8183,8158,8132,8105,8078,8051,8023,7995,7966,7936,7907,7876,7845,7814,7782,7749,7716,7682,7647,7612,7577,7540,7503,7465,7426,7387,7346,7305,7263,7221,7177,7132,7087,7040,6992,6944,6894,6843,6791,6738,6683,6627,6570,6512,6452,6390,6327,6263,6197,6129,6059,5987,5913,5838,5760,5680,5598,5513,5426,5336,5244,5148,5050,4949,4844,4736,4624,4508,4389,4265,4137,4004,3866,3723,3575,3426,3276,3125,2973,2821,2669,2517,2366,2216,2069,1923,1780,1640,1504,1372,1244,1122,1005,889,771,651,530,407,282,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c22:Array ℕ:= #[8617,8599,8580,8560,8541,8521,8501,8481,8460,8439,8418,8396,8375,8352,8330,8307,8284,8261,8237,8212,8188,8163,8137,8112,8085,8059,8032,8004,7976,7948,7919,7890,7860,7829,7798,7767,7735,7702,7669,7635,7601,7566,7531,7494,7457,7420,7381,7342,7302,7261,7220,7178,7134,7090,7045,6999,6953,6905,6856,6806,6755,6702,6649,6594,6539,6481,6423,6363,6302,6239,6174,6108,6041,5971,5900,5827,5752,5675,5596,5515,5431,5345,5257,5166,5072,4976,4876,4774,4668,4559,4446,4330,4210,4085,3956,3823,3685,3542,3393,3241,3086,2931,2775,2619,2463,2308,2154,2000,1849,1701,1555,1412,1273,1139,1010,886,768,650,531,410,287,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c23:Array ℕ:= #[8534,8514,8495,8475,8454,8434,8413,8392,8370,8348,8326,8304,8281,8258,8235,8211,8187,8162,8137,8112,8087,8061,8034,8007,7980,7953,7924,7896,7867,7837,7807,7777,7746,7715,7683,7650,7617,7583,7549,7514,7478,7442,7405,7368,7330,7291,7251,7211,7170,7128,7085,7041,6997,6951,6905,6858,6809,6760,6710,6659,6606,6552,6498,6442,6384,6326,6266,6205,6142,6078,6012,5944,5875,5804,5732,5657,5581,5503,5422,5340,5255,5167,5078,4985,4891,4793,4692,4589,4482,4372,4258,4141,4020,3895,3766,3632,3494,3350,3202,3048,2890,2731,2571,2411,2251,2092,1933,1777,1622,1470,1321,1176,1035,898,767,641,522,403,282,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c24:Array ℕ:= #[8444,8424,8403,8382,8361,8339,8318,8295,8273,8250,8227,8204,8180,8156,8132,8107,8082,8056,8031,8004,7978,7951,7923,7895,7867,7838,7809,7779,7749,7719,7688,7656,7624,7591,7558,7524,7490,7455,7419,7383,7347,7309,7271,7232,7193,7153,7112,7070,7027,6984,6940,6895,6849,6802,6755,6706,6656,6606,6554,6501,6447,6392,6336,6278,6220,6160,6098,6035,5971,5905,5838,5769,5699,5627,5552,5477,5399,5319,5237,5153,5067,4978,4887,4794,4698,4599,4497,4392,4284,4173,4059,3941,3819,3693,3564,3430,3291,3148,2999,2846,2687,2523,2359,2195,2031,1867,1705,1545,1387,1231,1079,931,787,648,514,387,266,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c25:Array ℕ:= #[8347,8325,8304,8282,8260,8237,8214,8191,8168,8144,8120,8096,8071,8046,8021,7995,7969,7942,7915,7888,7860,7832,7803,7774,7745,7715,7685,7654,7623,7591,7558,7526,7492,7458,7424,7389,7353,7317,7280,7243,7205,7166,7126,7086,7045,7004,6962,6918,6875,6830,6784,6738,6691,6642,6593,6543,6492,6440,6387,6332,6277,6220,6163,6104,6043,5982,5919,5855,5789,5721,5653,5582,5510,5436,5361,5284,5204,5123,5040,4954,4867,4777,4684,4589,4492,4392,4289,4183,4074,3962,3847,3728,3606,3479,3349,3215,3076,2932,2784,2631,2472,2308,2139,1971,1802,1635,1468,1304,1142,983,827,676,529,388,252,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c26:Array ℕ:= #[8241,8219,8196,8173,8150,8126,8103,8078,8054,8029,8004,7979,7953,7926,7900,7873,7846,7818,7790,7761,7733,7703,7673,7643,7613,7581,7550,7518,7485,7452,7419,7384,7350,7315,7279,7242,7205,7168,7130,7091,7051,7011,6970,6929,6887,6844,6800,6755,6710,6664,6617,6569,6520,6470,6419,6368,6315,6261,6207,6151,6094,6036,5976,5916,5854,5791,5726,5660,5593,5524,5454,5382,5308,5233,5156,5077,4996,4913,4829,4742,4653,4561,4468,4371,4273,4171,4067,3960,3851,3737,3621,3502,3378,3251,3121,2986,2847,2704,2555,2402,2244,2081,1912,1738,1565,1393,1223,1054,888,725,566,412,262,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c27:Array ℕ:= #[8125,8102,8078,8054,8030,8005,7980,7955,7930,7904,7877,7851,7824,7796,7769,7740,7712,7683,7654,7624,7594,7563,7532,7501,7469,7436,7403,7370,7336,7302,7267,7231,7195,7158,7121,7083,7045,7006,6966,6926,6885,6844,6801,6758,6714,6670,6625,6578,6532,6484,6435,6386,6335,6284,6232,6178,6124,6069,6012,5955,5896,5837,5776,5713,5650,5585,5519,5451,5383,5312,5240,5166,5091,5014,4936,4855,4773,4689,4602,4514,4423,4331,4236,4138,4038,3936,3830,3722,3611,3497,3380,3260,3136,3009,2877,2742,2603,2460,2312,2159,2002,1839,1671,1498,1320,1143,968,795,625,458,295,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c28:Array ℕ:= #[7999,7974,7949,7924,7899,7873,7847,7820,7793,7766,7739,7711,7683,7654,7625,7595,7566,7535,7505,7474,7442,7410,7378,7345,7311,7278,7243,7209,7173,7137,7101,7064,7026,6988,6950,6910,6870,6830,6789,6747,6704,6661,6617,6573,6527,6481,6434,6387,6338,6289,6238,6187,6135,6082,6028,5973,5917,5860,5802,5743,5683,5621,5559,5495,5430,5363,5295,5226,5155,5083,5010,4934,4857,4779,4699,4617,4533,4447,4359,4269,4177,4083,3987,3888,3787,3683,3576,3467,3355,3240,3122,3001,2877,2749,2617,2482,2343,2199,2052,1900,1743,1581,1415,1242,1065,883,703,525,350,179,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c29:Array ℕ:= #[7859,7833,7807,7781,7754,7727,7700,7672,7644,7615,7586,7557,7527,7497,7467,7436,7405,7373,7341,7309,7276,7242,7208,7174,7139,7104,7068,7032,6995,6957,6919,6881,6842,6802,6762,6721,6680,6637,6595,6551,6507,6462,6417,6370,6323,6275,6227,6177,6127,6076,6024,5971,5917,5862,5807,5750,5692,5634,5574,5513,5451,5388,5323,5257,5190,5122,5053,4982,4909,4835,4760,4683,4605,4524,4442,4359,4273,4186,4097,4005,3912,3816,3718,3618,3516,3411,3303,3193,3080,2964,2846,2724,2599,2470,2339,2203,2064,1921,1774,1622,1466,1306,1140,970,794,612,427,245,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c30:Array ℕ:= #[7705,7678,7650,7622,7594,7566,7537,7508,7478,7448,7418,7387,7356,7324,7293,7260,7227,7194,7161,7127,7092,7057,7022,6986,6949,6912,6875,6837,6798,6759,6720,6680,6639,6598,6556,6513,6470,6426,6381,6336,6290,6244,6196,6148,6099,6050,5999,5948,5896,5843,5789,5735,5679,5622,5565,5506,5447,5386,5325,5262,5198,5133,5066,4999,4930,4860,4789,4716,4642,4566,4489,4410,4330,4248,4165,4079,3992,3903,3813,3720,3625,3528,3429,3327,3224,3118,3009,2898,2784,2667,2548,2426,2300,2171,2039,1904,1765,1622,1475,1324,1170,1010,846,678,504,325,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c31:Array ℕ:= #[7533,7504,7475,7446,7416,7386,7356,7325,7294,7262,7230,7198,7165,7132,7099,7065,7031,6996,6960,6925,6889,6852,6815,6777,6739,6700,6661,6621,6581,6540,6499,6457,6414,6371,6328,6283,6238,6192,6146,6099,6051,6003,5954,5904,5853,5801,5749,5696,5642,5587,5531,5475,5417,5359,5299,5239,5177,5115,5051,4987,4921,4854,4786,4716,4646,4574,4501,4426,4350,4273,4194,4113,4031,3948,3863,3776,3687,3596,3504,3410,3314,3215,3115,3012,2907,2800,2691,2579,2464,2347,2227,2104,1978,1849,1717,1582,1443,1300,1155,1005,851,693,531,364,193,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c32:Array ℕ:= #[7340,7310,7279,7248,7217,7185,7153,7121,7088,7055,7021,6987,6953,6918,6883,6847,6811,6774,6737,6700,6662,6623,6584,6545,6505,6464,6423,6382,6339,6297,6253,6210,6165,6120,6074,6028,5981,5933,5885,5836,5786,5736,5685,5633,5580,5527,5472,5417,5361,5304,5247,5188,5128,5068,5007,4944,4881,4816,4751,4684,4616,4547,4477,4406,4333,4260,4185,4108,4030,3951,3870,3788,3705,3619,3532,3444,3354,3262,3168,3072,2975,2875,2773,2670,2564,2456,2345,2232,2117,1999,1879,1755,1629,1501,1369,1234,1095,954,809,660,508,352,191,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c33:Array ℕ:= #[7122,7090,7058,7025,6992,6959,6925,6890,6856,6821,6785,6749,6713,6676,6639,6602,6563,6525,6486,6447,6407,6366,6325,6284,6242,6199,6156,6113,6069,6024,5978,5933,5886,5839,5791,5743,5694,5644,5594,5543,5491,5438,5385,5331,5276,5221,5164,5107,5049,4990,4930,4870,4808,4745,4682,4617,4552,4485,4418,4349,4279,4208,4136,4063,3989,3913,3836,3758,3678,3597,3515,3431,3345,3259,3170,3080,2988,2895,2800,2703,2604,2503,2400,2296,2189,2080,1969,1855,1739,1621,1501,1377,1251,1123,991,857,719,579,435,288,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c34:Array ℕ:= #[6875,6841,6806,6772,6736,6701,6665,6629,6592,6555,6518,6480,6441,6402,6363,6324,6283,6243,6202,6160,6118,6076,6033,5989,5945,5900,5855,5809,5763,5716,5669,5621,5572,5523,5473,5422,5371,5319,5266,5213,5159,5104,5049,4993,4936,4878,4819,4760,4700,4639,4577,4514,4450,4385,4320,4253,4185,4117,4047,3977,3905,3832,3758,3683,3606,3529,3450,3370,3288,3206,3121,3036,2949,2860,2770,2679,2586,2491,2395,2296,2196,2095,1991,1886,1778,1668,1557,1443,1327,1209,1088,965,839,711,581,447,311,172,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c35:Array ℕ:= #[6590,6554,6517,6480,6443,6406,6367,6329,6290,6251,6211,6171,6130,6089,6048,6006,5963,5921,5877,5833,5789,5744,5699,5653,5607,5560,5512,5464,5415,5366,5316,5266,5215,5163,5111,5058,5005,4950,4896,4840,4784,4727,4669,4610,4551,4491,4430,4369,4306,4243,4179,4114,4048,3981,3913,3844,3775,3704,3632,3559,3486,3411,3335,3258,3179,3100,3019,2937,2854,2770,2684,2597,2509,2419,2327,2235,2140,2044,1947,1848,1747,1644,1540,1434,1326,1216,1104,990,875,757,636,514,389,262,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c36:Array ℕ:= #[6260,6221,6182,6143,6103,6063,6023,5982,5940,5899,5856,5814,5771,5727,5683,5639,5594,5549,5503,5457,5410,5363,5315,5266,5218,5168,5118,5068,5017,4965,4913,4860,4806,4752,4698,4642,4586,4530,4472,4414,4356,4296,4236,4175,4113,4051,3988,3924,3859,3794,3727,3660,3592,3523,3453,3382,3310,3237,3164,3089,3013,2936,2859,2780,2700,2618,2536,2453,2368,2282,2195,2106,2017,1926,1833,1739,1644,1547,1449,1349,1248,1145,1040,934,826,716,605,491,376,259,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c37:Array ℕ:= #[5871,5830,5788,5746,5704,5661,5618,5574,5531,5486,5441,5396,5350,5304,5258,5211,5163,5115,5067,5018,4968,4918,4868,4817,4765,4713,4661,4608,4554,4500,4445,4389,4333,4277,4219,4162,4103,4044,3984,3924,3862,3800,3738,3675,3611,3546,3480,3414,3347,3279,3211,3141,3071,3000,2928,2855,2781,2706,2631,2554,2477,2398,2319,2238,2156,2074,1990,1905,1819,1732,1644,1554,1463,1371,1278,1184,1088,991,892,792,691,588,483,377,270,161,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c38:Array ℕ:= #[5407,5363,5319,5274,5229,5183,5137,5090,5044,4996,4949,4901,4852,4803,4754,4704,4653,4602,4551,4499,4447,4394,4341,4287,4233,4178,4123,4067,4011,3954,3896,3838,3779,3720,3660,3600,3539,3477,3415,3352,3288,3224,3159,3093,3027,2960,2892,2824,2754,2684,2614,2542,2470,2397,2323,2248,2173,2096,2019,1941,1862,1782,1701,1619,1536,1452,1367,1281,1195,1107,1018,928,836,744,651,556,460,363,265,165,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c39:Array ℕ:= #[4844,4797,4749,4701,4653,4604,4555,4505,4455,4405,4354,4303,4251,4199,4147,4094,4041,3987,3932,3878,3823,3767,3711,3654,3597,3539,3481,3423,3363,3304,3243,3183,3121,3060,2997,2934,2871,2806,2742,2676,2610,2544,2477,2409,2340,2271,2201,2131,2060,1988,1915,1842,1768,1694,1618,1542,1465,1387,1309,1229,1149,1068,987,904,820,736,651,565,477,389,300,210,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c40:Array ℕ:= #[4356,4307,4257,4207,4156,4105,4054,4002,3950,3897,3844,3791,3737,3683,3628,3573,3518,3462,3406,3349,3291,3234,3175,3117,3058,2998,2938,2877,2816,2754,2692,2629,2566,2502,2438,2373,2308,2242,2175,2108,2040,1972,1903,1834,1763,1693,1621,1549,1477,1403,1329,1255,1179,1103,1026,949,871,792,712,631,550,468,385,302,217,132,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c41:Array ℕ:= #[4027,3976,3925,3874,3822,3770,3718,3665,3611,3558,3504,3449,3394,3339,3283,3226,3170,3112,3055,2997,2938,2879,2819,2759,2699,2638,2576,2514,2452,2389,2325,2261,2197,2131,2066,1999,1932,1865,1797,1728,1659,1589,1519,1448,1376,1304,1231,1157,1083,1008,932,856,779,701,623,544,464,383,302,220,137,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c42:Array ℕ:= #[3680,3628,3576,3523,3470,3417,3363,3309,3255,3200,3144,3088,3032,2975,2918,2860,2802,2744,2685,2625,2565,2505,2444,2383,2321,2258,2196,2132,2068,2004,1939,1873,1807,1740,1673,1605,1537,1468,1398,1328,1257,1186,1114,1041,968,894,819,744,668,591,514,436,357,278,198,117,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c43:Array ℕ:= #[3313,3260,3207,3153,3099,3044,2989,2934,2878,2821,2765,2707,2650,2592,2533,2474,2415,2355,2294,2233,2172,2110,2048,1985,1922,1858,1793,1728,1663,1597,1530,1463,1395,1327,1258,1189,1119,1048,977,905,833,760,686,612,537,461,385,308,230,151,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c44:Array ℕ:= #[2926,2871,2817,2761,2706,2650,2593,2536,2479,2421,2363,2305,2246,2186,2126,2066,2005,1943,1881,1819,1756,1693,1629,1564,1499,1434,1368,1301,1234,1167,1098,1030,960,890,820,749,677,605,532,458,384,309,234,157,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c45:Array ℕ:= #[2515,2459,2403,2347,2289,2232,2174,2116,2057,1998,1938,1878,1817,1756,1695,1633,1570,1507,1444,1380,1315,1250,1185,1119,1052,985,917,849,780,711,641,571,499,428,355,282,209,135,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c46:Array ℕ:= #[2079,2022,1965,1906,1848,1789,1729,1670,1609,1548,1487,1425,1363,1301,1237,1174,1110,1045,980,914,848,781,714,646,578,509,439,369,299,228,156,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c47:Array ℕ:= #[1617,1558,1498,1439,1379,1318,1257,1195,1133,1071,1008,944,881,816,751,686,620,553,487,419,351,282,213,144,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c48:Array ℕ:= #[1124,1063,1002,941,879,816,754,690,627,562,498,432,367,300,234,166,98,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c49:Array ℕ:= #[598,535,473,409,346,281,217,152,86,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def c50:Array ℕ:= #[58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def row:ℕ→Array ℕ
 | 14=>c14
 | 15=>c15
 | 16=>c16
 | 17=>c17
 | 18=>c18
 | 19=>c19
 | 20=>c20
 | 21=>c21
 | 22=>c22
 | 23=>c23
 | 24=>c24
 | 25=>c25
 | 26=>c26
 | 27=>c27
 | 28=>c28
 | 29=>c29
 | 30=>c30
 | 31=>c31
 | 32=>c32
 | 33=>c33
 | 34=>c34
 | 35=>c35
 | 36=>c36
 | 37=>c37
 | 38=>c38
 | 39=>c39
 | 40=>c40
 | 41=>c41
 | 42=>c42
 | 43=>c43
 | 44=>c44
 | 45=>c45
 | 46=>c46
 | 47=>c47
 | 48=>c48
 | 49=>c49
 | 50=>c50
 | _=> #[]
def cut (r y:ℕ):ℕ:=min 11784 (((row r)[y-59]?).getD 11784)
def checkCut (r y:ℕ):Bool:=
 let c:=cut r y
 Nat.ble y (c+1) && (decide (c=11784) ||
   decide (DDX TG.cheap (rawFlag r (y-r) (c+1-y))))
theorem cut14:allN (fun v=>checkCut 14 (v+59)) 171=true:=by decide+kernel
theorem box14:allN (fun v=>corners 14 (v+59) (cut 14 (v+59))) 171=true:=by decide+kernel
theorem cut15:allN (fun v=>checkCut 15 (v+59)) 171=true:=by decide+kernel
theorem box15:allN (fun v=>corners 15 (v+59) (cut 15 (v+59))) 171=true:=by decide+kernel
theorem cut16:allN (fun v=>checkCut 16 (v+59)) 171=true:=by decide+kernel
theorem box16:allN (fun v=>corners 16 (v+59) (cut 16 (v+59))) 171=true:=by decide+kernel
theorem cut17:allN (fun v=>checkCut 17 (v+59)) 171=true:=by decide+kernel
theorem box17:allN (fun v=>corners 17 (v+59) (cut 17 (v+59))) 171=true:=by decide+kernel
theorem cut18:allN (fun v=>checkCut 18 (v+59)) 171=true:=by decide+kernel
theorem box18:allN (fun v=>corners 18 (v+59) (cut 18 (v+59))) 171=true:=by decide+kernel
theorem cut19:allN (fun v=>checkCut 19 (v+59)) 171=true:=by decide+kernel
theorem box19:allN (fun v=>corners 19 (v+59) (cut 19 (v+59))) 171=true:=by decide+kernel
theorem cut20:allN (fun v=>checkCut 20 (v+59)) 171=true:=by decide+kernel
theorem box20:allN (fun v=>corners 20 (v+59) (cut 20 (v+59))) 171=true:=by decide+kernel
theorem cut21:allN (fun v=>checkCut 21 (v+59)) 171=true:=by decide+kernel
theorem box21:allN (fun v=>corners 21 (v+59) (cut 21 (v+59))) 171=true:=by decide+kernel
theorem cut22:allN (fun v=>checkCut 22 (v+59)) 171=true:=by decide+kernel
theorem box22:allN (fun v=>corners 22 (v+59) (cut 22 (v+59))) 171=true:=by decide+kernel
theorem cut23:allN (fun v=>checkCut 23 (v+59)) 171=true:=by decide+kernel
theorem box23:allN (fun v=>corners 23 (v+59) (cut 23 (v+59))) 171=true:=by decide+kernel
theorem cut24:allN (fun v=>checkCut 24 (v+59)) 171=true:=by decide+kernel
theorem box24:allN (fun v=>corners 24 (v+59) (cut 24 (v+59))) 171=true:=by decide+kernel
theorem cut25:allN (fun v=>checkCut 25 (v+59)) 171=true:=by decide+kernel
theorem box25:allN (fun v=>corners 25 (v+59) (cut 25 (v+59))) 171=true:=by decide+kernel
theorem cut26:allN (fun v=>checkCut 26 (v+59)) 171=true:=by decide+kernel
theorem box26:allN (fun v=>corners 26 (v+59) (cut 26 (v+59))) 171=true:=by decide+kernel
theorem cut27:allN (fun v=>checkCut 27 (v+59)) 171=true:=by decide+kernel
theorem box27:allN (fun v=>corners 27 (v+59) (cut 27 (v+59))) 171=true:=by decide+kernel
theorem cut28:allN (fun v=>checkCut 28 (v+59)) 171=true:=by decide+kernel
theorem box28:allN (fun v=>corners 28 (v+59) (cut 28 (v+59))) 171=true:=by decide+kernel
theorem cut29:allN (fun v=>checkCut 29 (v+59)) 171=true:=by decide+kernel
theorem box29:allN (fun v=>corners 29 (v+59) (cut 29 (v+59))) 171=true:=by decide+kernel
theorem cut30:allN (fun v=>checkCut 30 (v+59)) 171=true:=by decide+kernel
theorem box30:allN (fun v=>corners 30 (v+59) (cut 30 (v+59))) 171=true:=by decide+kernel
theorem cut31:allN (fun v=>checkCut 31 (v+59)) 171=true:=by decide+kernel
theorem box31:allN (fun v=>corners 31 (v+59) (cut 31 (v+59))) 171=true:=by decide+kernel
theorem cut32:allN (fun v=>checkCut 32 (v+59)) 171=true:=by decide+kernel
theorem box32:allN (fun v=>corners 32 (v+59) (cut 32 (v+59))) 171=true:=by decide+kernel
theorem cut33:allN (fun v=>checkCut 33 (v+59)) 171=true:=by decide+kernel
theorem box33:allN (fun v=>corners 33 (v+59) (cut 33 (v+59))) 171=true:=by decide+kernel
theorem cut34:allN (fun v=>checkCut 34 (v+59)) 171=true:=by decide+kernel
theorem box34:allN (fun v=>corners 34 (v+59) (cut 34 (v+59))) 171=true:=by decide+kernel
theorem cut35:allN (fun v=>checkCut 35 (v+59)) 171=true:=by decide+kernel
theorem box35:allN (fun v=>corners 35 (v+59) (cut 35 (v+59))) 171=true:=by decide+kernel
theorem cut36:allN (fun v=>checkCut 36 (v+59)) 171=true:=by decide+kernel
theorem box36:allN (fun v=>corners 36 (v+59) (cut 36 (v+59))) 171=true:=by decide+kernel
theorem cut37:allN (fun v=>checkCut 37 (v+59)) 171=true:=by decide+kernel
theorem box37:allN (fun v=>corners 37 (v+59) (cut 37 (v+59))) 171=true:=by decide+kernel
theorem cut38:allN (fun v=>checkCut 38 (v+59)) 171=true:=by decide+kernel
theorem box38:allN (fun v=>corners 38 (v+59) (cut 38 (v+59))) 171=true:=by decide+kernel
theorem cut39:allN (fun v=>checkCut 39 (v+59)) 171=true:=by decide+kernel
theorem box39:allN (fun v=>corners 39 (v+59) (cut 39 (v+59))) 171=true:=by decide+kernel
theorem cut40:allN (fun v=>checkCut 40 (v+59)) 171=true:=by decide+kernel
theorem box40:allN (fun v=>corners 40 (v+59) (cut 40 (v+59))) 171=true:=by decide+kernel
theorem cut41:allN (fun v=>checkCut 41 (v+59)) 171=true:=by decide+kernel
theorem box41:allN (fun v=>corners 41 (v+59) (cut 41 (v+59))) 171=true:=by decide+kernel
theorem cut42:allN (fun v=>checkCut 42 (v+59)) 171=true:=by decide+kernel
theorem box42:allN (fun v=>corners 42 (v+59) (cut 42 (v+59))) 171=true:=by decide+kernel
theorem cut43:allN (fun v=>checkCut 43 (v+59)) 171=true:=by decide+kernel
theorem box43:allN (fun v=>corners 43 (v+59) (cut 43 (v+59))) 171=true:=by decide+kernel
theorem cut44:allN (fun v=>checkCut 44 (v+59)) 171=true:=by decide+kernel
theorem box44:allN (fun v=>corners 44 (v+59) (cut 44 (v+59))) 171=true:=by decide+kernel
theorem cut45:allN (fun v=>checkCut 45 (v+59)) 171=true:=by decide+kernel
theorem box45:allN (fun v=>corners 45 (v+59) (cut 45 (v+59))) 171=true:=by decide+kernel
theorem cut46:allN (fun v=>checkCut 46 (v+59)) 171=true:=by decide+kernel
theorem box46:allN (fun v=>corners 46 (v+59) (cut 46 (v+59))) 171=true:=by decide+kernel
theorem cut47:allN (fun v=>checkCut 47 (v+59)) 171=true:=by decide+kernel
theorem box47:allN (fun v=>corners 47 (v+59) (cut 47 (v+59))) 171=true:=by decide+kernel
theorem cut48:allN (fun v=>checkCut 48 (v+59)) 171=true:=by decide+kernel
theorem box48:allN (fun v=>corners 48 (v+59) (cut 48 (v+59))) 171=true:=by decide+kernel
theorem cut49:allN (fun v=>checkCut 49 (v+59)) 171=true:=by decide+kernel
theorem box49:allN (fun v=>corners 49 (v+59) (cut 49 (v+59))) 171=true:=by decide+kernel
theorem cut50:allN (fun v=>checkCut 50 (v+59)) 171=true:=by decide+kernel
theorem box50:allN (fun v=>corners 50 (v+59) (cut 50 (v+59))) 171=true:=by decide+kernel
theorem cut_checked (r y:ℕ) (hr:14≤r) (hR:r≤50) (hy:59≤y) (hY:y≤229):checkCut r y=true:=by
 interval_cases r
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 14 (v+59)) 171 cut14 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 15 (v+59)) 171 cut15 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 16 (v+59)) 171 cut16 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 17 (v+59)) 171 cut17 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 18 (v+59)) 171 cut18 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 19 (v+59)) 171 cut19 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 20 (v+59)) 171 cut20 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 21 (v+59)) 171 cut21 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 22 (v+59)) 171 cut22 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 23 (v+59)) 171 cut23 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 24 (v+59)) 171 cut24 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 25 (v+59)) 171 cut25 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 26 (v+59)) 171 cut26 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 27 (v+59)) 171 cut27 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 28 (v+59)) 171 cut28 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 29 (v+59)) 171 cut29 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 30 (v+59)) 171 cut30 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 31 (v+59)) 171 cut31 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 32 (v+59)) 171 cut32 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 33 (v+59)) 171 cut33 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 34 (v+59)) 171 cut34 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 35 (v+59)) 171 cut35 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 36 (v+59)) 171 cut36 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 37 (v+59)) 171 cut37 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 38 (v+59)) 171 cut38 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 39 (v+59)) 171 cut39 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 40 (v+59)) 171 cut40 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 41 (v+59)) 171 cut41 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 42 (v+59)) 171 cut42 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 43 (v+59)) 171 cut43 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 44 (v+59)) 171 cut44 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 45 (v+59)) 171 cut45 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 46 (v+59)) 171 cut46 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 47 (v+59)) 171 cut47 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 48 (v+59)) 171 cut48 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 49 (v+59)) 171 cut49 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>checkCut 50 (v+59)) 171 cut50 (y-59) (by omega)
theorem FFN (r y:ℕ) (hr:14≤r) (hR:r≤50) (hy:59≤y) (hY:y≤229):corners r y (cut r y)=true:=by
 interval_cases r
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 14 (v+59) (cut 14 (v+59))) 171 box14 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 15 (v+59) (cut 15 (v+59))) 171 box15 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 16 (v+59) (cut 16 (v+59))) 171 box16 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 17 (v+59) (cut 17 (v+59))) 171 box17 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 18 (v+59) (cut 18 (v+59))) 171 box18 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 19 (v+59) (cut 19 (v+59))) 171 box19 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 20 (v+59) (cut 20 (v+59))) 171 box20 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 21 (v+59) (cut 21 (v+59))) 171 box21 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 22 (v+59) (cut 22 (v+59))) 171 box22 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 23 (v+59) (cut 23 (v+59))) 171 box23 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 24 (v+59) (cut 24 (v+59))) 171 box24 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 25 (v+59) (cut 25 (v+59))) 171 box25 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 26 (v+59) (cut 26 (v+59))) 171 box26 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 27 (v+59) (cut 27 (v+59))) 171 box27 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 28 (v+59) (cut 28 (v+59))) 171 box28 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 29 (v+59) (cut 29 (v+59))) 171 box29 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 30 (v+59) (cut 30 (v+59))) 171 box30 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 31 (v+59) (cut 31 (v+59))) 171 box31 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 32 (v+59) (cut 32 (v+59))) 171 box32 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 33 (v+59) (cut 33 (v+59))) 171 box33 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 34 (v+59) (cut 34 (v+59))) 171 box34 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 35 (v+59) (cut 35 (v+59))) 171 box35 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 36 (v+59) (cut 36 (v+59))) 171 box36 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 37 (v+59) (cut 37 (v+59))) 171 box37 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 38 (v+59) (cut 38 (v+59))) 171 box38 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 39 (v+59) (cut 39 (v+59))) 171 box39 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 40 (v+59) (cut 40 (v+59))) 171 box40 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 41 (v+59) (cut 41 (v+59))) 171 box41 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 42 (v+59) (cut 42 (v+59))) 171 box42 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 43 (v+59) (cut 43 (v+59))) 171 box43 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 44 (v+59) (cut 44 (v+59))) 171 box44 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 45 (v+59) (cut 45 (v+59))) 171 box45 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 46 (v+59) (cut 46 (v+59))) 171 box46 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 47 (v+59) (cut 47 (v+59))) 171 box47 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 48 (v+59) (cut 48 (v+59))) 171 box48 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 49 (v+59) (cut 49 (v+59))) 171 box49 (y-59) (by omega)
 · simpa only [Nat.sub_add_cancel hy] using allN_sound (fun v=>corners 50 (v+59) (cut 50 (v+59))) 171 box50 (y-59) (by omega)


end BU

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace MH
open RCN095
open DY KZ FV
open Lower80899.AMY
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
local notation "NN" =>BU.num
local notation "NZ" =>FI.num
local notation "PN" =>BU.pair
local notation "PZ" =>FI.pair

theorem num_cast (L U S r y t:ℕ) (hr:1≤r):
 (NN L U S r y t:ℤ)=NZ L U S r y t:=by
 have hs:((2*r-1:ℕ):ℤ)=2*(r:ℤ)-1:=by omega
 unfold BU.num FI.num
 simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,hs]

theorem num_zero (L U S:ℤ):NZ L U S 0 0 0=0:=by
 simp [FI.num]

theorem FKP (L U S r y t:ℕ)
 (hr:1≤r∨r=0∧y=0∧t=0):(NN L U S r y t:ℤ)=NZ L U S r y t:=by
 rcases hr with hr | ⟨rfl,rfl,rfl⟩
 · exact num_cast L U S r y t hr
 · simp [BU.num,FI.num]

theorem pair_cast (r y t:ℕ) (hy:y≤229) (ht:t≤11784):
 (PN r y t:ℤ)=if r<50 then PZ r y t else 0:=by
 by_cases hr:r<50
 · simp only [BU.pair,if_pos hr]
   rw [num_cast _ _ _ _ _ _ (by omega)]
   unfold FI.pair
   rw [Nat.cast_sub (by omega:t≤11785),Nat.cast_sub (by omega:y≤348),
     Nat.cast_sub (by omega:r≤78),Nat.cast_sub (by omega:r≤50),
     Nat.cast_sub hy,Nat.cast_sub (by omega:t≤17230)]
   norm_num only [Nat.cast_ofNat]
 · simp only [BU.pair,if_neg hr,Nat.cast_zero]

theorem charge_eq (L U S r y t:ℕ):
 CY.cost L U S r y t=NN L U S r y t/50164:=by
 rw [CY.cost_eq,CY.num_formula]
 rfl

theorem pair_cap_eq (r y t:ℕ):QQ.cap r y t=PN r y t/50164:=by
 by_cases hr:r<50
 · simp only [QQ.cap,BU.pair,if_pos hr]
   change CY.cost (11785-t) (348-y) (78-r) (50-r) (229-y) (17230-t)=_
   exact charge_eq _ _ _ _ _ _
 · simp [QQ.cap,BU.pair,hr]

theorem floor_three (A B C D:ℕ) (h:A+B+C≤D):
 A/50164+B/50164+C/50164≤D/50164:=by
 apply (Nat.le_div_iff_mul_le (by decide)).2
 have hA:=Nat.div_mul_le_self A 50164
 have hB:=Nat.div_mul_le_self B 50164
 have hC:=Nat.div_mul_le_self C 50164
 nlinarith only [h,hA,hB,hC]

theorem FXK (p:FlagDegree)
 (hr:14≤p.all) (hR:p.all≤50) (hy:59≤middle p) (hY:middle p≤229)
 (ht:total p≤11784) (hs: ¬TG.cheap.Routeable p):
 total p≤BU.cut p.all (middle p):=by
 have hc:=BU.cut_checked p.all (middle p) hr hR hy hY
 simp only [BU.checkCut,Bool.and_eq_true,Nat.ble_eq,
   Bool.or_eq_true,decide_eq_true_eq] at hc
 rcases hc.2 with he | hf
 · omega
 · by_contra hn
   have hz:BU.cut p.all (middle p)+1-middle p≤p.zOnly:=by
     unfold middle total at*
     omega
   have htotal:p.all+(middle p-p.all)+p.zOnly≤TG.cheap.totalCap:=by
     dsimp only [TG.cheap]
     unfold middle total at*
     omega
   have hm:=Lower80899.PhaseRows.DZI TG.cheap hz htotal
     ((EUB _ _).mp hf)
   apply hs
   simpa only [rawFlag,middle,Nat.add_sub_cancel_right] using hm
theorem DTQ (r y t rv yv tv wr wy wt:ℕ)
 (hr:r<50) (hRR:r≤rv) (hRW:rv≤wr)
 (hYV:y≤yv) (hYW:yv≤wy) (hY:wy≤229)
 (hTV:t≤tv) (hTW:tv≤wt) (hT:wt≤11784)
 (hB:r<rv∨rv=r∧yv=y∧tv=t)
 (hA:rv<wr∨wr=rv∧wy=yv∧wt=tv):
 FI.wholeMargin r y t rv yv tv
   (if wr<50 then 1 else 0) wr wy wt=
 (PN r y t:ℤ)-(NN 88902 1382 308 (rv-r) (yv-y) (tv-t):ℤ)-
   (NN 18000 348 78 (wr-rv) (wy-yv) (wt-tv):ℤ)-(PN wr wy wt:ℤ):=by
 have hb:1≤rv-r∨rv-r=0∧yv-y=0∧tv-t=0:=by
  rcases hB with hb | ⟨rfl,rfl,rfl⟩<;>omega
 have ha:1≤wr-rv∨wr-rv=0∧wy-yv=0∧wt-tv=0:=by
  rcases hA with ha | ⟨rfl,rfl,rfl⟩<;>omega
 rw [pair_cast r y t (hYV.trans (hYW.trans hY)) (hTV.trans (hTW.trans hT)),
   pair_cast wr wy wt hY hT,FKP _ _ _ _ _ _ hb,FKP _ _ _ _ _ _ ha]
 rw [Nat.cast_sub hRR,Nat.cast_sub hYV,Nat.cast_sub hTV,
   Nat.cast_sub hRW,Nat.cast_sub hYW,Nat.cast_sub hTW]
 unfold FI.wholeMargin
 by_cases hw:wr<50
 · simp only [if_pos hr,if_pos hw]
   norm_num only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]<;>ring
 · simp only [if_pos hr,if_neg hw]
   norm_num only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]<;>ring




end MH

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace AOO
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def wr (rv k:ℕ):=if k/4=0 then rv else if k/4=1 then rv+1 else if k/4=2 then 49 else 50
def wy (yv k:ℕ):=if k/2%2=0 then yv else 229
def vt (t ct j:ℕ):=if j=0 then t else ct
def wt (tv k:ℕ):=if k%2=0 then tv else 11784
def Good (rv k:ℕ):Prop:=
 wr rv k≤50∧rv≤wr rv k∧(k/4≠0→ rv<wr rv k)∧
 (k/4=0→k/2%2=0∧k%2=0)

def fixedCase (rv yv ct j k:ℕ):ℤ→ℤ→ℤ→ℤ:=
 FI.fixedMargin rv yv (wr rv k) (wy yv k)
  (if j=0 then 1 else 0) (if j=0 then 0 else (ct:ℤ))
  (if k%2=0 then 1 else 0) (if k%2=0 then 0 else 11784)
  (if wr rv k<50 then 1 else 0)

theorem fixed_at_nat (rv yv ct j k r y t:ℕ):
 fixedCase rv yv ct j k r y t=
 FI.wholeMargin r y t rv yv (vt t ct j)
  (if wr rv k<50 then 1 else 0) (wr rv k) (wy yv k) (wt (vt t ct j) k):=by
 by_cases hj:j=0<;>by_cases hk:k%2=0<;>
  simp [fixedCase,vt,wt,FI.fixedMargin,FI.wholeMargin,hj,hk]

theorem core_bounds (rv yv ct i:ℕ) (hr:14≤rv) (hy:59≤yv) (ht:3611≤ct):
 let (r,y,t):=BU.core rv yv ct i
 13≤r∧r≤17∧r<rv∧59≤y∧y≤76∧y≤yv∧3611≤t∧t≤4879∧t≤ct:=by
 dsimp only [BU.core]
 split_ifs<;>omega

theorem GJJ (rv yv i j k:ℕ)
 (hr:14≤rv) (hR:rv≤50) (hy:59≤yv) (hY:yv≤229)
 (ht:3611≤BU.cut rv yv) (hi:i<8) (hj:j<2) (hk:k<16):
 BU.corner rv yv (BU.cut rv yv) i j k=true:=by
 have hc:=BU.FFN rv yv hr hR hy hY
 have hn: ¬(min 17 (rv-1)<13∨min 76 yv<59∨min 4879 (BU.cut rv yv)<3611):=by omega
 simp only [BU.corners,if_neg hn] at hc
 have h1:=BU.allN_sound _ 8 hc i hi
 have h2:=BU.allN_sound _ 2 h1 j hj
 exact BU.allN_sound _ 16 h2 k hk

theorem corner_le (rv yv i j k:ℕ)
 (hr:14≤rv) (hR:rv≤50) (hy:59≤yv) (hY:yv≤229)
 (ht:3611≤BU.cut rv yv) (hi:i<8) (hj:j<2) (hk:k<16) (hg:Good rv k):
 let ct:=BU.cut rv yv
 let (r,y,t):=BU.core rv yv ct i
 BU.num 88902 1382 308 (rv-r) (yv-y) (vt t ct j-t)+
 BU.num 18000 348 78 (wr rv k-rv) (wy yv k-yv) (wt (vt t ct j) k-vt t ct j)+
 BU.pair (wr rv k) (wy yv k) (wt (vt t ct j) k)≤BU.pair r y t:=by
 have hc:=GJJ rv yv i j k hr hR hy hY ht hi hj hk
 have hn: ¬(50<wr rv k∨wr rv k<rv∨
   (k/4≠0∧wr rv k=rv)∨(k/4=0∧(k/2%2≠0∨k%2≠0))):=by
  rcases hg with ⟨ha,hb,hc,hd⟩
  omega
 dsimp only [BU.corner] at hc
 change (if 50<wr rv k∨wr rv k<rv∨
   (k/4≠0∧wr rv k=rv)∨(k/4=0∧(k/2%2≠0∨k%2≠0)) then true else
   Nat.ble _ _)=true at hc
 rw [if_neg hn] at hc
 exact Nat.le_of_ble_eq_true hc

theorem AGJ (rv yv i j k:ℕ)
 (hr:14≤rv) (hR:rv≤50) (hy:59≤yv) (hY:yv≤229)
 (ht:3611≤BU.cut rv yv) (hi:i<8) (hj:j<2) (hk:k<16) (hg:Good rv k):
 let (r,y,t):=BU.core rv yv (BU.cut rv yv) i
 0≤fixedCase rv yv (BU.cut rv yv) j k r y t:=by
 rcases he:BU.core rv yv (BU.cut rv yv) i with ⟨r,y,t⟩
 have hb:=core_bounds rv yv (BU.cut rv yv) i hr hy ht
 rw [he] at hb
 dsimp only at hb
 rcases hb with ⟨hrl,hrh,hrr,hyl,hyh,hyy,htl,hth,htt⟩
 have hc:=corner_le rv yv i j k hr hR hy hY ht hi hj hk hg
 dsimp only at hc
 rw [he] at hc
 dsimp only at hc
 dsimp only
 rw [fixed_at_nat]
 have hct:BU.cut rv yv≤11784:=Nat.min_le_left _ _
 have htv:t≤vt t (BU.cut rv yv) j∧vt t (BU.cut rv yv) j≤11784:=by
  unfold vt
  split_ifs<;>omega
 have hyw:yv≤wy yv k∧wy yv k≤229:=by
  unfold wy
  split_ifs<;>omega
 have htw:vt t (BU.cut rv yv) j≤wt (vt t (BU.cut rv yv) j) k∧
   wt (vt t (BU.cut rv yv) j) k≤11784:=by
  unfold wt
  split_ifs<;>omega
 have ha:rv<wr rv k∨wr rv k=rv∧wy yv k=yv∧
   wt (vt t (BU.cut rv yv) j) k=vt t (BU.cut rv yv) j:=by
  by_cases hz:k/4=0
  · have hh:=hg.2.2.2 hz
    exact Or.inr ⟨by simp [wr,hz],by simp [wy,hh.1],by simp [wt,hh.2]⟩
  · exact Or.inl (hg.2.2.1 hz)
 rw [MH.DTQ r y t rv yv (vt t (BU.cut rv yv) j)
   (wr rv k) (wy yv k) (wt (vt t (BU.cut rv yv) j) k)
   (by omega) (by omega) hg.2.1 hyy hyw.1 hyw.2 htv.1 htw.1 htw.2 (Or.inl hrr) ha]
 have hz:(BU.num 88902 1382 308 (rv-r) (yv-y) (vt t (BU.cut rv yv) j-t):ℤ)+
   (BU.num 18000 348 78 (wr rv k-rv) (wy yv k-yv)
     (wt (vt t (BU.cut rv yv) j) k-vt t (BU.cut rv yv) j):ℤ)+
   (BU.pair (wr rv k) (wy yv k) (wt (vt t (BU.cut rv yv) j) k):ℤ)≤(BU.pair r y t:ℤ):=by
  exact_mod_cast hc
 linarith only [hz]

theorem fixed_nonneg (rv yv j k r y t:ℕ)
 (hR:rv≤50) (hY:yv≤229) (hj:j<2) (hk:k<16) (hg:Good rv k)
 (hrl:13≤r) (hrh:r≤17) (hrv:r<rv)
 (hyl:59≤y) (hyh:y≤76) (hyv:y≤yv)
 (htl:3611≤t) (hth:t≤4879) (htt:t≤BU.cut rv yv):
 0≤fixedCase rv yv (BU.cut rv yv) j k r y t:=by
 have hr:14≤rv:=by omega
 have hy:59≤yv:=by omega
 have ht:3611≤BU.cut rv yv:=by omega
 have hrr:r≤min 17 (rv-1):=by omega
 have hyy:y≤min 76 yv:=by omega
 have htte:t≤min 4879 (BU.cut rv yv):=by omega
 refine FI.box_nonneg
   (fixedCase rv yv (BU.cut rv yv) j k)
   (by exact FI.fixed_affine _ _ _ _ _ _ _ _ _)
   13 ((min 17 (rv-1):ℕ):ℤ) 59 ((min 76 yv:ℕ):ℤ)
   3611 ((min 4879 (BU.cut rv yv):ℕ):ℤ)
   r y t (by exact_mod_cast hrl) (by exact_mod_cast hrr)
   (by exact_mod_cast hyl) (by exact_mod_cast hyy) (by exact_mod_cast htl) (by exact_mod_cast htte) ?_
 intro rr yy tt hrr hyy htt
 rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
 · simpa [BU.core] using AGJ rv yv 0 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 4 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 2 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 6 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 1 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 5 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 3 j k hr hR hy hY ht (by decide) hj hk hg
 · simpa [BU.core] using AGJ rv yv 7 j k hr hR hy hY ht (by decide) hj hk hg
theorem FWW (rv yv k r y t tv:ℕ)
 (hR:rv≤50) (hY:yv≤229) (hk:k<16) (hg:Good rv k)
 (hrl:13≤r) (hrh:r≤17) (hrv:r<rv)
 (hyl:59≤y) (hyh:y≤76) (hyv:y≤yv)
 (htl:3611≤t) (hth:t≤4879) (htv:t≤tv)
 (hcut:tv≤BU.cut rv yv):
 0≤FI.wholeMargin r y t rv yv tv
   (if wr rv k<50 then 1 else 0) (wr rv k) (wy yv k) (wt tv k):=by
 let aw:ℤ:=if k%2=0 then 1 else 0
 let bw:ℤ:=if k%2=0 then 0 else 11784
 let pw:ℤ:=if wr rv k<50 then 1 else 0
 let f:ℤ→ℤ:=fun x=>FI.wholeMargin r y t rv yv x pw
   (wr rv k) (wy yv k) (aw*x+bw)
 have hl:0≤f t:=by
  have h:=fixed_nonneg rv yv 0 k r y t hR hY (by decide) hk hg
    hrl hrh hrv hyl hyh hyv htl hth (htv.trans hcut)
  simpa [f,aw,bw,pw,fixedCase,FI.fixedMargin,
    FI.wholeMargin] using h
 have hh:0≤f (BU.cut rv yv):=by
  have h:=fixed_nonneg rv yv 1 k r y t hR hY (by decide) hk hg
    hrl hrh hrv hyl hyh hyv htl hth (htv.trans hcut)
  simpa [f,aw,bw,pw,fixedCase,FI.fixedMargin,
    FI.wholeMargin] using h
 have hf (x:ℤ):f x=(f 1-f 0)*x+f 0:=by
  simpa only [f,mul_one,mul_zero,zero_add] using
    FI.tv_affine r y t rv yv (wr rv k) (wy yv k) aw bw pw x
 have he:=FI.DJM f hf
   t (BU.cut rv yv) tv
   (by exact_mod_cast htv) (by exact_mod_cast hcut) hl hh
 by_cases hz:k%2=0
 · simpa [f,aw,bw,pw,wt,hz] using he
 · simpa [f,aw,bw,pw,wt,hz] using he



end AOO

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace BXN
open AOO
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem DRQ (r y t rv yv tv rw yw tw:ℕ)
 (hRV:rv≤50) (hYV:yv≤229)
 (hrl:13≤r) (hrh:r≤17) (hrv:r<rv)
 (hyl:59≤y) (hyh:y≤76) (hyv:y≤yv)
 (htl:3611≤t) (hth:t≤4879) (htv:t≤tv)
 (hcut:tv≤BU.cut rv yv)
 (hRW:rw≤50) (hYW:yw≤229) (hTW:tw≤11784)
 (hry:rv≤rw) (hyy:yv≤yw) (htt:tv≤tw)
 (hA:rv<rw∨rw=rv∧yw=yv∧tw=tv):
 0≤FI.wholeMargin r y t rv yv tv
   (if rw<50 then 1 else 0) rw yw tw:=by
 have pick (k:ℕ) (hk:k<16) (hg:Good rv k):=
   FWW rv yv k r y t tv hRV hYV hk hg
     hrl hrh hrv hyl hyh hyv htl hth htv hcut
 rcases hA with ha | ⟨rfl,rfl,rfl⟩
 · by_cases hw50:rw=50
   · subst rw
     have hrv49:rv≤49:=by omega
     change 0≤FI.wholeMargin r y t rv yv tv 0 50 yw tw
     refine FI.box_nonneg
       (FI.wholeMargin r y t rv yv tv 0)
       (FI.whole_affine _ _ _ _ _ _ _)
       50 50 yv 229 tv 11784 50 yw tw (by omega) (by omega)
       (by exact_mod_cast hyy) (by exact_mod_cast hYW)
       (by exact_mod_cast htt) (by exact_mod_cast hTW) ?_
     intro rr yy tt hrr hyy htt
     rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
     · simpa [wr,wy,wt] using pick 12 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 13 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 14 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 15 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 12 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 13 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 14 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt] using pick 15 (by decide) (by norm_num [Good,wr];omega)
   · have hwr:rw<50:=by omega
     have hrv48:rv≤48:=by omega
     have hrvplus:rv+1<50:=by omega
     rw [if_pos hwr]
     refine FI.box_nonneg
       (FI.wholeMargin r y t rv yv tv 1)
       (FI.whole_affine _ _ _ _ _ _ _)
       ((rv+1:ℕ):ℤ) 49 yv 229 tv 11784 rw yw tw
       (by exact_mod_cast (show rv+1≤rw by omega)) (by exact_mod_cast (show rw≤49 by omega))
       (by exact_mod_cast hyy) (by exact_mod_cast hYW)
       (by exact_mod_cast htt) (by exact_mod_cast hTW) ?_
     intro rr yy tt hrr hyy htt
     rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
     · simpa [wr,wy,wt,hrvplus] using pick 4 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 5 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 6 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 7 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 8 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 9 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 10 (by decide) (by norm_num [Good,wr];omega)
     · simpa [wr,wy,wt,hrvplus] using pick 11 (by decide) (by norm_num [Good,wr];omega)
 · simpa [wr,wy,wt] using pick 0 (by decide) (by norm_num [Good,wr];omega)

theorem charges_le (r y t rv yv tv rw yw tw:ℕ)
 (hRV:rv≤50) (hYV:yv≤229)
 (hrl:13≤r) (hrh:r≤17) (hrv:r<rv)
 (hyl:59≤y) (hyh:y≤76) (hyv:y≤yv)
 (htl:3611≤t) (hth:t≤4879) (htv:t≤tv)
 (hcut:tv≤BU.cut rv yv)
 (hRW:rw≤50) (hYW:yw≤229) (hTW:tw≤11784)
 (hry:rv≤rw) (hyy:yv≤yw) (htt:tv≤tw)
 (hA:rv<rw∨rw=rv∧yw=yv∧tw=tv):
 CY.cost 18000 348 78 (rw-rv) (yw-yv) (tw-tv)+
 CY.cost 88902 1382 308 (rv-r) (yv-y) (tv-t)+
 QQ.cap rw yw tw≤QQ.cap r y t:=by
 have hm:=DRQ r y t rv yv tv rw yw tw hRV hYV
   hrl hrh hrv hyl hyh hyv htl hth htv hcut hRW hYW hTW hry hyy htt hA
 rw [MH.DTQ r y t rv yv tv rw yw tw
   (by omega) (by omega) hry hyv hyy hYW htv htt hTW (Or.inl hrv) hA] at hm
 have hz:(BU.num 88902 1382 308 (rv-r) (yv-y) (tv-t):ℤ)+
   (BU.num 18000 348 78 (rw-rv) (yw-yv) (tw-tv):ℤ)+
   (BU.pair rw yw tw:ℤ)≤(BU.pair r y t:ℤ):=by
  linarith only [hm]
 have hn:BU.num 88902 1382 308 (rv-r) (yv-y) (tv-t)+
   BU.num 18000 348 78 (rw-rv) (yw-yv) (tw-tv)+
   BU.pair rw yw tw≤BU.pair r y t:=by
  exact_mod_cast hz
 have hd:=MH.floor_three _ _ _ _ hn
 rw [MH.charge_eq,MH.charge_eq,
   MH.pair_cap_eq,MH.pair_cap_eq]
 simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hd


end BXN

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace CCD
open AOO
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def core (i:ℕ):ℕ × ℕ × ℕ:=
 (if i%2=0 then 13 else 17,if i/2%2=0 then 59 else 76,
  if i/4%2=0 then 3611 else 4879)
def ewr (r k:ℕ):=if k/4=0 then r+1 else if k/4=1 then 49 else 50
def emptyCase (k:ℕ):ℤ→ℤ→ℤ→ℤ:=
 FI.emptyMargin
  (if k/4=0 then 1 else 0) (if k/4=0 then 1 else if k/4=1 then 49 else 50)
  (if k/2%2=0 then 1 else 0) (if k/2%2=0 then 0 else 229)
  (if k%2=0 then 1 else 0) (if k%2=0 then 0 else 11784)
  (if k/4=2 then 0 else 1)

theorem at_nat (k r y t:ℕ) (hk:k<12) (hr:r≤17):
 emptyCase k r y t=FI.wholeMargin r y t r y t
  (if ewr r k<50 then 1 else 0) (ewr r k) (wy y k) (wt t k):=by
 have hp:r+1<50:=by omega
 interval_cases k<;>
  simp [emptyCase,ewr,wy,wt,FI.emptyMargin,
    FI.wholeMargin,MH.num_zero,hp]

theorem core_bounds (i:ℕ):
 let (r,y,t):=core i
 13≤r∧r≤17∧59≤y∧y≤76∧3611≤t∧t≤4879:=by
 dsimp only [core]
 split_ifs<;>omega

theorem corner_le (i k:ℕ) (hi:i<8) (hk:k<12):
 let (r,y,t):=core i
 BU.num 18000 348 78 (ewr r k-r) (wy y k-y) (wt t k-t)+
 BU.pair (ewr r k) (wy y k) (wt t k)≤BU.pair r y t:=by
 have h1:=BU.allN_sound _ 8 BU.GWO i hi
 have h2:=BU.allN_sound _ 12 h1 k hk
 simpa only [BU.emptyCorner,core,ewr,wy,wt,Nat.ble_eq] using h2

theorem BME (i k:ℕ) (hi:i<8) (hk:k<12):
 let (r,y,t):=core i
 0≤emptyCase k r y t:=by
 rcases he:core i with ⟨r,y,t⟩
 have hb:=core_bounds i
 rw [he] at hb
 dsimp only at hb
 rcases hb with ⟨hrl,hrh,hyl,hyh,htl,hth⟩
 have hc:=corner_le i k hi hk
 rw [he] at hc
 dsimp only at hc
 dsimp only
 rw [at_nat k r y t hk hrh]
 have hrw:r<ewr r k∧ewr r k≤50:=by
  interval_cases k<;>simp [ewr]<;>omega
 have hyw:y≤wy y k∧wy y k≤229:=by
  unfold wy
  split_ifs<;>omega
 have htw:t≤wt t k∧wt t k≤11784:=by
  unfold wt
  split_ifs<;>omega
 rw [MH.DTQ r y t r y t (ewr r k) (wy y k) (wt t k)
   (by omega) (by omega) (by omega) (by omega) hyw.1 hyw.2 (by omega) htw.1 htw.2
   (Or.inr ⟨rfl,rfl,rfl⟩) (Or.inl hrw.1)]
 have hz:(BU.num 18000 348 78 (ewr r k-r) (wy y k-y) (wt t k-t):ℤ)+
   (BU.pair (ewr r k) (wy y k) (wt t k):ℤ)≤
   (BU.pair r y t:ℤ):=by exact_mod_cast hc
 have h0:BU.num 88902 1382 308 0 0 0=0:=by decide+kernel
 simp only [Nat.sub_self,h0,Nat.cast_zero,sub_zero]
 linarith only [hz]

theorem fixed_nonneg (k r y t:ℕ) (hk:k<12)
 (hrl:13≤r) (hrh:r≤17) (hyl:59≤y) (hyh:y≤76) (htl:3611≤t) (hth:t≤4879):
 0≤emptyCase k r y t:=by
 refine FI.box_nonneg (emptyCase k)
   (by exact FI.empty_affine _ _ _ _ _ _ _)
   13 17 59 76 3611 4879 r y t
   (by exact_mod_cast hrl) (by exact_mod_cast hrh)
   (by exact_mod_cast hyl) (by exact_mod_cast hyh)
   (by exact_mod_cast htl) (by exact_mod_cast hth) ?_
 intro rr yy tt hrr hyy htt
 rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
 · simpa [core] using BME 0 k (by decide) hk
 · simpa [core] using BME 4 k (by decide) hk
 · simpa [core] using BME 2 k (by decide) hk
 · simpa [core] using BME 6 k (by decide) hk
 · simpa [core] using BME 1 k (by decide) hk
 · simpa [core] using BME 5 k (by decide) hk
 · simpa [core] using BME 3 k (by decide) hk
 · simpa [core] using BME 7 k (by decide) hk
theorem DRQ (r y t rw yw tw:ℕ)
 (hrl:13≤r) (hrh:r≤17) (hyl:59≤y) (hyh:y≤76)
 (htl:3611≤t) (hth:t≤4879)
 (hRW:rw≤50) (hYW:yw≤229) (hTW:tw≤11784)
 (hyy:y≤yw) (htt:t≤tw)
 (hA:r<rw∨rw=r∧yw=y∧tw=t):
 0≤FI.wholeMargin r y t r y t
   (if rw<50 then 1 else 0) rw yw tw:=by
 have pick (k:ℕ) (hk:k<12):
   0≤FI.wholeMargin r y t r y t
     (if ewr r k<50 then 1 else 0) (ewr r k) (wy y k) (wt t k):=by
  have h:=fixed_nonneg k r y t hk hrl hrh hyl hyh htl hth
  rwa [at_nat k r y t hk hrh] at h
 rcases hA with ha | ⟨rfl,rfl,rfl⟩
 · by_cases hw50:rw=50
   · subst rw
     change 0≤FI.wholeMargin r y t r y t 0 50 yw tw
     refine FI.box_nonneg
       (FI.wholeMargin r y t r y t 0)
       (FI.whole_affine _ _ _ _ _ _ _)
       50 50 y 229 t 11784 50 yw tw (by omega) (by omega)
       (by exact_mod_cast hyy) (by exact_mod_cast hYW)
       (by exact_mod_cast htt) (by exact_mod_cast hTW) ?_
     intro rr yy tt hrr hyy htt
     rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
     · simpa [ewr,wy,wt] using pick 8 (by decide)
     · simpa [ewr,wy,wt] using pick 9 (by decide)
     · simpa [ewr,wy,wt] using pick 10 (by decide)
     · simpa [ewr,wy,wt] using pick 11 (by decide)
     · simpa [ewr,wy,wt] using pick 8 (by decide)
     · simpa [ewr,wy,wt] using pick 9 (by decide)
     · simpa [ewr,wy,wt] using pick 10 (by decide)
     · simpa [ewr,wy,wt] using pick 11 (by decide)
   · have hwr:rw<50:=by omega
     have hrplus:r+1<50:=by omega
     rw [if_pos hwr]
     refine FI.box_nonneg
       (FI.wholeMargin r y t r y t 1)
       (FI.whole_affine _ _ _ _ _ _ _)
       ((r+1:ℕ):ℤ) 49 y 229 t 11784 rw yw tw
       (by exact_mod_cast (show r+1≤rw by omega)) (by exact_mod_cast (show rw≤49 by omega))
       (by exact_mod_cast hyy) (by exact_mod_cast hYW)
       (by exact_mod_cast htt) (by exact_mod_cast hTW) ?_
     intro rr yy tt hrr hyy htt
     rcases hrr with rfl | rfl<;>rcases hyy with rfl | rfl<;>rcases htt with rfl | rfl
     · simpa [ewr,wy,wt,hrplus] using pick 0 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 1 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 2 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 3 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 4 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 5 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 6 (by decide)
     · simpa [ewr,wy,wt,hrplus] using pick 7 (by decide)
 · have hr:rw<50:=by omega
   simp [FI.wholeMargin,MH.num_zero,hr]

theorem charges_le (r y t rw yw tw:ℕ)
 (hrl:13≤r) (hrh:r≤17) (hyl:59≤y) (hyh:y≤76)
 (htl:3611≤t) (hth:t≤4879)
 (hRW:rw≤50) (hYW:yw≤229) (hTW:tw≤11784)
 (hyy:y≤yw) (htt:t≤tw)
 (hA:r<rw∨rw=r∧yw=y∧tw=t):
 CY.cost 18000 348 78 (rw-r) (yw-y) (tw-t)+
 QQ.cap rw yw tw≤QQ.cap r y t:=by
 have hm:=DRQ r y t rw yw tw hrl hrh hyl hyh htl hth hRW hYW hTW hyy htt hA
 have hrw:r≤rw:=by rcases hA with ha | ⟨rfl,_,_⟩<;>omega
 rw [MH.DTQ r y t r y t rw yw tw
   (by omega) (by omega) hrw (by omega) hyy hYW (by omega) htt hTW
   (Or.inr ⟨rfl,rfl,rfl⟩) hA] at hm
 have h0:BU.num 88902 1382 308 0 0 0=0:=by decide+kernel
 simp only [Nat.sub_self,h0,Nat.cast_zero,sub_zero] at hm
 have hz:(BU.num 18000 348 78 (rw-r) (yw-y) (tw-t):ℤ)+
   (BU.pair rw yw tw:ℤ)≤(BU.pair r y t:ℤ):=by
  linarith only [hm]
 have hn:0+BU.num 18000 348 78 (rw-r) (yw-y) (tw-t)+
   BU.pair rw yw tw≤BU.pair r y t:=by
  simp only [Nat.zero_add]
  exact_mod_cast hz
 have hd:=MH.floor_three _ _ _ _ hn
 rw [MH.charge_eq,MH.pair_cap_eq,MH.pair_cap_eq]
 simpa using hd




end CCD

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace WM
open ProximityPrize.Benchmark RCN095 RCN266
open scoped BigOperators
open DY KZ FV
open MM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq P4:=Classical.decEq _

def Critical (p:FlagDegree):Prop:=
 13≤p.all∧p.all≤17∧59≤middle p∧middle p≤76∧3611≤total p∧total p≤4879

theorem split_flags (H:P4) (U V:Finset (RegularIndex H)) (hUV:U⊆V):
 (BF H U).all+(BF H (V\U)).all=(BF H V).all∧
 middle (BF H U)+middle (BF H (V\U))=middle (BF H V)∧
 total (BF H U)+total (BF H (V\U))=total (BF H V):=by
 simp only [BF,sumFlag_all,AQT,AXF]
 exact ⟨by rw [Nat.add_comm];exact Finset.sum_sdiff hUV,
   by rw [Nat.add_comm];exact Finset.sum_sdiff hUV,
   by rw [Nat.add_comm];exact Finset.sum_sdiff hUV⟩

theorem FQW (H:P4) (A:Finset (RegularIndex H))
 (hz:(BF H A).all=0):A=∅ :=by
 classical
 apply Finset.not_nonempty_iff_eq_empty.mp
 intro hne
 obtain ⟨F,hF⟩:=hne
 have hp:=RCN130.JH H F
 have he:(∑ G∈A,(RCN130.BG H G).all)=0:=by
  simpa only [BF,sumFlag_all] using hz
 have hm:=Finset.single_le_sum (f:=fun G:RegularIndex H=>(RCN130.BG H G).all)
   (fun G _=>Nat.zero_le _) hF
 omega

theorem strict_or_eq (H:P4) (U V:Finset (RegularIndex H)) (hUV:U⊆V):
 (BF H U).all<(BF H V).all∨U=V:=by
 classical
 by_cases h:(BF H U).all<(BF H V).all
 · exact Or.inl h
 have hm:=LY H hUV
 have he:=(split_flags H U V hUV).1
 have hz:(BF H (V\U)).all=0:=by omega
 have hempty:=FQW H (V\U) hz
 apply Or.inr
 apply Finset.Subset.antisymm hUV
 intro F hF
 by_contra hnot
 have hh:F∈V\U:=Finset.mem_sdiff.mpr ⟨hF,hnot⟩
 rw [hempty] at hh
 simpa using hh

theorem charge_zero (L U S:ℕ):CY.cost L U S 0 0 0=0:=by
 rw [MH.charge_eq]
 simp [BU.num]

theorem FEG (H:P4) (V U:Finset (RegularIndex H)) (hUV:U⊆V)
 (hR:(BF H Finset.univ).all≤50)
 (hY:middle (BF H Finset.univ)≤229)
 (hT:total (BF H Finset.univ)≤11784)
 (hstop: ¬TG.cheap.Routeable (BF H V))
 (hc:Critical (BF H U)):
 CY.cost 18000 348 78
    (BF H (Finset.univ\V)).all
    (middle (BF H (Finset.univ\V)))
    (total (BF H (Finset.univ\V)))+
 CY.cost 88902 1382 308
    (BF H (V\U)).all (middle (BF H (V\U)))
    (total (BF H (V\U)))+
 QQ.cap (BF H Finset.univ).all
    (middle (BF H Finset.univ)) (total (BF H Finset.univ))≤
 QQ.cap (BF H U).all
    (middle (BF H U)) (total (BF H U)):=by
 classical
 let p:=BF H U
 let q:=BF H V
 let w:=BF H Finset.univ
 change Critical p at hc
 rcases hc with ⟨h13,h17,h59,h76,h3611,h4879⟩
 have hq:=LY H (Finset.subset_univ V)
 have hp:=LY H hUV
 have ha:=split_flags H V Finset.univ (Finset.subset_univ V)
 have hb:=split_flags H U V hUV
 have hAr:(BF H (Finset.univ\V)).all=w.all-q.all:=by dsimp only [q,w];omega
 have hAy:middle (BF H (Finset.univ\V))=middle w-middle q:=by dsimp only [q,w];omega
 have hAt:total (BF H (Finset.univ\V))=total w-total q:=by dsimp only [q,w];omega
 have hBr:(BF H (V\U)).all=q.all-p.all:=by dsimp only [p,q];omega
 have hBy:middle (BF H (V\U))=middle q-middle p:=by dsimp only [p,q];omega
 have hBt:total (BF H (V\U))=total q-total p:=by dsimp only [p,q];omega
 have hA:q.all<w.all∨w.all=q.all∧middle w=middle q∧total w=total q:=by
  rcases strict_or_eq H V Finset.univ (Finset.subset_univ V) with hl | he
  · exact Or.inl hl
  · have hew:w=q:=congrArg (BF H) he.symm
    exact Or.inr ⟨congrArg FlagDegree.all hew,congrArg middle hew,congrArg total hew⟩
 rw [hAr,hAy,hAt,hBr,hBy,hBt]
 change _+_+QQ.cap w.all (middle w) (total w)≤QQ.cap p.all (middle p) (total p)
 rcases strict_or_eq H U V hUV with hl | he
 · have hcut:=MH.FXK q (by change 14≤q.all;change p.all<q.all at hl;omega)
     (hq.1.trans hR) (h59.trans hp.2.1)
     (hq.2.1.trans hY) (hq.2.2.trans hT) hstop
   exact BXN.charges_le p.all (middle p) (total p)
     q.all (middle q) (total q) w.all (middle w) (total w)
     (hq.1.trans hR) (hq.2.1.trans hY) h13 h17 hl h59 h76 hp.2.1 h3611 h4879 hp.2.2 hcut
     hR hY hT hq.1 hq.2.1 hq.2.2 hA
 · have heq:q=p:=congrArg (BF H) he.symm
   have hA' :p.all<w.all∨w.all=p.all∧middle w=middle p∧total w=total p:=by
     simpa only [heq] using hA
   have hyw0:middle q≤middle w:=hq.2.1
   have htw0:total q≤total w:=hq.2.2
   have hyw:middle p≤middle w:=by simpa only [heq] using hyw0
   have htw:total p≤total w:=by simpa only [heq] using htw0
   have hs:=CCD.charges_le p.all (middle p) (total p)
     w.all (middle w) (total w) h13 h17 h59 h76 h3611 h4879 hR hY hT hyw htw hA'
   rw [heq]
   simpa only [Nat.sub_self,charge_zero,Nat.add_zero] using hs
theorem EYK (L U S L' U' S' r y t:ℕ)
 (hL:L≤L') (hU:U≤U') (hS:S≤S'):
 CY.cost L U S r y t≤CY.cost L' U' S' r y t:=by
 rw [CY.cost_eq,CY.cost_eq]
 apply Nat.div_le_div_right
 rw [CY.num_formula,CY.num_formula]
 gcongr

theorem cost_two (L U S r y t r' y' t' :ℕ):
 CY.cost L U S r y t+CY.cost L U S r' y' t'≤
 CY.cost L U S (r+r') (y+y') (t+t'):=by
 have h:=CY.sum_cost_le (Finset.univ:Finset (Fin 2)) L U S
   ![r,r'] ![y,y'] ![t,t']
 simpa [Fin.sum_univ_two] using h

theorem pair_mono (r y t capR capY capT:ℕ) (hr:r≤capR) (hy:y≤capY) (ht:t≤capT):
 QQ.cap capR capY capT≤QQ.cap r y t:=by
 by_cases hR:capR<50
 · have hr' :r<50:=by omega
   simp only [QQ.cap,if_pos hR,if_pos hr']
   change CY.cost (11785-capT) (348-capY) (78-capR) (50-capR) (229-capY) (17230-capT)≤
     CY.cost (11785-t) (348-y) (78-r) (50-r) (229-y) (17230-t)
   have hs:=EYK (11785-capT) (348-capY) (78-capR) (11785-t) (348-y) (78-r)
     (50-capR) (229-capY) (17230-capT) (by omega) (by omega) (by omega)
   exact hs.trans (CY.cost_mono _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
 · simp only [QQ.cap,if_neg hR]
   exact Nat.zero_le _

theorem FKO (H:P4) (V U:Finset (RegularIndex H)) (hUV:U⊆V)
 (hR:(BF H Finset.univ).all≤50)
 (hY:middle (BF H Finset.univ)≤229)
 (hT:total (BF H Finset.univ)≤11784):
 CY.cost 18000 348 78
    (BF H (Finset.univ\V)).all
    (middle (BF H (Finset.univ\V)))
    (total (BF H (Finset.univ\V)))+
 CY.cost 88902 1382 308
    (BF H (V\U)).all (middle (BF H (V\U)))
    (total (BF H (V\U)))+
 QQ.cap (BF H Finset.univ).all
    (middle (BF H Finset.univ)) (total (BF H Finset.univ))≤
 CY.cost 88902 1382 308
    (50-(BF H U).all) (229-middle (BF H U))
    (11784-total (BF H U))+
 QQ.cap (BF H U).all
    (middle (BF H U)) (total (BF H U)):=by
 classical
 let a:=BF H (Finset.univ\V)
 let b:=BF H (V\U)
 let p:=BF H U
 let q:=BF H V
 let w:=BF H Finset.univ
 have ha:=split_flags H V Finset.univ (Finset.subset_univ V)
 have hb:=split_flags H U V hUV
 have hm:=LY H (Finset.subset_univ U)
 have hsum:CY.cost 18000 348 78 a.all (middle a) (total a)+
   CY.cost 88902 1382 308 b.all (middle b) (total b)≤
   CY.cost 88902 1382 308 (50-p.all) (229-middle p) (11784-total p):=by
  calc
   _≤CY.cost 88902 1382 308 a.all (middle a) (total a)+
       CY.cost 88902 1382 308 b.all (middle b) (total b):=
     Nat.add_le_add (EYK _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)) (Nat.le_refl _)
   _≤CY.cost 88902 1382 308 (a.all+b.all) (middle a+middle b) (total a+total b):=
     cost_two _ _ _ _ _ _ _ _ _
   _≤_:=CY.cost_mono _ _ _ _ _ _ _ _ _
     (by dsimp only [a,b,p];omega) (by dsimp only [a,b,p];omega) (by dsimp only [a,b,p];omega)
 exact Nat.add_le_add hsum (pair_mono p.all (middle p) (total p) w.all (middle w) (total w) hm.1 hm.2.1 hm.2.2)


end
end WM

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace DZG



def FKA:ℕ→ℕ→ℕ→ℕ→ℕ × ℕ
  | 0,code,out,_=>(out,code)
  | fuel+1,code,out,scale=>
    let d:=code%64
    if d<32 then (out+d*scale,code/64)
    else FKA fuel (code/64) (out+(d%32)*scale) (scale*32)
def variableNat (code:ℕ):=FKA 16 code 0 1

def ESH:List ℕ→ℕ→List ℕ × ℕ
  | [],code=>([],code)
  | p::ps,code=>
    let z:=variableNat code
    let value:=if z.1%2=0 then p+z.1/2 else p-z.1/2
    let rest:=ESH ps z.2
    (value::rest.1,rest.2)










end DZG
end MergedPart0
section MergedPart1
namespace DR
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

structure Point where
  s:ℕ
  b:ℕ
  u:ℕ
  t:ℕ
  deriving DecidableEq
structure Box where
  slo:ℕ
  shi:ℕ
  blo:ℕ
  bhi:ℕ
  ulo:ℕ
  uhi:ℕ
  tlo:ℕ
  thi:ℕ
  deriving DecidableEq

def Contains (a:Box) (p:Point):Prop:=
  a.slo≤p.s∧p.s≤a.shi∧a.blo≤p.b∧p.b≤a.bhi∧
  a.ulo≤p.u∧p.u≤a.uhi∧a.tlo≤p.t∧p.t≤a.thi

def Empty (a:Box):Prop:=a.shi<a.slo∨a.bhi<a.blo∨a.uhi<a.ulo∨a.thi<a.tlo
instance (a:Box):Decidable (Empty a):=by unfold Empty;infer_instance










def lower (a:Box) (axis:Fin 4) (v:ℕ):Box:=
  match axis.val with
  | 0=>{a with shi:=v}
  | 1=>{a with bhi:=v}
  | 2=>{a with uhi:=v}
  | _=>{a with thi:=v}
def upper (a:Box) (axis:Fin 4) (v:ℕ):Box:=
  match axis.val with
  | 0=>{a with slo:=v+1}
  | 1=>{a with blo:=v+1}
  | 2=>{a with ulo:=v+1}
  | _=>{a with tlo:=v+1}

theorem EQB (a:Box) (p:Point) (axis:Fin 4) (v:ℕ) (hp:Contains a p):
    Contains (lower a axis v) p∨Contains (upper a axis v) p:=by
  fin_cases axis<;>simp [lower,upper,Contains] at* <;>omega







end DR
end MergedPart1
section MergedPart2
namespace BAL
set_option autoImplicit false
set_option maxHeartbeats 1200000

def Chord (lo hi:ℕ) (f:ℕ→ℕ):Prop:=
  ∀x,lo≤x→x≤hi→(hi-lo)*f x≤(hi-x)*f lo+(x-lo)*f hi

private theorem weights (lo x hi:ℕ) (hl:lo≤x) (hh:x≤hi):
    (hi-x)+(x-lo)=hi-lo∧(hi-x)*lo+(x-lo)*hi=(hi-lo)*x:=by
  constructor
  · omega
  · have ha:=Nat.sub_add_cancel hh
    have hb:=Nat.sub_add_cancel hl
    have hc:=Nat.sub_add_cancel (hl.trans hh)
    nlinarith

theorem constant (lo hi c:ℕ):Chord lo hi (fun _=>c):=by
  intro x hl hh
  have h:=(weights lo x hi hl hh).1
  rw [←Nat.add_mul,h]

theorem affine (lo hi a b:ℕ):Chord lo hi (fun x=>a*x+b):=by
  intro x hl hh
  have hw:=weights lo x hi hl hh
  have ha:=congrArg (fun z=>a*z) hw.2
  have hb:=congrArg (fun z=>b*z) hw.1
  nlinarith only [ha,hb]

theorem add {lo hi:ℕ} {f g:ℕ→ℕ} (hf:Chord lo hi f) (hg:Chord lo hi g):
    Chord lo hi (fun x=>f x+g x):=by
  intro x hl hh
  have h:=Nat.add_le_add (hf x hl hh) (hg x hl hh)
  simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem mul_left {lo hi:ℕ} {f:ℕ→ℕ} (hf:Chord lo hi f) (c:ℕ):
    Chord lo hi (fun x=>c*f x):=by
  intro x hl hh
  have h:=Nat.mul_le_mul_left c (hf x hl hh)
  simpa only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem max {lo hi:ℕ} {f g:ℕ→ℕ} (hf:Chord lo hi f) (hg:Chord lo hi g):
    Chord lo hi (fun x=>Max.max (f x) (g x)):=by
  intro x hl hh
  dsimp only
  rcases le_total (f x) (g x) with h | h
  · rw [Nat.max_eq_right h]
    exact (hg x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_right _ _)) (Nat.mul_le_mul_left _ (le_max_right _ _)))
  · rw [Nat.max_eq_left h]
    exact (hf x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_left _ _)) (Nat.mul_le_mul_left _ (le_max_left _ _)))

theorem sub_affine (lo hi a b c d:ℕ):
    Chord lo hi (fun x=>(a*x+b)-(c*x+d)):=by
  intro x hl hh
  by_cases hx:a*x+b≤c*x+d
  · simp only [Nat.sub_eq_zero_of_le hx,Nat.mul_zero]
    exact Nat.zero_le _
  have he:=Nat.sub_add_cancel (show c*x+d≤a*x+b by omega)
  have h0:a*lo+b≤((a*lo+b)-(c*lo+d))+(c*lo+d):=by omega
  have h1:a*hi+b≤((a*hi+b)-(c*hi+d))+(c*hi+d):=by omega
  have hsum:=Nat.add_le_add (Nat.mul_le_mul_left (hi-x) h0) (Nat.mul_le_mul_left (x-lo) h1)
  have hw:=weights lo x hi hl hh
  have ha:=congrArg (fun z=>a*z) hw.2
  have hc:=congrArg (fun z=>c*z) hw.2
  have hb:=congrArg (fun z=>b*z) hw.1
  have hd:=congrArg (fun z=>d*z) hw.1
  have he' :=congrArg (fun z=>(hi-lo)*z) he
  nlinarith only [hsum,ha,hb,hc,hd,he']

theorem EIT {lo hi:ℕ} {f:ℕ→ℕ} (hf:Chord lo hi f)
    (cap:ℕ) (hlo:f lo≤cap) (hhi:f hi≤cap)
    (x:ℕ) (hl:lo≤x) (hh:x≤hi):f x≤cap:=by
  by_cases he:lo=hi
  · have hx:x=lo:=by omega
    simpa only [hx] using hlo
  have h:=(hf x hl hh).trans (Nat.add_le_add
    (Nat.mul_le_mul_left (hi-x) hlo) (Nat.mul_le_mul_left (x-lo) hhi))
  rw [←Nat.add_mul,(weights lo x hi hl hh).1] at h
  exact Nat.le_of_mul_le_mul_left h (by omega:0<hi-lo)

end BAL
end MergedPart2
section MergedPart3
namespace TP
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem GRM (a b m n d finish:ℕ) (hd:d≤finish)
    (h0:a≤b) (h1:a+m*finish≤b+n*finish):a+m*d≤b+n*d:=by
  by_cases hmn:m≤n
  · exact Nat.add_le_add h0 (Nat.mul_le_mul_right d hmn)
  · have hnm:n≤m:=by omega
    have he:n+(m-n)=m:=Nat.add_sub_of_le hnm
    have hh:=Nat.mul_le_mul_left (m-n) hd
    nlinarith only [h1,he,hh]

theorem BCJ (lo hi z p q a b m n:ℕ)
    (hp:p≤lo) (hq:q≤lo) (hz:lo≤z) (hh:z≤hi)
    (h0:a+m*(lo-p)≤b+n*(lo-q))
    (h1:a+m*(hi-p)≤b+n*(hi-q)):
    a+m*(z-p)≤b+n*(z-q):=by
  have hhi:a+m*(lo-p)+m*(hi-lo)≤b+n*(lo-q)+n*(hi-lo):=by
    rw [show hi-p=(lo-p)+(hi-lo) by omega,show hi-q=(lo-q)+(hi-lo) by omega,
      Nat.mul_add,Nat.mul_add] at h1
    simpa only [Nat.add_assoc] using h1
  have h:=GRM (a+m*(lo-p)) (b+n*(lo-q)) m n (z-lo) (hi-lo) (by omega) h0 hhi
  rwa [show z-p=(lo-p)+(z-lo) by omega,show z-q=(lo-q)+(z-lo) by omega,
    Nat.mul_add,Nat.mul_add,←Nat.add_assoc,←Nat.add_assoc]

def left (cc cs clo charge slope x z:ℕ):=cc+cs*(x-clo)+charge+slope*(z-x)
def right (pc ps plo z:ℕ):=pc+ps*(z-plo)
def EndAt (cc cs clo chi charge slope pc ps plo z:ℕ):Prop:=
  left cc cs clo charge slope clo z≤right pc ps plo z∧
  left cc cs clo charge slope (min chi z) z≤right pc ps plo z

theorem triangle (cc cs clo chi charge slope pc ps plo phi x z:ℕ)
    (hchild:clo≤chi) (hparent:max plo clo≤phi)
    (h0:EndAt cc cs clo chi charge slope pc ps plo (max plo clo))
    (h1:EndAt cc cs clo chi charge slope pc ps plo phi)
    (hm:EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
    (hx:clo≤x) (hxh:x≤chi) (hxp:x≤z) (hz:plo≤z) (hzh:z≤phi):
    left cc cs clo charge slope x z≤right pc ps plo z:=by
  let lo:=max plo clo
  have hlo:lo≤z:=by dsimp only [lo];omega
  by_cases hc:cs≤slope
  · have hc' :=Nat.mul_le_mul_right (x-clo) hc
    have hdecomp:(x-clo)+(z-x)=z-clo:=by omega
    have hmul:=congrArg (fun n=>slope*n) hdecomp
    have hbound:left cc cs clo charge slope x z≤cc+charge+slope*(z-clo):=by
      unfold left
      rw [Nat.mul_add] at hmul
      omega
    have he0:cc+charge+slope*(lo-clo)≤pc+ps*(lo-plo):=by
      have h:=h0.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,lo] using h
    have he1:cc+charge+slope*(phi-clo)≤pc+ps*(phi-plo):=by
      have h:=h1.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using h
    exact hbound.trans (BCJ lo phi z clo plo (cc+charge) pc slope ps
      (le_max_right _ _) (le_max_left _ _) hlo hzh he0 he1)
  have hc:slope≤cs:=by omega
  let top:=min chi z
  have htop:x≤top:=le_min hxh hxp
  have hc' :=Nat.mul_le_mul_right (top-x) hc
  have e1:top-clo=(x-clo)+(top-x):=by omega
  have e2:z-x=(z-top)+(top-x):=by dsimp only [top];omega
  have hbound:left cc cs clo charge slope x z≤left cc cs clo charge slope top z:=by
    unfold left
    rw [e1,e2,Nat.mul_add,Nat.mul_add]
    omega
  apply hbound.trans
  by_cases hzc:z≤chi
  · have hloc:lo≤chi:=hlo.trans hzc
    have hpivot:min phi (max lo chi)=min phi chi:=by rw [max_eq_right hloc]
    have hmid:min phi chi≤chi:=min_le_right _ _
    have he0:cc+charge+cs*(lo-clo)≤pc+ps*(lo-plo):=by
      have h:=h0.2
      change left cc cs clo charge slope (min chi lo) lo≤_ at h
      rw [min_eq_right hloc] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have he1:cc+charge+cs*(min phi chi-clo)≤pc+ps*(min phi chi-plo):=by
      have h:=hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_right hmid] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have h:=BCJ lo (min phi chi) z clo plo (cc+charge) pc cs ps
      (le_max_right _ _) (le_max_left _ _) hlo (le_min hzh hzc) he0 he1
    simpa only [left,right,top,min_eq_right hzc,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  · have hcz:chi≤z:=by omega
    have hpivot:min phi (max lo chi)=max lo chi:=min_eq_right (by omega)
    have he0:cc+cs*(chi-clo)+charge+slope*(max lo chi-chi)≤pc+ps*(max lo chi-plo):=by
      have h:=hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_left (le_max_right _ _)] at h
      exact h
    have he1:cc+cs*(chi-clo)+charge+slope*(phi-chi)≤pc+ps*(phi-plo):=by
      have h:=h1.2
      rw [min_eq_left (hcz.trans hzh)] at h
      exact h
    have h:=BCJ (max lo chi) phi z chi plo (cc+cs*(chi-clo)+charge) pc slope ps
      (le_max_right _ _) ((le_max_left plo clo).trans (le_max_left _ _)) (by omega) hzh he0 he1
    simpa only [left,right,top,min_eq_left hcz] using h

instance (cc cs clo chi charge slope pc ps plo z:ℕ):
    Decidable (EndAt cc cs clo chi charge slope pc ps plo z):=by unfold EndAt;infer_instance

def check (cc cs clo chi charge slope pc ps plo phi:ℕ):Bool:=
  if clo≤chi∧max plo clo≤phi then
    decide (EndAt cc cs clo chi charge slope pc ps plo (max plo clo)∧
      EndAt cc cs clo chi charge slope pc ps plo phi∧
      EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
  else true

theorem check_sound (cc cs clo chi charge slope pc ps plo phi x z:ℕ)
    (h:check cc cs clo chi charge slope pc ps plo phi=true)
    (hx:clo≤x) (hxh:x≤chi) (hxp:x≤z) (hz:plo≤z) (hzh:z≤phi):
    left cc cs clo charge slope x z≤right pc ps plo z:=by
  have hc:clo≤chi∧max plo clo≤phi:=by omega
  simp only [check,if_pos hc,decide_eq_true_eq] at h
  exact triangle cc cs clo chi charge slope pc ps plo phi x z hc.1 hc.2 h.1 h.2.1 h.2.2 hx hxh hxp hz hzh

end TP
end MergedPart3
section MergedPart4
namespace DZ
set_option autoImplicit false
set_option maxHeartbeats 1300000

structure Piece where
  stop:ℕ
  base:ℕ
  slope:ℕ
  deriving DecidableEq

def value (p:Piece) (start z:ℕ):=p.base+p.slope*(z-start)
def evalFrom:ℕ→List Piece→ℕ→ℕ
  | _,[],_=>0
  | start,p::ps,z=>if z<p.stop then value p start z else evalFrom p.stop ps z
def eval (ps:List Piece) (z:ℕ):=evalFrom 0 ps z

def decodeAux (baseRadix slopeRadix:ℕ):ℕ→ℕ→List Piece
  | 0,_=>[]
  | n+1,code=>
      ⟨code%16384,(code/16384)%baseRadix,(code/16384/baseRadix)%slopeRadix⟩::
        decodeAux baseRadix slopeRadix n (code/16384/baseRadix/slopeRadix)
def decode (baseBits slopeBits code:ℕ):List Piece:=
  decodeAux (2^baseBits) (2^slopeBits) (code%65536) (code/65536)

def validFrom (finish:ℕ):ℕ→List Piece→Bool
  | start,[]=>Nat.beq start finish
  | start,p::ps=>Nat.blt start p.stop && Nat.ble p.stop finish && validFrom finish p.stop ps
def allCells (test:ℕ→Piece→Bool):ℕ→List Piece→Bool
  | _,[]=>true
  | start,p::ps=>test start p && allCells test p.stop ps
def Cells (test:ℕ→Piece→Prop):ℕ→List Piece→Prop
  | _,[]=>True
  | start,p::ps=>test start p∧Cells test p.stop ps

theorem ANC (test:ℕ→Piece→Bool) (start:ℕ) (ps:List Piece)
    (h:allCells test start ps=true):Cells (fun s p=>test s p=true) start ps:=by
  induction ps generalizing start with
  | nil=>trivial
  | cons p ps ih=>
    simp only [allCells,Bool.and_eq_true] at h
    exact ⟨h.1,ih _ h.2⟩

theorem cells_mono (p q:ℕ→Piece→Prop) (start:ℕ) (ps:List Piece)
    (h:Cells p start ps) (hpq: ∀lo piece,p lo piece→q lo piece):Cells q start ps:=by
  induction ps generalizing start with
  | nil=>trivial
  | cons piece ps ih=>exact ⟨hpq _ _ h.1,ih _ h.2⟩

theorem DMA (property:ℕ→ℕ→Prop) (start finish:ℕ) (ps:List Piece)
    (hv:validFrom finish start ps=true)
    (hc:Cells (fun lo p=> ∀z,lo≤z→z<p.stop→property z (value p lo z)) start ps)
    (z:ℕ) (hz:start≤z) (hf:z<finish):property z (evalFrom start ps z):=by
  induction ps generalizing start with
  | nil=>simp only [validFrom,Nat.beq_eq] at hv;omega
  | cons p ps ih=>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h:z<p.stop
    · simpa only [evalFrom,if_pos h] using hc.1 z hz h
    · simpa only [evalFrom,if_neg h] using ih p.stop hv.2 hc.2 (by omega)







theorem cell_at (test:ℕ→Piece→Prop) (start finish:ℕ) (ps:List Piece)
    (hv:validFrom finish start ps=true) (hc:Cells test start ps)
    (z:ℕ) (hz:start≤z) (hf:z<finish):
    ∃lo p,lo≤z∧z<p.stop∧evalFrom start ps z=value p lo z∧test lo p:=by
  induction ps generalizing start with
  | nil=>simp only [validFrom,Nat.beq_eq] at hv;omega
  | cons p ps ih=>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h:z<p.stop
    · exact ⟨start,p,hz,h,by simp only [evalFrom,if_pos h],hc.1⟩
    · obtain ⟨lo,q,hlo,hhi,he,hq⟩:=ih p.stop hv.2 hc.2 (by omega)
      exact ⟨lo,q,hlo,hhi,by simpa only [evalFrom,if_neg h] using he,hq⟩



end DZ
end MergedPart4
section MergedPart5
namespace FYL
open DZ
set_option autoImplicit false




end FYL
end MergedPart5

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace Codec0
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
def s0:ℕ:=0x3a352944000015d3ef79800003a35294400009184e72a00001d1a94a200000bd937adbe8c01d1a94a200012309ce54000005e99d54584c8c273950000000bd33aa8b0a48c27395000048c2739500000002f3b37eb6448c273950000000000000000
def s1:ℕ:=0x5bf9973aba50b08acfc7dec1c9faff6023414bec3399178e55e5e9b43bbf2ae644c565d79d76b66806ed86bfe93bb579e300bd47558b1893ad40605977415d3ef7980000e8d4a51000028b792a74b409384f720839b801490954808200f51e0201a1
def s2:ℕ:=0x5dc09a06bb51adf74b87dd17568725062e42e5829960245171f6810400023123a7e7dd30a070403a30008433d00dbd6e3b1989d5a6cc541178090600128774d1aba26f8398f4b69c31e1c7efee04bc90e32eb9da62306ee157b3124a36aba931a3c3
def s3:ℕ:=0x27d6832c551a0eb5b16156db057c02db00074bc0335ab77c32f30b39d1a4112abb14a14bec930bf724a7e831d019e0003e5c89986ebaf491314dc1bf4408736c4af35c842718da838b91e660bab38e52d88cb03dd03caf396d7a06ca4c2ef15366b0
def s4:ℕ:=0x52b588bfb523987297546e665678a5126e5e2629d80cd80c720de372ee2c51046cf5a7e8348139883593bc26501400003658889212b89dac90c936dc2cd5cc63d1adc92ae5d1fb76f8555418c1fb5efa9a8c47c5a5d4b171b14ddcd8523e6e7f572b
def s5:ℕ:=0x1e0538cfd8ef0efe5bdb0272876ed2317d7663ae28b639e451d4081b1da970e932f372261c73754a4f155a39b41b9ead0d1cadbcb52b708e24afbaddc507122e36ffd5e3835ef70f8931bb763e8a8280d93077aa87c94fc62b1ad7b2212011580032
def s6:ℕ:=0x217eddb87bf610be75c209dc083a3e19827ae41d1ce08ecee20a3dc7c6b46902a82a4000fc814bc141c3e0401de44974611fc11229f6538fbd03e6848d87cb47c2fb21c3df1a14fd0181ee51d7558050f4c95f6f15d87a3832a570523ca0663b4dde
def s7:ℕ:=0x2515067ecb15928152f84e78c92d913890b7e48f3de456b72246caf3c97729210ad4548e4c8f7b5f1a817247ad711123e6238c7032e0b411a1e035458008d03075231d045ef0bb65f3c22aacb2086f4915454873ad1c885351b205d6441b2364c08e
def s8:ℕ:=0x552d8ccdb6b5940e3da59af209e058fbc821e4ea44c8777be26e64c930b2b1362450656b789ae13c1baae24cea07d2ac42264b3536f5ce931749ac53f809879df28664a4bc033234a1625b01ddae07212cc4e52513849612823521b24a965e73e7eb
def s9:ℕ:=0x30d3a306c1ef14282c59f9d5493ab2541dd1a48a1e4274c412405e0b1421e91db8d6b6a7d08d0b24b4b30844ff63522ecb2269301bf0b68df185dd20fe46f24f544a744329a83b40fed18f080ab75248c2b95d80efac38a01dc0005cb09522436fd1
def s10:ℕ:=0x231d439a03d41141b62e9957087a654818620436e32ac475421727a564aea9093c6c8cb0387ef3e671ade23164f9aab1a017bdd6b4c6c605f80326000a804a3533440089e39042d641b4da680b3b22aa6873f5fd86352c01eda2bdfe91e4f0235c71
def s11:ℕ:=0x29fa09dc61a714e47b239eae4a6b1209aa00052404943a8552915ded32800143163af8951c853ef78e4188416bcd4d7e781ce8659501bc8e155daa983cc5c9206e5be5c13d00a8000265a459473b93fa76241455970cc0b58b4bf1325816d7eafc3a
def s12:ℕ:=0x2373f643d4ef117a3c5347cf88ae37b1efe4a31c1764fe87856788e2ab6c5aa534599dad153f8a1186ce625eeb2dfa37992e70e7bf39c116d88df0aca08b3c5400de30456c26a946f292b1854f68e771556cfc9a64f0a9f036ed4ae454c49d1d3677
def s13:ℕ:=0x2b94a06d96b615666a43db1b0a814228756d8527a7977ea6c287570d614b614309867dc2d09e8ca97f147a4e36d7607f7b26e523efd1e313302a1a15308989c75ff7a9e4b4a79702a092569170feb6c1275129dffd4090bc36ffa92e47988938e03e
def s14:ℕ:=0x100d1b458abd87c60d3c4535c3b4464fa27d21b2a2e6f12570cda15fd88b4a8b0c2e8d9c2d3dc60aaac9429b02ff0762374b917c5cafe6a4d0bc9ad758d04a5ada2a56a7dfacfc350033cd1645aa6a89d52b069d2a7cbfc1fdebeb045a487072af6c
def s15:ℕ:=0x1cbaff949ade8e3f17dfc95b47194be2e4a5e376c5ccf243d1b602de891ff8d9496c248e746908b046452233da56fb220b19242a3a90918c5894bb481e46018a18e3f6a2dd04d191e4715ca24b58e6c88d08ef4c5dec452475322e1a21cc395f168d
def s16:ℕ:=0x205135ef94ff900c9ad04a7947f60d512536e3f886a19295f1edd339994298f6c99c44a0947ae8cdb650923cd465ab27a91da1319293608ece18cb49b6c75bdc6287dd83ab6466b249d1d3dc4814a058e921fb21de587440c27a4be639a0bc81c64f
def s17:ℕ:=0x23413abd96d991991d64cb8048bbfe364222a4522735d2d092278397a96659114f9308aa788850e3ca5926439270ad2bd921bc9a25020910b1f5f49109c8554de9e56ee424efe3aff21211e3743958a907cc1507656483d8dc6e564a413bcae25db0
def s18:ℕ:=0x2ee94df49e5e972f2697cf134b5012d6275be5844930339712b0447aa9c0194f322e9cda549e0233184caa4d6181b0655525e0f4ea522a9288947e38d5491f01723bc064882ba1d225523d23bb1974091e69ddacba6c8ed7fd43ef1846e322416155
def s19:ℕ:=0x36515a1ea3149b182d085193cd59161f2897e6a2ab02f449735125839a2709a052b22d0c24cfd1598a86e667b2ac21430532d6548ba102994eaa04d05ccc6e14ad2812e6323bb1d7db0316152029ff0984d286ecfca4c0953fee7c9e5ef89e0d3dbb
def s20:ℕ:=0x3c396394a6969e1331c7d3534ef198d0e9aea7682c4754c713acc6158a5cb9d60b096d2d4ceaa185b2980e740ac0674adf398a5f95a54c9cb92f90d2784e32578b2929a70d8bb7d492b38185ceaa4159bc6ae12d1eecdd396f9e8f7a6d7cb5674675
def s21:ℕ:=0x40a16ac9a95da01f354fd4cb500d1a8d2a4de8062d4ad52b93f296862a8709f903464546fcfbd5a13ea24e7db4cffb50b93eac675ea7d59f013378d4144f6e599229f2a7b62cbf74f073d8065c6a7819e72328d53b8cf279901e9a3a78fac8834e03
def s22:ℕ:=0x450971feac24a26b38b1d5d5512d9c7eeb1ca8884e1b3579143e5706babb7a1cc381255ddd0e45be5eacde85d0dd4555db42c86e0caa63a154b7325577509e9b936ac128432da615495418e6c6baa12a0b6b62ed512d0571b1daa9368174d56b5239
def s23:ℕ:=0x2d305410242016400b80001807bc0eb0065c02100120000601000088000200679d23358dc02200140000c9020ef015d2f47997680ae12a37b3aa3d6bf51bc9d6a6b7828dc8e97559e3465d7479ad49a2ea39e95694d1671cc42b28e8a42e4e55901
def s24:ℕ:=0xa1cd6203d6884c0083c4347c256013e0004c10bb9bbb027307711a580f7583ac73432795c1952d8d805e40aada7e0766b04f508c0fca1024d843581cc0123c20c40da808ad7cd222bd03bb06c302d401db836b017680bb4158008f405ce0aaa047c
def s25:ℕ:=0xbcfcdc79f5d05de0a1343fec2ed84a2b6c52174fcaeadd9a0ba4b56c604405cd0c488c71c2dbb2d9a5ad416c32cab0e9c0b5005fc00150594f843d88ec2c824c5bdba4163bacada42f0b1d13298799857abb459fc302b587dde61a0153c249f0e8d
def s26:ℕ:=0xc5b6ad4e979862c8a9844314315b8a057fe218a82013cc520c50a9012876861902c87270430a4e96317f2183ef4a21ed60c165acb5fb005feb7c89e1882ff43e7bbd1c17eb336f71610be82041ede485efce89036d82f7a0254e19017a4915e7b07
def s27:ℕ:=0xcf78a9f88b7867b5cb3a138433949bad94a219b593f138860cd855149a8f866c2926167a83360582a22d6197df5297f4d0cadf896eead0655479e0e95c327a190ba1c419347e6b7d240c929d05a67c063db316a0d84318987fad80818c2ea3a8a27
def s28:ℕ:=0xda85ad24a9c86c7e47f8e70035edf6b64a101af3a156af9a0d780718001706b3f5ec0a27c35725239cf041aaa7ea8974b0d541ed3f37206a2789c6292c34af907dd16c1a53d739f0f20d23708a9987068a820d36dc8343b7cffb5201a15151b3aca
def s29:ℕ:=0xe2d4519fbb2870f4607a0834382a378f301a1c0cf87891350dff70bb9c5006fc0bea44b5c37d99c901eb81bdca63347440deab0c4c37686f257fbe3ab8378dd8e126501bc1ada1751b0dcd73af4aa186e573ee65524370eeb4313f21b5a72059714
def s30:ℕ:=0xe9472e84e1a07445e1923c403a11b58feba61d06c7934c390e77a804fad187383043fd55039b5d6c5ca761cd29393d3970e651913015987286f4068120393b487369641c8d911543a10e4102bc365b07190c20c4c8438ba37988ae61c5b30e4d41a
def s31:ℕ:=0xf0756d7afe887807e78290043bf52b5eaf001de0753c43890eede39c0c408774adaaa412c3b67a5a3bed41dadaa49ab460eccf5d2402707600eb2fc8003aeda29393d81d70bace32680eb22f61acc887588c8dc4f1c3abf8b25e7a21d559cb30fa5
def s32:ℕ:=0xf72ff8ad0eb07b93eb7175a83d9402d414461eb99791b6450f58e8e849f387a8b7766c18c3d0c896f216c1e75ff0460cc0f397241502f079b8cd4aeef43cdc428f3a7a1e630d48bc270f3137acd118079134ca29cc83c6f4e1973921e2c33571445
def s33:ℕ:=0xfe4dbfe53bf87f161367050c3f83539f7dc21fa0109800320fcde750778207e3ccae296d83f0d4bb855ac1f8681c924720fbc03f10ef407d9638e53af43eca3240a11c1f60c080b2300faeeada724107c5a4f2dcda43e29476ea4c01f146a4eb9ab
def s34:ℕ:=0x1040ee38c00a081f2b762f4bc40d06e0a2b662067c2e6feed102c1bf7fe8e08148dc1456844099b7fbb72a202e3eee1bd71016706db57a0809d363802f840433bf87862201e79e787021004b532770087fb8ba0289503fd711de00481fe0300234dc
def s35:ℕ:=0x10994f149975084aa53f71580424cc00735342103d6a7b91b107bec43f4cd083dd88939cf841ecbd34bf2a20f112c85e721070cf145d8b88345c88731044173039761dc20b475ca19c61058ac4526a9082a199b3aa7c413e54e170dc2084045d0f3b
def s36:ℕ:=0x10ee15d92fa68871b89ceae7c438334425f1221c0e1e2d40b10dbd782a303086a8cc14e7d043313661905a218bb100e24010ba611cf796885a9b2b6b52c42d1daf6a2d6215038b9164710a570d355bd085204e35f80c428e4feb34fe2139f764af1d
def s37:ℕ:=0x114ac2c82235889b459d16ea844d963ddf19a2261e82ce02e112de8f6bbea0894c66894be044994276baf6223d8b5d59d91117e207e20c888b9187eb8c8445c0e8028a6220c8d328a4e11004ae49613887e611533ac043ed3943798021de4a797bf1
def s38:ℕ:=0x119b161de0e588cc0d45020dc464577956a0e23116a80e2481184e4b6b88888c207ca3787445fdab321b5622fc267b1b0e11703c9f4a8588b71b17427b445b59baae8e422d061ad64ad115a4444699608a90eacc5c84453950ec058c229648fa52f4
def s39:ℕ:=0x1200084d2b0588fda41563d9847e8031372b823f1f646683b11e83af06f1508f1781984fd047891d642cbc239f5a1fa69711c91df42b8d88e1416c6f2f846f7799884b4237b9e46e09111b7e01d850408d90d7e0fc3046be962417b4235bb177cf17
def s40:ℕ:=0x124ac8b5d2430921e7b7f685849007b9a3086247c3de71845123da3aec96e891c9a806e19c48e3e9d174702452d6a7d802121f092beab1890e3a98b7f004863e7b08092242950acf5e012116f655b4b09085fdfef0284825fa236bf42401b054795b
def s41:ℕ:=0x12871c6da21209434d4f7f9184a147d4e313e2507802fc68912839d16ebd4894049d07e0ec49eaefa3a9e824ec74ee29f61276319c749409380f984623c496f8bc36ad024b01330003612571cbb00d3892a4babc230c494845d6dc52249a64b069c5
def s42:ℕ:=0x12c24f5fb44b895fe63fd78304aea2790cd8a255bc887a27412a78c7d853c8953655340a584a8bf0e7d1f6254429666a6812a09b6c84bc894e1c4c927c84a5f1af0f636251fa7f6170b128e5f7edd0f89470c2d7eb904a2b1102c9e8250ec7aed602
def s43:ℕ:=0x130e850c926b898516ca8f63c4c1a29140672260cc40735f7130428487a1389820c8e04d4c4be3fee740c625e65db41a9812eea7ed89db0975db4e91a444ba126d128fc25cca78ffbc112dd6f6ca9ee896ce311f94504b66067cd5dc25af660b06b1
def s44:ℕ:=0x133bdec78a92099c6941a3b704cd0245a11662666d34d18c71332a3c99a9909964741474444ca8cf46ddba265045b0d2c61326ef47fe4a0992ad49b84004c85db4bc9b0263f3f51d80b131920508caa89899a3c90cbc4c4ac8b47f9c26250f3d95f4
def s45:ℕ:=0x138e21078cfe89c641eab23d84e3203a41c7027124de09445138361105f9b89c0b6751c8104e0141fd16f426fadbeec1b1137d3b2a8a6e89b7de6bfc04c4d927554d1ba26bcd7cdcd1a135bbfa5b8d209a5d22585bd44d0b3a6e094026831f5660e4
def s46:ℕ:=0x13c1215a8d1889dedd8ad7fac4ef4ceab87042771033130aa13b48e2707c889d7b5ab6642c4eab895820582754a6a956f4139fce53440c89cf10599449c4e68847633f227329402832413974bff425b89caf50cc0a3c4e487bd1fe4a271cc71243a6
def s47:ℕ:=0x140aa1fa09580a02d9c5fec444fdecb2f0a7a27ed85a5701013f187a4e58489f1ab174bd184f7152bf7e6227af71e666cc13d56c6d69e309ea7c9b315504f50862a348627a096e1964b13cfee9e49e309e6a59ae66584f12fa678e4a2786a29eebfe
def s48:ℕ:=0x143f3704ad058a1f44471c78450cb51e4c976286427a264bf142ed56411e28a163416b340850976342eeaa28481debe172142015a085120a0f3c363a7c050741ba1abba2837cba2c9a11414ea6168320a0a18f3741485049de34326c2817d7b9f293
def s49:ℕ:=0x1477ba642a638a3b8cda475fc51c8195e315e28e245291b0d14706299e2278a380bd7079b851b28d2b91f028d91b9623e41468407648b88a30a405bdbf451793886e76428ac271a75841448d261c5520a23d2bd8e9285111d2ba888428843e1517f4
def s50:ℕ:=0x14b9020788f60a5964390dd7452bb4faa7f80295c1899152214ac22de8db58a552657a7ab452a6110e2a9c294dedc72ea014a5166482db8a503fd1c3a28526ea9000c1e2930dc6224351493a5f1cc6a8a48915bc6cbc523ac326a1c028fce3e92d34
def s51:ℕ:=0x14e7688091f10a729089d4a6453725b86a02429b5799e650314d9eac06c7a0a69f4d6ed57453419f12afb4299f7db1c6e614cf02b28d858a6303779e16053054995809e297fbae3204014bf2dcc12d98a5e695325b7452e9b71fa76029731f9114a9
def s52:ℕ:=0x151f862a0ae38a8f326a8bccc546b693b89aa2a26f3fbef081511deb93de68a88badb2bcb854402bf000742a1d40835d99150b5c4447b00a80c6d14ac8c53fcfb1e03f629fa46c31bc314f423548dd78a76955efce7453a5b225999a29cf461a2211
def s53:ℕ:=0x1555641b64b30aaa53924fd88552b4cdbfbce2a8b37c356d615413254e74f0a9f0f12d68dc54f05d283d382a7805f120201539bbe046768a9ccc6fa783854daee0095ea2a6341e8110e152f9917d6368a9416d44c1c0549465d6a6e82a47c69eba06
def s54:ℕ:=0x156dd42347de0ab6549c4a44855a8e65729602ad448431c4115650f039f080ab2633b723e8558b0592f6562abe01f3e016155ece606e058aae4f3215f7455716b6ad6e62ab7784fa5e41559fa0d45f80aac9855e53f055620b1da8242aad0ae7be6e
def s55:ℕ:=0x15aca3bded0d8ad5a27656ca456ace8af45042b53668f985e15a45b791d188ad066c7870c45674d60e19f42b39d9d3139915984693f8c60acb3bfd2353c5650ea8c1af82b025650e0831578bd73e9208ab90a82d572455c6d9d933e82ae1eff0d06f
def s56:ℕ:=0x15d2b807cf908ae91adde6efc57320373d6762b97187bc00615c9f9a4958f8ae3cbd407030571d47bfad8e2b88bba7fc5c15c3b4044bc10ae1439c1f3f456ff12da4e022b757d46a9df15baae8e2f470adb6e175f3a856da458833802b6339ec8442
def s57:ℕ:=0x16007b877a0f8b002b0cfab3857f1a88831ba2bf58fac4c0615fa4ce3bf670afb7fa6adfd057c75f0b04e22be193f608e615efbe80b50d8af74d072742c57b7b4ad3f102bd4308c0acf15e84df0bf858af08104d46a45770590053142bab94ebd9e6
def s58:ℕ:=0x162e5c30c2f10b17268cf751c58ad8947def62c54a43a4530162530e3a9dc0b1292adc74bc58947959e8382c3b6f9d7e5d161a0563aad80b0b7fc7daf285828499d013e2c1327308b3e1609822c2d7a0b04928f47424581e2e0e4e902c01d6eeba75
def s59:ℕ:=0x16556b1b6bf40b2a5c5fb5264594bc7e665402ca554bb5f41165264400f678b27916456aa45938962e3aca2c9189c690561647d415f3b60b23b4614e1a4590f706e56b62c855f1a6b9b163ea19c39130b1d961fc5fe058e495a23aaa2c634226db38
def s60:ℕ:=0x167f4fb93b3a0b3f32de1782c59efa65434402cea5f24358816744106c9518b378edae5f1c599dfd8fa73c2ccea3d3e40a1664af1e44960b2fa2ecd2624597b3e57c1522cbb1cb8270b165cf50fb2a08b2cdd261f7e45966a31888f22cafe0a1361d
def s61:ℕ:=0x16ab92f38f6c0b552848216585a99f7dfdad22d49e0182fb716a14de20dfa0b4f851c3667c5a70d77fb3ba2d36ceb52efe169aa20e70448b4ce23e328605a5b02fc27c82d280596e52e168b2cbe18678b456aee653505a0e873c5a582d03c092b321
def s62:ℕ:=0x16d8e815bc6c8b6b65919db345b4283e6d47e2d9dfc1463b916cebff6c3238b64e898c5ac05b2446120f682d8a61fdd9ba16c294aa42df0b611332c77e45b0132a6a34c2d65cdd8223116b21b335af18b58b9ba6c26c5ac12304a05c2d58cbf03986
def s63:ℕ:=0x170046de30208b801a0e698f05c009ae23c7e2df980546f3216fbebcc147a0b7a237e783fc5bce144064122de415aca7d716efc09432380b75b4b8096485b979bf282382dc8dc002c5616e22dc74b5b0b705aee948485b679ef571ee2db245f722f7
def s64:ℕ:=0x17348ab8edaa0b965e26f75705c9cab732fa82e4e343f0fe71725ed38dfc68b8e44b48a1945c5e313885682e2dd2f758c71715d367635c8b8718b507c2c5c33dae9b7162e19092a959917099985f5ac0b82a397eb3dc5c0dca27ce6e2e01a7b97c4c
def s65:ℕ:=0x174fb15613160ba74bcadd4f85d345673c7c82e972fa8a8a2174989fe3a508ba40a690d2945d1a1ee132ae2e8d0bc4881817436857a7ca8b9f82c18603c5cf2de0c3dc42e78033b9add17391997ee7a0b9bc05f19c685cdcdf8429042e6c7eca5b2d
def s66:ℕ:=0x1784cfd303128bc093c2c7b8c5e041fa8e27e2efd785a3889177cf2cbfa820bbcce7fb5ec05de00d28d4f82eee336f2df51775276f8f738bb9eed4530685db412ca36982ec9a2c65d451764acb20ba28bab552fd26445d54dc0567a42ea9b6378c72
def s67:ℕ:=0x17a6acb6fd228bd0f7e0bd8845e7f5e3933d62f3ecb5ffacf179f4e55c3598bcefe8bf802c5e6251f447e02f2c974b89e917959c0047ae8bca3b46e93805e4216b8dbbc2f184e65b9d4178b5e2a457d0bc4bde20f4205e171b7095ce2f0b7c48de78
def s68:ℕ:=0x17cc8e31c01e0be5f7e95e8ec5f29eb1959de2f90633ced8c17c7dac59b3b8be2283595a645f041253d48c2f7d6a8319c717be114145dd8bde1b04998ac5ef06a4158082f7462e73aa017b7a1fd03068bd741f6d36105ea71a15b4a42f504f851f1b
def s69:ℕ:=0x1801c1cbba250c00cfb5d2dcc5fe031e0007c2fee077dd58217f5b7ae06518bf96bd190ef05fbf6aa684622fdee34d759317ee23f05cc50bf510ac857f85f8ab91c53c22fc0a56eb1c117dbcd5badee8bec941147d445f4395373be82fa19c43a00a
def s70:ℕ:=0x181fa0911c240c0fb93c12018607687516c52303984fa1f00181cb4a62a378c0de6920c578606069239ada302f6fa15352181794cfb2390c0b3abb2d6cc605441ce71e63022c19b070c1810f7e097728c0554361028c601274915ecc3003a8a95719
def s71:ℕ:=0x184a84cdc59d8c2497d47935461132da264ec30867fbd01d61842eef262520c2116569c4a86102d189e1dc307b7346edea183d445380e08c1dac6b0399c60eae504618c306c857d25cd182dc8c5d0858c14b466a62c060947e41658e30442684e501
def s72:ℕ:=0x187c1c410bcc8c3dcc8cc737461e8da6da7c030d513f262fa1868b103af7a0c334083b6b1c61706fc429fe30b1b444dc661854b316f05e0c29b72aabec0613d98d27432309cdba8c087184d48c7b2ac8c266093ece88612eafc49d52309584de8f5f
def s73:ℕ:=0x18a18cc270360c4ddf02fcc68626eb99f69ac312ef315b2bd1896294f901e8c4a14ae480fc624af789fce831253f6ca07f189136fe7a278c47e5805885c623e4acf459e311c961a69381888a50b1a6f8c406ef18a8cc61fc2ec2f05230fa7a2e13ec
def s74:ℕ:=0x18bd9473b1058c5d6466815dc62e8eef9f624317372e4f7b118b6cf9ccb410c5ab49614c1062d3ac3a84fa31660e5f43f218b1d36c0bea8c5744edab67862b364df3e0631552356426718aa59cc61600c547abe39a98629360bc869e31481abde105
def s75:ℕ:=0x18f58783f6d68c77ecec51afc63981959deba31cb88e43e9218e4398a98658c70300de40486364d26cb36031ae97f8220018d260e26a100c68d660c0608632a123126683191685bc73b18c87b69cb1c8c6411a89f0a0631538d26bae317ba10a5b7f
def s76:ℕ:=0x191b64d76eee8c8d13bb5d8606459f4bced263228f9f704fb1913f6086d2a8c891f37c442c64393335378e32166a99cb631904fb9019170c815cbb71ccc6408a7e641a23200f9731ff418fec3653cb10c7c94f6482f463e162f423b631ee669a3fb8
def s77:ℕ:=0x1940e7c9431c0c9ef85c3d20864f47b24421c326eafa9435e193564c2ff668c99f40b7626464c9299f2a0a326254cd210919300074fa4e8c974de78ff7864b2903a164a3258d19fe4b319279d1bd0ce0c8ee86c4e4e4647706b2da2a3239188bd5db
def s78:ℕ:=0x1958de3cab0a8cac678e7afbc655fc28f937832adab513ffc195653f073dc0ca8da67e6d346543f7ae9de0329ca6a93c9a194e19f543930ca6b010c8c2c652f65be83243296bfc05e031949e806bd608ca3ecd9ff93065129ccfb5a6328388bbd991
def s79:ℕ:=0x1998486f707a0cc925549a9c46648c15a7792331f8109907c198d2ae990b98cc681aa1bd60662476ea342c331200d21ab019881f8c96c78cbb4dbd55e0865cdddbf759632e67e4435981972aec1d05f0cb9080da5b5865967f7e2a3632b6e8960fca
def s80:ℕ:=0x19bb9f5321b18cdd984aa7b7466deed6a6bbc336e23acd84419b618932e638cd8ed6ca906c66c2ff5b5b54335c7fe986ff19abb858bc0a0cd535595f88866a98821ffd43351c0c03c8119a04c98a5fd0ccea1925d01c6671cf4b17523332ce866726
def s81:ℕ:=0x19e1569434808ceeeffdf930c6774af3dc81633b7e38d884719da46fe7da88cec14e7d746c67524a4c95b833a82132922519cfe3c5bfae0ce740ec6feac6734b94bdfe233930c8eca6f19c3ff0d58788ce13832a28ac670268e7dcd83377e7160836
def s82:ℕ:=0x1a085ebab8fb0d03e41c73698681eecdf0388340d1d87e5841a0509cc47dd8d01b287514d4680c203fe8ea33ff322302e919fcd16ab4d70cfcc97eca2cc67db55b3a4cc33e6df2584e619eef4a7acf78cf5d9f666664679f2ad7801033c5da6d8184
def s83:ℕ:=0x1a422d8c6b198d20139151b2068f72adf3d5834791a8002041a39af04c1890d1c661b76ec068dc12338618346cceb118821a30142550fa0d16b102a54a468b49bd4bc7034586a3d44cf1a2c2be6911d8d0f28c572548686a15e5dd94341e64904930
def s84:ℕ:=0x1a62a8c26ed48d2f631b650886978e8321dd234bbc8b21dc71a5c2c3091438d2d7e2997f7469681cf53a4634aa37aca05c1a53fc361d380d27419b2793c692c46b5549034921b99d0921a47e6a10de70d238b28b6ea86913d0f9e3843485a54d6097
def s85:ℕ:=0x1a8c8361328a8d4165f1b32246a0a347657e83503e817f1e61a808bb8e6988d3d776e2eda469ea255cabb434ef0e31c66e1a774d483a000d39f321f2ce869c4b14e452e34dcc7369dc31a6cf77d52858d348d5625db06998b14e450a34c9e49aced4
def s86:ℕ:=0x1aafebe1de430d576e396a4cc6ab87df03e5c35564adc5cc91aa54a6e268c0d51bfe156a646a8cef4a56fc354189317d461a9e29bb0c6f0d4cd30c040f46a536ef371ba35297403f3931a90097ce4e78d46e886e99fc6a36186e78963519d6c764ed
def s87:ℕ:=0x1ae0b1653b250d6ffef0aa0886b4f66dc5ecc35a56a1f00d81acf4c82b7c40d672494e80846b37a7cb16a035945b2b06631ac879615ff10d63efed98bd06b1e96c31c2235873cce07f61abdc19fb41d8d5c4023056706adcb03e12ec356a9254d421
def s88:ℕ:=0x1b0c20fb05ab8d84f645ec6c86c16c07bbd8e360979e13c541afede4baa090d7ea901229086bf30caccc1635f5902220dd1af633366cc10d7ad3e3855f06bd5b6fc77ee35e1cd2b9c9b1aee1deea8e30d744c02672c06b9c5fd070bc35c45a352281
def s89:ℕ:=0x1b300f62d5b28d965eb60ebd86cb28d9c1d723655c43f6feb1b28261a46d48d9292d5848686c85e4e69fc836425b1b23731b20801b306c8d8d2b68ac5706c65b6c38e8236301382f98d1b1064b069080d880706001086c350ff0fdfc3619992d7a99
def s90:ℕ:=0x1b5936e824f38dac809f6d8246d5e78549cfe36ab38b9990f1b52c3bd2ee38da8967e7ec306d3513666238369364dc4db21b47189438308da25be3643786d04b6c2472a36820678abc21b33d765c67b0d99710667d506ccac33a35a83661cd24586c
def s91:ℕ:=0x1b8c025bcd450dc4195de69146defa3c7cae436f02dcde8901b73c807a7590db931f3669046db11bd0986e36d3e7ddd3ec1b679f6731820db310144d8686d97d215664036c7217aea9b1b62339a1b268dafe66690bfc6d7eae4447e836b697311b99
def s92:ℕ:=0x1bbad45784d98ddd697b584406ed7fc513504376aeb7679211bb56c57b1be0dd833290f3346eb5ef933f8e375a20c3efd51ba6580094b60dd19d58227f06e82eb74a082373829755cc51b9a93cef0ee8dcc31e9576c06e3743d5fd8e37191db2270b
def s93:ℕ:=0x1be4188af0610df1c984690346f83cc01f9bc37b3bb7b736d1bd71763b95c8de940f02a5ac6f43a1730b963796426b24461bcada6927070de46c6ddeba86f19db7cd7ae378a9e50343c1bc2c36091660de1173ec90e46eff5300cb5e377c5d2f243d
def s94:ℕ:=0x1c157b4ae27d0e098bb737264703c782730f238089ca874a01bffa9422c580dff540cc55506ff226fb8a6037f1659618691bf8b2780cb60dfbee41888946fdddd1bc9e837e5b79746dd1bebeb295f0f0df5dff195a5c6fa84cda936437d25d752471
def s95:ℕ:=0x1c52ec1448340e2505c359f0c7120be823d60388b329868011c3a5f8cd16e8e1c98b2253ec70e0ea9faede38705e9524cb1c3554bf4a958e19a12822e6070c7eaa6a4023861d986fcb61c2c595828328e14e737cd4a470942dabfd4a3838b50de80b
def s96:ℕ:=0x1c75caf22dc10e3ace855ea5471c78735923a38e31369af0c1c6f2fd705bd8e3777565b10871b81912ba9438db4160a52b1c6c6da33b6b0e35567d5229c71a91faf567838d1b2ad47871c66cf97c2f40e2aa3d55831c7152c657e0b438a7ad8757c9
def s97:ℕ:=0x1cbc08797d520e5c49577becc72db93c56858396b402c63af1caf65c04fac8e56131a6a42c72a13178c7fc39337eeb400d1c91741693ad8e47a17e697d0720dc847f024390193a109431c7fe415acf20e3f1c54d3bfc71e8e67f2cd038ef65f26a2f
def s98:ℕ:=0x1cf7d8716a0d8e7a983bc96dc73ccc6c6b2aa39e50e94dcc11cf1f952b8718e7301b42ec8473808b9c52bc39bfa9af1ba01cde88c2c9530e6d15a558f7473575cacbdc2399e50309ff91ccbc67be8420e6571a2276647301f977b4d83980593fedc4
def s99:ℕ:=0x1d2a0d0c81de0e93875959bd07497a9b680b83a2dbf6d2dfe1d12646740ea0e88985a49774743c1e839c003a19e9f952b91d04c653c8738e81d3079f72073fe0183741439fc85231e941cfd137090e38e7d23918d8d073e0094ae58239eff6dcdfb0
def s100:ℕ:=0x1d685fef9a798eb28f662abe0759240524a943ac26243264b1d5d9db0b9688eadd509869b07569f4b194243ab0622926371d4d16efa7f80e9f68203bee874efc78ad4163a779e7216581d3596d00e410e9a6b68dab1874c54076f3703a5e482ef893
def s101:ℕ:=0x1d9a9d2fd1f68ecaed9fc085c764760a1e9043b1f324a91601d8d770ce2848ec42521e6db076172e4587a63b0abcde60ed1d82af1a2f4c8ebee78ab7c6875eb064b821a3af3ee1124dd1d791abc72ed0ebaf630611ec75ae5ba8dd5a3ad1e5d25cd0
def s102:ℕ:=0x1dda013f590d8ee7f716e55fc7730c7ba4d963b97e18b26d31dc4e6168a3a8ee17ecfc69547702e602f1083b8112dbf2591dbeda6893fa0edc2d95a334876abed3272603b4f8e78a0b01da5f91ebee00ed26f9b38b1c768af43f37ca3b3674c65416
def s103:ℕ:=0x1e0c321088498f051920c9c4478165261e9963c078b72ea181e017a7443bb0eff60bb9149477f35ac1ac623bf62b00b5f61df9df6ecc098efab156f760877c8dc71ae7e3bdee9cb151d1ded2490973a8ef2f41520ba877919e4748e23bc81d1e5abf
def s104:ℕ:=0x1e4caafc51e38f25f0d3ba238792f482554943c8e543a58ae1e45a3c86d580f21a72d542987902cf2f4dc63c74f5e01f991e256dbf65378f10c6df1e6b0787eafea46723c371876a4f91e1b6db8e8038f0ce16339774785775637df83c20eb768ba6
def s105:ℕ:=0x1e814c1a5bb48f3ee93e6aeb079f03924f3163ce5d8ecfaec1e71f71d86a50f38568f784e079ac162780703cd265f127951e66eb8f0a238f2f28f7a5f4479603ee0008c3caf261461b01e56a61e747a0f2b28ef9fb3c794fbfab117c3ca02c535c6c
def s106:ℕ:=0x1eb0ac048fc20f581e0a564b87aa59193b60a3d52667d27d91ea77f515c488f50ec6d9bf787a7d259276963d3cc9a7e9a11e9b8d075b2f8f4c7c836f3ac7a5dfc179e543d25931adb551e910c34607a0f44de2ebd4587a20f89be1e23d0a448b7597
def s107:ℕ:=0x1ef3d5debb398f792362f82647bb9c75153e83ddc675728351ee860f04bc98f7173db170ac7b7aaa1f63c43daf092484aa1eca8e101e6d8f6309a3abbd07b1259890ac83d858f9121281ebadd205e540f5cc74229b747ae40d5940ba3d6a5d179e82
def s108:ℕ:=0x1f17e20f8eb60f8991a7966d47c47620521823e22d2b6a9881f0fb301800a8f83af6c08ac07c187397d5e23e0bcaec1bd71f0448b351678f820a4e6eb647c07a03d9e0c3e03cd6d93bd1f01c58adfa20f8099edca11c7bedc84e7f0c3de8ed8464c7
def s109:ℕ:=0x1f62957b4e2a8fade1b8528f47d656908cfba3e9ef0af9f071f4c98ed3b250fa54b3cfe78c7d13c0fd352e3e86324380961f375b10f3020f99b933b30a47cc982e2cc083e4e05d0cbf31f26a453708c0f91e9e2f1b7c7c83cb59c2c63e2ffaeaf3c1
def s110:ℕ:=0x1faa129bd0cc8fd27d41ff0047e84d1082b543f38851025c71f95a9a585898fc7de516f88c7e35ed991f503f0c7b146af41f85b898e96e8fc11c168e77c7e0300b9b13c3ef94287bce01f78e390518f8fba7d34d7e087dcd4e6307ce3ecbfdf486e4
def s111:ℕ:=0x1fda354594ac8febef7c9dce07f518a7e02663f9df26cc7da1fcc80d76a208fe5ce905ae407f15e033217a3f8aa379f1021fbf6964ce660fdfb2beb7f087ef80f35b4703f6fdceeb57d1fb72aa5f1d80fd8ddcfc2f447ebf760b3d763f547eeeadce
def s112:ℕ:=0x201e094015fa100e07b4f70ac806e81262c2440352fffc7df201993cfb0379006d53f0eb288026ae9bccea400db5b974f620010ffdc5ca0ffed6f7092707fe4980051ba3fd22c7cb19d1fe807a362a80ff01742130dc7f7eb7d5bcd83fb86a712957
def s113:ℕ:=0x20640a2560579030ef38d8a648174d81653f640b5fe0772ba20594ce731af102c47b06edd8814d21a3f8024096b126f35a20440e4df363901e6975cda2880f12e7880c6406dd40089962036d1b8cf26901b358e6ba8080d3191e41044064c2d25d55
def s114:ℕ:=0x20a36afc815e1050cb76c8440826a533739ec4131e37be9dd2095367f952390458f83bc024821e614dfdf441086c852a33207cff9657289039e20d8889481b7d37d37e840da2989dc3e206c2d826e2b103592ff5749481ac909f78ac40cdece7a4b0
def s115:ℕ:=0x20f694a2a453907a78381c03483d24895c30441e26e052ab120ef44c683879075ed09e9f1c83ae9ad3cc5e41c27e2a06ff20d762fa358e106ba5d4c1bc88322a3b68134418fd46f614320b5d4f5f67a1058f92467ebc82c315889eaa414ef3b69f6c
def s116:ℕ:=0x215d09b4e53410ad401138b98854c060f17f842a2ca046f29214da0abd6fa10a2705d674f8850abf3e536642717af7aadd212e366b8d611096a114a942084ac17d929924247f68e826b2119aa4791cc908b6120d96c0841d66c7f02442045aae1e55
def s117:ℕ:=0x21d1761d724c90e8a6e7d15ec874045f00094438d1c1f26b021b4696d30a690da2f01a8a0886cbdb80ad08435c705f2b9d219aef48e70010c9d2ecda31c8648a9063d2842fd7c1210e821725c0a98e410b7a2e0981b085bcd70423fa42c7b9ac7a0e
def s118:ℕ:=0x2216f44a52639108eaae8ee848844e332583a44104241f52121fdc74baa3610fe9636873f087d5cd3ab90243e9f552451621ec5757429910f41c4e4af9c8795b186dde843bc319fb6b521da01af347110ec862b1ed00876224e6d7ba43a3f289df55
def s119:ℕ:=0x228b231913fd1144a0f9a96648a1c4ad8c36e44fc5d18277e227854f7966e913b2ceeb9ec089d194cee06844e853c263822270fd501e7d9120a9de70de488edc67e538e446e234e216c222e84dfd1f69116dff03d2088872b2c2bc7c443471b32c31
def s120:ℕ:=0x231503cd787a118802e0727288bfb7633c4d845e88ed00c2622e33d65756391709d14cb46c8b38f8324b484594177ccf8022c9557f653791610d3b5e7688b04e81a59f24566711a1fda22a4ecb1332d1150e299681548a62414036084520102e4f59
def s121:ℕ:=0x237d23327d1c11b2758f281748d793fe4952646b650b887d02355b00da7e411a3073f8d7408d043724cd3246784bedf0f1233804054889919a8c8b120b88ccfd6fc4904465e07802373232625ab5458118c8ce28cbe48c6082d5dbba462ef92f9aed
def s122:ℕ:=0x23e945a492da91f40955fa7f08f7eee778dbe47abe2f269b023cb1b595de611e354b968db08f14ee4e5c7e477527f7c5a623b7ec73576e91d81db84b8bc8eb33e0d63e8474e20e23df723a1dcf5b60b11c58495aaf1c8e00ec9a5bc646febd6836df
def s123:ℕ:=0x2457b83137ee92281e504bdbc91126ce4e5e8486a0e3a48f62433b42a873192196a789b31c90ca2fd5dac24860754d24f1240a760030cc1204b3b29d530900202f4ec9447f829ce1c4723f8d99f13cc91fb1df9cb9d48fcf0673cb0447da146009ea
def s124:ℕ:=0x24d13d5097c29262c5afac2bc92e4f4925f1a4968fda2a00524b38d7ad34112590da780af892c295d3d1324956213ff061249c165c261b924ac6a6231449239d562c8d8490b7a8e2ab024835144ce66123e6d9dbee8c9178cab5cd0a48bb56bff05f
def s125:ℕ:=0x2537abfb1112929ac48a7aec094b0f7a2606e4a5534781e522526e6ebb95d1290524c2dc289441c349a3204a127b79302d2500c2c40d8c127bc1f78c37493c52806227c49da7b1b2fab24e3521aa7d5126f10d230d3893719bbc67e849b5416e2dc7
def s126:ℕ:=0x25a3da2822e892cba7d67c7749659a63af4c64b136ea6993c258461559dfb92c1363e7bb1c95e4f96a60c24ae86549f4f425735958b3c112b71f3bcc37495a1c52b53324ad0436de936255f963d655f12ab209f495b09548f87660524a8c7c0f302d
def s127:ℕ:=0x26354d0237949319929b4a20898c4fe2e62ce4c547085afc726203d20b54c930f140f73eb498783491ccd84c2a86c044b5260aada97abb93021fa54c40c97b4ca57c4144bcaa9c5acb025d34199fc0912e53e495229c96aeef91c3864b480cd2a77e
def s128:ℕ:=0x26c1407798f7935ae28ac80c09aaa3ff722d24d3671ebc881269520b0b6d8134620274c92c9a19007e63da4cddae71ce00266e12398f4a1324c08169470991bc630e1144c8a7f8731bf263a433ced6f931bce001f5ac98dc6dab65ba4c6da6610c7c
def s129:ℕ:=0x27194114992e9388d3f03d2089c29b35f47da4df930edcfd526f2f11474c11375047826d0c9b9764294ed84dc1c562451726e04994e0ab136e204f4c8ac9b6023da57324dadce5173dd26d42e86db12136902045c31c9b2cc65ca6b04d83d4f93735
def s130:ℕ:=0x278b604bd05113c51a776726c9e193fb34f9a4f0283953351277a81d731b713bce7e74c71c9ddacb9a69ba4ec1b9034ae9275ec72e14a313a680e4587b89d24fd575df24e89d8fd2eb0273da751de111396a090cca0c9caecc02d7324e488229326f
def s131:ℕ:=0x27f4b84c77d813f92e627fccc9f81095a67464fbe916f418627d81914c65393e85f52f9b6c9ed4f61d94de4f6579e4aa8227afafeafd4713d6d2781a1b09ea9089667724f5283e5334127a60276bced93c7ea663b2649e3481518bf84f18f0c01b04
def s132:ℕ:=0x287243359a149431eafd04650a18cc1836ec050b1a65ca05d2847a0a256cc9420cc0ad3f20a100ed5b062450701c1df0f1283037b8785a94162b2263910a0a59a6f0e3250433728f2c728167ea47aee94092150cce44a02fcfb6eb424fee8b6b9570
def s133:ℕ:=0x28e143e89a52946e96da496d4a34d3c7236dc51a4b93974bb28c9675a59e3946421fe4d49ca31db3aedb20517a87a334e328b70b59d02d145b25312db74a2c50e7a68b2514a982b7be728a4841a585814496f3745dd0a217c96faa4250e511a06b82
def s134:ℕ:=0x29544fe838d814a9a93ad8978a54aa80d8274528ce84aed612945449b9a87949d2246cd564a4c952b85904524288b3351b291987f2d587147fb63c1ba64a3f1a354ec9451edda9c3c4d28f6440b9a5a947b20df5a624a3b91eb3c43251c7477bc6df
def s135:ℕ:=0x29f5e1de1c6e94f91045fb608a7b7057dd7e6536e709c2f9929b0899299a994d68ec4e03eca67ff9f0986e531e72d99ccc298a04a2338314bc61a9bee8ca5e18bd2b66652eccd014627297133203a6394b2b99dd501ca5888b17962652ac2c4077dd
def s136:ℕ:=0x2a468fda8ce51521ca1188894a902cc82add254759e3772ba2a2045f89b0f950f34a6506a8a8746fd9237e5432fbc970e02a18fee61ae3950a2c7934640a834e8c7eb9854108b9936272a041bb619581501bcc5ce9f8a805635691aa53f28bb13675
def s137:ℕ:=0x2ac46fa4941095606555fdb1caaf2552337325570a33c20852ab3e783f9d81558f634eba08aabfba454efc555ebe6b2f4c2aa17fdb907b1550a362cdb0caa651b026dea552b5b37f9dd2a9546af9b63954a23624dc3caa2362ee2d5854de0847f099
def s138:ℕ:=0x2b7148229be095b53afe43a60ada259c76f8e56cfbc9d02c42b63b351da5815aeb2cac570cad2e10c0fad6567f0c57076d2b357959dd6e959aa3efce01cac9b3fe7633255ce5393f8122ae664caa453956e4b1140104ab5122de59ac55908e0536fb
def s139:ℕ:=0x2c137f1fbad81608a493ce33cb041f151ea1e5820c46f78c72c08a2b2669815fdb9f2b62c4afb923ee718a57ce339e53582bde9bcfb94c95eec63dbb790af55145ef7ba573c90c738252b91fa798f4a15c55fb873800adca71a9cd7256e3708f6f82
def s140:ℕ:=0x2d4e337b7a4c96a425994e9ecb4d12bea74465a5315c2c1f42d14dc937eef1661a576cdac0b2e0b7f6738e593493f339412c9667a599cc9648df95c03d0b24527b2725a58ea21ab3cde2c7149e69ccc9624a4bb4e3a4b0c610966104585c929f38ad
def s141:ℕ:=0x2ea24d699e189740a689cee5cb9b133c2770e5ca8e81e7fde2e3c4ca69d9d97117144ae2c0b81f1625778e5c0bfea2b5992dfd4c3d9d8596e0ab4ba0bd0b6d2a1457dbc5b5a97db3b2b2d9d4ba99d3996c4a5c74eaa4b5cc5aedef605abff386fac7
def s142:ℕ:=0x303245f2fdd817ff946d7fb1cbff13e827bce5f929e613d252fb14f049e9697ca05c580778be22e6e38be85f04f44a3ab02f575d151ee39780a6facf20cbbd0ff3481bc5de1dc0604f42ed2ae573cd8176526c8cf084baf72c9ced325d5f229e7cc7
def s143:ℕ:=0x32615361a035992c29aa5015cc8414b7a802663eca57f401d31f552b79feb98f8a961d00dcc595472e7e9e62aca3af3f9d30e211c0de5818537a506ff1cc1e541727cba60e2a0753e01306050289f0f982527fecf724c0f93f9e7b9a6067ae91c2de
def s144:ℕ:=0x36745a02a2b99b2cacfc51714d93567168a766c82b35f453f35b458cca24f9a912bf6d1064d3855e4687d6699aaeb34393346656aba1729a28ab4450b54d08558fa851267c4abab4259338c5556a10d99b4aa9550844cc65524a82e26560a81d4153
def s145:ℕ:=0x3b2a61b1a5b89d48305852a3ce8857ff6942673d2bf5d49f939e45fb2a5099cac2f5d524ace5257b1a92f27104bab3480138795d4ca3f69c272e8dd2054e0d5739e8fae7062b9ad47a937d15c5fa3cf9bc32de1d1b94dae16a128c2e6d02b44145b5
def s146:ℕ:=0x41e16c99a9dda0e93652d502502e5ab2aa5028140d52d5243403c6a0ea9059ff8b4b954544fc15a00ea0be7d9ccf3f4ffd3ea66777a8069f00b325d3b9cf54594f29c7a7a20c9c14e0f3cfc64a8a6db9e08b192531f4ee7589d6983676f4c4934c11
def s147:ℕ:=0x47ad75fdad65a3c4baf356c251a51d1aab4068d02e8cb5a234616737bac8aa2eab98fd639d1705cb9eb11e8b02e4ed581944fe71d3ac02a222384255b3d1085c162ad8a87a2df81562543686f3cab03a1aab777d559d09c9b636a91284dadb2354a3
def s148:ℕ:=0x4a4c7b2eb005a508bd4757d252765e612bafa9380f3315dff49ba7969aed0a4d53cdad79a525c5e4cebbae927af15b5d2b492e7957af4ea46abc43d76dd2141ddfab9669054ee035c0147f976ccadfea3f43b3956d6d1f75a880df388f62ec1d5af9
def s149:ℕ:=0x4db8805ab1c5a6af3fabd88b533b1fb1ac3f6994afc77616f4c897e9cb136a6443f6e58b9d3185f806c31698bcfc4761d54c057d0bb017a5c63e3057f9d2da9f416c2f296acf85f5ffd4b4d7c95b06da5823df65807d2bc5edd2be9a95d2f7355fb1
def s150:ℕ:=0x51008638b44fa864c29b59c6541b21322cdeea0bb08336593503d84b1b391a80c41fa597dd40360f26cb669ea3059f653f4f30824eb239a7894148d95053c060aaacb229d0502bb63f94e598102b1c8a718c04958b85376601a2c6ca9b8b014763ff
def s151:ℕ:=0x53b98a04b566a9bac4abda7dd4d12248ad3e6a67913cd6b7b533888c4b49ba990449b5a98d4b5220f2d1fea5130f4168455241879db479a90f4407da835471a1bfed15aa3830d2167d551ae868bb3faa8bcc35c5a2d544aa15b6cd52a2050a8b66b9
def s152:ℕ:=0x58219139b82dac034873dbfb55e96436ee11eaea91ee56e5356e18eaeb6d4ab6ec772db8ed5aa63b4add02ace11ca16def56698ed4b77eaaea46d25b73d551a306ed78aaa6318d76ca755298c1eb60caa6d45dcdafc552d62c9ed5eea8f516db6c19
def s153:ℕ:=0x5d0198bbbac3ae4b4c5bdd975725663deedaeb6e12c41736f5b5996f0baa2ad9e4b405d29d6ce656f2e61ab6652c2b73e95b119594b98ead0eca74dcecd66724dfae3d6b33327417235596292c9b870ac86c91adc16d63864b8ae442b1232359705d
def s154:ℕ:=0x60a49f5cbdbfafdf582667d2d7e776687a0b6bf2539fb78e95f919ccabc38afc64e675e22d7de674f2f33abe99bccfd62f5f4a9d25bce4af9d57246706d7c3abc673c82be0fc729dc755ef19be2bbf8aef84d775e04d75fa65deebfabacb328775bf
def s155:ℕ:=0x63e9a3d8beeab1f0d238dfcad8ea28df2fb4ec6b147957eeb6336a2ebbebab19051845f77d8b4688c2f98ac59344ad7d296269a20abea8b0ff50c9df4d586f68146f646c335404b7b19618aa071bdf0b0b24ffa5ecbd83c67e8ef6eec1c33e137a5b
def s156:ℕ:=0x67e2aacdc1ecb3e2551560b0d9b6aa3670402cda3527f82df66b1a87ec0ccb326541b6076d98c69f9302dacc2b4ebf8087660ca838c12bb2db5369e00d595669b63020aca114bc57fbb64c1a557bf97b25b52cfdff7592ca98070142c8fb4a3b7f4b
def s157:ℕ:=0x6be0b0d8c3efb5a6d81ce1f4dace6c1d310dad61d5ff787d56a91aeccc336b53f5763e1a35a9b6b9b70bd6d3a55b03855169c1ae0dc349b4ccd6b9616c5a5e2b5930baed15957a1844768a1aba5c201b424d5d3612e5a106ab9b0672cfcb5557838f
def s158:ℕ:=0x6ff4b7acc6afb7e85be06373dbe86dea71bf6dd8b6af78b4f6eb5b5c7c60bb738da8d62d05b8ead4a717a2dc536a858c216e22b4b5c58cb6f75a17e29b5b406cc0313ead96365b78a476ca4b292c4e9b64cd8fa62275b206c7cf11aed8a1637d88d3
def s159:ℕ:=0x7492bf85c9e4ba20df47e49fdd062f8d3242ee7a37c39927d7398bd9ac8f5b98ede44e42cdcbf2f3bb2396e4a376d19015721dbb55c82db9055d6ee3e25c71aea8f1f4ae2cd74af8fcd70f1b902c700b834dc47638e5c186e1071b56dff96f0d8cfb
def s160:ℕ:=0x79a1c71ecc64bcaa63a56670de43b19ff317af1db8ce398e37834c4e2cb99bc10e26ee5d4ddefb12cf2f8aeeeb872f9617773cc388cb3bbb9ce1d565b05d8c706db29d2ec51843995c77626c18bca52bac2e071e527dd5ab02472862ea9380219365
def s161:ℕ:=0x7fe1d179d07dbfdee8c6e85adfa133d933f1efcbd9dcf9edd7e09cec6cfa4befce716678b5f7c7394b3d22f96598db9d497c55cbffce93be2865c86713df0072caf384ef79b954b9b7b7ae0c976cd81bd50e49c66c15e90b20e73382f423900999bd
def s162:ℕ:=0x8696dc43d48ac2e66da06a29e16c76bbb50730911b1d9a687847dd8c1d321c1fd6c24e99860f075f1f4b9f064bae37a5af827ad595d1fcc128ea9d68e4608a3554b483703a3a941a3658171d454d1c6c036691f685ae015b496f43ab004ba367a0df
def s163:ℕ:=0x8ecee99fd9a6c6b8f3c56c78634b79b7762171a29ce39b1bf8cc0e648d85fc5c0f231ebdde2d0b90975ef31603c6adae598ab2e2f1d718c4c8f09e6b43625c384bb5a6711abbf9faba788a4df9ad5d1c3d0ef0aeaa8e1e7b78df55db0d53b891a8f5
def s164:ℕ:=0x9a35fc07e09bcc8a7d297004e6027e2037d0b2e43ee9bbdf39706f6fbdec2caeefa7ceef4e54c7d09b771329f1e749baf793b1f172dc90c9a0f87fee47e4babc13770d3230bdbd7b66f9151edd8db5ac86e767b6d76e3d87aac768971eb3d4c9b3bd
def s165:ℕ:=0xab96183feb63d4b50a5c750569cf844c7a2c74a241b55ceb1a2e60a23e5ffd0a683d77292e82e81a73929b3e7e08afc7bd9e8e0315e34dce988080714be7187fe3b87d33645fb53c2a1
def table (i:ℕ):ℕ:=match i with
 | 0=>s0
 | 1=>s1
 | 2=>s2
 | 3=>s3
 | 4=>s4
 | 5=>s5
 | 6=>s6
 | 7=>s7
 | 8=>s8
 | 9=>s9
 | 10=>s10
 | 11=>s11
 | 12=>s12
 | 13=>s13
 | 14=>s14
 | 15=>s15
 | 16=>s16
 | 17=>s17
 | 18=>s18
 | 19=>s19
 | 20=>s20
 | 21=>s21
 | 22=>s22
 | 23=>s23
 | 24=>s24
 | 25=>s25
 | 26=>s26
 | 27=>s27
 | 28=>s28
 | 29=>s29
 | 30=>s30
 | 31=>s31
 | 32=>s32
 | 33=>s33
 | 34=>s34
 | 35=>s35
 | 36=>s36
 | 37=>s37
 | 38=>s38
 | 39=>s39
 | 40=>s40
 | 41=>s41
 | 42=>s42
 | 43=>s43
 | 44=>s44
 | 45=>s45
 | 46=>s46
 | 47=>s47
 | 48=>s48
 | 49=>s49
 | 50=>s50
 | 51=>s51
 | 52=>s52
 | 53=>s53
 | 54=>s54
 | 55=>s55
 | 56=>s56
 | 57=>s57
 | 58=>s58
 | 59=>s59
 | 60=>s60
 | 61=>s61
 | 62=>s62
 | 63=>s63
 | 64=>s64
 | 65=>s65
 | 66=>s66
 | 67=>s67
 | 68=>s68
 | 69=>s69
 | 70=>s70
 | 71=>s71
 | 72=>s72
 | 73=>s73
 | 74=>s74
 | 75=>s75
 | 76=>s76
 | 77=>s77
 | 78=>s78
 | 79=>s79
 | 80=>s80
 | 81=>s81
 | 82=>s82
 | 83=>s83
 | 84=>s84
 | 85=>s85
 | 86=>s86
 | 87=>s87
 | 88=>s88
 | 89=>s89
 | 90=>s90
 | 91=>s91
 | 92=>s92
 | 93=>s93
 | 94=>s94
 | 95=>s95
 | 96=>s96
 | 97=>s97
 | 98=>s98
 | 99=>s99
 | 100=>s100
 | 101=>s101
 | 102=>s102
 | 103=>s103
 | 104=>s104
 | 105=>s105
 | 106=>s106
 | 107=>s107
 | 108=>s108
 | 109=>s109
 | 110=>s110
 | 111=>s111
 | 112=>s112
 | 113=>s113
 | 114=>s114
 | 115=>s115
 | 116=>s116
 | 117=>s117
 | 118=>s118
 | 119=>s119
 | 120=>s120
 | 121=>s121
 | 122=>s122
 | 123=>s123
 | 124=>s124
 | 125=>s125
 | 126=>s126
 | 127=>s127
 | 128=>s128
 | 129=>s129
 | 130=>s130
 | 131=>s131
 | 132=>s132
 | 133=>s133
 | 134=>s134
 | 135=>s135
 | 136=>s136
 | 137=>s137
 | 138=>s138
 | 139=>s139
 | 140=>s140
 | 141=>s141
 | 142=>s142
 | 143=>s143
 | 144=>s144
 | 145=>s145
 | 146=>s146
 | 147=>s147
 | 148=>s148
 | 149=>s149
 | 150=>s150
 | 151=>s151
 | 152=>s152
 | 153=>s153
 | 154=>s154
 | 155=>s155
 | 156=>s156
 | 157=>s157
 | 158=>s158
 | 159=>s159
 | 160=>s160
 | 161=>s161
 | 162=>s162
 | 163=>s163
 | 164=>s164
 | 165=>s165
 | _=>0
def slope (i:ℕ):=table (i/16)/(2^(49*(i%16)))%2^49
def readCurve:ℕ→ℕ→ℕ→ℕ→ℕ→ℕ→List Piece
 | 0,_,_,_,_,_=>[]
 | n+1,code,prevBase,prevSlope,prevStart,start=>
  let stop:=code%16384
  let si:=code/16384%2^12
  let digits:=code/2^26%2^5
  let payload:=code/2^31
  let difference:=payload%(16^digits)
  let predicted:=prevBase+prevSlope*(start-prevStart)
  let base:=if difference%2=0 then predicted+difference/2 else predicted-difference/2
  let sl:=slope si
  ⟨stop,base,sl⟩::readCurve n (payload/(16^digits)) base sl start stop

def curve (code:ℕ):=readCurve (code%65536) (code/65536) 0 0 0 0
end Codec0

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace OP
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 300000

variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" =>MvPolynomial (Fin 3) K
local notation "PE" =>MvPolynomial (Fin 3) E

theorem DHH {R:Type*} [CommRing R] (A H G:R):
    filteredCut 0 (fun _:Fin 1=>A) H G=A:=by
  simp [filteredCut,Fin.sum_univ_succ]

def AWE (ell:Poly):PE:=
  MvPolynomial.C (algebraMap (RatFunc K) E (RCN202.PF K))-
    CD K E ell

abbrev GDI (F A R:Poly) (C:AU K F A R):
    AU K F (filteredCut 0 (fun _:Fin 1=>A) 1 0) 1:=
  ⟨C.1,by
    classical
    apply (AJF K).mpr
    constructor
    · simpa only [DHH] using AAS K F A R C
    · intro h
      have hz:BR K C.1 (1:Poly)=0:=by
        apply RingHom.mem_ker.mp
        change (1:Poly) ∈ RingHom.ker (BR K C.1).toRingHom
        rwa [FB K C.1]
      exact one_ne_zero (by simpa only [map_one] using hz)⟩

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem APL (P:Ideal Poly) [P.IsPrime]
    (f:AJ K P→ₐ[K] E) (A:Poly):
    MvPolynomial.eval (GM P f) (CD K E A)=
      f (BR K P A):=by
  have h:=AlgHom.congr_fun (ALG P f) A
  change MvPolynomial.eval (GM P f)
    (MvPolynomial.map (algebraMap K E) A)=_
  rw [MvPolynomial.eval_map]
  exact h

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem APM (P:Ideal Poly) [P.IsPrime]
    (f:AJ K P→ₐ[K] E) (A:Poly) (hA:A ∉ P):
    MvPolynomial.eval (GM P f) (CD K E A) ≠ 0:=by
  rw [APL]
  intro h
  apply hA
  rw [← FB K P]
  exact (map_eq_zero_iff f f.injective).mp h

theorem VX
    (F A R ell:Poly) (C:AU K F A R)
    [Algebra (RatFunc K) (AJ K C.1)]
    [IsScalarTower K (RatFunc K) (AJ K C.1)]
    [FiniteDimensional (RatFunc K) (AJ K C.1)]
    (hj:algebraMap (RatFunc K) (AJ K C.1)
      (RCN202.PF K)=BR K C.1 ell)
    (f:AJ K C.1→ₐ[RatFunc K] E):
    let mu:=CD K E
    let v:=GM C.1 (f.restrictScalars K)
    MvPolynomial.eval v (mu F)=0∧
      MvPolynomial.eval v (AWE (E:=E) ell)=0∧
      MvPolynomial.aeval v (mu A)=0∧
      MvPolynomial.eval v (mu R) ≠ 0∧
      UK (mu F) (AWE (E:=E) ell) (mu A) v:=by
  let C0:=GDI F A R C
  have hj0:algebraMap (RatFunc K) (AJ K C0.1)
      (RCN202.PF K)=movingValue C0.1 1 0 ell 1:=by
    simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero]
      using hj
  have h1:(1:Poly) ∉ C0.1:=_Q6 K _ _ _ C0
  have hcert:=RCN202.VX F 1 0 ell 1 0
    (fun _:Fin 1=>A) C0 hj0 h1 f
  have hc:
      MvPolynomial.eval (GM C.1 (f.restrictScalars K))
        (CD K E F)=0∧
      MvPolynomial.eval (GM C.1 (f.restrictScalars K))
        (AWE (E:=E) ell)=0∧
      MvPolynomial.aeval (GM C.1 (f.restrictScalars K))
        (CD K E A)=0∧
      MvPolynomial.eval (GM C.1 (f.restrictScalars K)) (1:PE) ≠ 0∧
      UK (CD K E F) (AWE (E:=E) ell)
        (CD K E A) (GM C.1 (f.restrictScalars K)):=by
    simpa only [map_one,map_zero,
      JF,AEY,DHH,one_mul,mul_zero,
      sub_zero,AWE] using hcert
  exact ⟨hc.1,hc.2.1,hc.2.2.1,
    APM C.1 (f.restrictScalars K) R
      (_Q6 K F A R C),hc.2.2.2.2⟩

section WeightedEmbeddings
variable {I:Type} [Fintype I]
  (P:I→Ideal (MvPolynomial (Fin 3) K)) [∀i,(P i).IsPrime]
  [∀i,Algebra (RatFunc K) (AJ K (P i))]
  [∀i,IsScalarTower K (RatFunc K) (AJ K (P i))]
  [∀i,FiniteDimensional (RatFunc K) (AJ K (P i))]
  [∀i,Algebra.IsSeparable (RatFunc K) (AJ K (P i))]

theorem DOP (weight:I→ℕ):
    (∑ z:(Σ i,AJ K (P i)→ₐ[RatFunc K] E),weight z.1)=
      ∑ i,weight i*Module.finrank (RatFunc K) (AJ K (P i)):=by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,AlgHom.card,mul_comm]

end WeightedEmbeddings
end
end OP
end MergedPart0
section MergedPart1
namespace DFC
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217 RCN248
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}

end
end DFC
end MergedPart1
section MergedPart2
namespace BEN
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN208 RCN217 RCN244 RCN248 RCN313
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
variable {K I E:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "PK4" =>MvPolynomial (Fin 4) K

def YA (D:Ideal PE):PK4→+*IT E D:=
  (Ideal.Quotient.mk D).comp ((CD Ω E).comp
    (surfaceMap (AL K)))

def slicePoint (S:Stage K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:AJ Ω C.1→ₐ[Ω] E)
    (D:Ideal PE)
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (GM C.1 emb):PE→ₐ[E] E).toRingHom):
    PointOn E D:=⟨GM C.1 emb,hD⟩

theorem CMD
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:AJ Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (GM C.1 emb):PE→ₐ[E] E).toRingHom)
    (F:PK4):
    pointHom E D (slicePoint S C emb D hD) (YA (K:=K) D F)=
      emb (BR Ω C.1 (surfaceMap (AL K) F)):=by
  change MvPolynomial.eval (GM C.1 emb)
    (CD Ω E (surfaceMap (AL K) F))=_
  exact OP.APL C.1 emb _

theorem DXH
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:AJ Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (GM C.1 emb):PE→ₐ[E] E).toRingHom):
    Ideal.comap (YA (K:=K) D)
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom)=
        QP S C:=by
  ext F
  change pointHom E D (slicePoint S C emb D hD) (YA D F)=0 ↔
    surfaceMap (AL K) F ∈ C.1
  rw [CMD S C emb D hD,
    map_eq_zero_iff emb emb.injective]
  change surfaceMap (AL K) F ∈
    RingHom.ker (BR Ω C.1).toRingHom ↔ _
  rw [FB Ω C.1]

theorem FEX
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (D:Ideal PE) [D.IsPrime]
    (hcarrier:CD Ω E S.G ∈ D):
    YA (K:=K) D (originalData S C).factor=0:=by
  change Ideal.Quotient.mk D
    (CD Ω E
      (surfaceMap (AL K) (originalData S C).factor))=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact D.mem_of_dvd (map_dvd (CD Ω E)
    (originalData S C).factor_dvd) hcarrier

def AKZ
    (S:Stage K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    IT E D:=
  Ideal.Quotient.mk D (CD Ω E
    (_Q2 (AL K) S.F (RCN326.w+1)))

def ZA (D:Ideal PE):IT E D:=
  Ideal.Quotient.mk D (CD Ω E
    (MvPolynomial.C ((-(AL K) Polynomial.X)^(RCN326.w+1))))

theorem BQY
    (S:Stage K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    AKZ S D=YA (K:=K) D
      (numerator K S.F (RCN326.w+1))*ZA (K:=K) D:=by
  simp only [AKZ,ZA,YA,
    ALA,map_mul,RingHom.comp_apply]

theorem BKK
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (RCN326.w+1))
    (C:CM S) (emb:AJ Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (GM C.1 emb):PE→ₐ[E] E).toRingHom)
    (hcarrier:CD Ω E S.G ∈ D):
    AKZ S D ∈
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom)^
        FO S (DN S hproper) C:=by
  let phi:=pointHom E D (slicePoint S C emb D hD)
  let J:=RingHom.ker phi.toRingHom
  letI:J.IsMaximal:=RCN017.AWX phi
  have hf:=FEX S C D hcarrier
  have hc:=DXH S C emb D hD
  have h:=AGK S hproper C
    (YA (K:=K) D) 0 (AKZ S D)
    (ZA (K:=K) D) J
    (by rw [hf];exact Ideal.zero_mem _)
    (J.zero_mem) hc (BQY S D)
  simpa [J] using h

theorem CXZ
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (C:CM S) (emb:AJ Ω C.1→ₐ[Ω] E)
    (D:Ideal PE) [D.IsPrime]
    (hD:D≤RingHom.ker
      (MvPolynomial.aeval (GM C.1 emb):PE→ₐ[E] E).toRingHom):
    pointHom E D (slicePoint S C emb D hD)
      (YA (K:=K) D (polyH K S.F)) ≠ 0:=by
  rw [CMD S C emb D hD]
  intro hz
  have he:=(map_eq_zero_iff emb emb.injective).mp hz
  apply RCN312.JX S C
  rw [← FB Ω C.1]
  exact he

theorem BWR (F:PK4):
    CD Ω E (surfaceMap (AL K) F)=
      surfaceMap ((algebraMap Ω E).comp (AL K)) F:=by
  simp only [RCN208.CD,RCN136.surfaceMap,
    RingHom.comp_apply,MvPolynomial.map_map]

theorem EAS
    (D:Ideal PE) [D.IsPrime] (point:PointOn E D):
    pointHom E D point (ZA (K:=K) D)=
      algebraMap Ω E ((-(AL K) Polynomial.X)^(RCN326.w+1)):=by
  simp only [ZA,pointHom_mk,
    RCN208.CD,MvPolynomial.map_C,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]

theorem BWP
    (D:Ideal PE) [D.IsPrime] (point:PointOn E D):
    pointHom E D point (ZA (K:=K) D) ≠ 0:=by
  rw [EAS]
  exact (map_ne_zero (algebraMap Ω E)).mpr (AVR (AL K)
    (DI K) (RCN326.w+1))

theorem CAZ
    (S:Stage K I Gamma x p flag errorCap stageSupport) (D:Ideal PE):
    AKZ S D=ZA (K:=K) D*
      (YA (K:=K) D (polyH K S.F))^3*
        YA (K:=K) D (MN S.F (RCN326.w-1)):=by
  rw [BQY,
    show RCN326.w+1=(RCN326.w-1)+2 by decide,
    CAN,map_mul,map_pow]
  ring

theorem AKL (D:Ideal PE) [D.IsPrime] (F:PK4):
    algebraMap (IT E D) (AJ E D)
      (YA (K:=K) D F)=
      BR E D
        (surfaceMap ((algebraMap Ω E).comp (AL K)) F):=by
  change BR E D
    (CD Ω E (surfaceMap (AL K) F))=_
  rw [BWR]

theorem DAU
    (S:Stage K I Gamma x p flag errorCap stageSupport) (D:Ideal PE)
    (hproper:CD Ω E
      (_Q2 (AL K) S.F (RCN326.w+1)) ∉ D):
    AKZ S D ≠ 0:=by
  intro hz
  exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem BRC {A L:Type*}
    [CommRing A] [Field L] (ev:A→+*L)
    (tail base H kappa:A) (w:ℕ)
    (hrel:tail=kappa*H^3*base)
    (hH:ev H ≠ 0) (hk:ev kappa ≠ 0):
    ev tail/ev (kappa*H^(w+3))=ev base/(ev H)^w:=by
  rw [hrel]
  simp only [map_mul,map_pow]
  rw [pow_add]
  field_simp
  <;>ring

end
end BEN
end MergedPart2

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace DSQ
open scoped BigOperators
set_option autoImplicit false
variable {L:Type*} [Field L]

end DSQ
end MergedPart0
section MergedPart1
namespace VI
open scoped BigOperators
open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open JE DSQ
set_option autoImplicit false
noncomputable section
variable {K Ω L:Type} [Field K] [Field Ω] [Field L]

theorem BIH
    (V:Valuation L (WithZero (Multiplicative ℤ)))
    (a:L) (bound:ℤ) (hb:0≤bound)
    (ha:V a≤WithZero.exp bound):RCN187.poleOrder V a≤bound:=by
  unfold RCN187.poleOrder
  apply max_le hb
  by_cases hz:V a=0
  · simpa [hz] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr ha

end
end VI
end MergedPart1

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace EPB
open scoped Classical BigOperators WithZero
open RCN057 (WeightBound)
open RCN002 RCN005 RCN006 RCN026 RCN055 RCN341 RCN095 RCN136 RCN156 RCN187 RCN204 RCN234 RCN313
open DX BX FR
open VI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

section ActualSource
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

end ActualSource
end
end EPB
end MergedPart0
section MergedPart1
namespace AKA
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN026 RCN046 RCN084 RCN095 RCN114
open RCN204 RCN234 RCN237 RCN264 RCN340 RCN341
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {E:Type} [Field E] [IsAlgClosed E]
  {G T H:MvPolynomial (Fin 3) E} {p q:FlagDegree}
  {base: ∀C:AU E G T H,BP C.1}

theorem CUE (U:QZ base p q)
    (C:AU E G T H) (r:FlagDegree)
    (W:Finset (Place E (AJ E C.1))):
    (∑ v ∈ W,flagPole v.val (coordinate E C.1) r)≤
      (U.toFE.weightedCost r C:ℤ):=by
  have hz:=U.zPole C W
  have hy:=U.yzPole C W
  have ha:=U.allPole C W
  simp only [UC] at hz
  simp only [QD] at hy
  simp only [SF] at ha
  have h:=add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    FE.weightedCost,
    QZ.toFE,Nat.cast_add,Nat.cast_mul] using h

theorem FBV (U:QZ base p q)
    (C:AU E G T H) (d w:ℕ) (J V:FlagDegree):
    U.toFE.weightedCost (d • J+w • V) C=
      d*U.toFE.weightedCost J C+
        w*U.toFE.weightedCost V C:=by
  simp only [FE.weightedCost]
  change (d*J.zOnly+w*V.zOnly)*U.zCost C+
      (d*J.yz+w*V.yz)*U.yzCost C+(d*J.all+w*V.all)*U.allCost C=_
  dsimp only [QZ.toFE]
  ring

theorem EHZ (F N R:MvPolynomial (Fin 3) E)
    (hF:F ≠ 0) (p q r:FlagDegree) (hFp:BI p F)
    (base: ∀g: ↥(HR F N),∀C:AU E g.1 N R,
      BP C.1)
    (U: ∀g: ↥(HR F N),QZ (base g) (exactFlag g.1) q):
    (∑ g: ↥(HR F N),∑ C:AU E g.1 N R,
      (U g).toFE.weightedCost r C)≤flagMixed p q r:=by
  exact (Finset.sum_le_sum (fun g _=>
    (U g).toFE.DGB r)).trans
      (ASF F N hF p q r hFp)

end
end AKA
end MergedPart1
section MergedPart2
namespace DOW
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

section ValuationFiltration
variable {A L:Type*} [CommRing A] [Field L]
  (iota:A→+*L) (v:Valuation L (WithZero (Multiplicative ℤ)))
  (hbound: ∀a:A,v (iota a)≤1)

def orderIdeal (n:ℕ):Ideal A where
  carrier:={a | v (iota a)≤WithZero.exp (-(n:ℤ))}
  zero_mem' :=by simp
  add_mem' :=by
    intro a b ha hb
    change v (iota (a+b))≤_
    rw [map_add]
    exact (v.map_add _ _).trans (max_le ha hb)
  smul_mem' :=by
    intro r a ha
    change v (iota (r*a))≤_
    rw [map_mul,map_mul]
    simpa only [one_mul] using mul_le_mul' (hbound r) ha

theorem FOH (J:Ideal A)
    (hvanish: ∀a ∈ J,v (iota a)<1) (n:ℕ):
    J^n≤orderIdeal iota v hbound n:=by
  induction n with
  | zero=>
    intro a _
    change v (iota a)≤WithZero.exp (-(0:ℤ))
    simpa only [neg_zero,WithZero.exp_zero] using hbound a
  | succ n ih=>
    rw [pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have h1:v (iota b)≤WithZero.exp (-1:ℤ):=
      RCN359.CVX (hvanish b hb)
    have hn:v (iota a)≤WithZero.exp (-(n:ℤ)):=ih ha
    change v (iota (a*b))≤WithZero.exp (-((n+1:ℕ):ℤ))
    rw [map_mul,map_mul]
    have hm:=mul_le_mul' hn h1
    have he:WithZero.exp (-(n:ℤ))*WithZero.exp (-1:ℤ)=
        WithZero.exp (-((n+1:ℕ):ℤ)):=by
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    exact hm.trans_eq he

theorem FGI (x:L) (hx:x ≠ 0) (n:ℕ)
    (hn:v x≤WithZero.exp (-(n:ℤ))):
    (n:ℤ)≤ -(v x).log:=by
  have hv0:v x ≠ 0:=(Valuation.ne_zero_iff v).mpr hx
  have hlog:(v x).log≤ -(n:ℤ):=by
    have h:=(WithZero.log_le_log hv0 (by simp)).2 hn
    simpa only [WithZero.log_exp] using h
  omega

include hbound in

theorem EUP {K:Type*} [Field K] [Algebra K A]
    (phi:A→ₐ[K] K)
    (hpoint: ∀a,v (iota a)<1 ↔ phi a=0)
    (n:ℕ) (a b:A) (ha:a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb:phi b ≠ 0) (hx:iota a/iota b ≠ 0):
    (n:ℤ)≤ -(v (iota a/iota b)).log:=by
  have hbval:v (iota b)=1:=by
    apply le_antisymm (hbound b)
    apply le_of_not_gt
    intro h
    exact hb ((hpoint b).mp h)
  have han:v (iota a)≤WithZero.exp (-(n:ℤ)):=
    FOH iota v hbound (RingHom.ker phi.toRingHom)
      (fun a ha=>(hpoint a).mpr ha) n ha
  apply FGI v _ hx n
  simpa only [map_div₀,hbval,div_one] using han

end ValuationFiltration

section ActualAffinePlaces
variable (K A L:Type*) [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
  [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance:IsScalarTower K (RatFunc K) L:=
  IsScalarTower.of_algebraMap_eq fun a=>by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) L]

theorem DQM (phi:A→ₐ[K] K)
    (n:ℕ) (a b:A) (ha:a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb:phi b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0):
    (n:ℤ)≤RCN026.order K L (RCN344.modelPlace K L A phi)
      (algebraMap A L a/algebraMap A L b):=by
  exact EUP (algebraMap A L)
    ((RCN000.BPB K A L phi).valuation L)
    (RCN000.CVU K A L phi) phi
    (RCN000.BWC K A L phi) n a b ha hb hx

end ActualAffinePlaces
end
end DOW
end MergedPart2
section MergedPart3
namespace CVS
open scoped Classical BigOperators WithZero
open RCN026
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem EDY {I:Type*} [Fintype I]
    (x:L) (hx:x ≠ 0) (place:I→Place K L)
    (hinj:Function.Injective place) (mu:I→ℕ)
    (hmu: ∀i,1≤mu i)
    (horder: ∀i,(mu i:ℤ)≤order K L (place i) x):
    (∑ i,(mu i:ℤ))≤
      ∑ v ∈ placesFor K L x hx,RCN346.poleOrder K L v x:=by
  classical
  let U:Finset (Place K L):=Finset.univ.image place
  have hsub:U ⊆ placesFor K L x hx:=by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    apply ALB K L x hx (place i)
    have hi:=horder i
    have hm:(1:ℤ)≤(mu i:ℤ):=by exact_mod_cast hmu i
    omega
  calc
    (∑ i,(mu i:ℤ))≤ ∑ i,zeroOrder K L (place i) x:=by
      apply Finset.sum_le_sum
      intro i _
      exact (horder i).trans (le_max_right _ _)
    _= ∑ v ∈ U,zeroOrder K L v x:=by
      dsimp only [U]
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤ ∑ v ∈ placesFor K L x hx,zeroOrder K L v x:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact AUU K L v x
    _=_:=AJO K L x hx

section Affine
variable (A:Type*) [CommRing A] [IsDomain A]
  [Algebra K A] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
  [IsScalarTower (Polynomial K) A L]

theorem CXI {I:Type*} [Fintype I]
    (phi:I→(A→ₐ[K] K)) (hinj:Function.Injective phi)
    (mu:I→ℕ) (hmu: ∀i,1≤mu i) (a b:A)
    (ha: ∀i,a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb: ∀i,phi i b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0):
    (∑ i,(mu i:ℤ))≤
      ∑ v ∈ placesFor K L (algebraMap A L a/algebraMap A L b) hx,
        RCN346.poleOrder K L v (algebraMap A L a/algebraMap A L b):=by
  apply EDY K L _ hx
    (fun i=>RCN344.modelPlace K L A (phi i))
    ((RCN344.BQJ K L A).comp hinj) mu hmu
  intro i
  exact DOW.DQM K A L
    (phi i) (mu i) a b (ha i) (hb i) hx

theorem BUY {I:Type*} [Fintype I]
    (phi:I→(A→ₐ[K] K)) (hinj:Function.Injective phi)
    (mu:I→ℕ) (hmu: ∀i,1≤mu i) (a b:A)
    (ha: ∀i,a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb: ∀i,phi i b ≠ 0)
    (hx:algebraMap A L a/algebraMap A L b ≠ 0)
    (d cost:ℕ)
    (hpole: ∀W:Finset (Place K L),
      (d:ℤ)*(∑ v ∈ W,
        RCN346.poleOrder K L v (algebraMap A L a/algebraMap A L b))≤cost):
    d*(∑ i,mu i)≤cost:=by
  have hm:=CXI K L A phi hinj mu hmu a b ha hb hx
  have hs:=(mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg d)).trans
    (hpole (placesFor K L _ hx))
  exact_mod_cast hs

end Affine
end
end CVS
end MergedPart3
section MergedPart4
namespace CBG
open RCN057 (WeightBound)
open RCN204 (flagPole)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open DX BX FR
open BEN VI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "w" =>RCN326.w

local notation "φE" =>RingHom.comp (algebraMap (GenericField K) E) (AL K)

theorem EBF
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (old:T→CM S)
    (emb: ∀i,AJ Ω (old i).1→ₐ[Ω] E)
    (hinj:Function.Injective (fun i=>GM (old i).1 (emb i)))
    (D:Ideal PE) [D.IsPrime] (sep:BP D)
    (hpoint: ∀i,D≤RingHom.ker
      (MvPolynomial.aeval (GM (old i).1 (emb i)):PE→ₐ[E] E).toRingHom)
    (hcarrier:CD Ω E S.G ∈ D)
    (hisolated:CD Ω E
      (_Q2 (AL K) S.F (w+1)) ∉ D)
    (e d cost:ℕ)
    (hpole:surfaceMap φE S.F ∈ D→surfaceMap φE (polyH K S.F) ∉ D→
      (∀F0:MvPolynomial (Fin 4) K,
        (∀i,surfaceMap (AL K) F0 ∉ (old i).1)→surfaceMap φE F0 ∉ D)→
      ∀W:Finset (Place E (AJ E D)),
        (d:ℤ)*(∑ nu ∈ W,RCN187.poleOrder nu.val
          (CT.GP φE D (MN S.F (w-1))/
            CT.GP φE D (polyH K S.F)^e))≤cost):
    d*(∑ i,FO S (DN S hproper) (old i))≤cost:=by
  classical
  let A:=IT E D
  let Lf:=AJ E D
  letI:=JI E D sep.index
  letI:=IP E D sep.index
  letI:=DT E D sep.index sep.transcendental
  letI:=MB E D sep.index
  letI:=IU E D sep.index
  letI:=KE E D sep.index
  letI:=_Q5 E D sep.index sep.transcendental
  letI:=IS E D sep.index sep.transcendental
  letI:FiniteDimensional (RatFunc E) Lf:=sep.finite
  letI:Algebra.IsSeparable (RatFunc E) Lf:=sep.separable
  let i0:T:=Classical.choice inferInstance
  let ev:=CT.GP φE D
  let evalPoint:=fun i=>pointHom E D (slicePoint S (old i) (emb i) D (hpoint i))
  let mu:=fun i=>FO S (DN S hproper) (old i)
  let a:A:=AKZ S D
  let H:A:=YA (K:=K) D (polyH K S.F)
  let c:A:=ZA (K:=K) D
  let b:A:=c*H^(e+3)
  let iota:A→+*Lf:=algebraMap A Lf
  have hpi:Function.Injective evalPoint:=by
    intro i j hh
    have hs:=BOL E D hh
    exact hinj (congrArg Subtype.val hs)
  have hmu: ∀i,1≤mu i:=fun i=>YW S hproper (old i)
  have ha: ∀i,a ∈ (RingHom.ker (evalPoint i).toRingHom)^(mu i):=by
    intro i
    exact BKK S hproper (old i) (emb i) D
      (hpoint i) hcarrier
  have hHpt: ∀i,evalPoint i H ≠ 0:=fun i=>
    CXZ S (old i) (emb i) D (hpoint i)
  have hcpt: ∀i,evalPoint i c ≠ 0:=fun i=>BWP D _
  have hb: ∀i,evalPoint i b ≠ 0:=by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota:Function.Injective iota:=IsFractionRing.injective A Lf
  have hHi:iota H ≠ 0:=by
    intro hz
    have hH0:H=0:=hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hH0,map_zero])
  have hci:iota c ≠ 0:=by
    intro hz
    have hc0:c=0:=hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hc0,map_zero])
  have hai:iota a ≠ 0:=by
    intro hz
    exact DAU S D hisolated
      (hiota (by simpa only [map_zero] using hz))
  have hbi:iota b ≠ 0:=by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx:iota a/iota b ≠ 0:=div_ne_zero hai hbi
  have hrepr:iota a/iota b=ev (MN S.F (w-1))/ev (polyH K S.F)^e:=by
    have hh:=BRC iota a
      (YA (K:=K) D (MN S.F (w-1))) H c e
      (CAZ S D) hHi hci
    have hbv:iota (YA (K:=K) D (MN S.F (w-1)))=
        ev (MN S.F (w-1)):=AKL D _
    have hHv:iota H=ev (polyH K S.F):=AKL D _
    exact hh.trans (by rw [hbv,hHv])
  have hnot (F0:MvPolynomial (Fin 4) K)
      (hn0: ∀i,surfaceMap (AL K) F0 ∉ (old i).1):
      surfaceMap φE F0 ∉ D:=by
    intro hmem
    have hz:=RingHom.mem_ker.mp (hpoint i0 hmem)
    change MvPolynomial.eval (GM (old i0).1 (emb i0))
      (surfaceMap φE F0)=0 at hz
    apply OP.APM (old i0).1 (emb i0)
      (surfaceMap (AL K) F0) (hn0 i0)
    simpa only [BWR,MvPolynomial.aeval_eq_eval] using hz
  have hFd:surfaceMap φE S.F ∈ D:=by
    rw [← BWR]
    exact D.mem_of_dvd (map_dvd (CD Ω E) S.RR) hcarrier
  have hHd:surfaceMap φE (polyH K S.F) ∉ D:=
    hnot _ (fun i=>RCN312.JX S (old i))
  apply CVS.BUY E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d:ℤ)*(∑ nu ∈ W,RCN187.poleOrder nu.val (iota a/iota b))≤(cost:ℤ)
  rw [hrepr]
  exact hpole hFd hHd hnot W

end
end CBG
end MergedPart4
section MergedPart5
namespace YE
open scoped Classical BigOperators
open RCN002 RCN007 RCN072 RCN084 RCN095 RCN134 RCN264
noncomputable section
set_option autoImplicit false
local instance {A:Type*}:DecidableEq A:=Classical.decEq A
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {E I:Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" =>MvPolynomial (Fin 3) E

abbrev ANR (F N R:Poly):=
  (g: ↥(HR F N)) × AU E g.1 N R

theorem DIX (F N R:Poly) (point:I→Fin 3→E)
    (hcover: ∀i,∃g: ↥(HR F N),MvPolynomial.eval (point i) g.1=0)
    (hN: ∀i,MvPolynomial.eval (point i) N=0)
    (hR: ∀i,MvPolynomial.eval (point i) R ≠ 0):
    ∃assign:I→ANR F N R,
      ∀i,(assign i).2.1≤RingHom.ker
        (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom:=by
  classical
  have he (i:I): ∃a:ANR F N R,
      a.2.1≤RingHom.ker (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom:=by
    obtain ⟨g,hg⟩:=hcover i
    obtain ⟨C,hC⟩:=AZA E g.1 N R (point i) hg (hN i) (hR i)
    exact ⟨⟨g,C⟩,hC⟩
  exact ⟨fun i=>(he i).choose,fun i=>(he i).choose_spec⟩

omit [Field E] [IsAlgClosed E] in

theorem DKM {A:Type*} [Fintype A] [DecidableEq A]
    (assign:I→A) (mu:I→ℕ):
    (∑ a,∑ i with assign i=a,mu i)= ∑ i,mu i:=by
  classical
  exact Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ)
    (g:=assign) (fun _ _=>Finset.mem_univ _) _

omit [Field E] [IsAlgClosed E] in

theorem EXR {A:Type*} [Fintype A] [DecidableEq A]
    (assign:I→A) (mu:I→ℕ) (cost:A→ℕ) (d:ℕ)
    (hlocal: ∀a,d*(∑ i with assign i=a,mu i)≤cost a):
    d*(∑ i,mu i)≤ ∑ a,cost a:=by
  rw [← DKM assign mu,Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _=>hlocal a)

theorem CLZ (F N A R:Poly)
    (point:I→Fin 3→E) (assign:I→ANR F N R)
    (hpoint: ∀i,(assign i).2.1≤RingHom.ker
      (MvPolynomial.aeval (point i):Poly→ₐ[E] E).toRingHom)
    (hisolated: ∀i,UK F N A (point i)) (i:I):
    A ∉ (assign i).2.1:=by
  let g:=(assign i).1
  let C:=(assign i).2
  exact hisolated i C.1 inferInstance (PU E g.1 N R C)
    (hpoint i)
    (C.1.mem_of_dvd (OJ F N g).2.1
      (EN E g.1 N R C))
    (GV E g.1 N R C)

end
end YE
end MergedPart5
section MergedPart6
namespace AVZ
open scoped Classical BigOperators
open RCN095 RCN237 RCN264 RCN340 RCN341 RCN084 RCN039 RCN046
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
variable {E:Type} [Field E] [IsAlgClosed E]
local notation "Poly" =>MvPolynomial (Fin 3) E

structure SliceBudgets (F N R:Poly) (q:FlagDegree) where
  base: ∀g: ↥(HR F N),∀C:AU E g.1 N R,
    BP C.1
  unit: ∀g: ↥(HR F N),
    QZ (base g) (exactFlag g.1) q

theorem EFX (F N R:Poly) (p q:FlagDegree)
    (hF:F ≠ 0) (hFp:BI p F) (hNq:BI q N)
    (c:ℕ) [CharP E c] (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c):
    Nonempty (SliceBudgets F N R q):=by
  classical
  obtain ⟨base,hY,hZ⟩:=AOE F N R hF p q hFp hNq
    c hdeg hmix
  have he (g: ↥(HR F N)):
      Nonempty (EE (base g) (exactFlag g.1) q):=by
    have hg:=OJ F N g
    exact ACA (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((EI _ _).mpr (ATU g.1))
      ((EI _ _).mpr hNq)
  exact ⟨⟨base,fun g=>(Classical.choice (he g)).toQZ⟩⟩

theorem sum_cost_le (F N R:Poly) (p q r:FlagDegree)
    (hF:F ≠ 0) (hFp:BI p F) (B:SliceBudgets F N R q):
    (∑ g: ↥(HR F N),∑ C:AU E g.1 N R,
      (B.unit g).toFE.weightedCost r C)≤flagMixed p q r:=
  AKA.EHZ F N R hF p q r hFp B.base B.unit

end
end AVZ
end MergedPart6
section MergedPart7
namespace ABB
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN007 RCN084 RCN095 RCN134 RCN135 RCN136 RCN156 RCN159
open RCN207 RCN208 RCN234 RCN237 RCN243 RCN244 RCN248 RCN264 RCN267 RCN313 RCN341
open DX BX FR
open VI OP YE
open AVZ
open RCN204 (flagPole)
open RCN026 (Place)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "w" =>RCN326.w

theorem EET
    (S:Stage K I Gamma x p flag errorCap stageSupport) (C:CM S):
    MvPolynomial.pderiv (1:Fin 3) S.G ∉ C.1:=by
  intro hd
  apply RCN312.JX S C
  change surfaceMap (AL K)
    (MvPolynomial.pderiv (2:Fin 4) S.F) ∈ C.1
  rw [← ZO]
  obtain ⟨Q,hQ⟩:=S.RR
  rw [hQ,MvPolynomial.pderiv_mul]
  exact C.1.add_mem (C.1.mul_mem_right Q hd)
    (C.1.mul_mem_right (MvPolynomial.pderiv (1:Fin 3) Q)
      (EN Ω S.G _ _ C))

def SliceCharge (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (Good:CM S→Prop) (N:PE) (c m n:ℕ) (J V:FlagDegree):Prop:=
  ∀(T0:Type) [Fintype T0] [Nonempty T0] (old:T0→CM S),
    (∀i,Good (old i))→ ∀emb: ∀i,AJ Ω (old i).1→ₐ[Ω] E,
    Function.Injective (fun i=>GM (old i).1 (emb i))→
    ∀(D:Ideal PE) [D.IsPrime],BP D→
    (∀i,D≤RingHom.ker
      (MvPolynomial.aeval (GM (old i).1 (emb i)):PE→ₐ[E] E).toRingHom)→
    CD Ω E S.G ∈ D→N ∈ D→
    CD Ω E (_Q2 (AL K) S.F (w+1)) ∉ D→
    ∀CJ CV:ℕ,
    (∀W:Finset (Place E (AJ E D)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E D) J)≤(CJ:ℤ))→
    (∀W:Finset (Place E (AJ E D)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E D) V)≤(CV:ℤ))→
    c*(∑ i,FO S (DN S hproper) (old i))≤m*CJ+n*CV

theorem DPM
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (old:T→CM S)
    (emb: ∀i,AJ Ω (old i).1→ₐ[Ω] E)
    (hinj:Function.Injective (fun i=>GM (old i).1 (emb i)))
    (N:PE) (q:FlagDegree) (hNq:BI q N)
    (hNpoint: ∀i,MvPolynomial.eval (GM (old i).1 (emb i)) N=0)
    (hisolated: ∀i,UK (CD Ω E S.G) N
      (CD Ω E (_Q2 (AL K) S.F (w+1)))
      (GM (old i).1 (emb i)))
    (hdeg:flag.zOnly+flag.yz+flag.all<p)
    (hmix:2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<p)
    (Good:CM S→Prop) (hgood: ∀i,Good (old i))
    (c m n:ℕ) (J V:FlagDegree) (hslice:SliceCharge S hproper Good N c m n J V):
    c*(∑ i,FO S (DN S hproper) (old i))≤
      flagMixed flag q (m • J+n • V):=by
  classical
  let F:=CD Ω E S.G
  let A:=CD Ω E (_Q2 (AL K) S.F (w+1))
  let R:=CD Ω E (CR (AL K) S.F)
  let point:=fun i=>GM (old i).1 (emb i)
  let mu:=fun i=>FO S (DN S hproper) (old i)
  let D1:=m • J+n • V
  have hF:F ≠ 0:=by
    intro hz
    apply S.MW.ne_zero
    apply MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
    simpa only [F,CD,map_zero] using hz
  have hFp:BI flag F:=inFlag_map _ S.flag_support
  have hFpoint (i:T):MvPolynomial.eval (point i) F=0:=by
    rw [APL]
    have hc:=EN Ω S.G _ _ (old i)
    have hz:BR Ω (old i).1 S.G=0:=by
      apply (RingHom.mem_ker (f:=(BR Ω (old i).1).toRingHom)).mp
      rw [FB]
      exact hc
    rw [hz,map_zero]
  have hApoint (i:T):MvPolynomial.eval (point i) A=0:=by
    rw [APL]
    have hc:=GV Ω S.G _ _ (old i)
    have hz:BR Ω (old i).1
        (_Q2 (AL K) S.F (w+1))=0:=by
      apply (RingHom.mem_ker (f:=(BR Ω (old i).1).toRingHom)).mp
      rw [FB]
      exact hc
    rw [hz,map_zero]
  have hRpoint (i:T):MvPolynomial.eval (point i) R ≠ 0:=
    APM (old i).1 (emb i) _
      (_Q6 Ω S.G _ _ (old i))
  have hDpoint (i:T):
      MvPolynomial.eval (point i) (MvPolynomial.pderiv (1:Fin 3) F) ≠ 0:=by
    have hh:=APM (old i).1 (emb i)
      (MvPolynomial.pderiv (1:Fin 3) S.G) (EET S (old i))
    simpa only [F,CD,MvPolynomial.pderiv_map] using hh
  have hcover (i:T): ∃g: ↥(HR F N),MvPolynomial.eval (point i) g.1=0:=
    AAU F N A R hF (point i)
      (hFpoint i) (hApoint i) (hRpoint i) (hDpoint i) (hisolated i)
  obtain ⟨assign,hassigned⟩:=DIX F N R point hcover hNpoint hRpoint
  let budgets:=Classical.choice
    (EFX F N R flag q hF hFp hNq p hdeg hmix)
  let cost:=fun a:ANR F N R=>
    (budgets.unit a.1).toFE.weightedCost D1 a.2
  have hlocal (a:ANR F N R):
      c*(∑ i with assign i=a,mu i)≤cost a:=by
    let T0:={i:T//assign i=a}
    by_cases hne:Nonempty T0
    · letI:Nonempty T0:=hne
      let old0:=fun i:T0=>old i.1
      let emb0:=fun i:T0=>emb i.1
      have hi0:Function.Injective (fun i:T0=>GM (old0 i).1 (emb0 i)):=by
        intro i j hh
        exact Subtype.ext (hinj hh)
      have hpt (i:T0):a.2.1≤RingHom.ker
          (MvPolynomial.aeval (GM (old0 i).1 (emb0 i)):PE→ₐ[E] E).toRingHom:=by
        have he:assign i.1=a:=i.2
        have hh:=hassigned i.1
        rw [he] at hh
        exact hh
      have hcar:F ∈ a.2.1:=a.2.1.mem_of_dvd (OJ F N a.1).2.1
        (EN E a.1.1 N R a.2)
      let i0:T0:=Classical.choice hne
      have hAz:A ∉ a.2.1:=by
        have hh:=CLZ F N A R point assign hassigned hisolated i0.1
        have he:assign i0.1=a:=i0.2
        rwa [he] at hh
      let unit:=budgets.unit a.1
      let CJ:=unit.toFE.weightedCost J a.2
      let CV:=unit.toFE.weightedCost V a.2
      have hb:=hslice T0 old0 (fun i=>hgood i.1) emb0 hi0 a.2.1 (budgets.base a.1 a.2)
        hpt hcar (GV E a.1.1 N R a.2) hAz CJ CV
        (AKA.CUE unit a.2 J)
        (AKA.CUE unit a.2 V)
      have hsum:(∑ i with assign i=a,mu i)= ∑ i:T0,mu i.1:=by
        simpa only [T0,Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s:=(Finset.univ:Finset T))
            mu (p:=fun i=>assign i=a)).symm
      rw [hsum]
      calc
        _≤m*CJ+n*CV:=hb
        _=cost a:=(AKA.FBV
          unit a.2 m n J V).symm
    · have he:(Finset.univ.filter (fun i:T=>assign i=a))= ∅ :=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hne ⟨⟨i,(Finset.mem_filter.mp hi).2⟩⟩
      simp only [he,Finset.sum_empty,Nat.mul_zero,Nat.zero_le]
  calc
    _≤ ∑ a:ANR F N R,cost a:=EXR assign mu cost c hlocal
    _= ∑ g: ↥(HR F N),∑ C:AU E g.1 N R,
        (budgets.unit g).toFE.weightedCost D1 C:=by
      rw [Fintype.sum_sigma]
    _≤flagMixed flag q D1:=sum_cost_le F N R flag q D1 hF hFp budgets
end
end ABB
end MergedPart7
section MergedPart8
namespace DCJ
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248
open RCN264 RCN313 RCN341 RCN344
open DX BX FR
open VI OP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E A:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
  [Fintype A]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "w" =>RCN326.w

theorem DTB
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (old:A→CM S) (hold:Function.Injective old)
    (ell:MvPolynomial (Fin 3) Ω) (q:FlagDegree) (hell:BI q ell)
    (projection: ∀a,DB Ω (AJ Ω (old a).1))
    (hvalue: ∀a,DB.value Ω (AJ Ω (old a).1) (projection a)=
      BR Ω (old a).1 ell)
    (hdeg:flag.zOnly+flag.yz+flag.all<p)
    (hmix:2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<p)
    (Good:CM S→Prop) (hgood: ∀a,Good (old a))
    (c m n:ℕ) (J V:FlagDegree) (hslice:ABB.SliceCharge S hproper Good
      (AWE (E:=E) ell) c m n J V):
    c*(∑ a,FO S (DN S hproper) (old a)*
      DB.degree Ω (AJ Ω (old a).1) (projection a))≤
      flagMixed flag q (m • J+n • V):=by
  classical
  let oldPrime:=fun a=>(old a).1
  letI: ∀a:A,Algebra (RatFunc Ω) (AJ Ω (oldPrime a)):=
    fun a=>(projection a).embedding.toRingHom.toAlgebra
  letI: ∀a:A,IsScalarTower Ω (RatFunc Ω) (AJ Ω (oldPrime a)):=
    fun a=>IsScalarTower.of_algebraMap_eq fun c=>((projection a).embedding.commutes c).symm
  letI: ∀a:A,FiniteDimensional (RatFunc Ω) (AJ Ω (oldPrime a)):=
    fun a=>(projection a).finite
  letI: ∀a:A,Algebra.IsSeparable (RatFunc Ω) (AJ Ω (oldPrime a)):=
    fun a=>(projection a).separable
  let T:=(a:A) × (AJ Ω (oldPrime a)→ₐ[RatFunc Ω] E)
  let oldT:=fun i:T=>old i.1
  let embT:=fun i:T=>i.2.restrictScalars Ω
  let N:=AWE (E:=E) ell
  have hprimes:Function.Injective oldPrime:=by
    intro a b hh
    exact hold (Subtype.ext hh)
  have hpoints:Function.Injective
      (fun i:T=>GM (oldT i).1 (embT i)):=
    ANW oldPrime hprimes
  have hcert (i:T):=OP.VX S.G
    (_Q2 (AL K) S.F (w+1))
    (RCN243.CR (AL K) S.F) ell (old i.1)
    (hvalue i.1) i.2
  have hNq:BI q N:=
    BBP (inFlag_const q _) (inFlag_map _ hell)
  have hmass:=ABB.DPM S hproper
    oldT embT hpoints N q hNq (fun i=>(hcert i).2.1)
    (fun i=>(hcert i).2.2.2.2) hdeg hmix Good (fun i=>hgood i.1) c m n J V hslice
  have hsum:=OP.DOP (E:=E) oldPrime
    (fun a=>FO S (DN S hproper) (old a))
  simpa only [oldT,embT,T,DB.degree,oldPrime,hsum] using hmass

theorem DKP
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (old:A→CM S) (hold:Function.Injective old)
    (ell:MvPolynomial (Fin 3) Ω) (q:FlagDegree) (hell:BI q ell)
    (projection: ∀a,Coordinate Ω (AJ Ω (old a).1))
    (hvalue: ∀a,FT Ω (AJ Ω (old a).1) (projection a)=
      BR Ω (old a).1 ell)
    (hdeg:flag.zOnly+flag.yz+flag.all<p)
    (hmix:2*(flag.zOnly+flag.yz+flag.all)*(q.zOnly+q.yz+q.all)<p)
    (Good:CM S→Prop) (hgood: ∀a,Good (old a))
    (c m n:ℕ) (J V:FlagDegree) (hslice:ABB.SliceCharge S hproper Good
      (AWE (E:=E) ell) c m n J V):
    c*(∑ a,FO S (DN S hproper) (old a)*
      DQ Ω (AJ Ω (old a).1) (projection a))≤
      flagMixed flag q (m • J+n • V):=by
  classical
  let Alive:Set A:={a | ∃c,projection a=Sum.inr c}
  let sep:=fun a:Alive=>Classical.choose a.2
  have hsep (a:Alive):projection a.1=Sum.inr (sep a):=
    Classical.choose_spec a.2
  let old0:=fun a:Alive=>old a.1
  have hi0:Function.Injective old0:=by
    intro a b hh
    exact Subtype.ext (hold hh)
  have hv0 (a:Alive):
      DB.value Ω (AJ Ω (old0 a).1) (sep a)=
        BR Ω (old0 a).1 ell:=by
    have hh:=hvalue a.1
    rw [hsep a] at hh
    exact hh
  let weight:=fun a=>FO S (DN S hproper) (old a)
  have hsum:(∑ a,weight a*DQ Ω
      (AJ Ω (old a).1) (projection a))=
      ∑ a:Alive,weight a.1*DB.degree Ω
        (AJ Ω (old0 a).1) (sep a):=by
    apply Finset.sum_congr_set Alive
      (fun a=>weight a*DQ Ω (AJ Ω (old a).1) (projection a))
      (fun a=>weight a.1*DB.degree Ω (AJ Ω (old0 a).1) (sep a))
    · intro a ha
      simp only [hsep ⟨a,ha⟩,DQ,Sum.elim_inr,old0]
    · intro a ha
      cases hpj:projection a with
      | inl c=>simp only [hpj,DQ,Sum.elim_inl,Nat.mul_zero]
      | inr c=>exact (ha ⟨c,hpj⟩).elim
  have hb:=DTB (E:=E) S hproper old0 hi0 ell q hell
    sep hv0 hdeg hmix Good (fun a=>hgood a.1) c m n J V hslice
  rw [show (∑ a,FO S (DN S hproper) (old a)*
      DQ Ω (AJ Ω (old a).1) (projection a))=
      ∑ a:Alive,weight a.1*DB.degree Ω
        (AJ Ω (old0 a).1) (sep a) from hsum]
  exact hb

end
end DCJ
end MergedPart8
section MergedPart9
namespace PR
open scoped Classical BigOperators
open RCN002 RCN022 RCN030 RCN037 RCN038 RCN040 RCN042 RCN046 RCN093
open RCN095 RCN207 RCN237 RCN264 RCN340 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 40000
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local notation "Poly" =>MvPolynomial (Fin 3) Ω

def linearZ:Poly:=MvPolynomial.X 2
def linearU (lam:Ω):Poly:=MvPolynomial.X 0+MvPolynomial.C lam*MvPolynomial.X 2
def linearA (mu lam:Ω):Poly:=MvPolynomial.X 1+
  MvPolynomial.C mu*MvPolynomial.X 0+MvPolynomial.C (mu*lam)*MvPolynomial.X 2

private theorem inFlag_X (i:Fin 3) (q:FlagDegree)
    (hi:InFlag q (Finsupp.single i 1)):BI q (MvPolynomial.X i:Poly):=by
  intro e he
  have hh:e=Finsupp.single i 1:=by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
private theorem ELM {q:FlagDegree} {A B:Poly}
    (hA:BI q A) (hB:BI q B):BI q (A+B):=by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
private theorem EBS {q:FlagDegree} {A:Poly}
    (c:Ω) (hA:BI q A):BI q (MvPolynomial.C c*A):=by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem FFR:BI unitZFlag (linearZ:Poly):=by
  exact inFlag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem FDG (lam:Ω):BI unitYZFlag (linearU lam):=by
  exact ELM
    (inFlag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (EBS lam (inFlag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem FFE (mu lam:Ω):BI unitAllFlag (linearA mu lam):=by
  exact ELM (ELM
    (inFlag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (EBS mu (inFlag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (EBS (mu*lam) (inFlag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem eval_linearU (P:Ideal Poly) [P.IsPrime] (lam:Ω):
    BR Ω P (linearU lam)=affineU Ω P lam:=by
  rw [HJ]
  simp only [linearU,affineU,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]
theorem eval_linearA (P:Ideal Poly) [P.IsPrime] (mu lam:Ω):
    BR Ω P (linearA mu lam)=affineV Ω P mu (mu*lam):=by
  rw [HJ]
  simp only [linearA,affineV,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]

variable {G T H:MvPolynomial (Fin 3) Ω} {p q:FlagDegree}
  {base: ∀C:AU Ω G T H,BP C.1}

structure AND
    (unit:EE (Omega:=Ω) (G:=G) (T:=T) (H:=H) base p q) where
  lam:Ω
  mu:Ω
  yzValue: ∀C:AU Ω G T H,
    FT Ω (AJ Ω C.1) (unit.yzProjection C)=affineU Ω C.1 lam
  allValue: ∀C:AU Ω G T H,
    FT Ω (AJ Ω C.1) (unit.NV C)=affineV Ω C.1 mu (mu*lam)

theorem FKV (unit:EE base p q)
    (C:AU Ω G T H):
    FT Ω (AJ Ω C.1) (unit.zProjection C)=
      BR Ω C.1 (linearZ:Poly):=unit.zValue C

theorem ETQ (unit:EE base p q)
    (D:AND unit) (C:AU Ω G T H):
    FT Ω (AJ Ω C.1) (unit.yzProjection C)=
      BR Ω C.1 (linearU D.lam):=by
  rw [eval_linearU]
  exact D.yzValue C

theorem FKF (unit:EE base p q)
    (D:AND unit) (C:AU Ω G T H):
    FT Ω (AJ Ω C.1) (unit.NV C)=
      BR Ω C.1 (linearA D.mu D.lam):=by
  rw [eval_linearA]
  exact D.allValue C

def EYJ
    (base: ∀C:AU Ω G T H,BP C.1)
    (hactive: ∀C:AU Ω G T H,
      KaehlerDifferential.D Ω (AJ Ω C.1) (coordinate Ω C.1 0) ≠ 0∨
      KaehlerDifferential.D Ω (AJ Ω C.1) (coordinate Ω C.1 2) ≠ 0)
    (hZ: ∀C:AU Ω G T H,GR C 2)
    (hSderiv:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (D:JO (Omega:=Ω) (G:=G) (T:=T) (H:=H)
      base hactive hSderiv)
    (hG:Irreducible G) (hproper: ¬G ∣ T)
    (hGsupport:G.support ⊆ flagSupport p) (hTsupport:T.support ⊆ flagSupport q):
    AND (NJ base hactive hZ hSderiv D hG hproper hGsupport hTsupport) where
  lam:=D.lam
  mu:=D.mu
  yzValue:=by
    intro C
    change FT Ω (AJ Ω C.1)
      (JV (affineU Ω C.1 D.lam) (D.uGate C))=_
    exact MT _ _
  allValue:=by
    intro C
    change (BO Ω (AJ Ω C.1)
      (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.GN C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=_
    exact KA Ω (AJ Ω C.1) _ _

def EZN {T' :Poly} (h:G ∣ T-T')
    {base' : ∀C:AU Ω G T' H,BP C.1}
    (U:EE base' p q)
    (newBase: ∀C:AU Ω G T H,BP C.1)
    (D:AND U):
    AND (JN.YV h U newBase) where
  lam:=D.lam
  mu:=D.mu
  yzValue C:=D.yzValue (RCN066.JA h C)
  allValue C:=D.allValue (RCN066.JA h C)

end
end PR
end MergedPart9
section MergedPart10
namespace EKA
open scoped BigOperators
open RCN095 RCN237
set_option autoImplicit false

variable {ι:Type*} [Fintype ι]

end EKA
end MergedPart10
section MergedPart11
namespace FCV
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN136 RCN156 RCN207 RCN244 RCN264 RCN313
open RCN341 RCN344 RCN046 RCN237
open DX BX FR
open VI PR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "w" =>RCN326.w

end
end FCV
end MergedPart11
section MergedPart12
namespace AJT
open scoped Classical BigOperators
open RCN159 RCN263 RCN086 RCN327
open RCN135 RCN136 RCN264 RCN243 RCN095 RCN237 RCN198 RCN275 RCN244
open RCN334 RCN332 RCN336 RCN338 RCN199 RCN207 RCN313 RCN341 RCN030
open JN PR KF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] {stageErrorCap a b s:ℕ}

def GJU
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hc:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hm:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
    AND (QK S hp hc hm):=by
  let A:=LI S hp hc hm
  exact EYJ A.base A.hactive A.hZ
    (RCN315.EH S) A.data
    S.MW (AHF S hp)
    ((EI flag S.G).2 S.flag_support)
    ((EI
      (CI (support a b s) (w+1))
      (VQ S)).2 (AFM S))

def CVD
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hc:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hm:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
    AND (YV (EW S)
      (QK S hp hc hm) (AHP S hp hc hm)):=
  EZN (EW S)
    (QK S hp hc hm) (AHP S hp hc hm)
    (GJU S hp hc hm)

theorem ENF
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hc:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hm:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
    (CVD S hp hc hm).lam ∈ Set.range (AL K):=
  (LI S hp hc hm).lam_poly

theorem ERF
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hc:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hm:flagMixed flag (CI (support a b s) (w+1)) unitZFlag<p):
    (CVD S hp hc hm).mu ∈ Set.range (AL K):=
  (LI S hp hc hm).mu_poly

end
end AJT
end MergedPart12
section MergedPart13
section Compact_SecondJetActiveMovingBudget6807

namespace DLT
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (DB DQ)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K:Type} [Field K] [IsAlgClosed K]

end
end DLT

end Compact_SecondJetActiveMovingBudget6807

section Compact_SecondJetRetainedBudgets6807

namespace DYS
open scoped Classical BigOperators
open MvPolynomial DX BX FR
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (DQ)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

end
end DYS

end Compact_SecondJetRetainedBudgets6807
end MergedPart13
section MergedPart14
namespace APU
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
open JE
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap:ℕ}

def cellNormal (t y r:ℕ):FlagDegree:=
  JE.normalFlag w r (y-r) (t-y)

theorem AYF
    (t y r:Nat) (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t)
    (hchar:2*(w-1)<p)
    (S:FH (AL K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper: ¬S.G ∣ _Q2 (AL K) S.F
      (w+1))
    (tail1:FlagDegree)
    (B:FE
      (G:=S.G) (T:=_Q2 (AL K) S.F
        (w+1))
      (H:=CR (AL K) S.F) flag tail1)
    (base: ∀C:CM S,BP C.1)
    (budget: ∀C:CM S,
      RD C.1
        (CR (AL K) S.F)
        (surfaceMap (AL K) (polyG K S.F)))
    (hcost: ∀C:CM S,
      (budget C).zCost=B.zCost C∧(budget C).yzCost=B.yzCost C∧
        (budget C).allCost=B.allCost C)
    (active:Finset (CM S)) (divisorBound:ℕ)
    (hinactive: ∀C:CM S,C ∉ active→
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card=0)
    (hjoint:(∑ C ∈ active,
      (FO (MU S)
        (DN (MU S) hfirstProper) C*
        B.weightedCost (cellNormal t y r) C+
        65539*(budget C).movingCost))≤divisorBound)
    (hgate:stageErrorCap+1≤(cellNormal t y r).yz)
    (htangent: ∀C:CM S,
      (∀delay,_Q2 (AL K) S.F
        (w+1+delay) ∈ C.1)→
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤
          (stageErrorCap+1)*B.yzCost C)
    :Nonempty (AKI
      (tailFlag1:=tail1)
      (tailFlag2:=cellNormal t y r) S divisorBound):=by
  classical
  have hry:r<y:=by omega
  have hr2:2≤r:=by omega
  let S0:=MU S
  let multiplicity:CM S→ℕ:=fun C=>
    FO S0 (DN S0 hfirstProper) C
  have hone: ∀C,1≤multiplicity C:=
    ADP S hfirstProper
  have hwcEq: ∀(C:CM S) (f:FlagDegree),
      (budget C).weightedCost f=B.weightedCost f C:=by
    intro C f
    obtain ⟨hz,hy',ha⟩:=hcost C
    simp only [RD.weightedCost,
      FE.weightedCost,hz,hy',ha]
  have hscale: ∀(m:ℕ) (f:FlagDegree) (C:CM S),
      B.weightedCost (m • f) C=m*B.weightedCost f C:=by
    intro m f C
    simp only [FE.weightedCost,nsmul_zOnly,nsmul_yz,
      nsmul_all]
    ring
  have hnormal: ∀C:CM S,
      B.weightedCost (MK t y r) C≤
        B.weightedCost (cellNormal t y r) C:=by
    intro C
    unfold cellNormal
    rw [CML t y r hr3 hb]
    apply CUY B C
    all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
      nsmul_yz,nsmul_all,unitAllFlag]
    all_goals omega
  let cost:CM S→ℕ:=fun C=>
    multiplicity C*B.weightedCost (cellNormal t y r) C+
      65539*(budget C).movingCost
  have hcost_pointwise: ∀C,cost C≤
      multiplicity C*B.weightedCost (cellNormal t y r) C+
        65539*(budget C).movingCost:=fun _=>le_rfl
  have hbound: ∀C,
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤cost C:=by
    intro C
    have dichotomy:=AEM S0
      (DN S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay,hdelay,hdelayMu,htail⟩:=hproper
      by_cases hm:6≤multiplicity C
      · have hzero: ∀gamma ∈ HF (GenericField K) S.G
            (_Q2 (AL K) S.F (w+1))
            (CR (AL K) S.F) Gamma
            (DK (AL K) S.selected) C,
            MvPolynomial.aeval
              (DK (AL K) S.selected gamma)
              (_Q2 (AL K) S.F (w+1+delay))=0:=by
          intro gamma hgamma
          have hGamma:=LU (GenericField K) S.G
            (_Q2 (AL K) S.F (w+1))
            (CR (AL K) S.F) Gamma
            (DK (AL K) S.selected) C hgamma
          exact VZ (AL K)
            S.F S.selected gamma w (w+1+delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod:BIU C.1
            (multiplicity C • MK t y r)
            (_Q2 (AL K) S.F (w+1+delay)):=by
          refine ⟨_Q2 (AL K) S.F (w+1+delay),
            CUW t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm,?_⟩
          simp
        have hcount:=AQR (Seed:=K) B C Gamma
          (DK (AL K) S.selected)
          (ABD (AL K) S.selected)
          hflagMod htail hzero
        rw [hscale] at hcount
        exact hcount.trans ((Nat.mul_le_mul_left _ (hnormal C)).trans
          (Nat.le_add_right _ _))
      · have hdm:delay≤multiplicity C:=hdelayMu
        have hcount:=CNQ.BRG
          t y r hr3 hb hyt hchar S C (budget C) (base C) delay hdelay
          65539 (EZO delay (multiplicity C) hdm (by omega)) htail
        simp only [hwcEq] at hcount
        have hmono:=DBT w (multiplicity C) delay r
          (y-r) (t-y) (by norm_num [w]) (hone C) hdm (by omega)
        have hcostle:=CUY B C hmono.1 hmono.2.1 hmono.2.2
        rw [hscale] at hcostle
        exact hcount.trans (Nat.add_le_add_right hcostle _)
    · have hcount:=htangent C htangentBranch
      calc _≤(stageErrorCap+1)*B.yzCost C:=hcount
        _≤B.weightedCost (cellNormal t y r) C:=
          BIB B (cellNormal t y r) C
            (stageErrorCap+1) hgate
        _≤multiplicity C*B.weightedCost (cellNormal t y r) C:=by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (B.weightedCost (cellNormal t y r) C) (hone C)
        _≤cost C:=Nat.le_add_right _ _
  let activeCost:CM S→ℕ:=fun C=>if C ∈ active then cost C else 0
  have hactiveBound: ∀C,
      (HF (GenericField K) S.G
        (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤activeCost C:=by
    intro C
    by_cases hC:C ∈ active
    · simpa only [activeCost,if_pos hC] using hbound C
    · simp only [activeCost,if_neg hC,hinactive C hC,le_refl]
  have hsum:(∑ C,activeCost C)≤divisorBound:=by
    have ha:(∑ C,activeCost C)= ∑ C ∈ active,cost C:=by
      simp only [activeCost,Finset.sum_ite_mem,Finset.univ_inter]
    rw [ha]
    simpa only [cost,multiplicity,S0] using hjoint
  have providerDichotomy:=AFC S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily:=B
    multiplicity:=multiplicity
    cost:=activeCost
    one_le_multiplicity:=hone
    EHX:=hgate
    cost_sum_le:=hsum
    CRK:=hactiveBound
    dichotomy:=providerDichotomy}⟩

end
end APU
end MergedPart14
section MergedPart15
namespace DYF
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open FA GJ IB
open ND JN
open ID
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap:ℕ}

end
end DYF
end MergedPart15

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace AQW
open RCN095 RCN198 RCN263 RCN287 RCN327 FA
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem DVW (f q:FlagDegree) (R capY:ℕ) (hfa:f.all≤31)
    (hfy:f.yz+f.all≤142) (hqa:q.all≤R)
    (hqy:q.yz+q.all≤capY):
    flagMixed f q unitZFlag≤31*capY+111*R:=by
  have h1:=Nat.mul_le_mul_right q.all hfy
  have h2:=Nat.mul_le_mul_right q.yz hfa
  have h3:=Nat.mul_le_mul_left 31 hqy
  have h4:=Nat.mul_le_mul_left 111 hqa
  simp only [flagMixed,unitZFlag]
  nlinarith

theorem reduced_gate (f:FlagDegree) (t y r:ℕ)
    (hr:3≤r) (hrcap:r≤31) (hycap:y≤142)
    (hry:r+2≤y) (hyt:y≤t)
    (hfa:f.all≤r) (hfy:f.yz+f.all≤y):
    flagMixed f (TX t y r) unitZFlag<2130706433:=by
  have hys:cellB y r+cellS r+3=y:=by dsimp [cellB,cellS];omega
  have hs:cellS r+2=r:=by dsimp [cellS];omega
  have hqa:(TX t y r).all≤7864320:=by
    simp only [TX,CI,UH,cellSupport,RCN198.support,hs,w]
    omega
  have hqy:(TX t y r).yz+(TX t y r).all≤36962305:=by
    rw [TX,ACH]
    simp only [cellSupport,RCN198.support,hys,w]
    omega
  exact (DVW f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

theorem EJG (f:FlagDegree) (t y r:ℕ)
    (hr:3≤r) (hrcap:r≤31) (hycap:y≤142)
    (hry:r+2≤y) (hyt:y≤t)
    (hfa:f.all≤r) (hfy:f.yz+f.all≤y):
    flagMixed f (DL (cellSupport t y r) w) unitZFlag<
      2130706433:=by
  have hys:cellB y r+cellS r+3=y:=by dsimp [cellB,cellS];omega
  have hs:cellS r+2=r:=by dsimp [cellS];omega
  have hqa:(DL (cellSupport t y r) w).all≤7995331:=by
    simp only [DL,SS,cellSupport,RCN198.support,hs,w]
    omega
  have hqy:(DL (cellSupport t y r) w).yz+
      (DL (cellSupport t y r) w).all≤36962023:=by
    rw [AXA (cellSupport t y r) (by
      simp only [cellSupport,RCN198.support];omega)]
    simp only [cellSupport,RCN198.support,hys,w]
    omega
  exact (DVW f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

end AQW

end ProximityPrize.SubmissionLower
end
section
section MergedPart0
namespace ProximityPrize.SubmissionLower.BIZ
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open DX BX FR
open VI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" =>RCN326.w



section Slice
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

structure GEZ (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0:FlagDegree):Prop where
  pole_le: ∀W:Finset (Place E (AJ E C)),
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu+
        2*RCN026.zeroOrder E (AJ E C) nu
          (CT.GP phi C (polyH K F)))+
      3*flagPole nu.val (coordinate E C) C0)

end Slice

section Stage
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "φE" =>RingHom.comp (algebraMap (GenericField K) E) (AL K)

variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

end Stage
end
end ProximityPrize.SubmissionLower.BIZ
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.HK
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open FA GJ JN IB
open ID PR BD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap:ℕ}
local notation "Ω" =>GenericField K

def rawFirstFlag (t y r:ℕ):FlagDegree:=
  RCN198.center (cellA t y) (cellB y r) (cellS r)+
    w • (⟨cellA t y,cellB y r+1,cellS r+2⟩:FlagDegree)





def channel {t y r:ℕ}
    (S:FH (AL K) Gamma x p errorCap flag w (cellSupport t y r))
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hflagChar:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hmixedRed:flagMixed flag (TX t y r) unitZFlag<p):
    Fin 3→MvPolynomial (Fin 3) Ω:=
  let common:=AJT.CVD S hproper hflagChar hmixedRed
  ![PR.linearZ,PR.linearU common.lam,
    PR.linearA common.mu common.lam]

end
end ProximityPrize.SubmissionLower.HK
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.EHT
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

end
end ProximityPrize.SubmissionLower.EHT
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.DQL
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433

end
end ProximityPrize.SubmissionLower.DQL
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.BJU
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 FA GJ RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

structure Data (nodes:I ↪ K) (u0 u1:I→K) where
  D:ℕ
  t:ℕ
  y:ℕ
  r:ℕ
  Dlow:131072≤D
  Dchar:D<2130706433
  tbound:t≤7501
  ybound:y≤142
  rbound:r≤31
  rpos:3≤r
  ry:r+2≤y
  yt:y+2≤t
  F:MvPolynomial (Fin 4) K
  irreducible:Irreducible F
  rdegree:0<F.degreeOf 2
  box:F ∈ BA K D w t r
  support:KW (cellSupport t y r) F
  selected:K→Polynomial K
  seeds:Finset K
  degree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w
  agreement: ∀gamma ∈ seeds,181265≤
    (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  solution: ∀gamma ∈ seeds,BM K (selected gamma) gamma F=0
  regular: ∀gamma ∈ seeds,
    BM K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil:BL selected seeds w 80879

namespace Data
variable {nodes:I ↪ K} {u0 u1:I→K}











end Data
end
end ProximityPrize.SubmissionLower.BJU
end MergedPart4
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P24
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=190
def B:ℕ:=84
def s:ℕ:=38
def U:ℕ:=258
def L:ℕ:=3371
def k:ℕ:=9
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      18818379352629200:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=71786307291:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=18818379352629200:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=71786307291:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*71786307291<18818379352629200:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P24

namespace CH.P25
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=111
def B:ℕ:=46
def s:ℕ:=21
def U:ℕ:=151
def L:ℕ:=3695
def k:ℕ:=5
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      2295616262780031:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=8757079531:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=2295616262780031:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=8757079531:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*8757079531<2295616262780031:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P25

namespace CH.P26
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=189
def B:ℕ:=83
def s:ℕ:=37
def U:ℕ:=257
def L:ℕ:=3419
def k:ℕ:=9
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      18460634273493806:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=70421712902:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=18460634273493806:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=70421712902:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*70421712902<18460634273493806:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P26

namespace CH.P27
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=72
def B:ℕ:=31
def s:ℕ:=14
def U:ℕ:=98
def L:ℕ:=1030
def k:ℕ:=2
def n0:ℕ:=3

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      124018968771506:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=473093628:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=124018968771506:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=473093628:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*473093628<124018968771506:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P27

namespace CH.P28
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=105
def B:ℕ:=45
def s:ℕ:=21
def U:ℕ:=142
def L:ℕ:=1799
def k:ℕ:=4
def n0:ℕ:=5

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      937664436201184:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=3576905761:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=937664436201184:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=3576905761:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*3576905761<937664436201184:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P28

namespace CH.P29
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=104
def B:ℕ:=45
def s:ℕ:=21
def U:ℕ:=141
def L:ℕ:=1965
def k:ℕ:=4
def n0:ℕ:=6

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      1004090341797434:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=3830295149:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=1004090341797434:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=3830295149:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*3830295149<1004090341797434:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P29
end MergedPart0
section MergedPart1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace CH.P30
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=136
def B:ℕ:=59
def s:ℕ:=27
def U:ℕ:=185
def L:ℕ:=2596
def k:ℕ:=6
def n0:ℕ:=7

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      3792284745481463:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=14466415914:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=3792284745481463:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=14466415914:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*14466415914<3792284745481463:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P30

namespace CH.P31
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=130
def B:ℕ:=53
def s:ℕ:=24
def U:ℕ:=177
def L:ℕ:=3666
def k:ℕ:=6
def n0:ℕ:=8

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      4099763288934857:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=15639342340:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=4099763288934857:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=15639342340:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*15639342340<4099763288934857:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P31

namespace CH.P32
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=158
def B:ℕ:=62
def s:ℕ:=28
def U:ℕ:=215
def L:ℕ:=3573
def k:ℕ:=7
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      8042682771894533:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=30680385247:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=8042682771894533:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=30680385247:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*30680385247<8042682771894533:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P32

namespace CH.P33
open DD AM
noncomputable section
set_option autoImplicit false
def m:ℕ:=187
def B:ℕ:=82
def s:ℕ:=37
def U:ℕ:=253
def L:ℕ:=3593
def k:ℕ:=9
def n0:ℕ:=10

theorem FD:
    AW (BB.cutoff m k n0) 131071 L B s U=
      18629703639247968:=by decide+kernel

theorem local_rank:AR.rankBound m L B s U=71066622349:=by decide+kernel

theorem cutoff_caps: ∀h:Fin (s+1),
    U≤(BB.cutoff m k n0 h.val+B-1)/131071:=by decide+kernel

theorem source_card:
    Fintype.card (Index (BB.cutoff m k n0) 131071 L B s U)=18629703639247968:=by
  rw [JY _ _ _ _ _ _ (by decide+kernel),FD]

theorem exact_rank:
    EG.rankBound m L B s U
      (fun h=>(BB.cutoff m k n0 h+B-1)/131071)=71066622349:=by
  rw [AR.IX _ _ _ _ _ _ (by decide+kernel)
    (by decide+kernel) (by decide+kernel) (by decide+kernel)
    (fun h hh=>cutoff_caps ⟨h,by omega⟩),local_rank]

theorem IG:262144*71066622349<18629703639247968:=by decide+kernel

theorem _Q3 {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144):
    ∃P,BB.Interpolant m B s U L k n0 nodes u0 u1 P:=by
  apply BB.JD m B s U L k n0
    (by decide+kernel) (by decide+kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact IG

end
end CH.P33
end MergedPart1
section MergedPart2
namespace ZX
open MvPolynomial DX HZ HH
open BX JQ IM
open AQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]

theorem BFX (f:Polynomial K) (z:K) (w:ℕ)
    (hf:f.natDegree≤w) (e:Fin 4→₀ ℕ) (c:K):
    (FL f z (MvPolynomial.monomial e c)).natDegree≤
      e 0+w*e 1+(w-1)*e 2:=by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,map_mul,map_pow]
    have hc:(FL f z (MvPolynomial.C c)).natDegree≤0:=by
      simp [FL]
    have h0:(FL f z (MvPolynomial.X 0)^e 0).natDegree≤e 0:=by
      simp [FL]
    have h1:(FL f z (MvPolynomial.X 1)^e 1).natDegree≤e 1*w:=by
      simpa [FL] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2:(FL f z (MvPolynomial.X 2)^e 2).natDegree≤e 2*(w-1):=by
      simpa [FL] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3:(FL f z (MvPolynomial.X 3)^e 3).natDegree≤0:=by
      simp [FL]
    have hh:=Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem BOT (P:MvPolynomial (Fin 4) K) (f:Polynomial K)
    (z:K) (w D:ℕ) (hf:f.natDegree≤w) (hD:0<D)
    (hP: ∀e ∈ P.support,e 0+w*e 1+(w-1)*e 2<D):
    (FL f z P).natDegree<D:=by
  classical
  have ht: ∀e ∈ P.support,
      (FL f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))).natDegree≤D-1:=by
    intro e he
    have hh:=BFX f z w hf e (AddMonoidAlgebra.coeff P e)
    have hb:=hP e he
    omega
  rw [MvPolynomial.as_sum P,map_sum]
  have hh:=Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e=>FL f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))) ht
  omega

theorem CHD {R:Type*} [CommRing R] (P:Polynomial R) (d:ℕ)
    (hh: ∀j,d<j→P.coeff j=0):
    (Polynomial.derivative)^[d] P=Polynomial.C (d.factorial • P.coeff d):=by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj:j=0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem DIO (P:Poly (K:=K)) (f:Polynomial K) (z:K) (d:ℕ)
    (hh: ∀j,d<j→FL f z ((asS P).coeff j)=0):
    specialize f z ((pderiv 1)^[d] P)=
      d.factorial • FL f z ((asS P).coeff d):=by
  rw [FAP,asS_iterate,← Polynomial.eval_map,← Polynomial.iterate_derivative_map]
  rw [CHD _ d (by intro j hj;simpa using hh j hj)]
  simp



end
end ZX
end MergedPart2

end ProximityPrize.SubmissionLower
end
section
section MergedPart0
namespace ProximityPrize.SubmissionLower.ELA
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

end
end ProximityPrize.SubmissionLower.ELA
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.DQD
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433

end
end ProximityPrize.SubmissionLower.DQD
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.AAG
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 FA GJ RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

structure Data (nodes:I ↪ K) (u0 u1:I→K) where
  D:ℕ
  t:ℕ
  y:ℕ
  r:ℕ
  Dlow:131072≤D
  Dchar:D<2130706433
  tbound:t≤7501
  ybound:y≤142
  rbound:r≤31
  rpos:3≤r
  ry:r+2≤y
  yt:y+2≤t
  F:MvPolynomial (Fin 4) K
  irreducible:Irreducible F
  rdegree:0<F.degreeOf 2
  box:F ∈ BA K D w t r
  support:KW (cellSupport t y r) F
  selected:K→Polynomial K
  seeds:Finset K
  degree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w
  agreement: ∀gamma ∈ seeds,181235≤
    (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card
  solution: ∀gamma ∈ seeds,BM K (selected gamma) gamma F=0
  regular: ∀gamma ∈ seeds,
    BM K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil:BL selected seeds w 80909

namespace Data
variable {nodes:I ↪ K} {u0 u1:I→K}

def restrict (S:Data nodes u0 u1) (Delta:Finset K) (hsub:Delta ⊆ S.seeds):
    Data nodes u0 u1:=
  {S with
           seeds:=Delta
           degree:=fun gamma h=>S.degree gamma (hsub h)
           agreement:=fun gamma h=>S.agreement gamma (hsub h)
           solution:=fun gamma h=>S.solution gamma (hsub h)
           regular:=fun gamma h=>S.regular gamma (hsub h)
           noPencil:=KX S.selected S.seeds Delta w 80909 hsub S.noPencil}

def pair (S:Data nodes u0 u1) (R capY T:ℕ):DG:=
  ⟨262144,131071,181235,S.y,S.r,S.t,capY,R,T⟩

def PairGates (S:Data nodes u0 u1) (R capY T:ℕ):Prop:=
  (S.pair R capY T).mixedCost.y<2130706433∧
  (S.pair R capY T).mixedCost.r<2130706433∧
  (S.pair R capY T).mixedCost.z<2130706433

theorem weights (S:Data nodes u0 u1):
    wt BE S.F≤S.r∧wt BC S.F≤S.y∧
      wt AT S.F≤S.t:=by
  have hs:cellS S.r+2=S.r:=by have:=S.rpos;dsimp [cellS];omega
  have hy:cellB S.y S.r+cellS S.r+3=S.y:=by have:=S.ry;dsimp [cellB,cellS];omega
  have ht:cellA S.t S.y+cellB S.y S.r+cellS S.r+3=S.t:=by
    have:=S.yt;dsimp [cellA];omega
  have h:=S.support
  exact ⟨by simpa only [cellSupport,RCN198.support,hs] using h.s_weight,
    by simpa only [cellSupport,RCN198.support,hy] using h.ys_weight,
    by simpa only [cellSupport,RCN198.support,ht] using h.total_weight⟩

theorem DVV (S:Data nodes u0 u1) (hI:Fintype.card I=262144)
    (Q:MvPolynomial (Fin 4) K) (R capY T:ℕ) (hrel:IsRelPrime S.F Q)
    (hQ:Q.degreeOf 1≤capY∧Q.degreeOf 2≤R∧Q.degreeOf 3≤T)
    (hgates:S.PairGates R capY T)
    (hzero: ∀gamma ∈ S.seeds,BM K (S.selected gamma) gamma Q=0):
    S.seeds.card≤GB.FU (S.pair R capY T):=by
  have hF:=ZM.ATW S.F S.r S.y S.t S.weights
  have hcount:=BCH.BUM
    (S.pair R capY T) S.F Q S.irreducible S.rdegree hrel 2130706433
    hF.1 hF.2.1 hF.2.2 hQ.1 hQ.2.1 hQ.2.2 (by have:=S.rpos;dsimp [pair];omega)
    (by have:=S.ybound;dsimp [pair];omega)
    (by have:=S.rbound;dsimp [pair];omega)
    (by have:=S.tbound;dsimp [pair];omega)
    hgates.1 hgates.2.1 hgates.2.2 S.selected S.seeds Finset.univ nodes u0 u1
    nodes.injective.injOn (by simpa only [Finset.card_univ,pair] using hI)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    S.degree S.agreement (by simpa only [pair,DG.errors,
      (show (262144-181235:ℕ)=80909 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact ZM.DUQ (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0<(181235-131071:ℕ);decide) hcount

end Data
end
end ProximityPrize.SubmissionLower.AAG
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.KB
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open FA GJ ID
open AAG BD BB AXB
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m:ℕ
  B:ℕ
  s:ℕ
  U:ℕ
  L:ℕ
  k:ℕ
  n0:ℕ
  deriving DecidableEq,Repr

def Params.d (P:Params):ℕ:=P.k+1
def Params.flag (P:Params):FlagDegree:=EJ.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P:Params):Prop:=
  2*P.s≤P.B∧P.B≤P.U∧P.U≤P.L∧P.k≤P.s∧P.s<P.m∧
    P.k+1≤P.n0∧2*(P.n0-(P.k+1))≤P.B∧P.s<2130706433


variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {nodes:I ↪ K} {u0 u1:I→K}

def helperCap (S:Data nodes u0 u1) (P:Params):ℕ:=
  GB.FU (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def CRL (S:Data nodes u0 u1) (P:Params):ℕ:=
  GB.FU (S.pair P.B P.U P.L)


end
end ProximityPrize.SubmissionLower.KB
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.KM
open KB BB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

local instance (P:Params):Decidable P.WellFormed:=by
  unfold Params.WellFormed
  infer_instance

def source0:Params:=⟨132,54,25,180,1935,5,7⟩
def source1:Params:=⟨133,56,25,180,3119,6,8⟩
def source2:Params:=⟨136,56,25,185,2911,6,8⟩
def source3:Params:=⟨116,46,21,158,3225,5,7⟩
def source4:Params:=⟨114,45,20,155,3642,5,7⟩
def source5:Params:=⟨158,63,28,215,3383,7,10⟩
def source6:Params:=⟨167,73,33,226,3496,8,9⟩
def source7:Params:=⟨114,47,21,154,3257,5,7⟩
def source8:Params:=⟨142,56,25,193,3083,6,9⟩
def source9:Params:=⟨174,76,34,236,3018,8,9⟩
def source10:Params:=⟨170,71,32,231,3484,8,10⟩
def source11:Params:=⟨97,41,19,132,2775,4,6⟩
def source12:Params:=⟨142,59,27,193,2685,6,9⟩
def source13:Params:=⟨158,69,31,214,2660,7,8⟩
def source14:Params:=⟨146,58,26,198,2766,6,9⟩
def source15:Params:=⟨98,41,19,133,2667,4,6⟩
def source16:Params:=⟨150,60,27,204,2504,6,9⟩
def source17:Params:=⟨161,71,32,218,2524,7,8⟩
def source18:Params:=⟨114,47,21,155,3155,5,7⟩
def source19:Params:=⟨166,66,30,226,2932,7,10⟩
def source20:Params:=⟨175,76,34,237,2990,8,9⟩
def source21:Params:=⟨111,46,21,151,3695,5,7⟩
def source22:Params:=⟨189,83,37,256,3453,9,10⟩
def source23:Params:=⟨114,45,20,155,3642,5,7⟩
def source24:Params:=⟨190,84,38,258,3371,9,10⟩
def source25:Params:=⟨111,46,21,151,3695,5,7⟩
def source26:Params:=⟨189,83,37,257,3419,9,10⟩
def source27:Params:=⟨72,31,14,98,1030,2,3⟩
def source28:Params:=⟨105,45,21,142,1799,4,5⟩
def source29:Params:=⟨104,45,21,141,1965,4,6⟩
def source30:Params:=⟨136,59,27,185,2596,6,7⟩
def source31:Params:=⟨130,53,24,177,3666,6,8⟩
def source32:Params:=⟨158,62,28,215,3573,7,10⟩
def source33:Params:=⟨187,82,37,253,3593,9,10⟩

def sources:Fin 34→Params:= ![source0,source1,source2,source3,source4,source5,source6,source7,source8,source9,source10,source11,source12,source13,source14,source15,source16,source17,source18,source19,source20,source21,source22,source23,source24,source25,source26,source27,source28,source29,source30,source31,source32,source33]
def groups:Fin 21→Fin 3→Params:= ![![source0,source0,source0],![source1,source1,source1],![source2,source2,source2],![source3,source3,source3],![source4,source5,source6],![source7,source8,source9],![source10,source10,source10],![source11,source12,source13],![source11,source14,source13],![source15,source16,source17],![source18,source19,source20],![source21,source5,source22],![source23,source5,source24],![source25,source5,source24],![source25,source5,source26],![source21,source5,source26],![source27,source27,source27],![source28,source28,source28],![source29,source29,source29],![source30,source30,source30],![source31,source32,source33]]

theorem wellFormed (g:Fin 21) (j:Fin 3):(groups g j).WellFormed:=by
  have h: ∀g:Fin 21,∀j:Fin 3,(groups g j).WellFormed:=by decide+kernel
  exact h g j

theorem common_caps (g:Fin 21) (j:Fin 3):
    (groups g j).B≤84∧(groups g j).U≤258∧(groups g j).L≤3695∧(groups g j).s≤40:=by
  have h: ∀g:Fin 21,∀j:Fin 3,
    (groups g j).B≤84∧(groups g j).U≤258∧(groups g j).L≤3695∧(groups g j).s≤40:=by decide+kernel
  exact h g j

theorem GUO {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144) (i:Fin 34):
    ∃P,Interpolant (sources i).m (sources i).B (sources i).s (sources i).U
      (sources i).L (sources i).k (sources i).n0 nodes u0 u1 P:=by
  fin_cases i
  · change∃P,Interpolant 132 54 25 180 1935 5 7 nodes u0 u1 P
    exact CH.P0._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 133 56 25 180 3119 6 8 nodes u0 u1 P
    exact CH.P1._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 136 56 25 185 2911 6 8 nodes u0 u1 P
    exact CH.P2._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 116 46 21 158 3225 5 7 nodes u0 u1 P
    exact CH.P3._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 114 45 20 155 3642 5 7 nodes u0 u1 P
    exact CH.P4._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 158 63 28 215 3383 7 10 nodes u0 u1 P
    exact CH.P5._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 167 73 33 226 3496 8 9 nodes u0 u1 P
    exact CH.P6._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 114 47 21 154 3257 5 7 nodes u0 u1 P
    exact CH.P7._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 142 56 25 193 3083 6 9 nodes u0 u1 P
    exact CH.P8._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 174 76 34 236 3018 8 9 nodes u0 u1 P
    exact CH.P9._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 170 71 32 231 3484 8 10 nodes u0 u1 P
    exact CH.P10._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 97 41 19 132 2775 4 6 nodes u0 u1 P
    exact CH.P11._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 142 59 27 193 2685 6 9 nodes u0 u1 P
    exact CH.P12._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 158 69 31 214 2660 7 8 nodes u0 u1 P
    exact CH.P13._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 146 58 26 198 2766 6 9 nodes u0 u1 P
    exact CH.P14._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 98 41 19 133 2667 4 6 nodes u0 u1 P
    exact CH.P15._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 150 60 27 204 2504 6 9 nodes u0 u1 P
    exact CH.P16._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 161 71 32 218 2524 7 8 nodes u0 u1 P
    exact CH.P17._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 114 47 21 155 3155 5 7 nodes u0 u1 P
    exact CH.P18._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 166 66 30 226 2932 7 10 nodes u0 u1 P
    exact CH.P19._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 175 76 34 237 2990 8 9 nodes u0 u1 P
    exact CH.P20._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 111 46 21 151 3695 5 7 nodes u0 u1 P
    exact CH.P21._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 189 83 37 256 3453 9 10 nodes u0 u1 P
    exact CH.P22._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 114 45 20 155 3642 5 7 nodes u0 u1 P
    exact CH.P23._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 190 84 38 258 3371 9 10 nodes u0 u1 P
    exact CH.P24._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 111 46 21 151 3695 5 7 nodes u0 u1 P
    exact CH.P25._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 189 83 37 257 3419 9 10 nodes u0 u1 P
    exact CH.P26._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 72 31 14 98 1030 2 3 nodes u0 u1 P
    exact CH.P27._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 105 45 21 142 1799 4 5 nodes u0 u1 P
    exact CH.P28._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 104 45 21 141 1965 4 6 nodes u0 u1 P
    exact CH.P29._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 136 59 27 185 2596 6 7 nodes u0 u1 P
    exact CH.P30._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 130 53 24 177 3666 6 8 nodes u0 u1 P
    exact CH.P31._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 158 62 28 215 3573 7 10 nodes u0 u1 P
    exact CH.P32._Q3 nodes u0 u1 hI
  · change∃P,Interpolant 187 82 37 253 3593 9 10 nodes u0 u1 P
    exact CH.P33._Q3 nodes u0 u1 hI

def groupIndices:Fin 21→Fin 3→Fin 34:= ![![0,0,0],![1,1,1],![2,2,2],![3,3,3],![4,5,6],![7,8,9],![10,10,10],![11,12,13],![11,14,13],![15,16,17],![18,19,20],![21,5,22],![23,5,24],![25,5,24],![25,5,26],![21,5,26],![27,27,27],![28,28,28],![29,29,29],![30,30,30],![31,32,33]]

theorem FOR (g:Fin 21) (j:Fin 3):groups g j=sources (groupIndices g j):=by
  have h: ∀g:Fin 21,∀j:Fin 3,groups g j=sources (groupIndices g j):=by decide+kernel
  exact h g j

theorem exists_group {K I:Type} [Field K] [Fintype I]
    (nodes:I ↪ K) (u0 u1:I→K) (hI:Fintype.card I=262144) (g:Fin 21):
    ∃P:Fin 3→DX.Poly (K:=K),∀j,
      Interpolant (groups g j).m (groups g j).B (groups g j).s (groups g j).U
        (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 (P j):=by
  classical
  have hex (j:Fin 3): ∃P,Interpolant (groups g j).m (groups g j).B (groups g j).s
      (groups g j).U (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 P:=by
    rw [FOR g j]
    exact GUO nodes u0 u1 hI (groupIndices g j)
  exact Classical.skolem.mp hex

end ProximityPrize.SubmissionLower.KM
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.GU
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 FA GJ
open KB BD AAG
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000


def normal (a b c:ℕ):FlagDegree:=⟨131074*c,131074*b+131076,131074*a+262148⟩
def raw (a b c:ℕ):FlagDegree:=⟨131073*c,131073*b+262146,131073*a+393218⟩

def DS (p:FlagDegree) (a b c:ℕ):ℕ:=
  p.zOnly*(655365+262146*a)+p.yz*(1310730+524292*a)+
    p.all*(2097170+524292*a+524292*b+262146*c)
def CZ (a b c capY capR capT:ℕ):ℕ:=
  131073*((1+262142*(a+b+5))*((a+3)*capT+(a+b+c+5)*capR)+
    131071*(2*a+5)*((a+b+5)*capT+(a+b+c+5)*capY)+
    (1+262142*(a+b+c+5))*((a+b+5)*capR+(a+3)*capY))+
    80910*50164*((a+b+5)*capR+(a+3)*capY)
def coeff (P:Params) (a b c:ℕ):ℕ:=CZ a b c P.U P.B P.L
def helper (P:Params) (a b c:ℕ):ℕ:=
  CZ a b c (P.U+P.s*(a+b+4)) (P.B+P.s*(a+2)) (P.L+P.s*(a+b+c+4))



theorem FGF (f:FlagDegree) (a b c:ℕ):
    IY f (cellA (a+3+(b+2)+c) (a+3+(b+2)))
      (cellB (a+3+(b+2)) (a+3)) (cellS (a+3)) w=DS f a b c:=by
  change IY f _ _ _ Lower80788.YM.w=_
  rw [Lower80788.YM.APP]
  have ha:cellA (a+3+(b+2)+c) (a+3+(b+2))=c:=by dsimp [cellA];omega
  have hb:cellB (a+3+(b+2)) (a+3)=b+1:=by dsimp [cellB];omega
  have hs:cellS (a+3)=a+1:=by dsimp [cellS];omega
  rw [ha,hb,hs]
  simp only [DS]
  ring

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

theorem GJE (S:Data nodes u0 u1) (a b c:ℕ)
    (hr:S.r=a+3) (hy:S.y=a+3+(b+2)) (ht:S.t=a+3+(b+2)+c) (R U T:ℕ):
    GB.KP (S.pair R U T)=CZ a b c U R T:=by
  have hR:2*(a+3)-1=2*a+5:=by omega
  norm_num only [Data.pair,GB.KP,DG.errors,
    DG.gap,DG.KO,DG.mixedCost,dot,hr,hy,ht,hR,CZ]
  ring

theorem FVG (S:Data nodes u0 u1) (R U T:ℕ)
    (hR:R≤1284) (hU:U≤5898) (hT:T≤303695):S.PairGates R U T:=by
  have hr:=S.rbound
  have hy:=S.ybound
  have ht:=S.tbound
  have hm:(S.pair R U T).mixedCost.y≤31*303695+7501*1284∧
      (S.pair R U T).mixedCost.r≤142*303695+7501*5898∧
      (S.pair R U T).mixedCost.z≤142*1284+31*5898:=by
    dsimp [Data.pair,DG.mixedCost]
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hr hT) (Nat.mul_le_mul ht hR)
    constructor
    · exact Nat.add_le_add (Nat.mul_le_mul hy hT) (Nat.mul_le_mul ht hU)
    · exact Nat.add_le_add (Nat.mul_le_mul hy hR) (Nat.mul_le_mul hr hU)
  exact ⟨hm.1.trans_lt (by decide),hm.2.1.trans_lt (by decide),hm.2.2.trans_lt (by decide)⟩

theorem FYB (S:Data nodes u0 u1) (g:Fin 21) (j:Fin 3):
    let P:=KM.groups g j
    S.PairGates (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1))∧
    S.PairGates P.B P.U P.L:=by
  dsimp only
  have hp:=KM.common_caps g j
  have hr:S.r-1≤30:=by have:=S.rbound;omega
  have hy:S.y-1≤141:=by have:=S.ybound;omega
  have ht:S.t-1≤7500:=by have:=S.tbound;omega
  constructor
  · apply FVG
    · calc _≤84+40*30:=by gcongr;exact hp.1;exact hp.2.2.2
           _≤1284:=by decide
    · calc _≤258+40*141:=by gcongr;exact hp.2.1;exact hp.2.2.2
           _≤5898:=by decide
    · calc _≤3695+40*7500:=by gcongr;exact hp.2.2.1;exact hp.2.2.2
           _≤303695:=by decide
  · exact FVG S _ _ _ (by omega) (by omega) (by omega)

def Own (S:Data nodes u0 u1):Prop:=
  RCN130.FX S.F=⟨S.t-S.y,S.y-S.r,S.r⟩

theorem own_total (S:Data nodes u0 u1) (hown:Own S):RCN234.wt RCN156.AT S.F=S.t:=by
  have h:=(RCN130.GX S.F).2.2
  rw [hown] at h
  have:=S.ry
  have:=S.yt
  dsimp only at h
  omega

end ProximityPrize.SubmissionLower.GU
end MergedPart5
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open MvPolynomial

section Resultant

variable {A:Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]

theorem DXZ (P Q:Polynomial A) (hP:Irreducible P)
    (hpos:0<P.natDegree) (hPQ: ¬P ∣ Q):P.resultant Q ≠ 0:=by
  intro hz
  have hprim:=hP.isPrimitive (Nat.ne_of_gt hpos)
  let f:A→+*FractionRing A:=algebraMap A (FractionRing A)
  have hf:Function.Injective f:=IsFractionRing.injective A (FractionRing A)
  have hPd:(P.map f).natDegree=P.natDegree:=Polynomial.natDegree_map_eq_of_injective hf P
  have hQd:(Q.map f).natDegree=Q.natDegree:=Polynomial.natDegree_map_eq_of_injective hf Q
  have hres:(P.map f).resultant (Q.map f)=0:=by
    have h1:=Polynomial.resultant_map_map P Q P.natDegree Q.natDegree f
    show (P.map f).resultant (Q.map f) (P.map f).natDegree (Q.map f).natDegree=0
    rw [hPd,hQd,h1,show P.resultant Q P.natDegree Q.natDegree=0 from hz,map_zero]
  have hnot: ¬IsCoprime (P.map f) (Q.map f):=(Polynomial.resultant_eq_zero_iff.mp hres).2
  have hi:Irreducible (P.map f):=hprim.irreducible_iff_irreducible_map_fraction_map.mp hP
  exact hPQ (hprim.dvd_of_fraction_map_dvd_fraction_map
    ((Irreducible.dvd_iff_not_isCoprime hi).mpr hnot))

end Resultant

variable {Ω:Type*} [Field Ω]

theorem FUC {R:Type*} [CommRing R] [Algebra Ω R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (z:Fin 3→R) (hGz:aeval z G=0) (hPz:aeval z P=0):
    ∃Q:MvPolynomial (Fin 2) Ω,Q ≠ 0∧aeval (fun m=>z m.succ) Q=0:=by
  classical
  let e:=finSuccEquiv Ω 2
  have hback: ∀q:MvPolynomial (Fin 2) Ω,
      aeval z (e.symm (Polynomial.C q))=aeval (fun m=>z m.succ) q:=by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a=>
      have h1:e.symm (Polynomial.C (C a))=C a:=
        RingHom.congr_fun (finSuccEquiv_comp_C_eq_C (R:=Ω) 2) a
      rw [h1,aeval_C,aeval_C]
    | add p q hp hq=>simp only [map_add,hp,hq]
    | mul_X p j hp=>
      have h1:e.symm (Polynomial.C (MvPolynomial.X j))=MvPolynomial.X j.succ:=by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply,finSuccEquiv_X_succ]
      simp only [map_mul,h1,hp,aeval_X]
  have hg:Irreducible (e G):=(MulEquiv.irreducible_iff e).mpr hG
  have hgp: ¬e G ∣ e P:=by
    rintro ⟨c,hc⟩
    exact hGP ⟨e.symm c,by apply e.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hc]⟩
  by_cases hdeg:(e G).natDegree=0
  · refine ⟨(e G).coeff 0,?_,?_⟩
    · intro h0
      apply hg.ne_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg,h0,map_zero]
    · rw [← hback,← Polynomial.eq_C_of_natDegree_eq_zero hdeg,AlgEquiv.symm_apply_apply,hGz]
  · obtain ⟨a,b,-,-,hab⟩:=
      Polynomial.exists_mul_add_mul_eq_C_resultant (e G) (e P) le_rfl le_rfl (Or.inl hdeg)
    refine ⟨(e G).resultant (e P),
      DXZ (e G) (e P) hg (by omega) hgp,?_⟩
    rw [← hback,← hab,map_add,map_mul,map_mul,AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply,map_add,map_mul,map_mul,hGz,hPz,zero_mul,zero_mul,
      add_zero]

theorem GET {R:Type*} [CommRing R] [Algebra Ω R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (z:Fin 3→R) (hGz:aeval z G=0) (hPz:aeval z P=0) (m i:Fin 3) (hmi:m ≠ i):
    ∃Q:MvPolynomial (Fin 2) Ω,Q ≠ 0∧aeval ![z m,z i] Q=0:=by
  classical
  let i' :=Equiv.swap 1 m i
  have hi' :i' ≠ 1:=by
    intro h
    exact hmi ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_left 1 m)).symm
  let σ:Equiv.Perm (Fin 3):=Equiv.swap 1 m*Equiv.swap 2 i'
  have hσ1:σ 1=m:=by
    change Equiv.swap 1 m (Equiv.swap 2 i' 1)=m
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) hi'.symm,Equiv.swap_apply_left]
  have hσ2:σ 2=i:=by
    change Equiv.swap 1 m (Equiv.swap 2 i' 2)=i
    rw [Equiv.swap_apply_left,Equiv.swap_apply_self]
  let r:=renameEquiv Ω σ.symm
  have hr: ∀p:MvPolynomial (Fin 3) Ω,aeval (z ∘ σ) (r p)=aeval z p:=by
    intro p
    change aeval (z ∘ σ) (rename σ.symm p)=aeval z p
    rw [aeval_rename,show (z ∘ σ) ∘ σ.symm=z by funext x;simp]
  have hG' :Irreducible (r G):=(MulEquiv.irreducible_iff r).mpr hG
  have hGP' : ¬r G ∣ r P:=by
    rintro ⟨c,hc⟩
    exact hGP ⟨r.symm c,by apply r.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hc]⟩
  obtain ⟨Q,hQ,hQz⟩:=FUC (r G) (r P) hG' hGP' (z ∘ σ)
    (by rw [hr,hGz]) (by rw [hr,hPz])
  have hfun:(fun j:Fin 2=>(z ∘ σ) j.succ)= ![z m,z i]:=by
    funext j
    fin_cases j
    · simp [hσ1]
    · simp [hσ2]
  rw [hfun] at hQz
  exact ⟨Q,hQ,hQz⟩

theorem EOA {E R:Type*} [Field E] [Field R] [Algebra Ω E] [Algebra E R]
    [Algebra Ω R] [IsScalarTower Ω E R] (t:E) (ht:Transcendental Ω t) (a:R)
    (Q:MvPolynomial (Fin 2) Ω) (hQ:Q ≠ 0) (h:aeval ![a,algebraMap E R t] Q=0):
    IsAlgebraic E a:=by
  classical
  let e:=finSuccEquiv Ω 1
  let φt:MvPolynomial (Fin 1) Ω→ₐ[Ω] E:=aeval ![t]
  have hinj:Function.Injective φt:=
    algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_iff_transcendental.mpr ht)
  let q:Polynomial E:=(e Q).map φt.toRingHom
  have hq0:q ≠ 0:=by
    intro h
    apply hQ
    have h1:e Q=0:=by
      apply Polynomial.map_injective φt.toRingHom hinj
      rw [Polynomial.map_zero]
      exact h
    simpa using congrArg e.symm h1
  refine ⟨q,hq0,?_⟩
  let Ψ:MvPolynomial (Fin 2) Ω→ₐ[Ω] R:=
    ((Polynomial.aeval a).restrictScalars Ω).comp ((Polynomial.mapAlgHom φt).comp e.toAlgHom)
  have hΨ:Ψ=aeval ![a,algebraMap E R t]:=by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · simp [Ψ,e,finSuccEquiv_X_zero]
    · have hX1:e (MvPolynomial.X 1)=Polynomial.C (MvPolynomial.X 0):=finSuccEquiv_X_succ (j:=0)
      show Polynomial.aeval a ((e (MvPolynomial.X 1)).map (φt:MvPolynomial (Fin 1) Ω→+*E))=_
      rw [hX1,Polynomial.map_C,Polynomial.aeval_C]
      simp [φt]
  have h1:Ψ Q=Polynomial.aeval a q:=rfl
  rw [← h1,hΨ,h]

theorem DLB {E R:Type*} [Field E] [Field R] [Algebra Ω E]
    [Algebra E R] [Algebra Ω R] [IsScalarTower Ω E R]
    (G P:MvPolynomial (Fin 3) Ω) (hG:Irreducible G) (hGP: ¬G ∣ P)
    (y:Fin 3→R) (hGy:aeval y G=0) (hPy:aeval y P=0)
    (i:Fin 3) (c:Fin 3→Ω) (hci:c i=1) (t:E) (ht:Transcendental Ω t)
    (hℓ: ∑ m,algebraMap Ω R (c m)*y m=algebraMap E R t):
    ∀m,IsAlgebraic E (y m):=by
  classical
  let f:Fin 3→MvPolynomial (Fin 3) Ω:=fun m=>
    if m=i then MvPolynomial.X i- ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' else MvPolynomial.X m
  let g:Fin 3→MvPolynomial (Fin 3) Ω:=fun m=>
    if m=i then ∑ m',C (c m')*MvPolynomial.X m' else MvPolynomial.X m
  have herase: ∀T:MvPolynomial (Fin 3) Ω,
      ∑ m' ∈ Finset.univ.erase i,C (c m')*(if m' =i then T else MvPolynomial.X m')=
        ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' :=fun T=>
    Finset.sum_congr rfl (fun m' hm' =>by rw [if_neg (Finset.ne_of_mem_erase hm')])
  have hsplit: ∑ m',C (c m')*(MvPolynomial.X m' :MvPolynomial (Fin 3) Ω)=
      MvPolynomial.X i+ ∑ m' ∈ Finset.univ.erase i,C (c m')*MvPolynomial.X m' :=by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),hci,map_one,one_mul]
  have hgf: ∀m,bind₁ g (f m)=MvPolynomial.X m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,g,if_true,map_sub,map_sum,map_mul,bind₁_X_right,bind₁_C_right]
      rw [herase,hsplit]
      ring
    · simp [f,g,hm]
  have hfg: ∀m,bind₁ f (g m)=MvPolynomial.X m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,g,if_true,map_sum,map_mul,bind₁_X_right,bind₁_C_right]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul,if_pos rfl,
        herase]
      ring
    · simp [f,g,hm]
  let τ:MvPolynomial (Fin 3) Ω ≃ₐ[Ω] MvPolynomial (Fin 3) Ω:=
    AlgEquiv.ofAlgHom (bind₁ f) (bind₁ g)
      (MvPolynomial.algHom_ext fun m=>by simp [hfg])
      (MvPolynomial.algHom_ext fun m=>by simp [hgf])
  let z:Fin 3→R:=fun m=>if m=i then algebraMap E R t else y m
  have hz: ∀m,aeval z (f m)=y m:=by
    intro m
    by_cases hm:m=i
    · subst hm
      simp only [f,z,if_true,map_sub,map_sum,map_mul,aeval_X,aeval_C]
      rw [Finset.sum_congr rfl (fun m' hm' =>by rw [if_neg (Finset.ne_of_mem_erase hm')]),
        ← hℓ,← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul]
      ring
    · simp [f,z,hm]
  have hτ: ∀p,aeval z (τ p)=aeval y p:=by
    intro p
    change aeval z (bind₁ f p)=aeval y p
    rw [aeval_bind₁,show (fun m=>aeval z (f m))=y from funext hz]
  have hG' :Irreducible (τ G):=(MulEquiv.irreducible_iff τ).mpr hG
  have hGP' : ¬τ G ∣ τ P:=by
    rintro ⟨d,hd⟩
    exact hGP ⟨τ.symm d,by apply τ.injective;rw [map_mul,AlgEquiv.apply_symm_apply,hd]⟩
  have hother: ∀m,m ≠ i→IsAlgebraic E (y m):=by
    intro m hm
    obtain ⟨Q,hQ,hQz⟩:=GET (τ G) (τ P) hG' hGP' z
      (by rw [hτ,hGy]) (by rw [hτ,hPy]) m i hm
    have hzz: ![z m,z i]= ![y m,algebraMap E R t]:=by simp [z,hm]
    rw [hzz] at hQz
    exact EOA t ht (y m) Q hQ hQz
  intro m
  by_cases hm:m=i
  · subst hm
    have hy:y m=algebraMap E R t-
        ∑ m' ∈ Finset.univ.erase m,algebraMap Ω R (c m')*y m' :=by
      rw [← hℓ,← Finset.add_sum_erase _ _ (Finset.mem_univ m),hci,map_one,one_mul]
      ring
    rw [isAlgebraic_iff_isIntegral,hy]
    refine (integralClosure E R).sub_mem (IsIntegral.algebraMap isIntegral_algebraMap)
      ((integralClosure E R).sum_mem fun m' hm' => ?_)
    refine (integralClosure E R).mul_mem ?_ ?_
    · rw [IsScalarTower.algebraMap_apply Ω E R]
      exact IsIntegral.algebraMap isIntegral_algebraMap
    · exact isAlgebraic_iff_isIntegral.mp (hother m' (Finset.ne_of_mem_erase hm'))
  · exact hother m hm

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341

section Contraction

theorem ABU {E:Type} [Field E] (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (x:MvPolynomial (Fin 3) E):BR E D x=0 ↔ x ∈ D:=by
  have h:=FB E D
  constructor
  · intro hx
    rw [← h]
    exact hx
  · intro hx
    rw [← h] at hx
    exact hx

variable {Ω E:Type} [Field Ω] [Field E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]

noncomputable abbrev sliceValue (Ω E:Type) [Field Ω] [Field E] [Algebra (RatFunc Ω) E]:E:=
  algebraMap (RatFunc Ω) E (PF Ω)

theorem AMM:Transcendental Ω (sliceValue Ω E):=by
  have h:PF Ω=RatFunc.X:=RatFunc.algebraMap_X
  rw [sliceValue,h,transcendental_algebraMap_iff (algebraMap (RatFunc Ω) E).injective]
  exact RatFunc.transcendental_X

omit [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in

theorem EXZ (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (A:MvPolynomial (Fin 3) Ω) (hA:A ≠ 0) (hAD:CD Ω E A ∈ D):
    ∃G,Irreducible G∧G ∣ A∧CD Ω E G ∈ D:=by
  classical
  revert hA hAD
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁=>intro h;exact absurd rfl h
  | h₂ u hu=>
    intro _ hAD
    exact absurd (Ideal.eq_top_of_isUnit_mem D hAD (hu.map _)) Ideal.IsPrime.ne_top'
  | h₃ a q ha hq ih=>
    intro hA hAD
    rw [map_mul] at hAD
    rcases Ideal.IsPrime.mem_or_mem inferInstance hAD with h | h
    · exact ⟨q,hq.irreducible,dvd_mul_right q a,h⟩
    · obtain ⟨G,hG,hGa,hGD⟩:=ih ha h
      exact ⟨G,hG,hGa.mul_left q,hGD⟩

theorem GPB (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:BP D) (G:MvPolynomial (Fin 3) Ω) (hG:Irreducible G)
    (hGD:CD Ω E G ∈ D) (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue Ω E)-
      CD Ω E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    D.comap (CD Ω E)=Ideal.span {G}:=by
  classical
  have hev: ∀A:MvPolynomial (Fin 3) Ω,
      aeval (coordinate E D) A=BR E D (CD Ω E A):=by
    intro A
    rw [HJ,CD,aeval_map_algebraMap]
  have hzero: ∀A:MvPolynomial (Fin 3) E,A ∈ D→BR E D A=0:=
    fun A hA=>(ABU D A).2 hA
  apply le_antisymm
  · intro P hP
    rw [Ideal.mem_span_singleton]
    by_contra hGP
    have hℓ: ∑ m,algebraMap Ω (AJ E D) (c m)*coordinate E D m=
        algebraMap E (AJ E D) (sliceValue Ω E):=by
      have h1:=hzero _ hslice
      rw [map_sub,sub_eq_zero] at h1
      rw [← hev] at h1
      have h2:BR E D (MvPolynomial.C (sliceValue Ω E))=
          algebraMap E (AJ E D) (sliceValue Ω E):=
        (BR E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum,map_mul,aeval_C,aeval_X]
    have halg:=DLB G P hG hGP (coordinate E D)
      (by rw [hev];exact hzero _ hGD) (by rw [hev];exact hzero _ hP) i c hci
      (sliceValue Ω E) AMM hℓ
    exact sep.transcendental (halg sep.index)
  · rw [Ideal.span_le,Set.singleton_subset_iff]
    exact hGD

end Contraction

section Descent

variable {K:Type} [Field K] {E:Type} [Field E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

noncomputable def sliceMap (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]:
    MvPolynomial (Fin 4) K→+*AJ E D:=
  (BR E D).toRingHom.comp
    (surfaceMap ((algebraMap (GenericField K) E).comp (AL K)))

omit [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem AXD (A:MvPolynomial (Fin 4) K):
    surfaceMap ((algebraMap (GenericField K) E).comp (AL K)) A=
      CD (GenericField K) E (surfaceMap (AL K) A):=by
  simp only [surfaceMap,CD,RingHom.comp_apply,MvPolynomial.map_map]

theorem FVZ (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:BP D) (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0)
    (hFD:surfaceMap ((algebraMap (GenericField K) E).comp (AL K)) F ∈ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    ∃F₀:MvPolynomial (Fin 4) K,Irreducible F₀∧F₀ ∣ F∧
      RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀}:=by
  classical
  set φ:=AL K
  have hA:surfaceMap φ F ≠ 0:=ZL φ (DI K) F hF
  have hAD:CD (GenericField K) E (surfaceMap φ F) ∈ D:=by
    rw [← AXD];exact hFD
  obtain ⟨G,hG,-,hGD⟩:=EXZ D (surfaceMap φ F) hA hAD
  have hcomap:=GPB D sep G hG hGD c i hci hslice
  have hker:RingHom.ker (sliceMap (K:=K) D)=AWO (Ideal.span {G}):=by
    ext A
    rw [RingHom.mem_ker,AOX,← hcomap,Ideal.mem_comap,
      ← AXD]
    exact ABU D _
  haveI hGprime:(Ideal.span {G}).IsPrime:=
    (Ideal.span_singleton_prime hG.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hG)
  have hGheight:(Ideal.span {G}).height=1:=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hG.ne_zero) hG.not_isUnit
  set Q:=RingHom.ker (sliceMap (K:=K) D)
  haveI hQprime:Q.IsPrime:=RingHom.ker_isPrime _
  have hQheight:Q.height≤1:=by
    rw [hker,← hGheight]
    exact BCQ _
  have hFQ:F ∈ Q:=(ABU D _).2 hFD
  have hQbot:Q ≠ ⊥ :=by
    intro h;rw [h] at hFQ;exact hF ((Submodule.mem_bot _).mp hFQ)
  obtain ⟨F₀,hF₀Q,hF₀⟩:=hQprime.exists_mem_prime_of_ne_bot hQbot
  haveI hF₀prime:(Ideal.span {F₀}).IsPrime:=(Ideal.span_singleton_prime hF₀.ne_zero).mpr hF₀
  have hF₀height:(Ideal.span {F₀}).height=1:=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hF₀.ne_zero) hF₀.not_unit
  have hle:Ideal.span {F₀}≤Q:=by
    rw [Ideal.span_le,Set.singleton_subset_iff];exact hF₀Q
  have heq:Ideal.span {F₀}=Q:=by
    by_contra hne
    have hlt:=Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hF₀height] at hlt
    have h2:(2:ℕ∞)≤1:=hlt.trans hQheight
    exact absurd h2 (by decide)
  refine ⟨F₀,hF₀.irreducible,?_,heq.symm⟩
  rw [← Ideal.mem_span_singleton,heq]
  exact hFQ

end Descent

section SliceField

open RCN313 RCN055 RCN077 RCN188

variable {K:Type} [Field K] (F F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]

abbrev SliceRing:=MvPolynomial (Fin 4) K ⧸ Ideal.span {F₀}

instance sliceRing_isPrime:(Ideal.span {F₀}).IsPrime:=
  (Ideal.span_singleton_prime hF₀.out.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF₀.out)

instance:IsDomain (SliceRing F₀):=Ideal.Quotient.isDomain _

abbrev SliceField:=FractionRing (SliceRing F₀)

noncomputable def sliceProj:MvPolynomial (Fin 4) K→+*SliceField F₀:=
  (algebraMap (SliceRing F₀) (SliceField F₀)).comp (Ideal.Quotient.mk _)

omit hF₀ in
theorem BMJ (A:MvPolynomial (Fin 4) K):sliceProj F₀ A=0 ↔ F₀ ∣ A:=by
  rw [sliceProj,RingHom.comp_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (SliceRing F₀) (SliceField F₀)),
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]

omit hF₀ in

theorem FCH (hdvd:F₀ ∣ F):
    ∀P ∈ Ideal.span {F₀},OB F P ∈ Ideal.span {F₀}:=by
  obtain ⟨F₁,rfl⟩:=hdvd
  have h0:OB (F₀*F₁) F₀ ∈ Ideal.span {F₀}:=by
    rw [Ideal.mem_span_singleton]
    refine ⟨MvPolynomial.pderiv 2 F₁*(MvPolynomial.pderiv 0 F₀+
        MvPolynomial.X 2*MvPolynomial.pderiv 1 F₀)-
      (MvPolynomial.pderiv 0 F₁+MvPolynomial.X 2*MvPolynomial.pderiv 1 F₁)*
        MvPolynomial.pderiv 2 F₀,?_⟩
    rw [AEH,polyH,polyG]
    simp only [Derivation.leibniz,smul_eq_mul]
    ring
  intro P hP
  obtain ⟨Q,rfl⟩:=Ideal.mem_span_singleton.mp hP
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
  exact (Ideal.span {F₀}).add_mem
    ((Ideal.span {F₀}).mul_mem_right _ (Ideal.mem_span_singleton_self F₀))
    ((Ideal.span {F₀}).mul_mem_left _ h0)

noncomputable def DOT (hdvd:F₀ ∣ F):
    Derivation K (SliceField F₀) (SliceField F₀):=
  ANA (nonZeroDivisors (SliceRing F₀))
    (ATK (OB F) (Ideal.span {F₀}) (FCH F F₀ hdvd))

noncomputable def JJ (hdvd:F₀ ∣ F):
    Derivation K (SliceField F₀) (SliceField F₀):=
  (sliceProj F₀ (polyH K F))⁻¹ • DOT F F₀ hdvd

theorem BQH (hdvd:F₀ ∣ F) (P:MvPolynomial (Fin 4) K):
    JJ F F₀ hdvd (sliceProj F₀ P)=
      sliceProj F₀ (OB F P)/sliceProj F₀ (polyH K F):=by
  rw [JJ,Derivation.smul_apply,smul_eq_mul,div_eq_inv_mul]
  congr 1
  simp only [DOT,sliceProj,RingHom.comp_apply]
  rw [AGQ,AXS]

theorem ARA (hdvd:F₀ ∣ F) (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (P:MvPolynomial (Fin 4) K):
    JJ F F₀ hdvd (sliceProj F₀ P)=
      sliceProj F₀ (MvPolynomial.pderiv 0 P+MvPolynomial.X 2*MvPolynomial.pderiv 1 P)+
        sliceProj F₀ (MvPolynomial.pderiv 2 P)*
          (sliceProj F₀ (polyG K F)/sliceProj F₀ (polyH K F)):=by
  rw [BQH,AEH]
  simp only [map_add,map_mul]
  field_simp

theorem DJY (hdvd:F₀ ∣ F) (hH:sliceProj F₀ (polyH K F) ≠ 0) (n:ℕ):
    (⇑(JJ F F₀ hdvd))^[n+1] (sliceProj F₀ (MvPolynomial.X 2))=
      sliceProj F₀ (MN F n)/sliceProj F₀ (polyH K F)^(2*n+1):=by
  induction n with
  | zero=>
    rw [Function.iterate_one,BQH,EZS]
    simp [MN]
  | succ n ih=>
    rw [Function.iterate_succ_apply',ih,Derivation.leibniz_div,Derivation.leibniz_pow,
      BQH,BQH]
    simp only [MN,smul_eq_mul,nsmul_eq_mul,map_sub,map_mul,map_natCast,
      Nat.add_sub_cancel]
    field_simp
    ring

end SliceField

section Embedding

variable {K:Type} [Field K] {E:Type} [Field E]
  [Algebra (GenericField K) E] (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
  (F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]

noncomputable def RY (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀}):
    SliceField F₀→+*AJ E D:=
  IsFractionRing.lift (A:=SliceRing F₀)
    (g:=Ideal.Quotient.lift (Ideal.span {F₀}) (sliceMap (K:=K) D) (fun a ha=>by
      rw [← hker] at ha;exact ha))
    ((Ideal.injective_lift_iff _).mpr hker)

theorem SR (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
    (A:MvPolynomial (Fin 4) K):
    RY D F₀ hker (sliceProj F₀ A)=sliceMap (K:=K) D A:=by
  rw [RY,sliceProj,RingHom.comp_apply,IsFractionRing.lift_algebraMap]
  rfl

end Embedding

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero Polynomial

section Core

variable {K L:Type*} [Field K] [Field L] [Algebra K L]
variable (v:Valuation L ℤᵐ⁰) (D:Derivation K L L)

def Tame (Λ:ℤᵐ⁰) (z:L):Prop:=v z≤1∧v (D z)≤Λ

omit [Field K] [Algebra K L] in
theorem GAB (n:ℕ):v (n:L)≤1:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

omit [Field K] [Algebra K L] in
theorem v_nsmul_le (n:ℕ) (x:L):v (n • x)≤v x:=by
  rw [nsmul_eq_mul,v.map_mul]
  exact mul_le_of_le_one_left' (GAB v n)

def tameSubring (Λ:ℤᵐ⁰):Subring L where
  carrier:={z | Tame v D Λ z}
  mul_mem' :=by
    rintro a b ⟨ha,hDa⟩ ⟨hb,hDb⟩
    refine ⟨by rw [v.map_mul];exact mul_le_one' ha hb,?_⟩
    rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
    refine (v.map_add _ _).trans (max_le ?_ ?_)<;>rw [v.map_mul]
    · exact (mul_le_mul_left ha _).trans (by rw [one_mul];exact hDb)
    · exact (mul_le_mul_left hb _).trans (by rw [one_mul];exact hDa)
  one_mem' :=⟨by simp,by simp⟩
  add_mem' :=by
    rintro a b ⟨ha,hDa⟩ ⟨hb,hDb⟩
    exact ⟨(v.map_add _ _).trans (max_le ha hb),
      by rw [map_add];exact (v.map_add _ _).trans (max_le hDa hDb)⟩
  zero_mem' :=⟨by simp,by simp⟩
  neg_mem' :=by
    rintro a ⟨ha,hDa⟩
    exact ⟨by rw [v.map_neg];exact ha,by rw [map_neg,v.map_neg];exact hDa⟩

theorem Tame.mono {Λ Λ' :ℤᵐ⁰} (h:Λ≤Λ') {z:L} (hz:Tame v D Λ z):
    Tame v D Λ' z:=
  ⟨hz.1,hz.2.trans h⟩

def NO (Λ:ℤᵐ⁰):Prop:=
  ∀z:L,v z≤1→ ∃μ:L[X],(∀j,Tame v D Λ (μ.coeff j))∧
    v (μ.eval z)<1∧v (μ.derivative.eval z)=1

theorem NO.mono {Λ Λ' :ℤᵐ⁰} (h:Λ≤Λ')
    (hsep:NO v D Λ):NO v D Λ' :=by
  intro z hz
  obtain ⟨μ,hμ,h1,h2⟩:=hsep z hz
  exact ⟨μ,fun j=>(hμ j).mono v D h,h1,h2⟩

def CrudeBound (C:ℤ):Prop:= ∀z:L,v z≤1→v (D z)≤exp C

theorem GIJ (μ:L[X]) (z:L):
    D (μ.eval z)=μ.derivative.eval z*D z+ ∑ n ∈ μ.support,z^n*D (μ.coeff n):=by
  rw [Polynomial.eval_eq_sum,Polynomial.derivative_eval,Polynomial.sum_def,
    Polynomial.sum_def,map_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _=> ?_
  rw [Derivation.leibniz,Derivation.leibniz_pow]
  simp only [smul_eq_mul,nsmul_eq_mul]
  ring

theorem EVJ (Λ:ℤᵐ⁰) (μ:L[X]) (hμ: ∀j,Tame v D Λ (μ.coeff j))
    (z:L) (hz:v z≤1):
    v (D (μ.eval z)-μ.derivative.eval z*D z)≤Λ:=by
  rw [GIJ,add_sub_cancel_left]
  refine v.map_sum_le fun n _=> ?_
  rw [v.map_mul,v.map_pow]
  exact (mul_le_mul_left (pow_le_one' hz n) _).trans (by rw [one_mul];exact (hμ n).2)

theorem GFH (π:L) (hπ:v π=exp (-1)) (x:L) (hx:v x<1):
    ∃e:L,v e≤1∧x=π*e:=by
  have hπ0:π ≠ 0:=by
    intro h;rw [h,v.map_zero] at hπ;exact exp_ne_zero hπ.symm
  refine ⟨x/π,?_,by field_simp⟩
  have hx' :v x≤exp (-1):=by
    rw [← lt_mul_exp_iff_le exp_ne_zero,← exp_add];simpa using hx
  rw [map_div₀,hπ,div_le_iff₀ exp_pos,one_mul]
  exact hx'

theorem bootstrap (π:L) (hπ:v π=exp (-1)) (Λ:ℤᵐ⁰) (hπΛ:v (D π)≤Λ) (C:ℤ)
    (hcont:CrudeBound v D C) (hsep:NO v D Λ):
    ∀N:ℕ,∀z:L,v z≤1→v (D z)≤max Λ (exp (C-N)):=by
  intro N
  induction N with
  | zero=>intro z hz;simpa using le_max_of_le_right (hcont z hz)
  | succ N ih=>
    intro z hz
    obtain ⟨μ,hμ,hμz,hμ'⟩:=hsep z hz
    obtain ⟨e,he,hμe⟩:=GFH v π hπ _ hμz
    have hkey:μ.derivative.eval z*D z=
        π*D e+e*D π-(D (μ.eval z)-μ.derivative.eval z*D z):=by
      rw [hμe,Derivation.leibniz,smul_eq_mul,smul_eq_mul];ring
    have hvz:v (D z)=v (μ.derivative.eval z*D z):=by rw [v.map_mul,hμ',one_mul]
    rw [hvz,hkey]
    refine (v.map_sub _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)
    · rw [v.map_mul,hπ]
      refine (mul_le_mul_right (ih e he) _).trans ?_
      rw [mul_max]
      refine max_le_max ?_ ?_
      · exact mul_le_of_le_one_left' (by rw [← exp_zero,exp_le_exp];omega)
      · rw [← exp_add];simp only [exp_le_exp];push_cast;omega
    · rw [v.map_mul]
      exact le_max_of_le_left ((mul_le_mul_left he _).trans (by rw [one_mul];exact hπΛ))
    · exact le_max_of_le_left (EVJ v D Λ μ hμ z hz)

theorem FOE (π:L) (hπ:v π=exp (-1)) (Λ:ℤᵐ⁰) (hΛ:1≤Λ)
    (hπΛ:v (D π)≤Λ) (C:ℤ) (hcont:CrudeBound v D C)
    (hsep:NO v D Λ):
    ∀u:L,v u≤1→v (D u)≤Λ:=by
  intro u hu
  refine (bootstrap v D π hπ Λ hπΛ C hcont hsep C.toNat u hu).trans (max_le le_rfl ?_)
  refine le_trans ?_ hΛ
  rw [← exp_zero,exp_le_exp];omega

omit [Field K] [Algebra K L] in
theorem pi_ne_zero (π:L) (hπ:v π=exp (-1)):π ≠ 0:=by
  intro h;rw [h,v.map_zero] at hπ;exact exp_ne_zero hπ.symm

theorem CVO (k:ℕ):(exp (-1:ℤ))^k=exp (-(k:ℤ)):=by
  rw [← exp_nsmul];congr 1;simp

omit [Field K] [Algebra K L] in

theorem unit_part (π:L) (hπ:v π=exp (-1)) (f:L) (n:ℕ)
    (hf:v f=exp (-(n:ℤ))):
    v (f/π^n)=1∧f=f/π^n*π^n:=by
  have hπn:π^n ≠ 0:=pow_ne_zero _ (pi_ne_zero v π hπ)
  refine ⟨?_,by field_simp⟩
  rw [map_div₀,v.map_pow,hπ,CVO,hf,div_self exp_ne_zero]

theorem FTJ (π:L) (hπ:v π=exp (-1)) (θ:ℤ)
    (hint: ∀u:L,v u≤1→v (D u)≤exp θ) (hπθ:v (D π)≤exp (θ-1)):
    ∀f:L,v (D f)≤exp θ*v f:=by
  have hI: ∀f:L,v f≤1→v (D f)≤exp θ*v f:=by
    intro f hf
    by_cases hf0:f=0
    · simp [hf0]
    have hvf:v f ≠ 0:=(Valuation.ne_zero_iff v).2 hf0
    have hm:v f=exp (v f).log:=(exp_log hvf).symm
    have hm0:(v f).log≤0:=by
      rw [← exp_le_exp,← hm,exp_zero];exact hf
    obtain ⟨n,hn⟩: ∃n:ℕ,(v f).log= -(n:ℤ):=⟨((v f).log).natAbs,by omega⟩
    rw [hn] at hm
    obtain ⟨hu,hfu⟩:=unit_part v π hπ f n hm
    set u:=f/π^n
    rw [hm,hfu,Derivation.leibniz,Derivation.leibniz_pow]
    simp only [smul_eq_mul]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · cases n with
      | zero=>simp
      | succ k=>
        rw [v.map_mul,hu,one_mul]
        refine (v_nsmul_le v _ _).trans ?_
        rw [v.map_mul,v.map_pow,hπ,Nat.add_sub_cancel,CVO]
        refine (mul_le_mul_right hπθ _).trans ?_
        rw [← exp_add,← exp_add,exp_le_exp];push_cast;omega
    · rw [v.map_mul,v.map_pow,hπ,CVO,mul_comm (exp θ)]
      exact mul_le_mul_right (hint u hu.le) _
  intro f
  by_cases hf:v f≤1
  · exact hI f hf
  have hf0:f ≠ 0:=by rintro rfl;simp at hf
  have hvf:v f ≠ 0:=(Valuation.ne_zero_iff v).2 hf0
  have hg:v f⁻¹≤1:=by
    rw [map_inv₀];exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hf))
  have h:=hI f⁻¹ hg
  rw [← inv_inv f,Derivation.leibniz_inv,smul_eq_mul,v.map_mul,v.map_neg,v.map_pow,
    inv_inv]
  calc v f^2*v (D f⁻¹)≤v f^2*(exp θ*v f⁻¹):=mul_le_mul_right h _
    _=exp θ*v f:=by rw [map_inv₀];field_simp

theorem GTL (θ:ℤ) (hθ:0≤θ) (f g:L) (h:v g≤exp θ*v f):
    max 0 (v g).log≤max 0 (v f).log+θ:=by
  by_cases hg:v g=0
  · rw [hg,log_zero];omega
  have hf:v f ≠ 0:=by
    intro hf;rw [hf,mul_zero] at h;exact hg (le_antisymm h zero_le)
  have hlog:(v g).log≤θ+(v f).log:=by
    rw [← log_exp θ,← log_mul exp_ne_zero hf,log_le_log hg (mul_ne_zero exp_ne_zero hf)]
    exact h
  omega

theorem EAH (π:L) (hπ:v π=exp (-1)) (s:ℤ) (hs:0≤s) (C:ℤ)
    (hcont:CrudeBound v D C) (hsep:NO v D (exp s)):
    ∀u:L,v u≤1→v (D u)≤max (exp s) (v (D π)):=
  FOE v D π hπ _ (le_max_of_le_left (by rw [← exp_zero,exp_le_exp];exact hs))
    (le_max_right _ _) C hcont (hsep.mono v D (le_max_left _ _))

theorem GFD (π:L) (hπ:v π=exp (-1)) (s θ:ℤ) (hs:0≤s)
    (hsθ:s≤θ) (hπθ:v (D π)≤exp (θ-1)) (C:ℤ)
    (hcont:CrudeBound v D C) (hsep:NO v D (exp s)) (f:L):
    v (D f)≤exp θ*v f:=by
  refine FTJ v D π hπ θ (fun u hu=> ?_) hπθ f
  refine (EAH v D π hπ s hs C hcont hsep u hu).trans (max_le ?_ ?_)
  · rw [exp_le_exp];exact hsθ
  · exact hπθ.trans (by rw [exp_le_exp];omega)

theorem EYP [v.IsTrivialOn K] (π:L) (hπ:v π=exp (-1)) (s T:ℤ)
    (hint: ∀u:L,v u≤1→v (D u)≤max (exp s) (v (D π)))
    (f:L) (n:ℕ) (hn:(n:K) ≠ 0) (hf:v f=exp (-(n:ℤ)))
    (hDf:v (D f)≤exp T):
    v (D π)≤exp (max s (T+n)-1):=by
  by_contra hlt
  rw [not_le] at hlt
  have hDπ0:v (D π) ≠ 0:=(exp_pos.trans hlt).ne'
  have hd:v (D π)=exp (v (D π)).log:=(exp_log hDπ0).symm
  rw [hd,exp_lt_exp] at hlt
  have hn1:n ≠ 0:=by rintro rfl;exact hn (by simp)
  obtain ⟨k,rfl⟩: ∃k,n=k+1:=⟨n-1,by omega⟩
  obtain ⟨hu,hfu⟩:=unit_part v π hπ f (k+1) hf
  set u:=f/π^(k+1)
  have hvn:v ((k+1:ℕ):L)=1:=by
    rw [← map_natCast (algebraMap K L)];exact Valuation.IsTrivialOn.eq_one _ hn
  rw [hfu,Derivation.leibniz,Derivation.leibniz_pow] at hDf
  simp only [smul_eq_mul] at hDf
  have hA:v (u*((k+1) • (π^(k+1-1)*D π)))=exp ((v (D π)).log-k):=by
    rw [v.map_mul,hu,one_mul,nsmul_eq_mul,v.map_mul,hvn,one_mul,
      v.map_mul,v.map_pow,hπ,Nat.add_sub_cancel,CVO,hd,← exp_add,log_exp]
    congr 1;ring
  have hs1:s-1<(v (D π)).log:=lt_of_le_of_lt (by omega) hlt
  have hB:v (π^(k+1)*D u)<exp ((v (D π)).log-k):=by
    rw [v.map_mul,v.map_pow,hπ,CVO]
    have h1:=hint u hu.le
    rw [hd] at h1
    refine lt_of_le_of_lt (mul_le_mul_right h1 _) ?_
    rw [mul_max,← exp_add,← exp_add]
    apply max_lt<;>rw [exp_lt_exp]<;>push_cast<;>omega
  rw [v.map_add_eq_of_lt_left (by rw [hA];exact hB),hA,exp_le_exp] at hDf
  have hT1:T+((k+1:ℕ):ℤ)-1<(v (D π)).log:=lt_of_le_of_lt (by omega) hlt
  push_cast at hT1
  omega

theorem ECM [v.IsTrivialOn K] (π:L) (hπ:v π=exp (-1)) (s:ℤ)
    (hs:0≤s) (C:ℤ) (hcont:CrudeBound v D C) (hsep:NO v D (exp s))
    (f:L) (n:ℕ) (hn:(n:K) ≠ 0) (hf:v f=exp (-(n:ℤ))) (T:ℤ)
    (hDf:v (D f)≤exp T):
    ∀g:L,v (D g)≤exp (max s (T+n))*v g:=by
  have h1:=EYP v D π hπ s T (EAH v D π hπ s hs C hcont hsep)
    f n hn hf hDf
  exact GFD v D π hπ s (max s (T+n)) hs (le_max_left _ _) h1 C hcont hsep

theorem GSO [v.IsTrivialOn K] (π:L) (hπ:v π=exp (-1)) (s:ℤ)
    (hs:0≤s) (C:ℤ) (hcont:CrudeBound v D C) (hsep:NO v D (exp s))
    (c:L) (P:ℕ) (hP:(P:K) ≠ 0) (hc:v c=exp (P:ℤ)) (Q:ℤ)
    (hQ:v (D c)≤exp Q):
    ∀g:L,v (D g)≤exp (max s (max 0 (Q-2*P)+P))*v g:=by
  have hc0:c ≠ 0:=by intro h;rw [h,v.map_zero] at hc;exact exp_ne_zero hc.symm
  have hu:v c⁻¹=exp (-(P:ℤ)):=by rw [map_inv₀,hc,exp_neg]
  have hDu:v (D c⁻¹)≤exp (max 0 (Q-2*P)):=by
    rw [Derivation.leibniz_inv,smul_eq_mul,v.map_mul,v.map_neg,v.map_pow,hu]
    calc exp (-(P:ℤ))^2*v (D c)≤exp (-(P:ℤ))^2*exp Q:=mul_le_mul_right hQ _
      _≤exp (max 0 (Q-2*P)):=by
        rw [sq,← exp_add,← exp_add,exp_le_exp];omega
  exact ECM v D π hπ s hs C hcont hsep c⁻¹ P hP hu _ hDu

end Core

section Bridges

variable {K L:Type*} [Field K] [Field L] [Algebra K L]
variable (v:Valuation L ℤᵐ⁰) (D:Derivation K L L)

theorem EEO (R:Subring L) (C:ℤ)
    (hR: ∀r ∈ R,Tame v D (exp C) r)
    (hloc: ∀z:L,v z≤1→ ∃r ∈ R,∃u ∈ R,v u=1∧z=r/u):
    CrudeBound v D C:=by
  intro z hz
  obtain ⟨r,hr,u,hu,hu1,rfl⟩:=hloc z hz
  rw [Derivation.leibniz_div,smul_eq_mul,v.map_mul,v.map_pow,map_inv₀,hu1,inv_one,
    one_pow,one_mul]
  simp only [smul_eq_mul]
  refine (v.map_sub _ _).trans (max_le ?_ ?_)<;>rw [v.map_mul]
  · rw [hu1,one_mul];exact (hR r hr).2
  · exact (mul_le_mul_left (hR r hr).1 _).trans (by rw [one_mul];exact (hR u hu).2)

theorem tame_inv (Λ:ℤᵐ⁰) (u:L) (hu:Tame v D Λ u) (hu1:v u=1):
    Tame v D Λ u⁻¹:=by
  refine ⟨by rw [map_inv₀,hu1,inv_one],?_⟩
  rw [Derivation.leibniz_inv,smul_eq_mul,v.map_mul,v.map_neg,v.map_pow,map_inv₀,hu1,
    inv_one,one_pow,one_mul]
  exact hu.2

noncomputable def residue (z:L):IsLocalRing.ResidueField v.valuationSubring:=
  open Classical in
  if h:v z≤1 then IsLocalRing.residue v.valuationSubring ⟨z,h⟩ else 0

theorem AJL (z:L) (hz:v z≤1):
    residue v z=IsLocalRing.residue v.valuationSubring ⟨z,hz⟩:=by
  simp [residue,hz]

theorem ZT (z:L) (hz:v z≤1):residue v z=0 ↔ v z<1:=by
  rw [AJL v z hz,IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  exact (Valuation.isEquiv_iff_val_lt_one.1 v.isEquiv_valuation_valuationSubring).symm

def tameIn (Λ:ℤᵐ⁰):Subring v.valuationSubring:=
  (tameSubring v D Λ).comap v.valuationSubring.subtype

noncomputable def tameResidue (Λ:ℤᵐ⁰):
    tameIn v D Λ→+*IsLocalRing.ResidueField v.valuationSubring:=
  (IsLocalRing.residue v.valuationSubring).comp (tameIn v D Λ).subtype

theorem EUO (Λ:ℤᵐ⁰) (a:tameIn v D Λ):
    tameResidue v D Λ a=residue v ((a:v.valuationSubring):L):=by
  rw [AJL v _ (a:v.valuationSubring).2];rfl

theorem DXX (Λ:ℤᵐ⁰) (S:Set L) (hS: ∀z ∈ S,Tame v D Λ z):
    (Subfield.closure (residue v '' S):Set (IsLocalRing.ResidueField v.valuationSubring)) ⊆
      Set.range (tameResidue v D Λ):=by
  have hsub:Subring.closure (residue v '' S)≤(tameResidue v D Λ).range:=by
    refine Subring.closure_le.2 ?_
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨⟨⟨z,(hS z hz).1⟩,hS z hz⟩,by rw [EUO]⟩
  intro c hc
  obtain ⟨y,hy,w,hw,rfl⟩:=Subfield.mem_closure_iff.1 hc
  obtain ⟨y',rfl⟩:=hsub hy
  obtain ⟨w',rfl⟩:=hsub hw
  by_cases hw0:tameResidue v D Λ w' =0
  · exact ⟨0,by rw [hw0,div_zero,map_zero]⟩
  set wL:L:=((w' :v.valuationSubring):L)
  have hwt:Tame v D Λ wL:=w'.2
  have hw1:v wL=1:=by
    rw [EUO] at hw0
    exact le_antisymm hwt.1 (not_lt.1 fun h=>hw0 ((ZT v wL hwt.1).2 h))
  have hwi:Tame v D Λ wL⁻¹:=tame_inv v D Λ wL hwt hw1
  let winv:tameIn v D Λ:=⟨⟨wL⁻¹,hwi.1⟩,hwi⟩
  have hprod:tameResidue v D Λ w' *tameResidue v D Λ winv=1:=by
    rw [← map_mul,← map_one (tameResidue v D Λ)]
    congr 1
    apply Subtype.ext;apply Subtype.ext
    change wL*wL⁻¹=1
    exact mul_inv_cancel₀ (by intro h;rw [h,v.map_zero] at hw1;exact zero_ne_one hw1)
  refine ⟨y' *winv,?_⟩
  rw [map_mul,eq_inv_of_mul_eq_one_right hprod,div_eq_mul_inv]

theorem DPF (Λ:ℤᵐ⁰) (S:Set L) (hS: ∀z ∈ S,Tame v D Λ z)
    (hres: ∀x:IsLocalRing.ResidueField v.valuationSubring,
      ∃p:(IsLocalRing.ResidueField v.valuationSubring)[X],
        (∀j,p.coeff j ∈ Subfield.closure (residue v '' S))∧
        p.eval x=0∧p.derivative.eval x ≠ 0):
    NO v D Λ:=by
  intro z hz
  set O:=v.valuationSubring
  let z' :O:=⟨z,hz⟩
  obtain ⟨p,hpc,hp0,hp1⟩:=hres (IsLocalRing.residue O z')
  have hlift:p ∈ Polynomial.lifts (tameResidue v D Λ):=by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact DXX v D Λ S hS (hpc n)
  obtain ⟨q,hq⟩:=(Polynomial.mem_lifts p).1 hlift
  set qO:O[X]:=q.map (tameIn v D Λ).subtype
  have hqO:qO.map (IsLocalRing.residue O)=p:=by
    rw [Polynomial.map_map];exact hq
  refine ⟨qO.map O.subtype,fun j=> ?_,?_,?_⟩
  · rw [Polynomial.coeff_map,Polynomial.coeff_map]
    exact (q.coeff j).2
  · have he:(qO.map O.subtype).eval z=((qO.eval z' :O):L):=by
      rw [Polynomial.eval_map O.subtype,show z=O.subtype z' from rfl,
        Polynomial.eval₂_at_apply];rfl
    have hr:residue v ((qO.eval z' :O):L)=0:=by
      rw [AJL v _ (qO.eval z').2,← hp0,← hqO,
        Polynomial.eval_map (IsLocalRing.residue O),Polynomial.eval₂_at_apply]
    rw [he]
    exact (ZT v _ (qO.eval z').2).1 hr
  · have he:(qO.map O.subtype).derivative.eval z=((qO.derivative.eval z' :O):L):=by
      rw [Polynomial.derivative_map,Polynomial.eval_map O.subtype,
        show z=O.subtype z' from rfl,Polynomial.eval₂_at_apply];rfl
    have hr:residue v ((qO.derivative.eval z' :O):L) ≠ 0:=by
      rw [AJL v _ (qO.derivative.eval z').2]
      intro h
      apply hp1
      rw [← hqO,Polynomial.derivative_map,Polynomial.eval_map (IsLocalRing.residue O),
        Polynomial.eval₂_at_apply]
      exact h
    rw [he]
    exact le_antisymm (qO.derivative.eval z').2
      (not_lt.1 fun h=>hr ((ZT v _ (qO.derivative.eval z').2).2 h))

theorem CXW (Λ:ℤᵐ⁰) (S:Set L) (hS: ∀z ∈ S,Tame v D Λ z)
    [Algebra.IsSeparable (Subfield.closure (residue v '' S))
      (IsLocalRing.ResidueField v.valuationSubring)]:
    NO v D Λ:=by
  refine DPF v D Λ S hS fun x=> ?_
  set F:=Subfield.closure (residue v '' S)
  have hsx:IsSeparable F x:=Algebra.IsSeparable.isSeparable F x
  refine ⟨(minpoly F x).map (algebraMap F _),fun j=> ?_,?_,?_⟩
  · rw [Polynomial.coeff_map];exact ((minpoly F x).coeff j).2
  · rw [Polynomial.eval_map_algebraMap];exact minpoly.aeval F x
  · rw [Polynomial.derivative_map,Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hsx (minpoly.aeval F x)

end Bridges

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero Polynomial

section Local

variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)

theorem FRA (S:Subring L) (hS: ∀h ∈ S,v h≤1)
    (hfrac: ∀x:L,∃f ∈ S,∃g ∈ S,g ≠ 0∧x=f/g)
    (hsurj: ∃x:L,v x=exp (-1))
    (t:L) (ht:v t<1)
    (hloc: ∀h ∈ S,v h<1→ ∃u ∈ S,v u=1∧ ∃h' ∈ S,u*h=t*h'):
    v t=exp (-1):=by
  obtain ⟨x₀,hx₀⟩:=hsurj
  obtain ⟨f,hf,g,hg,hg0,rfl⟩:=hfrac x₀
  have hvg:v g ≠ 0:=(Valuation.ne_zero_iff v).2 hg0
  have hvf:v f=exp (-1)*v g:=by
    rw [map_div₀,div_eq_iff hvg] at hx₀;exact hx₀
  have hf0:f ≠ 0:=by
    intro h;rw [h,v.map_zero] at hvf;exact (mul_ne_zero exp_ne_zero hvg) hvf.symm
  have hflt:v f<1:=by
    rw [hvf]
    calc exp (-1)*v g≤exp (-1)*1:=mul_le_mul_right (hS g hg) _
      _<1:=by rw [mul_one,← exp_zero,exp_lt_exp];omega
  have ht0:t ≠ 0:=by
    intro ht0
    obtain ⟨u,-,hu,h',-,hu'⟩:=hloc f hf hflt
    rw [ht0,zero_mul] at hu'
    have hu0:u ≠ 0:=by rintro rfl;simp at hu
    exact hf0 ((mul_eq_zero.1 hu').resolve_left hu0)
  have hvt0:v t ≠ 0:=(Valuation.ne_zero_iff v).2 ht0
  set m:ℤ:= -(v t).log with hm_def
  have hvt:v t=exp (-m):=by rw [hm_def,neg_neg,exp_log hvt0]
  have hm:1≤m:=by
    have h1:v t<exp 0:=by rw [exp_zero];exact ht
    rw [hvt,exp_lt_exp] at h1;omega
  have key: ∀n:ℕ,∀h ∈ S,v h=exp (-(n:ℤ))→ ∃k:ℕ,v h=exp (-(m*k)):=by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih=>
      intro h hh hvh
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨0,by simpa using hvh⟩
      have hlt:v h<1:=by rw [hvh,← exp_zero,exp_lt_exp];omega
      obtain ⟨u,-,hu1,h',hh',hu'⟩:=hloc h hh hlt
      have hvv:v h=v t*v h' :=by
        have:=congrArg v hu';rwa [v.map_mul,v.map_mul,hu1,one_mul] at this
      have hvh'0:v h' ≠ 0:=by
        intro h0;rw [h0,mul_zero,hvh] at hvv;exact exp_ne_zero hvv
      have hvh' :v h' =exp (v h').log:=(exp_log hvh'0).symm
      have hn' :(v h').log≤0:=by
        rw [← exp_le_exp,← hvh',exp_zero];exact hS h' hh'
      have heq: -(n:ℤ)= -m+(v h').log:=by
        rw [hvh,hvt,hvh',← exp_add,exp_inj] at hvv;exact hvv
      obtain ⟨k,hk⟩:=ih (-(v h').log).toNat (by omega) h' hh'
        (hvh'.trans (by congr 1;omega))
      exact ⟨k+1,by rw [hvv,hvt,hk,← exp_add];congr 1;push_cast;ring⟩
  have ord: ∀h ∈ S,h ≠ 0→ ∃k:ℕ,v h=exp (-(m*k)):=by
    intro h hh h0
    have hvh0:=(Valuation.ne_zero_iff v).2 h0
    have hle:(v h).log≤0:=by
      rw [← exp_le_exp,exp_log hvh0,exp_zero];exact hS h hh
    exact key (-(v h).log).toNat h hh ((exp_log hvh0).symm.trans (by congr 1;omega))
  obtain ⟨k₁,hk₁⟩:=ord f hf hf0
  obtain ⟨k₂,hk₂⟩:=ord g hg hg0
  rw [hk₁,hk₂,← exp_add,exp_inj] at hvf
  have hmk:m*((k₂:ℤ)-k₁)= -1:=by linear_combination hvf
  have hm1:m=1:=by
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmk with h | h<;>omega
  rw [hvt,hm1]

variable {A:Type*} [CommRing A] (φ:A→+*L)

theorem range_frac (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g):
    ∀x:L,∃f ∈ φ.range,∃g ∈ φ.range,g ≠ 0∧x=f/g:=by
  intro x
  obtain ⟨f,g,hg,rfl⟩:=hfrac x
  exact ⟨φ f,⟨f,rfl⟩,φ g,⟨g,rfl⟩,hg,rfl⟩

theorem FKL (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g):
    ∃f:A,v (φ f)<1∧φ f ≠ 0:=by
  obtain ⟨x₀,hx₀⟩:=hsurj
  obtain ⟨f,g,hg0,rfl⟩:=hfrac x₀
  have hvg:v (φ g) ≠ 0:=(Valuation.ne_zero_iff v).2 hg0
  have hvf:v (φ f)=exp (-1)*v (φ g):=by
    rw [map_div₀,div_eq_iff hvg] at hx₀;exact hx₀
  refine ⟨f,?_,?_⟩
  · rw [hvf]
    calc exp (-1)*v (φ g)≤exp (-1)*1:=mul_le_mul_right (hint g) _
      _<1:=by rw [mul_one,← exp_zero,exp_lt_exp];omega
  · intro h;rw [h,v.map_zero] at hvf;exact (mul_ne_zero exp_ne_zero hvg) hvf.symm

theorem EMP (hint: ∀g:A,v (φ g)≤1) (g:A) (h: ¬v (φ g)<1):
    v (φ g)=1:=
  le_antisymm (hint g) (not_lt.1 h)

theorem linear_case (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g)
    (a b:A) (hb:v (φ b)<1)
    (hgen: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*a+y*b)
    (α β:A) (hα:v (φ α)=1) (hrel:φ α*φ a+φ β*φ b=0):
    v (φ b)=exp (-1):=by
  refine FRA v φ.range ?_ (range_frac φ hfrac) hsurj (φ b) hb ?_
  · rintro _ ⟨g,rfl⟩;exact hint g
  · rintro _ ⟨g,rfl⟩ hlt
    obtain ⟨s,x,y,hs,hsg⟩:=hgen g hlt
    refine ⟨φ (α*s),⟨_,rfl⟩,by rw [map_mul,v.map_mul,hα,hs,one_mul],
      φ (y*α-x*β),⟨_,rfl⟩,?_⟩
    have h1:=congrArg φ hsg
    simp only [map_mul,map_add,map_sub] at h1 ⊢
    linear_combination φ α*h1+φ x*hrel

theorem node_case (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g)
    (a b:A) (ha:v (φ a)<1)
    (hgen: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*a+y*b)
    (α β γ:A) (hγ:v (φ γ)=1) (hδ:v (φ (β^2-4*α*γ))=1)
    (hrel:φ α*φ a^2+φ β*φ a*φ b+φ γ*φ b^2=0):
    v (φ a)=exp (-1):=by
  have hγ0:φ γ ≠ 0:=by intro h;rw [h,v.map_zero] at hγ;exact zero_ne_one hγ
  have hunit: ∀g:A,v (φ g)=1→φ g ≠ 0:=by
    intro g hg h;rw [h,v.map_zero] at hg;exact zero_ne_one hg

  have ha0:φ a ≠ 0:=by
    intro ha0
    have hb0:φ b=0:=by
      rw [ha0] at hrel
      have h1:φ γ*φ b^2=0:=by linear_combination hrel
      exact pow_eq_zero_iff (n:=2) (by norm_num) |>.1 ((mul_eq_zero.1 h1).resolve_left hγ0)
    obtain ⟨f,hf,hf0⟩:=FKL v φ hint hsurj hfrac
    obtain ⟨s,x,y,hs,hsf⟩:=hgen f hf
    have h1:=congrArg φ hsf
    simp only [map_mul,map_add,ha0,hb0,mul_zero,add_zero] at h1
    exact hf0 ((mul_eq_zero.1 h1).resolve_left (hunit s hs))
  set z:L:=φ b/φ a with hz_def
  have hz:φ b=φ a*z:=by rw [hz_def,mul_div_cancel₀ _ ha0]
  have hQ:φ α+φ β*z+φ γ*z^2=0:=by
    have h1:φ a^2*(φ α+φ β*z+φ γ*z^2)=0:=by
      rw [hz] at hrel;linear_combination hrel
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 ha0)

  have hzint:v z≤1:=by
    by_contra hz1
    rw [not_le] at hz1
    have h1:φ γ*z^2= -(φ α+φ β*z):=by linear_combination hQ
    have h2:=congrArg v h1
    rw [v.map_mul,hγ,one_mul,v.map_pow,v.map_neg] at h2
    have h3:v (φ α+φ β*z)≤v z:=by
      refine (v.map_add _ _).trans (max_le ((hint α).trans hz1.le) ?_)
      rw [v.map_mul];exact mul_le_of_le_one_left' (hint β)
    have h4:v z<v z^2:=by
      rw [sq];exact lt_mul_of_one_lt_left (zero_lt_one.trans hz1) hz1
    rw [← h2] at h3
    exact absurd h3 (not_le.2 h4)

  set w:L:=2*φ γ*z+φ β with hw_def
  have hw2:w^2=φ (β^2-4*α*γ):=by
    rw [hw_def];simp only [map_sub,map_mul,map_pow,map_ofNat]
    linear_combination 4*φ γ*hQ
  have hw:v w=1:=by
    have h1:v w^2=1:=by rw [← v.map_pow,hw2,hδ]
    rcases lt_trichotomy (v w) 1 with h | h | h
    · exact absurd h1 (ne_of_lt (by rw [sq];exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h h.le))
    · exact h
    · exact absurd h1 (ne_of_gt (by rw [sq];exact one_lt_mul_of_lt_of_le h h.le))

  set S:Subring L:=(Polynomial.eval₂RingHom φ z).range with hS_def
  have hSφ: ∀g:A,φ g ∈ S:=fun g=>⟨C g,by simp⟩
  have hSz:z ∈ S:=⟨Polynomial.X,by simp⟩
  have h2S:(2:L) ∈ S:=by rw [← map_ofNat φ 2];exact hSφ 2
  have hSint: ∀h ∈ S,v h≤1:=by
    rintro _ ⟨P,rfl⟩
    rw [Polynomial.coe_eval₂RingHom]
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ' =>rw [Polynomial.eval₂_add];exact (v.map_add _ _).trans (max_le hP hQ')
    | monomial n g=>
      rw [Polynomial.eval₂_monomial,v.map_mul,v.map_pow]
      exact mul_le_one' (hint g) (pow_le_one' hzint n)

  have hpow: ∀n:ℕ,∃c₀ c₁:A,φ γ^n*z^n=φ c₀+φ c₁*z:=by
    intro n
    induction n with
    | zero=>exact ⟨1,0,by simp⟩
    | succ n ih=>
      obtain ⟨c₀,c₁,h⟩:=ih
      refine ⟨-(c₁*α),γ*c₀-c₁*β,?_⟩
      simp only [map_neg,map_mul,map_sub]
      linear_combination (φ γ*z)*h+φ c₁*hQ
  have hlin: ∀P:A[X],∃N:ℕ,∃c₀ c₁:A,
      φ γ^N*P.eval₂ φ z=φ c₀+φ c₁*z:=by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ' =>
      obtain ⟨N₁,c₀,c₁,h₁⟩:=hP
      obtain ⟨N₂,d₀,d₁,h₂⟩:=hQ'
      refine ⟨N₁+N₂,γ^N₂*c₀+γ^N₁*d₀,γ^N₂*c₁+γ^N₁*d₁,?_⟩
      simp only [Polynomial.eval₂_add,map_add,map_mul,map_pow,pow_add]
      linear_combination φ γ^N₂*h₁+φ γ^N₁*h₂
    | monomial n g=>
      obtain ⟨c₀,c₁,h⟩:=hpow n
      refine ⟨n,g*c₀,g*c₁,?_⟩
      simp only [Polynomial.eval₂_monomial,map_mul]
      linear_combination φ g*h

  have hdeg1: ∀c₀ c₁:A,v (φ c₀+φ c₁*z)<1→
      ∃u ∈ S,v u=1∧ ∃h' ∈ S,u*(φ c₀+φ c₁*z)=φ a*h' :=by
    intro c₀ c₁ he
    by_cases hc₁:v (φ c₁)<1
    · have hc₀:v (φ c₀)<1:=by
        have h1:φ c₀=(φ c₀+φ c₁*z)-φ c₁*z:=by ring
        rw [h1]
        refine (v.map_sub _ _).trans_lt (max_lt he ?_)
        rw [v.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' hzint) hc₁
      obtain ⟨s₀,x₀,y₀,hs₀,h₀⟩:=hgen c₀ hc₀
      obtain ⟨s₁,x₁,y₁,hs₁,h₁⟩:=hgen c₁ hc₁
      have h₀' :=congrArg φ h₀
      have h₁' :=congrArg φ h₁
      simp only [map_mul,map_add] at h₀' h₁'
      refine ⟨φ (s₀*s₁),hSφ _,by rw [map_mul,v.map_mul,hs₀,hs₁,one_mul],
        φ s₁*(φ x₀+φ y₀*z)+φ s₀*(φ x₁+φ y₁*z)*z,?_,?_⟩
      · exact S.add_mem (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)))
          (S.mul_mem (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz))) hSz)
      · rw [map_mul]
        linear_combination φ s₁*h₀' +φ s₀*z*h₁' +(φ s₁*φ y₀+φ s₀*φ y₁*z)*hz
    · have hc₁1:v (φ c₁)=1:=EMP v φ hint c₁ hc₁
      set e:L:=φ c₀+φ c₁*z with he_def
      set M:L:=φ c₁*w-φ γ*e with hM_def
      have hM:v M=1:=by
        rw [hM_def,Valuation.map_sub_eq_of_lt_left]
        · rw [v.map_mul,hc₁1,hw,one_mul]
        · rw [v.map_mul,v.map_mul,hγ,hc₁1,hw,one_mul,one_mul];exact he
      have hN:φ (c₁^2*α-c₁*c₀*β+c₀^2*γ)= -(e*M):=by
        rw [hM_def,he_def,hw_def];simp only [map_sub,map_add,map_mul,map_pow]
        linear_combination φ c₁^2*hQ
      have hNlt:v (φ (c₁^2*α-c₁*c₀*β+c₀^2*γ))<1:=by
        rw [hN,v.map_neg,v.map_mul,hM,mul_one];exact he
      obtain ⟨s,x,y,hs,hsN⟩:=hgen _ hNlt
      have h1:=congrArg φ hsN
      rw [map_mul,hN,map_add,map_mul,map_mul] at h1
      have hMS:M ∈ S:=by
        rw [hM_def,hw_def,he_def]
        exact S.sub_mem (S.mul_mem (hSφ _) (S.add_mem (S.mul_mem (S.mul_mem h2S (hSφ _)) hSz)
          (hSφ _))) (S.mul_mem (hSφ _) (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)))
      refine ⟨φ s*M,S.mul_mem (hSφ _) hMS,by rw [v.map_mul,hs,hM,one_mul],
        -(φ x+φ y*z),S.neg_mem (S.add_mem (hSφ _) (S.mul_mem (hSφ _) hSz)),?_⟩
      linear_combination-h1-φ y*hz

  have hloc: ∀h ∈ S,v h<1→ ∃u ∈ S,v u=1∧ ∃h' ∈ S,u*h=φ a*h' :=by
    rintro _ ⟨P,rfl⟩ hlt
    rw [Polynomial.coe_eval₂RingHom] at hlt ⊢
    obtain ⟨N,c₀,c₁,hN⟩:=hlin P
    have hvN:v (φ γ^N)=1:=by rw [v.map_pow,hγ,one_pow]
    have he:v (φ c₀+φ c₁*z)<1:=by rw [← hN,v.map_mul,hvN,one_mul];exact hlt
    obtain ⟨u,huS,hu,h',hh',hu'⟩:=hdeg1 c₀ c₁ he
    refine ⟨u*φ γ^N,S.mul_mem huS (S.pow_mem (hSφ _) _),by
      rw [v.map_mul,hu,hvN,one_mul],h',hh',?_⟩
    rw [mul_assoc,hN,hu']
  have hfracS: ∀x:L,∃f ∈ S,∃g ∈ S,g ≠ 0∧x=f/g:=by
    intro x
    obtain ⟨f,g,hg,rfl⟩:=hfrac x
    exact ⟨φ f,hSφ f,φ g,hSφ g,hg,rfl⟩
  exact FRA v S hSint hfracS hsurj (φ a) ha hloc

variable {R:Type*} [CommRing R] [Algebra R A] (D₀:Derivation R A A)

theorem deriv_triple (hint: ∀g:A,v (φ g)≤1) (e:ℤᵐ⁰) (x y z:A)
    (hx:v (φ x)≤e) (hy:v (φ y)≤e) (hz:v (φ z)≤e):
    v (φ (D₀ (x*y*z)))≤e*e:=by
  rw [Derivation.leibniz,Derivation.leibniz]
  simp only [smul_eq_mul,map_add,map_mul]
  refine (v.map_add _ _).trans (max_le ?_ ?_)
  · rw [v.map_mul,v.map_mul]
    calc v (φ x)*v (φ y)*v (φ (D₀ z))≤e*e*1:=
          mul_le_mul' (mul_le_mul' hx hy) (hint _)
      _=e*e:=mul_one _
  · rw [v.map_mul]
    refine (mul_le_mul' hz ((v.map_add _ _).trans (max_le ?_ ?_))).trans (le_of_eq (mul_comm _ _))
    · rw [v.map_mul];exact (mul_le_mul' hx (hint _)).trans (le_of_eq (mul_one _))
    · rw [v.map_mul];exact (mul_le_mul' hy (hint _)).trans (le_of_eq (mul_one _))

theorem deriv_square (hint: ∀g:A,v (φ g)≤1) (x:A):
    v (φ (D₀ (x*x)))≤v (φ x):=by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul,map_add,map_mul]
  refine (v.map_add _ _).trans (max_le ?_ ?_)<;>rw [v.map_mul]<;>
    exact mul_le_of_le_one_right' (hint _)

theorem cube_case (hint: ∀g:A,v (φ g)≤1) (F:A) (hF:φ F=0)
    (n₁:ℕ) (hn₁: ∀g:A,v (φ g)<1→v (φ g)≤exp (-(n₁:ℤ)))
    (a b:A) (ha:v (φ a)<1) (hb:v (φ b)<1)
    (s α β γ:A) (hs:v (φ s)=1) (hα:v (φ α)<1) (hβ:v (φ β)<1)
    (hγ:v (φ γ)<1) (hrep:s*F=α*a^2+β*a*b+γ*b^2):
    v (φ (D₀ F))≤exp (-(2*n₁:ℤ)):=by
  set e:ℤᵐ⁰:=exp (-(n₁:ℤ)) with he
  have hrep' :s*F=α*a*a+β*a*b+γ*b*b:=by rw [hrep];ring
  have h1:φ (D₀ (s*F))=φ s*φ (D₀ F):=by
    rw [Derivation.leibniz];simp only [smul_eq_mul,map_add,map_mul,hF,zero_mul,add_zero]
  have hbd:v (φ (D₀ (s*F)))≤e*e:=by
    rw [hrep']
    simp only [map_add]
    refine (v.map_add _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)
    · exact deriv_triple v φ D₀ hint e _ _ _ (hn₁ _ hα) (hn₁ _ ha) (hn₁ _ ha)
    · exact deriv_triple v φ D₀ hint e _ _ _ (hn₁ _ hβ) (hn₁ _ ha) (hn₁ _ hb)
    · exact deriv_triple v φ D₀ hint e _ _ _ (hn₁ _ hγ) (hn₁ _ hb) (hn₁ _ hb)
  rw [h1,v.map_mul,hs,one_mul] at hbd
  refine hbd.trans (le_of_eq ?_)
  rw [he,← exp_add];congr 1;ring

theorem cusp_case (hint: ∀g:A,v (φ g)≤1) (h2:v (2:L)=1) (F:A) (hF:φ F=0)
    (n₁:ℕ) (hn₁: ∀g:A,v (φ g)<1→v (φ g)≤exp (-(n₁:ℤ)))
    (a b:A) (hb:v (φ b)<1)
    (s α β γ:A) (hs:v (φ s)=1) (hα:v (φ α)=1)
    (hδ:v (φ (β^2-4*α*γ))<1)
    (hrep:s*F=α*a^2+β*a*b+γ*b^2):
    v (φ (D₀ F))^2≤exp (-(3*n₁:ℤ)):=by
  set e:ℤᵐ⁰:=exp (-(n₁:ℤ)) with he
  have he1:e≤1:=by rw [he,← exp_zero,exp_le_exp];omega
  set δ:A:=β^2-4*α*γ with hδ_def
  set ℓ:A:=2*α*a+β*b with hℓ_def
  have hid:(4*α*s)*F=ℓ*ℓ-δ*b*b:=by
    rw [hℓ_def,hδ_def];linear_combination (4*α)*hrep

  have hℓ:v (φ ℓ)*v (φ ℓ)≤e*e*e:=by
    have h1:=congrArg φ hid
    rw [map_mul,hF,mul_zero,map_sub,eq_comm,sub_eq_zero] at h1
    have h3:=congrArg v h1
    simp only [map_mul,v.map_mul] at h3
    rw [h3]
    exact mul_le_mul' (mul_le_mul' (hn₁ _ hδ) (hn₁ _ hb)) (hn₁ _ hb)

  have h4:φ (D₀ ((4*α*s)*F))=φ (4*α*s)*φ (D₀ F):=by
    rw [Derivation.leibniz];simp only [smul_eq_mul,map_add,map_mul,hF,zero_mul,add_zero]
  have h4' :v (4:L)=1:=by
    rw [show (4:L)=2*2 by norm_num,v.map_mul,h2,one_mul]
  have hunit:v (φ (4*α*s))=1:=by
    simp only [map_mul,map_ofNat,v.map_mul,hα,hs,h4',one_mul]
  have hbd:v (φ (D₀ F))≤max (v (φ ℓ)) (e*e):=by
    have h5:=congrArg (fun g=>v (φ (D₀ g))) hid
    rw [h4,v.map_mul,hunit,one_mul] at h5
    rw [h5,map_sub,map_sub]
    exact (v.map_sub _ _).trans (max_le_max (deriv_square v φ D₀ hint ℓ)
      (deriv_triple v φ D₀ hint e _ _ _ (hn₁ _ hδ) (hn₁ _ hb) (hn₁ _ hb)))
  have hsq:v (φ (D₀ F))^2≤e*e*e:=by
    rw [sq]
    refine (mul_le_mul' hbd hbd).trans ?_
    rcases le_total (v (φ ℓ)) (e*e) with h | h
    · rw [max_eq_right h]
      calc e*e*(e*e)≤e*e*(e*1):=mul_le_mul' le_rfl (mul_le_mul' le_rfl he1)
        _=e*e*e:=by rw [mul_one]
    · rw [max_eq_left h];exact hℓ
  refine hsq.trans (le_of_eq ?_)
  rw [he,← exp_add,← exp_add];congr 1;ring

theorem GIW (hint: ∀g:A,v (φ g)≤1) (hsurj: ∃x:L,v x=exp (-1))
    (hfrac: ∀x:L,∃f g:A,φ g ≠ 0∧x=φ f/φ g) (h2:v (2:L)=1)
    (F:A) (hF:φ F=0)
    (a b:A) (ha:v (φ a)<1) (hb:v (φ b)<1)
    (hgen: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*a+y*b)
    (n₁:ℕ) (hn₁: ∀g:A,v (φ g)<1→v (φ g)≤exp (-(n₁:ℤ))):
    n₁≤1∨v (φ (D₀ F))^2≤exp (-(3*n₁:ℤ)):=by
  have hone: ∀t:A,v (φ t)<1→v (φ t)=exp (-1)→n₁≤1:=by
    intro t ht h1
    have h3:=hn₁ t ht
    rw [h1,exp_le_exp] at h3;omega
  have hswap: ∀g:A,v (φ g)<1→ ∃s x y:A,v (φ s)=1∧s*g=x*b+y*a:=by
    intro g hg
    obtain ⟨s,x,y,h1,h3⟩:=hgen g hg
    exact ⟨s,y,x,h1,by rw [h3];ring⟩
  have hunit:=EMP v φ hint
  have hFP:v (φ F)<1:=by rw [hF,v.map_zero];exact zero_lt_one
  obtain ⟨s,α,β,hs,hsF⟩:=hgen F hFP
  have hφsF:=congrArg φ hsF
  simp only [map_mul,map_add,hF,mul_zero] at hφsF

  by_cases hα:v (φ α)<1
  swap
  · exact Or.inl (hone b hb (linear_case v φ hint hsurj hfrac a b hb hgen α β (hunit α hα)
      (by linear_combination-hφsF)))
  by_cases hβ:v (φ β)<1
  swap
  · exact Or.inl (hone a ha (linear_case v φ hint hsurj hfrac b a ha hswap β α (hunit β hβ)
      (by linear_combination-hφsF)))

  obtain ⟨s₁,α₁,α₂,hs₁,h₁⟩:=hgen α hα
  obtain ⟨s₂,β₁,β₂,hs₂,h₂⟩:=hgen β hβ
  have hrep:(s₁*s₂*s)*F=(s₂*α₁)*a^2+(s₂*α₂+s₁*β₁)*a*b+
      (s₁*β₂)*b^2:=by
    linear_combination (s₁*s₂)*hsF+s₂*a*h₁+s₁*b*h₂
  set s' :=s₁*s₂*s
  set A₂:=s₂*α₁
  set B₂:=s₂*α₂+s₁*β₁
  set C₂:=s₁*β₂
  have hs' :v (φ s')=1:=by simp only [s',map_mul,v.map_mul,hs,hs₁,hs₂,one_mul]
  have hrel:φ A₂*φ a^2+φ B₂*φ a*φ b+φ C₂*φ b^2=0:=by
    have h3:=congrArg φ hrep
    simp only [map_mul,map_add,map_pow,hF,mul_zero] at h3
    linear_combination-h3

  by_cases hall:v (φ A₂)<1∧v (φ B₂)<1∧v (φ C₂)<1
  · right
    have h3:=cube_case v φ D₀ hint F hF n₁ hn₁ a b ha hb s' A₂ B₂ C₂ hs' hall.1 hall.2.1
      hall.2.2 hrep
    rw [sq]
    refine (mul_le_mul' h3 h3).trans ?_
    rw [← exp_add,exp_le_exp];omega
  by_cases hδ:v (φ (B₂^2-4*A₂*C₂))<1
  ·
    right
    by_cases hA:v (φ A₂)<1
    · have hC: ¬v (φ C₂)<1:=by
        intro hC
        apply hall
        refine ⟨hA,?_,hC⟩
        by_contra hB
        have hB1:=hunit B₂ hB
        have h3:φ B₂^2=φ (B₂^2-4*A₂*C₂)+4*φ A₂*φ C₂:=by
          simp only [map_sub,map_mul,map_pow,map_ofNat];ring
        have h4:=congrArg v h3
        rw [v.map_pow,hB1,one_pow] at h4
        have h5:v (4*φ A₂*φ C₂)<1:=by
          rw [v.map_mul,v.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (mul_le_one' (by
            rw [show (4:L)=φ 4 from (map_ofNat φ 4).symm];exact hint 4) (hint A₂)))
            hC
        exact absurd h4 (ne_of_gt ((v.map_add _ _).trans_lt (max_lt hδ h5)))
      exact cusp_case v φ D₀ hint h2 F hF n₁ hn₁ b a ha s' C₂ B₂ A₂ hs' (hunit C₂ hC)
        (by rwa [show B₂^2-4*C₂*A₂=B₂^2-4*A₂*C₂ by ring])
        (by rw [hrep];ring)
    · exact cusp_case v φ D₀ hint h2 F hF n₁ hn₁ a b hb s' A₂ B₂ C₂ hs' (hunit A₂ hA) hδ hrep

  left
  have hδ1:=hunit _ hδ
  by_cases hC:v (φ C₂)<1
  · by_cases hA:v (φ A₂)<1
    ·
      have hB:v (φ B₂)=1:=by
        by_contra hB
        have hB' :v (φ B₂)<1:=lt_of_le_of_ne (hint B₂) hB
        exact hall ⟨hA,hB',hC⟩
      have hγ' :v (φ (A₂-B₂+C₂))=1:=by
        have h3:φ (A₂-B₂+C₂)= -φ B₂+(φ A₂+φ C₂):=by
          simp only [map_add,map_sub];ring
        rw [h3,Valuation.map_add_eq_of_lt_left,v.map_neg,hB]
        rw [v.map_neg,hB]
        exact (v.map_add _ _).trans_lt (max_lt hA hC)
      have hgen' : ∀g:A,v (φ g)<1→
          ∃s x y:A,v (φ s)=1∧s*g=x*(a+b)+y*b:=by
        intro g hg
        obtain ⟨s,x,y,h1,h3⟩:=hgen g hg
        exact ⟨s,x,y-x,h1,by rw [h3];ring⟩
      have hab:v (φ (a+b))<1:=by
        rw [map_add];exact (v.map_add _ _).trans_lt (max_lt ha hb)
      exact hone _ hab (node_case v φ hint hsurj hfrac (a+b) b hab hgen' A₂ (B₂-2*A₂)
        (A₂-B₂+C₂) hγ'
        (by rwa [show (B₂-2*A₂)^2-4*A₂*(A₂-B₂+C₂)=B₂^2-4*A₂*C₂ by ring])
        (by simp only [map_add,map_sub,map_mul,map_ofNat];linear_combination hrel))
    · exact hone b hb (node_case v φ hint hsurj hfrac b a hb hswap C₂ B₂ A₂ (hunit A₂ hA)
        (by rwa [show B₂^2-4*C₂*A₂=B₂^2-4*A₂*C₂ by ring])
        (by linear_combination hrel))
  · exact hone a ha (node_case v φ hint hsurj hfrac a b ha hgen A₂ B₂ C₂ (hunit C₂ hC) hδ1 hrel)

end Local

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open IsLocalRing

theorem CMC {A:Type*} [CommRing A] (𝔓:Ideal A) [𝔓.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime 𝔓)] (h:𝔓.height≤2):
    ∃a ∈ 𝔓,∃b ∈ 𝔓,∀g ∈ 𝔓,∃s ∉ 𝔓,∃x y:A,s*g=x*a+y*b:=by
  classical
  let Aₚ:=Localization.AtPrime 𝔓
  have hdim:ringKrullDim Aₚ=𝔓.height:=IsLocalization.AtPrime.ringKrullDim_eq_height 𝔓 Aₚ
  have hspan:((maximalIdeal Aₚ).spanFinrank:WithBot ℕ∞)=ringKrullDim Aₚ:=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hle:(maximalIdeal Aₚ).spanFinrank≤2:=by
    have h1:((maximalIdeal Aₚ).spanFinrank:WithBot ℕ∞)≤2:=by
      rw [hspan,hdim]
      exact (WithBot.coe_le_coe.2 h).trans_eq rfl
    exact_mod_cast h1
  have hfg:(maximalIdeal Aₚ).FG:=IsNoetherian.noetherian _
  obtain ⟨s,hs,hspan'⟩:=Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hpair: ∃a' b' :Aₚ,Ideal.span {a',b'}=maximalIdeal Aₚ:=by
    have hcard:s.card≤2:=hs ▸ hle
    have hcases:s.card=0∨s.card=1∨s.card=2:=by omega
    rcases hcases with hc | hc | hc
    · rw [Finset.card_eq_zero] at hc
      subst hc
      refine ⟨0,0,?_⟩
      rw [← hspan']
      simp [Ideal.span]
    · obtain ⟨x,rfl⟩:=Finset.card_eq_one.1 hc
      refine ⟨x,0,?_⟩
      rw [← hspan',Set.pair_comm,Ideal.span_insert_zero]
      simp [Ideal.span]
    · obtain ⟨x,y,-,rfl⟩:=Finset.card_eq_two.1 hc
      refine ⟨x,y,?_⟩
      rw [← hspan']
      simp [Ideal.span]
  obtain ⟨a',b',hab⟩:=hpair
  obtain ⟨a,b,d,ha',hb'⟩:=IsLocalization.surj₂ 𝔓.primeCompl Aₚ a' b'
  have hmem: ∀(z:Aₚ) (w:A),z ∈ maximalIdeal Aₚ→
      z*algebraMap A Aₚ d=algebraMap A Aₚ w→w ∈ 𝔓:=by
    intro z w hz hzw
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff Aₚ 𝔓,← hzw]
    exact Ideal.mul_mem_right _ _ hz
  have ha:a ∈ 𝔓:=hmem a' a (hab ▸ Ideal.subset_span (by simp)) ha'
  have hb:b ∈ 𝔓:=hmem b' b (hab ▸ Ideal.subset_span (by simp)) hb'
  refine ⟨a,ha,b,hb,fun g hg=> ?_⟩
  have hgm:algebraMap A Aₚ g ∈ maximalIdeal Aₚ:=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Aₚ 𝔓 g).2 hg
  rw [← hab,Ideal.mem_span_pair] at hgm
  obtain ⟨c,e,hce⟩:=hgm
  obtain ⟨c₀,e₀,t,hc,he⟩:=IsLocalization.surj₂ 𝔓.primeCompl Aₚ c e
  have key:algebraMap A Aₚ (t*d*g)=algebraMap A Aₚ (c₀*a+e₀*b):=by
    rw [map_mul,map_mul,map_add,map_mul,map_mul,← ha',← hb',← hc,← he,← hce]
    ring
  obtain ⟨u,hu⟩:=(IsLocalization.eq_iff_exists 𝔓.primeCompl Aₚ).1 key
  refine ⟨u*(t*d),𝔓.primeCompl.mul_mem u.2 (𝔓.primeCompl.mul_mem t.2 d.2),
    u*c₀,u*e₀,?_⟩
  linear_combination hu

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero MvPolynomial
open RCN313 RCN055

section Helpers

variable {K L:Type*} [Field K] [Field L] [Algebra K L] (v:Valuation L ℤᵐ⁰)

def vpole (x:L):ℤ:=max 0 (v x).log

def vzero (x:L):ℤ:=max 0 (-(v x).log)

theorem vpole_nonneg (x:L):0≤vpole v x:=le_max_left _ _

theorem vzero_nonneg (x:L):0≤vzero v x:=le_max_left _ _

omit [Field K] [Algebra K L] in
theorem AQZ (x:L):v x≤exp (vpole v x):=by
  by_cases hx:v x=0
  · rw [hx];exact zero_le
  · calc v x=exp (v x).log:=(exp_log hx).symm
      _≤exp (vpole v x):=by rw [exp_le_exp];exact le_max_right _ _

omit [Field K] [Algebra K L] in
theorem vpole_le_iff (x:L) (n:ℤ) (hn:0≤n):vpole v x≤n ↔ v x≤exp n:=by
  constructor
  · intro h
    exact (AQZ v x).trans (by rw [exp_le_exp];exact h)
  · intro h
    by_cases hx:v x=0
    · simp [vpole,hx,hn]
    · exact max_le hn ((log_le_iff_le_exp hx).2 h)

theorem CNO (D:Derivation K L L) (θ:ℤ) (hθ0:0≤θ)
    (hθ: ∀g,v (D g)≤exp θ*v g) (m:ℕ) (g:L):
    vpole v ((⇑D)^[m] g)≤vpole v g+m*θ:=by
  have hit: ∀m:ℕ,v ((⇑D)^[m] g)≤exp (m*θ)*v g:=by
    intro m
    induction m with
    | zero=>simp
    | succ m ih=>
      rw [Function.iterate_succ_apply']
      refine (hθ _).trans ?_
      refine (mul_le_mul_right ih _).trans ?_
      rw [← mul_assoc,← exp_add];push_cast;ring_nf;exact le_rfl
  exact GTL v (m*θ) (mul_nonneg (by positivity) hθ0) g _ (hit m)

theorem GEX (D:Derivation K L L) (hD: ∀u,v u≤1→v (D u)≤1)
    (m:ℕ) (g:L) (hg:v g≤1):v ((⇑D)^[m] g)≤1:=by
  induction m with
  | zero=>simpa using hg
  | succ m ih=>rw [Function.iterate_succ_apply'];exact hD _ ih

end Helpers

section Slice

variable {K:Type} [Field K] (F F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]
  (hdvd:F₀ ∣ F)
set_option linter.unusedSectionVars false

noncomputable def sliceCoord (j:Fin 3):SliceField F₀:=sliceProj F₀ (MvPolynomial.X j.succ)

noncomputable def sliceSigma:SliceField F₀:=sliceProj F₀ (polyG K F)/sliceProj F₀ (polyH K F)

theorem sliceProj_C (a:K):sliceProj F₀ (C a)=algebraMap K (SliceField F₀) a:=by
  rw [IsScalarTower.algebraMap_apply K (SliceRing F₀) (SliceField F₀)]
  rfl

theorem ATS (hH:sliceProj F₀ (polyH K F) ≠ 0):
    JJ F F₀ hdvd (sliceCoord F₀ 0)=sliceCoord F₀ 1:=by
  rw [sliceCoord,ARA F F₀ hdvd hH]
  simp [sliceCoord,pderiv_X]

theorem CGT (hH:sliceProj F₀ (polyH K F) ≠ 0):
    JJ F F₀ hdvd (sliceCoord F₀ 1)=sliceSigma F F₀:=by
  rw [sliceCoord,ARA F F₀ hdvd hH]
  simp [sliceSigma,pderiv_X]

theorem ATX (hH:sliceProj F₀ (polyH K F) ≠ 0):
    JJ F F₀ hdvd (sliceCoord F₀ 2)=0:=by
  rw [sliceCoord,ARA F F₀ hdvd hH]
  simp [pderiv_X]

include hdvd in
theorem FKE: ∃F₁:MvPolynomial (Fin 4) K,
    sliceProj F₀ (polyH K F)=sliceProj F₀ F₁*sliceProj F₀ (pderiv 2 F₀):=by
  obtain ⟨F₁,rfl⟩:=hdvd
  refine ⟨F₁,?_⟩
  have h0:sliceProj F₀ F₀=0:=(BMJ F₀ F₀).2 dvd_rfl
  rw [polyH,Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,h0,
    zero_mul,zero_add]

theorem DMP (hH:sliceProj F₀ (polyH K F) ≠ 0):
    JJ F F₀ hdvd (sliceProj F₀ (MvPolynomial.X 0))=1:=by
  rw [ARA F F₀ hdvd hH]
  simp [pderiv_X]

noncomputable def sliceLinearL (q:Fin 3→Polynomial K):SliceField F₀:=
  ∑ m,Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) (q m)*sliceCoord F₀ m

variable (v:Valuation (SliceField F₀) ℤᵐ⁰)

theorem DHW (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1) (p:Polynomial K):
    v (Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) p)≤1:=by
  haveI:v.IsTrivialOn K:=⟨hK⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>rw [map_add];exact (v.map_add _ _).trans (max_le hp hq)
  | monomial n a=>
    rw [Polynomial.aeval_monomial,v.map_mul,v.map_pow]
    exact mul_le_one' (Valuation.IsTrivialOn.valuation_algebraMap_le_one v a) (pow_le_one' hX0 n)

noncomputable def placeP:ℤ:=
  max (vpole v (sliceCoord F₀ 1)) (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))

noncomputable def placeT:ℤ:=
  max (2*placeP F₀ v)
    (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))+vpole v (sliceSigma F F₀))

noncomputable def placeH:ℤ:=vzero v (sliceProj F₀ (polyH K F))

theorem place_hint (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1) (hP0:placeP F₀ v=0):
    ∀g:MvPolynomial (Fin 4) K,v (sliceProj F₀ g)≤1:=by
  haveI:v.IsTrivialOn K:=⟨hK⟩
  have hcint: ∀j:Fin 3,v (sliceCoord F₀ j)≤1:=by
    intro j
    have hj:vpole v (sliceCoord F₀ j)≤0:=by
      have h1:=le_max_left (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))
      have h2:=le_max_right (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2)))
      have h3:=le_max_left (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))
      have h4:=le_max_right (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))
      have hP:placeP F₀ v=max (vpole v (sliceCoord F₀ 1))
        (max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))):=rfl
      fin_cases j
      · show vpole v (sliceCoord F₀ 0)≤0;omega
      · show vpole v (sliceCoord F₀ 1)≤0;omega
      · show vpole v (sliceCoord F₀ 2)≤0;omega
    have:=(vpole_le_iff v _ 0 le_rfl).1 hj
    rwa [exp_zero] at this
  intro g
  induction g using MvPolynomial.induction_on with
  | C a=>
    rw [sliceProj_C]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v a
  | add p q hp hq=>rw [map_add];exact (v.map_add _ _).trans (max_le hp hq)
  | mul_X p i hp=>
    rw [map_mul,v.map_mul]
    refine mul_le_one' hp ?_
    fin_cases i
    · exact hX0
    · exact hcint 0
    · exact hcint 1
    · exact hcint 2

theorem DMT (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1) (q:Fin 3→Polynomial K):
    v (JJ F F₀ hdvd (sliceLinearL F₀ q))≤
      max (exp (placeP F₀ v)) (v (sliceSigma F F₀)):=by
  set x0:=sliceProj F₀ (MvPolynomial.X 0)
  have hcoord: ∀j,v (sliceCoord F₀ j)≤exp (placeP F₀ v):=by
    intro j
    refine (AQZ v _).trans ?_
    rw [exp_le_exp,placeP]
    fin_cases j
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_right _ _)
  have hDa: ∀p:Polynomial K,JJ F F₀ hdvd (Polynomial.aeval x0 p)=
      Polynomial.aeval x0 (Polynomial.derivative p):=by
    intro p
    rw [Derivation.map_aeval,DMP F F₀ hdvd hH,smul_eq_mul,mul_one]
  rw [sliceLinearL,map_sum]
  refine v.map_sum_le fun m _=> ?_
  rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,hDa]
  refine (v.map_add _ _).trans (max_le ?_ ?_)
  · rw [v.map_mul]
    refine (mul_le_of_le_one_left' (DHW F₀ v hK hX0 _)).trans ?_
    fin_cases m
    · show v (JJ F F₀ hdvd (sliceCoord F₀ 0))≤_
      rw [ATS F F₀ hdvd hH];exact le_max_of_le_left (hcoord 1)
    · show v (JJ F F₀ hdvd (sliceCoord F₀ 1))≤_
      rw [CGT F F₀ hdvd hH];exact le_max_right _ _
    · show v (JJ F F₀ hdvd (sliceCoord F₀ 2))≤_
      rw [ATX F F₀ hdvd hH,v.map_zero];exact zero_le
  · rw [v.map_mul]
    exact (mul_le_of_le_one_right' (DHW F₀ v hK hX0 _)).trans
      (le_max_of_le_left (hcoord m))

theorem place_bound (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm: ∃x,v x=exp (-1))
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1)
    (ℓ:SliceField F₀)
    (hℓ:v (JJ F F₀ hdvd ℓ)≤max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (C:ℤ) (hcrude:CrudeBound v (JJ F F₀ hdvd) C)
    (hsep:NO v (JJ F F₀ hdvd)
      (exp (vpole v (JJ F F₀ hdvd ℓ))))
    (h2:(2:K) ≠ 0)
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0)
    (hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b)
    (m:ℕ):
    3*vpole v ((⇑(JJ F F₀ hdvd))^[m] (sliceCoord F₀ 1))≤
      m*(4*placeT F F₀ v+2*placeH F F₀ v)+3*placeP F₀ v:=by
  classical
  haveI:v.IsTrivialOn K:=⟨hK⟩
  set Dd:=JJ F F₀ hdvd with hDd
  set P:=placeP F₀ v with hPdef
  set T:=placeT F F₀ v with hTdef
  set h:=placeH F F₀ v with hhdef
  set pσ:=vpole v (sliceSigma F F₀) with hpσdef
  set s:=vpole v (Dd ℓ) with hsdef
  set p0:=vpole v (sliceCoord F₀ 0)
  set p1:=vpole v (sliceCoord F₀ 1)
  set p2:=vpole v (sliceCoord F₀ 2)
  have hp0:0≤p0:=vpole_nonneg _ _
  have hp1:0≤p1:=vpole_nonneg _ _
  have hp2:0≤p2:=vpole_nonneg _ _
  have hPeq:P=max p1 (max p0 p2):=rfl
  have hTeq:T=max (2*P) (max p0 p2+pσ):=rfl
  have hP0:0≤P:=by rw [hPeq];exact le_max_of_le_left hp1
  have hh0:0≤h:=vzero_nonneg _ _
  have hpσ0:0≤pσ:=vpole_nonneg _ _
  have hs0:0≤s:=vpole_nonneg _ _
  have hTP:2*P≤T:=by rw [hTeq];exact le_max_left _ _
  have hTσ:pσ≤T:=by
    rw [hTeq];exact le_max_of_le_right (by have:=le_max_left p0 p2;omega)
  have hsP:s≤max P pσ:=by
    rw [hsdef,vpole_le_iff _ _ _ (le_max_of_le_left hP0)]
    refine hℓ.trans (max_le ?_ ?_)
    · rw [exp_le_exp];exact le_max_left _ _
    · exact (AQZ v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
  obtain ⟨π₀,hπ₀⟩:=hnorm
  have hmθ: ∀θ:ℤ,0≤θ→3*θ≤4*T+2*h→
      3*((m:ℤ)*θ)≤m*(4*T+2*h):=by
    intro θ _ hθ
    have:=mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α:=ℤ) m)
    linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  ·
    have hPz' :P=0:=hPz.symm
    have hq0:p0=0:=by have:=le_max_left p0 p2;have:=le_max_right p1 (max p0 p2);omega
    have hq1:p1=0:=by have:=le_max_left p1 (max p0 p2);omega
    have hq2:p2=0:=by have:=le_max_right p0 p2;have:=le_max_right p1 (max p0 p2);omega
    have hcint: ∀j:Fin 3,v (sliceCoord F₀ j)≤1:=by
      intro j
      have hj:vpole v (sliceCoord F₀ j)≤0:=by
        fin_cases j
        · exact hq0.le
        · exact hq1.le
        · exact hq2.le
      have:=(vpole_le_iff v _ 0 le_rfl).1 hj
      rwa [exp_zero] at this
    have hint_all: ∀g:MvPolynomial (Fin 4) K,v (sliceProj F₀ g)≤1:=by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a=>
        rw [sliceProj_C]
        exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v a
      | add p q hp hq=>rw [map_add];exact (v.map_add _ _).trans (max_le hp hq)
      | mul_X p i hp=>
        rw [map_mul,v.map_mul]
        refine mul_le_one' hp ?_
        fin_cases i
        · exact hX0
        · exact hcint 0
        · exact hcint 1
        · exact hcint 2
    have hfrac: ∀x:SliceField F₀,∃f g:MvPolynomial (Fin 4) K,
        sliceProj F₀ g ≠ 0∧x=sliceProj F₀ f/sliceProj F₀ g:=by
      intro x
      obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=SliceRing F₀) x
      obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective a
      obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective b
      refine ⟨f,g,?_,rfl⟩
      exact (map_ne_zero_iff _ (IsFractionRing.injective (SliceRing F₀) (SliceField F₀))).2
        (nonZeroDivisors.ne_zero hb)
    have h2v:v (2:SliceField F₀)=1:=by
      rw [← map_ofNat (algebraMap K (SliceField F₀)) 2]
      exact hK 2 h2
    have hFz:sliceProj F₀ F₀=0:=(BMJ F₀ F₀).2 dvd_rfl
    obtain ⟨a,b,ha,hb,hgen'⟩:=hgen hPz'

    obtain ⟨g₀,hg₀,hg₀0⟩:=FKL v (sliceProj F₀) hint_all ⟨π₀,hπ₀⟩ hfrac
    have hex: ∃n:ℕ,0<n∧ ∃g,v (sliceProj F₀ g)=exp (-(n:ℤ)):=by
      have hne:v (sliceProj F₀ g₀) ≠ 0:=(Valuation.ne_zero_iff v).2 hg₀0
      have hl:(v (sliceProj F₀ g₀)).log<0:=by
        rw [log_lt_iff_lt_exp hne,exp_zero];exact hg₀
      exact ⟨(-(v (sliceProj F₀ g₀)).log).toNat,by omega,g₀,
        (exp_log hne).symm.trans (by congr 1;omega)⟩
    set n₁:=Nat.find hex with hn₁def
    obtain ⟨hn₁pos,f₀,hf₀⟩:=Nat.find_spec hex
    have hn₁: ∀g,v (sliceProj F₀ g)<1→v (sliceProj F₀ g)≤exp (-(n₁:ℤ)):=by
      intro g hg
      by_cases hz:v (sliceProj F₀ g)=0
      · rw [hz];exact zero_le
      have hl:(v (sliceProj F₀ g)).log<0:=by
        rw [log_lt_iff_lt_exp hz,exp_zero];exact hg
      have hmin:=Nat.find_min' hex (m:=(-(v (sliceProj F₀ g)).log).toNat)
        ⟨by omega,g,(exp_log hz).symm.trans (by congr 1;omega)⟩
      rw [← exp_log hz,exp_le_exp]
      omega
    have hdich:=GIW v (sliceProj F₀) (MvPolynomial.pderiv (2:Fin 4)) hint_all
      ⟨π₀,hπ₀⟩ hfrac h2v F₀ hFz a b ha hb hgen' n₁ hn₁
    obtain ⟨F₁,hHF⟩:=FKE F F₀ hdvd
    have hHne:v (sliceProj F₀ (polyH K F)) ≠ 0:=(Valuation.ne_zero_iff v).2 hH
    have hdich' :n₁≤1∨3*(n₁:ℤ)≤2*h:=by
      rcases hdich with h1 | h1
      · exact Or.inl h1
      right
      have hle:v (sliceProj F₀ (polyH K F))≤v (sliceProj F₀ (pderiv 2 F₀)):=by
        rw [hHF,v.map_mul];exact mul_le_of_le_one_left' (hint_all F₁)
      have h2' :v (sliceProj F₀ (polyH K F))^2≤exp (-(3*n₁:ℤ)):=
        (pow_le_pow_left₀ zero_le hle 2).trans h1
      rw [← exp_log hHne,← exp_nsmul,exp_le_exp] at h2'
      have:h=max 0 (-(v (sliceProj F₀ (polyH K F))).log):=rfl
      simp only [nsmul_eq_mul] at h2'
      push_cast at h2'
      omega
    have hn₁K:(n₁:K) ≠ 0:=by
      rcases hdich' with h1 | h1
      · have:n₁=1:=by omega
        rw [this,Nat.cast_one];exact one_ne_zero
      · exact hchar n₁ hn₁pos (by rw [hPz'];omega)

    have hTa:T=pσ:=by rw [hTeq,hPz',hq0,hq2];omega
    have hsσ:s≤pσ:=by have:=hsP;rw [hPz'] at this;omega
    have hDf:v (Dd (sliceProj F₀ f₀))≤exp pσ:=by
      rw [hDd,ARA F F₀ hdvd hH]
      refine (v.map_add _ _).trans (max_le ?_ ?_)
      · exact (hint_all _).trans (by rw [← exp_zero,exp_le_exp];exact hpσ0)
      · rw [v.map_mul]
        refine (mul_le_of_le_one_left' (hint_all _)).trans ?_
        exact AQZ v _
    have hθ:=ECM v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceProj F₀ f₀) n₁ hn₁K
      hf₀ pσ hDf
    have hmax:max s (pσ+n₁)=pσ+n₁:=max_eq_right (by omega)
    rw [hmax] at hθ
    by_cases hA:pσ=0∧n₁=1
    ·
      have hπ:=EYP v Dd π₀ hπ₀ s pσ
        (EAH v Dd π₀ hπ₀ s hs0 C hcrude hsep) (sliceProj F₀ f₀) n₁ hn₁K hf₀ hDf
      have hs00:s=0:=by omega
      have hmx:max s (pσ+n₁)-1=0:=by rw [hmax];omega
      rw [hmx,exp_zero] at hπ
      have hD1: ∀u,v u≤1→v (Dd u)≤1:=by
        intro u hu
        refine (EAH v Dd π₀ hπ₀ s hs0 C hcrude hsep u hu).trans (max_le ?_ hπ)
        rw [hs00,exp_zero]
      have hit:=GEX v Dd hD1 m _ (hcint 1)
      have hz:vpole v ((⇑Dd)^[m] (sliceCoord F₀ 1))≤0:=
        (vpole_le_iff v _ 0 le_rfl).2 (by rwa [exp_zero])
      have:=vpole_nonneg v ((⇑Dd)^[m] (sliceCoord F₀ 1))
      have:0≤(m:ℤ)*(4*T+2*h):=
        mul_nonneg (Nat.cast_nonneg m) (by omega)
      omega
    ·
      have hσh:pσ≤h:=by
        rw [hpσdef,vpole_le_iff _ _ _ hh0,sliceSigma,map_div₀]
        by_cases hG0:v (sliceProj F₀ (polyG K F))=0
        · rw [hG0,zero_div];exact zero_le
        · rw [div_le_iff₀ (zero_lt_iff.2 hHne)]
          calc v (sliceProj F₀ (polyG K F))≤1:=hint_all _
            _≤exp h*v (sliceProj F₀ (polyH K F)):=by
              rw [← exp_log hHne,← exp_add,← exp_zero,exp_le_exp]
              have:h=max 0 (-(v (sliceProj F₀ (polyH K F))).log):=rfl
              omega
      have hlaw:3*(pσ+n₁)≤4*T+2*h:=by
        rw [hTa]
        rcases hdich' with h1 | h1
        · have:n₁=1:=by omega
          have:pσ ≠ 0:=fun h0=>hA ⟨h0,by omega⟩
          omega
        · omega
      have hit:=CNO v Dd (pσ+n₁) (by omega) hθ m (sliceCoord F₀ 1)
      have:=hmθ (pσ+n₁) (by omega) hlaw
      have hc1:vpole v (sliceCoord F₀ 1)=0:=hq1
      rw [hc1,zero_add] at hit
      rw [hPz']
      omega
  ·
    obtain ⟨j,hj⟩: ∃j:Fin 3,vpole v (sliceCoord F₀ j)=P:=by
      rcases max_choice p1 (max p0 p2) with h1 | h1
      · exact ⟨1,by rw [hPeq,h1]⟩
      · rcases max_choice p0 p2 with h2 | h2
        · exact ⟨0,by rw [hPeq,h1,h2]⟩
        · exact ⟨2,by rw [hPeq,h1,h2]⟩
    have hcj0:v (sliceCoord F₀ j) ≠ 0:=by
      intro h0
      have:vpole v (sliceCoord F₀ j)=0:=by simp [vpole,h0]
      omega
    have hcj:v (sliceCoord F₀ j)=exp ((P.toNat:ℕ):ℤ):=by
      rw [← exp_log hcj0]
      congr 1
      have:vpole v (sliceCoord F₀ j)=max 0 (v (sliceCoord F₀ j)).log:=rfl
      omega
    have hPK:((P.toNat:ℕ):K) ≠ 0:=
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hP0];exact le_max_left _ _)
    have hQ:v (Dd (sliceCoord F₀ j))≤exp (max P pσ):=by
      fin_cases j
      · show v (Dd (sliceCoord F₀ 0))≤_
        rw [hDd,ATS F F₀ hdvd hH]
        exact (AQZ v _).trans (by
          rw [exp_le_exp];have:=le_max_left p1 (max p0 p2);exact le_max_of_le_left (by omega))
      · show v (Dd (sliceCoord F₀ 1))≤_
        rw [hDd,CGT F F₀ hdvd hH]
        exact (AQZ v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
      · show v (Dd (sliceCoord F₀ 2))≤_
        rw [hDd,ATX F F₀ hdvd hH,v.map_zero];exact zero_le
    have hθ:=GSO v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat hPK
      hcj (max P pσ) hQ
    set θ:=max s (max 0 (max P pσ-2*((P.toNat:ℕ):ℤ))+((P.toNat:ℕ):ℤ)) with hθdef
    have hPn:((P.toNat:ℕ):ℤ)=P:=Int.toNat_of_nonneg hP0
    have hθT:θ≤T:=by
      rw [hθdef,hPn]
      refine max_le (hsP.trans (max_le (by omega) hTσ)) ?_
      rcases le_total P pσ with h1 | h1
      · rw [max_eq_right h1];omega
      · rw [max_eq_left h1];omega
    have hθ0:0≤θ:=le_max_of_le_left hs0
    have hit:=CNO v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1:vpole v (sliceCoord F₀ 1)≤P:=by rw [hPeq];exact le_max_left _ _
    have h1:(m:ℤ)*θ≤m*T:=mul_le_mul_of_nonneg_left hθT (Nat.cast_nonneg m)
    have h3:0≤(m:ℤ)*T:=mul_nonneg (Nat.cast_nonneg m) (by omega)
    have h4:0≤(m:ℤ)*h:=mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith

end Slice

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero

variable {L:Type*} [Field L]

theorem DZW (w:Valuation L ℤᵐ⁰) (hnt: ∃x:L,w x ≠ 0∧w x ≠ 1):
    ∃(e:ℕ) (v:Valuation L ℤᵐ⁰),1≤e∧(∃x,v x=exp (-1))∧
      ∀x,w x=v x^e:=by
  classical
  have hex: ∃n:ℕ,0<n∧ ∃x,w x=exp (-(n:ℤ)):=by
    obtain ⟨x,hx0,hx1⟩:=hnt
    have hm:w x=exp (w x).log:=(exp_log hx0).symm
    have hm0:(w x).log ≠ 0:=by intro h;rw [h,exp_zero] at hm;exact hx1 hm
    rcases lt_or_gt_of_ne hm0 with h | h
    · exact ⟨(-(w x).log).toNat,by omega,x,hm.trans (by congr 1;omega)⟩
    · refine ⟨((w x).log).toNat,by omega,x⁻¹,?_⟩
      calc w x⁻¹=(w x)⁻¹:=map_inv₀ _ _
        _=(exp (w x).log)⁻¹:=by rw [exp_log hx0]
        _=exp (-(((w x).log).toNat:ℤ)):=by rw [← exp_neg];congr 1;omega
  set e:=Nat.find hex with he_def
  have he:0<e∧ ∃x,w x=exp (-(e:ℤ)):=Nat.find_spec hex
  obtain ⟨u,hu⟩:=he.2
  have hu0:u ≠ 0:=by intro h;rw [h,map_zero] at hu;exact exp_ne_zero hu.symm
  have hdvd: ∀x,w x ≠ 0→(e:ℤ) ∣ (w x).log:=by
    intro x hx
    have hy:w (x*u^((w x).log/e))=exp ((w x).log%e):=by
      rw [map_mul,map_zpow₀,hu,← exp_zsmul,← exp_log hx,← exp_add,log_exp]
      congr 1;rw [Int.emod_def];simp only [smul_eq_mul];ring
    by_contra hnd
    have hr0:0≤(w x).log%e:=Int.emod_nonneg _ (by omega)
    have hr1:(w x).log%e ≠ 0:=fun h=>hnd (Int.dvd_of_emod_eq_zero h)
    have hr2:(w x).log%e<e:=Int.emod_lt_of_pos _ (by omega)
    apply Nat.find_min hex (m:=((w x).log%e).toNat) (by omega)
    refine ⟨by omega,(x*u^((w x).log/e))⁻¹,?_⟩
    rw [map_inv₀,hy,← exp_neg];congr 1;omega
  let v:Valuation L ℤᵐ⁰:=
    {
      toFun:=fun x=>if w x=0 then 0 else exp ((w x).log/e)
      map_zero' :=by simp
      map_one' :=by simp
      map_mul' :=by
        intro x y
        by_cases hx:w x=0
        · simp [hx]
        by_cases hy:w y=0
        · simp [hy]
        have hxy:w (x*y) ≠ 0:=by rw [map_mul];exact mul_ne_zero hx hy
        show (if w (x*y)=0 then 0 else exp ((w (x*y)).log/e))=
          (if w x=0 then 0 else exp ((w x).log/e))*
            (if w y=0 then 0 else exp ((w y).log/e))
        rw [if_neg hxy,if_neg hx,if_neg hy,map_mul,log_mul hx hy,
          Int.add_ediv_of_dvd_left (hdvd x hx),exp_add]
      map_add_le_max' :=by
        intro x y
        by_cases hxy:w (x+y)=0
        · simp [hxy]
        have hle:=w.map_add x y
        have key: ∀z,w (x+y)≤w z→
            (if w (x+y)=0 then 0 else exp ((w (x+y)).log/e))≤
              (if w z=0 then 0 else exp ((w z).log/e)):=by
          intro z hz
          have hz0:w z ≠ 0:=by
            intro h;rw [h] at hz;exact hxy (le_antisymm hz zero_le)
          simp only [hxy,hz0,if_false,exp_le_exp]
          exact Int.ediv_le_ediv (by omega) ((log_le_log hxy hz0).2 hz)
        show (if w (x+y)=0 then 0 else exp ((w (x+y)).log/e))≤
          max (if w x=0 then 0 else exp ((w x).log/e))
            (if w y=0 then 0 else exp ((w y).log/e))
        rcases le_total (w x) (w y) with h | h
        · exact (key y (hle.trans (max_eq_right h).le)).trans (le_max_right _ _)
        · exact (key x (hle.trans (max_eq_left h).le)).trans (le_max_left _ _)}
  have hv: ∀x,v x=if w x=0 then 0 else exp ((w x).log/e):=fun _=>rfl
  refine ⟨e,v,he.1,⟨u,?_⟩,fun x=> ?_⟩
  · rw [hv,if_neg (by rw [hu];exact exp_ne_zero),hu,log_exp]
    congr 1
    rw [Int.neg_ediv_of_dvd (dvd_refl _),Int.ediv_self (by omega)]
  · rw [hv]
    by_cases hx:w x=0
    · rw [if_pos hx,hx,zero_pow (by omega)]
    · rw [if_neg hx,← exp_nsmul,nsmul_eq_mul,Int.mul_ediv_cancel' (hdvd x hx),exp_log hx]

theorem FXJ (v w:Valuation L ℤᵐ⁰) (e:ℕ) (hw: ∀x,w x=v x^e) (x:L):
    max 0 (w x).log=e*max 0 (v x).log:=by
  rw [hw,log_pow,nsmul_eq_mul,mul_max_of_nonneg _ _ (by positivity),mul_zero]

theorem FSG (v w:Valuation L ℤᵐ⁰) (e:ℕ) (hw: ∀x,w x=v x^e) (x:L):
    max 0 (-(w x).log)=e*max 0 (-(v x).log):=by
  rw [hw,log_pow,nsmul_eq_mul,mul_max_of_nonneg _ _ (by positivity),mul_zero,mul_neg]

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section Centre

variable {Ω R:Type*} [Field Ω] [IsAlgClosed Ω] [Field R] [Algebra Ω R]

theorem DZO (ν:Valuation R ℤᵐ⁰) (y:Fin 3→R)
    (𝔮:Ideal (MvPolynomial (Fin 3) Ω)) [𝔮.IsPrime]
    (h𝔮: ∀P,P ∈ 𝔮 ↔ ν (aeval y P)<1)
    (c:Fin 3→Ω) (hcω: ∀a:Ω,a ≠ 0→ν (algebraMap Ω R a)=1)
    (hℓ: ∀a:Fin 3→Ω,ν (∑ m,algebraMap Ω R (c m)*y m-algebraMap Ω R (∑ m,c m*a m))=1):
    𝔮.height≤2:=by
  classical
  have hnotmax: ¬𝔮.IsMaximal:=by
    intro hmax
    obtain ⟨a,ha⟩:=(MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (I:=𝔮)).1 hmax
    have hsmall: ∀j,ν (y j-algebraMap Ω R (a j))<1:=by
      intro j
      have hmem:(MvPolynomial.X j-MvPolynomial.C (a j):MvPolynomial (Fin 3) Ω) ∈ 𝔮:=by
        rw [ha,MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp
      have:=(h𝔮 _).1 hmem
      simpa using this
    have hsum: ∑ m,algebraMap Ω R (c m)*y m-algebraMap Ω R (∑ m,c m*a m)=
        ∑ m,algebraMap Ω R (c m)*(y m-algebraMap Ω R (a m)):=by
      simp only [map_sum,map_mul,mul_sub,Finset.sum_sub_distrib]
    have hlt:ν (∑ m,algebraMap Ω R (c m)*y m-algebraMap Ω R (∑ m,c m*a m))<1:=by
      rw [hsum]
      refine ν.map_sum_lt one_ne_zero fun m _=> ?_
      rw [ν.map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) (hsmall m)
      rcases eq_or_ne (c m) 0 with hc | hc
      · rw [hc,map_zero,ν.map_zero];exact zero_le
      · exact (hcω _ hc).le
    exact absurd (hℓ a) (ne_of_lt hlt)
  obtain ⟨𝔪,h𝔪max,h𝔮𝔪⟩:=Ideal.exists_le_maximal 𝔮 Ideal.IsPrime.ne_top'
  have hlt:𝔮<𝔪:=lt_of_le_of_ne h𝔮𝔪 (fun h=>hnotmax (h ▸ h𝔪max))
  have h1:=Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2:(𝔪.height:WithBot ℕ∞)≤3:=by
    refine (Ideal.height_le_ringKrullDim_of_isPrime (I:=𝔪)).trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,ringKrullDim_eq_zero_of_field,zero_add,
      ENat.card_eq_coe_fintype_card,Fintype.card_fin]
    rfl
  have h3:𝔪.height≤3:=WithBot.coe_le_coe.mp h2
  have h4:𝔮.height+1≤3:=h1.trans h3
  have hne:𝔮.height ≠ ⊤ :=by
    intro htop;rw [htop] at h4;exact absurd h4 (by decide)
  lift 𝔮.height to ℕ using hne with n hn
  have:n+1≤3:=by exact_mod_cast h4
  exact_mod_cast (show n≤2 by omega)

end Centre

section ValCentre

variable {R L:Type*} [CommRing R] [Field L]

def valCentre (f:R→+*L) (ν:Valuation L ℤᵐ⁰) (hint: ∀r,ν (f r)≤1):Ideal R where
  carrier:={r | ν (f r)<1}
  add_mem' :=by
    intro a b ha hb
    simp only [Set.mem_setOf_eq,map_add] at ha hb ⊢
    exact (ν.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' :=by simp
  smul_mem' :=by
    intro c x hx
    simp only [Set.mem_setOf_eq,smul_eq_mul,map_mul,ν.map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx

theorem BYN (f:R→+*L) (ν:Valuation L ℤᵐ⁰) (hint: ∀r,ν (f r)≤1) (r:R):
    r ∈ valCentre f ν hint ↔ ν (f r)<1:=Iff.rfl

instance valCentre_isPrime (f:R→+*L) (ν:Valuation L ℤᵐ⁰) (hint: ∀r,ν (f r)≤1):
    (valCentre f ν hint).IsPrime:=by
  refine ⟨?_,?_⟩
  · intro htop
    have h1:(1:R) ∈ valCentre f ν hint:=htop ▸ Submodule.mem_top
    rw [BYN,map_one,ν.map_one] at h1
    exact lt_irrefl _ h1
  · intro a b hab
    rw [BYN,map_mul,ν.map_mul] at hab
    by_contra h
    rw [not_or] at h
    have ha:ν (f a)=1:=le_antisymm (hint a) (not_lt.1 fun h' =>h.1 h')
    have hb:ν (f b)=1:=le_antisymm (hint b) (not_lt.1 fun h' =>h.2 h')
    rw [ha,hb,one_mul] at hab
    exact lt_irrefl _ hab

theorem DVA {x:ℤᵐ⁰} {e:ℕ} (he:e ≠ 0):x^e≤1 ↔ x≤1:=by
  constructor
  · intro h;by_contra hx;exact absurd h (not_le.2 (one_lt_pow' (not_le.1 hx) he))
  · intro h;exact pow_le_one' h e

theorem DTJ {x:ℤᵐ⁰} {e:ℕ} (he:e ≠ 0):x^e<1 ↔ x<1:=by
  constructor
  · intro h;by_contra hx;exact absurd h (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hx) e))
  · intro h;exact pow_lt_one' h he

end ValCentre

section Budget

variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

local notation "w" =>RCN326.w

noncomputable abbrev phiE (K E:Type) [Field K] [Field E] [Algebra (GenericField K) E]:
    Polynomial K→+*E:=
  (algebraMap (GenericField K) E).comp (AL K)

section Images

variable (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀:MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_coord (j:Fin 3):
    RY D F₀ hker (sliceCoord F₀ j)=coordinate E D j:=by
  rw [sliceCoord,SR,sliceMap,RingHom.comp_apply,AMP]
  rfl

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_const (a:K):
    RY D F₀ hker (algebraMap K (SliceField F₀) a)=
      algebraMap E (AJ E D) (phiE K E (Polynomial.C a)):=by
  rw [← sliceProj_C,SR,sliceMap,RingHom.comp_apply,surfaceMap_C]
  exact (BR E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_X0:
    RY D F₀ hker (sliceProj F₀ (MvPolynomial.X 0))=
      algebraMap E (AJ E D) (phiE K E Polynomial.X):=by
  rw [SR,sliceMap,RingHom.comp_apply,CSU]
  exact (BR E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_sigma (F:MvPolynomial (Fin 4) K):
    RY D F₀ hker (sliceSigma F F₀)=
      RCN064.movingRatio D (surfaceMap (phiE K E) (polyH K F))
        (surfaceMap (phiE K E) (polyG K F)):=by
  rw [sliceSigma,map_div₀,SR,SR]
  rfl

end Images

theorem scale_target (e:ℤ) (he:0≤e) (a b c d:ℤ):
    max (2*max (e*a) (max (e*b) (e*c))) (max (e*b) (e*c)+e*d)=
      e*max (2*max a (max b c)) (max b c+d):=by
  rw [mul_max_of_nonneg _ _ he,mul_add,mul_left_comm e 2,mul_max_of_nonneg _ _ he,
    mul_max_of_nonneg _ _ he]

theorem scale_flag (e:ℤ) (he:0≤e) (a b c:ℤ):
    max (e*a) (max (e*b) (e*c))=e*max a (max b c):=by
  rw [mul_max_of_nonneg _ _ he,mul_max_of_nonneg _ _ he]





end Budget

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section Signed

variable {K L:Type*} [Field K] [Field L] [Algebra K L]
variable (v:Valuation L ℤᵐ⁰) (D:Derivation K L L)

theorem FCO [v.IsTrivialOn K] (π:L) (hπ:v π=exp (-1)) (s:ℤ)
    (hs:0≤s) (C:ℤ) (hcont:CrudeBound v D C) (hsep:NO v D (exp s))
    (c:L) (P:ℕ) (hP:(P:K) ≠ 0) (hc:v c=exp (P:ℤ)) (Q:ℤ)
    (hQ:v (D c)≤exp Q):
    ∀g:L,v (D g)≤exp (max s (Q-P))*v g:=by
  have hc0:c ≠ 0:=by intro h;rw [h,v.map_zero] at hc;exact exp_ne_zero hc.symm
  have hu:v c⁻¹=exp (-(P:ℤ)):=by rw [map_inv₀,hc,exp_neg]
  have hDu:v (D c⁻¹)≤exp (Q-2*P):=by
    rw [Derivation.leibniz_inv,smul_eq_mul,v.map_mul,v.map_neg,v.map_pow,hu]
    calc exp (-(P:ℤ))^2*v (D c)≤exp (-(P:ℤ))^2*exp Q:=mul_le_mul_right hQ _
      _=exp (Q-2*P):=by rw [sq,← exp_add,← exp_add];congr 1;ring
  have h:=ECM v D π hπ s hs C hcont hsep c⁻¹ P hP hu _ hDu
  intro g
  have hg:=h g
  rwa [show Q-2*(P:ℤ)+P=Q-P by ring] at hg

end Signed

def infCap (d:Fin 3):FlagDegree:= ![⟨0,3,5⟩,⟨0,0,5⟩,⟨0,3,2⟩] d

theorem infCap_zOnly (d:Fin 3):(infCap d).zOnly=0:=by fin_cases d<;>rfl

def capPole (d:Fin 3) (P t:ℤ):ℤ:=((infCap d).yz:ℤ)*t+((infCap d).all:ℤ)*P

def dirS (d:Fin 3) (P pσ:ℤ):ℤ:= ![0,P,max P pσ] d

def DirShape {K:Type} [Field K] (d:Fin 3) (q:Fin 3→Polynomial K):Prop:=
  ![q 0=0∧q 1=0∧Polynomial.derivative (q 2)=0,q 1=0,True] d

section Slice

variable {K:Type} [Field K] (F F₀:MvPolynomial (Fin 4) K) [hF₀:Fact (Irreducible F₀)]
  (hdvd:F₀ ∣ F)
set_option linter.unusedSectionVars false

noncomputable def placeYZ (v:Valuation (SliceField F₀) ℤᵐ⁰):ℤ:=
  max (vpole v (sliceCoord F₀ 0)) (vpole v (sliceCoord F₀ 2))

variable (v:Valuation (SliceField F₀) ℤᵐ⁰)

theorem GDQ (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1) (d:Fin 3) (q:Fin 3→Polynomial K)
    (hq:DirShape d q):
    vpole v (JJ F F₀ hdvd (sliceLinearL F₀ q))≤
      dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)):=by
  set x0:=sliceProj F₀ (MvPolynomial.X 0)
  set Dd:=JJ F F₀ hdvd
  have hP0:0≤placeP F₀ v:=le_max_of_le_left (vpole_nonneg _ _)
  have hcoord: ∀j,v (sliceCoord F₀ j)≤exp (placeP F₀ v):=by
    intro j
    refine (AQZ v _).trans ?_
    rw [exp_le_exp,placeP]
    fin_cases j
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_right _ _)
  have hDa: ∀p:Polynomial K,Dd (Polynomial.aeval x0 p)=
      Polynomial.aeval x0 (Polynomial.derivative p):=by
    intro p
    rw [Derivation.map_aeval,DMP F F₀ hdvd hH,smul_eq_mul,mul_one]
  have hterm: ∀m,Dd (Polynomial.aeval x0 (q m)*sliceCoord F₀ m)=
      Polynomial.aeval x0 (q m)*Dd (sliceCoord F₀ m)+
        sliceCoord F₀ m*Polynomial.aeval x0 (Polynomial.derivative (q m)):=by
    intro m;rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,hDa]
  have hDc0:Dd (sliceCoord F₀ 0)=sliceCoord F₀ 1:=ATS F F₀ hdvd hH
  have hDc2:Dd (sliceCoord F₀ 2)=0:=ATX F F₀ hdvd hH
  have hℓ:Dd (sliceLinearL F₀ q)= ∑ m,(Polynomial.aeval x0 (q m)*Dd (sliceCoord F₀ m)+
      sliceCoord F₀ m*Polynomial.aeval x0 (Polynomial.derivative (q m))):=by
    rw [sliceLinearL,map_sum];exact Finset.sum_congr rfl fun m _=>hterm m
  fin_cases d
  · obtain ⟨h0,h1,h2⟩:q 0=0∧q 1=0∧Polynomial.derivative (q 2)=0:=hq
    have hz:Dd (sliceLinearL F₀ q)=0:=by
      rw [hℓ,Fin.sum_univ_three,h0,h1,h2]
      simp [hDc2]
    change vpole v _≤0
    rw [hz];simp [vpole]
  · have h1:q 1=0:=hq
    change vpole v _≤placeP F₀ v
    rw [vpole_le_iff _ _ _ hP0,hℓ,Fin.sum_univ_three,h1,hDc0,hDc2]
    simp only [map_zero,zero_mul,mul_zero,add_zero,zero_add]
    refine (v.map_add _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)<;>
      rw [v.map_mul]
    · exact (mul_le_of_le_one_left' (DHW F₀ v hK hX0 _)).trans (hcoord 1)
    · exact (mul_le_of_le_one_right' (DHW F₀ v hK hX0 _)).trans (hcoord 0)
    · exact (mul_le_of_le_one_right' (DHW F₀ v hK hX0 _)).trans (hcoord 2)
  · change vpole v _≤max (placeP F₀ v) (vpole v (sliceSigma F F₀))
    rw [vpole_le_iff _ _ _ (le_max_of_le_left hP0)]
    refine (DMT F F₀ hdvd v hH hK hX0 q).trans (max_le ?_ ?_)
    · rw [exp_le_exp];exact le_max_left _ _
    · exact (AQZ v _).trans (by rw [exp_le_exp];exact le_max_right _ _)

theorem GIA (d:Fin 3) (hH:sliceProj F₀ (polyH K F) ≠ 0)
    (hnorm: ∃x,v x=exp (-1))
    (hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1)
    (hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1)
    (ℓ:SliceField F₀)
    (hℓ:v (JJ F F₀ hdvd ℓ)≤max (exp (placeP F₀ v)) (v (sliceSigma F F₀)))
    (hdir:vpole v (JJ F F₀ hdvd ℓ)≤
      dirS d (placeP F₀ v) (vpole v (sliceSigma F F₀)))
    (C:ℤ) (hcrude:CrudeBound v (JJ F F₀ hdvd) C)
    (hsep:NO v (JJ F F₀ hdvd)
      (exp (vpole v (JJ F F₀ hdvd ℓ))))
    (h2:(2:K) ≠ 0)
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0)
    (hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b)
    (m:ℕ):
    3*vpole v ((⇑(JJ F F₀ hdvd))^[m] (sliceCoord F₀ 1))+
        m*capPole d (placeP F₀ v) (placeYZ F₀ v)≤
      m*(4*placeT F F₀ v+2*placeH F F₀ v)+3*placeP F₀ v:=by
  classical
  haveI:v.IsTrivialOn K:=⟨hK⟩
  set Dd:=JJ F F₀ hdvd with hDd
  set P:=placeP F₀ v with hPdef
  set T:=placeT F F₀ v with hTdef
  set h:=placeH F F₀ v with hhdef
  set pσ:=vpole v (sliceSigma F F₀) with hpσdef
  set s:=vpole v (Dd ℓ) with hsdef
  set t:=placeYZ F₀ v with htdef
  set p0:=vpole v (sliceCoord F₀ 0)
  set p1:=vpole v (sliceCoord F₀ 1)
  set p2:=vpole v (sliceCoord F₀ 2)
  have hp0:0≤p0:=vpole_nonneg _ _
  have hp1:0≤p1:=vpole_nonneg _ _
  have hp2:0≤p2:=vpole_nonneg _ _
  have hPeq:P=max p1 (max p0 p2):=rfl
  have hteq:t=max p0 p2:=rfl
  have hTeq:T=max (2*P) (max p0 p2+pσ):=rfl
  have ht0:0≤t:=le_max_of_le_left hp0
  have htP:t≤P:=le_max_right _ _
  have hh0:0≤h:=vzero_nonneg _ _
  have hs0:0≤s:=vpole_nonneg _ _
  have hTP:2*P≤T:=le_max_left _ _
  have hTσ:t+pσ≤T:=le_max_right _ _
  have hold:=place_bound F F₀ hdvd v hH hnorm hK hX0 ℓ hℓ C hcrude hsep h2 hchar hgen m
  rcases eq_or_lt_of_le (le_max_of_le_left hp1:0≤P) with hPz | hPpos
  ·
    have hcap:capPole d P t=0:=by
      have hPz' :P=0:=hPz.symm
      have htz:t=0:=by omega
      rw [capPole,htz,hPz'];ring
    rw [hcap,mul_zero,add_zero]
    exact hold
  ·
    have hPpos:0<P:=hPpos
    obtain ⟨π₀,hπ₀⟩:=hnorm
    obtain ⟨j,hj⟩: ∃j:Fin 3,vpole v (sliceCoord F₀ j)=P:=by
      rcases max_choice p1 (max p0 p2) with h1 | h1
      · exact ⟨1,by rw [hPeq,h1]⟩
      · rcases max_choice p0 p2 with h2 | h2
        · exact ⟨0,by rw [hPeq,h1,h2]⟩
        · exact ⟨2,by rw [hPeq,h1,h2]⟩
    have hcj0:v (sliceCoord F₀ j) ≠ 0:=by
      intro h0
      have:vpole v (sliceCoord F₀ j)=0:=by simp [vpole,h0]
      omega
    have hcj:v (sliceCoord F₀ j)=exp ((P.toNat:ℕ):ℤ):=by
      rw [← exp_log hcj0]
      congr 1
      have:vpole v (sliceCoord F₀ j)=max 0 (v (sliceCoord F₀ j)).log:=rfl
      omega
    have hPK:((P.toNat:ℕ):K) ≠ 0:=
      hchar P.toNat (by omega) (by rw [Int.toNat_of_nonneg hPpos.le];exact le_max_left _ _)
    have hQ:v (Dd (sliceCoord F₀ j))≤exp (max P pσ):=by
      fin_cases j
      · show v (Dd (sliceCoord F₀ 0))≤_
        rw [hDd,ATS F F₀ hdvd hH]
        exact (AQZ v _).trans (by
          rw [exp_le_exp];have:=le_max_left p1 (max p0 p2);exact le_max_of_le_left (by omega))
      · show v (Dd (sliceCoord F₀ 1))≤_
        rw [hDd,CGT F F₀ hdvd hH]
        exact (AQZ v _).trans (by rw [exp_le_exp];exact le_max_right _ _)
      · show v (Dd (sliceCoord F₀ 2))≤_
        rw [hDd,ATX F F₀ hdvd hH,v.map_zero];exact zero_le
    have hθ:=FCO v Dd π₀ hπ₀ s hs0 C hcrude hsep (sliceCoord F₀ j) P.toNat
      hPK hcj (max P pσ) hQ
    have hPn:((P.toNat:ℕ):ℤ)=P:=Int.toNat_of_nonneg hPpos.le
    rw [hPn] at hθ
    set θ:=max s (max P pσ-P) with hθdef
    have hθ0:0≤θ:=le_max_of_le_left hs0

    have hlaw:3*θ+capPole d P t≤4*T:=by
      rw [hθdef]
      fin_cases d<;>simp only [capPole,infCap,dirS] at hdir ⊢ <;>simp at hdir ⊢ <;>omega
    have hit:=CNO v Dd θ hθ0 hθ m (sliceCoord F₀ 1)
    have hc1:vpole v (sliceCoord F₀ 1)≤P:=by rw [hPeq];exact le_max_left _ _
    have h1:(m:ℤ)*(3*θ+capPole d P t)≤m*(4*T):=
      mul_le_mul_of_nonneg_left hlaw (Nat.cast_nonneg m)
    have h4:0≤(m:ℤ)*h:=mul_nonneg (Nat.cast_nonneg m) hh0
    nlinarith

end Slice

section Budget

variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

local notation "w" =>RCN326.w

omit [IsAlgClosed E] in

theorem GCV (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (H G:MvPolynomial (Fin 3) E) (ν:RCN026.Place E (AJ E D)) (d:Fin 3):
    flagPole ν.val (coordinate E D) (infCap d)≤4*RCN064.KS D H G ν:=by
  have hT:=le_max_left (2*max (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2))))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2))+
      RCN187.poleOrder ν.val (RCN064.movingRatio D H G))
  have ht:=le_max_right (RCN187.poleOrder ν.val (coordinate E D 1))
    (max (RCN187.poleOrder ν.val (coordinate E D 0)) (RCN187.poleOrder ν.val (coordinate E D 2)))
  have ht0:0≤max (RCN187.poleOrder ν.val (coordinate E D 0))
      (RCN187.poleOrder ν.val (coordinate E D 2)):=
    le_max_of_le_left (le_max_left _ _)
  unfold RCN064.KS
  fin_cases d<;>simp only [flagPole,infCap]<;>simp<;>omega

theorem FNW (d:Fin 3) (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
    (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
    (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K) (hqd:DirShape d q)
    (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (h2:(2:K) ≠ 0)
    (ν:RCN026.Place E (AJ E D))
    (hchar: ∀n:ℕ,0<n→(n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
      (RCN026.zeroOrder E (AJ E D) ν
        (CT.GP (phiE K E) D (polyH K F)))→(n:K) ≠ 0)
    (hdefer: ∀(e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (RY D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (JJ F F₀ hdvd) C)∧
      NO v (JJ F F₀ hdvd)
        (exp (vpole v (JJ F F₀ hdvd (sliceLinearL F₀ q))))):
    3*RCN187.poleOrder ν.val
      (CT.GP (phiE K E) D (MN F (w-1))/
        CT.GP (phiE K E) D (polyH K F)^(2*w-1))+
      ((w+1:ℕ):ℤ)*flagPole ν.val (coordinate E D) (infCap d)≤
    ((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν+
        2*RCN026.zeroOrder E (AJ E D) ν
          (CT.GP (phiE K E) D (polyH K F)))+
      3*flagPole ν.val (coordinate E D) unitAllFlag:=by
  classical
  set ψ:=RY D F₀ hker with hψdef
  set Dd:=JJ F F₀ hdvd with hDd
  set wv:Valuation (SliceField F₀) ℤᵐ⁰:=ν.val.comap ψ with hwvdef
  have hwv: ∀x,wv x=ν.val (ψ x):=fun _=>rfl
  have hHψ:ψ (sliceProj F₀ (polyH K F)) ≠ 0:=by
    rw [hψdef,SR]
    intro h
    exact hHD ((ABU D _).1 h)
  have hH:sliceProj F₀ (polyH K F) ≠ 0:=fun h=>hHψ (by rw [h,map_zero])
  have hτ:CT.GP (phiE K E) D (MN F (w-1))/
      CT.GP (phiE K E) D (polyH K F)^(2*w-1)=
      ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)):=by
    have h:=DJY F F₀ hdvd hH (w-1)
    have hw1:w-1+1=w:=rfl
    have hw2:2*(w-1)+1=2*w-1:=rfl
    rw [hw1,hw2] at h
    rw [show sliceCoord F₀ 1=sliceProj F₀ (MvPolynomial.X 2) from rfl,h,map_div₀,map_pow,
      hψdef,SR,SR]
    rfl
  rw [hτ]
  have hcap4:=GCV D (surfaceMap (phiE K E) (polyH K F))
    (surfaceMap (phiE K E) (polyG K F)) ν d
  have hRHS0:((w+1:ℕ):ℤ)*flagPole ν.val (coordinate E D) (infCap d)≤
      ((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) ν+
        2*RCN026.zeroOrder E (AJ E D) ν
          (CT.GP (phiE K E) D (polyH K F)))+
      3*flagPole ν.val (coordinate E D) unitAllFlag:=by
    have h2:=RCN026.AUU E (AJ E D) ν
      (CT.GP (phiE K E) D (polyH K F))
    have h3:=ALZ ν.val (coordinate E D) unitAllFlag
    have hw:(0:ℤ)≤((w+1:ℕ):ℤ):=by positivity
    have h4:=mul_le_mul_of_nonneg_left hcap4 hw
    have h5:=mul_nonneg hw (mul_nonneg (show (0:ℤ)≤2 by norm_num) h2)
    rw [mul_add]
    linarith
  by_cases hnt: ∃x,wv x ≠ 0∧wv x ≠ 1
  swap
  · have hpole:RCN187.poleOrder ν.val (ψ ((⇑Dd)^[w] (sliceCoord F₀ 1)))=0:=by
      set x:=(⇑Dd)^[w] (sliceCoord F₀ 1)
      have hx:wv x=0∨wv x=1:=by
        by_contra h;rw [not_or] at h;exact hnt ⟨x,h.1,h.2⟩
      show max 0 (ν.val (ψ x)).log=0
      rw [← hwv]
      rcases hx with h | h<;>simp [h]
    rw [hpole,mul_zero,zero_add]
    exact hRHS0
  obtain ⟨e,v,he,hvn,hwve⟩:=DZW wv hnt
  have he0:e ≠ 0:=by omega
  have hν: ∀x,ν.val (ψ x)=v x^e:=fun x=>hwve x
  have hpole: ∀x,RCN187.poleOrder ν.val (ψ x)=e*vpole v x:=
    fun x=>FXJ v wv e hwve x
  have hzeroν: ∀x,RCN026.zeroOrder E (AJ E D) ν (ψ x)=e*vzero v x:=
    fun x=>FSG v wv e hwve x
  have hνE: ∀a:E,a ≠ 0→ν.val (algebraMap E (AJ E D) a)=1:=
    fun a ha=>(ν.property.2).eq_one a ha
  have hφinj:Function.Injective (phiE K E):=
    (algebraMap (GenericField K) E).injective.comp (DI K)
  have hK: ∀a:K,a ≠ 0→v (algebraMap K (SliceField F₀) a)=1:=by
    intro a ha
    have h1:ν.val (ψ (algebraMap K _ a))=1:=by
      rw [hψdef,psi_const]
      exact hνE _ (fun h=>ha (Polynomial.C_eq_zero.mp (hφinj (h.trans (map_zero _).symm))))
    rw [hν] at h1
    exact le_antisymm ((DVA he0).1 h1.le)
      (not_lt.1 fun hlt=>absurd h1 (ne_of_lt ((DTJ he0).2 hlt)))
  have hX0:v (sliceProj F₀ (MvPolynomial.X 0))≤1:=by
    have h1:ν.val (ψ (sliceProj F₀ (MvPolynomial.X 0)))≤1:=by
      rw [hψdef,psi_X0]
      haveI:=ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    rw [hν] at h1
    exact (DVA he0).1 h1
  obtain ⟨⟨C,hcrude⟩,hsep⟩:=hdefer e v he hvn hwve
  have hℓ:=DMT F F₀ hdvd v hH hK hX0 q
  have hdir:=GDQ F F₀ hdvd v hH hK hX0 d q hqd

  have hcoordν: ∀j,RCN187.poleOrder ν.val (coordinate E D j)=
      e*vpole v (sliceCoord F₀ j):=by
    intro j;rw [← psi_coord D F₀ hker j,← hψdef,hpole]
  have hPν:flagPole ν.val (coordinate E D) unitAllFlag=e*placeP F₀ v:=by
    simp only [flagPole,unitAllFlag,Nat.cast_zero,zero_mul,Nat.cast_one,one_mul,zero_add]
    rw [hcoordν,hcoordν,hcoordν,placeP,scale_flag (e:ℤ) (by positivity)]
  have hcapν:flagPole ν.val (coordinate E D) (infCap d)=
      e*capPole d (placeP F₀ v) (placeYZ F₀ v):=by
    simp only [flagPole,infCap_zOnly,Nat.cast_zero,zero_mul,zero_add]
    rw [hcoordν,hcoordν,hcoordν,capPole,placeP,placeYZ,scale_flag (e:ℤ) (by positivity),
      ← mul_max_of_nonneg _ _ (by positivity:(0:ℤ)≤e)]
    ring
  have hhν:RCN026.zeroOrder E (AJ E D) ν
      (CT.GP (phiE K E) D (polyH K F))=
        e*placeH F F₀ v:=by
    have:CT.GP (phiE K E) D (polyH K F)=
        ψ (sliceProj F₀ (polyH K F)):=by rw [hψdef,SR];rfl
    rw [this,hzeroν]
    rfl
  have hTν:RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
      (surfaceMap (phiE K E) (polyG K F)) ν=e*placeT F F₀ v:=by
    unfold RCN064.KS
    rw [hcoordν,hcoordν,hcoordν,← psi_sigma D F₀ hker F,← hψdef,hpole,placeT,placeP,
      scale_target (e:ℤ) (by positivity)]
  have hPv0:0≤placeP F₀ v:=le_max_of_le_left (vpole_nonneg _ _)
  have hhv0:0≤placeH F F₀ v:=vzero_nonneg _ _
  have hcharv: ∀n:ℕ,0<n→(n:ℤ)≤max (placeP F₀ v) (placeH F F₀ v)→(n:K) ≠ 0:=by
    intro n hn hle
    refine hchar n hn ?_
    rw [hPν,hhν]
    have h1:placeP F₀ v≤e*placeP F₀ v:=le_mul_of_one_le_left hPv0 (by exact_mod_cast he)
    have h2:placeH F F₀ v≤e*placeH F F₀ v:=le_mul_of_one_le_left hhv0 (by exact_mod_cast he)
    exact hle.trans (max_le_max h1 h2)
  have hgen:placeP F₀ v=0→ ∃a b:MvPolynomial (Fin 4) K,
      v (sliceProj F₀ a)<1∧v (sliceProj F₀ b)<1∧
      ∀g,v (sliceProj F₀ g)<1→ ∃s x y:MvPolynomial (Fin 4) K,
        v (sliceProj F₀ s)=1∧s*g=x*a+y*b:=by
    intro hP0
    have hint:=place_hint F₀ v hK hX0 hP0
    set 𝔓:=valCentre (sliceProj F₀) v hint with h𝔓def
    set y:Fin 3→AJ E D:=coordinate E D
    have hev: ∀P:MvPolynomial (Fin 3) (GenericField K),
        aeval y P=BR E D (CD (GenericField K) E P):=by
      intro P
      rw [HJ,CD,aeval_map_algebraMap]
    have hνΩ: ∀a:GenericField K,
        ν.val (algebraMap (GenericField K) (AJ E D) a)≤1:=by
      intro a
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (AJ E D)]
      haveI:=ν.property.2
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one ν.val _
    have hyint: ∀j,ν.val (y j)≤1:=by
      intro j
      rw [show y j=ψ (sliceCoord F₀ j) from (psi_coord D F₀ hker j).symm,hν]
      exact pow_le_one' (hint _) e
    let fy:MvPolynomial (Fin 3) (GenericField K)→+*AJ E D:=(aeval y).toRingHom
    have hintΩ: ∀P:MvPolynomial (Fin 3) (GenericField K),ν.val (fy P)≤1:=by
      intro P
      change ν.val (aeval y P)≤1
      induction P using MvPolynomial.induction_on with
      | C a=>rw [aeval_C];exact hνΩ a
      | add p r hp hr=>rw [map_add];exact (ν.val.map_add _ _).trans (max_le hp hr)
      | mul_X p j hp=>
        rw [map_mul,ν.val.map_mul,aeval_X];exact mul_le_one' hp (hyint j)
    set 𝔮:=valCentre fy ν.val hintΩ with h𝔮def
    have hP𝔮:AWO 𝔮=𝔓:=by
      ext g
      rw [AOX,h𝔮def,h𝔓def,BYN,BYN]
      change ν.val (aeval y _)<1 ↔ _
      rw [hev,← AXD]
      change ν.val (sliceMap D g)<1 ↔ _
      rw [← SR D F₀ hker,← hψdef,hν,DTJ he0]
    have hcω: ∀a:GenericField K,a ≠ 0→
        ν.val (algebraMap (GenericField K) (AJ E D) a)=1:=by
      intro a ha
      rw [IsScalarTower.algebraMap_apply (GenericField K) E (AJ E D)]
      exact hνE _ ((map_ne_zero_iff _ (algebraMap (GenericField K) E).injective).2 ha)
    have hsl: ∑ m,algebraMap (GenericField K) (AJ E D) (c m)*y m=
        algebraMap E (AJ E D) (sliceValue (GenericField K) E):=by
      have h1:=(ABU D _).2 hslice
      rw [map_sub,sub_eq_zero,← hev] at h1
      have h2:BR E D (MvPolynomial.C (sliceValue (GenericField K) E))=
          algebraMap E (AJ E D) (sliceValue (GenericField K) E):=
        (BR E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum,map_mul,aeval_C,aeval_X]
    have hℓ' : ∀a:Fin 3→GenericField K,
        ν.val (∑ m,algebraMap (GenericField K) (AJ E D) (c m)*y m-
          algebraMap (GenericField K) (AJ E D) (∑ m,c m*a m))=1:=by
      intro a
      rw [hsl,IsScalarTower.algebraMap_apply (GenericField K) E (AJ E D),
        ← map_sub]
      apply hνE
      intro h
      apply AMM (Ω:=GenericField K) (E:=E)
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap _
    have h𝔮h:𝔮.height≤2:=
      DZO ν.val y 𝔮 (fun P=>BYN _ _ _ P) c hcω hℓ'
    have h𝔓h:𝔓.height≤2:=hP𝔮 ▸ (BCQ 𝔮).trans h𝔮h
    haveI:=RCN230.AHH 𝔓
    obtain ⟨a,ha,b,hb,hgen'⟩:=CMC 𝔓 h𝔓h
    refine ⟨a,b,ha,hb,fun g hg=> ?_⟩
    obtain ⟨s,hs,x,y,hsg⟩:=hgen' g hg
    exact ⟨s,x,y,le_antisymm (hint s) (not_lt.1 hs),hsg⟩
  have hmain:=GIA F F₀ hdvd v d hH hvn hK hX0 (sliceLinearL F₀ q) hℓ hdir C hcrude
    hsep h2 hcharv hgen w
  rw [hpole,hTν,hhν,hPν,hcapν]
  rw [hcapν,hTν] at hcap4
  have hk:=mul_le_mul_of_nonneg_left hmain (show (0:ℤ)≤e by positivity)
  have heh:0≤(e:ℤ)*placeH F F₀ v:=mul_nonneg (by positivity) hhv0
  push_cast at hk ⊢
  linarith

theorem DOC (d:Fin 3) (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (sep:BP D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hqd:DirShape d q) (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (h2:(2:K) ≠ 0)
    (hchar: ∀ν:RCN026.Place E (AJ E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (AJ E D) ν
          (CT.GP (phiE K E) D (polyH K F)))→(n:K) ≠ 0)
    (hdefer: ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place E (AJ E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (RY D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (JJ F F₀ hdvd) C)∧
      NO v (JJ F F₀ hdvd)
        (exp (vpole v (JJ F F₀ hdvd (sliceLinearL F₀ q)))))
    (W:Finset (RCN026.Place E (AJ E D))):
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (CT.GP (phiE K E) D (MN F (w-1))/
        CT.GP (phiE K E) D (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS D (surfaceMap (phiE K E) (polyH K F))
          (surfaceMap (phiE K E) (polyG K F)) nu+
        2*RCN026.zeroOrder E (AJ E D) nu
          (CT.GP (phiE K E) D (polyH K F))-
        flagPole nu.val (coordinate E D) (infCap d))+
      3*flagPole nu.val (coordinate E D) unitAllFlag):=by
  have hF:F ≠ 0:=by
    rintro rfl
    apply hHD
    simp [polyH]
  obtain ⟨F₀,hirr,hdvd,hker⟩:=FVZ D sep F hF hFD c i hci hslice
  haveI:Fact (Irreducible F₀):=⟨hirr⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _=> ?_
  have h:=FNW d F D F₀ hdvd hker hHD c q hqd hq hslice h2 ν (hchar ν)
    (hdefer F₀ hdvd hker ν)
  linarith

end Budget

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN005 RCN006 RCN095 RCN135 RCN136 RCN202 RCN204 RCN208 RCN313 RCN341
noncomputable section
set_option autoImplicit false

section SliceForm
variable {Ω E:Type} [Field Ω] [Field E] [Algebra Ω E] [Algebra (RatFunc Ω) E]

abbrev sliceForm (c:Fin 3→Ω):MvPolynomial (Fin 3) E:=
  C (sliceValue Ω E)-CD Ω E (∑ m,C (c m)*MvPolynomial.X m)

theorem sliceForm_eq (c:Fin 3→Ω):
    sliceForm (E:=E) c=
      C (sliceValue Ω E)- ∑ m,C (algebraMap Ω E (c m))*MvPolynomial.X m:=by
  simp [CD]

theorem GHQ (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1):
    (sliceForm (E:=E) c).coeff (Finsupp.single i 1)= -1:=by
  classical
  rw [sliceForm_eq,coeff_sub,coeff_C,if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm,
    coeff_sum]
  simp [coeff_C_mul,coeff_X,Finsupp.single_left_inj one_ne_zero,Finset.sum_ite_eq',hci]

theorem DSD (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1):
    (sliceForm (E:=E) c).totalDegree=1:=by
  apply le_antisymm
  · rw [sliceForm_eq]
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _=> ?_)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
  · have h:=le_totalDegree (p:=sliceForm (E:=E) c) (s:=Finsupp.single i 1)
      (by rw [MvPolynomial.mem_support_iff,GHQ c i hci]
          exact neg_ne_zero.mpr one_ne_zero)
    simpa using h

private theorem CQT {a:MvPolynomial (Fin 3) E} (ha:a ≠ 0)
    (h:a.totalDegree=0):IsUnit a:=by
  rw [totalDegree_eq_zero_iff_eq_C] at h
  rw [h] at ha ⊢
  exact (isUnit_iff_ne_zero.mpr fun h0=>ha (by rw [h0,map_zero])).map C

theorem FBG (c:Fin 3→Ω) (i:Fin 3) (hci:c i=1):
    Irreducible (sliceForm (E:=E) c):=by
  have hd:=DSD (E:=E) c i hci
  have hne:sliceForm (E:=E) c ≠ 0:=fun h=>by rw [h] at hd;simp at hd
  refine ⟨fun hu=> ?_,fun a b hab=> ?_⟩
  · obtain ⟨q,hq⟩:=hu.exists_right_inv
    have h1:=congrArg totalDegree hq
    rw [totalDegree_mul_of_isDomain hne (right_ne_zero_of_mul_eq_one hq),totalDegree_one,
      hd] at h1
    omega
  · have ha:a ≠ 0:=by rintro rfl;exact hne (by rw [hab,zero_mul])
    have hb:b ≠ 0:=by rintro rfl;exact hne (by rw [hab,mul_zero])
    have h1:=congrArg totalDegree hab
    rw [totalDegree_mul_of_isDomain ha hb,hd] at h1
    rcases Nat.eq_zero_or_pos a.totalDegree with h | h
    · exact Or.inl (CQT ha h)
    · exact Or.inr (CQT hb (by omega))

theorem FWZ [IsScalarTower Ω (RatFunc Ω) E] [Infinite Ω] (c:Fin 3→Ω)
    (i:Fin 3) (hci:c i=1)
    (A:MvPolynomial (Fin 3) Ω) (hA:A ≠ 0):
    ¬sliceForm (E:=E) c ∣ CD Ω E A:=by
  classical
  rintro ⟨Q,hQ⟩
  apply hA
  apply MvPolynomial.funext
  intro ω
  rw [map_zero]
  set s:= ∑ m,c m*ω m
  let f:Fin 3→Polynomial Ω:=fun m=>
    Polynomial.C (ω m)+if m=i then Polynomial.X-Polynomial.C s else 0
  have hP:aeval f A=0:=by
    apply transcendental_iff_injective.mp (AMM (Ω:=Ω) (E:=E))
    rw [map_zero,← AlgHom.comp_apply,comp_aeval]
    have hev:aeval (fun m=>Polynomial.aeval (sliceValue Ω E) (f m)) A=
        eval (fun m=>Polynomial.aeval (sliceValue Ω E) (f m)) (CD Ω E A):=by
      rw [CD,eval_map,aeval_def]
    rw [hev,hQ,eval_mul]
    apply mul_eq_zero_of_left
    rw [sliceForm_eq]
    simp only [f,map_sub,map_sum,map_mul,eval_C,eval_X,map_add,Polynomial.aeval_C,
      apply_ite (Polynomial.aeval (sliceValue Ω E)),Polynomial.aeval_X,map_zero,mul_add,
      Finset.sum_add_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      hci,map_one,one_mul,s]
    ring
  have h:=congrArg (Polynomial.aeval s) hP
  rw [← AlgHom.comp_apply,comp_aeval,map_zero] at h
  have hf:(fun m=>Polynomial.aeval s (f m))=ω:=by
    funext m
    by_cases hm:m=i<;>simp [f,hm]
  rw [hf] at h
  exact h

end SliceForm

section Gate
variable {E:Type} [Field E]

theorem GFP (P:Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime] (j:Fin 3)
    (hj:Transcendental E (coordinate E P j)) (p:ℕ) [CharP E p]
    (G H:MvPolynomial (Fin 3) E) (hG:Irreducible G) (hGP:G ∈ P) (hHP:H ∈ P)
    (hGH: ¬G ∣ H) (hdeg: ∀k,G.degreeOf k<p)
    (hmix:RCN001.EB E G H j<p):
    letI:=DT E P j hj
    FiniteDimensional (RatFunc E) (AJ E P)∧
      Algebra.IsSeparable (RatFunc E) (AJ E P)∧
      Module.finrank (RatFunc E) (AJ E P)≤
        RCN001.EB E G H j:=by
  have key: ∀k (hk:Transcendental E (coordinate E P k)),k=j→
      (letI:=DT E P k hk
       FiniteDimensional (RatFunc E) (AJ E P)∧
        Algebra.IsSeparable (RatFunc E) (AJ E P)∧
        Module.finrank (RatFunc E) (AJ E P)≤
        RCN001.EB E G H j)→
      (letI:=DT E P j hj
       FiniteDimensional (RatFunc E) (AJ E P)∧
        Algebra.IsSeparable (RatFunc E) (AJ E P)∧
        Module.finrank (RatFunc E) (AJ E P)≤
        RCN001.EB E G H j):=by
    rintro k hk rfl h;exact h
  have hj' :Transcendental E (coordinate E P ((Equiv.swap 0 j) 0)):=by
    rwa [Equiv.swap_apply_left]
  exact key _ hj' (Equiv.swap_apply_left 0 j)
    (RCN004.AGY E (Equiv.swap 0 j) P hj' p G H hG hGP hHP hGH
      (hdeg _) (hdeg _) hmix)

end Gate

section Char
variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

theorem inFlag_total {L:Type} [Field L] (φ:Polynomial K→+*L) (P:MvPolynomial (Fin 4) K)
    (N:ℕ) (h:MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤N):
    BI ⟨0,0,N⟩ (surfaceMap φ P):=by
  intro e he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (VO φ P he)
  have ht:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,1] hd).trans h
  simp [RCN081.weight_fin4] at ht
  simp only [InFlag,Finsupp.tail_apply,show Fin.succ (0:Fin 3)=1 from rfl,
    show Fin.succ (1:Fin 3)=2 from rfl,show Fin.succ (2:Fin 3)=3 from rfl]
  omega

theorem hchar_holds [CharP K 2130706433] (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep:BP D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N) (hN9:N≤9678):
    ∀ν:RCN026.Place E (AJ E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (AJ E D) ν
          (CT.GP (phiE K E) D (polyH K F)))→(n:K) ≠ 0:=by
  classical
  haveI:CharP E 2130706433:=
    charP_of_injective_algebraMap (algebraMap (GenericField K) E).injective 2130706433
  set L:=AJ E D
  set y:=coordinate E D
  set Fp:=surfaceMap (phiE K E) F with hFp
  have hF:F ≠ 0:=by rintro rfl;apply hHD;simp [polyH]
  have hFflag:BI ⟨0,0,N⟩ Fp:=inFlag_total _ F N hN
  have hHflag:BI ⟨0,0,N⟩ (surfaceMap (phiE K E) (polyH K F)):=
    inFlag_total _ _ N ((RCN234.wt_polyH_le _ F N hN).trans (Nat.sub_le _ _))
  have hirr:=FBG (E:=E) c i hci
  have hdvd: ¬sliceForm (E:=E) c ∣ Fp:=by
    rw [hFp,AXD]
    exact FWZ c i hci _ (ZL _ (DI K) F hF)
  have hdeg1: ∀k,(sliceForm (E:=E) c).degreeOf k≤1:=fun k=>
    (degreeOf_le_totalDegree _ k).trans (DSD c i hci).le
  have hdegF: ∀k,Fp.degreeOf k≤N:=fun k=>by
    simpa using RCN084.AHE Fp _ hFflag k

  have hpole: ∀j (W:Finset (RCN026.Place E L)),
      (∑ ν ∈ W,RCN187.poleOrder ν.val (y j))≤2*N:=by
    intro j W
    have hmix:RCN001.EB E (sliceForm c) Fp j≤2*N:=
      (Nat.add_le_add (Nat.mul_le_mul (hdegF _) (hdeg1 _))
        (Nat.mul_le_mul (hdeg1 _) (hdegF _))).trans (by omega)
    have gate:=fun hx:Transcendental E (y j)=>GFP D j hx 2130706433 _ _ hirr
      hslice hFD hdvd (fun k=>by have:=hdeg1 k;omega) (by omega)
    have h:=RCN344.PY E L
      (RCN042.JV (y j) (fun hx=>⟨(gate hx).1,(gate hx).2.1⟩)) W
    rw [RCN042.MT] at h
    refine h.trans ?_
    by_cases hx:Transcendental E (y j)
    · rw [RCN042.LO _ _ hx]
      exact_mod_cast (gate hx).2.2.trans hmix
    · rw [RCN042.AIH _ _ (not_not.mp hx)]
      positivity
  have hp (j) (ν:RCN026.Place E L):RCN187.poleOrder ν.val (y j)≤2*N:=by
    simpa using hpole j {ν}

  set Hev:=CT.GP (phiE K E) D (polyH K F)
  have hHne:Hev ≠ 0:=fun h=>hHD ((CT.AAE D _).mp h)
  letI:=IP E D sep.index
  letI:=DT E D sep.index sep.transcendental
  letI:=IU E D sep.index
  letI:=_Q5 E D sep.index sep.transcendental
  letI:=IS E D sep.index sep.transcendental
  letI:FiniteDimensional (RatFunc E) L:=sep.finite
  letI:Algebra.IsSeparable (RatFunc E) L:=sep.separable
  set Pl:=RCN026.placesFor E L Hev hHne
  have hpoleH (μ:RCN026.Place E L):RCN346.poleOrder E L μ Hev≤
      N*(RCN187.poleOrder μ.val (y 0)+RCN187.poleOrder μ.val (y 1)+
        RCN187.poleOrder μ.val (y 2)):=by
    have h0:0≤RCN187.poleOrder μ.val (y 0):=le_max_left _ _
    have h1:0≤RCN187.poleOrder μ.val (y 1):=le_max_left _ _
    have h2:0≤RCN187.poleOrder μ.val (y 2):=le_max_left _ _
    have hle:flagPole μ.val y ⟨0,0,N⟩≤N*(RCN187.poleOrder μ.val (y 0)+
        RCN187.poleOrder μ.val (y 1)+RCN187.poleOrder μ.val (y 2)):=by
      simp only [flagPole,Nat.cast_zero,zero_mul,zero_add]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) (max_le (by linarith) (by linarith)))
        (by positivity)
    refine le_trans ?_ hle
    apply VI.BIH μ.val _ _ (ALZ _ _ _)
    have h:=ADJ μ.val (algebraMap E L)
      (RCN344.NP E L μ) y ⟨0,0,N⟩ _ hHflag
    simpa only [Hev,CT.GP,
      HJ,MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h
  have hzero (ν:RCN026.Place E L):RCN026.zeroOrder E L ν Hev≤N*(6*N):=by
    have hsum:RCN026.zeroOrder E L ν Hev≤ ∑ μ ∈ Pl,RCN026.zeroOrder E L μ Hev:=by
      by_cases hν:ν ∈ Pl
      · exact Finset.single_le_sum (fun μ _=>RCN026.AUU E L μ Hev) hν
      · have hno:RCN026.order E L ν Hev=0:=by
          by_contra hne;exact hν (RCN026.ALB E L Hev hHne ν hne)
        simp only [RCN026.zeroOrder,hno,max_self]
        exact Finset.sum_nonneg fun μ _=>RCN026.AUU E L μ Hev
    rw [RCN026.AJO] at hsum
    refine hsum.trans ((Finset.sum_le_sum fun μ _=>hpoleH μ).trans ?_)
    rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (by linarith [hpole 0 Pl,hpole 1 Pl,hpole 2 Pl])
      (by positivity)
  intro ν n hn hle
  have hf:flagPole ν.val y unitAllFlag≤2*N:=by
    rw [BPD]
    exact max_le (hp 1 ν) (max_le (hp 0 ν) (hp 2 ν))
  have hN9' :(N:ℤ)≤9678:=by exact_mod_cast hN9
  have hlt:(n:ℤ)<2130706433:=by
    have h1:=le_max_iff.mp hle
    rcases h1 with h1 | h1
    · linarith
    · have:=hzero ν;nlinarith
  intro h
  exact absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

end Char

end
end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero Polynomial

section Basic

theorem BQP {F:Type*} [Field F] {f:F[X]} (hf:Irreducible f)
    (hn:(f.natDegree:F) ≠ 0):f.Separable:=by
  rw [separable_iff_derivative_ne_zero hf]
  intro h
  obtain ⟨m,hm⟩: ∃m,f.natDegree=m+1:=
    ⟨f.natDegree-1,(Nat.succ_pred_eq_of_pos (Irreducible.natDegree_pos hf)).symm⟩
  have h1:=congrArg (fun g=>g.coeff m) h
  simp only [coeff_derivative,coeff_zero] at h1
  have h2:((m:F)+1)=(f.natDegree:F):=by rw [hm];push_cast;ring
  rw [h2,← hm] at h1
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact (leadingCoeff_ne_zero.2 hf.ne_zero) h3
  · exact hn h3

variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)

theorem ASC {R:Type*} [CommRing R] [Algebra R L]
    (hR: ∀r:R,v (algebraMap R L r)≤1) {x:L} (hx:IsIntegral R x):v x≤1:=by
  obtain ⟨f,hf,hfx⟩:=hx
  by_contra h
  rw [not_le] at h
  have hx0:v x ≠ 0:=(lt_trans zero_lt_one h).ne'
  rw [hf.as_sum,eval₂_add,eval₂_X_pow,eval₂_finsetSum] at hfx
  have hlt:v (∑ i ∈ Finset.range f.natDegree,
      eval₂ (algebraMap R L) x (C (f.coeff i)*Polynomial.X^i))<v (x^f.natDegree):=by
    refine v.map_sum_lt (by rw [v.map_pow];exact pow_ne_zero _ hx0) fun i hi=> ?_
    rw [eval₂_mul,eval₂_C,eval₂_X_pow,v.map_mul,v.map_pow,v.map_pow]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hR _)) ?_
    exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have:=v.map_add_eq_of_lt_left hlt
  rw [hfx,v.map_zero,v.map_pow] at this
  exact pow_ne_zero _ hx0 this.symm

end Basic

section Dedekind

variable {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰)
variable (A K' :Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]

include K' in

theorem FQL (hA: ∀a:A,v (algebraMap A L a)≤1) (hπ: ∃x,v x=exp (-1))
    (z:L) (hz:v z≤1):
    ∃r u:L,IsIntegral A r∧IsIntegral A u∧v u=1∧z=r/u:=by
  classical
  set C:=integralClosure A L
  haveI:IsDedekindDomain C:=integralClosure.isDedekindDomain A K' L
  haveI:IsFractionRing C L:=IsIntegralClosure.isFractionRing_of_finite_extension A K' L C
  have hCv: ∀c:C,v (c:L)≤1:=fun c=>ASC v hA c.2
  let ρ:C→+*v.valuationSubring:=
    (algebraMap C L).codRestrict v.valuationSubring fun c=>(Valuation.mem_valuationSubring_iff _ _).2 (hCv c)
  set 𝔓:Ideal C:=(IsLocalRing.maximalIdeal v.valuationSubring).comap ρ
  have hmem: ∀c:C,c ∈ 𝔓 ↔ v (c:L)<1:=by
    intro c
    rw [Ideal.mem_comap,← IsLocalRing.residue_eq_zero_iff,← ZT v _ (hCv c),
      AJL v _ (hCv c)]
    rfl
  have hunit: ∀c:C,c ∉ 𝔓→v (c:L)=1:=fun c hc=>
    le_antisymm (hCv c) (not_lt.1 fun h=>hc ((hmem c).2 h))
  have h𝔓:𝔓 ≠ ⊥ :=by
    obtain ⟨π,hπ⟩:=hπ
    obtain ⟨y,hy0,hy⟩:=exists_integral_multiples A K' ({π}:Finset L)
    have hint:=hy π (Finset.mem_singleton_self π)
    have hinj:Function.Injective (algebraMap A L):=by
      rw [IsScalarTower.algebraMap_eq A K' L]
      exact (algebraMap K' L).injective.comp (IsFractionRing.injective A K')
    have hπ0:π ≠ 0:=by rintro rfl;rw [v.map_zero] at hπ;exact exp_ne_zero hπ.symm
    intro hbot
    have hmem' :(⟨y • π,hint⟩:C) ∈ 𝔓:=by
      rw [hmem]
      change v (y • π)<1
      rw [Algebra.smul_def,v.map_mul,hπ]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' (hA y)) ?_
      rw [← exp_zero,exp_lt_exp];omega
    rw [hbot,Ideal.mem_bot] at hmem'
    have h0:=congrArg (fun c:C=>(c:L)) hmem'
    simp only [ZeroMemClass.coe_zero] at h0
    change y • π=0 at h0
    rw [Algebra.smul_def] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hy0 (hinj (h.trans (map_zero _).symm))
    · exact hπ0 h
  haveI:𝔓.IsPrime:=Ideal.comap_isPrime _ _
  set Bp:=Localization.subalgebra.ofField L 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors
  haveI:IsDiscreteValuationRing Bp:=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C h𝔓 Bp
  have hBp: ∀y:Bp,∃a s:C,s ∉ 𝔓∧(y:L)=(a:L)/(s:L):=by
    intro y
    obtain ⟨a,s,hs,hy⟩:=y.2
    exact ⟨a,s,hs,by rw [hy,div_eq_mul_inv];rfl⟩
  rcases ValuationRing.isInteger_or_isInteger Bp z with ⟨y,hy⟩ | ⟨y,hy⟩
  · obtain ⟨a,s,hs,hys⟩:=hBp y
    refine ⟨a,s,a.2,s.2,hunit s hs,?_⟩
    rw [← hy,← hys];rfl
  · obtain ⟨a,s,hs,hys⟩:=hBp y
    have hyz:z⁻¹=(a:L)/(s:L):=by rw [← hy,← hys];rfl
    by_cases hz0:z=0
    · exact ⟨0,1,isIntegral_zero,isIntegral_one,v.map_one,by rw [hz0,zero_div]⟩
    by_cases ha:a ∈ 𝔓
    · exfalso
      have h1:v z⁻¹<1:=by
        rw [hyz,map_div₀,hunit s hs,div_one];exact (hmem a).1 ha
      rw [map_inv₀] at h1
      have hz1:v z ≠ 0:=(Valuation.ne_zero_iff v).2 hz0
      have:1<v z:=by
        by_contra hle;rw [not_lt] at hle
        exact absurd h1 (not_lt.2 (one_le_inv₀ (zero_lt_iff.2 hz1) |>.2 hle))
      exact absurd hz (not_le.2 this)
    · have ha0:(a:L) ≠ 0:=by
        intro h;have:=hunit a ha;rw [h,v.map_zero] at this;exact zero_ne_one this
      refine ⟨s,a,s.2,a.2,hunit a ha,?_⟩
      rw [← inv_inv z,hyz,inv_div]

end Dedekind

section Tame

variable {K L:Type*} [Field K] [Field L] [Algebra K L] (v:Valuation L ℤᵐ⁰)
  (D:Derivation K L L)
variable (A K' :Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]

omit [Field K] [Algebra K L] in
theorem EYS (x:L):v x≤exp (max 0 (v x).log):=by
  by_cases hx:v x=0
  · rw [hx];exact zero_le
  · calc v x=exp (v x).log:=(exp_log hx).symm
      _≤exp (max 0 (v x).log):=by rw [exp_le_exp];exact le_max_right _ _

include K' in

theorem GXV (Λ0:ℤ) (hA: ∀a:A,Tame v D (exp Λ0) (algebraMap A L a)):
    ∃C:ℤ,∀r:L,IsIntegral A r→Tame v D (exp C) r:=by
  classical
  set B:=integralClosure A L
  haveI:Module.Finite A B:=IsIntegralClosure.finite A K' L B
  obtain ⟨G,hG⟩:=Module.Finite.fg_top (R:=A) (M:=B)
  set n:ℤ:= ∑ g ∈ G,max 0 (v (D (g:L))).log
  refine ⟨max Λ0 n,fun r hr=> ?_⟩
  have hgen: ∀g ∈ G,Tame v D (exp (max Λ0 n)) (g:L):=by
    intro g hg
    refine ⟨ASC v (fun a=>(hA a).1) g.2,(EYS v _).trans ?_⟩
    rw [exp_le_exp]
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f:=fun g:B=>max 0 (v (D (g:L))).log)
      (fun _ _=>le_max_left _ _) hg
  have key: ∀c:B,c ∈ Submodule.span A (G:Set B)→Tame v D (exp (max Λ0 n)) (c:L):=by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx=>exact hgen x hx
    | zero=>exact (tameSubring v D _).zero_mem
    | add x y _ _ hx hy=>exact (tameSubring v D _).add_mem hx hy
    | smul a x _ hx=>
      change Tame v D _ (a • (x:L))
      rw [Algebra.smul_def]
      exact (tameSubring v D _).mul_mem
        ((hA a).mono v D (by rw [exp_le_exp];exact le_max_left _ _)) hx
  exact key ⟨r,hr⟩ (by rw [hG];exact Submodule.mem_top)

omit [Field K] [Algebra K L] in
theorem residue_add (x y:L) (hx:v x≤1) (hy:v y≤1):
    residue v (x+y)=residue v x+residue v y:=by
  rw [AJL v _ hx,AJL v _ hy,
    AJL v _ ((v.map_add _ _).trans (max_le hx hy)),← map_add];rfl

omit [Field K] [Algebra K L] in
theorem residue_mul (x y:L) (hx:v x≤1) (hy:v y≤1):
    residue v (x*y)=residue v x*residue v y:=by
  have h:v (x*y)≤1:=by rw [v.map_mul];exact mul_le_one' hx hy
  rw [AJL v _ hx,AJL v _ hy,AJL v _ h,← map_mul];rfl

omit [Field K] [Algebra K L] [Algebra.IsSeparable K' L] in
include K' in

theorem FIC (hA: ∀a:A,v (algebraMap A L a)≤1)
    (F' :Subfield (IsLocalRing.ResidueField v.valuationSubring))
    (hF' : ∀a:A,residue v (algebraMap A L a) ∈ F') (N:ℕ) (hN:Module.finrank K' L≤N)
    (hNF: ∀n:ℕ,0<n→n≤N→(n:IsLocalRing.ResidueField v.valuationSubring) ≠ 0)
    (r:L) (hr:IsIntegral A r):
    IsSeparable F' (residue v r):=by
  classical
  have hr1:v r≤1:=ASC v hA hr
  let ρA:A→+*v.valuationSubring:=(algebraMap A L).codRestrict v.valuationSubring fun a=>
    (Valuation.mem_valuationSubring_iff _ _).2 (hA a)
  let ψ0:A→+*IsLocalRing.ResidueField v.valuationSubring:=
    (IsLocalRing.residue v.valuationSubring).comp ρA
  have hψ0: ∀a,ψ0 a=residue v (algebraMap A L a):=fun a=>(AJL v _ (hA a)).symm
  let φ:A→+*F' :=ψ0.codRestrict F' fun a=>by rw [hψ0];exact hF' a
  set f:=minpoly A r
  have hfm:f.Monic:=minpoly.monic hr
  have hfdeg:f.natDegree≤N:=by
    have h1:=minpoly.isIntegrallyClosed_eq_field_fractions' K' hr
    have h2:(minpoly K' r).natDegree≤Module.finrank K' L:=minpoly.natDegree_le r
    rw [h1,hfm.natDegree_map] at h2
    exact h2.trans hN
  set g:=f.map φ
  have hgm:g.Monic:=hfm.map φ
  have hg0:aeval (residue v r) g=0:=by
    have hcomp:(algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)).comp φ=ψ0:=by
      ext a;rfl
    rw [aeval_def,eval₂_map,hcomp,AJL v r hr1]
    change eval₂ ((IsLocalRing.residue v.valuationSubring).comp ρA)
      (IsLocalRing.residue v.valuationSubring ⟨r,hr1⟩) f=0
    rw [← hom_eval₂]
    have h0:eval₂ ρA ⟨r,(Valuation.mem_valuationSubring_iff _ _).2 hr1⟩ f=0:=by
      apply Subtype.ext
      have:=hom_eval₂ f ρA v.valuationSubring.subtype
        ⟨r,(Valuation.mem_valuationSubring_iff _ _).2 hr1⟩
      refine this.trans ?_
      exact minpoly.aeval A r
    rw [h0,map_zero]
  have hint:IsIntegral F' (residue v r):=⟨g,hgm,hg0⟩
  have hdvd:=minpoly.dvd F' (residue v r) hg0
  have hdeg:(minpoly F' (residue v r)).natDegree≤N:=
    (natDegree_le_of_dvd hdvd hgm.ne_zero).trans (by rw [hfm.natDegree_map];exact hfdeg)
  refine BQP (minpoly.irreducible hint) ?_
  intro h0
  apply hNF _ (minpoly.natDegree_pos hint) hdeg
  have:=congrArg (algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)) h0
  simpa using this

end Tame

section Engine

variable {K L:Type*} [Field K] [Field L] [Algebra K L] (v:Valuation L ℤᵐ⁰)
  (D:Derivation K L L)

theorem engine (k:IntermediateField K L) (hkv: ∀a ∈ k,a ≠ 0→v a=1) (Λ0:ℤ)
    (hkD: ∀a ∈ k,v (D a)≤exp Λ0) (s:L) (hs1:v s≤1) (hst:Transcendental k s)
    (b:L) (hgen: ∀E:Subfield L,(∀x ∈ k,x ∈ E)→s ∈ E→b ∈ E→ ∀x,x ∈ E)
    (P:L[X]) (hP0:P ≠ 0) (hPb:P.eval b=0)
    (hPc: ∀n,P.coeff n ∈ IntermediateField.adjoin k {s}) (N:ℕ) (hPN:P.natDegree≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0) (hπ: ∃x,v x=exp (-1)):
    (∃C,CrudeBound v D C)∧
      ∀s₀:L,Tame v D (exp Λ0) s₀→v (s-s₀)<1→NO v D (exp Λ0):=by
  classical
  let A:=Polynomial k
  letI:Algebra A L:=(Polynomial.aeval s).toRingHom.toAlgebra
  have hAmap: ∀a:A,algebraMap A L a=aeval s a:=fun _=>rfl
  have hinj:Function.Injective (algebraMap A L):=transcendental_iff_injective.1 hst
  haveI:FaithfulSMul A L:=(faithfulSMul_iff_algebraMap_injective A L).2 hinj
  let K' :=FractionRing A
  letI:Algebra K' L:=FractionRing.liftAlgebra A L
  have hAK' : ∀a:A,algebraMap K' L (algebraMap A K' a)=aeval s a:=fun a=>by
    rw [← IsScalarTower.algebraMap_apply];rfl
  have hrange: ∀x ∈ IntermediateField.adjoin k {s},∃y:K',algebraMap K' L y=x:=by
    intro x hx
    obtain ⟨r,t,rfl⟩:=(IntermediateField.mem_adjoin_simple_iff k x).1 hx
    exact ⟨algebraMap A K' r/algebraMap A K' t,by rw [map_div₀,hAK',hAK']⟩
  have hlift:P ∈ Polynomial.lifts (algebraMap K' L):=by
    rw [Polynomial.lifts_iff_coeff_lifts];intro n;exact hrange _ (hPc n)
  obtain ⟨P',hP'⟩:=(Polynomial.mem_lifts P).1 hlift
  have hP'0:P' ≠ 0:=by rintro rfl;exact hP0 (by rw [← hP',Polynomial.map_zero])
  have hP'b:aeval b P' =0:=by rw [aeval_def,← eval_map,hP'];exact hPb
  have hbint:IsIntegral K' b:=IsAlgebraic.isIntegral ⟨P',hP'0,hP'b⟩
  have hdegb:(minpoly K' b).natDegree≤N:=by
    refine (natDegree_le_of_dvd (minpoly.dvd K' b hP'b) hP'0).trans ?_
    rw [← natDegree_map_eq_of_injective (algebraMap K' L).injective,hP'];exact hPN
  have htop:IntermediateField.adjoin K' {b}= ⊤ :=by
    have hK'E: ∀y:K',algebraMap K' L y ∈ (IntermediateField.adjoin K' {b}).toSubfield:=
      fun y=>(IntermediateField.adjoin K' {b}).algebraMap_mem y
    have hall:=hgen (IntermediateField.adjoin K' {b}).toSubfield
      (fun x hx=>by
        have h1:=hAK' (Polynomial.C ⟨x,hx⟩)
        rw [aeval_C] at h1
        rw [← show algebraMap k L ⟨x,hx⟩=x from rfl,← h1];exact hK'E _)
      (by have h1:=hAK' Polynomial.X
          rw [aeval_X] at h1
          rw [← h1];exact hK'E _)
      (IntermediateField.subset_adjoin K' {b} (Set.mem_singleton b))
    exact eq_top_iff.2 fun x _=>hall x
  let e:IntermediateField.adjoin K' {b} ≃ₐ[K'] L:=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  haveI:FiniteDimensional K' (IntermediateField.adjoin K' {b}):=
    IntermediateField.adjoin.finiteDimensional hbint
  haveI:FiniteDimensional K' L:=e.toLinearEquiv.finiteDimensional
  have hfinrank:Module.finrank K' L≤N:=by
    rw [← e.toLinearEquiv.finrank_eq,IntermediateField.adjoin.finrank hbint];exact hdegb
  have hcharL: ∀n:ℕ,0<n→n≤N→(n:L) ≠ 0:=by
    intro n hn hnN h
    apply hNK n hn hnN
    rw [← map_natCast (algebraMap K L)] at h
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h
  haveI:Algebra.IsSeparable K' L:=⟨fun x=>by
    have hx:IsIntegral K' x:=Algebra.IsIntegral.isIntegral x
    refine BQP (minpoly.irreducible hx) fun h=> ?_
    refine hcharL _ (minpoly.natDegree_pos hx) ((minpoly.natDegree_le x).trans hfinrank) ?_
    have:=congrArg (algebraMap K' L) h
    rwa [map_natCast,map_zero] at this⟩

  have hkle: ∀a ∈ k,v a≤1:=by
    intro a ha
    by_cases h0:a=0
    · rw [h0,v.map_zero];exact zero_le
    · exact (hkv a ha h0).le
  set Λ1:ℤ:=max Λ0 (max 0 (v (D s)).log)
  have hAtame: ∀Λ:ℤ,Λ0≤Λ→Tame v D (exp Λ) s→ ∀a:A,Tame v D (exp Λ) (aeval s a):=by
    intro Λ hΛ hs a
    induction a using Polynomial.induction_on' with
    | add p q hp hq=>rw [map_add];exact (tameSubring v D _).add_mem hp hq
    | monomial n c=>
      rw [aeval_monomial]
      refine (tameSubring v D _).mul_mem ⟨hkle _ c.2,(hkD _ c.2).trans ?_⟩
        ((tameSubring v D _).pow_mem hs n)
      rw [exp_le_exp];exact hΛ
  have hsΛ1:Tame v D (exp Λ1) s:=
    ⟨hs1,(EYS v _).trans (by rw [exp_le_exp];exact le_max_right _ _)⟩
  have hA1: ∀a:A,Tame v D (exp Λ1) (algebraMap A L a):=
    hAtame Λ1 (le_max_left _ _) hsΛ1
  have hfrac:=FQL v A K' (fun a=>(hA1 a).1) hπ
  refine ⟨?_,fun s₀ hs₀ hss₀=> ?_⟩
  · obtain ⟨C,hC⟩:=GXV v D A K' Λ1 hA1
    refine ⟨C,EEO v D (tameSubring v D (exp C)) C (fun r hr=>hr)
      fun z hz=> ?_⟩
    obtain ⟨r,u,hr,hu,hu1,rfl⟩:=hfrac z hz
    exact ⟨r,hC r hr,u,hC u hu,hu1,rfl⟩
  · set S:Set L:=(k:Set L) ∪ {s₀}
    have hS: ∀z ∈ S,Tame v D (exp Λ0) z:=by
      rintro z (hz | hz)
      · exact ⟨hkle z hz,hkD z hz⟩
      · rw [Set.mem_singleton_iff.1 hz];exact hs₀
    set F' :=Subfield.closure (residue v '' S)
    have hs₀1:v s₀≤1:=hs₀.1
    have hress:residue v s=residue v s₀:=by
      have h1:v (s-s₀)≤1:=hss₀.le
      have h2:=residue_add v (s-s₀) s₀ h1 hs₀1
      rw [sub_add_cancel,(ZT v _ h1).2 hss₀,zero_add] at h2
      exact h2
    have hF' : ∀a:A,residue v (algebraMap A L a) ∈ F' :=by
      intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq=>
        rw [map_add,residue_add v _ _ (hA1 p).1 (hA1 q).1];exact F'.add_mem hp hq
      | monomial n c=>
        have hpow: ∀n:ℕ,v (s^n)≤1:=fun n=>by rw [v.map_pow];exact pow_le_one' hs1 n
        rw [hAmap,aeval_monomial]
        change residue v ((c:L)*s^n) ∈ F'
        rw [residue_mul v _ _ (hkle _ c.2) (hpow n)]
        refine F'.mul_mem (Subfield.subset_closure ⟨c,Or.inl c.2,rfl⟩) ?_
        induction n with
        | zero=>
          rw [pow_zero];exact Subfield.subset_closure ⟨1,Or.inl k.one_mem,rfl⟩
        | succ n ih=>
          rw [pow_succ,residue_mul v _ _ (hpow n) hs1,hress]
          exact F'.mul_mem ih (Subfield.subset_closure ⟨s₀,Or.inr rfl,rfl⟩)
    have hNF: ∀n:ℕ,0<n→n≤N→
        (n:IsLocalRing.ResidueField v.valuationSubring) ≠ 0:=by
      intro n hn hnN h
      have hvn:v (n:L)=1:=hkv _ (by
        rw [← map_natCast (algebraMap K L)];exact k.algebraMap_mem _) (hcharL n hn hnN)
      have h1:residue v (n:L)=0:=by
        rw [AJL v _ hvn.le,← h,← map_natCast (IsLocalRing.residue _)];rfl
      rw [ZT v _ hvn.le,hvn] at h1
      exact lt_irrefl _ h1
    have hsepres:=FIC v A K' (fun a=>(hA1 a).1) F' hF' N hfinrank hNF
    haveI:Algebra.IsSeparable F' (IsLocalRing.ResidueField v.valuationSubring):=⟨fun x=>by
      obtain ⟨z,rfl⟩:=IsLocalRing.residue_surjective x
      obtain ⟨r,u,hr,hu,hu1,hz⟩:=hfrac z z.2
      have hr1:v r≤1:=ASC v (fun a=>(hA1 a).1) hr
      have hu0:residue v u ≠ 0:=fun h=>
        (lt_irrefl (1:ℤᵐ⁰)) (hu1 ▸ (ZT v u hu1.le).1 h)
      have hzr:residue v (z:L)*residue v u=residue v r:=by
        rw [← residue_mul v _ _ z.2 hu1.le,hz,div_mul_cancel₀]
        intro h;rw [h,v.map_zero] at hu1;exact zero_ne_one hu1
      have hx:IsLocalRing.residue v.valuationSubring z=residue v r/residue v u:=by
        rw [eq_div_iff hu0,← hzr,AJL v _ z.2]
      rw [hx]
      exact (separableClosure F' _).div_mem (hsepres r hr) (hsepres u hu)⟩
    exact CXW v D (exp Λ0) S hS

end Engine

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open MvPolynomial

section Core

variable {K L:Type*} [Field K] [Field L] [Algebra K L]

theorem DTY {M:Type*} [AddCommMonoid M] (f:Fin 3→M) (i a c:Fin 3)
    (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c): ∑ m,f m=f i+f a+f c:=by
  rw [Fin.sum_univ_three]
  fin_cases i<;>fin_cases a<;>fin_cases c<;>simp at hia hic hac ⊢ <;>abel

theorem FKB {i a c m:Fin 3} (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c)
    (hma:m ≠ a) (hmc:m ≠ c):m=i:=by
  rw [ne_eq,Fin.ext_iff] at hia hic hac hma hmc
  have:=i.isLt;have:=a.isLt;have:=c.isLt;have:=m.isLt
  ext;omega

theorem FOI {R:Type*} [CommRing R] [Algebra K R] (F:MvPolynomial (Fin 4) K)
    (g:Fin 4→Polynomial R) (N:ℕ) (hN: ∀d ∈ F.support,d 1+d 2+d 3≤N)
    (h0:(g 0).natDegree=0) (h1: ∀m,(g m).natDegree≤1):(aeval g F).natDegree≤N:=by
  rw [aeval_def,eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le (s:=F.support) _ fun d hd=> ?_
  rw [Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hp: ∀m,(g m^d m).natDegree≤d m*(g m).natDegree:=fun m=>
    Polynomial.natDegree_pow_le
  refine (Finset.sum_le_sum fun m _=>hp m).trans ?_
  rw [Fin.sum_univ_four,h0,mul_zero,zero_add]
  refine le_trans ?_ (hN d hd)
  have e1:=Nat.mul_le_mul_left (d 1) (h1 1)
  have e2:=Nat.mul_le_mul_left (d 2) (h1 2)
  have e3:=Nat.mul_le_mul_left (d 3) (h1 3)
  simp only [mul_one] at e1 e2 e3
  omega

theorem ELD (F:MvPolynomial (Fin 4) K) (N:ℕ)
    (hN:weightedTotalDegree ![0,1,1,1] F≤N): ∀d ∈ F.support,d 1+d 2+d 3≤N:=by
  intro d hd
  refine le_trans (le_of_eq ?_) ((le_weightedTotalDegree _ hd).trans hN)
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_four]
  simp

theorem EER {ι R:Type*} [CommRing R] [Algebra K R] (w:ι→R)
    (hw:AlgebraicIndependent K w):
    Function.Injective (aeval (R:=K) (fun o:Option ι=>
      o.elim (Polynomial.X:Polynomial R) fun j=>Polynomial.C (w j))):=by
  have h:(aeval (R:=K) (fun o:Option ι=>o.elim (Polynomial.X:Polynomial R)
      fun j=>Polynomial.C (w j)):MvPolynomial (Option ι) K→ₐ[K] Polynomial R)=
      (Polynomial.mapAlgHom (aeval w)).comp (optionEquivLeft K ι).toAlgHom:=by
    apply MvPolynomial.algHom_ext
    rintro (_ | j)
    · simp [optionEquivLeft_X_none]
    · simp [optionEquivLeft_X_some]
  rw [h,AlgHom.coe_comp]
  exact (Polynomial.map_injective _ hw).comp (optionEquivLeft K ι).injective

noncomputable def subVals {M:Type*} [CommRing M] [Algebra K M] (q:Fin 3→Polynomial K)
    (a c:Fin 3) (x0 ℓ t z:M):Fin 4→M:=
  Fin.cons x0 fun m=>if m=a then t else if m=c then z else
    ℓ-Polynomial.aeval x0 (q a)*t-Polynomial.aeval x0 (q c)*z

theorem map_subVals {M M' :Type*} [CommRing M] [Algebra K M] [CommRing M'] [Algebra K M']
    (φ:M→ₐ[K] M') (q:Fin 3→Polynomial K) (a c:Fin 3) (x0 ℓ t z:M):
    (fun m=>φ (subVals q a c x0 ℓ t z m))=subVals q a c (φ x0) (φ ℓ) (φ t) (φ z):=by
  funext m
  refine Fin.cases ?_ (fun m=> ?_) m
  · rfl
  · simp only [subVals,Fin.cons_succ]
    split_ifs
    · rfl
    · rfl
    · simp only [map_sub,map_mul,Polynomial.aeval_algHom_apply]

theorem subVals_cons {M:Type*} [CommRing M] [Algebra K M] (q:Fin 3→Polynomial K)
    (i a c:Fin 3) (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c) (hqi:q i=1) (x0:M)
    (y:Fin 3→M):
    subVals q a c x0 (∑ m,Polynomial.aeval x0 (q m)*y m) (y a) (y c)=Fin.cons x0 y:=by
  funext m
  refine Fin.cases ?_ (fun m=> ?_) m
  · rfl
  · simp only [subVals,Fin.cons_succ]
    split_ifs with h1 h2
    · rw [h1]
    · rw [h2]
    · rw [FKB hia hic hac h1 h2,DTY _ i a c hia hic hac,hqi,map_one,
        one_mul]
      ring

theorem core_poly (F:MvPolynomial (Fin 4) K) (hF:F ≠ 0) (N:ℕ)
    (hN: ∀d ∈ F.support,d 1+d 2+d 3≤N) (x0:L) (x:Fin 3→L)
    (hFx:aeval (Fin.cons x0 x:Fin 4→L) F=0) (q:Fin 3→Polynomial K) (i a c:Fin 3)
    (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c) (hqi:q i=1)
    (hind:AlgebraicIndependent K (fun o:Option (Fin 2)=>
      o.elim (x a) ![∑ m,Polynomial.aeval x0 (q m)*x m,x0])):
    ∃P:Polynomial L,P ≠ 0∧P.eval (x c)=0∧P.natDegree≤N∧
      ∀n,P.coeff n ∈ Algebra.adjoin K {x0,∑ m,Polynomial.aeval x0 (q m)*x m,x a}:=by
  classical
  set ℓ:= ∑ m,Polynomial.aeval x0 (q m)*x m with hℓ
  set S:=Algebra.adjoin K ({x0,ℓ,x a}:Set L)
  set w:Option (Fin 2)→L:=fun o=>o.elim (x a) ![ℓ,x0]
  have hwS: ∀o,w o ∈ S:=by
    rintro (_ | j)
    · exact Algebra.subset_adjoin (by simp [w])
    · fin_cases j
      · exact Algebra.subset_adjoin (by simp [w])
      · exact Algebra.subset_adjoin (by simp [w])
  let wS:Option (Fin 2)→S:=fun o=>⟨w o,hwS o⟩
  have hwSind:AlgebraicIndependent K wS:=AlgebraicIndependent.of_comp S.val hind
  let V:Option (Option (Fin 2))→Polynomial S:=
    fun o=>o.elim Polynomial.X fun j=>Polynomial.C (wS j)
  let σv:Fin 4→MvPolynomial (Option (Option (Fin 2))) K:=
    subVals q a c (MvPolynomial.X (some (some 1))) (MvPolynomial.X (some (some 0))) (MvPolynomial.X (some none)) (MvPolynomial.X none)
  let τv:Option (Option (Fin 2))→MvPolynomial (Fin 4) K:=fun o=>
    o.elim (MvPolynomial.X c.succ) fun o' =>o'.elim (MvPolynomial.X a.succ)
      ![∑ m,Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) (q m)*MvPolynomial.X m.succ,MvPolynomial.X 0]
  have hτσ:(fun m=>aeval τv (σv m))=MvPolynomial.X:=by
    rw [map_subVals]
    simp only [aeval_X]
    rw [show τv (some (some 0))= ∑ m,Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) (q m)*
      (fun m:Fin 3=>(MvPolynomial.X m.succ:MvPolynomial (Fin 4) K)) m from rfl,
      show τv (some (some 1))=MvPolynomial.X 0 from rfl,show τv (some none)=MvPolynomial.X a.succ from rfl,
      show τv none=MvPolynomial.X c.succ from rfl]
    rw [subVals_cons q i a c hia hic hac hqi]
    funext m
    refine Fin.cases rfl (fun m=>rfl) m
  have hσF:aeval σv F ≠ 0:=by
    intro h
    apply hF
    have h1:=congrArg (aeval τv) h
    rw [comp_aeval_apply,map_zero,hτσ,aeval_X_left_apply] at h1
    exact h1
  set Q:Polynomial S:=aeval V (aeval σv F)
  have hQ0:Q ≠ 0:=fun h=>
    hσF (EER wS hwSind (h.trans (map_zero _).symm))
  have hSinj:Function.Injective (algebraMap S L):=Subtype.val_injective
  refine ⟨Q.map (algebraMap S L),?_,?_,?_,?_⟩
  · exact (Polynomial.map_ne_zero_iff hSinj).2 hQ0
  · rw [Polynomial.eval_map,← Polynomial.aeval_def]
    have h1:=comp_aeval_apply ((Polynomial.aeval (R:=S) (x c)).restrictScalars K) (f:=V)
      (aeval σv F)
    rw [AlgHom.restrictScalars_apply] at h1
    rw [show (Polynomial.aeval (x c)) Q=_ from h1,comp_aeval_apply,map_subVals]
    simp only [aeval_X]
    rw [← hFx,← subVals_cons q i a c hia hic hac hqi x0 x]
    simp only [V,Option.elim,AlgHom.restrictScalars_apply,Polynomial.aeval_C,
      Polynomial.aeval_X]
    rfl
  · rw [Polynomial.natDegree_map_eq_of_injective hSinj]
    change (aeval V (aeval σv F)).natDegree≤N
    rw [comp_aeval_apply,map_subVals]
    simp only [aeval_X]
    have hC: ∀j,(V (some j)).natDegree=0:=fun j=>Polynomial.natDegree_C _
    refine FOI F _ N hN (hC _) fun m=> ?_
    refine Fin.cases ((hC _).le.trans zero_le_one) (fun m=> ?_) m
    simp only [subVals,Fin.cons_succ]
    split_ifs
    · exact (hC _).le.trans zero_le_one
    · exact Polynomial.natDegree_X_le
    · have h1: ∀p:Polynomial K,(Polynomial.aeval (V (some (some 1))) p).natDegree=0:=
        fun p=>by
          rw [show V (some (some 1))=Polynomial.C (wS (some 1)) from rfl,
            ← Polynomial.algebraMap_eq (R:=S),Polynomial.aeval_algebraMap_apply,
            Polynomial.algebraMap_eq]
          exact Polynomial.natDegree_C _
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ((hC _).le.trans zero_le_one) ?_)) ?_)
      · exact Polynomial.natDegree_mul_le.trans (by rw [h1,hC];simp)
      · refine Polynomial.natDegree_mul_le.trans ?_
        rw [h1,zero_add];exact Polynomial.natDegree_X_le
  · intro n
    rw [Polynomial.coeff_map]
    exact (Q.coeff n).2

end Core

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section SliceField

variable {K:Type} [Field K] (F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)]

theorem slice_gen (E' :Subfield (SliceField F₀))
    (hK: ∀a:K,algebraMap K (SliceField F₀) a ∈ E') (hX:sliceProj F₀ (MvPolynomial.X 0) ∈ E')
    (hc: ∀j,sliceCoord F₀ j ∈ E'): ∀z,z ∈ E' :=by
  have hP: ∀P:MvPolynomial (Fin 4) K,sliceProj F₀ P ∈ E' :=by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a=>rw [sliceProj_C];exact hK a
    | add p q hp hq=>rw [map_add];exact E'.add_mem hp hq
    | mul_X p j hp=>
      rw [map_mul]
      refine E'.mul_mem hp ?_
      refine Fin.cases hX (fun m=>hc m) j
  intro z
  obtain ⟨r,s,-,rfl⟩:=IsFractionRing.div_surjective (A:=SliceRing F₀) z
  obtain ⟨P,rfl⟩:=Ideal.Quotient.mk_surjective r
  obtain ⟨Q,rfl⟩:=Ideal.Quotient.mk_surjective s
  exact E'.div_mem (hP P) (hP Q)

theorem aeval_slice (P:MvPolynomial (Fin 4) K):
    aeval (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀):Fin 4→SliceField F₀) P=
      sliceProj F₀ P:=by
  induction P using MvPolynomial.induction_on with
  | C a=>rw [aeval_C,sliceProj_C]
  | add p q hp hq=>rw [map_add,map_add,hp,hq]
  | mul_X p j hp=>
    rw [map_mul,map_mul,hp,aeval_X]
    congr 1
    refine Fin.cases rfl (fun m=>rfl) j

theorem DJT {L:Type*} [Field L] (v:Valuation L ℤᵐ⁰) {k:Type*}
    [Field k] [Algebra k L] (hk: ∀a:k,v (algebraMap k L a)≤1) {z:L} (hz0:z ≠ 0)
    (hz:IsAlgebraic k z):v z=1:=by
  have h1:=ASC v hk hz.isIntegral
  have h2:=ASC v hk (IsAlgebraic.inv_iff.2 hz).isIntegral
  rw [map_inv₀] at h2
  have hv0:v z ≠ 0:=(Valuation.ne_zero_iff v).2 hz0
  refine le_antisymm h1 ?_
  by_contra h
  rw [not_le] at h
  exact absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 hv0)).2 h))

theorem GYJ (p:Polynomial K):
    (Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) p).vars ⊆ {0}:=by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>rw [map_add];exact (vars_add_subset _ _).trans (Finset.union_subset hp hq)
  | monomial n a=>
    rw [Polynomial.aeval_monomial,algebraMap_eq]
    refine (vars_mul _ _).trans (Finset.union_subset (by rw [vars_C];exact Finset.empty_subset _) ?_)
    exact (vars_pow _ _).trans (by rw [vars_X])

theorem algInd_of_Y'_free (q:Fin 3→Polynomial K) (i a:Fin 3) (hia:i ≠ a) (hi1:i ≠ 1)
    (ha1:a ≠ 1) (hqi:q i=1) (hq1:q 1=0) (h2:(2:Fin 4) ∈ F₀.vars):
    AlgebraicIndependent K (fun o:Option (Fin 2)=>
      o.elim (sliceCoord F₀ a) ![sliceLinearL F₀ q,sliceProj F₀ (MvPolynomial.X 0)]):=by
  classical
  rw [algebraicIndependent_iff_injective_aeval,injective_iff_map_eq_zero]
  intro Q hQ
  set ℓp:MvPolynomial (Fin 4) K:=
    ∑ m,Polynomial.aeval (MvPolynomial.X 0) (q m)*MvPolynomial.X m.succ
  let ρv:Option (Fin 2)→MvPolynomial (Fin 4) K:=
    fun o=>o.elim (MvPolynomial.X a.succ) ![ℓp,MvPolynomial.X 0]
  have hfun:(fun o=>aeval (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀):
      Fin 4→SliceField F₀) (ρv o))=
      fun o=>o.elim (sliceCoord F₀ a) ![sliceLinearL F₀ q,sliceProj F₀ (MvPolynomial.X 0)]:=by
    funext o
    rcases o with _ | j
    · simp [ρv]
    · fin_cases j
      · show aeval (Fin.cons (sliceProj F₀ (MvPolynomial.X 0)) (sliceCoord F₀):
          Fin 4→SliceField F₀) ℓp=sliceLinearL F₀ q
        simp only [ℓp,map_sum,map_mul,← Polynomial.aeval_algHom_apply,aeval_X,Fin.cons_zero,
          Fin.cons_succ]
        rfl
      · simp [ρv]
  have hρ:sliceProj F₀ (aeval ρv Q)=0:=by
    rw [← aeval_slice,comp_aeval_apply,hfun,hQ]
  have hdvd:F₀ ∣ aeval ρv Q:=(BMJ F₀ _).1 hρ
  have hv:(2:Fin 4) ∉ (aeval ρv Q).vars:=by
    rw [aeval_eq_bind₁]
    intro hmem
    obtain ⟨o,-,ho⟩:=Finset.mem_biUnion.1 (vars_bind₁ _ _ hmem)
    rcases o with _ | j
    · rw [show ρv none=MvPolynomial.X a.succ from rfl,vars_X,Finset.mem_singleton] at ho
      exact ha1 (Fin.succ_injective _ (by simpa using ho.symm))
    · fin_cases j
      · have hsub:=vars_sum_subset (Finset.univ:Finset (Fin 3))
          (fun m=>Polynomial.aeval (MvPolynomial.X 0:MvPolynomial (Fin 4) K) (q m)*
            MvPolynomial.X m.succ)
        obtain ⟨m,-,hm⟩:=Finset.mem_biUnion.1 (hsub ho)
        rcases Finset.mem_union.1 (vars_mul _ _ hm) with h | h
        · have:=GYJ (q m) h
          simp at this
        · rw [vars_X,Finset.mem_singleton] at h
          have hm1:m=1:=Fin.succ_injective _ (by simpa using h.symm)
          subst hm1
          rw [hq1,map_zero,zero_mul,vars_0] at hm
          exact Finset.notMem_empty _ hm
      · simp [ρv] at ho
  have hzero:aeval ρv Q=0:=by
    obtain ⟨G,hG⟩:=hdvd
    by_contra hne
    have hG0:G ≠ 0:=by rintro rfl;rw [mul_zero] at hG;exact hne hG
    have hF0:F₀ ≠ 0:=(Fact.out:Irreducible F₀).ne_zero
    apply hv
    rw [hG,mem_vars_iff_degreeOf_ne_zero,degreeOf_mul_eq hF0 hG0]
    have:=mem_vars_iff_degreeOf_ne_zero.1 h2
    omega

  let τv:Fin 4→MvPolynomial (Option (Fin 2)) K:=Fin.cons (MvPolynomial.X (some 1))
    fun m=>if m=a then MvPolynomial.X none else if m=i then
      MvPolynomial.X (some 0)-Polynomial.aeval (MvPolynomial.X (some 1)) (q a)*
        MvPolynomial.X none else 0
  have hτρ: ∀o,aeval τv (ρv o)=MvPolynomial.X o:=by
    rintro (_ | j)
    · simp [ρv,τv]
    · fin_cases j
      · show aeval τv ℓp=MvPolynomial.X (some 0)
        simp only [ℓp,map_sum,map_mul,← Polynomial.aeval_algHom_apply,aeval_X]
        rw [DTY _ i a 1 hia hi1 ha1]
        have t1:τv i.succ=MvPolynomial.X (some 0)-
            Polynomial.aeval (MvPolynomial.X (some 1)) (q a)*MvPolynomial.X none:=by
          simp [τv,hia]
        have t2:τv a.succ=MvPolynomial.X none:=by simp [τv]
        have t0:τv 0=MvPolynomial.X (some 1):=rfl
        rw [t0,t1,t2,hqi,hq1,map_one,map_zero]
        simp
      · simp [ρv,τv]
  have h:=congrArg (aeval τv) hzero
  rw [comp_aeval_apply,show (fun o=>aeval τv (ρv o))=MvPolynomial.X from funext hτρ,
    aeval_X_left_apply,map_zero] at h
  exact h

end SliceField

section Slice

variable {K:Type} [Field K] {E:Type} [Field E] [Algebra (GenericField K) E]
  [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
  (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀:MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})

noncomputable abbrev kField (q:Fin 3→Polynomial K):IntermediateField K (SliceField F₀):=
  IntermediateField.adjoin K (Set.range ![sliceLinearL F₀ q,sliceProj F₀ (MvPolynomial.X 0)])

omit [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_aeval_X0 (p:Polynomial K):
    RY D F₀ hker (Polynomial.aeval (sliceProj F₀ (MvPolynomial.X 0)) p)=
      algebraMap E (AJ E D) (phiE K E p):=by
  refine Polynomial.induction_on p (fun a=> ?_) (fun p r hp hr=> ?_) (fun n a h=> ?_)
  · rw [Polynomial.aeval_C,psi_const]
  · rw [map_add,map_add,hp,hr,map_add,map_add]
  · rw [pow_succ,← mul_assoc,map_mul,map_mul,h,Polynomial.aeval_X,psi_X0]
    simp only [map_mul]

omit [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in

theorem psi_ell (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    RY D F₀ hker (sliceLinearL F₀ q)=
      algebraMap E (AJ E D) (sliceValue (GenericField K) E):=by
  have hev: ∀P:MvPolynomial (Fin 3) (GenericField K),
      aeval (coordinate E D) P=BR E D (CD (GenericField K) E P):=by
    intro P
    rw [HJ,CD,aeval_map_algebraMap]
  have hsl: ∑ m,algebraMap (GenericField K) (AJ E D) (c m)*coordinate E D m=
      algebraMap E (AJ E D) (sliceValue (GenericField K) E):=by
    have h1:=(ABU D _).2 hslice
    rw [map_sub,sub_eq_zero,← hev] at h1
    have h2:BR E D (MvPolynomial.C (sliceValue (GenericField K) E))=
        algebraMap E (AJ E D) (sliceValue (GenericField K) E):=
      (BR E D).commutes _
    rw [h2] at h1
    rw [h1]
    simp only [map_sum,map_mul,aeval_C,aeval_X]
  rw [sliceLinearL,map_sum,← hsl]
  refine Finset.sum_congr rfl fun m _=> ?_
  rw [map_mul,psi_aeval_X0,psi_coord,← hq m,
    IsScalarTower.algebraMap_apply (GenericField K) E (AJ E D)]
  rfl

omit [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_kField (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    ∀z ∈ kField F₀ q,RY D F₀ hker z ∈
      (algebraMap E (AJ E D)).fieldRange:=by
  let T:Subfield (SliceField F₀):=
    (algebraMap E (AJ E D)).fieldRange.comap (RY D F₀ hker)
  have hT:kField F₀ q≤T.toIntermediateField (fun a=>
      show RY D F₀ hker (algebraMap K _ a) ∈
        (algebraMap E (AJ E D)).fieldRange from by
      rw [psi_const];exact ⟨_,rfl⟩):=by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · show RY D F₀ hker (sliceLinearL F₀ q) ∈
        (algebraMap E (AJ E D)).fieldRange
      rw [psi_ell D F₀ hker c q hq hslice];exact ⟨_,rfl⟩
    · show RY D F₀ hker (sliceProj F₀ (MvPolynomial.X 0)) ∈
        (algebraMap E (AJ E D)).fieldRange
      rw [psi_X0];exact ⟨_,rfl⟩
  exact fun z hz=>hT hz

theorem GCL (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (ν:RCN026.Place E (AJ E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰)
    (he:1≤e) (hwve: ∀x,ν.val (RY D F₀ hker x)=v x^e):
    ∀z ∈ kField F₀ q,z ≠ 0→v z=1:=by
  intro z hz hz0
  obtain ⟨y,hy⟩:=psi_kField D F₀ hker c q hq hslice z hz
  have hy0:y ≠ 0:=by
    rintro rfl
    rw [map_zero,eq_comm,map_eq_zero_iff _ (RY D F₀ hker).injective] at hy
    exact hz0 hy
  have h1:ν.val (RY D F₀ hker z)=1:=by
    rw [← hy];exact (ν.property.2).eq_one y hy0
  rw [hwve] at h1
  have he0:e ≠ 0:=by omega
  exact le_antisymm ((DVA he0).1 h1.le)
    (not_lt.1 fun hlt=>absurd h1 (ne_of_lt ((DTJ he0).2 hlt)))

omit [D.IsPrime] [Fact (Irreducible F₀)] in
theorem DHY:
    letI:Algebra K E:=((phiE K E).comp Polynomial.C).toAlgebra
    Transcendental (Algebra.adjoin K (Set.range ![phiE K E Polynomial.X]))
      (sliceValue (GenericField K) E):=by
  letI:Algebra K E:=((phiE K E).comp Polynomial.C).toAlgebra
  rw [transcendental_iff]
  intro p hp
  have hsub: ∀y ∈ Algebra.adjoin K (Set.range ![phiE K E Polynomial.X]),
      y ∈ (algebraMap (GenericField K) E).range:=by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy=>
      obtain ⟨j,rfl⟩:=hy
      fin_cases j
      exact ⟨AL K Polynomial.X,rfl⟩
    | algebraMap r=>exact ⟨AL K (Polynomial.C r),rfl⟩
    | add y z _ _ hy hz=>exact (algebraMap (GenericField K) E).range.add_mem hy hz
    | mul y z _ _ hy hz=>exact (algebraMap (GenericField K) E).range.mul_mem hy hz
  have hlift:p.map (algebraMap (Algebra.adjoin K (Set.range ![phiE K E Polynomial.X])) E) ∈
      Polynomial.lifts (algebraMap (GenericField K) E):=by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact hsub _ (p.coeff n).2
  obtain ⟨p',hp'⟩:=(Polynomial.mem_lifts _).1 hlift
  have hp'0:p' =0:=by
    refine (transcendental_iff.1 (AMM (Ω:=GenericField K) (E:=E))) p' ?_
    rw [Polynomial.aeval_def,← Polynomial.eval_map,hp',Polynomial.eval_map,← Polynomial.aeval_def]
    exact hp
  rw [hp'0,Polynomial.map_zero,eq_comm,Polynomial.map_eq_zero_iff Subtype.val_injective] at hp'
  exact hp'

include hker in

theorem GWP (c:Fin 3→GenericField K) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    AlgebraicIndependent K ![sliceLinearL F₀ q,sliceProj F₀ (MvPolynomial.X 0)]:=by
  classical
  letI iKE:Algebra K E:=((phiE K E).comp Polynomial.C).toAlgebra
  have hφinj:Function.Injective (phiE K E):=
    (algebraMap (GenericField K) E).injective.comp (DI K)
  have hx:Transcendental K (phiE K E Polynomial.X):=by
    rw [transcendental_iff_injective]
    have: ∀p:Polynomial K,Polynomial.aeval (phiE K E Polynomial.X) p=phiE K E p:=by
      intro p
      rw [Polynomial.aeval_def]
      conv_rhs=>rw [← Polynomial.eval₂_C_X (p:=p)]
      rw [Polynomial.hom_eval₂]
      rfl
    intro p r h
    exact hφinj ((this p).symm.trans (h.trans (this r)))
  have h:=(AlgebraicIndependent.option_iff (x:= ![phiE K E Polynomial.X])
    (a:=sliceValue (GenericField K) E)).2
    ⟨algebraicIndependent_unique_type_iff.2 hx,DHY⟩
  have hE:AlgebraicIndependent K ![sliceValue (GenericField K) E,phiE K E Polynomial.X]:=by
    refine (algebraicIndependent_equiv' (finSuccEquiv 1) ?_).2 h
    funext j
    fin_cases j<;>rfl
  have hψQ: ∀Q,RY D F₀ hker
      (aeval ![sliceLinearL F₀ q,sliceProj F₀ (MvPolynomial.X 0)] Q)=
      algebraMap E (AJ E D)
        (aeval (R:=K) ![sliceValue (GenericField K) E,phiE K E Polynomial.X] Q):=by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a=>rw [aeval_C,aeval_C,psi_const];rfl
    | add p r hp hr=>rw [map_add,map_add,hp,hr,map_add,map_add]
    | mul_X p j hp=>
      rw [map_mul,map_mul,map_mul,hp,aeval_X,aeval_X,map_mul]
      congr 1
      fin_cases j
      · exact psi_ell D F₀ hker c q hq hslice
      · exact psi_X0 D F₀ hker
  rw [algebraicIndependent_iff_injective_aeval,injective_iff_map_eq_zero]
  rw [algebraicIndependent_iff_injective_aeval,injective_iff_map_eq_zero] at hE
  intro Q hQ
  refine hE Q ?_
  have h1:=hψQ Q
  rw [hQ,map_zero,eq_comm,map_eq_zero_iff _ (algebraMap E (AJ E D)).injective] at h1
  exact h1

end Slice

section Main

theorem exists_third (i a:Fin 3) (h:a ≠ i): ∃c,c ≠ i∧c ≠ a:=by
  revert h;revert i a;decide

theorem FVX (i:Fin 3): ∃a c:Fin 3,i ≠ a∧i ≠ c∧a ≠ c:=by
  revert i;decide

theorem GPD (i:Fin 3) (hi:i ≠ 1): ∃a:Fin 3,i ≠ a∧a ≠ 1:=by
  revert hi;revert i;decide

theorem split_sum' {K M:Type*} [Field K] [CommRing M] [Algebra K M] (q:Fin 3→Polynomial K)
    (i a c:Fin 3) (hia:i ≠ a) (hic:i ≠ c) (hac:a ≠ c) (hqi:q i=1) (z:M)
    (y:Fin 3→M):
    y i= ∑ m,Polynomial.aeval z (q m)*y m-Polynomial.aeval z (q a)*y a-
      Polynomial.aeval z (q c)*y c:=by
  rw [DTY _ i a c hia hic hac,hqi,map_one,one_mul];ring

variable {K:Type} [Field K] {E:Type} [Field E] [Algebra (GenericField K) E]
  [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

theorem hdefer_holds (F:MvPolynomial (Fin 4) K) (D:Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0):
    ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place E (AJ E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (RY D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (JJ F F₀ hdvd) C)∧
      NO v (JJ F F₀ hdvd)
        (exp (vpole v (JJ F F₀ hdvd (sliceLinearL F₀ q)))):=by
  intro F₀ _ hdvd hker ν e v he hvn hwve
  classical
  set Dd:=JJ F F₀ hdvd with hDd
  set X0:=sliceProj F₀ (MvPolynomial.X 0) with hX0
  set x:=sliceCoord F₀ with hx
  set ℓ:=sliceLinearL F₀ q with hℓ
  set k:=kField F₀ q with hk
  set Λ0:=vpole v (Dd ℓ) with hΛ0
  have hqi:q i=1:=DI K (by rw [hq,hci,map_one])
  have hH:sliceProj F₀ (polyH K F) ≠ 0:=by
    intro h
    apply hHD
    have h1:RY D F₀ hker (sliceProj F₀ (polyH K F))=0:=by rw [h,map_zero]
    rw [SR] at h1
    exact (ABU D _).1 h1
  have hF:F ≠ 0:=by rintro rfl;apply hHD;simp [polyH]
  have hkv: ∀z ∈ k,z ≠ 0→v z=1:=GCL D F₀ hker c q hq hslice ν e v he hwve
  have hkle: ∀z ∈ k,v z≤1:=fun z hz=>by
    by_cases h0:z=0
    · rw [h0,v.map_zero];exact zero_le
    · exact (hkv z hz h0).le
  have hkle' : ∀r:k,v (algebraMap k (SliceField F₀) r)≤1:=fun r=>hkle r r.2
  have hAI1:=GWP D F₀ hker c q hq hslice
  have hΛ0nn:0≤Λ0:=vpole_nonneg _ _
  have hℓk:ℓ ∈ k:=IntermediateField.subset_adjoin K _ ⟨0,rfl⟩
  have hX0k:X0 ∈ k:=IntermediateField.subset_adjoin K _ ⟨1,rfl⟩
  have hkT: ∀z ∈ k,Tame v Dd (exp Λ0) z:=by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem z hz=>
      obtain ⟨j,rfl⟩:=hz
      fin_cases j
      · exact ⟨hkle _ hℓk,AQZ v _⟩
      · refine ⟨hkle _ hX0k,?_⟩
        show v (Dd X0)≤_
        rw [hDd,DMP F F₀ hdvd hH,v.map_one,← exp_zero,exp_le_exp]
        exact hΛ0nn
    | algebraMap r=>
      refine ⟨hkle _ (k.algebraMap_mem r),?_⟩
      rw [Derivation.map_algebraMap,v.map_zero];exact zero_le
    | add z w _ _ hz hw=>exact (tameSubring v Dd _).add_mem hz hw
    | mul z w _ _ hz hw=>exact (tameSubring v Dd _).mul_mem hz hw
    | inv z hzk hz=>
      by_cases h0:z=0
      · rw [h0,inv_zero];exact (tameSubring v Dd _).zero_mem
      · exact tame_inv v Dd _ z hz (hkv z hzk h0)
  have hkD: ∀z ∈ k,v (Dd z)≤exp Λ0:=fun z hz=>(hkT z hz).2
  have hN' :=ELD F N hN
  have hFx:aeval (Fin.cons X0 x:Fin 4→SliceField F₀) F=0:=by
    rw [aeval_slice];exact (BMJ F₀ F).2 hdvd
  have haevk: ∀p:Polynomial K,Polynomial.aeval X0 p ∈ k:=by
    intro p
    have h1:=Polynomial.aeval_algebraMap_apply (SliceField F₀) (⟨X0,hX0k⟩:k) p
    rw [show algebraMap k (SliceField F₀) ⟨X0,hX0k⟩=X0 from rfl] at h1
    rw [h1];exact (Polynomial.aeval (⟨X0,hX0k⟩:k) p).2

  have key: ∀a c',i ≠ a→i ≠ c' →a ≠ c' →
      AlgebraicIndependent K (fun o:Option (Fin 2)=>o.elim (x a) ![ℓ,X0])→
      ∀s:SliceField F₀,(s=x a∨s*x a=1)→v s≤1→
      ∀s₀,Tame v Dd (exp Λ0) s₀→v (s-s₀)<1→
      (∃C,CrudeBound v Dd C)∧NO v Dd (exp Λ0):=by
    intro a c' hia hic hac hind s hs hs1 s₀ hs₀ hss₀
    obtain ⟨P,hP0,hPb,hPN,hPc⟩:=
      core_poly F hF N hN' X0 x hFx q i a c' hia hic hac hqi hind
    have htr:Transcendental k (x a):=
      IntermediateField.transcendental_adjoin_iff.2 (AlgebraicIndependent.option_iff.1 hind).2
    have hinv:s*x a=1→x a=s⁻¹:=fun h=>eq_inv_of_mul_eq_one_right h
    have hxa:x a ∈ IntermediateField.adjoin k {s}:=by
      rcases hs with rfl | hs
      · exact IntermediateField.mem_adjoin_simple_self k _
      · rw [hinv hs];exact inv_mem (IntermediateField.mem_adjoin_simple_self k s)
    have hst:Transcendental k s:=by
      rcases hs with rfl | hs
      · exact htr
      · have h1:s=(x a)⁻¹:=by rw [hinv hs,inv_inv]
        rw [h1];exact fun h=>htr (IsAlgebraic.inv_iff.1 h)
    have hkin: ∀z ∈ k,z ∈ IntermediateField.adjoin k {s}:=fun z hz=>
      (IntermediateField.adjoin k {s}).algebraMap_mem ⟨z,hz⟩
    have hPc' : ∀n,P.coeff n ∈ IntermediateField.adjoin k {s}:=by
      intro n
      have hle:Algebra.adjoin K {X0,ℓ,x a}≤
          ((IntermediateField.adjoin k {s}).restrictScalars K).toSubalgebra:=by
        rw [Algebra.adjoin_le_iff]
        rintro z (rfl | rfl | rfl)
        · exact hkin _ hX0k
        · exact hkin _ hℓk
        · exact hxa
      exact hle (hPc n)
    have hgen: ∀E' :Subfield (SliceField F₀),(∀z ∈ k,z ∈ E')→s ∈ E' →x c' ∈ E' →
        ∀z,z ∈ E' :=by
      intro E' hkE hsE hcE
      have haE:x a ∈ E' :=by
        rcases hs with rfl | hs
        · exact hsE
        · rw [hinv hs];exact E'.inv_mem hsE
      refine slice_gen F₀ E' (fun r=>hkE _ (k.algebraMap_mem r)) (hkE _ hX0k) fun j=> ?_
      by_cases hja:j=a
      · rw [hja];exact haE
      by_cases hjc:j=c'
      · rw [hjc];exact hcE
      rw [FKB hia hic hac hja hjc]
      change x i ∈ E'
      rw [split_sum' q i a c' hia hic hac hqi X0 x]
      exact E'.sub_mem (E'.sub_mem (hkE _ hℓk) (E'.mul_mem (hkE _ (haevk _)) haE))
        (E'.mul_mem (hkE _ (haevk _)) hcE)
    have hen:=engine v Dd k hkv Λ0 hkD s hs1 hst (x c') hgen P hP0 hPb hPc' N hPN hNK hvn
    exact ⟨hen.1,hen.2 s₀ hs₀ hss₀⟩
  obtain ⟨π,hπ⟩:=hvn
  by_cases hinf: ∃j,j ≠ i∧1<v (x j)
  ·
    obtain ⟨a,hai,ha⟩:=hinf
    obtain ⟨c',hci',hca⟩:=exists_third i a hai
    have hxa0:x a ≠ 0:=by
      intro h;rw [h,v.map_zero] at ha;exact not_lt.2 zero_le ha
    have htr:Transcendental k (x a):=fun halg=>
      (ne_of_gt ha) (DJT v hkle' hxa0 halg)
    have hind:=AlgebraicIndependent.option_iff.2
      ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 htr⟩
    have hvs:v (x a)⁻¹<1:=by
      rw [map_inv₀];exact inv_lt_one_of_one_lt₀ ha
    refine key a c' (Ne.symm hai) (Ne.symm hci') (Ne.symm hca) hind (x a)⁻¹
      (Or.inr (inv_mul_cancel₀ hxa0)) hvs.le 0 (tameSubring v Dd _).zero_mem (by rwa [sub_zero])

  push Not at hinf
  obtain ⟨a1,a2,h1,h2,h12⟩:=FVX i
  have hall: ∀j,v (x j)≤1:=by
    intro j
    by_cases hji:j=i
    · rw [hji,split_sum' q i a1 a2 h1 h2 h12 hqi X0 x]
      have hq' : ∀m,v (Polynomial.aeval X0 (q m))≤1:=fun m=>hkle _ (haevk _)
      refine (v.map_sub _ _).trans (max_le ((v.map_sub _ _).trans (max_le (hkle _ hℓk) ?_)) ?_)
      · rw [v.map_mul];exact mul_le_one' (hq' _) (hinf a1 (Ne.symm h1))
      · rw [v.map_mul];exact mul_le_one' (hq' _) (hinf a2 (Ne.symm h2))
    · exact hinf j hji
  have htame: ∀a:Fin 3,a ≠ 1→Tame v Dd (exp Λ0) (x a):=by
    intro a ha1
    refine ⟨hall a,?_⟩
    fin_cases a
    · show v (Dd (sliceCoord F₀ 0))≤_
      rw [hDd,ATS F F₀ hdvd hH]
      exact (hall 1).trans (by rw [← exp_zero,exp_le_exp];exact hΛ0nn)
    · exact absurd rfl ha1
    · show v (Dd (sliceCoord F₀ 2))≤_
      rw [hDd,ATX F F₀ hdvd hH,v.map_zero];exact zero_le
  have hself: ∀a:Fin 3,v (x a-x a)<1:=fun a=>by
    rw [sub_self,v.map_zero];exact zero_lt_one
  by_cases hi1:i=1
  · subst hi1
    by_cases ht0:Transcendental k (x 0)
    · exact key 0 2 (by decide) (by decide) (by decide) (AlgebraicIndependent.option_iff.2
        ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 ht0⟩) (x 0) (Or.inl rfl) (hall 0)
        (x 0) (htame 0 (by decide)) (hself 0)
    by_cases ht2:Transcendental k (x 2)
    · exact key 2 0 (by decide) (by decide) (by decide) (AlgebraicIndependent.option_iff.2
        ⟨hAI1,IntermediateField.transcendental_adjoin_iff.1 ht2⟩) (x 2) (Or.inl rfl) (hall 2)
        (x 2) (htame 2 (by decide)) (hself 2)
    exfalso
    have hA: ∀z,z ∈ (algebraicClosure k (SliceField F₀)).toSubfield:=by
      have hkA: ∀z ∈ k,z ∈ (algebraicClosure k (SliceField F₀)).toSubfield:=fun z hz=>
        mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap (⟨z,hz⟩:k))
      set A:=(algebraicClosure k (SliceField F₀)).toSubfield
      have h0:x 0 ∈ A:=mem_algebraicClosure_iff.2 (not_not.1 ht0)
      have h2' :x 2 ∈ A:=mem_algebraicClosure_iff.2 (not_not.1 ht2)
      refine slice_gen F₀ A (fun r=>hkA _ (k.algebraMap_mem r)) (hkA _ hX0k) fun j=> ?_
      fin_cases j
      · exact h0
      · change x 1 ∈ A
        rw [split_sum' q 1 0 2 (by decide) (by decide) (by decide) hqi X0 x]
        exact A.sub_mem (A.sub_mem (hkA _ hℓk) (A.mul_mem (hkA _ (haevk _)) h0))
          (A.mul_mem (hkA _ (haevk _)) h2')
      · exact h2'
    have hπ0:π ≠ 0:=by rintro rfl;rw [v.map_zero] at hπ;exact exp_ne_zero hπ.symm
    have h1:=DJT v hkle' hπ0 (mem_algebraicClosure_iff.1 (hA π))
    rw [hπ,← exp_zero,exp_inj] at h1
    omega
  · have hq10:q 1=0:=hq1.resolve_left hi1
    have h2vars:(2:Fin 4) ∈ F₀.vars:=by
      obtain ⟨F₁,hF₁⟩:=FKE F F₀ hdvd
      by_contra h
      rw [pderiv_eq_zero_of_notMem_vars h,map_zero,mul_zero] at hF₁
      exact hH hF₁
    obtain ⟨a,hia,ha1⟩:=GPD i hi1
    exact key a 1 hia hi1 ha1 (algInd_of_Y'_free F₀ q i a hia hi1 ha1 hqi hq10 h2vars) (x a)
      (Or.inl rfl) (hall a) (x a) (htame a ha1) (hself a)

end Main

end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
noncomputable section
set_option autoImplicit false

section Gaps
variable {K:Type} [Field K] {E:Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

theorem hdefer_gap (F:MvPolynomial (Fin 4) K) (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hq: ∀m,AL K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0):
    ∀(F₀:MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd:F₀ ∣ F)
      (hker:RingHom.ker (sliceMap (K:=K) D)=Ideal.span {F₀})
      (ν:RCN026.Place E (AJ E D)) (e:ℕ) (v:Valuation (SliceField F₀) ℤᵐ⁰),
      1≤e→(∃x,v x=exp (-1))→
      (∀x,ν.val (RY D F₀ hker x)=v x^e)→
      (∃C,CrudeBound v (JJ F F₀ hdvd) C)∧
      NO v (JJ F F₀ hdvd)
        (exp (vpole v (JJ F F₀ hdvd (sliceLinearL F₀ q)))):=
  hdefer_holds F D hHD c i hci q hq hq1 hslice N hN hNK

theorem hchar_gap [CharP K 2130706433] (F:MvPolynomial (Fin 4) K)
    (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep:BP D)
    (hFD:surfaceMap (phiE K E) F ∈ D) (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D)
    (N:ℕ) (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N) (hN9:N≤9678):
    ∀ν:RCN026.Place E (AJ E D),∀n:ℕ,0<n→
      (n:ℤ)≤max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (AJ E D) ν
          (CT.GP (phiE K E) D (polyH K F)))→(n:K) ≠ 0:=
  hchar_holds F D sep hFD hHD c i hci hslice N hN hN9

end Gaps

section Stage
open HK PR FA
variable {K I:Type} [Field K] [CharP K 2130706433]
  {Gamma:Finset K} {x:I→K} {flag:FlagDegree} {errorCap:ℕ}
  [CharP (GenericField K) 2130706433]





end Stage

end
end HFree6812

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace HFreeDir6813
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open DX BX FR
open VI BIZ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

section Flags
local notation "w" =>RCN326.w

theorem flag_eq_iff (p q:FlagDegree):
    p=q ↔ p.zOnly=q.zOnly∧p.yz=q.yz∧p.all=q.all:=by
  cases p;cases q;simp

def cuspFlag (d:Fin 3) (r v z:ℕ):FlagDegree:=
  ![⟨2*z,2*v-3-(7-2*r),2*r-7⟩,⟨2*z,2*v-(7-2*r),2*r-7⟩,⟨2*z,2*v-3,2*r-4⟩] d

def capFlag (d:Fin 3) (r:ℕ):FlagDegree:=
  ![⟨0,3+(7-2*r),5-(7-2*r)⟩,⟨0,7-2*r,5-(7-2*r)⟩,⟨0,3,2⟩] d

theorem cusp_add_cap (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v):
    cuspFlag d r v z+capFlag d r=2 • (⟨z,v,r-1⟩:FlagDegree):=by
  rw [flag_eq_iff]
  fin_cases d<;>simp [cuspFlag,capFlag]<;>omega

theorem FHA {L:Type*} [Field L] (V:Valuation L (WithZero (Multiplicative ℤ)))
    (x:Fin 3→L) (d:Fin 3) (r:ℕ) (hr:3≤r):
    flagPole V x (capFlag d r)≤flagPole V x (HFree6812.infCap d):=by
  have h1:0≤RCN187.poleOrder V (x 0):=le_max_left _ _
  have h2:=le_max_right (RCN187.poleOrder V (x 1))
    (max (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2)))
  have h3:=le_max_left (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2))
  rcases (show r=3∨7-2*r=0 by omega) with rfl | h0
  · fin_cases d<;>simp [flagPole,capFlag,HFree6812.infCap]<;>omega
  · fin_cases d<;>simp [flagPole,capFlag,HFree6812.infCap,h0]

def hfreeFlagDir (d:Fin 3) (r v z:ℕ) (C0:FlagDegree):FlagDegree:=
  (w+1) • cuspFlag d r v z+3 • C0

end Flags

section Slice
local notation "w" =>RCN326.w
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]

structure APH (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 Cap:FlagDegree):Prop where
  pole_le: ∀W:Finset (Place E (AJ E C)),
    3*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)))≤
    ∑ nu ∈ W,(((w+1:ℕ):ℤ)*
      (4*RCN064.KS C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu+
        2*RCN026.zeroOrder E (AJ E C) nu
          (CT.GP phi C (polyH K F))-
        flagPole nu.val (coordinate E C) Cap)+
      3*flagPole nu.val (coordinate E C) C0)

theorem EHO
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:BP C)
    (P:Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hF:surfaceMap phi F ∈ C)
    (hH:surfaceMap phi (polyH K F) ∉ C)
    (hlead:surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv: ∀j≤k,F ∣ helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE F (r:ℤ))
    (hYR:WeightBound BC F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hbudget:APH phi F C C0 (HFree6812.infCap d))
    (CX CV:ℕ)
    (hXbudget: ∀W:Finset (Place E (AJ E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C) (hfreeFlagDir d r v z C0))≤(CX:ℤ))
    (hVbudget: ∀W:Finset (Place E (AJ E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C)
        (EJ.budgetFlag B U T (k+1) n0))≤(CV:ℤ))
    (W:Finset (Place E (AJ E C))):
    ((3*(k+1):ℕ):ℤ)*(∑ nu ∈ W,RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)))≤
      ((k+1:ℕ):ℤ)*(CX:ℤ)+((4*(w+1):ℕ):ℤ)*(CV:ℤ):=by
  letI:=IP E C base.index
  letI:=DT E C base.index base.transcendental
  letI:=IU E C base.index
  letI:=_Q5 E C base.index base.transcendental
  letI:=IS E C base.index base.transcendental
  letI:FiniteDimensional (RatFunc E) (AJ E C):=base.finite
  letI:Algebra.IsSeparable (RatFunc E) (AJ E C):=base.separable
  let L:=AJ E C
  let ev:=CT.GP phi C
  let H:=ev (polyH K F)
  let sigma:=ev (polyG K F)/H
  let theta:=fun nu:Place E L=>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag+RCN187.poleOrder nu.val sigma)
  let Hf:FlagDegree:=⟨z,v,r-1⟩
  have hHne:H ≠ 0:=by
    intro hz
    apply hH
    exact (CT.AAE C _).mp hz
  let Pl:=RCN026.placesFor E L H hHne
  set W' :=W ∪ Pl with hW'

  have hdeg:=CT.ELO phi C P hlead
  have hroot:=CT.FKC phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree:n0≤(CT.AGC phi C P).natDegree:=by
    rw [hdeg.2]
    exact hn
  have hs:=EJ.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (BZJ.DVE _ P B U T hP)
    (coordinate E C) (CT.AGC phi C P)
    (CT.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV:ℤ) hVbudget W'
  have hsource:((k+1:ℕ):ℤ)*(∑ nu ∈ W',theta nu)≤(CV:ℤ):=by
    simpa only [CWV.pole_half _ h2,theta,sigma,H,ev,
      CT.GP,RCN064.movingRatio,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hs
  have htarget:(∑ nu ∈ W',RCN064.KS C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu)= ∑ nu ∈ W',theta nu:=by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta,RCN204.BPD,RCN204.CWP]
    rfl

  have hHF:=(JE.BNS phi F r v z (by omega) (by omega)
    hR hYR hAll).1
  have hpoleH (nu:Place E L):
      RCN346.poleOrder E L nu H≤flagPole nu.val (coordinate E C) Hf:=by
    apply BIH nu.val _ _ (RCN204.ALZ _ _ _)
    have h:=RCN204.ADJ nu.val (algebraMap E L)
      (RCN344.NP E L nu) (coordinate E C) Hf _ hHF
    simpa only [H,ev,CT.GP,
      HJ,MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h
  have hzero:(∑ nu ∈ W',RCN026.zeroOrder E L nu H)≤
      ∑ nu ∈ W',flagPole nu.val (coordinate E C) Hf:=by
    have hout: ∀nu ∈ W'.filter (fun nu=>nu ∉ Pl),RCN026.zeroOrder E L nu H=0:=by
      intro nu hnu
      have hno:RCN026.order E L nu H=0:=by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.ALB E L H hHne nu hne)
      simp only [RCN026.zeroOrder,hno,max_self]
    calc
      _=(∑ nu ∈ W'.filter (fun nu=>nu ∈ Pl),RCN026.zeroOrder E L nu H)+
          ∑ nu ∈ W'.filter (fun nu=>nu ∉ Pl),RCN026.zeroOrder E L nu H:=
        (Finset.sum_filter_add_sum_filter_not W' _ _).symm
      _= ∑ nu ∈ W'.filter (fun nu=>nu ∈ Pl),RCN026.zeroOrder E L nu H:=by
        rw [Finset.sum_eq_zero hout,add_zero]
      _≤ ∑ nu ∈ Pl,RCN026.zeroOrder E L nu H:=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu=>(Finset.mem_filter.mp hnu).2)
          (fun nu _ _=>RCN026.AUU E L nu H)
      _= ∑ nu ∈ Pl,RCN346.poleOrder E L nu H:=RCN026.AJO E L H hHne
      _≤ ∑ nu ∈ Pl,flagPole nu.val (coordinate E C) Hf:=Finset.sum_le_sum (fun nu _=>hpoleH nu)
      _≤_:=Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun nu _ _=>RCN204.ALZ nu.val (coordinate E C) Hf)

  have hcusp:2*(∑ nu ∈ W',flagPole nu.val (coordinate E C) Hf)≤
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlag d r v z))+
        ∑ nu ∈ W',flagPole nu.val (coordinate E C) (HFree6812.infCap d):=by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun nu _=> ?_
    have e1:=congrArg (flagPole nu.val (coordinate E C)) (cusp_add_cap d r v z hr hv)
    rw [RCN204.flagPole_add,RCN204.DZP] at e1
    have e2:=FHA nu.val (coordinate E C) d r hr
    push_cast at e1
    linarith
  have hX:=hXbudget W'
  simp only [hfreeFlagDir,RCN204.flagPole_add,RCN204.DZP,Finset.sum_add_distrib,
    ← Finset.mul_sum] at hX
  have hb:=hbudget.pole_le W'
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hb
  rw [htarget] at hb
  have hWW:(∑ nu ∈ W,RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)))≤
      ∑ nu ∈ W',RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)):=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun nu _ _=>le_max_left _ _)
  push_cast at hb hsource hX ⊢
  have hk:(0:ℤ)≤(k:ℤ)+1:=by positivity
  have hw:(0:ℤ)≤(w:ℤ)+1:=by positivity
  have e0:=mul_le_mul_of_nonneg_left (show
    2*(∑ nu ∈ W',RCN026.zeroOrder E L nu H)≤
      (∑ nu ∈ W',flagPole nu.val (coordinate E C) (cuspFlag d r v z))+
        ∑ nu ∈ W',flagPole nu.val (coordinate E C) (HFree6812.infCap d) by linarith) hw
  have hb' :3*(∑ nu ∈ W',RCN187.poleOrder nu.val
      (CT.GP phi C (MN F (w-1))/
        CT.GP phi C (polyH K F)^(2*w-1)))≤
      4*((w:ℤ)+1)*(∑ nu ∈ W',theta nu)+(CX:ℤ):=by
    nlinarith
  have e1:=mul_le_mul_of_nonneg_left hb' hk
  have e2:=mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num:(0:ℤ)≤4) hw)
  have e3:=mul_le_mul_of_nonneg_left hWW (mul_nonneg (by norm_num:(0:ℤ)≤3) hk)
  nlinarith

end Slice

section Stage
local notation "w" =>RCN326.w
variable {K I E T:Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap:ℕ}
  {stageSupport:RCN275.BT}
local notation "Ω" =>GenericField K
local notation "PE" =>MvPolynomial (Fin 3) E
local notation "φE" =>RingHom.comp (algebraMap (GenericField K) E) (AL K)

theorem CXB [Fintype T] [Nonempty T]
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (old:T→CM S)
    (emb: ∀i,AJ Ω (old i).1→ₐ[Ω] E)
    (hinj:Function.Injective (fun i=>GM (old i).1 (emb i)))
    (D:Ideal PE) [D.IsPrime] (sep:BP D)
    (hpoint: ∀i,D≤RingHom.ker
      (MvPolynomial.aeval (GM (old i).1 (emb i)):PE→ₐ[E] E).toRingHom)
    (hcarrier:CD Ω E S.G ∈ D)
    (hisolated:CD Ω E
      (_Q2 (AL K) S.F (w+1)) ∉ D)
    (P:Poly (K:=K)) (B U L s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L)
    (hBU:B≤U) (hUL:U≤L) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hlead: ∀i,surfaceMap (AL K) (asS P).leadingCoeff ∉ (old i).1)
    (hdiv: ∀j≤k,S.F ∣ helper P S.F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE S.F (r:ℤ))
    (hYR:WeightBound BC S.F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT S.F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree)
    (hbudget:surfaceMap φE S.F ∈ D→surfaceMap φE (polyH K S.F) ∉ D→
      APH φE S.F D C0 (HFree6812.infCap d))
    (CX CV:ℕ)
    (hXbudget: ∀W:Finset (Place E (AJ E D)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E D) (hfreeFlagDir d r v z C0))≤(CX:ℤ))
    (hVbudget: ∀W:Finset (Place E (AJ E D)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E D)
        (EJ.budgetFlag B U L (k+1) n0))≤(CV:ℤ)):
    3*(k+1)*(∑ i,FO S (DN S hproper) (old i))≤
      (k+1)*CX+4*(w+1)*CV:=by
  apply CBG.EBF S hproper old emb hinj D sep
    hpoint hcarrier hisolated (2*w-1) (3*(k+1)) ((k+1)*CX+4*(w+1)*CV)
  intro hFd hHd hnot W
  have hs:=EHO φE S.F D sep P B U L s k n0 hS hP hBU hUL hdn hB hn
    hFd hHd (hnot _ hlead) hdiv h2 hfact d r v z hr hv hR hYR hAll C0
    (hbudget hFd hHd) CX CV hXbudget hVbudget W
  simpa only [Nat.cast_add,Nat.cast_mul] using hs

variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

def CTP (F:MvPolynomial (Fin 4) K) (ell:MvPolynomial (Fin 3) Ω)
    (C0:FlagDegree) (d:Fin 3):Prop:=
  ∀(D:Ideal PE) [D.IsPrime],BP D→
    surfaceMap φE F ∈ D→OP.AWE (E:=E) ell ∈ D→
    surfaceMap φE (polyH K F) ∉ D→APH φE F D C0 (HFree6812.infCap d)

theorem EWL
    (S:Stage K I Gamma x p flag errorCap stageSupport)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (ell:MvPolynomial (Fin 3) Ω)
    (P:Poly (K:=K)) (B U L s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤L)
    (hBU:B≤U) (hUL:U≤L) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(asS P).natDegree)
    (hdiv: ∀j≤k,S.F ∣ helper P S.F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (d:Fin 3) (r v z:ℕ) (hr:3≤r) (hv:2≤v)
    (hR:WeightBound BE S.F (r:ℤ))
    (hYR:WeightBound BC S.F ((r+v:ℕ):ℤ))
    (hAll:WeightBound AT S.F ((r+v+z:ℕ):ℤ))
    (C0:FlagDegree) (hH:CTP (E:=E) S.F ell C0 d):
    ABB.SliceCharge (E:=E) S hproper
      (fun C=>surfaceMap (AL K) (asS P).leadingCoeff ∉ C.1)
      (OP.AWE (E:=E) ell) (3*(k+1)) (k+1) (4*(w+1))
      (hfreeFlagDir d r v z C0) (EJ.budgetFlag B U L (k+1) n0):=
  fun _ _ _ old hlead emb hinj D _ sep hpt hcar hN hA CX CV hX hV=>
    CXB S hproper old emb hinj D sep hpt hcar hA
      P B U L s k n0 hS hP hBU hUL hdn hB hn hlead hdiv h2 hfact d r v z hr hv hR hYR hAll C0
      (fun hFd hHd=>hH D sep hFd hN hHd) CX CV hX hV

end Stage

section Retained
open HK PR FA
open RCN046 RCN084 RCN085 RCN159 RCN198 RCN199 RCN206 RCN207 RCN237 RCN238 RCN243
open RCN263 RCN264 RCN271 RCN275 RCN287 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339
open RCN340 RCN344
open GJ JN IB
open ID BD
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap:ℕ}
local notation "Ω" =>GenericField K

def DGR {t y r:ℕ}
    (S:FH (AL K) Gamma x p errorCap flag w (cellSupport t y r)):
    Prop:=
  ∀hproper hflagChar hmixedRed (j:Fin 3),
    CTP (E:=AlgebraicClosure (RatFunc Ω)) S.F
      (channel S hproper hflagChar hmixedRed j) unitAllFlag j

def ASY (t y r:ℕ) (j:Fin 3):FlagDegree:=
  hfreeFlagDir j r (y-r) (t-y) unitAllFlag

def numeratorDir {F:MvPolynomial (Fin 4) K} (source:Fin 3→Source F)
    (scale t y r:ℕ) (flag:FlagDegree):ℕ:=
  ∑ j:Fin 3,(scale/3*weight (cellNormal t y r) j*
      flagMixed flag (ASY t y r j) (BD.direction j)+
    (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (BD.direction j) (source j).flag)

theorem EHQ {J:Type*} [Fintype J] {F:MvPolynomial (Fin 4) K}
    (source:Fin 3→Source F) (scale t y r:ℕ) (flags:J→FlagDegree) (total:FlagDegree)
    (hs:(∑ i,(flags i).all)≤total.all)
    (hm:(∑ i,((flags i).yz+(flags i).all))≤total.yz+total.all)
    (ht:(∑ i,((flags i).zOnly+(flags i).yz+(flags i).all))≤
      total.zOnly+total.yz+total.all):
    (∑ i,numeratorDir source scale t y r (flags i))≤numeratorDir source scale t y r total:=by
  have hfirst (j:Fin 3):=RCN084.TO flags total
    (ASY t y r j) (BD.direction j) hs hm ht
  have hsource (j:Fin 3):=RCN084.TO flags total
    (BD.direction j) (source j).flag hs hm ht
  unfold numeratorDir
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _=> ?_
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (hfirst j)) (Nat.mul_le_mul_left _ (hsource j))

theorem DAB
    (t y r scale:ℕ) (hr3:3≤r) (hb:r+2≤y) (hyt:y≤t)
    (S:FH (AL K) Gamma x p errorCap flag w (cellSupport t y r))
    (source:Fin 3→Source S.F) (hscale:0<scale) (hscaleDiv: ∀j,3*(source j).d ∣ scale)
    (hfree:DGR S)
    (hproper: ¬S.G ∣ _Q2 (AL K) S.F (w+1))
    (hflagChar:flag.yz+flag.all<p∧flag.all<p∧flag.zOnly+flag.yz+flag.all<p)
    (hmixedRed:flagMixed flag (TX t y r) unitZFlag<p)
    (hlinear:2*(flag.zOnly+flag.yz+flag.all)<p)
    (hmovingGate:2*(flag.zOnly+flag.yz+flag.all)*(t+1)<p)
    (hchar:2*(w-1)<p)
    (hgate:errorCap+1≤(cellNormal t y r).yz)
    (htangent: ∀C:CM S,
      (∀delay,_Q2 (AL K) S.F (w+1+delay) ∈ C.1)→
      (HF Ω S.G (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card≤
        (errorCap+1)*(KF.MQ S hproper hflagChar hmixedRed).yzCost C)
    (h2:(2:Ω) ≠ 0) (hfact: ∀j,((source j).k.factorial:Ω) ≠ 0)
    (hgood: ∀gamma ∈ Gamma,∀j,
      MvPolynomial.eval (DK (AL K) S.selected gamma)
        ((source j).leading (AL K)) ≠ 0):
    Gamma.card≤numeratorDir source scale t y r flag/scale:=by
  classical
  let Ext:=AlgebraicClosure (RatFunc Ω)
  letI:CharP Ext p:=charP_of_injective_algebraMap (algebraMap Ω Ext).injective p
  have h2E:(2:Ext) ≠ 0:=by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfactE (j:Fin 3):((source j).k.factorial:Ext) ≠ 0:=by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
  let base:=KF.AHP S hproper hflagChar hmixedRed
  let Uold:=KF.QK S hproper hflagChar hmixedRed
  let unit:=YV (EW S) Uold base
  let Bfam:=KF.MQ S hproper hflagChar hmixedRed
  let common:=AJT.CVD S hproper hflagChar hmixedRed
  let active:Finset (CM S):=Finset.univ.filter
    (fun C=> ∀j:Fin 3,(source j).leading (AL K) ∉ C.1)
  have hlead (C:active) (j:Fin 3):(source j).leading (AL K) ∉ C.val.1:=
    (Finset.mem_filter.mp C.property).2 j
  have Hsupport:KW (cellSupport t y r) S.F:=
    ⟨S.AFS,S.ACG,S.UT⟩
  have hs:cellS r+2=r:=by dsimp [cellS];omega
  have hys:cellB y r+cellS r+3=r+(y-r):=by dsimp [cellB,cellS];omega
  have htot:cellA t y+cellB y r+cellS r+3=r+(y-r)+(t-y):=by
    dsimp [cellA,cellB,cellS];omega
  have hR:WeightBound BE S.F (r:ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt BE S.F≤r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR:WeightBound BC S.F ((r+(y-r):ℕ):ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt BC S.F≤r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll:WeightBound AT S.F ((r+(y-r)+(t-y):ℕ):ℤ):=by
    apply Or.inr
    exact_mod_cast (show wt AT S.F≤r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)
  have hgates:2*(flag.zOnly+flag.yz+flag.all)*(cellA t y+(cellB y r+1)+(cellS r+3))<p:=by
    have he:cellA t y+(cellB y r+1)+(cellS r+3)=t+1:=by dsimp [cellA,cellB,cellS];omega
    simpa only [he] using hmovingGate
  have hdiv1 (j:Fin 3):(source j).d ∣ scale:=(Dvd.intro_left 3 rfl).trans (hscaleDiv j)
  obtain ⟨budget,hcost,hmoving⟩:=DDE.EOV (E:=Ext)
    (AL K) S.F source scale hscale hdiv1 S.G flag (TX t y r)
    S.MW.ne_zero S.RR S.flag_support
    (cellA t y) (cellB y r) (cellS r) w (by norm_num [w])
    Hsupport.IZ.2.1 Hsupport.ys_weight Hsupport.total_weight p hlinear hgates h2E
    hfactE base unit active (fun C hC j=>(Finset.mem_filter.mp hC).2 j)
  have hcost' (C:CM S):
      (budget C).zCost=Bfam.zCost C∧(budget C).yzCost=Bfam.yzCost C∧
        (budget C).allCost=Bfam.allCost C:=by
    obtain ⟨hz,hy,ha⟩:=hcost C
    obtain ⟨ez,ey,ea⟩:=
      AUD (EW S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f:FlagDegree) (C:CM S):
      unit.toFE.weightedCost f C=Bfam.weightedCost f C:=by
    obtain ⟨ez,ey,ea⟩:=
      AUD (EW S) Uold base C
    change unit.toFE.zCost C=Bfam.zCost C at ez
    change unit.toFE.yzCost C=Bfam.yzCost C at ey
    change unit.toFE.allCost C=Bfam.allCost C at ea
    unfold FE.weightedCost
    rw [ez,ey,ea]
  let mu:=fun C:CM S=>FO (MU S)
    (DN (MU S) hproper) C
  let first:=ASY t y r
  let normal:=cellNormal t y r
  let projection:(j:Fin 3)→(C:CM S)→
      Coordinate Ω (AJ Ω C.1):=
    ![unit.zProjection,unit.yzProjection,unit.NV]
  let ell:=channel S hproper hflagChar hmixedRed
  have hell (j:Fin 3):BI (BD.direction j) (ell j):=by
    fin_cases j
    · exact FFR
    · exact FDG _
    · exact FFE _ _
  have hvalue (j:Fin 3) (C:CM S):
      FT Ω (AJ Ω C.1) (projection j C)=
        BR Ω C.1 (ell j):=by
    fin_cases j
    · exact FKV unit C
    · exact ETQ unit common C
    · exact FKF unit common C
  have hnormal (j:Fin 3):
      scale*(∑ C:active,mu C.val*
        DQ Ω (AJ Ω C.val.1) (projection j C.val))≤
      scale/3*flagMixed flag (first j) (BD.direction j)+
        4*(w+1)*(scale/(3*(source j).d))*
          flagMixed flag (BD.direction j) (source j).flag:=by
    have hq:(BD.direction j).zOnly+
        (BD.direction j).yz+
        (BD.direction j).all=1:=by fin_cases j<;>rfl
    have h:=DCJ.DKP (E:=Ext)
      (MU S) hproper (fun C:active=>C.val) Subtype.val_injective
      (ell j) (BD.direction j) (hell j)
      (fun C=>projection j C.val) (fun C=>hvalue j C.val)
      hflagChar.2.2 (by rw [hq,mul_one];exact hlinear) _ (fun C=>hlead C j)
      _ _ _ _ _ (EWL (E:=Ext) (MU S) hproper
        (ell j) (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k
        (source j).n0 (source j).hS (source j).hshape (source j).hBU (source j).hUT
        (source j).hdn (source j).hB (source j).hn (source j).hdiv h2E (hfactE j)
        j r (y-r) (t-y) hr3 (by omega) hR hYR hAll
        unitAllFlag (hfree hproper hflagChar hmixedRed j))
    have hexp:flagMixed flag (BD.direction j)
        ((source j).d • first j+(4*(w+1)) • (source j).flag)=
        (source j).d*flagMixed flag (first j) (BD.direction j)+
          4*(w+1)*flagMixed flag (BD.direction j) (source j).flag:=by
      simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
      ring
    change 3*(source j).d*(∑ C:active,mu C.val*
        DQ Ω (AJ Ω C.val.1) (projection j C.val))≤
      flagMixed flag (BD.direction j)
        ((source j).d • first j+(4*(w+1)) • (source j).flag) at h
    rw [hexp] at h
    obtain ⟨m,hm⟩:=hscaleDiv j
    have hd0:0<3*(source j).d:=by simp only [Source.d];omega
    have h3:scale/3=(source j).d*m:=by
      rw [hm,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by norm_num)]
    have h3d:scale/(3*(source j).d)=m:=by rw [hm,Nat.mul_div_cancel_left _ hd0]
    rw [h3,h3d,hm]
    calc
      _=m*(3*(source j).d*(∑ C:active,mu C.val*
          DQ Ω (AJ Ω C.val.1) (projection j C.val))):=by ring
      _≤m*((source j).d*flagMixed flag (first j) (BD.direction j)+
          4*(w+1)*flagMixed flag (BD.direction j) (source j).flag):=
        Nat.mul_le_mul_left m h
      _=_:=by ring
  have hnormalSum:scale*(∑ C ∈ active,mu C*Bfam.weightedCost normal C)≤
      ∑ j:Fin 3,(scale/3*weight normal j*
          flagMixed flag (first j) (BD.direction j)+
        4*(w+1)*weight normal j*(scale/(3*(source j).d))*
          flagMixed flag (BD.direction j) (source j).flag):=by
    have h:=Finset.sum_le_sum (fun j (_:j ∈ (Finset.univ:Finset (Fin 3)))=>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    have hsum:(∑ C ∈ active,mu C*Bfam.weightedCost normal C)=
        ∑ C:active,mu C.val*unit.toFE.weightedCost normal C.val:=by
      calc
        _= ∑ C ∈ active,mu C*unit.toFE.weightedCost normal C:=by
          apply Finset.sum_congr rfl
          intro C _
          rw [heq]
        _=_:=(Finset.sum_coe_sort active
          (fun C=>mu C*unit.toFE.weightedCost normal C)).symm
    rw [hsum]
    have hl:scale*(∑ C:active,mu C.val*unit.toFE.weightedCost normal C.val)=
        ∑ j:Fin 3,weight normal j*(scale*∑ C:active,mu C.val*
          DQ Ω (AJ Ω C.val.1) (projection j C.val)):=by
      rw [Fin.sum_univ_three]
      change scale*(∑ C:active,mu C.val*unit.toFE.weightedCost normal C.val)=
        normal.zOnly*(scale*∑ C:active,mu C.val*
          DQ Ω (AJ Ω C.val.1) (unit.zProjection C.val))+
        normal.yz*(scale*∑ C:active,mu C.val*
          DQ Ω (AJ Ω C.val.1) (unit.yzProjection C.val))+
        normal.all*(scale*∑ C:active,mu C.val*
          DQ Ω (AJ Ω C.val.1) (unit.NV C.val))
      have hp (C:active):mu C.val*unit.toFE.weightedCost normal C.val=
          normal.zOnly*(mu C.val*
            DQ Ω (AJ Ω C.val.1) (unit.zProjection C.val))+
          normal.yz*(mu C.val*
            DQ Ω (AJ Ω C.val.1) (unit.yzProjection C.val))+
          normal.all*(mu C.val*
            DQ Ω (AJ Ω C.val.1) (unit.NV C.val)):=by
        simp only [FE.weightedCost,
          EE.toFE,
          QZ.toFE,
          EE.toQZ]
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    rw [hl]
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _=> ?_))
    ring
  let moveNum:= ∑ j:Fin 3,weight (rawFirstFlag t y r) j*(scale/(source j).d)*
    flagMixed flag (BD.direction j) (source j).flag
  have hmovingScaled:scale*(∑ C ∈ active,(budget C).movingCost)≤moveNum:=by
    exact (Nat.mul_le_mul_left scale hmoving).trans (by
      simpa only [moveNum,rawFirstFlag,Nat.mul_comm] using Nat.div_mul_le_self moveNum scale)
  have hjointScaled:scale*(∑ C ∈ active,
      (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost))≤
      numeratorDir source scale t y r flag:=by
    have h:=Nat.add_le_add hnormalSum (Nat.mul_le_mul_left 65539 hmovingScaled)
    convert h using 1
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    · simp only [numeratorDir,moveNum,first,normal,Nat.add_mul,Finset.sum_add_distrib,
        Finset.mul_sum,Nat.mul_assoc]
      ring
  have hjoint:(∑ C ∈ active,(mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost))≤
      numeratorDir source scale t y r flag/scale:=by
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa only [Nat.mul_comm] using hjointScaled
  have hinactive: ∀C:CM S,C ∉ active→
      (HF Ω S.G (_Q2 (AL K) S.F (w+1))
        (CR (AL K) S.F) Gamma
        (DK (AL K) S.selected) C).card=0:=by
    intro C hC
    have hex: ∃j:Fin 3,(source j).leading (AL K) ∈ C.1:=by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using hC
    obtain ⟨j,hj⟩:=hex
    exact AEF.BOK _ _ _
      ((source j).leading (AL K)) Gamma _ C hj
      (fun gamma hgamma=>hgood gamma hgamma j)
  obtain ⟨provider⟩:=APU.AYF
    t y r hr3 hb hyt hchar S hproper (TX t y r) Bfam base budget hcost'
    active (numeratorDir source scale t y r flag/scale) hinactive hjoint hgate htangent
  exact BIF S provider

end Retained

section Discharge
open HFree6812 HK PR FA
open WithZero MvPolynomial
variable {K I:Type} [Field K] [CharP K 2130706433]
  {Gamma:Finset K} {x:I→K} {flag:FlagDegree} {errorCap:ℕ}
  [CharP (GenericField K) 2130706433]

omit [CharP (GenericField K) 2130706433] in
private theorem BUC {n:ℕ} (h0:0<n) (hn:n<2130706433):(n:K) ≠ 0:=by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

omit [CharP (GenericField K) 2130706433] in

private theorem FMM {E:Type} [Field E] [IsAlgClosed E]
    [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
    [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
    (F:MvPolynomial (Fin 4) K) (N:ℕ)
    (hN:MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9:N≤9678) (D:Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep:BP D) (hFD:surfaceMap (phiE K E) F ∈ D)
    (hHD:surfaceMap (phiE K E) (polyH K F) ∉ D) (d:Fin 3)
    (c:Fin 3→GenericField K) (i:Fin 3) (hci:c i=1) (q:Fin 3→Polynomial K)
    (hqd:DirShape d q) (hq: ∀m,AL K (q m)=c m) (hq1:i=1∨q 1=0)
    (hslice:MvPolynomial.C (sliceValue (GenericField K) E)-
      CD (GenericField K) E
        (∑ m,MvPolynomial.C (c m)*MvPolynomial.X m) ∈ D):
    APH (phiE K E) F D unitAllFlag (infCap d):=by
  have hNK: ∀n:ℕ,0<n→n≤N→(n:K) ≠ 0:=
    fun n h0 hn=>BUC h0 (by omega)
  exact ⟨DOC d F D sep hFD hHD c i hci q hqd hq hslice
    (by exact_mod_cast BUC (K:=K) (n:=2) (by norm_num) (by norm_num))
    (hchar_gap F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap F D hHD c i hci q hq hq1 hslice N hN hNK)⟩

theorem DIV {t y r:ℕ}
    (S:RCN159.FH (AL K) Gamma x 2130706433 errorCap flag RCN326.w
      (cellSupport t y r)) (htot:(cellSupport t y r).total≤9678):DGR S:=by
  intro hproper hflagChar hmixedRed j D _ sep hFD hsl hHD
  set common:=AJT.CVD S hproper hflagChar hmixedRed with hcommon
  obtain ⟨ql,hql⟩:=
    AJT.ENF S hproper hflagChar hmixedRed
  obtain ⟨qm,hqm⟩:=
    AJT.ERF S hproper hflagChar hmixedRed
  have go:=FMM S.F _ S.UT htot D sep hFD hHD j
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (by simp [DirShape])
      (fun m=>by fin_cases m<;>simp) (Or.inr rfl) ?_
    have he:(∑ m,MvPolynomial.C ((![0,0,1]:Fin 3→GenericField K) m)*MvPolynomial.X m:
        MvPolynomial (Fin 3) (GenericField K))=linearZ:=by
      simp [linearZ,Fin.sum_univ_three]
    rw [he];exact hsl
  · refine go ![1,0,common.lam] 0 rfl ![1,0,ql] (by simp [DirShape])
      (fun m=>by fin_cases m<;>simp [hql,hcommon]) (Or.inr rfl) ?_
    have he:(∑ m,MvPolynomial.C ((![1,0,common.lam]:Fin 3→GenericField K) m)*
        MvPolynomial.X m:MvPolynomial (Fin 3) (GenericField K))=linearU common.lam:=by
      simp [linearU,Fin.sum_univ_three]
    rw [he];exact hsl
  · refine go ![common.mu,1,common.mu*common.lam] 1 rfl ![qm,1,qm*ql] trivial
      (fun m=>by fin_cases m<;>simp [hql,hqm,hcommon]) (Or.inl rfl) ?_
    have he:(∑ m,MvPolynomial.C
        ((![common.mu,1,common.mu*common.lam]:Fin 3→GenericField K) m)*
        MvPolynomial.X m:MvPolynomial (Fin 3) (GenericField K))=
          linearA common.mu common.lam:=by
      simp [linearA,Fin.sum_univ_three];ring
    rw [he];exact hsl

end Discharge

end
end HFreeDir6813

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace OF
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 FA GJ
open KB BD AAG
open GU
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def numberDir (cfg:Fin 3→Params) (scale t y r:ℕ) (f:FlagDegree):ℕ:=
  ∑ j:Fin 3,(scale/3*weight (ID.cellNormal t y r) j*
      flagMixed f (HFreeDir6813.ASY t y r j) (direction j)+
    (4*(w+1)*weight (ID.cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (HK.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

def firstDir (j:Fin 3) (a b c:ℕ):FlagDegree:=
  HFreeDir6813.ASY (a+3+(b+2)+c) (a+3+(b+2)) (a+3) j

def firstLo (j:Fin 3) (b c:ℕ):FlagDegree:=
  ![⟨262144*c,262144*b,3⟩,⟨262144*c,262144*b+393216,3⟩,
    ⟨262144*c,262144*b+131072,262147⟩] j

def firstHi (j:Fin 3) (a b c:ℕ):FlagDegree:=
  ![⟨262144*c,262144*b+131072,262144*a+131075⟩,⟨262144*c,262144*b+524288,262144*a+131075⟩,
    ⟨262144*c,262144*b+131072,262144*a+524291⟩] j

theorem YK (j:Fin 3) (b c:ℕ):firstDir j 0 b c=firstLo j b c:=by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j<;>
    simp [firstDir,firstLo,HFreeDir6813.ASY,HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag,unitAllFlag,RCN326.w]<;>omega

theorem YJ (j:Fin 3) (a b c:ℕ):firstDir j (a+1) b c=firstHi j a b c:=by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j<;>
    simp [firstDir,firstHi,HFreeDir6813.ASY,HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag,unitAllFlag,RCN326.w]<;>omega

def graphDir (cfg:Fin 3→Params) (scale:ℕ) (f:FlagDegree) (a b c:ℕ):ℕ:=
  ∑ j:Fin 3,(scale/3*weight (normal a b c) j*flagMixed f (firstDir j a b c) (direction j)+
    (524288*weight (normal a b c) j*(scale/(3*(cfg j).d))+
      65539*weight (raw a b c) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

theorem DUL (cfg:Fin 3→Params) (scale:ℕ) (f:FlagDegree) (a b c:ℕ):
    numberDir cfg scale (a+3+(b+2)+c) (a+3+(b+2)) (a+3) f=graphDir cfg scale f a b c:=by
  have hy:a+3+(b+2)-(a+3)=b+2:=by omega
  have hz:a+3+(b+2)+c-(a+3+(b+2))=c:=by omega
  have hr2:a+3-2=a+1:=by omega
  have hb:b+2-1=b+1:=by omega
  have hv2:131074*(b+2)-131072=131074*b+131076:=by omega
  have hn:ID.cellNormal (a+3+(b+2)+c) (a+3+(b+2)) (a+3)=normal a b c:=by
    norm_num only [ID.cellNormal,JE.normalFlag,normal,w,hy,hz,
      hv2,FlagDegree.mk.injEq,true_and]
    omega
  have hraw:HK.rawFirstFlag (a+3+(b+2)+c) (a+3+(b+2)) (a+3)=
      raw a b c:=by
    simp only [HK.rawFirstFlag,cellA,cellB,cellS,hz,hy,hb,hr2,
      RCN198.center,RCN198.direction,raw,w,unitYZFlag]
    change FlagDegree.mk (0+2*c+131071*c) (1+(2*(b+1)+1)+131071*(b+1+1))
      (0+(2*(a+1)+3)+131071*(a+1+2))=_
    have e0:0+2*c+131071*c=131073*c:=by ring
    have e1:1+(2*(b+1)+1)+131071*(b+1+1)=131073*b+262146:=by ring
    have e2:0+(2*(a+1)+3)+131071*(a+1+2)=131073*a+393218:=by ring
    rw [e0,e1,e2]
  have hw4:4*(w+1)=524288:=rfl
  simp only [numberDir,graphDir,firstDir,hn,hraw,hw4]

end OF
end MergedPart0
section MergedPart1
namespace ESY
noncomputable section

section FixedStage
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {Gamma:Finset K} {x:I→K} {flag:FlagDegree}

theorem GHE
    (D t y r scale:ℕ) (hDlow:131072≤D) (hDchar:D<2130706433)
    (ht:t≤7501) (hy:y≤142) (hr:r≤31)
    (hr3:3≤r) (hry:r+2≤y) (hyt:y+2≤t)
    (S:FH (AL K) Gamma x 2130706433 80909 flag w (cellSupport t y r))
    (hnodes:S.nodes.card=262144)
    (hagreement: ∀gamma ∈ Gamma,181235≤(S.AJW gamma).card)
    (hbox:S.F ∈ BA K D w t r)
    (hflag:flag.all≤r∧flag.yz+flag.all≤y∧flag.zOnly+flag.yz+flag.all≤t)
    (source:Fin 3→Source S.F) (hscale:0<scale) (hscaleDiv: ∀j,3*(source j).d ∣ scale)
    (hfree:HFreeDir6813.DGR S)
    (h2:(2:GenericField K) ≠ 0) (hfact: ∀j,((source j).k.factorial:GenericField K) ≠ 0)
    (hgood: ∀gamma ∈ Gamma,∀j,
      MvPolynomial.eval (DK (AL K) S.selected gamma)
        ((source j).leading (AL K)) ≠ 0)
    (hidentityAbs:scale*131073*80910*IY flag (cellA t y) (cellB y r) (cellS r) w≤
      50164*HFreeDir6813.numeratorDir source scale t y r flag):
    Gamma.card≤HFreeDir6813.numeratorDir source scale t y r flag/scale:=by
  have hflagChar:flag.yz+flag.all<2130706433∧flag.all<2130706433∧
      flag.zOnly+flag.yz+flag.all<2130706433:=by omega
  by_cases hTail:S.G ∣ _Q2 (AL K) S.F (w+1)
  · have hTailNumerator:=(AWJ (AL K)
      (DI K) S.F (w+1) S.G).mp hTail
    have hmixed:=AQW.EJG flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have hprovider:=BRK.AAB S 181235
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive:1≤IY flag (cellA t y) (cellB y r) (cellS r) w:=by
      apply Lower80788.FixedStage.CVP
      have hp:=S.y_dependent
      have hd:=AHE S.G flag S.flag_support 1
      omega
    have hinc:=AQH S 181235 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes];norm_num) hpositive
    have hinc' :Gamma.card*50164≤131073*80910*IY flag (cellA t y) (cellB y r) (cellS r) w:=by
      simpa only [hnodes,w] using hinc
    have hnum:scale*Gamma.card≤HFreeDir6813.numeratorDir source scale t y r flag:=by
      apply Nat.le_of_mul_le_mul_left (c:=50164) _ (by decide)
      calc
        50164*(scale*Gamma.card)=scale*(Gamma.card*50164):=by ring
        _≤scale*(131073*80910*IY flag (cellA t y) (cellB y r) (cellS r) w):=
          Nat.mul_le_mul_left _ hinc'
        _≤_:=by simpa only [Nat.mul_assoc] using hidentityAbs
    exact (Nat.le_div_iff_mul_le hscale).mpr (by simpa only [Nat.mul_comm] using hnum)
  · have hmixed:=AQW.reduced_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have htangent: ∀C:CM S,
        (∀delay,_Q2 (AL K) S.F (w+1+delay) ∈ C.1)→
        (HF (GenericField K) S.G (_Q2 (AL K) S.F (w+1))
          (CR (AL K) S.F) Gamma
          (DK (AL K) S.selected) C).card≤
          (80909+1)*(KF.MQ S hTail hflagChar hmixed).yzCost C:=by
      intro C hall
      exact ALX S C hTail (KF.AHP S hTail hflagChar hmixed C)
        181235 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (KF.MQ S hTail hflagChar hmixed)
        (KF.ADY S hTail hflagChar hmixed C) hall
        (KF.AJM S hTail hflagChar hmixed C)
    have hmov:2*(flag.zOnly+flag.yz+flag.all)*(t+1)<2130706433:=by
      have hm:=Nat.mul_le_mul (show 2*(flag.zOnly+flag.yz+flag.all)≤2*7501 by omega)
        (show t+1≤7502 by omega)
      omega
    exact HFreeDir6813.DAB t y r scale hr3 hry (by omega) S source hscale hscaleDiv hfree hTail
      hflagChar hmixed (by omega) hmov (by norm_num [w]) (by
        unfold cellNormal
        rw [JE.CML t y r hr3 hry]
        simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
          FNF t y r 80909 hry (by norm_num)) htangent h2 hfact hgood

end FixedStage

section RegularGeometry
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ IB JN
open ID BD HK
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433

theorem EYG
    (D t y r scale:ℕ) (hDlow:131072≤D) (hDchar:D<2130706433)
    (ht:t≤7501) (hy:y≤142) (hr:r≤31)
    (hr3:3≤r) (hry:r+2≤y) (hyt:y+2≤t)
    (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hFR:0<F.degreeOf 2)
    (hbox:F ∈ BA K D w t r)
    (hsupport:KW (cellSupport t y r) F)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I→K) (hinj:Set.InjOn x nodes) (hnodes:nodes.card=262144)
    (hdegree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤w)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      (nodes.filter (fun i=>(selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hsolution: ∀gamma ∈ Gamma,BM K (selected gamma) gamma F=0)
    (hregular: ∀gamma ∈ Gamma,BM K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
    (hno:BL selected Gamma w 80909)
    (source:Fin 3→Source F) (hscale:0<scale) (hscaleDiv: ∀j,3*(source j).d ∣ scale)
    (hfree: ∀(G:Finset K) (fl:FlagDegree) (S:FH (AL K) G x
      2130706433 80909 fl w (cellSupport t y r)),S.F=F→HFreeDir6813.DGR S)
    (h2:(2:GenericField K) ≠ 0) (hfact: ∀j,((source j).k.factorial:GenericField K) ≠ 0)
    (hgood: ∀gamma ∈ Gamma,∀j,
      MvPolynomial.eval (DK (AL K) selected gamma)
        ((source j).leading (AL K)) ≠ 0)
    (hidentity: ∀f:FlagDegree,scale*131073*80910*IY f (cellA t y) (cellB y r) (cellS r) w≤
      50164*HFreeDir6813.numeratorDir source scale t y r f):
    scale*Gamma.card≤HFreeDir6813.numeratorDir source scale t y r (FX F):=by
  have hFRsmall:F.degreeOf 2<2130706433:=(UY F D w t r hbox).trans_lt (by omega)
  have hs:cellS r+2=r:=by dsimp [cellS];omega
  have hys:cellB y r+cellS r+3=y:=by dsimp [cellB,cellS];omega
  have hts:cellA t y+cellB y r+cellS r+3=t:=by dsimp [cellA,cellB,cellS];omega
  have hcover:=AAD K F hF.ne_zero selected Gamma hsolution
  have hstage (g:EX K F):
      scale*(KK K F selected Gamma g).card≤
        HFreeDir6813.numeratorDir source scale t y r (CO K g):=by
    let S0:=AIT K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S:=BJP S0 (AES g.1)
    have hsub:=WK K F selected Gamma g
    have hag: ∀gamma ∈ KK K F selected Gamma g,181235≤(S.AJW gamma).card:=
      fun gamma hgamma=>hagreement gamma (hsub hgamma)
    have hf:=AER F hF.ne_zero hsupport g
    have hf' :(CO K g).all≤r∧
        (CO K g).yz+(CO K g).all≤y∧
        (CO K g).zOnly+(CO K g).yz+(CO K g).all≤t:=by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc:=GHE D t y r scale hDlow hDchar ht hy hr hr3 hry hyt
      S hnodes hag hbox hf' source hscale hscaleDiv (hfree _ _ S rfl) h2 hfact
      (fun gamma hgamma j=>hgood gamma (hsub hgamma) j) (hidentity _)
    have hm:=(Nat.le_div_iff_mul_le hscale).mp hc
    dsimp only [S,S0,BJP,AIT] at hm
    simpa only [Nat.mul_comm,CO] using hm
  have hb:=VD F hF.ne_zero
  calc
    scale*Gamma.card≤scale*∑ g:EX K F,(KK K F selected Gamma g).card:=
      Nat.mul_le_mul_left _ hcover
    _= ∑ g:EX K F,scale*(KK K F selected Gamma g).card:=Finset.mul_sum _ _ _
    _≤ ∑ g:EX K F,
        HFreeDir6813.numeratorDir source scale t y r (CO K g):=
      Finset.sum_le_sum (fun g _=>hstage g)
    _≤_:=HFreeDir6813.EHQ source scale t y r (CO K)
      (FX F) hb.1 hb.2.1 hb.2.2

end RegularGeometry

section Profile
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open FA GJ ID
open AAG BD BB AXB
open KB OF
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP (GenericField K) 2130706433:=MP K 2130706433
variable {nodes:I ↪ K} {u0 u1:I→K}

def boundDir (S:Data nodes u0 u1) (cfg:Fin 3→Params) (scale:ℕ):ℕ:=
  max (Finset.univ.sup (fun j:Fin 3=>helperCap S (cfg j)))
    (numberDir cfg scale S.t S.y S.r (FX S.F)/scale+
      ∑ j:Fin 3,CRL S (cfg j))

theorem EJH
    (S:Data nodes u0 u1) (hI:Fintype.card I=262144)
    (cfg:Fin 3→Params) (hc: ∀j,(cfg j).WellFormed)
    (scale:ℕ) (hscale:0<scale) (hscaleDiv: ∀j,3*(cfg j).d ∣ scale)
    (hfree: ∀(G:Finset K) (fl:FlagDegree) (S' :RCN159.FH (AL K) G
      ⇑nodes 2130706433 80909 fl w (cellSupport S.t S.y S.r)),S'.F=S.F→
      HFreeDir6813.DGR S')
    (P:Fin 3→DX.Poly (K:=K))
    (hP: ∀j,Interpolant (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 nodes u0 u1 (P j))
    (hL: ∀j,(cfg j).L<wt AT S.F)
    (hHelperGates: ∀j,S.PairGates ((cfg j).B+(cfg j).s*(S.r-1))
      ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)))
    (hCoefficientGates: ∀j,S.PairGates (cfg j).B (cfg j).U (cfg j).L)
    (hidentity: ∀f:FlagDegree,scale*131073*80910*
      IY f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w≤
        50164*numberDir cfg scale S.t S.y S.r f):
    S.seeds.card≤boundDir S cfg scale:=by
  classical
  have hshape (j:Fin 3): ∀e ∈ (P j).support,2*e 1+e 3≤(cfg j).B∧
      e 1+e 2+e 3≤(cfg j).U∧e 1+e 2+e 3+e 4≤(cfg j).L:=by
    intro e he
    have h:=(hP j).2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS (j:Fin 3): ∀e ∈ (P j).support,e 1≤(cfg j).s:=fun e he=>((hP j).2.1 e he).2.1
  have factorial (j:Fin 3) (d:ℕ) (hd:d≤(cfg j).s):(d.factorial:K) ≠ 0:=
    TI.factorial_ne d (hd.trans_lt (hc j).2.2.2.2.2.2.2)
  have alternatives (j:Fin 3):=EXD (P j) S.F
    (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 S.r S.y S.t
    nodes u0 u1 (hP j) S.irreducible (hL j) (hc j).1
    (by have:=hc j;unfold Params.WellFormed at this;omega)
    (by have:=hc j;unfold Params.WellFormed at this;omega)
    (hc j).2.2.2.1 (hc j).2.2.2.2.1
    (by have:=S.rpos;omega) (by have:=S.ry;omega) (by have:=S.yt;omega)
    S.weights (factorial j)
  by_cases hall: ∀j:Fin 3,(cfg j).n0≤(BX.asS (P j)).natDegree∧
      ∀d≤(cfg j).k,S.F ∣ FR.helper (P j) S.F ((cfg j).s-d) d
  · let source:Fin 3→Source S.F:=fun j=>{
      P:=P j,B:=(cfg j).B,U:=(cfg j).U,T:=(cfg j).L,
      s:=(cfg j).s,k:=(cfg j).k,n0:=(cfg j).n0,
      hS:=hS j,hshape:=hshape j,hBU:=(hc j).2.1,
      hUT:=(hc j).2.2.1,hdn:=(hc j).2.2.2.2.2.1,
      hB:=(hc j).2.2.2.2.2.2.1,hn:=(hall j).1,hdiv:=(hall j).2}
    let point:=DK (AL K) S.selected
    let LC:=fun j:Fin 3=>surfaceMap (AL K) (BX.asS (P j)).leadingCoeff
    let Good:=S.seeds.filter (fun gamma=> ∀j:Fin 3,MvPolynomial.eval (point gamma) (LC j) ≠ 0)
    let Bad:=fun j:Fin 3=>S.seeds.filter (fun gamma=>MvPolynomial.eval (point gamma) (LC j)=0)
    let SG:=S.restrict Good (Finset.filter_subset _ _)
    have hnum (f:FlagDegree):HFreeDir6813.numeratorDir source scale S.t S.y S.r f=
        numberDir cfg scale S.t S.y S.r f:=rfl
    have h2:(2:GenericField K) ≠ 0:=TI.two_ne
    have hf (j:Fin 3):((source j).k.factorial:GenericField K) ≠ 0:=
      TI.factorial_ne (cfg j).k (by
        have:=hc j;unfold Params.WellFormed at this;omega)
    have hgood: ∀gamma ∈ SG.seeds,∀j,
        MvPolynomial.eval (DK (AL K) SG.selected gamma)
          ((source j).leading (AL K)) ≠ 0:=by
      intro gamma hgamma j
      exact (Finset.mem_filter.mp hgamma).2 j
    have hid (f:FlagDegree):scale*131073*80910*
        IY f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w≤
          50164*HFreeDir6813.numeratorDir source scale S.t S.y S.r f:=by
      rw [hnum]
      exact hidentity f
    have hg:=EYG
      SG.D SG.t SG.y SG.r scale SG.Dlow SG.Dchar SG.tbound SG.ybound SG.rbound SG.rpos SG.ry SG.yt
      SG.F SG.irreducible SG.rdegree SG.box SG.support SG.selected SG.seeds Finset.univ nodes u0 u1
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      SG.degree SG.agreement SG.solution SG.regular SG.noPencil
      source hscale hscaleDiv hfree h2 hf hgood hid
    have hGood:Good.card≤numberDir cfg scale S.t S.y S.r (FX S.F)/scale:=by
      apply (Nat.le_div_iff_mul_le hscale).mpr
      rw [← hnum]
      dsimp only [SG,Data.restrict] at hg
      simpa only [Nat.mul_comm] using hg
    have hBad (j:Fin 3):(Bad j).card≤CRL S (cfg j):=by
      let SB:=S.restrict (Bad j) (Finset.filter_subset _ _)
      have hnot:=AFH.CAK (P j) (hP j).1 S.F (cfg j).L
        (fun e he=>(hshape j e he).2.2) (hL j)
      have hrel:IsRelPrime SB.F (BX.asS (P j)).leadingCoeff:=
        S.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2
      apply SB.DVV hI _ (cfg j).B (cfg j).U (cfg j).L hrel
        (ZM.FJS (P j) (cfg j).B (cfg j).U (cfg j).L (hshape j))
        (hCoefficientGates j)
      intro gamma hgamma
      have hz:MvPolynomial.eval (point gamma) (LC j)=0:=(Finset.mem_filter.mp hgamma).2
      change MvPolynomial.eval (DK (AL K) S.selected gamma)
        (surfaceMap (AL K) (BX.asS (P j)).leadingCoeff)=0 at hz
      rw [UM] at hz
      dsimp only [SB,Data.restrict]
      exact (DI K) (by simpa only [map_zero] using hz)
    have hcover:S.seeds ⊆ Good ∪ Finset.univ.biUnion Bad:=by
      intro gamma hgamma
      by_cases hg: ∀j:Fin 3,MvPolynomial.eval (point gamma) (LC j) ≠ 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgamma,hg⟩)
      · have hex: ∃j:Fin 3,MvPolynomial.eval (point gamma) (LC j)=0:=by simpa only [not_forall,not_not] using hg
        obtain ⟨j,hj⟩:=hex
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hgamma,hj⟩⟩)
    have hcard:S.seeds.card≤Good.card+∑ j:Fin 3,(Bad j).card:=
      ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _)).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _)
    exact (hcard.trans (Nat.add_le_add hGood (Finset.sum_le_sum (fun j _=>hBad j)))).trans (le_max_right _ _)
  · obtain ⟨j,hj⟩:=not_forall.mp hall
    rcases alternatives j with ⟨Q,hrel,hw,hzero⟩ | hret
    · have hb:=S.DVV hI Q ((cfg j).B+(cfg j).s*(S.r-1))
        ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)) hrel
        (ZM.ATW Q _ _ _ hw) (hHelperGates j) (by
          intro gamma hgamma
          apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
            (Finset.univ.filter (fun i=>(S.selected gamma).eval (nodes i)=u0 i+gamma*u1 i))
            (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
          intro i hi
          simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
      exact (hb.trans (Finset.le_sup (f:=fun j:Fin 3=>helperCap S (cfg j)) (Finset.mem_univ j))).trans (le_max_left _ _)
    · exact (hj hret).elim

end Profile

end
end ESY
end MergedPart1

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G0
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source0,source0,source0]
def scale:ℕ:=18
def denominator:ℕ:=16253136
def gLo0 (b c:ℕ):ℕ:=
    5325894189560*b+
    46601779286330
def FY (b c:ℕ):ℕ:=
    267168156125087840*b+
    2212627657794813020
def HV (b c:ℕ):ℕ:=
    5365718755913607480*b^2+
    10733207588108877816*b*c+
    891342791786919170664*b+
    100740765466675425744*c+
    2529155053033010096976
def gLo1 (b c:ℕ):ℕ:=
    5325894189560*b+
    5325894189560*c+
    423495740984480
def GC (b c:ℕ):ℕ:=
    267168156125087840*b+
    267168156125087840*c+
    20994032354096164520
def HX (b c:ℕ):ℕ:=
    5365718755913607480*b^2+
    10733207588108877816*b*c+
    891342791786919170664*b+
    100740765466675425744*c+
    2529155053033010096976
def gLo2 (b c:ℕ):ℕ:=
    206161575936*b^2+
    412323151872*b*c+
    184241640981592*b+
    18099455723173*c+
    650863295402336
def FZ (b c:ℕ):ℕ:=
    10341889295253504*b^2+
    20683778590507008*b*c+
    9142214479540865008*b+
    857899497567392332*c+
    32249573174139727304
def HW (b c:ℕ):ℕ:=
    5365718755913607480*b^2+
    10733207588108877816*b*c+
    891342791786919170664*b+
    100740765466675425744*c+
    2529155053033010096976
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    10738584612285249888*b+
    100777141098493068672
def interceptLo (b:ℕ):ℕ:=
    5371095780089979552*b^2+
    891523235432298511620*b+
    2529923457412758302496
def gHi0 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    18821021238949*a+
    5635136553464*b+
    65113556588511
def GA (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    894096110100779596*a+
    282680990067968096*b+
    3091210855051562664
def HS (a b c:ℕ):ℕ:=
    184484124029975472*a^3+
    555122255374514016*a^2*b+
    556792138659101616*a^2*c+
    167922340623611008344*a^2+
    556792138659101616*a*b^2+
    1115254160602790832*a*b*c+
    335769490930171722048*a*b+
    35938687422436258176*a*c+
    1755475575426329516136*a+
    5829433890915427560*b^2+
    11662307741397105576*b*c+
    1226277928030523839560*b+
    135843428319260043168*c+
    4116706615112002628112
def gHi1 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    412323151872*a*c+
    184653964133464*a+
    5635136553464*b+
    5635136553464*c+
    607840461181176
def GD (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    20683778590507008*a*c+
    9162898258131372016*a+
    282680990067968096*b+
    282680990067968096*c+
    30141417699383506584
def HY (a b c:ℕ):ℕ:=
    184484124029975472*a^3+
    555122255374514016*a^2*b+
    556792138659101616*a^2*c+
    167922340623611008344*a^2+
    556792138659101616*a*b^2+
    1115254160602790832*a*b*c+
    335769490930171722048*a*b+
    35938687422436258176*a*c+
    1755475575426329516136*a+
    5829433890915427560*b^2+
    11662307741397105576*b*c+
    1226277928030523839560*b+
    135843428319260043168*c+
    4116706615112002628112
def gHi2 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    412323151872*a*c+
    184653964133464*a+
    206161575936*b^2+
    412323151872*b*c+
    184653964133464*b+
    18511778875045*c+
    835311097959864
def _Q4 (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    20683778590507008*a*c+
    9162898258131372016*a+
    10341889295253504*b^2+
    20683778590507008*b*c+
    9162898258131372016*b+
    878583276157899340*c+
    41402129542975845816
def HU (a b c:ℕ):ℕ:=
    184484124029975472*a^3+
    555122255374514016*a^2*b+
    556792138659101616*a^2*c+
    167922340623611008344*a^2+
    556792138659101616*a*b^2+
    1115254160602790832*a*b*c+
    335769490930171722048*a*b+
    35938687422436258176*a*c+
    1755475575426329516136*a+
    5829433890915427560*b^2+
    11662307741397105576*b*c+
    1226277928030523839560*b+
    135843428319260043168*c+
    4116706615112002628112
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    558462021943689216*a^2+
    1116924043887378432*a*b+
    35959204723849607088*a+
    11669354648858065248*b+
    135898651369206447408
def interceptHi (a b:ℕ):ℕ:=
    186154007314563072*a^3+
    558462021943689216*a^2*b+
    167995469339897784336*a^2+
    558462021943689216*a*b^2+
    335849666553919457712*a*b+
    1756069433902684096056*a+
    5836480798376387232*b^2+
    1226535207533081740980*b+
    4117997419135103225160
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source0,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source0,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G0

namespace AV.G1
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source1,source1,source1]
def scale:ℕ:=21
def denominator:ℕ:=22122324
def gLo0 (b c:ℕ):ℕ:=
    5583598518800*b+
    47160143516040
def FY (b c:ℕ):ℕ:=
    280095636097083200*b+
    2219786774626544610
def HV (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1663494998666776038414*b+
    119289919096856364654*c+
    4743940389752277530796
def gLo1 (b c:ℕ):ℕ:=
    5583598518800*b+
    5583598518800*c+
    678323307864110
def GC (b c:ℕ):ℕ:=
    280095636097083200*b+
    280095636097083200*c+
    33735501086271042140
def HX (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1663494998666776038414*b+
    119289919096856364654*c+
    4743940389752277530796
def gLo2 (b c:ℕ):ℕ:=
    240521838592*b^2+
    481043677184*b*c+
    296368933924359*b+
    18297029134004*c+
    1048014637348892
def FZ (b c:ℕ):ℕ:=
    12065537511129088*b^2+
    24131075022258176*b*c+
    14750287469611876116*b+
    859470303593342276*c+
    52105550895476253188
def HW (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1663494998666776038414*b+
    119289919096856364654*c+
    4743940389752277530796
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    13289365731071879904*b+
    119339733426505039812
def interceptLo (b:ℕ):ℕ:=
    6647228509832000160*b^2+
    1663839886225043283057*b+
    4745481176970294408732
def gHi0 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    19138855569076*a+
    5944381276688*b+
    65938214492220
def GA (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    901699684882294084*a+
    298193942363776832*b+
    3103388061190803750
def HS (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    314404629885754318050*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    628635154470606006024*a*b+
    42977345360702235756*a*c+
    3294602962296052426614*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2290994503702887999870*b+
    161129342126371644942*c+
    7724136445399726393356
def gHi1 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    296849977601543*a+
    5944381276688*b+
    5944381276688*c+
    974812500872757
def GD (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    14774418544634134292*a+
    298193942363776832*b+
    298193942363776832*c+
    48491821232587141488
def HY (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    314404629885754318050*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    628635154470606006024*a*b+
    42977345360702235756*a*c+
    3294602962296052426614*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2290994503702887999870*b+
    161129342126371644942*c+
    7724136445399726393356
def gHi2 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    296849977601543*a+
    240521838592*b^2+
    481043677184*b*c+
    296849977601543*b+
    18778072811188*c+
    1344624093111843
def _Q4 (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    14774418544634134292*a+
    12065537511129088*b^2+
    24131075022258176*b*c+
    14774418544634134292*b+
    883601378615600452*c+
    66867903902599258392
def HU (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    314404629885754318050*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    628635154470606006024*a*b+
    42977345360702235756*a*c+
    3294602962296052426614*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2290994503702887999870*b+
    161129342126371644942*c+
    7724136445399726393356
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    760128863201132544*a^2+
    1520257726402265088*a*b+
    43005332298204438288*a+
    14556247169740434144*b+
    161204870496829611732
def interceptHi (a b:ℕ):ℕ:=
    253376287733710848*a^3+
    760128863201132544*a^2*b+
    314540108267070771960*a^2+
    760128863201132544*a*b^2+
    628780285086545021556*a*b+
    3295761844901065400574*a+
    7280669229166277280*b^2+
    2291479976083708438245*b+
    7726702909738132702242
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source1,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source1,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G1

namespace AV.G2
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source2,source2,source2]
def scale:ℕ:=21
def denominator:ℕ:=22122324
def gLo0 (b c:ℕ):ℕ:=
    5583598518800*b+
    48233915486690
def FY (b c:ℕ):ℕ:=
    280095636097083200*b+
    2273651471762231210
def HV (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1554290930079980394288*b+
    121915036932968136564*c+
    4429434883547509717812
def gLo1 (b c:ℕ):ℕ:=
    5583598518800*b+
    5583598518800*c+
    633654393885070
def GC (b c:ℕ):ℕ:=
    280095636097083200*b+
    280095636097083200*c+
    31494729685426479580
def HX (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1554290930079980394288*b+
    121915036932968136564*c+
    4429434883547509717812
def gLo2 (b c:ℕ):ℕ:=
    240521838592*b^2+
    481043677184*b*c+
    276714659210935*b+
    18769487660769*c+
    978330825104092
def FZ (b c:ℕ):ℕ:=
    12065537511129088*b^2+
    24131075022258176*b*c+
    13764350432887674580*b+
    883170713129981736*c+
    48609932138028105988
def HW (b c:ℕ):ℕ:=
    6639849171902349438*b^2+
    13281986393142229182*b*c+
    1554290930079980394288*b+
    121915036932968136564*c+
    4429434883547509717812
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    13289365731071879904*b+
    121965267960343845387
def interceptLo (b:ℕ):ℕ:=
    6647228509832000160*b^2+
    1554618899710530072132*b+
    4430891107940495139816
def gHi0 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    19611314095841*a+
    5944381276688*b+
    67484444989635
def GA (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    925400094418933544*a+
    298193942363776832*b+
    3180953167863129810
def HS (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    293687648167115128122*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    587213494980758583840*a*b+
    43973065614133481196*a*c+
    3076142278379436124362*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2140368775626244933560*b+
    164750180215914662292*c+
    7211887236996981468048
def gHi1 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    277195702888119*a+
    5944381276688*b+
    5944381276688*c+
    910489312180293
def GD (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    13788481507909932756*a+
    298193942363776832*b+
    298193942363776832*c+
    45265112795018377392
def HY (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    293687648167115128122*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    587213494980758583840*a*b+
    43973065614133481196*a*c+
    3076142278379436124362*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2140368775626244933560*b+
    164750180215914662292*c+
    7211887236996981468048
def gHi2 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    277195702888119*a+
    240521838592*b^2+
    481043677184*b*c+
    277195702888119*b+
    19250531337953*c+
    1255286006153619
def _Q4 (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    13788481507909932756*a+
    12065537511129088*b^2+
    24131075022258176*b*c+
    13788481507909932756*b+
    907301788152239912*c+
    62386348108426909656
def HU (a b c:ℕ):ℕ:=
    251103391040799948*a^3+
    755583069815310744*a^2*b+
    757855966508221644*a^2*c+
    293687648167115128122*a^2+
    757855966508221644*a*b^2+
    1517984829709354188*a*b*c+
    587213494980758583840*a*b+
    43973065614133481196*a*c+
    3076142278379436124362*a+
    7271016994543715658*b^2+
    14546594935117872522*b*c+
    2140368775626244933560*b+
    164750180215914662292*c+
    7211887236996981468048
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    760128863201132544*a^2+
    1520257726402265088*a*b+
    44001204078081877788*a+
    14556247169740434144*b+
    164826276810545856807
def interceptHi (a b:ℕ):ℕ:=
    253376287733710848*a^3+
    760128863201132544*a^2*b+
    293816974574716103196*a^2+
    760128863201132544*a*b^2+
    587352473622982120536*a*b+
    3077241188178575305692*a+
    7280669229166277280*b^2+
    2140831178105632326300*b+
    7214315317678198007208
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source2,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source2,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G2

namespace AV.G3
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source3,source3,source3]
def scale:ℕ:=18
def denominator:ℕ:=16253136
def gLo0 (b c:ℕ):ℕ:=
    4569960546736*b+
    40915071143710
def FY (b c:ℕ):ℕ:=
    229247500866464704*b+
    1927359630528423340
def HV (b c:ℕ):ℕ:=
    4683458672804847384*b^2+
    9368375710344901272*b*c+
    1469608576306444909080*b+
    88608199643985721104*c+
    4199190610917835111824
def gLo1 (b c:ℕ):ℕ:=
    4569960546736*b+
    4569960546736*c+
    699566797940420
def GC (b c:ℕ):ℕ:=
    229247500866464704*b+
    229247500866464704*c+
    34842860855233938680
def HX (b c:ℕ):ℕ:=
    4683458672804847384*b^2+
    9368375710344901272*b*c+
    1469608576306444909080*b+
    88608199643985721104*c+
    4199190610917835111824
def gLo2 (b c:ℕ):ℕ:=
    206161575936*b^2+
    412323151872*b*c+
    306135940886962*b+
    16020638205407*c+
    1083036938651336
def FZ (b c:ℕ):ℕ:=
    10341889295253504*b^2+
    20683778590507008*b*c+
    15256920139993845688*b+
    753617695606178708*c+
    53929131814082563304
def HW (b c:ℕ):ℕ:=
    4683458672804847384*b^2+
    9368375710344901272*b*c+
    1469608576306444909080*b+
    88608199643985721104*c+
    4199190610917835111824
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    9372906660323748960*b+
    88639242780658820040
def interceptLo (b:ℕ):ℕ:=
    4687989622783695072*b^2+
    1469858650658924510916*b+
    4200328249838362280160
def gHi0 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    16742203721183*a+
    4879202910640*b+
    57348030928125
def GA (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    789814308139565972*a+
    244760334809344960*b+
    2701661025823959360
def HS (a b c:ℕ):ℕ:=
    184751305355509488*a^3+
    555656618025582048*a^2*b+
    557059319984635632*a^2*c+
    278047124300798244360*a^2+
    557059319984635632*a*b^2+
    1115521341928324848*a*b*c+
    555959555388384600672*a*b+
    32185655807695367328*a*c+
    2916725915740155255288*a+
    5147440989132201480*b^2+
    10297743044958663048*b*c+
    2024733242645611388568*b+
    119957563700503913664*c+
    6837867996814791680112
def gHi1 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    412323151872*a*c+
    306548264038834*a+
    4879202910640*b+
    4879202910640*c+
    1005805818042486
def GD (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    20683778590507008*a*c+
    15277603918584352696*a+
    244760334809344960*b+
    244760334809344960*c+
    50104951860974261424
def HY (a b c:ℕ):ℕ:=
    184751305355509488*a^3+
    555656618025582048*a^2*b+
    557059319984635632*a^2*c+
    278047124300798244360*a^2+
    557059319984635632*a*b^2+
    1115521341928324848*a*b*c+
    555959555388384600672*a*b+
    32185655807695367328*a*c+
    2916725915740155255288*a+
    5147440989132201480*b^2+
    10297743044958663048*b*c+
    2024733242645611388568*b+
    119957563700503913664*c+
    6837867996814791680112
def gHi2 (a b c:ℕ):ℕ:=
    206161575936*a^2+
    412323151872*a*b+
    412323151872*a*c+
    306548264038834*a+
    206161575936*b^2+
    412323151872*b*c+
    306548264038834*b+
    16432961357279*c+
    1389379041114234
def _Q4 (a b c:ℕ):ℕ:=
    10341889295253504*a^2+
    20683778590507008*a*b+
    20683778590507008*a*c+
    15277603918584352696*a+
    10341889295253504*b^2+
    20683778590507008*b*c+
    15277603918584352696*b+
    774301474196685716*c+
    69196393843371662496
def HU (a b c:ℕ):ℕ:=
    184751305355509488*a^3+
    555656618025582048*a^2*b+
    557059319984635632*a^2*c+
    278047124300798244360*a^2+
    557059319984635632*a*b^2+
    1115521341928324848*a*b*c+
    555959555388384600672*a*b+
    32185655807695367328*a*c+
    2916725915740155255288*a+
    5147440989132201480*b^2+
    10297743044958663048*b*c+
    2024733242645611388568*b+
    119957563700503913664*c+
    6837867996814791680112
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    558462021943689216*a^2+
    1116924043887378432*a*b+
    32203055993304411504*a+
    10303676696896564320*b+
    120004604320827003192
def interceptHi (a b:ℕ):ℕ:=
    186154007314563072*a^3+
    558462021943689216*a^2*b+
    278144333345594651616*a^2+
    558462021943689216*a*b^2+
    556062698085118909200*a*b+
    2917573662774609615816*a+
    5153374641070102752*b^2+
    2025083654290907191764*b+
    6839757576426935855304
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source3,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source3,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G3
end MergedPart0
section MergedPart1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G4
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source4,source5,source6]
def scale:ℕ:=216
def denominator:ℕ:=2340451584
def gLo0 (b c:ℕ):ℕ:=
    55123001676891*b+
    475020311572550
def FY (b c:ℕ):ℕ:=
    2765190256119560124*b+
    22327670929829657000
def HV (b c:ℕ):ℕ:=
    677654740019026519200*b^2+
    1339996501121000383008*b*c+
    161327136164993905380768*b+
    12453411188485380652416*c+
    447707888581307893896384
def gLo1 (b c:ℕ):ℕ:=
    55123001676891*b+
    53705626096596*c+
    6092995262013350
def GC (b c:ℕ):ℕ:=
    2765190256119560124*b+
    2694089027509641744*c+
    302646518363846207000
def HX (b c:ℕ):ℕ:=
    677404658298326680224*b^2+
    1339746419400300544032*b*c+
    161326520015357806812000*b+
    12451702296372575256576*c+
    447711030339003017360064
def gLo2 (b c:ℕ):ℕ:=
    2473938911232*b^2+
    4947877822464*b*c+
    2893224296133117*b+
    188845957072176*c+
    9701016328084202
def FZ (b c:ℕ):ℕ:=
    124102671543042048*b^2+
    248205343086084096*b*c+
    143934705207305088228*b+
    8872769398610340384*c+
    481837784964939239528
def HW (b c:ℕ):ℕ:=
    677252364942772291104*b^2+
    1339594126044746154912*b*c+
    161323985317419711870048*b+
    12450887927478310609728*c+
    447702160772523077546688
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    1340621705422749980448*b+
    12457727503686107254656
def interceptLo (b:ℕ):ℕ:=
    678279944320776116640*b^2+
    161366541075766844249184*b+
    447889359789759619605312
def gHi0 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    193725075047368*a+
    58833910043739*b+
    665034459378702
def GA (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    9117525472717871872*a+
    2951344263434123196*b+
    31259041448419169448
def HS (a b c:ℕ):ℕ:=
    26613806498912590848*a^3+
    80033790051122264064*a^2*b+
    80226160605506755584*a^2*c+
    29065091788035270657792*a^2+
    80226160605506755584*a*b^2+
    160644691765398002688*a*b*c+
    60628615923148456247136*a*b+
    4520692388383896425472*a*c+
    307490636710861581449664*a+
    744477812097884733600*b^2+
    1473835015833101303328*b*c+
    221835508827999513728256*b+
    16853667946172044686720*c+
    726133240724556260172672
def gHi1 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    4947877822464*a*c+
    2665628087081848*a+
    58833910043739*b+
    57416534463444*c+
    8754912421853982
def GD (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    248205343086084096*a*c+
    132517568976457230112*a+
    2951344263434123196*b+
    2880243034824204816*c+
    434977932386175077688
def HY (a b c:ℕ):ℕ:=
    26536858277158794240*a^3+
    79879893607614670848*a^2*b+
    80149212383752958976*a^2*c+
    29064527677200955700736*a^2+
    80149212383752958976*a*b^2+
    160567743543644206080*a*b*c+
    60627724782371687654496*a*b+
    4519736947865941314048*a*c+
    307490621121810230741568*a+
    744150782155431098016*b^2+
    1473507985890647667744*b*c+
    221834155434030154160064*b+
    16851080561763037976064*c+
    726136854055812594088704
def gHi2 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    4947877822464*a*c+
    2665628087081848*a+
    2473938911232*b^2+
    4947877822464*b*c+
    2898172173955581*b+
    193793834894640*c+
    12364170476254818
def _Q4 (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    248205343086084096*a*c+
    132517568976457230112*a+
    124102671543042048*b^2+
    248205343086084096*b*c+
    144182910550391172324*b+
    9120974741696424480*c+
    614231251269853427592
def HU (a b c:ℕ):ℕ:=
    26488765638562671360*a^3+
    79783708330422425088*a^2*b+
    80101119745156836096*a^2*c+
    29063382781708637728128*a^2+
    80101119745156836096*a*b^2+
    160519650905048083200*a*b*c+
    60626379500885219169888*a*b+
    4519228768923622196736*a*c+
    307482900468770540276928*a+
    743950396161280586016*b^2+
    1473307599896497155744*b*c+
    221830371639882782979264*b+
    16849806106565050334784*c+
    726121360639146685660416
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    80418531159891247104*a^2+
    160837062319782494208*a*b+
    4523097020558316244992*a+
    1474652590689235392288*b+
    16860196522992806616960
def interceptHi (a b:ℕ):ℕ:=
    26806177053297082368*a^3+
    80418531159891247104*a^2*b+
    29080270987551128030976*a^2+
    80418531159891247104*a*b^2+
    60644612697520447709280*a*b+
    307624923650275164575424*a+
    745295386954018822560*b^2+
    221890525772035675075776*b+
    726434012043460096125696
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G4

namespace AV.G5
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source7,source8,source9]
def scale:ℕ:=378
def denominator:ℕ:=7167632976
def gLo0 (b c:ℕ):ℕ:=
    97103071945692*b+
    862162941984460
def FY (b c:ℕ):ℕ:=
    4871078501083693488*b+
    40622357856890904340
def HV (b c:ℕ):ℕ:=
    2087299042787112017976*b^2+
    4190974226522644589280*b*c+
    478695082059237987105624*b+
    38760833874892388014980*c+
    1249872621927614433031248
def gLo1 (b c:ℕ):ℕ:=
    97103071945692*b+
    97953497293869*c+
    9226417084559700
def GC (b c:ℕ):ℕ:=
    4871078501083693488*b+
    4913739238249644516*c+
    457579618700217696600
def HX (b c:ℕ):ℕ:=
    2086916105152290389544*b^2+
    4190591288887822960848*b*c+
    478695097151558979415164*b+
    38757974115730248719172*c+
    1249882209945140018647176
def gLo2 (b c:ℕ):ℕ:=
    4329393094656*b^2+
    8658786189312*b*c+
    5271709334873364*b+
    328496099063895*c+
    15805094736884676
def FZ (b c:ℕ):ℕ:=
    217179675200323584*b^2+
    434359350400647168*b*c+
    262348279902733394016*b+
    15427804727514209940*c+
    784439775676198715064
def HW (b c:ℕ):ℕ:=
    2086056950202370069344*b^2+
    4189732133937902640648*b*c+
    478687547984476611253284*b+
    38752760271331111302864*c+
    1249865883832538796994296
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    4192982194377029794776*b+
    38774464984701672629760
def interceptLo (b:ℕ):ℕ:=
    2089307010641497223472*b^2+
    478806219674145195705180*b+
    1250378342388417563482392
def gHi0 (a b c:ℕ):ℕ:=
    4329393094656*a^2+
    8658786189312*a*b+
    352247720082314*a+
    103597161587676*b+
    1207916539394646
def GA (a b c:ℕ):ℕ:=
    217179675200323584*a^2+
    434359350400647168*a*b+
    16619281044282180656*a+
    5196848013884178864*b+
    56915867731448456004
def HS (a b c:ℕ):ℕ:=
    81475325661779684208*a^3+
    245044568549281683168*a^2*b+
    245663160113224313712*a^2*c+
    77013211850957210529960*a^2+
    245663160113224313712*a*b^2+
    491944911790391257968*a*b*c+
    177631204449093404533776*a*b+
    14057411680997117755560*a*c+
    835461605981558743226424*a+
    2291915244287475174312*b^2+
    4600825221087313532496*b*c+
    655958100437626200197256*b+
    52449440893620371697852*c+
    2008320396214017370523472
def gHi1 (a b c:ℕ):ℕ:=
    4329393094656*a^2+
    8658786189312*a*b+
    8658786189312*a*c+
    4032510660170958*a+
    103597161587676*b+
    104447586935853*c+
    13252433622058530
def GD (a b c:ℕ):ℕ:=
    217179675200323584*a^2+
    434359350400647168*a*b+
    434359350400647168*a*c+
    200185117584961899432*a+
    5196848013884178864*b+
    5239508751050129892*c+
    657438965115454967040
def HY (a b c:ℕ):ℕ:=
    81357498697219183152*a^3+
    244808914620160681056*a^2*b+
    245545333148663812656*a^2*c+
    77012696627678990567592*a^2+
    245545333148663812656*a*b^2+
    491827084825830756912*a*b*c+
    177630188461215802441920*a*b+
    14055860292480578615400*a*c+
    835464975463599099939432*a+
    2291414479688093044824*b^2+
    4600324456487931403008*b*c+
    655957335195998711417052*b+
    52445147572906253762940*c+
    2008333751109896972313720
def gHi2 (a b c:ℕ):ℕ:=
    4329393094656*a^2+
    8658786189312*a*b+
    8658786189312*a*c+
    4032510660170958*a+
    4329393094656*b^2+
    8658786189312*b*c+
    5280368121062676*b+
    337154885253207*c+
    19833276003960978
def _Q4 (a b c:ℕ):ℕ:=
    217179675200323584*a^2+
    434359350400647168*a*b+
    434359350400647168*a*c+
    200185117584961899432*a+
    217179675200323584*b^2+
    434359350400647168*b*c+
    262782639253134041184*b+
    15862164077914857108*c+
    984407713585960290912
def HU (a b c:ℕ):ℕ:=
    81092388026958055776*a^3+
    244278693279638426304*a^2*b+
    245280222478402685280*a^2*c+
    77008773351092680564992*a^2+
    245280222478402685280*a*b^2+
    491561974155569629536*a*b*c+
    177625140919009310991744*a*b+
    14052811519435467429000*a*c+
    835445639177004262221360*a+
    2290290214067911597248*b^2+
    4599200190867749955432*b*c+
    655945268708050374059748*b+
    52437150066132266287608*c+
    2008301746876616961817992
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    246281751677166944256*a^2+
    492563503354333888512*a*b+
    14065055706109566111912*a+
    4603451780505641368536*b+
    52470097436978162038440
def interceptHi (a b:ℕ):ℕ:=
    82093917225722314752*a^3+
    246281751677166944256*a^2*b+
    77056365788210114007408*a^2+
    246281751677166944256*a*b^2+
    177676984945764635847264*a*b+
    835838259074923722890832*a+
    2294541803705803010352*b^2+
    656113781366076754849212*b+
    2009160234422496519792120
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G5

namespace AV.G6
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source10,source10,source10]
def scale:ℕ:=27
def denominator:ℕ:=36569556
def gLo0 (b c:ℕ):ℕ:=
    7138415936163*b+
    60552249349760
def FY (b c:ℕ):ℕ:=
    358091497021680732*b+
    2849887038894392990
def HV (b c:ℕ):ℕ:=
    10920100512101992956*b^2+
    21845110481060673456*b*c+
    2394928020681923520690*b+
    196927009473741375816*c+
    6820692308421393144780
def gLo1 (b c:ℕ):ℕ:=
    7138415936163*b+
    7138415936163*c+
    759148293454650
def GC (b c:ℕ):ℕ:=
    358091497021680732*b+
    358091497021680732*c+
    37706602997885127300
def HX (b c:ℕ):ℕ:=
    10920100512101992956*b^2+
    21845110481060673456*b*c+
    2394928020681923520690*b+
    196927009473741375816*c+
    6820692308421393144780
def gLo2 (b c:ℕ):ℕ:=
    309242363904*b^2+
    618484727808*b*c+
    331356633987834*b+
    23511252928669*c+
    1171275610057704
def FZ (b c:ℕ):ℕ:=
    15512833942880256*b^2+
    31025667885760512*b*c+
    16472049389376130656*b+
    1104356092918964656*c+
    58155369938300079756
def HW (b c:ℕ):ℕ:=
    10920100512101992956*b^2+
    21845110481060673456*b*c+
    2394928020681923520690*b+
    196927009473741375816*c+
    6820692308421393144780
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    21860690492105875764*b+
    197032324859864666406
def interceptLo (b:ℕ):ℕ:=
    10935680523147195264*b^2+
    2395587485698644334311*b+
    6823601900704587836106
def gHi0 (a b c:ℕ):ℕ:=
    309242363904*a^2+
    618484727808*a*b+
    24593601202333*a+
    7602279482019*b+
    84681984646941
def GA (a b c:ℕ):ℕ:=
    15512833942880256*a^2+
    31025667885760512*a*b+
    1158651011719045552*a+
    381360747936001116*b+
    3985268681347393614
def HS (a b c:ℕ):ℕ:=
    414037252598154624*a^3+
    1246921021654076160*a^2*b+
    1251730285513688448*a^2*c+
    452457279085377155976*a^2+
    1251730285513688448*a*b^2+
    2508269834886989184*a*b*c+
    904597035555197020392*a*b+
    71004585961641786408*a*c+
    4736815109242774416576*a+
    11962407539386797948*b^2+
    23934533799489895728*b*c+
    3297649862245283251866*b+
    266051592179686260720*c+
    11105045322923937667716
def gHi1 (a b c:ℕ):ℕ:=
    309242363904*a^2+
    618484727808*a*b+
    618484727808*a*c+
    331975118715642*a+
    7602279482019*b+
    7602279482019*c+
    1090659546265140
def GD (a b c:ℕ):ℕ:=
    15512833942880256*a^2+
    31025667885760512*a*b+
    31025667885760512*a*c+
    16503075057261891168*a+
    381360747936001116*b+
    381360747936001116*c+
    54186408685880973540
def HY (a b c:ℕ):ℕ:=
    414037252598154624*a^3+
    1246921021654076160*a^2*b+
    1251730285513688448*a^2*c+
    452457279085377155976*a^2+
    1251730285513688448*a*b^2+
    2508269834886989184*a*b*c+
    904597035555197020392*a*b+
    71004585961641786408*a*c+
    4736815109242774416576*a+
    11962407539386797948*b^2+
    23934533799489895728*b*c+
    3297649862245283251866*b+
    266051592179686260720*c+
    11105045322923937667716
def gHi2 (a b c:ℕ):ℕ:=
    309242363904*a^2+
    618484727808*a*b+
    618484727808*a*c+
    331975118715642*a+
    309242363904*b^2+
    618484727808*b*c+
    331975118715642*b+
    24129737656477*c+
    1502941486409442
def _Q4 (a b c:ℕ):ℕ:=
    15512833942880256*a^2+
    31025667885760512*a*b+
    31025667885760512*a*c+
    16503075057261891168*a+
    15512833942880256*b^2+
    31025667885760512*b*c+
    16503075057261891168*b+
    1135381760804725168*c+
    74642932161619090668
def HU (a b c:ℕ):ℕ:=
    414037252598154624*a^3+
    1246921021654076160*a^2*b+
    1251730285513688448*a^2*c+
    452457279085377155976*a^2+
    1251730285513688448*a*b^2+
    2508269834886989184*a*b*c+
    904597035555197020392*a*b+
    71004585961641786408*a*c+
    4736815109242774416576*a+
    11962407539386797948*b^2+
    23934533799489895728*b*c+
    3297649862245283251866*b+
    266051592179686260720*c+
    11105045322923937667716
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    1256539549373300736*a^2+
    2513079098746601472*a*b+
    71063800029028604592*a+
    23954923074394710324*b+
    266211312369336757206
def interceptHi (a b:ℕ):ℕ:=
    418846516457766912*a^3+
    1256539549373300736*a^2*b+
    452718471220926543072*a^2+
    1256539549373300736*a*b^2+
    904878616965651222084*a*b+
    4739018809965725160252*a+
    11982796814291612544*b^2+
    3298581290144739042603*b+
    11109902233058393327910
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source10,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source10,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G6

namespace AV.G7
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source11,source12,source13]
def scale:ℕ:=840
def denominator:ℕ:=35395718400
def gLo0 (b c:ℕ):ℕ:=
    227123608966120*b+
    1962085248063300
def FY (b c:ℕ):ℕ:=
    11393428720176443680*b+
    92587857795363943200
def HV (b c:ℕ):ℕ:=
    10785983223359684323200*b^2+
    21508962828595222216320*b*c+
    2168047537654422938304000*b+
    196366532765247061049280*c+
    5894992025716804188326400
def gLo1 (b c:ℕ):ℕ:=
    227123608966120*b+
    225611741680472*c+
    20347208929532600
def GC (b c:ℕ):ℕ:=
    11393428720176443680*b+
    11317587409659197408*c+
    1009021015564106470400
def HX (b c:ℕ):ℕ:=
    10782201123262680585600*b^2+
    21505180728498218478720*b*c+
    2168015550985674519931200*b+
    196340555065947415092480*c+
    5894926189533028136294400
def gLo2 (b c:ℕ):ℕ:=
    9620873543680*b^2+
    19241747087360*b*c+
    10210601683832160*b+
    748511705502288*c+
    33037459100487080
def FZ (b c:ℕ):ℕ:=
    482621500445163520*b^2+
    965243000890327040*b*c+
    507534073596969723840*b+
    35213066559423400032*c+
    1638608883417091277120
def HW (b c:ℕ):ℕ:=
    10780261584751396617600*b^2+
    21503241189986934510720*b*c+
    2167997669798257110676800*b+
    196328590534981378850880*c+
    5894885126004806290195200
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    21517860461515737419520*b+
    196426088732237149188480
def interceptLo (b:ℕ):ℕ:=
    10794880856280199526400*b^2+
    2168519465344009408276800*b+
    5897130194988851166768000
def gHi0 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    796736485529530*a+
    241554919281640*b+
    2744390349876990
def GA (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    37632214424709967720*a+
    12117360970844188960*b+
    129496136287352513160
def HS (a b c:ℕ):ℕ:=
    402638217995357702400*a^3+
    1210678496364652761600*a^2*b+
    1213442338743232416000*a^2*c+
    377119775657136464736000*a^2+
    1213442338743232416000*a*b^2+
    2429648519865044486400*a*b*c+
    810611408423954481859200*a*b+
    70789532361638364348480*a*c+
    4015419366004201668038400*a+
    11796724531915948060800*b^2+
    23533209288086329345920*b*c+
    2976840161398526793283200*b+
    265334516604656218863360*c+
    9533288846035640675808000
def gHi1 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8886171380799860*a+
    241554919281640*b+
    240043051995992*c+
    29218948926616620
def GD (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    441095351875657426640*a+
    12117360970844188960*b+
    12041519660326942688*c+
    1449392431507042499280
def HY (a b c:ℕ):ℕ:=
    401474494888587321600*a^3+
    1208351050151112000000*a^2*b+
    1212278615636462035200*a^2*c+
    377103001312635905126400*a^2+
    1212278615636462035200*a*b^2+
    2428484796758274105600*a*b*c+
    810589688256250148131200*a*b+
    70775034309786754946880*a*c+
    4015338757737205792924800*a+
    11791778708712173942400*b^2+
    23528263464882555227520*b*c+
    2976788782008287581944000*b+
    265295204576611733885760*c+
    9533158012206262537891200
def gHi2 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8886171380799860*a+
    9620873543680*b^2+
    19241747087360*b*c+
    10229843430919520*b+
    767753452589648*c+
    41914009607743260
def _Q4 (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    441095351875657426640*a+
    482621500445163520*b^2+
    965243000890327040*b*c+
    508499316597860050880*b+
    36178309560313727072*c+
    2079221613792303540240
def HU (a b c:ℕ):ℕ:=
    400892633335202131200*a^3+
    1207187327044341619200*a^2*b+
    1211696754083076844800*a^2*c+
    377094056523063631180800*a^2+
    1211696754083076844800*a*b^2+
    2427902935204888915200*a*b*c+
    810578222066613205027200*a*b+
    70768197435794598089280*a*c+
    4015292932077495482736000*a+
    11789257308647504784000*b^2+
    23525742064817886069120*b*c+
    2976760598354339999966400*b+
    265276985033206925976960*c+
    9533079485946349270358400
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    1216206181121812070400*a^2+
    2432412362243624140800*a*b+
    70823256091017748476480*a+
    23544870763385424203520*b+
    265425032458647111476160
def interceptHi (a b:ℕ):ℕ:=
    405402060373937356800*a^3+
    1216206181121812070400*a^2*b+
    377303825474697104592000*a^2+
    1216206181121812070400*a*b^2+
    810807119716814216572800*a*b+
    4017016632912206952067200*a+
    11808386007215042918400*b^2+
    2977502272696215838660800*b+
    9536842996240510878076800
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G7
end MergedPart1
section MergedPart2
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G8
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source11,source14,source13]
def scale:ℕ:=840
def denominator:ℕ:=35395718400
def gLo0 (b c:ℕ):ℕ:=
    223343940752000*b+
    1957274690704500
def FY (b c:ℕ):ℕ:=
    11203825443883328000*b+
    92346540996017100000
def HV (b c:ℕ):ℕ:=
    10626667982810685052800*b^2+
    21349647588046222945920*b*c+
    2206239098568517527782400*b+
    196164250927752571020480*c+
    5943900352633861469980800
def gLo1 (b c:ℕ):ℕ:=
    223343940752000*b+
    225611741680472*c+
    20342398372173800
def GC (b c:ℕ):ℕ:=
    11203825443883328000*b+
    11317587409659197408*c+
    1008779698764759627200
def HX (b c:ℕ):ℕ:=
    10623298034647329158400*b^2+
    21346277639882867051520*b*c+
    2206199516395427595604800*b+
    196139533929040170295680*c+
    5943786183556004220729600
def gLo2 (b c:ℕ):ℕ:=
    9620873543680*b^2+
    19241747087360*b*c+
    10516754809175880*b+
    748511705502288*c+
    33427114246549880
def FZ (b c:ℕ):ℕ:=
    482621500445163520*b^2+
    965243000890327040*b*c+
    522891938976712093920*b+
    35213066559423400032*c+
    1658155544164185576320
def HW (b c:ℕ):ℕ:=
    10620946344202397347200*b^2+
    21343925949437935240320*b*c+
    2206189230712351700155200*b+
    196126308697486888822080*c+
    5943793452921863571849600
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    21358545220966738149120*b+
    196223806894742659159680
def interceptLo (b:ℕ):ℕ:=
    10635565615731200256000*b^2+
    2206711026258103997755200*b+
    5946038521905908448422400
def gHi0 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    796736485529530*a+
    237775251067520*b+
    2739579792518190
def GA (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    37632214424709967720*a+
    11927757694551073280*b+
    129254819488005669960
def HS (a b c:ℕ):ℕ:=
    402638217995357702400*a^3+
    1210678496364652761600*a^2*b+
    1213442338743232416000*a^2*c+
    377123897176472943168000*a^2+
    1213442338743232416000*a*b^2+
    2429648519865044486400*a*b*c+
    823516088373811769059200*a*b+
    70789726315489492745280*a*c+
    4031878648209489336470400*a+
    11637409291366948790400*b^2+
    23373894047537330075520*b*c+
    3027936402262478669961600*b+
    265132428721012857231360*c+
    9598652333638649147462400
def gHi1 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8886171380799860*a+
    237775251067520*b+
    240043051995992*c+
    29214138369257820
def GD (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    441095351875657426640*a+
    11927757694551073280*b+
    12041519660326942688*c+
    1449151114707695656080
def HY (a b c:ℕ):ℕ:=
    401619960276933619200*a^3+
    1208641980927804595200*a^2*b+
    1212424081024808332800*a^2*c+
    377105164777334800464000*a^2+
    1212424081024808332800*a*b^2+
    2428630262146620403200*a*b*c+
    823492967768791846377600*a*b+
    70776367742698232892480*a*c+
    4031768405092977591840000*a+
    11633021085485168812800*b^2+
    23369505841655550097920*b*c+
    3027875735999805663268800*b+
    265095371407227620736960*c+
    9598445635585699872201600
def gHi2 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8886171380799860*a+
    9620873543680*b^2+
    19241747087360*b*c+
    10535996556263240*b+
    767753452589648*c+
    42303664753806060
def _Q4 (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    441095351875657426640*a+
    482621500445163520*b^2+
    965243000890327040*b*c+
    523857181977602420960*b+
    36178309560313727072*c+
    2098768274539397839440
def HU (a b c:ℕ):ℕ:=
    400892633335202131200*a^3+
    1207187327044341619200*a^2*b+
    1211696754083076844800*a^2*c+
    377098178042400109612800*a^2+
    1211696754083076844800*a*b^2+
    2427902935204888915200*a*b*c+
    823482902016470492227200*a*b+
    70768391389645726486080*a*c+
    4031752214282783151168000*a+
    11629942068098505513600*b^2+
    23366426824268886798720*b*c+
    3027856839218291876644800*b+
    265074897149563564344960*c+
    9598442973549357742012800
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    1216206181121812070400*a^2+
    2432412362243624140800*a*b+
    70823450044868876873280*a+
    23385555522836424933120*b+
    265222944575003749844160
def interceptHi (a b:ℕ):ℕ:=
    405402060373937356800*a^3+
    1216206181121812070400*a^2*b+
    377307946994033583024000*a^2+
    1216206181121812070400*a*b^2+
    823711799666671503772800*a*b+
    4033475915117494620499200*a+
    11649070766666043648000*b^2+
    3028598513560167715339200*b+
    9602206483843519349731200
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G8

namespace AV.G9
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source15,source16,source17]
def scale:ℕ:=840
def denominator:ℕ:=35395718400
def gLo0 (b c:ℕ):ℕ:=
    230903277180240*b+
    1996961420600300
def FY (b c:ℕ):ℕ:=
    11583031996469559360*b+
    94337386114510011200
def HV (b c:ℕ):ℕ:=
    10945395440834247792000*b^2+
    21668375046069785685120*b*c+
    2038973603459465504160000*b+
    198507784388400818694720*c+
    5569757874438339042921600
def gLo1 (b c:ℕ):ℕ:=
    230903277180240*b+
    225611741680472*c+
    19329788570832600
def GC (b c:ℕ):ℕ:=
    11583031996469559360*b+
    11317587409659197408*c+
    957983140690279670400
def HX (b c:ℕ):ℕ:=
    10941564852274461955200*b^2+
    21664544457509999848320*b*c+
    2038949529668213717520000*b+
    198480230813968269405120*c+
    5569732728955068115276800
def gLo2 (b c:ℕ):ℕ:=
    9620873543680*b^2+
    19241747087360*b*c+
    9526481737076440*b+
    753803241002056*c+
    31144517302485480
def FZ (b c:ℕ):ℕ:=
    482621500445163520*b^2+
    965243000890327040*b*c+
    473215880587915785760*b+
    35478511146233761984*c+
    1543651351062139014720
def HW (b c:ℕ):ℕ:=
    10939213161829530144000*b^2+
    21662192767065068037120*b*c+
    2038922709419329126243200*b+
    198467272268960289477120*c+
    5569657342640684981251200
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    21677272678990300888320*b+
    198567473698663557606720
def interceptLo (b:ℕ):ℕ:=
    10954293073754762995200*b^2+
    2039431263418878341443200*b+
    5571824713621432865222400
def gHi0 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    809965324278950*a+
    245334587495760*b+
    2792495361163410
def GA (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    38295825891735872600*a+
    12306964247137304640*b+
    131909276073524486040
def HS (a b c:ℕ):ℕ:=
    402638217995357702400*a^3+
    1210678496364652761600*a^2*b+
    1213442338743232416000*a^2*c+
    358152534108504773702400*a^2+
    1213442338743232416000*a*b^2+
    2429648519865044486400*a*b*c+
    762817030213105829136000*a*b+
    71570812239190906272960*a*c+
    3802844857166461899676800*a+
    11956136749390511529600*b^2+
    23692621505560892814720*b*c+
    2799971848992720706416000*b+
    268257048105362518433280*c+
    9014447427468067453075200
def gHi1 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8436390863319580*a+
    245334587495760*b+
    240043051995992*c+
    27751748050436340
def GD (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    418532561996776660720*a+
    12306964247137304640*b+
    12041519660326942688*c+
    1375791766754334933360
def HY (a b c:ℕ):ℕ:=
    401474494888587321600*a^3+
    1208351050151112000000*a^2*b+
    1212278615636462035200*a^2*c+
    358138766048696704243200*a^2+
    1212278615636462035200*a*b^2+
    2428484796758274105600*a*b*c+
    762798267841631203459200*a*b+
    71555780814248693780160*a*c+
    3802793419579274802259200*a+
    11951142437723955312000*b^2+
    23687627193894336597120*b*c+
    2799931340276207834860800*b+
    268215626829094527031680*c+
    9014383448734310727091200
def gHi2 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    8436390863319580*a+
    9620873543680*b^2+
    19241747087360*b*c+
    9545723484163800*b+
    773044988089416*c+
    39571287292261380
def _Q4 (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    418532561996776660720*a+
    482621500445163520*b^2+
    965243000890327040*b*c+
    474181123588806112800*b+
    36443754147124089024*c+
    1961701291558470511920
def HU (a b c:ℕ):ℕ:=
    400747167946855833600*a^3+
    1206896396267649024000*a^2*b+
    1211551288694730547200*a^2*c+
    358125766744377033091200*a^2+
    1211551288694730547200*a*b^2+
    2427757469816542617600*a*b*c+
    762782189519924869008000*a*b+
    71547901438121751572160*a*c+
    3802718611933843801651200*a+
    11948063420337292012800*b^2+
    23684548176507673297920*b*c+
    2799889896359500372108800*b+
    268195516234901336383680*c+
    9014245526751874532121600
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    1216206181121812070400*a^2+
    2432412362243624140800*a*b+
    71604584457033072500160*a+
    23704282980859987672320*b+
    268347745791088843918080
def interceptHi (a b:ℕ):ℕ:=
    405402060373937356800*a^3+
    1216206181121812070400*a^2*b+
    358331395660547728944000*a^2+
    1216206181121812070400*a*b^2+
    763007553240447879235200*a*b+
    3804391541339641427817600*a+
    11967798224689606387200*b^2+
    2800614504294718434489600*b+
    9017884853114676427929600
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G9

namespace AV.G10
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source18,source19,source20]
def scale:ℕ:=216
def denominator:ℕ:=2340451584
def gLo0 (b c:ℕ):ℕ:=
    57674277721422*b+
    497165824473180
def FY (b c:ℕ):ℕ:=
    2893172467617413208*b+
    23438578438976860320
def HV (b c:ℕ):ℕ:=
    705294088438703173056*b^2+
    1392208434148264828992*b*c+
    139522305704311392810624*b+
    12742691123989249752384*c+
    384771472395638134234752
def gLo1 (b c:ℕ):ℕ:=
    57674277721422*b+
    55973427025068*c+
    5226916600792300
def GC (b c:ℕ):ℕ:=
    2893172467617413208*b+
    2807850993285511152*c+
    259200548402353454800
def HX (b c:ℕ):ℕ:=
    705016754222798864448*b^2+
    1391931099932360520384*b*c+
    139521019129185821460480*b+
    12740757799526303731776*c+
    384771937656462304534272
def gLo2 (b c:ℕ):ℕ:=
    2473938911232*b^2+
    4947877822464*b*c+
    2509682464105290*b+
    188845957072176*c+
    8343539232661732
def FZ (b c:ℕ):ℕ:=
    124102671543042048*b^2+
    248205343086084096*b*c+
    124694712745461174600*b+
    8872769398610340384*c+
    413741303950166454448
def HW (b c:ℕ):ℕ:=
    704888507186542536768*b^2+
    1391802852896104192704*b*c+
    139519193141469907852992*b+
    12740054845275363479040*c+
    384766009915985346233088
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    1392864097121125304256*b+
    12747150915604595514432
def interceptLo (b:ℕ):ℕ:=
    705949751411563648320*b^2+
    139557705022392476457600*b+
    384932153596783792356864
def gHi0 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    202040345118432*a+
    61385186088270*b+
    695495242350396
def GA (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    9534652680562726368*a+
    3079326474931976280*b+
    32787076165411227264
def HS (a b c:ℕ):ℕ:=
    26604187971193366272*a^3+
    80014552995683814912*a^2*b+
    80216542077787531008*a^2*c+
    24917394259887571320192*a^2+
    80216542077787531008*a*b^2+
    160635073237678778112*a*b*c+
    52325065595450892729024*a*b+
    4610793468354107516928*a*c+
    263740081958266646862720*a+
    772107541989842162880*b^2+
    1526037330332646524736*b*c+
    191727147276674876089152*b+
    17233058580173844102720*c+
    623593957695911546037120
def gHi1 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    4947877822464*a*c+
    2283125663812904*a+
    61385186088270*b+
    59684335391916*c+
    7506331337363988
def GD (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    248205343086084096*a*c+
    113329717415593923296*a+
    3079326474931976280*b+
    2994005000600074224*c+
    372344110863819018672
def HY (a b c:ℕ):ℕ:=
    26517621221720345088*a^3+
    79841419496737772544*a^2*b+
    80129975328314509824*a^2*c+
    24916533199025576914944*a^2+
    80129975328314509824*a*b^2+
    160548506488205756928*a*b*c+
    52323840633623520993984*a*b+
    4609711383875618598144*a*c+
    263737865258765449241472*a+
    771743641024464833088*b^2+
    1525673429367269194944*b*c+
    191724808873220879046336*b+
    17230129737981882184512*c+
    623592980751347040099456
def gHi2 (a b c:ℕ):ℕ:=
    2473938911232*a^2+
    4947877822464*a*b+
    4947877822464*a*c+
    2283125663812904*a+
    2473938911232*b^2+
    4947877822464*b*c+
    2514630341927754*b+
    193793834894640*c+
    10624190957563404
def _Q4 (a b c:ℕ):ℕ:=
    124102671543042048*a^2+
    248205343086084096*a*b+
    248205343086084096*a*c+
    113329717415593923296*a+
    124102671543042048*b^2+
    248205343086084096*b*c+
    124942918088547258696*b+
    9120974741696424480*c+
    526946918694217335696
def HU (a b c:ℕ):ℕ:=
    26479147110843446784*a^3+
    79764471274983975936*a^2*b+
    80091501217437611520*a^2*c+
    24915707696792283247872*a^2+
    80091501217437611520*a*b^2+
    160510032377328858624*a*b*c+
    52322848410243094100928*a*b+
    4609291374782956389888*a*c+
    263732555051430868744704*a+
    771576919877331607104*b^2+
    1525506708220135968960*b*c+
    191722067610346292342400*b+
    17229045248749156621824*c+
    623582529831657918070272
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    80418531159891247104*a^2+
    160837062319782494208*a*b+
    4613292682729997061888*a+
    1526894982387610716096*b+
    17239815597082975693632
def interceptHi (a b:ℕ):ℕ:=
    26806177053297082368*a^3+
    80418531159891247104*a^2*b+
    24931161517672992575232*a^2+
    80418531159891247104*a*b^2+
    52339690505291278175424*a*b+
    263859913630471501049472*a+
    772965194044806354240*b^2+
    191776767526432137750336*b+
    623860905300558740807040
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G10

namespace AV.G11
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source21,source5,source22]
def scale:ℕ:=360
def denominator:ℕ:=6501254400
def gLo0 (b c:ℕ):ℕ:=
    91871669461485*b+
    804299443743210
def FY (b c:ℕ):ℕ:=
    4608650426865933540*b+
    37844797329441484440
def HV (b c:ℕ):ℕ:=
    1882396542941090388000*b^2+
    3756363357957111943200*b*c+
    428051854243294484335200*b+
    34479918006181334092800*c+
    1143237118386401901432000
def gLo1 (b c:ℕ):ℕ:=
    91871669461485*b+
    91399210934720*c+
    9043137020146530
def GC (b c:ℕ):ℕ:=
    4608650426865933540*b+
    4584950017329294080*c+
    448635765545644726920
def HX (b c:ℕ):ℕ:=
    1881777572870269917600*b^2+
    3755744387886291472800*b*c+
    428052053992796871717600*b+
    34475427132517989345600*c+
    1143253501450215790708800
def gLo2 (b c:ℕ):ℕ:=
    4123231518720*b^2+
    8246463037440*b*c+
    4822040493555195*b+
    307183925358720*c+
    15056505463597950
def FZ (b c:ℕ):ℕ:=
    206837785905070080*b^2+
    413675571810140160*b*c+
    239891175345508480380*b+
    14408742445097669280*c+
    747287876547466447800
def HW (b c:ℕ):ℕ:=
    1880998294004129037600*b^2+
    3754965109020150592800*b*c+
    428041949290054889767200*b+
    34470747005194892880000*c+
    1143222409405836636609600
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3758175737948651018400*b+
    34492163819500022673600
def interceptLo (b:ℕ):ℕ:=
    1884208922932629463200*b^2+
    428163223605044197932000*b+
    1143748861035650796945600
def gHi0 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    328418638459656*a+
    98056516739565*b+
    1126533203467506
def GA (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    15473960593093022784*a+
    4918907105723538660*b+
    53008499665653908184
def HS (a b c:ℕ):ℕ:=
    73900522142203795200*a^3+
    222262647210232819200*a^2*b+
    222823727993854252800*a^2*c+
    71901187726522036158720*a^2+
    222823727993854252800*a*b^2+
    446208536771329939200*a*b*c+
    159577639204369903895520*a*b+
    12521186353091988023040*a*c+
    772216383382811728453440*a+
    2067989469472032026400*b^2+
    4128110291802616653600*b*c+
    587295537827977139757120*b+
    46666587658802452208640*c+
    1843551751825731416670720
def gHi1 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3953498422622148*a+
    98056516739565*b+
    97584058212800*c+
    12990450564033318
def GD (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    196321630899223110672*a+
    4918907105723538660*b+
    4895206696186899200*c+
    644647138187987238552
def HY (a b c:ℕ):ℕ:=
    73713495214329984000*a^3+
    221888593354485196800*a^2*b+
    222636701065980441600*a^2*c+
    71900463425258639790720*a^2+
    222636701065980441600*a*b^2+
    446021509843456128000*a*b*c+
    159576108906107813245920*a*b+
    12518750549769717392640*a*c+
    772222620053233497695040*a+
    2067183472473337744800*b^2+
    4127304294803922372000*b*c+
    587294581333073184112320*b+
    46659848008744710642240*c+
    1843574908834302597745920
def gHi2 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3953498422622148*a+
    4123231518720*b^2+
    8246463037440*b*c+
    4830286956592635*b+
    315430388396160*c+
    19005880654701378
def _Q4 (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    196321630899223110672*a+
    206837785905070080*b^2+
    413675571810140160*b*c+
    240304850917318620540*b+
    14822418016907809440*c+
    943402669660784488392
def HU (a b c:ℕ):ℕ:=
    73473032021349369600*a^3+
    221407666968523968000*a^2*b+
    222396237872999827200*a^2*c+
    71895720393866178213120*a^2+
    222396237872999827200*a*b^2+
    445781046650475513600*a*b*c+
    159570346132656230173920*a*b+
    12516003034833042167040*a*c+
    772193533608265566738240*a+
    2066163730414216250400*b^2+
    4126284552744800877600*b*c+
    587279194783265580318720*b+
    46652660829677919565440*c+
    1843519232913154993653120
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    223384808777475686400*a^2+
    446769617554951372800*a*b+
    12528084085026314423040*a+
    4130483752577777162400*b+
    46685170123271845755840
def interceptHi (a b:ℕ):ℕ:=
    74461602925825228800*a^3+
    223384808777475686400*a^2*b+
    71944194842898007374720*a^2+
    223384808777475686400*a*b^2+
    159623019781521035620320*a*b+
    772595682632302758344640*a+
    2070362930247192535200*b^2+
    587451165605310742211520*b+
    1844400347688878992293120
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G11
end MergedPart2
section MergedPart3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G12
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source23,source5,source24]
def scale:ℕ:=360
def denominator:ℕ:=6501254400
def gLo0 (b c:ℕ):ℕ:=
    91871669461485*b+
    809453549202330
def FY (b c:ℕ):ℕ:=
    4608650426865933540*b+
    38103347875692780120
def HV (b c:ℕ):ℕ:=
    1882472244316658359200*b^2+
    3722310469599919092000*b*c+
    424234400037720248210400*b+
    34914685098760678267200*c+
    1124147956398012185083200
def gLo1 (b c:ℕ):ℕ:=
    91871669461485*b+
    89509376827660*c+
    8831818696322610
def GC (b c:ℕ):ℕ:=
    4608650426865933540*b+
    4490148379182736240*c+
    438035193149341604040
def HX (b c:ℕ):ℕ:=
    1881777572870269917600*b^2+
    3721615798153530650400*b*c+
    424232688510953307741600*b+
    34909938176225107723200*c+
    1124156683502720861371200
def gLo2 (b c:ℕ):ℕ:=
    4123231518720*b^2+
    8246463037440*b*c+
    4822040493555195*b+
    314743261786960*c+
    14845187139774030
def FZ (b c:ℕ):ℕ:=
    206837785905070080*b^2+
    413675571810140160*b*c+
    239891175345508480380*b+
    14787948997683900640*c+
    736687304151163324920
def HW (b c:ℕ):ℕ:=
    1880922592628561066400*b^2+
    3720760817911821799200*b*c+
    424223831951116437679200*b+
    34904855050300741752000*c+
    1124133723133385802436800
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3724047148215890196000*b+
    34926674863207141051200
def interceptLo (b:ℕ):ℕ:=
    1884208922932629463200*b^2+
    424343858123200633956000*b+
    1124652043088155867608000
def gHi0 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    330686439388128*a+
    98056516739565*b+
    1133955109855098
def GA (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    15587722558868892192*a+
    4918907105723538660*b+
    53380812177681073272
def HS (a b c:ℕ):ℕ:=
    73927240274757196800*a^3+
    222316083475339622400*a^2*b+
    222850446126407654400*a^2*c+
    70221754905246774829440*a^2+
    222850446126407654400*a*b^2+
    446235254903883340800*a*b*c+
    157898308802602763939040*a*b+
    12698926654083944670720*a*c+
    756641372566356581417280*a+
    2068091888980153399200*b^2+
    4094084121577977204000*b*c+
    581798699784370656872640*b+
    47279068334241199629120*c+
    1810567038560294368016640
def gHi1 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3860518584554796*a+
    98056516739565*b+
    95694224105740*c+
    12686152402142046
def GD (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    191657390302412464944*a+
    4918907105723538660*b+
    4800405058040341360*c+
    629382325194873469944
def HY (a b c:ℕ):ℕ:=
    73713495214329984000*a^3+
    221888593354485196800*a^2*b+
    222636701065980441600*a^2*c+
    70220187930707011059840*a^2+
    222636701065980441600*a*b^2+
    446021509843456128000*a*b*c+
    157895833411556184515040*a*b+
    12696272652645180472320*a*c+
    756641329263436162783680*a+
    2067183472473337744800*b^2+
    4093175705071161549600*b*c+
    581794940356677991405440*b+
    47271881155327292099520*c+
    1810577075591561962227840
def gHi2 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3860518584554796*a+
    4123231518720*b^2+
    8246463037440*b*c+
    4830286956592635*b+
    322989724824400*c+
    18701582492810106
def _Q4 (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    191657390302412464944*a+
    206837785905070080*b^2+
    413675571810140160*b*c+
    240304850917318620540*b+
    15201624569494040800*c+
    928137856667670719784
def HU (a b c:ℕ):ℕ:=
    73446313888795968000*a^3+
    221354230703417164800*a^2*b+
    222369519740446425600*a^2*c+
    70215751105737978349440*a^2+
    222369519740446425600*a*b^2+
    445754328517922112000*a*b*c+
    157890274425019908937440*a*b+
    12693253503326904875520*a*c+
    756617161268291427391680*a+
    2066061310906094877600*b^2+
    4092053543503918682400*b*c+
    581781059172955913797440*b+
    47264046061410184547520*c+
    1810534116870725666595840
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    223384808777475686400*a^2+
    446769617554951372800*a*b+
    12705606187901777502720*a+
    4096355162845016340000*b+
    47297203269854427213120
def interceptHi (a b:ℕ):ℕ:=
    74461602925825228800*a^3+
    223384808777475686400*a^2*b+
    70263919348346378643840*a^2+
    223384808777475686400*a*b^2+
    157942744286969406889440*a*b+
    757014391842505423433280*a+
    2070362930247192535200*b^2+
    581951524628915549504640*b+
    1811402514446138356775040
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G12

namespace AV.G13
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source25,source5,source24]
def scale:ℕ:=360
def denominator:ℕ:=6501254400
def gLo0 (b c:ℕ):ℕ:=
    91871669461485*b+
    809453549202330
def FY (b c:ℕ):ℕ:=
    4608650426865933540*b+
    38103347875692780120
def HV (b c:ℕ):ℕ:=
    1882405448985274855200*b^2+
    3756372264001296410400*b*c+
    424233778437397089612000*b+
    34573089716312724504000*c+
    1124146519857832382568000
def gLo1 (b c:ℕ):ℕ:=
    91871669461485*b+
    91399210934720*c+
    8831818696322610
def GC (b c:ℕ):ℕ:=
    4608650426865933540*b+
    4584950017329294080*c+
    438035193149341604040
def HX (b c:ℕ):ℕ:=
    1881786478914454384800*b^2+
    3755753293930475940000*b*c+
    424233978186899476994400*b+
    34568598842649379756800*c+
    1124162902921646271844800
def gLo2 (b c:ℕ):ℕ:=
    4123231518720*b^2+
    8246463037440*b*c+
    4822040493555195*b+
    307183925358720*c+
    14845187139774030
def FZ (b c:ℕ):ℕ:=
    206837785905070080*b^2+
    413675571810140160*b*c+
    239891175345508480380*b+
    14408742445097669280*c+
    736687304151163324920
def HW (b c:ℕ):ℕ:=
    1880931498672745533600*b^2+
    3754898313688767088800*b*c+
    424225121627062606932000*b+
    34563515716725013785600*c+
    1124139942552311212910400
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3758184643992835485600*b+
    34585335529631413084800
def interceptLo (b:ℕ):ℕ:=
    1884217828976813930400*b^2+
    424345147799146803208800*b+
    1124658262507081278081600
def gHi0 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    330686439388128*a+
    98056516739565*b+
    1133955109855098
def GA (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    15587722558868892192*a+
    4918907105723538660*b+
    53380812177681073272
def HS (a b c:ℕ):ℕ:=
    73900522142203795200*a^3+
    222262647210232819200*a^2*b+
    222823727993854252800*a^2*c+
    70221357534179630787840*a^2+
    222823727993854252800*a*b^2+
    446208536771329939200*a*b*c+
    157897817918071682991840*a*b+
    12562167378903854411520*a*c+
    756639452750970595942080*a+
    2067998375516216493600*b^2+
    4128119197846801120800*b*c+
    581797640735781524130240*b+
    46800740394745709008320*c+
    1810564052857663170666240
def gHi1 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3860518584554796*a+
    98056516739565*b+
    97584058212800*c+
    12686152402142046
def GD (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    191657390302412464944*a+
    4918907105723538660*b+
    4895206696186899200*c+
    629382325194873469944
def HY (a b c:ℕ):ℕ:=
    73713495214329984000*a^3+
    221888593354485196800*a^2*b+
    222636701065980441600*a^2*c+
    70220633232916234419840*a^2+
    222636701065980441600*a*b^2+
    446021509843456128000*a*b*c+
    157896287619809592342240*a*b+
    12559731575581583781120*a*c+
    756645689421392365183680*a+
    2067192378517522212000*b^2+
    4127313200848106839200*b*c+
    581796684240877568485440*b+
    46794000744687967441920*c+
    1810587209866234351741440
def gHi2 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3860518584554796*a+
    4123231518720*b^2+
    8246463037440*b*c+
    4830286956592635*b+
    315430388396160*c+
    18701582492810106
def _Q4 (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    191657390302412464944*a+
    206837785905070080*b^2+
    413675571810140160*b*c+
    240304850917318620540*b+
    14822418016907809440*c+
    928137856667670719784
def HU (a b c:ℕ):ℕ:=
    73446313888795968000*a^3+
    221354230703417164800*a^2*b+
    222369519740446425600*a^2*c+
    70216196407947201709440*a^2+
    222369519740446425600*a*b^2+
    445754328517922112000*a*b*c+
    157890728633273316764640*a*b+
    12556712426263308184320*a*c+
    756621521426247629791680*a+
    2066070216950279344800*b^2+
    4126191039280863972000*b*c+
    581782803057155490877440*b+
    46786165650770859889920*c+
    1810544251145398056109440
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    223384808777475686400*a^2+
    446769617554951372800*a*b+
    12569065110838180811520*a+
    4130492658621961629600*b+
    46819322859215102555520
def interceptHi (a b:ℕ):ℕ:=
    74461602925825228800*a^3+
    223384808777475686400*a^2*b+
    70264364650555602003840*a^2+
    223384808777475686400*a*b^2+
    157943198495222814716640*a*b+
    757018752000461625833280*a+
    2070371836291377002400*b^2+
    581953268513115126584640*b+
    1811412648720810746288640
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G13

namespace AV.G14
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source25,source5,source26]
def scale:ℕ:=360
def denominator:ℕ:=6501254400
def gLo0 (b c:ℕ):ℕ:=
    91871669461485*b+
    806876496472770
def FY (b c:ℕ):ℕ:=
    4608650426865933540*b+
    37974072602567132280
def HV (b c:ℕ):ℕ:=
    1882396542941090388000*b^2+
    3756363357957111943200*b*c+
    426468716676726814375200*b+
    34526481596128074600000*c+
    1135321432129931313124800
def gLo1 (b c:ℕ):ℕ:=
    91871669461485*b+
    91399210934720*c+
    8955517227341490
def GC (b c:ℕ):ℕ:=
    4608650426865933540*b+
    4584950017329294080*c+
    444240406259372700360
def HX (b c:ℕ):ℕ:=
    1881777572870269917600*b^2+
    3755744387886291472800*b*c+
    426468916426229201757600*b+
    34521990722464729852800*c+
    1135337815193745202401600
def gLo2 (b c:ℕ):ℕ:=
    4123231518720*b^2+
    8246463037440*b*c+
    4822040493555195*b+
    307183925358720*c+
    14968885670792910
def FZ (b c:ℕ):ℕ:=
    206837785905070080*b^2+
    413675571810140160*b*c+
    239891175345508480380*b+
    14408742445097669280*c+
    742892517261194421240
def HW (b c:ℕ):ℕ:=
    1880998294004129037600*b^2+
    3754965109020150592800*b*c+
    426459619946996960205600*b+
    34517286103520126102400*c+
    1135310762690546988801600
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3758175737948651018400*b+
    34538727409446763180800
def interceptLo (b:ℕ):ℕ:=
    1884208922932629463200*b^2+
    426580086038476527972000*b+
    1135833174779180208638400
def gHi0 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    329552538923892*a+
    98056516739565*b+
    1130244156661302
def GA (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    15530841575980957488*a+
    4918907105723538660*b+
    53194655921667490728
def HS (a b c:ℕ):ℕ:=
    73900522142203795200*a^3+
    222262647210232819200*a^2*b+
    222823727993854252800*a^2*c+
    71204670596515627964160*a^2+
    222823727993854252800*a*b^2+
    446208536771329939200*a*b*c+
    158881122074363495700960*a*b+
    12541672412975828983680*a*c+
    765757626431655121629120*a+
    2067989469472032026400*b^2+
    4128110291802616653600*b*c+
    585015883131403061602560*b+
    46733637308633033676480*c+
    1829873825748110629733760
def gHi1 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3914945806838124*a+
    98056516739565*b+
    97584058212800*c+
    12864278155444254
def GD (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    194387677481033330736*a+
    4918907105723538660*b+
    4895206696186899200*c+
    638317825483525432056
def HY (a b c:ℕ):ℕ:=
    73713495214329984000*a^3+
    221888593354485196800*a^2*b+
    222636701065980441600*a^2*c+
    71203946295252231596160*a^2+
    222636701065980441600*a*b^2+
    446021509843456128000*a*b*c+
    158879591776101405051360*a*b+
    12539236609653558353280*a*c+
    765763863102076890870720*a+
    2067183472473337744800*b^2+
    4127304294803922372000*b*c+
    585014926636499105957760*b+
    46726897658575292110080*c+
    1829896982756681810808960
def gHi2 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3914945806838124*a+
    4123231518720*b^2+
    8246463037440*b*c+
    4830286956592635*b+
    315430388396160*c+
    18879708246112314
def _Q4 (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    194387677481033330736*a+
    206837785905070080*b^2+
    413675571810140160*b*c+
    240304850917318620540*b+
    14822418016907809440*c+
    937073356956322681896
def HU (a b c:ℕ):ℕ:=
    73473032021349369600*a^3+
    221407666968523968000*a^2*b+
    222396237872999827200*a^2*c+
    71199497163317857436160*a^2+
    222396237872999827200*a*b^2+
    445781046650475513600*a*b*c+
    158874122902107909396960*a*b+
    12536480188672698660480*a*c+
    765737641651369391737920*a+
    2066163730414216250400*b^2+
    4126284552744800877600*b*c+
    585000642209659329980160*b+
    46719677081842809281280*c+
    1829847917471517491621760
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    223384808777475686400*a^2+
    446769617554951372800*a*b+
    12548570144910155383680*a+
    4130483752577777162400*b+
    46752219773102427223680
def interceptHi (a b:ℕ):ℕ:=
    74461602925825228800*a^3+
    223384808777475686400*a^2*b+
    71247677712891599180160*a^2+
    223384808777475686400*a*b^2+
    158926502651514627425760*a*b+
    766136925681146151520320*a+
    2070362930247192535200*b^2+
    585171510908736664056960*b+
    1830722421611258205356160
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G14

namespace AV.G15
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source21,source5,source26]
def scale:ℕ:=360
def denominator:ℕ:=6501254400
def gLo0 (b c:ℕ):ℕ:=
    91871669461485*b+
    806876496472770
def FY (b c:ℕ):ℕ:=
    4608650426865933540*b+
    37974072602567132280
def HV (b c:ℕ):ℕ:=
    1882396542941090388000*b^2+
    3756363357957111943200*b*c+
    426468716676726814375200*b+
    34526481596128074600000*c+
    1135321432129931313124800
def gLo1 (b c:ℕ):ℕ:=
    91871669461485*b+
    91399210934720*c+
    8955517227341490
def GC (b c:ℕ):ℕ:=
    4608650426865933540*b+
    4584950017329294080*c+
    444240406259372700360
def HX (b c:ℕ):ℕ:=
    1881777572870269917600*b^2+
    3755744387886291472800*b*c+
    426468916426229201757600*b+
    34521990722464729852800*c+
    1135337815193745202401600
def gLo2 (b c:ℕ):ℕ:=
    4123231518720*b^2+
    8246463037440*b*c+
    4822040493555195*b+
    307183925358720*c+
    14968885670792910
def FZ (b c:ℕ):ℕ:=
    206837785905070080*b^2+
    413675571810140160*b*c+
    239891175345508480380*b+
    14408742445097669280*c+
    742892517261194421240
def HW (b c:ℕ):ℕ:=
    1880998294004129037600*b^2+
    3754965109020150592800*b*c+
    426459619946996960205600*b+
    34517286103520126102400*c+
    1135310762690546988801600
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3758175737948651018400*b+
    34538727409446763180800
def interceptLo (b:ℕ):ℕ:=
    1884208922932629463200*b^2+
    426580086038476527972000*b+
    1135833174779180208638400
def gHi0 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    329552538923892*a+
    98056516739565*b+
    1130244156661302
def GA (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    15530841575980957488*a+
    4918907105723538660*b+
    53194655921667490728
def HS (a b c:ℕ):ℕ:=
    73900522142203795200*a^3+
    222262647210232819200*a^2*b+
    222823727993854252800*a^2*c+
    71204670596515627964160*a^2+
    222823727993854252800*a*b^2+
    446208536771329939200*a*b*c+
    158881122074363495700960*a*b+
    12541672412975828983680*a*c+
    765757626431655121629120*a+
    2067989469472032026400*b^2+
    4128110291802616653600*b*c+
    585015883131403061602560*b+
    46733637308633033676480*c+
    1829873825748110629733760
def gHi1 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3914945806838124*a+
    98056516739565*b+
    97584058212800*c+
    12864278155444254
def GD (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    194387677481033330736*a+
    4918907105723538660*b+
    4895206696186899200*c+
    638317825483525432056
def HY (a b c:ℕ):ℕ:=
    73713495214329984000*a^3+
    221888593354485196800*a^2*b+
    222636701065980441600*a^2*c+
    71203946295252231596160*a^2+
    222636701065980441600*a*b^2+
    446021509843456128000*a*b*c+
    158879591776101405051360*a*b+
    12539236609653558353280*a*c+
    765763863102076890870720*a+
    2067183472473337744800*b^2+
    4127304294803922372000*b*c+
    585014926636499105957760*b+
    46726897658575292110080*c+
    1829896982756681810808960
def gHi2 (a b c:ℕ):ℕ:=
    4123231518720*a^2+
    8246463037440*a*b+
    8246463037440*a*c+
    3914945806838124*a+
    4123231518720*b^2+
    8246463037440*b*c+
    4830286956592635*b+
    315430388396160*c+
    18879708246112314
def _Q4 (a b c:ℕ):ℕ:=
    206837785905070080*a^2+
    413675571810140160*a*b+
    413675571810140160*a*c+
    194387677481033330736*a+
    206837785905070080*b^2+
    413675571810140160*b*c+
    240304850917318620540*b+
    14822418016907809440*c+
    937073356956322681896
def HU (a b c:ℕ):ℕ:=
    73473032021349369600*a^3+
    221407666968523968000*a^2*b+
    222396237872999827200*a^2*c+
    71199497163317857436160*a^2+
    222396237872999827200*a*b^2+
    445781046650475513600*a*b*c+
    158874122902107909396960*a*b+
    12536480188672698660480*a*c+
    765737641651369391737920*a+
    2066163730414216250400*b^2+
    4126284552744800877600*b*c+
    585000642209659329980160*b+
    46719677081842809281280*c+
    1829847917471517491621760
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    223384808777475686400*a^2+
    446769617554951372800*a*b+
    12548570144910155383680*a+
    4130483752577777162400*b+
    46752219773102427223680
def interceptHi (a b:ℕ):ℕ:=
    74461602925825228800*a^3+
    223384808777475686400*a^2*b+
    71247677712891599180160*a^2+
    223384808777475686400*a*b^2+
    158926502651514627425760*a*b+
    766136925681146151520320*a+
    2070362930247192535200*b^2+
    585171510908736664056960*b+
    1830722421611258205356160
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G15
end MergedPart3

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G16
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source27,source27,source27]
def scale:ℕ:=9
def denominator:ℕ:=4063284
def gLo0 (b c:ℕ):ℕ:=
    3135405621545*b+
    25727621663120
def FY (b c:ℕ):ℕ:=
    157284487599183380*b+
    1228048413946429130
def HV (b c:ℕ):ℕ:=
    1554936543941115168*b^2+
    3110112437819687892*b*c+
    237676404049739230464*b+
    27793595876159305242*c+
    673487161096547391660
def gLo1 (b c:ℕ):ℕ:=
    3135405621545*b+
    3135405621545*c+
    225878716992280
def GC (b c:ℕ):ℕ:=
    157284487599183380*b+
    157284487599183380*c+
    11205875960876088820
def HX (b c:ℕ):ℕ:=
    1554936543941115168*b^2+
    3110112437819687892*b*c+
    237676404049739230464*b+
    27793595876159305242*c+
    673487161096547391660
def gLo2 (b c:ℕ):ℕ:=
    103080787968*b^2+
    206161575936*b*c+
    98073797928035*b+
    9852907357087*c+
    346537802371468
def FZ (b c:ℕ):ℕ:=
    5170944647626752*b^2+
    10341889295253504*b*c+
    4869732399932089700*b+
    469240444995983248*c+
    17183555729950792852
def HW (b c:ℕ):ℕ:=
    1554936543941115168*b^2+
    3110112437819687892*b*c+
    237676404049739230464*b+
    27793595876159305242*c+
    673487161096547391660
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    3110869451575367604*b+
    27798666756139144467
def interceptLo (b:ℕ):ℕ:=
    1555693557696794880*b^2+
    237700845384018054750*b+
    673590525306683060070
def gHi0 (a b c:ℕ):ℕ:=
    103080787968*a^2+
    206161575936*a*b+
    10213690114975*a+
    3290026803497*b+
    35786689809711
def GA (a b c:ℕ):ℕ:=
    5170944647626752*a^2+
    10341889295253504*a*b+
    487338751262676880*a+
    165040904570623508*b+
    1707630708787091034
def HS (a b c:ℕ):ℕ:=
    46304718168798504*a^3+
    139147938166237776*a^2*b+
    139381721826080040*a^2*c+
    44659699642661392296*a^2+
    139381721826080040*a*b^2+
    278997227312002344*a*b*c+
    89309500517050748280*a*b+
    9710419268343218616*a*c+
    467114126954508122004*a+
    1671049014852874824*b^2+
    3342571163303049468*b*c+
    326776948520825606184*b+
    37294825314878309034*c+
    1095941353914623931840
def gHi1 (a b c:ℕ):ℕ:=
    103080787968*a^2+
    206161575936*a*b+
    206161575936*a*c+
    98279959503971*a+
    3290026803497*b+
    3290026803497*c+
    324004054527867
def GD (a b c:ℕ):ℕ:=
    5170944647626752*a^2+
    10341889295253504*a*b+
    10341889295253504*a*c+
    4880074289227343204*a+
    165040904570623508*b+
    165040904570623508*c+
    16078193793681417048
def HY (a b c:ℕ):ℕ:=
    46304718168798504*a^3+
    139147938166237776*a^2*b+
    139381721826080040*a^2*c+
    44659699642661392296*a^2+
    139381721826080040*a*b^2+
    278997227312002344*a*b*c+
    89309500517050748280*a*b+
    9710419268343218616*a*c+
    467114126954508122004*a+
    1671049014852874824*b^2+
    3342571163303049468*b*c+
    326776948520825606184*b+
    37294825314878309034*c+
    1095941353914623931840
def gHi2 (a b c:ℕ):ℕ:=
    103080787968*a^2+
    206161575936*a*b+
    206161575936*a*c+
    98279959503971*a+
    103080787968*b^2+
    206161575936*b*c+
    98279959503971*b+
    10059068933023*c+
    444714681087471
def _Q4 (a b c:ℕ):ℕ:=
    5170944647626752*a^2+
    10341889295253504*a*b+
    10341889295253504*a*c+
    4880074289227343204*a+
    5170944647626752*b^2+
    10341889295253504*b*c+
    4880074289227343204*b+
    479582334291236752*c+
    22058459074530509304
def HU (a b c:ℕ):ℕ:=
    46304718168798504*a^3+
    139147938166237776*a^2*b+
    139381721826080040*a^2*c+
    44659699642661392296*a^2+
    139381721826080040*a*b^2+
    278997227312002344*a*b*c+
    89309500517050748280*a*b+
    9710419268343218616*a*c+
    467114126954508122004*a+
    1671049014852874824*b^2+
    3342571163303049468*b*c+
    326776948520825606184*b+
    37294825314878309034*c+
    1095941353914623931840
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    139615505485922304*a^2+
    279231010971844608*a*b+
    9713280335334752268*a+
    3343561960718571444*b+
    37302523478189839647
def interceptHi (a b:ℕ):ℕ:=
    46538501828640768*a^3+
    139615505485922304*a^2*b+
    44669627955255026088*a^2+
    139615505485922304*a*b^2+
    89320419627059904048*a*b+
    467194256338335280182*a+
    1672039812268396800*b^2+
    326811841397793901710*b+
    1096115152979652966900
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source27,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source27,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G16

namespace AV.G17
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source28,source28,source28]
def scale:ℕ:=15
def denominator:ℕ:=11286900
def gLo0 (b c:ℕ):ℕ:=
    4595731333555*b+
    37496182803960
def FY (b c:ℕ):ℕ:=
    230540266616453020*b+
    1776705182240645190
def HV (b c:ℕ):ℕ:=
    3844881170765934450*b^2+
    7690806018584736150*b*c+
    689593447285714118610*b+
    67657450697737785480*c+
    1958805378708956747400
def gLo1 (b c:ℕ):ℕ:=
    4595731333555*b+
    4595731333555*c+
    393344213877370
def GC (b c:ℕ):ℕ:=
    230540266616453020*b+
    230540266616453020*c+
    19523212481069980180
def HX (b c:ℕ):ℕ:=
    3844881170765934450*b^2+
    7690806018584736150*b*c+
    689593447285714118610*b+
    67657450697737785480*c+
    1958805378708956747400
def gLo2 (b c:ℕ):ℕ:=
    171801313280*b^2+
    343602626560*b*c+
    171236146954122*b+
    14405689214281*c+
    605146179632680
def FZ (b c:ℕ):ℕ:=
    8618241079377920*b^2+
    17236482158755840*b*c+
    8506487410256812608*b+
    680945660970310384*c+
    30022941974741213020
def HW (b c:ℕ):ℕ:=
    3844881170765934450*b^2+
    7690806018584736150*b*c+
    689593447285714118610*b+
    67657450697737785480*c+
    1958805378708956747400
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    7693937049743337900*b+
    67678250799278086905
def interceptLo (b:ℕ):ℕ:=
    3848012201924536200*b^2+
    689705640404266243185*b+
    1959288400190742651750
def gHi0 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    15006993810761*a+
    4853433303475*b+
    52245473334081
def GA (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    711109504748133104*a+
    243467628235519900*b+
    2474887259618753334
def HS (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    129929467176156419070*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    259809989467144866240*a*b+
    23938551601412960220*a*c+
    1359499581038144200590*a+
    4167091112659930350*b^2+
    8336200000955404050*b*c+
    948823652690901956250*b+
    91015244138611041000*c+
    3188374516499833110420
def gHi1 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    343602626560*a*c+
    171579749580682*a+
    4853433303475*b+
    4853433303475*c+
    564666260177412
def GD (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    17236482158755840*a*c+
    8523723892415568448*a+
    243467628235519900*b+
    243467628235519900*c+
    28034008946115523668
def HY (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    129929467176156419070*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    259809989467144866240*a*b+
    23938551601412960220*a*c+
    1359499581038144200590*a+
    4167091112659930350*b^2+
    8336200000955404050*b*c+
    948823652690901956250*b+
    91015244138611041000*c+
    3188374516499833110420
def gHi2 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    343602626560*a*c+
    171579749580682*a+
    171801313280*b^2+
    343602626560*b*c+
    171579749580682*b+
    14749291840841*c+
    776554127900082
def _Q4 (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    17236482158755840*a*c+
    8523723892415568448*a+
    8618241079377920*b^2+
    17236482158755840*b*c+
    8523723892415568448*b+
    698182143129066224*c+
    38538047626077403548
def HU (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    129929467176156419070*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    259809989467144866240*a*b+
    23938551601412960220*a*c+
    1359499581038144200590*a+
    4167091112659930350*b^2+
    8336200000955404050*b*c+
    948823652690901956250*b+
    91015244138611041000*c+
    3188374516499833110420
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    387820848572006400*a^2+
    775641697144012800*a*b+
    23950372211642963220*a+
    8340305130696681900*b+
    91046890751798669325
def interceptHi (a b:ℕ):ℕ:=
    129273616190668800*a^3+
    387820848572006400*a^2*b+
    129974661961157073120*a^2+
    387820848572006400*a*b^2+
    259859289381886798140*a*b+
    1359870706812849597540*a+
    4171196242401208200*b^2+
    948983197527030660525*b+
    3189184443069906433770
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source28,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source28,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G17

namespace AV.G18
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source29,source29,source29]
def scale:ℕ:=15
def denominator:ℕ:=11286900
def gLo0 (b c:ℕ):ℕ:=
    4406747922849*b+
    36826146147760
def FY (b c:ℕ):ℕ:=
    221060102801797236*b+
    1743093463419028390
def HV (b c:ℕ):ℕ:=
    3702678713546097690*b^2+
    7406401104145062630*b*c+
    751000219673993993040*b+
    66442177588961893830*c+
    2136623112640152699600
def gLo1 (b c:ℕ):ℕ:=
    4406747922849*b+
    4406747922849*c+
    428538161040880
def GC (b c:ℕ):ℕ:=
    221060102801797236*b+
    221060102801797236*c+
    21288681646580295820
def HX (b c:ℕ):ℕ:=
    3702678713546097690*b^2+
    7406401104145062630*b*c+
    751000219673993993040*b+
    66442177588961893830*c+
    2136623112640152699600
def gLo2 (b c:ℕ):ℕ:=
    171801313280*b^2+
    343602626560*b*c+
    186827278337367*b+
    14216705803575*c+
    660424203769180
def FZ (b c:ℕ):ℕ:=
    8618241079377920*b^2+
    17236482158755840*b*c+
    9288600924965914788*b+
    671465497155654600*c+
    32795908777524599020
def HW (b c:ℕ):ℕ:=
    3702678713546097690*b^2+
    7406401104145062630*b*c+
    751000219673993993040*b+
    66442177588961893830*c+
    2136623112640152699600
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    7409532135303664380*b+
    66462935170325967330
def interceptLo (b:ℕ):ℕ:=
    3705809744704699440*b^2+
    751119428621623725240*b+
    2137141210542255660450
def gHi0 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    14818010400055*a+
    4664449892769*b+
    51386453267175
def GA (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    701629340933477320*a+
    233987464420864116*b+
    2431795376982480750
def HS (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    141666272317940302770*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    283278497329565282640*a*b+
    23654115763208757300*a*c+
    1483265748913823403990*a+
    4024888655440093590*b^2+
    8051795086515730530*b*c+
    1033698932941602247080*b+
    89515535191630946430*c+
    3478221613164924382320
def gHi1 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    343602626560*a*c+
    187170880963927*a+
    4664449892769*b+
    4664449892769*c+
    615451338724167
def GD (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    17236482158755840*a*c+
    9305837407124670628*a+
    233987464420864116*b+
    233987464420864116*c+
    30581591626334941488
def HY (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    141666272317940302770*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    283278497329565282640*a*b+
    23654115763208757300*a*c+
    1483265748913823403990*a+
    4024888655440093590*b^2+
    8051795086515730530*b*c+
    1033698932941602247080*b+
    89515535191630946430*c+
    3478221613164924382320
def gHi2 (a b c:ℕ):ℕ:=
    171801313280*a^2+
    343602626560*a*b+
    343602626560*a*c+
    187170880963927*a+
    171801313280*b^2+
    343602626560*b*c+
    187170880963927*b+
    14560308430135*c+
    847423283419827
def _Q4 (a b c:ℕ):ℕ:=
    8618241079377920*a^2+
    17236482158755840*a*b+
    17236482158755840*a*c+
    9305837407124670628*a+
    8618241079377920*b^2+
    17236482158755840*b*c+
    9305837407124670628*b+
    688701979314410440*c+
    42093127943569891728
def HU (a b c:ℕ):ℕ:=
    128299517607992700*a^3+
    385872651406654200*a^2*b+
    386846749989330300*a^2*c+
    141666272317940302770*a^2+
    386846749989330300*a*b^2+
    774667598561336700*a*b*c+
    283278497329565282640*a*b+
    23654115763208757300*a*c+
    1483265748913823403990*a+
    4024888655440093590*b^2+
    8051795086515730530*b*c+
    1033698932941602247080*b+
    89515535191630946430*c+
    3478221613164924382320
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    387820848572006400*a^2+
    775641697144012800*a*b+
    23665920911556495600*a+
    8055900216257008380*b+
    89547123822760082130
def interceptHi (a b:ℕ):ℕ:=
    129273616190668800*a^3+
    387820848572006400*a^2*b+
    141714018313514632320*a^2+
    387820848572006400*a*b^2+
    283330348454880890040*a*b+
    1483661748083265143190*a+
    4028993785181371440*b^2+
    1033868044817382234480*b+
    3479088938339477428920
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source29,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source29,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G18

namespace AV.G19
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source30,source30,source30]
def scale:ℕ:=21
def denominator:ℕ:=22122324
def gLo0 (b c:ℕ):ℕ:=
    6056057045565*b+
    49049989550670
def FY (b c:ℕ):ℕ:=
    303796045633722660*b+
    2314589011107723930
def HV (b c:ℕ):ℕ:=
    7137285024568628790*b^2+
    14277130846077937194*b*c+
    1391059835813913394542*b+
    124067570560767852354*c+
    3955907064077472280728
def gLo1 (b c:ℕ):ℕ:=
    6056057045565*b+
    6056057045565*c+
    566822833798100
def GC (b c:ℕ):ℕ:=
    303796045633722660*b+
    303796045633722660*c+
    28142191305223716500
def HX (b c:ℕ):ℕ:=
    7137285024568628790*b^2+
    14277130846077937194*b*c+
    1391059835813913394542*b+
    124067570560767852354*c+
    3955907064077472280728
def gLo2 (b c:ℕ):ℕ:=
    240521838592*b^2+
    481043677184*b*c+
    247044263730093*b+
    18863979366122*c+
    873135070080692
def FZ (b c:ℕ):ℕ:=
    12065537511129088*b^2+
    24131075022258176*b*c+
    12275964713986716492*b+
    887910795037309628*c+
    43332892283034268388
def HW (b c:ℕ):ℕ:=
    7137285024568628790*b^2+
    14277130846077937194*b*c+
    1391059835813913394542*b+
    124067570560767852354*c+
    3955907064077472280728
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    14285055679213886532*b+
    124120362385835682300
def interceptLo (b:ℕ):ℕ:=
    7145209857704578128*b^2+
    1391366698351968246657*b+
    3957244104833005043946
def gHi0 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    19705805801194*a+
    6416839803453*b+
    68395010758968
def GA (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    930140176326261436*a+
    321894351900416292*b+
    3226630789115950422
def HS (a b c:ℕ):ℕ:=
    250921559305367076*a^3+
    755219406344445000*a^2*b+
    757674134772788772*a^2*c+
    262409933238836370414*a^2+
    757674134772788772*a*b^2+
    1517802997973921316*a*b*c+
    524679225376221124104*a*b+
    44170664094837338100*a*c+
    2746334717781315788862*a+
    7768271015474562138*b^2+
    15541557556318147662*b*c+
    1914603775419111339822*b+
    167100494156153667858*c+
    6439829390025367020300
def gHi1 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    247525307407277*a+
    6416839803453*b+
    6416839803453*c+
    813987356612481
def GD (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    12300095789008974668*a+
    321894351900416292*b+
    321894351900416292*c+
    40424188695914656224
def HY (a b c:ℕ):ℕ:=
    250921559305367076*a^3+
    755219406344445000*a^2*b+
    757674134772788772*a^2*c+
    262409933238836370414*a^2+
    757674134772788772*a*b^2+
    1517802997973921316*a*b*c+
    524679225376221124104*a*b+
    44170664094837338100*a*c+
    2746334717781315788862*a+
    7768271015474562138*b^2+
    15541557556318147662*b*c+
    1914603775419111339822*b+
    167100494156153667858*c+
    6439829390025367020300
def gHi2 (a b c:ℕ):ℕ:=
    240521838592*a^2+
    481043677184*a*b+
    481043677184*a*c+
    247525307407277*a+
    240521838592*b^2+
    481043677184*b*c+
    247525307407277*b+
    19345023043306*c+
    1120419855649377
def _Q4 (a b c:ℕ):ℕ:=
    12065537511129088*a^2+
    24131075022258176*a*b+
    24131075022258176*a*c+
    12300095789008974668*a+
    12065537511129088*b^2+
    24131075022258176*b*c+
    12300095789008974668*b+
    912041870059567804*c+
    55620922534532113968
def HU (a b c:ℕ):ℕ:=
    250921559305367076*a^3+
    755219406344445000*a^2*b+
    757674134772788772*a^2*c+
    262409933238836370414*a^2+
    757674134772788772*a*b^2+
    1517802997973921316*a*b*c+
    524679225376221124104*a*b+
    44170664094837338100*a*c+
    2746334717781315788862*a+
    7768271015474562138*b^2+
    15541557556318147662*b*c+
    1914603775419111339822*b+
    167100494156153667858*c+
    6439829390025367020300
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    760128863201132544*a^2+
    1520257726402265088*a*b+
    44200560265792798560*a+
    15551937117882440772*b+
    167180727423748614492
def interceptHi (a b:ℕ):ℕ:=
    253376287733710848*a^3+
    760128863201132544*a^2*b+
    262532508727068455316*a^2+
    760128863201132544*a*b^2+
    524812180426017502116*a*b+
    2747354714213449118436*a+
    7778650577038855248*b^2+
    1915038683550105882405*b+
    6442066306453229371962
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source30,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source30,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G19
end MergedPart0
section MergedPart1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace AV.G20
open scoped BigOperators
open RCN095 KB GU
open KM OF
def cfg:Fin 3→Params:= ![source31,source32,source33]
def scale:ℕ:=840
def denominator:ℕ:=35395718400
def gLo0 (b c:ℕ):ℕ:=
    211060019056110*b+
    1854450095271620
def FY (b c:ℕ):ℕ:=
    10587614795930702040*b+
    87188447990722107680
def HV (b c:ℕ):ℕ:=
    10108057025043446212800*b^2+
    20257676322768602289600*b*c+
    2444988357601573331368800*b+
    187152174163426643740800*c+
    6502593664014666116875200
def gLo1 (b c:ℕ):ℕ:=
    211060019056110*b+
    212004936109640*c+
    21938281034309220
def GC (b c:ℕ):ℕ:=
    10587614795930702040*b+
    10635015615003980960*c+
    1088835556628120836080
def HX (b c:ℕ):ℕ:=
    10106165974994944344000*b^2+
    20255785272720100420800*b*c+
    2444977764669741478480800*b+
    187138185239231939966400*c+
    6502587683509706358830400
def gLo2 (b c:ℕ):ℕ:=
    9620873543680*b^2+
    19241747087360*b*c+
    11879797658892905*b+
    720542160717800*c+
    36773438467618650
def FZ (b c:ℕ):ℕ:=
    482621500445163520*b^2+
    965243000890327040*b*c+
    591267620489916936020*b+
    33810002314854344000*c+
    1826020552389879354600
def HW (b c:ℕ):ℕ:=
    10101923234501510664000*b^2+
    20251542532226666740800*b*c+
    2444929817370485623264800*b+
    187113104575846367083200*c+
    6502453766358185621966400
def conductorLo (b c:ℕ):ℕ:=
    0
def slopeLo (b:ℕ):ℕ:=
    20268974134596831403200*b+
    187229064759283281369600
def interceptLo (b:ℕ):ℕ:=
    10119354836871675326400*b^2+
    2445607868920655756637600*b+
    6505410090882532745563200
def gHi0 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    758372853156212*a+
    225491329371630*b+
    2598391564711992
def GA (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    35707741170334843568*a+
    11311547046598447320*b+
    122172253228335553488
def HS (a b c:ℕ):ℕ:=
    401910891053626214400*a^3+
    1209223842481189785600*a^2*b+
    1212715011801500928000*a^2*c+
    407079432127376753646720*a^2+
    1212715011801500928000*a*b^2+
    2428921192923312998400*a*b*c+
    910905474455378882380320*a*b+
    67991467309602084904320*a*c+
    4382841274667395227253440*a+
    11118071006657978462400*b^2+
    22281195455317977931200*b*c+
    3354076502030985049845120*b+
    253322820277741253598720*c+
    10478352009199514143173120
def gHi1 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    9595237137768772*a+
    225491329371630*b+
    226436246425160*c+
    31519086788362152
def GD (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    476664926508245928208*a+
    11311547046598447320*b+
    11358947865671726240*c+
    1564776547203645366528
def HY (a b c:ℕ):ℕ:=
    401329029500241024000*a^3+
    1208060119374419404800*a^2*b+
    1212133150248115737600*a^2*c+
    407073008737869148859520*a^2+
    1212133150248115737600*a*b^2+
    2428339331369927808000*a*b*c+
    910896578154269390533920*a*b+
    67983854620205414459520*a*c+
    4382820095940377199944640*a+
    11115598095056091403200*b^2+
    22278722543716090872000*b*c+
    3354058176521150475491520*b+
    253301800525703264569920*c+
    10478330691495490577416320
def gHi2 (a b c:ℕ):ℕ:=
    9620873543680*a^2+
    19241747087360*a*b+
    19241747087360*a*c+
    9595237137768772*a+
    9620873543680*b^2+
    19241747087360*b*c+
    11899039405980265*b+
    739783907805160*c+
    46359054731843742
def _Q4 (a b c:ℕ):ℕ:=
    482621500445163520*a^2+
    965243000890327040*a*b+
    965243000890327040*a*c+
    476664926508245928208*a+
    482621500445163520*b^2+
    965243000890327040*b*c+
    592232863490807263060*b+
    34775245315744671040*c+
    2302202857397680119288
def HU (a b c:ℕ):ℕ:=
    400019841005124345600*a^3+
    1205441742384186048000*a^2*b+
    1210823961752999059200*a^2*c+
    407049755455482087083520*a^2+
    1210823961752999059200*a*b^2+
    2427030142874811129600*a*b*c+
    910867772942893778399520*a*b+
    67969041393160751195520*a*c+
    4382686801416309996939840*a+
    11110046166067541044800*b^2+
    22273170614727540513600*b*c+
    3353984042387509241497920*b+
    253263215823768145101120*c+
    10478085423913794582645120
def conductorHi (a b c:ℕ):ℕ:=
    0
def slopeHi (a b:ℕ):ℕ:=
    1216206181121812070400*a^2+
    2432412362243624140800*a*b+
    68034622045917438414720*a+
    22295984436466518187200*b+
    253439374440592933595520
def interceptHi (a b:ℕ):ℕ:=
    405402060373937356800*a^3+
    1216206181121812070400*a^2*b+
    407320266331149300232320*a^2+
    1216206181121812070400*a*b^2+
    911161097640299969221920*a*b+
    4384940454595691030658240*a+
    11132859987806518718400*b^2+
    3354944654196347939670720*b+
    10483030272961224339822720
def slope:ℕ→ℕ→ℕ
  | 0,b=>slopeLo b
  | a+1,b=>slopeHi a b
def intercept:ℕ→ℕ→ℕ
  | 0,b=>interceptLo b
  | a+1,b=>interceptHi a b
def conductor:ℕ→ℕ→ℕ→ℕ
  | 0,b,c=>conductorLo b c
  | a+1,b,c=>conductorHi a b c
def full (a b c:ℕ):ℕ:=slope a b*c+intercept a b
def rounded (a b c:ℕ):ℕ:=(slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive:0<scale:=by decide+kernel
theorem divides (j:Fin 3):3*(cfg j).d ∣ scale:=by
  have h: ∀j:Fin 3,3*(cfg j).d ∣ scale:=by decide+kernel
  exact h j
theorem graph_eq_lo (f:FlagDegree) (b c:ℕ):
    graphDir cfg scale f 0 b c=f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c:=by
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YK,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem graph_eq_hi (f:FlagDegree) (a b c:ℕ):
    graphDir cfg scale f (a+1) b c=f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c:=by
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,BD.weight,BD.direction,Params.d,Params.flag,EJ.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,YJ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;>ring
theorem GY (f:FlagDegree) (a b c:ℕ):
    scale*131073*80910*DS f a b c≤50164*graphDir cfg scale f a b c:=by
  cases a with
  | zero=>
    have he:50164*graphDir cfg scale f 0 b c=scale*131073*80910*DS f 0 b c+
        (f.zOnly*FY b c+f.yz*GC b c+f.all*FZ b c):=by
      rw [graph_eq_lo]
      simp only [scale,DS,gLo0,gLo1,gLo2,FY,GC,FZ]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a=>
    have he:50164*graphDir cfg scale f (a+1) b c=scale*131073*80910*DS f (a+1) b c+
        (f.zOnly*GA a b c+f.yz*GD a b c+f.all*_Q4 a b c):=by
      rw [graph_eq_hi]
      simp only [scale,DS,gHi0,gHi1,gHi2,GA,GD,_Q4]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c:ℕ):full a b c=
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j:Fin 3,coeff (cfg j) a b c)+conductor a b c:=by
  cases a with
  | zero=>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,CZ,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
  | succ a=>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,CZ,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;>ring
theorem helper_cap (a b c:ℕ) (j:Fin 3):
    helper (cfg j) a b c/50164≤full a b c/denominator:=by
  have he:scale^2*helper (cfg j) a b c≤full a b c:=by
    cases a with
    | zero=>
      fin_cases j
      · have h:full 0 b c=scale^2*helper (cfg 0) 0 b c+HV b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HV,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 1) 0 b c+HX b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HX,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full 0 b c=scale^2*helper (cfg 2) 0 b c+HW b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,CZ,HW,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a=>
      fin_cases j
      · have h:full (a+1) b c=scale^2*helper (cfg 0) (a+1) b c+HS a b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HS,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 1) (a+1) b c+HY a b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HY,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h:full (a+1) b c=scale^2*helper (cfg 2) (a+1) b c+HU a b c:=by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,CZ,HU,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;>ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hh:=Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c:ℕ):
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (cfg j) a b c/50164)≤full a b c/denominator:=by
  apply (Nat.le_div_iff_mul_le (show 0<denominator by decide+kernel)).mpr
  have hx:=Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy:(∑ j:Fin 3,coeff (cfg j) a b c/50164)*50164≤ ∑ j:Fin 3,coeff (cfg j) a b c:=by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _=>Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem KG (a b c:ℕ):full a b c/denominator≤rounded a b c:=by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0<denominator by decide+kernel)).mpr
  have hs:=Nat.lt_mul_div_succ (slope a b) (show 0<denominator by decide+kernel)
  have hi:=Nat.lt_mul_div_succ (intercept a b) (show 0<denominator by decide+kernel)
  have hm:=Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
end AV.G20
end MergedPart1
section MergedPart2
namespace WI
open scoped BigOperators
open RCN095 RCN130 RCN146 RCN260 RCN327
open KB GU KM AAG
open OF ESY
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Receipt (g:Fin 21) where
  scale:ℕ
  denominator:ℕ
  full:ℕ→ℕ→ℕ→ℕ
  rounded:ℕ→ℕ→ℕ→ℕ
  slope:ℕ→ℕ→ℕ
  intercept:ℕ→ℕ→ℕ
  rounded_formula: ∀a b c,rounded a b c=slope a b*c+intercept a b
  positive:0<scale
  divides: ∀j:Fin 3,3*(groups g j).d ∣ scale
  identity: ∀(f:FlagDegree) (a b c:ℕ),
    scale*131073*80910*DS f a b c≤50164*graphDir (groups g) scale f a b c
  helper: ∀(a b c:ℕ) (j:Fin 3),
    GU.helper (groups g j) a b c/50164≤full a b c/denominator
  retained: ∀a b c,
    graphDir (groups g) scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j:Fin 3,coeff (groups g j) a b c/50164)≤full a b c/denominator
  rounded_bound: ∀a b c,full a b c/denominator≤rounded a b c

def receipt0:Receipt 0 where
  scale:=AV.G0.scale
  denominator:=AV.G0.denominator
  full:=AV.G0.full
  rounded:=AV.G0.rounded
  slope:=fun a b=>AV.G0.slope a b/AV.G0.denominator+1
  intercept:=fun a b=>AV.G0.intercept a b/AV.G0.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G0.positive
  divides:=AV.G0.divides
  identity:=AV.G0.GY
  helper:=AV.G0.helper_cap
  retained:=AV.G0.retained_cap
  rounded_bound:=AV.G0.KG

def receipt1:Receipt 1 where
  scale:=AV.G1.scale
  denominator:=AV.G1.denominator
  full:=AV.G1.full
  rounded:=AV.G1.rounded
  slope:=fun a b=>AV.G1.slope a b/AV.G1.denominator+1
  intercept:=fun a b=>AV.G1.intercept a b/AV.G1.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G1.positive
  divides:=AV.G1.divides
  identity:=AV.G1.GY
  helper:=AV.G1.helper_cap
  retained:=AV.G1.retained_cap
  rounded_bound:=AV.G1.KG

def receipt2:Receipt 2 where
  scale:=AV.G2.scale
  denominator:=AV.G2.denominator
  full:=AV.G2.full
  rounded:=AV.G2.rounded
  slope:=fun a b=>AV.G2.slope a b/AV.G2.denominator+1
  intercept:=fun a b=>AV.G2.intercept a b/AV.G2.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G2.positive
  divides:=AV.G2.divides
  identity:=AV.G2.GY
  helper:=AV.G2.helper_cap
  retained:=AV.G2.retained_cap
  rounded_bound:=AV.G2.KG

def receipt3:Receipt 3 where
  scale:=AV.G3.scale
  denominator:=AV.G3.denominator
  full:=AV.G3.full
  rounded:=AV.G3.rounded
  slope:=fun a b=>AV.G3.slope a b/AV.G3.denominator+1
  intercept:=fun a b=>AV.G3.intercept a b/AV.G3.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G3.positive
  divides:=AV.G3.divides
  identity:=AV.G3.GY
  helper:=AV.G3.helper_cap
  retained:=AV.G3.retained_cap
  rounded_bound:=AV.G3.KG

def receipt4:Receipt 4 where
  scale:=AV.G4.scale
  denominator:=AV.G4.denominator
  full:=AV.G4.full
  rounded:=AV.G4.rounded
  slope:=fun a b=>AV.G4.slope a b/AV.G4.denominator+1
  intercept:=fun a b=>AV.G4.intercept a b/AV.G4.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G4.positive
  divides:=AV.G4.divides
  identity:=AV.G4.GY
  helper:=AV.G4.helper_cap
  retained:=AV.G4.retained_cap
  rounded_bound:=AV.G4.KG

def receipt5:Receipt 5 where
  scale:=AV.G5.scale
  denominator:=AV.G5.denominator
  full:=AV.G5.full
  rounded:=AV.G5.rounded
  slope:=fun a b=>AV.G5.slope a b/AV.G5.denominator+1
  intercept:=fun a b=>AV.G5.intercept a b/AV.G5.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G5.positive
  divides:=AV.G5.divides
  identity:=AV.G5.GY
  helper:=AV.G5.helper_cap
  retained:=AV.G5.retained_cap
  rounded_bound:=AV.G5.KG

def receipt6:Receipt 6 where
  scale:=AV.G6.scale
  denominator:=AV.G6.denominator
  full:=AV.G6.full
  rounded:=AV.G6.rounded
  slope:=fun a b=>AV.G6.slope a b/AV.G6.denominator+1
  intercept:=fun a b=>AV.G6.intercept a b/AV.G6.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G6.positive
  divides:=AV.G6.divides
  identity:=AV.G6.GY
  helper:=AV.G6.helper_cap
  retained:=AV.G6.retained_cap
  rounded_bound:=AV.G6.KG

def receipt7:Receipt 7 where
  scale:=AV.G7.scale
  denominator:=AV.G7.denominator
  full:=AV.G7.full
  rounded:=AV.G7.rounded
  slope:=fun a b=>AV.G7.slope a b/AV.G7.denominator+1
  intercept:=fun a b=>AV.G7.intercept a b/AV.G7.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G7.positive
  divides:=AV.G7.divides
  identity:=AV.G7.GY
  helper:=AV.G7.helper_cap
  retained:=AV.G7.retained_cap
  rounded_bound:=AV.G7.KG

def receipt8:Receipt 8 where
  scale:=AV.G8.scale
  denominator:=AV.G8.denominator
  full:=AV.G8.full
  rounded:=AV.G8.rounded
  slope:=fun a b=>AV.G8.slope a b/AV.G8.denominator+1
  intercept:=fun a b=>AV.G8.intercept a b/AV.G8.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G8.positive
  divides:=AV.G8.divides
  identity:=AV.G8.GY
  helper:=AV.G8.helper_cap
  retained:=AV.G8.retained_cap
  rounded_bound:=AV.G8.KG

def receipt9:Receipt 9 where
  scale:=AV.G9.scale
  denominator:=AV.G9.denominator
  full:=AV.G9.full
  rounded:=AV.G9.rounded
  slope:=fun a b=>AV.G9.slope a b/AV.G9.denominator+1
  intercept:=fun a b=>AV.G9.intercept a b/AV.G9.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G9.positive
  divides:=AV.G9.divides
  identity:=AV.G9.GY
  helper:=AV.G9.helper_cap
  retained:=AV.G9.retained_cap
  rounded_bound:=AV.G9.KG

def receipt10:Receipt 10 where
  scale:=AV.G10.scale
  denominator:=AV.G10.denominator
  full:=AV.G10.full
  rounded:=AV.G10.rounded
  slope:=fun a b=>AV.G10.slope a b/AV.G10.denominator+1
  intercept:=fun a b=>AV.G10.intercept a b/AV.G10.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G10.positive
  divides:=AV.G10.divides
  identity:=AV.G10.GY
  helper:=AV.G10.helper_cap
  retained:=AV.G10.retained_cap
  rounded_bound:=AV.G10.KG

def receipt11:Receipt 11 where
  scale:=AV.G11.scale
  denominator:=AV.G11.denominator
  full:=AV.G11.full
  rounded:=AV.G11.rounded
  slope:=fun a b=>AV.G11.slope a b/AV.G11.denominator+1
  intercept:=fun a b=>AV.G11.intercept a b/AV.G11.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G11.positive
  divides:=AV.G11.divides
  identity:=AV.G11.GY
  helper:=AV.G11.helper_cap
  retained:=AV.G11.retained_cap
  rounded_bound:=AV.G11.KG

def receipt12:Receipt 12 where
  scale:=AV.G12.scale
  denominator:=AV.G12.denominator
  full:=AV.G12.full
  rounded:=AV.G12.rounded
  slope:=fun a b=>AV.G12.slope a b/AV.G12.denominator+1
  intercept:=fun a b=>AV.G12.intercept a b/AV.G12.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G12.positive
  divides:=AV.G12.divides
  identity:=AV.G12.GY
  helper:=AV.G12.helper_cap
  retained:=AV.G12.retained_cap
  rounded_bound:=AV.G12.KG

def receipt13:Receipt 13 where
  scale:=AV.G13.scale
  denominator:=AV.G13.denominator
  full:=AV.G13.full
  rounded:=AV.G13.rounded
  slope:=fun a b=>AV.G13.slope a b/AV.G13.denominator+1
  intercept:=fun a b=>AV.G13.intercept a b/AV.G13.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G13.positive
  divides:=AV.G13.divides
  identity:=AV.G13.GY
  helper:=AV.G13.helper_cap
  retained:=AV.G13.retained_cap
  rounded_bound:=AV.G13.KG

def receipt14:Receipt 14 where
  scale:=AV.G14.scale
  denominator:=AV.G14.denominator
  full:=AV.G14.full
  rounded:=AV.G14.rounded
  slope:=fun a b=>AV.G14.slope a b/AV.G14.denominator+1
  intercept:=fun a b=>AV.G14.intercept a b/AV.G14.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G14.positive
  divides:=AV.G14.divides
  identity:=AV.G14.GY
  helper:=AV.G14.helper_cap
  retained:=AV.G14.retained_cap
  rounded_bound:=AV.G14.KG

def receipt15:Receipt 15 where
  scale:=AV.G15.scale
  denominator:=AV.G15.denominator
  full:=AV.G15.full
  rounded:=AV.G15.rounded
  slope:=fun a b=>AV.G15.slope a b/AV.G15.denominator+1
  intercept:=fun a b=>AV.G15.intercept a b/AV.G15.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G15.positive
  divides:=AV.G15.divides
  identity:=AV.G15.GY
  helper:=AV.G15.helper_cap
  retained:=AV.G15.retained_cap
  rounded_bound:=AV.G15.KG

def receipt16:Receipt 16 where
  scale:=AV.G16.scale
  denominator:=AV.G16.denominator
  full:=AV.G16.full
  rounded:=AV.G16.rounded
  slope:=fun a b=>AV.G16.slope a b/AV.G16.denominator+1
  intercept:=fun a b=>AV.G16.intercept a b/AV.G16.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G16.positive
  divides:=AV.G16.divides
  identity:=AV.G16.GY
  helper:=AV.G16.helper_cap
  retained:=AV.G16.retained_cap
  rounded_bound:=AV.G16.KG

def receipt17:Receipt 17 where
  scale:=AV.G17.scale
  denominator:=AV.G17.denominator
  full:=AV.G17.full
  rounded:=AV.G17.rounded
  slope:=fun a b=>AV.G17.slope a b/AV.G17.denominator+1
  intercept:=fun a b=>AV.G17.intercept a b/AV.G17.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G17.positive
  divides:=AV.G17.divides
  identity:=AV.G17.GY
  helper:=AV.G17.helper_cap
  retained:=AV.G17.retained_cap
  rounded_bound:=AV.G17.KG

def receipt18:Receipt 18 where
  scale:=AV.G18.scale
  denominator:=AV.G18.denominator
  full:=AV.G18.full
  rounded:=AV.G18.rounded
  slope:=fun a b=>AV.G18.slope a b/AV.G18.denominator+1
  intercept:=fun a b=>AV.G18.intercept a b/AV.G18.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G18.positive
  divides:=AV.G18.divides
  identity:=AV.G18.GY
  helper:=AV.G18.helper_cap
  retained:=AV.G18.retained_cap
  rounded_bound:=AV.G18.KG

def receipt19:Receipt 19 where
  scale:=AV.G19.scale
  denominator:=AV.G19.denominator
  full:=AV.G19.full
  rounded:=AV.G19.rounded
  slope:=fun a b=>AV.G19.slope a b/AV.G19.denominator+1
  intercept:=fun a b=>AV.G19.intercept a b/AV.G19.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G19.positive
  divides:=AV.G19.divides
  identity:=AV.G19.GY
  helper:=AV.G19.helper_cap
  retained:=AV.G19.retained_cap
  rounded_bound:=AV.G19.KG

def receipt20:Receipt 20 where
  scale:=AV.G20.scale
  denominator:=AV.G20.denominator
  full:=AV.G20.full
  rounded:=AV.G20.rounded
  slope:=fun a b=>AV.G20.slope a b/AV.G20.denominator+1
  intercept:=fun a b=>AV.G20.intercept a b/AV.G20.denominator+1
  rounded_formula:=by intro a b c;rfl
  positive:=AV.G20.positive
  divides:=AV.G20.divides
  identity:=AV.G20.GY
  helper:=AV.G20.helper_cap
  retained:=AV.G20.retained_cap
  rounded_bound:=AV.G20.KG
def receipt (g:Fin 21):Receipt g:=by
  exact (Fin.cases (motive:=fun j:Fin 21=>Receipt (j)) receipt0 (Fin.cases (motive:=fun j:Fin 20=>Receipt (j.succ)) receipt1 (Fin.cases (motive:=fun j:Fin 19=>Receipt (j.succ.succ)) receipt2 (Fin.cases (motive:=fun j:Fin 18=>Receipt (j.succ.succ.succ)) receipt3 (Fin.cases (motive:=fun j:Fin 17=>Receipt (j.succ.succ.succ.succ)) receipt4 (Fin.cases (motive:=fun j:Fin 16=>Receipt (j.succ.succ.succ.succ.succ)) receipt5 (Fin.cases (motive:=fun j:Fin 15=>Receipt (j.succ.succ.succ.succ.succ.succ)) receipt6 (Fin.cases (motive:=fun j:Fin 14=>Receipt (j.succ.succ.succ.succ.succ.succ.succ)) receipt7 (Fin.cases (motive:=fun j:Fin 13=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ)) receipt8 (Fin.cases (motive:=fun j:Fin 12=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt9 (Fin.cases (motive:=fun j:Fin 11=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt10 (Fin.cases (motive:=fun j:Fin 10=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt11 (Fin.cases (motive:=fun j:Fin 9=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt12 (Fin.cases (motive:=fun j:Fin 8=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt13 (Fin.cases (motive:=fun j:Fin 7=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt14 (Fin.cases (motive:=fun j:Fin 6=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt15 (Fin.cases (motive:=fun j:Fin 5=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt16 (Fin.cases (motive:=fun j:Fin 4=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt17 (Fin.cases (motive:=fun j:Fin 3=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt18 (Fin.cases (motive:=fun j:Fin 2=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt19 (Fin.cases (motive:=fun j:Fin 1=>Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt20 (fun i=>Fin.elim0 i)))))))))))))))))))))) g

def scales (g:Fin 21):ℕ:=(receipt g).scale
def denominators (g:Fin 21):ℕ:=(receipt g).denominator
def fulls (g:Fin 21):ℕ→ℕ→ℕ→ℕ:=(receipt g).full
def roundedCaps (g:Fin 21):ℕ→ℕ→ℕ→ℕ:=(receipt g).rounded
def sourceLimit (g:Fin 21):ℕ:=Finset.univ.sup (fun j:Fin 3=>(groups g j).L)

theorem GMM (g:Fin 21):0<scales g:=(receipt g).positive
theorem GUI (g:Fin 21) (j:Fin 3):3*(groups g j).d ∣ scales g:=(receipt g).divides j
theorem GY (g:Fin 21) (f:FlagDegree) (a b c:ℕ):
    scales g*131073*80910*DS f a b c≤50164*graphDir (groups g) (scales g) f a b c:=
  (receipt g).identity f a b c
theorem helper_cap (g:Fin 21) (a b c:ℕ) (j:Fin 3):
    helper (groups g j) a b c/50164≤fulls g a b c/denominators g:=(receipt g).helper a b c j
theorem retained_cap (g:Fin 21) (a b c:ℕ):
    graphDir (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c/scales g+
      (∑ j:Fin 3,coeff (groups g j) a b c/50164)≤fulls g a b c/denominators g:=
  (receipt g).retained a b c
theorem rounded_cap (g:Fin 21) (a b c:ℕ):
    fulls g a b c/denominators g≤roundedCaps g a b c:=(receipt g).rounded_bound a b c

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}

theorem GXT (S:Data nodes u0 u1) (hown:Own S) (g:Fin 21):
    boundDir S (groups g) (scales g)≤
      fulls g (S.r-3) (S.y-S.r-2) (S.t-S.y)/denominators g:=by
  obtain ⟨a,ha⟩: ∃a,S.r=a+3:=⟨S.r-3,by have:=S.rpos;omega⟩
  obtain ⟨b,hb⟩: ∃b,S.y=a+3+(b+2):=⟨S.y-S.r-2,by have:=S.ry;omega⟩
  obtain ⟨c,hc⟩: ∃c,S.t=a+3+(b+2)+c:=⟨S.t-S.y,by have:=S.yt;omega⟩
  have hv:S.y-S.r=b+2:=by omega
  have hz:S.t-S.y=c:=by omega
  have har:S.r-3=a:=by omega
  have hbr:S.y-S.r-2=b:=by omega
  have hp (R U T:ℕ):GB.FU (S.pair R U T)=
      CZ a b c U R T/50164:=by
    unfold GB.FU
    rw [GJE S a b c ha hb hc]
    norm_num only [Data.pair,DG.gap]
  have hcoeff (j:Fin 3):CRL S (groups g j)=coeff (groups g j) a b c/50164:=hp _ _ _
  have hhelper (j:Fin 3):helperCap S (groups g j)=helper (groups g j) a b c/50164:=by
    unfold helperCap
    rw [hp,ha,hb,hc]
    have h1:a+3-1=a+2:=by omega
    have h2:a+3+(b+2)-1=a+b+4:=by omega
    have h3:a+3+(b+2)+c-1=a+b+c+4:=by omega
    simp only [h1,h2,h3,helper]
  have hn:numberDir (groups g) (scales g) S.t S.y S.r (FX S.F)=
      graphDir (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c:=by
    rw [hown,hv,hz,hc,hb,ha,DUL]
  rw [har,hbr,hz]
  unfold boundDir
  apply max_le
  · apply Finset.sup_le
    intro j _
    rw [hhelper]
    exact helper_cap g a b c j
  · rw [hn]
    simp_rw [hcoeff]
    exact retained_cap g a b c

theorem GHI (S:Data nodes u0 u1):
    ∀(G:Finset K) (fl:FlagDegree) (S' :RCN159.FH (RCN135.AL K) G
      ⇑nodes 2130706433 80909 fl w (FA.cellSupport S.t S.y S.r)),S'.F=S.F→
      HFreeDir6813.DGR S' :=by
  intro G fl S' _
  haveI:CharP (RCN135.GenericField K) 2130706433:=RCN135.MP K 2130706433
  refine HFreeDir6813.DIV S' ?_
  have:=S.tbound;have:=S.yt;have:=S.ry;have:=S.rpos
  simp only [FA.cellSupport,RCN198.support,FA.cellA,
    FA.cellB,FA.cellS]
  omega

theorem count_group (S:Data nodes u0 u1) (hI:Fintype.card I=262144)
    (hown:Own S) (g:Fin 21) (hL:sourceLimit g<S.t):
    S.seeds.card≤roundedCaps g (S.r-3) (S.y-S.r-2) (S.t-S.y):=by
  obtain ⟨P,hP⟩:=exists_group nodes u0 u1 hI g
  have hLt (j:Fin 3):(groups g j).L<RCN234.wt RCN156.AT S.F:=by
    rw [own_total S hown]
    exact (Finset.le_sup (f:=fun j:Fin 3=>(groups g j).L) (Finset.mem_univ j)).trans_lt hL
  have hid (f:FlagDegree):scales g*131073*80910*
      IY f (FA.cellA S.t S.y)
        (FA.cellB S.y S.r) (FA.cellS S.r) w≤
        50164*numberDir (groups g) (scales g) S.t S.y S.r f:=by
    obtain ⟨a,ha⟩: ∃a,S.r=a+3:=⟨S.r-3,by have:=S.rpos;omega⟩
    obtain ⟨b,hb⟩: ∃b,S.y=a+3+(b+2):=⟨S.y-S.r-2,by have:=S.ry;omega⟩
    obtain ⟨c,hc⟩: ∃c,S.t=a+3+(b+2)+c:=⟨S.t-S.y,by have:=S.yt;omega⟩
    rw [ha,hb,hc,FGF,DUL]
    exact GY g f a b c
  have hcount:=EJH S hI (groups g) (wellFormed g) (scales g)
    (GMM g) (GUI g) (GHI S) P hP hLt
    (fun j=>(FYB S g j).1) (fun j=>(FYB S g j).2) hid
  exact (hcount.trans (GXT S hown g)).trans (rounded_cap g _ _ _)

end WI
end MergedPart2
section MergedPart3
namespace ATY

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open FA

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (g:Fin 21) (p:FlagDegree):Prop:=
  3≤p.all∧2≤p.yz∧3≤p.zOnly∧WI.sourceLimit g<p.all+p.yz+p.zOnly

def ledgerCap (g:Fin 21) (p:FlagDegree):ℕ:=
  WI.roundedCaps g (p.all-3) (p.yz-2) p.zOnly

section Carrier
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes:I ↪ K} {u0 u1:I→K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

def ofCarrier (D L s:ℕ) (F:MvPolynomial (Fin 4) K)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (hF:Irreducible F) (hrdegree:0<F.degreeOf 2)
    (hbox:F ∈ BA K D w L s)
    (ht:wt AT F≤7501) (hy:wt BC F≤142)
    (hr:wt BE F≤31)
    (h3:3≤wt BE F)
    (hry:wt BE F+2≤wt BC F)
    (hyt:wt BC F+2≤wt AT F)
    (selected:K→Polynomial K) (seeds:Finset K)
    (hdegree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w)
    (hagreement: ∀gamma ∈ seeds,181235≤
      (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hsolution: ∀gamma ∈ seeds,BM K (selected gamma) gamma F=0)
    (hregular: ∀gamma ∈ seeds,
      BM K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno:BL selected seeds w 80909):
    AAG.Data nodes u0 u1 where
  D:=D
  t:=wt AT F
  y:=wt BC F
  r:=wt BE F
  Dlow:=hDlow
  Dchar:=hDchar
  tbound:=ht
  ybound:=hy
  rbound:=hr
  rpos:=h3
  ry:=hry
  yt:=hyt
  F:=F
  irreducible:=hF
  rdegree:=hrdegree
  box:=by
    intro e he
    have hs:=MvPolynomial.le_weightedTotalDegree BE he
    have ht:=MvPolynomial.le_weightedTotalDegree AT he
    simp only [RCN081.weight_fin4,BE,AT,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Nat.mul_zero,Nat.mul_one,
      Nat.zero_add,Nat.add_zero] at hs ht
    change e 1+e 2+e 3≤wt AT F at ht
    exact ⟨by omega,hs,(hbox he).2.2⟩
  support:=by
    constructor<;>dsimp only [cellSupport,RCN198.support,cellA,cellB,cellS]<;>omega
  selected:=selected
  seeds:=seeds
  degree:=hdegree
  agreement:=hagreement
  solution:=hsolution
  regular:=hregular
  noPencil:=hno

theorem EUE (g:Fin 21) (D L s:ℕ) (F:MvPolynomial (Fin 4) K)
    (hDlow:131072≤D) (hDchar:D<2130706433)
    (hF:Irreducible F) (hrdegree:0<F.degreeOf 2)
    (hbox:F ∈ BA K D w L s)
    (ht:wt AT F≤7501) (hy:wt BC F≤142)
    (hr:wt BE F≤31)
    (selected:K→Polynomial K) (seeds:Finset K)
    (hdegree: ∀gamma ∈ seeds,(selected gamma).natDegree≤w)
    (hagreement: ∀gamma ∈ seeds,181235≤
      (Finset.univ.filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hsolution: ∀gamma ∈ seeds,BM K (selected gamma) gamma F=0)
    (hregular: ∀gamma ∈ seeds,
      BM K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno:BL selected seeds w 80909)
    (hI:Fintype.card I=262144)
    (ha:Active g (FX F)):
    seeds.card≤ledgerCap g (FX F):=by
  let p:=FX F
  have ha' :3≤p.all∧2≤p.yz∧3≤p.zOnly∧
      WI.sourceLimit g<p.all+p.yz+p.zOnly:=ha
  have h3:3≤wt BE F:=ha'.1
  have hry:wt BE F+2≤wt BC F:=by
    have hv:2≤wt BC F-wt BE F:=ha'.2.1
    omega
  have hyt:wt BC F+2≤wt AT F:=by
    have hz:3≤wt AT F-wt BC F:=ha'.2.2.1
    omega
  have htotal:p.all+p.yz+p.zOnly=wt AT F:=by
    change wt BE F+(wt BC F-wt BE F)+
      (wt AT F-wt BC F)=wt AT F
    omega
  let S:=ofCarrier D L s F hDlow hDchar hF hrdegree hbox ht hy hr h3 hry hyt
    selected seeds hdegree hagreement hsolution hregular hno
  have hown:GU.Own S:=rfl
  have hL:WI.sourceLimit g<S.t:=by
    change WI.sourceLimit g<wt AT F
    rw [← htotal]
    exact ha'.2.2.2
  exact WI.count_group S hI hown g hL

end Carrier
end
end ATY
end MergedPart3

end ProximityPrize.SubmissionLower
end
