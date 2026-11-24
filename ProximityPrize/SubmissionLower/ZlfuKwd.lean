import ProximityPrize.SubmissionLower.ZNOTm7b
import ProximityPrize.SubmissionLower.Zm5KYKd
import ProximityPrize.SubmissionLower.ZDqG8Fa
import ProximityPrize.SubmissionLower.ZTqYzLd
import ProximityPrize.SubmissionLower.ZSSMtJa
import ProximityPrize.SubmissionLower.ZAcMpba
import ProximityPrize.SubmissionLower.Zv93Rac
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZbVGGOc
import ProximityPrize.SubmissionLower.Z7znM4a
import ProximityPrize.SubmissionLower.Z5KYTEa
import ProximityPrize.SubmissionLower.Zytxfqb
import ProximityPrize.SubmissionLower.Z9of3la
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZrgYIVd
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.ZEXAOre
import ProximityPrize.SubmissionLower.ZNBvygc
import ProximityPrize.SubmissionLower.ZLt6kU
set_option Elab.async false
section
namespace qSQfSDc
noncomputable section
open Finset MvPolynomial Module
open cu (L)
open qQ9yWTb (Curve)
open q1vkLGd (Smooth)
private abbrev V (d:ℕ) :=restrictTotalDegree (Fin 2) L d
private theorem degree_dim (d:ℕ) :2*finrank L (V d)=(d+1)*(d+2) := by
 rw [V,restrictTotalDegree,finrank_eq_nat_card_basis (basisRestrictSupport L _),
  Nat.card_coe_set_eq]
 change 2 * {e :Fin 2 →₀ ℕ | e.degree≤d}.ncard= _
 rw [Finsupp.ncard_setOf_degree_le,Nat.card_eq_fintype_card,Fintype.card_fin,
  Nat.mul_comm 2,Nat.mul_comm (d+1) (d+2)]
 simpa only [Nat.choose_one_right] using
  (Nat.add_one_mul_choose_eq (d+1) 1).symm
private def ED (z :Fin 2→L) :Dual L Curve :=
 (aeval z :Curve →ₐ[L] L).toLinearMap
private theorem select {ι E :Type} [AddCommGroup E] [Module L E]
  (v :ι→Dual L E) (h:Submodule.span L (Set.range v) = ⊤) :
  ∃ (J:Type) (b:Basis J L (Dual L E)) (i:J ↪ ι),∀ j,b j=v (i j) := by
 let b:=Basis.ofSpan h.ge
 have hb (j:_) :b j∈Set.range v :=Basis.ofSpan_subset h.ge ⟨j,rfl⟩
 choose i hi using hb
 refine ⟨_,b,⟨i,?_⟩,fun j=>(hi j).symm⟩
 intro j k he
 exact b.injective ((hi j).symm.trans ((congrArg v he).trans (hi k)))
private theorem smooth_on {J:Type} [Finite J] [DecidableEq J] (z :J→Fin 2→L) (d:ℕ)
    (g:J→V d) (hg : ∀ j k,eval (z k) (g j).1=if k=j then 1 else 0)
    [Nonempty J] : ∃ f :Curve,f≠0∧f.totalDegree≤d+1 ∧ ∀ j,Smooth f (z j) := by
  classical
  let S:Submodule L Curve :=V (d+1) ⊓ ⨅ j,LinearMap.ker (ED (z j))
  let D (j:J) :Dual L Curve :=(ED (z j)).comp (pderiv 0).toLinearMap
  have h (j:J) : ∃ f∈S,D j f≠0:= by
    let l:Curve :=MvPolynomial.X 0 - C (z j 0)
    have hl:eval (z j) l=0:= by simp [l]
    have hp:pderiv 0 l=1 := by simp [l]
    refine ⟨l*(g j).1,⟨(mem_restrictTotalDegree _ _ _).mpr ?_,?_⟩,?_⟩
    · have hld:l.totalDegree≤1 :=(totalDegree_sub_C_le _ _).trans_eq (totalDegree_X _)
      exact (totalDegree_mul _ _).trans <| (Nat.add_le_add hld
        ((mem_restrictTotalDegree _ _ _).mp (g j).2)).trans_eq (Nat.add_comm 1 d)
    · apply (Submodule.mem_iInf _).mpr
      intro k
      change eval (z k) (l*(g j).1)=0
      rw [map_mul,hg j k]
      by_cases he :k=j
      · subst k
        simp [hl]
      · simp [he]
    · change eval (z j) (pderiv 0 (l*(g j).1))≠0
      simp [hp,hg j j,hl]
  obtain ⟨f,hf,hD⟩:=Dual.exists_forall_mem_ne_zero_of_forall_exists S D h
  refine ⟨f,?_,(mem_restrictTotalDegree _ _ _).mp hf.1,fun j=>⟨?_,0,hD j⟩⟩
  · intro hzero
    subst f
    exact hD (Classical.choice ‹Nonempty J›) (map_zero _)
  · exact (Submodule.mem_iInf _).mp hf.2 j
theorem proof :q1vkLGd.c1 := by
 classical
 intro T s _ d
 by_cases h : ∃ f :Curve,f≠0∧f.totalDegree≤d ∧ ∀ γ∈T,eval (s γ) f=0
 · exact Or.inl h
 right
 let v (a : ↥T) :Dual L (V d) :=(ED (s a)).comp (V d).subtype
 have hv :Submodule.span L (Set.range v) = ⊤ := by
   apply Submodule.span_eq_top_of_ne_zero
   intro f hf
   by_contra! hz
   exact h ⟨f.1,fun he=>hf (Subtype.ext he),(mem_restrictTotalDegree _ _ _).mp f.2,
     fun a ha=>hz (v ⟨a,ha⟩) ⟨⟨a,ha⟩,rfl⟩⟩
 obtain ⟨J,b,i,hi⟩:=select v hv
 let _:Finite J:=Module.Finite.finite_basis b
 let _:Fintype J:=Fintype.ofFinite J
 have hcard:2*Fintype.card J=(d+1)*(d+2) := by
   rw [← finrank_eq_card_basis b,Subspace.dual_finrank_eq,degree_dim]
 have hpos :0<(d+1)*(d+2) :=Nat.mul_pos (by omega) (by omega)
 let _:Nonempty J:=Fintype.card_pos_iff.mp (by omega)
 let g (j:J) :V d:=(Module.evalEquiv L (V d)).symm (b.dualBasis j)
 have hg (j k :J) :eval (s (i k)) (g j).1=if k=j then 1 else 0:= by
   change v (i k) (g j)= _
   rw [← hi k]
   change b k ((Module.evalEquiv L (V d)).symm (b.dualBasis j))= _
   rw [Module.apply_evalEquiv_symm_apply,b.dualBasis_apply_self]
 obtain ⟨f,hf,hdeg,hs⟩:=smooth_on (fun j=>s (i j)) d g hg
 let e :J ↪ _:=i.trans ⟨Subtype.val,Subtype.val_injective⟩
 let U:=univ.map e
 refine ⟨U,?_,?_,f,hf,hdeg,?_⟩
 · intro a ha
   obtain ⟨j,_,rfl⟩:=mem_map.mp ha
   exact (i j).2
 · simpa only [U,card_map,card_univ] using hcard.symm.le
 · intro a ha
   obtain ⟨j,_,rfl⟩:=mem_map.mp ha
   exact hs j
end
end qSQfSDc
end
section
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3000 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s6) 3000 e ((((P5_7_3.fO.s6).schedule.gw).drop a).take 1)
theorem yQh0:gZ! 10 9:=⟨r! 167871 10 211 73 76 25 5 9 5 0xa6000462b800da67a00c7532a59ee51e,trivial⟩
theorem yQh1:gZ! 11 10:=⟨r! 168460 11 200 76 76 22 5 9 5 0x37a00068fe80320a44b459fc,trivial⟩
theorem yQh2:gZ! 12 11:=⟨r! 168460 12 186 76 76 22 5 6 5 0x299c0064640031eab4b47752,trivial⟩
theorem yQh3:gZ! 13 12:=⟨r! 168460 13 170 76 76 22 5 3 5 0x1d30005ff98031ce74b492bc,trivial⟩
theorem yQh4:gZ! 14 13:=⟨r! 168460 14 152 76 76 22 5 1 5 0x12d8005bad0031b564b4ac3e,trivial⟩
theorem grades3000C:GradeSigns (terminal .s6) 3000 10 ((((P5_7_3.fO.s6).schedule.gw).drop 9).take 5) :=⟨yQh0.1,yQh1.1,yQh2.1,yQh3.1,yQh4.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3000 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s6) 3000 e ((((P5_7_3.fO.s6).schedule.gw).drop a).take 1)
theorem yQh5:gZ! 15 14:=⟨r! 168460 15 131 75 76 23 5 11 4 0xaea002bd7200c68da96984c8,trivial⟩
theorem yQh6:gZ! 16 15:=⟨r! 168460 16 108 72 76 26 5 9 4 0x54c00053ae2803194804b4d70c4,trivial⟩
theorem yQh7:gZ! 17 16:=⟨r! 168460 17 84 76 76 22 5 8 4 0x1e0004f7b80318534b4eb84,trivial⟩
theorem yQh8:gZ! 18 17:=⟨r! 168460 18 57 76 76 22 5 6 4 0x54004b8300317c8434fd40,trivial⟩
theorem yQh9:gZ! 19 18:=⟨r! 168460 19 28 76 76 22 5 5 4 0x479e803176d4350db0,trivial⟩
theorem grades3000D:GradeSigns (terminal .s6) 3000 15 (((P5_7_3.fO.s6).schedule.gw).drop 14) :=⟨yQh5.1,yQh6.1,yQh7.1,yQh8.1,yQh9.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3050 e v k l b d z n x
theorem ordinary3050:Signs (terminal .tT) 3050 19 0 :=
 r! 168460 19 0 81 76 17 5 4 4 0x5c000af225b160
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tT) 3050 e ((((P5_7_3.fO.tT).schedule.gw).drop a).take 1)
theorem yQh10:gZ! 1 0:=⟨r! 127232 1 237 74 76 23 4 7 4 0x556c00ee430069221578c190,trivial⟩
theorem yQh11:gZ! 2 1:=⟨r! 128747 2 233 76 76 21 4 8 4 0x62a003bc1806b2c15ef0b8,trivial⟩
theorem yQh12:gZ! 3 2:=⟨r! 129800 3 228 71 76 26 4 9 4 0x6e02801da30601b1bdeabef67a2,trivial⟩
theorem yQh13:gZ! 4 3:=⟨r! 132226 4 224 76 76 22 4 10 4 0x3f2800f10400e0342a0b1e8,trivial⟩
theorem grades3050A:GradeSigns (terminal .tT) 3050 1 (((P5_7_3.fO.tT).schedule.gw).take 4) :=⟨yQh10.1,yQh11.1,yQh12.1,yQh13.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3050 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tT) 3050 e ((((P5_7_3.fO.tT).schedule.gw).drop a).take 1)
theorem yQh14:gZ! 5 4:=⟨r! 134427 5 219 77 76 21 4 11 4 0x466001e6a0039b7d90e940,trivial⟩
theorem yQh15:gZ! 6 5:=⟨r! 136546 6 213 75 76 23 4 12 4 0x4c68007a62003b58a645dbce,trivial⟩
theorem yQh16:gZ! 7 6:=⟨r! 139976 7 207 75 76 23 4 2 5 0x400053b0007dd6803e35764976ee,trivial⟩
theorem yQh17:gZ! 8 7:=⟨r! 144523 8 200 74 76 24 4 4 5 0x440005ab60041dfc0108e26c9cb5fc,trivial⟩
theorem yQh18:gZ! 9 8:=⟨r! 152512 9 192 74 76 24 4 7 5 0x7a0006586004909601274eceae7e2e,trivial⟩
theorem grades3050B:GradeSigns (terminal .tT) 3050 5 ((((P5_7_3.fO.tT).schedule.gw).drop 4).take 5) :=⟨yQh14.1,yQh15.1,yQh16.1,yQh17.1,yQh18.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3050 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tT) 3050 e ((((P5_7_3.fO.tT).schedule.gw).drop a).take 1)
theorem yQh19:gZ! 10 9:=⟨r! 168460 10 182 77 76 21 5 11 5 0x20003d5000b5fa00b52aa5a93be,trivial⟩
theorem yQh20:gZ! 11 10:=⟨r! 168460 11 168 76 76 22 5 8 5 0x2c700055e8002d1424b54b18,trivial⟩
theorem yQh21:gZ! 12 11:=⟨r! 168460 12 151 71 76 27 5 4 5 0x1dea600289e9800b3a34c86ad4b80,trivial⟩
theorem yQh22:gZ! 13 12:=⟨r! 168460 13 133 76 76 22 5 2 5 0x11e4004c4b802cbc343589cc,trivial⟩
theorem yQh23:gZ! 14 13:=⟨r! 168460 14 111 72 76 26 5 11 4 0x94500047d3f802c9fcd435a3744,trivial⟩
theorem grades3050C:GradeSigns (terminal .tT) 3050 10 ((((P5_7_3.fO.tT).schedule.gw).drop 9).take 5) :=⟨yQh19.1,yQh20.1,yQh21.1,yQh22.1,yQh23.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3050 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tT) 3050 e ((((P5_7_3.fO.tT).schedule.gw).drop a).take 1)
theorem yQh24:gZ! 15 14:=⟨r! 168460 15 88 76 76 22 5 9 4 0x3a400430c002c822435bd24,trivial⟩
theorem yQh25:gZ! 16 15:=⟨r! 168460 16 62 76 76 22 5 8 4 0xd4003e6d002c6e0435d38c,trivial⟩
theorem yQh26:gZ! 17 16:=⟨r! 168460 17 33 71 76 27 5 6 4 0x78001cfc7200b18b2086bce3fc,trivial⟩
theorem yQh27:gZ! 18 17:=⟨r! 168460 18 3 76 76 22 5 5 4 0x3580802c560435faa6,trivial⟩
theorem grades3050D:GradeSigns (terminal .tT) 3050 15 (((P5_7_3.fO.tT).schedule.gw).drop 14) :=⟨yQh24.1,yQh25.1,yQh26.1,yQh27.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (Signs GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3100 e v k l b d z n x
theorem ordinary3100:Signs (terminal .s7) 3100 17 0 :=
 r! 168460 17 0 80 76 18 5 5 4 0x27000268d436eee
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s7) 3100 e ((((P5_7_3.fO.s7).schedule.gw).drop a).take 1)
theorem yQh28:gZ! 1 0:=⟨r! 120852 1 213 75 75 22 5 7 4 0x1fac00591b802a50e5376c54,trivial⟩
theorem yQh29:gZ! 2 1:=⟨r! 122219 2 209 76 75 21 5 8 4 0x257800b26e00abd2a9c5f1a,trivial⟩
theorem yQh30:gZ! 3 2:=⟨r! 124016 3 205 76 75 21 5 9 4 0x2c1000b3bc00afac29d3d94,trivial⟩
theorem yQh31:gZ! 4 3:=⟨r! 125423 4 200 75 76 22 4 10 4 0x63980165fe0164d12bbe1d0,trivial⟩
theorem yQh32:gZ! 5 4:=⟨r! 127536 5 195 75 76 22 4 11 4 0x70780168ae016e9dabdfa6e,trivial⟩
theorem grades3100A:GradeSigns (terminal .s7) 3100 1 (((P5_7_3.fO.s7).schedule.gw).take 5) :=⟨yQh28.1,yQh29.1,yQh30.1,yQh31.1,yQh32.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3100 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s7) 3100 e ((((P5_7_3.fO.s7).schedule.gw).drop a).take 1)
theorem yQh33:gZ! 6 5:=⟨r! 130719 6 190 76 75 22 5 1 5 0x1fdc002e408017f275a094f4,trivial⟩
theorem yQh34:gZ! 7 6:=⟨r! 134480 7 184 76 75 22 5 3 5 0x80002338002fd400193d76228252,trivial⟩
theorem yQh35:gZ! 8 7:=⟨r! 140064 8 177 75 76 23 4 6 5 0x3c0004d7c0066208036a8f64ae5b2,trivial⟩
theorem yQh36:gZ! 9 8:=⟨r! 152557 9 169 77 76 21 4 11 5 0xe0005de001ebe80412bdd63106,trivial⟩
theorem yQh37:gZ! 10 9:=⟨r! 168460 10 156 76 76 22 5 10 5 0x3360004c1080280474361152,trivial⟩
theorem grades3100B:GradeSigns (terminal .s7) 3100 6 ((((P5_7_3.fO.s7).schedule.gw).drop 5).take 5) :=⟨yQh33.1,yQh34.1,yQh35.1,yQh36.1,yQh37.1,trivial⟩
end qHo4MUb
end
end
section
section
set_option autoImplicit true
namespace qaYBFeb
open scoped qqf9uAa
set_option quotPrecheck false in
scoped notation "r2800!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨8400,11722,2444,u⟩,0x3d818764c80000,0x1c91bb99c39fb⟩:Dt.Bank) 2800 e v k l b d z n x
set_option quotPrecheck false in
scoped notation "r2900!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨8400,11702,2444,u⟩,0x3d818764c80000,0x1c69affdd747b⟩:Dt.Bank) 2900 e v k l b d z n x
end qaYBFeb
end
section
set_option autoImplicit true
namespace q65qCJc
set_option quotPrecheck false in
scoped notation "receipt!" h:arg u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 qqf9uAa.book ⟨⟨7200,10017,2095,u⟩,0x26bd0736200000,0xf4625385a36c⟩
  h e v k l b d z n x (by
    repeat' apply And.intro
    all_goals first | exact True.intro | decide +kernel) rfl rfl rfl rfl rfl
end q65qCJc
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨7200,10017,2095,u⟩,0x26bd0736200000,0xf4625385a36c⟩:Dt.Bank) 2980 e v k l b d z n x
theorem ordinary2980:Signs (terminal .tI) 2980 20 0 :=
 r! 205763 20 0 81 78 18 4 12 3 0x29a00db0abfa3a
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tI) 2980 e ((((P5_7_3.fO.tI).schedule.gw).drop a).take 1)
theorem yQh38:gZ! 1 0:=⟨r! 157507 1 279 76 77 23 4 3 4 0x23c00372880261b56492f32,trivial⟩
theorem yQh39:gZ! 2 1:=⟨r! 158611 2 274 75 77 24 4 4 4 0x3bc001bbc60098a96c948da8,trivial⟩
theorem yQh40:gZ! 3 2:=⟨r! 160088 3 269 71 77 28 4 4 4 0x5c22001bfa580099a91ac9774ab8,trivial⟩
theorem yQh41:gZ! 4 3:=⟨r! 162045 4 264 74 77 25 4 5 4 0x85f000e2bb8026e94193699e2,trivial⟩
theorem grades2980A:GradeSigns (terminal .tI) 2980 1 (((P5_7_3.fO.tI).schedule.gw).take 4) :=⟨yQh38.1,yQh39.1,yQh40.1,yQh41.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨7200,10017,2095,u⟩,0x26bd0736200000,0xf4625385a36c⟩:Dt.Bank) 2980 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tI) 2980 e ((((P5_7_3.fO.tI).schedule.gw).drop a).take 1)
theorem yQh42:gZ! 5 4:=⟨r! 164641 5 259 76 77 23 4 6 4 0xba40039c60027bd47503714,trivial⟩
theorem yQh43:gZ! 6 5:=⟨r! 167075 6 253 76 77 23 4 7 4 0xf0c003a6280287d5752aae0,trivial⟩
theorem yQh44:gZ! 7 6:=⟨r! 170661 7 247 76 77 23 4 9 4 0x1304003bd00029dc47564f5a,trivial⟩
theorem yQh45:gZ! 8 7:=⟨r! 174879 8 240 76 77 23 4 11 4 0x16c8003d87802b9c075aaebe,trivial⟩
theorem yQh46:gZ! 9 8:=⟨r! 180812 9 232 69 77 30 5 1 5 0x40000d17ac00205468001730c5f4307d2344,trivial⟩
theorem grades2980B:GradeSigns (terminal .tI) 2980 5 ((((P5_7_3.fO.tI).schedule.gw).drop 4).take 5) :=⟨yQh42.1,yQh43.1,yQh44.1,yQh45.1,yQh46.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨7200,10017,2095,u⟩,0x26bd0736200000,0xf4625385a36c⟩:Dt.Bank) 2980 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tI) 2980 e ((((P5_7_3.fO.tI).schedule.gw).drop a).take 1)
theorem yQh47:gZ! 10 9:=⟨r! 191957 10 223 75 77 24 5 5 5 0xef8000922a801a2ff92da8c1a,trivial⟩
theorem yQh48:gZ! 11 10:=⟨r! 205763 11 211 76 77 23 5 7 5 0xe2a0014d6c0078cd6a7d8990,trivial⟩
theorem yQh49:gZ! 12 11:=⟨r! 205763 12 196 76 77 23 5 4 5 0x7bc0012d1e00771a4a7dcb78,trivial⟩
theorem yQh50:gZ! 13 12:=⟨r! 205763 13 179 77 77 22 5 1 5 0x33400219c801d62853f04a2,trivial⟩
theorem yQh51:gZ! 14 13:=⟨r! 205763 14 159 76 78 23 4 10 4 0x190003b78803a1ca57e3fb6,trivial⟩
theorem grades2980C:GradeSigns (terminal .tI) 2980 10 ((((P5_7_3.fO.tI).schedule.gw).drop 9).take 5) :=⟨yQh47.1,yQh48.1,yQh49.1,yQh50.1,yQh51.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨7200,10017,2095,u⟩,0x26bd0736200000,0xf4625385a36c⟩:Dt.Bank) 2980 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tI) 2980 e ((((P5_7_3.fO.tI).schedule.gw).drop a).take 1)
theorem yQh52:gZ! 15 14:=⟨r! 205763 15 137 76 78 23 4 8 4 0xc0033cd003980357e72b8,trivial⟩
theorem yQh53:gZ! 16 15:=⟨r! 205763 16 113 77 78 22 4 6 4 0x58fe00e3b7abf512a,trivial⟩
theorem yQh54:gZ! 17 16:=⟨r! 205763 17 86 77 78 22 4 4 4 0x4bc400e1c8abf661a,trivial⟩
theorem yQh55:gZ! 18 17:=⟨r! 205763 18 57 77 78 22 4 3 4 0x3f9800dfeeabf79b0,trivial⟩
theorem yQh56:gZ! 19 18:=⟨r! 205763 19 25 75 78 24 4 1 4 0xd2b200de57aafe2bbc,trivial⟩
theorem grades2980D:GradeSigns (terminal .tI) 2980 15 (((P5_7_3.fO.tI).schedule.gw).drop 14) :=⟨yQh52.1,yQh53.1,yQh54.1,yQh55.1,yQh56.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3000 e v k l b d z n x
theorem ordinary3000:Signs (terminal .s6) 3000 20 0 :=
 r! 168460 20 0 78 76 20 5 4 4 0x10df80316a90d47f8
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s6) 3000 e ((((P5_7_3.fO.s6).schedule.gw).drop a).take 1)
theorem yQh57:gZ! 1 0:=⟨r! 135121 1 267 76 76 22 4 7 4 0x3d20014792010495b216f2a,trivial⟩
theorem yQh58:gZ! 2 1:=⟨r! 136018 2 262 74 76 24 4 8 4 0x43140051366010768cc87a5a2,trivial⟩
theorem yQh59:gZ! 3 2:=⟨r! 138065 3 258 76 76 22 4 9 4 0x4b80014874010ed8322f74a,trivial⟩
theorem yQh60:gZ! 4 3:=⟨r! 139760 4 253 76 76 22 4 10 4 0x52c001497a0114f7b23dc32,trivial⟩
theorem grades3000A:GradeSigns (terminal .s6) 3000 1 (((P5_7_3.fO.s6).schedule.gw).take 4) :=⟨yQh57.1,yQh58.1,yQh59.1,yQh60.1,trivial⟩
end qsX8Fva
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qsX8Fva
open qqf9uAa
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3000 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s6) 3000 e ((((P5_7_3.fO.s6).schedule.gw).drop a).take 1)
theorem yQh61:gZ! 5 4:=⟨r! 141151 5 247 75 76 23 4 10 4 0x589800a42c00467c2649391a,trivial⟩
theorem yQh62:gZ! 6 5:=⟨r! 144203 6 242 77 76 21 4 12 4 0x61b002a050049765931e5e,trivial⟩
theorem yQh63:gZ! 7 6:=⟨r! 146449 7 235 73 76 25 4 1 5 0x672d002a648004ba961d3bc298,trivial⟩
theorem yQh64:gZ! 8 7:=⟨r! 151402 8 229 76 76 22 4 3 5 0x60007178016520014354baa33bc,trivial⟩
theorem yQh65:gZ! 9 8:=⟨r! 157251 9 221 76 76 22 5 5 5 0x180003d50005f3e802b9d142d896a,trivial⟩
theorem grades3000B:GradeSigns (terminal .s6) 3000 5 ((((P5_7_3.fO.s6).schedule.gw).drop 4).take 5) :=⟨yQh61.1,yQh62.1,yQh63.1,yQh64.1,yQh65.1,trivial⟩
end qsX8Fva
end
end
section
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2715 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daC) 2715 e ((((P5_7_3.fO.daC).schedule.gw).drop a).take 1)
theorem yQh66:gZ! 19 18:=⟨r! 131530 19 607 69 72 24 4 3 3 0x35423f0a288c84da2,trivial⟩
theorem yQh67:gZ! 20 19:=⟨r! 153600 20 569 69 72 25 4 3 3 0xb288ad0db99109366,trivial⟩
theorem yQh68:gZ! 21 20:=⟨r! 153600 21 524 70 72 24 4 2 3 0x6a22b231ac886b06,trivial⟩
theorem yQh69:gZ! 22 21:=⟨r! 153600 22 474 65 72 29 4 2 3 0x5c88ac15a51911121d8,trivial⟩
theorem yQh70:gZ! 23 22:=⟨r! 153600 23 422 69 72 25 4 2 3 0x8ab9efd9114d96,trivial⟩
theorem yQh71:gZ! 24 23:=⟨r! 153600 24 365 66 72 28 4 2 3 0x22accf06c88c1934,trivial⟩
theorem grades2715D:GradeSigns (terminal .daC) 2715 19 ((((P5_7_3.fO.daC).schedule.gw).drop 18).take 6) :=⟨yQh66.1,yQh67.1,yQh68.1,yQh69.1,yQh70.1,yQh71.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3349,708,u⟩,0x173aef7b80000,0x3159e5efa65⟩:Dt.Bank) 2715 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daC) 2715 e ((((P5_7_3.fO.daC).schedule.gw).drop a).take 1)
theorem yQh72:gZ! 25 24:=⟨r! 153600 25 306 69 72 25 4 1 3 0x8aac9ed911b81e,trivial⟩
theorem yQh73:gZ! 26 25:=⟨r! 153600 26 242 66 72 28 4 1 3 0x22a9a9c8c88f3e72,trivial⟩
theorem yQh74:gZ! 27 26:=⟨r! 153600 27 176 69 72 25 4 1 3 0x8aa0c4191216f0,trivial⟩
theorem yQh75:gZ! 28 27:=⟨r! 153600 28 106 69 72 25 4 1 3 0x8a9b4c591242ae,trivial⟩
theorem yQh76:gZ! 29 28:=⟨r! 153600 29 33 69 72 25 4 1 3 0x8a961119126c8c,trivial⟩
theorem grades2715E:GradeSigns (terminal .daC) 2715 25 (((P5_7_3.fO.daC).schedule.gw).drop 24) :=⟨yQh72.1,yQh73.1,yQh74.1,yQh75.1,yQh76.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (Signs GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3350,708,u⟩,0x173aef7b80000,0x316608594b8⟩:Dt.Bank) 2725 e v k l b d z n x
theorem ordinary2725:Signs (terminal .daF) 2725 29 0 :=
 r! 153600 29 0 75 72 19 4 1 3 0x8bb35642616
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daF) 2725 e ((((P5_7_3.fO.daF).schedule.gw).drop a).take 1)
theorem yQh77:gZ! 1 0:=⟨r! 87303 1 778 65 71 27 4 1 3 0x149e88f6490845542e94,trivial⟩
theorem yQh78:gZ! 2 1:=⟨r! 87842 2 771 68 71 24 4 1 3 0xc2a23e45828acb066,trivial⟩
theorem yQh79:gZ! 3 2:=⟨r! 88273 3 763 67 71 25 4 1 3 0x70588fb42a515ce5bc,trivial⟩
theorem yQh80:gZ! 4 3:=⟨r! 88781 4 755 67 71 25 4 1 3 0x80d88fde3511610b0e,trivial⟩
theorem yQh81:gZ! 5 4:=⟨r! 89374 5 747 68 71 24 4 2 3 0x125a24041588b2f208,trivial⟩
theorem yQh82:gZ! 6 5:=⟨r! 90069 6 739 69 71 23 4 2 3 0x2998904c4e45ae5ca,trivial⟩
theorem grades2725A:GradeSigns (terminal .daF) 2725 1 (((P5_7_3.fO.daF).schedule.gw).take 6) :=⟨yQh77.1,yQh78.1,yQh79.1,yQh80.1,yQh81.1,yQh82.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3350,708,u⟩,0x173aef7b80000,0x316608594b8⟩:Dt.Bank) 2725 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daF) 2725 e ((((P5_7_3.fO.daF).schedule.gw).drop a).take 1)
theorem yQh83:gZ! 7 6:=⟨r! 90689 7 730 68 71 24 4 2 3 0x173424205908b85e22,trivial⟩
theorem yQh84:gZ! 8 7:=⟨r! 91441 8 721 68 71 24 4 2 3 0x19c62430d708bb7ef8,trivial⟩
theorem yQh85:gZ! 9 8:=⟨r! 92148 9 711 63 71 29 4 2 3 0xe1c1091015e0517cefc9a,trivial⟩
theorem yQh86:gZ! 10 9:=⟨r! 93250 10 702 69 71 23 4 2 3 0x3e509166374618cd8,trivial⟩
theorem yQh87:gZ! 11 10:=⟨r! 94163 11 691 65 71 27 4 2 3 0x4335891b97d84637fb7a,trivial⟩
theorem yQh88:gZ! 12 11:=⟨r! 95591 12 681 69 71 23 4 2 3 0x49309240c85668f6c,trivial⟩
theorem grades2725B:GradeSigns (terminal .daF) 2725 7 ((((P5_7_3.fO.daF).schedule.gw).drop 6).take 6) :=⟨yQh83.1,yQh84.1,yQh85.1,yQh86.1,yQh87.1,yQh88.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3350,708,u⟩,0x173aef7b80000,0x316608594b8⟩:Dt.Bank) 2725 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daF) 2725 e ((((P5_7_3.fO.daF).schedule.gw).drop a).take 1)
theorem yQh89:gZ! 13 12:=⟨r! 96953 13 669 68 71 24 4 3 3 0x270a24b0da2ad30d56,trivial⟩
theorem yQh90:gZ! 14 13:=⟨r! 98843 14 657 68 71 24 4 3 3 0x29be24df8fcadb62de,trivial⟩
theorem yQh91:gZ! 15 14:=⟨r! 101274 15 644 69 71 23 4 3 3 0x58f89475f75732806,trivial⟩
theorem yQh92:gZ! 16 15:=⟨r! 104455 16 629 69 71 23 4 4 3 0x5e9095c5f967a7c42,trivial⟩
theorem yQh93:gZ! 17 16:=⟨r! 109597 17 612 69 71 24 4 4 3 0x19e823001d0c86c440,trivial⟩
theorem yQh94:gZ! 18 17:=⟨r! 119425 18 591 69 72 24 3 4 3 0x7cc91c9b2b69fcb5c,trivial⟩
theorem grades2725C:GradeSigns (terminal .daF) 2725 13 ((((P5_7_3.fO.daF).schedule.gw).drop 12).take 6) :=⟨yQh89.1,yQh90.1,yQh91.1,yQh92.1,yQh93.1,yQh94.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3350,708,u⟩,0x173aef7b80000,0x316608594b8⟩:Dt.Bank) 2725 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daF) 2725 e ((((P5_7_3.fO.daF).schedule.gw).drop a).take 1)
theorem yQh95:gZ! 19 18:=⟨r! 141558 19 561 69 72 24 4 4 3 0x2e382510290adfd6c4,trivial⟩
theorem yQh96:gZ! 20 19:=⟨r! 153600 20 518 70 72 24 4 4 3 0x168e22fc63cc83b1e2,trivial⟩
theorem yQh97:gZ! 21 20:=⟨r! 153600 21 469 68 72 26 4 3 3 0x404e22fabb5b20f4b70,trivial⟩
theorem yQh98:gZ! 22 21:=⟨r! 153600 22 417 67 72 27 4 3 3 0x158108be4511641f94fc,trivial⟩
theorem yQh99:gZ! 23 22:=⟨r! 153600 23 362 69 72 25 4 3 3 0x34c88bddbb19082248,trivial⟩
theorem yQh100:gZ! 24 23:=⟨r! 153600 24 302 64 72 30 4 2 3 0xe5da22f5e630b210b2a3c,trivial⟩
theorem grades2725D:GradeSigns (terminal .daF) 2725 19 ((((P5_7_3.fO.daF).schedule.gw).drop 18).take 6) :=⟨yQh95.1,yQh96.1,yQh97.1,yQh98.1,yQh99.1,yQh100.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qNKxb0a
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨2400,3350,708,u⟩,0x173aef7b80000,0x316608594b8⟩:Dt.Bank) 2725 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daF) 2725 e ((((P5_7_3.fO.daF).schedule.gw).drop a).take 1)
theorem yQh101:gZ! 25 24:=⟨r! 153600 25 240 70 72 24 4 2 3 0x19a22f451cc8447f2,trivial⟩
theorem yQh102:gZ! 26 25:=⟨r! 153600 26 173 68 72 26 4 2 3 0x20622f2d9b32118222,trivial⟩
theorem yQh103:gZ! 27 26:=⟨r! 153600 27 103 66 72 28 4 2 3 0x11222f166b2c847827a,trivial⟩
theorem yQh104:gZ! 28 27:=⟨r! 153600 28 30 68 72 26 4 2 3 0x22effd4b2123b46,trivial⟩
theorem grades2725E:GradeSigns (terminal .daF) 2725 25 (((P5_7_3.fO.daF).schedule.gw).drop 24) :=⟨yQh101.1,yQh102.1,yQh103.1,yQh104.1,trivial⟩
end qNKxb0a
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (book)
set_option quotPrecheck false in
scoped notation "rLo!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 book (⟨⟨1600,2234,472,u⟩,0x6e3d37900000,0x9c78f462de⟩:Dt.Bank) 2750 e v k l b d z n x (by
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel) rfl rfl rfl rfl rfl
set_option quotPrecheck false in
scoped notation "rHi!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 book (⟨⟨8400,11722,2444,u⟩,0x3d818764c80000,0x1c91bb99c39fb⟩:Dt.Bank) 2775 e v k l b d z n x (by
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel) rfl rfl rfl rfl rfl
end q5HD6ae
end
end
section
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def r0:=m2! 61 13 428950
private def r1 :=m2! 65 14 552788
private def r2 :=m2! 72 16 841239
private def r3:=m2! 75 16 957077
private def r4 :=m2! 79 17 1179228
private def r5:=m2! 83 18 1437938
private def r6:=m2! 86 19 1674513
private def r7:=m2! 87 19 1737013
private def r8:=m2! 93 20 2228964
private def r9:=m2! 94 21 2390729
private def dz :=m2! 97 21 2641452
private def dD:=m2! 100 22 3011935
private def dK:=m2! 105 23 3635193
private def e8:=m2! 108 24 4103823
private def gD:=m2! 114 25 5024682
private def gx :=m2! 118 26 5774377
private def iu:=m2! 122 27 6604929
private def kD:=m2! 127 28 7713813
private def lH :=m2! 130 29 8531244
private def kR:=m2! 136 30 10105062
private def jV:=m2! 137 30 10343855
private def lp:=m2! 141 31 11621252
private def kZ:=m2! 144 32 12729182
private def lQ:=m2! 145 32 13013367
private def nJ:=m2! 147 33 13913593
private def nP:=m2! 151 33 15158299
private def qA:=m2! 152 34 15833621
private def tj:=m2! 155 34 16852996
private def qH :=m2! 158 35 18313194
private def oQ:=m2! 166 37 22362213
private def xM:=m2! 172 38 25559185
private def xd:=m2! 179 39 29610973
private def r32 :=m2! 180 40 30727249
private def A4 :=m2! 181 39 30680913
private def BY:=m2! 190 42 37902732
private def Cp:=m2! 191 38 35709156
private def EZ:=m2! 208 47 55148872
private def Iz :=p2! 212 47 58616088 26 2 0x171b7e6352
private def IB:=m2! 213 43 55592342
private def Ku:=p2! 218 49 66158447 26 2 0x21903f0f92f
private def Hz :=p2! 234 52 86843546 27 2 0x4602e524603e
private def ID :=p2! 237 52 90459259 27 2 0x5cad0d58b6da
private def LU:=p2! 238 48 86226612 27 2 0x4747e51acdb8
private def Vr :=p2! 244 55 0x62d69eb 27 2 0xc911d61447b1
private def Xv :=p2! 247 55 0x66c8fdf 27 2 0xf64c764dc651
private def Xw:=p2! 251 56 0x6db6545 27 2 0x14f0a5eb183fa
private def Cw:=p2! 253 56 0x7089a92 27 2 0x17892eed98835
private def Cx :=p2! 265 59 0x87dcd2b 28 2 0x63ac7281a20b9
private def zB:=p2! 272 60 0x959cd28 28 2 0x8be5d88cde750
private def CR:=p2! 273 56 0x8f913f4 28 2 0x7d795087b9aa4
private def Db:=p2! 280 63 0xaa6c000 28 2 0xd246ae9d47952
private def LB:=p2! 288 64 0xbccad0e 28 2 0x11ca584ab0078a
private def De :=p2! 290 58 0xb2efe3a 28 2 0xfe9b32a306308
private def LD:=p2! 294 65 0xcc1a54f 28 2 0x1615baab6049a5
private def OD:=p2! 306 63 0xe27e8a0 28 2 0x1db2710c4cc190
private def OK :=p2! 321 72 0x12495fec 28 2 0x34e9da6efac246
private def LH :=p2! 331 74 0x149b3254 29 2 0x8930aef051acdd
private def Vb:=p2! 333 67 0x1375624c 28 2 0x3ec2489f893dc3
private def Vc:=p2! 333 73 0x14ca45ad 29 2 0x8c825ef06632b6
private def WV:=p2! 338 70 0x151cf7c9 29 2 0x93a1a8d07fea83
private def OL:=p2! 344 71 0x1695456b 29 2 0xa9a21c3148348a
private def OM:=p2! 354 72 0x1905a6ab 29 2 0xd0a75e32806bba
private def OP:=p2! 362 79 0x1ce04d8e 29 2 0x10c6707547d1554
private def Vd:=p2! 363 75 0x1bfccd5c 29 2 0x100c3d8f3f6ae95
private def r64 :=p2! 372 77 0x1ee4e90d 29 2 0x1334592d54abc77
private def WZ:=p2! 373 84 0x21528d20 29 2 0x159355ef688e229
private def r66:=p2! 374 84 0x219c32db 29 2 0x15ea2cc16a71c7b
private def r67:=p2! 405 84 0x2b63ec50 29 2 0x22277fcfa502c69
private def r68:=p2! 407 84 0x2c149e97 29 2 0x230ffb15a8ca10d
private def r69:=p2! 408 84 0x2c6dadd9 29 2 0x2385a4f5aaadb5f
private def r70:=p2! 443 98 0x412b6560 30 3 0xf7c947e35306618e9cb3
private def W7:=p2! 451 93 0x424808ad 30 3 0x14d7588240c47a1a30037
private def Vo:=p2! 453 94 0x43c9d90c 30 3 0x1b00458663575621602f2
private def r73:=p2! 459 95 0x474aa726 30 3 0x2e01c79045299e30b5af8
private def r74 :=p2! 473 96 0x4f233f81 30 3 0x71b84ea6a48f2e5086368
def dataA:Array aqm := #[
 r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,dz,dD,dK,e8,gD,gx,iu,kD,lH,kR,jV,lp,kZ,lQ,
 nJ,nP,qA,tj,qH,oQ,xM,xd,r32,A4,BY,Cp,EZ,Iz,IB,Ku,Hz,ID,LU,Vr,Xv,Xw,Cw,Cx,
 zB,CR,Db,LB,De,LD,OD,OK,LH,Vb,Vc,WV,OL,OM,OP,Vd,r64,WZ,r66,r67,r68,r69,r70,W7,
 Vo,r73,r74
]
end qpECY2d
end
section
set_option autoImplicit true
namespace qpECY2d
open Dt (Bank)
open P5_7_3 (fO terminal stages)
private def banks :Array (Array aqm) := #[dataA,dataB,dataC,dataD,dataE,dataF,dataG,dataH,dataI,dataJ,dataK,dataL,dataM]
private def limits :Array ℕ := #[7749728,13648043,18432230,26558802,36602328,49382006,58671852,79545342,94110905,0x8918728,0x9c8482f,0xb6d898c,0xb72898c]
private def key (B J:ℕ) :=16384*B+J
private def search (a :Array aqm) (k :ℕ) :ℕ→ℕ→ℕ→aqm
 | 0,lo,_=>a[lo]!
 | n+1,lo,hi =>
   let mid :=(lo+hi)/2
   let c:=a[mid]!
   let x :=key c.B c.J
   if k=x then c else
     if k<x then search a k n lo mid else search a k n (mid+1) hi
private def lookup (B J:ℕ) :aqm :=
 let k :=key B J
 let i:=((List.range banks.size).find? (fun j=>k≤limits[j]!)).getD 0
 let a :=banks[i]!
 search a k 8 0 a.size
private theorem row (t:Bank)
  (h: (t.shape.B,t.shape.J,t.poleMoment) =
    let c:=lookup t.shape.B t.shape.J
    (c.B,c.J,c.total))
  (hn:bXa t=true) (hB:t.shape.B<K1.p) :ay t :=
 checked t _ h hn hB
local notation "r!" => row _ rfl rfl (by decide)
private theorem dg5 (b:fO) :ay (terminal b) := by
 cases b <;> exact r!
set_option maxHeartbeats 6000000 in
private theorem dfr (b:fO) :a1d (stages b) := by
 cases b <;> dsimp only [stages,P5_7_3.fO.schedule]
 all_goals
  repeat'
   apply guI
   · exact r!
   · exact r!
  exact guJ
theorem proof :P5_7_3.c1 := by
 intro b t ht
 change ay t
 rcases ht with rfl | ⟨s,hs,rfl | rfl⟩ | ⟨i,rfl⟩
 · exact dg5 b
 · exact (dfr b s hs).1
 · exact (dfr b s hs).2
 · exact dg5 b
end qpECY2d
end
section
set_option autoImplicit true
namespace qAxtVye
noncomputable section
open Polynomial
open P5 (jG p blockLength)
open P5_7 (midAgreement)
open P5_7_3 (fO stages terminal O2 prefixFee)
open Dt (Ls)
open cu (Shape vP)
open gT (Ambient)
open pI (weight)
open scoped BigOperators Classical
export TD (GM FP bCb bf7 auN arC aIe
 a3D running XM aBh)
def nV (b:fO) (i:ℕ) :Ls :=
 ((stages b)[i]?).getD ⟨0,terminal b,terminal b⟩
theorem cqz {b:fO} {i:ℕ} (hi:i<(stages b).length) :
  nV b i∈stages b:= by
 rw [nV,List.getElem?_eq_getElem hi]
 exact List.getElem_mem hi
def Fo (b:fO) :=(stages b).length - 1
abbrev RU (b:fO) :=b.schedule.RU
def azi (b:fO) (k :Fin 4) :
    List ℕ→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [],cap,old =>
    aIe cap old (nV b 0).moving.shape k +
      (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2] :Fin 4→ℕ) k
  | i :: is,cap,old =>
    let s :=nV b i
    let c:=s.free.shape
    aIe cap old c k+azi b k is
      (fun j=>min (cap j) (auN c j/(s.dI+1)))
      (fun j=>max (old j) (arC c k j))
def BC (b:fO) (k :Fin 4) :ℕ :=
 azi b k (RU b) (auN (nV b 0).free.shape) (fun _=>0)
def V8 (b:fO) :ℕ→GM
 | 0=> fun k=>BC b k
 | i+1=>bCb (V8 b i) (bf7 (nV b (i+1)).free.shape
     (nV b (i+1)).moving.shape (nV b (i+1)).dI true)
def aHp (b:fO) (i:ℕ) :Shape :=
 if i<Fo b then a3D (nV b (i+1)) else (terminal b).shape
def SS (b:fO) (bw:Fin 3) (i:ℕ) :GM :=
 fun k=>weight (aHp b i) bw k
def ash (b:fO) :ℚ :=
 XM (Fo b+1) (SS b 0) (V8 b)
def cb1 (b:fO) :ℚ :=
 FP (running (SS b 2) (Fo b+1)) (V8 b 0)
def a5z (b:fO) (a h:ℕ→ℚ) (i:ℕ) :GM :=
 fun k=>a i*SS b 0 i k+h i*SS b 1 i k
def wX (b:fO) :=131071+b.pricedHi
def gap (b:fO) :=midAgreement - wX b
def au1 (b:fO) (B J:ℕ) :ℕ :=
 let d:=wX b
 let q:=gap b
 let a :=1+(2*d-3)*(B-1)
 let v :=min a ((2*d-3)*(J-1)+d)
 let published:=((blockLength-midAgreement)*((B-J)*v+J*a)+(q-1))/q+B^2
 let lam:ℚ:=(blockLength:ℚ)/midAgreement
 let mu:ℚ:=((blockLength-d:ℕ) :ℚ)/q
 let ap:=mu+2*lam*d*(B-1 :ℕ)
 let vp:=min ap (lam*d*(2*J-1 :ℕ))
 let persistent:=(((B-J:ℕ) :ℚ)*vp+J*ap).ceil.toNat+B^2
 min published persistent
def a4f (b:fO) :ℕ :=
  let jX (s :Shape) :=au1 b s.B s.J
  ∑ i∈Finset.range (stages b).length,
    (jX (nV b i).free.shape+jX (nV b i).moving.shape)
def exitFee (b:fO) :ℕ :=
  (p+1)*BC b 2+BC b 3+BC b 0 +
    au1 b (BC b 2) (BC b 1)+a4f b +
    (p+1)*((nV b 0).free.shape.U + (nV b 0).moving.shape.U)
def agA (rows :vP) (s :Shape) (I:Ideal Ambient) :Prop :=
 ∀ P∈rows s (O2 s),gT.iJ P∈I
def axS {h rows s} (pair :P5_7_3.akE h rows s) (I:Ideal Ambient) :Prop :=
  agA rows s.free.shape I∧agA rows s.moving.shape I ∧
    aFX.aTw pair.free pair.moving I
structure am1 (hi dI:ℕ) (s :Shape) :Prop where
 ode :aBh s.B s.J
 seed_small:s.U<p
 pos :0<s.m*midAgreement
 buffer :2*hi*dI≤O2 s
structure aqE (b:fO) :Prop where
 aXU:0<(stages b).length
 zero : (nV b 0).dI=0
 bIj : ∀ i<Fo b,0<(nV b (i+1)).dI
 bN7 : ∀ i<(stages b).length,(nV b i).dI<p
 brd : ∀ i∈RU b,0< i∧i<(stages b).length
 b6r : (RU b).Pairwise (· < ·)
 aE7 : ∀ i<(stages b).length,
  let s :=nV b i
  am1 b.jX.hi s.dI s.free.shape∧am1 b.jX.hi s.dI s.moving.shape
 bxE :am1 b.jX.hi 0 (terminal b).shape
 bq6 : ∀ k,BC b k<p
 bDl: (nV b 0).free.shape.U + (nV b 0).moving.shape.U<p
 bK5:aBh (BC b 2) (BC b 1)
abbrev graphUnit :ℚ:=((p+1 :ℕ) :ℚ)
def alO (b:fO) (g:ℕ) :ℚ :=
  let d:=wX b
  (2*(g:ℚ)-1)*(1+2*((blockLength:ℚ)/midAgreement)*d) +
    ((blockLength-d:ℕ) :ℚ)/gap b
def lineUnit (b:fO) :ℚ:=1+3*(blockLength:ℚ)/gap b
def branchDegree (b:fO) (g:ℕ) :ℕ :=
 let d:=wX b
 2*g*(2*d*g*(g+1))-g*g*d
def horizontalUnit (b:fO) (g:ℕ) :ℚ :=
 let B:=branchDegree b g
 let v :=8+6*(g:ℚ)+((2*g*blockLength+2*g*(2*B-1) :ℕ) :ℚ)/gap b
 if g=2 then min v (13+8*(blockLength:ℚ)/gap b) else v
def horizontalBase (d:ℚ) (g:ℕ) :ℚ:=2*d/3+4*(g:ℚ)+8
def HorizontalBand (b:fO) :Prop :=b = .h2704∨b = .h2708
structure aSz (b:fO) (cap a h:ℚ) :Prop where
 degree :cap≤a
 nonneg:0≤a
 height:0≤h
 interpolation : ∀ g:ℕ,0<g→a<graphUnit/(g:ℚ) →
  let direct :=graphUnit/(g:ℚ)
  (direct-a)*alO b g≤direct*h ∨
  (HorizontalBand b∧g=1∧(direct-a)*lineUnit b≤direct*h) ∨
  (HorizontalBand b∧2≤g∧branchDegree b g<p ∧
    horizontalBase cap g≤a ∧
    (direct-a)*horizontalUnit b g≤(direct-horizontalBase cap g)*h)
structure Cv (b:fO) :Prop where
 seed_small:ash b<(p:ℚ)
 budget :
  ∃ (a h:ℕ→ℚ) (point loss :ℕ),
    (∀ i≤Fo b,
      aSz b (min (ash b) (FP (SS b 0 i) (V8 b i))) (a i) (h i)) ∧
    cb1 b≤(point :ℚ) ∧
    XM (Fo b+1) (a5z b a h) (V8 b)+ash b≤(loss :ℚ) ∧
    point+loss+exitFee b≤prefixFee b
open gT (abX aQ bbt aSf)
def aKd (b:fO) {u del} (M:jG u del) {Γ}
    (F:P1.bje midAgreement M Γ) :Prop :=
  ∀ T⊆Γ,∀ I g H,0<g→ g<p→bbt I g H →
    Module.finrank aQ (abX I)<p →
    (∀ γ∈T,aSf I (M.label γ) (F.scalar γ)) →
    (T.card:ℚ)≤alO b g*H+g
end
end qAxtVye
end
end
section
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨6300,8774,1832,u⟩,0x19f125fa480000,0x8fae93773c8c⟩:Dt.Bank) 3100 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s7) 3100 e ((((P5_7_3.fO.s7).schedule.gw).drop a).take 1)
theorem yQh105:gZ! 11 10:=⟨r! 168460 11 140 76 76 22 5 6 5 0x21740046bb8027bb143638cc,trivial⟩
theorem yQh106:gZ! 12 11:=⟨r! 168460 12 121 75 76 23 5 3 5 0x13580020d0a009e00686cb738,trivial⟩
theorem yQh107:gZ! 13 12:=⟨r! 168460 13 100 77 76 21 5 12 4 0x9300078c8009d2aa1b3e2e,trivial⟩
theorem yQh108:gZ! 14 13:=⟨r! 168460 14 76 77 76 21 5 10 4 0x320006e7a009c8721b4c8e,trivial⟩
theorem yQh109:gZ! 15 14:=⟨r! 168460 15 49 76 76 22 5 8 4 0x7c0032288027046436b262,trivial⟩
theorem yQh110:gZ! 16 15:=⟨r! 168460 16 20 76 76 22 5 6 4 0x2d188026ea8436ca20,trivial⟩
theorem grades3100C:GradeSigns (terminal .s7) 3100 11 (((P5_7_3.fO.s7).schedule.gw).drop 10) :=⟨yQh105.1,yQh106.1,yQh107.1,yQh108.1,yQh109.1,yQh110.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (Signs GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨5400,7521,1571,u⟩,0x10582db9780000,0x4d9c456593b2⟩:Dt.Bank) 3200 e v k l b d z n x
theorem ordinary3200:Signs (terminal .sJ) 3200 17 0 :=
 r! 110156 17 0 63 75 33 4 9 3 0x1274a8002cfb4d4d1f1d8d98c
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .sJ) 3200 e ((((P5_7_3.fO.sJ).schedule.gw).drop a).take 1)
theorem yQh111:gZ! 1 0:=⟨r! 94574 1 177 74 74 22 4 1 4 0x20006df000bb13baca24c,trivial⟩
theorem yQh112:gZ! 2 1:=⟨r! 95497 2 173 71 74 25 5 2 4 0x70000385f2005d6e5216c8648,trivial⟩
theorem yQh113:gZ! 3 2:=⟨r! 96819 3 169 70 74 26 5 3 4 0x14a4001d0a300178a1b42ee3dde,trivial⟩
theorem yQh114:gZ! 4 3:=⟨r! 98702 4 165 74 74 22 5 5 4 0x2cc001e230018045430c87c,trivial⟩
theorem yQh115:gZ! 5 4:=⟨r! 101425 5 161 76 74 20 5 6 4 0x520007ea8018f310ce3bc,trivial⟩
theorem grades3200A:GradeSigns (terminal .sJ) 3200 1 (((P5_7_3.fO.sJ).schedule.gw).take 5) :=⟨yQh111.1,yQh112.1,yQh113.1,yQh114.1,yQh115.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨5400,7521,1571,u⟩,0x10582db9780000,0x4d9c456593b2⟩:Dt.Bank) 3200 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .sJ) 3200 e ((((P5_7_3.fO.sJ).schedule.gw).drop a).take 1)
theorem yQh116:gZ! 6 5:=⟨r! 103349 6 155 72 74 24 5 8 4 0x754000802f001976012d660c2,trivial⟩
theorem yQh117:gZ! 7 6:=⟨r! 108569 7 150 76 74 20 5 11 4 0xa60008c3001bdc92ecace,trivial⟩
theorem yQh118:gZ! 8 7:=⟨r! 110156 8 143 76 74 20 5 1 5 0x8400082d801bfe54f435e,trivial⟩
theorem yQh119:gZ! 9 8:=⟨r! 110156 9 134 74 74 22 5 4 5 0x43c001c7b801b38853d38f8,trivial⟩
theorem yQh120:gZ! 10 9:=⟨r! 110156 10 124 73 74 23 5 12 4 0x12c000bfec0069d74a7ac994,trivial⟩
theorem grades3200B:GradeSigns (terminal .sJ) 3200 6 ((((P5_7_3.fO.sJ).schedule.gw).drop 5).take 5) :=⟨yQh116.1,yQh117.1,yQh118.1,yQh119.1,yQh120.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨5400,7521,1571,u⟩,0x10582db9780000,0x4d9c456593b2⟩:Dt.Bank) 3200 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .sJ) 3200 e ((((P5_7_3.fO.sJ).schedule.gw).drop a).take 1)
theorem yQh121:gZ! 11 10:=⟨r! 110156 11 113 76 74 20 5 9 4 0x4db0019b4d4f63f6,trivial⟩
theorem yQh122:gZ! 12 11:=⟨r! 110156 12 99 75 74 21 5 6 4 0x1ec800646329ed9c0,trivial⟩
theorem yQh123:gZ! 13 12:=⟨r! 110156 13 83 75 74 21 5 4 4 0x179600622429ee9e6,trivial⟩
theorem yQh124:gZ! 14 13:=⟨r! 110156 14 65 74 74 22 5 2 4 0x8ad801802853df10e,trivial⟩
theorem yQh125:gZ! 15 14:=⟨r! 110156 15 45 70 75 26 4 12 3 0x183a200bc10623e0b8f4,trivial⟩
theorem yQh126:gZ! 16 15:=⟨r! 110156 16 24 75 75 21 4 10 3 0x1f5002defd1f12b8,trivial⟩
theorem grades3200C:GradeSigns (terminal .sJ) 3200 11 (((P5_7_3.fO.sJ).schedule.gw).drop 10) :=⟨yQh121.1,yQh122.1,yQh123.1,yQh124.1,yQh125.1,yQh126.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (Signs GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨3000,4189,858,u⟩,0x2c49ea7940000,0x75c8c30a950⟩:Dt.Bank) 3400 e v k l b d z n x
theorem ordinary3400:Signs (terminal .tv) 3400 16 0 :=
 r! 50872 16 0 75 70 17 4 3 3 0x29e55182a
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tv) 3400 e ((((P5_7_3.fO.tv).schedule.gw).drop a).take 1)
theorem yQh127:gZ! 1 0:=⟨r! 46136 1 134 71 70 20 4 7 3 0x100a0195ae8dd578,trivial⟩
theorem yQh128:gZ! 2 1:=⟨r! 46966 2 131 72 70 19 4 8 3 0x23d006751572dd8,trivial⟩
theorem yQh129:gZ! 3 2:=⟨r! 47535 3 127 71 70 20 4 9 3 0x1334019f6aaebc2e,trivial⟩
theorem yQh130:gZ! 4 3:=⟨r! 48497 4 123 70 70 21 4 10 3 0xa65806a4395eb95a,trivial⟩
theorem yQh131:gZ! 5 4:=⟨r! 50122 5 119 71 70 21 4 11 3 0x5be0037f81506dba,trivial⟩
theorem yQh132:gZ! 6 5:=⟨r! 50872 6 114 71 70 21 4 12 3 0x57680384d550f8f8,trivial⟩
theorem yQh133:gZ! 7 6:=⟨r! 50872 7 108 69 70 23 4 2 4 0x124880369f154427c6,trivial⟩
theorem grades3400A:GradeSigns (terminal .tv) 3400 1 (((P5_7_3.fO.tv).schedule.gw).take 7) :=⟨yQh127.1,yQh128.1,yQh129.1,yQh130.1,yQh131.1,yQh132.1,yQh133.1,trivial⟩
end qHo4MUb
end
section
set_option autoImplicit true
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace qHo4MUb
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped qqf9uAa
set_option quotPrecheck false in
local notation "r!" u:arg e:arg v:arg k:arg l:arg b:arg d:arg z:arg n:arg x:arg =>
 pack! (⟨⟨3000,4189,858,u⟩,0x2c49ea7940000,0x75c8c30a950⟩:Dt.Bank) 3400 e v k l b d z n x
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .tv) 3400 e ((((P5_7_3.fO.tv).schedule.gw).drop a).take 1)
theorem yQh134:gZ! 8 7:=⟨r! 50872 8 102 71 70 21 4 3 4 0x37c0034d09511ccc,trivial⟩
theorem yQh135:gZ! 9 8:=⟨r! 50872 9 94 71 70 21 4 1 4 0x27d003342d512d36,trivial⟩
theorem yQh136:gZ! 10 9:=⟨r! 50872 10 84 71 70 21 4 11 3 0x19f8031e1d513bae,trivial⟩
theorem yQh137:gZ! 11 10:=⟨r! 50872 11 72 69 70 23 4 9 3 0x3b88030a0654521da,trivial⟩
theorem yQh138:gZ! 12 11:=⟨r! 50872 12 59 71 70 21 4 7 3 0x6e002f5295154ec,trivial⟩
theorem yQh139:gZ! 13 12:=⟨r! 50872 13 44 71 70 21 4 6 3 0x23002e1c9515fca,trivial⟩
theorem yQh140:gZ! 14 13:=⟨r! 50872 14 27 71 70 21 4 5 3 0x4002cfc1516948,trivial⟩
theorem yQh141:gZ! 15 14:=⟨r! 50872 15 8 70 70 22 4 4 3 0xafcf2a2e32c,trivial⟩
theorem grades3400B:GradeSigns (terminal .tv) 3400 8 (((P5_7_3.fO.tv).schedule.gw).drop 7) :=⟨yQh134.1,yQh135.1,yQh136.1,yQh137.1,yQh138.1,yQh139.1,yQh140.1,yQh141.1,trivial⟩
end qHo4MUb
end
end
section
section
set_option autoImplicit true
set_option maxRecDepth 4096
namespace qMNQHHc
open Finset qlc9qed q7IA62d
theorem ambient_eq (b:Bank) (h t:ℕ) :
  Aw b h t=q7IA62d.Aw h (qPQ4nYa.top b) t:= by
 have hU:b.U≤70000:= by cases b <;> decide
 ext F
 rw [qlc9qed.mem_ambient,q7IA62d.mem_ambient]
 exact ⟨fun ⟨⟨a1,a2,a3,_⟩,a4,a5⟩=>⟨a1,a2,a3,a4,a5⟩,
  fun ⟨a1,a2,a3,a4,a5⟩=>⟨⟨a1,a2,a3,a4.trans hU⟩,a4,a5⟩⟩
end qMNQHHc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qbIP9ia
noncomputable section
open Polynomial Finset
open cu (L)
open qHEUR1a (Raw)
open private expand coeff_expand weights c0Q bg6 from ProximityPrize.SubmissionLower.BJ
abbrev Vars :=Option (Fin 2 ⊕ Unit)
abbrev Exps :=Vars →₀ ℕ
abbrev Flat :=MvPolynomial Vars L
abbrev amm:Vars :=some (.inr ())
abbrev seed (i:Fin 2) :Vars :=some (.inl i)
abbrev flatten:Raw ≃+* Flat :=expand
def exps (j k :ℕ) (m:Fin 2 →₀ ℕ) :Exps :=
 (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m,Finsupp.single () k)).optionElim j
@[simp] theorem exps_y (j k :ℕ) (m:Fin 2 →₀ ℕ) :exps j k m none=j :=
  Finsupp.optionElim_apply_none ..
@[simp] theorem exps_x (j k :ℕ) (m:Fin 2 →₀ ℕ) :exps j k m amm=k := by
  simp [exps]
@[simp] theorem exps_s (j k :ℕ) (m:Fin 2 →₀ ℕ) (i:Fin 2) :exps j k m (seed i)=m i:= by
  simp [exps]
theorem flat_coeff (F:Raw) (j k :ℕ) (m:Fin 2 →₀ ℕ) :
  (flatten F).coeff (exps j k m)=((F.coeff j).coeff m).coeff k := by
 rw [coeff_expand,exps_y]
 simp [exps]
abbrev ao8 (m:Exps) :Fin 2 →₀ ℕ :=
 (Finsupp.sumFinsuppAddEquivProdFinsupp m.some).1
theorem flat_coeff' (F:Raw) (m:Exps) :
  (flatten F).coeff m=((F.coeff (m none)).coeff (ao8 m)).coeff (m amm) := by
 rw [coeff_expand]
 rfl
@[simp] theorem rawSeed_apply (m:Exps) (i:Fin 2) :ao8 m i=m (seed i) :=rfl
theorem flatten_X :
   flatten (Y3.aka (Polynomial.X:L[X]))=MvPolynomial.X amm:= by
 apply flatten.symm.injective
 rw [RingEquiv.symm_apply_apply]
 change _=(MvPolynomial.optionEquivLeft L (Fin 2 ⊕ Unit) (MvPolynomial.X amm)).map
   bg6.toRingHom
 rw [MvPolynomial.optionEquivLeft_X_some,Polynomial.map_C]
 change _=C (MvPolynomial.map (MvPolynomial.uniqueAlgEquiv L Unit).toRingHom
     (MvPolynomial.sumRingEquiv L (Fin 2) Unit (MvPolynomial.X (.inr ()))))
 rw [MvPolynomial.sumRingEquiv_X_inr,MvPolynomial.map_C]
 simp [Y3.aka]
abbrev wt (d:ℕ) (P:Flat) :ℕ:=P.weightedTotalDegree (weights d)
theorem wt_term (d:ℕ) {P:Flat} {m:Exps} (hm:m∈P.support) :
  m amm+m none*d≤wt d P:= by
 rw [← c0Q]
 exact MvPolynomial.le_weightedTotalDegree _ hm
theorem wt_le {P:Flat} {d n:ℕ}
  (h : ∀ m∈P.support,m amm+m none*d≤n) :wt d P≤n :=
 Finset.sup_le fun m hm=> by rw [c0Q]; exact h m hm
def seedMon (a b:ℕ) :Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![a,b]
@[simp] theorem seedMon_zero (a b:ℕ) :seedMon a b 0=a :=rfl
@[simp] theorem seedMon_one (a b:ℕ) :seedMon a b 1=b:=rfl
theorem exps_eta (m:Exps) :
   exps (m none) (m amm) (seedMon (m (seed 0)) (m (seed 1)))=m:= by
 ext t
 rcases t with _ | (_ | ⟨⟩)
 · simp
 · rename_i i
   fin_cases i <;> simp [seed]
 · simp [← show amm=some (.inr ()) from rfl]
abbrev Idx (n a b:ℕ) (w:ℕ→ℕ) :=(Σ j:Fin n,Fin (w j))×Fin (a+1)×Fin (b+1)
def coord {n a b:ℕ} {w:ℕ→ℕ} (t:Idx n a b w) :Exps :=
 exps t.1.1 t.1.2 (seedMon t.2.1 t.2.2)
theorem coord_inj {n a b:ℕ} {w:ℕ→ℕ} :
  Function.Injective (@coord n a b w) := by
 intro t u h
 have hy :=congrArg (fun m:Exps=>m none) h
 have hx :=congrArg (fun m:Exps=>m amm) h
 have ha :=congrArg (fun m:Exps=>m (seed 0)) h
 have hb:=congrArg (fun m:Exps=>m (seed 1)) h
 simp only [coord,exps_y,exps_x,exps_s,seedMon_zero,seedMon_one] at hy hx ha hb
 have he :t.1.1=u.1.1 :=Fin.ext hy
 exact Prod.ext (Sigma.ext he ((Fin.heq_ext_iff (congrArg (fun j:Fin n=>w j) he)).2 hx))
  (Prod.ext (Fin.ext ha) (Fin.ext hb))
theorem mem_coord {n a b:ℕ} {w:ℕ→ℕ} {m:Exps} :
   m∈Set.range (@coord n a b w) ↔
     m none<n∧m amm<w (m none)∧m (seed 0)≤a∧m (seed 1)≤b:= by
 constructor
 · rintro ⟨t,rfl⟩
   simpa only [coord,exps_y,exps_x,exps_s,seedMon_zero,seedMon_one] using
     ⟨t.1.1.isLt,t.1.2.isLt,Nat.le_of_lt_succ t.2.1.isLt,Nat.le_of_lt_succ t.2.2.isLt⟩
 · rintro ⟨hy,hx,ha,hb⟩
   exact ⟨⟨⟨⟨m none,hy⟩,⟨m amm,hx⟩⟩,⟨m (seed 0),Nat.lt_succ_of_le ha⟩,
     ⟨m (seed 1),Nat.lt_succ_of_le hb⟩⟩,exps_eta m⟩
def rows {n a b:ℕ} {w:ℕ→ℕ} : (Idx n a b w →₀ L) →ₗ[L] Flat :=
 (AddMonoidAlgebra.coeffLinearEquiv L).symm.toLinearMap.comp (Finsupp.lmapDomain L L coord)
theorem rows_inj {n a b:ℕ} {w:ℕ→ℕ} :
   Function.Injective (@rows n a b w) :=
 (AddMonoidAlgebra.coeffLinearEquiv L).symm.injective.comp (Finsupp.mapDomain_injective coord_inj)
theorem rows_support {n a b:ℕ} {w:ℕ→ℕ} (h:Idx n a b w →₀ L) {m:Exps}
  (hm:m∈(rows h).support) :m∈Set.range (@coord n a b w) := by
 change m∈(Finsupp.mapDomain (@coord n a b w) h).support at hm
 rw [Finsupp.mapDomain_support_of_injective coord_inj,Finset.mem_image] at hm
 obtain ⟨t,_,ht⟩:=hm
 exact ⟨t,ht⟩
theorem rows_range {n a b:ℕ} {w:ℕ→ℕ} {P:Flat}
  (h : ∀ m∈P.support,m∈Set.range (@coord n a b w)) :
  P∈(@rows n a b w).range := by
 obtain ⟨q,hq⟩:=(Finsupp.mem_range_mapDomain_iff (@coord n a b w) coord_inj
  (AddMonoidAlgebra.coeffLinearEquiv L P)).mpr (fun m hm =>
    MvPolynomial.notMem_support_iff.mp (fun hp=>hm (h m hp)))
 exact ⟨q,(AddMonoidAlgebra.coeffLinearEquiv L).injective (by simpa [rows] using hq)⟩
theorem idx_card (n a b:ℕ) (w:ℕ→ℕ) :
  Fintype.card (Idx n a b w)=(∑ j:Fin n,w j)*(a+1)*(b+1) := by
 rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_sigma]
 simp only [Fintype.card_fin,Nat.mul_assoc]
def rem (M:ℕ) :Flat →ₗ[L] Flat where
  toFun P:=P.modMonomial (Finsupp.single amm M)
  map_add' P Q:= by
    ext m
    by_cases hm:Finsupp.single amm M≤ m <;>
     simp [MvPolynomial.coeff_modMonomial_of_le,MvPolynomial.coeff_modMonomial_of_not_le,hm]
  map_smul' c P:= by
    ext m
    by_cases hm:Finsupp.single amm M≤ m <;>
     simp [MvPolynomial.coeff_modMonomial_of_le,MvPolynomial.coeff_modMonomial_of_not_le,hm]
theorem rem_support {M:ℕ} {P:Flat} {m:Exps} (hm:m∈(rem M P).support) :
    m∈P.support∧m amm<M:= by
  by_cases h:M≤ m amm
  · exact (MvPolynomial.mem_support_iff.mp hm (MvPolynomial.coeff_modMonomial_of_le _
      (Finsupp.single_le_iff.mpr h))).elim
  · exact ⟨MvPolynomial.mem_support_iff.mpr (by
      simpa only [rem,LinearMap.coe_mk,AddHom.coe_mk,
        MvPolynomial.coeff_modMonomial_of_not_le _ (Finsupp.single_le_iff.not.mpr h)]
        using MvPolynomial.mem_support_iff.mp hm),Nat.lt_of_not_ge h⟩
theorem rem_eq (M:ℕ) (P:Flat) :
  P=rem M P+MvPolynomial.X amm^M*P.divMonomial (Finsupp.single amm M) := by
 rw [MvPolynomial.X_pow_eq_monomial]
 exact (MvPolynomial.modMonomial_add_divMonomial ..).symm
end
end qbIP9ia
end
end
