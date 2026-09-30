import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R150
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨17,18,4257,4372,1424574087666458⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2359261 6293400 := wide_block_sound band profiles 2359261 6293400 (wideData 1 0x2082982082999b15a7200c823e70) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 17)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 17≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤18)
    (hT0 : 4257≤T) (hT1 : T≤4372) (hnu : 2359261≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1424574087666458 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R150

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R151
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,18,3938,4249,726207447517077⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2359260 6474645 := wide_block_sound band profiles 2359260 6474645 (wideData 3 0x13c672003f72f7a0000000005f83ec001fb9bbc0820a80820a8068d12ff0006bb9b34) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤18)
    (hT0 : 3938≤T) (hT1 : T≤4249) (hnu : 2359260≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤726207447517077 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R151

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R152
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,19,3806,4199,1445814988581091⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2490331 6655890 := wide_block_sound band profiles 2490331 6655890 (wideData 1 0xaa0aa0aa0aa0aa0aa0b7e13ee600cda7e64) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 3806≤T) (hT1 : T≤4199) (hnu : 2490331≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1445814988581091 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R152

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R153
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,19,4200,4250,1462590739470564⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2490331 6655890 := wide_block_sound band profiles 2490331 6655890 (wideData 1 0x2082a82082a8b9159e600cda7e64) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 4200≤T) (hT1 : T≤4250) (hnu : 2490331≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1462590739470564 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R153

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R154
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨19,19,3536,3730,5361476641883917⟩
private def profiles : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2490330 6837135 := wide_block_sound band profiles 2490330 6837135 (wideData 1 0xac0ac0ac0ac0ac0ac07da1edbc00d869e3e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 19)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 19≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 3536≤T) (hT1 : T≤3730) (hnu : 2490330≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤5361476641883917 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R154

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R155
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨19,20,3423,3529,8208778260150074⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨27543,195,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 2621401 7018380 := wide_block_sound band profiles 2621401 7018380 (wideData 16 0x2080082013917d32c800a38be000000000069fe44ed8e80028e2f80000000001abe813d39b000a38be000000000724e148add800a38e0082002080360a0dfb5c000a38be0000000007a4c0debad000a38e00000000007bdb0e879d000a38be00000000006082c3ad96c0028e3802080082007a4b8b08800a38be0000000005fea0b87a9800a38be00000000063cc0bb7be800a38be2cb00b2c0522c282e0a33c820a38e00000000007e0062cae088b2bf00000000008e00001871bee0ac0ac002b02b0070bb800a38bee82082b82082b96b128220099a5ee4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 19)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 19≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤20)
    (hT0 : 3423≤T) (hT1 : T≤3529) (hnu : 2621401≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤8208778260150074 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R155
