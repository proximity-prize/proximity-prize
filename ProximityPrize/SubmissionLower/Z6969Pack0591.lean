import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- Source: Research6969.PrefixNearLight
section Z6969Source0692
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2_2 (Active mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Prefix6969Main (Band)
open Research6969 Research6966
open scoped Classical BigOperators

abbrev ordinaryNearFee : ℕ := 234329630343844473
abbrev ordinaryNearOrd : ℕ := 133994566145700
abbrev ordinaryNearSeed : ℕ := 1590006772040

/-- A low-weight quadratic uses its verified light primary source and pays
all original helper zeros directly before the ordinary near terminal count. -/
theorem light_packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (slope : G.natDegree=1) (quad : jetDegree G=2) (i : Fin 56)
    (positive : 1≤seedDegree G) (width : seedDegree G≤seed i)
    (low : RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw<threshold i) :
    Nonempty (Packet F Crt ordinaryNearFee ordinaryNearOrd ordinaryNearSeed 351 6143) := by
  have prime := Prefix6969MiddleTransfer.prime_of_irred known.1
  have lower := HelperWeightCap.weight_lower phys prime.ne_zero (131071-M.overhead.toNat) (by omega)
  rw [quad,slope] at lower
  have floor : 257319≤RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw := by omega
  obtain ⟨R,J,C,A,same,pay,ms,mg,mo,covered⟩ := Prefix6969Main.main_prefix F Crt
    Prefix6969MainCases.NearLight0.plan Prefix6969MainCases.NearLight0.valid Band.near
    Prefix6969MainCases.NearLight0.price Prefix6969MainCases.NearLight0.priced
    Prefix6969MainCases.NearLight0.sources (by decide) lo hi noPole residues phys known quad.ge positive floor
  let T := Γ.filter (fun γ=>jetAt G (M.label γ) (F.scalar γ)=0)
  have lowPay : T.card≤lowFee :=
    low_quadratic_count F (filter_subset _ _) lo hi noPole
      (fun γ h=>residues γ (mem_filter.mp h).1) phys prime slope quad i width low
      (fun _ h=>(mem_filter.mp h).2)
  have ma (P) (h:P∈J.final) : Active P := (J.kept_geom (mem_filter.mp h).1).1
  obtain ⟨f,project⟩:=JointProjection.exists_product A (fun q h=>(mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md : mass J.final 0≤335 := by
    have q := ms 0
    change (mass J.final 0:ℚ)≤459151/1369 at q
    apply Nat.le_of_lt_succ
    exact_mod_cast q.trans_lt (by decide +kernel : (459151:ℚ)/1369<336)
  have mv : mass J.final 1≤5620 := by
    have q := ms 1
    change (mass J.final 1:ℚ)≤30778769/5476 at q
    apply Nat.le_of_lt_succ
    exact_mod_cast q.trans_lt (by decide +kernel : (30778769:ℚ)/5476<5621)
  let price := Prefix6969MainCases.NearLight0.price
  let extra := (ordinaryNearOrd-price.retainedCredit 0)*335+(ordinaryNearSeed-price.retainedCredit 1)*5620
  have adj : ordinaryNearOrd*f.natDegree+ordinaryNearSeed*K1_14_4.seedDegree f≤
      price.charge J.final+extra := by
    have p0:=Nat.mul_le_mul_left ordinaryNearOrd measures.1
    have p1:=Nat.mul_le_mul_left ordinaryNearSeed measures.2
    have q0 := compensate ordinaryNearOrd (price.retainedCredit 0) (mass J.final 0) 335 md
    have q1 := compensate ordinaryNearSeed (price.retainedCredit 1) (mass J.final 1) 5620 mv
    unfold Prefix6969Main.Pricing.charge extra
    simp only [Fin.sum_univ_four]
    omega
  have bill : price.fee+extra+lowFee≤ordinaryNearFee := by decide +kernel
  change C.paid.card+price.charge J.final≤price.fee at pay
  refine ⟨⟨C.paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans (by decide),(measures.2.trans mv).trans (by decide),?_,?_⟩⟩
  · have union:=card_union_le C.paid T
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨hγ,root⟩))
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ,by simpa only [same] using root⟩
      rcases covered γ inMain with p|on
      · exact Or.inl (mem_union_left _ p)
      · exact Or.inr on

end
end Lower6960.Prefix6969Early
end Z6969Source0692

-- Source: Research6969.PhysicalChecks087
section Z6969Source0693
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1173 : Request := ⟨⟨⟨556,772,170,5648⟩,5255817068544,9968090926⟩,10,3,2,433856,34⟩
theorem cover1173 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1173) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1174 : Request := ⟨⟨⟨556,772,170,5725⟩,5255817068544,9968090926⟩,10,3,2,434049,33⟩
theorem cover1174 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1174) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1175 : Request := ⟨⟨⟨556,772,170,5803⟩,5255817068544,9968090926⟩,10,3,2,434235,32⟩
theorem cover1175 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1175) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1176 : Request := ⟨⟨⟨556,772,170,5882⟩,5255817068544,9968090926⟩,10,3,2,434416,31⟩
theorem cover1176 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1176) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1177 : Request := ⟨⟨⟨556,772,170,5963⟩,5255817068544,9968090926⟩,10,3,2,434591,30⟩
theorem cover1177 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1177) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1178 : Request := ⟨⟨⟨556,772,170,6045⟩,5255817068544,9968090926⟩,10,3,2,434759,29⟩
theorem cover1178 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1178) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1179 : Request := ⟨⟨⟨556,772,170,6129⟩,5255817068544,9968090926⟩,10,3,2,434922,28⟩
theorem cover1179 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1179) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1180 : Request := ⟨⟨⟨556,772,170,6214⟩,5255817068544,9968090926⟩,10,3,2,435079,27⟩
theorem cover1180 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1180) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1181 : Request := ⟨⟨⟨556,772,170,6301⟩,5255817068544,9968090926⟩,10,3,2,435230,26⟩
theorem cover1181 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1181) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1182 : Request := ⟨⟨⟨556,772,170,6389⟩,5255817068544,9968090926⟩,10,3,2,435375,25⟩
theorem cover1182 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1182) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1183 : Request := ⟨⟨⟨556,772,170,6477⟩,5255817068544,9968090926⟩,10,3,2,435514,24⟩
theorem cover1183 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1183) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1184 : Request := ⟨⟨⟨556,772,170,6567⟩,5255817068544,9968090926⟩,10,3,2,435648,23⟩
theorem cover1184 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1184) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1185 : Request := ⟨⟨⟨556,772,170,6658⟩,5255817068544,9968090926⟩,10,3,2,435775,22⟩
theorem cover1185 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1185) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1186 : Request := ⟨⟨⟨556,772,170,6751⟩,5255817068544,9968090926⟩,10,3,2,435896,21⟩
theorem cover1186 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1186) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1187 : Request := ⟨⟨⟨556,772,170,6844⟩,5255817068544,9968090926⟩,10,3,2,436012,20⟩
theorem cover1187 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1187) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1188 : Request := ⟨⟨⟨556,772,170,6939⟩,5255817068544,9968090926⟩,10,3,2,436121,19⟩
theorem cover1188 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1188) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0693

-- Source: Research6969.PrefixMainDataQuadraticSingletons0
section Z6969Source0694
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuadraticSingletons0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank30 1953, bank40 2218, bank49 2815, bank58 2557, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank126 26574, bank153 6368, bank199 9241, bank186 46700, bank176 98699, bank170 227095, bank212 10770] i
  head := src1187
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 165763, 768018, 3712793],
    ![12303, 130616, 590614, 2778664],
    ![53398/9, 566116/9, 590614, 2778664],
    ![29433/8, 37922, 2746672/9, 12579272/9],
    ![63824/25, 653678/25, 408177/2, 3814209/4],
    ![72196/49, 739792/49, 3334324/25, 15179992/25],
    ![40539/50, 441173/50, 188605/2, 7924225/16],
    ![95180/121, 83070/11, 4109332/49, 17500108/49],
    ![95180/121, 83070/11, 1336459/18, 12837889/36],
    ![63754/121, 3082616/441, 543881/8, 12837889/36],
    ![63754/121, 3082616/441, 543881/8, 10582009/36],
    ![63754/121, 753076/121, 252225/4, 3230368/15],
    ![1355575/3362, 753076/121, 252225/4, 3230368/15],
    ![1355575/3362, 9093664/1681, 2448496/49, 6011392/29],
    ![1355575/3362, 6632380/1323, 9952912/225, 126490808/675],
    ![481425/1369, 6632380/1323, 9952912/225, 126490808/675],
    ![466774/1369, 6632380/1323, 9952912/225, 126490808/675],
    ![920087/2738, 6632380/1323, 9952912/225, 126490808/675],
    ![920087/2738, 6641474/1369, 219708/5, 4639716/25]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 19 307353 := by
  refine ⟨?_, rank154 6844, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1187⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free30_0
    · exact free40_0
    · exact free49_0
    · exact free58_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free126_0
    · exact free153_0
    · exact free199_0
    · exact free186_0
    · exact free176_0
    · exact free170_0
    · exact free212_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [333197174, 332700328, 331974128, 332068544, 331551260, 331747343, 331972242, 146240031, 146597514, 146789285, 146522942, 73032174, 73063202, 87065647, 101033294, 108473872, 151195476, 101057369, 233857807], [1033540, 1034902, 1036892, 1036633, 1038051, 1037514, 1036897, 2633709, 2625870, 2621664, 2627505, 5486330, 5483864, 4564307, 3911904, 3631798, 2547563, 3910888, 1581264],
  ![124136401111740, 1607170869308, 210472026300, 4654567020], 181571188063194285⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,8,8,8,8,15,15,12,11,10,7,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 6641474/1369, 219708/5, 4639716/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuadraticSingletons0
end Z6969Source0694

-- Source: Research6969.TransitionBankChecks12
section Z6969Source0695
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole216 : momentEstimate 1342 302 = 92143933560 := by
  refine moment_from_blocks [(128,446037280),(128,2809498912),(128,6686281749),(128,10268005824),(128,12596286912),(128,13653693888),(128,13440226752),(128,11955885504),(128,9302805070),(128,6224371457),(128,3385461417),(128,1234036000),(108,141342795)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank216 (u : ℕ) : P3_7_1.BankOK (bank216 u) :=
  P3_7_1.checked (bank216 u) (m:=967) (B:=1342) (J:=302) (N:=27995979907072) (M:=92143933560) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole216
theorem free216_0 : TransitionSources.Free 2314 76 (bank216 10294) := by
  have left : TransitionArithmetic.value (TransitionSources.request 76 (bank216 10294)) 2314 = 12958766186258880 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 76 (bank216 10294)) 2315 = 22379919391783440 := by decide +kernel
  refine ⟨rank216 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free216_1 : TransitionSources.Free 2412 76 (bank216 8567) := by
  have left : TransitionArithmetic.value (TransitionSources.request 76 (bank216 8567)) 2412 = 9664011457230816 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 76 (bank216 8567)) 2413 = 15924736389244032 := by decide +kernel
  refine ⟨rank216 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole217 : momentEstimate 1393 307 = 105228376929 := by
  refine moment_from_blocks [(128,464283040),(128,2935535008),(128,7038751247),(128,10942417024),(128,13579094144),(128,14923925632),(128,14976911488),(128,13738051712),(128,11228222098),(128,7969756705),(128,4783547427),(128,2150485312),(128,491353408),(36,6042684)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank217 (u : ℕ) : P3_7_1.BankOK (bank217 u) :=
  P3_7_1.checked (bank217 u) (m:=1000) (B:=1393) (J:=307) (N:=30557599170560) (M:=105228376929) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole217
private theorem pole218 : momentEstimate 1394 307 = 105471636407 := by
  refine moment_from_blocks [(128,464640800),(128,2938006304),(128,7045357155),(128,10954047104),(128,13595770496),(128,14945648256),(128,15003680384),(128,13769866880),(128,11264153312),(128,8003279200),(128,4811016291),(128,2169498416),(128,500129584),(37,6542225)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank218 (u : ℕ) : P3_7_1.BankOK (bank218 u) :=
  P3_7_1.checked (bank218 u) (m:=1000) (B:=1394) (J:=307) (N:=30557599170560) (M:=105471636407) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole218
private theorem pole219 : momentEstimate 1394 315 = 107596110457 := by
  refine moment_from_blocks [(128,464640800),(128,2938006304),(128,7067437381),(128,11085431680),(128,13816480640),(128,15222129536),(128,15302378368),(128,14057227136),(128,11514622025),(128,8231264845),(128,5004898348),(128,2309979504),(128,570114416),(45,11499474)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank219 (u : ℕ) : P3_7_1.BankOK (bank219 u) :=
  P3_7_1.checked (bank219 u) (m:=1000) (B:=1394) (J:=315) (N:=31157463285760) (M:=107596110457) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole219
private theorem pole220 : momentEstimate 1395 296 = 102755930405 := by
  refine moment_from_blocks [(128,464998560),(128,2940477600),(128,7013010006),(128,10772156736),(128,13297635648),(128,14577406272),(128,14611468608),(128,13399822656),(128,10953459983),(128,7725823135),(128,4576053612),(128,2001051744),(128,419903584),(27,2662261)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank220 (u : ℕ) : P3_7_1.BankOK (bank220 u) :=
  P3_7_1.checked (bank220 u) (m:=1000) (B:=1395) (J:=296) (N:=29722184515584) (M:=102755930405) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole220
private theorem pole221 : momentEstimate 1395 301 = 104105680031 := by
  refine moment_from_blocks [(128,464998560),(128,2940477600),(128,7032021491),(128,10861939776),(128,13442305088),(128,14755990592),(128,14802996288),(128,13583322176),(128,11111265212),(128,7866761745),(128,4694678983),(128,2085368160),(128,459235680),(32,4318680)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank221 (u : ℕ) : P3_7_1.BankOK (bank221 u) :=
  P3_7_1.checked (bank221 u) (m:=1000) (B:=1395) (J:=301) (N:=30103476895744) (M:=104105680031) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole221
private theorem pole222 : momentEstimate 1395 307 = 105715278267 := by
  refine moment_from_blocks [(128,464998560),(128,2940477600),(128,7051963063),(128,10965677184),(128,13612446848),(128,14967370880),(128,15030449280),(128,13801682048),(128,11300112840),(128,8036869508),(128,4838563497),(128,2188602704),(128,508995920),(38,7068335)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank222 (u : ℕ) : P3_7_1.BankOK (bank222 u) :=
  P3_7_1.checked (bank222 u) (m:=1000) (B:=1395) (J:=307) (N:=30557599170560) (M:=105715278267) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole222
private theorem pole223 : momentEstimate 1395 315 = 107844841957 := by
  refine moment_from_blocks [(128,464998560),(128,2940477600),(128,7074064625),(128,11097202048),(128,13833428352),(128,15244254592),(128,15329680768),(128,14089706880),(128,11551150857),(128,8265304097),(128,5032970444),(128,2329693200),(128,579647504),(46,12262430)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank223 (u : ℕ) : P3_7_1.BankOK (bank223 u) :=
  P3_7_1.checked (bank223 u) (m:=1000) (B:=1395) (J:=315) (N:=31157463285760) (M:=107844841957) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole223
private theorem pole224 : momentEstimate 1673 368 = 218387554859 := by
  refine moment_from_blocks [(128,564455840),(128,3627497888),(128,8987090372),(128,15245521344),(128,20281586112),(128,23769952704),(128,25710621120),(128,26103591360),(128,24948863424),(128,22246437312),(128,18093377494),(128,13327613011),(128,8716872445),(128,4724664011),(128,1791740944),(121,247669478)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank224 (u : ℕ) : P3_7_1.BankOK (bank224 u) :=
  P3_7_1.checked (bank224 u) (m:=1200) (B:=1673) (J:=368) (N:=52718727069696) (M:=218387554859) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole224
private theorem pole225 : momentEstimate 1673 378 = 222977190790 := by
  refine moment_from_blocks [(128,564455840),(128,3627497888),(128,8987924767),(128,15361421824),(128,20565012992),(128,24178962944),(128,26203271680),(128,26637939200),(128,25482965504),(128,22738350592),(128,18530992161),(128,13734323180),(128,9072482073),(128,5004959240),(128,1974124832),(128,312494368),(3,11705)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank225 (u : ℕ) : P3_7_1.BankOK (bank225 u) :=
  P3_7_1.checked (bank225 u) (m:=1200) (B:=1673) (J:=378) (N:=53798525730816) (M:=222977190790) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole225
private theorem pole226 : momentEstimate 1674 355 = 212765123946 := by
  refine moment_from_blocks [(128,564813600),(128,3629969184),(128,8989383071),(128,15083748480),(128,19910311040),(128,23243701376),(128,25083919488),(128,25430965376),(128,24284839040),(128,21645540480),(128,17576530568),(128,12851308604),(128,8302054396),(128,4400417393),(128,1585099888),(109,182521962)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank226 (u : ℕ) : P3_7_1.BankOK (bank226 u) :=
  P3_7_1.checked (bank226 u) (m:=1200) (B:=1674) (J:=355) (N:=51296765214720) (M:=212765123946) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole226
private theorem pole227 : momentEstimate 1674 361 = 215563369662 := by
  refine moment_from_blocks [(128,564813600),(128,3629969184),(128,8992028326),(128,15167475648),(128,20093177792),(128,23500541888),(128,25389567936),(128,25760255936),(128,24612605888),(128,21946617792),(128,17838997106),(128,13092415058),(128,8511053404),(128,4562861232),(128,1687458624),(115,213530248)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank227 (u : ℕ) : P3_7_1.BankOK (bank227 u) :=
  P3_7_1.checked (bank227 u) (m:=1200) (B:=1674) (J:=361) (N:=51955677528064) (M:=215563369662) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole227
private theorem pole228 : momentEstimate 1674 368 = 218807905514 := by
  refine moment_from_blocks [(128,564813600),(128,3629969184),(128,8993771676),(128,15258014208),(128,20300124672),(128,23794536960),(128,25741251072),(128,26140267008),(128,24991584768),(128,22295204352),(128,18145396182),(128,13375411937),(128,8757351895),(128,4755571328),(128,1810768496),(122,253868176)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank228 (u : ℕ) : P3_7_1.BankOK (bank228 u) :=
  P3_7_1.checked (bank228 u) (m:=1200) (B:=1674) (J:=368) (N:=52718727069696) (M:=218807905514) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole228
private theorem pole229 : momentEstimate 1674 378 = 223406703910 := by
  refine moment_from_blocks [(128,564813600),(128,3629969184),(128,8994606716),(128,15374010688),(128,20583811392),(128,24203970880),(128,26234489152),(128,26675366208),(128,25526602048),(128,22788196672),(128,18583713389),(128,13782803521),(128,9113735745),(128,5036757130),(128,1994116768),(128,319719072),(4,21745)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank229 (u : ℕ) : P3_7_1.BankOK (bank229 u) :=
  P3_7_1.checked (bank229 u) (m:=1200) (B:=1674) (J:=378) (N:=53798525730816) (M:=223406703910) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole229
private theorem pole230 : momentEstimate 1749 391 = 264101254943 := by
  refine moment_from_blocks [(128,591645600),(128,3815316384),(128,9495800736),(128,16453501778),(128,22365362432),(128,26633132288),(128,29256734976),(128,30236170496),(128,29571438848),(128,27262540032),(128,23320442490),(128,18251597211),(128,13023741983),(128,8179577089),(128,4153183680),(128,1374848448),(92,116220472)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank230 (u : ℕ) : P3_7_1.BankOK (bank230 u) :=
  P3_7_1.checked (bank230 u) (m:=1258) (B:=1749) (J:=391) (N:=61347730554880) (M:=264101254943) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole230
theorem free230_0 : TransitionSources.Free 2314 105 (bank230 14067) := by
  have left : TransitionArithmetic.value (TransitionSources.request 105 (bank230 14067)) 2314 = 45886384533355592 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 105 (bank230 14067)) 2315 = 84173584451305824 := by decide +kernel
  refine ⟨rank230 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free230_1 : TransitionSources.Free 2412 105 (bank230 11634) := by
  have left : TransitionArithmetic.value (TransitionSources.request 105 (bank230 11634)) 2412 = 34524736892542000 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 105 (bank230 11634)) 2413 = 59651505993466790 := by decide +kernel
  refine ⟨rank230 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole231 : momentEstimate 2021 445 = 465028319332 := by
  refine moment_from_blocks [(128,688956320),(128,4487508896),(128,11313300384),(128,20284534871),(128,29134389824),(128,36174938688),(128,41344827968),(128,44644057664),(128,46072627776),(128,45630538304),(128,43317789248),(128,39134380608),(128,33151269675),(128,26239892982),(128,19309058981),(128,12868494373),(128,7339460368),(128,3183651600),(128,701173520),(34,7467282)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank231 (u : ℕ) : P3_7_1.BankOK (bank231 u) :=
  P3_7_1.checked (bank231 u) (m:=1450) (B:=2021) (J:=445) (N:=92998964346880) (M:=465028319332) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole231
private theorem pole232 : momentEstimate 2022 436 = 458421718666 := by
  refine moment_from_blocks [(128,689314080),(128,4489980192),(128,11319982368),(128,20262131315),(128,28930378880),(128,35803794560),(128,40844299392),(128,44051893376),(128,45426576512),(128,44968348800),(128,42677210240),(128,38553160832),(128,32646039398),(128,25765049770),(128,18873931415),(128,12490700744),(128,7039368432),(128,2978447600),(128,607634672),(26,3476088)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank232 (u : ℕ) : P3_7_1.BankOK (bank232 u) :=
  P3_7_1.checked (bank232 u) (m:=1450) (B:=2022) (J:=436) (N:=91566841790464) (M:=458421718666) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole232
private theorem pole233 : momentEstimate 2022 445 = 465769321795 := by
  refine moment_from_blocks [(128,689314080),(128,4489980192),(128,11319982368),(128,20297474579),(128,29154598976),(128,36202455104),(128,41379651648),(128,44686188608),(128,46122065984),(128,45687283776),(128,43381841984),(128,39205740608),(128,33227552805),(128,26312272864),(128,19373968205),(128,12923390794),(128,7381962688),(128,3211675584),(128,713801664),(35,8119284)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank233 (u : ℕ) : P3_7_1.BankOK (bank233 u) :=
  P3_7_1.checked (bank233 u) (m:=1450) (B:=2022) (J:=445) (N:=92998964346880) (M:=465769321795) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole233
end Research6969.TransitionBanks
end Z6969Source0695

-- Source: Research6969.TransitionBankChecks13
section Z6969Source0696
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole234 : momentEstimate 2022 457 = 475487789910 := by
  refine moment_from_blocks [(128,689314080),(128,4489980192),(128,11319982368),(128,20331762030),(128,29430229952),(128,36712737728),(128,42074254272),(128,45514779584),(128,47034313664),(128,46632856512),(128,44310408128),(128,40066968512),(128,34002486726),(128,27046619888),(128,20047546222),(128,13509245760),(128,7849666144),(128,3535492704),(128,870139488),(47,19005956)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank234 (u : ℕ) : P3_7_1.BankOK (bank234 u) :=
  P3_7_1.checked (bank234 u) (m:=1450) (B:=2022) (J:=457) (N:=94890063298560) (M:=475487789910) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole234
private theorem pole235 : momentEstimate 2023 429 = 453391020534 := by
  refine moment_from_blocks [(128,689671840),(128,4492451488),(128,11326664352),(128,20241005155),(128,28765541440),(128,35511243840),(128,40453395520),(128,43591996480),(128,44927046720),(128,44458546240),(128,42186495040),(128,38110893120),(128,32268019925),(128,25412779519),(128,18551726592),(128,12211624981),(128,6818693248),(128,2829101184),(128,542462080),(20,1661770)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank235 (u : ℕ) : P3_7_1.BankOK (bank235 u) :=
  P3_7_1.checked (bank235 u) (m:=1450) (B:=2023) (J:=429) (N:=90444517867520) (M:=453391020534) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole235
private theorem pole236 : momentEstimate 2023 436 = 459151377566 := by
  refine moment_from_blocks [(128,689671840),(128,4492451488),(128,11326664352),(128,20275047989),(128,28950431936),(128,35831007424),(128,40878672064),(128,44093425856),(128,45475268800),(128,45024200896),(128,42740222144),(128,38623332544),(128,32721486052),(128,25836804721),(128,18938153962),(128,12544823025),(128,7081015008),(128,3005550304),(128,619276000),(27,3871161)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank236 (u : ℕ) : P3_7_1.BankOK (bank236 u) :=
  P3_7_1.checked (bank236 u) (m:=1450) (B:=2023) (J:=436) (N:=91566841790464) (M:=459151377566) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole236
private theorem pole237 : momentEstimate 2023 445 = 466511127281 := by
  refine moment_from_blocks [(128,689671840),(128,4492451488),(128,11326664352),(128,20310414287),(128,29174808128),(128,36229971520),(128,41414475328),(128,44728319552),(128,46171504192),(128,45744029248),(128,43445894720),(128,39277100608),(128,33303890341),(128,26384746826),(128,19438986021),(128,12978402660),(128,7424597376),(128,3239830912),(128,726560128),(36,8807754)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank237 (u : ℕ) : P3_7_1.BankOK (bank237 u) :=
  P3_7_1.checked (bank237 u) (m:=1450) (B:=2023) (J:=445) (N:=92998964346880) (M:=466511127281) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole237
private theorem pole238 : momentEstimate 2023 457 = 476245648464 := by
  refine moment_from_blocks [(128,689671840),(128,4492451488),(128,11326664352),(128,20344724134),(128,29450631104),(128,36740642752),(128,42109663168),(128,45557692352),(128,47084730304),(128,46690777024),(128,44375832512),(128,40139896768),(128,34079927884),(128,27120043208),(128,20113616054),(128,13565435756),(128,7893611232),(128,3565044448),(128,884380384),(48,20211700)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank238 (u : ℕ) : P3_7_1.BankOK (bank238 u) :=
  P3_7_1.checked (bank238 u) (m:=1450) (B:=2023) (J:=457) (N:=94890063298560) (M:=476245648464) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole238
private theorem pole239 : momentEstimate 2439 537 = 985665319192 := by
  refine moment_from_blocks [(128,838500000),(128,5520510624),(128,14106369696),(128,25790770848),(128,39436022386),(128,52013857216),(128,62340151744),(128,70409910720),(128,76223134144),(128,79779822016),(128,81079974336),(128,80123591104),(128,76910672320),(128,71441217984),(128,63715955131),(128,54131861401),(128,43959757276),(128,33884404651),(128,24407061816),(128,15939321211),(128,8952687328),(128,3829766880),(128,822414048),(32,7584312)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank239 (u : ℕ) : P3_7_1.BankOK (bank239 u) :=
  P3_7_1.checked (bank239 u) (m:=1750) (B:=2439) (J:=537) (N:=163381988556800) (M:=985665319192) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole239
private theorem pole240 : momentEstimate 2440 537 = 986966790957 := by
  refine moment_from_blocks [(128,838857760),(128,5522981920),(128,14113051680),(128,25803760672),(128,39457235098),(128,52043881920),(128,62378991040),(128,70457564608),(128,76279602624),(128,79845105088),(128,81154072000),(128,80206503360),(128,77002399168),(128,71541759424),(128,63825198936),(128,54241988864),(128,44063605769),(128,33978918078),(128,24489558373),(128,16008007675),(128,9004440688),(128,3863603312),(128,837416048),(33,8286852)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank240 (u : ℕ) : P3_7_1.BankOK (bank240 u) :=
  P3_7_1.checked (bank240 u) (m:=1750) (B:=2440) (J:=537) (N:=163381988556800) (M:=986966790957) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole240
private theorem pole241 : momentEstimate 2441 527 = 973912060302 := by
  refine moment_from_blocks [(128,839215520),(128,5525453216),(128,14119733664),(128,25816750496),(128,39371208340),(128,51693126144),(128,61801529856),(128,69695341056),(128,75374559744),(128,78839185920),(128,80089219584),(128,79124660736),(128,75945509376),(128,70551765504),(128,62943459774),(128,53431722716),(128,43291935698),(128,33263259250),(128,23849581332),(128,15467105226),(128,8583013920),(128,3580331552),(128,711042592),(24,3349086)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank241 (u : ℕ) : P3_7_1.BankOK (bank241 u) :=
  P3_7_1.checked (bank241 u) (m:=1750) (B:=2441) (J:=527) (N:=161065121873920) (M:=973912060302) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole241
private theorem pole242 : momentEstimate 2441 537 = 988269431527 := by
  refine moment_from_blocks [(128,839215520),(128,5525453216),(128,14119733664),(128,25816750496),(128,39478447810),(128,52073906624),(128,62417830336),(128,70505218496),(128,76336071104),(128,79910388160),(128,81228169664),(128,80289415616),(128,77094126016),(128,71642300864),(128,63934455224),(128,54352216118),(128,44167571189),(128,34073562646),(128,24572197293),(128,16076844401),(128,9056353168),(128,3897597840),(128,852575120),(34,9030942)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank242 (u : ℕ) : P3_7_1.BankOK (bank242 u) :=
  P3_7_1.checked (bank242 u) (m:=1750) (B:=2441) (J:=537) (N:=163381988556800) (M:=988269431527) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole242
private theorem pole243 : momentEstimate 2441 551 = 1008217465165 := by
  refine moment_from_blocks [(128,839215520),(128,5525453216),(128,14119733664),(128,25816750496),(128,39596943194),(128,52569636096),(128,63246040320),(128,71607188736),(128,77653081344),(128,81383718144),(128,82799099136),(128,81899224320),(128,78684093696),(128,73153707264),(128,65311303704),(128,55646067942),(128,45401655485),(128,35219026261),(128,25597667321),(128,16946965038),(128,9738094752),(128,4363417760),(128,1074948256),(48,24433500)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank243 (u : ℕ) : P3_7_1.BankOK (bank243 u) :=
  P3_7_1.checked (bank243 u) (m:=1750) (B:=2441) (J:=551) (N:=166595992223744) (M:=1008217465165) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole243
private theorem pole244 : momentEstimate 2442 518 = 962176592398 := by
  refine moment_from_blocks [(128,839573280),(128,5527924512),(128,14126415648),(128,25829740320),(128,39277887867),(128,51361003968),(128,61267343808),(128,68996839872),(128,74549492160),(128,77925300672),(128,79124265408),(128,78146386368),(128,74991663552),(128,69660096960),(128,62151686592),(128,52714589495),(128,42610358659),(128,32632461035),(128,23286931947),(128,14993369875),(128,8216294784),(128,3337336192),(128,608548224),(16,1081200)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank244 (u : ℕ) : P3_7_1.BankOK (bank244 u) :=
  P3_7_1.checked (bank244 u) (m:=1750) (B:=2442) (J:=518) (N:=158964379549696) (M:=962176592398) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole244
private theorem pole245 : momentEstimate 2442 527 = 975196209190 := by
  refine moment_from_blocks [(128,839573280),(128,5527924512),(128,14126415648),(128,25829740320),(128,39392362692),(128,51722930688),(128,61839985152),(128,69742447104),(128,75430316544),(128,78903593472),(128,80162277888),(128,79206369792),(128,76035869184),(128,70650776064),(128,63051108544),(128,53541138436),(128,43395038474),(128,33356968890),(128,23931199075),(128,15534800034),(128,8633718640),(128,3613045616),(128,724848496),(25,3760645)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank245 (u : ℕ) : P3_7_1.BankOK (bank245 u) :=
  P3_7_1.checked (bank245 u) (m:=1750) (B:=2442) (J:=527) (N:=161065121873920) (M:=975196209190) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole245
private theorem pole246 : momentEstimate 2442 537 = 989573241440 := by
  refine moment_from_blocks [(128,839573280),(128,5527924512),(128,14126415648),(128,25829740320),(128,39499660522),(128,52103931328),(128,62456669632),(128,70552872384),(128,76392539584),(128,79975671232),(128,81302267328),(128,80372327872),(128,77185852864),(128,71742842304),(128,64043722604),(128,54462542980),(128,44271653369),(128,34168338254),(128,24654978633),(128,16145831270),(128,9108424768),(128,3931750464),(128,867891264),(35,9819024)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank246 (u : ℕ) : P3_7_1.BankOK (bank246 u) :=
  P3_7_1.checked (bank246 u) (m:=1750) (B:=2442) (J:=537) (N:=163381988556800) (M:=989573241440) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole246
private theorem pole247 : momentEstimate 2928 645 = 2046887686018 := by
  refine moment_from_blocks [(128,1013444640),(128,6728974368),(128,17373859872),(128,32142794784),(128,50230472736),(128,70152028145),(128,88298360128),(128,103735217472),(128,116462554432),(128,126480371008),(128,133788667200),(128,138387443008),(128,140276698432),(128,139456433472),(128,135926648128),(128,129687342400),(128,120738516288),(128,109081540282),(128,95212951515),(128,80588828830),(128,65919170723),(128,51721474088),(128,38471648960),(128,26528728304),(128,16430233840),(128,8541285616),(128,3113541872),(117,398455475)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank247 (u : ℕ) : P3_7_1.BankOK (bank247 u) :=
  P3_7_1.checked (bank247 u) (m:=2100) (B:=2928) (J:=645) (N:=282396798484480) (M:=2046887686018) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole247
private theorem pole248 : momentEstimate 2928 662 = 2088662039796 := by
  refine moment_from_blocks [(128,1013444640),(128,6728974368),(128,17373859872),(128,32142794784),(128,50230472736),(128,70397500665),(128,89109703488),(128,105045125952),(128,118199724864),(128,128573500224),(128,136166452032),(128,140978580288),(128,143009884992),(128,142260366144),(128,138730023744),(128,132418857792),(128,123326868288),(128,111461875252),(128,97480170395),(128,82775665451),(128,67991484321),(128,53642178761),(128,40201644146),(128,28022690672),(128,17649672048),(128,9452776304),(128,3683661680),(128,593986416),(6,99477)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank248 (u : ℕ) : P3_7_1.BankOK (bank248 u) :=
  P3_7_1.checked (bank248 u) (m:=2100) (B:=2928) (J:=662) (N:=288013660979200) (M:=2088662039796) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole248
private theorem pole249 : momentEstimate 2929 645 = 2049139102608 := by
  refine moment_from_blocks [(128,1013802400),(128,6731445664),(128,17380541856),(128,32155784608),(128,50251867552),(128,70183614981),(128,88340531008),(128,103787972416),(128,116525893440),(128,126554294080),(128,133873174336),(128,138482534208),(128,140382373696),(128,139572692800),(128,136053491520),(128,129824769856),(128,120886527808),(128,109239953046),(128,95372282227),(128,80741290058),(128,66061611121),(128,51851053802),(128,38586034768),(128,26626007696),(128,16507117200),(128,8596855440),(128,3146880656),(118,408704365)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank249 (u : ℕ) : P3_7_1.BankOK (bank249 u) :=
  P3_7_1.checked (bank249 u) (m:=2100) (B:=2929) (J:=645) (N:=282396798484480) (M:=2049139102608) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole249
private theorem pole250 : momentEstimate 2929 662 = 2090961110089 := by
  refine moment_from_blocks [(128,1013802400),(128,6731445664),(128,17380541856),(128,32155784608),(128,50251867552),(128,70429199140),(128,89152262784),(128,105098547840),(128,118264009344),(128,128648647296),(128,136252461696),(128,141075452544),(128,143117619840),(128,142378963584),(128,138859483776),(128,132559180416),(128,123478053504),(128,111623328189),(128,97641327396),(128,82930066194),(128,68136004386),(128,53773997485),(128,40318450039),(128,28122609856),(128,17729317056),(128,9511229632),(128,3720005824),(128,607303872),(7,146316)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank250 (u : ℕ) : P3_7_1.BankOK (bank250 u) :=
  P3_7_1.checked (bank250 u) (m:=2100) (B:=2929) (J:=662) (N:=288013660979200) (M:=2090961110089) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole250
private theorem pole251 : momentEstimate 2930 622 = 1994139134137 := by
  refine moment_from_blocks [(128,1014160160),(128,6733916960),(128,17387223840),(128,32168774432),(128,50271038513),(128,69757060800),(128,87160391360),(128,101950670528),(128,114127898304),(128,123692074688),(128,130643199680),(128,134981273280),(128,136706295488),(128,135818266304),(128,132317185728),(128,126203053760),(128,117475870400),(128,106135635648),(128,92475588923),(128,77954635192),(128,63427431723),(128,49416365205),(128,36401231541),(128,24750121600),(128,14988984960),(128,7480779392),(128,2477163136),(96,222842592)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank251 (u : ℕ) : P3_7_1.BankOK (bank251 u) :=
  P3_7_1.checked (bank251 u) (m:=2100) (B:=2930) (J:=622) (N:=274699477319680) (M:=1994139134137) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole251
end Research6969.TransitionBanks
end Z6969Source0696

-- Source: Research6969.PackedRanks252To254
section Z6969Source0697
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks252To254
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment2930_632 : P1_7_1.groupedPoleMoment 2930 632 ≤ 2019119590628 :=
  _root_.PoleAffine6970.certified 2930 632 2019119590628 (by decide) (by decide +kernel)

theorem moment2930_645 : P1_7_1.groupedPoleMoment 2930 645 ≤ 2051392203643 :=
  _root_.PoleAffine6970.certified 2930 645 2051392203643 (by decide) (by decide +kernel)

theorem moment2930_662 : P1_7_1.groupedPoleMoment 2930 662 ≤ 2093261903519 :=
  _root_.PoleAffine6970.certified 2930 662 2093261903519 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks252To254

namespace Research6969.PackedRanks.PackedRanks252To254
open Research6969.TransitionBanks
theorem rank252 (u:ℕ) : P3_7_1.BankOK (bank252 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank252 u).shape (by change 2*632≤2100;decide) (by change 2100+632≤2930+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2100-2*632) 632=6*278060332482560:=by decide
  change 6*P1_7_1.nodeRows (bank252 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank252 u).shape=262144*P1_7_1_2.sixPerNode (2100-2*632) 632 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank252 u).shape=278060332482560; omega, moment2930_632,by change 2930<K1.p;decide⟩
theorem rank253 (u:ℕ) : P3_7_1.BankOK (bank253 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank253 u).shape (by change 2*645≤2100;decide) (by change 2100+645≤2930+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2100-2*645) 645=6*282396798484480:=by decide
  change 6*P1_7_1.nodeRows (bank253 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank253 u).shape=262144*P1_7_1_2.sixPerNode (2100-2*645) 645 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank253 u).shape=282396798484480; omega, moment2930_645,by change 2930<K1.p;decide⟩
theorem rank254 (u:ℕ) : P3_7_1.BankOK (bank254 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank254 u).shape (by change 2*662≤2100;decide) (by change 2100+662≤2930+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2100-2*662) 662=6*288013660979200:=by decide
  change 6*P1_7_1.nodeRows (bank254 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank254 u).shape=262144*P1_7_1_2.sixPerNode (2100-2*662) 662 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank254 u).shape=288013660979200; omega, moment2930_662,by change 2930<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks252To254
end Z6969Source0697

-- Source: Research6969.PackedRanks255To257
section Z6969Source0698
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks255To257
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment2931_632 : P1_7_1.groupedPoleMoment 2931 632 ≤ 2021337557218 :=
  _root_.PoleAffine6970.certified 2931 632 2021337557218 (by decide) (by decide +kernel)

theorem moment3322_747 : P1_7_1.groupedPoleMoment 3322 747 ≤ 3445098204118 :=
  _root_.PoleAffine6970.certified 3322 747 3445098204118 (by decide) (by decide +kernel)

theorem moment3544_792 : P1_7_1.groupedPoleMoment 3544 792 ≤ 4440399084942 :=
  _root_.PoleAffine6970.certified 3544 792 4440399084942 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks255To257

namespace Research6969.PackedRanks.PackedRanks255To257
open Research6969.TransitionBanks
theorem rank255 (u:ℕ) : P3_7_1.BankOK (bank255 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank255 u).shape (by change 2*632≤2100;decide) (by change 2100+632≤2931+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2100-2*632) 632=6*278060332482560:=by decide
  change 6*P1_7_1.nodeRows (bank255 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank255 u).shape=262144*P1_7_1_2.sixPerNode (2100-2*632) 632 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank255 u).shape=278060332482560; omega, moment2931_632,by change 2931<K1.p;decide⟩
theorem rank256 (u:ℕ) : P3_7_1.BankOK (bank256 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank256 u).shape (by change 2*747≤2387;decide) (by change 2387+747≤3322+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2387-2*747) 747=6*420533089861632:=by decide
  change 6*P1_7_1.nodeRows (bank256 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank256 u).shape=262144*P1_7_1_2.sixPerNode (2387-2*747) 747 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank256 u).shape=420533089861632; omega, moment3322_747,by change 3322<K1.p;decide⟩
theorem rank257 (u:ℕ) : P3_7_1.BankOK (bank257 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank257 u).shape (by change 2*792≤2546;decide) (by change 2546+792≤3544+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2546-2*792) 792=6*507920948920320:=by decide
  change 6*P1_7_1.nodeRows (bank257 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank257 u).shape=262144*P1_7_1_2.sixPerNode (2546-2*792) 792 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank257 u).shape=507920948920320; omega, moment3544_792,by change 3544<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks255To257
end Z6969Source0698
