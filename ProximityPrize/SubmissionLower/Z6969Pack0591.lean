import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

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
    (lo : 2293≤M.overhead.toNat) (hi : M.overhead.toNat≤2389)
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
  have floor : 257363≤RawPhysicalDegree.weight (131071-M.overhead.toNat)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1173 : Request := ⟨⟨⟨556,772,170,5648⟩,5255817068544,9968090926⟩,10,3,2,433878,34⟩
private theorem pass1173_2293 : (Triangular src1173) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1173_2294 : (Triangular src1173) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1173_2297 : (Triangular src1173) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1173_2306 : (Triangular src1173) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1173_2335 : (Triangular src1173) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1173 : Cover (Triangular src1173) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1173_2293, by decide, by decide, pass1173_2294, by decide, by decide, pass1173_2297, by decide, by decide, pass1173_2306, by decide, by decide, pass1173_2335, rfl⟩
def src1174 : Request := ⟨⟨⟨556,772,170,5725⟩,5255817068544,9968090926⟩,10,3,2,434071,33⟩
private theorem pass1174_2293 : (Triangular src1174) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1174_2294 : (Triangular src1174) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1174_2297 : (Triangular src1174) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1174_2306 : (Triangular src1174) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1174_2335 : (Triangular src1174) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1174 : Cover (Triangular src1174) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1174_2293, by decide, by decide, pass1174_2294, by decide, by decide, pass1174_2297, by decide, by decide, pass1174_2306, by decide, by decide, pass1174_2335, rfl⟩
def src1175 : Request := ⟨⟨⟨556,772,170,5803⟩,5255817068544,9968090926⟩,10,3,2,434257,32⟩
private theorem pass1175_2293 : (Triangular src1175) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1175_2294 : (Triangular src1175) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1175_2297 : (Triangular src1175) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1175_2306 : (Triangular src1175) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1175_2335 : (Triangular src1175) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1175 : Cover (Triangular src1175) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1175_2293, by decide, by decide, pass1175_2294, by decide, by decide, pass1175_2297, by decide, by decide, pass1175_2306, by decide, by decide, pass1175_2335, rfl⟩
def src1176 : Request := ⟨⟨⟨556,772,170,5882⟩,5255817068544,9968090926⟩,10,3,2,434438,31⟩
private theorem pass1176_2293 : (Triangular src1176) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1176_2294 : (Triangular src1176) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1176_2297 : (Triangular src1176) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1176_2306 : (Triangular src1176) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1176_2335 : (Triangular src1176) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1176 : Cover (Triangular src1176) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1176_2293, by decide, by decide, pass1176_2294, by decide, by decide, pass1176_2297, by decide, by decide, pass1176_2306, by decide, by decide, pass1176_2335, rfl⟩
def src1177 : Request := ⟨⟨⟨556,772,170,5963⟩,5255817068544,9968090926⟩,10,3,2,434613,30⟩
private theorem pass1177_2293 : (Triangular src1177) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1177_2294 : (Triangular src1177) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1177_2297 : (Triangular src1177) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1177_2306 : (Triangular src1177) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1177_2335 : (Triangular src1177) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1177 : Cover (Triangular src1177) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1177_2293, by decide, by decide, pass1177_2294, by decide, by decide, pass1177_2297, by decide, by decide, pass1177_2306, by decide, by decide, pass1177_2335, rfl⟩
def src1178 : Request := ⟨⟨⟨556,772,170,6045⟩,5255817068544,9968090926⟩,10,3,2,434781,29⟩
private theorem pass1178_2293 : (Triangular src1178) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1178_2294 : (Triangular src1178) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1178_2297 : (Triangular src1178) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1178_2306 : (Triangular src1178) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1178_2335 : (Triangular src1178) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1178 : Cover (Triangular src1178) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1178_2293, by decide, by decide, pass1178_2294, by decide, by decide, pass1178_2297, by decide, by decide, pass1178_2306, by decide, by decide, pass1178_2335, rfl⟩
def src1179 : Request := ⟨⟨⟨556,772,170,6129⟩,5255817068544,9968090926⟩,10,3,2,434944,28⟩
private theorem pass1179_2293 : (Triangular src1179) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1179_2294 : (Triangular src1179) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1179_2297 : (Triangular src1179) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1179_2306 : (Triangular src1179) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1179_2335 : (Triangular src1179) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1179 : Cover (Triangular src1179) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1179_2293, by decide, by decide, pass1179_2294, by decide, by decide, pass1179_2297, by decide, by decide, pass1179_2306, by decide, by decide, pass1179_2335, rfl⟩
def src1180 : Request := ⟨⟨⟨556,772,170,6214⟩,5255817068544,9968090926⟩,10,3,2,435101,27⟩
private theorem pass1180_2293 : (Triangular src1180) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1180_2294 : (Triangular src1180) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1180_2297 : (Triangular src1180) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1180_2306 : (Triangular src1180) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1180_2335 : (Triangular src1180) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1180 : Cover (Triangular src1180) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1180_2293, by decide, by decide, pass1180_2294, by decide, by decide, pass1180_2297, by decide, by decide, pass1180_2306, by decide, by decide, pass1180_2335, rfl⟩
def src1181 : Request := ⟨⟨⟨556,772,170,6301⟩,5255817068544,9968090926⟩,10,3,2,435252,26⟩
private theorem pass1181_2293 : (Triangular src1181) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1181_2294 : (Triangular src1181) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1181_2297 : (Triangular src1181) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1181_2306 : (Triangular src1181) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1181_2335 : (Triangular src1181) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1181 : Cover (Triangular src1181) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1181_2293, by decide, by decide, pass1181_2294, by decide, by decide, pass1181_2297, by decide, by decide, pass1181_2306, by decide, by decide, pass1181_2335, rfl⟩
def src1182 : Request := ⟨⟨⟨556,772,170,6389⟩,5255817068544,9968090926⟩,10,3,2,435397,25⟩
private theorem pass1182_2293 : (Triangular src1182) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1182_2294 : (Triangular src1182) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1182_2297 : (Triangular src1182) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1182_2306 : (Triangular src1182) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1182_2335 : (Triangular src1182) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1182 : Cover (Triangular src1182) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1182_2293, by decide, by decide, pass1182_2294, by decide, by decide, pass1182_2297, by decide, by decide, pass1182_2306, by decide, by decide, pass1182_2335, rfl⟩
def src1183 : Request := ⟨⟨⟨556,772,170,6477⟩,5255817068544,9968090926⟩,10,3,2,435536,24⟩
private theorem pass1183_2293 : (Triangular src1183) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1183_2294 : (Triangular src1183) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1183_2297 : (Triangular src1183) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1183_2306 : (Triangular src1183) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1183_2335 : (Triangular src1183) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1183 : Cover (Triangular src1183) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1183_2293, by decide, by decide, pass1183_2294, by decide, by decide, pass1183_2297, by decide, by decide, pass1183_2306, by decide, by decide, pass1183_2335, rfl⟩
def src1184 : Request := ⟨⟨⟨556,772,170,6567⟩,5255817068544,9968090926⟩,10,3,2,435670,23⟩
private theorem pass1184_2293 : (Triangular src1184) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1184_2294 : (Triangular src1184) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1184_2297 : (Triangular src1184) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1184_2306 : (Triangular src1184) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1184_2335 : (Triangular src1184) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1184 : Cover (Triangular src1184) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1184_2293, by decide, by decide, pass1184_2294, by decide, by decide, pass1184_2297, by decide, by decide, pass1184_2306, by decide, by decide, pass1184_2335, rfl⟩
def src1185 : Request := ⟨⟨⟨556,772,170,6658⟩,5255817068544,9968090926⟩,10,3,2,435797,22⟩
private theorem pass1185_2293 : (Triangular src1185) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1185_2294 : (Triangular src1185) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1185_2297 : (Triangular src1185) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1185_2306 : (Triangular src1185) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1185_2334 : (Triangular src1185) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1185 : Cover (Triangular src1185) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1185_2293, by decide, by decide, pass1185_2294, by decide, by decide, pass1185_2297, by decide, by decide, pass1185_2306, by decide, by decide, pass1185_2334, rfl⟩
def src1186 : Request := ⟨⟨⟨556,772,170,6751⟩,5255817068544,9968090926⟩,10,3,2,435918,21⟩
private theorem pass1186_2293 : (Triangular src1186) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1186_2294 : (Triangular src1186) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1186_2297 : (Triangular src1186) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1186_2306 : (Triangular src1186) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1186_2335 : (Triangular src1186) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1186 : Cover (Triangular src1186) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1186_2293, by decide, by decide, pass1186_2294, by decide, by decide, pass1186_2297, by decide, by decide, pass1186_2306, by decide, by decide, pass1186_2335, rfl⟩
def src1187 : Request := ⟨⟨⟨556,772,170,6844⟩,5255817068544,9968090926⟩,10,3,2,436034,20⟩
private theorem pass1187_2293 : (Triangular src1187) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1187_2294 : (Triangular src1187) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1187_2297 : (Triangular src1187) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1187_2306 : (Triangular src1187) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1187_2335 : (Triangular src1187) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1187 : Cover (Triangular src1187) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1187_2293, by decide, by decide, pass1187_2294, by decide, by decide, pass1187_2297, by decide, by decide, pass1187_2306, by decide, by decide, pass1187_2335, rfl⟩
def src1188 : Request := ⟨⟨⟨556,772,170,6939⟩,5255817068544,9968090926⟩,10,3,2,436143,19⟩
private theorem pass1188_2293 : (Triangular src1188) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1188_2294 : (Triangular src1188) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1188_2297 : (Triangular src1188) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1188_2306 : (Triangular src1188) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1188_2335 : (Triangular src1188) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1188 : Cover (Triangular src1188) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1188_2293, by decide, by decide, pass1188_2294, by decide, by decide, pass1188_2297, by decide, by decide, pass1188_2306, by decide, by decide, pass1188_2335, rfl⟩
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 2 19 307353 := by
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

def price : Pricing := ⟨55/100, 90/100, [333197174, 332700328, 331974128, 332068544, 331551260, 331747343, 331972242, 146240031, 146597514, 146789285, 146522942, 73032174, 73063202, 87065647, 101033294, 108473872, 151195476, 101057369, 233857807], [1033312, 1034673, 1036664, 1036405, 1037823, 1037285, 1036669, 2633129, 2625291, 2621086, 2626926, 5485121, 5482655, 4563301, 3911042, 3630997, 2547002, 3910026, 1580916],
  ![124136401111740, 1607170869308, 210472026300, 4654567020], 181551255855730995⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
theorem free216_0 : TransitionSources.Free 2293 76 (bank216 10294) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank216 10294)) 2293 = 216180583870320 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank216 10294)) 2294 = 9637333789394880 := by decide +kernel
  refine ⟨rank216 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free216_1 : TransitionSources.Free 2390 76 (bank216 8567) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank216 8567)) 2390 = 138967137084384 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank216 8567)) 2391 = 6399692069097600 := by decide +kernel
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
theorem free230_0 : TransitionSources.Free 2293 105 (bank230 14067) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 105 (bank230 14067)) 2293 = 472985337216240 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 105 (bank230 14067)) 2294 = 38760185255166472 := by decide +kernel
  refine ⟨rank230 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free230_1 : TransitionSources.Free 2390 105 (bank230 11634) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 105 (bank230 11634)) 2390 = 652386996858220 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 105 (bank230 11634)) 2391 = 25779156097783010 := by decide +kernel
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

private def pole2930_632_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 434804440⟩
private theorem pole2930_632_0_checked :
    packedBlock 2930 632 pole2930_632_0.length 632 pole2930_632_0.packed = pole2930_632_0.total := by decide +kernel

private def pole2930_632_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 2904123352⟩
private theorem pole2930_632_1_checked :
    packedBlock 2930 632 pole2930_632_1.length 728 pole2930_632_1.packed = pole2930_632_1.total := by decide +kernel

private def pole2930_632_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 7582185688⟩
private theorem pole2930_632_2_checked :
    packedBlock 2930 632 pole2930_632_2.length 824 pole2930_632_2.packed = pole2930_632_2.total := by decide +kernel

private def pole2930_632_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 14214187480⟩
private theorem pole2930_632_3_checked :
    packedBlock 2930 632 pole2930_632_3.length 920 pole2930_632_3.packed = pole2930_632_3.total := by decide +kernel

private def pole2930_632_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 22545324760⟩
private theorem pole2930_632_4_checked :
    packedBlock 2930 632 pole2930_632_4.length 1016 pole2930_632_4.packed = pole2930_632_4.total := by decide +kernel

private def pole2930_632_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 32320793560⟩
private theorem pole2930_632_5_checked :
    packedBlock 2930 632 pole2930_632_5.length 1112 pole2930_632_5.packed = pole2930_632_5.total := by decide +kernel

private def pole2930_632_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 43261607702⟩
private theorem pole2930_632_6_checked :
    packedBlock 2930 632 pole2930_632_6.length 1208 pole2930_632_6.packed = pole2930_632_6.total := by decide +kernel

private def pole2930_632_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 54288875328⟩
private theorem pole2930_632_7_checked :
    packedBlock 2930 632 pole2930_632_7.length 1304 pole2930_632_7.packed = pole2930_632_7.total := by decide +kernel

private def pole2930_632_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 64264550208⟩
private theorem pole2930_632_8_checked :
    packedBlock 2930 632 pole2930_632_8.length 1400 pole2930_632_8.packed = pole2930_632_8.total := by decide +kernel

private def pole2930_632_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 73120149312⟩
private theorem pole2930_632_9_checked :
    packedBlock 2930 632 pole2930_632_9.length 1496 pole2930_632_9.packed = pole2930_632_9.total := by decide +kernel

private def pole2930_632_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 80855672640⟩
private theorem pole2930_632_10_checked :
    packedBlock 2930 632 pole2930_632_10.length 1592 pole2930_632_10.packed = pole2930_632_10.total := by decide +kernel

private def pole2930_632_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 87471120192⟩
private theorem pole2930_632_11_checked :
    packedBlock 2930 632 pole2930_632_11.length 1688 pole2930_632_11.packed = pole2930_632_11.total := by decide +kernel

private def pole2930_632_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 92966491968⟩
private theorem pole2930_632_12_checked :
    packedBlock 2930 632 pole2930_632_12.length 1784 pole2930_632_12.packed = pole2930_632_12.total := by decide +kernel

private def pole2930_632_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 97341787968⟩
private theorem pole2930_632_13_checked :
    packedBlock 2930 632 pole2930_632_13.length 1880 pole2930_632_13.packed = pole2930_632_13.total := by decide +kernel

private def pole2930_632_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 100597008192⟩
private theorem pole2930_632_14_checked :
    packedBlock 2930 632 pole2930_632_14.length 1976 pole2930_632_14.packed = pole2930_632_14.total := by decide +kernel

private def pole2930_632_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 102732152640⟩
private theorem pole2930_632_15_checked :
    packedBlock 2930 632 pole2930_632_15.length 2072 pole2930_632_15.packed = pole2930_632_15.total := by decide +kernel

private def pole2930_632_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 103747221312⟩
private theorem pole2930_632_16_checked :
    packedBlock 2930 632 pole2930_632_16.length 2168 pole2930_632_16.packed = pole2930_632_16.total := by decide +kernel

private def pole2930_632_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 103642214208⟩
private theorem pole2930_632_17_checked :
    packedBlock 2930 632 pole2930_632_17.length 2264 pole2930_632_17.packed = pole2930_632_17.total := by decide +kernel

private def pole2930_632_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 102417131328⟩
private theorem pole2930_632_18_checked :
    packedBlock 2930 632 pole2930_632_18.length 2360 pole2930_632_18.packed = pole2930_632_18.total := by decide +kernel

private def pole2930_632_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 100071972672⟩
private theorem pole2930_632_19_checked :
    packedBlock 2930 632 pole2930_632_19.length 2456 pole2930_632_19.packed = pole2930_632_19.total := by decide +kernel

private def pole2930_632_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 96606738240⟩
private theorem pole2930_632_20_checked :
    packedBlock 2930 632 pole2930_632_20.length 2552 pole2930_632_20.packed = pole2930_632_20.total := by decide +kernel

private def pole2930_632_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 92021428032⟩
private theorem pole2930_632_21_checked :
    packedBlock 2930 632 pole2930_632_21.length 2648 pole2930_632_21.packed = pole2930_632_21.total := by decide +kernel

private def pole2930_632_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 86316042048⟩
private theorem pole2930_632_22_checked :
    packedBlock 2930 632 pole2930_632_22.length 2744 pole2930_632_22.packed = pole2930_632_22.total := by decide +kernel

private def pole2930_632_23 : Block := ⟨96, 53977736334985159844637945175026475573827104349707981516002885182864858187587404896202629630690222366058903632830571485655909230980367648220078480696010139537691989807562064414362209338857922174300923661389095598999721616869125146577286060138602213409550339440402126837534813983887181743972631829479719913886843061906408878011997145435143239282316186124029851665065919770502613212589517386894474717202593, 79490617080⟩
private theorem pole2930_632_23_checked :
    packedBlock 2930 632 pole2930_632_23.length 2840 pole2930_632_23.packed = pole2930_632_23.total := by decide +kernel

private def pole2930_632_24 : Block := ⟨96, 56134033284458747338406348514517327706650949884643092141431163703819025965313757680118276632039590105142817805473621716466792618774491135135324850998782361666865054507558182436454158599481058419847871356652482481566096715652345355307378112642603142585831380596113327399319726196364025210581586934750274717999543203508171508945845540501086574902463373698097053117564627431385043677437176390342373367892224, 71704674899⟩
private theorem pole2930_632_24_checked :
    packedBlock 2930 632 pole2930_632_24.length 2936 pole2930_632_24.packed = pole2930_632_24.total := by decide +kernel

private def pole2930_632_25 : Block := ⟨96, 58126264161521795887701396148460965557311285261594661836158578681583091728335368878288103461615564556063780336213341649663705783599549481299530190451368998723466534646537463632834228319048776019557490100724936708482027182736141113168337461611899233683847561666862073991389601081087145449441079320651989121203547210494655518669558591151066136197738260754061073061916424476507480403855437284801834374351196, 63547742393⟩
private theorem pole2930_632_25_checked :
    packedBlock 2930 632 pole2930_632_25.length 3032 pole2930_632_25.packed = pole2930_632_25.total := by decide +kernel

private def pole2930_632_26 : Block := ⟨96, 59930992386659451680750831069744641528530784802057413233545208375471178438442364245759787712798943638348929930865439993129146373881149322036330424643675455973495170080045884832782696563204353739317314763474565620206991762029595420588882409194827901528405103376660809348684634848290349848763481982692293672921065030559204855612885852074366890108209329072782361099795485526883211410282508454435878005934513, 55294012945⟩
private theorem pole2930_632_26_checked :
    packedBlock 2930 632 pole2930_632_26.length 3128 pole2930_632_26.packed = pole2930_632_26.total := by decide +kernel

private def pole2930_632_27 : Block := ⟨96, 61571653109018573279899097122944282622992629361451368944770496762739592012771024100062472799087599558799453666445511389146133592594005965220478819930121114455436593320108556710107312772542971928482630450654580647467738207751096218628130242319892355527844996089788190229453422982938084394038553090024000380746246289246086051321188699743368336635558710124057149325961373885759866685960457231343985220372990, 47114613291⟩
private theorem pole2930_632_27_checked :
    packedBlock 2930 632 pole2930_632_27.length 3224 pole2930_632_27.packed = pole2930_632_27.total := by decide +kernel

private def pole2930_632_28 : Block := ⟨96, 63048247759141782718839813479060599598236055838765039050051651023297462188075318877062835100964188468436475828119287078751847640787513263182268984347601541998565299286175779234981605824620811771212115367516180182238866432924141472727497732266608850573526080670870991264885856584154167400492204878386741852210023229223747694835891600095048634408441346708917636198674262365487424383604848894568204201970244, 39171010002⟩
private theorem pole2930_632_28_checked :
    packedBlock 2930 632 pole2930_632_28.length 3320 pole2930_632_28.packed = pole2930_632_28.total := by decide +kernel

private def pole2930_632_29 : Block := ⟨96, 64360774906573771355687035939979379019895908868740593591340068577922454759513730377123356273546108651297505446650478862217503360177334842229019150101058988251671677193476413389212156284338245339806570569896574179123878390454086085538952697944135136316140452552129783391907708387793515403759300073825792133199406665821075927802151490900715624353340596007957521601663491532597268782408385179051323004340867, 31615008478⟩
private theorem pole2930_632_29_checked :
    packedBlock 2930 632 pole2930_632_29.length 3416 pole2930_632_29.packed = pole2930_632_29.total := by decide +kernel

private def pole2930_632_30 : Block := ⟨96, 65227982718934791564309869023288005821218924488587338492321727934536854720123001204211913589542199884969703988449060481399398551539103621797139991777909712923368281221315083012898767053844796251447729233872775960241087488713180046817356179989621078320072766011789466751897067394911376293400810259371107070189493858656055557023825250656543663081269655478563734623236376705184165551030339434940917997292218, 24577021800⟩
private theorem pole2930_632_30_checked :
    packedBlock 2930 632 pole2930_632_30.length 3512 pole2930_632_30.packed = pole2930_632_30.total := by decide +kernel

private def pole2930_632_31 : Block := ⟨96, 65790494966600776112477760968013595992361164100091149331501578765083752351169356165557667550603800049314451414373891978150870472023578548800365464866206630344265956934621490388082104578919428865051678801753574882495355109829664857785680094182428943078747527593435583293981165184106018156467164767064460342671326302184258931603247741303354095204975205511760162318490903403965096088739071261889313105251040, 18156902868⟩
private theorem pole2930_632_31_checked :
    packedBlock 2930 632 pole2930_632_31.length 3608 pole2930_632_31.packed = pole2930_632_31.total := by decide +kernel

private def pole2930_632_32 : Block := ⟨96, 66353007214266760660645652912739186163503403711594960170681429595630649982215711126903421511665400213659198840298723474902342392508053475803590937954503547765163632647927897763265442103994061478655628350038840489116747048882073156971137209206182939385181295365037001737096020743809809277562623369462325070041651728155847433196836803164785286286007005307791509240874147588225484816369216921506477636455160, 12568058388⟩
private theorem pole2930_632_32_checked :
    packedBlock 2930 632 pole2930_632_32.length 3704 pole2930_632_32.packed = pole2930_632_32.total := by decide +kernel

private def pole2930_632_33 : Block := ⟨96, 66915519461932745208813544857464776334645643323098771009861280426177547613262066088249175472727000378003946266223554971653814312992528402806816411042800465186061308361234305138448779629068694092259577898324106095738138987934481456156594324229936935691615063136638420180210876303513600398658081971860189797411977154127435934790425865026216477367038805103822856163257391772485873543999362581123642167659280, 7908103764⟩
private theorem pole2930_632_33_checked :
    packedBlock 2930 632 pole2930_632_33.length 3800 pole2930_632_33.packed = pole2930_632_33.total := by decide +kernel

private def pole2930_632_34 : Block := ⟨96, 67478031709598729756981436802190366505787882934602581849041131256724445244308421049594929433788600542348693692148386468405286233477003329810041884131097382606958984074540712513632117154143326705863527446609371702359530926986889755342051439253690931998048830908239838623325731863217391519753540574258054524782302580099024436384014926887647668448070604899854203085640635956746262271629508240740806698863400, 4256665236⟩
private theorem pole2930_632_34_checked :
    packedBlock 2930 632 pole2930_632_34.length 3896 pole2930_632_34.packed = pole2930_632_34.total := by decide +kernel

private def pole2930_632_35 : Block := ⟨96, 68040543957264714305149328746915956676930122546106392688220982087271342875354776010940683394850200706693441118073217965156758153961478256813267357219394300027856659787847119888815454679217959319467476994894637308980922866039298054527508554277444928304482598679841257066440587422921182640848999176655919252152628006070612937977603988749078859529102404695885550008023880141006650999259653900357971230067520, 1693369044⟩
private theorem pole2930_632_35_checked :
    packedBlock 2930 632 pole2930_632_35.length 3992 pole2930_632_35.packed = pole2930_632_35.total := by decide +kernel

private def pole2930_632_36 : Block := ⟨96, 68603056204930698853317220691641546848072362157610203527400832917818240506401130972286437355911800871038188543998049461908230074445953183816492830307691217448754335501153527263998792204292591933071426543179902915602314805091706353712965669301198924610916366451442675509555442982624973761944457779053783979522953432042201439571193050610510050610134204491916896930407124325267039726889799559975135761271640, 297841428⟩
private theorem pole2930_632_36_checked :
    packedBlock 2930 632 pole2930_632_36.length 4088 pole2930_632_36.packed = pole2930_632_36.total := by decide +kernel

private def pole2930_632_37 : Block := ⟨10, 249272048127676742106768820178120192297840, 365742⟩
private theorem pole2930_632_37_checked :
    packedBlock 2930 632 pole2930_632_37.length 4184 pole2930_632_37.packed = pole2930_632_37.total := by decide +kernel

private def poleBlocks2930_632 : List Block := [pole2930_632_0, pole2930_632_1, pole2930_632_2, pole2930_632_3, pole2930_632_4, pole2930_632_5, pole2930_632_6, pole2930_632_7, pole2930_632_8, pole2930_632_9, pole2930_632_10, pole2930_632_11, pole2930_632_12, pole2930_632_13, pole2930_632_14, pole2930_632_15, pole2930_632_16, pole2930_632_17, pole2930_632_18, pole2930_632_19, pole2930_632_20, pole2930_632_21, pole2930_632_22, pole2930_632_23, pole2930_632_24, pole2930_632_25, pole2930_632_26, pole2930_632_27, pole2930_632_28, pole2930_632_29, pole2930_632_30, pole2930_632_31, pole2930_632_32, pole2930_632_33, pole2930_632_34, pole2930_632_35, pole2930_632_36, pole2930_632_37]
theorem moment2930_632 : P1_7_1.groupedPoleMoment 2930 632 ≤ 2019119590628 := by
  refine grouped_from_blocks 2930 632 _ poleBlocks2930_632 ?_ (by decide) (by decide)
  exact ⟨pole2930_632_0_checked, pole2930_632_1_checked, pole2930_632_2_checked, pole2930_632_3_checked, pole2930_632_4_checked, pole2930_632_5_checked, pole2930_632_6_checked, pole2930_632_7_checked, pole2930_632_8_checked, pole2930_632_9_checked, pole2930_632_10_checked, pole2930_632_11_checked, pole2930_632_12_checked, pole2930_632_13_checked, pole2930_632_14_checked, pole2930_632_15_checked, pole2930_632_16_checked, pole2930_632_17_checked, pole2930_632_18_checked, pole2930_632_19_checked, pole2930_632_20_checked, pole2930_632_21_checked, pole2930_632_22_checked, pole2930_632_23_checked, pole2930_632_24_checked, pole2930_632_25_checked, pole2930_632_26_checked, pole2930_632_27_checked, pole2930_632_28_checked, pole2930_632_29_checked, pole2930_632_30_checked, pole2930_632_31_checked, pole2930_632_32_checked, pole2930_632_33_checked, pole2930_632_34_checked, pole2930_632_35_checked, pole2930_632_36_checked, pole2930_632_37_checked, True.intro⟩

private def pole2930_645_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 434804440⟩
private theorem pole2930_645_0_checked :
    packedBlock 2930 645 pole2930_645_0.length 645 pole2930_645_0.packed = pole2930_645_0.total := by decide +kernel

private def pole2930_645_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 2904123352⟩
private theorem pole2930_645_1_checked :
    packedBlock 2930 645 pole2930_645_1.length 741 pole2930_645_1.packed = pole2930_645_1.total := by decide +kernel

private def pole2930_645_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 7582185688⟩
private theorem pole2930_645_2_checked :
    packedBlock 2930 645 pole2930_645_2.length 837 pole2930_645_2.packed = pole2930_645_2.total := by decide +kernel

private def pole2930_645_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 14214187480⟩
private theorem pole2930_645_3_checked :
    packedBlock 2930 645 pole2930_645_3.length 933 pole2930_645_3.packed = pole2930_645_3.total := by decide +kernel

private def pole2930_645_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 22545324760⟩
private theorem pole2930_645_4_checked :
    packedBlock 2930 645 pole2930_645_4.length 1029 pole2930_645_4.packed = pole2930_645_4.total := by decide +kernel

private def pole2930_645_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 32320793560⟩
private theorem pole2930_645_5_checked :
    packedBlock 2930 645 pole2930_645_5.length 1125 pole2930_645_5.packed = pole2930_645_5.total := by decide +kernel

private def pole2930_645_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 43278368953⟩
private theorem pole2930_645_6_checked :
    packedBlock 2930 645 pole2930_645_6.length 1221 pole2930_645_6.packed = pole2930_645_6.total := by decide +kernel

private def pole2930_645_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 54512751344⟩
private theorem pole2930_645_7_checked :
    packedBlock 2930 645 pole2930_645_7.length 1317 pole2930_645_7.packed = pole2930_645_7.total := by decide +kernel

private def pole2930_645_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 64731995888⟩
private theorem pole2930_645_8_checked :
    packedBlock 2930 645 pole2930_645_8.length 1413 pole2930_645_8.packed = pole2930_645_8.total := by decide +kernel

private def pole2930_645_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 73808161520⟩
private theorem pole2930_645_9_checked :
    packedBlock 2930 645 pole2930_645_9.length 1509 pole2930_645_9.packed = pole2930_645_9.total := by decide +kernel

private def pole2930_645_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 81741248240⟩
private theorem pole2930_645_10_checked :
    packedBlock 2930 645 pole2930_645_10.length 1605 pole2930_645_10.packed = pole2930_645_10.total := by decide +kernel

private def pole2930_645_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 88531256048⟩
private theorem pole2930_645_11_checked :
    packedBlock 2930 645 pole2930_645_11.length 1701 pole2930_645_11.packed = pole2930_645_11.total := by decide +kernel

private def pole2930_645_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 94178184944⟩
private theorem pole2930_645_12_checked :
    packedBlock 2930 645 pole2930_645_12.length 1797 pole2930_645_12.packed = pole2930_645_12.total := by decide +kernel

private def pole2930_645_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 98682034928⟩
private theorem pole2930_645_13_checked :
    packedBlock 2930 645 pole2930_645_13.length 1893 pole2930_645_13.packed = pole2930_645_13.total := by decide +kernel

private def pole2930_645_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 102042806000⟩
private theorem pole2930_645_14_checked :
    packedBlock 2930 645 pole2930_645_14.length 1989 pole2930_645_14.packed = pole2930_645_14.total := by decide +kernel

private def pole2930_645_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 104260498160⟩
private theorem pole2930_645_15_checked :
    packedBlock 2930 645 pole2930_645_15.length 2085 pole2930_645_15.packed = pole2930_645_15.total := by decide +kernel

private def pole2930_645_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 105335111408⟩
private theorem pole2930_645_16_checked :
    packedBlock 2930 645 pole2930_645_16.length 2181 pole2930_645_16.packed = pole2930_645_16.total := by decide +kernel

private def pole2930_645_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 105266645744⟩
private theorem pole2930_645_17_checked :
    packedBlock 2930 645 pole2930_645_17.length 2277 pole2930_645_17.packed = pole2930_645_17.total := by decide +kernel

private def pole2930_645_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 104055101168⟩
private theorem pole2930_645_18_checked :
    packedBlock 2930 645 pole2930_645_18.length 2373 pole2930_645_18.packed = pole2930_645_18.total := by decide +kernel

private def pole2930_645_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 101700477680⟩
private theorem pole2930_645_19_checked :
    packedBlock 2930 645 pole2930_645_19.length 2469 pole2930_645_19.packed = pole2930_645_19.total := by decide +kernel

private def pole2930_645_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 98202775280⟩
private theorem pole2930_645_20_checked :
    packedBlock 2930 645 pole2930_645_20.length 2565 pole2930_645_20.packed = pole2930_645_20.total := by decide +kernel

private def pole2930_645_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 93561993968⟩
private theorem pole2930_645_21_checked :
    packedBlock 2930 645 pole2930_645_21.length 2661 pole2930_645_21.packed = pole2930_645_21.total := by decide +kernel

private def pole2930_645_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 87778133744⟩
private theorem pole2930_645_22_checked :
    packedBlock 2930 645 pole2930_645_22.length 2757 pole2930_645_22.packed = pole2930_645_22.total := by decide +kernel

private def pole2930_645_23 : Block := ⟨96, 53977736334985159844637925322259516942167987572331418607642201441978254568926285860389612532410473394810100446684931802072171176020716697861054203210964082799850157828726906147701025486223636332465233858425168133758877299367985059270281512792954816432334257784716042456680906965743718372520966157342226948596916963179684023105702796685189661038771258001252086425483266716333581120959488771910398317725857, 80852216093⟩
private theorem pole2930_645_23_checked :
    packedBlock 2930 645 pole2930_645_23.length 2853 pole2930_645_23.packed = pole2930_645_23.total := by decide +kernel

private def pole2930_645_24 : Block := ⟨96, 56110595274139331315566019683487094782853356567497100023132003485900148982900887217985254949072866870612931619089665191350917987273824768019502943421634177404724080548786484675636318007814768913513523742373179216753738710271943013063447223244889791288217321843242213998839500288699623244690179040028117747675657584615393220098535482330558034103457677523390842585422212399979691586425333692528907555719424, 73007116651⟩
private theorem pole2930_645_24_checked :
    packedBlock 2930 645 pole2930_645_24.length 2949 pole2930_645_24.packed = pole2930_645_24.total := by decide +kernel

private def pole2930_645_25 : Block := ⟨96, 58079388140970277234153641490026660386365191798862474050416591574465318177619527098991548180506670345892947571778013005646112672236699491097043048375753684147215288062656706798218532089813382827012091550594155356122130485497334129582551334941279198519010454686155965942817376911054884108840117491741285407766318607884653414216317440114565533270352700143586418899679777060362440157140810547575342532856155, 64817138789⟩
private theorem pole2930_645_25_checked :
    packedBlock 2930 645 pole2930_645_25.length 3045 pole2930_645_25.packed = pole2930_645_25.total := by decide +kernel

private def pole2930_645_26 : Block := ⟨96, 59884114935565310992858961479354669471586029243762158534621732438619000117408776710076104382029321662185016779348602656286649736107680892633819296868425257212508330468156408332271973199251693838539748197140117942680880654986705783676195931277035743201609031212687723985580311026244043009636825009362966629277167997414702066508446290378615380221569194996452223294725430582807077708897865005324052716063151, 56519904071⟩
private theorem pole2930_645_26_checked :
    packedBlock 2930 645 pole2930_645_26.length 3141 pole2930_645_26.packed = pole2930_645_26.total := by decide +kernel

private def pole2930_645_27 : Block := ⟨96, 61524775657837124528410360317228786187000284458564558935537137969290064979439890505578549185411092506039877926374929191753852082644222531517820337556563316995993837710946518056431260084957429873205991956720202470752957528558000320727028349751354732957866476812988261099635170253947700454140231164196332953363531724263370829980584689244698236929278293389957941471774209340550655870241520324729115552729596, 48285659859⟩
private theorem pole2930_645_27_checked :
    packedBlock 2930 645 pole2930_645_27.length 3237 pole2930_645_27.packed = pole2930_645_27.total := by decide +kernel

private def pole2930_645_28 : Block := ⟨96, 62977933728183534650318826984758258050848503902697119621501009128264342206807309069425008899674485833380842809742495208443076921416142516882378943291927815982161750686081988117702494521658029322370530886975709639286740786576655202296537811334341901562368885751508791079997989402118928241011471076096160387699029111512965278179153946585445365887635136800911906497455436348567371515450167020003577448925761, 40275187087⟩
private theorem pole2930_645_28_checked :
    packedBlock 2930 645 pole2930_645_28.length 3333 pole2930_645_28.packed = pole2930_645_28.total := by decide +kernel

private def pole2930_645_29 : Block := ⟨96, 64267024295751421235398216212360357437098300733516071108681358756800523801622065186260594374682683506610333090533786560790219433418423590636892509818723294967355808596600644099385308571606352642402285823802297358968796423101099468704683268906977784798757411603990682840404937634409995932954874035697661753091809793476996441883186689893302225645662654579650786607121034442709992003982579367871153151412864, 32639800261⟩
private theorem pole2930_645_29_checked :
    packedBlock 2930 645 pole2930_645_29.length 3429 pole2930_645_29.packed = pole2930_645_29.total := by decide +kernel

private def pole2930_645_30 : Block := ⟨96, 65157668687976538166927598862024903151296944902079275053884476720514193522122510537960617109267902149259109467432715374346551677611302318263640426101202314500522716888787911976261168522669936377659506858725496070031411804135253087597065559886262938508461585457667529800246422406370536118627046807986642031810127741320427817547942621827104280087704498467855792714818385356108710537517840582216036404562615, 25509093085⟩
private theorem pole2930_645_30_checked :
    packedBlock 2930 645 pole2930_645_30.length 3525 pole2930_645_30.packed = pole2930_645_30.total := by decide +kernel

private def pole2930_645_31 : Block := ⟨96, 65720180935642522715095490806750493322439184513583085893064327551061091153168865499306371070329502313603856893357546871098023598095777245266865899189499231921420392602094319351444506047744568991263456407011957766094030866693324179419038291706491749723702543880077410583899044507276297598578918867174995316407156185980159616192272562797476527472771634827768060332857449981872227041386011046458487079389916, 18980778696⟩
private theorem pole2930_645_31_checked :
    packedBlock 2930 645 pole2930_645_31.length 3621 pole2930_645_31.packed = pole2930_645_31.total := by decide +kernel

private def pole2930_645_32 : Block := ⟨96, 66282693183308507263263382751476083493581424125086896732244178381607988784215220460652125031391102477948604319282378367849495518580252172270091372277796149342318068315400726726627843572819201604867405955297223372715422805745732478604495406730245746030136311651678829027013900066980088719674377469572860043777481611951748117785861624658907718553803434623799407255240694166132615769016156706075651610594036, 13272268488⟩
private theorem pole2930_645_32_checked :
    packedBlock 2930 645 pole2930_645_32.length 3717 pole2930_645_32.packed = pole2930_645_32.total := by decide +kernel

private def pole2930_645_33 : Block := ⟨96, 66845205430974491811431274696201673664723663736590707571424029212154886415261575421997878992452702642293351745207209864600967439064727099273316845366093066763215744028707134101811181097893834218471355503582488979336814744798140777789952521753999742336570079423280247470128755626683879840769836071970724771147807037923336619379450686520338909634835234419830754177623938350393004496646302365692816141798156, 8481865416⟩
private theorem pole2930_645_33_checked :
    packedBlock 2930 645 pole2930_645_33.length 3813 pole2930_645_33.packed = pole2930_645_33.total := by decide +kernel

private def pole2930_645_34 : Block := ⟨96, 67407717678640476359599166640927263835865903348094518410603880042701784046307930383343632953514302806638099171132041361352439359549202026276542318454389984184113419742013541476994518622968466832075305051867754585958206683850549076975409636777753738643003847194881665913243611186387670961865294674368589498518132463894925120973039748381770100715867034215862101100007182534653393224276448025309980673002276, 4689195720⟩
private theorem pole2930_645_34_checked :
    packedBlock 2930 645 pole2930_645_34.length 3909 pole2930_645_34.packed = pole2930_645_34.total := by decide +kernel

private def pole2930_645_35 : Block := ⟨96, 67970229926306460907767058585652854007008142959598329249783730873248681677354285344689386914575902970982846597056872858103911280033676953279767791542686901605011095455319948852177856148043099445679254600153020192579598622902957376160866751801507734949437614966483084356358466746091462082960753276766454225888457889866513622566628810243201291796898834011893448022390426718913781951906593684927145204206396, 1973885640⟩
private theorem pole2930_645_35_checked :
    packedBlock 2930 645 pole2930_645_35.length 4005 pole2930_645_35.packed = pole2930_645_35.total := by decide +kernel

private def pole2930_645_36 : Block := ⟨96, 68532742173972445455934950530378444178150382571102140088963581703795579308400640306035140875637503135327594022981704354855383200518151880282993264630983819025908771168626356227361193673117732059283204148438285799200990561955365675346323866825261731255871382738084502799473322305795253204056211879164318953258783315838102124160217872104632482877930633807924794944773670903174170679536739344544309735410516, 415561416⟩
private theorem pole2930_645_36_checked :
    packedBlock 2930 645 pole2930_645_36.length 4101 pole2930_645_36.packed = pole2930_645_36.total := by decide +kernel

private def pole2930_645_37 : Block := ⟨23, 1528033208872687388057097482192974092233882950602925882407313205292032880337739517671957694466924, 3568074⟩
private theorem pole2930_645_37_checked :
    packedBlock 2930 645 pole2930_645_37.length 4197 pole2930_645_37.packed = pole2930_645_37.total := by decide +kernel

private def poleBlocks2930_645 : List Block := [pole2930_645_0, pole2930_645_1, pole2930_645_2, pole2930_645_3, pole2930_645_4, pole2930_645_5, pole2930_645_6, pole2930_645_7, pole2930_645_8, pole2930_645_9, pole2930_645_10, pole2930_645_11, pole2930_645_12, pole2930_645_13, pole2930_645_14, pole2930_645_15, pole2930_645_16, pole2930_645_17, pole2930_645_18, pole2930_645_19, pole2930_645_20, pole2930_645_21, pole2930_645_22, pole2930_645_23, pole2930_645_24, pole2930_645_25, pole2930_645_26, pole2930_645_27, pole2930_645_28, pole2930_645_29, pole2930_645_30, pole2930_645_31, pole2930_645_32, pole2930_645_33, pole2930_645_34, pole2930_645_35, pole2930_645_36, pole2930_645_37]
theorem moment2930_645 : P1_7_1.groupedPoleMoment 2930 645 ≤ 2051392203643 := by
  refine grouped_from_blocks 2930 645 _ poleBlocks2930_645 ?_ (by decide) (by decide)
  exact ⟨pole2930_645_0_checked, pole2930_645_1_checked, pole2930_645_2_checked, pole2930_645_3_checked, pole2930_645_4_checked, pole2930_645_5_checked, pole2930_645_6_checked, pole2930_645_7_checked, pole2930_645_8_checked, pole2930_645_9_checked, pole2930_645_10_checked, pole2930_645_11_checked, pole2930_645_12_checked, pole2930_645_13_checked, pole2930_645_14_checked, pole2930_645_15_checked, pole2930_645_16_checked, pole2930_645_17_checked, pole2930_645_18_checked, pole2930_645_19_checked, pole2930_645_20_checked, pole2930_645_21_checked, pole2930_645_22_checked, pole2930_645_23_checked, pole2930_645_24_checked, pole2930_645_25_checked, pole2930_645_26_checked, pole2930_645_27_checked, pole2930_645_28_checked, pole2930_645_29_checked, pole2930_645_30_checked, pole2930_645_31_checked, pole2930_645_32_checked, pole2930_645_33_checked, pole2930_645_34_checked, pole2930_645_35_checked, pole2930_645_36_checked, pole2930_645_37_checked, True.intro⟩

private def pole2930_662_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 434804440⟩
private theorem pole2930_662_0_checked :
    packedBlock 2930 662 pole2930_662_0.length 662 pole2930_662_0.packed = pole2930_662_0.total := by decide +kernel

private def pole2930_662_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 2904123352⟩
private theorem pole2930_662_1_checked :
    packedBlock 2930 662 pole2930_662_1.length 758 pole2930_662_1.packed = pole2930_662_1.total := by decide +kernel

private def pole2930_662_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 7582185688⟩
private theorem pole2930_662_2_checked :
    packedBlock 2930 662 pole2930_662_2.length 854 pole2930_662_2.packed = pole2930_662_2.total := by decide +kernel

private def pole2930_662_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 14214187480⟩
private theorem pole2930_662_3_checked :
    packedBlock 2930 662 pole2930_662_3.length 950 pole2930_662_3.packed = pole2930_662_3.total := by decide +kernel

private def pole2930_662_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 22545324760⟩
private theorem pole2930_662_4_checked :
    packedBlock 2930 662 pole2930_662_4.length 1046 pole2930_662_4.packed = pole2930_662_4.total := by decide +kernel

private def pole2930_662_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 32320793560⟩
private theorem pole2930_662_5_checked :
    packedBlock 2930 662 pole2930_662_5.length 1142 pole2930_662_5.packed = pole2930_662_5.total := by decide +kernel

private def pole2930_662_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 43285416847⟩
private theorem pole2930_662_6_checked :
    packedBlock 2930 662 pole2930_662_6.length 1238 pole2930_662_6.packed = pole2930_662_6.total := by decide +kernel

private def pole2930_662_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 54751399248⟩
private theorem pole2930_662_7_checked :
    packedBlock 2930 662 pole2930_662_7.length 1334 pole2930_662_7.packed = pole2930_662_7.total := by decide +kernel

private def pole2930_662_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 65291508048⟩
private theorem pole2930_662_8_checked :
    packedBlock 2930 662 pole2930_662_8.length 1430 pole2930_662_8.packed = pole2930_662_8.total := by decide +kernel

private def pole2930_662_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 74658456912⟩
private theorem pole2930_662_9_checked :
    packedBlock 2930 662 pole2930_662_9.length 1526 pole2930_662_9.packed = pole2930_662_9.total := by decide +kernel

private def pole2930_662_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 82852245840⟩
private theorem pole2930_662_10_checked :
    packedBlock 2930 662 pole2930_662_10.length 1622 pole2930_662_10.packed = pole2930_662_10.total := by decide +kernel

private def pole2930_662_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 89872874832⟩
private theorem pole2930_662_11_checked :
    packedBlock 2930 662 pole2930_662_11.length 1718 pole2930_662_11.packed = pole2930_662_11.total := by decide +kernel

private def pole2930_662_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 95720343888⟩
private theorem pole2930_662_12_checked :
    packedBlock 2930 662 pole2930_662_12.length 1814 pole2930_662_12.packed = pole2930_662_12.total := by decide +kernel

private def pole2930_662_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 100394653008⟩
private theorem pole2930_662_13_checked :
    packedBlock 2930 662 pole2930_662_13.length 1910 pole2930_662_13.packed = pole2930_662_13.total := by decide +kernel

private def pole2930_662_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 103895802192⟩
private theorem pole2930_662_14_checked :
    packedBlock 2930 662 pole2930_662_14.length 2006 pole2930_662_14.packed = pole2930_662_14.total := by decide +kernel

private def pole2930_662_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 106223791440⟩
private theorem pole2930_662_15_checked :
    packedBlock 2930 662 pole2930_662_15.length 2102 pole2930_662_15.packed = pole2930_662_15.total := by decide +kernel

private def pole2930_662_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 107378620752⟩
private theorem pole2930_662_16_checked :
    packedBlock 2930 662 pole2930_662_16.length 2198 pole2930_662_16.packed = pole2930_662_16.total := by decide +kernel

private def pole2930_662_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 107360290128⟩
private theorem pole2930_662_17_checked :
    packedBlock 2930 662 pole2930_662_17.length 2294 pole2930_662_17.packed = pole2930_662_17.total := by decide +kernel

private def pole2930_662_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 106168799568⟩
private theorem pole2930_662_18_checked :
    packedBlock 2930 662 pole2930_662_18.length 2390 pole2930_662_18.packed = pole2930_662_18.total := by decide +kernel

private def pole2930_662_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 103804149072⟩
private theorem pole2930_662_19_checked :
    packedBlock 2930 662 pole2930_662_19.length 2486 pole2930_662_19.packed = pole2930_662_19.total := by decide +kernel

private def pole2930_662_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 100266338640⟩
private theorem pole2930_662_20_checked :
    packedBlock 2930 662 pole2930_662_20.length 2582 pole2930_662_20.packed = pole2930_662_20.total := by decide +kernel

private def pole2930_662_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 95555368272⟩
private theorem pole2930_662_21_checked :
    packedBlock 2930 662 pole2930_662_21.length 2678 pole2930_662_21.packed = pole2930_662_21.total := by decide +kernel

private def pole2930_662_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 89671237968⟩
private theorem pole2930_662_22_checked :
    packedBlock 2930 662 pole2930_662_22.length 2774 pole2930_662_22.packed = pole2930_662_22.total := by decide +kernel

private def pole2930_662_23 : Block := ⟨96, 53977736334985159844637925322259516942167987572331418607642201441978254568926282621755889100094369055156790901189080053370566111547087048129649775285747969004882522422565306256934040305758600910818105291408455268520947877323255378648369390282646310412761733673984927527657063047841168798749674590206568253603194756421177714612426147004836364989197562670485166266392348567769614043821134702842324848248993, 82620609375⟩
private theorem pole2930_662_23_checked :
    packedBlock 2930 662 pole2930_662_23.length 2870 pole2930_662_23.packed = pole2930_662_23.total := by decide +kernel

private def pole2930_662_24 : Block := ⟨96, 56087157263732601900267520116192196817266306715859953429548841805292602533768572298741002733319458677085620142721279746034514863345568170048171689736609204452154361122442842364987542760650714910869748976282861176396786595809874340171444750336336736876671240283821536208806498916069408927586226798636295489419865839802731101812887326074033075719413435023207123318614075030871433360804791273141761671710976, 74716533227⟩
private theorem pole2930_662_24_checked :
    packedBlock 2930 662 pole2930_662_24.length 2966 pole2930_662_24.packed = pole2930_662_24.total := by decide +kernel

private def pole2930_662_25 : Block := ⟨96, 58032512120244131796340080824340033862120911993010693362961936876491942992472034976337421338943545348013456105858776111482940569986636394571057768621751980851502422843754152305317788224959163167003816896581612995481683249020551859104033974263487294209912399231191744128955020254534708440422917636331793125752373899851480615485580312183641569136743941536221394041564349911950560254661586799575576062904666, 66486020462⟩
private theorem pole2930_662_25_checked :
    packedBlock 2930 662 pole2930_662_25.length 3062 pole2930_662_25.packed = pole2930_662_25.total := by decide +kernel

private def pole2930_662_26 : Block := ⟨96, 59813800904519754861066355650810139973781200305462269881914731626722856772728522941946726228800401320546682670952033092772554915138869550828040145570923689819520119556159141752117707409928515722218896640753500711621442112451172419570761587549443204474209805395388711237277594362244810501824342179425517974333073699142932267151412613700268497899758085940437472721961407483271847108520444421308172989073837, 58134426440⟩
private theorem pole2930_662_26_checked :
    packedBlock 2930 662 pole2930_662_26.length 3158 pole2930_662_26.packed = pole2930_662_26.total := by decide +kernel

private def pole2930_662_27 : Block := ⟨96, 61431023616646768500320684180116927116566431849501123728178852045118354266889594573311304550794824764561892223981155255255806302675670920228983103357955734500930990258802753091178419600790055033347808998258215711045883235312903346135834034078976800498709323193670805058675262406094504148372056434739893835638191080084831438366221800846362083636024920651673587007811597920740836279875201912664470866250233, 49830899902⟩
private theorem pole2930_662_27_checked :
    packedBlock 2930 662 pole2930_662_27.length 3254 pole2930_662_27.packed = pole2930_662_27.total := by decide +kernel

private def pole2930_662_28 : Block := ⟨96, 62884180256450561916746319585074704820647529888542063837137566410160892162170868041496217723101321753884559519777111440248258236282161251606418374312037855213905150911878206826755347736309517068361503000487957298640664588606052363157649222594168381012652660524112743913676884547754160819443043577738808175310506153266961700011221096097002442415411252254225153234295173619370321972683108869540265373698622, 41735366003⟩
private theorem pole2930_662_28_checked :
    packedBlock 2930 662 pole2930_662_28.length 3350 pole2930_662_28.packed = pole2930_662_28.total := by decide +kernel

private def pole2930_662_29 : Block := ⟨96, 64173272254473757144036900888239351789101499944602509150949328614029041475929724174395802803010426514083324138010937171741788574709280783324532574999738578424688684857404247296184352684126914137634765118235281823434754164011933224370467394564123725917630896412343518064819821085586645078704793172631152453303852735269837474868565281677607382554441027997451526192633301738728344368016460112375310786169468, 33998525780⟩
private theorem pole2930_662_29_checked :
    packedBlock 2930 662 pole2930_662_29.length 3446 pole2930_662_29.packed = pole2930_662_29.total := by decide +kernel

private def pole2930_662_30 : Block := ⟨96, 65063916646611566012294664201238497953699750645188529865098445328188324259844003019265570889154003484197080858701914851392617076638649906845321018244557279693753607662922217518791528852434251456711808042247079043579926956235354085569739379789980270763590575310485195170738635621270749561042064180034454371107053228272080424990362343266757648595460029908687160865224909902167608689317094790829914689686195, 26748902123⟩
private theorem pole2930_662_30_checked :
    packedBlock 2930 662 pole2930_662_30.length 3542 pole2930_662_30.packed = pole2930_662_30.total := by decide +kernel

private def pole2930_662_31 : Block := ⟨96, 65626428894277550560462556145964088124841990256692340704278296158735221890890357980611324850215603648541828284626746348144088997123124833848546491332854197114651283376228624893974866377508884070315757590533540739638090510377778502311675242095741256858640152497547130357138919009214927974208069688607322537442057116834962436179748437733580938489090230607362400268176797746871804607447394713821645188238040, 20081324352⟩
private theorem pole2930_662_31_checked :
    packedBlock 2930 662 pole2930_662_31.length 3638 pole2930_662_31.packed = pole2930_662_31.total := by decide +kernel

private def pole2930_662_32 : Block := ⟨96, 66188941141943535108630448090689678295984229868196151543458146989282119521936712941957078811277203812886575710551577844895560917607599760851771964421151114535548959089535032269158203902583516683919707138818806346259482449430186801497132357119495253165073920269148548800253774568918719095303528291005187264812382542806550937773337499595012129570122030403393747190560041931132193335077540373438809719442160, 14218531392⟩
private theorem pole2930_662_32_checked :
    packedBlock 2930 662 pole2930_662_32.length 3734 pole2930_662_32.packed = pole2930_662_32.total := by decide +kernel

private def pole2930_662_33 : Block := ⟨96, 66751453389609519656798340035415268467126469479699962382637997819829017152983067903302832772338803977231323136476409341647032838092074687854997437509448031956446634802841439644341541427658149297523656687104071952880874388482595100682589472143249249471507688040749967243368630128622510216398986893403051992182707968778139439366926561456443320651153830199425094112943286115392582062707686033055974250646280, 9259745088⟩
private theorem pole2930_662_33_checked :
    packedBlock 2930 662 pole2930_662_33.length 3830 pole2930_662_33.packed = pole2930_662_33.total := by decide +kernel

private def pole2930_662_34 : Block := ⟨96, 67313965637275504204966231980140858638268709091203773221817848650375914784029422864648586733400404141576070562401240838398504758576549614858222910597744949377344310516147847019524878952732781911127606235389337559502266327535003399868046587167003245777941455812351385686483485688326301337494445495800916719553033394749727940960515623317874511732185629995456441035326530299652970790337831692673138781850400, 5284591680⟩
private theorem pole2930_662_34_checked :
    packedBlock 2930 662 pole2930_662_34.length 3926 pole2930_662_34.packed = pole2930_662_34.total := by decide +kernel

private def pole2930_662_35 : Block := ⟨96, 67876477884941488753134123924866448809410948702707584060997699480922812415075777825994340694462004305920817988326072335149976679061024541861448383686041866798241986229454254394708216477807414524731555783674603166123658266587411699053503702190757242084375223583952804129598341248030092458589904098198781446923358820721316442554104685179305702813217429791487787957709774483913359517967977352290303313054520, 2372697408⟩
private theorem pole2930_662_35_checked :
    packedBlock 2930 662 pole2930_662_35.length 4022 pole2930_662_35.packed = pole2930_662_35.total := by decide +kernel

private def pole2930_662_36 : Block := ⟨96, 68438990132607473301302015869592038980553188314211394900177550311469710046122132787340094655523604470265565414250903831901448599545499468864673856774338784219139661942760661769891554002882047138335505331959868772745050205639819998238960817214511238390808991355554222572713196807733883579685362700596646174293684246692904944147693747040736893894249229587519134880093018668173748245598123011907467844258640, 603688512⟩
private theorem pole2930_662_36_checked :
    packedBlock 2930 662 pole2930_662_36.length 4118 pole2930_662_36.packed = pole2930_662_36.total := by decide +kernel

private def pole2930_662_37 : Block := ⟨40, 674950247495150891561973230385413882265477077784420898286068472028824093550904053005799336111803321683920925081719937927016113446137756464652911109020016602638026673000, 17325840⟩
private theorem pole2930_662_37_checked :
    packedBlock 2930 662 pole2930_662_37.length 4214 pole2930_662_37.packed = pole2930_662_37.total := by decide +kernel

private def poleBlocks2930_662 : List Block := [pole2930_662_0, pole2930_662_1, pole2930_662_2, pole2930_662_3, pole2930_662_4, pole2930_662_5, pole2930_662_6, pole2930_662_7, pole2930_662_8, pole2930_662_9, pole2930_662_10, pole2930_662_11, pole2930_662_12, pole2930_662_13, pole2930_662_14, pole2930_662_15, pole2930_662_16, pole2930_662_17, pole2930_662_18, pole2930_662_19, pole2930_662_20, pole2930_662_21, pole2930_662_22, pole2930_662_23, pole2930_662_24, pole2930_662_25, pole2930_662_26, pole2930_662_27, pole2930_662_28, pole2930_662_29, pole2930_662_30, pole2930_662_31, pole2930_662_32, pole2930_662_33, pole2930_662_34, pole2930_662_35, pole2930_662_36, pole2930_662_37]
theorem moment2930_662 : P1_7_1.groupedPoleMoment 2930 662 ≤ 2093261903519 := by
  refine grouped_from_blocks 2930 662 _ poleBlocks2930_662 ?_ (by decide) (by decide)
  exact ⟨pole2930_662_0_checked, pole2930_662_1_checked, pole2930_662_2_checked, pole2930_662_3_checked, pole2930_662_4_checked, pole2930_662_5_checked, pole2930_662_6_checked, pole2930_662_7_checked, pole2930_662_8_checked, pole2930_662_9_checked, pole2930_662_10_checked, pole2930_662_11_checked, pole2930_662_12_checked, pole2930_662_13_checked, pole2930_662_14_checked, pole2930_662_15_checked, pole2930_662_16_checked, pole2930_662_17_checked, pole2930_662_18_checked, pole2930_662_19_checked, pole2930_662_20_checked, pole2930_662_21_checked, pole2930_662_22_checked, pole2930_662_23_checked, pole2930_662_24_checked, pole2930_662_25_checked, pole2930_662_26_checked, pole2930_662_27_checked, pole2930_662_28_checked, pole2930_662_29_checked, pole2930_662_30_checked, pole2930_662_31_checked, pole2930_662_32_checked, pole2930_662_33_checked, pole2930_662_34_checked, pole2930_662_35_checked, pole2930_662_36_checked, pole2930_662_37_checked, True.intro⟩

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

private def pole2931_632_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 434956536⟩
private theorem pole2931_632_0_checked :
    packedBlock 2931 632 pole2931_632_0.length 632 pole2931_632_0.packed = pole2931_632_0.total := by decide +kernel

private def pole2931_632_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 2905169400⟩
private theorem pole2931_632_1_checked :
    packedBlock 2931 632 pole2931_632_1.length 728 pole2931_632_1.packed = pole2931_632_1.total := by decide +kernel

private def pole2931_632_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 7585010424⟩
private theorem pole2931_632_2_checked :
    packedBlock 2931 632 pole2931_632_2.length 824 pole2931_632_2.packed = pole2931_632_2.total := by decide +kernel

private def pole2931_632_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 14219675640⟩
private theorem pole2931_632_3_checked :
    packedBlock 2931 632 pole2931_632_3.length 920 pole2931_632_3.packed = pole2931_632_3.total := by decide +kernel

private def pole2931_632_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 22554361080⟩
private theorem pole2931_632_4_checked :
    packedBlock 2931 632 pole2931_632_4.length 1016 pole2931_632_4.packed = pole2931_632_4.total := by decide +kernel

private def pole2931_632_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 32334262776⟩
private theorem pole2931_632_5_checked :
    packedBlock 2931 632 pole2931_632_5.length 1112 pole2931_632_5.packed = pole2931_632_5.total := by decide +kernel

private def pole2931_632_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 43280383890⟩
private theorem pole2931_632_6_checked :
    packedBlock 2931 632 pole2931_632_6.length 1208 pole2931_632_6.packed = pole2931_632_6.total := by decide +kernel

private def pole2931_632_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 54313455984⟩
private theorem pole2931_632_7_checked :
    packedBlock 2931 632 pole2931_632_7.length 1304 pole2931_632_7.packed = pole2931_632_7.total := by decide +kernel

private def pole2931_632_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 64294964592⟩
private theorem pole2931_632_8_checked :
    packedBlock 2931 632 pole2931_632_8.length 1400 pole2931_632_8.packed = pole2931_632_8.total := by decide +kernel

private def pole2931_632_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 73156397424⟩
private theorem pole2931_632_9_checked :
    packedBlock 2931 632 pole2931_632_9.length 1496 pole2931_632_9.packed = pole2931_632_9.total := by decide +kernel

private def pole2931_632_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 80897754480⟩
private theorem pole2931_632_10_checked :
    packedBlock 2931 632 pole2931_632_10.length 1592 pole2931_632_10.packed = pole2931_632_10.total := by decide +kernel

private def pole2931_632_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 87519035760⟩
private theorem pole2931_632_11_checked :
    packedBlock 2931 632 pole2931_632_11.length 1688 pole2931_632_11.packed = pole2931_632_11.total := by decide +kernel

private def pole2931_632_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 93020241264⟩
private theorem pole2931_632_12_checked :
    packedBlock 2931 632 pole2931_632_12.length 1784 pole2931_632_12.packed = pole2931_632_12.total := by decide +kernel

private def pole2931_632_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 97401370992⟩
private theorem pole2931_632_13_checked :
    packedBlock 2931 632 pole2931_632_13.length 1880 pole2931_632_13.packed = pole2931_632_13.total := by decide +kernel

private def pole2931_632_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 100662424944⟩
private theorem pole2931_632_14_checked :
    packedBlock 2931 632 pole2931_632_14.length 1976 pole2931_632_14.packed = pole2931_632_14.total := by decide +kernel

private def pole2931_632_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 102803403120⟩
private theorem pole2931_632_15_checked :
    packedBlock 2931 632 pole2931_632_15.length 2072 pole2931_632_15.packed = pole2931_632_15.total := by decide +kernel

private def pole2931_632_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 103824305520⟩
private theorem pole2931_632_16_checked :
    packedBlock 2931 632 pole2931_632_16.length 2168 pole2931_632_16.packed = pole2931_632_16.total := by decide +kernel

private def pole2931_632_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 103725132144⟩
private theorem pole2931_632_17_checked :
    packedBlock 2931 632 pole2931_632_17.length 2264 pole2931_632_17.packed = pole2931_632_17.total := by decide +kernel

private def pole2931_632_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 102505882992⟩
private theorem pole2931_632_18_checked :
    packedBlock 2931 632 pole2931_632_18.length 2360 pole2931_632_18.packed = pole2931_632_18.total := by decide +kernel

private def pole2931_632_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 100166558064⟩
private theorem pole2931_632_19_checked :
    packedBlock 2931 632 pole2931_632_19.length 2456 pole2931_632_19.packed = pole2931_632_19.total := by decide +kernel

private def pole2931_632_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 96707157360⟩
private theorem pole2931_632_20_checked :
    packedBlock 2931 632 pole2931_632_20.length 2552 pole2931_632_20.packed = pole2931_632_20.total := by decide +kernel

private def pole2931_632_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 92127680880⟩
private theorem pole2931_632_21_checked :
    packedBlock 2931 632 pole2931_632_21.length 2648 pole2931_632_21.packed = pole2931_632_21.total := by decide +kernel

private def pole2931_632_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 86428128624⟩
private theorem pole2931_632_22_checked :
    packedBlock 2931 632 pole2931_632_22.length 2744 pole2931_632_22.packed = pole2931_632_22.total := by decide +kernel

private def pole2931_632_23 : Block := ⟨96, 53977736334985159844963193056109738045137268109938109189084612128091942712753627157152742382555014875371786115384706616432234906416438929713559217141270247816071361888989480688203588386026335310106335641066020084952001598761240453177651487549463103374142917608665822471651449886553155519864457347761852901532662587903000090569718027378991380564400512233052756603468358860181869053236852409099340441225377, 79608522331⟩
private theorem pole2931_632_23_checked :
    packedBlock 2931 632 pole2931_632_23.length 2840 pole2931_632_23.packed = pole2931_632_23.total := by decide +kernel

private def pole2931_632_24 : Block := ⟨96, 56134034714914055980617540590079949241661550630214179452597964850185236823656533875745826880513330929566121480814444984381846219583520356045542103082498203682182097413044382066328693460950499102859818199288709819095759663221338991520830548814087689062454504554495471478051706369518420964541483611030087536519543436466662480958354297123655505637346835287447608290985036929119926852689322452112526924597504, 71823806565⟩
private theorem pole2931_632_24_checked :
    packedBlock 2931 632 pole2931_632_24.length 2936 pole2931_632_24.packed = pole2931_632_24.total := by decide +kernel

private def pole2931_632_25 : Block := ⟨96, 58126264161521801216562679816633295503034608367677759779182738360179089763199688155338300730919699022793237255647290534857962452590215036358795507873883111617382571807749072372699844262393184526588187232876812415848378733862741110302436899105147301214753535101407133792228320035085221226533314968114060331607712075294601266755641127834108773827847820100603980742552615351555560614580441101731917125339484, 63663451014⟩
private theorem pole2931_632_25_checked :
    packedBlock 2931 632 pole2931_632_25.length 3032 pole2931_632_25.packed = pole2931_632_25.total := by decide +kernel

private def pole2931_632_26 : Block := ⟨96, 59954428966436245669247044968819133613523839494653349235506806462740102893821516185725151554442044873526901146392813684675575131290333158681112863424268104185302462134174257019918646343904779744058811059130428683237271412751541065115796079872918158135511076558680843405634275796754218815146538274598302541453345415989668421302015901914716342907241300056026340679710146089947519629044555381048542269049265, 55404907361⟩
private theorem pole2931_632_26_checked :
    packedBlock 2931 632 pole2931_632_26.length 3128 pole2931_632_26.packed = pole2931_632_26.total := by decide +kernel

private def pole2931_632_27 : Block := ⟨96, 61595089688795372596931346810319484958393064410002535290434619323108427183320684875746768430543792526582971354615533128847786072704781897393221553642108861494268961615946881189626156362849040730866801940436204928369970418305549937065873984623911477404162532178410662731979722869208025956791568468312337067435514471959115883474537389671739428746236940529283135751280728272717692439584653511791475704187390, 47219403202⟩
private theorem pole2931_632_27_checked :
    packedBlock 2931 632 pole2931_632_27.length 3224 pole2931_632_27.packed = pole2931_632_27.total := by decide +kernel

private def pole2931_632_28 : Block := ⟨96, 63071684338918582035872083016779401060499636141474472222688612572465669608748815465028969187063320312061736035656102020535009270102437832025595655024388698377606830526781656204919504199698488742795874712428595263091450727515433518325051256952447399043956628005672149186440429297085919312814475907396805696348083123064626507971655502555329003227417593631913906091935719441908133138022267318878169061214788, 39268505662⟩
private theorem pole2931_632_28_checked :
    packedBlock 2931 632 pole2931_632_28.length 3320 pole2931_632_28.packed = pole2931_632_28.total := by decide +kernel

private def pole2931_632_29 : Block := ⟨96, 64360776337029085326759511684925973281138050304783127363964128232088218046671725092471191267454113900511155222168656003321211392916154381680151613344925860617052971176336907984814665182149156356170528211955495911177708741715916858734072904499096199994184925542299533360876899327340418724806164117621676240976249717776745009044638685673150805854107306211097546723190961647718872017582622104948092761606787, 31704120626⟩
private theorem pole2931_632_29_checked :
    packedBlock 2931 632 pole2931_632_29.length 3416 pole2931_632_29.packed = pole2931_632_29.total := by decide +kernel

private def pole2931_632_30 : Block := ⟨96, 65251420729254202258288914186145834846487318170663243527081118525605343127296903031518242769444835509983234038420187290471796997692048139430844671615918467404005662841005646538791724776849041813259844063556393098207695979653414879608186443408116031285231820298075908369238643562757915213174191003892451603334242683425756864969384458259465291738521249285058555174445361923764886774138457441895747087682235, 24657224446⟩
private theorem pole2931_632_30_checked :
    packedBlock 2931 632 pole2931_632_30.length 3512 pole2931_632_30.packed = pole2931_632_30.total := by decide +kernel

private def pole2931_632_31 : Block := ⟨96, 65813932976920186806456806130871425017629557782167054366260969356152240758343257992863996730506435674327981464345018787223268918176523066434070144704215384824903338554312053913975062301923674426864114665059502033864262856535392229283281144210450749108108171842010980324418187100560262785428161967574639437635543756975424366457870739774381725986276934793773284819921324012582291829324368656394681167923936, 18226757320⟩
private theorem pole2931_632_31_checked :
    packedBlock 2931 632 pole2931_632_31.length 3608 pole2931_632_31.packed = pole2931_632_31.total := by decide +kernel

private def pole2931_632_32 : Block := ⟨96, 66376445224586171354624698075597015188771797393670865205440820186699138389389612954209750691568035838672728890269850283974740838660997993437295617792512302245801014267618461289158399826998307040468064213344767640485654795587800528468738259234204745414541939613612398767533042660264053906523620569972504165005869182947012868051459801635812917067308734589804631742304568196842680556954514316011845699128056, 12626386504⟩
private theorem pole2931_632_32_checked :
    packedBlock 2931 632 pole2931_632_32.length 3704 pole2931_632_32.packed = pole2931_632_32.total := by decide +kernel

private def pole2931_632_33 : Block := ⟨96, 66938957472252155902792590020322605359914037005174676044620671017246036020435967915555504652629636003017476316194681780726212759145472920440521090880809219666698689980924868664341737352072939654072013761630033247107046734640208827654195374257958741720975707385213817210647898219967845027619079172370368892376194608918601369645048863497244108148340534385835978664687812381103069284584659975629010230332176, 7954518472⟩
private theorem pole2931_632_33_checked :
    packedBlock 2931 632 pole2931_632_33.length 3800 pole2931_632_33.packed = pole2931_632_33.total := by decide +kernel

private def pole2931_632_34 : Block := ⟨96, 67501469719918140450960481965048195531056276616678486883800521847792933651482322876901258613691236167362223742119513277477684679629947847443746563969106137087596365694231276039525074877147572267675963309915298853728438673692617126839652489281712738027409475156815235653762753779671636148714537774768233619746520034890189871238637925358675299229372334181867325587071056565363458012214805635246174761536296, 4290779464⟩
private theorem pole2931_632_34_checked :
    packedBlock 2931 632 pole2931_632_34.length 3896 pole2931_632_34.packed = pole2931_632_34.total := by decide +kernel

private def pole2931_632_35 : Block := ⟨96, 68063981967584124999128373909773785702198516228182297722980372678339831282528677838247012574752836331706971168044344774229156600114422774446972037057403054508494041407537683414708412402222204881279912858200564460349830612745025426025109604305466734333843242928416654096877609339375427269809996377166098347116845460861778372832226987220106490310404133977898672509454300749623846739844951294863339292740416, 1714795720⟩
private theorem pole2931_632_35_checked :
    packedBlock 2931 632 pole2931_632_35.length 3992 pole2931_632_35.packed = pole2931_632_35.total := by decide +kernel

private def pole2931_632_36 : Block := ⟨96, 68626494215250109547296265854499375873340755839686108562160223508886728913575032799592766535814436496051718593969176270980628520598897701450197510145699971929391717120844090789891749927296837494883862406485830066971222551797433725210566719329220730640277010700018072539992464899079218390905454979563963074487170886833366874425816049081537681391435933773930019431837544933884235467475096954480503823944536, 306193480⟩
private theorem pole2931_632_36_checked :
    packedBlock 2931 632 pole2931_632_36.length 4088 pole2931_632_36.packed = pole2931_632_36.total := by decide +kernel

private def pole2931_632_37 : Block := ⟨11, 4085467118174548250648791076497411258208504688, 471161⟩
private theorem pole2931_632_37_checked :
    packedBlock 2931 632 pole2931_632_37.length 4184 pole2931_632_37.packed = pole2931_632_37.total := by decide +kernel

private def poleBlocks2931_632 : List Block := [pole2931_632_0, pole2931_632_1, pole2931_632_2, pole2931_632_3, pole2931_632_4, pole2931_632_5, pole2931_632_6, pole2931_632_7, pole2931_632_8, pole2931_632_9, pole2931_632_10, pole2931_632_11, pole2931_632_12, pole2931_632_13, pole2931_632_14, pole2931_632_15, pole2931_632_16, pole2931_632_17, pole2931_632_18, pole2931_632_19, pole2931_632_20, pole2931_632_21, pole2931_632_22, pole2931_632_23, pole2931_632_24, pole2931_632_25, pole2931_632_26, pole2931_632_27, pole2931_632_28, pole2931_632_29, pole2931_632_30, pole2931_632_31, pole2931_632_32, pole2931_632_33, pole2931_632_34, pole2931_632_35, pole2931_632_36, pole2931_632_37]
theorem moment2931_632 : P1_7_1.groupedPoleMoment 2931 632 ≤ 2021337557218 := by
  refine grouped_from_blocks 2931 632 _ poleBlocks2931_632 ?_ (by decide) (by decide)
  exact ⟨pole2931_632_0_checked, pole2931_632_1_checked, pole2931_632_2_checked, pole2931_632_3_checked, pole2931_632_4_checked, pole2931_632_5_checked, pole2931_632_6_checked, pole2931_632_7_checked, pole2931_632_8_checked, pole2931_632_9_checked, pole2931_632_10_checked, pole2931_632_11_checked, pole2931_632_12_checked, pole2931_632_13_checked, pole2931_632_14_checked, pole2931_632_15_checked, pole2931_632_16_checked, pole2931_632_17_checked, pole2931_632_18_checked, pole2931_632_19_checked, pole2931_632_20_checked, pole2931_632_21_checked, pole2931_632_22_checked, pole2931_632_23_checked, pole2931_632_24_checked, pole2931_632_25_checked, pole2931_632_26_checked, pole2931_632_27_checked, pole2931_632_28_checked, pole2931_632_29_checked, pole2931_632_30_checked, pole2931_632_31_checked, pole2931_632_32_checked, pole2931_632_33_checked, pole2931_632_34_checked, pole2931_632_35_checked, pole2931_632_36_checked, pole2931_632_37_checked, True.intro⟩

private def pole3322_747_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 494426072⟩
private theorem pole3322_747_0_checked :
    packedBlock 3322 747 pole3322_747_0.length 747 pole3322_747_0.packed = pole3322_747_0.total := by decide +kernel

private def pole3322_747_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 3314174168⟩
private theorem pole3322_747_1_checked :
    packedBlock 3322 747 pole3322_747_1.length 843 pole3322_747_1.packed = pole3322_747_1.total := by decide +kernel

private def pole3322_747_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 8689482200⟩
private theorem pole3322_747_2_checked :
    packedBlock 3322 747 pole3322_747_2.length 939 pole3322_747_2.packed = pole3322_747_2.total := by decide +kernel

private def pole3322_747_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 16365546200⟩
private theorem pole3322_747_3_checked :
    packedBlock 3322 747 pole3322_747_3.length 1035 pole3322_747_3.packed = pole3322_747_3.total := by decide +kernel

private def pole3322_747_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 26087562200⟩
private theorem pole3322_747_4_checked :
    packedBlock 3322 747 pole3322_747_4.length 1131 pole3322_747_4.packed = pole3322_747_4.total := by decide +kernel

private def pole3322_747_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 37600726232⟩
private theorem pole3322_747_5_checked :
    packedBlock 3322 747 pole3322_747_5.length 1227 pole3322_747_5.packed = pole3322_747_5.total := by decide +kernel

private def pole3322_747_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 50650234328⟩
private theorem pole3322_747_6_checked :
    packedBlock 3322 747 pole3322_747_6.length 1323 pole3322_747_6.packed = pole3322_747_6.total := by decide +kernel

private def pole3322_747_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 64977340505⟩
private theorem pole3322_747_7_checked :
    packedBlock 3322 747 pole3322_747_7.length 1419 pole3322_747_7.packed = pole3322_747_7.total := by decide +kernel

private def pole3322_747_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 79678988576⟩
private theorem pole3322_747_8_checked :
    packedBlock 3322 747 pole3322_747_8.length 1515 pole3322_747_8.packed = pole3322_747_8.total := by decide +kernel

private def pole3322_747_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 93242083616⟩
private theorem pole3322_747_9_checked :
    packedBlock 3322 747 pole3322_747_9.length 1611 pole3322_747_9.packed = pole3322_747_9.total := by decide +kernel

private def pole3322_747_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 105481613600⟩
private theorem pole3322_747_10_checked :
    packedBlock 3322 747 pole3322_747_10.length 1707 pole3322_747_10.packed = pole3322_747_10.total := by decide +kernel

private def pole3322_747_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 116397578528⟩
private theorem pole3322_747_11_checked :
    packedBlock 3322 747 pole3322_747_11.length 1803 pole3322_747_11.packed = pole3322_747_11.total := by decide +kernel

private def pole3322_747_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 125989978400⟩
private theorem pole3322_747_12_checked :
    packedBlock 3322 747 pole3322_747_12.length 1899 pole3322_747_12.packed = pole3322_747_12.total := by decide +kernel

private def pole3322_747_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 134258813216⟩
private theorem pole3322_747_13_checked :
    packedBlock 3322 747 pole3322_747_13.length 1995 pole3322_747_13.packed = pole3322_747_13.total := by decide +kernel

private def pole3322_747_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 141204082976⟩
private theorem pole3322_747_14_checked :
    packedBlock 3322 747 pole3322_747_14.length 2091 pole3322_747_14.packed = pole3322_747_14.total := by decide +kernel

private def pole3322_747_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 146825787680⟩
private theorem pole3322_747_15_checked :
    packedBlock 3322 747 pole3322_747_15.length 2187 pole3322_747_15.packed = pole3322_747_15.total := by decide +kernel

private def pole3322_747_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 151123927328⟩
private theorem pole3322_747_16_checked :
    packedBlock 3322 747 pole3322_747_16.length 2283 pole3322_747_16.packed = pole3322_747_16.total := by decide +kernel

private def pole3322_747_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 154098501920⟩
private theorem pole3322_747_17_checked :
    packedBlock 3322 747 pole3322_747_17.length 2379 pole3322_747_17.packed = pole3322_747_17.total := by decide +kernel

private def pole3322_747_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 155749511456⟩
private theorem pole3322_747_18_checked :
    packedBlock 3322 747 pole3322_747_18.length 2475 pole3322_747_18.packed = pole3322_747_18.total := by decide +kernel

private def pole3322_747_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 156076955936⟩
private theorem pole3322_747_19_checked :
    packedBlock 3322 747 pole3322_747_19.length 2571 pole3322_747_19.packed = pole3322_747_19.total := by decide +kernel

private def pole3322_747_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 155080835360⟩
private theorem pole3322_747_20_checked :
    packedBlock 3322 747 pole3322_747_20.length 2667 pole3322_747_20.packed = pole3322_747_20.total := by decide +kernel

private def pole3322_747_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 152761149728⟩
private theorem pole3322_747_21_checked :
    packedBlock 3322 747 pole3322_747_21.length 2763 pole3322_747_21.packed = pole3322_747_21.total := by decide +kernel

private def pole3322_747_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 149117899040⟩
private theorem pole3322_747_22_checked :
    packedBlock 3322 747 pole3322_747_22.length 2859 pole3322_747_22.packed = pole3322_747_22.total := by decide +kernel

private def pole3322_747_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 144151083296⟩
private theorem pole3322_747_23_checked :
    packedBlock 3322 747 pole3322_747_23.length 2955 pole3322_747_23.packed = pole3322_747_23.total := by decide +kernel

private def pole3322_747_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 137860702496⟩
private theorem pole3322_747_24_checked :
    packedBlock 3322 747 pole3322_747_24.length 3051 pole3322_747_24.packed = pole3322_747_24.total := by decide +kernel

private def pole3322_747_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 130246756640⟩
private theorem pole3322_747_25_checked :
    packedBlock 3322 747 pole3322_747_25.length 3147 pole3322_747_25.packed = pole3322_747_25.total := by decide +kernel

private def pole3322_747_26 : Block := ⟨96, 60727883306976974422652628658966598995874862910377148677800411408541027010846662524436595237391986057048091722558170777802117332361555997298881941921022845211361654497311235322576226173015236439890433226537135012370500867951187806129497118756540218446371510646643116956195405018778067928019477692168705734565672221899183694614799718969474777369256006617955111735343677545638886436179305147992961415416257, 121310065664⟩
private theorem pole3322_747_26_checked :
    packedBlock 3322 747 pole3322_747_26.length 3243 pole3322_747_26.packed = pole3322_747_26.total := by decide +kernel

private def pole3322_747_27 : Block := ⟨96, 62884180256363248524288148847598249088222728625415114142765583611751155204320914045324850614709894843891382402013477604125749152287027879907638530079095131970792096140552382150592801265492789124497150608364510747758345670778067747162568349266564861075964151020678283605123847075931289448501841138211515061670962267146654962883248929074041199665965252422931294929374120008599582349859131293423823938406944, 111285383040⟩
private theorem pole3322_747_27_checked :
    packedBlock 3322 747 pole3322_747_27.length 3339 pole3322_747_27.packed = pole3322_747_27.total := by decide +kernel

private def pole3322_747_28 : Block := ⟨96, 64899849143833026488231180435115018063505590139740308706055942332495643352236116504691107533783750926676548774274947501338231271213206932374359994258654795274737963717794514709368413128199611462235425548028240606589525382163208952993409692029888748534909406823280727538965547449591534616602380989594464656117448594009759793758658589783319744032313590459555805580148930101298756605214701443892752632728188, 100802967777⟩
private theorem pole3322_747_28_checked :
    packedBlock 3322 747 pole3322_747_28.length 3435 pole3322_747_28.packed = pole3322_747_28.total := by decide +kernel

private def pole3322_747_29 : Block := ⟨96, 66751453389609514327286501047987180455286243897738879581095705882404613702017598285593641185837570976762420467603420617515080783665346301928907062903748872161377040818728572816487201323262467852424564552690862684791866518825544398233192804934899516728194279503763701377793521045793934346982263485253194556053839894635544425855329833676468598443428927923468968920475646047394530001584448218913460702202578, 90114315407⟩
private theorem pole3322_747_29_checked :
    packedBlock 3322 747 pole3322_747_29.length 3531 pole3322_747_29.packed = pole3322_747_29.total := by decide +kernel

private def pole3322_747_30 : Block := ⟨96, 68485864722703683311988023131996321778890727649479353652604098597668438043743793484387676726175590181222535630361249106547954772490688883170640987366485330750965891742054848637325513836049631782925847667922749531785463272830773889548447297557252540326974982113274414028432845381036256630275753024688194581120894662763415056101973398748229283114271765931111401789752091724559357032369750278501942352710433, 79392687211⟩
private theorem pole3322_747_30_checked :
    packedBlock 3322 747 pole3322_747_30.length 3627 pole3322_747_30.packed = pole3322_747_30.total := by decide +kernel

private def pole3322_747_31 : Block := ⟨96, 70056211414191864905561693999242643078594493637842035773644123239351549731450431592167265253049886271739703221009408611847485510464999879968070204580599527313855167100288855435636798449688708075645021148203924925169935864807462292869992189498060638515419947925117535155672940760000359734445725004806089951791504941769382040357948557919646074086065471564675043860847020267462927415620794187145232023997290, 68803169531⟩
private theorem pole3322_747_31_checked :
    packedBlock 3322 747 pole3322_747_31.length 3723 pole3322_747_31.packed = pole3322_747_31.total := by decide +kernel

private def pole3322_747_32 : Block := ⟨96, 71485930043676242299147000573170187854364277281121171252929452027273868436921379325408372044335002542651360465775352977369286079317586370720008197347799976664827084945015130989835477452458687555171619999476030763786560951358236795713681912020462637546708141279110786101414779692324021862511693372726841211171286911515369079765291974056155895565616763700104538709952605987082090008566189819286113160498094, 58502672747⟩
private theorem pole3322_747_32_checked :
    packedBlock 3322 747 pole3322_747_32.length 3819 pole3322_747_32.packed = pole3322_747_32.total := by decide +kernel

private def pole3322_747_33 : Block := ⟨96, 72775020611244123555365086281044641443740402787396493344414485551468001258682578778895374504085604457317919952854058693971462388932845727328305918031478684685446485733520345200712712050081938422025780651769587657688828459027757593921207980485493292789182775607627881431198917198518444843600093036905982275375604223230136965474822375991215668882668992536055702981177315734612105355683996351758509308300267, 48639931918⟩
private theorem pole3322_747_33_checked :
    packedBlock 3322 747 pole3322_747_33.length 3915 pole3322_747_33.packed = pole3322_747_33.total := by decide +kernel

private def pole3322_747_34 : Block := ⟨96, 73712541024020769798164790924276583401656612253829913300929654594200013343361138698458084033236559738777818145600304832701319721089877235249092856814321281599556296306731560194144210291324137010835745868345944610567515440471528831485471944275388694154417139907053983485837626172498096572470085733086099417948531970445842860622188042957935753810967590369722727180352986285314462685945210555069895476284449, 39343769129⟩
private theorem pole3322_747_34_checked :
    packedBlock 3322 747 pole3322_747_34.length 4011 pole3322_747_34.packed = pole3322_747_34.total := by decide +kernel

private def pole3322_747_35 : Block := ⟨96, 74275053271686754346332682869002173572798851865333724140109505424746910974407493659803837994298159903122565571525136329452791641574352162252318329902618199020453972020139719605475992154533072578563972564000221134796115271851111351006768987914129762989647448929414332347765911366666412107056760995492964362479624852655206674546446806602528037994662048374607855526525077986655609226521971503021951764548681, 30684285956⟩
private theorem pole3322_747_35_checked :
    packedBlock 3322 747 pole3322_747_35.length 4107 pole3322_747_35.packed = pole3322_747_35.total := by decide +kernel

private def pole3322_747_36 : Block := ⟨96, 74837565519352738894500574813727763743941091476837534979289356255293808605453848621149591955359760067467312997449967826204263562058827089255543802990915116441351647733446126980659329679607705192167922112285486741417507210903519650192226102937883759296081216701015750790880766926370203228152219597890829089849950278626795176140035868463959229075693848170639202448908322170915997954152117162639116295752801, 22911675716⟩
private theorem pole3322_747_36_checked :
    packedBlock 3322 747 pole3322_747_36.length 4203 pole3322_747_36.packed = pole3322_747_36.total := by decide +kernel

private def pole3322_747_37 : Block := ⟨96, 75400077767018723442668466758453353915083331088341345818469207085840706236500203582495345916421360231812060423374799322955735482543302016258769276079212033862249323446752534355842667204682337805771871660570752348038899149955927949377683217961637755602514984472617169233995622486073994349247678200288693817220275704598383677733624930325390420156725647966670549371291566355176386681782262822256280826956921, 16139342468⟩
private theorem pole3322_747_37_checked :
    packedBlock 3322 747 pole3322_747_37.length 4299 pole3322_747_37.packed = pole3322_747_37.total := by decide +kernel

private def pole3322_747_38 : Block := ⟨96, 75962590014684707990836358703178944086225570699845156657649057916387603867546558543841099877482960396156807849299630819707207403027776943261994749167508951283146999160058941731026004729756970419375821208856017954660291089008336248563140332985391751908948752244218587677110478045777785470343136802686558544590601130569972179327213992186821611237757447762701896293674810539436775409412408481873445358161041, 10446912452⟩
private theorem pole3322_747_38_checked :
    packedBlock 3322 747 pole3322_747_38.length 4395 pole3322_747_38.packed = pole3322_747_38.total := by decide +kernel

private def pole3322_747_39 : Block := ⟨96, 76525102262350692539004250647904534257367810311348967496828908746934501498592913505186853838544560560501555275224462316458679323512251870265220222255805868704044674873365349106209342254831603032979770757141283561281683028060744547748597448009145748215382520015820006120225333605481576591438595405084423271960926556541560680920803054048252802318789247558733243216058054723697164137042554141490609889365161, 5914011908⟩
private theorem pole3322_747_39_checked :
    packedBlock 3322 747 pole3322_747_39.length 4491 pole3322_747_39.packed = pole3322_747_39.total := by decide +kernel

private def pole3322_747_40 : Block := ⟨96, 77087614510016677087172142592630124428510049922852778336008759577481399129639268466532607799606160724846302701149293813210151243996726797268445695344102786124942350586671756481392679779906235646583720305426549167903074967113152846934054563032899744521816287787421424563340189165185367712534054007482287999331251982513149182514392115909683993399821047354764590138441298907957552864672699801107774420569281, 2620267076⟩
private theorem pole3322_747_40_checked :
    packedBlock 3322 747 pole3322_747_40.length 4587 pole3322_747_40.packed = pole3322_747_40.total := by decide +kernel

private def pole3322_747_41 : Block := ⟨96, 77650126757682661635340034537355714599652289534356589175188610408028296760685623427878361760667760889191050127074125309961623164481201724271671168432399703545840026299978163856576017304980868260187669853711814774524466906165561146119511678056653740828250055559022843006455044724889158833629512609880152726701577408484737684107981177771115184480852847150795937060824543092217941592302845460724938951773401, 645304196⟩
private theorem pole3322_747_41_checked :
    packedBlock 3322 747 pole3322_747_41.length 4683 pole3322_747_41.packed = pole3322_747_41.total := by decide +kernel

private def pole3322_747_42 : Block := ⟨37, 173997877578345786097217281983107554343031909156962096867973444148051388129452653111460455820595437205709523505326988822330455622803877221482903189596163313, 15700225⟩
private theorem pole3322_747_42_checked :
    packedBlock 3322 747 pole3322_747_42.length 4779 pole3322_747_42.packed = pole3322_747_42.total := by decide +kernel

private def poleBlocks3322_747 : List Block := [pole3322_747_0, pole3322_747_1, pole3322_747_2, pole3322_747_3, pole3322_747_4, pole3322_747_5, pole3322_747_6, pole3322_747_7, pole3322_747_8, pole3322_747_9, pole3322_747_10, pole3322_747_11, pole3322_747_12, pole3322_747_13, pole3322_747_14, pole3322_747_15, pole3322_747_16, pole3322_747_17, pole3322_747_18, pole3322_747_19, pole3322_747_20, pole3322_747_21, pole3322_747_22, pole3322_747_23, pole3322_747_24, pole3322_747_25, pole3322_747_26, pole3322_747_27, pole3322_747_28, pole3322_747_29, pole3322_747_30, pole3322_747_31, pole3322_747_32, pole3322_747_33, pole3322_747_34, pole3322_747_35, pole3322_747_36, pole3322_747_37, pole3322_747_38, pole3322_747_39, pole3322_747_40, pole3322_747_41, pole3322_747_42]
theorem moment3322_747 : P1_7_1.groupedPoleMoment 3322 747 ≤ 3445098204118 := by
  refine grouped_from_blocks 3322 747 _ poleBlocks3322_747 ?_ (by decide) (by decide)
  exact ⟨pole3322_747_0_checked, pole3322_747_1_checked, pole3322_747_2_checked, pole3322_747_3_checked, pole3322_747_4_checked, pole3322_747_5_checked, pole3322_747_6_checked, pole3322_747_7_checked, pole3322_747_8_checked, pole3322_747_9_checked, pole3322_747_10_checked, pole3322_747_11_checked, pole3322_747_12_checked, pole3322_747_13_checked, pole3322_747_14_checked, pole3322_747_15_checked, pole3322_747_16_checked, pole3322_747_17_checked, pole3322_747_18_checked, pole3322_747_19_checked, pole3322_747_20_checked, pole3322_747_21_checked, pole3322_747_22_checked, pole3322_747_23_checked, pole3322_747_24_checked, pole3322_747_25_checked, pole3322_747_26_checked, pole3322_747_27_checked, pole3322_747_28_checked, pole3322_747_29_checked, pole3322_747_30_checked, pole3322_747_31_checked, pole3322_747_32_checked, pole3322_747_33_checked, pole3322_747_34_checked, pole3322_747_35_checked, pole3322_747_36_checked, pole3322_747_37_checked, pole3322_747_38_checked, pole3322_747_39_checked, pole3322_747_40_checked, pole3322_747_41_checked, pole3322_747_42_checked, True.intro⟩

private def pole3544_792_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 528191384⟩
private theorem pole3544_792_0_checked :
    packedBlock 3544 792 pole3544_792_0.length 792 pole3544_792_0.packed = pole3544_792_0.total := by decide +kernel

private def pole3544_792_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 3546396824⟩
private theorem pole3544_792_1_checked :
    packedBlock 3544 792 pole3544_792_1.length 888 pole3544_792_1.packed = pole3544_792_1.total := by decide +kernel

private def pole3544_792_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 9316573592⟩
private theorem pole3544_792_2_checked :
    packedBlock 3544 792 pole3544_792_2.length 984 pole3544_792_2.packed = pole3544_792_2.total := by decide +kernel

private def pole3544_792_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 17583917720⟩
private theorem pole3544_792_3_checked :
    packedBlock 3544 792 pole3544_792_3.length 1080 pole3544_792_3.packed = pole3544_792_3.total := by decide +kernel

private def pole3544_792_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 28093625240⟩
private theorem pole3544_792_4_checked :
    packedBlock 3544 792 pole3544_792_4.length 1176 pole3544_792_4.packed = pole3544_792_4.total := by decide +kernel

private def pole3544_792_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 40590892184⟩
private theorem pole3544_792_5_checked :
    packedBlock 3544 792 pole3544_792_5.length 1272 pole3544_792_5.packed = pole3544_792_5.total := by decide +kernel

private def pole3544_792_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 54820914584⟩
private theorem pole3544_792_6_checked :
    packedBlock 3544 792 pole3544_792_6.length 1368 pole3544_792_6.packed = pole3544_792_6.total := by decide +kernel

private def pole3544_792_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 70528888472⟩
private theorem pole3544_792_7_checked :
    packedBlock 3544 792 pole3544_792_7.length 1464 pole3544_792_7.packed = pole3544_792_7.total := by decide +kernel

private def pole3544_792_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 87292173974⟩
private theorem pole3544_792_8_checked :
    packedBlock 3544 792 pole3544_792_8.length 1560 pole3544_792_8.packed = pole3544_792_8.total := by decide +kernel

private def pole3544_792_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 103451734880⟩
private theorem pole3544_792_9_checked :
    packedBlock 3544 792 pole3544_792_9.length 1656 pole3544_792_9.packed = pole3544_792_9.total := by decide +kernel

private def pole3544_792_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 118214476640⟩
private theorem pole3544_792_10_checked :
    packedBlock 3544 792 pole3544_792_10.length 1752 pole3544_792_10.packed = pole3544_792_10.total := by decide +kernel

private def pole3544_792_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 131574027104⟩
private theorem pole3544_792_11_checked :
    packedBlock 3544 792 pole3544_792_11.length 1848 pole3544_792_11.packed = pole3544_792_11.total := by decide +kernel

private def pole3544_792_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 143530386272⟩
private theorem pole3544_792_12_checked :
    packedBlock 3544 792 pole3544_792_12.length 1944 pole3544_792_12.packed = pole3544_792_12.total := by decide +kernel

private def pole3544_792_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 154083554144⟩
private theorem pole3544_792_13_checked :
    packedBlock 3544 792 pole3544_792_13.length 2040 pole3544_792_13.packed = pole3544_792_13.total := by decide +kernel

private def pole3544_792_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 163233530720⟩
private theorem pole3544_792_14_checked :
    packedBlock 3544 792 pole3544_792_14.length 2136 pole3544_792_14.packed = pole3544_792_14.total := by decide +kernel

private def pole3544_792_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 170980316000⟩
private theorem pole3544_792_15_checked :
    packedBlock 3544 792 pole3544_792_15.length 2232 pole3544_792_15.packed = pole3544_792_15.total := by decide +kernel

private def pole3544_792_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 177323909984⟩
private theorem pole3544_792_16_checked :
    packedBlock 3544 792 pole3544_792_16.length 2328 pole3544_792_16.packed = pole3544_792_16.total := by decide +kernel

private def pole3544_792_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 182264312672⟩
private theorem pole3544_792_17_checked :
    packedBlock 3544 792 pole3544_792_17.length 2424 pole3544_792_17.packed = pole3544_792_17.total := by decide +kernel

private def pole3544_792_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 185801524064⟩
private theorem pole3544_792_18_checked :
    packedBlock 3544 792 pole3544_792_18.length 2520 pole3544_792_18.packed = pole3544_792_18.total := by decide +kernel

private def pole3544_792_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 187935544160⟩
private theorem pole3544_792_19_checked :
    packedBlock 3544 792 pole3544_792_19.length 2616 pole3544_792_19.packed = pole3544_792_19.total := by decide +kernel

private def pole3544_792_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 188666372960⟩
private theorem pole3544_792_20_checked :
    packedBlock 3544 792 pole3544_792_20.length 2712 pole3544_792_20.packed = pole3544_792_20.total := by decide +kernel

private def pole3544_792_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 187994010464⟩
private theorem pole3544_792_21_checked :
    packedBlock 3544 792 pole3544_792_21.length 2808 pole3544_792_21.packed = pole3544_792_21.total := by decide +kernel

private def pole3544_792_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 185918456672⟩
private theorem pole3544_792_22_checked :
    packedBlock 3544 792 pole3544_792_22.length 2904 pole3544_792_22.packed = pole3544_792_22.total := by decide +kernel

private def pole3544_792_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 182439711584⟩
private theorem pole3544_792_23_checked :
    packedBlock 3544 792 pole3544_792_23.length 3000 pole3544_792_23.packed = pole3544_792_23.total := by decide +kernel

private def pole3544_792_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 177557775200⟩
private theorem pole3544_792_24_checked :
    packedBlock 3544 792 pole3544_792_24.length 3096 pole3544_792_24.packed = pole3544_792_24.total := by decide +kernel

private def pole3544_792_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 171272647520⟩
private theorem pole3544_792_25_checked :
    packedBlock 3544 792 pole3544_792_25.length 3192 pole3544_792_25.packed = pole3544_792_25.total := by decide +kernel

private def pole3544_792_26 : Block := ⟨96, 60751321317296390445492957489996831919672456227523140796099571859813813542776140281294343047877804367474791155033925993419540487380972627460156513723982684274612050299834592232817566018256040710515759530467324843312310583624970845569473039502920095891291642435743249636271632958193880986061667720339402158813292431294693811722611881330958539315090095707759056013525282113849158466604898998563280201484737, 163584328544⟩
private theorem pole3544_792_26_checked :
    packedBlock 3544 792 pole3544_792_26.length 3288 pole3544_792_26.packed = pole3544_792_26.total := by decide +kernel

private def pole3544_792_27 : Block := ⟨96, 63001370307960328638164525268899192604241414673538384152818975182001404066961560126677358892124205024853780858733251980425428169318872335473058406077170353958202753153060221733550916118554571164931557723608387269797878339834604042311301499597936081117026713522148923408731055197009045470443502129930861068294594135181047818096968128776683303639217294891884443703058258850890713377125481637031938326301217, 154492818272⟩
private theorem pole3544_792_27_checked :
    packedBlock 3544 792 pole3544_792_27.length 3384 pole3544_792_27.packed = pole3544_792_27.total := by decide +kernel

private def pole3544_792_28 : Block := ⟨96, 65227981288304850807995764216771320365012779802407635391239218052916207189853381848670968321326372342051739419685709988400004521236586116520936880141430327461643043769472411599303203534177796328521212778424433517645693619692214603402455094414582991879451979179593202670729086637690799492027941653296891014202548595173228289093792118130410794283256856217240530494992338330623390259838719858679090109254273, 144003816056⟩
private theorem pole3544_792_28_checked :
    packedBlock 3544 792 pole3544_792_28.length 3480 pole3544_792_28.packed = pole3544_792_28.total := by decide +kernel

private def pole3544_792_29 : Block := ⟨96, 67360840227371714215652239242545067479286099810711404508919500405406410044147799385682790530131139730761494501067418046044758867535551243977655316174085648964234743611631390842637678074547896434319036690852308348616900934358887832391341291912957181643319547102669515782964201659430653064455807422306363240692073869313518540114723103131938019521183345817693487373379454012360810041354259902205121244187360, 132466239379⟩
private theorem pole3544_792_29_checked :
    packedBlock 3544 792 pole3544_792_29.length 3576 pole3544_792_29.packed = pole3544_792_29.total := by decide +kernel

private def pole3544_792_30 : Block := ⟨96, 69376509114841486850733967310334264610501717537637484505172817910331213147814459401560686814231999333639776335974460276338274169112997663758764707702858663457402061105770093610654562185711460581733377920402150737524966785626312400482070521895680903369443944147952878241124212068538445485316197640456462735960026466701338914723385365037885031545719238198707467890204718264902853020275893245991982677822267, 120508609329⟩
private theorem pole3544_792_30_checked :
    packedBlock 3544 792 pole3544_792_30.length 3672 pole3544_792_30.packed = pole3544_792_30.total := by decide +kernel

private def pole3544_792_31 : Block := ⟨96, 71228111930162666047578115697987404589621194742421317490063820620894359388386820792951821318248656990866594754434777567436705973189664617572951145234982371605168165761043929532654451179792321409902754472246138108816099364165384044693376601036820021635656919448196845430447643917443824801212327915036492910167098769538209508398300462378509178626529505867013424540771518713166573797054384307208771785214865, 108351961583⟩
private theorem pole3544_792_31_checked :
    packedBlock 3544 792 pole3544_792_31.length 3768 pole3544_792_31.packed = pole3544_792_31.total := by decide +kernel

private def pole3544_792_32 : Block := ⟨96, 72962524693712143674490829859982453000225823225808712665523614919942012999509655567103482131978335604258556624240175391570188694000858955168035644659778024330129800787467525075529829748769677940789520793490993137641442926489382750547639295887990690968606361524601308162553976600255756128440817215480532068235812875964247440626887015337747828636985029647137366965988752471247565193500089147988587012705248, 96169364943⟩
private theorem pole3544_792_32_checked :
    packedBlock 3544 792 pole3544_792_32.length 3864 pole3544_792_32.packed = pole3544_792_32.total := by decide +kernel

private def pole3544_792_33 : Block := ⟨96, 74556309395519741290904809705492122544874493274269391242330220765756177221008818193945977657160230080849652420864762933253360566758685284534556518753358191808047678949423952103049624863370135030878124871191760486383126076539437922777553044805165456455849047389434798496955823488567192844924528706570246249768957746616210687276181832382236206810966446052670088205992185881317135634171426559522741850639402, 84126177217⟩
private theorem pole3544_792_33_checked :
    packedBlock 3544 792 pole3544_792_33.length 3960 pole3544_792_33.packed = pole3544_792_33.total := by decide +kernel

private def pole3544_792_34 : Block := ⟨96, 76009466035323534707005217080921879675989348234396220239575803099651615519198799063526778582231055473989770694860083335860506841323232780399779330087420826140519866113496811332778423235166934441335275374318120914170782589147037148070988828931988723485553977209863422990141432703901183655519592148716772042080594912604416044425492971918325905275584819952918358676504960525808210576266858295930883342568558, 72380044173⟩
private theorem pole3544_792_34_checked :
    packedBlock 3544 792 pole3544_792_34.length 4056 pole3544_792_34.packed = pole3544_792_34.total := by decide +kernel

private def pole3544_792_35 : Block := ⟨96, 77321996043666145957461355244644780141207154686516768783399857552585740543150759665556554054101305804187565574620969244013420537920445839597092532374881336889654375376392643126358059510756210859961032379043527371107044030220978157941530588185711643925120887694965269352600061947684686527350676404405136373898752608284965875178624199173666281675156184520359779339880126266398948006045283563118007966960812, 61080900136⟩
private theorem pole3544_792_35_checked :
    packedBlock 3544 792 pole3544_792_35.length 4152 pole3544_792_35.packed = pole3544_792_35.total := by decide +kernel

private def pole3544_792_36 : Block := ⟨96, 78470458549317531076962755550531730365922852557023692996208654017445678898710836236567233231648854164814138952345974212725669067064755000291725832234897729549618827073654999431631375531579431441069766789339409994967482284580626650621843865437552734935459343897113631768453009070444727886137046366018185819057852213824507774029617009211090537020561436081454403519689425215679477673628992490095528164003044, 50370271856⟩
private theorem pole3544_792_36_checked :
    packedBlock 3544 792 pole3544_792_36.length 4248 pole3544_792_36.packed = pole3544_792_36.total := by decide +kernel

private def pole3544_792_37 : Block := ⟨96, 79032970796983515625130647495257320537065367664199832371398074286769615430828484559351794255517074232091641935835230354054169768669777260758753599937264062312712554543364667335844410725120961361209888491332371030781265057793509632898403150161878168828644951054047603251376309848821949693649833045756431873101479769157821724160287745431024325920348125746109501918310784138411069282632532934697399848602900, 40303288400⟩
private theorem pole3544_792_37_checked :
    packedBlock 3544 792 pole3544_792_37.length 4344 pole3544_792_37.packed = pole3544_792_37.total := by decide +kernel

private def pole3544_792_38 : Block := ⟨96, 79595483044649500173298539439982910708207607275703643210577925117316513061874839520697548216578674396436389361760061850805641689154252187761979073025560979733610230256671074711027748250195593974813838039617636637402656996845917932083860265185632165135078718825649021694491165408525740814745291648154296600471805195129410225753876807292455517001379925542140848840694028322671458010262678594314564379807020, 31099273808⟩
private theorem pole3544_792_38_checked :
    packedBlock 3544 792 pole3544_792_38.length 4440 pole3544_792_38.packed = pole3544_792_38.total := by decide +kernel

private def pole3544_792_39 : Block := ⟨96, 80157995292315484721466431384708500879349846887207454049757775947863410692921194482043302177640274560781136787684893347557113609638727114765204546113857897154507905969977482086211085775270226588417787587902902244024048935898326231269317380209386161441512486597250440137606020968229531935840750250552161327842130621100998727347465869153886708082411725338172195763077272506931846737892824253931728911011140, 22931533904⟩
private theorem pole3544_792_39_checked :
    packedBlock 3544 792 pole3544_792_39.length 4536 pole3544_792_39.packed = pole3544_792_39.total := by decide +kernel

private def pole3544_792_40 : Block := ⟨96, 80720507539981469269634323329434091050492086498711264888937626778410308323967549443389056138701874725125884213609724844308585530123202041768430019202154814575405581683283889461394423300344859202021737136188167850645440874950734530454774495233140157747946254368851858580720876527933323056936208852950026055212456047072587228941054931015317899163443525134203542685460516691192235465522969913548893442215260, 15879694928⟩
private theorem pole3544_792_40_checked :
    packedBlock 3544 792 pole3544_792_40.length 4632 pole3544_792_40.packed = pole3544_792_40.total := by decide +kernel

private def pole3544_792_41 : Block := ⟨96, 81283019787647453817802215274159681221634326110215075728117477608957205955013904404734810099763474889470631639534556341060057450607676968771655492290451731996303257396590296836577760825419491815625686684473433457266832814003142829640231610256894154054380022140453277023835732087637114178031667455347890782582781473044175730534643992876749090244475324930234889607843760875452624193153115573166057973419380, 10023383120⟩
private theorem pole3544_792_41_checked :
    packedBlock 3544 792 pole3544_792_41.length 4728 pole3544_792_41.packed = pole3544_792_41.total := by decide +kernel

private def pole3544_792_42 : Block := ⟨96, 81845532035313438365970107218885271392776565721718886567297328439504103586060259366080564060825075053815379065459387837811529371092151895774880965378748649417200933109896704211761098350494124429229636232758699063888224753055551128825688725280648150360813789912054695466950587647340905299127126057745755509953106899015764232128233054738180281325507124726266236530227005059713012920783261232783222504623500, 5442224720⟩
private theorem pole3544_792_42_checked :
    packedBlock 3544 792 pole3544_792_42.length 4824 pole3544_792_42.packed = pole3544_792_42.total := by decide +kernel

private def pole3544_792_43 : Block := ⟨96, 82408044282979422914137999163610861563918805333222697406477179270051001217106614327426318021886675218160126491384219334563001291576626822778106438467045566838098608823203111586944435875568757042833585781043964670509616692107959428011145840304402146667247557683656113910065443207044696420222584660143620237323432324987352733721822116599611472406538924522297583452610249243973401648413406892400387035827620, 2215845968⟩
private theorem pole3544_792_43_checked :
    packedBlock 3544 792 pole3544_792_43.length 4920 pole3544_792_43.packed = pole3544_792_43.total := by decide +kernel

private def pole3544_792_44 : Block := ⟨96, 82970556530645407462305891108336451735061044944726508245657030100597898848152969288772071982948275382504873917309050831314473212061101749781331911555342484258996284536509518962127773400643389656437535329329230277131008631160367727196602955328156142973681325455257532353180298766748487541318043262541484964693757750958941235315411178461042663487570724318328930374993493428233790376043552552017551567031740, 423873104⟩
private theorem pole3544_792_44_checked :
    packedBlock 3544 792 pole3544_792_44.length 5016 pole3544_792_44.packed = pole3544_792_44.total := by decide +kernel

private def pole3544_792_45 : Block := ⟨16, 5832024109643010059484448182554013422553290191365278378810058018260, 1570488⟩
private theorem pole3544_792_45_checked :
    packedBlock 3544 792 pole3544_792_45.length 5112 pole3544_792_45.packed = pole3544_792_45.total := by decide +kernel

private def poleBlocks3544_792 : List Block := [pole3544_792_0, pole3544_792_1, pole3544_792_2, pole3544_792_3, pole3544_792_4, pole3544_792_5, pole3544_792_6, pole3544_792_7, pole3544_792_8, pole3544_792_9, pole3544_792_10, pole3544_792_11, pole3544_792_12, pole3544_792_13, pole3544_792_14, pole3544_792_15, pole3544_792_16, pole3544_792_17, pole3544_792_18, pole3544_792_19, pole3544_792_20, pole3544_792_21, pole3544_792_22, pole3544_792_23, pole3544_792_24, pole3544_792_25, pole3544_792_26, pole3544_792_27, pole3544_792_28, pole3544_792_29, pole3544_792_30, pole3544_792_31, pole3544_792_32, pole3544_792_33, pole3544_792_34, pole3544_792_35, pole3544_792_36, pole3544_792_37, pole3544_792_38, pole3544_792_39, pole3544_792_40, pole3544_792_41, pole3544_792_42, pole3544_792_43, pole3544_792_44, pole3544_792_45]
theorem moment3544_792 : P1_7_1.groupedPoleMoment 3544 792 ≤ 4440399084942 := by
  refine grouped_from_blocks 3544 792 _ poleBlocks3544_792 ?_ (by decide) (by decide)
  exact ⟨pole3544_792_0_checked, pole3544_792_1_checked, pole3544_792_2_checked, pole3544_792_3_checked, pole3544_792_4_checked, pole3544_792_5_checked, pole3544_792_6_checked, pole3544_792_7_checked, pole3544_792_8_checked, pole3544_792_9_checked, pole3544_792_10_checked, pole3544_792_11_checked, pole3544_792_12_checked, pole3544_792_13_checked, pole3544_792_14_checked, pole3544_792_15_checked, pole3544_792_16_checked, pole3544_792_17_checked, pole3544_792_18_checked, pole3544_792_19_checked, pole3544_792_20_checked, pole3544_792_21_checked, pole3544_792_22_checked, pole3544_792_23_checked, pole3544_792_24_checked, pole3544_792_25_checked, pole3544_792_26_checked, pole3544_792_27_checked, pole3544_792_28_checked, pole3544_792_29_checked, pole3544_792_30_checked, pole3544_792_31_checked, pole3544_792_32_checked, pole3544_792_33_checked, pole3544_792_34_checked, pole3544_792_35_checked, pole3544_792_36_checked, pole3544_792_37_checked, pole3544_792_38_checked, pole3544_792_39_checked, pole3544_792_40_checked, pole3544_792_41_checked, pole3544_792_42_checked, pole3544_792_43_checked, pole3544_792_44_checked, pole3544_792_45_checked, True.intro⟩

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
