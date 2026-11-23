import ProximityPrize.SubmissionLower.ZPuXYRc
import ProximityPrize.SubmissionLower.ZpYo3sb
import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.Z3ozsyb
import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZxDTsFd
import ProximityPrize.SubmissionLower.Zj5kWte
import ProximityPrize.SubmissionLower.ZdY8S8d
import ProximityPrize.SubmissionLower.ZUkTKja
import ProximityPrize.SubmissionLower.Z0Ff26b
import ProximityPrize.SubmissionLower.ZuFhpOb
import ProximityPrize.SubmissionLower.ZVMYHza
import ProximityPrize.SubmissionLower.ZnTmQ9b
set_option Elab.async false
open _root_ renaming Nat.add_le_add_left → z3b, Nat.cast_nonneg → zqJ, Nat.mul_le_mul_left → zBI, Nat.zero_le → zD0, Polynomial.map_injective → zTo, Polynomial.uniqueFactorizationMonoid → zV6
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace qXdgDRd
open P6_7_1 (jJ degree gw seedCap retainedFee)
open P5_7 (NativeWitness)
private abbrev Ya (e a r :ℕ) :=
  gap degree*e+r*(a+P6.p*a)≤gap degree*(retainedFee-1)
private def af (e a prev rate :ℕ) (x :NativeWitness) :Prop :=
  prev≤ rate∧(e=1∨Witness degree e x)∧jX degree e x=rate∧Ya e a rate
private instance rowDec (e a prev rate :ℕ) (x :NativeWitness) :Decidable (af e a prev rate x) := by
  unfold af Witness
  infer_instance
private inductive dG:ℕ→ℕ→List (ℕ×ℕ)→Prop
  | nil {e prev} : dG e prev []
  | cons {e a b prev rate gs} (x :NativeWitness) (h:af e a prev rate x)
      (tail:dG (e+1) rate gs) :dG e prev ((a,b)::gs)
private theorem dG.get {e prev gs} (rows :dG e prev gs) (i:Fin gs.length) :
    ∃ r,prev≤ r∧Ya (e+i.val) (gs.get i).1 r ∧
      ∀ l,e≤l→l≤e+i.val →
        ∃ x :NativeWitness,(l=1∨Witness degree l x)∧jX degree l x≤ r := by
  induction rows with
  | nil=>exact Fin.elim0 i
  | @cons e a b prev rate gs x h rows ih =>
    obtain ⟨hprev,hx,hrate,hbill⟩:=h
    rcases i with ⟨i,hi⟩
    cases i with
    | zero =>
      refine ⟨rate,hprev,hbill,fun l hl₁ hl₂ => ?_⟩
      have heq :l=e := by dsimp at hl₂; omega
      exact ⟨x,heq.symm ▸ hx,heq.symm ▸ hrate.le⟩
    | succ i =>
      let j:Fin gs.length:=⟨i,by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi⟩
      obtain ⟨r,hp,hb,hr⟩:=ih j
      have heq :e+(⟨i+1,hi⟩:Fin ((a,b)::gs).length).val=e+1+j.val := by dsimp [j]; omega
      refine ⟨r,hprev.trans hp,?_,fun l hl₁ hl₂ => ?_⟩
      · rw [heq]
        exact hb
      · by_cases hl:l=e
        · exact ⟨x,hl.symm ▸ hx,hl.symm ▸ (hrate.le.trans hp)⟩
        · exact hr l (by omega) (heq ▸ hl₂)
set_option quotPrecheck false in
local notation "r!" "[" g "," c "," j "," W "," r "]" t =>
  dG.cons (rate :=r) ⟨g,c,j,W⟩ (by decide) t
private theorem b4 :dG 81 0x34f639d9 (gw.drop 80) :=
  r![810,230,807,3193484,0x36327b16]
  r![820,232,817,3231718,0x3774f7bd]
  r![830,235,827,3269345,0x38b7860f]
  r![840,237,837,3307564,0x3a023249]
  r![850,240,847,3345189,0x3b4bfdd7]
  r![860,242,857,3383395,0x3c9decf5]
  r![870,245,867,3421017,0x3deef32f]
  r![880,248,877,3458641,0x3f4396ed]
  r![890,250,887,3496829,0x40a063d7]
  r![900,253,897,3534452,0x41fc45bd]
  r![1092,253,1088,3572542,0x435f9dd5]
  r![1104,256,1100,3609828,0x44bfec39]
  r![1116,258,1112,3647767,0x4629496b]
  r![1128,261,1124,3685051,0x4790b615]
  r![1140,263,1136,3722977,0x490137bf]
  r![1152,266,1148,3760260,0x4a6fc461]
  r![1164,269,1160,3797545,0x4be613c1]
  r![1176,271,1172,3835455,0x4d5d1525]
  r![1188,274,1184,3872740,0x4ed651b9]
  r![1200,276,1196,3910639,0x5058ad65]
  dG.nil
private theorem b3:dG 61 0x1f288e31 (gw.drop 60) :=
  r![610,178,607,2435141,0x201b8977]
  r![620,181,617,2472810,0x2115a5da]
  r![630,183,627,2511221,0x22109477]
  r![640,186,637,2548882,0x230e6ae9]
  r![650,188,647,2587268,0x241421c5]
  r![660,191,657,2624921,0x25193375]
  r![670,193,667,2663284,0x26262fd9]
  r![680,196,677,2700930,0x27327ce1]
  r![690,199,687,2738579,0x28426943]
  r![700,201,697,2776912,0x295a47d5]
  r![710,204,707,2814555,0x2a716fbb]
  r![720,206,717,2852868,0x2b909231]
  r![730,209,727,2890506,0x2caef621]
  r![740,212,737,2928146,0x2dd4a640]
  r![750,214,747,2966434,0x2efafc6d]
  r![760,217,757,3004069,0x302438dd]
  r![770,219,767,3042340,0x3155812d]
  r![780,222,777,3079972,0x3285fb25]
  r![790,224,787,3118226,0x33be84f5]
  r![800,227,797,3155854,0x34f639d9]
  b4
private theorem b2 :dG 41 0xeed0699 (gw.drop 40) :=
  r![328,127,326,1667546,0xf98b381]
  r![336,130,334,1705806,0x1048140d]
  r![344,132,342,1744855,0x10fe3ac3]
  r![352,135,350,1783091,0x11b50415]
  r![360,138,358,1821324,0x126f807d]
  r![368,140,366,1860310,0x1330d305]
  r![376,143,374,1898523,0x13f2b77b]
  r![384,146,382,1936734,0x14b84ed9]
  r![392,148,390,1975664,0x1584c9bd]
  r![400,151,398,2013858,0x1651c85d]
  r![408,154,406,2052052,0x17227b39]
  r![416,156,414,2090934,0x17fa1e11]
  r![424,159,422,2129113,0x18d2371f]
  r![432,162,430,2167293,0x19ae2258]
  r![440,164,438,2206131,0x1a90cc4b]
  r![448,167,446,2244298,0x1b73ffd9]
  r![456,170,454,2282466,0x1c5e1ffc]
  r![464,172,462,2321266,0x1d48d3cd]
  r![590,173,587,2359025,0x1e35014f]
  r![600,175,597,2397474,0x1f288e31]
  b3
private theorem b1 :dG 21 74399881 (gw.drop 20) :=
  r![126,75,125,884964,80852541]
  r![132,77,131,925342,87607669]
  r![138,80,137,964726,94532957]
  r![144,83,143,1004078,0x60ffbc9]
  r![150,86,149,1043400,0x6815b9d]
  r![156,88,155,1083535,0x6f88745]
  r![162,91,161,1122782,0x7719e15]
  r![168,94,167,1162009,0x7ee8dad]
  r![174,97,173,1201217,0x86f554f]
  r![180,100,179,1240408,0x8f54d78]
  r![186,102,185,1280331,0x97e801b]
  r![192,105,191,1319474,0xa0ad3a9]
  r![264,106,262,1358358,0xa9a43a9]
  r![272,108,270,1397672,0xb2ed82d]
  r![280,111,278,1436018,0xbc44a7d]
  r![288,114,286,1474354,0xc5d6fe1]
  r![296,116,294,1513565,0xcfd3947]
  r![304,119,302,1551865,0xd9dc975]
  r![312,122,310,1590158,0xe420c8d]
  r![320,124,318,1629282,0xeed0699]
  b2
private theorem b0:dG 1 46387 gw :=
  r![0,0,0,0,524288]
  r![4,24,4,88327,2683109]
  r![6,26,6,136218,4290925]
  r![12,28,12,181426,6204193]
  r![15,31,15,226011,8428179]
  r![18,34,18,270142,10957077]
  r![28,36,28,313182,13758509]
  r![32,39,32,355559,16831669]
  r![36,42,36,397657,20183823]
  r![40,45,40,439533,23813141]
  r![44,48,44,481229,27718231]
  r![60,50,59,522433,31874637]
  r![65,53,64,563108,36270765]
  r![70,56,69,603661,40929653]
  r![75,59,74,644111,45923130]
  r![80,61,79,685389,51117821]
  r![85,64,84,725643,56564307]
  r![90,67,89,765832,62271501]
  r![114,69,113,805923,68234603]
  r![120,72,119,845468,74399881]
  b1
theorem grade_certificate (i:jJ) :
    ∃ rate,Guards degree (i.val+1) rate ∧
      gap degree*(i.val+1)+rate*(seedCap i+P6.p*seedCap i)≤gap degree*(retainedFee-1) := by
  obtain ⟨r,hprev,hfee,hx⟩:=b0.get i
  have he :1+i.val=i.val+1 :=Nat.add_comm _ _
  rw [he] at hfee hx
  have hs :seedCap i≤(gw.get i).1 :=Nat.min_le_right _ _
  refine ⟨r,⟨hprev,hx⟩,?_⟩
  apply LE.le.trans ?_ hfee
  exact z3b (zBI _ (Nat.add_le_add hs (zBI _ hs))) _
end qXdgDRd
end
section
set_option autoImplicit true
namespace qXdgDRd
noncomputable section
open Polynomial Finset
open P6_7_1 (packetHi degree gw)
open P5_7_7 (sites mem_sites)
def c1 :Prop :=NodeBound gw.length
def c2 :Prop :=PoleBound (width degree) gw.length
theorem of_children (h1 :c1) (h2 :c2) :P6_7_1.c8:= by
  intro x T hT i g hg hd hH hroot
  obtain ⟨rate,guard,hbudget⟩:=grade_certificate i
  have hi:i.val+1≤gw.length:=i.isLt
  have hnode :NodeBound (i.val+1) :=
    fun F l h hl=>h1 F l h (hl.trans hi)
  have hpoles :PoleBound (width degree) (i.val+1) :=
    fun F l h u s W hl=>h2 F l h u s W (hl.trans hi)
  have hw:x.M.iF.toNat≤packetHi:= by
    have h:=x.kA.2
    change x.M.iF≤(packetHi:ℤ) at h
    omega
  have hA (γ) (hγ:γ∈T) :
      P6.dw≤(sites x.M.word x.F.scalar γ).card:= by
    let m:=x.F.mark γ (hT hγ)
    exact m.bad.dw.trans (card_le_card fun j hj=>mem_sites.mpr (m.scalar_hits j hj))
  have M:StrongMarks degree x.M.word T x.M.label x.F.scalar :=
    ⟨⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
       fun γ hγ=>(P6_7.aic x.F (hT hγ)).trans (z3b hw _),
       fun γ hγ=>(by decide :P5_7.farAgreement≤P6.dw).trans (hA γ hγ)⟩,hA⟩
  exact native_count guard (by decide) (by decide) (hi.trans_lt (by decide))
    (by decide) (by decide) hbudget hnode hpoles M g hg hd hH hroot
end
end qXdgDRd
end
section
set_option autoImplicit true
set_option Elab.async false
section
namespace P5_7_2_6Q4
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna qps5rle
open P5 (K)
open cu (L)
open E7 (CurvePlace axV poleOrder)
open qb0hmCe (CurveModel)
open qFD8jve (aFA sheetPole)
open private coeff_le_pole from ProximityPrize.SubmissionLower.ZexDIsb
open private sum_le_all finite_tuple from ProximityPrize.SubmissionLower.ZG9rwXd
open scoped Classical WithZero
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (v :Valuation E ℤᵐ⁰)
    (x :L) (f :E[X][X]) (b:ℕ),
    0<f.natDegree→v (algebraMap L E x)≤1→aFA v f b →
    v (initialAt x f.discr)≤WithZero.exp (((2*f.natDegree-2)*b:ℕ) :ℤ)
private theorem cHQ {E :Type} [Field E] [Algebra L E]
    (v :CurvePlace L E) (x :L) :v.value (algebraMap L E x)≤1 := by
  by_cases hx :x=0
  · simp [hx]
  · rw [v.on_constants x hx]
private theorem aVi (bound:c2) {J:Input} {U:Finset K} {B:DualWord J U}
    {q:SeedPlane} {C:CurveModel q} (S:Sheet B C) (x :L)
    (hD:initialAt x S.f.discr≠0) :
    (∑ᶠ v :CurvePlace L C.E,poleOrder v.value (initialAt x S.f.discr))≤(2*S.d-2)*S.h:= by
  let D:=initialAt x S.f.discr
  let H (v :CurvePlace L C.E) :=sheetPole v.value S.f
  let P (v :CurvePlace L C.E) :=poleOrder v.value D
  have hdiv :axV L C.E :=
    aFU.of_children
      bRt.proof bRu.proof L C.E C.curve
  have hH :H.HasFiniteSupport:=finite_tuple hdiv _
  have hP:P.HasFiniteSupport:=(hdiv D).1
  have hp (v :CurvePlace L C.E) :P v≤(2*S.d-2)*H v :=
    Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hD)).2
      (bound v.value x S.f (H v) S.positive (cHQ v x) (coeff_le_pole v.value S.f)))
  change (∑ᶠ v,P v)≤_
  rw [finsum_eq_finsetSum_of_support_subset P (s :=hP.toFinset)
    (fun _ hv=>hP.mem_toFinset.mpr hv)]
  calc
    _ ≤ ∑ v∈hP.toFinset,(2*S.d-2)*H v :=sum_le_sum fun v _=>hp v
    _≤(2*S.d-2)*S.h:= by
      rw [← mul_sum]
      exact zBI _ (sum_le_all H hH _)
end
end P5_7_2_6Q4
end
section
namespace P5_7_2_6Q4
open Polynomial
open scoped WithZero
open cu (L)
open qps5rle (initialAt)
open private efc aMX from ProximityPrize.SubmissionLower.Y
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private discr_val_le from ProximityPrize.SubmissionLower.ZW8Nc6b
private theorem taylor_coeff_le {E :Type} [Field E] (v :Valuation E ℤᵐ⁰)
    (g:E[X]) {a :E} (ha :v a≤1) (n:ℕ) :
    v ((g.taylor a).coeff n)≤efc v g:= by
  rw [taylor_coeff,eval_eq_sum,Polynomial.sum]
  apply v.map_sum_le
  intro i _
  rw [hasseDeriv_coeff,map_mul,map_mul,map_pow]
  have hc:v (g.coeff (i+n))≤efc v g:=aMX v g (i+n)
  simpa only [one_mul,mul_one] using
    mul_le_mul' (mul_le_mul' (cast_le_one (v :=v) ((i+n).choose n)) hc)
      (pow_le_one₀ (n:=i) zero_le ha)
theorem bound:c2 := by
  intro E _ _ v x f b hd hx h
  let u:ℤᵐ⁰:=WithZero.exp (b:ℤ)
  have hf (i:ℕ) :efc v (f.coeff i)≤u :=
    Finset.sup_le fun j _=>h i j
  unfold initialAt trailingCoeff
  refine (taylor_coeff_le v f.discr hx _).trans
    ((discr_val_le (efc v) f hd u hf).trans_eq ?_)
  rw [← WithZero.exp_nsmul]
  simp
end P5_7_2_6Q4
end
section
namespace P5_7_2_6Q4
noncomputable section
open Polynomial qe6nVeb qE3Ebna qps5rle q14iMuc
open P5 (K p)
open cu (L)
open qb0hmCe (CurveModel)
open qb8HqGc (covariance)
open scoped Classical WithZero
private theorem chart_initial {J:Input} {U:Finset K} {B:DualWord J U}
    {q:SeedPlane} {C₀:CurveModel q} (S:Sheet B C₀) (R:SiteTarget)
    (T:qgpYCte.SiteChart S R) (hp:S.d<p) :
    initialAt R.center T.g.discr =
      (targetDet R (C₀.seed R.coord) T.V*algebraMap L C₀.E T.M.det)^(S.d*(S.d-1)) *
      initialAt R.center S.f.discr := by
  let τ:C₀.E[X] :=physicalParameter R.center
  let u:=targetDet R (C₀.seed R.coord) T.V*algebraMap L C₀.E T.M.det
  let M:=siteMatrix R (C₀.seed R.coord) T.V T.M
  have hτ:τ≠0:=X_sub_C_ne_zero _
  have hu:u≠0:=mul_ne_zero T.det_ne
    (fun hz=>T.matrix_ne ((algebraMap L C₀.E).injective (by simpa using hz)))
  have hM:M.det=τ*C u:=site_det _ _ _ _
  have htrans :C (τ^T.k)*T.g=qgpYCte.changeOrdinate S.f M:=T.transformed
  have hg:0<T.g.natDegree :=T.degree.symm ▸ S.positive
  have hdeg: (qgpYCte.changeOrdinate S.f M).natDegree=S.d:= by
    rw [← htrans,natDegree_C_mul (pow_ne_zero _ hτ),T.degree]
  have he :=covariance S.f M S.positive hp (hM ▸ mul_ne_zero hτ (C_ne_zero.mpr hu)) hdeg
  rw [← htrans,discr_scale _ (pow_ne_zero _ hτ) _ hg,T.degree,
    hM,mul_pow,← C_pow,← pow_mul] at he
  exact initialAt_identity _ _ _ _ _ _ _ he
theorem proof :qgpYCte.c2 := by
  intro J U B q C₀ S hp R T
  have bound:c2 :=P5_7_2_6Q4.bound
  have hdis :S.f.discr≠0:=discr_ne S.f S.irreducible S.positive hp
  have hD:initialAt R.center S.f.discr≠0:= by
    intro hz
    exact hdis ((taylor_eq_zero _ _).mp (trailingCoeff_eq_zero.mp hz))
  refine ⟨hD,aVi bound S _ hD,?_⟩
  intro γ hγ hhit hunit
  let a :=S.atPlace γ hγ
  let f :=atArc a T.g
  let d:=S.d
  let D:=initialAt R.center S.f.discr
  let u:=targetDet R (C₀.seed R.coord) T.V*algebraMap L C₀.E T.M.det
  have hdeg:f.natDegree=d :=
    (natDegree_map_eq_of_injective (zTo _ a.injective) _).trans T.degree
  have hg:0<T.g.natDegree :=T.degree.symm ▸ S.positive
  have hf :0<f.natDegree :=hdeg.symm ▸ S.positive
  have hm:initialAt R.center f.discr=a (u^(d*(d-1))*D) := by
    change initialAt R.center ((T.g.map (mapRingHom a.toRingHom)).discr)= _
    rw [discr_map _ (zTo _ a.injective) _ hg]
    change initialAt R.center (T.g.discr.map a.toRingHom)= _
    rw [initialAt_map,chart_initial S R T hp]
  have hle :vSeed (initialAt R.center f.discr)≤1 := by
    simpa only [Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero] using
      bound vSeed R.center f 0 hf (constant_val_le R.center) (by
        intro i j
        simpa only [Nat.cast_zero,WithZero.exp_zero] using T.integral γ hγ hhit i j)
  have hD' : 1≤vSeed (a D) :=(S.value γ hγ D) ▸ hunit
  have hu:1≤vSeed (a u) := by
    change 1≤vSeed (a (targetDet R (C₀.seed R.coord) T.V*algebraMap L C₀.E T.M.det))
    rw [map_mul,map_mul,a.commutes,constant_val_eq _ T.matrix_ne,mul_one]
    exact coeff_nonzero_val_le (T.det_unit γ hγ hhit)
  apply coeff_nonzero_of_val_eq (le_antisymm hle ?_)
  rw [hm,map_mul,map_mul,map_pow,map_pow]
  exact one_le_mul (one_le_pow₀ hu) hD'
end
end P5_7_2_6Q4
end
end
section
set_option autoImplicit true
namespace qQFLLod
theorem proof :q8SCoCa.c2 :=
  qgpYCte.of_children
    P5_7_2_6Q3.proof
    P5_7_2_6Q4.proof
    (qymFiQe.of_children qPfoxUd.proof qmgvT1d.proof)
    qLjY93c.proof
end qQFLLod
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qlH1Cxb
noncomputable section
open P6_7 (RectTail)
open P6_7_2 (Input Poles Ls Aux Bs free moving auxiliary dI auxReserve cutoff)
open qO6e97d
open cu (Shape Jet)
open qQ (aeH)
open private emz from ProximityPrize.SubmissionLower.ZUkTKja
private theorem height {b:RectTail} (x :Input b) :0<x.h∧x.h≤131070:= by
  have hl:0<b.kA.lo:= by cases b <;> decide
  have hu: (Bs b).hi≤131070:= by cases b <;> decide
  exact ⟨hl.trans_le (emz x).1,(emz x).2.trans hu⟩
private theorem toTest {h r :ℕ} {s :Shape} {mode :ℕ} (t:Tested h r s mode) :
    qdY8S8d.Test h (count h r s) s (DG s) mode :=
  ⟨t.jet_le,t.aH4,t.aH4.trans_lt t.seed_lt,pole_excess s t.jet_le t.aH4,
    t.width,t.x5⟩
private theorem Yf (h r :ℕ) (s :Shape) :cutoff h r s=count h r s - 1 := by
  unfold cutoff count
  omega
private theorem bVl {b:RectTail} {x :Input b} (P:Poles x)
    {s :Shape} {r mode :ℕ} (t:Tested x.h r s mode) :
    ∃ Q∈P.rows s (cutoff x.h r s),Q≠0:= by
  rw [Yf]
  exact qdY8S8d.bVl P.crt x.word (height x).1 (height x).2 (toTest t)
private theorem pick_pair {b:RectTail} {x :Input b} (P:Poles x) (i:Ls) :
    ∃ Q R:Jet,Q∈P.rows (free b i) (cutoff x.h (dI i) (free b i)) ∧
      R∈P.rows (moving b i) (cutoff x.h (dI i) (moving b i)) ∧
      Q≠0∧R≠0∧aeH Q R:= by
  obtain ⟨hl,hu⟩:=emz x
  have hf :=free_test b i hl hu
  rw [Yf,Yf]
  exact qdY8S8d.pick_pair P.crt x.word (height x).1 (height x).2 (toTest hf)
    (toTest (moving_test b i hl hu)) hf.seed_lt
theorem proof :P6_7_2.c1 := by
  classical
  intro b x P
  choose Q R hQ hR hQn hRn havoid using pick_pair P
  obtain ⟨hl,hu⟩:=emz x
  choose A hA hAn using fun i=>bVl P (aux_test b i hl hu)
  let auxRow (i:Aux) :=if i=9 then Q 1 else if i=10 then Q 3 else A i
  have ha (i:Aux) :auxRow i∈P.rows (auxiliary b i) (cutoff x.h (auxReserve i) (auxiliary b i)) ∧
      auxRow i≠0:= by
    unfold auxRow
    split_ifs with h9 Kr
    · subst i
      exact ⟨hQ 1,hQn 1⟩
    · subst i
      exact ⟨hQ 3,hQn 3⟩
    · exact ⟨hA i,hAn i⟩
  exact ⟨⟨Q,R,auxRow,hQn,hRn,fun i=>(ha i).2,hQ,hR,fun i=>(ha i).1,havoid,
    by constructor <;> simp [auxRow]⟩⟩
end
end qlH1Cxb
end
section
set_option autoImplicit true
namespace qcuQADa
noncomputable section
open Finset
open P6_7 (RectTail)
open P6_7_2 (Bs)
open qXdgDRd (width StrongMarks NodeBound PoleBound)
open P5_7_7 (sites mem_sites)
def c1 :Prop :=NodeBound 100
def c2 :Prop := ∀ b:RectTail,PoleBound (width (degree b)) (Bs b).ordinateCap
theorem of_children (h1 :c1) (h2 :c2) :P6_7_2.c7:= by
  intro b i w T z S hz hs hd hA g hg he hH hr
  obtain ⟨rate,guards,budget⟩:=grade_certificate i
  have hi:i.val+1≤(Bs b).ordinateCap:=i.isLt
  have cap (b:RectTail) : (Bs b).ordinateCap≤100:= by cases b <;> decide
  have hnode :NodeBound (i.val+1) := fun F l h hl=>h1 F l h (hl.trans (hi.trans (cap b)))
  have hpole :PoleBound (width (degree b)) (i.val+1) :=
    fun F l h u s W hl=>h2 b F l h u s W (hl.trans hi)
  have lg (γ) (hγ:γ∈T) :P6.dw≤(sites w S γ).card:= by
    obtain ⟨U,hU,hhit⟩:=hA γ hγ
    exact hU.trans (card_le_card fun j hj=>mem_sites.mpr (hhit j hj))
  have M:StrongMarks (degree b) w T z S :=
    ⟨⟨hz,hs,hd,fun γ hγ=>(by decide :P5_7.farAgreement≤P6.dw).trans (lg γ hγ)⟩,
      lg⟩
  exact qXdgDRd.native_count guards (by cases b <;> decide) (by cases b <;> decide)
    ((hi.trans (cap b)).trans_lt (by decide)) (by cases b <;> decide) (by cases b <;> decide)
    budget hnode hpole M g hg he hH hr
end
end qcuQADa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q4xoUqc
noncomputable section
open Finset Polynomial
open scoped BigOperators Classical
open P6 (p)
open P6_7_4 (wordLift)
open q6nKpZc (Input aAT Pass)
open qkrKkqa (QV live_mem live_dual chosen_order)
open P5_7_2 (fO stages introduction)
open q7F2qKe (aur originBudget originCutter nV kK freeCount freeCap origins
  fibreShape afterFree partMass isLast originFreeCap chosen_mem)
open q3soobb (stages_len cqz shapes_ok after_free)
open cu (Jet Shape aZ Equation)
open DP (d3r)
open gT (Ambient iJ)
open pI (mass oU)
open XY (ag6)
open TD (auN J2 bfw)
open akZ (yE bCj cN4)
open qzVScmb (budget_J intro_guard final_valid matrix_mono)
open private cap_fold mixed_cast from ProximityPrize.SubmissionLower.ZBMOaEd
open private b6z from ProximityPrize.SubmissionLower.D7
private abbrev reference (b:fO) (o:ℕ) :Shape :=
  aur fun k=>max (originBudget b o k) (auN (originCutter b o) k)
private abbrev freeIndices (b:fO) (j:ℕ) :=
  List.range' 1 (min (j-1) (freeCount b))
private abbrev aE6 (b:fO) (o i:ℕ) (k :Fin 4) :ℚ :=
  (kK (auN (nV b i).free) (reference b o) k :ℚ)/((nV b i).dI+1 :ℕ)
private theorem bound_freeCap {b:fO} {o j:ℕ} {k :Fin 4} {v :ℚ}
    (h0:v≤(kK (originBudget b o) (originCutter b o) k :ℚ))
    (hs : ∀ i∈freeIndices b j,v≤aE6 b o i k) :v≤freeCap b o j k :=
  cap_fold (a := fun k=>kK (originBudget b o) (originCutter b o) k)
    (g:= fun i k=>aE6 b o i k) h0 hs
private theorem reserve_small (b:fO) : ∀ s∈stages b,s.dI<p:= by
  fin_cases b <;> simp only [stages,List.map_cons,List.map_nil,List.forall_mem_cons]
  all_goals repeat' first
    | exact fun _ h=>(List.not_mem_nil h).elim
    | refine ⟨by decide,?_⟩
private theorem free_before {b:fO} {j i:ℕ} (hi:i∈freeIndices b j) :
    0< i∧i<j∧i<(stages b).length:= by
  have h:=List.mem_range'_1.mp hi
  have hj:=h.2.trans_le (z3b (Nat.min_le_left (j-1) (freeCount b)) 1)
  have hs :=h.2.trans_le (z3b (Nat.min_le_right (j-1) (freeCount b)) 1)
  have hn:0<(stages b).length:= by rw [stages_len]; decide
  unfold freeCount at hs
  omega
private theorem cutter_J (b:fO) (o:ℕ) (ho:o∈origins b) :
    (originCutter b o).J≤(originCutter b o).B:= by
  by_cases h:o<(introduction b).length
  · rw [originCutter,List.getElem?_eq_getElem h]
    exact (intro_guard (List.getElem_mem h)).1
  · have hb:=mem_range.mp ho
    change o<(introduction b).length+1 at hb
    have he :o=(introduction b).length:= by omega
    subst o
    exact (final_valid b).1
private theorem ref_left {b o H} (h : ∀ k,yE H k≤originBudget b o k) :
    oU H (reference b o) :=
  (bCj _ _).mpr fun k=>(h k).trans (by fin_cases k <;> exact le_max_left _ _)
private theorem ref_right {b o H e} (h:oU H (fibreShape b o e)) :
    oU H (reference b o) := by
  apply (bCj _ _).mpr
  intro k
  refine ((bCj _ _).mp h k).trans ?_
  cases e <;> fin_cases k <;> first | exact le_max_left _ _ | exact le_max_right _ _
variable {b u del M Γ F} {x : @Input b u del M Γ F} (C:aAT F b x)
variable {o:ℕ} (ho:o∈origins b)
include ho
private theorem origin_spend (k :Fin 3) :
    (∑ f∈C.factors o,yE f k)≤originBudget b o k := by
  have h : {o} ⊆ (origins b).filter (o ≤ ·) :=
    singleton_subset_iff.mpr (mem_filter.mpr ⟨ho,le_rfl⟩)
  simpa only [sum_singleton] using
    (sum_le_sum_of_subset_of_nonneg (f := fun o => ∑ f∈C.factors o,yE f k)
      h (fun _ _ _=>zD0 _)).trans (C.tail o ho k)
private theorem factor_spend {f :Jet} (hf :f∈C.factors o) (k :Fin 3) :
    yE f k≤originBudget b o k :=
  (single_le_sum (f := fun g=>yE g k) (fun _ _=>zD0 _) hf).trans
    (origin_spend C ho k)
private theorem initial_factor {f j} (hf :f∈C.factors o) (k :Fin 4) :
    J2 (QV C o f j) k≤kK (yE f) (originCutter b o) k := by
  refine (bfw (filter_subset _ _) k).trans ((C.factor_cap o ho f hf k).trans ?_)
  apply Nat.cast_le.mpr
  apply sum_le_sum
  intro q _
  apply Nat.mul_le_mul_right
  cases he :C.rescue o f
  · exact le_rfl
  · have heq :o=(introduction b).length:=(C.rescue_last o ho f hf he).1
    subst o
    obtain ⟨_,hJ,hDiff,hB,hU⟩:=final_valid b
    exact matrix_mono hJ hDiff hB hU k q
private theorem initial_origin (j:ℕ) (k :Fin 4) :
    partMass C.factors (QV C) o j k≤kK (originBudget b o) (originCutter b o) k := by
  unfold partMass
  refine (sum_le_sum fun f hf=>initial_factor C ho hf k).trans ?_
  simp only [kK,Nat.cast_sum,Nat.cast_mul]
  rw [sum_comm]
  simp only [← mul_sum]
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (zqJ _)
  exact_mod_cast origin_spend C ho q
private theorem free_stage {i j:ℕ} (hi:i∈freeIndices b j) {H Q:Jet}
    (hproper :ag6 H Q) (hH :oU H (reference b o)) (hQ:oU Q (reference b o))
    (S:Finset (Ideal Ambient))
    (hS : ∀ I∈S,∃ f∈C.factors o,I∈QV C o f j∧iJ H∈I∧iJ Q∈I)
    (k :Fin 4) :J2 S k≤aE6 b o i k := by
  obtain ⟨hip,hij,hil⟩:=free_before hi
  let s :=nV b i
  have hs :s∈stages b:=cqz hil
  let R:=(x.donors.staged s hs).free
  have h:=q41fOQb.proof R.jet H Q s.free (reference b o) S (s.dI+1)
    (Nat.succ_pos _) R.nonzero hproper (shapes_ok b s hs).1.2.2.1
    (max_le_max (budget_J b o) (cutter_J b o ho))
    (d3r x.crt (wordLift M) (chosen_mem R)) hH hQ (fun I hI=> by
      obtain ⟨f,hf,hl,hF,hG⟩:=hS I hI
      have hm:=live_mem hl
      have ha :=(C.DN o ho f hf I hm.1).1
      have hd:=live_dual C hl (hip.trans hij)
      have hpass :=hm.2 i hij
      rw [Pass,ite_eq_right hip.ne',ite_eq_left ((after_free b).symm ▸ hil)] at hpass
      exact ⟨ha,hd,hF,hG,chosen_order R (reserve_small b s hs) ha hd hpass⟩) k
  rw [mixed_cast] at h
  exact h
private theorem free_factor {f j} (hf :f∈C.factors o) (k :Fin 4) :
    J2 (QV C o f j) k≤freeCap b o j k := by
  refine bound_freeCap ((initial_factor C ho hf k).trans ?_) ?_
  · exact Nat.cast_le.mpr (sum_le_sum fun q _ =>
      zBI _ (factor_spend C ho hf q))
  · intro i hi
    obtain ⟨hc,hn⟩:=C.proper o ho f hf
    exact free_stage C ho hi (b6z (C.firstFactor o ho f hf).1 hn)
      (ref_left (factor_spend C ho hf)) (ref_right hc) _ (fun I hI =>
        let hg:=C.DN o ho f hf I (live_mem hI).1
        ⟨f,hf,hI,hg.2.2.1,hg.2.2.2.1⟩) k
private theorem shared_stage {j i:ℕ} (hnlast : ¬ isLast b o)
    (hi:i∈freeIndices b j) (k :Fin 4) :partMass C.factors (QV C) o j k≤aE6 b o i k := by
  let D:=C.factors o
  by_cases he :D.Nonempty
  · obtain ⟨f,hf⟩:=he
    let H :Jet := ∏ g∈D,g
    have hcuts (g:Jet) (hg:g∈D) :=C.nonlast_common o ho hnlast g hg f hf
    have hirr (g:Jet) (hg:g∈D) :=(C.firstFactor o ho g hg).1
    have hn (g:Jet) (hg:g∈D) :=(hirr g hg).ne_zero
    have hproper :ag6 H (C.cut o f) := by
      refine ⟨(prod_ne_zero_iff (s :=D) (f := fun g:Jet=>g)).mpr hn,
        (b6z (hirr f hf) (C.proper o ho f hf).2).right_ne,?_⟩
      intro g hg hd hc
      let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
      let:UniqueFactorizationMonoid Equation :=zV6 (D:=aZ)
      let:UniqueFactorizationMonoid Jet:=zV6 (D:=Equation)
      change g ∣ ∏ a∈D,a at hd
      obtain ⟨a,ha,hga⟩:=(hg.prime.dvd_finsetProd_iff (S:=D) (fun a :Jet=>a)).mp hd
      exact (C.proper o ho a ha).2 ((hg.associated_of_dvd (hirr a ha) hga).dvd'.trans
        ((hcuts a ha).symm ▸ hc))
    have hH :oU H (reference b o) :=ref_left fun q =>
      (cN4 (S:=D) (f := fun g:Jet=>g) hn q).trans_le (origin_spend C ho q)
    have hd: (D:Set Jet).PairwiseDisjoint (fun g=>QV C o g j) := by
      intro g hg a ha hne
      exact disjoint_left.mpr fun I hI hJ=>hne
        (C.parent_unique o ho g hg o ho a ha I (live_mem hI).1 (live_mem hJ).1).2
    have h:=free_stage C ho hi hproper hH (ref_right (C.proper o ho f hf).1)
      (D.biUnion fun g=>QV C o g j) (fun I hI=> by
        obtain ⟨g,hg,hl⟩:=mem_biUnion.mp hI
        obtain ⟨_,_,hF,hG,_⟩:=C.DN o ho g hg I (live_mem hl).1
        have hp:iJ H∈I:=I.mem_of_dvd (map_dvd iJ (dvd_prod_of_mem (fun a=>a) hg)) hF
        exact ⟨g,hg,hl,hp,hcuts g hg ▸ hG⟩) k
    simpa only [partMass,J2,mass,sum_biUnion hd,Nat.cast_sum,D] using h
  · have hD:C.factors o = ∅ := not_nonempty_iff_eq_empty.mp he
    rw [partMass,hD,sum_empty]
    exact div_nonneg (zqJ _) (zqJ _)
private theorem d5P: (C.factors o).card ≤ ∑ q,originBudget b o q:= by
  calc
    _ = ∑ f∈C.factors o,(1 :ℕ) := by simp
    _ ≤ ∑ f∈C.factors o,yE f 2 := by
      apply sum_le_sum
      intro f hf
      obtain ⟨i,j,h⟩:=(C.firstFactor o ho f hf).2.1
      exact h.trans_le ((atc.bv9 f _).mp le_rfl i j)
    _≤originBudget b o 2 :=origin_spend C ho 2
    _≤_:=single_le_sum (fun _ _=>zD0 _) (mem_univ 2)
omit ho in
theorem proof :qkrKkqa.c1 := by
  intro b _ u del M Γ F x C o ho
  refine ⟨?_,?_⟩
  · intro f hf j _ I hI k
    exact (Nat.cast_le.mpr (YX.evL hI k)).trans (free_factor C ho hf k)
  · intro k
    rw [originFreeCap]
    by_cases hl:isLast b o
    · rw [ite_eq_left hl]
      have hnon :0≤freeCap b o (afterFree b) k :=
        bound_freeCap (zqJ _) (fun _ _=>div_nonneg (zqJ _) (zqJ _))
      calc
        _ ≤ ∑ f∈C.factors o,freeCap b o (afterFree b) k :=
          sum_le_sum fun f hf=>free_factor C ho hf k
        _=((C.factors o).card:ℚ)*freeCap b o (afterFree b) k := by rw [sum_const,nsmul_eq_mul]
        _≤_:=mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (d5P C ho)) hnon
    · rw [ite_eq_right hl,Nat.cast_one,one_mul]
      exact bound_freeCap (initial_origin C ho _ k) (fun i hi=>shared_stage C ho hl hi k)
end
end q4xoUqc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qNUt03b
noncomputable section
open Finset Polynomial
open scoped Classical
open P6 (K p blockLength jG)
open P5_7_2 (A)
open q7F2qKe (wX weakAgreement)
open qYdH9sc (FilterOK polarDegree poleFee)
open q6nKpZc (Input)
open q4V2ihd (DescendedMarks)
open qK3TPae (high_count)
open quN7Z4a (Sheet physicalWeight)
open qkgz7gb (UJ)
open gT (aQ abX pZ)
open Cu (sQ)
open YY (bnQ U7)
open private b1I from ProximityPrize.SubmissionLower.G
open private q6nKpZc.bd0 from ProximityPrize.SubmissionLower.ZqKag5d
open private OF.distinct OF.degree OF.lg from ProximityPrize.SubmissionLower.ZogIzOe
open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
open private height_guard from ProximityPrize.SubmissionLower.ZQmiAIb
open private low_count slope from ProximityPrize.SubmissionLower.ZX8w26c
def c1 :Prop :=qYdH9sc.c1
def c2 :Prop :=qYdH9sc.c2
def c3:Prop :=qYdH9sc.c3
def c4 :Prop :=qYdH9sc.c4
private theorem sheet {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    {T J Q g H} (h:DescendedMarks F T J Q g H) (hg:0<g) :
    ∃ (C:sQ) (hC:Irreducible C),C.totalDegree= Q.totalDegree ∧
      Nonempty (@Sheet C ⟨hC⟩ J g H T M.label F.scalar) := by
  have hlen:Module.finrank aQ (abX J)= Q.totalDegree*g:= by
    obtain ⟨_,C,hc,hp,_,hs,_,_⟩:=h.curve
    change J.comap pZ=Ideal.span {MvPolynomial.map U7 C} at hp
    let f :=MvPolynomial.map U7 C
    have hf :f≠0:=(map_ne_zero_iff _ (MvPolynomial.map_injective _
      U7.injective)).mpr hc.ne_zero
    have hd:=b1I f hf Q (hp.symm.trans h.projection)
    rw [← hd,bnQ]
    exact hs
  exact quN7Z4a.sheet hg h.curve hlen h.marks
private theorem marks {b u del M Γ F} (x : @Input b u del M Γ F) {T:Finset K}
    (hT:T⊆Γ) :UJ (wX b) M.word T M.label F.scalar := by
  have hw:=q6nKpZc.bd0 F x.vo hT
  have hlo:=(height_guard b).1
  have hwin:=x.vo.1
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,OF.distinct hw,OF.degree hw,
    OF.lg hw,M.iF.toNat,by omega,x.D,fun γ hγ=>x.residues γ (hT hγ)⟩
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :q4V2ihd.c2 := by
  intro b u del M Γ F _ x T J Q g H hm hg _ v hv
  have hg0:0<g:= by omega
  obtain ⟨C,hC,hdeg,⟨S⟩⟩:=sheet hm hg0
  let:Fact (Irreducible C) :=⟨hC⟩
  have m:=marks x hm.subset
  have hcP:C.totalDegree*g<p:=hdeg ▸ hm.seed_lt
  have hgP:g<p:=(Nat.le_mul_of_pos_left _ (hdeg ▸ hm.plane_pos)).trans_lt hcP
  let D:=wX b
  have hD:D <weakAgreement:=(z3b (bLI b).2 131071).trans_lt (by decide)
  obtain ⟨extra,c,hc,hv⟩:=hv
  let e :=g+extra
  let r :=(extra+1)*c
  let j:=r/(c+1)
  let ranks :=D*(e*(e+1)+j*(j+1))/2
  let W:=max (g*D) (max ((c+1)*ranks/r-j*D) ((e-j)*D))
  let N :=W+1+j*D
  change e*D <N∧(c+1)*ranks< r*N∧polarDegree D g W<p ∧
    7+6*(g:ℚ)+((2*g+1)*blockLength+poleFee D g W:ℕ)/(weakAgreement-D:ℕ)≤v ∧
    ((g*(c+1)+e :ℕ) :ℚ)≤v at hv
  obtain ⟨hN,hr,hguard,hlow,hhigh⟩:=hv
  have hW:g*D ≤W:=le_max_left _ _
  rw [slope hg0]
  by_cases hw:physicalWeight D S.root.equation≤W
  · have h:=low_count h2 h3 h4 qJnk13b.proof S m hD hg hgP hcP hw hW hguard hlow
    rw [hdeg] at h
    have hrest: (0:ℚ)≤8*(g:ℚ)*Q.totalDegree+g:= by positivity
    linarith only [h,hrest]
  · have hD0:0<D:=Nat.lt_of_lt_of_le (by decide :0<131071) (Nat.le_add_right _ _)
    have hok :FilterOK D g extra c W N :=⟨hD0,hc,hW,rfl,hN,hr⟩
    obtain ⟨B,hB⟩:=h1 C J T M.label F.scalar D g H extra c W N S
      hg hgP hok (lt_of_not_ge hw) m.Kw m.degree
    have h:=Nat.lt_of_mul_lt_mul_left ((high_count B).trans_lt hB)
    have hcard: (T.card:ℚ)≤((g*(c+1)+e :ℕ) :ℚ)*H := by
      exact_mod_cast Nat.le_of_lt_succ h
    have hrest: (0:ℚ)≤(Q.totalDegree :ℚ)^2/3+(4*(g:ℚ)^2+8*g)*Q.totalDegree+g:= by
      positivity
    linarith only [hcard.trans (mul_le_mul_of_nonneg_right hhigh (Nat.cast_nonneg H)),hrest]
end
end qNUt03b
end
