import ProximityPrize.SubmissionLower.Z6969Pack0636
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalGeometry
import ProximityPrize.SubmissionLower.R6966ProofPadePhysicalQuotient
import ProximityPrize.SubmissionLower.R6966ProofHelperPhysicalModel
import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0635
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts

set_option Elab.async false

-- Source: Research6969.OrdinaryBounds
section Z6969Source0854
set_option autoImplicit true
namespace Research6969.OrdinaryBounds
noncomputable section
open Research6966
open K1_14 (L FX Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface Parent SeedField)
open PadeNativeQuotient (Native)
open PhysicalWindow (Request Triangular Cover)
open Finset
set_option maxRecDepth 8500
set_option maxHeartbeats 1300000

structure Source (first last:ℕ) where
  row:Request
  fits:TerminalWitness.Fits row first last SpreadCatalogue.shape
  cover:∃endpoints,Cover (Triangular row) last first endpoints

structure Cap where
  grade:ℕ
  seed:ℕ

def step {first last} (c:Cap) (t:Source first last) (a l wt:ℕ) (high:Option ℕ):Cap:=
  if t.row.jet=a ∧ 0<t.row.seed ∧ t.row.seed≤l ∧ t.row.weight≤wt then
    ⟨min c.grade ((t.row.shape.B+(a-1)*t.row.shape.J)/(t.row.reserve+1)),
     match high with
     | some v=>min c.seed ((t.row.shape.U+t.row.shape.J*v)/(t.row.reserve+1))
     | none=>c.seed⟩
  else c

def run {first last:ℕ} (a l wt:ℕ) (high:Option ℕ):List (Source first last)→Cap→Cap
  | [],c=>c
  | t::ts,c=>run a l wt high ts (step c t a l wt high)

theorem sound {first last:ℕ} (ts:List (Source first last)) {a lo wt h:ℕ} {high:Option ℕ} {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (hp:0<h) (hl:h≤131070) (earlier:first≤h) (later:h≤last)
    {S:Finset Surface} (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (deg:G.graphDegree=a)
    {H:Equation} (on:NativeWitnessBank.witnessed N S H) (low:lo≤seedDegree N.poly)
    (up:∀v,high=some v→seedDegree N.poly≤v)
    (phys:HelperPhysicalModel.Model Crt N.poly) (physical:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (c:Cap) (grade:H.natDegree≤c.grade) (seed:K1_14_4.seedDegree H≤c.seed):
    H.natDegree≤(run a lo wt high ts c).grade ∧ K1_14_4.seedDegree H≤(run a lo wt high ts c).seed:=by
  induction ts generalizing c with
  | nil=>exact ⟨grade,seed⟩
  | cons t ts ih=>
    have all (fits:t.row.jet=a ∧ 0<t.row.seed ∧ t.row.seed≤lo ∧ t.row.weight≤wt) (v:ℕ) (cap:seedDegree N.poly≤v):
        H.natDegree≤(t.row.shape.B+(a-1)*t.row.shape.J)/(t.row.reserve+1) ∧
        K1_14_4.seedDegree H≤(t.row.shape.U+t.row.shape.J*v)/(t.row.reserve+1):=by
      obtain ⟨ends,cert⟩:=t.cover
      obtain ⟨same,pos,floor,weight⟩:=fits
      have lower:=floor.trans low
      have use:=NearTerminal.seeded_of_positive (pos.trans_le lower)
      obtain ⟨g,s⟩:=TerminalWitness.triangular t.fits cert earlier later hp hl Crt word N gp phys on
        (deg.trans same.symm) use (weight.trans physical) lower (fun j i=>(K1_14_2_2_2_1.seedDegree_le ..).mp cap j i) geo pass
      rw [deg] at g
      exact ⟨(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa only [Nat.mul_comm H.natDegree] using g),
        (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa only [Nat.mul_comm (K1_14_4.seedDegree H)] using s)⟩
    apply ih
    · dsimp only [step];split
      · rename_i h;exact le_min grade (all h _ le_rfl).1
      · exact grade
    · dsimp only [step];split
      · rename_i h
        cases hh:high with
        | none=>exact seed
        | some v=>exact le_min seed (all h v (up v hh)).2
      · exact seed

end
end Research6969.OrdinaryBounds
end Z6969Source0854

-- Source: Research6969.SharedPhysicalModel
section Z6969Source0855
set_option autoImplicit true
namespace Research6969.SharedPhysicalModel
noncomputable section
open Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift jetConstant)
open K1_14_1_4 (doubleMap evalRaw specialized)
open K1_14_3 (SeedField SeedClosure fibreRow)
open Research6966
open scoped Polynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

private abbrev extField:=algebraMap SeedField SeedClosure

/-- Use the very same primitive physical polynomial when switching from
a native helper test to a forced-power test after passage to the seed closure. -/
theorem compatible {h} {D:PoleData h} (Crt:CRTLift D) {G:Pade.Row SeedField}
    (gp:G.primitive) (N:PadeNativeQuotient.Native G) (physical:HelperPhysicalModel.Model Crt N.poly) :
    ∃ M:PadeConcentration.Model Crt G,M.raw=physical.raw := by
  obtain ⟨basis⟩:=PadeConcentration.exists_model Crt gp
  have raw:doubleMap extField (doubleMap evalRaw physical.raw)=doubleMap PadeRawField.rawField physical.raw:=by
    ext j i
    simp only [doubleMap,coe_mapRingHom,coeff_map,PadeRawField.rawField,RingHom.comp_apply]
  have scalar (c:SeedField):doubleMap extField (jetConstant c)=jetConstant (extField c):=by
    simp only [jetConstant,doubleMap,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply]
  have fixed (c:SeedClosure):basis.transform (jetConstant c)=jetConstant c:=basis.transform.commutes c
  refine ⟨⟨physical.raw,physical.primitive,basis.transform,extField physical.c*N.scalar,
    mul_ne_zero ((map_ne_zero extField).mpr physical.unit_c) N.nonzero,?_,basis.onRows,basis.leading⟩,rfl⟩
  rw [←raw,physical.eq,map_mul,scalar,←basis.onRows,N.eq,map_mul,fixed,map_mul jetConstant,mul_assoc]

end
end Research6969.SharedPhysicalModel
end Z6969Source0855

-- Source: Research6969.PowerBox
section Z6969Source0856
set_option autoImplicit true
namespace Research6969.PowerBox
noncomputable section
open K1_14 (Shape)
open K1_14_4 (gradeWidth)
open Research6966 Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def balanced (n:ℕ):ℕ:=n/2*(n-n/2)

private theorem near_half {x y n:ℕ} (order:x≤y) (room:x+y≤n):x*y≤balanced n:=by
  let m:=n/2
  have h:x≤m:=by dsimp [m];omega
  have hm:2*m≤n:=by dsimp [m];omega
  obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le h
  obtain ⟨c,hc⟩:=Nat.exists_eq_add_of_le hm
  have ht:y≤n-x:=by omega
  apply (Nat.mul_le_mul_left x ht).trans
  change x*(n-x)≤m*(n-m)
  rw [show n-x=c+d+m by omega,show n-m=c+m by omega,hd]
  nlinarith only [Nat.zero_le (d*d),Nat.zero_le (d*c)]

theorem balanced_le {x y n:ℕ} (room:x+y≤n):x*y≤balanced n:=by
  rcases le_total x y with h|h
  · exact near_half h room
  · rw [Nat.mul_comm];apply near_half h;omega

theorem seed_sum (Q:K1_14.Jet):
    K1_14_2_2_2_1.seedDegree Q ≤ PadeNativeQuotient.axis Q 0+PadeNativeQuotient.axis Q 1 := by
  let S:=K1_14_2_2_2_1.seedVariables Q
  change S.totalDegree≤S.degreeOf 0+S.degreeOf 1
  apply Finset.sup_le
  intro d hd
  change d.sum (fun _ n=>n)≤_
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two]
  exact Nat.add_le_add ((MvPolynomial.degreeOf_le_iff.mp le_rfl) _ hd) ((MvPolynomial.degreeOf_le_iff.mp le_rfl) _ hd)

def boundGrade (B J W w:ℕ):ℕ:=min B ((W+J)/w)

theorem grade_le {B J W w smallW largeW j:ℕ} (positive:0<w) (step:w≤smallW)
    (top:W≤largeW) (index:j≤J):gradeWidth smallW B W j≤boundGrade B J largeW w+1-j := by
  let b:=min B ((W+j)/smallW)
  have sw:0<smallW:=positive.trans_le step
  have room:b*smallW≤W+j:=(Nat.le_div_iff_mul_le sw).mp (min_le_right ..)
  have l:b≤boundGrade B J largeW w:=le_min (min_le_left ..) ((Nat.le_div_iff_mul_le positive).mpr
    (((Nat.mul_le_mul_left b step).trans room).trans (Nat.add_le_add top index)))
  change min (B+1) ((W+j)/smallW+1)-j≤_+1-j
  have eq:min (B+1) ((W+j)/smallW+1)=b+1:=by dsimp [b];omega
  rw [eq]
  omega

def residual (step W B J e k t a wt U lower:ℕ):ℕ :=
  if t*a≤B ∧ t≤J ∧ t*wt≤W ∧ t*lower≤2*U then
    SpreadWindow.lex (boundGrade (B-t*a) (J-t) (W-t*wt) step) (J-t) e (k-t) *
       balanced (2*(U+1)-t*lower)
  else 0

theorem residual_le {step W B J e k t a wt U lower s H weight:ℕ} (axis:Fin 2→ℕ)
    (pos:0<s) (w:s≤step) (top:W≤H) (physical:weight≤wt) (seed:lower≤axis 0+axis 1) :
    PadeResidualBank.cost step W B J e k t a wt (fun _=>U) axis ≤
      residual s H B J e k t a weight U lower := by
  unfold PadeResidualBank.cost
  split
  · rename_i allowed
    obtain ⟨ba,jt,ww,axes⟩:=allowed
    have a0:t*axis 0≤U:=axes 0
    have a1:t*axis 1≤U:=axes 1
    have hs:t*lower≤t*axis 0+t*axis 1:=by simpa only [Nat.mul_add] using Nat.mul_le_mul_left t seed
    have fit:t*lower≤2*U:=by omega
    have phys:(t*weight)≤W:=(Nat.mul_le_mul_left t physical).trans ww
    rw [residual,ite_eq_left ⟨ba,jt,phys.trans top,fit⟩]
    let b:=boundGrade (B-t*a) (J-t) (H-t*weight) s
    rw [←sum_mul]
    apply Nat.mul_le_mul _ _
    · refine (sum_le_sum (fun j hj=>Nat.sub_le_sub_right (grade_le pos w
        ((Nat.sub_le_sub_right top _).trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left _ physical) H))
        (Nat.lt_succ_iff.mp (mem_range.mp hj))) _)).trans ?_
      exact SpreadWindow.lex_ge b (J-t) e (k-t)
    · change (U-t*axis 0+1)*(U-t*axis 1+1)≤_
      apply balanced_le
      omega
  · exact Nat.zero_le _

end
end Research6969.PowerBox
end Z6969Source0856

-- Source: Research6969.MeasuredBound
section Z6969Source0857
set_option autoImplicit true
namespace Research6969.MeasuredBound
noncomputable section
open K1_14 (Jet Equation Shape L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (SeedField Surface Parent)
open Research6966
open PadeNativeQuotient (Native)
open PhysicalWindow (Request Cover Triangular Rectangle)
open Finset
open scoped Classical
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

inductive Kind where | triangle | either (side:ℕ)
deriving DecidableEq

structure Test where
  source:Request
  kind:Kind
  fits:TerminalWitness.Fits source 2314 2411 SpreadCatalogue.shape
  verified:match kind with
    | .triangle=>∃ends,Cover (Triangular source) 2411 2314 ends
    | .either side=>side≤source.shape.U ∧ ∃ends,Cover (Rectangle source side) 2411 2314 ends

def Test.seedFloor (t:Test):ℕ:=match t.kind with
  | .triangle=>t.source.seed
  | .either _=>2*t.source.seed-1

def Test.degreeCap (t:Test):ℕ:=(t.source.shape.B+(t.source.jet-1)*t.source.shape.J)/(t.source.reserve+1)
def Test.totalCap (t:Test) (u:ℕ):ℕ:=(t.source.shape.U+t.source.shape.J*u)/(t.source.reserve+1)

theorem Test.bounds (t:Test) {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2314≤h) (hi:h≤2411) {S:Finset Surface} (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (actual:G.graphDegree=t.source.jet)
    {H:Equation} (on:NativeWitnessBank.witnessed N S H) (low:t.seedFloor≤seedDegree N.poly)
    (positive:0<seedDegree N.poly) (phys:HelperPhysicalModel.Model Crt N.poly)
    (weight:t.source.weight≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw):
    H.natDegree≤t.degreeCap ∧ (t.kind=.triangle → ∀u,seedDegree N.poly≤u→K1_14_4.seedDegree H≤t.totalCap u) := by
  have uses:=NearTerminal.seeded_of_positive positive
  have cut (n a b:ℕ) (bound:(t.source.reserve+1)*n≤a+b):n≤(a+b)/(t.source.reserve+1):=
    (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa [Nat.mul_comm n] using bound)
  have checked:=t.verified
  cases mode:t.kind with
  | triangle=>
    rw [mode] at checked
    obtain ⟨ends,cert⟩:=checked
    have sl:t.source.seed≤seedDegree N.poly:=by simpa [Test.seedFloor,mode] using low
    have applyAt (v:ℕ) (bound:seedDegree N.poly≤v):=
      TerminalWitness.triangular t.fits cert lo hi (by omega) (by omega) Crt word N gp phys on actual uses weight sl
        (fun j i=>(K1_14_2_2_2_1.seedDegree_le ..).mp bound j i) geo pass
    have deg:=(applyAt _ le_rfl).1
    rw [actual] at deg
    exact ⟨cut _ _ _ deg,fun _ v h=>cut _ _ _ (applyAt v h).2⟩
  | either side=>
    rw [mode] at checked
    obtain ⟨space,ends,cert⟩:=checked
    have minSeed:2*t.source.seed-1≤seedDegree N.poly:=by simpa [Test.seedFloor,mode] using low
    have sum:=PowerBox.seed_sum N.poly
    have pick:∃z:Fin 2,t.source.seed≤PadeNativeQuotient.axis N.poly z:=by
      by_cases yes:t.source.seed≤PadeNativeQuotient.axis N.poly 0
      · exact ⟨0,yes⟩
      · exact ⟨1,by omega⟩
    obtain ⟨z,atZ⟩:=pick
    let n:=seedDegree N.poly
    have high:=(K1_14_2_2_2_1.seedDegree_le N.poly n).mp le_rfl
    have deg:=(TerminalWitness.rectangle t.fits cert space lo hi (by omega) (by omega) Crt word N gp phys on
      actual uses weight z atZ (fun _=>n) (fun j i z=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (high j i)) geo pass).1
    rw [actual] at deg
    exact ⟨cut _ _ _ deg,fun h=>by contradiction⟩

end
end Research6969.MeasuredBound
end Z6969Source0857

-- Source: Research6969.UnionLedger
section Z6969Source0858
set_option autoImplicit true
namespace Research6969.UnionLedger

/-- Pay the off-graph words from one prefix, using the unused coefficient
on its on-graph source mass as credit toward the shared curve. -/
theorem one_seed (raw credit total onMass offSeed cap:ℤ)
    (rawNonneg:0≤raw) (creditNonneg:0≤credit) (offNonneg:0≤offSeed)
    (room:onMass+offSeed≤total) (maximal:total≤cap) :
    raw*offSeed-credit*total≤max 0 (raw-credit)*cap-(credit+max 0 (raw-credit))*onMass := by
  let k:=max 0 (raw-credit)
  have upper:raw≤credit+k:=by dsimp [k];omega
  have paid:=mul_le_mul_of_nonneg_right upper offNonneg
  have left:=mul_le_mul_of_nonneg_left room (show 0≤credit+k from add_nonneg creditNonneg (le_max_left ..))
  have right:=mul_le_mul_of_nonneg_left maximal (show 0≤k from le_max_left ..)
  change _≤k*cap-(credit+k)*onMass
  linarith only [paid,left,right]

private theorem shared (a b x y z:ℤ) (an:0≤a) (bn:0≤b) (xn:0≤x) (yn:0≤y) (fits:z≤x+y) :
    min a b*z≤a*x+b*y := by
  have a1:=mul_le_mul_of_nonneg_right (min_le_left a b) xn
  have b1:=mul_le_mul_of_nonneg_right (min_le_right a b) yn
  have sum:=mul_le_mul_of_nonneg_left fits (le_min an bn)
  linarith only [a1,b1,sum]

/-- One on-graph invoice, using the actual union projection and the two
disjoint off-graph source budgets, applies to either graph comparison. -/
theorem count (total paid inside offM offR:ℤ)
    (mFee rFee mu ru m0 r0 m1 r1:ℤ)
    (md rd mainMass rescueMass onM onR seedM seedR:ℤ)
    (g v low high maxV:ℤ) (rawOff tail constant ordinate seedRate:ℤ)
    (covered:total≤paid+inside+offM+offR)
    (prefixBill:paid+m0*md+m1*mainMass+r0*rd+r1*rescueMass≤mFee+rFee)
    (insideFee:inside≤constant+ordinate*g+seedRate*v)
    (leftFee:offM≤tail+rawOff*seedM) (rightFee:offR≤tail+rawOff*seedR)
    (mainRoom:onM+seedM≤mainMass) (rescueRoom:onR+seedR≤rescueMass)
    (mainCap:mainMass≤mu) (rescueCap:rescueMass≤ru)
    (gradeSum:g≤md+rd) (seedSum:v≤onM+onR) (gradeLow:low≤g) (gradeHigh:g≤high) (seedCap:v≤maxV)
    (nonneg:0≤rawOff ∧ 0≤m0 ∧ 0≤r0 ∧ 0≤m1 ∧ 0≤r1 ∧ 0≤md ∧ 0≤rd ∧
      0≤onM ∧ 0≤onR ∧ 0≤seedM ∧ 0≤seedR ∧ 0≤v) :
    let om:=max 0 (rawOff-m1)
    let orc:=max 0 (rawOff-r1)
    let cm:=min m0 r0
    let cv:=min (m1+om) (r1+orc)
    total≤mFee+rFee+om*mu+orc*ru+2*tail+constant+
      (ordinate-cm)*(if 0≤ordinate-cm then high else low)+max 0 (seedRate-cv)*maxV := by
  intro om orc cm cv
  obtain ⟨rn,m0n,r0n,m1n,r1n,mdn,rdn,onMn,onRn,smn,srn,vn⟩:=nonneg
  have l:=one_seed rawOff m1 mainMass onM seedM mu rn m1n smn mainRoom mainCap
  have r:=one_seed rawOff r1 rescueMass onR seedR ru rn r1n srn rescueRoom rescueCap
  have grade:=shared m0 r0 md rd g m0n r0n mdn rdn gradeSum
  have sd:=shared (m1+om) (r1+orc) onM onR v (add_nonneg m1n (le_max_left ..)) (add_nonneg r1n (le_max_left ..)) onMn onRn seedSum
  have degree:=TerminalLedger.choose_degree (ordinate-cm) g low high gradeLow gradeHigh
  have qv:=mul_le_mul_of_nonneg_right (le_max_right 0 (seedRate-cv)) vn
  have ub:=mul_le_mul_of_nonneg_left seedCap (le_max_left 0 (seedRate-cv))
  change rawOff*seedM-m1*mainMass≤om*mu-(m1+om)*onM at l
  change rawOff*seedR-r1*rescueMass≤orc*ru-(r1+orc)*onR at r
  change cm*g≤m0*md+r0*rd at grade
  change cv*v≤(m1+om)*onM+(r1+orc)*onR at sd
  linarith only [covered,prefixBill,insideFee,leftFee,rightFee,l,r,grade,sd,degree,qv,ub]

end Research6969.UnionLedger
end Z6969Source0858

-- Source: Research6969.UnionPartition
section Z6969Source0859
set_option autoImplicit true
namespace Research6969.UnionPartition
noncomputable section
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass)
open K1_14_3 (Surface Parent SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface)
open Research6966
open NearBook (owning outside ownerSources otherSources)
open PadeNativeQuotient (Native)
open TransitionPacket (Pair)
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem credit (S:Finset (Ideal Ambient)) (active:∀J∈S,Active J) (w:Fin 4→ℕ):
    w 0*mass S 0+(w 1+w 2)*mass S 1≤∑k,w k*mass S k:=by
  have h:=Nat.mul_le_mul_left (w 2) (MixedSectionCredit.mass_le S active)
  rw [Nat.add_mul]
  simp only [Fin.sum_univ_succ]
  change _ ≤ w 0*mass S 0+(w 1*mass S 1+(w 2*mass S 2+(w 3*mass S 3+0)))
  omega

private theorem outside_measures {parents:Finset Surface} {f:Equation} (G:Jet)
    (pr:JointProjection.Product (outside G parents) f) (sources:Finset (Ideal Ambient))
    (active:∀J∈sources,Active J) (origin:∀q∈parents,∃J∈sources,q.asIdeal=J.comap toJet):
    mass (ownerSources G sources) 1+K1_14_4.seedDegree f≤mass sources 1:=by
  have m:=JointProjection.measures pr (otherSources G sources) (fun j hj=>active j (mem_filter.mp hj).1) (by
    intro q h
    obtain ⟨J,hJ,eq⟩:=origin q (mem_filter.mp h).1
    exact ⟨J,mem_filter.mpr ⟨hJ,by have no:G∉q.asIdeal:=(mem_filter.mp h).2;rwa [eq] at no⟩,eq⟩)
  exact (Nat.add_le_add_left m.2 _).trans_eq (NearBook.split_mass ..)

variable {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}
variable {H:Jet} {mb rb:JointLedger.Book} (P:Pair F Crt H mb rb)
variable {G:Pade.Row SeedField} (N:Native G)

def labels (q:Finset Surface):Finset K:=Γ.filter fun z=>∃j∈q,OnSurface F j z

structure Data (content:ℕ) (onEq:Equation) where
  left:Equation
  right:Equation
  leftProjection:JointProjection.Product (outside N.poly P.main) left
  rightProjection:JointProjection.Product (outside N.poly P.rescue) right
  leftDegree:left.natDegree≤content-G.graphDegree
  rightDegree:right.natDegree≤content-G.graphDegree
  onGrade:onEq.natDegree≤mass P.aSrc 0+mass P.bSrc 0
  onSeed:K1_14_4.seedDegree onEq≤mass (ownerSources N.poly P.aSrc) 1+mass (ownerSources N.poly P.bSrc) 1
  leftRoom:mass (ownerSources N.poly P.aSrc) 1+K1_14_4.seedDegree left≤mass P.aSrc 1
  rightRoom:mass (ownerSources N.poly P.bSrc) 1+K1_14_4.seedDegree right≤mass P.bSrc 1
  cover:Γ.card≤P.paid.card+(labels (F:=F) (owning N.poly (P.main∪P.rescue))).card+
      (labels (F:=F) (outside N.poly P.main)).card+(labels (F:=F) (outside N.poly P.rescue)).card

theorem data {content:ℕ} {onEq offEq:Equation} (on:ProjectedProduct (owning N.poly (P.main∪P.rescue)) onEq)
    (off:JointProjection.Product (outside N.poly (P.main∪P.rescue)) offEq) (offCap:offEq.natDegree≤content-G.graphDegree):
    Nonempty (Data P N content onEq):=by
  classical
  let A:=P.main;let B:=P.rescue
  obtain ⟨l,lp⟩:=JointProjection.exists_product (outside N.poly A) (fun q h=>(P.mainGeo q (mem_filter.mp h).1).1)
  obtain ⟨r,rp⟩:=JointProjection.exists_product (outside N.poly B) (fun q h=>(P.rescueGeo q (mem_filter.mp h).1).1)
  have ld:l∣offEq:=lp.divides (fun q h=>off.vanishes (mem_filter.mpr ⟨mem_union_left _ (mem_filter.mp h).1,(mem_filter.mp h).2⟩))
  have rd:r∣offEq:=rp.divides (fun q h=>off.vanishes (mem_filter.mpr ⟨mem_union_right _ (mem_filter.mp h).1,(mem_filter.mp h).2⟩))
  let LA:=ownerSources N.poly P.aSrc
  let LB:=ownerSources N.poly P.bSrc
  have measured:=JointProjection.measures (Or.inl on) (LA∪LB) (by
    intro J h
    exact (mem_union.mp h).elim (fun z=>P.mainActive _ (mem_filter.mp z).1) (fun z=>P.rescueActive _ (mem_filter.mp z).1)) (by
    intro q h
    obtain ⟨onU,owns⟩:=mem_filter.mp h
    rcases mem_union.mp onU with left|right
    · obtain ⟨J,mem,eq⟩:=P.mainOrigin q left
      exact ⟨J,mem_union_left _ (mem_filter.mpr ⟨mem,by rwa [eq] at owns⟩),eq⟩
    · obtain ⟨J,mem,eq⟩:=P.rescueOrigin q right
      exact ⟨J,mem_union_right _ (mem_filter.mpr ⟨mem,by rwa [eq] at owns⟩),eq⟩)
  have add (k:Fin 4):mass (LA∪LB) k≤mass LA k+mass LB k:=K1_14_2_2.sum_union_le _ _ _
  have subL:LA⊆P.aSrc:=filter_subset _ _
  have subR:LB⊆P.bSrc:=filter_subset _ _
  have degree:=measured.1.trans ((add 0).trans (Nat.add_le_add (K1_14_2_2.mass_mono subL 0) (K1_14_2_2.mass_mono subR 0)))
  refine ⟨⟨l,r,lp,rp,(natDegree_le_of_dvd ld off.primitive.ne_zero).trans offCap,
    (natDegree_le_of_dvd rd off.primitive.ne_zero).trans offCap,degree,measured.2.trans (add 1),
    outside_measures N.poly lp _ P.mainActive P.mainOrigin,outside_measures N.poly rp _ P.rescueActive P.rescueOrigin,?_⟩⟩
  let s:=labels (F:=F) (owning N.poly (A∪B))
  let a:=labels (F:=F) (outside N.poly A)
  let b:=labels (F:=F) (outside N.poly B)
  have inc:Γ⊆P.paid∪(s∪(a∪b)):=by
    intro z hz
    rcases P.cover z hz with paid|⟨_,q,hq,mark⟩|⟨_,_,q,hq,mark⟩
    · exact mem_union_left _ paid
    · by_cases ok:N.poly∈q.asIdeal
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨mem_union_left _ hq,ok⟩,mark⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨hq,ok⟩,mark⟩)))
    · by_cases ok:N.poly∈q.asIdeal
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨mem_union_right _ hq,ok⟩,mark⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨hq,ok⟩,mark⟩)))
  have size:= (card_le_card inc).trans ((card_union_le ..).trans (Nat.add_le_add_left ((card_union_le ..).trans
      (Nat.add_le_add_left (card_union_le ..) _)) _))
  change Γ.card≤P.paid.card+s.card+a.card+b.card
  simpa only [Nat.add_assoc] using size

end
end Research6969.UnionPartition
end Z6969Source0859

-- Source: Research6969.WholeGraph
section Z6969Source0860
set_option autoImplicit true
namespace Research6969.WholeGraph
noncomputable section
open K1 (K p)
open K1_14 (Equation Jet FX atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass)
open K1_14_3 (Surface SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NearBook (owning outside ownerSources)
open TransitionPacket (Pair)
open GraphLedger (coefficient_mono)
open UnionPartition (labels)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def degreeCost (off:ℕ):ℕ:=if off=0 then 0 else JointLedger.coefficient off
def bill (m r:JointLedger.Book) (off md gd cap:ℕ) (constant ordinate seed:ℤ):ℤ:=
  let raw:ℤ:=degreeCost off
  let mo:=max 0 (raw-m.seedCredit)
  let ro:=max 0 (raw-r.seedCredit)
  let deg:=min (m.ordinateCredit:ℤ) r.ordinateCredit
  let sd:=min ((m.seedCredit:ℤ)+mo) ((r.seedCredit:ℤ)+ro)
  (m.fee:ℤ)+r.fee+mo*m.seedMass+ro*r.seedMass+2*((off*(max 3 off-1):ℕ):ℤ)+constant+
    (ordinate-deg)*(if 0≤ordinate-deg then (gd:ℤ) else md)+max 0 (seed-sd)*cap

private theorem off_price {u del} {M:Model u del} {Γ} {F:Family M Γ} (hi:M.overhead.toNat≤2557)
    {Q:Finset Surface} {f:Equation} (pr:JointProjection.Product Q f) (off:ℕ) (le:f.natDegree≤off) (low:off<64)
    (char:(2*f.natDegree-1)*K1_14_4.seedDegree f<p) :
    (labels (F:=F) Q).card≤degreeCost off*K1_14_4.seedDegree f+off*(max 3 off-1):=by
  have pay:=JointMarked.owned_count F (filter_subset _ _) hi f pr.primitive pr.separable (le.trans_lt low) le_rfl char
    (by intro z hz;obtain ⟨q,hq,mark⟩:=(mem_filter.mp (show z∈labels (F:=F) Q from hz)).2
        simpa [jetAt,Polynomial.eval_map] using mark (C f) (pr.vanishes hq))
  refine pay.trans ?_
  by_cases zero:f.natDegree=0
  · simp [JointMarked.price,zero]
  · have nz:off≠0:=by omega
    unfold JointMarked.price degreeCost
    rw [ite_eq_right zero,ite_eq_right nz,←Nat.mul_assoc]
    change JointLedger.coefficient f.natDegree*K1_14_4.seedDegree f+_≤_
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (coefficient_mono le))
      ((Nat.mul_le_mul (Nat.sub_le_sub_right (max_le_max_left 3 le) _) le).trans_eq (Nat.mul_comm ..))

variable {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}
variable {H:Jet} {m r:JointLedger.Book} (P:Pair F Crt H m r)
variable {G:Pade.Row SeedField} (N:Native G)

theorem count {content:ℕ} {onEq:Equation} (s:UnionPartition.Data P N content onEq)
    (hhi:M.overhead.toNat≤2557) (small:content-G.graphDegree<64)
    (charM:(2*(content-G.graphDegree)-1)*m.seedMass<p) (charR:(2*(content-G.graphDegree)-1)*r.seedMass<p)
    {lo hi v:ℕ} (low:lo≤onEq.natDegree) (high:onEq.natDegree≤hi) (seedMax:K1_14_4.seedDegree onEq≤v)
    (constant ordinate seed:ℤ)
    (onPrice:((labels (F:=F) (owning N.poly (P.main∪P.rescue))).card:ℤ)≤
      constant+ordinate*onEq.natDegree+seed*K1_14_4.seedDegree onEq) :
    (Γ.card:ℤ)≤bill m r (content-G.graphDegree) lo hi v constant ordinate seed := by
  let off:=content-G.graphDegree
  let sd:=K1_14_4.seedDegree
  let onM:=mass (ownerSources N.poly P.aSrc) 1
  let onR:=mass (ownerSources N.poly P.bSrc) 1
  have mc:=s.leftRoom
  have rc:=s.rightRoom
  have ls:sd s.left≤m.seedMass:=(Nat.le_add_left ..).trans (mc.trans P.boundsM)
  have rs:sd s.right≤r.seedMass:=(Nat.le_add_left ..).trans (rc.trans P.boundsR)
  have pl:=off_price (F:=F) hhi s.leftProjection off s.leftDegree small
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 s.leftDegree) _) ls).trans_lt charM)
  have pr:=off_price (F:=F) hhi s.rightProjection off s.rightDegree small
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 s.rightDegree) _) rs).trans_lt charR)
  have wa:=UnionPartition.credit P.aSrc P.mainActive P.wm
  have wb:=UnionPartition.credit P.bSrc P.rescueActive P.wr
  rw [←P.mainOrd,←P.mainSeed] at wa
  rw [←P.rescueOrd,←P.rescueSeed] at wb
  have joint:P.paid.card+m.ordinateCredit*mass P.aSrc 0+m.seedCredit*mass P.aSrc 1+
      r.ordinateCredit*mass P.bSrc 0+r.seedCredit*mass P.bSrc 1≤m.fee+r.fee:=by have:=P.bill;omega
  apply UnionLedger.count (Γ.card:ℤ) P.paid.card (labels (F:=F) (owning N.poly (P.main∪P.rescue))).card
    (labels (F:=F) (outside N.poly P.main)).card (labels (F:=F) (outside N.poly P.rescue)).card
    m.fee r.fee m.seedMass r.seedMass m.ordinateCredit r.ordinateCredit m.seedCredit r.seedCredit
    (mass P.aSrc 0) (mass P.bSrc 0) (mass P.aSrc 1) (mass P.bSrc 1) onM onR (sd s.left) (sd s.right)
    onEq.natDegree (sd onEq) lo hi v (degreeCost off) (off*(max 3 off-1):ℕ) constant ordinate seed
  · exact_mod_cast s.cover
  · exact_mod_cast joint
  · exact onPrice
  · exact_mod_cast (pl.trans_eq (Nat.add_comm ..))
  · exact_mod_cast (pr.trans_eq (Nat.add_comm ..))
  · exact_mod_cast mc
  · exact_mod_cast rc
  · exact_mod_cast P.boundsM
  · exact_mod_cast P.boundsR
  · exact_mod_cast s.onGrade
  · exact_mod_cast s.onSeed
  · exact_mod_cast low
  · exact_mod_cast high
  · exact_mod_cast seedMax
  · exact ⟨Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,
      Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _,Nat.cast_nonneg _⟩

end
end Research6969.WholeGraph
end Z6969Source0860

-- Source: Research6969.WholeAffine
section Z6969Source0861
set_option autoImplicit true
namespace Research6969.WholeAffine
noncomputable section
open Finset Polynomial
open K1 (K p)
open K1_14 (Equation Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active mass)
open K1_14_3 (Surface Parent SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NearBook (owning outside)
open JointLedger (Book markedDebit)
open TransitionPacket (Pair)
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000

def fee (d w:ℕ):ℕ:=p*w+(3*(d*w)^2*(262144-d)^3)/(179730-d)^3

private theorem debit_mono (b:Book):Monotone (markedDebit b):=by
  intro i j le
  by_cases zero:i=0
  · simp [zero,markedDebit]
  · have jn:j≠0:=by omega
    simp only [markedDebit,ite_eq_right zero,ite_eq_right jn]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (GraphLedger.coefficient_mono le) _))
      (Nat.mul_le_mul (Nat.sub_le_sub_right (max_le_max_left 3 le) _) le)

private theorem off_bound {u del} {M:Model u del} {Γ S:Finset K} (F:Family M Γ) (sub:S⊆Γ)
    (hi:M.overhead.toNat≤2557) (b:Book) (weights:Fin 4→ℕ) (wc:b.seedCredit=weights 1+weights 2)
    (parents:Finset Surface) {f:Equation} (project:JointProjection.Product parents f) {off:ℕ}
    (degree:f.natDegree≤off) (small:off<64) (safe:(2*off-1)*b.seedMass<p)
    (sources:Finset (Ideal Ambient)) (active:∀J∈sources,Active J)
    (origins:∀q∈parents,∃J∈sources,q.asIdeal=J.comap K1_14_2.toJet) (cap:mass sources 1≤b.seedMass)
    (marks:∀z∈S,∃q∈parents,OnSurface F q z) :
    S.card≤(∑k,weights k*mass sources k)+markedDebit b off := by
  let v:=K1_14_4.seedDegree f
  have fit:=((JointProjection.measures project sources active origins).2).trans cap
  have price:=JointMarked.owned_count F sub hi f project.primitive project.separable (degree.trans_lt small)
    (le_rfl:K1_14_4.seedDegree f≤v) ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 degree) _) fit).trans_lt safe)
    (by intro z hz;obtain ⟨q,hq,on⟩:=marks z hz
        have h:=on (C f) (project.vanishes hq)
        simpa [K1_14.jetAt,Polynomial.eval_map] using h)
  have credit:=JointProjection.credit project sources active origins weights (Nat.zero_le _) (le_rfl : v≤_)
  simp only [Nat.mul_zero,Nat.zero_add,←wc] at credit
  exact price.trans ((JointLedger.marked_le b f.natDegree v fit).trans (Nat.add_le_add credit (debit_mono b degree)))

/-- Count every on-graph mark once across the two actual packets. Each
off-graph projection then consumes only its own native seed credit. -/
theorem price {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {H:Jet} {m r} (P:Pair F Crt H m r) (hi:M.overhead.toNat≤2557)
    {d w c:ℕ} (wp:0<w) (char:w<p) (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (linear:G.graphDegree=1)
    (width:K1_14_2_2_2_1.seedDegree N.poly≤w)
    {f:Equation} (pr:ProjectedProduct (P.main∪P.rescue) f) (large:c<f.natDegree)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue)) c)
    (small:c-1<64) (safeM:(2*(c-1)-1)*m.seedMass<p) (safeR:(2*(c-1)-1)*r.seedMass<p) :
    Γ.card≤m.fee+r.fee+markedDebit m (c-1)+markedDebit r (c-1)+fee d w := by
  classical
  let A:=P.main;let B:=P.rescue
  let X₀:=owning N.poly (A∪B)
  let L₀:=outside N.poly A
  let R₀:=outside N.poly B
  have geo q (hq:q∈A∪B):Parent q:=(mem_union.mp hq).elim (fun h=>(P.mainGeo q h).1) (fun h=>(P.rescueGeo q h).1)
  obtain ⟨_,J,_,off,deg,_⟩:=NearTerminal.partition geo pr c large N gp control
  have fullOff:JointProjection.Product (outside N.poly (A∪B)) J:=off
  rw [linear] at deg
  obtain ⟨l,lp⟩:=JointProjection.exists_product L₀ (fun q h=>(P.mainGeo q (mem_filter.mp h).1).1)
  obtain ⟨r',rp⟩:=JointProjection.exists_product R₀ (fun q h=>(P.rescueGeo q (mem_filter.mp h).1).1)
  have left:l∣J:=lp.divides (fun q h=>fullOff.vanishes (mem_filter.mpr ⟨mem_union_left _ (mem_filter.mp h).1,(mem_filter.mp h).2⟩))
  have right:r'∣J:=rp.divides (fun q h=>fullOff.vanishes (mem_filter.mpr ⟨mem_union_right _ (mem_filter.mp h).1,(mem_filter.mp h).2⟩))
  let marks (s:Finset Surface):=Γ.filter fun z=>∃q∈s,OnSurface F q z
  have coverage:Γ⊆P.paid∪(marks X₀∪(marks L₀∪marks R₀)):=by
    intro z hz
    rcases P.cover z hz with paid|⟨_,q,hq,on⟩|⟨_,_,q,hq,on⟩
    · exact mem_union_left _ paid
    · by_cases owner:N.poly∈q.asIdeal
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨mem_union_left _ hq,owner⟩,on⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨hq,owner⟩,on⟩)))
    · by_cases owner:N.poly∈q.asIdeal
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨mem_union_right _ hq,owner⟩,on⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,q,mem_filter.mpr ⟨hq,owner⟩,on⟩)))
  have leftCost:=off_bound F (filter_subset _ _) hi m P.wm P.mainSeed L₀ lp ((natDegree_le_of_dvd left fullOff.primitive.ne_zero).trans deg)
    small safeM P.aSrc P.mainActive (fun q h=>P.mainOrigin q (mem_filter.mp h).1) P.boundsM
    (fun _ h=>(mem_filter.mp (show _∈marks L₀ from h)).2)
  have rightCost:=off_bound F (filter_subset _ _) hi r P.wr P.rescueSeed R₀ rp ((natDegree_le_of_dvd right fullOff.primitive.ne_zero).trans deg)
    small safeR P.bSrc P.rescueActive (fun q h=>P.rescueOrigin q (mem_filter.mp h).1) P.boundsR
    (fun _ h=>(mem_filter.mp (show _∈marks R₀ from h)).2)
  have weightBound:∀ j i,(N.poly.coeff j).coeff i∈MvPolynomial.restrictWeightAtMost (fun _=>1) w:=by
      intro j i
      apply MvPolynomial.mem_restrictWeightAtMost.mpr
      intro a ha
      rw [←Finsupp.degree_eq_weight_one]
      exact (MvPolynomial.le_totalDegree ha).trans ((K1_14_2_2_2_1.seedDegree_le N.poly w).mp width j i)
  have owned:NativeAffineRows.Owned F (marks X₀) X₀ N:=by
    intro z hz
    obtain ⟨q,hq,on⟩:=(mem_filter.mp hz).2
    exact ⟨q,hq,(mem_filter.mp hq).2,on⟩
  have aff:(marks X₀).card≤fee d w:=NativeAffineTariff.price_floor F (filter_subset _ _) N gp linear w wp weightBound
    char d phys tame dp gap (by decide) owned
  change (marks L₀).card≤_ at leftCost
  change (marks R₀).card≤_ at rightCost
  have all:Γ.card≤P.paid.card+((marks X₀).card+((marks L₀).card+(marks R₀).card)):=
    (card_le_card coverage).trans ((card_union_le ..).trans (Nat.add_le_add_left ((card_union_le ..).trans
      (Nat.add_le_add_left (card_union_le ..) _)) _))
  have bill:=P.bill
  omega

end
end Research6969.WholeAffine
end Z6969Source0861

-- Source: Research6969.UnionTariffs
section Z6969Source0862
set_option autoImplicit true
namespace Research6969.UnionTariffs
noncomputable section
open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet Equation FX atX graphEval jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open NativeSurfaceCount (label)
open NearBook (owning)
open UnionPartition (labels)
open scoped Classical Differential
set_option maxRecDepth 9000
set_option maxHeartbeats 1600000

variable {u del} {M:Model u del} {Γ} (F:Family M Γ) {G:Pade.Row SeedField} (N:Native G) (parents:Finset Surface)

abbrev group:=labels (F:=F) (owning N.poly parents)

theorem owners:NativeAffineRows.Owned F (group F N parents) (owning N.poly parents) N:=by
  intro z h
  obtain ⟨q,hq,on⟩:=(mem_filter.mp h).2
  exact ⟨q,hq,(mem_filter.mp hq).2,on⟩

theorem marked {f:Equation} (pr:ProjectedProduct (owning N.poly parents) f) (hi:M.overhead.toNat≤2557)
    {g:ℕ} (cap:f.natDegree≤g) (small:g<64) (char:(2*f.natDegree-1)*K1_14_4.seedDegree f<p):
    (group F N parents).card≤JointLedger.coefficient g*K1_14_4.seedDegree f+g*(max 3 g-1):=by
  let v:=K1_14_4.seedDegree f
  have cost:=JointMarked.owned_count F (filter_subset _ _) hi f pr.primitive pr.separable (cap.trans_lt small)
    le_rfl char (by intro z hz;obtain ⟨q,hq,on⟩:=(mem_filter.mp (show z∈group F N parents from hz)).2
                    simpa [jetAt,Polynomial.eval_map] using on (C f) (pr.vanishes q hq))
  have nz:f.natDegree≠0:=pr.positive.ne'
  refine cost.trans ?_
  rw [JointMarked.price,ite_eq_right nz,←Nat.mul_assoc]
  change JointLedger.coefficient f.natDegree*v+_≤_
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (GraphLedger.coefficient_mono cap))
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (max_le_max_left 3 cap) _) cap).trans_eq (Nat.mul_comm ..))

theorem affine {d w:ℕ} (gp:G.primitive) (linear:G.graphDegree=1) (wp:0<w)
    (char:w<p) (width:K1_14_2_2_2_1.seedDegree N.poly≤w)
    (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p) :
    (group F N parents).card≤WholeAffine.fee d w:=by
  have bounds:∀j i,(N.poly.coeff j).coeff i∈MvPolynomial.restrictWeightAtMost (fun _=>1) w:=by
    intro j i
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [←Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le ..).mp width j i)
  exact NativeAffineTariff.price_floor F (filter_subset _ _) N gp linear w wp bounds char d phys tame dp gap
    (by decide) (owners F N parents)

theorem surface {d w:ℕ} (gp:G.primitive) (large:2≤G.graphDegree) (wp:0<w)
    (char:(2*G.graphDegree-1)*w<p) (width:K1_14_2_2_2_1.seedDegree N.poly≤w)
    (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p)
    {f:Equation} (pr:ProjectedProduct (owning N.poly parents) f):
    (group F N parents).card≤(2*G.graphDegree-1)*((p+1)*w)+f.natDegree*JointRouted.seedWeight d w^2+
      2*K1_14_4.seedDegree f*JointRouted.seedWeight d w*JointRouted.ordWeight d (G.graphDegree-1):=by
  have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
  have c:=NativeSurfaceCount.price_owned F (filter_subset _ _) pr N gp large wp
    ((K1_14_2_2_2_1.seedDegree_le ..).mp width) ((K1_14_4.seedDegree_le_iff ..).mp le_rfl)
    char phys dp gap fit tame (owners F N parents)
  exact NativeSurfaceCount.round_price c

theorem seedless {d:ℕ} (gp:G.primitive) (large:2≤G.graphDegree)
    (width:K1_14_2_2_2_1.seedDegree N.poly=0)
    (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p) {f:Equation}
    (pr:ProjectedProduct (owning N.poly parents) f) :
    (group F N parents).card≤f.natDegree*JointRouted.seedWeight d 0^2+
      2*K1_14_4.seedDegree f*JointRouted.seedWeight d 0*JointRouted.ordWeight d (G.graphDegree-1) := by
  classical
  let T:=group F N parents
  let ev (z:K):=evaluate (label (M.label z)) (atX (F.scalar z))
  have seed:=((K1_14_2_2_2_1.seedDegree_le N.poly 0).mp width.le)
  have law z (hz:z∈T):ev z (den N)*atX (F.scalar z).derivative=ev z (rhs N):=by
    obtain ⟨q,_,hit,atQ⟩:=owners F N parents z hz
    exact NativeGraphMarks.mark_law N gp hit atQ
  have on z (hz:z∈T):ev z f=0:=by
    obtain ⟨q,hq,_,atQ⟩:=owners F N parents z hz
    simpa [jetAt,ev,label,evaluate,graphEval] using atQ (C f) (pr.vanishes q hq)
  have degree z (hz:z∈T):(F.scalar z).natDegree≤d:=by
    rcases (F.mark z (mem_filter.mp hz).1).scalar_degree with zero|bd
    · simp [zero]
    · change ((F.scalar z).natDegree:ℤ)≤131071+M.overhead at bd;omega
  have bval:JointRouted.seedWeight d 0=4:=by simp [JointRouted.seedWeight]
  rw [bval]
  by_cases zero:K1_14_4.seedDegree f=0
  · have card:=ZeroSeeds.roots F (filter_subset _ _) f pr.primitive.ne_zero
      (fun i=>Nat.eq_zero_of_le_zero ((K1_14_4.seedDegree_le_iff ..).mp zero.le i)) on
    simp only [zero,Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
    exact card.trans (Nat.le_mul_of_pos_right _ (by decide))
  let bad:=T.filter fun z=>ev z (den N)=0
  have inject:Function.Injective M.label:=fun _ _ eq=>sub_left_inj.mp eq
  have outside:=NativeGraphExceptional.singular_count N gp (fun _=>0)
    (fun j i z=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (seed j i))
    (by simp only [Nat.mul_zero];decide) bad _ inject.injOn (fun z=>atX (F.scalar z))
    (fun z h=>(mem_filter.mp h).2) (by
      intro z hz;have e:=law z (mem_filter.mp hz).1;rw [(mem_filter.mp hz).2,zero_mul] at e;exact e.symm)
  have empty:bad=∅:=by apply card_eq_zero.mp;simpa using outside
  have regular z (hz:z∈T):ev z (den N)≠0:=by intro no;have a:z∈bad:=mem_filter.mpr ⟨hz,no⟩;simp [empty] at a
  obtain ⟨dy,ny⟩:=NativeGraphMarks.equation_degrees N gp
  have wordCount:=ZeroSeeds.line F (filter_subset _ _) (by omega:0<G.graphDegree-1) dp gap tame (den N) (rhs N) dy
    (ny.trans (by omega)) (fun i=>Nat.eq_zero_of_le_zero (seed 1 i)) (fun i=>by simpa [rhs] using Nat.eq_zero_of_le_zero (seed 0 i))
    degree (fun z hz=>⟨law z hz,regular z hz⟩)
  let R:=MarkedAdaptive.price (Fintype.card I) d 179730
  have bound:R*(G.graphDegree-1:ℕ)≤(JointRouted.ordWeight d (G.graphDegree-1):ℚ):=by
    unfold JointRouted.ordWeight
    have extra:(0:ℚ)≤((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ):=by positivity
    have ceil:=Nat.le_ceil (R*(G.graphDegree-1:ℕ)+((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ))
    push_cast
    linarith
  have wg:(T.card:ℚ)≤(JointRouted.ordWeight d (G.graphDegree-1):ℚ):=wordCount.trans
    (by simpa only [R,mul_comm (MarkedAdaptive.price (Fintype.card I) d 179730)] using bound)
  have n:T.card≤JointRouted.ordWeight d (G.graphDegree-1):=by exact_mod_cast wg
  exact n.trans ((Nat.le_mul_of_pos_left _ (show 0<2*K1_14_4.seedDegree f*4 by positivity)).trans (Nat.le_add_left ..))

end
end Research6969.UnionTariffs
end Z6969Source0862

-- Source: Research6969.CaseBounds
section Z6969Source0863
set_option autoImplicit true
namespace Research6969.CaseBounds
noncomputable section
open K1_14 (Equation FX L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (SeedField Surface Parent)
open Research6966
open PadeNativeQuotient (Native)
open MeasuredBound (Test Kind)
open Finset
set_option maxHeartbeats 1400000
set_option maxRecDepth 11000

structure Cap where
  grade:ℕ
  seed:ℕ
deriving DecidableEq

def Cap.step (c:Cap) (t:Test) (a lo wt:ℕ) (high:Option ℕ):Cap:=
  if t.source.jet=a ∧ 0<t.seedFloor ∧ t.seedFloor≤lo ∧ t.source.weight≤wt then
    ⟨min c.grade t.degreeCap,match high with
      | some v=>if t.kind=.triangle then min c.seed (t.totalCap v) else c.seed
      | none=>c.seed⟩
  else c

def run (a lo wt:ℕ) (high:Option ℕ) : List Test→Cap→Cap
  | [],c=>c
  | t::rest,c=>run a lo wt high rest (c.step t a lo wt high)

theorem sound (ts:List Test) {a lo wt h:ℕ} {high:Option ℕ} {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (floor:2314≤h) (ceil:h≤2411) {S:Finset Surface}
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (deg:G.graphDegree=a)
    {H:Equation} (on:NativeWitnessBank.witnessed N S H) (low:lo≤seedDegree N.poly)
    (up:∀ v,high=some v→seedDegree N.poly≤v)
    (phys:HelperPhysicalModel.Model Crt N.poly) (physical:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (c:Cap) (grade:H.natDegree≤c.grade) (seed:K1_14_4.seedDegree H≤c.seed):
    H.natDegree≤(run a lo wt high ts c).grade ∧ K1_14_4.seedDegree H≤(run a lo wt high ts c).seed := by
  induction ts generalizing c with
  | nil=>exact ⟨grade,seed⟩
  | cons t tail ih=>
    apply ih
    · dsimp only [Cap.step]
      split
      · rename_i accepted
        obtain ⟨same,pos,minimal,pole⟩:=accepted
        have bounds:=t.bounds Crt word floor ceil geo pass N gp (deg.trans same.symm) on
          (minimal.trans low) (pos.trans_le (minimal.trans low)) phys (pole.trans physical)
        exact le_min grade bounds.1
      · exact grade
    · dsimp only [Cap.step]
      split
      · rename_i accepted
        obtain ⟨same,pos,minimal,pole⟩:=accepted
        cases hHigh:high with
        | none=>exact seed
        | some v=>
          simp only
          split_ifs with tri
          · have bounds:=t.bounds Crt word floor ceil geo pass N gp (deg.trans same.symm) on
              (minimal.trans low) (pos.trans_le (minimal.trans low)) phys (pole.trans physical)
            exact le_min seed (bounds.2 tri v (up v hHigh))
          · exact seed
      · exact seed

end
end Research6969.CaseBounds
end Z6969Source0863

-- Source: Research6969.CertifiedCell
section Z6969Source0864
set_option autoImplicit true
namespace Research6969.CertifiedCell
noncomputable section
open K1 (K I p)
open K1_14 (Equation Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct Parent)
open Lower6960.Far6969RescueGeometry (Model Family word)
open Research6966
open Finset Polynomial
open PadeNativeQuotient (Native)
open TransitionPacket (Pair)
open JointLedger (Book)
open JointRouted (seedWeight ordWeight)
open scoped Classical
set_option maxHeartbeats 2400000
set_option maxRecDepth 15000

inductive Method where | excluded | marked | affine | surface
deriving DecidableEq
structure Row where
  minGrade:ℕ
  maxGrade:ℕ
  content:ℕ
  graph:ℕ
  lowSeed:ℕ
  highSeed:Option ℕ
  tests:List MeasuredBound.Test
  method:Method

abbrev target:ℕ:=274779381266040419
abbrev d:ℕ:=133482
def Row.weight (b:Row):ℕ:=b.graph*(131071-2411)-1
def Row.off (b:Row):ℕ:=b.content-b.graph
def Row.lower (b:Row):ℕ:=b.minGrade-b.off
def Row.cap (b:Row) (m r:Book):CaseBounds.Cap:=
  CaseBounds.run b.graph b.lowSeed b.weight b.highSeed b.tests ⟨b.maxGrade,m.seedMass+r.seedMass⟩
def Row.affineFee (b:Row):ℕ:=WholeAffine.fee d (max 1 (b.highSeed.getD 0))
def Row.side (b:Row):ℕ:=seedWeight d (b.highSeed.getD 0)
def Row.y (b:Row):ℕ:=ordWeight d (b.graph-1)

def Row.check (b:Row) (m r:Book):Prop:=
  let bound:=b.cap m r
  b.content<b.minGrade ∧ b.off<64 ∧ (2*b.off-1)*m.seedMass<p ∧ (2*b.off-1)*r.seedMass<p ∧
  match b.method with
  | .excluded=>bound.grade<b.lower
  | .marked=>bound.grade<64 ∧ (2*bound.grade-1)*bound.seed<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed (bound.grade*(max 3 bound.grade-1):ℕ) 0 (JointLedger.coefficient bound.grade)≤target
  | .affine=>b.graph=1 ∧ b.highSeed.isSome=true ∧ max 1 (b.highSeed.getD 0)<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed b.affineFee 0 0≤target
  | .surface=>2≤b.graph ∧ b.highSeed.isSome=true ∧ (2*b.graph-1)*(b.highSeed.getD 0)<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed
      ((2*b.graph-1)*((p+1)*(b.highSeed.getD 0)):ℕ) (b.side^2:ℕ) (2*b.side*b.y:ℕ)≤target

instance (b:Row) (m r:Book):Decidable (b.check m r):=by
  unfold Row.check
  cases b.method <;> infer_instance

theorem Row.proves (b:Row) {m r:Book} (ok:b.check m r)
    {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {H:Jet} (P:Pair F Crt H m r) (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    {f:Equation} (pr:ProjectedProduct (P.main∪P.rescue) f) (minGrade:b.minGrade≤f.natDegree) (maxGrade:f.natDegree≤b.maxGrade)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (degree:G.graphDegree=b.graph)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue)) b.content)
    (low:b.lowSeed≤seedDegree N.poly) (upper:∀v,b.highSeed=some v→seedDegree N.poly≤v):
    Γ.card≤target := by
  classical
  let S:=P.main∪P.rescue
  have geo q (hq:q∈S):Parent q:=(mem_union.mp hq).elim (fun h=>(P.mainGeo q h).1) (fun h=>(P.rescueGeo q h).1)
  have pass q (hq:q∈S):TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q:=
    (mem_union.mp hq).elim (fun h=>(P.mainGeo q h).2.1) (fun h=>(P.rescueGeo q h).2.1)
  obtain ⟨gc,offSmall,guardM,guardR,pay⟩:=ok
  obtain ⟨onEq,offEq,seen,off,offCap,total⟩:=NearTerminal.partition geo pr b.content (gc.trans_le minGrade) N gp control
  obtain ⟨data⟩:=UnionPartition.data P N seen.1 off offCap
  have passOn q (hq:q∈NearBook.owning N.poly S):=pass q (mem_filter.mp hq).1
  have geoOn q (hq:q∈NearBook.owning N.poly S):=geo q (mem_filter.mp hq).1
  have slope:=NativeGraphMarks.slope_degree N gp
  obtain ⟨phys⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp) (by omega)
  have wt:=HelperWeightCap.weight_lower phys N.primitive.ne_zero (131071-M.overhead.toNat) (by omega)
  rw [HelperWeightCap.native_degree N gp,slope,degree] at wt
  have weight:b.weight≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw:=by
    have sw:=Nat.mul_le_mul_right b.graph (Nat.sub_le_sub_left hi 131071)
    unfold Row.weight
    rw [Nat.mul_comm b.graph]
    omega
  have rawDegree:=NearTerminal.subset_degree (show NearBook.owning N.poly S⊆S from filter_subset _ _) seen.1 pr
  have x:=K1_14_2_2.mass_mono (show NearBook.ownerSources N.poly P.aSrc⊆P.aSrc from filter_subset ..) 1
  have y:=K1_14_2_2.mass_mono (show NearBook.ownerSources N.poly P.bSrc⊆P.bSrc from filter_subset ..) 1
  have seedCap:=data.onSeed.trans (Nat.add_le_add (x.trans P.boundsM) (y.trans P.boundsR))
  have ⟨gcap,vcap⟩:=CaseBounds.sound b.tests Crt (word M) lo hi geoOn passOn N gp degree seen low upper phys weight
    (⟨b.maxGrade,m.seedMass+r.seedMass⟩:CaseBounds.Cap) (rawDegree.trans maxGrade) seedCap
  change onEq.natDegree≤(b.cap m r).grade at gcap
  change K1_14_4.seedDegree onEq≤(b.cap m r).seed at vcap
  have lower:b.lower≤onEq.natDegree:=by
    have cf:=offCap;rw [degree] at cf;unfold Row.lower Row.off;omega
  have small: b.content-G.graphDegree<64:=degree ▸ offSmall
  have guards:(2*(b.content-G.graphDegree)-1)*m.seedMass<p ∧ (2*(b.content-G.graphDegree)-1)*r.seedMass<p:=degree ▸ ⟨guardM,guardR⟩
  have budget:=WholeGraph.count P N data (hi.trans (by decide)) small guards.1 guards.2 lower gcap vcap
  have dh:131071+M.overhead≤(d:ℤ):=by change 131071+M.overhead≤(133482:ℤ);omega
  have ds:0<d:=by decide
  have gap:d<179730:=by decide
  have tp:d<p:=by decide
  let t:=UnionTariffs.group F N S
  have close (k y z:ℤ) (cp:(t.card:ℤ)≤k+y*onEq.natDegree+z*K1_14_4.seedDegree onEq)
      (paid:WholeGraph.bill m r b.off b.lower (b.cap m r).grade (b.cap m r).seed k y z≤target) :
      Γ.card≤target:=by
    have due:=budget k y z cp
    rw [degree] at due
    exact_mod_cast due.trans paid
  cases method:b.method with
  | excluded=>
    rw [method] at pay
    exact (Nat.not_lt_of_ge (lower.trans gcap) pay).elim
  | marked=>
    rw [method] at pay
    obtain ⟨legal,char,paid⟩:=pay
    have char':(2*onEq.natDegree-1)*K1_14_4.seedDegree onEq<p:=
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 gcap) _) vcap).trans_lt char
    have all:=UnionTariffs.marked F N S seen.1 (hi.trans (by decide)) gcap legal char'
    apply close _ _ _ _ paid
    simp only [Int.zero_mul,Int.add_zero]
    exact_mod_cast all.trans_eq (Nat.add_comm ..)
  | affine=>
    rw [method] at pay
    obtain ⟨eq,yes,char,paid⟩:=pay
    have up:seedDegree N.poly≤b.highSeed.getD 0:=upper _ (by cases h:b.highSeed <;>simp_all)
    have all:=UnionTariffs.affine F N S gp (degree.trans eq) (by omega:0<max 1 (b.highSeed.getD 0)) char
      (up.trans (le_max_right ..)) dh ds gap tp
    apply close _ _ _ _ paid
    simpa [Row.affineFee] using (show (t.card:ℤ)≤(WholeAffine.fee d (max 1 (b.highSeed.getD 0)):ℤ) by exact_mod_cast all)
  | surface=>
    rw [method] at pay
    obtain ⟨big,yes,char,paid⟩:=pay
    let U:=b.highSeed.getD 0
    have up:seedDegree N.poly≤U:=upper _ (by cases h:b.highSeed <;>simp_all [U])
    have nonlinear:2≤G.graphDegree:=big.trans_eq degree.symm
    have all:t.card≤(2*b.graph-1)*((p+1)*U)+onEq.natDegree*b.side^2+2*K1_14_4.seedDegree onEq*b.side*b.y:=by
      by_cases z:U=0
      · have empty:seedDegree N.poly=0:=by omega
        have small:=UnionTariffs.seedless F N S gp nonlinear empty dh ds gap tp seen.1
        have emptyWidth:b.highSeed.getD 0=0:=z
        simpa only [degree,t,Row.side,Row.y,U,emptyWidth,Nat.mul_zero,Nat.zero_add] using small
      · have cost:=UnionTariffs.surface F N S gp nonlinear (Nat.pos_of_ne_zero z) (degree ▸ char) up dh ds gap tp seen.1
        simpa only [degree,Row.side,Row.y] using cost
    apply close _ _ _ _ paid
    exact_mod_cast all.trans_eq (by dsimp [Row.side,Row.y]; ring)

end
end Research6969.CertifiedCell
end Z6969Source0864

-- Source: Research6969.FastCell
section Z6969Source0865
set_option autoImplicit true
namespace Research6969.FastCell
open JointRouted (seedWeight ordWeight)
open K1 (I)
set_option maxHeartbeats 800000

def ceilRatio (n d:ℕ):ℕ:=(-((-(n:ℤ))/(d:ℤ))).toNat
theorem ratio (n d:ℕ) : ceilRatio n d=⌈(n:ℚ)/d⌉₊:=by
  rw [←Int.ceil_toNat,Rat.ceil_natCast_div_natCast]
  rfl

def side (u:ℕ):ℕ:=ceilRatio (2*262144*133482*u) 179730+4
def ordinate (r:ℕ):ℕ:=ceilRatio (2*262144*133482*r*(179730-133482)+(262144-133482)*179730) (179730*(179730-133482))+4

theorem side_eq (u:ℕ):seedWeight CertifiedCell.d u=side u:=by
  unfold seedWeight side MarkedAdaptive.price
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18),ratio]
  congr 2
  dsimp [CertifiedCell.d]
  push_cast
  ring

theorem ordinate_eq (r:ℕ):ordWeight CertifiedCell.d r=ordinate r:=by
  unfold ordWeight ordinate MarkedAdaptive.price
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18),ratio]
  congr 2
  dsimp [CertifiedCell.d]
  norm_num
  ring


/-- A closed decision procedure for case receipts; expensive section
proofs in the interpolation sources are never inspected by these tests. -/
def accepts (b:CertifiedCell.Row) (m r:JointLedger.Book):Bool:=
  let g:=(b.cap m r).grade
  let v:=(b.cap m r).seed
  let offs:=b.off
  decide (b.content<b.minGrade ∧ offs<64 ∧ (2*offs-1)*m.seedMass<K1.p ∧ (2*offs-1)*r.seedMass<K1.p) &&
    match b.method with
    | .excluded=>decide (g<b.lower)
    | .marked=>decide (g<64 ∧ (2*g-1)*v<K1.p ∧
        WholeGraph.bill m r offs b.lower g v (g*(max 3 g-1):ℕ) 0 (JointLedger.coefficient g)≤CertifiedCell.target)
    | .affine=>decide (b.graph=1 ∧ b.highSeed.isSome=true ∧ max 1 (b.highSeed.getD 0)<K1.p ∧
        WholeGraph.bill m r offs b.lower g v b.affineFee 0 0≤CertifiedCell.target)
    | .surface=>
      let u:=b.highSeed.getD 0
      let x:=side u
      let y:=ordinate (b.graph-1)
      decide (2≤b.graph ∧ b.highSeed.isSome=true ∧ (2*b.graph-1)*u<K1.p ∧
        WholeGraph.bill m r offs b.lower g v ((2*b.graph-1)*((K1.p+1)*u):ℕ) (x^2:ℕ) (2*x*y:ℕ)≤CertifiedCell.target)

theorem checked {b:CertifiedCell.Row} {m r:JointLedger.Book} (h:accepts b m r=true):b.check m r:=by
  unfold accepts at h
  obtain ⟨guard,caseOK⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨large,small,mc,rc⟩:=of_decide_eq_true guard
  refine ⟨large,small,mc,rc,?_⟩
  cases method:b.method <;> rw [method] at caseOK <;>
    simpa only [CertifiedCell.Row.side,CertifiedCell.Row.y,side_eq,ordinate_eq] using of_decide_eq_true caseOK

end Research6969.FastCell
end Z6969Source0865
