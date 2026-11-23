import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.ZdY8S8d
import ProximityPrize.SubmissionLower.Zqby9gc
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Fin.lastCases → zsB, Finset → zJe, Finset.sup_le_iff → zUp, Finsupp.mapDomain → z8D, Finsupp.optionElim_apply_none → z6S, Finsupp.optionElim_apply_some → zd8, LinearMap.range → zWl, Module.Finite → zAa, Module.finrank → zsE, Module.rank → z1x, MvPolynomial.C → znf, MvPolynomial.coeff_C_mul → z06, MvPolynomial.eval → zY9, MvPolynomial.le_degreeOf_of_mem_support → zTo, MvPolynomial.le_weightedTotalDegree → z6P, Nat.sub_add_cancel → zxt, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Submodule → zpI, Submodule.mem_iInf → zxR
section
set_option autoImplicit true
namespace qBPZs8a
noncomputable section
open Polynomial
open P6 (K)
open P6_7_1
open cu (FX Jet kr rD)
open DP (Source complete U4)
open pI (oU)
open akZ (btm)
abbrev last :=introductions.length
abbrev shape (i:Intro) :=(introductions.get i).2
abbrev dI (i:Intro) :=(introductions.get i).1
abbrev referenceIndex :Intro:=⟨8,by decide⟩
def Mark (x :Input) (f :Jet) (γ:K) :Prop :=
  rD f (x.M.label γ) (x.F.scalar γ)=0
structure Reference (x :Input) (P:Poles x) where
  raw:Source
  mem:raw∈complete P.crt x.word (shape referenceIndex) (cutoff (shape referenceIndex))
  nonzero :U4 raw≠0
abbrev fixedContentFee :ℕ:=0x1b61671120
abbrev eHB:ℕ:=0xbd5a511066e
abbrev akj:ℕ:=0x471c0984879
abbrev projectionFee :ℕ:=0x49c98b7519e33
abbrev LineRow :=MvPolynomial (Fin 3) FX
def LineCaps (f :Jet) (g:LineRow) :Prop :=
  ∀ e∈g.support,e 1+e 2≤wD f 0∧e 2≤wD f 1∧e 0≤wD f 2
def LineRoot (x :Input) (g:LineRow) (γ:K) :Prop :=
  ∃ z :cu.L,
    let v := ![algebraMap cu.L FX z,kr (x.F.scalar γ),kr (x.F.scalar γ).derivative]
    zY9 v g=0∧zY9 v (MvPolynomial.pderiv 2 g)≠0
structure LastCut (x :Input) (S:zJe K) (f :Jet) where
  cut:Jet
  proper : ¬ f∣cut
  line :Bool
  row:LineRow
  caps :oU cut (if line then btm f else aOm f)
  separant:line=true→cut=f.derivative
  line_caps :line=true→LineCaps f row
  line_pos :line=true→0<wD f 2
  Eh : ∀ γ∈x.Γ,Mark x f γ →
    γ∈S∨Mark x cut γ∨(line=true∧LineRoot x row γ)
end
end qBPZs8a
end
section
set_option autoImplicit true
namespace q3rjQGe
noncomputable section
open P6 (K p)
open P6_7_1
open cu (FX Jet Shape)
open gT (Ambient gk aQ Pp IZ iJ)
open pI (acW dual pN weight)
open TD (GM J2 FP)
open scoped Classical BigOperators
abbrev Free :=Fin 4
abbrev Trial:=Fin 5
abbrev bAL:=Fin 6
abbrev stage (i:Free) :=stages.get i.succ
abbrev termTrial:Trial:=Fin.last _
abbrev termStop:bAL:=termTrial.succ
def aHp (t:Trial) :Shape :=
  zsB terminal.box (fun i:Free=>(stage i).free) t
def aV {x :Input} (P:Poles x) (t:Trial) :zpI FX Jet :=
  zsB (rectBank P terminal (rectCut terminal))
    (fun i:Free=>P.rows (stage i).free (cutoff (stage i).free)) t
def passes {x :Input} (P:Poles x) (t:Trial) (q:Ideal Ambient) :Prop :=
  ∀ g∈aV P t,iJ g∈q
def QV {x P R} (O:OriginCover x P R) (f :Jet) (s :bAL) :zJe (Ideal Ambient) :=
  (O.parents f).filter fun q=>(0<s.val→dual q) ∧
    ∀ t:Trial,t.val+1<s.val→passes P t q
def stopped {x P R} (O:OriginCover x P R) (f :Jet) :bAL→zJe (Ideal Ambient) :=
  Fin.cases ((QV O f 0).filter fun q => ¬ dual q)
    (fun t=>(QV O f t.succ).filter fun q => ¬ passes P t q)
def final {x P R} (O:OriginCover x P R) (f :Jet) :zJe (Ideal Ambient) :=
  (O.parents f).filter fun q=>dual q ∧ ∀ t,passes P t q
abbrev onMark (x :Input) (q:Ideal Ambient) (γ:K) :Prop :=
  IZ q (x.M.label γ) (x.F.scalar γ)
def marks (x :Input) (q:Ideal Ambient) :zJe K:=x.Γ.filter (onMark x q)
def onCurves (x :Input) (C:acW) :zJe K :=
  x.Γ.filter fun γ => ∃ q∈C.qv,onMark x q γ
def bankBook {x :Input} (P:Poles x) :zJe K :=
  x.Γ.filter fun γ => ∃ t:Trial,(∃ g∈aV P t,g≠0) ∧
    ∀ g∈aV P t,seedSpecialize g (x.M.label γ)=0
abbrev bankFee :ℕ:=0x1ba81a4dd
def asShape (a :Fin 3→ℕ) :Shape :=⟨0,a 0,a 1,a 2⟩
def originShape (o:Origin) :Shape :=
  if h:o.val< introductions.length then (introductions.get ⟨_,h⟩).2
  else
    let v :=introCap o.val
    ⟨0,164+19*(v 0-1),50+19*(v 1-1),490+19*v 2⟩
def mixedCols (s :Shape) :Fin 4→Fin 3→ℕ :=
  ![![s.J,s.B-s.J,0],![0,s.U,s.J],![s.U,0,s.B],![0,0,s.U]]
def kK (a :Fin 3→ℕ) (s :Shape) (k :Fin 4) :ℚ :=
  ∑ j,(a j:ℚ)*mixedCols s k j
def originBox (o:Origin) :GM:=kK (introCap o.val) (originShape o)
def resourceBill (v :Origin→Fin 3→ℚ) :ℚ :=
  ∑ o:Origin,∑ j:Fin 3,
    let old:=((List.ofFn v).take o.val).foldl (fun a w=>max a (w j)) 0
    (max (v o j) old-old)*introCap o.val j
def initialBound (k :Fin 4) :ℚ :=
  let v :=introCap lastOrigin.val
  resourceBill (fun o j=>mixedCols (originShape o) k j) +
    (![v 0,v 2,2*v 0*v 2,v 2*v 2] :Fin 4→ℕ) k
def refShape (o:Origin) :Shape :=
  asShape fun j=>max (introCap o.val j) (bgK (originShape o) j)
def freeBound (o:Origin) (i:Free) (k :Fin 4) :ℚ :=
  kK (bgK (stage i).free) (refShape o) k/((stage i).dI+1 :ℚ)
def survivedBound (o:Origin) (s :bAL) (k :Fin 4) :ℚ :=
  ((List.ofFn (fun i:Free=>freeBound o i k)).take (s.val-1)).foldl min (originBox o k)
def memberCap (o:Origin) (s :bAL) (k :Fin 4) :ℚ :=
  min (survivedBound o s k) (initialBound k)
def allFreeCap (o:Origin) (k :Fin 4) :ℚ :=
  survivedBound o termStop k*(if o=lastOrigin then
    (∑ j,introCap o.val j:ℕ) else 1)
def afF (o:Origin) (f :Jet) (line :Bool) :Shape :=
  if line then asShape (wD f) else originShape o
def lineCharge (f :Jet) (line :Bool) :ℚ :=
  ((if line then lineFee (wD f 0) (wD f 1) (wD f 2) else 0:ℕ) :ℚ)
structure Geometry {x P R} (O:OriginCover x P R) :Prop where
  spend_order : ∀ f∈O.factors,wD f 1≤wD f 0
  initial : ∀ f∈O.factors,∀ k,
    J2 (O.parents f) k≤kK (wD f) (afF (O.origin f) f (O.line f)) k
  global : ∀ k,(∑ f∈O.factors,J2 (O.parents f) k)≤ initialBound k
  all_free : ∀ o k,(∑ f∈O.factors.filter (fun f=>O.origin f=o),
    J2 (QV O f termStop) k)≤allFreeCap o k
  member : ∀ f∈O.factors,∀ s,∀ q∈QV O f s,∀ k,
    (pN q k :ℚ)≤ memberCap (O.origin f) s k
structure aAU where
  factors :zJe Jet
  origin :Jet→Origin
  line :Jet→Bool
  stops :Jet→bAL→GM
  nonneg : ∀ f∈factors,∀ s k,0≤ stops f s k
  spend_order : ∀ f∈factors,wD f 1≤wD f 0
  line_ok : ∀ f∈factors,line f=true →
    origin f=lastOrigin∧0<wD f 1∧0<wD f 2
  nested : ∀ o:Origin,∀ j,
    (∑ f∈factors.filter (fun f=>o.val≤(origin f).val),wD f j)≤ introCap o.val j
  initial : ∀ f∈factors,∀ k,(∑ s,stops f s k) ≤
    kK (wD f) (afF (origin f) f (line f)) k
  global : ∀ k,(∑ f∈factors,∑ s,stops f s k)≤ initialBound k
  all_free : ∀ o k,(∑ f∈factors.filter (fun f=>origin f=o),
    stops f termStop k)≤allFreeCap o k
def rankPrice (o:Origin) :GM :=
  let B:=memberCap o 0 2
  let J:=min (memberCap o 0 1) B
  let T:=4*B/5
  let a :=min J (B-T/4)
  let V:=4*a-(2*a*a+T*a)/B
  let lambdaD:=(262144 :ℚ)*degree/P5_7.midAgreement
  let μ:=((262144-degree :ℕ) :ℚ)/(P5_7.midAgreement-degree :ℕ)
  if B=0 then 0 else ![0,max 0 (lambdaD*(T-1)+μ),max 1 (lambdaD*(V-1)+B+1),0]
def SS (j:Fin 3) (t:Trial) :GM:= fun k=>weight (aHp t) j k
def freeDegree (o:Origin) (i:Free) :ℚ :=
  FP (SS 0 i.castSucc) (memberCap o i.castSucc.succ)
def axisWeight:GM:= fun k =>
  (![terminal.z,terminal.B-terminal.J,terminal.J,0] :Fin 4→ℕ) k
def axisCap (o:Origin) :ℚ:=FP axisWeight (memberCap o termStop)
def planeCap (o:Origin) :ℚ :=
  FP (SS 0 termTrial) (memberCap o termStop)
abbrev gap:ℕ:=P5_7.midAgreement-degree
abbrev graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
abbrev axisRate (g:ℕ) :ℚ:=(p:ℚ)/g
abbrev linearRate :ℚ:=1+3*(262144 :ℚ)/gap
abbrev quadraticRate :ℚ:=13+8*(262144 :ℚ)/gap
def persistentRate (g:ℕ) :ℚ :=
  let a :=1+2*(262144 :ℚ)/P5_7.midAgreement*degree
  (2*(g:ℚ)-1)*a+((262144-degree :ℕ) :ℚ)/gap
def nativeSlope (d:ℚ) (e :ℕ) :ℚ:=d/(3*(e :ℚ))+4*e+8
def nativeRate (e g c W:ℕ) :ℚ :=
  max (e*(c+1)+e+g:ℕ)
    ((7+6*e :ℕ)+((2*e+1)*262144+(6*e-2)*W-3*e*e*degree :ℕ)/(gap:ℚ))
def NativeOK (e g c W M:ℕ) :Prop :=
  let E :=e+g
  let L:=(g+1)*c
  let j:=L/(c+1)
  0<c∧e*degree≤W∧M=W+1+j*degree∧E*degree<M ∧
    (c+1)*(degree*E*(E+1)/2+degree*j*(j+1)/2)<L*M ∧
    (2*e-1)*W-e*e*degree<p
def FreeRateOK (d a b:ℚ) :Prop :=
  0≤d∧d<(p:ℚ)∧max d (graphRate 55)≤a∧0≤b ∧
    ∀ e :ℕ,0<e→a<graphRate e →
      (1-a/graphRate e)*persistentRate e≤b ∨
      (e=1∧(1-a/graphRate e)*linearRate≤b) ∨
      (e=2∧16≤a∧quadraticRate*(graphRate e-a)/(graphRate e-16)≤b) ∨
      (3≤e ∧ ∃ g c W M,NativeOK e g c W M ∧
        let a₀:=nativeSlope d e
        a₀≤a∧nativeRate e g c W*(graphRate e-a)/(graphRate e-a₀)≤b)
def RectRateOK (kd u7 z a b:ℚ) :Prop :=
  0≤kd∧0≤u7∧u7<(p:ℚ)∧2*kd≤a ∧
    0<a∧a<(p:ℚ)∧2≤z∧0≤b ∧
    ∀ e :ℕ,0<e→a<axisRate e →
      (1-a/axisRate e)*persistentRate e≤b ∨
      (e=1∧(1-a/axisRate e)*linearRate≤b) ∨
      (e=2∧16≤ min z a∧quadraticRate*(axisRate e-a)/(axisRate e-16)≤b) ∨
      (3≤e ∧ ∃ g c W M,NativeOK e g c W M ∧
        let a₀:=nativeSlope (min u7 (2*kd)) e
        a₀≤ min z a∧nativeRate e g c W*(axisRate e-a)/(axisRate e-a₀)≤b)
abbrev AxisSection (q:Ideal Ambient) (a :Fin 2) :=
  gk (q.map (MvPolynomial.map (algebraMap FX aQ)) ⊔
    Ideal.span {Pp (if a=0 then (1 :Fin 4) else 0)})
structure RectCover extends acW where
  finite_axis : ∀ q∈qv,∀ a,zAa aQ (AxisSection q a)
def RectCover.kd (C:RectCover) (a :Fin 2) :ℕ :=
  ∑ q∈C.qv,zsE aQ (AxisSection q a)
def freePrice (a b:ℚ) (i:Free) :GM:= fun k =>
  (a+1)*SS 0 i.castSucc k+b*SS 1 i.castSucc k+SS 2 i.castSucc k
def rectPrice (z a b:ℚ) :GM:= fun k =>
  (z+a+1)*axisWeight k+b*SS 1 termTrial k+
    SS 0 termTrial k+SS 2 termTrial k
def stopPrice (a b:Origin→Free→ℚ) (z ar br :Origin→ℚ) (o:Origin) (s :bAL) :
    GM :=
  Fin.cases (rankPrice o)
    (zsB (rectPrice (z o) (ar o) (br o)) (fun i=>freePrice (a o i) (b o i) i)) s
structure cL where
  a :Origin→Free→ℚ
  b:Origin→Free→ℚ
  z :Origin→ℚ
  ar :Origin→ℚ
  br :Origin→ℚ
  free_ok : ∀ o i,FreeRateOK (freeDegree o i) (a o i) (b o i)
  rect_ok : ∀ o,RectRateOK (axisCap o) (planeCap o) (z o) (ar o) (br o)
  Ya : ∀ B:aAU,
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (stopPrice a b z ar br (B.origin f) s) (B.stops f s))) +
      bankFee+paidFee≤(prefixFee :ℚ)
end
end q3rjQGe
end
section
set_option autoImplicit true
namespace qiFSOoc
noncomputable section
open Finset Polynomial MvPolynomial
open cu (FX Equation Jet)
open P6_7_1
open private flatten from ProximityPrize.SubmissionLower.A0
open private a2f dGs from ProximityPrize.SubmissionLower.Z
private theorem unflatten (f :Equation) :
    optionEquivLeft FX (Fin 2) (flatten f)=f := by simp [flatten]
private theorem axis_le_iff (f :Equation) (a :Fin 2) (u:ℕ) :
    axisDegree f a≤u↔(flatten f).degreeOf (some a)≤u:= by
  rw [degreeOf_le_iff]
  rw [axisDegree,zUp]
  constructor
  · intro h d hd
    have hd' := MvPolynomial.mem_support_iff.mp hd
    rw [← optionEquivLeft_coeff_some_coeff_none FX (Fin 2),unflatten] at hd'
    have hj:d none∈f.support :=Polynomial.mem_support_iff.mpr (by
      intro hz
      exact hd' (by simp [hz]))
    exact (degreeOf_le_iff.mp (h _ hj)) _ (MvPolynomial.mem_support_iff.mpr hd')
  · intro h j _
    apply degreeOf_le_iff.mpr
    intro d hd
    have hd' := MvPolynomial.mem_support_iff.mp hd
    rw [← unflatten f,optionEquivLeft_coeff_coeff] at hd'
    simpa only [zd8] using h _ (MvPolynomial.mem_support_iff.mpr hd')
private theorem flat_axis (f :Equation) (a :Fin 2) :
    (flatten f).degreeOf (some a)=axisDegree f a :=
  le_antisymm ((axis_le_iff f a _).mp le_rfl) ((axis_le_iff f a _).mpr le_rfl)
private theorem axis_mul {g q:Equation} (hg:g≠0) (hq:q≠0) (a :Fin 2) :
    axisDegree (g*q) a=axisDegree g a+axisDegree q a := by
  simp only [← flat_axis,map_mul]
  exact degreeOf_mul_eq (by simpa using hg) (by simpa using hq)
theorem axis_pow {f :Equation} (hf :f≠0) (a :Fin 2) (r :ℕ) :
    axisDegree (f^r) a=r*axisDegree f a := by
  simp only [← flat_axis,map_pow]
  exact degreeOf_pow_eq _ _ _ (by simpa using hf)
private theorem one_ne_zero_fin: (1 :Fin 2)≠0:= by decide
private def boxIndex (ord zcap tcap:ℕ) : (Fin ord×Fin zcap×Fin tcap) ↪ (Option (Fin 2) →₀ ℕ) where
  toFun k :=(Finsupp.equivFunOnFinite.symm (fun a :Fin 2=>if a=0 then k.2.1.val else k.2.2.val)).optionElim k.1.val
  inj' := by
    intro k l h
    have h₀:=zmU h none
    have h₁:=zmU h (some 0)
    have h₂:=zmU h (some 1)
    simp only [z6S,zd8,
      Finsupp.coe_equivFunOnFinite_symm,ite_eq_right one_ne_zero_fin] at h₀ h₁ h₂
    exact Prod.ext (Fin.ext h₀) (Prod.ext (Fin.ext h₁) (Fin.ext h₂))
private theorem bI2 {ord zcap tcap:ℕ} {d:Option (Fin 2) →₀ ℕ}
    (hA:d none<ord) (hZ:d (some 0)<zcap) (hT:d (some 1)<tcap) :
    d∈univ.map (boxIndex ord zcap tcap) := by
  refine mem_map.mpr ⟨(⟨_,hA⟩,⟨_,hZ⟩,⟨_,hT⟩),mem_univ _,?_⟩
  ext a
  change (Finsupp.equivFunOnFinite.symm
    (fun b:Fin 2=>if b=0 then d (some 0) else d (some 1))).optionElim (d none) a=d a
  rcases a with _ | a
  · rw [z6S]
  · rw [zd8]
    change (if a=0 then d (some 0) else d (some 1))=d (some a)
    by_cases ha :a=0
    · simp [ha]
    · rw [ite_eq_right ha,Fin.eq_one_of_ne_zero a ha]
theorem rank_multiples (C:zpI FX Equation) {g:Equation} (hg:g≠0)
    {ord zcap tcap D dz dt:ℕ} (hD:D ≤g.natDegree) (hz :dz≤axisDegree g 0)
    (ht:dt≤axisDegree g 1)
    (hC : ∀ c∈C,c≠0 →
      c.natDegree<ord∧axisDegree c 0≤zcap∧axisDegree c 1≤tcap∧g∣c) :
    z1x FX C≤(↑((ord-D)*(zcap+1-dz)*(tcap+1-dt)) :Cardinal) := by
  let S:=(univ.map (boxIndex (ord-D) (zcap+1-dz) (tcap+1-dt)))
  let B:=restrictSupport FX (↑S:Set (Option (Fin 2) →₀ ℕ))
  let m:B →ₗ[FX] Equation :=
    (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
  have hm:C≤zWl m:= by
    intro c hc
    by_cases hn:c=0
    · rw [hn]
      exact (zWl m).zero_mem
    obtain ⟨hA,hZ,hT,q,rfl⟩:=hC c hc hn
    have hq:=right_ne_zero_of_mul hn
    rw [Polynomial.natDegree_mul hg hq] at hA
    rw [axis_mul hg hq] at hZ hT
    have hb:flatten q∈B:= by
      apply (mem_restrictSupport_iff FX).mpr
      intro d hd
      have hh:=natDegree_optionEquivLeft FX (flatten q)
      have hdA:=le_degreeOf_of_mem_support none hd
      have hdZ:=le_degreeOf_of_mem_support (some 0) hd
      have hdT:=le_degreeOf_of_mem_support (some 1) hd
      rw [← hh,unflatten] at hdA
      rw [flat_axis] at hdZ hdT
      exact bI2 (by omega) (by omega) (by omega)
    refine ⟨⟨flatten q,hb⟩,?_⟩
    change g*flatten.symm (flatten q)=g*q
    rw [AlgEquiv.symm_apply_apply]
  let:zAa FX B:=restrictSupport_finite (finite_toSet S)
  have hB:zsE FX B=(ord-D)*(zcap+1-dz)*(tcap+1-dt) := by
    rw [finrank_restrictSupport_finset]
    simp [S,mul_assoc]
  calc
    _≤z1x FX (zWl m) :=Submodule.rank_mono hm
    _≤z1x FX B:=rank_range_le m
    _ = _:= by rw [← Module.finrank_eq_rank,hB]
theorem bank_seed {x :Input} {P:Poles x} {s :Rectangle} {W:ℕ} {g:Jet}
    (hg:g∈rectBank P s W) (j:ℕ) :
    axisDegree (g.coeff j) 0≤ s.z∧axisDegree (g.coeff j) 1≤ s.t:= by
  have hz (i:ℕ) (d:Fin 2 →₀ ℕ) (hd:s.z<d 0∨s.t<d 1) :
      a2f j i d g=0:= by
    have hle :rectBank P s W≤LinearMap.ker (a2f j i d) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨Q,hQ,rfl⟩
        exact LinearMap.mem_ker.mpr (dGs Q j i d (fun b=>hQ.2 j i b d hd)))
    exact LinearMap.mem_ker.mp (hle hg)
  constructor <;> rw [axisDegree,zUp] <;> intro i _ <;>
    apply degreeOf_le_iff.mpr <;> intro d hd <;> by_contra! h
  · exact MvPolynomial.mem_support_iff.mp hd (hz i d (Or.inl h))
  · exact MvPolynomial.mem_support_iff.mp hd (hz i d (Or.inr h))
end
end qiFSOoc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxSynthPendingDepth 8
namespace qbnhR9d
noncomputable section
open P6 (p)
open P6_7_1 (Input Poles Pick afa Intro introductions buffer cutoff heights)
open qxWWUna
open cu (Jet)
open DP (d3r)
open gT (alm)
open qQ (aeH)
open Finset Polynomial UniqueFactorizationMonoid
open private cSB from ProximityPrize.SubmissionLower.T
open qdY8S8d (ofTests)
private theorem height (x :Input) :0<x.h∧x.h≤131070 :=
  ⟨(show 0<P6_7_1.packetLo by decide).trans_le (heights x).1,
   (heights x).2.trans (show P6_7_1.packetHi≤131070 by decide)⟩
private theorem buffer_eq (h:ℕ) (b:Bank) :
    buffer h b.dI b.shape=count h b - 1 := by
  unfold count buffer cutoff
  omega
private theorem bVl {x :Input} (P:Poles x) (b:Bank) {mode :ℕ}
    (test :Tests x.h b mode) : ∃ Q∈P.rows b.shape (buffer x.h b.dI b.shape),Q≠0:= by
  rw [buffer_eq]
  exact qdY8S8d.bVl P.crt x.word (height x).1 (height x).2 (ofTests test)
private theorem cCz {x :Input} (P:Poles x) (b:Bank) (test :Tests x.h b 1)
    {G Q:Jet} (hg:Irreducible G) (hv :0<G.natDegree) (hm:alm G)
    (hq:Q≠0) (hd:G∣Q) {U:ℕ} (hp:U<p)
    (hseed : ∀ j i,((Q.coeff j).coeff i).totalDegree≤U) :
    ∃ R∈P.rows b.shape (buffer x.h b.dI b.shape),¬ G∣R:= by
  rw [buffer_eq]
  exact qdY8S8d.cCz P.crt x.word (height x).1 (height x).2 (ofTests test)
    hg hv hm hq hd hp hseed
private theorem choose_free {x :Input} (P:Poles x) (b:Bank) (test :Tests x.h b 0) :
    Nonempty (Pick x P b.dI b.shape) := by
  obtain ⟨Q,hQ,hn,ha,_⟩:=exists_selected (x :=x) _ ∅ (bVl P b test) (by simp)
  exact ⟨⟨Q,hn,hQ,ha⟩⟩
private theorem choose_moving {x :Input} (P:Poles x) (i:afa)
    (Q:Pick x P (free i).dI (free i).shape) :
    ∃ R:Pick x P (moving i).dI (moving i).shape,aeH Q.row R.row:= by
  classical
  let b:=moving i
  let test :=moving_tests (heights x).1 (heights x).2 i
  let D:=(factors Q.row).toFinset.filter fun f =>
    ∃ G,Irreducible G∧G∣Q.row∧0<G.natDegree∧alm G∧Associated G f
  have hseed (j k :ℕ) : ((Q.row.coeff j).coeff k).totalDegree≤(free i).shape.U:= by
    by_cases hz : (Q.row.coeff j).coeff k=0
    · simp [hz]
    · exact (d3r P.crt x.word Q.mem j k hz).2.2
  have hd : ∀ f∈D,∃ R∈P.rows b.shape (buffer x.h b.dI b.shape),¬ f∣R:= by
    intro f hf
    obtain ⟨G,hg,hdiv,hv,hm,hassoc⟩:=(mem_filter.mp hf).2
    obtain ⟨R,hR,hn⟩:=cCz P b test hg hv hm Q.ne_zero hdiv (ddk i) hseed
    exact ⟨R,hR,fun hf=>hn (hassoc.dvd.trans hf)⟩
  obtain ⟨R,hR,hn,ha,hD⟩:=exists_selected (x :=x) _ D (bVl P b test) hd
  refine ⟨⟨R,hn,hR,ha⟩,fun G hg hG hR' hv=>cSB G fun hm => ?_⟩
  obtain ⟨f,hf,hassoc⟩:=exists_mem_factors_of_dvd Q.ne_zero hg hG
  exact hD f (mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hf,G,hg,hG,hv,hm,hassoc⟩)
    (hassoc.symm.dvd.trans hR')
theorem proof :P6_7_1.c1 := by
  classical
  intro x P
  let f (i:afa) :=Classical.choice (choose_free P (free i)
    (free_tests (heights x).1 (heights x).2 i))
  choose r hr using fun i=>choose_moving P i (f i)
  let a (i:Intro) :Pick x P (introductions.get i).1 (introductions.get i).2 :=
    if h:i=⟨8,by decide⟩ then h.symm ▸ f ⟨1,by decide⟩
    else if h' : i=⟨9,by decide⟩ then h'.symm ▸ f ⟨3,by decide⟩
    else Classical.choice (choose_free P (aux i) (aux_tests (heights x).1 (heights x).2 i))
  exact ⟨⟨f,r,hr,a,by constructor <;> simp [a]⟩⟩
end
end qbnhR9d
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qFAh60c
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (K dw)
open P6_7_1 (Input TopCaps)
open P5_7_1 (atTop)
open qlc9qed (bsz toTop aD duQ)
open aR (af embed extend cK jet jF)
open jA Rk
open private sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
open private eval_rename_top raw_eval_degree from ProximityPrize.SubmissionLower.Z7znM4a
open private gt6 cfm weight_eq_sum aWN from ProximityPrize.SubmissionLower.C
open private d2J from ProximityPrize.SubmissionLower.S
private theorem poleData (x :Input) :
    ∃ P:jF x.Γ x.F.scalar,P.H=x.H∧P.H.natDegree=x.h ∧
      ∀ γ,P.z γ=embed (x.M.label γ) := by
  let M:=x.M
  let z := fun γ:K=>embed (M.label γ)
  obtain ⟨hm,hd,hdiv,_,_,_,_,hnode,_,_,_⟩:=x.bY
  have unit {P:K[X]} (hp:IsCoprime P M.E) :IsCoprime (extend P) x.H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ:K) :extend (M.wK γ)=extend M.A₀+C (z γ)*extend M.A₁:= by
    change (M.A₀+C (M.label γ)*M.A₁).map embed= _
    rw [zS4,zNl,Polynomial.map_C]
  refine ⟨⟨x.H,hm,?_,?_,?_,z,?_,extend M.factor,extend M.Q,extend M.A₀,
    extend M.A₁,unit M.coprime_factor.symm,unit M.offset_reduced,unit M.first_amplitude_unit,
    ?_,?_⟩,rfl,hd,fun _=>rfl⟩
  · rw [hd]
    change 1≤x.h∧x.h≤2600
    exact ⟨(by decide :1≤2350).trans (emz x).1,
      (emz x).2.trans (by decide)⟩
  · exact fun i=>(hnode i).1
  · intro γ hγ
    rw [hd]
    exact P6_7.aic x.F hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (x.F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn:=(x.F.mark γ hγ).identity
    have orig:M.factor*M.wK γ*x.F.scalar γ+C (M.label γ)*M.Q =
        M.E*M.decoder (x.F.mark γ hγ).bad:= by rw [← eqn]; ring
    have mapped:=congrArg (Polynomial.map embed) orig
    simp only [zS4,zNl,Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
theorem onePole (x :Input) :Nonempty (OnePole x) := by
  obtain ⟨P,hH,hh,hz⟩:=poleData x
  obtain ⟨L⟩:=bRd.proof x.Γ x.F.scalar P
  exact ⟨⟨P,L,hH,hh,hz⟩⟩
theorem topCaps {x :Input} (P:OnePole x) (b:Bank) {F}
    (hF:F∈aV P b (cut b)) :
    TopCaps x.h b.m b.box.b b.box.j b.box.t (width b) (toTop F) := by
  classical
  obtain ⟨⟨hB,hJ,hC,_⟩,hU,hw⟩:=mem_ambient.mp (Submodule.mem_inf.mp hF).1
  intro a ha
  rw [toTop,MvPolynomial.support_rename_of_injective aD.injective] at ha
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp ha
  rw [toTop,MvPolynomial.coeff_rename_mapDomain _ aD.injective]
  have hB' := (z6P (fun i:mA=>i.elim 0 (fun _=>1)) he).trans hB
  have hJ' := (z6P (fun i:mA=>i.elim 0 Fin.val) he).trans hJ
  have hC' := (zTo (some 2) he).trans hC
  have hU' := (zTo none he).trans hU
  have hf :=hw e he
  simp only [Finsupp.weight_apply,smul_eq_mul] at hB' hJ'
  have hs (w:Fin 3→ℕ) :
      e.sum (fun i n=>n*i.elim 0 w) =
        w 0*e (some 0)+w 1*e (some 1)+w 2*e (some 2) := by
    rw [← sum_coeffs e w]
    congr 1
    funext i n
    cases i <;> simp [Nat.mul_comm]
  rw [hs] at hB' hJ'
  rw [sum_coeffs] at hf
  let d:=131071 + x.h
  have h1 : (d-1)*e (some 1)+e (some 1)=d*e (some 1) := by
    calc
      _=(d-1)*e (some 1)+1*e (some 1) := by simp
      _ = _:= by rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  have h2 : (d-2)*e (some 2)+2*e (some 2)=d*e (some 2) := by
    rw [← Nat.add_mul,zxt (by dsimp [d]; omega)]
  change (F.coeff e).natDegree+(d*e (some 0)+(d-1)*e (some 1) +
    (d-2)*e (some 2))≤(cut b)+(b.box.b+b.box.j)*x.h at hf
  have he0: (z8D aD e) 0=e none := by
    simpa only [aD,finSuccEquiv_symm_none] using
      Finsupp.mapDomain_apply_of_injective aD.injective e none
  have he1 : (z8D aD e) 1=e (some 0) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((0:Fin 3).succ)=1)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 0)
  have he2 : (z8D aD e) 2=e (some 1) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((1 :Fin 3).succ)=2)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 1)
  have he3: (z8D aD e) 3=e (some 2) := by
    simpa only [aD,finSuccEquiv_symm_some,(by decide : ((2 :Fin 3).succ)=3)] using
      Finsupp.mapDomain_apply_of_injective aD.injective e (some 2)
  rw [he0,he1,he2,he3]
  refine ⟨by simpa using hB',by simpa using hJ',hC',hU',?_⟩
  change (F.coeff e).natDegree+d*(e (some 0)+e (some 1)+e (some 2)) ≤
    (cut b)+(b.box.b+b.box.j)*x.h+e (some 1)+2*e (some 2)
  simp only [Nat.mul_add]
  omega
theorem source_zero {x :Input} (P:OnePole x) (b:Bank) {F}
    (hF:F∈aV P b (cut b)) {γ:K} (hγ:γ∈x.Γ) :
    atTop (toTop F) (x.M.label γ) (x.F.scalar γ)=0:= by
  let L:=P.bY
  let H :=P.data.H
  let z :=P.data.z γ
  let res :=Tj L.numerator L.denominator z
  let r :=b.box.b+b.box.j
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  have hcut:=(mem_ambient.mp hA).2.2
  rw [← P.height] at hcut
  obtain ⟨Q,hQ⟩:=gt6 P.data L r F z (L.regular γ hγ)
    ((NR.aVU _ _ _ _ _).mp hP)
  have hres :res.natDegree≤H.natDegree :=
    (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans L.small.le)
  have hr :=cfm z hres hcut
  rw [hQ] at hr
  have hQcut:a04 (cut b) Q:= by
    intro a ha
    have hn:=MvPolynomial.mem_support_iff.mp ha
    have hp:=pow_ne_zero r P.data.monic.ne_zero
    have hc: (znf (H^r)*Q).coeff a≠0:= by
      rw [z06]
      exact mul_ne_zero hp hn
    have hb:=MvPolynomial.mem_restrictJointDegree.mp hr a hc
    rw [z06,natDegree_mul hp hn,natDegree_pow] at hb
    simp only [weight_eq_sum,aWN] at hb
    change r*H.natDegree+_+_≤(cut b)+r*H.natDegree at hb
    omega
  obtain ⟨T,hT,hST⟩:=L.quotient γ hγ
  have hcontact :=c6X b.m x.M.word H res z r F Q P.data.nodes
    (fun i=>(bsz _ _ _ _).mp ((zxR _).mp hC i)) hQ
  let B:=x.F.mark γ hγ
  have hz :cK Q T=0:= by
    apply wT.aHG B.bad.support (fun i=>embed (P6.node i))
      ((RingHom.injective embed).comp IRSProfile.domain.injective) b.m
    · intro i hi
      apply hcontact i T
      rw [← hST,extend,Polynomial.eval_map,Polynomial.eval₂_at_apply,B.scalar_hits i hi]
    · have hA:b.m*dw≤b.m*B.bad.support.card :=
        Nat.mul_le_mul_left _ B.bad.dw
      have hpos :0<b.m*dw :=
        Nat.mul_pos (by cases b <;> decide) (by decide)
      have hdeg:=raw_eval_degree hT hQcut
      unfold cut at hdeg
      omega
  have h:=congrArg (fun R:af 3=>cK R T) hQ
  change cK (az5 H res (JX (C z) F)) T= _ at h
  rw [d2J,← hST] at h
  have h0:cK (znf (H^r)*Q) T=0:= by
    change zY9 (jet T) (_ *_)= _
    rw [map_mul,MvPolynomial.eval_C]
    change H^r*cK Q T=0
    rw [hz,mul_zero]
  rw [h0] at h
  rw [duQ,eval_rename_top,← P.Kw γ,h,map_zero]
end
end qFAh60c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qFAh60c
noncomputable section
open Polynomial
open P6 (p)
open P6_7_1 (Input)
open qlc9qed (ays bsz toTop toTop_injective b4I
  choose_strong topCommon cHJ)
open aR (ao)
open jA Rk
open NR (TT)
open acZ (agr)
open aA0 (cEb c4E)
open private a8W dxN from ProximityPrize.SubmissionLower.S
open private trueCut_shift from ProximityPrize.SubmissionLower.ZTFKldb
open private line b7T cYc ct4 c40 from ProximityPrize.SubmissionLower.A3
open private bXt bCP cKM from ProximityPrize.SubmissionLower.DG
theorem shift {x :Input} (P:OnePole x) (b:Bank) {t F}
    (hF:F∈aV P b t) (i:ℕ) :
    Yd P.data.H i F∈aV P b (t+(3*x.h)*i) := by
  obtain ⟨hA,hC,hP⟩:=Submodule.mem_inf.mp hF
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  refine Submodule.mem_inf.mpr ⟨mem_ambient.mpr ⟨cEb P.data.H i F b.box hc,?_,?_⟩,?_,?_⟩
  · rw [gY,MvPolynomial.degreeOf_le_iff]
    intro a ha
    exact (Nat.le_add_left ..).trans
      ((zTo none (a8W ha)).trans hs)
  · rw [← P.height] at hw ⊢
    simpa only [Nat.add_right_comm] using trueCut_shift P.data.H i _ F hw
  · apply (zxR _).mpr
    intro j
    have hj:=(bsz _ _ _ _).mp ((zxR _).mp hC j)
    apply (bsz _ _ _ _).mpr
    intro a
    exact dxN P.data.H i b.m _ _ F hj a
  · exact (NR.aVU _ _ _ _ _).mpr
      (c4E P.data P.bY _ i F ((NR.aVU _ _ _ _ _).mp hP))
theorem bank_mono {x :Input} (P:OnePole x) (b:Bank) {s t:ℕ} (hst:s≤t) :
    aV P b s≤aV P b t:= by
  rintro F ⟨hA,hC⟩
  obtain ⟨hc,hs,hw⟩:=mem_ambient.mp hA
  exact ⟨mem_ambient.mpr ⟨hc,hs,fun a ha=>(hw a ha).trans (Nat.add_le_add_right hst _)⟩,hC⟩
theorem factor_power {x :Input} (P:OnePole x) {G:ko}
    (hi:Irreducible G) (hs :0<G.degreeOf none) (hsmall:G.degreeOf none<p)
    (hdiv : ∀ F∈aV P .strong (cut .strong),G∣bC F) :
    ∀ t≤ cut .strong,∀ F∈aV P .strong t,G^powerAt x.h t∣bC F:= by
  intro t ht F hF
  have hpos :0<3*x.h:= by
    have h:=(emz x).1
    change 2350≤x.h at h
    omega
  apply c40 (line none) (b7T none)
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi) (ct4 hs hsmall)
  intro i hi'
  have hle :i≤(cut .strong - t)/(3*x.h) := by
    unfold powerAt at hi'
    omega
  have hm: (3*x.h)*i≤ cut .strong - t:= by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpos).mp hle
  have hcut:t+(3*x.h)*i≤ cut .strong:= by omega
  have hd:=hdiv _ (bank_mono P .strong hcut (shift P .strong hF i))
  rw [cYc]
  have hn:qV (P.data.H^(3*i))≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] iP)).mpr
      (pow_ne_zero _ P.data.monic.ne_zero)
  have hunit :IsUnit (znf (qV (P.data.H^(3*i))) :ko) :=
    (IsUnit.mk0 _ hn).map znf
  apply hunit.dvd_mul_left.mp
  simpa only [Yd,bC,map_mul,MvPolynomial.map_C] using hd
def c1 :Prop :=
  ∀ (b:Bank) (h:ℕ),h≤2369 →
    zAa ao (Aw b h (cut b)) ∧
    ambientCount b h≤zsE ao (Aw b h (cut b))
def c2 :Prop :=
  ∀ (b:Bank) (a v :ao) (V:zpI ao jK),zAa ao V →
    (∀ F∈V,Jn b.box F∧gY F≤width b) →
    TT V (ays b.m a v)≤(width b+1)*b.contactRank
def c3:Prop :=
  ∀ (x :Input) (P:OnePole x) (b:Bank) (V:zpI ao jK),
    zAa ao V→(∀ F∈V,Jn b.box F∧gY F≤width b) →
    TT V (pole P b)≤eMG b x.h
def c4 :Prop :=
  ∀ (x :Input) (P:OnePole x) (G:ko),
    0<G.degreeOf (some 2)→0<G.degreeOf none →
    (∀ t≤ cut .strong,∀ F∈aV P .strong t,G^powerAt x.h t∣bC F) →
    zsE ao (aV P .strong (cut .strong))≤topCeiling
private theorem debit_ok (b:Bank) (h:ℕ) (hh:h≤2369) :
    rank b+262144*((width b+1)*b.contactRank)+eMG b h≤ambientCount b h:= by
  cases b <;> simp only [rank,width,qlc9qed.Bank.contactRank,eMG,ambientCount,
    az0,qlc9qed.Bank.basePole,qlc9qed.Bank.poleExcess,Nat.mul_add] <;> omega
private theorem rank_lower (h1 :c1) (h2 :c2) (h3:c3)
    {x :Input} (P:OnePole x) (b:Bank) :
    rank b≤zsE ao (aV P b (cut b)) := by
  classical
  have hh:x.h≤2369:=(emz x).2
  let V:=Aw b x.h (cut b)
  obtain ⟨hV,hcol⟩:=h1 b x.h hh
  let:zAa ao V:=hV
  have hcaps (F:jK) (hF:F∈V) :Jn b.box F∧gY F≤width b :=
    ⟨(mem_ambient.mp hF).1,(mem_ambient.mp hF).2.1⟩
  let A (i:P6.I) :=ays b.m (aR.embed (P6.node i)) (x.word i)
  have hc:=bCP V (Finset.univ :zJe P6.I) A ((width b+1)*b.contactRank)
    (fun _ _=>h2 b _ _ V hV hcaps)
  have hcard: (Finset.univ :zJe P6.I).card = 262144 := by
    exact Fintype.card_fin (2^18)
  rw [Finset.inf_univ_eq_iInf,hcard] at hc
  have hd:TT V (contacts x b ⊓ pole P b) ≤
      262144*((width b+1)*b.contactRank)+eMG b x.h :=
    (bXt V _ _).trans (Nat.add_le_add hc (h3 x P b V hV hcaps))
  exact cKM ((debit_ok b x.h hh).trans hcol) hd
private theorem exists_row (V:zpI ao jK) (hV:0<zsE ao V) :
    ∃ F∈V,F≠0:= by
  let:Nontrivial V:=Module.nontrivial_of_finrank_pos hV
  obtain ⟨F,hF⟩:=exists_ne (0:V)
  exact ⟨F.val,F.property,fun h=>hF (Subtype.ext h)⟩
private theorem degree_dvd {F G:ko} (i:mA) (hF:F≠0) (hd:G∣F) :
    G.degreeOf i≤F.degreeOf i:= by
  obtain ⟨Q,e⟩:=hd
  rw [e] at hF
  have hn:=mul_ne_zero_iff.mp hF
  rw [e,MvPolynomial.degreeOf_mul_eq hn.1 hn.2]
  exact Nat.le_add_right _ _
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_7_1.c2 := by
  intro x
  obtain ⟨P⟩:=onePole x
  have hcheap:=rank_lower h1 h2 h3 P .cheap
  have hstrong:=rank_lower h1 h2 h3 P .strong
  obtain ⟨F,hF,hnF⟩:=exists_row _ ((by decide :0< rank .cheap).trans_le hcheap)
  have hU:=(mem_ambient.mp (Submodule.mem_inf.mp hF).1).2.1
  obtain ⟨W,hW,hnW,havoid⟩:=choose_strong F hnF _
    (exists_row _ ((by decide :0< rank .strong).trans_le hstrong)) (by
      intro G hi hd ht hs
      by_contra! hall
      have hseed :=degree_dvd none (agr hnF) hd
      change gY G≤gY (bC F) at hseed
      rw [b4I] at hseed
      have hsmall:G.degreeOf none<P6.p :=
        hseed.trans_lt (hU.trans_lt (by decide))
      have hforced:=factor_power P hi hs hsmall hall
      exact (not_le_of_gt (by decide :topCeiling< rank .strong))
        (hstrong.trans (h4 x P G ht hs hforced)))
  refine ⟨⟨toTop F,toTop W,toTop_injective.ne hnF,toTop_injective.ne hnW,
    topCaps P .cheap hF,topCaps P .strong hW,topCommon havoid,?_⟩⟩
  intro γ hγ
  have hf :=source_zero P .cheap hF hγ
  have hw:=source_zero P .strong hW hγ
  have hs :=(x.F.mark γ hγ).scalar_fixed
  exact ⟨hf,hw,cHJ _ _ _ hs hf,cHJ _ _ _ hs hw⟩
end
end qFAh60c
end
