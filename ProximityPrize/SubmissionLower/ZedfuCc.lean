import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.ZFZJbJc
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Zw2ME7d
set_option Elab.async false
open _root_ renaming Finset.sum_le_sum → zQk, Finset.sup_le → zf9, Finsupp.degree_eq_sum → zFi, Finsupp.some_optionElim → zpo, Finsupp.weight_apply → zDM, Finsupp.weight_eq_sum → z1K, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map_C → zpw, MvPolynomial.optionEquivRight → zyD, Nat.mul_le_mul_right → ztf, Polynomial.coeff_map → z0b
section
set_option autoImplicit true
namespace P6_6_1
noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P6 (I node dw)
open P6_6 (tB gZ m6 M8)
open aR (ao embed extend af shape aO)
open scoped BigOperators Polynomial
open private bFD from ProximityPrize.SubmissionLower.I
private theorem b1o {u v :Exponent} (h:v≤u) (hu:FF u) :FF v := by
  have hd:v.some.degree≤u.some.degree := by
    rw [zFi,zFi]
    exact zQk fun j _=>h (some j)
  have hw (w:Fin 4→ℕ) :v.some.weight w≤u.some.weight w:= by
    rw [z1K,z1K]
    exact zQk fun j _=>ztf (w j) (h (some j))
  have ht:v.weight (differentialWeight gZ)≤u.weight (differentialWeight gZ) := by
    rw [z1K,z1K]
    exact zQk fun j _=>ztf (differentialWeight gZ j) (h j)
  obtain ⟨hdeg,hi,hf,htail,hwgt⟩:=hu
  refine ⟨hd.trans hdeg,(hw _).trans hi,(h _).trans hf,?_,ht.trans hwgt⟩
  exact (add_le_add (add_le_add (h _) (h _)) (h _)).trans (htail.trans (gAu hd))
private theorem translate_mem_space (x y :ao) (Q:space) :
    globalPointTranslation x y (Q:DifferentialPolynomial ao 3)∈space := by
  classical
  let f :=globalPointTranslation (d:=3) x y
  change f (Q:DifferentialPolynomial ao 3)∈space
  rw [(Q:DifferentialPolynomial ao 3).as_sum,map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff ao).mpr
  intro v hv
  exact b1o (bFD x y u v _ hv) (Q.property hu)
private theorem fTm (x y :ao) :
    zsE ao (zWl (DV x y)) ≤
      zsE ao (zWl (DV 0 0)) := by
  let tr :space →ₗ[ao] space :=
    ((globalPointTranslation x y).toLinearMap.domRestrict space).codRestrict space (translate_mem_space x y)
  have h:DV x y=(DV 0 0).comp tr := by
    ext Q:1
    exact localConstraintAt_eq_zero_globalPointTranslation (d:=3) (m:=99) x y
      (Q:DifferentialPolynomial ao 3)
  rw [h]
  exact LinearMap.finrank_range_comp_le_left (DV 0 0) tr
open private bcz cBu from ProximityPrize.SubmissionLower.BF
private theorem cKH :differentialWeight (d:=3) gZ =
    fun v=>v.elim 1 (fun i=>gZ - i.val) := by
  funext v
  cases v <;> rfl
private theorem dte (Q:space) :
    aO (shape (zyD ao (Fin 4) Q)) m6 ∧
      tB (zyD ao (Fin 4) Q) M8:= by
  classical
  let P:af 4 :=zyD ao (Fin 4) Q
  have hQ:=(MvPolynomial.mem_restrictSupport_iff ao).mp Q.property
  have hm (m:Fin 4 →₀ ℕ) (h:m∈P.support) : ∃ i,FF (m.optionElim i) := by
    obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i,hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff,← Polynomial.mem_support_iff])
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · apply zf9
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [zpo,Finsupp.degree_apply,Finsupp.sum] using hi.1
  · apply zf9
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [zpo,zDM,smul_eq_mul,Nat.mul_comm,
      fP.lP] using hi.2.1
  · change P.degreeOf 3≤16
    rw [MvPolynomial.degreeOf_eq_sup]
    apply zf9
    intro m h
    obtain ⟨i,hi⟩:=hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1
  · intro m hm
    let d:=(P.coeff m).natDegree
    have hc: (P.coeff m).coeff d≠0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    rw [← bcz,AlgEquiv.symm_apply_apply] at hc
    have hu:m.optionElim d∈(Q:DifferentialPolynomial ao 3).support :=
      MvPolynomial.mem_support_iff.mpr hc
    have hb:=(hQ hu).2.2.2.2
    rw [cKH,Finsupp.weight_optionElim,one_mul] at hb
    simpa only [zDM,smul_eq_mul,Nat.mul_comm] using hb
def c1 :Prop :=
  zsE ao (zWl (DV 0 0))≤17466625
def c2 :Prop :=
  0x42a14040000<zsE ao space
theorem of_children (h1 :c1) (h2 :c2) :P6_6.c1 := by
  intro w Γ s hm
  have rank_local (x y :ao) :
      zsE ao (zWl (DV x y))≤17466625 :=
    (fTm x y).trans h1
  let localRows (i:I) :=DV (embed (node i)) (embed (w i))
  have hr : (∑ i,zsE ao (zWl (localRows i))) ≤
      0x42a14040000:= by
    calc
      _ ≤ ∑ _:I,(17466625:ℕ) :=zQk fun i _=>rank_local _ _
      _ = _:= by simp
  obtain ⟨Q,hQ,hlocal⟩ :=
    LinearMap.exists_ne_zero_of_sum_finrank_range_lt localRows (hr.trans_lt h2)
  let P:af 4 :=zyD ao (Fin 4) Q
  have hP:P≠0:= by
    intro h
    exact hQ (Subtype.ext ((zyD ao (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  obtain ⟨hbox,hweight⟩:=dte Q
  refine ⟨P,hP,hbox,hweight,?_⟩
  intro γ hγ
  obtain ⟨T,hT,hhit⟩:=hm.lg γ hγ
  have hdeg:differentialWeightedDegree gZ (Q:DifferentialPolynomial ao 3) <
      99*dw:= by
    apply lt_of_le_of_lt _ (by decide :M8<99*dw)
    rw [differentialWeightedDegree,MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
    exact fun u hu=>(Q.property hu).2.2.2.2
  have hS: (extend (s γ)).natDegree≤gZ :=
    Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
  rw [cBu]
  refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i=>embed (node i)) (fun i=>embed (w i)) T hdeg
    (fun i _=>hlocal i) _ hS
    ((RingHom.injective embed).comp node.injective).injOn hT ?_
  intro i hi
  rw [Polynomial.eval_map,Polynomial.eval₂_hom,hhit i hi]
end
end P6_6_1
end
section
set_option autoImplicit true
namespace P6_6_7
noncomputable section
open Polynomial P6_6
open P6 (I K)
open aR (ao af Shape shape aO extend cK wU ceilDiv)
open dN (GeoJets kC Ch bC YR Invariant separant)
open agL (BV EY)
structure Context where
  w:I→K
  Δ:Finset K
  s :K→K[X]
  messages :Messages w Δ s
  nonempty :Δ.Nonempty
  n:ℕ
  f :Fin n→af 4
  S:Finset (Fin n)
  v :Shape
  marks :ChartMarks Δ s f S
  fits :aO (v.plus (wD (shape ∘ f) S)) m6
inductive ChartCase (n:ℕ) where
  | union (l:ℕ)
  | own (i:Fin n)
def chartIndices (C:Context) :ChartCase C.n→Finset (Fin C.n)
  | .union _=>C.S
  | .own i => {i}
def chartBody (C:Context) (R:af 4) :ChartCase C.n→Shape
  | .union _=>remainingChart C.v
  | .own _=>(shape R).iU
def firstBody (C:Context) (R:af 4) :ChartCase C.n→Shape
  | .union l=>physicalBody C.v l
  | .own _=>(shape R).iU
def firstSlot (C:Context) (R:af 4) :ChartCase C.n→Shape
  | .union _=>shape R
  | .own _=>(shape R).iU
def topBound (C:Context) (R:af 4) :ChartCase C.n→ℕ
  | .union l=>(firstCaps C.v l).t
  | .own _=>(shape R).t
def CaseGuard (C:Context) (R:af 4) (ell:ℕ) :ChartCase C.n→Prop
  | .union l=>ell≤l∧aO (C.v.scale l) Wk∧aO (shape R) (firstCaps C.v l)
  | .own i=>i∈C.S∧Associated R (C.f i)∧aO (C.v.scale ell) Wk
structure PairInput (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n) :Prop where
  factor :JetFactor R
  positive :0<ell
  guard :CaseGuard C R ell cs
  proper : ¬ R∣G
  H6:aO (shape G) (physicalBody C.v ell)
  cutterWeight:tB G aWx
  order : ∀ γ∈C.Δ,wU G (extend (C.s γ)) ell
abbrev cutterBody (C:Context) (ell:ℕ) :=physicalBody C.v ell
abbrev commonBody (C:Context) (R:af 4) (ell:ℕ) (cs :ChartCase C.n) :=
  joinBody (firstBody C R cs) (cutterBody C ell)
def ord (C:Context) (R:af 4) (γ:K) :ℕ :=
  ambientOrder R (extend (C.s γ))
def genericOrder (R:af 4) (assigned:Ideal GeoJets) :ℕ:= by
  classical
  exact Nat.findGreatest
    (fun d => ∀ a,EY a<d→bC (BV a R)∈assigned) (shape R).b
structure SurfaceAssignment (C:Context) (R G:af 4) where
  aI:K→ Ideal GeoJets
  valid : ∀ γ∈C.Δ,0<ord C R γ →
    (kC R G).IsMinimalPrime (aI γ)∧aI γ≤Ch (extend (C.s γ))
def surfaceOrder (C:Context) (R G:af 4) (assigned:SurfaceAssignment C R G) (γ:K) :ℕ :=
  if 0<ord C R γ then genericOrder R (assigned.aI γ) else 0
def RegularInvariant (C:Context) (cs :ChartCase C.n) (assigned:Ideal GeoJets) (γ:K) :Prop :=
  ∃ i∈chartIndices C cs,bC (C.f i)∈assigned ∧
    (∀ j∈chartIndices C cs,bC (C.f j)∈assigned→i≤j) ∧
    ∃ a,YR (C.f i) assigned a ∧
      let g:=(separant^[a]) (C.f i)
      cK (separant g) (extend (C.s γ))≠0∧Invariant g assigned
def DG (C:Context) (R G:af 4) (assigned:SurfaceAssignment C R G) :ℕ :=
  ∑ γ∈C.Δ,(ord C R γ - surfaceOrder C R G assigned γ)
def lowGeneric (C:Context) (R G:af 4) (ell:ℕ) (assigned:SurfaceAssignment C R G) :ℕ :=
  ∑ γ∈C.Δ,if genericOrder G (assigned.aI γ)<ell then surfaceOrder C R G assigned γ else 0
def highAux (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n) (assigned:SurfaceAssignment C R G) :ℕ:= by
  classical
  exact ∑ γ∈C.Δ,if ell≤genericOrder G (assigned.aI γ) ∧
      ¬ RegularInvariant C cs (assigned.aI γ) γ then surfaceOrder C R G assigned γ else 0
def highInv (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n) (assigned:SurfaceAssignment C R G) :ℕ:= by
  classical
  exact ∑ γ∈C.Δ,if ell≤genericOrder G (assigned.aI γ) ∧
      RegularInvariant C cs (assigned.aI γ) γ then surfaceOrder C R G assigned γ else 0
abbrev feeScale :ℕ:=32*mV
def point32 (r q both:Shape) :ℤ :=
  (mV:ℤ)*wP r q both both
def taylor32 (dR:Bool) (p r q:Shape) :ℤ :=
  (mV:ℤ)*pair32 dR p r q +
    32*((P6.t:ℤ)+2*mV)*r.b*q.b*(weightedChart (bf+1) p).b
def fresh32 (r q:Shape) :ℤ :=
  64*(mV:ℤ)*gZ*r.b*q.b
def smallCore (p r :Shape) :ℤ :=
  let a :=r.iU
  let E :=curve32 a a p
  (mV:ℤ)*min (pair32 false a a p) (pair32 true a a p) +
    32*((P6.t:ℤ)+2*mV)*a.b*p.b*(weightedChart (bf+1) a).b +
    (2+2*(r.t:ℤ))*E a+E (joinBody a p) +
    mV*wP a p a a+fresh32 r p
def biR (r :Shape) :ℕ :=
  let u:=r.b - r.t
  let c:=(r.j-3*r.t)/2
  let g:=max u ((2*c - 1)*u - c^2)
  ceilDiv (4*bf*P6.t*(r.b*u^2+g^2)) mV +
    r.b*u+g^2+u
def thirdFiber (R:af 4) (T:ao[X]) : (ao[X])[X] :=
  zSZ Polynomial.C
    (fun i:Fin 4=>if i=3 then Polynomial.X else Polynomial.C (aR.jet T i)) R
def smallMarks (C:Context) (R:af 4) (zero :Bool) :ℕ:= by
  classical
  exact ∑ γ∈C.Δ,if (thirdFiber R (extend (C.s γ))=0↔zero=true) then ord C R γ else 0
def SmallGuard (C:Context) (R:af 4) (l ell:ℕ) :Prop :=
  0<ell∧ell≤l∧aO (shape R) (firstCaps C.v l) ∧
    ¬ CompanionTest C.v (shape R) ell ∧ ¬ R∣factorProd C.f C.S
end
end P6_6_7
end
section
set_option autoImplicit true
namespace P6_6_5
noncomputable section
open P6 (I K)
open P6_6 (mW LN bf tB M8)
open aR (af qE)
open oR (Rr AR Wc)
open scoped BigOperators Polynomial
abbrev tC:=ON.tC
structure Zl (v :ℕ) {n:ℕ} (f :Fin n→af 3) :Prop where
  irreducible : ∀ i,Irreducible (f i)
  positive : ∀ i,0<(f i).degreeOf 2
  weight : ∀ i,tB (f i) M8
  total: (∑ i,(f i).totalDegree)≤(mW v).b
  index : (∑ i,qE (f i))≤(mW v).j
  top: (∑ i,(f i).degreeOf 2)≤(mW v).t
def Fb (f :af 3) :Prop :=
  f∣AR f (bf-3)
def R4 (v :ℕ) :ℕ :=
  let p:=mW v
  let x :=LN (bf+1) p
  let y :=LN (bf+2) p
  Wc p x y+(bf - 1)*Wc p (tC p) y +
    bf*Wc p (tC p) x
abbrev aHT:ℕ:=2*bf - 5
def acg (v :ℕ) :ℕ :=
  let p:=mW v
  p.b*(1+aHT*(p.b - 1))
def O1 (v :ℕ) :ℕ :=
  let p:=mW v
  max p.b ((2*p.t - 1)*p.b - p.t^2)
def ayY (v :ℕ) :ℕ :=
  let p:=mW v
  max p.j ((2*p.t - 1)*p.j - 2*p.t^2)
def aNR (v :ℕ) :ℕ:=1+aHT*(O1 v - 1)
def aUS (v :ℕ) :ℕ :=
  min (aNR v) (aHT*(ayY v - 1)+bf - 1)
def bGL (v :ℕ) :ℕ :=
  let a :=aNR v
  let d:=aUS v
  O1 v*d+ayY v*(a - d)
structure a93 (v :ℕ) (q:af 2) :Prop where
  ne_zero :q≠0
  total:q.totalDegree≤O1 v
  index :qE q≤ayY v
structure bjg (v :ℕ) {n:ℕ} (f :Fin n→af 2) :Prop where
  irreducible : ∀ i,Irreducible (f i)
  positive : ∀ i,0<(f i).degreeOf 1
  total: (∑ i,(f i).totalDegree)≤O1 v
  index : (∑ i,qE (f i))≤ayY v
structure a0Z (v :ℕ) (w:I→K) (Γ:Finset K) (s :K→K[X]) where
  isolated:Finset K
  multiple :Rr w Γ s
  invariant:Rr w Γ s
  cover :Γ⊆isolated∪multiple.CF∪invariant.CF
  kK:isolated.card+2*multiple.BJ≤R4 v
  fresh:invariant.BJ≤acg v
  components :multiple.n+invariant.n≤2*acg v
theorem a5C (v :ℕ) : (mW v).t≤28:= by
  change (56-3*v)/2≤28
  omega
theorem cSk {v :ℕ} (hv :v≤P6_6.m6.t) :2≤O1 v := by
  apply le_trans _ (le_max_left _ _)
  change 2≤ max (133 - v) (56-3*v+3)
  change v≤16 at hv
  omega
theorem ebr {v :ℕ} (hv :v≤P6_6.m6.t) :0<ayY v := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  change v≤16 at hv
  change 0<56-3*v
  omega
theorem ebv (v :ℕ) :O1 v<P6.p:= by
  have hb: (mW v).b≤133:= by
    change max (133 - v) (56-3*v+3)≤133
    omega
  have ht:2*(mW v).t - 1≤55:= by
    have :=a5C v
    omega
  have h:=Nat.mul_le_mul ht hb
  unfold O1
  change max (mW v).b
    ((2*(mW v).t - 1)*(mW v).b-(mW v).t^2)<0x7f000001
  omega
end
end P6_6_5
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace qs56oUd
noncomputable section
open Polynomial aR dN rW wH as9 bzK
open Rl (aYV aip Ue)
open P6_6 (gZ M8)
open private beF Lv cFX dmq c84 cMO from ProximityPrize.SubmissionLower.J
open private bgS rowTrajectory_degree from ProximityPrize.SubmissionLower.Zw2ME7d
open private bPa bDc from ProximityPrize.SubmissionLower.J
private theorem c1U {f :af 4} {P:Ideal GeoJets}
    (hinv :Invariant f P) (hmem:bC (vU f)∈P)
    {n:ℕ} (hn:P6_6.bf≤n) :bC (su f n)∈P:= by
  induction n,hn using Nat.le_induction with
  | base=>exact hmem
  | succ n _ ih =>
    rw [su,aqZ]
    simp only [bC,map_sub,map_mul]
    exact P.sub_mem (P.mul_mem_left _ (hinv _ ih)) (P.mul_mem_left _ ih)
private abbrev donorWeight:ℕ:=M8+133671*133
private theorem donor_weight {f :af 4} (hf :P6_6.wm f) :
    aR.tB f donorWeight:= by
  intro m hm
  have hc: (f.coeff m).natDegree≤M8 :=
    (Nat.le_add_right _ _).trans (hf.2.2.2 m hm)
  have hb:m.sum (fun _ a=>a)≤133 :=
    (MvPolynomial.le_totalDegree hm).trans hf.2.2.1.1
  refine Nat.add_le_add hc ?_
  calc
    _ ≤ ∑ i∈m.support,133671*m i :=
      zQk fun i _=>ztf _ (Nat.sub_le ..)
    _=133671*m.sum (fun _ a=>a) :=(Finset.mul_sum ..).symm
    _≤_:=Nat.mul_le_mul_left _ hb
theorem bN8 {f :af 4} {P:Ideal GeoJets} [P.IsPrime]
    (hs :bC (separant f)∉P) (hf :P6_6.wm f)
    (hfactor :bC f∈P) (hmem:bC (dN.vU f)∈P)
    (δ:Derivation ao (ChartRing f P) (ChartRing f P)) (hδ:asX f P δ) :
    jW (CX P) f ((RH f P).map (afJ f P hs))=0:= by
  let U:=RH f P
  let x :=CW f P
  let k :=Jb f P
  let V:=bgS k f U
  let d:=beF (R:=ChartRing f P) δ.toLinearMap.toAddMonoidHom δ.map_one_eq_zero
    (fun a b=> by
      change δ (a*b)=a*δ b+b*δ a
      simpa only [smul_eq_mul] using δ.leibniz a b)
  have hx :d x=1 :=dHV hδ
  have hc (a :ao) :d (k a)=0:=dHX hδ a
  have hU:Lv d U=0 :=
    cFX d x hx U (dIg hδ hmem)
  have he :V.eval x=0:=(cMO f P f).trans (cac hfactor)
  have hd:V.natDegree≤donorWeight :=
    rowTrajectory_degree k f U (donor_weight hf) (Nat.le_of_lt_succ (dIc f P))
  have hz :V=0:=dmq d x hx V
    (c84 d k hc f U hU) he (fun n hn=>cFi f P
      (hn.trans_lt (hd.trans_lt (by decide :donorWeight<K1.p))))
  let φ:=afJ f P hs
  have hk :φ.comp (Jb f P)=CX P:= by
    apply RingHom.ext
    intro a
    simpa only [RingHom.comp_apply,Jb,CX,ni,
      bC,zpw] using
      bef f P hs (MvPolynomial.C (C a))
  have hm:V.map φ=jW (CX P) f (U.map φ) := by
    change (mapRingHom φ) (zSZ (mapRingHom (Jb f P))
      (fun i:Fin 4=>hasseDeriv i.val U) f)= _
    rw [MvPolynomial.hom_eval₂ f (mapRingHom (Jb f P)) (mapRingHom φ)
      (fun i:Fin 4=>hasseDeriv i.val U),mapRingHom_comp,hk,jW]
    simp only [coe_mapRingHom,hasseDeriv_map]
  rw [← hm,hz,Polynomial.map_zero]
theorem dPy (f :af 4) (hf :P6_6.wm f)
    (P:Ideal GeoJets) (hp:P.IsPrime) (hheight:P.height=2)
    (hP:bC f∈P) (hs :bC (separant f)∉P)
    (hinv :Invariant f P) (hmem:bC (vU f)∈P)
    (S:ao[X]) (hle :P≤Ch S) (hreg:qg f S)
    (hd:S.natDegree≤gZ) :aYV f S:= by
  let:=hp
  have hold:bC (dN.vU f)∈P :=
    c1U hinv hmem (by decide :P6_6.bf≤aR.bf)
  obtain ⟨δ,hδ⟩:=bRC.proof f P hp hs hinv
  let U:=(RH f P).map (afJ f P hs)
  have hdegree :U.natDegree<bf :=ezp _
  have hjet : ∀ i:Fin 4,
      (hasseDeriv i.val U).eval (K4 P (MvPolynomial.C rI)) =
        K4 P (MvPolynomial.X i) := by
    intro i
    simpa only [U,CW,bef,rI,
      bC,zpw,MvPolynomial.map_X] using
      bpA (afJ f P hs) i
  have hsolve :jW (CX P) f U=0:=bN8 hs hf hP hold δ hδ
  have hregular :jW (CX P) (separant f) U≠0:= by
    intro hzero
    apply bDc hs
    rw [← bPa P U (separant f) hjet,hzero,eval_zero]
  let A:=Zv (CX P) U
  refine ⟨A,⟨RingHom.ker_isPrime _,cyM.proof P hp U hheight hdegree hjet,?_,?_⟩,?_⟩
  · intro j
    change zOD (CX P)
      (fun i:Fin aR.bf=>U.coeff i.val) ((aip f).coeff j)=0
    rw [← z0b,map_universalEval _ _ hdegree,hsolve,coeff_zero]
  · obtain ⟨j,hj⟩:=not_forall.mp (mt Polynomial.ext_iff.mpr hregular)
    refine ⟨j,?_⟩
    change zOD (CX P)
      (fun i:Fin aR.bf=>U.coeff i.val) ((aip (separant f)).coeff j)≠0
    rw [← z0b,map_universalEval _ _ hdegree]
    simpa only [coeff_zero] using hj
  · exact specializes hs hle hreg (Ue.mp (hle hP))
      (hd.trans (by decide :gZ≤133671))
end
end qs56oUd
end
