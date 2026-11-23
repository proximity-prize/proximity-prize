import ProximityPrize.SubmissionLower.AE
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→lI,Cardinal.toNat_add→ oK,CommSemiring→ oq,Finset→n5,Finset.range→ ov,Ideal.mem_span_singleton→pC,Module.Finite→nX,Module.finrank→ oj,MvPolynomial→mD,MvPolynomial.C→c9,MvPolynomial.X→aU,MvPolynomial.eval₂→ oz,Option→nI,Polynomial→ oy,Polynomial.C→lz,Polynomial.X→nq,Polynomial.hasseDeriv→ oD,Submodule→cy,Submodule.mem_comap→ oZ,Submodule.rank_mono→pz,Submodule.restrictScalars_mem→ oY,aR.Shape→lV,inf_le_left→lJ,inf_le_right→ ox
set_option autoImplicit true
section
namespace jA
noncomputable section
open K1 aR
open scoped Polynomial BigOperators
abbrev iP:=FractionRing (oy ao)
abbrev kS:=FractionRing (oy ao)
abbrev mA:=nI (Fin 3)
abbrev VP (R:Type*) [oq R] :=mD mA R
abbrev jK:=VP (oy ao)
abbrev ko:=VP iP
abbrev Lower :=mD (Fin 3) iP
abbrev qV:ao[X] →+* iP:=lI _ _
abbrev DI:ao →+* iP:=lI _ _
def jH (p:ao[X]) :kS[X] :=p.map (lI ao kS)
def ahH (num :ao[X][X]) (den:ao[X]) :kS[X] :=
  lz ((lI ao[X] kS den)⁻¹) *
    num.map (lI ao[X] kS)
def Tj (num :ao[X][X]) (den:ao[X]) (z :ao) :ao[X] :=
 lz ((den.eval z)⁻¹)*num.map (Polynomial.evalRingHom z)
structure kH {Γ:n5 K} {s :K→K[X]} (P:jF Γ s) where
 numerator :ao[X][X]
 denominator :ao[X]
 at_zero :denominator.eval 0≠0
 small:numerator.natDegree<P.H.natDegree
 generic_unit :IsCoprime
  (jH P.c*(jH P.a₀ +
    lz (lI ao[X] kS nq)*jH P.a₁))
  (jH P.H)
 generic_congruence :jH P.H ∣
  jH P.c*(jH P.a₀ +
    lz (lI ao[X] kS nq)*jH P.a₁) *
    ahH numerator denominator +
    lz (lI ao[X] kS nq)*jH P.q
 regular : ∀ γ∈Γ,denominator.eval (P.z γ)≠0
 quotient : ∀ γ∈Γ,∃ T:ao[X],T.natDegree≤131071 ∧
  extend (s γ)=P.H*T+Tj numerator denominator (P.z γ)
def vC {R:Type*} [oq R] (F:VP R) :ℕ :=
 F.weightedTotalDegree (fun i=>i.elim 0 (fun _=>1))
def lP {R:Type*} [oq R] (F:VP R) :ℕ :=
 F.weightedTotalDegree (fun i=>i.elim 0 Fin.val)
def gY {R:Type*} [oq R] (F:VP R) :ℕ:=F.degreeOf none
def Jn {R:Type*} [oq R] (a :lV) (F:VP R) :Prop :=
  vC F≤a.b∧lP F≤a.j∧F.degreeOf (some 2)≤a.t ∧
    gY F≤70000
def ahD:Shape :=⟨6789,2300,1150⟩
def Ga :Shape :=⟨6820,2300,1150⟩
abbrev Cj:ℕ:=5746355
abbrev Fw:ℕ:=2769994
abbrev ajA:ℕ:=5000*180265 - Cj
abbrev E3:ℕ:=5000*180265-Fw
def aCk (x v :ao) (F:jK) :jK :=
  oz c9 (fun j =>
    if j=some 0 then
      aU (some 0)+MvPolynomial.C (lz v) -
        c9 (lz x-Polynomial.X)*aU (some 1) -
        c9 ((lz x-Polynomial.X)^2)*aU (some 2)
    else aU j) F
def bAy (w:I→K) (F:jK) :Prop :=
  ∀ i (a :mA →₀ ℕ),
    (nq-Polynomial.C (embed (node i)))^(5000-3*a (some 0)) ∣
      (aCk (embed (node i)) (embed (w i)) F).coeff a
def ahb (h t:ℕ) (F:jK) :Prop :=
  ∀ a∈F.support,(F.coeff a).natDegree +
    a.sum (fun i e=>i.elim 0 (fun j=>(131071+h - j.val)*e))≤t
def ar9 {Γ s} (P:jF Γ s) (L:kH P) (i:Fin 3) :
    mD (Fin 3) kS[X] :=
  c9 (oD i.val (ahH L.numerator L.denominator)) +
    ∑ j:Fin 3,if j.val≤ i.val then
      c9 (oD (i.val - j.val) (jH P.H)) *
        aU j
    else 0
def restore {Γ s} (P:jF Γ s) (L:kH P) (F:jK) :
    mD (Fin 3) kS[X] :=
  oz (MvPolynomial.C.comp (Polynomial.mapRingHom (lI ao kS)))
    (fun i=>i.elim
      (c9 (lz (lI ao[X] kS nq)))
      (ar9 P L)) F
def Source {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (a :lV) (t:ℕ) (F:jK) :Prop :=
  Jn a F∧ahb P.H.natDegree (t+(a.b+a.j)*P.H.natDegree) F ∧
    bAy w F ∧
    (c9 (jH P.H))^(a.b+a.j)∣restore P L F
def ap2 {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (a :lV) (t n:ℕ) :Prop :=
  ∃ e :Fin n→jK,LinearIndependent ao e ∧
    ∀ i,Source w P L a t (e i)
def Dl (a :mA →₀ ℕ) :ℕ :=
 7800*a none+49196*a.some.sum (fun _ e=>e)
def aox (a :mA →₀ ℕ) (F:jK) :jK :=
  (oz (MvPolynomial.C.comp c9)
    (fun i=>aU i+MvPolynomial.C (aU i)) F).coeff a
def bC (F:jK) :ko:=MvPolynomial.map qV F
def ED (z :iP) (y :Fin 3→iP) :mA→iP :=
 fun i=>i.elim z y
def jW (S:ao[X]) :Fin 3→iP:= fun i=>qV (jet S i)
def translate {σ:Type*} (y :σ→iP) :
    mD σ iP →+* mD σ iP :=
  MvPolynomial.eval₂Hom c9 (fun i=>aU i+MvPolynomial.C (y i))
def Qu (F:Lower) (y :Fin 3→iP) (d:ℕ) :Prop :=
 ∀ a∈(translate y F).support,d≤a.sum (fun _ e=>e)
def H9 (F:Lower) :ℕ:=F.support.sup (fun a=>a.sum (fun i e=>i.val*e))
def qN (F:ko) :Lower[X] :=MvPolynomial.optionEquivLeft _ _ F
def YB (f :iP[X]) :ko :=
 Polynomial.eval₂RingHom c9 (aU none) f
structure awY (F G:ko) where
 fixed:n5 ko
 moving:n5 ko
 pure :iP[X]
 exponent:ko→ℕ
 left:ko
 right:ko
 pure_ne :pure≠0
 pure_degree :pure.natDegree≤140000
 fixed_kind : ∀ f∈fixed,Irreducible f∧0<vC f∧gY f=0
 moving_kind : ∀ f∈moving,Irreducible f∧0<vC f ∧
  0<gY f∧f.degreeOf (some 2)=0
 fixed_total:vC (∏ f∈fixed,f)≤68
 fixed_index :lP (∏ f∈fixed,f)≤23
 moving_total:vC (∏ f∈moving,f)≤10
 moving_index :lP (∏ f∈moving,f)≤3
 moving_seed :gY (∏ f∈moving,f)≤112
 azo:F=(YB pure*(∏ f∈fixed,f^exponent f) *
  (∏ f∈moving,f^exponent f))*left
 az7:G=(YB pure*(∏ f∈fixed,f^exponent f) *
  (∏ f∈moving,f^exponent f))*right
 left_ne :left≠0
 right_ne :right≠0
 proper :IsRelPrime left right
 left_caps :Jn ahD left
 right_caps :Jn Ga right
def pad (F:ko) (a :ao[X]) :ko :=
 F*YB (a.map DI)
end
end jA
end
section
namespace jA
noncomputable section
open aR Polynomial
open scoped BigOperators
set_option maxRecDepth 4000
end
end jA
end
section
namespace jA
noncomputable section
open K1 aR
open scoped Polynomial BigOperators
def c1 :Prop :=
 ∀ Γ s (P:jF Γ s),Nonempty (kH P)
end
end jA
end
section
namespace NR
set_option backward.isDefEq.respectTransparency false
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
inductive Bank where
 | first
 | second
def Bank.box :Bank→lV
 | .first=>ahD
 | .second=>Ga
def Bank.cut:Bank→ℕ
 | .first=>ajA
 | .second=>E3
def Bank.avF:Bank→ℕ
 | .first=>10697571688375
 | .second=>10697783317215
def ay8 (a :lV) (q:ℕ) :ℕ :=
  ∑ e₂∈ov (min q (min a.t (a.j/2))+1),
    (min (q-e₂) (a.j - 2*e₂)+1)
def eMG (a :lV) :ℕ :=
  ∑ q∈ov (a.b+1),
    (a.b+a.j - q)*ay8 a q*(70001+(a.b - q))
def TT (V W:cy ao jK) :ℕ :=
 oj ao V-Module.finrank ao (V ⊓ W:cy ao jK)
private def dxP (x v :ao) :jK →ₗ[ao] jK :=
  (MvPolynomial.aeval (R:=ao[X]) (fun j:mA =>
    if j=some 0 then
      aU (some 0)+MvPolynomial.C (lz v) -
        c9 (lz x-Polynomial.X)*aU (some 1) -
        c9 ((lz x-Polynomial.X)^2)*aU (some 2)
    else aU j)).toLinearMap.restrictScalars ao
def ays (x v :ao) :cy ao jK :=
  ⨅ e :mA →₀ ℕ,
    ((Ideal.span {((nq-Polynomial.C x)^(5000-3*e (some 0)) :
      ao[X])}).restrictScalars ao).comap
      (((MvPolynomial.lcoeff ao[X] e).restrictScalars ao).comp (dxP x v))
abbrev Lq:=mD (Fin 3) kS[X]
private def fW5 {Γ s} (P:jF Γ s) (L:kH P) :
   jK →ₗ[ao] Lq :=
 (MvPolynomial.aevalTower
   (((Algebra.ofId kS[X] Lq).restrictScalars ao).comp
     (Polynomial.mapAlgHom (Algebra.ofId ao kS)))
   (fun i:mA=>i.elim
     (c9 (lz (lI ao[X] kS nq)))
     (ar9 P L))).toLinearMap
def amn {Γ s} (P:jF Γ s) (L:kH P)
    (a :lV) (D:kS[X]) :cy ao jK :=
  ((Ideal.span {((c9 D:Lq)^(a.b+a.j))}).restrictScalars ao).comap
    (fW5 P L)
def O8 (α:ao) :kS[X] :=
 nq-Polynomial.C (lI ao kS α)
def cxD {Γ s Γ' s'} (P:jF Γ s) (P' : jF Γ' s') :Prop :=
  (∃ ε:ao,P'.H=P.H+Polynomial.C ε) ∧
    P'.c=P.c∧P'.q=P.q∧P'.a₀=P.a₀∧P'.a₁=P.a₁
theorem bsz (x v :ao) (F:jK) :
    F∈ays x v ↔ ∀ e :mA →₀ ℕ,
      (nq-Polynomial.C x)^(5000-3*e (some 0)) ∣
        (aCk x v F).coeff e := by
  simp only [ays,Submodule.mem_iInf,oZ,oY ,
    LinearMap.comp_apply,LinearMap.restrictScalars_apply,MvPolynomial.lcoeff_apply,
    pC]
  rfl
theorem aVU {Γ s} (P:jF Γ s) (L:kH P) (a :lV)
  (D:kS[X]) (F:jK) :
  F∈amn P L a D↔(c9 D)^(a.b+a.j)∣restore P L F:= by
 simp only [amn,oZ,oY ,
  pC]
 rfl
end
end NR
end
section
namespace NR
set_option maxHeartbeats 700000
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
def c3:Prop :=
  ∀ (Γ:n5 K) (s :K→K[X]) (P:jF Γ s) (L:kH P)
    (a :lV) (α:ao) (V:cy ao jK),nX ao V →
    (∀ F∈V,Jn a F)→P.H.IsRoot α→P.H.derivative.eval α≠0 →
    TT V (amn P L a (O8 α))≤eMG a
def c4 :Prop :=
  ∀ (Γ:n5 K) (s :K→K[X]) (P:jF Γ s) (L:kH P)
    (a :lV) (V:cy ao jK) (r :ℕ),nX ao V →
    (∀ (P' : jF ∅ (fun _:K=>(0:K[X]))) (L' : kH P'),
      cxD P P' → P'.H.natDegree=P.H.natDegree→P'.H.Separable →
      TT V (amn P' L' a (jH P'.H))≤ r) →
    TT V (amn P L a (jH P.H))≤ r
private theorem buG {V U:cy ao jK} [nX ao V]
   (h:U≤V) :Module.rank ao U<Cardinal.aleph0 :=
 (pz h).trans_lt (Module.rank_lt_aleph0 ao ↥V)
private theorem bXt (V U W:cy ao jK) [nX ao V] :
    TT V (U ⊓ W)≤TT V U + TT V W:= by
  have he : (V ⊓ U) ⊓ (V ⊓ W)=V ⊓ (U ⊓ W) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans lJ)
        (le_inf (inf_le_left.trans ox) (inf_le_right.trans ox))
    · exact le_inf (le_inf lJ (inf_le_right.trans lJ))
        (le_inf lJ (inf_le_right.trans ox))
  have h:=Submodule.rank_sup_add_rank_inf_eq (V ⊓ U) (V ⊓ W)
  rw [he] at h
  have hle : (V ⊓ U) ⊔ (V ⊓ W)≤V:=sup_le lJ lJ
  have hdim:=congrArg Cardinal.toNat h
  rw [oK (buG hle) (buG lJ),
    oK (buG lJ) (buG lJ)] at hdim
  change oj ao ((V ⊓ U) ⊔ (V ⊓ W) :cy ao jK) +
    oj ao (V ⊓ (U ⊓ W) :cy ao jK) =
      oj ao (V ⊓ U:cy ao jK) +
      oj ao (V ⊓ W:cy ao jK) at hdim
  have hsup:=Submodule.finrank_mono hle
  unfold TT
  omega
private theorem bCP {ι:Type*} (V:cy ao jK)
   [nX ao V] (T:n5 ι) (U:ι→cy ao jK) (r :ℕ)
   (hr : ∀ i∈T,TT V (U i)≤ r) :
   TT V (T.inf U)≤T.card*r := by
 classical
 induction T using Finset.induction_on with
 | empty=>rw [Finset.inf_empty,Finset.card_empty,zero_mul,TT,inf_top_eq,Nat.sub_self]
 | insert i T hi ih =>
   rw [Finset.inf_insert,Finset.card_insert_of_notMem hi,Nat.succ_mul]
   have hi' := hr i (Finset.mem_insert_self i T)
   have hT:=ih fun j hj=>hr j (Finset.mem_insert_of_mem hj)
   exact (bXt V (U i) (T.inf U)).trans
     (by simpa only [add_comm] using Nat.add_le_add hi' hT)
private theorem cFT (V:cy ao jK) [nX ao V]
  {U W:cy ao jK} (h:U≤W) :TT V W≤TT V U :=
 Nat.sub_le_sub_left
  (Cardinal.toNat_le_toNat (pz (inf_le_inf_left V h))
    (buG (show V ⊓ W≤V from lJ))) _
private theorem cKM {Aw Bp required amm pole :ℕ}
  (hsize :required+amm+pole≤Aw)
  (hcodim:Aw - Bp≤amm+pole) :required≤Bp:= by
 omega
end
end NR
end
section
namespace Rj
noncomputable section
open aR jA MvPolynomial
open scoped BigOperators
abbrev Flat :=mD (nI (Fin 3)) ao
abbrev Exp:=nI (Fin 3) →₀ ℕ
def BU (v :nI (Fin 3)) :ℕ:=v.elim 0 (fun _=>1)
def indexWeight (v :nI (Fin 3)) :ℕ:=v.elim 0 Fin.val
def topWeight (v :nI (Fin 3)) :ℕ:=v.elim 0 (Pi.single (2 :Fin 3) 1)
def FF (B:ℕ) (e :Exp) :Prop :=
 e.weight BU≤B∧e.weight indexWeight≤2300∧e (some 2)≤1150
def apR (B:ℕ) :cy ao Flat :=restrictSupport ao {e | FF B e}
def La (v :nI (Fin 3)) :Flat :=
  if v=some 0 then
    aU (some 0)+MvPolynomial.X none*aU (some 1) -
      aU none^2*aU (some 2)
  else aU v
def J6:Flat →ₐ[ao] Flat :=bind₁ La
def oH (v :nI (Fin 3)) :ℕ:=v.elim 1 (Pi.single (0:Fin 3) 3)
def origin :Flat →ₗ[ao] Flat :=(weightedTruncation oH 5000).comp J6.toLinearMap
def offset (k :ℕ) :ℤ:=(k :ℤ) - 2300
def TO (q k :ℕ) :Set Exp :=
  { e | FF q e∧e.weight BU=q ∧
    (e none :ℤ)-(e.weight indexWeight:ℤ)=offset k }
def Block (q k :ℕ) :cy ao Flat :=restrictSupport ao (TO q k)
def af3 (q k :ℕ) :Block q k →ₗ[ao] Flat :=
 origin.domRestrict (Block q k)
abbrev lK:=mD (Fin 3) ao
abbrev adf :=Fin 3 →₀ ℕ
def iO (q:ℕ) :ℕ:=min q 2300
def cbQ (q:ℕ) (g:ℤ) :Set adf :=
  { e | e.weight (fun _=>1)=iO q ∧
    -g≤(e.weight Fin.val :ℤ)∧e.weight Fin.val≤2300∧e 2≤1150 }
def aqz (q:ℕ) (g:ℤ) :cy ao lK :=
 restrictSupport ao (cbQ q g)
def acw (j:Fin 3) :lK :=
 if j=0 then aU 0+MvPolynomial.X 1-MvPolynomial.X 2
 else aU j
def Ic (q:ℕ) (g:ℤ) :ℤ:=5000-(q:ℤ) - g
def aPi (q:ℕ) (g:ℤ) :aqz q g →ₗ[ao] lK :=
  ((weightedTruncation (![2,0,1] :Fin 3→ℕ) (Ic q g).toNat).comp
    (bind₁ acw).toLinearMap).domRestrict (aqz q g)
structure Flag where
 iy :ℤ
 HE :ℤ
def pT (q:ℕ) (g:ℤ) (i:Fin 3) :Flag :=
 let d:ℤ:=iO q
 ![⟨0,-g⟩,⟨d - 1150,2*d - 2300⟩,⟨0,Ic q g⟩] i
abbrev kJ:=Fin 6→ℕ
def yE (j:Fin 6) :ℤ:=if j=5 then 2 else 1
def Jd (j:Fin 6) (i:Fin 3) :Flag :=
  (![![⟨1,2⟩,⟨0,0⟩,⟨1,1⟩],
    ![⟨1,1⟩,⟨1,1⟩,⟨0,0⟩],
    ![⟨0,0⟩,⟨1,1⟩,⟨1,1⟩],
    ![⟨0,0⟩,⟨1,2⟩,⟨0,0⟩],
    ![⟨0,0⟩,⟨0,0⟩,⟨1,2⟩],
    ![⟨1,1⟩,⟨1,2⟩,⟨1,2⟩]] :Fin 6→Fin 3→Flag) j i
def K6 (q:ℕ) (p:kJ) :ℤ :=
 iO q - ∑ j,(p j:ℤ)*yE j
def D8 (q:ℕ) (g:ℤ) (p:kJ) (i:Fin 3) :Flag :=
  ⟨(pT q g i).iy - ∑ j,(p j:ℤ)*(Jd j i).iy,
    (pT q g i).HE - ∑ j,(p j:ℤ)*(Jd j i).HE⟩
def sG (n:ℤ) :ℤ:=n*(n+1)/2
def yC (F:Flag) :ℤ :=
 let u:=max 0 (max F.iy ((F.HE+1)/2))
 let v :=max u F.HE
 sG u+sG (v - u)
def m5 (d:ℤ) (F:Fin 3→Flag) :ℤ :=
 if d<0 then 0 else sG (d+1) - ∑ i,yC (F i)
def gd (d w:ℤ) :ℤ :=
  if w<0 then 0 else
    let u:=min w (2*d)
    (u+2)^2/4 - sG (max 0 (u - d))
def Bb (q:ℕ) (g:ℤ) :ℤ :=
 let d:ℤ:=iO q
 gd d 2300 - gd d (min 2300 (-g - 1))
def xR (q:ℕ) (g:ℤ) (p:kJ) :ℕ :=
  if Ic q g≤0 then 0 else
    let base :=m5 (iO q) (pT q g)
    let ic:=m5 (K6 q p) (D8 q g p)
    (Bb q g - max 0 (max base ic)).toNat
def Xi (p:ℕ→ℕ→kJ) (q:ℕ) :ℕ :=
 ∑ k∈ov 7300,xR q (offset k) (p q k)
end
end Rj
end
section
namespace aw9
def cost (w:ℤ) :ℤ:=((w+1)/2)*(w/2+1)
def columns (k :ℤ) :ℤ:=1324801 - cost (max 0 (2300 - k))
def RZ (k t:ℤ) :ℤ:=t - 2*k - 1
def PO (k t:ℤ) :ℤ:=2*t - 2301 - k
def azu (both:Bool) (k t:ℤ) :ℤ :=
 if both then RZ k t else 0
def aJt (both:Bool) (k t:ℤ) :ℤ :=
  let n:=azu both k t
  let m:=PO k t
  columns k+cost (2300 - k - 2*n - m)+cost (t - n - 2*m) -
    (1151 - n - m)^2
def admissible (both:Bool) (k l r :ℤ) :Prop :=
  (if both then 0≤RZ k l else RZ k r≤0) ∧
    0≤PO k l∧azu both k r+PO k r≤1150 ∧
    0≤2300 - k - 2*azu both k r-PO k r ∧
    0≤ r-azu both k r - 2*PO k r
instance (both:Bool) (k l r :ℤ) :Decidable (admissible both k l r) := by
 unfold admissible
 cases both <;> infer_instance
inductive Mode where
 | columns
 | empty
 | ic (both:Bool)
 deriving DecidableEq
def valid (mode :Mode) (k l r :ℤ) :Prop :=
 match mode with
 | .columns | .empty=>True
 | .ic both=>admissible both k l r
instance (mode :Mode) (k l r :ℤ) :Decidable (valid mode k l r) := by
 cases mode <;> unfold valid <;> infer_instance
def anR (k t:ℤ) :Mode :=
  let c:=columns k
  let e :=cost t
  let both:=decide (0<RZ k t)
  if admissible both k t t∧aJt both k t< min c e then
    .ic both
  else if c≤e then .columns else .empty
def a5v (len:ℕ) :ℤ:=(len:ℤ)*(len - 1 :ℤ)/2
def a8K (len:ℕ) :ℤ:=(len:ℤ)*(len - 1 :ℤ)*(2*len - 1 :ℤ)/6
def aJF (a b:ℤ) (len:ℕ) :ℤ :=
 (len:ℤ)*cost a+b*(a+1)*a5v len+b^2*a8K len
def bhE (a b:ℤ) (len:ℕ) :ℤ :=
 (len:ℤ)*a^2+2*a*b*a5v len+b^2*a8K len
def azE (mode :Mode) (k start:ℤ) (len:ℕ) :ℤ :=
  match mode with
  | .columns=>(len:ℤ)*columns k
  | .empty=>aJF start 1 len
  | .ic both =>
    let n:=azu both k start
    let m:=PO k start
    let s :ℤ:=if both then 1 else 0
    (len:ℤ)*columns k +
      aJF (2300 - k - 2*n - m) (-2*s - 2) len +
      aJF (start - n - 2*m) (-3 - s) len -
      bhE (1151 - n - m) (-2*s-4) len
def Ly (k start:ℤ) (mode :Mode) :ℕ→ℕ→ℕ→ℕ
  | 0,lo,_=>lo
  | fuel+1,lo,hi =>
    if hi≤lo+1 then lo
    else
      let mid :=(lo+hi)/2
      if anR k (start+2*mid)=mode then Ly k start mode fuel mid hi
      else Ly k start mode fuel lo mid
def E0 (k start:ℤ) (len:ℕ) (mode :Mode) :ℕ :=
 if anR k (start+2*((len:ℤ) - 1))=mode then len
 else min len (Ly k start mode 12 0 (len - 1)+1)
def aoE (k :ℤ) :ℕ→ℤ→ℕ→ℤ
  | 0,_,len=>(len:ℤ)*columns k
  | fuel+1,start,len =>
    if len=0 then 0 else
      let mode :=anR k start
      let width :=E0 k start len mode
      let last :=start+2*((width :ℤ) - 1)
      let bound:=if valid mode k start last then
        azE mode k start width else (width :ℤ)*columns k
      bound+aoE k fuel (start+2*width) (len - width)
def aDZ (k :ℕ) :ℤ :=
 let len:=min 2700 (5000 - k)
 let start:ℤ:=5001-(k :ℤ)-len
 aoE k 8 start ((len+1)/2)+aoE k 8 (start+1) (len/2)
def total (start:ℕ) :ℕ→ℤ
 | 0=>0
 | len+1=>total start len+aDZ (start+len)
end aw9
end
