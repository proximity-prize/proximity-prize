import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import ProximityPrize.SubmissionLower.BE
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→lI,Fin.castLE→pz,Finset→aU,Finset.card_biUnion_le→pQ,FractionRing→ oD,Function.Injective→qm,Ideal→cy,Ideal.span→ oj,Irreducible→ oq,IsFractionRing.injective→qx,IsSeparable→pC,Module.Finite→nI,Module.finrank→lz,MvPolynomial→mD,MvPolynomial.C→lV,MvPolynomial.X→c9,MvPolynomial.eval→n5,MvPolynomial.eval_rename→p5,MvPolynomial.eval₂Hom→p7,MvPolynomial.map→ ov,MvPolynomial.rename→ oZ,Polynomial→lJ,Polynomial.X→ oY,Polynomial.eval₂RingHom→nX,Polynomial.hom_eval₂→p9,Polynomial.mapRingHom→ ox,RingHom.ext→pL,RingHom.ker→ oK,Submodule→ oz,Submodule.mem_bot→p6,Submodule.mem_top→pU,cu.Equation→ oy,cu.Shape→nq,ringKrullDim→pG
set_option autoImplicit true
section
namespace gT
noncomputable section
open K1 cu Polynomial
open scoped BigOperators
structure Ls where
 dI:ℕ
 cheap:nq
 layered:nq
def stages :List Ls :=
 [⟨0,⟨59,82,18,1899⟩,⟨136,190,40,8441⟩⟩,
  ⟨1,⟨66,92,21,2076⟩,⟨150,210,44,9356⟩⟩,
  ⟨2,⟨73,102,23,2261⟩,⟨164,229,48,10272⟩⟩,
  ⟨3,⟨80,112,25,2455⟩,⟨178,249,52,11191⟩⟩,
  ⟨5,⟨94,131,30,2824⟩,⟨213,298,62,12959⟩⟩,
  ⟨8,⟨115,160,36,3401⟩,⟨262,366,77,15611⟩⟩,
  ⟨12,⟨136,190,43,4204⟩,⟨325,454,96,19187⟩⟩,
  ⟨18,⟨178,248,56,5332⟩,⟨409,572,121,24615⟩⟩,
  ⟨28,⟨241,336,78,7235⟩,⟨570,797,169,33523⟩⟩,
  ⟨42,⟨325,453,104,9976⟩,⟨759,1061,224,46271⟩⟩]
def full:Shape :=⟨836,1164,247,273617⟩
def fF:List Shape :=full :: stages.flatMap (fun s=>[s.cheap,s.layered])
def alm (G:Jet) :Prop :=
 ∃ j i,0<((G.coeff j).coeff i).totalDegree
abbrev tK:=lJ (lJ FX)
def FW (G:tK) (S:K[X]) :FX :=
 G.eval₂ (evalRingHom (kr S)) (kr S.derivative)
def dmY {u del} {M:jG u del} {Γ} (F:mJ M Γ)
    (T:aU K) (B J:ℕ) :Prop :=
  ∃ G:tK,G≠0∧G.natDegree≤J ∧
    (∀ j i,((G.coeff j).coeff i)≠0→i+j≤B) ∧
    ∀ γ∈T,FW G (F.scalar γ)=0
def b3o:List (ℕ×ℕ) :=(507836,93976) :: fF.map (fun s=>(s.B,s.J))
def an6:ℕ:=134625
def cKN :ℕ :=
 5980+((p+1)*1052972+19635660)+(p+1)*(fF.map Shape.U).sum+310966947964
def eye :ℕ:=220891211
def eyf :ℕ:=4783514411
abbrev Ambient:=mD (Fin 4) FX
abbrev kM:=mD (Fin 3) FX
def pZ:aZ →+* kM :=
 (oZ (pz (by decide :2≤3))).toRingHom
def oi:kM →+* Ambient :=
 (oZ (pz (by decide :3≤4))).toRingHom
def A7:oy →+* kM:=nX pZ (c9 2)
def iJ:Jet →+* Ambient:=nX (oi.comp A7) (c9 3)
def aEE (z :K) (S:K[X]) :kM →+* FX :=
 n5 ![jz z,(jz z)^p,kr S]
def aci (z :K) (S:K[X]) :Ambient →+* FX :=
 n5 ![jz z,(jz z)^p,kr S,kr S.derivative]
private theorem d2K (a b y :FX) (f :oy) :
   n5 ![a,b,y] (A7 f)=f.eval₂ (n5 ![a,b]) y := by
 have hseed : (n5 ![a,b,y]).comp pZ=n5 ![a,b] := by
   apply pL
   intro g
   change n5 ![a,b,y] (oZ (pz (by decide :2≤3)) g)= _
   rw [p5]
   have hvec : ![a,b,y] ∘ Fin.castLE (by decide :2≤3) = ![a,b] := by
     funext i
     fin_cases i <;> rfl
   rw [hvec]
 change n5 ![a,b,y] (f.eval₂ pZ (c9 2))= _
 rw [p9,hseed,MvPolynomial.eval_X]
 rfl
private theorem d2u (a b y v :FX) (f :kM) :
  n5 ![a,b,y,v] (oi f)=n5 ![a,b,y] f := by
 change n5 ![a,b,y,v] (oZ (pz (by decide :3≤4)) f)= _
 rw [p5]
 have hvec : ![a,b,y,v] ∘ Fin.castLE (by decide :3≤4) = ![a,b,y] := by
  funext i
  fin_cases i <;> rfl
 rw [hvec]
theorem d2L (z :K) (S:K[X]) (f :oy) :
   aci z S (oi (A7 f))=yq f z S :=
 (d2u (jz z) _ _ _ (A7 f)).trans (d2K (jz z) _ _ f)
theorem aNB (z :K) (S:K[X]) (P:Jet) :
   aci z S (iJ P)=rD P z S:= by
 have h: (aci z S).comp (oi.comp A7) =
     nX (qD z) (kr S) := by
   exact pL (d2L z S)
 have hv :aci z S (c9 3)=kr S.derivative := by
   simp [aci]
 change aci z S (P.eval₂ (oi.comp A7) (c9 3))= _
 rw [p9,h,hv]
 rfl
def IZ (I:cy Ambient) (z :K) (S:K[X]) :Prop :=
 I≤oK (aci z S)
def aSf (I:cy kM) (z :K) (S:K[X]) :Prop :=
 I≤oK (aEE z S)
abbrev aQ:=oD aZ
def ek (i:Fin 2) :aQ :=
 lI aZ aQ (c9 i)
def B4 {n:ℕ} (i j:Fin n) :mD (Fin n) aQ :=
  c9 i+MvPolynomial.C (ek 0)*c9 j -
    lV (ek 1)
def Pp {n:ℕ} (i:Fin n) :mD (Fin n) aQ :=
 c9 i-MvPolynomial.C (ek 1)
abbrev gk {R:Type} [CommRing R] (I:cy R) :=R ⧸ I
abbrev rM (I:cy Ambient) :=
 gk (I.map (ov (lI FX aQ)) ⊔ oj {B4 0 1})
abbrev as2 (I:cy Ambient) :=
 gk (I.map (ov (lI FX aQ)) ⊔ oj {Pp 2})
abbrev abX (I:cy kM) :=
 gk (I.map (ov (lI FX aQ)) ⊔ oj {B4 0 1})
abbrev SI (I:cy kM) :=
 gk (I.map (ov (lI FX aQ)) ⊔ oj {Pp 2})
def dnD {u del} (M:jG u del) {Γ} (F:mJ M Γ)
    (T:aU K) :Prop :=
  ∃ cs :aU (cy Ambient),
    (∀ I∈cs,I.IsPrime∧pG (gk I)=1 ∧
      nI aQ (rM I) ∧
      0<lz aQ (rM I) ∧
      nI aQ (as2 I)) ∧
    (∑ I∈cs,lz aQ (rM I))≤eye ∧
    (∑ I∈cs,lz aQ (as2 I))≤eyf ∧
    ∀ γ∈T,∃ I∈cs,IZ I (M.label γ) (F.scalar γ)
def bbt (I:cy kM) (g H :ℕ) :Prop :=
  I.IsPrime ∧
    ∃ C₀:mD (Fin 2) L,oq C₀ ∧
      I.comap pZ =
        oj {ov
          ((lI L[X] FX).comp (Polynomial.C:L →+* L[X])) C₀} ∧
      nI aQ (abX I) ∧
      lz aQ (abX I)=C₀.totalDegree*g ∧
      nI aQ (SI I) ∧
      lz aQ (SI I)≤H
abbrev vR:=mD (Fin 2) aQ
def Dk :Ambient →+* vR :=
  p7 (MvPolynomial.C.comp (lI FX aQ))
    ![lV (ek 0),lV (ek 1),c9 0,c9 1]
abbrev Y0 (I:cy Ambient) :=
 gk (I.map Dk)
def CG:Ambient →+* vR :=
  p7 (MvPolynomial.C.comp (lI FX aQ))
    ![c9 0,c9 1,lV (ek 0),lV (ek 1)]
abbrev Lj (I:cy Ambient) :=
 gk (I.map CG)
structure cAl (rows :vP) where
 ideals :aU (cy Ambient)
 prime : ∀ I∈ideals,I.IsPrime
 bg9 : ∀ I∈ideals,nI aQ (Y0 I)
 seed_size : ∀ I∈ideals,0<lz aQ (Y0 I) ∧
  lz aQ (Y0 I)<p
 jet_finite : ∀ I∈ideals,nI aQ (Lj I)
 jet_size : ∀ I∈ideals,0<lz aQ (Lj I) ∧
  lz aQ (Lj I)<p
 terminal : ∀ I∈ideals,∀ P∈rows full (full.m*180265 - 1),iJ P∈I
structure Geometry {u del} (M:jG u del) {Γ} (F:mJ M Γ)
  (rows :vP) where
 direct :aU K
 Hj:aU K
 Bp:aU K
 fixedGroups : (ℕ×ℕ)→aU K
 parents :cAl rows
 direct_card:direct.card≤ cKN
 fixed_eq : ∀ k∈b3o,fixedGroups k⊆Γ∧dmY F (fixedGroups k) k.1 k.2
 lost_subset :Hj⊆Γ
 loss_cover :dnD M F Hj
 kept_subset :Bp⊆Γ
 kept_cover : ∀ γ∈Bp,∃ I∈parents.ideals,IZ I (M.label γ) (F.scalar γ)
 cover : ∀ γ∈Γ,γ∈direct∨(∃ k∈b3o,γ∈fixedGroups k)∨γ∈Hj∨γ∈Bp
end
end gT
end
section
namespace aBa
open cu gT
def Mq (h r :ℕ) (s :nq) :ℕ :=
 s.m*180265 - 2*h*r
def amv (h r :ℕ) (s :nq) (q j:ℕ) :ℕ :=
 Mq h r s+j - q*(131071 - h)
def az0 (h r :ℕ) (s :nq) :ℕ :=
 triangle s.U*ku s (amv h r s)
end aBa
end
section
set_option maxSynthPendingDepth 8
namespace aBa
noncomputable section
open cu gT Polynomial UniqueFactorizationMonoid
private def bEl (V:oz FX Jet) (G:Jet) :oz FX V where
 carrier := {Q | G∣(Q:Jet)}
 zero_mem' := dvd_zero G
 add_mem' := fun hP hQ=>dvd_add hP hQ
 smul_mem' a := by
  rintro Q ⟨R,hR⟩
  exact ⟨a•R,by
   change a•(Q:Jet)=G*(a•R)
   rw [hR,mul_smul_comm]⟩
theorem cNB (P:Jet) (hP:P≠0) (V:oz FX Jet)
    (hn : ∃ Q∈V,Q≠0)
    (hproper : ∀ G:Jet,oq G→G∣P→0<G.natDegree→alm G →
      ∃ Q∈V,¬ G∣Q) :
    ∃ Q∈V,Q≠0 ∧
      ∀ G:Jet,oq G→G∣P→0<G.natDegree→alm G → ¬ G∣Q:= by
  classical
  let:Infinite FX:=Infinite.of_injective _ (qx L[X] FX)
  let I := {H :Jet // H∈factors P}
  let:Finite I:=Set.finite_coe_iff.mpr (factors P).finite_toSet
  let tests :Option I→ oz FX V:= fun k =>
    match k with
    | none => ⊥
    | some H =>
      if ∃ G:Jet,oq G∧G∣P∧0<G.natDegree∧alm G ∧
          Associated G H.val then bEl V H.val else ⊥
  have bot_proper : (⊥ : oz FX V) ≠ ⊤ := by
    obtain ⟨Q,hQ,hnQ⟩:=hn
    intro heq
    have hmem: (⟨Q,hQ⟩:V)∈(⊥ : oz FX V) :=heq ▸ pU
    exact hnQ (congrArg Subtype.val ((p6 FX).mp hmem))
  have ht : ∀ k,tests k ≠ ⊤ := by
    intro k
    cases k with
    | none=>exact bot_proper
    | some H =>
      change (if _ then bEl V H.val else ⊥) ≠ ⊤
      split_ifs with h
      · obtain ⟨G,hi,hd,hv,hs,ha⟩:=h
        obtain ⟨Q,hQ,hnQ⟩:=hproper G hi hd hv hs
        intro heq
        have hmem: (⟨Q,hQ⟩:V)∈bEl V H.val :=heq ▸ pU
        exact hnQ (ha.dvd.trans (show H.val∣Q from hmem))
      · exact bot_proper
  obtain ⟨Q,hQ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (K:=FX) (M:=V) tests ht
  refine ⟨Q.val,Q.property,?_,?_⟩
  · intro hz
    exact hQ none ((p6 FX).mpr (Subtype.ext hz))
  · intro G hi hd hv hs hdiv
    obtain ⟨H,hH,ha⟩:=exists_mem_factors_of_dvd hP hi hd
    let k :I:=⟨H,hH⟩
    apply hQ (some k)
    change Q∈(if _ then bEl V H else ⊥)
    rw [ite_eq_left ⟨G,hi,hd,hv,hs,ha⟩]
    exact ha.symm.dvd.trans hdiv
end
end aBa
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace qQ
noncomputable section
open K1 cu Polynomial
open scoped BigOperators
abbrev IW:=lJ (lJ FX)
abbrev zI:=PrimeSpectrum Jet
def Ng:IW →+* Jet :=
 ox (ox lV)
def FW (G:IW) (S:K[X]) :FX :=
 G.eval₂ (evalRingHom (kr S)) (kr S.derivative)
def oU (G:Jet) (s :nq) :Prop :=
  ∀ v y,(G.coeff v).coeff y≠0 →
    y+v≤ s.B∧v≤ s.J∧((G.coeff v).coeff y).totalDegree≤ s.U
def ayj (i:Fin 4) :Shape :=
 ![⟨45,63,14,812⟩,⟨57,80,18,1041⟩,⟨81,114,26,1383⟩,⟨123,173,40,2173⟩] i
def aIq (i:Fin 4) :Shape :=
 ![⟨84,118,24,2907⟩,⟨114,160,33,3775⟩,⟨144,203,42,5064⟩,⟨231,325,67,8061⟩] i
def dI (i:Fin 4) :ℕ := ![0,2,5,12] i
def bk4 (h:ℕ) (rows :vP) (s :nq) :Prop :=
 ∀ W,∀ P∈rows s W,∀ i r,A5 i r P∈rows s (W+2*h*r)
def aSa (h:ℕ) (rows :vP) (s :nq) :Prop :=
  ∀ W,∀ P∈rows s W,P≠0 →
    (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree
def aeH (P Q:Jet) :Prop :=
  ∀ D:Jet,oq D→D ∣P→D ∣Q→0<D.natDegree →
    D∈Set.range Ng
abbrev aQ:=oD aZ
abbrev HR:=AlgebraicClosure aQ
abbrev tJ:=oD IW
abbrev aiF:=AlgebraicClosure tJ
abbrev bQR:=lJ (lJ HR)
def aif :aZ →+* HR :=
 (lI aQ HR).comp (lI aZ aQ)
def bHX:IW →+* aiF :=
 let first:IW →+* tJ:=lI IW tJ
 let second:tJ →+* aiF:=lI tJ aiF
 second.comp first
def aXz (y v :HR) :Jet →+* HR :=
 nX (nX aif y) v
def aF5 (q:zI) (y v :HR) :Prop :=
 oK (aXz y v)=q.asIdeal
structure N5 (q:zI) :Prop where
 a4E :q.asIdeal.height=2
 seed_side : ∃ y v,aF5 q y v∧pC aQ y∧pC aQ v
 jet_side : ∃ g:Jet →+* aiF,
  g.comp Ng=bHX∧oK g=q.asIdeal ∧
   ∀ i:Fin 2,pC tJ (g (C (C (c9 i))))
def aUO (P:Jet) :bQR:=P.map (ox aif)
def b20 (y v :HR) :cy bQR :=
  oj {C (R:=lJ HR) (oY (R:=HR) - C y),
    oY (R:=lJ HR) - C (C v)}
def wU (q:zI) (P:Jet) (m:ℕ) :Prop :=
 ∀ y v,aF5 q y v→aUO P∈b20 y v^m
abbrev aKb:=mD (Fin 2) L[X]
abbrev aix :=lJ aKb
def adV:aix →+* Equation :=
 ox (ov (lI L[X] FX))
def a2x (g:aix) :aix :=
 g.sum fun j a=>monomial j (∑ e∈MvPolynomial.support a,MvPolynomial.monomial e (AddMonoidAlgebra.coeff a e).derivative)
def caE (g:aix) :Jet :=
 C (adV (a2x g))+X*C (adV g.derivative)
def aw5 (f :oy) (g:aix) (a :L[X]) :Prop :=
 a≠0∧adV g=C (lV (lI L[X] FX a))*f
inductive Slice where
 | seed | jU | kK | Bo
abbrev dV:=oD (mD (Fin 4) FX)
abbrev bAF:=mD (Fin 2) dV
abbrev aSE :=lJ (lJ bAF)
def K9:Jet →+* aSE :=
  ox (ox
    (ov (lI FX dV)))
def bNs (i:Fin 4) :aSE :=
 C (C (lV (lI (mD (Fin 4) FX) dV (c9 i))))
def gnp (slice :Slice) :Set aSE :=
 let t₀:aSE :=C (C (c9 0))
 let t₁:aSE :=C (C (c9 1))
 let y :aSE :=C (R:=lJ bAF) (oY (R:=bAF))
 let v :aSE :=oY (R:=lJ bAF)
 let B4 :=t₀+bNs 0*t₁
 let aIh:=y+bNs 1*v
 let a :=bNs 2
 let b:=bNs 3
 match slice with
 | .seed => {t₀-a,t₁ - b}
 | .jU => {B4-a,y - b}
 | .kK => {B4-a,aIh - b}
 | .Bo => {y-a,v - b}
def pN (q:zI) (slice :Slice) :ℕ :=
 let J:=q.asIdeal.map K9 ⊔ oj (gnp slice)
 lz dV (aSE ⧸ J)
def mass (qs :aU zI) (s :Slice) :ℚ :=
 ∑ q∈qs,(pN q s :ℚ)
structure VN where
 curve :aZ
 curve_ne :curve≠0
 points :aU (FX×FX)
def VN.ow (C:VN) (z :K) :Prop :=
 qD z C.curve=0∨(jz z,jz z^p)∈C.points
structure aLQ (qs :aU zI) (f :oy) :Prop where
 positive :0<f.natDegree
 primitive :f.IsPrimitive
 separable : (f.map (lI aZ aQ)).Separable
 aiq : ∀ q∈qs,C f∈q.asIdeal
 divides_leading : ∀ (P:Jet) (k :ℕ),P≠0 →
  (∀ q∈qs,wU q P k)→f^(k-P.natDegree)∣P.leadingCoeff
end
end qQ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace pI
noncomputable section
open K1 cu gT Polynomial
open scoped Classical
def nV (i:Fin 10) :Ls :=
 stages.get ⟨i.val,by simp [stages]⟩
def oU (P:Jet) (s :nq) :Prop :=
  ∀ j i,(P.coeff j).coeff i≠0 →
    i+j≤ s.B∧j≤ s.J∧((P.coeff j).coeff i).totalDegree≤ s.U
def abM (G:tK) (B J:ℕ) :Prop :=
 G≠0∧G.natDegree≤J ∧ ∀ j i,(G.coeff j).coeff i≠0→i+j≤B
def Gw:tK →+* Jet:=qQ.Ng
structure NO (P:Jet) (s :nq) where
 equation :tK
 equation_caps :abM equation s.B s.J
 residual:Jet
 factorization :P=Gw equation*residual
 Ra : ∀ G:tK,oq (Gw G) → ¬ Gw G∣residual
def aaS (G:tK) (I:cy Ambient) :Prop :=
 iJ (Gw G)∈I
abbrev dV:=oD (mD (Fin 4) FX)
abbrev PI:=mD (Fin 4) dV
def kz (i:Fin 4) :dV :=
 lI (mD (Fin 4) FX) dV (c9 i)
def AU:Ambient →+* PI:=ov (lI FX dV)
def JN :PI :=
  c9 0+MvPolynomial.C (kz 0)*c9 1 -
    lV (kz 2)
def Z6:PI :=
  c9 2+MvPolynomial.C (kz 1)*c9 3 -
    lV (kz 3)
abbrev ani (I:cy Ambient) :=
 gk (I.map AU ⊔ oj {JN,c9 2 -
  lV (kz 3)})
abbrev Ik (I:cy Ambient) :=
 gk (I.map AU ⊔ oj {JN,Z6})
def F7:lJ FX →+* Ambient :=
 nX lV (c9 2)
def C7:tK →+* Ambient:=iJ.comp Gw
structure xN (I:cy Ambient) :Prop where
 prime :I.IsPrime
 dimension :pG (gk I)=2
 bg9:nI aQ (Y0 I)
 a6j:nI dV (ani I)
 bfE :nI dV (Ik I)
 jet_finite :nI aQ (Lj I)
 seed_size :0<lz aQ (Y0 I) ∧
  lz aQ (Y0 I)<p
 mixed_lt:lz dV (Ik I)<p
 jet_lt:lz aQ (Lj I)<p
 ordinate_dominant:qm ((Ideal.Quotient.mk I).comp F7)
def dual (I:cy Ambient) :Prop :=0<lz aQ (Lj I)
def pN (I:cy Ambient) :Fin 4→ℕ :=
  ![lz aQ (Y0 I),lz dV (ani I),
    lz dV (Ik I),lz aQ (Lj I)]
def mass (S:aU (cy Ambient)) (k :Fin 4) :ℕ :=
 ∑ I∈S,pN I k
def dM (S:aU (cy Ambient)) (cap:Fin 4→ℕ) :Prop :=
 ∀ k,mass S k≤ cap k
def O9 (I:cy Ambient) (P:Jet) (m:ℕ) :Prop :=
 let ajF:=if dual I then ⊥ else (I.comap C7).map C7
 ∃ a :Ambient,a∉I∧a*iJ P∈I^m ⊔ ajF
def budget (n:ℕ) :Fin 4→ℕ :=
 match n with
 | 0 => ![5980,227898,1052972,16029459]
 | 1 => ![3767,143910,648356,4855764]
 | 2 => ![3019,114928,521837,4855764]
 | 3 => ![2687,101858,521837,3052656]
 | 4 => ![422,15662,158698,1993744]
 | 5 => ![280,10171,103959,1285200]
 | 6 => ![225,8016,68569,995828]
 | 7 => ![170,6245, 54168,776610]
 | 8 => ![145, 5264,47174,606347]
 | _ => ![123,4633,40170,512888]
def weight (s :nq) (bw:Fin 3) :Fin 4→ℕ :=
  ![![s.U,s.B-s.J,s.J,0],
    ![0,s.U,0,s.J],
    ![0,0,s.U,s.B]] bw
def dot (weight values :Fin 4→ℕ) :ℕ := ∑ k,weight k*values k
def eol:ℕ:=5980+((p+1)*1052972+19635660)+(p+1)*(1899+8441)
def I0 {u del} (M:jG u del) {Γ} (F:mJ M Γ)
    (I:cy Ambient) (γ:K) :Prop :=
  IZ I (M.label γ) (F.scalar γ)
structure aAT {u del} (M:jG u del) {Γ} (F:mJ M Γ)
  (cheapFixed layeredFixed:tK) where
 parents :aU (cy Ambient)
 geometric : ∀ I∈parents,xN I
 initial_mass :dM parents (budget 0)
 direct :aU K
 direct_card:direct.card≤eol
 cover : ∀ γ∈Γ,γ∈direct∨FW cheapFixed (F.scalar γ)=0 ∨
  FW layeredFixed (F.scalar γ)=0 ∨ ∃ I∈parents,I0 M F I γ
def by6 (I:cy Ambient) :Prop :=
  I.IsPrime∧pG (gk I)=1 ∧
    nI aQ (rM I) ∧
    0<lz aQ (rM I) ∧
    nI aQ (as2 I)
structure acW where
 direct :aU K
 qv :aU (cy Ambient)
 geometric : ∀ I∈qv,by6 I
def bod (C:aU (cy Ambient)) :ℕ :=
 ∑ I∈C,lz aQ (rM I)
def bDF (C:aU (cy Ambient)) :ℕ :=
 ∑ I∈C,lz aQ (as2 I)
def acW.cost (C:acW) (bw:Fin 3) :ℕ :=
 ![bod C.qv,bDF C.qv,C.direct.card] bw
end
end pI
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace pI
noncomputable section
open K1 cu gT Polynomial
open scoped Classical
theorem d2l (z :K) (S:K[X]) (G:tK) :
   aci z S (iJ (Gw G))=FW G S:= by
 rw [aNB]
 change (G.map (ox lV)).eval₂
     (nX (qD z) (kr S)) (kr S.derivative) =
   G.eval₂ (evalRingHom (kr S)) (kr S.derivative)
 rw [eval₂_map]
 have h: (nX (qD z) (kr S)).comp (ox lV) =
     evalRingHom (kr S) := by
   apply pL
   intro f
   change (f.map lV).eval₂ (qD z) (kr S)=f.eval (kr S)
   rw [eval₂_map,← eval₂_id]
   have hc: (qD z).comp lV=RingHom.id FX:= by
     ext c
     simp [qD]
   rw [hc]
 rw [h]
theorem a5I {S T:aU (cy Ambient)} (h:S⊆T) (k :Fin 4) :
  mass S k≤ mass T k :=
 Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _=>Nat.zero_le _)
theorem bOC {α:Type*} (f :α→ℕ) (A B:aU α) :
  (∑ a∈A∪B,f a)≤(∑ a∈A,f a) + ∑ a∈B,f a := by
 have h:=Finset.sum_union_inter (f :=f) (s₁:=A) (s₂:=B)
 omega
theorem bhF {α β:Type*} (A:aU α) (B:α→aU β) (f :β→ℕ) :
   (∑ x∈A.biUnion B,f x) ≤ ∑ i∈A,∑ x∈B i,f x := by
 induction A using Finset.induction_on with
 | empty=>simp
 | @insert i A hi ih =>
   rw [Finset.biUnion_insert,Finset.sum_insert hi]
   exact (bOC f _ _).trans (Nat.add_le_add_left ih _)
def bH7 {α:Type*} (A:aU α) (B:α→acW) :acW where
  direct :=A.biUnion (fun i=>(B i).direct)
  qv :=A.biUnion (fun i=>(B i).qv)
  geometric:= fun I hI=> by
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hI
    exact (B i).geometric I hi
theorem b6V {α:Type*} (A:aU α) (B:α→acW) (bw:Fin 3) :
   (bH7 A B).cost bw ≤ ∑ i∈A,(B i).cost bw:= by
 fin_cases bw
 · exact bhF _ _ _
 · exact bhF _ _ _
 · exact pQ
theorem crE (A:aU (cy Ambient)) (w:Fin 4→ℕ) :
  (∑ I∈A,dot w (pN I))=dot w (mass A) := by
 simp only [dot,mass,Finset.mul_sum]
 exact Finset.sum_comm
def b1w:acW :=
 ⟨∅,∅,by simp⟩
theorem ecA {S T:aU (cy Ambient)} {cap:Fin 4→ℕ} (hs :S⊆T)
  (ht:dM T cap) :dM S cap :=
 fun k=>(a5I hs k).trans (ht k)
end
end pI
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace XY
noncomputable section
open K1 cu qQ Polynomial
open scoped BigOperators
def My (f :oy) :ℕ :=
 f.support.sup fun y=>(f.coeff y).totalDegree
structure ag6 (P Q:Jet) :Prop where
 left_ne :P≠0
 right_ne :Q≠0
 no_common : ∀ D:Jet,oq D→D ∣P → ¬ D ∣Q
def vf (z :K) (S:K[X]) :Jet →+* FX :=
 nX (nX (qD z) (kr S)) (kr S.derivative)
end
end XY
end
section
set_option backward.isDefEq.respectTransparency false
namespace qQ
noncomputable section
open K1 cu Polynomial
open scoped BigOperators Classical
theorem aJr {T:aU K} {label :K→K} (hinj:Set.InjOn label (T:Set K))
    (C:VN) (hdeg:C.curve.totalDegree<p)
    (hcover : ∀ γ∈T,C.ow (label γ)) :
    T.card≤(p+1)*C.curve.totalDegree+C.points.card:= by
  classical
  let zero :=T.filter (fun γ=>qD (label γ) C.curve=0)
  let other :=T.filter (fun γ=>qD (label γ) C.curve≠0)
  have inj:Set.InjOn (fun γ=>jz (label γ)) (T:Set K) :=
    fun _ ha _ hb h=>hinj ha hb (jz.injective h)
  have hzero :zero.card≤(p+1)*C.curve.totalDegree := by
    have hcard: (zero.image (fun γ=>jz (label γ))).card=zero.card :=
      Finset.card_image_iff.mpr (inj.mono (by exact Finset.filter_subset _ _))
    have hb:=bqt p
      C.curve.totalDegree C.curve.totalDegree (by decide) C.curve C.curve_ne
      (C.curve.degreeOf_le_totalDegree 0) hdeg (C.curve.degreeOf_le_totalDegree 1)
      (zero.image (fun γ=>jz (label γ))) (by
        intro x hx
        obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hγ).2)
    simpa only [hcard,Nat.add_mul,Nat.one_mul,Nat.add_comm (C.curve.totalDegree)] using hb
  have hother :other.card≤C.points.card:= by
    apply Finset.card_le_card_of_injOn
      (fun γ=>(jz (label γ),jz (label γ)^p))
    · intro γ hγ
      have hm:=Finset.mem_filter.mp (show γ∈other from hγ)
      exact (hcover γ hm.1).resolve_left hm.2
    · intro x hx y hy h
      exact inj (Finset.mem_filter.mp (show x∈other from hx)).1
        (Finset.mem_filter.mp (show y∈other from hy)).1 (congrArg Prod.fst h)
  rw [← Finset.card_filter_add_card_filter_not (s :=T)
    (p:= fun γ=>qD (label γ) C.curve=0)]
  exact Nat.add_le_add hzero hother
theorem bNe :qm kr :=
 (qx L[X] FX).comp
   (Polynomial.map_injective (lI K L) (lI K L).injective)
def a4N {ι:Type*} (I:aU ι) (C:ι→VN) :VN := by
  classical
  exact ⟨∏ i∈I,(C i).curve,
    Finset.prod_ne_zero_iff.mpr (fun i _=>(C i).curve_ne),
    I.biUnion (fun i=>(C i).points)⟩
theorem bH5 {ι:Type*} (I:aU ι) (C:ι→VN) :
  (a4N I C).curve.totalDegree ≤ ∑ i∈I,(C i).curve.totalDegree :=
 MvPolynomial.totalDegree_finsetProd I _
theorem bH6 {ι:Type*} (I:aU ι) (C:ι→VN) :
  (a4N I C).points.card ≤ ∑ i∈I,(C i).points.card :=
 pQ
theorem bH4 {ι:Type*} {I:aU ι} {C:ι→VN} {i:ι}
   (hi:i∈I) {z :K} (hz : (C i).ow z) :
   (a4N I C).ow z := by
 classical
 rcases hz with h | h
 · left
   change qD z (∏ j∈I,(C j).curve)=0
   rw [map_prod]
   exact Finset.prod_eq_zero hi h
 · exact Or.inr (Finset.mem_biUnion.mpr ⟨i,hi,h⟩)
end
end qQ
end
