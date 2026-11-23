import ProximityPrize.SubmissionLower.ZzOuVbd
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.Zy3W3oe
import ProximityPrize.SubmissionLower.ZzCHpGc
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZEXyWMe
set_option Elab.async false
open _root_ renaming Finset → zJe, Ideal → znc, Nat.add_le_add_left → z3b, Nat.le_add_left → zmL, Nat.le_add_right → z8K, Nat.mul_le_mul → zcp, Nat.mul_le_mul_right → ztf, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu
section
set_option autoImplicit true
namespace qeu0RUc

open we (eT DO)

open Qp (bF)
open P6_6 (mW LN bf)
open P6_6_5 (tC)
open private gre from ProximityPrize.SubmissionLower.ZZMyKHc
private theorem b6e (v :ℕ) : (mW v).j+3≤(mW v).b :=
  le_max_right _ _
theorem a5D (v :ℕ) :bF (mW v) := by
  have hb:=b6e v
  exact ⟨by omega,by
    change 2*((mW v).j/2)≤(mW v).j
    omega⟩
theorem F4 (v :ℕ) :bF (tC (mW v)) := by
  have hb:=b6e v
  constructor
  · change (mW v).j+1≤(mW v).b
    omega
  · change 2*min ((mW v).t+1) (((mW v).j+1)/2)≤(mW v).j+1
    have h:=min_le_right ((mW v).t+1) (((mW v).j+1)/2)
    omega
theorem bfa (v L:ℕ) (hL:1≤L-4) :bF (LN L (mW v)) := by
  let p:=mW v
  let r :=L-4
  have h:=Nat.mul_le_mul_left r (b6e v)
  change r*(p.j+2+1)≤ r*p.b at h
  rw [Nat.mul_add,Nat.mul_one] at h
  constructor
  · change 2+r*(p.j+2)≤1+r*p.b
    change 1≤ r at hL
    omega
  · change 2*min (1+r*(p.t+2)) ((2+r*(p.j+2))/2)≤2+r*(p.j+2)
    have ht:=min_le_right (1+r*(p.t+2)) ((2+r*(p.j+2))/2)
    omega
theorem aIn (v :ℕ) (i:Fin 4) :
    Finsupp.single i 1∈Wa v := by
  let p:=mW v
  let r :=bf+2 - 4
  have ht:1≤ min (1+r*(p.t+2)) ((2+r*(p.j+2))/2) :=
    le_min (z8K _ _) (by omega)
  exact gre (RY v) bf
    (z8K 1 _) (z8K 2 _) ht (by decide) i
theorem b0q (v :ℕ) {D:eT 4}
    (hD : let p := mW v
          let r :=bf-4
          DO D ⟨r*p.b,r*p.j,r*p.t⟩ 0) :
    DO D (RY v) bf := by
  let p:=mW v
  let r :=bf-4
  let s :=bf+2 - 4
  have hrs :r≤ s :=zIu (z8K _ _) _
  have hB:=ztf p.b hrs
  have hJ:=zcp hrs (z8K p.j 2)
  have hT:=zcp hrs (z8K p.t 2)
  have h2T:2*(r*p.t)≤ s*(p.j+2) := by
    rw [mul_left_comm]
    exact zcp hrs ((a5D v).2.trans (z8K p.j 2))
  intro a ha
  obtain ⟨hb,hj,ht,hh⟩:=hD a ha
  refine ⟨hb.trans (hB.trans (zmL _ _)),hj.trans (hJ.trans (zmL _ _)),?_,
    hh.trans (Nat.zero_le _)⟩
  change a 2≤ min (1+s*(p.t+2)) ((2+s*(p.j+2))/2)
  have hindex :r*p.t≤(2+s*(p.j+2))/2 := by
    apply (Nat.le_div_iff_mul_le (by decide :0<2)).mpr
    rw [Nat.mul_comm _ 2]
    exact h2T.trans (zmL _ _)
  exact ht.trans (le_min (hT.trans (zmL _ _)) hindex)
theorem dMX (v :ℕ) {N :eT 4}
    (hN :DO N (LN bf (mW v)) (bf - 2)) :
    DO N (RY v) bf := by
  let p:=mW v
  have h:bf-4≤bf+2 - 4 :=
    zIu (z8K _ _) _
  have hB:=z3b (ztf p.b h) 1
  have hJ:=z3b (ztf (p.j+2) h) 2
  have hT:=min_le_min (z3b (ztf (p.t+2) h) 1)
    (Nat.div_le_div_right (c:=2) hJ)
  intro a ha
  obtain ⟨hb,hj,ht,hh⟩:=hN a ha
  exact ⟨hb.trans hB,hj.trans hJ,ht.trans hT,hh.trans (Nat.sub_le _ _)⟩
end qeu0RUc
end
section
set_option autoImplicit true
namespace q90NBie
noncomputable section
open Polynomial P6_6 P6_6_7
open P6 (K)
open aR (af Shape shape aO extend wU)
open dN (GeoJets bC AX Ch)
open BO (pN)
variable {C:Context} {R G:af 4} {ell:ℕ}
def lowMarks (C:Context) (R G:af 4) (ell:ℕ) (A:SurfaceAssignment C R G) :zJe K :=
  C.Δ.filter fun γ=>0<ord C R γ∧genericOrder G (A.aI γ)<ell
def uG (A:SurfaceAssignment C R G) (ell:ℕ) :zJe (znc GeoJets) := by
  classical exact (lowMarks C R G ell A).image A.aI
def surfaceMarks (A:SurfaceAssignment C R G) (ell:ℕ) (z :znc GeoJets) :zJe K:= by
  classical exact (lowMarks C R G ell A).filter fun γ=>A.aI γ=z
structure Cuts (A:SurfaceAssignment C R G) (ell:ℕ) where
  first:znc GeoJets→af 4
  curve :K→ znc GeoJets
  proper : ∀ z∈uG A ell,bC (first z)∉z
  fits : ∀ z∈uG A ell,aO (shape (first z)) (cutterBody C ell)
  order : ∀ γ∈lowMarks C R G ell A,
    wU (first (A.aI γ)) (extend (C.s γ)) (ell - genericOrder G (A.aI γ))
  valid : ∀ γ∈lowMarks C R G ell A,
    (AX (A.aI γ) (first (A.aI γ))).IsMinimalPrime (curve γ) ∧
      curve γ≤Ch (extend (C.s γ))
def qv {A:SurfaceAssignment C R G} (F:Cuts A ell) (z :znc GeoJets) :zJe (znc GeoJets) := by
  classical exact (surfaceMarks A ell z).image F.curve
def aHl {A:SurfaceAssignment C R G} (F:Cuts A ell) (z D:znc GeoJets) :zJe K:= by
  classical exact (surfaceMarks A ell z).filter fun γ=>F.curve γ=D
abbrev curveOrder {A:SurfaceAssignment C R G} (F:Cuts A ell) (z D:znc GeoJets) :=
  genericOrder (F.first z) D
abbrev remainingOrder {A:SurfaceAssignment C R G} (F:Cuts A ell) (z D:znc GeoJets) :=
  ell - genericOrder G z - curveOrder F z D
def SecondCuts {A:SurfaceAssignment C R G} (F:Cuts A ell) :Prop :=
  ∀ z∈uG A ell,∀ D∈qv F z,0< remainingOrder F z D →
    ∃ V:af 4,bC V∉D ∧aO (shape V) (cutterBody C ell) ∧
      ∀ γ∈aHl F z D,wU V (extend (C.s γ)) (remainingOrder F z D)
def mass {A:SurfaceAssignment C R G} (F:Cuts A ell) (cost:znc GeoJets→ znc GeoJets→ℕ) :ℕ :=
  ∑ z∈uG A ell,∑ D∈qv F z,
    (genericOrder R z*genericOrder G z*curveOrder F z D)*cost z D
abbrev sectionCost (h:Shape) (D:znc GeoJets) :=pN D (h.scale 6)
end
end q90NBie
end
section
set_option autoImplicit true
namespace P6_6_7_3
noncomputable section
open P6_6 P6_6_7
open aR (af Shape shape aO)
open dN (GeoJets bC AX)
open BO (pN)
open scoped BigOperators
def GW (C:Context) (cs :ChartCase C.n) :af 4 :=
  factorProd C.f (chartIndices C cs)
def curveCharge (p:Shape) (D:znc GeoJets) :ℕ :=
  P6.t*pN D ((weightedChart bf p).scale 6) +
    2*mV*pN D (p.scale 6)
def an0 (h:Shape) (z :znc GeoJets) (F:af 4) :ℕ :=
  ∑ D∈(AX z F).minimalPrimesFinset,pN D (h.scale 6)
def PaidCut (p b:Shape) (ell cap i v :ℕ) (z :znc GeoJets) (F:af 4) :Prop :=
  bC F∉z ∧
    (aO (shape F) p ∨ ∃ a,0<a∧ell*i*a≤ max ell cap*v ∧
      aO (shape F) (b.plus (p.scale (2*a))))
end
end P6_6_7_3
end
section
set_option autoImplicit true
namespace qAzl5me
noncomputable section
open Polynomial
open P6 (K)
open P6_6 (bf weightedChart)
open P6_6_7
open aR (ao af Shape extend cK)
open dN (YR Invariant separant bC su AX oA Ch kC)
open agL (BV EY)
open rW (kT n8 aYK Gp dimension lA)
abbrev chartRow (C:Context) (i:Fin C.n) (a :ℕ) :af 4 :=(separant^[a]) (C.f i)
def memberTest (g:af 4) :af 4 :=su g bf
def ZV (g:af 4) :af 4 :=su g (bf+1)
structure Selected (C:Context) (cs :ChartCase C.n) (aI:n8) (γ:K)
    (i:Fin C.n) (a :ℕ) :Prop where
  index_mem:i∈chartIndices C cs
  contains :bC (C.f i)∈aI
  least : ∀ j∈chartIndices C cs,bC (C.f j)∈aI→i≤j
  canonical:YR (C.f i) aI a
  regular :cK (separant (chartRow C i a)) (extend (C.s γ))≠0
  invariant:Invariant (chartRow C i a) aI
structure MemberCurve (g:af 4) (aI P:n8) :Prop where
  proper :bC (memberTest g)∉aI
  minimal: (AX aI (memberTest g)).IsMinimalPrime P
def MemberCurve.simple {g:af 4} {aI P:n8} (h:MemberCurve g aI P) :Prop :=
  oA (AX aI (memberTest g)) P h.minimal.isPrime=1
def TerminalAt (g:af 4) (aI:n8) (U:ao[X]) :Prop :=
  ∃ P,∃ h:MemberCurve g aI P,P≤Ch U∧(¬ h.simple∨bC (ZV g)∉P)
def ContinueAt (g:af 4) (aI:n8) (U:ao[X]) :Prop :=
  bC (memberTest g)∈aI ∨
    ∃ P,∃ h:MemberCurve g aI P,P≤Ch U∧h.simple∧bC (ZV g)∈P
def active (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n)
    (A:SurfaceAssignment C R G) :zJe K:= by
  classical
  exact C.Δ.filter fun γ=>0<ord C R γ∧ell≤genericOrder G (A.aI γ) ∧
    RegularInvariant C cs (A.aI γ) γ
def TerminalMark (C:Context) (cs :ChartCase C.n) (aI:n8) (γ:K) :Prop :=
  ∃ i a,Selected C cs aI γ i a∧TerminalAt (chartRow C i a) aI (extend (C.s γ))
def terminalMarks (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n)
    (A:SurfaceAssignment C R G) :zJe K:= by
  classical
  exact (active C R G ell cs A).filter fun γ=>TerminalMark C cs (A.aI γ) γ
def Family (C:Context) (i:Fin C.n) (γ:K) (A:kT) :Prop :=
  aYK (C.f i) A ∧
    (∀ j:Fin aR.bf,bf≤j.val→MvPolynomial.X j∈A) ∧
    Gp (extend (C.s γ))∈MvPolynomial.zeroLocus ao A
def CurveWitness (C:Context) (cs :ChartCase C.n) (aI:n8) (γ:K) :Prop :=
  ∃ i a A,Selected C cs aI γ i a∧Family C i γ A∧dimension A=1 ∧
    ∃ h:MemberCurve (chartRow C i a) aI (lA A),
      lA A≤Ch (extend (C.s γ))∧h.simple ∧
        bC (ZV (chartRow C i a))∈lA A
def SurfaceWitness (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n)
    (aI:n8) (γ:K) :Prop :=
  ∃ i a A,Selected C cs aI γ i a∧Family C i γ A∧dimension A=2 ∧
    (kC R G).IsMinimalPrime (lA A) ∧
    (∀ u,EY u<genericOrder R aI→bC (BV u R)∈lA A) ∧
    (∀ u,EY u<ell→bC (BV u G)∈lA A)
def aid (C:Context) (R G:af 4) (ell:ℕ) (A:SurfaceAssignment C R G)
    (T:zJe K) :ℤ :=
  (feeScale :ℤ)*ell * ∑ γ∈T,(genericOrder R (A.aI γ) :ℤ)
abbrev memberDegree (p r q:Shape) :ℤ :=
  (r.b:ℤ)*q.b*(weightedChart (bf+1) p).b
def terminalCap (dR:Bool) (p r q:Shape) :ℤ :=
  (P6_6.mV:ℤ)*P6_6.pair32 dR p r q+32*(P6_6.mV:ℤ)*memberDegree p r q
def curveCap (p r q:Shape) :ℤ :=
  32*((P6.t:ℤ)+P6_6.mV)*memberDegree p r q
end
end qAzl5me
end
section
set_option autoImplicit true
namespace q6t08kb
noncomputable section
open Polynomial P6_6 P6_6_7
open aR (af ao Shape shape extend cK jet)
open Ex (X7)
open oR (Wc separant)
open aF0 (power BJ YM)
open scoped BigOperators
abbrev lowerBody (r :Shape) :Shape :=⟨max r.b (r.j+3),r.j,r.j/2⟩
theorem d1C:P6.t=82317:= by decide
theorem ee8:mV=46402 := by decide
def projectionTotal (a :Shape) :ℕ:=max a.b ((2*a.t - 1)*a.b-a.t^2)
def projectionIndex (a :Shape) :ℕ:=max a.j ((2*a.t - 1)*a.j - 2*a.t^2)
def firstMixed (b j:ℕ) :ℕ :=
  let a :=BJ gZ b
  let d:=YM gZ b j
  b*d+j*(a - d)
theorem firstMixed_eq (b j:ℕ) :firstMixed b j =
  let e :=2*bf - 5
  let a :=1+e*(b - 1)
  let d:=min a (e*(j - 1)+bf - 1)
  b*d+j*(a - d) := by
  dsimp only [firstMixed,YM,BJ]
  rw [show 2*bf - 5=power gZ by decide]
  rw [Nat.add_sub_assoc (by decide :1≤bf)]
  rfl
def lowerMixed (a :Shape) :ℕ :=
  let x :=LN (bf+1) a
  let y :=LN (bf+2) a
  let g:Shape :=⟨a.b,a.j+1,min (a.t+1) ((a.j+1)/2)⟩
  Wc a x y+(bf - 1)*Wc a g y+bf*Wc a g x
def freshBudget (a :Shape) :ℕ:=a.b*(1+(2*bf - 5)*(a.b - 1))
def HigherIndex (C:Context) (R:af 4) (l ell:ℕ) :Prop :=
  JetFactor R∧SmallGuard C R l ell∧(shape R).t=0∧2≤(shape R).j
def roots (C:Context) (R:af 4) :zJe P6.K:=C.Δ.filter fun γ=>0<ord C R γ
def regular (C:Context) (R:af 4) :zJe P6.K:= by
  classical
  exact (roots C R).filter fun γ=>cK (separant (X7 R)) (extend (C.s γ))≠0
def singular (C:Context) (R:af 4) :zJe P6.K:= by
  classical
  exact (roots C R).filter fun γ=>cK (separant (X7 R)) (extend (C.s γ))=0
def acA (R:af 4) :Prop :=
  X7 R∣oR.AR (X7 R) (bf-3)
def aP6 (R:af 4) (S:ao[X]) :ao[X][X] :=
  (aeA.view (X7 R)).map (MvPolynomial.eval (jet S))
def zeroFibers (C:Context) (R:af 4) :zJe P6.K:= by
  classical
  exact C.Δ.filter fun γ=>aP6 R (extend (C.s γ))=0
def nonzeroFibers (C:Context) (R:af 4) :zJe P6.K:= by
  classical
  exact C.Δ.filter fun γ=>aP6 R (extend (C.s γ))≠0
def excessWeight (C:Context) (R:af 4) (T:zJe P6.K) :ℕ :=
  ∑ γ∈T,(ord C R γ - 1)
end
end q6t08kb
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q3u9Tnc
noncomputable section
open Polynomial Finset q20JTGa
open P6 (K)
open P5_7_2 (A)
open P5_7_7 (mL ic mem_sites index_card)
open scoped Classical
open private output output_degree output_dvd quotient_degree hit_width reduced_word word_determinant det_ne from ProximityPrize.SubmissionLower.ZzCHpGc
private theorem gMz {a d₀ d₁ n:ℕ} (h₀:a≤d₀) (h₁:a≤d₁)
    (h:d₀+d₁=n) : (d₀-a)+(d₁-a)=n-2*a := by omega
private theorem pack (J:Input) {U:zJe K} (B:WordRows J.D J.model.word)
    {u₀ u₁:ℕ} (ho:u₀≤u₁) (hw:u₀+u₁=qe6nVeb.width J.D)
    (e₀:A+u₀=B.d₀) (e₁:A+u₁=B.d₁) (P Q:K→cu.L[X])
    (hQne : ∀ γ∈U,Q γ≠0)
    (hP : ∀ γ,mL (sites J γ)*P γ=output B.s (J.family.scalar γ))
    (hQ : ∀ γ,mL (sites J γ)*Q γ=output B.r (J.family.scalar γ))
    (degree : ∀ γ∈U,let a :=(sites J γ).card
      a≤B.d₀∧(Q γ).natDegree≤B.d₀-a∧(P γ).natDegree≤B.d₁-a) :
    Nonempty (DualWord J U) := by
  have hred γ:=reduced_word B (hP γ) (hQ γ)
  refine ⟨{
    a₀:=B.r.a,a₁:=B.s.a,b₀:=B.r.b,b₁:=B.s.b
    u₀:=u₀,u₁:=u₁
    order :=ho
    gMz :=hw
    row₀:=Eq.mpr (congrArg (ic J.D B.r.a B.r.b) e₀) B.bound₀
    row₁:=Eq.mpr (congrArg (ic J.D B.s.a B.s.b) e₁) B.bound₁
    determinant:=word_determinant B
    rows_hit := fun i=>⟨B.r.Ju i,B.s.Ju i⟩
    target :=wordRows_target B
    P:=P,Q:= Q
    denominator :=hQne
    coprime := fun γ _=>(hred γ).1
    numerator_id := fun γ _=>hP γ
    denominator_id := fun γ _=>hQ γ
    degrees := fun γ hγ=> by rw [e₀,e₁]; exact degree γ hγ
    dual_hits := fun γ _=>(hred γ).2 }⟩
private theorem bY (J:Input) {U:zJe K} (hU:U⊆J.CF)
    (B:WordRows J.D J.model.word) (hpos :U.Nonempty)
    (hn : ∀ γ∈U,output B.r (J.family.scalar γ)≠0) :
    Nonempty (DualWord J U) := by
  let S:=J.family.scalar
  choose P hP using fun γ:K=>output_dvd B.s S γ
  choose Q hQ using fun γ:K=>output_dvd B.r S γ
  have hP' γ:=(hP γ).symm
  have hQ' γ:=(hQ γ).symm
  have hdeg₀ γ (hγ:γ∈U) :=output_degree B.r B.bound₀ (J.degree γ (hU hγ))
  have hdeg₁ γ (hγ:γ∈U) :=output_degree B.s B.bound₁ (J.degree γ (hU hγ))
  have hwidth γ (hγ:γ∈U) :=hit_width (hQ' γ) (hdeg₀ γ hγ) (hn γ hγ)
  have hA:A≤B.d₀:= by
    obtain ⟨γ,hγ⟩:=hpos
    let m:=J.family.mark γ (hU hγ)
    exact m.bad.dw.trans ((card_le_card fun i hi =>
      mem_sites.mpr (m.scalar_hits i hi)).trans (hwidth γ hγ))
  have hA' := hA.trans B.order
  exact pack J B (zIu B.order A)
    (gMz hA hA' (B.width.trans (congrArg (· + J.D) index_card)))
    ((Nat.add_comm A _).trans (zxt hA))
    ((Nat.add_comm A _).trans (zxt hA')) P Q
    (fun γ hγ hz=>hn γ hγ (by rw [← hQ' γ,hz,mul_zero])) hP' hQ'
    (fun γ hγ=>⟨hwidth γ hγ,quotient_degree (hQ' γ) (hdeg₀ γ hγ),
      quotient_degree (hP' γ) (hdeg₁ γ hγ)⟩)
private theorem aWY (J:Input) (T:zJe K) (hT:T⊆J.CF)
    (hsmall : ¬ T.card≤1) (B:WordRows J.D J.model.word) :
    ∃ U⊆T,(T \ U).card≤1∧U.Nonempty ∧
      ∀ γ∈U,output B.r (J.family.scalar γ)≠0:= by
  let U:=T.filter fun γ=>output B.r (J.family.scalar γ)≠0
  have hU:U⊆T:=filter_subset _ _
  have hn : ∀ γ∈U,output B.r (J.family.scalar γ)≠0:= fun _ hγ=>(mem_filter.mp hγ).2
  have hbad: (T \ U).card≤1 := by
    apply card_le_one.mpr
    intro α hα β hβ
    obtain ⟨hαT,hαU⟩:=mem_sdiff.mp hα
    obtain ⟨hβT,hβU⟩:=mem_sdiff.mp hβ
    have ha :output B.r (J.family.scalar α)=0:= by
      by_contra hh
      exact hαU (mem_filter.mpr ⟨hαT,hh⟩)
    have hb:output B.r (J.family.scalar β)=0:= by
      by_contra hh
      exact hβU (mem_filter.mpr ⟨hβT,hh⟩)
    have hra :B.r.a≠0:= by
      intro hz
      have hrb:B.r.b=0:= by simpa only [output,hz,zero_mul,zero_add] using ha
      exact det_ne B (by simp only [det,hz,hrb,zero_mul,mul_zero,sub_self])
    have he :=ha.trans hb.symm
    unfold output at he
    apply J.family.distinct (hT hαT) (hT hβT)
    exact Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective K cu.L)
      (mul_left_cancel₀ hra (add_right_cancel he))
  have hpos :U.Nonempty := by
    have hsum:=card_sdiff_add_card_eq_card hU
    apply card_pos.mp
    omega
  exact ⟨U,hU,hbad,hpos,hn⟩
theorem dual_word (J:Input) (T:zJe K) (hT:T⊆J.CF) :
    T.card≤1 ∨ ∃ U⊆T,(T \ U).card≤1∧Nonempty (DualWord J U) := by
  by_cases hsmall:T.card≤1
  · exact Or.inl hsmall
  obtain ⟨B⟩:=wordRows J.D J.model.word
  obtain ⟨U,hU,hbad,hpos,hn⟩:=aWY J T hT hsmall B
  exact Or.inr ⟨U,hU,hbad,bY J (hU.trans hT) B hpos hn⟩
end
end q3u9Tnc
end
section
set_option autoImplicit true
namespace P6_7_5
noncomputable section
open P6 (K)
open P5_7 (midAgreement)
open P5_7_3 (fO Jr bbk Pairs agA terminal prefixFee)

open cu (vP rD)
open qQ (zI N5)
structure Source (b:fO) {cap u del} (M:P1.FJ cap u del) {Γ}
    (F:P1.bje midAgreement M Γ) (rows :vP) :Prop where
  nested : ∀ t,Jr b t → ∀ t',Jr b t' →
    t.shape.m=t'.shape.m→t.shape.B=t'.shape.B→t.shape.J=t'.shape.J →
    t.shape.U≤t'.shape.U → ∀ W W',W≤W' → rows t.shape W≤ rows t'.shape W'
  necessary : ∀ t,Jr b t → ∀ W<t.shape.m*midAgreement,∀ P∈rows t.shape W,
    ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0
  shape : ∀ t,Jr b t → ∀ W,∀ P∈rows t.shape W,qQ.oU P t.shape
  leading : ∀ t,Jr b t→qQ.aSa M.iF.toNat rows t.shape
  shift : ∀ t,Jr b t→qQ.bk4 M.iF.toNat rows t.shape
  ajB : ∀ t,Jr b t→bbk M.iF.toNat t rows
structure bkU (b:fO) {cap u del} (M:P1.FJ cap u del) {Γ}
    (F:P1.bje midAgreement M Γ) {rows :vP} (_:Pairs b M.iF.toNat rows) where
  book :zJe K
  book_bound:book.card≤prefixFee b
  parents :zJe zI
  geometric : ∀ q∈parents,N5 q
  terminal_pass : ∀ q∈parents,agA rows (terminal b).shape q
  Eh : ∀ γ∈Γ,γ∈book ∨ ∃ q∈parents,P6_7.axy M F q γ
end
end P6_7_5
end
