import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZUihISc
import ProximityPrize.SubmissionLower.ZfVU1Oc
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Finset.mul_sum → zxw, Finsupp.add_apply → zSs, Ideal → znc, Ideal.mem_sup_left → zKg, Ideal.span → zye, Ideal.span_insert → zf9, Ideal.span_singleton_le_iff_mem → zvl, Ideal.subset_span → zCn, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.X → z9v, MvPolynomial.ringHom_ext → zXT, Nat.pos_of_ne_zero → zOl, RingHom.ker → zdq
section
set_option autoImplicit true
namespace qeu0RUc
noncomputable section
open aR (af)
open oR (separant)
open we (DO eT cH fW)
open yz (oe iz aCt S3 F3 nD aa1)
open P6_6 (bf mW LN)
open P6_6_5 (Fb tC)
open qSCPCwb (BW)
open MvPolynomial
def yD (f :af 3) :Finset (znc (eT 3)) := by
  classical
  exact if Fb f then ∅ else
    (BW f).retainedMinimalPrimes (fW (separant f))
abbrev RY (v :ℕ) :=LN (bf+2) (mW v)
abbrev Wa (v :ℕ) :=aCt (RY v) bf
abbrev afR (v :ℕ) :=monomialMap cH (Wa v)
def i9 (v :ℕ) (f :af 3) (P:znc (eT 3)) :
    znc (MvPolynomial (Wa v) cH) :=
  (F3 f P).comap (afR v)
def aFK (v :ℕ) (f :af 3) (P:znc (eT 3)) :Prop :=
  (i9 v f P).IsPrime∧(affineHilbertPolynomial (i9 v f P)).natDegree=1
def pN (v :ℕ) (f :af 3) (P:znc (eT 3)) :ℚ :=
  affineDegree (i9 v f P)
structure am9 (v :ℕ) (f :af 3) where
  polynomial:eT 4
  support :DO polynomial (RY v) bf
  points :znc (eT 3)→Finset oe
  card_eq : ∀ P∈yD f,((points P).card:ℚ)=pN v f P
  proper : ∀ P∈yD f,polynomial∉F3 f P
  roots : ∀ P∈yD f,∀ y∈points P,
    y∈S3 f P∧eval y polynomial=0
  off_other_curves : ∀ P∈yD f,∀ P' ∈ yD f,P≠P' →
    ∀ y∈points P,y∉S3 f P'
def T7 (v :ℕ) (first:Set iz) :ℝ :=
  aa1 ![first,nD (tC (mW v)) 1,
    nD (LN (bf+1) (mW v)) (bf - 1),
    nD (RY v) bf]
end
end qeu0RUc
end
section
set_option autoImplicit true
namespace qsQcP6a
noncomputable section
open aR (af)
open oR (D3)
open we (eT fW vY graph rP ag9)
open qSCPCwb (Dm BW)
open aA2 (TC ad2 avJ ajV bs6
  aO6 aWc sep S7)
open MvPolynomial
open private bhV b5E bu1 from ProximityPrize.SubmissionLower.BG
def Wy (f :af 3) (E :eT 4) :znc (eT 4) :=
  rP f ⊔ zye {E}
abbrev aeI (f :af 3) :=TC (BW f) (sep f)
abbrev aYQ (f :af 3) (E :eT 4) :=TC (Wy f E) (S7 f)
abbrev Nt (f :af 3) :=ad2 (BW f) (sep f)
abbrev zp (f :af 3) (E :eT 4) :=ad2 (Wy f E) (S7 f)
private def a5Y (f :af 3) :aeI f :=
  -Nt f (fW (D3 f)) *
    ↑(((bhV ((Nt f).comp C)).mul (ajV (BW f) (sep f))).unit⁻¹)
private theorem bsV (f :af 3) :
    Nt f (fW (D3 f))+3*a5Y f*Nt f (sep f)=0:= by
  let a :=Nt f (fW (D3 f))
  let s :=Nt f (sep f)
  let u:=((bhV ((Nt f).comp C)).mul (ajV (BW f) (sep f))).unit
  have hu: (u:aeI f)=3*s :=IsUnit.unit_spec _
  change a+3*(-a*(↑u⁻¹:aeI f))*s=0
  calc
    _=a + -a*((↑u⁻¹:aeI f)*(u:aeI f)) := by rw [hu]; ring
    _=0:= by simp
private def substitute (f :af 3) :eT 4 →+* aeI f :=
  eval₂Hom ((Nt f).comp C) (Fin.snoc (fun i=>Nt f (z9v i)) (a5Y f))
@[simp] private theorem awF (f :af 3) (p:eT 3) :
    substitute f (vY p)=Nt f p:= by
  rw [substitute,vY,eval₂Hom_rename,Fin.snoc_comp_castSucc]
  have h:eval₂Hom ((Nt f).comp C) (fun i:Fin 3=>Nt f (z9v i))=Nt f := by
    apply zXT
    · intro c
      simp
    · intro i
      simp
  rw [h]
private theorem bw2 (f :af 3) :
    substitute f (z9v (Fin.last 3))=a5Y f := by
  rw [substitute,eval₂Hom_X']
  exact Fin.snoc_last _ _
private theorem cqL (f :af 3) :substitute f (graph f)=0:= by
  rw [graph,map_add,map_mul,map_mul,map_ofNat,awF,awF,
    show (3:Fin 4)=Fin.last 3 from rfl,bw2]
  exact bsV f
private theorem cqM (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) :
    Wy f E≤zdq (substitute f) := by
  have hG:rP f≤zdq (substitute f) := by
    rw [rP,zf9,sup_le_iff,zvl,
      zvl,RingHom.mem_ker,RingHom.mem_ker]
    refine ⟨?_,cqL f⟩
    rw [awF]
    exact avJ (zCn (by simp))
  have hs :IsUnit (substitute f (S7 f)) := by
    rw [awF]
    exact ajV _ _
  refine sup_le hG ((zvl _).mpr (RingHom.mem_ker.mpr ?_))
  apply (bu1 hE _ hG hs).mpr
  rw [awF]
  exact avJ (zCn (by simp))
private def aN4 (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) :aYQ f E →+* aeI f :=
  aO6 _ _ (substitute f) (cqM f hE)
    (by rw [awF]; exact ajV _ _)
private theorem bqL (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) (b:eT 4) :
    aN4 f hE (zp f E b)=substitute f b:= by
  rw [aN4,aWc]
private theorem bs5 (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) :
    BW f≤zdq ((zp f E).comp (rename z1o).toRingHom) := by
  have hG:rP f≤zdq (zp f E) := fun u hu =>
    RingHom.mem_ker.mpr (avJ (show u∈Wy f E from zKg hu))
  rw [BW,zf9,sup_le_iff]
  rw [zvl,zvl]
  refine ⟨hG (show vY (fW f)∈rP f from
    zCn (by simp)),RingHom.mem_ker.mpr ?_⟩
  exact (bu1 hE _ hG (ajV _ _)).mp
    (avJ (show E∈Wy f E from
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
private def a6e (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) :aeI f →+* aYQ f E :=
  aO6 _ _ ((zp f E).comp (rename z1o).toRingHom)
    (bs5 f hE) (ajV (Wy f E) (S7 f))
@[simp] private theorem a6f (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) (a :eT 3) :
    a6e f hE (Nt f a)=zp f E (vY a) :=
  aWc _ _ ((zp f E).comp (rename z1o).toRingHom)
    (bs5 f hE) (ajV (Wy f E) (S7 f)) a
def aH6 (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) :aeI f ≃+* aYQ f E := by
  refine RingEquiv.ofRingHom (a6e f hE) (aN4 f hE) ?_ ?_
  · apply bs6
    have hcomp: (aN4 f hE).comp (zp f E)=substitute f :=
      RingHom.ext (bqL f hE)
    rw [RingHom.comp_assoc,RingHom.id_comp,hcomp]
    apply zXT
    · intro c
      simp [substitute,vY]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hG:zp f E (graph f)=0 :=
          avJ (zKg (zCn (by simp)))
        have he :=DFunLike.congr_arg (a6e f hE) (bsV f)
        rw [map_add,map_mul,map_mul,map_ofNat,map_zero,a6f,a6f] at he
        have h:=b5E f (zp f E) (ajV _ _) hG he
        rw [RingHom.comp_apply,bw2]
        exact h.symm
      · simp [substitute,vY]
  · apply bs6
    apply RingHom.ext
    intro a
    simp [bqL]
@[simp] theorem bHy (f :af 3) {E :eT 4}
    (hE :ag9 f (Dm f) E) (a :eT 3) :
    aH6 f hE (Nt f a)=zp f E (vY a) :=
  a6f f hE a
end
end qsQcP6a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qXTnXJe
noncomputable section
open aR (ao)
open B7 Ey Pw
open P6_6 (gZ)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open private c0K from ProximityPrize.SubmissionLower.I
open private cG8 dh5 from ProximityPrize.SubmissionLower.I
open private cMU from ProximityPrize.SubmissionLower.CT
private theorem gxz (Q:znc jo) (L:Fin 2→nW)
    (hQ:Q.IsPrime) (hhom:Q.IsHomogeneous (homogeneousSubmodule rS ao))
    (hdim: (affineHilbertPolynomial Q).natDegree=2)
    (hL:agE L (aVq (oV Q))) (hlow:bjP Q) :
    2*affineDegree Q ≤
      (gZ:ℚ)*(adI L (oV Q) :ℚ) := by
  have h1 :=ap5.of_children cxY.proof
    cxZ.proof cx0.proof
  have h2 :=cx1.proof
  have h3:=cx2.proof
  have h4 :=aFR.of_children cx3.proof cx4.proof
  have h5:=bzv.proof
  have h6:=ban.proof
  obtain ⟨i,hi,hchart,hmonic,hdegree⟩:=c0K Q hQ hhom (by omega)
  have hid :i.val≤gZ :=
    Nat.le_of_lt_succ (lt_of_not_ge (fun h=>hi (hlow i h)))
  let:IsDomain (ChartRing Q i) :=hchart
  obtain ⟨a,ha,⟨s⟩⟩:=h2 (ChartRing Q i) (direction Q i) hmonic ((hdegree.trans hid).trans (by decide))
  obtain ⟨hdom,heval,hfinite,hcoeff⟩:=h1 Q i a hQ hhom hdim hi hchart ha
  let:IsDomain (ap0 Q i a) :=hdom
  let:IsDomain (TC Q i a) :=IsLocalization.Away.isDomain _ ha
  change Factorization (avK Q i a) at s
  obtain ⟨q,hq0,hq,hqspan⟩:=h3 (TC Q i a) (avK Q i a) s
  let e : (TC Q i a)[X] →+* ap0 Q i a :=V5 (TC Q i a)
  let x :=e (avK Q i a)
  let b:=e (auF s)
  let d:Fin 3→ap0 Q i a := fun j=>e (q j)
  have hx :x≠0:= by
    simpa only [e,x,avK,map_zero] using
      heval.ne (hmonic.map (algebraMap _ (TC Q i a))).ne_zero
  have hb:b≠0:= by
    simpa only [e,b,map_zero] using heval.ne (cG8 s).ne_zero
  have hd:d 0≠0:= by
    simpa only [d,hq0,e,map_zero] using heval.ne (dh5 s).ne_zero
  have htrim : ∀ j,b*d j=e (Polynomial.hasseDeriv j.val (avK Q i a)) := by
    intro j
    exact (e.map_mul _ _).symm.trans (congrArg e (hq j))
  have hspan:zye (Set.range d) = ⊤ := by
    have hm:=congrArg (Ideal.map e) hqspan
    rwa [Ideal.map_top,Ideal.map_span,← Set.range_comp] at hm
  let:zAa dF (SH x) :=hfinite
  have hdegree' : (avK Q i a).natDegree≤gZ :=
    Polynomial.natDegree_map_le.trans (hdegree.trans hid)
  have hdiv :=cMU e s hdegree' (by decide)
  have hdeq :d 0=e (aFm s) :=congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin,hlen⟩:=evE x (d 0) gZ hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ:2*(zsE dF (SH x) :ℚ) ≤
      (gZ:ℚ)*(zsE dF (SH (d 0)) :ℚ) := by
    exact_mod_cast hlen
  by_cases hu:IsUnit (d 0)
  · have hzero :zsE dF (SH (d 0))=0:= by
      have :Subsingleton (SH (d 0)) :=
        Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
      exact Module.finrank_zero_of_subsingleton
    exact hlenQ.trans (by rw [hzero,Nat.cast_zero,mul_zero]; positivity)
  · obtain ⟨hk,hcomparison⟩:=h4 Q i a hQ hhom hdim hi hchart ha hdom b d hb htrim
    obtain ⟨hpairfin,hrank⟩:=hcomparison L hL
    have hL' : agE L (adu d) :=hk ▸ hL
    obtain ⟨M,w,hM,hMw,hinj,hw⟩:=h5 _ d L hd hu hspan hL'
    obtain ⟨hwfin,hwRank⟩:=h6 _ d L M hL' hpairfin hM hinj
    rw [hMw] at hwfin hwRank hinj
    let:zAa MY (aPb (biw (d 0) w)) :=hwfin
    let:zAa dF (SH (d 0)) :=hdfin
    have hbound:=eLk (d 0) w hw hinj
    rw [hwRank,hrank] at hbound
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound)
      (Nat.cast_nonneg gZ))
theorem adr (P:znc jo) (g d:nW)
    (hchart:XP P g d) (hlow:bjP P) :
    (affineHilbertPolynomial P).natDegree=2 ∧
      2*affineDegree P≤(gZ:ℚ)*(g.totalDegree :ℚ) := by
  have hdim:=Ey.aTz P g d hchart
  refine ⟨hdim,?_⟩
  have h2 :=axc.of_children cx5.proof cx6.proof
  have h3:=axd.of_children bzw.proof
    cx7.proof cx8.proof
  obtain ⟨n,Q,hQ,hdeg,hfiber⟩:=h2 P hchart.prime hdim
  obtain ⟨L,hL,hfinite,hbudget⟩:=h3 P g d hchart
  have htail:bjP (adN P) := by
    intro i hi
    change z9v i∈zye _
    apply zCn
    refine ⟨z9v i,hlow i hi,?_⟩
    change homogeneousComponent (z9v (R:=ao) i).totalDegree
      (z9v i)=z9v i
    rw [totalDegree_X]
    exact homogeneousComponent_eq_self (isHomogeneous_X ao i)
  have hcurve (i:Fin n) :2*affineDegree (Q i) ≤
      (gZ:ℚ)*(adI L (oV (Q i)) :ℚ) := by
    obtain ⟨hi,hhom,hd⟩:=hQ i
    have hle :aVq (oV (adN P))≤aVq (oV (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact gxz (Q i) L hi.isPrime hhom hd (hL.of_le hle)
      (fun j hj=>hi.le (htail j hj))
  have hsum:=Finset.sum_le_sum (s :=Finset.univ) (fun i _=>hcurve i)
  rw [← zxw,← zxw] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg gZ))
  exact_mod_cast (hfiber L hfinite).trans hbudget
end
end qXTnXJe
end
section
set_option autoImplicit true
namespace qO9urca
noncomputable section
open aR (ao)
open xE (Flag)
open akL (Jp BU Oq azA)
open qnnEPee
open private cV weight from ProximityPrize.SubmissionLower.ZvIWsYa
private def powers {R:Type*} [CommMonoid R] (x :Fin 4→R) (a :Jp) :R :=
  ∏ j,x j^a j
private theorem powers_add {R:Type*} [CommMonoid R] (x :Fin 4→R) (a b:Jp) :
    powers x (a+b)=powers x a*powers x b:= by
  simp only [powers,zSs,pow_add,Finset.prod_mul_distrib]
private theorem powers_single {R:Type*} [CommMonoid R] (x :Fin 4→R) (i:Fin 4) (n:ℕ) :
    powers x (Finsupp.single i n)=x i^n:= by
  unfold powers
  rw [Finset.prod_eq_single i (fun j _ h=> by rw [Finsupp.single_eq_of_ne h,pow_zero])
    (fun h=>(h (Finset.mem_univ i)).elim),Finsupp.single_eq_same]
private theorem byG (a :Jp) (i:Fin 4) (n:ℕ) :
    (a+Finsupp.single i n).weight Oq=a.weight Oq+n*Oq i:= by
  rw [map_add,Finsupp.weight_single,smul_eq_mul]
private def interval {R:Type*} [CommRing R] [Algebra ao R] (y :R) (lo:ℤ) (n:ℕ) :R :=
  ∏ k∈Finset.range n,(y-algebraMap ao R (↑(lo+(k :ℤ)) :ao))
private theorem interval_lead {R:Type*} [CommRing R] [Algebra ao R]
    (L:R →ₗ[ao] ao) (x :Fin 4→R) (i:Fin 4) (hi:0<Oq i)
    (s :Finset (Fin 4)) (hs : ∀ j∈s,Oq j<Oq i)
    (lo:ℤ) (n:ℕ) (a :Jp)
    (h : ∀ b:Jp,b.weight Oq<(a+Finsupp.single i n).weight Oq →
      L (powers x b)=0) :
    L (powers x a*interval (x i + ∑ j∈s,x j) lo n) =
      L (powers x (a+Finsupp.single i n)) := by
  induction n generalizing a with
  | zero=>simp [interval]
  | succ n ih =>
    let g:=interval (x i + ∑ j∈s,x j) lo n
    let c:=algebraMap ao R (↑(lo+(n:ℤ)) :ao)
    have hshift (j:Fin 4) :powers x a*g*x j=powers x (a+Finsupp.single j 1)*g:= by
      rw [powers_add,powers_single,pow_one]
      ac_rfl
    have hsame :a+Finsupp.single i 1+Finsupp.single i n=a+Finsupp.single i (n+1) := by
      rw [add_assoc,← Finsupp.single_add,Nat.add_comm 1 n]
    have htop:=ih (a+Finsupp.single i 1) (fun b hb=>h b (by rwa [hsame] at hb))
    have hlow (j:Fin 4) (hj:j∈s) :L (powers x a*g*x j)=0:= by
      have hlt: (a+Finsupp.single j 1+Finsupp.single i n).weight Oq <
          (a+Finsupp.single i (n+1)).weight Oq:= by
        simp only [byG,Nat.add_mul,one_mul]
        have :=hs j hj
        omega
      rw [hshift,ih _ (fun b hb=>h b (hb.trans hlt))]
      exact h _ hlt
    have hlt: (a+Finsupp.single i n).weight Oq <
        (a+Finsupp.single i (n+1)).weight Oq:= by
      simp only [byG,Nat.add_mul,one_mul]
      omega
    have hc:L (powers x a*g*c)=0:= by
      rw [mul_comm _ c]
      change L (algebraMap ao R _ *(powers x a*g))= _
      rw [← Algebra.smul_def,map_smul,ih a (fun b hb=>h b (hb.trans hlt)),h _ hlt,smul_zero]
    have hg:interval (x i + ∑ j∈s,x j) lo (n+1) =
        g*(x i + ∑ j∈s,x j - c) :=Finset.prod_range_succ _ _
    rw [hg,← mul_assoc,mul_sub,mul_add,zxw,map_sub,map_add,map_sum,hc,sub_zero]
    rw [Finset.sum_eq_zero hlow,add_zero,hshift,htop,hsame]
private theorem interval_zero {ι:Type*} (y :ι→ao) (lo:ℤ) (n:ℕ)
    (h : ∀ e,∃ t:ℤ,lo≤t∧t<lo+(n:ℤ)∧y e=(t:ao)) :
    interval y lo n=0:= by
  funext e
  obtain ⟨t,hl,hu,ht⟩:=h e
  let k :=(t - lo).toNat
  have hk : (k :ℤ)=t - lo:=Int.toNat_of_nonneg (by omega)
  have he :lo+(k :ℤ)=t:= by omega
  simp only [interval,Finset.prod_apply,Pi.sub_apply,Pi.algebraMap_apply,
    Algebra.algebraMap_self_apply,Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr (show k<n by omega)) (by rw [he,ht,sub_self])
private def pointIndex (F:Flag) (i:Fin 4) (e :Tail F) :ℤ :=
  ![1,(coordU e.val :ℤ),(coordV e.val :ℤ),(coordW e.val :ℤ)] i
private def point (F:Flag) (i:Fin 4) (e :Tail F) :ao:=pointIndex F i e
private def axisLo (F:Flag) :Fin 4→ℤ :=
  ![0,(F.order+2)/3,max 0 ((F.order-F.degree+1)/2),
    if F.upper-F.order< min F.cap F.degree then F.order else 0]
private def axisSize (F:Flag) :Fin 4→ℤ := ![0,boxU F,boxV F,boxW F]
private def axisExtra (F:Flag) (i:Fin 4) :Finset (Fin 4) :=
  if i=3∧F.upper-F.order< min F.cap F.degree then {1, 2} else ∅
private theorem axis_lt (F:Flag) (i:Fin 4) : ∀ j∈axisExtra F i,Oq j<Oq i:= by
  intro j hj
  unfold axisExtra at hj
  split at hj
  · rename_i h
    obtain ⟨rfl,_⟩:=h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> decide
  · simp at hj
private theorem axis_root (F:Flag) (i:Fin 4) (hi:i≠0) (e :Tail F) :
    ∃ t:ℤ,axisLo F i≤t∧t<axisLo F i+((axisSize F i).toNat :ℤ) ∧
      (point F i + ∑ j∈axisExtra F i,point F j) e=(t:ao) := by
  let t:=pointIndex F i e + ∑ j∈axisExtra F i,pointIndex F j e
  refine ⟨t,?_,?_,by simp [t,point,Pi.add_apply,Finset.sum_apply,Int.cast_sum]⟩
  all_goals
    obtain ⟨hwv,hvu,hud,hwc,hlo,hhi⟩:=tail_lattice F e
    have h0:0≤(coordW e.val :ℤ) :=Int.natCast_nonneg _
    fin_cases i
    · exact (hi rfl).elim
    · simp [t,pointIndex,axisLo,axisSize,axisExtra,boxU]
      omega
    · simp [t,pointIndex,axisLo,axisSize,axisExtra,boxV]
      omega
    · by_cases h:F.upper-F.order< min F.cap F.degree
      · simp [t,pointIndex,axisLo,axisSize,axisExtra,boxW,h,
          min_eq_right (le_of_lt h),Finset.sum_insert]
        omega
      · simp [t,pointIndex,axisLo,axisSize,axisExtra,boxW,h,
          min_eq_left (le_of_not_gt h)] <;> omega
private def functional (F:Flag) (z :Tail F→ao) : (Tail F→ao) →ₗ[ao] ao :=
  ∑ e,z e•LinearMap.proj e
private theorem powers_point (F:Flag) (a :Jp) (e :Tail F) :
    powers (point F) a e=momentValue a e.val := by
  simp [powers,Fin.prod_univ_four,point,pointIndex,Pi.pow_apply,momentValue]
private theorem functional_apply (F:Flag) (z :Tail F→ao) (s :Finset Jp) (a : ↥s) :
    functional F z (powers (point F) a.val)=momentMap F s z a := by
  simp only [functional,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,
    powers_point,momentMap,Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply]
private theorem in_box (F:Flag) (z :Tail F→ao)
    (hz :momentMap F (reducedColumns F) z=0) (a :Jp)
    (ha : (a.weight Oq:ℤ)≤F.lower - 1)
    (h₁: (a 1 :ℤ)<boxU F) (h₂: (a 2 :ℤ)<boxV F) (h₃: (a 3:ℤ)<boxW F) :
    functional F z (powers (point F) a)=0:= by
  let b:=Finsupp.single (0:Fin 4) ((F.lower - 1).toNat - (a 1+a 2+a 3))+a.erase 0
  have hb0:b 0=(F.lower - 1).toNat - (a 1+a 2+a 3) := by simp [b,zSs]
  have hb (i:Fin 4) (hi:i≠0) :b i=a i:= by
    simp [b,zSs,Finsupp.single_eq_of_ne hi,Finsupp.erase_ne hi]
  have hb1 :=hb 1 (by decide)
  have hb2 :=hb 2 (by decide)
  have hb3:=hb 3 (by decide)
  rw [weight a] at ha
  have hbmem:b∈momentColumns F:= by
    apply azA.mpr
    change (b.weight BU:ℤ)=F.lower - 1∧(b.weight Oq:ℤ)≤F.lower - 1
    rw [cV b,weight b,hb0,hb1,hb2,hb3]
    exact ⟨by omega,ha⟩
  have hm:b∈reducedColumns F :=
    Finset.mem_filter.mpr ⟨hbmem,by simpa only [hb1,hb2,hb3] using And.intro h₁ (And.intro h₂ h₃)⟩
  have hp:powers (point F) a=powers (point F) b:= by
    funext e
    simp only [powers_point,momentValue,hb1,hb2,hb3]
  rw [hp,functional_apply F z _ ⟨b,hm⟩,hz]
  rfl
private theorem outside_box (F:Flag) (z :Tail F→ao) (a :Jp)
    (i:Fin 4) (hi:i≠0) (ha : (axisSize F i).toNat≤a i)
    (h : ∀ b:Jp,b.weight Oq<a.weight Oq →
      functional F z (powers (point F) b)=0) :
    functional F z (powers (point F) a)=0:= by
  let n:=(axisSize F i).toNat
  let b:=a-Finsupp.single i n
  have hpos :0<Oq i:=zOl (fun h=>hi (Fin.ext h))
  have hb:b+Finsupp.single i n=a :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr ha)
  have hz :interval (point F i + ∑ j∈axisExtra F i,point F j) (axisLo F i) n=0 :=
    interval_zero _ _ _ (axis_root F i hi)
  have hr :=interval_lead (functional F z) (point F) i hpos _ (axis_lt F i) (axisLo F i) n b
    (fun c hc=>h c (by rwa [hb] at hc))
  simpa only [hz,mul_zero,map_zero,hb] using hr.symm
theorem proof :qnnEPee.c2 := by
  intro F _ _ z hz
  have hz' := LinearMap.mem_ker.mp hz
  have hall (k :ℕ) (a :Jp) (hk :a.weight Oq=k)
      (ha : (k :ℤ)≤F.lower - 1) :functional F z (powers (point F) a)=0:= by
    induction k using Nat.strong_induction_on generalizing a with
    | h k ih =>
      have hsmall (b:Jp) (hb:b.weight Oq<a.weight Oq) :
          functional F z (powers (point F) b)=0 :=
        ih _ (by omega) b rfl (by omega)
      by_cases h₁: (a 1 :ℤ)<boxU F
      · by_cases h₂: (a 2 :ℤ)<boxV F
        · by_cases h₃: (a 3:ℤ)<boxW F
          · exact in_box F z hz' a (by rwa [hk]) h₁ h₂ h₃
          · exact outside_box F z a 3 (by decide)
              (show (boxW F).toNat≤a 3 by omega) hsmall
        · exact outside_box F z a 2 (by decide)
            (show (boxV F).toNat≤a 2 by omega) hsmall
      · exact outside_box F z a 1 (by decide)
          (show (boxU F).toNat≤a 1 by omega) hsmall
  apply LinearMap.mem_ker.mpr
  funext a
  have ha :=(azA.mp a.property).2
  rw [← functional_apply F z (momentColumns F) a]
  exact hall _ a.val rfl ha
end
end qO9urca
end
section
set_option autoImplicit true
namespace P6_6_7
noncomputable section
open P6_6
open aR (af shape)
def c1 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ assigned:SurfaceAssignment C R G,
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      let b:=commonBody C R ell cs
      (feeScale :ℤ)*DG C R G assigned≤ curve32 p r q b+point32 r q b
def c2 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ assigned:SurfaceAssignment C R G,
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      let b:=commonBody C R ell cs
      let c:=curve32 p r q b
      (3≤ell→(feeScale :ℤ)*((ell:ℤ) - 2)*lowGeneric C R G ell assigned≤ c+point32 r q b) ∧
      (ell<3→(feeScale :ℤ)*lowGeneric C R G ell assigned≤ c)
def c3:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ assigned:SurfaceAssignment C R G,
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      let a :=curve32 p r q p
      (feeScale :ℤ)*ell*highAux C R G ell cs assigned ≤
        a+curve32 p r q (commonBody C R ell cs)+2*(max ell (topBound C R cs) :ℕ)*a
def c4 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ assigned:SurfaceAssignment C R G,∀ dR,
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      (feeScale :ℤ)*ell*highInv C R G ell cs assigned≤taylor32 dR p r q+fresh32 r q
def c5:Prop :=
  ∀ (C:Context) R l ell,JetFactor R→SmallGuard C R l ell →
    (shape R).t=0→0<(shape R).j →
    markedWeight C.Δ C.s R≤ smallFee (remainingChart C.v) (shape R)
def c6:Prop :=
  ∀ (C:Context) R l ell,JetFactor R→SmallGuard C R l ell→0<(shape R).t →
    (feeScale :ℤ)*smallMarks C R false≤ smallCore (remainingChart C.v) (shape R)
def c7:Prop :=
  ∀ (C:Context) R l ell,JetFactor R→SmallGuard C R l ell→0<(shape R).t →
    smallMarks C R true≤(shape R).b*biR (shape R)
private theorem Az {ell e j a i t:ℕ} {c pt u m:ℤ}
    (hadd:t=e+j+a+i)
    (he : (feeScale :ℤ)*e≤ c+pt)
    (hj: (3≤ell→(feeScale :ℤ)*((ell:ℤ) - 2)*j≤ c+pt) ∧
      (ell<3→(feeScale :ℤ)*j≤ c))
    (ha : (feeScale :ℤ)*ell*a≤u)
    (hi: (feeScale :ℤ)*ell*i≤ m) :
    (↑(feeScale*ell*max 1 (ell - 2)) :ℤ)*t ≤
      if 3≤ell then (m+(ell:ℤ)*(c+pt)+u)*((ell:ℤ) - 2)+(ell:ℤ)*(c+pt)
      else m+(ell:ℤ)*(c+pt)+u+(ell:ℤ)*c:= by
  have hE :=mul_le_mul_of_nonneg_left he (show 0≤(ell:ℤ) by positivity)
  have hb: (feeScale :ℤ)*ell*(e+(a :ℤ)+i)≤ m+(ell:ℤ)*(c+pt)+u:= by
    calc
      _=(ell:ℤ)*(feeScale*(e :ℤ))+feeScale*(ell:ℤ)*a +
          feeScale*(ell:ℤ)*i:= by ring
      _≤_:= by linarith only [hE,ha,hi]
  by_cases h:3≤ell
  · have hh:1≤ell - 2 := by omega
    have hh' : (2 :ℤ)≤ell:= by exact_mod_cast (show 2≤ell by omega)
    have hbase :=mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hh')
    have hj' := mul_le_mul_of_nonneg_left (hj.1 h) (show 0≤(ell:ℤ) by positivity)
    rw [ite_eq_left h,max_eq_right hh,hadd]
    push_cast [Nat.cast_sub (show 2≤ell by omega)]
    calc
      _=(feeScale*(ell:ℤ)*(e+(a :ℤ)+i))*((ell:ℤ) - 2) +
          ell*(feeScale*((ell:ℤ) - 2)*j) := by
        simp only [feeScale,Nat.cast_mul,Nat.cast_ofNat]
        ring
      _≤_:=add_le_add hbase hj'
  · have hmax :max 1 (ell - 2)=1 :=max_eq_left (by omega)
    have hj' := mul_le_mul_of_nonneg_left (hj.2 (Nat.lt_of_not_ge h)) (show 0≤(ell:ℤ) by positivity)
    rw [ite_eq_right h,hmax,hadd]
    push_cast
    calc
      _=feeScale*(ell:ℤ)*(e+(a :ℤ)+i)+ell*(feeScale*(j:ℤ)) := by
        simp only [feeScale,Nat.cast_mul,Nat.cast_ofNat]
        ring
      _≤_:=add_le_add hb hj'
private theorem eJB (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    {C:Context} {R G:af 4} {ell:ℕ} {cs :ChartCase C.n} (h:PairInput C R G ell cs)
    (dR:Bool) :
    markedWeight C.Δ C.s R≤pairFee dR (chartBody C R cs) (firstSlot C R cs)
      (cutterBody C ell) (commonBody C R ell cs) ell (topBound C R cs) := by
  obtain ⟨assigned⟩:=assignSurfaces h
  have nY:=Az (dfk C R G ell cs assigned)
    (h1 C R G ell cs h assigned) (h2 C R G ell cs h assigned) (h3 C R G ell cs h assigned) (h4 C R G ell cs h assigned dR)
  rw [pairFee]
  apply fee_of_scaled (show 0<feeScale*ell*max 1 (ell - 2) from
    Nat.mul_pos (Nat.mul_pos (by decide) h.positive) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  refine nY.trans_eq ?_
  simp only [pairNumerator,point32,taylor32,fresh32]
  by_cases h3:3≤ell
  · simp only [ite_eq_left h3]
    ring
  · simp only [ite_eq_right h3]
    ring
private theorem small_bound (h5:c5) (h6:c6) (h7:c7)
    (C:Context) {R:af 4} (hR:JetFactor R) {l ell:ℕ} (hg:SmallGuard C R l ell) :
    markedWeight C.Δ C.s R≤ smallFee (remainingChart C.v) (shape R) := by
  by_cases ht: (shape R).t=0
  · by_cases hj: (shape R).j=0
    · simpa only [smallFee,ite_eq_left ht,ite_eq_left hj] using jU C hR.1 hj
    · exact h5 C R l ell hR hg ht (zOl hj)
  · have hreg:=fee_of_scaled (show 0<feeScale by decide)
      (h6 C R l ell hR hg (Nat.pos_of_ne_zero ht))
    have hz :=h7 C R l ell hR hg (Nat.pos_of_ne_zero ht)
    rw [split_small C R]
    simpa only [smallFee,ite_eq_right ht,smallCore,biR,fresh32] using Nat.add_le_add hreg hz
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) (h7:c7) :
    P6_6.c7:= by
  classical
  intro w Δ s hm n f S v hM hv R hR
  by_cases hn:Δ.Nonempty
  · let C:Context :=⟨w,Δ,s,hm,hn,n,f,S,v,hM,hv⟩
    refine ⟨?_,?_,?_⟩
    · intro l ell dR he hl hb hr hcut
      obtain ⟨G,hp,hbox,hw,ho⟩:=hcut
      exact eJB h1 h2 h3 h4 (C:=C) (cs := .union l)
        ⟨hR,he,⟨hl,hb,hr⟩,hp,hbox,hw,ho⟩ dR
    · intro l ell he hl hr hc hd
      exact small_bound h5 h6 h7 C hR (l:=l) (ell:=ell) ⟨he,hl,hr,hc,hd⟩
    · intro i hi ha ell dR he hb hcut
      obtain ⟨G,hp,hbox,hw,ho⟩:=hcut
      exact eJB h1 h2 h3 h4 (C:=C) (cs := .own i)
        ⟨hR,he,⟨hi,ha,hb⟩,hp,hbox,hw,ho⟩ dR
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    refine ⟨?_,?_,?_⟩ <;> intros <;> simp only [markedWeight,Finset.sum_empty,Nat.zero_le]
end
end P6_6_7
end
