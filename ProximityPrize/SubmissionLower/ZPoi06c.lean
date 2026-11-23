import ProximityPrize.SubmissionLower.ZxBy9Fe
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace qX7bYgd
noncomputable section
open Polynomial
open P6_7 (Source)
open P6_7_7 (I0 aS3)
open P5_7 (Jr farAgreement)
open P5_7_5 (afa arS nV aU2 a5S aqE Process Fo nextIndex agA axS a3D aHp kG)

open cu (Shape vP Jet rD jz)
open gT (Ambient aci iJ aNB gk)
open pI (xN oU acW pN weight dot bH7 b6V
  crE b1w mass)
open ac3
open private d1m from ProximityPrize.SubmissionLower.ZDyoNob
open private cpa from ProximityPrize.SubmissionLower.U
open scoped BigOperators Classical
private theorem b2N {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) {t:P5_7.Bank} (ht:Jr b t)
    (hpos :0<t.shape.m*farAgreement) {I:Ideal Ambient} (hf : ¬ agA rows t.shape I) :
    ∃ P:Jet,oU P t.shape∧iJ P∉I ∧
      ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0:= by
  classical
  unfold agA at hf
  push Not at hf
  obtain ⟨P,hP,hprop⟩:=hf
  exact ⟨P,src.shape t ht _ P hP,hprop,aS3 src ht hpos le_rfl hP⟩
private theorem d59 {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (sched:aqE b)
    (pairs :P5_7.Pairs b M.iF.toNat rows) (i:afa b) {I:Ideal Ambient}
    (hf : ¬ axS (arS pairs i) I) :
    ∃ P:Jet,oU P (a3D (nV b i))∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
  classical
  let s :=nV b i
  let pair :=arS pairs i
  obtain ⟨ga,gc⟩:=sched.aE7 i i.isLt
  have liftCaps {P:Jet} (h:oU P s.free.shape∨oU P s.moving.shape) :
      oU P (a3D s) :=d1m ga.ode.jb gc.ode.jb h
  by_cases hP:agA rows s.free.shape I
  · by_cases hQ:agA rows s.moving.shape I
    · have htest : ¬ aFX.aTw pair.free pair.moving I :=
        fun h=>hf ⟨hP,hQ,h⟩
      unfold aFX.aTw at htest
      push Not at htest
      obtain ⟨f,_,_,_,hdiv,hmem,g,a,hclear,hproper⟩:=htest
      have hcaps :=src.shape _ (a5S i) _ _ pair.moving_mem
      have hG:=YZ.bWO pair.moving_ne hcaps gc.ode.jpos hdiv hclear
      refine ⟨YZ.alD g,liftCaps (Or.inr hG),hproper,?_⟩
      intro γ _ hγ
      apply YZ.bWP hclear
      have hz :=RingHom.mem_ker.mp (hγ hmem)
      simpa only [aNB,rD,eval₂_C,coe_eval₂RingHom,cu.yq] using hz
    · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N src (a5S i) gc.pos hQ
      exact ⟨P,liftCaps (Or.inr hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
  · obtain ⟨P,hcaps,hproper,hzero⟩:=b2N src (aU2 i) ga.pos hP
    exact ⟨P,liftCaps (Or.inl hcaps),hproper,fun γ hγ _=>hzero γ hγ⟩
private theorem bKS {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    (s :Shape) {I:Ideal Ambient} {P:Jet} (hs :s.J≤ s.B) (hI:xN I)
    (hcaps :oU P s) (hprop:iJ P∉I) :
    ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (pN I)) ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0 →
        γ∈C.direct ∨ ∃ Q∈C.qv,I0 F Q γ:= by
  let Ia (Q:Ideal Ambient) :=Γ.filter (I0 F Q)
  let direct :=(a2T I P).biUnion Ia
  have hcard:direct.card≤(a2T I P).card:= by
    have hsingle (Q:Ideal Ambient) (hQ:Q∈a2T I P) :
        (Ia Q).card≤1 := by
      obtain ⟨hcomp,hconst⟩:=Finset.mem_filter.mp hQ
      let _:Q.IsPrime :=(bZk hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply jz.injective
      apply (algebraMap cu.FX (gk Q)).injective
      exact (cpa hconst (Finset.mem_filter.mp hγ).2).trans
        (cpa hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈a2T I P,(Ia Q).card:=Finset.card_biUnion_le
      _ ≤ ∑ _∈a2T I P,1 :=Finset.sum_le_sum hsingle
      _ = _:= by simp
  let C:acW :=
    ⟨direct,aOS I P,by
      intro Q hQ
      obtain ⟨hcomp,hmov⟩:=Finset.mem_filter.mp hQ
      obtain ⟨hp,hdim⟩:=bZk hI hprop hcomp
      exact ⟨hp,hdim,cy6.proof Q hp hdim hmov⟩⟩
  refine ⟨C,?_,?_⟩
  · intro bw
    fin_cases bw
    · exact ac6.Bridge.dS4 s I P hs hI hcaps hprop
    · exact ac6.Bridge.dSZ s I P hs hI hcaps hprop
    · exact hcard.trans (ac6.Bridge.dSJ s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    let e :=aci (M.label γ) (F.scalar γ)
    change I≤RingHom.ker e at hmark
    have hz :iJ P∈RingHom.ker e :=
      RingHom.mem_ker.mpr ((aNB (M.label γ) (F.scalar γ) P).trans hzero)
    have hle :I ⊔ Ideal.span {iJ P} ≤ RingHom.ker e :=
      sup_le hmark ((Ideal.span_singleton_le_iff_mem _).mpr hz)
    have : (RingHom.ker e).IsPrime :=RingHom.ker_isPrime e
    obtain ⟨Q,hmin,hQmark⟩:=Ideal.exists_minimalPrimes_le hle
    have hQ:Q∈aT1 I P:=Ideal.mem_minimalPrimesFinset.mpr hmin
    by_cases ht:aYy Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q,Finset.mem_filter.mpr ⟨hQ,ht⟩,Finset.mem_filter.mpr ⟨hγ,hQmark⟩⟩)
    · exact Or.inr ⟨Q,Finset.mem_filter.mpr ⟨hQ,ht⟩,hQmark⟩
private theorem dN1 {h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    (A:Finset (Ideal Ambient)) (s :Shape) (hs :s.J≤ s.B)
    (ha : ∀ I∈A,xN I)
    (hcut : ∀ I∈A,∃ P:Jet,oU P s∧iJ P∉I ∧
      ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0) :
    ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (mass A)) ∧
      ∀ γ∈Γ,(∃ I∈A,I0 F I γ)→γ∈C.direct ∨ ∃ I∈C.qv,I0 F I γ:= by
  have hex (I:Ideal Ambient) (hI:I∈A) :
      ∃ C:acW,(∀ bw,C.cost bw≤dot (weight s bw) (pN I)) ∧
        ∀ γ∈Γ,I0 F I γ→γ∈C.direct ∨ ∃ Q∈C.qv,I0 F Q γ:= by
    obtain ⟨P,hp,hprop,hzero⟩:=hcut I hI
    obtain ⟨C,hc,hmarks⟩:=bKS F s hs (ha I hI) hp hprop
    exact ⟨C,hc,fun γ hγ hm=>hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I:Ideal Ambient) :acW :=
    if hI:I∈A then Classical.choose (hex I hI) else b1w
  have hC (I:Ideal Ambient) (hI:I∈A) :
      (∀ bw,(C I).cost bw≤dot (weight s bw) (pN I)) ∧
      ∀ γ∈Γ,I0 F I γ→γ∈(C I).direct ∨ ∃ Q∈(C I).qv,I0 F Q γ:= by
    simpa only [C,dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨bH7 A C,?_,?_⟩
  · intro bw
    calc
      _ ≤ ∑ I∈A,(C I).cost bw:=b6V A C bw
      _ ≤ ∑ I∈A,dot (weight s bw) (pN I) :=
        Finset.sum_le_sum (fun I hI=>(hC I hI).1 bw)
      _ = _:=crE _ _
  · rintro γ hγ ⟨I,hI,hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q,hQ,hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I,hI,hd⟩)
    · exact Or.inr ⟨Q,Finset.mem_biUnion.mpr ⟨I,hI,hQ⟩,hmark⟩
theorem proof :P6_7_7.c2 := by
  intro b u del M Γ F rows src pairs R i
  have geom (I:Ideal Ambient) (hI:I∈R.Hj i) :=
    (R.DN I (R.bxI i (R.a4R i (R.cYQ i hI)))).1
  have hj: (aHp b i).J≤(aHp b i).B:= by
    by_cases hi:i<Fo b
    · rw [aHp,ite_eq_left hi]
      exact Nat.le_add_left _ _
    · rw [aHp,ite_eq_right hi]
      exact R.sched.bxE.ode.jb
  have an1 (I:Ideal Ambient) (hI:I∈R.Hj i) :
      ∃ P:Jet,oU P (aHp b i)∧iJ P∉I ∧
        ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
    by_cases hi:i<Fo b
    · rw [aHp,ite_eq_left hi]
      rw [Process.Hj,dite_eq_left hi] at hI
      exact d59 src R.sched pairs (nextIndex i hi) (Finset.mem_filter.mp hI).2
    · rw [aHp,ite_eq_right hi]
      rw [Process.Hj,dite_eq_right hi] at hI
      obtain ⟨P,hP,hproper,hzero⟩:=b2N src (Or.inl rfl) R.sched.bxE.pos
        (Finset.mem_filter.mp hI).2
      exact ⟨P,hP,hproper,fun γ hγ _=>hzero γ hγ⟩
  obtain ⟨C,hC,hcover⟩:=dN1 (R.Hj i) (aHp b i) hj geom an1
  refine ⟨C,fun bw => ?_,hcover⟩
  rw [← kG]
  exact (Nat.cast_le (α:=ℚ)).mpr (hC bw)
end
end qX7bYgd
