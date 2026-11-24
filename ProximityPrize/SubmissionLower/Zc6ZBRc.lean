import ProximityPrize.SubmissionLower.ZffaUPa
import ProximityPrize.SubmissionLower.ZwuC0Sd
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace qu56FMb
noncomputable section
open Finset
open P6 (p K)
open P6_7 (RectTail)
open P6_7_2 (Input)
open P6_7_2_3 (Origin MemberFits terminalStop TerminalCutter marks terminalPrice terminalAllowance sectionMass Tl BC terminalProjection degree persistentRate NativeOK nativeRate)
open cu (FX L jz)
open gT (Ambient aci iJ)
open pI (xN dual by6)
open ac3 (aYy bZk)
open YY (by9 xg aef a9E U7)
open TD (GM FP a3x dYl)
open Rk (KR bXR cGi)
open private aqH bOX from ProximityPrize.SubmissionLower.AH
open private cpa from ProximityPrize.SubmissionLower.U
open private c2p from ProximityPrize.SubmissionLower.G
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (b:RectTail) (x :Input b) (o:Origin) (Q:Ideal Ambient),
    xN Q→Q.height=2→dual Q→MemberFits b o terminalStop Q →
    ∀ F:TerminalCutter x Q,
      (∀ k :Fin 4,(k=0∨k=1) →
        divisorMass Q F.row (r b) (fun I=>curveMass I k)≤firstMass (s b) Q k) ∧
      (divisorMass Q F.row (r b) (fun I=>aef I) ≤
        FP (Tl (2*(s b).U) (s b)) (sectionMass Q)) ∧
      ∀ I∈qv Q F.row,aef I<p
def c2 :Prop :=
  ∀ (b:RectTail) (x :Input b) (o:Origin) (Q:Ideal Ambient),
    xN Q→Q.height=2→dual Q→MemberFits b o terminalStop Q →
    ∀ F:TerminalCutter x Q,(∀ I∈qv Q F.row,aef I<p) →
      (∀ k :Fin 4,(k=2∨k=3) →
        divisorMass Q F.row (r b) (fun I=>curveMass I k)≤firstMass (s b) Q k) ∧
      ((points Q F.row).card:ℚ)≤FP (terminalAllowance b) (sectionMass Q)
def c3:Prop :=
  ∀ (b:RectTail) (x :Input b) (I:Ideal Ambient),by6 I→aef I<p →
    ∀ G:Ambient,RectCaps (s b) G→G∉I →
      (∀ γ∈marks x I,aci (x.M.label γ) (x.F.scalar γ) G=0) →
      ((marks x I).card:ℚ)≤FP (rowPrice (s b)) (curveMass I)
def c4 :Prop :=
  ∀ (b:RectTail) (x :Input b) (I:Ideal Ambient),by6 I →
    ¬ by9 (xg I) →
    ((marks x I).card:ℚ)≤2*curveMass I 0*curveMass I 1
def c5:Prop :=
  ∀ I:Ideal Ambient,by6 I→by9 (xg I) →
    ∃ (C:MvPolynomial (Fin 2) L) (g:ℕ),Descended I C g
def c6:Prop :=
  ∀ (b:RectTail) (x :Input b) (I:Ideal Ambient) (C:MvPolynomial (Fin 2) L) (g:ℕ),
    Descended I C g→C.totalDegree*g<p →
    ((marks x I).card:ℚ)≤persistentRate b g*a9E I+g ∧
    (g=1→((marks x I).card:ℚ)≤linearRate b*a9E I+g)
def c7:Prop :=
  ∀ (b:RectTail) (x :Input b) (I:Ideal Ambient) (C:MvPolynomial (Fin 2) L),
    Descended I C 2→C.totalDegree*2<p →
    ((marks x I).card:ℚ)≤16*((C.totalDegree :ℚ)*2)+quadraticRate b*a9E I+2
def c8:Prop :=
  ∀ (b:RectTail) (x :Input b) (I:Ideal Ambient) (C:MvPolynomial (Fin 2) L) (g:ℕ),
    Descended I C g→C.totalDegree*g<p→3≤g →
    ∀ e c W M,NativeOK (degree b) g e c W M →
    ((marks x I).card:ℚ)≤nativeSlope C.totalDegree g*((C.totalDegree :ℚ)*g)+
      nativeRate (degree b) g e c W*a9E I+g
private theorem hasse_zero (F:Ambient) :KR (0:Exponent) F=F:= by
  ext a
  simpa using cGi (0:Exponent) a F (fun i=>Or.inl (by simp))
private theorem b5O {s :cu.Shape} {F:Ambient} (hF:RectCaps s F) (e :Exponent) :
    RectCaps s (KR e F) := by
  intro a ha
  have hm:e+a∈F.support := by
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp ha
      (bXR e a F (MvPolynomial.notMem_support_iff.mp hn))
  obtain ⟨h₀,h₁,h₂,h₃⟩:=hF _ hm
  simp only [Finsupp.add_apply] at h₀ h₁ h₂ h₃
  exact ⟨by omega,by omega,by omega,by omega⟩
private theorem DN {Q I:Ideal Ambient} {F:Ambient} (ha :xN Q) (hp:F∉Q)
    (hI:I∈qv Q F) :by6 I:= by
  have hs :Function.Surjective iJ:= by
    rw [bOX]
    exact aqH.symm.surjective
  obtain ⟨P,rfl⟩:=hs F
  obtain ⟨hm,hc⟩:=mem_filter.mp hI
  obtain ⟨hi,hd⟩:=bZk ha hp hm
  exact ⟨hi,hd,cy6.proof I hi hd hc⟩
private theorem marks_cover {b:RectTail} {x :Input b} {Q:Ideal Ambient}
    (F:TerminalCutter x Q) :
    marks x Q⊆(points Q F.row).biUnion (marks x)∪(qv Q F.row).biUnion (marks x) := by
  intro γ hγ
  obtain ⟨hΓ,hm⟩:=mem_filter.mp hγ
  let ev :=aci (x.M.label γ) (x.F.scalar γ)
  have hf :=F.necessary γ hΓ 0 (by simp)
  rw [hasse_zero] at hf
  have hle :Q ⊔ Ideal.span {F.row} ≤ RingHom.ker ev :=
    sup_le hm ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hf))
  have : (RingHom.ker ev).IsPrime :=RingHom.ker_isPrime ev
  obtain ⟨I,hI,hmark⟩:=Ideal.exists_minimalPrimes_le hle
  have hi:I∈cut Q F.row:=Ideal.mem_minimalPrimesFinset.mpr hI
  have hmi:γ∈marks x I:=mem_filter.mpr ⟨hΓ,hmark⟩
  by_cases hcon :aYy I
  · exact mem_union_left _ (mem_biUnion.mpr ⟨I,mem_filter.mpr ⟨hi,hcon⟩,hmi⟩)
  · exact mem_union_right _ (mem_biUnion.mpr ⟨I,mem_filter.mpr ⟨hi,hcon⟩,hmi⟩)
private theorem points_card {b:RectTail} {x :Input b} {Q:Ideal Ambient} (F:TerminalCutter x Q) :
    ((points Q F.row).biUnion (marks x)).card≤(points Q F.row).card:= by
  calc
    _ ≤ ∑ I∈points Q F.row,(marks x I).card:=card_biUnion_le
    _ ≤ ∑ _I∈points Q F.row,1 := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hc,hp⟩:=mem_filter.mp hI
      let _:I.IsPrime :=(Ideal.mem_minimalPrimesFinset.mp hc).isPrime
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply jz.injective
      apply (algebraMap cu.FX (gT.gk I)).injective
      exact (cpa hp (mem_filter.mp hγ).2).trans
        (cpa hp (mem_filter.mp hδ).2).symm
    _ = _:= by simp
private theorem shape_order (b:RectTail) : (s b).J≤(s b).B:= by cases b <;> decide
private theorem seed_nonneg (U:ℕ) (b:RectTail) (k :Fin 4) :
    0≤Tl U (s b) k := by
  fin_cases k <;> simp [Tl,(Nat.cast_le (α:=ℚ)).mpr (shape_order b)]
private theorem den_pos (b:RectTail) :0<den b:= by exact_mod_cast Nat.succ_pos (r b)
private theorem projection_le {b:RectTail} {o:Origin} {Q:Ideal Ambient}
    (hf :MemberFits b o terminalStop Q) {n:ℕ} (hn:n≤2) :
    FP (Tl (n*(s b).U) (s b)) (sectionMass Q)/den b≤terminalProjection b o n:= by
  apply div_le_div_of_nonneg_right _ (den_pos b).le
  apply le_min
  · apply (a3x (seed_nonneg _ _) fun k=>(hf k).trans (min_le_right _ _)).trans
    apply dYl
    · intro k
      cases b <;> fin_cases k <;> simp [BC]
    · intro k
      fin_cases k <;> simp [Tl]
      exact_mod_cast Nat.mul_le_mul_right (s b).U hn
  · exact a3x (seed_nonneg _ _) hf
private theorem first_axis (b:RectTail) (Q:Ideal Ambient) {k :Fin 4}
    (hk :k=0∨k=1) :
    firstMass (s b) Q k=FP (Tl (1*(s b).U) (s b)) (sectionMass Q) := by
  rcases hk with rfl | rfl <;> simp [firstMass,firstWeight,Tl,Nat.cast_sub (shape_order b)]
private theorem single_mass {b:RectTail} {x :Input b} {Q I:Ideal Ambient}
    {F:TerminalCutter x Q} (hI:I∈qv Q F.row) (hp:PaidOn F.row (r b) I)
    {m:Ideal Ambient→ℚ} (hm : ∀ R,0≤ m R) {d:ℚ}
    (hs :divisorMass Q F.row (r b) m≤d) :m I≤d/den b:= by
  apply (le_div_iff₀ (den_pos b)).mpr
  rw [mul_comm]
  have hi:=single_le_sum (s :=qv Q F.row)
    (f := fun R=>(paidWeight F.row (r b) R:ℚ)*m R)
    (fun R _=>mul_nonneg (Nat.cast_nonneg _) (hm R)) hI
  exact (by simpa only [paidWeight,ite_eq_left hp] using hi.trans hs)
private theorem eLN (C:MvPolynomial (Fin 2) L) :
    C.totalDegree≤C.degreeOf 0+C.degreeOf 1 := by
  apply Finset.sup_le
  intro a ha
  change a.degree≤_
  rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]
  exact Nat.add_le_add (C.le_degreeOf_of_mem_support 0 ha) (C.le_degreeOf_of_mem_support 1 ha)
private theorem graph_count {b:RectTail} (x :Input b) {I:Ideal Ambient}
    {C:MvPolynomial (Fin 2) L} {g:ℕ} (A:Descended I C g) (hc:C.degreeOf 0<p) :
    (marks x I).card≤C.degreeOf 0+p*C.degreeOf 1 := by
  let label (γ:K) :FX:=jz (x.M.label γ)
  have hin:Function.Injective label := fun _ _ h=>sub_left_inj.mp (jz.injective h)
  let G:=MvPolynomial.map U7 C
  have hG:G≠0:= fun h=>A.irreducible.ne_zero
    (MvPolynomial.map_injective _ U7.injective (h.trans (map_zero _).symm))
  have hdeg (i:Fin 2) :G.degreeOf i=C.degreeOf i:= by
    simp only [G,MvPolynomial.degreeOf_eq_sup,MvPolynomial.support_map_of_injective _
      U7.injective]
  have he :G∈xg I:= by
    rw [A.projection]
    exact Ideal.mem_span_singleton_self _
  have h:=cu.bqt p _ _ (by decide)
    G hG (hdeg 0).le hc (hdeg 1).le ((marks x I).image label) (by
      intro ℓ hℓ
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hℓ
      exact c2p (mem_filter.mp hγ).2 he)
  simpa only [card_image_of_injective _ hin] using h
private theorem curveMass_nonneg (I:Ideal Ambient) (k :Fin 4) :0≤ curveMass I k :=
  Nat.cast_nonneg _
private theorem paid_price (b:RectTail) (z a h:ℚ) (I:Ideal Ambient) :
    FP ![z,a+1,h,0] (curveMass I)≤den b*FP (aHm b z a h) (curveMass I) := by
  simp only [FP,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (curveMass_nonneg I k)
  rw [mul_comm (den b)]
  apply (div_le_iff₀ (den_pos b)).mp
  by_cases hr :r b=0
  · simp [aHm,hr]
  · simp [aHm,hr]
private theorem contract_price (b:RectTail) (z a h:ℚ) (Q:Ideal Ambient) :
    FP (aHm b z a h) (firstMass (s b) Q)+FP (terminalAllowance b) (sectionMass Q) =
      FP (terminalPrice b z a h+terminalAllowance b) (sectionMass Q) := by
  by_cases hr :r b=0 <;>
    simp [FP,firstMass,firstWeight,aHm,rowPrice,terminalPrice,hr,Fin.sum_univ_four,
      Pi.add_apply] <;> ring
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (h6:c6) (h7:c7) (h8:c8) :P6_7_2_3.c6:= by
  intro b x o Q ha hh hd hf F z a h hok
  obtain ⟨haxes,hplane,hsmall⟩:=h1 b x o Q ha hh hd hf F
  obtain ⟨hjet,hpoints⟩:=h2 b x o Q ha hh hd hf F hsmall
  let kd:=terminalProjection b o 1
  let d:=min (terminalProjection b o 2) (2*kd)
  obtain ⟨_,hdp,hapos,haa,hap,hz,hhn,hblend⟩:=hok
  have haz :0≤a+1 := by linarith only [hapos]
  have hzn:0≤z := by linarith only [hz]
  have hrate : ∀ k,0≤aHm b z a h k := by
    have hn (k :Fin 4) :0≤(![z,a+1,h,0] :GM) k := by
      fin_cases k <;> first | assumption | exact le_rfl
    intro k
    have hh:=div_nonneg (hn k) (den_pos b).le
    by_cases hr :r b=0
    · simpa only [aHm,ite_eq_left hr] using hh
    · exact (by simpa only [aHm,ite_eq_right hr] using
        hh.trans (le_max_right (rowPrice (s b) k) _))
  have hcount (I:Ideal Ambient) (hI:I∈qv Q F.row) :
      ((marks x I).card:ℚ)≤(paidWeight F.row (r b) I:ℚ)*
        FP (aHm b z a h) (curveMass I) := by
    have hgeom:=DN ha F.proper hI
    by_cases hp:PaidOn F.row (r b) I
    · have haxis (k :Fin 4) (hk :k=0∨k=1) :curveMass I k≤kd:= by
        apply (single_mass hI hp (fun R=>curveMass_nonneg R k) (haxes k hk)).trans
        rw [first_axis b Q hk]
        exact projection_le hf (by decide)
      have hT: ((marks x I).card:ℚ)≤z*curveMass I 0+(a+1)*curveMass I 1+h*curveMass I 2 := by
        by_cases hc:by9 (xg I)
        · obtain ⟨C,g,A⟩:=h5 I hgeom hc
          have hpg: (C.totalDegree :ℚ)*g≤d:= by
            apply le_min
            · have hcg: (C.totalDegree :ℚ)*g≤aef I:= by exact_mod_cast A.u7
              exact hcg.trans ((single_mass hI hp (fun R=>Nat.cast_nonneg (aef R)) hplane).trans
                (projection_le hf (by decide)))
            · have htot: (C.totalDegree :ℚ)≤(C.degreeOf 0:ℚ)+C.degreeOf 1 := by
                exact_mod_cast eLN C
              have hs₀:=A.first.trans (haxis 0 (Or.inl rfl))
              have hs₁:=A.second.trans (haxis 1 (Or.inr rfl))
              calc
                _≤((C.degreeOf 0:ℚ)+C.degreeOf 1)*g :=
                  mul_le_mul_of_nonneg_right htot (Nat.cast_nonneg g)
                _≤(2*kd) := by rw [add_mul]; linarith only [hs₀,hs₁]
          have hcP:C.totalDegree*g<p:= by exact_mod_cast hpg.trans_lt hdp
          have ha₀:=(Nat.le_mul_of_pos_right _ A.positive).trans_lt hcP
          have hc₀:=(C.degreeOf_le_totalDegree 0).trans_lt ha₀
          have ht: (C.totalDegree :ℚ)≤d:= by
            have hle : (C.totalDegree :ℚ)≤(C.totalDegree :ℚ)*g:= by
              exact_mod_cast (Nat.le_mul_of_pos_right C.totalDegree A.positive)
            exact hle.trans hpg
          obtain ⟨hpersist,hlinear⟩:=h6 b x I C g A hcP
          have hm:=constant_price b A.positive hz hapos hhn ht (eLN C)
            (hblend g A.positive) (graph_count x A hc₀) hpersist hlinear
            (fun he=> by subst g; exact h7 b x I C A hcP)
            (fun hg=>h8 b x I C g A hcP hg)
          exact hm.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left A.first hzn)
            (mul_le_mul_of_nonneg_left A.second haz)) le_rfl)
        · have hh:=h4 b x I hgeom hc
          have hm:=mul_le_mul_of_nonneg_right (haxis 0 (Or.inl rfl)) (curveMass_nonneg I 1)
          have ha' := mul_le_mul_of_nonneg_right haa (curveMass_nonneg I 1)
          linarith only [hh,hm,ha',curveMass_nonneg I 1,mul_nonneg hzn (curveMass_nonneg I 0),
            mul_nonneg hhn (curveMass_nonneg I 2)]
      have hpay : ((marks x I).card:ℚ)≤FP ![z,a+1,h,0] (curveMass I) := by
        simpa [FP,Fin.sum_univ_four] using hT
      simpa only [paidWeight,ite_eq_left hp] using hpay.trans (paid_price b z a h I)
    · obtain ⟨e,he⟩:=not_forall.mp hp
      obtain ⟨he',hproper⟩:=not_imp.mp he
      have hr :r b≠0:= by
        intro hr
        have hn (i:Fin 4) :e i ≤ ∑ j,e j:=single_le_sum (fun j _=>Nat.zero_le (e j)) (mem_univ i)
        have hzero :e=0:= by ext i; have :=hn i; simp only [hr] at he'; simpa using (by omega :e i=0)
        apply hproper
        rw [hzero,hasse_zero]
        exact (Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp hI).1).le
          (Ideal.mem_sup_right (Ideal.mem_span_singleton_self F.row))
      have hb:=h3 b x I hgeom (hsmall I hI) _ (b5O F.caps e) hproper
        (fun γ hγ=>F.necessary γ (mem_filter.mp hγ).1 e he')
      have hs :=dYl (curveMass_nonneg I) (v :=rowPrice (s b)) (w:=aHm b z a h)
        (fun k=> by simp [aHm,hr])
      simpa only [paidWeight,ite_eq_right hp,Nat.cast_one,one_mul] using hb.trans hs
  have hstock : ∀ k,divisorMass Q F.row (r b) (fun I=>curveMass I k)≤firstMass (s b) Q k := by
    intro k
    fin_cases k
    · exact haxes 0 (Or.inl rfl)
    · exact haxes 1 (Or.inr rfl)
    · exact hjet 2 (Or.inl rfl)
    · exact hjet 3 (Or.inr rfl)
  have hsum :
      (∑ I∈qv Q F.row,(paidWeight F.row (r b) I:ℚ)*FP (aHm b z a h) (curveMass I)) =
        FP (aHm b z a h) (fun k=>divisorMass Q F.row (r b) (fun I=>curveMass I k)) := by
    simp only [FP,divisorMass,Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun k _=>sum_congr rfl fun I _=> by ring
  have hcurves : (((qv Q F.row).biUnion (marks x)).card:ℚ) ≤
      FP (aHm b z a h) (firstMass (s b) Q) := by
    have hc: (((qv Q F.row).biUnion (marks x)).card:ℚ) ≤
        ∑ I∈qv Q F.row,((marks x I).card:ℚ) := by exact_mod_cast card_biUnion_le
    exact hc.trans ((sum_le_sum hcount).trans (hsum.trans_le (a3x hrate hstock)))
  have hcover : ((marks x Q).card:ℚ) ≤
      (((points Q F.row).biUnion (marks x)).card:ℚ)+(((qv Q F.row).biUnion (marks x)).card:ℚ) := by
    exact_mod_cast (card_le_card (marks_cover F)).trans (card_union_le _ _)
  have hpt: (((points Q F.row).biUnion (marks x)).card:ℚ)≤(points Q F.row).card:= by
    exact_mod_cast points_card F
  rw [← contract_price]
  simpa only [add_comm] using hcover.trans (add_le_add (hpt.trans hpoints) hcurves)
end
end qu56FMb
