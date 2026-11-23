import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZhDU57c
import ProximityPrize.SubmissionLower.ZpYo3sb
import ProximityPrize.SubmissionLower.Zk6yNvb
import ProximityPrize.SubmissionLower.ZVbskte
import ProximityPrize.SubmissionLower.ZPaaHRd
import ProximityPrize.SubmissionLower.ZFE6fqe
import ProximityPrize.SubmissionLower.ZIAMiic
import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.ZkL5N7c
import ProximityPrize.SubmissionLower.Zw100fa
import ProximityPrize.SubmissionLower.Znw9tNe
import ProximityPrize.SubmissionLower.ZLrBvqe
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P6_7_6
noncomputable section
open P6 (jG K I)
open P6_7 (YQ bW4 aic)
open P5_7 (farAgreement j3)
open P5_7_4 (LocalPole PoleDebit)
open cu (L FX j9 triangle)
open DP Polynomial
open scoped Polynomial BigOperators
open private c4y from ProximityPrize.SubmissionLower.Zq1cNdd
open private bank_ok from ProximityPrize.SubmissionLower.Z9Rfpte
theorem source (hlocal : LocalPole)
    {b u del} (M : jG u del) {Γ} (F : P1.bje farAgreement M Γ)
    (hlo : 0 < M.iF.toNat) (hhi : M.iF.toNat ≤ 131070)
    (H : L[X]) (hH : YQ M F H) :
    ∃ rows, P6_7.Source b M F rows := by
  let h := M.iF.toNat
  have hchar : h < K1.p := hhi.trans_lt (by decide)
  obtain ⟨D, _, _, hnode, hres⟩ := bW4 M F H hH
  obtain ⟨Crt⟩ := atp.dRH D
  let word : I → L := fun i => algebraMap K L (M.word i)
  refine ⟨VY Crt word, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t _ t' _ hm hB hJ hU W W' hW
    exact d3q Crt word hm hB hJ hU hW
  · intro t _ W hW P hP γ hγ
    let B := F.mark γ hγ
    have hdegree : (j9 (F.scalar γ)).natDegree ≤ 131071 + h := by
      rw [j9, Polynomial.natDegree_map]
      exact aic F hγ
    refine atp.dPr Crt word hnode _ _ (hres γ hγ) hdegree B.bad.support
      B.bad.dw ?_ t.shape W hW P hP
    intro i hit
    rw [j9, ad0, Polynomial.eval_map, Polynomial.eval₂_hom, B.scalar_hits i hit]
  · intro t _ W P hP j i hne
    exact d3r Crt word hP j i hne
  · intro t _ W P hP hne
    exact atp.eu5 hlo hhi Crt word t.shape W P hP hne
  · intro t _ W P hP i r
    exact atp.d3s Crt word hP i r
  · intro t ht W _ hW
    obtain ⟨hJ, hU, hB, hn⟩ := bank_ok b t ht
    have hp : PoleDebit t := qZyoMPc.proof b t ht
    have hvol := atp.bT9 (h := h) (hhi.trans (by decide)) t.shape W hW
    have hcontact := atp.Yw h word t.shape W
    have hpole := c4y hlocal hlo hchar Crt word t.shape hJ hU hB W
    have hsum := agU.telescope hhi Crt word t.shape W
    have hphys : bga t.shape ≤ triangle t.shape.U * t.ad1 := by
      unfold bga agU.ad1 at *
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hn
    unfold PoleDebit at hp
    have hcap := Nat.mul_le_mul_left (2*h) hp
    rw [Nat.mul_add] at hcap
    have hcredit : 2*h*(triangle t.shape.U * agU.arY t.shape) = azS h t.shape := by
      unfold agU.arY azS
      ac_rfl
    rw [hcredit] at hcap
    change ceG h t.shape W ≤ j3 h t +
      ∑ w ∈ Finset.range (W+1), Module.finrank FX (VY Crt word t.shape w)
    unfold j3
    dsimp only [h] at hvol hcontact hpole hsum hcap ⊢
    omega
end
end P6_7_6
end
section
set_option autoImplicit true
namespace P6_7_6
noncomputable section
open P6 (p)
open P6_7 (Source)
open P5_7 (Bank Ls akE Jr anM O2 j3 farAgreement)
open P5_7_4 (aL4 O3 amv Mq)
open cu (Shape vP Jet FX)
open gT (alm)
open aBa (cNB)
open Polynomial Finset
open private cSB from ProximityPrize.SubmissionLower.T
open private ee7 eHt eD6 from ProximityPrize.SubmissionLower.ZhDU57c
private theorem bwO {b H u del} {M : P1.FJ H u del} {Γ}
    {F : P1.bje farAgreement M Γ} {rows : vP} (src : Source b M F rows)
    {t : Bank} (ht : Jr b t) (r : ℕ)
    (hw : aL4 M.iF.toNat r t.shape) :
    O3 M.iF.toNat r t.shape 0 ≤ j3 M.iF.toNat t +
      ∑ W ∈ range (Mq M.iF.toNat r t.shape),
        Module.finrank FX (rows t.shape W) := by
  let h := M.iF.toNat
  let N := Mq h r t.shape
  change t.shape.B * (131071-h) < N at hw
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt : N ≤ t.shape.m * farAgreement := Nat.sub_le _ _
  have hc : N - 1 + 1 = N := by omega
  have hf := src.ajB t ht (N - 1) (by omega) (by
    intro q hq j _
    rw [hc]
    exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right N j))
  unfold O3 amv
  simpa only [hc, zero_mul, Nat.sub_zero] using hf
private theorem bVl {b H u del} {M : P1.FJ H u del} {Γ}
    {F : P1.bje farAgreement M Γ} {rows : vP} (src : Source b M F rows)
    {t : Bank} (ht : Jr b t) (r : ℕ)
    (hw : aL4 M.iF.toNat r t.shape)
    (hd : j3 M.iF.toNat t < O3 M.iF.toNat r t.shape 0) :
    ∃ P ∈ rows t.shape (Mq M.iF.toNat r t.shape - 1), P ≠ 0 := by
  by_contra! hz
  let N := Mq M.iF.toNat r t.shape
  have hf := bwO src ht r hw
  have hsum : (∑ W ∈ range N, Module.finrank FX (rows t.shape W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hle : W ≤ N - 1 := by have := mem_range.mp hW; omega
    have hb : rows t.shape W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (src.nested t ht t ht rfl rfl rfl le_rfl W _ hle hP))
    rw [hb, finrank_bot]
  change _ ≤ _ + ∑ W ∈ range N, Module.finrank FX (rows t.shape W) at hf
  omega
private theorem cCz {b H u del} {M : P1.FJ H u del} {Γ} {F : P1.bje farAgreement M Γ}
    {rows : vP} (src : Source b M F rows) (hh : 0 < M.iF.toNat)
    (hk : 1 ≤ 131071-M.iF.toNat) {t : Bank} (ht : Jr b t) (r : ℕ)
    (hw : aL4 M.iF.toNat r t.shape)
    (hd : j3 M.iF.toNat t < O3 M.iF.toNat r t.shape 1)
    {G P : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree) (hm : alm G)
    (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < p)
    (hseed : ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) :
    ∃ Q ∈ rows t.shape (Mq M.iF.toNat r t.shape - 1), ¬ G ∣ Q := by
  by_contra! hcommon
  let h := M.iF.toNat
  let N := Mq h r t.shape
  have hsum := eD6 rows t.shape h r hk (src.shape t ht) (src.leading t ht) (by
    intro W hW R hR hnR
    apply eHt h N W hh hW hi hv hm hP hdiv hp hseed hnR
    intro i a hshift
    exact hcommon _ (src.nested t ht t ht rfl rfl rfl le_rfl _ _ hshift
      (src.shift t ht W R hR i a)))
  have hf := bwO src ht r hw
  dsimp only [h] at hsum
  omega
theorem eJG {b H u del} {M : P1.FJ H u del} {Γ}
    {F : P1.bje farAgreement M Γ} {rows : vP} (src : Source b M F rows)
    (hh : 0 < M.iF.toNat) (hk : 1 ≤ 131071 - M.iF.toNat)
    {s : Ls} (hs : s ∈ b.row.stages)
    (hwidth : aL4 M.iF.toNat s.dI s.free.shape)
    (hfree : j3 M.iF.toNat s.free < O3 M.iF.toNat s.dI s.free.shape 0)
    (hchar : s.free.shape.U < p)
    (hwidth' : aL4 M.iF.toNat s.dI s.moving.shape)
    (hmoving : j3 M.iF.toNat s.moving < O3 M.iF.toNat s.dI s.moving.shape 1) :
    Nonempty (akE M.iF.toNat rows s) := by
  have hsFree : Jr b s.free := Or.inr (Or.inl ⟨s, hs, Or.inl rfl⟩)
  have hsMoving : Jr b s.moving := Or.inr (Or.inl ⟨s, hs, Or.inr rfl⟩)
  obtain ⟨P, hPm, hP⟩ := bVl src hsFree s.dI hwidth hfree
  have hnonzero := bVl src hsMoving s.dI hwidth'
    (hmoving.trans_le (ee7 _ _ _))
  have hseed (j y : ℕ) : ((P.coeff j).coeff y).totalDegree ≤ s.free.shape.U := by
    by_cases hz : (P.coeff j).coeff y = 0
    · simp [hz]
    · exact (src.shape s.free hsFree _ P hPm j y hz).2.2
  obtain ⟨Q, hQm, hQ, havoid⟩ := cNB P hP _ hnonzero (fun G hi hdiv hv hm =>
    cCz src hh hk hsMoving s.dI hwidth' hmoving hi hv hm hP hdiv hchar hseed)
  have hcut (a : Shape) : anM M.iF.toNat s.dI a =
      Mq M.iF.toNat s.dI a - 1 := by
    unfold anM O2 Mq
    omega
  exact ⟨⟨P, Q, hP, hQ, (hcut _).symm ▸ hPm, (hcut _).symm ▸ hQm,
    fun G hi hdiv hdiv' hv => cSB G (fun hm => havoid G hi hdiv hv hm hdiv')⟩⟩
end
end P6_7_6
end
section
set_option autoImplicit true
namespace P6_7_6
open P5_7 (aRe far_guards)
def c1 : Prop := qQCEOid.c1
def c2 : Prop := qQCEOid.c2
theorem of_children (h1 : c1) (h2 : c2) : P6_7.c6 := by
  intro b u del M Γ F hw _ H hH
  obtain ⟨hl, hu⟩ := aRe hw
  have hguards := far_guards b
  have hh := hguards.1.trans_le hl
  have htop : M.iF.toNat ≤ 131070 := hu.trans (by have h := hguards.2.1; omega)
  obtain ⟨rows, src⟩ := source (b := b) (qQCEOid.of_children h1 h2) M F hh htop H hH
  refine ⟨rows, src, ⟨fun s hs => Classical.choice ?_⟩⟩
  obtain ⟨wf, df, hc, wm, dm⟩ := P5_7_4.stage_tests hl hu hs
  have hk : 1 ≤ 131071 - M.iF.toNat :=
    Nat.le_sub_of_add_le (Nat.add_le_add_left htop 1)
  exact eJG src hh hk hs wf df hc wm dm
end P6_7_6
end
section
set_option autoImplicit true
namespace P6_7_8
open Polynomial Finset
open scoped Classical
open cu (L)
open P5 (p)
open P5_7_7 (Dg nodeRate)
open qGnV2ac (EquationBounds Sections HE pN)
def c1 : Prop :=
  ∀ (F : Dg) (l h : ℕ), EquationBounds F l h →
    ∀ (S : Sections F) (x a b : L), a ≠ 0 ∨ b ≠ 0 →
      (S.CF.filter fun γ =>
        (S.P γ).eval x * a = (S.Q γ).eval x * b ∧ (S.A γ).eval x ≠ 0).card ≤ nodeRate l*h
def c2 : Prop :=
  ∀ (F : Dg) (l h u s L₀ W : ℕ), EquationBounds F l h →
    2*u+s = L₀ → l*L₀ ≤ W → HE F s (W-l*u) →
    (2*l-2)*W - l*(l-1)*L₀ < p →
    ∀ S : Sections F,
      ∑ γ ∈ S.CF, max (S.B γ).natDegree ((S.A γ).natDegree-pN S s γ) ≤
        ((6*l-4)*W - (3*l*l-4*l+2)*L₀)*h
theorem of_children (h1 : c1) (h2 : c2) : P6_7.c8 :=
  ⟨qZCRTge.of_children q81Yhob.proof qCAunta.proof, h1, h2⟩
end P6_7_8
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace qT2dl0a
noncomputable section
open Polynomial Finset
open qNu3xvc (Equation Sections GraphVal qg Over seed poleCharge finitePoles
 NoHorizontalPole horizontalDegree)
open qJOpoVa (relativeRate c2 c3 c5 c6)
open P5 (p)
open cu (L)
open E7 (CurveField CurvePlace poleOrder KB)
open agN (b27 a6F)
open qFD8jve (aFA sheetPole)
open P5_7_1_7_4_3_4 (Pencil relativePolar adG)
open q82zwcd (width polar poles)
open private same_center sum_le_all from ProximityPrize.SubmissionLower.ZT8CHOb
open private budgets from ProximityPrize.SubmissionLower.ZATKiYa
open private gauss_of_pencil from ProximityPrize.SubmissionLower.Zk6yNvb
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool)
      (v : ∀ i,GraphVal A (r i)),(∀ i,qg A (w i)) →
      (∀ i,Over (v i) (w i) (x i)) →
      ∃ C:Pencil A,C.tilt≠0 ∧
        (∀ i,(v i).val (relativePolar C)=(v i).val (qNu3xvc.polar A (r i))) ∧
        ∀ i (g:L[X]),g≠0 →
          (v i).val (g.eval₂ ((seed A).comp (algebraMap L E)) (C.base RatFunc.X))=1
private theorem global_budget (qW:c1) (FT:c5) (localNorm:c6)
    {E :Type} [Field E] [Algebra L E] (A:Equation E) (hc:CurveField L E)
    (hd:2≤A.d) (hp:A.d<p) {ι:Type} [Fintype ι]
    (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool) (v : ∀ i,GraphVal A (r i))
    (hinj:Function.Injective (fun i=>(w i,x i)))
    (hreg : ∀ i,qg A (w i)) (hover : ∀ i,Over (v i) (w i) (x i)) :
    (∑ i,poleCharge (v i))≤ relativeRate A*A.h:= by
  obtain ⟨C,htilt,hpolar,hfresh⟩:=qW A hd hp ι w x r v hreg hover
  have hgauss (i:ι) :=gauss_of_pencil hc C (hover i) (hfresh i)
  have hq:relativePolar C≠0:=div_ne_zero C.polar_ne (pow_ne_zero _ C.gauge_ne)
  obtain ⟨P,hP,hdvd,hbound⟩:=FT A hd C htilt
  obtain ⟨j,hj⟩ : ∃ j,(P.coeff 0).coeff j≠0:= by
    by_contra! h
    exact hP (Polynomial.ext fun j=> by simp [h j])
  let a :=(P.coeff 0).coeff j
  let places :=univ.image w
  have hlocal (z :CurvePlace L E) (hz :z∈places) :
      (∑ i∈univ.filter (fun i=>w i=z),poleCharge (v i))≤KB z.value a := by
    obtain ⟨i,-,hi⟩:=mem_image.mp hz
    have h0:sheetPole z.value A.f=0:= by
      rw [← hi]
      exact (Finset.sup_eq_bot_iff _ _).mpr fun ij _ =>
        (a6F _ _).mpr ((hreg i).1 ij.1 ij.2)
    have hB:aFA z.value P 0:= by simpa only [h0,Nat.mul_zero] using hbound z
    have hh:=localNorm z C.base _ C.finite C.separable hq P hP hB hdvd
      (univ.filter (fun i=>w i=z)) (fun i=>(v i).val)
      (by
        intro i hi j hj h
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        have hw:=hi'.trans hj'.symm
        exact hinj (Prod.ext hw (same_center (hover i) (hw.symm ▸ hover j) h)))
      (fun i _=>(v i).normalized) (fun i hi=>(mem_filter.mp hi).2 ▸ hgauss i)
    simp only [KB,hpolar] at hh
    refine hh.trans (Int.toNat_le_toNat (neg_le_neg ?_))
    have hs :z.value a≤adG z.value (P.coeff 0) :=
      Finset.le_sup (f := fun k=>z.value ((P.coeff 0).coeff k))
        (Polynomial.mem_support_iff.mpr hj)
    exact (WithZero.log_le_log (z.value.ne_zero_iff.mpr hj)
      (ne_of_gt ((zero_lt_iff.mpr (z.value.ne_zero_iff.mpr hj)).trans_le hs))).mpr hs
  have hdiv :=aFU.of_children
    bRt.proof bRu.proof L E hc
  obtain ⟨hpf,hzf,hsum,_⟩:=hdiv a
  let M (z :CurvePlace L E) :=sheetPole z.value A.f
  have hM:M.HasFiniteSupport:=b27 hdiv _
  have hpoles : (∑ᶠ z :CurvePlace L E,poleOrder z.value a)≤ relativeRate A*A.h:= by
    change _≤ relativeRate A * ∑ᶠ z,M z
    rw [mul_finsum]
    apply finsum_le_finsum hpf
      (hM.subset fun z hz hzero=>hz (by change relativeRate A*M z=0; rw [hzero,mul_zero]))
    intro z
    exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (z.value.ne_zero_iff.mpr hj)).mpr (hbound z 0 j))
  calc
    (∑ i,poleCharge (v i)) =
        ∑ z∈places,∑ i∈univ.filter (fun i=>w i=z),poleCharge (v i) :=
      (sum_fiberwise_of_maps_to (fun _ hi=>mem_image_of_mem _ hi) _).symm
    _ ≤ ∑ z∈places,KB z.value a :=sum_le_sum hlocal
    _ ≤ ∑ᶠ z :CurvePlace L E,KB z.value a :=sum_le_all _ hzf _
    _ = ∑ᶠ z :CurvePlace L E,poleOrder z.value a :=hsum.symm
    _≤_:=hpoles
private theorem finite_budget (charge :c3) (qW:c1) (FT:c5) (localNorm:c6)
   {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A)
   (hc:CurveField L E) (hd:2≤A.d) (hp:A.d<p) (hor :NoHorizontalPole A) :
   finitePoles S≤ relativeRate A*A.h:= by
 let U:=S.marks.sigma fun γ=>(S.den γ).roots.toFinset
 let w (i : ↥U) :=S.place i.val.1
 let x (i : ↥U) :=i.val.2
 have hinj:Function.Injective (fun i=>(w i,x i)) := by
   intro i j hij
   have hi:=(Finset.mem_sigma.mp i.prop).1
   have hj:=(Finset.mem_sigma.mp j.prop).1
   exact Subtype.ext (Sigma.ext (S.distinct hi hj (congrArg Prod.fst hij))
     (heq_of_eq (congrArg Prod.snd hij)))
 have hv (i : ↥U) : ∃ (r :Bool) (v :GraphVal A r),Over v (w i) (x i) ∧
     (S.den i.val.1).rootMultiplicity (x i)≤poleCharge v := by
   obtain ⟨hγ,hx⟩:=Finset.mem_sigma.mp i.prop
   exact charge A S hc hd hp hor _ hγ _ hx
 choose r v hv hle using hv
 calc
   finitePoles S = ∑ i : ↥U,(S.den i.val.1).rootMultiplicity (x i) := by
     change finitePoles S = ∑ i∈U.attach,(S.den i.val.1).rootMultiplicity i.val.2
     rw [Finset.sum_attach U (fun i=>(S.den i.1).rootMultiplicity i.2)]
     unfold U finitePoles
     rw [Finset.sum_sigma]
     refine sum_congr rfl fun γ _ => ?_
     rw [← IsAlgClosed.card_roots_eq_natDegree,← Multiset.toFinset_sum_count_eq]
     exact sum_congr rfl fun _ _=>Polynomial.count_roots _
   _ ≤ ∑ i,poleCharge (v i) :=sum_le_sum fun i _=>hle i
   _≤_:=global_budget qW FT localNorm A hc hd hp w x r v hinj
     (fun i=>S.regular _ (Finset.mem_sigma.mp i.prop).1) hv
theorem of_children (transport:qJOpoVa.c1) (Oj:c2) (charge :c3)
  (qW:c1) (FT:c5) (localNorm:c6) :q82zwcd.c5:= by
 intro D w U s z q J F V W hd hp hW hg hf
 let t:=J.u₁-J.u₀
 let b:=W-F.d*J.u₀-F.d*t
 have hw:2*J.u₀+t=width D:= by
  have h:=J.xF
  have ho:=J.order
  change 2*q7F2qKe.weakAgreement+(J.u₀+J.u₁)=262144+D at h
  dsimp only [t,width]
  omega
 have hd₂:2≤F.d:= by omega
 obtain ⟨hb,hguard,hrate⟩:=budgets F.d J.u₀ t (width D) W hd₂ hw hW
 have hdu:F.d*J.u₀≤W :=
  (Nat.mul_le_mul_left F.d (by omega :J.u₀≤width D)).trans hW
 have he :b+F.d*(J.u₀+t)=W:= by
  change b+F.d*t=W-F.d*J.u₀ at hb
  rw [Nat.mul_add,Nat.add_left_comm,hb,add_comm,Nat.sub_add_cancel hdu]
 obtain ⟨A,S,had,hat,hab,hah,hS⟩:=transport V b hd (he.symm ▸ hf)
 have hAd:2≤A.d:=had.symm ▸ hd₂
 have hAp:A.d<p:=had.symm ▸ hp
 have hhor :horizontalDegree A<p:= by
  unfold horizontalDegree
  rw [had,hat,hab]
  exact hguard.trans_lt hg
 have hB:relativeRate A≤poles D F.d W+(2*F.d-2) := by
  unfold relativeRate
  rw [had,hat,hab]
  exact Nat.add_le_add_right hrate _
 exact hS.trans ((finite_budget charge qW FT localNorm A S F.curve.curve hAd hAp
  (Oj A hAd hAp hhor)).trans (Nat.mul_le_mul hB hah))
end
end qT2dl0a
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace quwKLBd
noncomputable section
open cu (L)
open Cu
open E7 (CurvePlace)
open qZfVj1b (gRK)
open qBajpRb (CurveRing incl yq)
open private incl_constant mark_place from ProximityPrize.SubmissionLower.ZIAMiic
open private constants const_le from ProximityPrize.SubmissionLower.ZFE6fqe
open scoped WithZero
attribute [local instance] gRK
private theorem specialize {k B E :Type} [Field k] [IsAlgClosed k]
   [CommRing B] [Algebra k B] [Field E] [Algebra k E]
   (j:B →ₐ[k] E) (φ:B →ₐ[k] k) (w:CurvePlace k E)
   (hw : ∀ b,φ b=0↔w.value (j b)<1)
   {u:E} (hu:IsTranscendenceBasis k (fun _:Unit=>u)) :
   ∃ (g:E →ₐ[k] LaurentSeries k) (s :B →ₐ[k] PowerSeries k),
     (∀ a,w.value a=(Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰) (g a)) ∧
     (∀ b,(s b:LaurentSeries k)=g (j b)) ∧
     (∀ b,PowerSeries.constantCoeff (s b)=φ b) := by
 obtain ⟨f,g,hfg,hc,hker,hval⟩:=exists_laurent w hu
 let c:=algebraMap k B
 have hdiff (b:B) :w.value (j (b - c (φ b)))<1 :=(hw _).mp (by
   rw [map_sub,φ.commutes,Algebra.algebraMap_self_apply,sub_self])
 have hreg (b:B) :w.value (j b)≤1 := by
   have he :j (b - c (φ b))+algebraMap k E (φ b)=j b:= by
     rw [map_sub,j.commutes,sub_add_cancel]
   rw [← he]
   exact (w.value.map_add _ _).trans (max_le (hdiff b).le (const_le w (φ b)))
 let a :=j.toRingHom.codRestrict w.value.valuationSubring.toSubring hreg
 have ha (b:k) :a (c b)=constants w b:=Subtype.ext (j.commutes b)
 let s :B →ₐ[k] PowerSeries k :=
   ⟨f.comp a,fun b=> by
     change f (a (c b))=algebraMap k (PowerSeries k) b
     rw [ha,hc,PowerSeries.algebraMap_apply,Algebra.algebraMap_self_apply]⟩
 refine ⟨g,s,fun b=>(hval b).symm,fun b=>hfg (a b),?_⟩
 intro b
 have hz :=(hker (a (b - c (φ b)))).mpr (hdiff b)
 change PowerSeries.constantCoeff (s (b - c (φ b)))=0 at hz
 rw [map_sub,map_sub,s.commutes,PowerSeries.algebraMap_apply,
   Algebra.algebraMap_self_apply,PowerSeries.constantCoeff_C,sub_eq_zero] at hz
 exact hz
theorem proof :qZfVj1b.c3:= by
 intro Q _ J e n R A _ hF x t h
 obtain ⟨i,hi⟩:=czr.proof Q
 obtain ⟨w,hw⟩:=mark_place A hF (hi.1.transcendental ()) h
 let j:CurveRing A →ₐ[L] oO Q:=⟨incl A,incl_constant A⟩
 obtain ⟨g,s,hv,hs,hr⟩:=specialize j (yq A x t h) w hw hi
 exact ⟨⟨w,g,hv,s,hs,hr⟩⟩
end
end quwKLBd
end
section
set_option autoImplicit true
namespace q6senCe
theorem proof :qxblDlc.c3 :=
  qyEseja.proof
end q6senCe
end
section
namespace qZcMfNa
noncomputable section
open Polynomial
open cu (L)
open P5 (K)
open qBd5KZd (MarkedCurve Allowance small)
def weight {E :Type} [Field E] (u v n:ℕ) (f :E[X][X]) :ℕ :=
  f.support.sup fun i=>(f.coeff i).natDegree+n*u+i*(v-u)
def Padded {E :Type} [Field E] (u v n M:ℕ) (f :E[X][X]) :Prop :=
  f.natDegree≤n ∧
  ∀ i,f.coeff i≠0→(f.coeff i).natDegree+n*u+i*(v-u)<M
def BA {E :Type} [CommRing E] (n:ℕ) (P Q:E[X]) (f :E[X][X]) :E[X] :=
  ∑ i∈Finset.range (n+1),f.coeff i*P^i*Q^(n-i)
def roots {T:Finset K} (C:MarkedCurve T) (P Q:T→ L[X]) (m:ℕ)
    (f :C.E[X][X]) (A:Allowance C.E) :Prop :=
  ∀ t i,small (C.Ia t) ((A (C.Ia t) :ℤ)-(m:ℤ))
    ((BA f.natDegree ((P t).map (algebraMap L C.E)) ((Q t).map (algebraMap L C.E)) f).coeff i)
end
end qZcMfNa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qMskYpa
noncomputable section
open Polynomial qNu3xvc
open P5_7_1_7_4_3_4 (Pencil gauge)
open qTFhFCb (pencilOrd pencilJet chart_transition)
open private O res constIn resConst res_mem gaugeIn bad_gauge avoid bad_zero_gauge gauged_coords a1v fresh from ProximityPrize.SubmissionLower.ZYcqQEc
theorem proof :qT2dl0a.c1 := by
  intro E _ _ A hd hp ι _ w x r v _ hover
  have hpolar :=(chart_transition A hd hp).1
  let T := {0} ∪ {l | gauge A l=0}
  have hT:T.Finite :=(Set.finite_singleton _).union (bad_zero_gauge (A:=A)).finite
  obtain ⟨l,hl,hG⟩:=avoid (fun i => {l | res (v i) (gaugeIn (v i) l)=0})
    (fun i=>bad_gauge (v i)) T hT
  have hg:gauge A l≠0:= fun h=>hl (Or.inr h)
  have hcoord (i:ι) :=gauged_coords (v i) l hg hd hp (hG i) (hover i).2.2
  choose u j hu hj hn using fun i=>(hcoord i).2
  obtain ⟨b,-,hb⟩:=avoid
    (fun i => {b | resConst (v i) b*res (v i) (u i)+res (v i) (j i) ∈
      (resConst (v i)).fieldRange})
    (fun i=>a1v _ _ _ (hn i)) ∅ Set.finite_empty
  obtain ⟨a,m,hmC,hmX,hfin,hsep⟩ :=
    separating A hp (constant A b*pencilOrd A l+pencilJet A l)
  obtain ⟨N,D,hN,hD,hNh,hDh,hDe,hratio⟩:=representatives A hd a b l hg hpolar
  let C:Pencil A :=
    { num :=N,den:=D,tilt:=l,num_weight:=hN,den_weight:=hD
      num_height:=hNh,den_height:=hDh
      den_ne :=hDe.symm ▸ mul_ne_zero (pow_ne_zero _ hg) hpolar
      gauge_ne :=hg,polar_ne :=hpolar
      base :=m,base_seed :=hmC,base_X:=hmX.trans hratio.symm
      finite :=hfin,separable :=hsep }
  refine ⟨C,fun h=>hl (Or.inl h),fun i=>(hcoord i).1,fun i g hgn => ?_⟩
  let X₀:O (v i) :=⟨amm A,(v i).base_regular⟩
  let t:=constIn (v i) a*X₀+(constIn (v i) b*u i+j i)
  have ht: (t:EC A)=m RatFunc.X:= by
    change constant A a*amm A+(constant A b*(u i:EC A)+(j i:EC A))= _
    rw [hu,hj,hmX]
  rw [show C.base=m from rfl,← ht]
  refine fresh (v i) t (fun h=>hb i ?_) g hgn
  let k :=(resConst (v i)).fieldRange
  have hX:res (v i) X₀∈k :=(res_mem _ _).mpr ⟨x i,(hover i).2.1⟩
  have ha :resConst (v i) a∈k :=(resConst (v i)).mem_fieldRange_self a
  change res (v i) t∈k at h
  change _∈k
  simpa only [t,map_add,map_mul,RingHom.comp_apply,add_sub_cancel_left] using
    k.sub_mem h (k.mul_mem ha hX)
end
end qMskYpa
end
end
