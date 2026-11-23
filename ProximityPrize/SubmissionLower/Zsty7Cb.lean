import ProximityPrize.SubmissionLower.ZY07HEa
import ProximityPrize.SubmissionLower.ZbvbtFa
import ProximityPrize.SubmissionLower.Z3BdPPe
set_option Elab.async false
set_option autoImplicit true
namespace qsnQ6jb
noncomputable section
open P6_6 (pair32 bf)
open P6_6_7 (Context cutterBody firstSlot genericOrder)
open qAzl5me (memberTest)
open qCj6p1d
open aR (ao af Shape aO qP shape extend)
open dN (GeoField GeoJets oA An kC bC)
open vS (g9 agB JV bTT tC)
open B8 (bF Component MH TB Ro bA1 cylinder
  bZD aC0 tW qK oF i9)
open NU (RW)
open aeM (FH azb aco)
open bjX (bZC ccZ bZB cKZ)
open private NU.btG from ProximityPrize.SubmissionLower.CE
open private NU.cKY from ProximityPrize.SubmissionLower.Z3BdPPe
open private B8.A9 from ProximityPrize.SubmissionLower.BI
open private NU.cH7 from ProximityPrize.SubmissionLower.CE
open private qCj6p1d.A9 from ProximityPrize.SubmissionLower.ZkoLWnc
open private qduj6fa.physical_chamber from ProximityPrize.SubmissionLower.ZY07HEa
def c1 :Prop := ∀ g:af 4,GraphLaws g
def c2 :Prop :=
  ∀ {R G ell} (b:Branch R G ell) (E :g9),GraphLaws b.g →
    (Iu b.g b.aI).IsPrime→TB (Iu b.g b.aI) 2 →
    Associated (yu b.g E) (qR b.g (bC (memberTest b.g))) →
    E∉Iu b.g b.aI ∧
      Component (Iu b.g b.aI) E (Iu b.g b.curve) b.demandWeight ∧
      TB (Iu b.g b.curve) 1
def c3:Prop :=
  ∀ (R:af 4) (r q p:Shape),R≠0→aO (shape R) r→bF q→bF p →
    1<p.t → ¬ aRQ p →
    32*tW (boxes q p) (a4d R) {1, 2,3,4} ≤ (pair32 true p r q:ℚ)
def c4 :Prop :=
  ∀ (R:af 4) (r q p:Shape),R≠0→aO (shape R) r→bF q→bF p →
    1<p.t→aRQ p →
    32*RW (boxes q p) (a4d R) {1, 2,3,4} ≤ (pair32 true p r q:ℚ)
private theorem bIi (q p:Shape) :
    1≤(boxes q p 4).1.b∧3≤(boxes q p 4).1.j∧1≤(boxes q p 4).1.t ∧
      1≤(boxes q p 4).2 := by
  let H :=4+(bf+2 - 5)*(p.j - 2)
  change 1≤ max _ H∧3≤H∧1≤ min _ (H/3)∧1≤bf+2
  have hH :4≤H :=Nat.le_add_right _ _
  refine ⟨(by omega :1≤H).trans (le_max_right _ _),by omega,
    le_min ?_ (by omega),by decide⟩
  omega
private theorem product_admissible (q p:Shape) (hq:bF q) :
    B8.Admissible (boxes q p) := by
  constructor
  · intro i
    fin_cases i
    · exact show bF ⟨5,4,1⟩ from ⟨by decide,by decide⟩
    · exact hq
    · change p.j+1≤ max p.b (p.j+1) ∧
        3*min (p.t+1) ((p.j+1)/3)≤p.j+1
      have ht:=min_le_right (p.t+1) ((p.j+1)/3)
      exact ⟨le_max_right _ _,by omega⟩
    · exact B8.A9 _ _
    · exact B8.A9 _ _
  · intro v
    refine ⟨4,?_⟩
    obtain ⟨hb,hj,ht,hd⟩:=bIi q p
    apply B8.blp
    change 1≤2*(boxes q p 4).1.b∧3≤2*(boxes q p 4).1.j ∧
      1≤2*(boxes q p 4).1.t∧1≤2*(boxes q p 4).2
    omega
private theorem unclips {p:Shape} (h:aRQ p) :
    azb p=tC p ∧
      aco (bf+1) p=qP (bf+1) p ∧
      aco (bf+2) p=qP (bf+2) p:= by
  obtain ⟨hg,_,hu,hv,_,_⟩:=h
  have hG:p.t+1≤(p.j+1)/3:= by omega
  have hl (L:ℕ) (hL:3*(2+(L - 5)*p.t)≤(qP L p).j) :
      aco L p=qP L p:= by
    have htop:2+(L - 5)*p.t≤(4+(L - 5)*(p.j - 2))/3:= by
      change 3*(2+(L - 5)*p.t)≤4+(L - 5)*(p.j - 2) at hL
      omega
    simp only [aco,qP,min_eq_left htop]
  exact ⟨by simp only [azb,tC,min_eq_left hG],hl _ hu,hl _ hv⟩
private theorem joint_admissible (q p:Shape) (hq:bF q) (h:aRQ p) :
    NU.Admissible (boxes q p) := by
  have hch:=(product_admissible q p hq).1
  have hg:=(unclips h).1
  obtain ⟨_,hG,_,_,hU,hV⟩:=h
  refine ⟨fun i=>⟨hch i,?_⟩,?_⟩
  · fin_cases i
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · change 2≤(tC p).t
      rw [← hg]
      exact hG
    · exact hU
    · exact hV
  · intro v
    obtain ⟨hb,_,_,hz⟩:=bIi q p
    have hj:=(hch 4).2
    have ht:2*(boxes q p 4).2≤(boxes q p 4).1.t:=hV
    exact NU.cH7 ⟨hb,by omega,by omega,hz⟩ v
private def ZO {R G ell} (b:Branch R G ell) (U:Polynomial ao) :Fin 5→GeoField:= by
  classical
  exact if h:b.dY U then fun i=>afU b.g U h.2.2 (MvPolynomial.X i)
    else Fin.lastCases 0 (JV U)
private theorem regularEval_old (g:af 4) (U:Polynomial ao) (h:An U (sigma g)≠0)
    (D:GeoJets) :aJf g U h (qR g D)=An U D :=
  IsLocalization.Away.lift_eq (sigma g) (isUnit_iff_ne_zero.mpr h) D
private theorem b10 {R G ell} (b:Branch R G ell) (U:Polynomial ao)
    (h:b.dY U) :MvPolynomial.eval (ZO b U)=afU b.g U h.2.2 := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [afU,yu,regularEval_old,An]
  · intro i
    simp [ZO,h]
private theorem b7H {R G ell} (b:Branch R G ell) (U:Polynomial ao)
    (h:b.dY U) (i:Fin 4) :ZO b U i.castSucc=JV U i:= by
  simp [ZO,h,afU,yu,regularEval_old,An,JV]
private theorem cXV {R G ell} (b:Branch R G ell) (U:Polynomial ao)
    (h:b.dY U) :Iu b.g b.curve≤oF (ZO b U) := by
  have hk :b.a5x≤RingHom.ker (aJf b.g U h.2.2) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro D hD
    change aJf b.g U h.2.2 (qR b.g D)=0
    rw [regularEval_old]
    exact h.1 hD
  intro D hD
  change MvPolynomial.eval (ZO b U) D =0
  rw [b10 b U h]
  exact hk hD
private structure aYw (cap:Fin 5→ g9→Prop)
    (degree :Ideal g9→Finset (Fin 5)→ℚ) :Prop where
  cut : ∀ (P:Ideal g9) (I:Finset (Fin 5)) (i:Fin 5),
    i∉I→MH P (I.card+1) →
    ∀ (D:g9),cap i D→ IsLeftRegular (Ideal.Quotient.mk P D) →
      degree (i9 P D) I≤degree P (insert i I)
  cycle : ∀ (J:Ideal g9) (I:Finset (Fin 5)),MH J I.card →
    ∀ {ι:Type} (S:Finset ι) (C:ι→ Ideal g9) (w:ι→ℕ),
      Set.InjOn C (S:Set ι) →
      (∀ a∈S,∃ h:J.IsMinimalPrime (C a),(w a :ℕ∞)≤Ro J (C a) h.isPrime) →
      (∑ a∈S,(w a :ℚ)*degree (C a) I)≤degree J I
private theorem aYw.divisor {cap degree} (h:aYw cap degree)
    (P:Ideal g9) (I:Finset (Fin 5)) (i:Fin 5)
    (hP:P.IsPrime) (hi:i∉I) (hd:TB P (I.card+1))
    (D:g9) (hD:cap i D) (hprop:D∉P)
    {ι:Type} (S:Finset ι) (C:ι→ Ideal g9) (w:ι→ℕ)
    (hinj:Set.InjOn C (S:Set ι)) (hcomp : ∀ a∈S,Component P D (C a) (w a)) :
    (∑ a∈S,(w a :ℚ)*degree (C a) I)≤degree P (insert i I) := by
  let:=hP
  have hr :IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle :MH P (I.card+1) :=le_of_eq hd
  exact (h.cycle (i9 P D) I (aC0 hr hdle) S C w hinj
    (fun a ha=>⟨(hcomp a ha).minimal,(hcomp a ha).length_le⟩)).trans
    (h.cut P I i hi hdle D hD hr)
private def cAf (cap:g9→Prop)
    (degree :Ideal g9→Finset (Fin 5)→ℚ) :Prop :=
  ∀ (D:Ideal g9),D.IsPrime→TB D 1 →
    ∀ (U:Finset (Fin 5→GeoField)),(∀ z∈U,D ≤oF z) →
      (U.card≤1 ∨ ∃ E,cap E∧E∉D ∧ ∀ z∈U,MvPolynomial.eval z E=0) →
      (U.card:ℚ)≤degree D {4}
private theorem dzH {cap degree} {C:Context} {R G ell p} (hpoint :cAf cap degree)
    (b:Branch R G ell) (T:Finset P6.K) (hΔ:T⊆C.Δ)
    (hT : ∀ γ∈T,b.dY (extend (C.s γ))) (hSlice :bMD p b C.s T)
    (support : ∀ D,FH (aco (bf+2) p) (bf+2) D→cap D)
    (hprime : (Iu b.g b.curve).IsPrime) (hdim:TB (Iu b.g b.curve) 1) :
    (T.card:ℚ)≤degree (Iu b.g b.curve) {4} := by
  classical
  let U:=T.image (fun γ=>ZO b (extend (C.s γ)))
  have hcard:U.card=T.card:=Finset.card_image_of_injOn (by
    intro x hx y hy he
    apply C.messages.distinct (hΔ hx) (hΔ hy)
    apply Polynomial.map_injective aR.embed aR.embed.injective
    apply bTT
    funext i
    have hz :=congrFun he i.castSucc
    change ZO b (extend (C.s x)) i.castSucc =
      ZO b (extend (C.s y)) i.castSucc at hz
    rwa [b7H b _ (hT x hx),b7H b _ (hT y hy)] at hz)
  rw [← hcard]
  apply hpoint _ hprime hdim U
  · intro z hz
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
    exact cXV b _ (hT y hy)
  · rcases hSlice with hsingle | ⟨D,hD,hproper,hvanish⟩
    · exact Or.inl (hcard ▸ hsingle)
    · refine Or.inr ⟨D,support D hD,hproper,?_⟩
      intro z hz
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
      rw [b10 b _ (hT y hy)]
      exact hvanish y hy (hT y hy)
private theorem eoo {cap degree} (h:aYw cap degree)
    (R G:af 4) (ell:ℕ) (hf :Irreducible R) (hQ : ¬ R∣G)
    (hboxQ:cap 1 (qK (bC G))) (S:Finset (Ideal GeoJets))
    (hS : ∀ P∈S,∃ h: (kC R G).IsMinimalPrime P,
      (↑(ell*genericOrder R P) :ℕ∞)≤oA (kC R G) P h.isPrime) :
    (∀ P∈S,(cylinder P).IsPrime∧TB (cylinder P) 3) ∧
      (∑ P∈S,(↑(ell*genericOrder R P) :ℚ)*degree (cylinder P) {2,3,4}) ≤
        degree (a4d R) {1, 2,3,4} := by
  let A:=a4d R
  let J:=i9 A (qK (bC G))
  obtain ⟨hregQ,hAlgebra⟩:=bZC R G hf hQ
  have hregR:IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal g9)
      (qK (bC R))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (P6_6_7_3.agr hf.ne_zero)
  have hAdim:MH A 4 :=aC0 hregR bA1
  have hJdim:MH J 3:=aC0 hregQ hAdim
  have hgeom (P:Ideal GeoJets) (hP:P∈S) :
      (cylinder P).IsPrime∧TB (cylinder P) 3 ∧
        ∃ hc:J.IsMinimalPrime (cylinder P),
          (↑(ell*genericOrder R P) :ℕ∞)≤Ro J (cylinder P) hc.isPrime := by
    obtain ⟨hs,hw⟩:=hS P hP
    obtain ⟨hd,hc,hl⟩:=hAlgebra P hs
    exact ⟨hc.isPrime,hd,hc,hw.trans hl⟩
  refine ⟨fun P hP=>⟨(hgeom P hP).1,(hgeom P hP).2.1⟩,?_⟩
  have hs :=h.cycle J {2,3,4} hJdim S cylinder (fun P=>ell*genericOrder R P)
    bZD.injOn (fun P hP=>(hgeom P hP).2.2)
  exact hs.trans (h.cut A {2,3,4} 1 (by decide) hAdim _ hboxQ hregQ)
private theorem dlW {cap degree} (aq2 :aYw cap degree)
    (hpoint :cAf (cap 4) degree) (hgraph:c1) (hmember :c2)
    {C:Context} {R G:af 4} {ell:ℕ} {p:Shape} (hf :Irreducible R) (hQ : ¬ R∣G)
    (hboxQ:cap 1 (qK (bC G)))
    (F:Finset (Branch R G ell)) (T:Branch R G ell→Finset P6.K) (hSame :SameChart F)
    (hF : ∀ b∈F,Nonempty (Member5 b.g p)∧bMD p b C.s (T b) ∧
      T b⊆C.Δ ∧ ∀ γ∈T b,b.dY (extend (C.s γ)))
    (hgcap : ∀ D,FH (azb p) 1 D→cap 2 D)
    (hmcap : ∀ D,FH (aco (bf+1) p) (bf+1) D→cap 3 D)
    (hscap : ∀ D,FH (aco (bf+2) p) (bf+2) D→cap 4 D) :
    (demandCost F T:ℚ)≤degree (a4d R) {1, 2,3,4} := by
  classical
  let S:=F.image Branch.aI
  let RS (P:Ideal GeoJets) :=F.filter fun b=>b.aI=P
  let charge (b:Branch R G ell) :ℚ:=(b.demandWeight:ℚ)*(T b).card
  let weight (P:Ideal GeoJets) :ℚ:=(↑(ell*genericOrder R P) :ℚ)
  obtain ⟨hZ,hsumZ⟩:=eoo aq2 R G ell hf hQ hboxQ S (by
    intro P hP
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hP
    exact ⟨b.base,b.gH⟩)
  have hfibre (P:Ideal GeoJets) (hP:P∈S) :
      (∑ c∈RS P,charge c)≤degree (cylinder P) {2,3,4} := by
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hP
    let liftedSurface :=Iu b.g b.aI
    let D (c:Branch R G ell) :=Iu c.g c.curve
    obtain ⟨E⟩:=(hF b hb).1
    obtain ⟨hZprime,hZdim⟩:=hZ _ hP
    have hσ:sigma b.g∉b.aI :=
      fun hm=>b.regular (le_sup_left.trans b.member.minimal.le hm)
    obtain ⟨hproperG,hGraph,hGdim⟩ :=
      (hgraph b.g).component b.aI b.base.isPrime hσ hZprime hZdim
    have hC (c:Branch R G ell) (hc:c∈RS b.aI) :
        E.polynomial∉liftedSurface ∧
          Component liftedSurface E.polynomial (D c) c.demandWeight∧TB (D c) 1 := by
      obtain ⟨hcF,hcs⟩:=Finset.mem_filter.mp hc
      have hcg:=hSame c hcF b hb hcs
      have he :Iu c.g c.aI=liftedSurface := by rw [hcg,hcs]
      rw [← he]
      exact hmember c E.polynomial (hgraph c.g) (he.symm ▸ hGraph.minimal.isPrime)
        (he.symm ▸ hGdim) (by rw [hcg]; exact E.aEA)
    have hb' : b∈RS b.aI:=Finset.mem_filter.mpr ⟨hb,rfl⟩
    have inj:Set.InjOn D (RS b.aI:Set (Branch R G ell)) := by
      intro c hc d hd he
      obtain ⟨hcF,hcs⟩:=Finset.mem_filter.mp hc
      obtain ⟨hdF,hds⟩:=Finset.mem_filter.mp hd
      have hs :=hcs.trans hds.symm
      apply Branch.b1G hs (hSame c hcF d hdF hs)
      rw [← (hgraph c.g).comap c.curve c.member.minimal.isPrime c.regular,
        ← (hgraph d.g).comap d.curve d.member.minimal.isPrime d.regular]
      exact congrArg (Ideal.comap qK) he
    calc
      _ ≤ ∑ c∈RS b.aI,(c.demandWeight:ℚ)*degree (D c) {4} := by
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨_,hs,hΔ,hon⟩:=hF c (Finset.mem_filter.mp hc).1
        obtain ⟨_,hcomp,hdim⟩:=hC c hc
        exact mul_le_mul_of_nonneg_left
          (dzH hpoint c (T c) hΔ hon hs hscap hcomp.minimal.isPrime hdim) (Nat.cast_nonneg _)
      _≤degree liftedSurface {3,4} :=
        aq2.divisor liftedSurface {4} 3 hGraph.minimal.isPrime (by decide) hGdim
          E.polynomial (hmcap _ E.fits) (hC b hb').1 (RS b.aI) D Branch.demandWeight inj
          (fun c hc=>(hC c hc).2.1)
      _≤degree (cylinder b.aI) {2,3,4} := by
        have h:=aq2.divisor (cylinder b.aI) {3,4} 2 hZprime (by decide) hZdim
          (graph b.g) (hgcap _ E.graph_fits) hproperG {liftedSurface} id (fun _=>1) (fun _ _ _ _ h=>h) (by
            intro P hP
            obtain rfl :=Finset.mem_singleton.mp hP
            exact hGraph)
        simpa only [Finset.sum_singleton,Nat.cast_one,one_mul,id_eq] using h
  calc
    _ = ∑ P∈S,weight P * ∑ c∈RS P,charge c:= by
      calc
        _ = ∑ c∈F,weight c.aI*charge c:= by
          simp only [demandCost,Nat.cast_sum,Nat.cast_mul,weight,charge,Branch.weight]
        _ = ∑ P∈S,∑ c∈RS P,weight c.aI*charge c :=
          (Finset.sum_fiberwise_of_maps_to (t:=S) (g:=Branch.aI)
            (fun b hb=>Finset.mem_image_of_mem Branch.aI hb) _).symm
        _ = _:= by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun P _=>Finset.sum_congr rfl fun c hc=> by
            rw [(Finset.mem_filter.mp hc).2]
    _ ≤ ∑ P∈S,weight P*degree (cylinder P) {2,3,4} :=
      Finset.sum_le_sum fun P hP=>mul_le_mul_of_nonneg_left (hfibre P hP) (Nat.cast_nonneg _)
    _≤_:=hsumZ
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qCj6p1d.c5:= by
  intro C R G ell cs h F T p ht hSame hF
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  let B:=boxes q p
  have hp:bF p:=qCj6p1d.A9 h
  have hq:bF q:=qduj6fa.physical_chamber C.v ell
  have hr :aO (shape R) r := by
    cases cs
    · exact ⟨le_rfl,le_rfl,le_rfl⟩
    · exact ⟨le_max_left _ _,le_rfl,le_rfl⟩
  have done {d:ℚ} (hcost: (demandCost F T:ℚ)≤d) (hdeg:32*d≤(pair32 true p r q:ℚ)) :
      (32 :ℤ)*(demandCost F T:ℤ)≤pair32 true p r q:= by
    exact_mod_cast (mul_le_mul_of_nonneg_left hcost (by norm_num : (0:ℚ)≤32)).trans hdeg
  by_cases hguard :aRQ p
  · have hB:=joint_admissible q p hq hguard
    obtain ⟨hg,hm,hs⟩:=unclips hguard
    let cap (i:Fin 5) :=FH (B i).1 (B i).2
    have aq2 :aYw cap (RW B) :=
      ⟨aKL.proof B hB,@aZB.proof B hB⟩
    have hD:=NU.cKY aKL.proof aZB.proof
    exact done (dlW aq2 (NU.btG hD B hB) h1 h2 h.factor.1 h.proper
      (NU.b99 h.H6) F T hSame hF
      (fun _ hD => by rw [hg] at hD; exact hD)
      (fun _ hD => by rw [hm] at hD; exact hD)
      (fun _ hD => by rw [hs] at hD; exact hD))
      (h4 R r q p h.factor.1.ne_zero hr hq hp ht hguard)
  · have hB:=product_admissible q p hq
    let cap (i:Fin 5) :=agB (B i).1 (B i).2
    have aq2 :aYw cap (tW B) :=
      ⟨ccZ B hB,@bZB B hB⟩
    exact done (dlW aq2
      (B8.btG cKZ B hB (bIi q p)) h1 h2 h.factor.1 h.proper
      (B8.bJT h.H6) F T hSame hF
      (fun _ hD =>ac7.FH.ctq hD) (fun _ hD =>ac7.FH.ctq hD)
      (fun _ hD =>ac7.FH.ctq hD)) (h3 R r q p h.factor.1.ne_zero hr hq hp ht hguard)
end
end qsnQ6jb
