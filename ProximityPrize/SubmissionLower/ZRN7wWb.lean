import ProximityPrize.SubmissionLower.BG
import ProximityPrize.SubmissionLower.ZJObpKc
import ProximityPrize.SubmissionLower.Ztd61Ce
import ProximityPrize.SubmissionLower.Z1mibXd
import ProximityPrize.SubmissionLower.ZqzGq1b
import ProximityPrize.SubmissionLower.ZzOuVbd
import ProximityPrize.SubmissionLower.ZZ2V61d
import ProximityPrize.SubmissionLower.Z4uiCKc
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Fin.forall_iff_castSucc → zy6, Fin.snoc → zBM, Fin.snoc_castSucc → zDN, Fin.snoc_last → zrK, Finset → zJe, Finset.sum_powerset_insert → z3Q, Ideal → znc, Ideal.comap_comap → zg6, Ideal.comap_injective_of_surjective → zyU, Ideal.comap_isPrime → zG1, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Ideal.subset_span → zCn
section
set_option autoImplicit true
namespace Qp
open aR yz
noncomputable def ftC (s :Shape) (h:ℕ) :ℝ :=
  (h:ℝ)*(s.t:ℝ)*((s.j:ℝ) - s.t)*((s.b:ℝ)-(s.j:ℝ)/2)
end Qp
end
section
set_option autoImplicit true
namespace Qp
noncomputable section
open aR yz MeasureTheory Set
private theorem a9x {α β:Type} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume :Measure α)]
    (e :β ≃ᵐ ℝ×α) (he :MeasurePreserving e) {C:Set β} (hC:MeasurableSet C)
    {d:ℝ} (hd : ∀ v∈C,(e v).1∈Icc 0 d) :
    volume C = ∫⁻ t in Icc 0 d,volume ((fun v=>e.symm (t,v)) ⁻¹' C) := by
  have hpre :MeasurableSet (e.symm ⁻¹' C) :=hC.preimage e.symm.measurable
  rw [← (MeasurePreserving.symm e he).measure_preimage_equiv C,Measure.volume_eq_prod,
    Measure.prod_apply hpre,← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht:t∈Icc 0 d
  · rw [indicator_of_mem ht]
    rfl
  · rw [indicator_of_notMem ht]
    have h:Prod.mk t ⁻¹' (e.symm ⁻¹' C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hv' := hd _ hv
      rw [e.apply_symm_apply] at hv'
      exact ht hv'
    rw [h,measure_empty]
private theorem fs1 {a b d:ℝ} (hd:0≤d)
    (hn : ∀ x∈Icc 0 d,0≤a+b*x) :
    (∫⁻ x in Icc 0 d,ENNReal.ofReal (a+b*x))=ENNReal.ofReal (d*a+b*d^2/2) := by
  have hi:IntegrableOn (fun x :ℝ=>a+b*x) (Icc 0 d) :=
    (show Continuous (fun x :ℝ=>a+b*x) by fun_prop).integrableOn_Icc
  have hnn : ∀ᵐ x ∂(volume :Measure ℝ).restrict (Icc 0 d),0≤a+b*x :=
    (ae_restrict_mem measurableSet_Icc).mono hn
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hd,
    intervalIntegral.integral_add
      (show IntervalIntegrable (fun _:ℝ=>a) volume 0 d from intervalIntegrable_const)
      ((show Continuous (fun x :ℝ=>b*x) by fun_prop).intervalIntegrable 0 d),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [sub_zero,smul_eq_mul,zero_pow (by decide : (2 :ℕ)≠0)]
  ring
private abbrev fbW {n:ℕ} : (Fin (n+1)→ℝ) ≃ᵐ ℝ×(Fin n→ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _=>ℝ) (Fin.last n)
private theorem fr7 {n:ℕ} (t:ℝ) (v :Fin n→ℝ) :
    fbW.symm (t,v)=zBM v t:= by
  change @Fin.insertNth n (fun _=>ℝ) (Fin.last n) t v = @zBM n (fun _=>ℝ) v t
  exact Fin.insertNth_last' t v
private def triangle (d e :ℝ) :Set (Fin 2→ℝ) :=
  {x | x 1∈Icc 0 e∧x 0∈Icc 0 (d - x 1)}
private theorem fvT {d e :ℝ} (he :0≤e) (hed:e≤d) :
    volume (triangle d e)=ENNReal.ofReal (e*d-e^2/2) := by
  let equiv : (Fin 2→ℝ) ≃ᵐ (ℝ×ℝ) :=
    (MeasurableEquiv.finTwoArrow (α:=ℝ)).trans MeasurableEquiv.prodComm
  have hpres :MeasurePreserving equiv :=
    (Measure.measurePreserving_swap (μ:=(volume :Measure ℝ)) (ν:=(volume :Measure ℝ))).comp
      (volume_preserving_finTwoArrow ℝ)
  have hm:MeasurableSet (triangle d e) := by
    have h0:Measurable (fun x :Fin 2→ℝ=>x 0) :=measurable_pi_apply 0
    have h1 :Measurable (fun x :Fin 2→ℝ=>x 1) :=measurable_pi_apply 1
    exact (measurableSet_Icc.preimage h1).inter
      ((measurableSet_le measurable_const h0).inter (measurableSet_le h0 (by fun_prop)))
  rw [a9x equiv hpres hm (fun v hv=>hv.1)]
  calc
    _ = ∫⁻ x in Icc 0 e,ENNReal.ofReal (d+(-1)*x) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hsec: (fun v :ℝ=>equiv.symm (x,v)) ⁻¹' triangle d e=Icc 0 (d - x) := by
        ext y
        change (x∈Icc 0 e∧y∈Icc 0 (d - x))↔_
        simp [hx]
      dsimp only
      rw [hsec,Real.volume_Icc]
      congr 1
      ring
    _ = _:= by
      rw [fs1 he (fun x hx=> by linarith [hx.2])]
      congr 1
      ring
private def bkw (b j c:ℝ) :Set (Fin 3→ℝ) :=
  {x | (∀ i,0≤x i)∧x 0 + x 1 + x 2≤b∧x 1+2*x 2≤j∧x 2≤ c}
private theorem frB (b j c:ℝ) :MeasurableSet (bkw b j c) := by
  have horth:MeasurableSet {x :Fin 3→ℝ | ∀ i,0≤x i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun i=>measurableSet_le measurable_const (measurable_pi_apply i))
  have hb:MeasurableSet {x :Fin 3→ℝ | x 0 + x 1 + x 2≤b} :=
    measurableSet_le (by fun_prop) measurable_const
  have hj:MeasurableSet {x :Fin 3→ℝ | x 1+2*x 2≤j} :=
    measurableSet_le (by fun_prop) measurable_const
  have ht:MeasurableSet {x :Fin 3→ℝ | x 2≤ c} :=
    measurableSet_le (measurable_pi_apply 2) measurable_const
  exact horth.inter (hb.inter (hj.inter ht))
private theorem fsM {b j c:ℝ} (hc:0≤ c) (hbj:j≤b) (hjc:2*c≤j) :
    volume (bkw b j c)=ENNReal.ofReal (c*(j - c)*(b - j/2)) := by
  have hbound (v :Fin 3→ℝ) (hv :v∈bkw b j c) : (fbW v).1∈Icc 0 c :=
    ⟨hv.1 2,hv.2.2.2⟩
  rw [a9x fbW (volume_preserving_piFinSuccAbove _ _) (frB b j c) hbound]
  calc
    _ = ∫⁻ z in Icc 0 c,ENNReal.ofReal (j*(b - j/2)+(-2*(b - j/2))*z) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro z hz
      have hsec: (fun v :Fin 2→ℝ=>fbW.symm (z,v)) ⁻¹' bkw b j c =
          triangle (b - z) (j - 2*z) := by
        ext v
        have h0: (@zBM 2 (fun _=>ℝ) v z) 0=v 0 :=
          @zDN 2 (fun _=>ℝ) z v 0
        have h1 : (@zBM 2 (fun _=>ℝ) v z) 1=v 1 :=
          @zDN 2 (fun _=>ℝ) z v 1
        have h2 : (@zBM 2 (fun _=>ℝ) v z) 2=z :=
          @zrK 2 (fun _=>ℝ) z v
        simp only [mem_preimage,fr7,bkw,triangle,mem_ofPred_eq,mem_Icc,
          zy6 (n:=2),zrK,zDN,Fin.forall_fin_two,
          h0,h1,h2]
        change ((0≤z∧0≤v 0∧0≤v 1)∧v 0+v 1+z≤b ∧
          v 1+2*z≤j∧z≤ c)↔((0≤v 1∧v 1≤j - 2*z) ∧
          0≤v 0∧v 0≤b - z - v 1)
        constructor
        · rintro ⟨⟨_,hv0,hv1⟩,hb',hj',_⟩
          exact ⟨⟨hv1,by linarith⟩,hv0,by linarith⟩
        · rintro ⟨⟨hv1,hj'⟩,hv0,hb'⟩
          exact ⟨⟨hz.1,hv0,hv1⟩,by linarith,by linarith,hz.2⟩
      dsimp only
      rw [hsec,fvT (by linarith [hz.2]) (by linarith [hz.1])]
      congr 1
      ring
    _ = _:= by
      rw [fs1 hc (fun z hz=> by
        have h1 :0≤j - 2*z := by linarith [hz.2]
        have h2 :0≤b - j/2 := by linarith
        nlinarith [mul_nonneg h1 h2])]
      congr 1
      ring
theorem fvU (s :Shape) (h:ℕ) (hs :bF s) :
    (volume (nD s h)).toReal=ftC s h:= by
  have hcap:nD s h = {x | (fun i:Fin 3=>x i.castSucc)∈bkw s.b s.j s.t ∧
      x 3∈Icc 0 (h:ℝ)} := by
    ext x
    simp only [nD,bkw,mem_ofPred_eq,mem_Icc,zy6 (n:=3)]
    change ((0≤x 3 ∧ ∀ i:Fin 3,0≤x i.castSucc) ∧
      x 0 + x 1 + x 2≤(s.b:ℝ)∧x 1+2*x 2≤(s.j:ℝ) ∧
      x 2≤(s.t:ℝ)∧x 3≤(h:ℝ)) ↔
      ((∀ i:Fin 3,0≤x i.castSucc)∧x 0 + x 1 + x 2≤(s.b:ℝ) ∧
      x 1+2*x 2≤(s.j:ℝ)∧x 2≤(s.t:ℝ))∧0≤x 3∧x 3≤(h:ℝ)
    tauto
  have hm:MeasurableSet (nD s h) := by
    rw [hcap]
    exact ((frB _ _ _).preimage
      (measurable_pi_iff.mpr (fun i=>measurable_pi_apply i.castSucc))).inter
        (measurableSet_Icc.preimage (measurable_pi_apply 3))
  have hbound (v :iz) (hv :v∈nD s h) : (fbW v).1∈Icc 0 (h:ℝ) :=
    ⟨hv.1 3,hv.2.2.2.2⟩
  have hvol:volume (nD s h) =
      volume (bkw s.b s.j s.t)*ENNReal.ofReal (h:ℝ) := by
    rw [a9x fbW (volume_preserving_piFinSuccAbove _ _) hm hbound]
    calc
      _ = ∫⁻ _ in Icc 0 (h:ℝ),volume (bkw s.b s.j s.t) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro z hz
        dsimp only
        congr 1
        ext v
        have h3: (@zBM 3 (fun _=>ℝ) v z) 3=z :=
          @zrK 3 (fun _=>ℝ) z v
        simp [hcap,fr7,h3,hz.1,hz.2]
      _ = _:= by rw [setLIntegral_const,Real.volume_Icc,sub_zero]
  have hbj: (s.j:ℝ)≤ s.b:= by exact_mod_cast hs.1
  have hjc:2*(s.t:ℝ)≤ s.j:= by exact_mod_cast hs.2
  have hn:0≤(s.t:ℝ)*((s.j:ℝ) - s.t)*((s.b:ℝ)-(s.j:ℝ)/2) := by
    have ht:0≤(s.t:ℝ) := by positivity
    exact mul_nonneg (mul_nonneg ht (by linarith)) (by linarith)
  rw [hvol,fsM (by positivity) hbj hjc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hn,ENNReal.toReal_ofReal (by positivity)]
  unfold ftC
  ring
end
end Qp
end
section
set_option autoImplicit true
namespace qS0pvXc
noncomputable section
open aR (af Shape)
open oR (Wc)
open we (eT DO fW vY graph)
open yz (oe oF Ny ay3 nD aa1)
open zP (auv aIA LK bIk ke)
open Qp (bF ftC fvU)
open P6_6 (bf LN)
open P6_6_5 (tC)
open q6t08kb (lowerMixed)
open qgLc7la (FactorBox Gf RY aIn)
open MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
open private c0v bCe bQd from ProximityPrize.SubmissionLower.BG
open private bDY efN from ProximityPrize.SubmissionLower.ZJObpKc
open private xl crv bOy from ProximityPrize.SubmissionLower.BG
open private c0p bIz from ProximityPrize.SubmissionLower.CD
open private bvn from ProximityPrize.SubmissionLower.BG
private theorem sparse {sh:Fin 4→Shape} {ht:Fin 4→ℕ}
    (hc : ∀ i,bF (sh i)) (hv : ∀ j:Fin 4,Finsupp.single j 1∈auv (sh 3) (ht 3))
    (F G E L:eT 4) (hF:DO F (sh 0) (ht 0))
    (hG:DO G (sh 1) (ht 1)) (hE :DO E (sh 2) (ht 2))
    (hL:DO L (sh 3) (ht 3)) (points :zJe oe)
    (hp : ∀ y∈points,oF y∈(ay3 F G E L).minimalPrimes) :
    (↑(∑ y∈points,(Ny (ay3 F G E L) y).toNat) :ℝ) ≤
      aa1 (fun i=>nD (sh i) (ht i)) := by
  let A (i:Fin 4) :=auv (sh i) (ht i)
  let p:Fin 4→eT 4 := ![F,G,E,L]
  have hz (i:Fin 4) :0∈A i:=bQd _ _
  have hs (i:Fin 4) : (p i).support⊆A i:= by
    intro e he
    apply aIA.mpr
    fin_cases i
    · exact hF e he
    · exact hG e he
    · exact hE e he
    · exact hL e he
  have hJ:ke p=ay3 F G E L:= by
    unfold ke ay3
    apply congrArg zye
    ext q
    simp [p,or_left_comm,or_comm]
  obtain ⟨hfin,hmv⟩:=c0v efN bak.proof A hz
    (fun i=>bCe (sh i) (ht i)) (fun j=>⟨3,hv j⟩)
  have hb (i:Fin 4) :LK (A i)=nD (sh i) (ht i) :=
    bIk _ _ (hc i).1 (hc i).2
  have h:=bDY A hz hfin p hs points (by simpa only [hJ] using hp)
  simpa only [hJ,hmv,hb] using (Nat.cast_le (α:=ℝ)).mpr h
private theorem prism_price {p g x y :Shape} (hp:bF p) (hg:bF g)
    (hx :bF x) (hy :bF y) (u v :ℕ) :
    aa1 (fun i=>nD (![p,g,x,y] i) (![0,1,u,v] i)) =
      (Wc p x y+u*Wc p g y+v*Wc p g x :ℕ) := by
  let sh:Fin 4→Shape := ![p,g,x,y]
  let ht:Fin 4→ℕ := ![0,1,u,v]
  have hch (i:Fin 4) :bF (sh i) := by
    fin_cases i <;> assumption
  change aa1 (fun i=>nD (sh i) (ht i))= _
  unfold aa1
  simp_rw [bOy _ _ _ hch,fvU _ _ (crv _ _ hch)]
  rw [show (Finset.univ :zJe (Fin 4))=insert 0 (insert 1 (insert 2 (insert 3 ∅))) by decide]
  simp only [
    z3Q (a :=(0:Fin 4)) (s :=insert 1 (insert 2 (insert 3 ∅))) (by decide),
    z3Q (a :=(1 :Fin 4)) (s :=insert 2 (insert 3 ∅)) (by decide),
    z3Q (a :=(2 :Fin 4)) (s :=insert 3 ∅) (by decide),
    z3Q (a :=(3:Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty,Finset.sum_singleton]
  simp only [Nat.cast_add,Nat.cast_mul,c0p p x y hp hx hy,
    c0p p g y hp hg hy,c0p p g x hp hg hx,
    bIz x y hx hy,bIz g y hg hy,bIz g x hg hx]
  norm_num [ftC,xl,sh,ht,Finset.sum_insert,Finset.card_insert_of_notMem]
  ring
private theorem bfa (a :Shape) (h:a.j+3≤a.b) (L:ℕ) (hL:1≤L-4) :
    bF (LN L a) := by
  let r :=L-4
  have hmul :=Nat.mul_le_mul_left r h
  change r*(a.j+2+1)≤ r*a.b at hmul
  rw [Nat.mul_add,Nat.mul_one] at hmul
  constructor
  · change 2+r*(a.j+2)≤1+r*a.b
    change 1≤ r at hL
    omega
  · change 2*min (1+r*(a.t+2)) ((2+r*(a.j+2))/2)≤2+r*(a.j+2)
    have hh:=min_le_right (1+r*(a.t+2)) ((2+r*(a.j+2))/2)
    omega
theorem point_budget {a :Shape} {f :af 3} (hf :FactorBox a f) (T:Gf a f)
    (L:eT 4) (hL:DO L (RY a) bf) (points :zJe oe)
    (hp : ∀ y∈points,
      oF y∈(ay3 (vY (fW f)) (graph f) T.cut L).minimalPrimes) :
    (∑ y∈points,(Ny (ay3 (vY (fW f)) (graph f) T.cut L) y).toNat)
      ≤ lowerMixed a := by
  let x :=LN (bf+1) a
  let y :=RY a
  have gap:=hf.gap
  have ha :bF a :=⟨by omega,by rw [hf.top_eq]; omega⟩
  have hg:bF (tC a) := by
    change a.j+1≤a.b∧2*min (a.t+1) ((a.j+1)/2)≤a.j+1
    have h:=min_le_right (a.t+1) ((a.j+1)/2)
    omega
  have hx :bF x :=bfa a gap _ (by decide)
  have hy :bF y :=bfa a gap _ (by decide)
  let sh:Fin 4→Shape := ![a,tC a,x,y]
  let ht:Fin 4→ℕ := ![0,1,bf - 1,bf]
  have hch (i:Fin 4) :bF (sh i) := by
    fin_cases i
    · exact ha
    · exact hg
    · exact hx
    · exact hy
  have hF:DO (vY (fW f)) a 0:= by
    intro e he
    obtain ⟨hB,hJ,hT,h0⟩:=bvn f e he
    exact ⟨hB.trans hf.total,hJ.trans hf.index,hT.trans hf.top,h0⟩
  have h:=sparse (ht:=ht) hch (fun j=>aIA.mpr (aIn a j))
    _ _ _ _ hF T.graph_box T.cut_box hL points hp
  have hprice :aa1 (fun i=>nD (sh i) (ht i))=(lowerMixed a :ℝ) :=
    prism_price ha hg hx hy _ _
  exact (Nat.cast_le (α:=ℝ)).mp (h.trans_eq hprice)
end
end qS0pvXc
end
section
set_option autoImplicit true
namespace qS0pvXc
noncomputable section
open aR (af Shape)
open we (eT cH DO)
open yz (oe S3 F3)
open ac0 (P5 auW bxW aYo
  bJD)
open P6_6 (bf)
open qeu0RUc (yD)
open qgLc7la (RY Wa aIn i9 pN gnI)
open MvPolynomial
open scoped Pointwise
open private epO from ProximityPrize.SubmissionLower.Z1mibXd
private abbrev afR (a :Shape) :=monomialMap cH (Wa a)
structure am9 (s :Shape) (f :af 3) where
  polynomial:eT 4
  support :DO polynomial (RY s) bf
  points :znc (eT 3)→zJe oe
  card_eq : ∀ P∈yD f,((points P).card:ℚ)=pN s f P
  proper : ∀ P∈yD f,polynomial∉F3 f P
  roots : ∀ P∈yD f,∀ y∈points P,
    y∈S3 f P∧eval y polynomial=0
  off_other_curves : ∀ P∈yD f,∀ P' ∈ yD f,P≠P' →
    ∀ y∈points P,y∉S3 f P'
private abbrev aRt (s :Shape) :=Wa s→cH
private def ave {s :Shape} (z :aRt s) :oe :=
  fun i=>z ⟨Finsupp.single i 1,aIn s i⟩
private theorem jetOf_point (s :Shape) (y :oe) :
    ave (monomialPoint (Wa s) y)=y :=
  funext fun i=>monomialPoint_single y (aIn s i)
private theorem bsL {s :Shape} {f :af 3} {P:znc (eT 3)} {z :aRt s}
    (hz :z∈zeroLocus cH (i9 s f P)) :
    monomialPoint (Wa s) (ave z)=z := by
  obtain ⟨y,hy⟩:=exists_monomialPoint_eq_of_mem_zeroLocus_ker (aIn s)
    (zeroLocus_anti_mono (Ideal.ker_le_comap (afR s)) hz)
  rw [← hy,jetOf_point]
private theorem epN {s :Shape} {f :af 3} {P:znc (eT 3)} {z :aRt s}
    (hz :z∈zeroLocus cH (i9 s f P)) :
    ave z∈zeroLocus cH (F3 f P) := by
  apply (monomialPoint_mem_zeroLocus_comap_iff (aIn s) _ _).mp
  rw [bsL hz]
  exact hz
private theorem d4a {s :Shape} {f :af 3} {P:znc (eT 3)}
    (hf :Irreducible f) (hP:P∈yD f) :
    ∃ B:zJe (aRt s),
      ∀ z∈zeroLocus cH (i9 s f P),z∉B →
        ave z∈S3 f P ∧
        ∀ Q∈yD f,P≠Q→ave z∉S3 f Q:= by
  classical
  let W:=monomialPoint (E :=cH) (qeu0RUc.Wa 0)
  obtain ⟨B,hB⟩:=qe9q5Za.d4a hP
    (qeu0RUc.gnI (v :=0) hf hP)
  refine ⟨B.image (fun u=>monomialPoint (Wa s) (qe9q5Za.ave u)),
    fun z hz hmiss => ?_⟩
  have hW:W (ave z)∈zeroLocus cH (qeu0RUc.i9 0 f P) :=
    (monomialPoint_mem_zeroLocus_comap_iff (qeu0RUc.aIn 0) _ _).mpr
      (epN hz)
  have hjet:qe9q5Za.ave (W (ave z))=ave z :=
    epO 0 _
  have hn:W (ave z)∉B:= fun hm =>
    hmiss (Finset.mem_image.mpr ⟨_,hm,by rw [hjet,bsL hz]⟩)
  simpa only [hjet] using hB _ hW hn
private theorem enz {s :Shape} (a :aRt s) (t:cH) :
    DO (afR s (P5 a-MvPolynomial.C t)) (RY s) bf := by
  have hz : (0:Fin 4 →₀ ℕ)∈Wa s := by
    change 0+0+0≤(RY s).b∧0+2*0≤(RY s).j∧0≤(RY s).t∧0≤bf
    simp
  have h:=monomialMap_mem_restrictSupport_nsmul hz (bxW a t)
  rw [one_nsmul] at h
  exact h
theorem adK (s :Shape) (f :af 3) (hf :Irreducible f) :
    Nonempty (am9 s f) := by
  classical
  have hC (P) (hP:P∈yD f) :=gnI (a :=s) hf hP
  have h1 :=aYZ.proof
  have h2 :=bRg.proof
  have h3:=bRh.proof
  let I (P:yD f) :=i9 s f P.val
  obtain ⟨degreeBad,hdegreeBad⟩:=Classical.skolem.mp fun P:yD f =>
    h1 cH (Wa s) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  obtain ⟨separationBad,hseparationBad⟩:=Classical.skolem.mp fun P:yD f =>
    h2 cH (Wa s) (I P) (hC P.val P.property).1 (hC P.val P.property).2
  let bad:=Finset.univ.biUnion fun P=>insert (separationBad P) (degreeBad P)
  obtain ⟨a,ha⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (fun V:bad=>V.val) (by
      intro V
      obtain ⟨P,_,hV⟩:=Finset.mem_biUnion.mp V.property
      rcases Finset.mem_insert.mp hV with h | h
      · rw [h]
        exact (hseparationBad P).1
      · exact (hdegreeBad P).1 _ h)
  have havoid (P:yD f) (V:Submodule cH (aRt s))
      (hV:V∈insert (separationBad P) (degreeBad P)) :a∉V :=
    ha ⟨V,Finset.mem_biUnion.mpr ⟨P,Finset.mem_univ _,hV⟩⟩
  have hdegree (P:yD f) :=
    (hdegreeBad P).2 a (fun V hV=>havoid P V (Finset.mem_insert_of_mem hV))
  obtain ⟨valueBad,hvalueBad⟩:=Classical.skolem.mp fun P:yD f =>
    h3 cH (Wa s) (I P) (hC P.val P.property).1 a (hdegree P).1
      ((hseparationBad P).2 a (havoid P _ (Finset.mem_insert_self _ _)))
  obtain ⟨pointsBad,hpointsBad⟩:=Classical.skolem.mp fun P:yD f =>
    d4a (s :=s) hf P.property
  let value (z :aRt s) :=aeval z (P5 a)
  let excludedValues :=Finset.univ.biUnion fun P=>valueBad P∪(pointsBad P).image value
  obtain ⟨t,ht⟩:=Infinite.exists_notMem_finset excludedValues
  have hmiss (P:yD f) :t∉valueBad P∪(pointsBad P).image value :=
    fun h=>ht (Finset.mem_biUnion.mpr ⟨P,Finset.mem_univ _,h⟩)
  let L:=P5 a-MvPolynomial.C t
  let J (P:znc (eT 3)) :=auW (i9 s f P) a t
  have hcut (P) (hP:P∈yD f) :
      (affineHilbertPolynomial (J P)).natDegree=0 ∧
        affineDegree (J P)=pN s f P :=
    (hdegree ⟨P,hP⟩).2 t
  have hproper (P) (hP:P∈yD f) :afR s L∉F3 f P:= by
    intro hmem
    have heq :J P=i9 s f P :=
      sup_eq_left.mpr ((zvl _).mpr hmem)
    have hz :=(hcut P hP).1
    rw [heq,(hC P hP).2] at hz
    exact Nat.one_ne_zero hz
  have hfinite (P) (hP:P∈yD f) : (zeroLocus cH (J P)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) _ (hcut P hP).1).1
  let points (P:znc (eT 3)) :zJe oe :=
    if hP:P∈yD f then (hfinite P hP).toFinset.image ave else ∅
  have hpoint (P) (hP:P∈yD f) (y) (hy :y∈points P) :
      y∈S3 f P∧eval y (afR s L)=0 ∧
        ∀ Q∈yD f,P≠Q→y∉S3 f Q:= by
    simp only [points,dite_eq_left hP] at hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    obtain ⟨hzC,hzt⟩:=aYo.mp hz'
    have ⟨hgraph,hoff⟩:=hpointsBad ⟨P,hP⟩ z hzC
      (fun hbad=>hmiss ⟨P,hP⟩ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z,hbad,hzt⟩)))
    have hev :=(mem_zeroLocus_sup_span_singleton_iff.mp hz').2
    rw [← bsL hzC,
      aeval_monomialPoint,aeval_eq_eval] at hev
    exact ⟨hgraph,hev,hoff⟩
  refine ⟨⟨afR s L,enz a t,points,?_,hproper,?_,?_⟩⟩
  · intro P hP
    have hrad:=hvalueBad ⟨P,hP⟩ t (fun ht' => hmiss ⟨P,hP⟩ (Finset.mem_union_left _ ht'))
    have hinj:Set.InjOn ave (zeroLocus cH (J P)) := by
      intro x hx y hy hxy
      rw [← bsL (aYo.mp hx).1,
        ← bsL (aYo.mp hy).1,hxy]
    simp only [points,dite_eq_left hP]
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite P hP)]
    exact (bJD (J P) (hcut P hP).1 hrad).trans (hcut P hP).2
  · intro P hP y hy
    exact ⟨(hpoint P hP y hy).1,(hpoint P hP y hy).2.1⟩
  · intro P hP Q hQ hne y hy
    exact (hpoint P hP y hy).2.2 Q hQ hne
end
end qS0pvXc
end
section
set_option autoImplicit true
namespace qsQcP6a
noncomputable section
open aR (af)
open we (eT cH fW D7 vY graph rP ag9)
open yz (oe S3 F3 ay3 oF Ny
  ahz bpz bpH)
open aA2 (sep S7 TC ad2 avJ
  cXp)
open qSCPCwb (Dm Lx BW)
open qeu0RUc (yD avw cfr)
open MvPolynomial
open private bHC from ProximityPrize.SubmissionLower.BG
open private bHx from ProximityPrize.SubmissionLower.BG
open private cT7 ddv from ProximityPrize.SubmissionLower.ZZ2V61d
open private cNE cam cGQ from ProximityPrize.SubmissionLower.A3
private theorem ctg {f :af 3} {E :eT 4}
    (hE :ag9 f (Dm f) E)
    {P:znc (eT 3)} (hP:BW f≤P) :
    Wy f E≤F3 f P:= by
  have hf (x :Fin 3→cH) (hx :x∈D7 f P) :
      eval x (fW f)=0 :=
    hx.1 _ (hP (zCn (by simp)))
  apply sup_le
  · apply Ideal.span_le.mpr
    intro u hu y hy
    obtain ⟨x,hx,rfl⟩:=hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simpa only [aeval_eq_eval,ahz] using hf x hx
    · exact bpz hx.2
  · apply (zvl _).mpr
    intro y hy
    obtain ⟨x,hx,rfl⟩:=hy
    exact (bpH hE (hf x hx) hx.2).mpr
      (hx.1 _ (hP (zCn (by simp))))
private theorem open_comap_injective {R:Type*} [CommRing R] (I:znc R) (s :R) :
    Function.Injective (Ideal.comap (ad2 I s)) := by
  intro p q h
  rw [ad2,← zg6,← zg6] at h
  exact (IsLocalization.orderEmbedding (Submonoid.powers (Ideal.Quotient.mk I s))
    (TC I s)).injective
      (zyU _ Ideal.Quotient.mk_surjective h)
private theorem chart_comap {f :af 3} {E :eT 4} (hE :ag9 f (Dm f) E)
    (q:znc (aYQ f E)) :
    (q.comap (aH6 f hE).toRingHom).comap (Nt f) =
      (q.comap (zp f E)).comap (rename z1o).toRingHom:= by
  ext a
  change aH6 f hE (Nt f a)∈q↔zp f E (vY a)∈q
  rw [bHy]
private theorem eOe {f :af 3} {E :eT 4} (hE :ag9 f (Dm f) E)
    (Q:znc (eT 4)) [Q.IsPrime] (hcut:Wy f E≤Q) (hsep:S7 f∉Q) :
    let P:= Q.comap (rename z1o).toRingHom
    BW f≤P∧F3 f P= Q:= by
  let P:= Q.comap (rename z1o).toRingHom
  let:P.IsPrime :=zG1 _ Q
  have hs :sep f∉P:=hsep
  obtain ⟨q,_,hq⟩:=cNE hcut hsep
  have hp: (q.comap (aH6 f hE).toRingHom).comap (Nt f)=P:= by
    rw [chart_comap,hq]
  have hP:BW f≤P:= by
    rw [← hp]
    intro a ha
    change aH6 f hE (Nt f a)∈q
    rw [avJ ha,map_zero]
    exact q.zero_mem
  let: (F3 f P).IsPrime :=(bHC f P hs).1
  have hrsep:S7 f∉F3 f P:= by
    change sep f∉(F3 f P).comap (rename z1o).toRingHom
    rwa [bHx hs]
  obtain ⟨r,_,hr⟩:=cNE (ctg hE hP) hrsep
  have hrq:r=q:= by
    apply zyU (aH6 f hE).toRingHom
      (aH6 f hE).surjective
    apply open_comap_injective (BW f) (sep f)
    change (r.comap (aH6 f hE).toRingHom).comap (Nt f) =
      (q.comap (aH6 f hE).toRingHom).comap (Nt f)
    rw [hp,chart_comap,hr,bHx hs]
  exact ⟨hP,hr.symm.trans (by rwa [hrq])⟩
private theorem dIo {f :af 3} {E :eT 4} (hE :ag9 f (Dm f) E)
    (P:znc (eT 3)) (Q:znc (eT 4)) [P.IsPrime] [Q.IsPrime]
    (hQ:Wy f E≤Q) (hsQ:S7 f∉Q)
    (hQP:Q.comap (rename z1o).toRingHom=P) :
    let A:=Localization.AtPrime P
    let B:=Localization.AtPrime Q
    Module.length A (A ⧸ (BW f).map (algebraMap (eT 3) A)) =
      Module.length B (B ⧸ (Wy f E).map (algebraMap (eT 4) B)) := by
  obtain ⟨q,hprime,hq⟩:=cNE hQ hsQ
  let:q.IsPrime :=hprime
  let e :=aH6 f hE
  let p:=q.comap e.toRingHom
  let:p.IsPrime :=zG1 _ q
  have hp:p.comap (Nt f)=P:= by
    change (q.comap (aH6 f hE).toRingHom).comap (Nt f)=P
    rw [chart_comap,hq,hQP]
  exact cGQ
    ((cam p hp).symm.trans
      ((Localization.localRingEquiv p q e rfl).trans (cam q hq)))
private theorem cUf {f :af 3} (hf :Irreducible f)
    {P:znc (eT 3)} (hP:P∈yD f) :
    (F3 f P).IsPrime∧(affineHilbertPolynomial (F3 f P)).natDegree=1 := by
  obtain ⟨hm,hs⟩:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  let:P.IsPrime :=hm.isPrime
  obtain ⟨hp,hdim⟩:=bHC f P hs
  exact ⟨hp,hdim.trans (cfr hf hP)⟩
private theorem eMq {f :af 3} (hf :Irreducible f)
    {E L:eT 4} (hE :ag9 f (Dm f) E)
    (hL : ∀ P∈yD f,L∉F3 f P)
    {P:znc (eT 3)} (hP:P∈yD f) {y :oe}
    (hy :y∈S3 f P) (hLy :eval y L=0) :
    oF y∈(Wy f E ⊔ zye {L}).minimalPrimes := by
  let m:=oF y
  have hmsep:S7 f∉m:=ddv hy
  obtain ⟨hProper,hRet⟩:=avw.mp hP
  have hBm:Wy f E≤ m :=
    (ctg hE (Ideal.mem_retainedMinimalPrimes.mp hRet).1.le).trans
      (cT7 hy)
  have hmL:L∈m:=(mem_vanishingIdeal_singleton_iff _ _).mpr hLy
  refine ⟨⟨inferInstance,sup_le hBm ((zvl _).mpr hmL)⟩,?_⟩
  intro Q hQ hQm
  let q:= Q.comap (rename z1o).toRingHom
  have hQsep:S7 f∉Q:= fun h=>hmsep (hQm h)
  let:Q.IsPrime :=hQ.1
  let:q.IsPrime :=hQ.1.comap _
  obtain ⟨hIq,hGQ⟩:=eOe hE Q (le_sup_left.trans hQ.2) hQsep
  have hsq:sep f∉q:=hQsep
  obtain ⟨P',hP',hP'q⟩:=Ideal.exists_mem_retainedMinimalPrimes_le (Q:=q) hIq hsq
  have hP'f :P' ∈ yD f :=avw.mpr ⟨hProper,hP'⟩
  have hle :F3 f P' ≤ Q:= by
    rw [← hGQ]
    exact vanishingIdeal_anti_mono
      (Set.image_mono fun _ hx=>⟨zeroLocus_anti_mono hP'q hx.1,hx.2⟩)
  obtain ⟨hp',hd⟩:=cUf hf hP'f
  have hLQ:zye {L} ≤ Q:=le_sup_right.trans hQ.2
  have hcut:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp' (hL P' hP'f) le_rfl).1
  rw [hd,Nat.sub_self] at hcut
  have hdeg:=(natDegree_affineHilbertPolynomial_le_of_le (sup_le hle hLQ)).trans hcut
  let:Module.Finite cH (eT 4 ⧸ Q) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  have hfield :IsField (eT 4 ⧸ Q) :=
    isField_of_isIntegral_of_isField' (R:=cH) (Field.toIsField _)
  exact (Ideal.Quotient.maximal_of_isField Q hfield).eq_of_le
    (inferInstance :m.IsPrime).ne_top hQm |>.ge
theorem bKS {f :af 3} (hf :Irreducible f) {E L:eT 4}
    (hE :ag9 f (Dm f) E)
    (hL : ∀ P∈yD f,L∉F3 f P)
    {P:znc (eT 3)} (hP:P∈yD f) {y :oe}
    (hy :y∈S3 f P) (hLy :eval y L=0) :
    let J:=ay3 (vY (fW f)) (graph f) E L
    oF y∈J.minimalPrimes∧Lx f P≤Ny J y := by
  have hJ:ay3 (vY (fW f)) (graph f) E L =
      Wy f E ⊔ zye {L} := by
    simp [ay3,Wy,rP,Ideal.span_insert,sup_assoc]
  rw [hJ]
  refine ⟨eMq hf hE hL hP hy hLy,?_⟩
  obtain ⟨hmin,hsep⟩:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  let:P.IsPrime :=hmin.isPrime
  let Q:=F3 f P
  let:Q.IsPrime :=(cUf hf hP).1
  have hQy :Q≤oF y :=cT7 hy
  have hLiftSep:S7 f∉Q:= fun h=>ddv hy (hQy h)
  rw [Lx,dite_eq_left hmin.isPrime]
  rw [dIo hE P Q (ctg hE hmin.le) hLiftSep (bHx hsep)]
  exact cXp hQy
    ((mem_vanishingIdeal_singleton_iff _ _).mpr hLy) (hL P hP)
theorem proof :qeu0RUc.c2 :=
  fun _ _ hf T _ hL _ hP _ hy hLy=>bKS hf T.cut_represents hL hP hy hLy
end
end qsQcP6a
end
section
set_option autoImplicit true
namespace qS0pvXc
open we (fW vY graph)
open yz (oF Ny ay3 bsa)
open qSCPCwb (Lx)
open qeu0RUc (yD)
open qsQcP6a (bKS)
open Finset
open scoped BigOperators
theorem proof :qgLc7la.c1 := by
  classical
  intro a f hf T
  obtain ⟨S⟩:=adK a f hf.irreducible
  let J:=ay3 (vY (fW f)) (graph f) T.cut S.polynomial
  let points :=(yD f).biUnion S.points
  have hlocal (P) (hP:P∈yD f) (y) (hy :y∈S.points P) :
      oF y∈J.minimalPrimes∧Lx f P≤Ny J y := by
    obtain ⟨hgraph,hroot⟩:=S.roots P hP y hy
    exact bKS hf.irreducible T.cut_represents S.proper hP hgraph hroot
  have hmin (y) (hy :y∈points) :oF y∈J.minimalPrimes := by
    obtain ⟨P,hP,hyP⟩:=mem_biUnion.mp hy
    exact (hlocal P hP y hyP).1
  have hd:Set.PairwiseDisjoint (↑(yD f)) S.points := by
    intro P hP Q hQ hne
    apply disjoint_left.mpr
    intro y hy hy'
    exact S.off_other_curves P hP Q hQ hne y hy (S.roots Q hQ y hy').1
  have hsum: (∑ P∈yD f,(Lx f P).toNat*(S.points P).card) ≤
      ∑ y∈points,(Ny J y).toNat := by
    change _ ≤ ∑ y∈(yD f).biUnion S.points,(Ny J y).toNat
    rw [sum_biUnion hd]
    apply sum_le_sum
    intro P hP
    calc
      _ = ∑ _∈S.points P,(Lx f P).toNat := by simp [Nat.mul_comm]
      _≤_:=sum_le_sum fun y hy=>ENat.toNat_le_toNat (hlocal P hP y hy).2
        (bsa (hlocal P hP y hy).1).ne
  have hbudget:=hsum.trans (point_budget hf T S.polynomial S.support points hmin)
  refine le_trans (le_of_eq ?_) (Nat.cast_le.mpr hbudget)
  rw [Nat.cast_sum]
  exact sum_congr rfl fun P hP=> by rw [Nat.cast_mul,S.card_eq P hP]
end qS0pvXc
end
