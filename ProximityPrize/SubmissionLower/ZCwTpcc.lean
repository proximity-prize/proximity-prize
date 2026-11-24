import ProximityPrize.SubmissionLower.L
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.ZqzGq1b
set_option Elab.async false
section
set_option autoImplicit true
namespace bRj
noncomputable section
open aR oR yz Qp aeB
open MeasureTheory Set Filter
open scoped Topology Pointwise ENNReal
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
    fbW.symm (t,v)=Fin.snoc v t:= by
  change @Fin.insertNth n (fun _=>ℝ) (Fin.last n) t v = @Fin.snoc n (fun _=>ℝ) v t
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
        have h0: (@Fin.snoc 2 (fun _=>ℝ) v z) 0=v 0 :=
          @Fin.snoc_castSucc 2 (fun _=>ℝ) z v 0
        have h1 : (@Fin.snoc 2 (fun _=>ℝ) v z) 1=v 1 :=
          @Fin.snoc_castSucc 2 (fun _=>ℝ) z v 1
        have h2 : (@Fin.snoc 2 (fun _=>ℝ) v z) 2=z :=
          @Fin.snoc_last 2 (fun _=>ℝ) z v
        simp only [mem_preimage,fr7,bkw,triangle,mem_ofPred_eq,mem_Icc,
          Fin.forall_iff_castSucc (n:=2),Fin.snoc_last,Fin.snoc_castSucc,Fin.forall_fin_two,
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
private def Ca (s :Shape) :Fin 6→ℝ := ![s.b,s.j,s.t,0,0,0]
private abbrev aBV:=Fin 6×Fin 6
private def bfO (p:aBV) :Prop :=
  p.1.val<3∧p.1≠p.2∧(p.1≠2∨p.2≠5)
private instance (p:aBV) :Decidable (bfO p) := by
  unfold bfO
  infer_instance
private def remaining (p:aBV) :Fin 4 :=
  (![![0,2,1,2,2,1],![2,0,0,2,0,0],![1,0,0,1,0,0],0,0,0] :
    Fin 6→Fin 6→Fin 4) p.1 p.2
end
end bRj
end
section
set_option autoImplicit true
namespace q5Xvxxc
noncomputable section
open aR (Shape)
open oR (S9)
open yz (iz nD aa1)
open Qp (OE bF)
open aeB (UB V9 WA ajg
  apK rest bPu biT)
open axb (bWo bXo)
open P6_6 (m6 mW LN bf)
open P6_6_5 (tC a5C)
open qeu0RUc (RY T7 a5D F4 bfa)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology
open private xl crv bOy aTp from ProximityPrize.SubmissionLower.BG
open private b7c c4T from ProximityPrize.SubmissionLower.AH
open private weights c4t from ProximityPrize.SubmissionLower.BG
open private bPM from ProximityPrize.SubmissionLower.BG
open private bhH from ProximityPrize.SubmissionLower.CD
variable (v :ℕ)
def aur :Fin 4→Shape := ![mW v,tC (mW v),LN (bf+1) (mW v),RY v]
def aTk :Fin 4→ℕ := ![0,1,bf - 1,bf]
abbrev aS5 (S:Finset (Fin 4)) :Shape :=xl S (aur v)
def aGI (S:Finset (Fin 4)) :ℕ := ∑ i∈S,aTk i
private def base (S:Finset (Fin 4)) :Set iz :=
  nD (aS5 v S) (aGI S)
private def slots (P:Set iz) :Fin 4→Set iz :=
  Function.update (fun i=>nD (aur v i) (aTk i)) 0 P
private theorem bJi (P:Set iz) :T7 v P=aa1 (slots v P) := by
  unfold T7
  congr 1
  funext i
  fin_cases i <;> rfl
theorem aCu (i:Fin 4) :bF (aur v i) := by
  fin_cases i
  · exact a5D v
  · exact F4 v
  · exact bfa v _ (by decide)
  · exact bfa v _ (by decide)
private theorem cDA (i:Fin 4) : (aur v i).j<(aur v i).b:= by
  have hb: (mW v).j+3≤(mW v).b:=le_max_right _ _
  have lift_lt (L:ℕ) (hL:2≤L-4) :
      (LN L (mW v)).j<(LN L (mW v)).b:= by
    let r :=L-4
    have h:=Nat.mul_le_mul_left r hb
    change r*((mW v).j+2+1)≤ r*(mW v).b at h
    rw [Nat.mul_add,Nat.mul_one] at h
    change 2≤ r at hL
    change 2+r*((mW v).j+2)<1+r*(mW v).b
    omega
  fin_cases i
  · change (mW v).j<(mW v).b
    omega
  · change (mW v).j+1<(mW v).b
    omega
  · exact lift_lt _ (by decide)
  · exact lift_lt _ (by decide)
private theorem cDC (hv :v≤ m6.t) (i:Fin 4) :0<(aur v i).t:= by
  have hj:2≤(mW v).j:= by
    change 2≤56-3*v
    change v≤16 at hv
    omega
  have lift_pos (L:ℕ) :0<(LN L (mW v)).t:= by
    change 0< min (1+(L-4)*((mW v).t+2))
      ((2+(L-4)*((mW v).j+2))/2)
    exact lt_min (by omega) (by omega)
  fin_cases i
  · change 0<(mW v).j/2
    omega
  · change 0< min ((mW v).t+1) (((mW v).j+1)/2)
    exact lt_min (by omega) (by omega)
  · exact lift_pos _
  · exact lift_pos _
private theorem deL (P:Set iz) (hP:OE P)
    (i:Fin 4) :0∈slots v P i:= by
  by_cases hi:i=0
  · simpa [slots,hi] using hP.zero_mem
  · simp [slots,Function.update_of_ne hi,nD]
private theorem gLl (P:Set iz) (hP:OE P) :
    ∃ p:MvPolynomial (Fin 4) ℝ,p.IsHomogeneous 4 ∧
      ∀ w:Fin 4→ℝ,(∀ i,0≤w i) →
        p.eval w=(volume (∑ i,w i•slots v P i)).toReal:= by
  classical
  have hslot (i:Fin 4) :
      ∃ vertices :Finset iz,slots v P i=convexHull ℝ (vertices :Set iz) := by
    by_cases hi:i=0
    · subst i
      obtain ⟨s,hs,hr⟩:=hP.polytope
      exact ⟨hs.toFinset,by simpa [slots] using hr⟩
    · rw [slots,Function.update_of_ne hi]
      exact bWo _ _ (aCu v i)
  choose vertices hv using hslot
  obtain ⟨p,hp,he⟩:=c4T bzu.proof
    cxW.proof (slots v P) vertices hv
  refine ⟨p,hp,bXo (slots v P) ?_ (deL v P hP) ?_ p he⟩
  · intro i
    rw [hv i]
    exact convex_convexHull _ _
  · intro w
    rw [← b7c (slots v P) vertices hv w]
    exact (Set.finite_range _).isCompact_convexHull ℝ
private theorem eMA (P:Set iz) (hP:OE P)
    (t:ℝ) (S:Finset (Fin 4)) :
    (∑ i,weights t S i•slots v P i) = ∑ i∈S,slots v (t•P) i:= by
  calc
    _ = ∑ i∈S,(![t,1,1,1] :Fin 4→ℝ) i•slots v P i:= by
      rw [← Finset.sum_subset (s₁:=S) (s₂:=Finset.univ) (Finset.subset_univ S)
        (f := fun i=>weights t S i•slots v P i)]
      · exact Finset.sum_congr rfl (fun i hi=> by simp [weights,hi])
      · intro i _ hi
        simp [weights,hi,Set.zero_smul_set (Set.nonempty_of_mem (deL v P hP i))]
    _ = _:= by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> simp [slots]
private theorem c0x (P:Set iz) (hP:OE P) (t:ℝ) (ht:0≤t) :
    T7 v (t•P)=t*T7 v P:= by
  obtain ⟨p,hp,heval⟩:=gLl v P hP
  have hw (s :ℝ) (hs :0≤ s) (S:Finset (Fin 4)) (i:Fin 4) :
      0≤weights s S i:= by
    unfold weights
    apply ite_nonneg _ (le_refl (0:ℝ))
    fin_cases i
    · exact hs
    all_goals exact zero_le_one
  have hpol (s :ℝ) (hs :0≤ s) (S:Finset (Fin 4)) :
      p.eval (weights s S)=(volume (∑ i∈S,slots v (s•P) i)).toReal:= by
    rw [heval _ (hw s hs S),eMA v P hP]
  simpa only [bJi,aa1,hpol _ ht,hpol 1 zero_le_one,one_smul]
    using c4t p hp t
private theorem dga (P:Set iz) {S:Finset (Fin 4)} (h0:0∉S) :
    (∑ i∈S,slots v P i)=base v S:= by
  change _=nD (xl S (aur v)) (∑ i∈S,aTk i)
  rw [← bOy _ _ _ (aCu v)]
  apply Finset.sum_congr rfl
  intro i hi
  have hne :i≠0:= fun h=>h0 (h ▸ hi)
  simp [slots,Function.update_of_ne hne]
private theorem eAT (P:Set iz) (t:ℝ) :
    T7 v (t•P) =
      ∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card) *
        ((volume (t•P+base v S)).toReal-(volume (base v S)).toReal) := by
  rw [bJi,aa1,bPu,
    Finset.sum_powerset_insert biT,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub:=Finset.mem_powerset.mp hS
  have h0: (0:Fin 4)∉S:= fun h=>biT (hsub h)
  have hs :S.card≤3 :=
    (Finset.card_le_card hsub).trans (show rest.card≤3 by decide)
  rw [Finset.sum_insert h0,Finset.card_insert_of_notMem h0,
    dga v _ h0,show slots v (t•P) 0=t•P by simp [slots]]
  have e₁:4 - S.card=(3 - S.card)+1 := by omega
  have e₂:4-(S.card+1)=3 - S.card:= by omega
  rw [e₁,e₂,pow_succ]
  ring
private theorem b1x (P:Set iz) (hP:OE P) (t:ℝ) :
    apK P (base v ∅) t=0:= by
  have hbase :base v ∅ = 0:= by simp [base,xl,aGI,aTp]
  have hPz :volume (t•P)=0:= by
    apply bPM
    intro x hx
    obtain ⟨y,hy,rfl⟩:=Set.mem_smul_set.mp hx
    simp [Pi.smul_apply,hP.zero_height y hy]
  rw [apK,hbase,add_zero,hPz,
    show (0:Set iz) = {0} by rfl]
  simp
private theorem dg2 (hv :v≤ m6.t) (P:Set iz)
    (hP:OE P) (hsub:P⊆nD S9 0) {S:Finset (Fin 4)} (hS:S⊆rest) :
    Tendsto (apK P (base v S)) (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (ajg (aS5 v S) (aGI S)
        (UB P) (V9 P) (WA P))) := by
  by_cases he :S = ∅
  · subst S
    rw [show apK P (base v ∅)=(fun _:ℝ=>0) from funext (b1x v P hP)]
    simp [ajg,xl,aGI]
  · have hn:=Finset.nonempty_iff_ne_empty.mpr he
    apply bRj.proof P hP hsub _ _ (crv S _ (aCu v))
    · exact Finset.sum_lt_sum_of_nonempty hn (fun i _=>cDA v i)
    · exact Finset.sum_pos (fun i _=>cDC v hv i) hn
    · apply Finset.sum_pos _ hn
      intro i hi
      have hne :i≠0:= fun h0=>biT (h0 ▸ hS hi)
      fin_cases i
      · exact (hne rfl).elim
      all_goals decide
private theorem gK7 (hv :v≤ m6.t) (P:Set iz) (hP:OE P) (hsub:P⊆nD S9 0) :
    T7 v P =
      ∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card) *
        ajg (aS5 v S) (aGI S)
          (UB P) (V9 P) (WA P) := by
  have hlim:=tendsto_finsetSum rest.powerset (fun S hS =>
    (dg2 v hv P hP hsub (Finset.mem_powerset.mp hS)).const_mul
      ((-1 :ℝ)^(3 - S.card)))
  have heq : (fun _:ℝ=>T7 v P) =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      (fun t:ℝ => ∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card) *
        apK P (base v S) t) := by
    filter_upwards [eventually_mem_nhdsWithin (a :=(0:ℝ)) (s :=Set.Ioi 0)] with t ht
    have ht' : 0<t:=ht
    have hquot:T7 v (t•P)/t=T7 v P:= by
      rw [c0x v P hP t ht'.le]
      exact mul_div_cancel_left₀ _ ht'.ne'
    calc
      T7 v P=T7 v (t•P)/t:=hquot.symm
      _ = _:= by simp only [eAT,Finset.sum_div,apK,mul_div_assoc]
  exact tendsto_const_nhds_iff.mp (hlim.congr' heq.symm)
theorem gK6 (hv :v≤ m6.t) (P:Set iz) (hP:OE P)
    (hsub:P⊆nD (mW v) 0) :
    T7 v P =
      ∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card) *
        ajg (aS5 v S) (aGI S)
          (UB P) (V9 P) (WA P) := by
  let a :ℝ:=1 / 2
  have ha :0≤a := by norm_num [a]
  have hbody :OE (a•P) := by
    obtain ⟨W,hW,hPW⟩:=hP.polytope
    refine ⟨⟨a•W,hW.smul_set,?_⟩,Set.mem_smul_set.mpr ⟨0,hP.zero_mem,smul_zero _⟩,?_⟩
    · rw [convexHull_smul,← hPW]
    · rintro _ ⟨x,hx,rfl⟩
      simp [Pi.smul_apply,hP.zero_height x hx]
  have hfit :a•P⊆nD S9 0:= by
    rintro _ ⟨x,hx,rfl⟩
    have hbNat : (mW v).b≤133:= by
      change max (133 - v) (56-3*v+3)≤133
      omega
    have hb: ((mW v).b:ℝ)≤133:= by exact_mod_cast hbNat
    have hj: ((mW v).j:ℝ)≤56:= by exact_mod_cast (Nat.sub_le 56 (3*v))
    have ht: ((mW v).t:ℝ)≤28:= by exact_mod_cast a5C v
    obtain ⟨h0,h1,h2,h3,h4⟩:=hsub hx
    change x 0 + x 1 + x 2≤((mW v).b:ℝ) at h1
    change x 1+2*x 2≤((mW v).j:ℝ) at h2
    change x 2≤((mW v).t:ℝ) at h3
    refine ⟨fun i=>mul_nonneg ha (h0 i),?_,?_,?_,?_⟩ <;>
      simp only [Pi.smul_apply,smul_eq_mul,a,Nat.cast_ofNat,Nat.cast_zero]
    · linarith
    · linarith
    · linarith
    · simp [hP.zero_height x hx]
  have hB:UB (a•P)=a*UB P :=
    bhH _ (fun r x=> by simp only [Pi.smul_apply,smul_eq_mul]; ring) _ _ ha
  have hJ:V9 (a•P)=a*V9 P :=
    bhH _ (fun r x=> by simp only [Pi.smul_apply,smul_eq_mul]; ring) _ _ ha
  have hT:WA (a•P)=a*WA P:=bhH _ (fun _ _=>rfl) _ _ ha
  apply mul_left_cancel₀ (show a≠0 by norm_num [a])
  rw [← c0x v P hP a ha,gK7 v hv _ hbody hfit,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [hB,hJ,hT]
  unfold ajg
  ring
end
end q5Xvxxc
end
section
set_option autoImplicit true
namespace q5Xvxxc
noncomputable section
open aR (Shape)
open oR (Wc)
open we (fW vY)
open yz (iz alT nD)
open Qp (OE b3f)
open aeB (UB V9 WA)
open P6_6 (m6 mW bf)
open P6_6_5 (R4)
open qeu0RUc (T7 a5D)
open MvPolynomial
open scoped BigOperators
open private bLF bvn b1b from ProximityPrize.SubmissionLower.BG
open private linear c0p BE from ProximityPrize.SubmissionLower.CD
private def cost (v :ℕ) (B J T:ℝ) :ℝ :=
  let a :=aur v
  linear (a 2) (a 3) B J T +
    ((bf - 1 :ℕ) :ℝ)*linear (a 1) (a 3) B J T +
    (bf :ℝ)*linear (a 1) (a 2) B J T
private theorem aVX (v :ℕ) (hv :v≤ m6.t) (P:Set iz)
    (hP:OE P) (hsub:P⊆nD (mW v) 0) :
    T7 v P=cost v (UB P) (V9 P) (WA P) := by
  rw [gK6 v hv P hP hsub]
  simpa only [cost,aS5,aGI,show aTk 1=1 from rfl,
    show aTk 2=bf - 1 from rfl,show aTk 3=bf from rfl,
    Nat.cast_one,one_mul] using
    BE (aur v) aTk (aCu v 1) (aCu v 2) (aCu v 3)
      (UB P) (V9 P) (WA P)
private theorem eNY (v :ℕ) :
    cost v (mW v).b (mW v).j (mW v).t=(R4 v :ℝ) := by
  let a :=aur v
  have hm (i j:Fin 4) :=c0p (mW v) (a i) (a j)
    (a5D v) (aCu v i) (aCu v j)
  change cost v (mW v).b (mW v).j (mW v).t =
    ((Wc (mW v) (a 2) (a 3)+(bf - 1)*Wc (mW v) (a 1) (a 3) +
      bf*Wc (mW v) (a 1) (a 2) :ℕ) :ℝ)
  simp only [cost,Nat.cast_add,Nat.cast_mul,hm]
  rfl
private theorem dQh (v :ℕ) {B J T B' J' T' : ℝ} (hB:B≤B') (hJ:J≤J') (hT:T≤T') :
    cost v B J T≤ cost v B' J' T' := by
  simp only [cost,linear]
  gcongr
private theorem sum_cost (v n:ℕ) (B J T:Fin n→ℝ) :
    (∑ i,cost v (B i) (J i) (T i))=cost v (∑ i,B i) (∑ i,J i) (∑ i,T i) := by
  simp only [cost,linear,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
private theorem gxx {P:Set iz} (hP:OE P)
    {s :Shape} (hs :P⊆nD s 0) :
    UB P≤ s.b∧V9 P≤ s.j∧WA P≤ s.t:= by
  have bound (L:iz→ℝ) (a :ℝ) (h : ∀ x∈P,L x≤a) :
      sSup (L '' P)≤a := by
    apply csSup_le ((Set.nonempty_of_mem hP.zero_mem).image L)
    rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  exact ⟨bound _ _ (fun _ hx=>(hs hx).2.1),bound _ _ (fun _ hx=>(hs hx).2.2.1),
    bound _ _ (fun _ hx=>(hs hx).2.2.2.1)⟩
theorem proof :qeu0RUc.c3:= by
  intro v hv n f hf
  let p:=mW v
  let s (i:Fin n) :=bLF (f i)
  let P (i:Fin n) :=alT (vY (fW (f i)))
  have hcap (d:Fin n→ℕ) {b:ℕ} (h: (∑ i,d i)≤b) (i:Fin n) :d i≤b :=
    (Finset.single_le_sum (fun j _=>Nat.zero_le (d j)) (Finset.mem_univ i)).trans h
  calc
    (∑ i,T7 v (P i)) ≤ ∑ i,cost v (s i).b (s i).j (s i).t:= by
      apply Finset.sum_le_sum
      intro i _
      have hP:OE (P i) :=b3f (hf.irreducible i).ne_zero
      have hs :P i⊆nD (s i) 0:=b1b (bvn (f i))
      have hp:P i⊆nD p 0:= by
        intro x hx
        obtain ⟨hn,hb,hj,ht,hh⟩:=hs hx
        exact ⟨hn,hb.trans (Nat.cast_le.mpr (hcap _ hf.total i)),
          hj.trans (Nat.cast_le.mpr (hcap _ hf.index i)),
          ht.trans (Nat.cast_le.mpr (hcap _ hf.top i)),hh⟩
      rw [aVX v hv _ hP hp]
      obtain ⟨hb,hj,ht⟩:=gxx hP hs
      exact dQh v hb hj ht
    _≤(R4 v :ℝ) := by
      rw [sum_cost,← eNY]
      exact dQh v (by exact_mod_cast hf.total) (by exact_mod_cast hf.index)
        (by exact_mod_cast hf.top)
end
end q5Xvxxc
end
