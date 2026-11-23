import ProximityPrize.SubmissionLower.ZxR2Ljc
import ProximityPrize.SubmissionLower.ZCYrWLb
import ProximityPrize.SubmissionLower.ZX4kd1a
import ProximityPrize.SubmissionLower.Z1LUzCd
set_option Elab.async false
set_option maxRecDepth 12000
section
set_option autoImplicit true
namespace qs8Tnzb
noncomputable section
open qK9H6va qaTCFjd qOrl4se MvPolynomial
open P1_6_1_3 (adjacentProduct)
open fP (lP cF xH)
open private witness recover shortCount shortCount_eq from ProximityPrize.SubmissionLower.ZxR2Ljc
open private step step_coeff from ProximityPrize.SubmissionLower.Zzm95ae
open private rU from ProximityPrize.SubmissionLower.ZZBDV9b
open scoped BigOperators Matrix
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
local notation "F" => ZMod P1.p
local notation "Exp" => (Fin 4 →₀ ℕ)
private def Bo:Fin 23→ℕ×ℕ×ℕ :=
  ![(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),
    (0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),
    (3,1,0),(5,0,0),(0,0,2),(0,3,0),(1,1,1),(2,2,0),(3,0,1),
    (4,1,0),(6,0,0)]
private def weight (i:Fin 23) :ℕ :=
  (Bo i).1+2*(Bo i).2.1+3*(Bo i).2.2
private def key (i:Fin 23) :ℕ:=64*weight i+8*(Bo i).1+(Bo i).2.1
private theorem key_mono:StrictMono key :=
  Fin.strictMono_iff_lt_succ.mpr (by decide)
private theorem dlP (i:Fin 23) :weight i≤6 :=
  (by decide : ∀ j:Fin 23,weight j≤6) i
private def seed (i:Fin 23) :Exp :=
  let j:=Bo i
  rU (53-(j.1+j.2.1+j.2.2)) j.1 j.2.1 j.2.2
private theorem seed_degree (i:Fin 23) : (seed i).degree=53:= by
  have h:=dlP i
  rw [cF]
  change 53-((Bo i).1+(Bo i).2.1+(Bo i).2.2) +
    (Bo i).1+(Bo i).2.1+(Bo i).2.2=53
  unfold weight at h
  omega
private theorem bwf (i:Fin 23) : (seed i).weight lP=weight i:= by
  rw [xH]
  rfl
private theorem seed_top (i:Fin 23) :seed i 3≤16:= by
  have h:=dlP i
  unfold weight at h
  change (Bo i).2.2≤16
  omega
private theorem seed_inj:Function.Injective seed := by
  intro i j h
  apply key_mono.injective
  exact congrArg (fun m:Exp=>64*(m 1+2*m 2 + 3*m 3)+8*m 1+m 2) h
private theorem diagonal_ne_zero {n:ℕ} (hn:n≤6) : (n:F) - 56≠0:= by
  have hp:56<P1.p:= by decide
  change (n:F)-((56:ℕ) :F)≠0
  intro h
  have hmod:=(ZMod.natCast_eq_natCast_iff' n 56 P1.p).mp (sub_eq_zero.mp h)
  rw [Nat.mod_eq_of_lt (by omega :n<P1.p),Nat.mod_eq_of_lt hp] at hmod
  omega
theorem proof :qtjtNFa.c1 := by
  classical
  let W:Matrix (AdjacentRow 53) (Fin 23) F:= fun e i=>witness e.val.val (seed i)
  have hker : (adjacentMatrix 53 46)ᵀ*W=0:= by
    ext m i
    rw [Matrix.mul_apply]
    change (∑ e :AdjacentRow 53,(adjacentProduct e.val.val).coeff m.val *
      witness e.val.val (seed i))=0
    have hlow: (10 :ℤ)≤ m.val.weight lP:=m.property.2.1
    have hhigh:m.val.weight lP≤56:= by exact_mod_cast m.property.2.2.1
    have hw:=dlP i
    rw [← bwf] at hw
    have hs : (seed i).weight lP+3< m.val.weight lP:= by omega
    rw [recover _ _ (seed_degree i) hhigh m.property.2.2.2,
      step_coeff _ _ _ (Or.inr hs),ite_eq_right (by intro he; rw [he] at hs; omega)]
  let R:Matrix (Fin 23) (AdjacentRow 53) F :=
    fun i e=>(adjacentProduct e.val.val).coeff (seed i)
  let T:=R*W
  have hT (i j:Fin 23) :T i j=(step 56 (monomial (seed j) 1)).coeff (seed i) := by
    change (R*W) i j= _
    rw [Matrix.mul_apply]
    exact recover _ _ (seed_degree j)
      ((bwf i).trans_le ((dlP i).trans (by decide))) (seed_top i)
  have htri:T.IsLowerTriangular := by
    intro i j hij
    change i<j at hij
    have hk :=key_mono hij
    unfold key at hk
    have htail:8*(Bo j).1+(Bo j).2.1<64 := by
      have hw:=dlP j
      unfold weight at hw
      omega
    have hi: (seed i).weight lP≤(seed j).weight lP:= by
      rw [bwf,bwf]
      omega
    have hne :seed j≠seed i:= fun h=>hij.ne (seed_inj h).symm
    rw [hT,step_coeff _ _ _ (Or.inl hi),ite_eq_right hne]
  have hdet:T.det≠0:= by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [hT,step_coeff _ _ _ (Or.inl le_rfl),ite_eq_left rfl]
    exact diagonal_ne_zero ((bwf i).trans_le (dlP i))
  have hrank :=Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at hrank
  have hW:=hrank.ge.trans (Matrix.rank_mul_le_right R W)
  have h:=Matrix.rank_add_rank_le_card_of_mul_eq_zero hker
  rw [Matrix.rank_transpose] at h
  have hs :=(Nat.add_le_add (rank_le_adjacent (q:=53) (r :=46) rfl rfl) hW).trans
    (h.trans (adjacent_card_le 53))
  rw [shortCount_eq,(by decide :shortCount 53=5541)] at hs
  change (Gy 53 (offset 46)).rank≤5518
  omega
end
end qs8Tnzb
end
section
set_option autoImplicit true
namespace q0TFWAc
noncomputable section
open Polynomial P6_6 P6_6_7 q6t08kb MvPolynomial
open aR (af ao Shape shape aO extend wU cK)
open Ex (YN aQU X7)
open dN (GeoJets bC j8 Ch An)
open BO (bfW Ue)
open agL (BV EY a4B bft aD7 bc1)
open Dr (AN a9B)
open lB (amo aFf)
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
open private duz from ProximityPrize.SubmissionLower.T
private theorem topView_lift (f :af 3) :
    YN (rename Fin.castSucc f)=Polynomial.C f := by
  have eq :YN.toRingHom.comp (rename (R:=ao[X]) (Fin.castSucc:Fin 3→Fin 4)).toRingHom =
      Polynomial.C:= by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [YN,optionEquivLeft_C]
    · intro i
      simp [YN,optionEquivLeft_X_some,finSuccEquivLast_castSucc]
  exact RingHom.congr_fun eq f
theorem lift_anchorLead (R:af 4) (ht: (shape R).t=0) :
    rename Fin.castSucc (X7 R)=R:= by
  apply YN.injective
  have hz :=(aQU R).trans ht
  rw [topView_lift,X7,Polynomial.leadingCoeff,hz]
  exact (Polynomial.eq_C_of_natDegree_eq_zero hz).symm
private theorem ab6 (R:af 4) :ajA R=pderiv 2 R:= by
  classical
  conv_rhs=>rw [R.as_sum]
  simp only [ajA,BV,map_sum,pderiv_monomial]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.prod_eq_single (2 :Fin 4)]
  · simp
  · intro j _ hji
    simp [Finsupp.single_eq_of_ne hji]
  · simp
theorem nonzero_proper {C R l ell} (h:Input C R l ell) :
    ajA R≠0 ∧ ¬ R∣ajA R:= by
  have hd:0<R.degreeOf 2 := by
    rw [← lift_anchorLead R h.1.2.2.1,← show (Fin.castSucc (2 :Fin 3))=2 from rfl,
      degreeOf_rename_of_injective (Fin.castSucc_injective 3)]
    exact h.2
  have hb:R.totalDegree≤4025:=h.1.2.1.2.2.1.1.trans (Nat.sub_le _ _)
  have hsmall:R.degreeOf 2<K1.p :=
    ((degreeOf_le_totalDegree _ _).trans hb).trans_lt (by decide)
  let _:CharP ao K1.p:=charP_of_injective_ringHom aR.embed.injective K1.p
  let _:CharP ao[X] K1.p:=charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hc: (R.degreeOf 2 :ao[X])≠0:= by
    intro hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hd ((CharP.cast_eq_zero_iff ao[X] K1.p _).mp hz))
  have hn:=pderiv_ne_zero_of_natCast_ne_zero 2 R hc
  rw [ab6]
  refine ⟨hn,?_⟩
  rintro ⟨b,hb⟩
  have hb0:b≠0:= fun he=>hn (by rw [hb,he,mul_zero])
  have ht:=degreeOf_pderiv_le_sub_one 2 R
  rw [hb,degreeOf_mul_eq h.1.1.1.ne_zero hb0] at ht
  omega
theorem hasse_fits {V:af 4} {a :Shape}
    (ha :a.t=a.j/2) (hv :aO (shape V) ⟨a.b,a.j,0⟩)
    (e :Fin 4 →₀ ℕ) :lowerFits (BV e V) a := by
  have hW:=a4B e hv
  refine ⟨hW,degreeOf_le_iff.mpr ?_⟩
  intro m hm
  have hj: (∑ i:Fin 4,i.val*m i)≤a.j:= by
    have hx :=(Finset.le_sup (f := fun m:Fin 4 →₀ ℕ=>m.sum fun i k=>i.val*k) hm).trans hW.2.1
    simpa only [Finsupp.sum_fintype _ _ (fun _=>Nat.mul_zero _)] using hx
  have hi:2*m 2 ≤ ∑ i:Fin 4,i.val*m i :=
    Finset.single_le_sum (fun i _=>Nat.zero_le (i.val*m i)) (Finset.mem_univ (2 :Fin 4))
  rw [ha]
  omega
theorem jump_fits {C R l ell} (h:Input C R l ell) (e :Fin 4 →₀ ℕ) :
    lowerFits (BV e (ajA R)) (body R) :=
  hasse_fits rfl
    (a4B (Finsupp.single 2 1)
      (show aO (shape R) ⟨(body R).b,(body R).j,0⟩ from
        ⟨le_max_left _ _,le_rfl,h.1.2.2.1.le⟩)) e
theorem order_one {V:af 4} {S:ao[X]} (h:cK V S=0) :wU V S 1 := by
  rw [duz] at h
  intro m hm
  by_contra! hn
  have hz :m=0:=(Finsupp.degree_eq_zero_iff m).mp (by
    change m.sum (fun _ k=>k)=0
    omega)
  exact (mem_support_iff.mp hm) (hz ▸ h)
theorem first_order (C:Context) (R:af 4) (γ:P6.K) :
    wU (ajA R) (extend (C.s γ)) (ord C R γ - 1) := by
  have h:=q8NBBre.cUA R (extend (C.s γ)) (Finsupp.single 2 1)
    (ord C R γ) (orderAt_ord C R γ)
  have he :EY (Finsupp.single (2 :Fin 4) 1)=1 := by simp [EY]
  simpa only [ajA,he] using h
theorem select_curve {C:Context} {R:af 4} {γ:P6.K} (h:γ∈active C R) :
    ∃ T,(ke R).IsMinimalPrime T∧T≤Ch (extend (C.s γ)) := by
  have ho:=(Finset.mem_filter.mp h).2
  have hle :ke R≤Ch (extend (C.s γ)) := by
    apply Ideal.span_le.mpr
    intro V hV
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hV
    rcases hV with rfl | rfl
    · exact Ue.mpr (bfW (by omega) (orderAt_ord C R γ))
    · exact Ue.mpr (bfW (by omega) (first_order C R γ))
  let _: (Ch (extend (C.s γ))).IsPrime :=RingHom.ker_isPrime (An _)
  exact Ideal.exists_minimalPrimes_le hle
theorem generic_le_weight {C R l ell} (h:Input C R l ell) {T:Ideal GeoJets}
    (hT: (ke R).IsMinimalPrime T) :
    genericOrder (ajA R) T≤AN (ke R) T:= by
  classical
  let _:=hT.isPrime
  have hr :=h.1.1.1
  have hg:bC R≠0:= fun hz =>
    hr.ne_zero (aFf (hz.trans (map_zero _).symm))
  have hheight:=aD7 hg (amo _ _ hr (nonzero_proper h).2) hT
  have hm:bC R∈T:=hT.le (Ideal.subset_span (by simp))
  apply ENat.natCast_le_natCast.mp
  rw [a9B hT]
  refine bc1 hheight hm (bRn.gK5 _ T _ ?_)
  intro e he
  change BV e (MvPolynomial.map j8 (ajA R))∈T
  rw [← bft]
  exact Nat.findGreatest_spec (P:= fun d => ∀ e,EY e<d →
    bC (BV e (ajA R))∈T) (Nat.zero_le _) (fun _ hf=>(Nat.not_lt_zero _ hf).elim) e he
end
end q0TFWAc
end
section
set_option autoImplicit true
set_option maxHeartbeats 1000000
namespace q0TFWAc
noncomputable section
open P6_6 P6_6_7 q6t08kb
open aR (af Shape extend cK ceilDiv)
open oR (Wc)
open dN (GeoJets bC Ch)
open BO (Ue)
open agL (BV)
open Dr (AN)
open Finset
open scoped BigOperators
def c1 :Prop :=
  ∀ (C:Context) R l ell,Input C R l ell →
    ∀ (S:Finset (Ideal GeoJets)),(∀ T∈S,(ke R).IsMinimalPrime T) →
    ∀ a :Shape,a=body R∨a=lowerTaylor (body R) →
      (∑ T∈S,(AN (ke R) T:ℚ)*curveDegree T a)≤Wc (body R) (body R) a
def c2 :Prop :=
  ∀ (C:Context) R l ell,Input C R l ell →
    ∀ T,(ke R).IsMinimalPrime T →
      SectionBound C T (body R)∧SectionBound C T (lowerTaylor (body R))
def c3:Prop :=
  ∀ (C:Context) R l ell,Input C R l ell →
    ∀ T,(ke R).IsMinimalPrime T →
      (∃ γ∈active C R,T≤Ch (extend (C.s γ)))→Nonempty (Chart C R T)
private theorem degree_nonneg (T:Ideal GeoJets) (a :Shape) :0≤ curveDegree T a :=
  div_nonneg (MvPolynomial.affineDegree_nonneg _) (by positivity)
private theorem count_section {C T a} (h:SectionBound C T a) (V:af 4)
    (hv :lowerFits V a) (hproper :bC V∉T) {M:Finset P6.K} (hm:M⊆C.Δ)
    (hmark : ∀ γ∈M,T≤Ch (extend (C.s γ)))
    (hzero : ∀ γ∈M,cK V (extend (C.s γ))=0) :
    (M.card:ℚ)≤ curveDegree T a := by
  simpa only [Nat.cast_one,sum_const,nsmul_eq_mul,mul_one] using
    h V hv hproper M hm hmark (fun _=>1) (fun γ hγ=>order_one (hzero γ hγ))
private theorem count_curve {C R T} (h:Chart C R T)
    (ha :SectionBound C T (body R)) (hb:SectionBound C T (lowerTaylor (body R)))
    {M:Finset P6.K} (hM:M⊆active C R)
    (hm : ∀ γ∈M,T≤Ch (extend (C.s γ))) :
    (mV:ℚ)*M.card≤(P6.t:ℚ)*curveDegree T (lowerTaylor (body R)) +
      2*(mV:ℚ)*curveDegree T (body R) := by
  classical
  let a :=body R
  let b:=lowerTaylor a
  let B:=M.filter fun γ=>cK h.sep (extend (C.s γ))=0
  let G:=M.filter fun γ=>cK h.sep (extend (C.s γ))≠0
  have hsub {γ} (hg:γ∈M) :γ∈C.Δ :=
    (mem_filter.mp (mem_filter.mp (hM hg)).1).1
  have hB: (B.card:ℚ)≤ curveDegree T a :=
    count_section ha h.sep h.fits h.proper
      (fun _ hγ=>hsub (mem_filter.mp hγ).1) (fun γ hγ=>hm γ (mem_filter.mp hγ).1)
      (fun _ hγ=>(mem_filter.mp hγ).2)
  let d := ⌊curveDegree T b⌋₊
  have regSub:G⊆C.Δ:= fun _ hγ=>hsub (mem_filter.mp hγ).1
  have hG:=P6_6_5.bv5 (C.messages.mono regSub) d
    (fun i ⟨γ,hg,hmiss⟩=> by
      obtain ⟨D,hD,hcriterion⟩:=h.D4 i
      obtain ⟨hγ,hsep⟩:=mem_filter.mp hg
      have hproper :bC D∉T:= fun hmem =>
        hmiss ((hcriterion γ (hM hγ) (hm γ hγ) hsep).mp (Ue.mp (hm γ hγ hmem)))
      apply Nat.le_floor
      apply count_section hb D hD hproper
      · intro δ hδ
        exact hsub (mem_filter.mp (mem_filter.mp hδ).1).1
      · intro δ hδ
        exact hm δ (mem_filter.mp (mem_filter.mp hδ).1).1
      · intro δ hδ
        obtain ⟨hg,hh⟩:=mem_filter.mp hδ
        obtain ⟨hm',hsep'⟩:=mem_filter.mp hg
        exact (hcriterion δ (hM hm') (hm δ hm') hsep').mpr hh)
  have hg' : (mV:ℚ)*G.card≤(P6.t:ℚ)*d+mV:= by
    rw [ee8,d1C]
    exact_mod_cast hG
  have hc' : B.card+G.card=M.card :=
    card_filter_add_card_filter_not (s :=M) (p:= fun γ=>cK h.sep (extend (C.s γ))=0)
  have hc: (G.card:ℚ)+B.card=M.card:= by
    exact_mod_cast (add_comm G.card B.card).trans hc'
  have hd:=mul_le_mul_of_nonneg_left (Nat.floor_le (degree_nonneg T b))
    (show (0:ℚ)≤P6.t by positivity)
  have hh:=mul_le_mul_of_nonneg_left h.unitDebit (show (0:ℚ)≤ mV by positivity)
  have hb' := mul_le_mul_of_nonneg_left hB (show (0:ℚ)≤ mV by positivity)
  rw [← hc,mul_add]
  linarith only [hg',hd,hh,hb']
private theorem branch_bound (h2 :c2) (h3:c3) {C R l ell} (h:Input C R l ell)
    {T:Ideal GeoJets} (ht: (ke R).IsMinimalPrime T) {M:Finset P6.K}
    (hne :M.Nonempty) (hM:M⊆active C R) (hm : ∀ γ∈M,T≤Ch (extend (C.s γ))) :
    (mV:ℚ)*(∑ γ∈M,((ord C R γ - 1 :ℕ) :ℚ)) ≤
      (P6.t:ℚ)*((AN (ke R) T:ℚ)*curveDegree T (lowerTaylor (body R))) +
      3*(mV:ℚ)*((AN (ke R) T:ℚ)*curveDegree T (body R)) := by
  classical
  obtain ⟨γ,hγ⟩:=hne
  obtain ⟨bY⟩:=h3 C R l ell h T ht ⟨γ,hM hγ,hm γ hγ⟩
  obtain ⟨ha,hb⟩:=h2 C R l ell h T ht
  have hu:=(nonzero_proper h).1
  obtain ⟨e,he,heproper⟩:=q8NBBre.cSn (ajA R) T ht.isPrime hu
  let m:=AN (ke R) T
  let g:=genericOrder (ajA R) T
  let j (δ:P6.K) :=ord C R δ - 1 - g
  have hg: (g:ℚ)≤ m:= by exact_mod_cast generic_le_weight h ht
  have hmpos : (1 :ℚ)≤ m:= by exact_mod_cast Nat.succ_le_of_lt (Dr.aFq ht)
  have hcut: (∑ δ∈M,(j δ:ℚ))≤ curveDegree T (body R) := by
    refine ha (BV e (ajA R)) (jump_fits h e) heproper M
      (fun _ hδ=>(mem_filter.mp (mem_filter.mp (hM hδ)).1).1) hm j ?_
    intro δ _
    simpa only [j,g,he] using
      q8NBBre.cUA _ _ e _ (first_order C R δ)
  have hcount:=count_curve bY ha hb hM hm
  have hsplit : (∑ δ∈M,((ord C R δ - 1 :ℕ) :ℚ)) ≤
      (m:ℚ)*M.card + ∑ δ∈M,(j δ:ℚ) := by
    calc
      _ ≤ ∑ δ∈M,((m:ℚ)+(j δ:ℚ)) := by
        apply sum_le_sum
        intro δ _
        have hj:ord C R δ - 1≤g+j δ:= by dsimp [j]; omega
        have hc: ((ord C R δ - 1 :ℕ) :ℚ)≤(g:ℚ)+j δ:= by exact_mod_cast hj
        exact hc.trans (add_le_add hg le_rfl)
      _ = _:= by rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_comm (M.card:ℚ)]
  have hj:=hcut.trans (le_mul_of_one_le_left (degree_nonneg T (body R)) hmpos)
  calc
    _≤(mV:ℚ)*((m:ℚ)*M.card + ∑ δ∈M,(j δ:ℚ)) :=
      mul_le_mul_of_nonneg_left hsplit (by positivity)
    _=(m:ℚ)*((mV:ℚ)*M.card) +
        (mV:ℚ) * ∑ δ∈M,(j δ:ℚ) := by ring
    _≤_:=(add_le_add (mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hj (by positivity))).trans_eq (by ring)
private theorem bw {n x y :ℕ}
    (h:46402*n≤82317*x+3*46402*y) :
    n≤ ceilDiv (82317*x) 46402 + 3*y := by
  unfold ceilDiv
  omega
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q6t08kb.c4 := by
  classical
  intro C R l ell h hr
  let hin:Input C R l ell:=⟨h,hr⟩
  let a :=body R
  let f (γ:P6.K) :Ideal GeoJets :=
    if hg:γ∈active C R then (select_curve hg).choose else ⊥
  have hv (γ) (hg:γ∈active C R) :
      (ke R).IsMinimalPrime (f γ)∧f γ≤Ch (extend (C.s γ)) := by
    simpa only [f,dite_eq_left hg] using (select_curve hg).choose_spec
  let S:=(active C R).image f
  let part (T:Ideal GeoJets) :=(active C R).filter (fun γ=>f γ=T)
  have ht {T} (hT:T∈S) : (ke R).IsMinimalPrime T:= by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hT
    exact (hv γ hγ).1
  have hcover :
      (∑ T∈S,∑ γ∈part T,((ord C R γ - 1 :ℕ) :ℚ))=(excessWeight C R (nonzeroFibers C R) :ℚ) := by
    dsimp only [S,part]
    rw [sum_fiberwise_of_maps_to (fun γ hγ=>mem_image_of_mem f hγ) (fun γ=>((ord C R γ - 1 :ℕ) :ℚ))]
    unfold active excessWeight
    rw [sum_filter,Nat.cast_sum]
    apply sum_congr rfl
    intro γ _
    by_cases he :1<ord C R γ
    · rw [ite_eq_left he]
    · rw [ite_eq_right he,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt he),Nat.cast_zero]
  let cost (b:Shape) := ∑ T∈S,(AN (ke R) T:ℚ)*curveDegree T b
  have hb: (mV:ℚ)*(excessWeight C R (nonzeroFibers C R) :ℚ) ≤
      (P6.t:ℚ)*cost (lowerTaylor a)+3*(mV:ℚ)*cost a := by
    rw [← hcover,mul_sum]
    unfold cost
    simp only [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro T hT
    rw [← mul_sum]
    apply branch_bound h2 h3 hin (ht hT)
    · obtain ⟨γ,hg,he⟩:=mem_image.mp hT
      exact ⟨γ,mem_filter.mpr ⟨hg,he⟩⟩
    · exact fun _ hγ=>(mem_filter.mp hγ).1
    · intro γ hγ
      obtain ⟨hg,hh⟩:=mem_filter.mp hγ
      rw [← hh]
      exact (hv γ hg).2
  have hx :=h1 C R l ell hin S (fun _ hT=>ht hT) (lowerTaylor a) (Or.inr rfl)
  have hy :=h1 C R l ell hin S (fun _ hT=>ht hT) a (Or.inl rfl)
  have hh:=hb.trans (add_le_add (mul_le_mul_of_nonneg_left hx (by positivity))
    (mul_le_mul_of_nonneg_left hy (by positivity)))
  rw [d1C,ee8] at hh
  have hn:46402*excessWeight C R (nonzeroFibers C R) ≤
      82317*Wc a a (lowerTaylor a)+3*46402*Wc a a a := by exact_mod_cast hh
  simpa only [d1C,ee8,a] using bw hn
end
end q0TFWAc
end
