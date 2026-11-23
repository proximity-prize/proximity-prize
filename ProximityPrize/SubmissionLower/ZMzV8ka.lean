import ProximityPrize.SubmissionLower.ZfbLZnc
import ProximityPrize.SubmissionLower.ZgKNZbc
import ProximityPrize.SubmissionLower.ZhEC96c
import ProximityPrize.SubmissionLower.ZvFqJTb
import ProximityPrize.SubmissionLower.Zj5kWte
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q1
noncomputable section
open P5 (K p)
open cu (L FX qD jz)
open qe6nVeb (Raw DualWord SeedPlane below dcQ immersedAt atDual phys)
open qb0hmCe (CurveModel coeffHeight cLN specialize zD)
open q1kuFjb (restrict headScalar AtSite)
open E7 (CurvePlace poleOrder Tq Gb)
open scoped Classical WithZero
section
open Polynomial hiding expand coeff_expand
open Finset
open qGWTmVd (factorize restrict_coeff restrict_degree b5S)
open private swap slice slice_coeff from ProximityPrize.SubmissionLower.ZkEPT8b
open private expand coeff_expand weights c0Q wdeg le_wdeg from ProximityPrize.SubmissionLower.ZgKNZbc
def dM {J U} (B:DualWord J U) {q:SeedPlane} {C₀:CurveModel q}
    (f :C₀.E[X][X]) (W:ℕ) :Prop :=
  ∀ i,f.coeff i=0∨(f.coeff i).natDegree+f.natDegree*B.u₀+i*(B.u₁-B.u₀)≤W
structure Factors {q:SeedPlane} (C₀:CurveModel q) (g:C₀.E[X][X]) where
  n:ℕ
  content:C₀.E[X]
  content_ne :content≠0
  factor :Fin n→ C₀.E[X][X]
  irreducible : ∀ j,Irreducible (factor j)
  positive : ∀ j,0<(factor j).natDegree
  normalized : ∀ j,(factor j).leadingCoeff.leadingCoeff=1
  product_eq :g=C content * ∏ j,factor j
private theorem restrict_ne {q:SeedPlane} (M:CurveModel q)
    {F:Raw} (hF:Irreducible F) (hd:0<F.natDegree) :restrict M F≠0:= by
  intro hz
  let ev :=MvPolynomial.eval₂Hom (algebraMap L M.E) M.seed
  have hq:ev q=0 :=
    RingHom.mem_ker.mp (M.equation.symm ▸ Ideal.subset_span (Set.mem_singleton q))
  have hnu : ¬ IsUnit (C (swap (C q)) :Raw) := by
    intro hu
    have hqu:IsUnit q:= by
      apply isUnit_C.mp
      simpa only [RingEquiv.symm_apply_apply] using (isUnit_C.mp hu).map swap.symm
    exact (hqu.map ev).ne_zero hq
  have hdvd:C (swap (C q))∣F:= by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    rw [← map_dvd_iff swap.symm,RingEquiv.symm_apply_apply,C_dvd_iff_dvd_coeff]
    intro j
    have hm:slice (F.coeff i) j∈RingHom.ker ev := by
      rw [RingHom.mem_ker]
      change MvPolynomial.eval₂Hom (algebraMap L M.E) M.seed (slice (F.coeff i) j)=0
      rw [slice,map_sum]
      simp only [MvPolynomial.eval₂Hom_monomial]
      have h:=restrict_coeff M F i j
      change ((restrict M F).coeff i).coeff j= _ at h
      rw [← h,hz,coeff_zero,coeff_zero]
    rw [show RingHom.ker ev=Ideal.span {q} from M.equation,
      Ideal.mem_span_singleton,slice_coeff] at hm
    exact hm
  obtain ⟨a,ha⟩:=hdvd
  have hu:=(hF.isUnit_or_isUnit ha).resolve_left hnu
  have hc: (C (swap (C q)) :Raw)≠0:=left_ne_zero_of_mul (ha ▸ hF.ne_zero)
  rw [ha,natDegree_mul hc hu.ne_zero,natDegree_C,natDegree_eq_zero_of_isUnit hu,
    zero_add] at hd
  exact (Nat.lt_irrefl 0) hd
private theorem fits_factor {J U} (B:DualWord J U) {q:SeedPlane} (M:CurveModel q)
    {F:Raw} (hn:restrict M F≠0) {W:ℕ} (hw:below B F W)
    {g:M.E[X][X]} (hdiv :g∣restrict M F) :dM B (C₀:=M) g W:= by
  intro i
  by_cases he :g.coeff i=0
  · exact Or.inl he
  right
  have hdeg:=(natDegree_le_of_dvd hdiv hn).trans (restrict_degree M F)
  let s :=B.u₁-B.u₀
  have hle {i j:ℕ} (h: (((restrict M F).coeff i).coeff j)≠0) :
      j+i*s+F.natDegree*B.u₀≤W:= by
    have hh:=restrict_coeff M F i j
    change ((restrict M F).coeff i).coeff j= _ at hh
    rw [hh] at h
    obtain ⟨a,_,ht⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
    have hk : (((F.coeff i).coeff a).coeff j)≠0:= fun hz=>ht (by simp [hz])
    have hj:=le_natDegree_of_ne_zero hk
    have hw' := hw i a (fun hz=>hk (by rw [hz,coeff_zero]))
    change _+F.natDegree*B.u₀+i*s≤W at hw'
    omega
  have hW:wdeg s (restrict M F)+F.natDegree*B.u₀≤W:= by
    have hz :expand (restrict M F)≠0:=(map_ne_zero_iff _ expand.injective).mpr hn
    obtain ⟨d,hd,hdmax⟩:=Finset.sup_mem_of_nonempty
      (f := fun d=>Finsupp.weight (weights s) d) (MvPolynomial.support_nonempty.mpr hz)
    have hc:=MvPolynomial.mem_support_iff.mp hd
    rw [coeff_expand] at hc
    change (expand (restrict M F)).support.sup _+_≤W
    rw [hdmax.symm]
    change Finsupp.weight (weights s) d+_≤W
    rw [c0Q]
    exact hle hc
  have hy :wdeg s g≤wdeg s (restrict M F) :=
    MvPolynomial.weightedTotalDegree_le_of_dvd _ (_root_.map_dvd expand hdiv)
      ((map_ne_zero_iff _ expand.injective).mpr hn)
  have hterm :=le_wdeg (s :=s) (leadingCoeff_ne_zero.mpr he)
  have hshift:=Nat.mul_le_mul_right B.u₀ hdeg
  change (g.coeff i).natDegree+g.natDegree*B.u₀+i*s≤W
  omega
private theorem t2 {J U} (B:DualWord J U) {q:SeedPlane} (M:CurveModel q)
    (F:Raw) (W:ℕ) (hF:Irreducible F) (hd:0<F.natDegree) (hw:below B F W) :
    ∃ S:Factors M (restrict M F),
      (∑ j,(S.factor j).natDegree)≤F.natDegree ∧ ∀ j,dM B (C₀:=M) (S.factor j) W:= by
  have hn:=restrict_ne M hF hd
  obtain ⟨S⟩:=factorize hn
  let a :=C (headScalar (restrict M F))*S.amm
  refine ⟨⟨S.n,a,mul_ne_zero (C_ne_zero.mpr (b5S hn)) S.monic.ne_zero,
    S.f,S.irreducible,S.positive,S.normalized,S.product⟩,
    (S.degree hn).le.trans (restrict_degree M F),fun j=>fits_factor B M hn hw ?_⟩
  calc
    S.f j ∣ ∏ k,S.f k :=dvd_prod_of_mem S.f (mem_univ j)
    _∣C a * ∏ k,S.f k :=dvd_mul_left _ _
    _∣restrict M F:=S.product.symm.dvd
end
open Polynomial Finset
open qE3Ebna (Sheet)
open Qt (gY)
open q1kuFjb (principal zero_budget IntSeries residue restrictOver integral_restrict
  expansion_coeff mapTwice Ua map_liftAt liftAt_reduce small_valuation power_residue coeffIntegral)
open qGWTmVd (Factorization head_C head_mul factor_heights)
open qFD8jve (aFA)
open agN (a6F)
open private restricted_bound gauss₂ gauss₂_bound coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
open private injective_seeds from ProximityPrize.SubmissionLower.ZYfUQxc
structure MarkedCurve (q:SeedPlane) (z :K→Fin 2→L) (T:Finset K) where
  curve :CurveModel q
  commonPole :Gb L curve.E curve.seed≤q.totalDegree
  place :K→CurvePlace L curve.E
  atPlace : ∀ γ∈T,curve.E →ₐ[L] LaurentSeries L
  distinct :Set.InjOn place (T:Set K)
  value : ∀ γ (hγ:γ∈T) c,
    (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
  arc : ∀ γ (hγ:γ∈T),∃ a :Fin 2→PowerSeries L,
    (∀ i,atPlace γ hγ (curve.seed i)=(a i:LaurentSeries L)) ∧
    (∀ i,PowerSeries.constantCoeff (a i)=z γ i) ∧
    ∃ i,PowerSeries.coeff 1 (a i)≠0
def IntegralAt {q z T} (M:MarkedCurve q z T) (γ:K) (f :M.curve.E[X][X]) :Prop :=
  ∀ i j,(M.place γ).value ((f.coeff i).coeff j)≤1
private theorem place_nonempty {q:SeedPlane} (Cq:CurveModel q) :
    Nonempty (CurvePlace L Cq.E) := by
  obtain ⟨t,ht,hfinite⟩:=Cq.curve
  let:=hfinite
  have hpos :0<Module.finrank (IntermediateField.adjoin L {t}) Cq.E :=Module.finrank_pos
  by_contra h
  have hz (v :CurvePlace L Cq.E) :poleOrder v.value t=0:=(h ⟨v⟩).elim
  rw [← (principal Cq t).2.2.2 ht,finsum_eq_zero_of_forall_eq_zero hz] at hpos
  exact (Nat.lt_irrefl 0) hpos
private theorem t1 (q:SeedPlane) (hq:Irreducible q) (z :K→Fin 2→L) (T:Finset K)
    (hz :Set.InjOn z (T:Set K)) (ha : ∀ γ∈T,immersedAt q (z γ)) :
    Nonempty (MarkedCurve q z T) := by
  obtain ⟨Cq,hheight⟩:=q9Dxm8d.proof q hq
  let A (γ:K) (hγ:γ∈T) :AtSite Cq (z γ) :=Classical.choice (by
    obtain ⟨a,hconst,hlinear,hq0⟩:=ha γ hγ
    exact qqpP4De.proof hq Cq (z γ) ⟨a,hconst,hq0,hlinear⟩)
  let v₀:=Classical.choice (place_nonempty Cq)
  let place (γ:K) :CurvePlace L Cq.E :=if hγ:γ∈T then (A γ hγ).place else v₀
  have hp (γ:K) (hγ:γ∈T) :place γ=(A γ hγ).place :=dite_eq_left hγ
  refine ⟨⟨Cq,hheight,place,fun γ hγ=>(A γ hγ).map,fun γ hγ δ hδ h => ?_,
    fun γ hγ c => ?_,fun γ hγ=>(A γ hγ).arc⟩⟩
  · exact hz hγ hδ ((A γ hγ).site_eq_of_place (A δ hδ)
      ((hp γ hγ).symm.trans (h.trans (hp δ hδ))))
  · exact (congrArg (fun v :CurvePlace L Cq.E=>v.value c) (hp γ hγ)).trans ((A γ hγ).value c)
private theorem eml {q:SeedPlane} {B:CurveModel q}
    {g:B.E[X][X]} (S:Factors B g) :headScalar g=S.content.leadingCoeff := by
  have hp (s :Finset (Fin S.n)) :headScalar (∏ j∈s,S.factor j)=1 := by
    induction s using Finset.induction_on with
    | empty=>simp [headScalar]
    | insert j s hj ih=>rw [prod_insert hj,head_mul,ih,mul_one]; exact S.normalized j
  calc
    headScalar g=headScalar (C S.content * ∏ j,S.factor j) :=congrArg headScalar S.product_eq
    _=S.content.leadingCoeff := by rw [head_mul,head_C,hp,mul_one]
private def monicContent {q:SeedPlane} {B:CurveModel q}
    {g:B.E[X][X]} (S:Factors B g) :Factorization g where
  amm:=C (headScalar g)⁻¹*S.content
  monic:= by
    rw [Monic,leadingCoeff_mul,leadingCoeff_C,eml S]
    exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr S.content_ne)
  n:=S.n
  f :=S.factor
  irreducible :=S.irreducible
  positive :=S.positive
  normalized:=S.normalized
  product := by
    have hn:headScalar g≠0:=(eml S).trans_ne (leadingCoeff_ne_zero.mpr S.content_ne)
    rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hn,map_one,one_mul]
    exact S.product_eq
private theorem marked_bound {q z T} (M:MarkedCurve q z T) (F:Raw)
    (γ:K) (hγ:γ∈T) :aFA (M.place γ).value (restrict M.curve F) 0:= by
  obtain ⟨a,ha,_,_⟩:=M.arc γ hγ
  have ht:Tq (M.place γ).value M.curve.seed=0:= by
    unfold Tq
    refine le_antisymm (Finset.sup_le fun i _ => ?_) (Nat.zero_le _)
    apply le_of_eq ((a6F _ _).2 ?_)
    rw [M.value γ hγ,ha i]
    exact (LaurentSeries.val_le_one_iff_eq_coe L _).2 ⟨a i,rfl⟩
  intro i j
  simpa only [ht,mul_zero] using restricted_bound M.curve F (M.place γ) i j
private theorem regular_of_unit {q:SeedPlane} {B:CurveModel q}
    {g:B.E[X][X]} (S:Factors B g) (v :Valuation B.E ℤᵐ⁰)
    (hg:aFA v g 0) (hc:v S.content.leadingCoeff=1) :
    (∀ i,v (S.content.coeff i)≤1) ∧ ∀ j,aFA v (S.factor j) 0:= by
  have hprod:gauss₂ v (C S.content)*(∏ j,gauss₂ v (S.factor j))≤1 := by
    simpa only [S.product_eq,map_mul,map_prod,Nat.cast_zero,WithZero.exp_zero] using
      gauss₂_bound v g hg
  have hhead (f :B.E[X][X]) (hf :v (f.leadingCoeff.leadingCoeff)=1) :
      1≤gauss₂ v f := by
    simpa only [coeff_natDegree,hf] using coeff_le_gauss₂ v f f.natDegree f.leadingCoeff.natDegree
  have ha :=hhead (C S.content) (by simpa only [leadingCoeff_C] using hc)
  have hb (j:Fin S.n) :=hhead (S.factor j) (by rw [S.normalized j,map_one])
  have hs :=one_le_prod (fun j _=>hb j : ∀ j∈(univ :Finset (Fin S.n)),_)
  refine ⟨fun i => ?_,fun j i k => ?_⟩
  · have h:gauss₂ v (C S.content)≤1 :=
      (by simpa only [mul_one] using mul_le_mul' (le_refl (gauss₂ v (C S.content))) hs :
        gauss₂ v (C S.content)≤_).trans hprod
    simpa only [coeff_C_zero] using (coeff_le_gauss₂ v (C S.content) 0 i).trans h
  · have h:gauss₂ v (S.factor j)≤1 := by
      have hj:=single_le_prod (fun i _=>hb i) (mem_univ j)
      simpa only [Nat.cast_zero,WithZero.exp_zero,one_mul] using
        (mul_le_mul' ha hj).trans hprod
    simpa only [Nat.cast_zero,WithZero.exp_zero] using (coeff_le_gauss₂ v (S.factor j) i k).trans h
private theorem t3 {q z T} (M:MarkedCurve q z T) (F:Raw) (S:Factors M.curve (restrict M.curve F)) :
    let H :=gY (Y3.embed F)*q.totalDegree
    ∃ G:Finset K,G⊆T∧(T \ G).card≤H∧(∑ j,coeffHeight (S.factor j))≤H ∧
      ∀ γ∈G,(M.place γ).value S.content.leadingCoeff=1 ∧
        (∀ i,(M.place γ).value (S.content.coeff i)≤1) ∧ ∀ j,IntegralAt M γ (S.factor j) := by
  let c:=S.content.leadingCoeff
  have hn:c≠0:=leadingCoeff_ne_zero.mpr S.content_ne
  have hhead:headScalar (restrict M.curve F)=c:=eml S
  have hne :restrict M.curve F≠0:= by
    intro hz
    rw [hz,headScalar,natDegree_zero,coeff_zero,leadingCoeff_zero] at hhead
    exact hn hhead.symm
  obtain ⟨hP,hH⟩:=factor_heights M.curve M.commonPole F hne (monicContent S)
  rw [hhead] at hP
  let bad:=T.filter fun γ=>(M.place γ).value c<1
  refine ⟨T \ bad,sdiff_subset,?_,(Nat.le_add_left _ _).trans hH,fun γ hγ => ?_⟩
  · rw [Finset.sdiff_sdiff_eq_self (filter_subset _ _)]
    exact (zero_budget (Cq:=M.curve) T M.place M.distinct hn).trans hP
  obtain ⟨hγT,hγbad⟩:=mem_sdiff.mp hγ
  have hb:=marked_bound M F γ hγT
  have hval : (M.place γ).value c≤1 := by
    rw [← hhead]
    simpa only [headScalar,← coeff_natDegree,Nat.cast_zero,WithZero.exp_zero] using
      hb (restrict M.curve F).natDegree ((restrict M.curve F).leadingCoeff.natDegree)
  have hc: (M.place γ).value c=1 :=
    hval.antisymm (le_of_not_gt fun h=>hγbad (mem_filter.mpr ⟨hγT,h⟩))
  obtain ⟨hi,hj⟩:=regular_of_unit S (M.place γ).value hb hc
  exact ⟨hc,hi,fun j i k=> by simpa only [Nat.cast_zero,WithZero.exp_zero] using hj j i k⟩
private theorem root_restrict {J U} (B:DualWord J U) (F:Raw) (γ:K)
    (h:atDual B F γ=0) :
    specialize (restrictOver (RingHom.id L) (dcQ J γ) F) (B.P γ) (B.Q γ)=0:= by
  unfold atDual Y3.embed at h
  unfold specialize restrictOver
  rw [eval₂_eq_eval_map] at h ⊢
  simp only [coe_mapRingHom,Polynomial.map_map] at h ⊢
  change _=0 at h
  have hm:P5_7_7.phys.comp (MvPolynomial.eval₂Hom (mapRingHom (RingHom.id L))
      (C ∘ dcQ J γ)) =
      (qD (J.model.label γ)).comp (MvPolynomial.map phys) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [qD,P5_7_7.phys]
    · intro i
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',Function.comp_apply,
        MvPolynomial.map_X,qD,MvPolynomial.eval_X]
      fin_cases i <;> simp [dcQ,jz,P5_7_7.phys]
  rw [hm]
  exact h
private theorem content_ne {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] LaurentSeries L) (g:E[X]) (P Q:L[X])
    (h: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a g.leadingCoeff)=1) :
    specialize (cLN a 0 (C g)) P Q≠0:= by
  have hu: (a g.leadingCoeff).coeff 0≠0:= by
    intro hz
    obtain ⟨z,hz'⟩:=(LaurentSeries.val_le_one_iff_eq_coe L _).mp h.le
    have hv :=(small_valuation z).mpr ((power_residue _ z hz'.symm).symm.trans hz)
    rw [hz',h] at hv
    exact (not_le_of_gt (WithZero.exp_lt_one_iff.mpr (by decide))) hv
  let b:=(cLN a 0 (C g)).coeff 0
  have he :cLN a 0 (C g)=C b:= by
    apply Polynomial.ext
    intro i
    by_cases hi:i=0
    · subst i
      exact coeff_C_zero.symm
    · apply Polynomial.ext
      intro j
      rw [expansion_coeff,coeff_C,ite_eq_right hi,coeff_C,ite_eq_right hi]
      simp
  rw [he,specialize,eval₂_C]
  intro hz
  have hb:b=0:=(map_eq_zero_iff phys (IsFractionRing.injective L[X] FX)).mp hz
  apply hu
  have hf :b.coeff g.natDegree=0:= by rw [hb,coeff_zero]
  simpa only [b,expansion_coeff,coeff_C_zero,coeff_natDegree] using hf
private theorem t4 {J U} (B:DualWord J U) {q T} (M:MarkedCurve q (dcQ J) T)
    (F:Raw) (S:Factors M.curve (restrict M.curve F)) (γ:K) (hγ:γ∈T)
    (hc: (M.place γ).value S.content.leadingCoeff=1)
    (hci : ∀ i,(M.place γ).value (S.content.coeff i)≤1)
    (hfi : ∀ j,IntegralAt M γ (S.factor j)) (hr :atDual B F γ=0) :
    ∃ j,specialize (cLN (M.atPlace γ hγ) 0 (S.factor j)) (B.P γ) (B.Q γ)=0:= by
  let A:AtSite M.curve (dcQ J γ) :=
    ⟨M.atPlace γ hγ,M.place γ,M.value γ hγ,M.arc γ hγ⟩
  obtain ⟨g,hg,hgr⟩:=integral_restrict A F
  have h₀ (i j:ℕ) :
      (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (A.map (((C S.content).coeff i).coeff j))≤1 := by
    rw [← A.value,coeff_C]
    split
    · exact hci j
    · simp
  let h₁ (k :Fin S.n) i j:=A.value _ ▸ hfi k i j
  let f₀:=Ua A.map (C S.content) h₀
  let f₁ (k :Fin S.n) :=Ua A.map (S.factor k) (h₁ k)
  have hm₀:mapTwice IntSeries.subtype f₀=mapTwice A.map.toRingHom (C S.content) :=
    map_liftAt _ _ _
  have hm₁ (k :Fin S.n) :mapTwice IntSeries.subtype (f₁ k)=mapTwice A.map.toRingHom (S.factor k) :=
    map_liftAt _ _ _
  have he :g=f₀ * ∏ k,f₁ k := by
    apply Polynomial.map_injective (mapRingHom IntSeries.subtype)
      (Polynomial.map_injective IntSeries.subtype IntSeries.subtype_injective)
    change mapTwice IntSeries.subtype g=mapTwice IntSeries.subtype _
    rw [hg]
    refine (congrArg (mapTwice A.map.toRingHom) S.product_eq).trans ?_
    simp only [map_mul,map_prod,hm₀,hm₁]
  have he' := congrArg (mapTwice residue) he
  rw [hgr,map_mul,map_prod] at he'
  have hr₀:mapTwice residue f₀=cLN A.map 0 (C S.content) :=liftAt_reduce _ _ _
  have hr₁ (k :Fin S.n) :mapTwice residue (f₁ k)=cLN A.map 0 (S.factor k) :=
    liftAt_reduce _ _ _
  simp only [hr₀,hr₁] at he'
  let ev :=eval₂RingHom phys (phys (B.P γ)/phys (B.Q γ))
  have hz :ev (restrictOver (RingHom.id L) (dcQ J γ) F)=0:=root_restrict B F γ hr
  rw [he',map_mul,map_prod,mul_eq_zero] at hz
  have hn:ev (cLN A.map 0 (C S.content))≠0 :=
    content_ne A.map S.content (B.P γ) (B.Q γ) ((A.value _).symm.trans hc)
  obtain ⟨j,_,hj⟩:=Finset.prod_eq_zero_iff.mp (hz.resolve_left hn)
  exact ⟨j,hj⟩
private theorem t5 {q z T} (M:MarkedCurve q z T) (G:Finset K) (hG:G⊆T)
    (f :M.curve.E[X][X]) (hi:Irreducible f) (hd:0<f.natDegree) (hp:f.natDegree<p)
    (hn:f.leadingCoeff.leadingCoeff=1) (hint : ∀ γ∈G,IntegralAt M γ f) :
    ∃ bad:Finset K,bad⊆G∧bad.card≤2*f.natDegree*coeffHeight f ∧
      ∀ γ (hγ:γ∈G),γ∉bad→((cLN (M.atPlace γ (hG hγ)) 0 f).map phys).Separable := by
  let A (γ:G) :AtSite M.curve (z γ) :=
    ⟨M.atPlace γ (hG γ.property),M.place γ,M.value γ (hG γ.property),M.arc γ (hG γ.property)⟩
  have hA:Function.Injective (fun γ:G=>(A γ).place) := fun a b h =>
    Subtype.ext (M.distinct (hG a.property) (hG b.property) h)
  let B:=G.attach.filter fun γ => ¬ (coeffIntegral (A γ).place.value f ∧
    ((cLN (A γ).map 0 f).map P5_7_7.phys).Separable)
  have hB:B.card≤2*f.natDegree*coeffHeight f :=
    qb2k8ya.proof M.curve G.attach (fun γ=>z γ) A hA.injOn f hi hd hp hn
  refine ⟨B.map (Function.Embedding.subtype _),fun γ hγ => ?_,(card_map _).trans_le hB,
    fun γ hγ hgood => ?_⟩
  · obtain ⟨a,_,rfl⟩:=mem_map.mp hγ
    exact a.property
  · by_contra hsep
    exact hgood (mem_map.mpr ⟨⟨γ,hγ⟩,mem_filter.mpr ⟨mem_attach _ _,fun h=>hsep h.2⟩,rfl⟩)
private theorem simple_of_separable (f :L[X][X]) (P Q:L[X])
    (h: (f.map phys).Separable) (hr :specialize f P Q=0) :
    specialize f.derivative P Q≠0:= by
  have h₀: (f.map phys).eval (phys P/phys Q)=0:= by
    rw [eval_map]
    exact hr
  have hn:=h.eval₂_derivative_ne_zero (RingHom.id FX) (by simpa only [eval₂_id] using h₀)
  rw [eval₂_id,derivative_map,eval_map] at hn
  exact hn
private theorem fraction (x :FX) :
    ∃ a b:L[X],b≠0∧IsCoprime a b∧phys a/phys b=x := by
  let e :FX ≃ₐ[L[X]] RatFunc L:=FractionRing.algEquiv (A:=L[X]) (RatFunc L)
  let r :=e x
  refine ⟨r.num,r.denom,r.denom_ne_zero,r.isCoprime_num_denom,e.injective ?_⟩
  simpa only [map_div₀,phys,e.commutes] using r.num_div_denom
theorem proof :qE3Ebna.c1 := by
  intro J U B q hq T hT ha F W hF hd hp hw hr
  obtain ⟨M⟩:=t1 q hq (dcQ J) T (injective_seeds J).injOn ha
  obtain ⟨S,hdegree,hweight⟩:=t2 B M.curve F W hF hd hw
  obtain ⟨G,hG,hbad,hheight,hint⟩:=t3 M F S
  have hdeg (j:Fin S.n) : (S.factor j).natDegree≤F.natDegree :=
    (single_le_sum (fun i _=>Nat.zero_le (S.factor i).natDegree) (mem_univ j)).trans hdegree
  choose bad hZG hZ hsep using fun j=>t5 M G hG (S.factor j) (S.irreducible j)
    (S.positive j) ((hdeg j).trans_lt hp) (S.normalized j) (fun γ hγ=>(hint γ hγ).2.2 j)
  let R (j:Fin S.n) (γ:K) (hγ:γ∈T) :Prop :=
    specialize (cLN (M.atPlace γ hγ) 0 (S.factor j)) (B.P γ) (B.Q γ)=0
  let V (j:Fin S.n) :=(G \ bad j).filter fun γ => ∃ hγ:γ∈T,R j γ hγ
  have inside (j:Fin S.n) :V j⊆T :=
    fun _ hγ=>hG (mem_sdiff.mp (mem_filter.mp hγ).1).1
  have good {j:Fin S.n} {γ:K} (hγ:γ∈V j) :γ∈G∧γ∉bad j :=
    mem_sdiff.mp (mem_filter.mp hγ).1
  have root {j:Fin S.n} {γ:K} (hγ:γ∈V j) :R j γ (inside j hγ) := by
    obtain ⟨_,h⟩:=(mem_filter.mp hγ).2
    exact h
  let t (j:Fin S.n) (γ:K) :FX :=
    if hγ:γ∈T then zD (M.atPlace γ hγ) (S.factor j) (B.P γ) (B.Q γ) else 0
  choose a b hb hab hfrac using fun (j:Fin S.n) (γ:K)=>fraction (t j γ)
  let part (j:Fin S.n) :Sheet B M.curve :=
    { f :=S.factor j
      irreducible :=S.irreducible j
      positive :=S.positive j
      normalized:=S.normalized j
      marks :=V j
      Bp:=(inside j).trans hT
      atPlace := fun γ hγ=>M.atPlace γ (inside j hγ)
      place :=M.place
      distinct :=M.distinct.mono (inside j)
      value := fun γ hγ=>M.value γ (inside j hγ)
      arc := fun γ hγ=>M.arc γ (inside j hγ)
      integral:= fun γ hγ=>(hint γ (good hγ).1).2.2 j
      root := fun _ hγ=>root hγ
      separable := fun γ hγ=>hsep j γ (good hγ).1 (good hγ).2
      simple := fun γ hγ =>
        simple_of_separable _ _ _ (hsep j γ (good hγ).1 (good hγ).2) (root hγ)
      num :=a j
      den:=b j
      den_ne := fun γ _=>hb j γ
      reduced:= fun γ _=>hab j γ
      formula := fun γ hγ=> by simpa only [t,dite_eq_left (inside j hγ)] using hfrac j γ }
  refine ⟨⟨M.curve,S.n,part,inside,?_,hdegree,hheight,hweight⟩⟩
  have hcover :T \ univ.biUnion V⊆(T \ G)∪univ.biUnion bad:= by
    intro γ hγ
    obtain ⟨hγT,hn⟩:=mem_sdiff.mp hγ
    by_cases hg:γ∈G
    · obtain ⟨hc,hci,hfi⟩:=hint γ hg
      obtain ⟨j,hj⟩:=t4 B M F S γ hγT hc hci hfi (hr γ hγT)
      refine mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ j,?_⟩)
      by_contra hz
      exact hn (mem_biUnion.mpr ⟨j,mem_univ j,mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨hg,hz⟩,hγT,hj⟩⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hγT,hg⟩)
  let H :=gY (Y3.embed F)*q.totalDegree
  have hs : (univ.biUnion bad).card≤2*F.natDegree*H := calc
    _ ≤ ∑ j,(bad j).card:=card_biUnion_le
    _ ≤ ∑ j,2*F.natDegree*coeffHeight (S.factor j) :=sum_le_sum fun j _ =>
      (hZ j).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hdeg j)))
    _≤_:= by rw [← mul_sum]; exact Nat.mul_le_mul_left _ hheight
  change (T \ univ.biUnion V).card≤(7+2*F.natDegree)*gY (Y3.embed F)*q.totalDegree
  calc
    _≤(T \ G).card+(univ.biUnion bad).card:=(card_le_card hcover).trans (card_union_le _ _)
    _≤H+2*F.natDegree*H :=Nat.add_le_add hbad hs
    _=(1+2*F.natDegree)*H := by rw [add_mul,one_mul]
    _≤_:= by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_right H (Nat.add_le_add_right (by decide) _)
end
end P5_7_2_6Q1
end
section
set_option autoImplicit true
namespace qcuzNoc
theorem proof :q8SCoCa.c1 :=
  P5_7_2_6Q1.proof
end qcuzNoc
end
