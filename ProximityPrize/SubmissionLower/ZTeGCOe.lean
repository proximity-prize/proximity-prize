import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.ZGijG6c
import ProximityPrize.SubmissionLower.ZEdS9yd
set_option Elab.async false
section
set_option autoImplicit true
namespace qylJznc
noncomputable section
open Polynomial
open P6 (K)
open P6_7_3 (Input)
open qy95ATd (WordChart)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel SiteTarget cLN specialize zD)
open qFD8jve (polarResultant aFA sheetPole seedPole Vanishes)
open qH2fULd (Sheet targetMatch exception)
open cu (L)
open E7 (CurvePlace)
structure Chart {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve}
    {C:CurveModel q} (S:Sheet J C) (R:SiteTarget) where
  F:C.E[X][X]
  degree :F.natDegree=S.d
  leading:F.leadingCoeff.coeff 0≠0
  separant:polarResultant F≠0
  bound : ∀ v :CurvePlace L C.E,
    aFA v.value F (sheetPole v.value S.f+S.d*seedPole C R v.value)
  integral : ∀ γ∈S.marks,aFA (S.place γ).value F 0
  yq : ∀ γ (hγ:γ∈S.marks),targetMatch R J γ → ∃ P Q:L[X],
    P.coeff 0=0∧Q.coeff 0≠0 ∧
    specialize (cLN (S.atPlace γ hγ) 0 F) P Q=0 ∧
    specialize (cLN (S.atPlace γ hγ) 0 F).derivative P Q≠0 ∧
    (Vanishes (zD (S.atPlace γ hγ) F P Q) → ¬ exception R S γ)
end
end qylJznc
end
section
set_option autoImplicit true
namespace qylJznc
noncomputable section
open Finset Polynomial qFD8jve
open P6 (K p)
open P6_7_3 (Input)
open qy95ATd (WordChart)
open qH2fULd (Sheet targetMatch exception)
open qQ9yWTb (Curve)
open qb0hmCe (SiteTarget CurveModel)
open q2TwyLa (i5 polar RootData ReducedPencil)
open cu (L)
open E7 (CurvePlace axV poleOrder KB Tq)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C),S.d<p → ∀ R:SiteTarget,
      (∃ γ∈S.marks,targetMatch R J γ)→Nonempty (Chart S R)
def c2 :Prop :=
  ∀ f :i5[X][X],0<f.natDegree→f.natDegree<p→polar f≠0 →
    Nonempty (RootData f)
def c3:Prop :=
  ∀ f :i5[X][X],0<f.natDegree→f.leadingCoeff.coeff 0≠0→polar f≠0 →
    RootData f→Nonempty (ReducedPencil f)
private theorem sum_le_all {α:Type} (f :α→ℕ) (hf :f.HasFiniteSupport) (s :Finset α) :
    ∑ i∈s,f i ≤ ∑ᶠ i,f i:= by
  rw [finsum_eq_finsetSum_of_support_subset f (s :=hf.toFinset∪s) (by
    intro i hi
    exact mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hi))]
  exact sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _=>Nat.zero_le _
private theorem finite_tuple {E σ:Type} [Field E] [Algebra L E] [Fintype σ]
    (h:axV L E) (u:σ→E) :
    (fun v :CurvePlace L E=>Tq v.value u).HasFiniteSupport:= by
  have hf : (⋃ i:σ,Function.support (fun v :CurvePlace L E =>
      poleOrder v.value (u i))).Finite :=Set.finite_iUnion fun i=>(h (u i)).1
  apply hf.subset
  intro v hv
  simp only [Set.mem_iUnion,Function.mem_support] at hv ⊢
  by_contra! hz
  exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun i _=>hz i)
theorem of_children (bY:c1) (tame :c2) (normalize :c3) :qH2fULd.c2 := by
  have local_test :=q2TwyLa.of_children tame normalize
  intro x U J q C S hp R
  let T:=S.marks.filter (exception R S)
  by_cases hm : ∃ γ∈S.marks,targetMatch R J γ
  swap
  · have he :T = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ=> by
      obtain ⟨hs,hr,_⟩:=mem_filter.mp hγ
      exact hm ⟨γ,hs,hr⟩
    change T.card≤_
    simp [he]
  obtain ⟨A⟩:=bY S hp R hm
  have hd:0<A.F.natDegree :=A.degree ▸ S.positive
  let g:=guard A.F
  have hc:aaD A.F≠0:= by
    intro hz
    have h:=congrArg (fun f :C.E[X]=>f.coeff A.F.natDegree) hz
    exact A.leading (by
      simpa only [aaD,coeff_map,coe_evalRingHom,← coeff_zero_eq_eval_zero,
        leadingCoeff,coeff_zero] using h)
  have hg:g≠0:=mul_ne_zero
    (mt trailingCoeff_eq_zero.mp A.separant) (mt trailingCoeff_eq_zero.mp hc)
  have hb (γ:K) (hγ:γ∈T) :1≤KB (S.place γ).value g:= by
    obtain ⟨hs,hr,he⟩:=mem_filter.mp hγ
    have hv : (S.place γ).value g≤1 := by
      simpa only [g,Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero] using guard_le hd (A.integral γ hs)
    have hn: (S.place γ).value g≠1 := by
      intro hunit
      obtain ⟨P,Q,hP,hQ,hroot,hsimple,hagree⟩:=A.yq γ hs hr
      let a :=S.atPlace γ hs
      let v :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap a.toRingHom
      have hv_eq (c:C.E) :v c=(S.place γ).value c:=(S.value γ hs c).symm
      have hi:aFA v A.F 0:= fun i j=>(hv_eq _).trans_le (A.integral γ hs i j)
      exact hagree (local_test C.E a A.F hd (A.degree ▸ hp) A.leading A.separant hi
        ((hv_eq g).trans hunit) P Q hP hQ hroot hsimple) ⟨hr,he⟩
    have hv0: (S.place γ).value g≠0:= by simpa using hg
    have hlog:WithZero.log ((S.place γ).value g)<(0:ℤ) :=
      (WithZero.log_lt_iff_lt_exp hv0).2 (by simpa using lt_of_le_of_ne hv hn)
    unfold KB
    omega
  have hdiv :axV L C.E :=
    aFU.of_children
      bRt.proof bRu.proof L C.E C.curve
  obtain ⟨hf,hz,hsum,_⟩:=hdiv g
  let V:=hf.toFinset
  let H (v :CurvePlace L C.E) :=sheetPole v.value S.f
  let seedCost (v :CurvePlace L C.E) :=seedPole C R v.value
  have hH :H.HasFiniteSupport:=finite_tuple hdiv _
  have hZ:seedCost.HasFiniteSupport∧(∑ᶠ v,seedCost v)≤R.height q:= by
    by_cases h:R.b=0∧R.d=0
    · simp [seedCost,seedPole,SiteTarget.height,Function.HasFiniteSupport,h]
    · exact ⟨by simpa [seedCost,seedPole,h] using (hdiv (C.seed R.coord)).1,
        by simpa [seedCost,seedPole,SiteTarget.height,h] using C.co6 R.coord⟩
  have hpoint (v :CurvePlace L C.E) :
      poleOrder v.value g≤2*S.d*(H v+S.d*seedCost v) := by
    have hv :v.value g≠0:= by simpa using hg
    have hb:=guard_le hd (A.bound v)
    rw [A.degree] at hb
    exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp hv).2 hb)
  have hP: (∑ᶠ v :CurvePlace L C.E,poleOrder v.value g)≤2*S.d*(S.h+S.d*R.height q) := by
    rw [finsum_eq_finsetSum_of_support_subset _ (s :=V)
      (fun v hv=>(Set.Finite.mem_toFinset _).mpr hv)]
    calc
      _ ≤ ∑ v∈V,2*S.d*(H v+S.d*seedCost v) :=sum_le_sum fun v _=>hpoint v
      _=2*S.d*((∑ v∈V,H v)+S.d*(∑ v∈V,seedCost v)) := by
        simp only [mul_sum,Nat.mul_add,sum_add_distrib]
      _≤_:=Nat.mul_le_mul_left _
        (Nat.add_le_add (sum_le_all H hH V)
          (Nat.mul_le_mul_left _ ((sum_le_all seedCost hZ.1 V).trans hZ.2)))
  have hinj:Set.InjOn S.place (T:Set K) := fun _ hi _ hj =>
    S.distinct (mem_filter.mp hi).1 (mem_filter.mp hj).1
  calc
    T.card = ∑ γ∈T,(1 :ℕ) := by simp
    _ ≤ ∑ γ∈T,KB (S.place γ).value g:=sum_le_sum hb
    _ = ∑ v∈T.image S.place,KB v.value g:= by rw [sum_image hinj]
    _ ≤ ∑ᶠ v :CurvePlace L C.E,KB v.value g:=sum_le_all _ hz _
    _ = ∑ᶠ v :CurvePlace L C.E,poleOrder v.value g:=hsum.symm
    _≤_:=hP
end
end qylJznc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qO4n7sd
noncomputable section
open Polynomial Finset
open P6 (K)
open cu (L FX)
open P6_7_3 (Input)
open qy95ATd (WordChart)
open qH2fULd (Sheet poleOrderAt)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel cLN specialize zD)
open q1kuFjb (expansion_coeff)
open qNu3xvc (Equation Sections qg finitePoles)
open qfJaLMa (cap move move_degree move_coeff pad_bound choose_cap
  move_irred changeY exp_move exp_ord_degree move_val_le aJj move_height)
open P5_7_7 (phys)
open qWIOgVd (bY rev width width_bound rev_ne rev_coprime rev_ratio rev_degree x x_ne)
open private eval_change deriv_change cancel_ratio layer_repr from ProximityPrize.SubmissionLower.ZGijG6c
open scoped Classical WithZero
theorem transport
    {input:Input} {U:Finset K} {J:WordChart input U} {q:Curve} {Cq:CurveModel q}
    (S:Sheet J Cq) (b:ℕ)
    (hw : ∀ i,(S.f.coeff i).natDegree+i*(J.u₁-J.u₀)≤b+S.d*(J.u₁-J.u₀) ∨
      S.f.coeff i=0) :
    ∃ (A:Equation Cq.E) (T:Sections A),
      A.d=S.d∧A.s=J.u₁-J.u₀∧A.b=b∧A.h≤S.h ∧
      (∑ γ∈S.marks,poleOrderAt S γ)≤finitePoles T:= by
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset
    (S.marks.biUnion fun γ=>(S.den γ).roots.toFinset)
  have hfresh (γ:K) (hγ:γ∈S.marks) : (S.den γ).eval a≠0:= fun hz =>
    ha (mem_biUnion.mpr ⟨γ,hγ,Multiset.mem_toFinset.mpr ((mem_roots (S.den_ne γ hγ)).mpr hz)⟩)
  let s :=J.u₁-J.u₀
  obtain ⟨k,hkb,hb,hhit⟩:=choose_cap S.irreducible.ne_zero s b hw
  let D:=bY a
  let g:=move (algebraMap L Cq.E a) s k S.d S.f
  have hd:g.natDegree=S.d:=move_degree _ _ _ _ S.irreducible.ne_zero
  have hgwt (i:ℕ) : (g.coeff i).natDegree+i*s≤b+g.natDegree*s∨g.coeff i=0:= by
    by_cases hz :g.coeff i=0
    · exact Or.inr hz
    have hi:i≤S.d:=hd ▸ le_natDegree_of_ne_zero hz
    have hh: (g.coeff i).natDegree≤ cap s k S.d i:= by rw [move_coeff]; exact pad_bound _ (hb i)
    have he : (S.d-i)*s+i*s=S.d*s := by rw [← add_mul,Nat.sub_add_cancel hi]
    rw [hd]
    unfold cap at hh
    exact Or.inl (by omega)
  let A:Equation Cq.E :=⟨g,move_irred S.irreducible S.positive hb hhit,hd.symm ▸ S.positive,
    s,b,hgwt⟩
  let m (γ:K) :=width s (J.P γ) (J.Q γ)
  let t (γ:K) :=s+2*m γ
  let n (γ:K) :=width (t γ) (S.num γ) (S.den γ)
  let P' (γ:K) :=rev a (m γ+s) (J.P γ)
  let Q' (γ:K) :=rev a (m γ) (J.Q γ)
  let N' (γ:K) :=rev a (n γ+t γ) (S.num γ)
  let B' (γ:K) :=rev a (n γ) (S.den γ)
  let c:FX:=x^(k+S.d*s)
  let v :FX:=x^s
  have hc:c≠0:=pow_ne_zero _ x_ne
  have hv :v≠0:=pow_ne_zero _ x_ne
  let changeOrd:=changeY D.changeX v hv
  let e :=S.atPlace
  have repr (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      (cLN (e γ hγ) j g).map phys=C c*changeOrd ((cLN (e γ hγ) j S.f).map phys) :=
    layer_repr (e γ hγ) j D s k S.f hb
  have hdeg (γ:K) (hγ:γ∈S.marks) : (cLN (e γ hγ) 0 g).natDegree=S.d:= by
    have h₀: (cLN (e γ hγ) 0 S.f).coeff S.d≠0:= by
      intro hz
      have he :=expansion_coeff (e γ hγ) 0 S.f S.d (S.f.coeff S.d).natDegree
      rw [hz,coeff_zero,← leadingCoeff,S.normalized,map_one] at he
      simp [HahnSeries.coeff_one] at he
    rw [exp_move,move_degree _ _ _ _ (fun h=>h₀ (by rw [h,coeff_zero]))]
    exact (exp_ord_degree _ _ _).antisymm (le_natDegree_of_ne_zero h₀)
  have hval (γ:K) (hγ:γ∈S.marks) (i j:ℕ) :
      (S.place γ).value ((g.coeff i).coeff j)≤1 :=move_val_le _ a s k S.d S.f (S.integral γ hγ) i j
  have hreg (γ:K) (hγ:γ∈S.marks) :qg A (S.place γ) := by
    refine ⟨hval γ hγ,?_⟩
    let F:=cLN (e γ hγ) 0 g
    have hF:F.natDegree=S.d:=hdeg γ hγ
    have hn:F.coeff S.d≠0:= by
      rw [← hF,← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr (fun h=>S.positive.ne' (hF.symm.trans (by rw [h,natDegree_zero])))
    refine ⟨S.d,(F.coeff S.d).natDegree,aJj (S.place γ) (e γ hγ) (S.value γ hγ _)
      (hval γ hγ _ _) ?_⟩
    rw [← expansion_coeff,← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hn
  have hsep (γ:K) (hγ:γ∈S.marks) : ((cLN (e γ hγ) 0 g).map phys).Separable := by
    let F:=(cLN (e γ hγ) 0 S.f).map phys
    rw [repr,separable_def,deriv_change]
    exact (isCoprime_mul_units_left (hc.isUnit.map C)
      ((mul_ne_zero hc (inv_ne_zero hv)).isUnit.map C) _ _).mpr
      (((separable_def F).mp (S.separable γ hγ)).map changeOrd.toRingHom)
  have hratio (γ:K) :phys (P' γ)/phys (Q' γ) =
      v*D.changeX (phys (J.P γ)/phys (J.Q γ)) :=rev_ratio D s
  have hsp (γ:K) (hγ:γ∈S.marks) (j:ℤ) :
      specialize (cLN (e γ hγ) j g) (P' γ) (Q' γ) =
        c*D.changeX (specialize (cLN (e γ hγ) j S.f) (J.P γ) (J.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,hratio,repr,eval_mul,eval_C]
    rw [eval_change]
  have hdsp (γ:K) (hγ:γ∈S.marks) :
      specialize (cLN (e γ hγ) 0 g).derivative (P' γ) (Q' γ) =
        (c*v⁻¹)*D.changeX (specialize (cLN (e γ hγ) 0 S.f).derivative (J.P γ) (J.Q γ)) := by
    simp only [specialize,eval₂_eq_eval_map,← derivative_map,hratio,repr]
    rw [deriv_change D.changeX v hv,eval_mul,eval_C,eval_change]
  let T:Sections A := {
    marks :=S.marks
    place :=S.place
    distinct :=S.distinct
    atPlace :=e
    value :=S.value
    regular :=hreg
    degree := fun γ hγ=>(hdeg γ hγ).trans hd.symm
    separable :=hsep
    P:=P'
    Q:= Q'
    denom:= fun γ hγ=>rev_ne a _ (J.denominator γ (S.Bp hγ))
    coprime := fun γ hγ=>rev_coprime a s (J.denominator γ (S.Bp hγ)) (J.coprime γ (S.Bp hγ))
    root := fun γ hγ=> by rw [hsp,S.root γ hγ,map_zero,mul_zero]
    simple := fun γ hγ=> by
      rw [hdsp]
      exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero hv))
        ((map_ne_zero_iff _ D.changeX.injective).mpr (S.simple γ hγ))
    num :=N'
    den:=B'
    den_ne := fun γ hγ=>rev_ne a _ (S.den_ne γ hγ)
    reduced:= fun γ hγ=>rev_coprime a _ (S.den_ne γ hγ) (S.reduced γ hγ)
    formula := fun γ hγ=> by
      rw [rev_ratio D (t γ),S.formula γ hγ]
      unfold zD
      rw [hsp,hdsp,cancel_ratio _ _ _ _ hc,show Q' γ=rev a (m γ) (J.Q γ) from rfl,
        D.CJ _ _ (width_bound s (J.P γ) (J.Q γ)).2]
      simp only [map_mul,map_neg,map_pow,map_div₀,mul_pow,t,pow_add,v]
      rw [Nat.mul_comm 2 (m γ),pow_mul]
      simp only [e,m,neg_mul,mul_neg]
      exact congrArg Neg.neg (mul_mul_mul_comm _ _ _ _) }
  refine ⟨A,T,hd,rfl,rfl,move_height Cq.curve a s k S.d S.f,le_of_eq ?_⟩
  apply sum_congr rfl
  intro γ hγ
  change n γ=(B' γ).natDegree
  exact (rev_degree (width_bound (t γ) (S.num γ) (S.den γ)).2 (hfresh γ hγ)).symm
end
end qO4n7sd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qO4n7sd
noncomputable section
open P6 (p)
open qy95ATd (left width)
open qH2fULd (poleRate)
open qNu3xvc (horizontalDegree polarRate)
open private finite_budget budgets from ProximityPrize.SubmissionLower.ZbbSEle
def c1 :Prop :=qNu3xvc.c2
def c2 :Prop :=qNu3xvc.c3
def c3:Prop :=qNu3xvc.c4
theorem of_children (Oj:c1) (charge :c2) (degree :c3) :
    qH2fULd.c3:= by
  intro input U J q C S e W hde hp hF hW hchar hwt
  let d:=S.d
  let u:=left J
  let s :=J.u₁-J.u₀
  let b:=W-d*(u+s)
  have hb:b+d*(u+s)=W:= by
    apply Nat.sub_add_cancel
    exact (Nat.mul_le_mul hde (by omega :u+s≤width)).trans hW
  obtain ⟨A,T,hd,hs,hB,hh,ht⟩:=transport S b (by
    intro i
    rcases hwt i with hi | hi
    · left
      change (S.f.coeff i).natDegree+d*u+i*s≤W at hi
      change (S.f.coeff i).natDegree+i*s≤b+d*s
      have hsum:b+(d*u+d*s)=W:= by simpa only [Nat.mul_add] using hb
      omega
    · exact Or.inr hi)
  change A.d=d at hd
  change A.s=s at hs
  obtain ⟨hguard,hrate⟩:=budgets d e b u s W width S.positive hde hW hb hF
  have hbound:polarRate A≤poleRate e W:= by
    unfold polarRate poleRate qy95ATd.polar
    rw [hd,hs,hB]
    exact hrate
  refine ht.trans (le_trans ?_ (Nat.mul_le_mul hbound hh))
  by_cases hlin:A.d = 1
  · apply (qn3rrcc.proof A T C.curve hlin).trans
    apply Nat.mul_le_mul_right
    unfold polarRate
    rw [hlin]
    omega
  · have hpos :1≤A.d:=A.positive
    have hd₂:2≤A.d:=Nat.succ_le_of_lt (lt_of_le_of_ne hpos (Ne.symm hlin))
    have hAp:A.d<p:=hd ▸ hde.trans_lt hp
    have hsmall:horizontalDegree A<p:= by
      unfold horizontalDegree
      rw [hd,hs,hB]
      exact hguard.trans_lt hchar
    exact finite_budget charge degree A T C.curve hd₂ hAp (Oj A hd₂ hAp hsmall)
end
end qO4n7sd
end
