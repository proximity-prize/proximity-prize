import ProximityPrize.SubmissionLower.Z5tZ7td
import ProximityPrize.SubmissionLower.Zl7U3sa
set_option Elab.async false
open _root_ renaming Finsupp.mapDomain_apply_of_injective → zm3, Nat.mul_le_mul_left → zBI, Polynomial.C → z1z, Polynomial.X → z7y, Set.Finite.mem_toFinset → zih
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qckEfrc
noncomputable section

open P5_7_1 (wD)
open qH0Nw9c (LineRow LineCaps)


open MvPolynomial Finset
open scoped Polynomial
private abbrev e := _root_.finSuccEquiv 2
private theorem rename_caps {f :cu.Jet} {g:LineRow} (h:LineCaps f g) :
   rename e g∈Box (wD f 0) (wD f 1) (wD f 2) := by
 classical
 rw [mem_restrictCappedBidegree]
 intro m hm
 rw [support_rename_of_injective e.injective] at hm
 obtain ⟨n,hn,rfl⟩:=mem_image.mp hm
 obtain ⟨hb,hj,hu⟩:=h n hn
 refine ⟨?_,?_,?_⟩
 · change n.mapDomain e (e 0)≤_
   rwa [zm3 e.injective]
 · change (n.mapDomain e).some.degree≤_
   rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]
   change n.mapDomain e (e 1)+n.mapDomain e (e 2)≤_
   simpa only [zm3 e.injective] using hb
 · change n.mapDomain e (e 2)≤_
   rwa [zm3 e.injective]
end
end qckEfrc
end
section
namespace qziIa4d
noncomputable section
open Polynomial Finset
open qFD8jve (aFA polarResultant)
open scoped WithZero
variable {E :Type} [Field E] {v :Valuation E ℤᵐ⁰}
private def Bounded (g:E[X]) (c:ℤᵐ⁰) :Prop := ∀ i,v (g.coeff i)≤ c
private theorem afg {g h:E[X]} {a b:ℤᵐ⁰}
  (hg:Bounded (v :=v) g a) (hh:Bounded (v :=v) h b) :
  Bounded (v :=v) (g*h) (a*b) := by
 intro i
 rw [coeff_mul]
 exact v.map_sum_le fun j _=> by
  rw [map_mul]
  exact mul_le_mul' (hg j.1) (hh j.2)
private theorem bmr {ι:Type} {g:ι→E[X]} {c:ℤᵐ⁰} (s :Finset ι)
   (h : ∀ j∈s,Bounded (v :=v) (g j) c) :
   Bounded (v :=v) (∏ j∈s,g j) (c^s.card) := by
 classical
 induction s using Finset.induction_on with
 | empty=>intro i; by_cases hi:i=0 <;> simp [hi,coeff_one]
 | insert j s hj ih =>
   rw [prod_insert hj,card_insert_of_notMem hj,pow_succ']
   exact afg (h j (mem_insert_self _ _)) (ih fun k hk=>h k (mem_insert_of_mem hk))
private theorem cast_le_one (n:ℕ) :v (n:E)≤1 := by
 induction n with
 | zero=>simp
 | succ n ih=>rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)
theorem guard_le {F:E[X][X]} {b:ℕ} (hd:0<F.natDegree)
    (h:aFA v F b) :v (siteGuard F)≤WithZero.exp ((2*F.natDegree*b:ℕ) :ℤ) := by
  classical
  let d:=F.natDegree
  let c:ℤᵐ⁰:=WithZero.exp (b:ℤ)
  let M:=sylvester F F.derivative d (d-1)
  have he (i j:Fin (d+(d-1))) :Bounded (v :=v) (M i j) c:= by
    intro k
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
      split
      · rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast,
          coeff_mul_C,map_mul]
        simpa using mul_le_mul' (h ((i:ℕ)-(a :ℕ)+1) k)
          (cast_le_one (v :=v) ((i:ℕ)-(a :ℕ)+1))
      · simp
    · intro a
      simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
      split
      · exact h _ k
      · simp
  have hM:Bounded (v :=v) M.det (c^(d+(d-1))) := by
    intro k
    rw [Matrix.det_apply,finsetSum_coeff]
    apply v.map_sum_le
    intro π _
    have hπ:=bmr (v :=v) univ (fun j _=>he (π j) j) k
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;>
      simpa [hs,Valuation.map_neg] using hπ
  have hr :=hM (polarResultant F).natTrailingDegree
  have hz :v (F.leadingCoeff.coeff 0)≤ c:=h d 0
  rw [siteGuard,map_mul]
  calc
    _≤ c^(d+(d-1))*c:=mul_le_mul' hr hz
    _ = _:= by
      rw [← pow_succ,show d+(d-1)+1=2*d by dsimp [d]; omega]
      simp [c,d,← WithZero.exp_nsmul]
end
end qziIa4d
end
section
namespace qziIa4d
noncomputable section
open Finset Polynomial
open P5 (K p)
open cu (L FX)
open P5_7_7 (phys)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation targetHit exception)
open qb0hmCe (CurveModel SiteTarget cLN specialize zD)
open qFD8jve (aFA sheetPole seedPole polarResultant)
open E7 (CurvePlace axV poleOrder KB Tq)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet C z S} (V:Variation F),F.d<p → ∀ R:SiteTarget,
      (∃ γ∈V.marks,targetHit R z S γ)→Nonempty (Chart V R)
def c2 :Prop :=
  ∀ {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet C z S} {V:Variation F} {R:SiteTarget} (T:Chart V R)
    (γ:K) (hγ:γ∈V.marks),targetHit R z S γ →
    let a :=F.atPlace γ (V.Bp hγ)
    ∃ Q:L[X],Q.coeff 0≠0 ∧
      specialize (cLN a 0 T.G) 1 Q=0 ∧
      specialize (cLN a 0 T.G).derivative 1 Q≠0 ∧
      zD a T.G 1 Q =
        -(phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ)) -
          phys (z1z (slope F R γ)))/phys (z7y:L[X])
def c3:Prop :=TameDerivative
def c4 :Prop :=
  TameDerivative → ∀ {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] LaurentSeries L) (G:E[X][X]),
    let v :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap a.toRingHom
    0<G.natDegree→G.natDegree<p→G.leadingCoeff.coeff 0≠0 →
    polarResultant G≠0→aFA v G 0→v (siteGuard G)=1 →
    ∀ Q:L[X],Q.coeff 0≠0→specialize (cLN a 0 G) 1 Q=0 →
      specialize (cLN a 0 G).derivative 1 Q≠0→atZeroRegular (zD a G 1 Q)
private theorem test {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet C z S} (V:Variation F) (R:SiteTarget) (T:Chart V R)
    (γ:K) (hγ:γ∈V.marks) (hh:targetHit R z S γ) (Q:L[X])
    (hid :zD (F.atPlace γ (V.Bp hγ)) T.G 1 Q =
      -(phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ)) -
        phys (z1z (slope F R γ)))/phys (z7y:L[X]))
    (hreg:atZeroRegular (zD (F.atPlace γ (V.Bp hγ)) T.G 1 Q)) :
    ¬ exception V R γ:= by
  obtain ⟨A,B,hb,hreg⟩:=hreg
  let N :=taylor R.center (V.num γ)
  let D:=taylor R.center (V.den γ)
  let s :=slope F R γ
  have hi:Function.Injective phys :=IsFractionRing.injective L[X] FX
  have hnz {g:L[X]} (h:g≠0) :phys g≠0:= fun hg=>h (hi (hg.trans phys.map_zero.symm))
  have hB:phys B≠0:=hnz (fun h=>hb (by simp [h]))
  have hD:phys D ≠0:=hnz ((taylor_eq_zero _ _).not.mpr (V.den_ne γ hγ))
  have h:=(div_eq_iff (hnz X_ne_zero)).mp (hid.symm.trans hreg)
  change -(phys N/phys D - phys (z1z s))=phys A/phys B*phys z7y at h
  have hr :phys N/phys D =phys (z1z s)-(phys A/phys B*phys z7y) := by
    linear_combination -h
  have hr' : phys N/phys D =phys (z1z s*B - A*z7y)/phys B:= by
    rw [hr,div_mul_eq_mul_div₀,sub_div' hB,map_sub,map_mul,map_mul]
  have hc:N*B=(z1z s*B - A*z7y)*D :=
    hi (by simpa only [map_mul] using (div_eq_div_iff hD hB).mp hr')
  have he :=congrArg (fun g:L[X]=>g.coeff 0) hc
  simp only [mul_coeff_zero,coeff_sub,coeff_C_zero,coeff_X_zero,mul_zero,sub_zero] at he
  rw [mul_right_comm s (B.coeff 0) (D.coeff 0)] at he
  have hn:=mul_right_cancel₀ hb he
  rw [taylor_coeff_zero,taylor_coeff_zero] at hn
  have heD: (V.den γ).eval R.center≠0:= by
    intro hd
    have hN : (V.num γ).eval R.center=0:=hn.trans (by simp [hd])
    obtain ⟨u,w,hw⟩:=(V.reduced γ hγ).map (evalRingHom R.center)
    simp [hN,hd] at hw
  intro he
  apply he.2
  rw [hn,mul_eq_zero,or_iff_left heD]
  simp [s,slope,div_eq_zero_iff,pow_ne_zero 2 hh.1]
private theorem sum_le_all {α:Type} (f :α→ℕ) (hf :f.HasFiniteSupport) (s :Finset α) :
  ∑ i∈s,f i ≤ ∑ᶠ i,f i:= by
 classical
 rw [finsum_eq_finsetSum_of_support_subset f (s :=hf.toFinset∪s) (fun _ hi =>
  mem_union_left _ ((zih _).mpr hi))]
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
theorem of_children (bY:c1) (transport:c2) (tame :c3) (local_test :c4) :P5_7_3_5_2.c2 := by
  intro q C z S F V hp R
  let T:=V.marks.filter (exception V R)
  by_cases hm : ∃ γ∈V.marks,targetHit R z S γ
  swap
  · have he :T = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ=> by
      obtain ⟨hs,hr,_⟩:=mem_filter.mp hγ
      exact hm ⟨γ,hs,hr⟩
    change T.card≤_
    simp [he]
  obtain ⟨J⟩:=bY V hp R hm
  have hd:0<J.G.natDegree :=J.degree ▸ F.positive
  let g:=siteGuard J.G
  have hg:g≠0:=mul_ne_zero (mt trailingCoeff_eq_zero.mp J.separant) J.leading
  have hb (γ:K) (hγ:γ∈T) :1≤KB (F.place γ).value g:= by
    obtain ⟨hs,hr,he⟩:=mem_filter.mp hγ
    have hv : (F.place γ).value g≤1 := by
      simpa only [g,Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero] using guard_le hd (J.integral γ hs hr)
    have hn: (F.place γ).value g≠1 := by
      intro hunit
      obtain ⟨Q,hQ,hroot,hsimple,heq⟩:=transport J γ hs hr
      let a :=F.atPlace γ (V.Bp hs)
      let v :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap a.toRingHom
      have hv_eq (c:C.E) :v c=(F.place γ).value c:=(F.value γ (V.Bp hs) c).symm
      have hi:aFA v J.G 0:= fun i j=>(hv_eq _).trans_le (J.integral γ hs hr i j)
      exact test V R J γ hs hr Q heq
        (local_test tame a J.G hd (J.degree ▸ hp) J.leading J.separant hi
          ((hv_eq g).trans hunit) Q hQ hroot hsimple) ⟨hr,he⟩
    have hlog:WithZero.log ((F.place γ).value g)<(0:ℤ) :=
      (WithZero.log_lt_iff_lt_exp (by simpa using hg)).2 (by simpa using lt_of_le_of_ne hv hn)
    unfold KB
    omega
  have hdiv :axV L C.E :=
    aFU.of_children
      bRt.proof bRu.proof L C.E C.curve
  obtain ⟨hf,hz,hsum,_⟩:=hdiv g
  let U:=hf.toFinset
  let H (v :CurvePlace L C.E) :=sheetPole v.value F.f
  let seedCost (v :CurvePlace L C.E) :=seedPole C R v.value
  have hH :H.HasFiniteSupport:=finite_tuple hdiv _
  have hZ:seedCost.HasFiniteSupport∧(∑ᶠ v,seedCost v)≤R.height q:= by
    by_cases h:R.b=0∧R.d=0
    · simp [seedCost,seedPole,SiteTarget.height,Function.HasFiniteSupport,h]
    · exact ⟨by simpa [seedCost,seedPole,h] using (hdiv (C.seed R.coord)).1,
        by simpa [seedCost,seedPole,SiteTarget.height,h] using C.co6 R.coord⟩
  have hpoint (v :CurvePlace L C.E) :poleOrder v.value g≤2*F.d*(H v+F.d*seedCost v) := by
    have hv :v.value g≠0:= by simpa using hg
    have hb:=guard_le hd (J.bound v)
    rw [J.degree] at hb
    exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp hv).2 hb)
  have hP: (∑ᶠ v :CurvePlace L C.E,poleOrder v.value g)≤2*F.d*(F.h+F.d*R.height q) := by
    rw [finsum_eq_finsetSum_of_support_subset _ (s :=U)
      (fun v hv=>(zih _).mpr hv)]
    calc
      _ ≤ ∑ v∈U,2*F.d*(H v+F.d*seedCost v) :=sum_le_sum fun v _=>hpoint v
      _=2*F.d*((∑ v∈U,H v)+F.d*(∑ v∈U,seedCost v)) := by
        simp only [mul_sum,Nat.mul_add,sum_add_distrib]
      _≤_:=zBI _
        (Nat.add_le_add (sum_le_all H hH U)
          (zBI _ ((sum_le_all seedCost hZ.1 U).trans hZ.2)))
  have hinj:Set.InjOn F.place (T:Set K) := fun _ hi _ hj =>
    F.distinct (V.Bp (mem_filter.mp hi).1) (V.Bp (mem_filter.mp hj).1)
  calc
    T.card = ∑ γ∈T,(1 :ℕ) := by simp
    _ ≤ ∑ γ∈T,KB (F.place γ).value g:=sum_le_sum hb
    _ = ∑ v∈T.image F.place,KB v.value g:= by rw [sum_image hinj]
    _ ≤ ∑ᶠ v :CurvePlace L C.E,KB v.value g:=sum_le_all _ hz _
    _ = ∑ᶠ v :CurvePlace L C.E,poleOrder v.value g:=hsum.symm
    _≤_:=hP
end
end qziIa4d
end
