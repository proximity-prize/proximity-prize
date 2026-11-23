import ProximityPrize.SubmissionLower.Z99zqBd
import ProximityPrize.SubmissionLower.ZFdiUYb
import ProximityPrize.SubmissionLower.ZQfUTPd
import ProximityPrize.SubmissionLower.ZjSNLAa
import ProximityPrize.SubmissionLower.ZlnMfEd
import ProximityPrize.SubmissionLower.ZPpouqc
set_option Elab.async false
section
section
namespace qgpYCte
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna
open P5 (K p)
open cu (L)
open E7 (CurvePlace poleOrder)
open qb0hmCe (CurveModel)
open qps5rle (atArc initialAt leadAt)
open private zero_count lead_nonzero chart_budget from ProximityPrize.SubmissionLower.Zd8LTIa
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C:CurveModel q}
    (S:Sheet B C) (R:SiteTarget),
    (∃ γ∈S.marks,matchesTarget R B γ)→Nonempty (SiteChart S R)
def c2 :Prop :=
  ∀ {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C:CurveModel q}
    (S:Sheet B C),S.d<p → ∀ (R:SiteTarget) (T:SiteChart S R),
    let D:=initialAt R.center S.f.discr
    D ≠0 ∧
    (∑ᶠ v :CurvePlace L C.E,poleOrder v.value D)≤(2*S.d-2)*S.h ∧
    ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ→1≤(S.place γ).value D →
      (initialAt R.center (atArc (S.atPlace γ hγ) T.g).discr).coeff 0≠0
theorem of_children (bY:c1) (disc:c2)
    (tame :qps5rle.c3) (specialize :qps5rle.c4) :
    qE3Ebna.c2 := by
  intro J U B q C S hp R
  by_cases hm : ∃ γ∈S.marks,matchesTarget R B γ
  · obtain ⟨T⟩:=bY S R hm
    obtain ⟨hd,hheight,hdisc⟩:=disc S hp R T
    let D:=initialAt R.center S.f.discr
    let b:=leadAt R.center T.g
    let bad (e :C.E) :=S.marks.filter fun γ=>(S.place γ).value e<1
    have hcover :S.marks.filter (exceptional R S)⊆bad b∪bad D:= by
      intro γ hγ
      obtain ⟨hS,hmatch,hex⟩:=mem_filter.mp hγ
      by_contra hout
      have hb:1≤(S.place γ).value b :=
        le_of_not_gt (fun h=>hout (mem_union_left _ (mem_filter.mpr ⟨hS,h⟩)))
      have hD:1≤(S.place γ).value D :=
        le_of_not_gt (fun h=>hout (mem_union_right _ (mem_filter.mpr ⟨hS,h⟩)))
      let a :=S.atPlace γ hS
      let f :=atArc a T.g
      have hf :f.natDegree=S.d :=
        (natDegree_map_eq_of_injective (Polynomial.map_injective _ a.injective) _).trans T.degree
      have hint :=T.integral γ hS hmatch
      have hlead: (leadAt R.center f).coeff 0≠0 :=
        lead_nonzero a _ _ hint (by rwa [← S.value γ hS b])
      have hdisc' : (initialAt R.center f.discr).coeff 0≠0:=hdisc γ hS hmatch hD
      have hT:=tame R.center f (hf.symm ▸ S.positive) (hf.symm ▸ hp)
        (fun hz=>hlead (hz ▸ by simp)) (fun hz=>hdisc' (by simp [hz,initialAt]))
      obtain ⟨A,hA⟩:=T.jet γ hS hmatch
      exact hex (hA (specialize R.center f hint hlead hdisc' hT A))
    exact ((card_le_card hcover).trans (card_union_le _ _)).trans
      ((Nat.add_le_add ((zero_count S b T.lead_ne).trans T.lead_height)
        ((zero_count S D hd).trans hheight)).trans (chart_budget R S.d S.h q S.positive))
  · have h:S.marks.filter (exceptional R S) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨hS,hmatch,_⟩:=mem_filter.mp hγ
      exact hm ⟨γ,hS,hmatch⟩
    rw [h,card_empty]
    exact Nat.zero_le _
end
end qgpYCte
end
section
set_option maxHeartbeats 700000
namespace qERExMc
noncomputable section
open Polynomial Finset qwGrtCa
open scoped Classical
open private ew subst subst_comp rehom from ProximityPrize.SubmissionLower.ZjSNLAa
open private bOH from ProximityPrize.SubmissionLower.Znkyowe
variable {R T:Type} [CommRing R] [CommRing T]
theorem transform_comp (a b c d e f g h:R) (n:ℕ) (P:R[X]) :
   transform e f g h n (transform a b c d n P) =
     transform (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) n P:= by
 conv_lhs=>rw [transform,rehom]
 change ew (((subst e f g h).comp (subst a b c d)) (P.homogenize n))= _
 rw [subst_comp,transform]
theorem transform_map (φ:R →+* T) (a b c d:R) (n:ℕ) (P:R[X]) :
  (transform a b c d n P).map φ =
    transform (φ a) (φ b) (φ c) (φ d) n (P.map φ) := by
 simp only [transform_sum,Polynomial.map_sum,coeff_map,Polynomial.map_mul,
  Polynomial.map_pow,Polynomial.map_add,
  form,map_C,map_X]
theorem transform_scale (a b c d s :R) (n:ℕ) (P:R[X]) :
  transform a b c d n (C s*P)=C s*transform a b c d n P:= by
 simp only [transform_sum,coeff_C_mul,mul_sum,map_mul,mul_assoc]
private theorem form_pow_bound (u v :R) (j:ℕ) : ((form u v)^j).natDegree≤j:= by
 have h: (form u v).natDegree≤1 := by
  simpa only [form,add_comm] using (natDegree_linear_le (a :=u) (b:=v))
 exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left j h)
theorem transform_degree (a b c d:R) (n:ℕ) (P:R[X]) :
   (transform a b c d n P).natDegree≤n:= by
 rw [transform_sum]
 refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
 rw [mul_assoc]
 exact (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans
   ((Nat.add_le_add (form_pow_bound a b i) (form_pow_bound c d (n-i))).trans_eq
     (Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi)))))
private theorem form_pow_top [IsDomain R] (a b:R) (i:ℕ) :
   ((form a b)^i).coeff i=a^i:= by
 by_cases h:a=0
 · subst a
   cases i <;> simp [form,← map_pow]
 have hd: (form a b).natDegree=1 := by
   rw [form,natDegree_C_add,natDegree_C_mul_X _ h]
 have hl: (form a b).leadingCoeff=a := by
   rw [leadingCoeff,hd]
   simp [form]
 simpa only [hd,mul_one,hl] using coeff_pow_mul_natDegree (form a b) i
theorem transform_top [IsDomain R] (a b c d:R) (n:ℕ) (P:R[X]) :
  (transform a b c d n P).coeff n = ∑ i∈range (n+1),P.coeff i*a^i*c^(n-i) := by
 rw [transform_sum,finsetSum_coeff]
 apply sum_congr rfl
 intro i hi
 have he :i+(n-i)=n:=Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))
 have ht:=coeff_mul_add_eq_of_natDegree_le (form_pow_bound a b i) (form_pow_bound c d (n-i))
 rw [he,form_pow_top,form_pow_top] at ht
 rw [mul_assoc,coeff_C_mul,ht,mul_assoc]
variable {E :Type} [Field E]
theorem strip_physical (H :E[X][X]) (hH :H≠0) :
   ∃ (n:ℕ) (H₀:E[X][X]),H=C ((Polynomial.X (R:=E))^n)*H₀ ∧
     H₀.map (evalRingHom (0:E))≠0:= by
 let J:=Bivariate.swap H
 have hJ:J≠0:= fun h=>hH (Bivariate.swap.injective (h.trans (map_zero _).symm))
 let n:=J.natTrailingDegree
 obtain ⟨U,he⟩: (Polynomial.X (R:=E[X]))^n∣J:=X_pow_dvd_iff.mpr fun _ h =>
   coeff_eq_zero_of_lt_natTrailingDegree h
 have h0:U.coeff 0≠0:= by
   have h:=coeff_natTrailingDegree_ne_zero.mpr hJ
   change J.coeff n≠0 at h
   have hc:=coeff_X_pow_mul U n 0
   rw [zero_add,← he] at hc
   exact hc ▸ h
 refine ⟨n,Bivariate.swap U,?_,?_⟩
 · have h:=congrArg Bivariate.swap he
   simpa only [J,Bivariate.swap_swap_apply,map_mul,map_pow,Bivariate.swap_Y] using h
 · intro hz
   apply h0
   ext j
   have h:=congrArg (fun u:E[X]=>u.coeff j) hz
   simpa only [coeff_map,coe_evalRingHom,← coeff_zero_eq_eval_zero,bOH,
     coeff_zero] using h
end
end qERExMc
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qZV9OWb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open cu (L FX)
open P5_7_7 (phys)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (expansion_coeff Ua liftAt_reduce residue power_residue small_valuation principal reduced_pair)
open qFD8jve (aFA polarResultant)
open P5_7_3_5_2 (Sheet Variation atPolynomial)
open qrezXJe (branch branch_exists bD9 resultant_val_le sheet_bound sum_zeroOrder)
open E7 (CurvePlace KB)
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private efc adG cTA aMX from ProximityPrize.SubmissionLower.Y
variable {q:Curve} {Cq:CurveModel q} {z :K→K} {s :K→K[X]}
private theorem cfo (w:CurvePlace L Cq.E) (f :Cq.E[X][X]) (b:ℕ)
  (h:aFA w.value f b) (j:ℕ) :
  w.value ((polarResultant f).coeff j)≤WithZero.exp (((2*f.natDegree-1)*b:ℕ) :ℤ) := by
 let v :=efc w.value
 let u:ℤᵐ⁰:=WithZero.exp (b:ℤ)
 have hF (i:ℕ) :v (f.coeff i)≤u:=Finset.sup_le fun k _=>h i k
 have hG (i:ℕ) :v (f.derivative.coeff i)≤u:= by
  rw [coeff_derivative,map_mul,← Nat.cast_succ,← C_eq_natCast]
  change _ *adG w.value (Polynomial.C ((i+1 :ℕ) :Cq.E))≤_
  rw [cTA]
  exact (mul_le_mul' (hF _) (cast_le_one (v :=w.value) (i+1))).trans_eq (mul_one _)
 refine (aMX w.value _ j).trans ?_
 change v (polarResultant f)≤_
 refine (resultant_val_le v f f.derivative _ _ _ hF hG).trans_eq ?_
 rw [show f.natDegree+(f.natDegree-1)=2*f.natDegree-1 by omega,← WithZero.exp_nsmul]
 simp [mul_comm]
private theorem residue_ne (y :LaurentSeries L)
  (hy : (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) y=1) :y.coeff 0≠0:= by
 obtain ⟨u,hu⟩:=(LaurentSeries.val_le_one_iff_eq_coe L y).mp hy.le
 intro h0
 have hz :=(small_valuation u).mpr ((power_residue _ _ hu.symm).symm.trans h0)
 rw [hu,hy,← WithZero.exp_zero] at hz
 have h:=WithZero.exp_le_exp.mp hz
 omega
private theorem separant_at (F:Sheet Cq z s) (hp:F.d<p) {γ:K} (hγ:γ∈F.marks)
    (j:ℕ) (hj: (F.place γ).value ((polarResultant F.f).coeff j)=1) :
    ((cLN (F.atPlace γ hγ) 0 F.f).map phys).Separable := by
  let a :=F.atPlace γ hγ
  let G:=Ua a F.f (fun i k=>(F.value γ hγ _).symm.trans_le (F.integral γ hγ i k))
  let f₀:=cLN a 0 F.f
  let incl:=(LaurentSeries.powerSeries_as_subring L).subtype
  have hG:G.map (mapRingHom incl)=F.f.map (mapRingHom a.toRingHom) := by
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro k
    simp only [coeff_map,coe_mapRingHom,incl,Subring.subtype_apply]
    exact q1kuFjb.coeff_liftAt a F.f _ i k
  have hG₀:G.map (mapRingHom residue)=f₀:=liftAt_reduce _ _ _
  let R:=G.resultant G.derivative F.d (F.d-1)
  have hR₁:R.map incl=(polarResultant F.f).map a.toRingHom:= by
    calc
      _=(G.map (mapRingHom incl)).resultant (G.derivative.map (mapRingHom incl)) F.d (F.d-1) :=
        (resultant_map_map G G.derivative F.d (F.d-1) (mapRingHom incl)).symm
      _ = _:= by
        rw [← derivative_map,hG,derivative_map,resultant_map_map]
        rfl
  have hR₀:R.map residue=f₀.resultant f₀.derivative F.d (F.d-1) := by
    calc
      _=(G.map (mapRingHom residue)).resultant (G.derivative.map (mapRingHom residue)) F.d (F.d-1) :=
        (resultant_map_map G G.derivative F.d (F.d-1) (mapRingHom residue)).symm
      _ = _:= by rw [← derivative_map,hG₀]
  have hr : (f₀.resultant f₀.derivative F.d (F.d-1)).coeff j≠0:= by
    rw [← hR₀,coeff_map,q1kuFjb.fWQ]
    have he :=congrArg (fun f : (LaurentSeries L)[X]=>f.coeff j) hR₁
    simp only [coeff_map,incl,Subring.subtype_apply,AlgHom.toRingHom_eq_coe] at he
    rw [he]
    exact residue_ne _ ((F.value γ hγ _).symm.trans hj)
  have hb:f₀.natDegree=F.d:= by
    refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_) ?_
    · ext k
      dsimp only [f₀]
      rw [expansion_coeff,coeff_eq_zero_of_natDegree_lt hi]
      simp
    · apply le_natDegree_of_ne_zero
      intro h
      have hzero :=congrArg (fun f :L[X]=>f.coeff (F.f.coeff F.d).natDegree) h
      simp only [f₀,expansion_coeff,coeff_zero] at hzero
      change (a ((F.f.coeff F.d).leadingCoeff)).coeff 0=0 at hzero
      rw [F.normalized,map_one] at hzero
      simp at hzero
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP FX p:=charP_of_injective_ringHom (IsFractionRing.injective L[X] FX)
    p
  let f :=f₀.map phys
  have hd:f.natDegree=F.d:=(natDegree_map_eq_of_injective
    (IsFractionRing.injective L[X] FX) _).trans hb
  have hd' : f.derivative.natDegree=F.d-1 := by
    rw [bD9 (hd.symm ▸ F.positive) (hd.symm ▸ hp),hd]
  have hn:f.resultant f.derivative≠0:= by
    rw [hd,hd']
    change (f₀.map phys).resultant (f₀.map phys).derivative F.d (F.d-1)≠0
    rw [derivative_map,resultant_map_map]
    exact (map_ne_zero_iff phys (IsFractionRing.injective L[X] FX)).mpr
      (fun h=>hr (by rw [h,coeff_zero]))
  change f.Separable
  by_contra hs
  exact hn (resultant_eq_zero_iff.mpr ⟨Or.inl (ne_zero_of_natDegree_gt (by rw [hd]; exact F.positive)),hs⟩)
theorem aWY (S:Sheet Cq z s) (D W:ℕ) (hp:S.d<p) (hW:S.weight D W) :
   ∃ V:Variation S,(S.marks \ V.marks).card≤(2*S.d-1)*S.h ∧
     ∀ γ (hγ:γ∈V.marks),((cLN (S.atPlace γ (V.Bp hγ)) 0 S.f).map phys).Separable := by
 obtain ⟨r,hn,_,_⟩:=branch_exists S.f D W S.irreducible S.positive hp hW
 have hR:polarResultant S.f≠0:= fun hz=>hn (by simp [branch,hz])
 let j:=(polarResultant S.f).natDegree
 let c:=(polarResultant S.f).coeff j
 have hc:c≠0:=leadingCoeff_ne_zero.mpr hR
 let T:=S.marks.filter fun γ=>(S.place γ).value c=1
 have hT:T⊆S.marks :=filter_subset _ _
 have hs (γ:K) (hγ:γ∈T) :
     ((cLN (S.atPlace γ (hT hγ)) 0 S.f).map phys).Separable :=
   separant_at S hp (hT hγ) j (mem_filter.mp hγ).2
 have hsimple (γ:K) (hγ:γ∈T) :
     atPolynomial (cLN (S.atPlace γ (hT hγ)) 0 S.f).derivative (s γ)≠0:= by
   let g:=cLN (S.atPlace γ (hT hγ)) 0 S.f
   have hr : (g.map phys).eval (phys (cu.j9 (s γ)))=0:= by
     rw [eval_map]
     exact S.root γ (hT hγ)
   have h:=(hs γ hγ).eval₂_derivative_ne_zero (RingHom.id FX) (by simpa only [eval₂_id] using hr)
   rw [eval₂_id,derivative_map,eval_map] at h
   exact h
 let τ (γ:K) :FX:=if hγ:γ∈T then
   -(atPolynomial (cLN (S.atPlace γ (hT hγ)) 1 S.f) (s γ) /
     atPolynomial (cLN (S.atPlace γ (hT hγ)) 0 S.f).derivative (s γ)) else 0
 choose num den hden hcop hfrac using fun γ=>reduced_pair (τ γ)
 let V:Variation S:=⟨T,hT,num,den,fun γ _=>hden γ,fun γ _=>hcop γ,hsimple,
   fun γ hγ=>(hfrac γ).trans (dite_eq_left hγ)⟩
 refine ⟨V,?_,hs⟩
 change (S.marks \ T).card≤_
 have hcard: (S.marks \ T).card ≤ ∑ γ∈S.marks \ T,KB (S.place γ).value c:= by
   rw [card_eq_sum_ones]
   apply sum_le_sum
   intro γ hγ
   obtain ⟨hm,ht⟩:=mem_sdiff.mp hγ
   have hi:aFA (S.place γ).value S.f 0:= by simpa [aFA] using S.integral γ hm
   have hv : (S.place γ).value c≤1 := by simpa [c] using cfo _ _ 0 hi j
   have hl: (S.place γ).value c<1 :=lt_of_le_of_ne hv
     (fun he=>ht (mem_filter.mpr ⟨hm,he⟩))
   have hlog:=(WithZero.log_lt_log ((S.place γ).value.ne_zero_iff.mpr hc) one_ne_zero).mpr hl
   rw [WithZero.log_one] at hlog
   unfold KB
   omega
 exact hcard.trans (sum_zeroOrder (principal Cq) _ S.place
   (S.distinct.mono (fun _ h=>(mem_sdiff.mp h).1)) S.f c _ hc (fun w =>
     cfo w _ _ (sheet_bound w.value S.f) j))
end
end qZV9OWb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qZV9OWb
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K p)
open cu (L)
open E7 (CurveField CurvePlace axV poleOrder KB Tq Gb)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel cLN)
open qNu3xvc (Equation Sections GraphVal Over qg NoHorizontalPole
 horizontalDegree finitePoles poleCharge)
open qZu9hjc (valueZeros valueCoeffs)
open P5_7_3_5_2 (Sheet Variation)
open P5_7_7 (phys)
def c1 :Prop :=
  ∀ {q:Curve} {Cq:CurveModel q} {z :K→K} {s :K→K[X]}
    (S:Sheet Cq z s) (V:Variation S) (D W:ℕ),
    0<D→2≤S.d→S.d<p→S.d*D ≤W→S.weight D W →
    (∀ γ∈V.marks,(s γ).natDegree≤D) →
    (∀ γ (hγ:γ∈V.marks),((cLN (S.atPlace γ (V.Bp hγ)) 0 S.f).map phys).Separable) →
    ∃ (A:Equation Cq.E) (T:Sections A),
      A.d=S.d∧A.s=D ∧A.b+A.d*A.s=W∧A.h≤S.h ∧
      T.marks=V.marks∧T.place=S.place∧(∀ γ∈T.marks,T.Q γ=1) ∧
      ∑ γ∈V.marks,V.DG D γ≤finitePoles T
def c2 :Prop :=qNu3xvc.c2
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (T:Sections A),
    CurveField L E→2≤A.d→A.d<p→NoHorizontalPole A →
    ∀ γ∈T.marks,T.Q γ=1 → ∀ x∈(T.den γ).roots.toFinset,
      ∃ v :GraphVal A false,Over v (T.place γ) x ∧
        (T.den γ).rootMultiplicity x≤poleCharge v
def c4 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),
    CurveField L E→0<A.s→2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (v :ι→GraphVal A false),
      Function.Injective (fun i=>(w i,x i)) →
      (∀ i,qg A (w i))→(∀ i,Over (v i) (w i) (x i)) →
      ∃ B:ValueSlice A,
        (∑ i,poleCharge (v i)) ≤ ∑ u∈univ.image w,valueZeros u.value B.N
def c5:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),
    CurveField L E→0<A.s→A.s<p→2≤A.d→A.d<p →
    ∀ B:ValueSlice A,
      Gb L E (valueCoeffs B.N)≤ rate A.d A.s (A.b+A.d*A.s)*A.h
private theorem sum_values {E :Type} [Field E] [Algebra L E]
   (hdiv :axV L E) (T:Finset (CurvePlace L E)) (N :E[X]) :
   (∑ v∈T,valueZeros v.value N)≤Gb L E (valueCoeffs N) := by
 let pord (v :CurvePlace L E) :=poleOrder v.value (N.coeff 0)
 let zord (v :CurvePlace L E) :=KB v.value (N.coeff 0)
 let height (v :CurvePlace L E) :=Tq v.value (valueCoeffs N)
 obtain ⟨hp,hz,heq,_⟩:=hdiv (N.coeff 0)
 have hh:=agN.b27 hdiv (valueCoeffs N)
 let U:=T∪hh.toFinset∪hp.toFinset∪hz.toFinset
 have hsP:Function.support pord⊆(U:Set (CurvePlace L E)) := fun _ hv =>
   mem_union_left _ (mem_union_right _ (hp.mem_toFinset.mpr hv))
 have hsZ:Function.support zord⊆(U:Set (CurvePlace L E)) := fun _ hv =>
   mem_union_right _ (hz.mem_toFinset.mpr hv)
 have hsH :Function.support height⊆(U:Set (CurvePlace L E)) := fun _ hv =>
   mem_union_left _ (mem_union_left _ (mem_union_right _ (hh.mem_toFinset.mpr hv)))
 have hTU:T⊆U:= fun _ hv=>mem_union_left _ (mem_union_left _ (mem_union_left _ hv))
 have he : ∑ v∈U,pord v = ∑ v∈U,zord v := by
   rw [← finsum_eq_sum_of_support_subset pord hsP,← finsum_eq_sum_of_support_subset zord hsZ]
   exact heq
 have ht: (∑ v∈U,valueZeros v.value N)+(∑ v∈U,pord v) =
     (∑ v∈U,height v) + ∑ v∈U,zord v := by
   rw [← sum_add_distrib,← sum_add_distrib]
   refine sum_congr rfl fun v _ => ?_
   have h:pord v≤height v :=Finset.le_sup (f := fun i=>poleOrder v.value (valueCoeffs N i))
     (mem_univ (⟨0,Nat.zero_lt_succ _⟩:Fin (N.natDegree+1)))
   change height v - pord v+zord v+pord v=height v+zord v
   omega
 exact (sum_le_sum_of_subset hTU).trans_eq
   ((show (∑ v∈U,valueZeros v.value N) = ∑ v∈U,height v by omega).trans
     (finsum_eq_sum_of_support_subset height hsH).symm)
private theorem finite_budget (exL:c3) (qW:c4) (degree :c5)
   {E :Type} [Field E] [Algebra L E] (A:Equation E) (T:Sections A)
   (hc:CurveField L E) (hs :0<A.s) (hsp:A.s<p) (hd:2≤A.d) (hp:A.d<p)
   (hor :NoHorizontalPole A) (hQ : ∀ γ∈T.marks,T.Q γ=1) :
   finitePoles T≤ rate A.d A.s (A.b+A.d*A.s)*A.h:= by
 let U:=T.marks.sigma fun γ=>(T.den γ).roots.toFinset
 let w (i : ↥U) :=T.place i.val.1
 let x (i : ↥U) :=i.val.2
 have hinj:Function.Injective (fun i=>(w i,x i)) := by
   intro i j hij
   have hi:=(mem_sigma.mp i.prop).1
   have hj:=(mem_sigma.mp j.prop).1
   exact Subtype.ext (Sigma.ext (T.distinct hi hj (congrArg Prod.fst hij))
     (heq_of_eq (congrArg Prod.snd hij)))
 have hlocal (i : ↥U) : ∃ v :GraphVal A false,Over v (w i) (x i) ∧
     (T.den i.val.1).rootMultiplicity (x i)≤poleCharge v := by
   obtain ⟨hγ,hx⟩:=mem_sigma.mp i.prop
   exact exL A T hc hd hp hor _ hγ (hQ _ hγ) _ hx
 choose v hv hle using hlocal
 obtain ⟨B,hB⟩:=qW A hc hs hd hp _ w x v hinj
   (fun i=>T.regular _ (mem_sigma.mp i.prop).1) hv
 have hdiv :axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hc
 calc
   finitePoles T = ∑ i : ↥U,(T.den i.val.1).rootMultiplicity (x i) := by
     change finitePoles T = ∑ i∈U.attach,(T.den i.val.1).rootMultiplicity i.val.2
     rw [Finset.sum_attach U (fun i=>(T.den i.1).rootMultiplicity i.2)]
     unfold U finitePoles
     rw [Finset.sum_sigma]
     refine sum_congr rfl fun γ _ => ?_
     rw [← IsAlgClosed.card_roots_eq_natDegree,← Multiset.toFinset_sum_count_eq]
     exact sum_congr rfl fun _ _=>Polynomial.count_roots _
   _ ≤ ∑ i,poleCharge (v i) :=sum_le_sum fun i _=>hle i
   _≤_:=hB.trans ((sum_values hdiv _ _).trans (degree A hc hs hsp hd hp B))
private theorem budgets {d e D W b:ℕ} (hd:2≤d) (hde :d≤e) (hW:e*D ≤W)
    (hb:b+d*D =W) :
    (2*d-2)*b+d*(d-1)*D ≤(2*e-1)*W-e^2*D ∧
      rate d D W≤ rate e D W:= by
  have he :2≤e :=hd.trans hde
  have hguard :e^2*D ≤(2*e-1)*W:= calc
    _=e*(e*D) := by ring
    _≤_:=Nat.mul_le_mul (by omega) hW
  have hrate (n:ℕ) (hn:2≤n) (hne :n≤e) :3*n^2*D ≤(6*n-2)*W:= calc
    _=(3*n)*(n*D) := by ring
    _≤_:=Nat.mul_le_mul (by omega) ((Nat.mul_le_mul_right D hne).trans hW)
  unfold rate
  zify [show 2≤2*d by omega,show 1≤d by omega,show 1≤2*e by omega,hguard,
    show 2≤6*d by omega,show 2≤6*e by omega,hrate d hd hde,hrate e he le_rfl]
    at hde hW hb ⊢
  have hgap:0≤(e :ℤ)-d:=sub_nonneg.mpr hde
  have hroom:0≤(W:ℤ)-e*D:=sub_nonneg.mpr hW
  have hD:0≤(D:ℤ) :=Int.natCast_nonneg D
  constructor <;> apply sub_nonneg.mp
  · calc
      _=((W:ℤ)-e*D)+((e :ℤ)-d)*(2*(W-e*D)+(e-d+1)*D) := by rw [← hb]; ring
      _≥0:=add_nonneg hroom (mul_nonneg hgap (add_nonneg
        (mul_nonneg (by decide) hroom) (mul_nonneg (by omega) hD)))
  · calc
      _=((e :ℤ)-d)*(6*(W-e*D)+3*(e-d)*D) := by ring
      _≥0:=mul_nonneg hgap (add_nonneg (mul_nonneg (by decide) hroom)
        (mul_nonneg (mul_nonneg (by decide) hgap) hD))
theorem of_children (rechart:c1) (Oj:c2) (exL:c3)
    (qW:c4) (QI:c5) :qXmh4Jb.c3:= by
  intro q Cq z s S D e W hD hd hde hp hW hguard hw hs
  have hdp:S.d<p:=hde.trans_lt hp
  have hdW:S.d*D ≤W:=(Nat.mul_le_mul_right D hde).trans hW
  have hDg:D ≤(2*e-1)*W-e^2*D:= by
    have he :2≤e :=hd.trans hde
    have hD' : D ≤(e-1)*(e*D) :=
      (Nat.le_mul_of_pos_left D (by omega :0<e)).trans
        (Nat.le_mul_of_pos_left (e*D) (by omega :0<e-1))
    have heq : (2*e-1)*(e*D)-e^2*D =(e-1)*(e*D) := by
      rw [show e^2*D =e*(e*D) by ring,← Nat.sub_mul,show 2*e-1-e=e-1 by omega]
    rw [← heq] at hD'
    exact hD'.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hW) _)
  have hDp:=hDg.trans_lt hguard
  obtain ⟨V,hV,hsep⟩:=aWY S D W hdp hw
  obtain ⟨A,T,hAd,hAs,hAb,hAh,_,_,hQ,hT⟩ :=
    rechart S V D W hD hd hdp hdW hw (fun γ hγ=>hs γ (V.Bp hγ)) hsep
  obtain ⟨hg,hr⟩:=budgets (b:=A.b) hd hde hW (by simpa only [hAd,hAs] using hAb)
  have hhor :horizontalDegree A<p:= by
    unfold horizontalDegree
    rw [hAd,hAs]
    exact hg.trans_lt hguard
  have hAd₂:2≤A.d:=hAd.symm ▸ hd
  have hAp:A.d<p:=hAd.symm ▸ hdp
  have hB:=finite_budget exL qW QI A T Cq.curve
    (hAs.symm ▸ hD) (hAs.symm ▸ hDp) hAd₂ hAp (Oj A hAd₂ hAp hhor) hQ
  rw [hAb,hAd,hAs] at hB
  exact ⟨V,hV.trans (Nat.mul_le_mul_right _ (by omega)),
    hT.trans (hB.trans (Nat.mul_le_mul hr hAh))⟩
end
end qZV9OWb
end
end
