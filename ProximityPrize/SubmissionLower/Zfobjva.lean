import ProximityPrize.SubmissionLower.Zgvu91a
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, MvPolynomial.ringHom_ext → zXT, Polynomial.C → z1z, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, PowerSeries.ext → zub, PowerSeries.map → zS4, RingHom.comp_apply → zQb
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7R
noncomputable section
open Polynomial qL2osVa
open P5_7_3_3_4_1_7 (CutEquation targetDen targetNum)
open cu (L)
open Cu (sQ)
variable {C₀:sQ} [Fact (Irreducible C₀)]
def normalized (C:MarkedSheet C₀) (x :L) (r :Target) (a :L) :CutEquation C.sheet.n :=
  let e :=(taylorAlgHom (MvPolynomial.C (σ:=Fin 2 ⊕ Fin C.sheet.n) x)).toRingHom.comp
    (Polynomial.mapRingHom (MvPolynomial.rename (Sum.inr :Fin C.sheet.n→Fin 2 ⊕ Fin C.sheet.n)).toRingHom)
  let c:=(z1z: (Cut C.sheet.n)[X] →+* CutEquation C.sheet.n).comp z1z
  let v :=1+c (MvPolynomial.C a)*Polynomial.X
  let n:=c (targetNum r)*v+Polynomial.X
  let d:=c (targetDen r)*v
  ∑ i∈Finset.range (C.g+1),z1z (e (C.sheet.bY.equation.coeff i)) *
    n^i*d^(C.g - i)
end
end P5_7_3_3_4_1_7R
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7R_3
noncomputable section
open Polynomial hiding constantCoeff expand
open TrivSqZeroExt
open qL2osVa P5_7_3_3_4_1_7
open cu (L)
open PowerSeries (constantCoeff)
abbrev Dual (R:Type*) :=DualNumber R
def pair {R:Type*} (a b:R) :Dual R:=⟨a,b⟩
@[simp] theorem pair_fst {R:Type*} (a b:R) : (pair a b).fst=a :=rfl
@[simp] theorem pair_snd {R:Type*} (a b:R) : (pair a b).snd=b:=rfl
abbrev pO:DoubleSeries →+* Series :=zS4 constantCoeff
abbrev amd:Series →+* DoubleSeries :=zS4 zMG
def jet:DoubleSeries →+* Dual Series where
  toFun t:=pair (pO t) (seedFirst t)
  map_zero' := by ext <;> simp [seedFirst]
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one pO
    · apply zub
      intro i
      simp [seedFirst,PowerSeries.coeff_one,apply_ite (z2o 1)]
  map_add' f g:= by
    apply TrivSqZeroExt.ext
    · exact map_add pO f g
    · apply zub
      intro i
      simp [seedFirst]
  map_mul' f g:= by
    apply TrivSqZeroExt.ext
    · exact map_mul pO f g
    · change seedFirst (f*g)=pO f*seedFirst g+seedFirst f*pO g
      apply zub
      intro i
      simp only [seedFirst,PowerSeries.coeff_mk,PowerSeries.coeff_mul i,map_sum,
        map_add,PowerSeries.coeff_map,PowerSeries.coeff_one_mul,Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _=>mul_comm _ _
@[simp] theorem jet_fst (t:DoubleSeries) : (jet t).fst=pO t:=rfl
@[simp] theorem jet_snd (t:DoubleSeries) : (jet t).snd=seedFirst t:=rfl
theorem jet_C (a :Series) :jet (zMG a) =
    pair (zMG (constantCoeff a)) (zMG (z2o 1 a)) := by
  apply TrivSqZeroExt.ext
  · simp [PowerSeries.map_C]
  · apply zub
    intro i
    by_cases hi:i=0 <;> simp [seedFirst,PowerSeries.coeff_C,hi]
@[simp] theorem jet_lift (t:Series) :jet (amd t)=inl t:= by
  apply TrivSqZeroExt.ext <;> apply zub <;> intro i <;>
    simp [seedFirst]
private def fstRing:Dual Series →+* Series :=(TrivSqZeroExt.fstHom Series Series Series).toRingHom
theorem eval_fst (f :LocalEquation) (u:Dual Series) :
    (f.eval₂ jet u).fst=(seedFibre f).eval u.fst:= by
  change fstRing (f.eval₂ jet u)= _
  rw [hom_eval₂,eval₂_eq_eval_map]
  rfl
theorem eval_snd (f :LocalEquation) (s v :Series) :
    (f.eval₂ jet (pair s v)).snd=seedFirst (f.eval (amd s)) +
      (seedFibre f).derivative.eval s*v := by
  let F:=f.map jet
  have hpair :pair s v=inl s+inr v :=(inl_fst_add_inr_snd_eq (pair s v)).symm
  obtain ⟨b,hb⟩:=exists_mul_sq_add_linear_part_eq_eval_add F (inl s) (inr v)
  have hsq: (inr v :Dual Series)^2=0:= by rw [pow_two,inr_mul_inr]
  rw [hsq,mul_zero,zero_add,← hpair] at hb
  rw [eval₂_eq_eval_map]
  change (F.eval (pair s v)).snd= _
  rw [← hb]
  have hval :F.eval (inl s)=jet (f.eval (amd s)) := by
    rw [← jet_lift s,eval_map_apply]
  have hder : (F.derivative.eval (inl s)).fst=(seedFibre f).derivative.eval s := by
    rw [show F.derivative=f.derivative.map jet from derivative_map f jet,
      ← eval₂_eq_eval_map,eval_fst]
    change (f.derivative.map pO).eval s=(f.map pO).derivative.eval s
    rw [derivative_map]
  simp only [snd_add,DualNumber.snd_mul,hder,fst_inr,snd_inr,mul_zero,add_zero,hval,jet_snd]
  exact add_comm _ _
def aUs (x :L) :Series[X] →+* DoubleSeries :=
  coeToPowerSeries.ringHom.comp (taylorAlgHom (zMG x)).toRingHom
@[simp] theorem expand_C (x a :L) :expand x (z1z a)=zMG a := by
  simp [P5_7_3_3_4_1_7.expand]
@[simp] theorem expandSeed_C (x :L) (a :Series) :
    aUs x (z1z a)=zMG a := by
  simp [aUs]
@[simp] theorem expand_centre (x :L) (f :L[X]) :
    constantCoeff (expand x f)=f.eval x := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [P5_7_3_3_4_1_7.expand]
theorem expand_lift (x :L) (f :L[X]) :
    aUs x (f.map zMG)=amd (expand x f) := by
  change (↑(taylor (zMG x) (f.map zMG)) :DoubleSeries) =
    zS4 zMG (↑(taylor x f) :Series)
  rw [← polynomial_map_coe,map_taylor]
theorem expand_fst (x :L) (f :Series[X]) :
    pO (aUs x f)=expand x (f.map constantCoeff) := by
  change zS4 constantCoeff (↑(taylor (zMG x) f) :DoubleSeries) =
    (↑(taylor x (f.map constantCoeff)) :Series)
  rw [← polynomial_map_coe,map_taylor,PowerSeries.constantCoeff_C]
theorem expand_snd (x :L) (f :Series[X]) :
    seedFirst (aUs x f)=expand x (firstCoeff f) := by
  let e :Series →+* Dual Series :=jet.comp zMG
  have h:jet.comp (aUs x)=eval₂RingHom e (inl (expand x (Polynomial.X:L[X]))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [e]
    · simp only [zQb,coe_eval₂RingHom,eval₂_X]
      rw [← jet_lift,← expand_lift,map_X]
  change ((jet.comp (aUs x)) f).snd= _
  rw [h,coe_eval₂RingHom,eval₂_eq_sum,Polynomial.sum_def]
  simp only [snd_sum,e,zQb,jet_C,inl_pow,DualNumber.snd_mul,fst_inl,snd_inl,
    pair_fst,pair_snd,mul_zero,zero_add,firstCoeff,map_sum,← C_mul_X_pow_eq_monomial,
    map_mul,map_pow,expand_C]
end
end P5_7_3_3_4_1_7R_3
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P5_7_3_3_4_1_7
noncomputable section
open Polynomial qL2osVa
open P5 (K p)
open cu (L)
open Cu (sQ)
def c2 :Prop :=
  ∀ (f :LocalEquation) (g d j:ℕ),2≤g→ g<p→LocalGuard f g d j →
    ∀ s :Series,zbO s=0→(seedFibre f).eval s=0 →
      ∃ v :Series,ZeroJet f s v
variable {C₀:sQ} [Fact (Irreducible C₀)] {C:MarkedSheet C₀} {γ:K}
private theorem arc_generic (A:Arc C γ) (q:Cut C.sheet.n) :
    algebraMap Series SeriesField (arcEval A q)=A.embedding (C.bee q) := by
  have h: (algebraMap Series SeriesField).comp (arcEval A) =
      A.embedding.comp C.bee := by
    apply zXT
    · intro u
      simpa [arcEval,MarkedSheet.bee] using (A.constant_eq u).symm
    · rintro (i | i)
      · simpa [arcEval,MarkedSheet.bee] using (A.seed_eq i).symm
      · simpa [arcEval,MarkedSheet.bee] using (A.parameter_eq i).symm
  exact zmU h q
private theorem arc_marked (A:Arc C γ) (q:Cut C.sheet.n) :
    zbO (arcEval A q)=C.markedCut γ q:= by
  have h:PowerSeries.constantCoeff.comp (arcEval A)=C.markedCut γ:= by
    apply zXT
    · intro u
      simp [arcEval,MarkedSheet.markedCut]
    · rintro (i | i)
      · simpa [arcEval,MarkedSheet.markedCut] using A.seed_value i
      · simpa [arcEval,MarkedSheet.markedCut] using A.parameter_value i
  exact zmU h q
private theorem arc_zero (A:Arc C γ) {q:Cut C.sheet.n} :
    arcEval A q=0↔C.bee q=0:= by
  rw [← map_eq_zero_iff (algebraMap Series SeriesField) (IsFractionRing.injective _ _),
    arc_generic,map_eq_zero_iff _ A.embedding.injective]
private theorem hit_den {x :L} {r :Target} (h:r.hit (C:=C) x γ) :
    C.markedCut γ (targetDen r)≠0:= by
  cases r with
  | constant v=>simp [targetDen]
  | projective i a b c =>
      simpa [targetDen,MarkedSheet.markedCut] using h.1
private theorem coeff_local (A:Arc C γ) (q: (Cut C.sheet.n)[X]) (i:ℕ) :
    z2o i (bfj A q)=arcEval A (q.coeff i) := by
  simp [bfj]
private theorem unitOfInitial {R:Type*} [CommRing R] (u:zpm R) (d:ℕ)
    (h₀ : ∀ i<d,z2o i u=0) (hd:IsUnit (z2o d u)) :
    ∃ v :zpm R,IsUnit v∧u=zWv^d*v := by
  obtain ⟨v,hv⟩:=PowerSeries.X_pow_dvd_iff.mpr h₀
  refine ⟨v,PowerSeries.isUnit_iff_constantCoeff.mpr ?_,hv⟩
  simpa [hv,PowerSeries.coeff_X_pow_mul',← PowerSeries.coeff_zero_eq_constantCoeff] using hd
private theorem unitLead {R:Type*} [CommRing R] [IsDomain R] {f : (zpm R)[X]}
    {g d:ℕ} (hg:0<g) (hdeg:f.natDegree≤g)
    (hl:zbO (f.coeff g)≠0)
    {u:zpm R} (hu:IsUnit u) (he :det f g=zWv^d*u) :
    IsUnit (f.coeff g) := by
  have hn:f.coeff g≠0:= fun h=>hl (by rw [h,map_zero])
  have hdeg' := le_antisymm hdeg (le_natDegree_of_ne_zero hn)
  have hfactor : ∃ w,det f g=f.coeff g*w:= by
    rw [det,← hdeg',resultant_deriv (natDegree_pos_iff_degree_pos.mp (hdeg' ▸ hg))]
    exact ⟨(-1)^(f.natDegree*(f.natDegree - 1)/2)*f.discr,by
      rw [coeff_natDegree]
      ac_rfl⟩
  obtain ⟨w,hw⟩:=hfactor
  have ho: (f.coeff g).order=0 :=
    PowerSeries.order_eq_nat.mpr ⟨by simpa [PowerSeries.coeff_zero_eq_constantCoeff],by simp⟩
  have hd:w.order=d:= by
    have heq :=congrArg PowerSeries.order (hw.symm.trans he)
    simpa only [PowerSeries.order_mul,ho,zero_add,PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit hu,add_zero] using heq
  obtain ⟨v,hv⟩:=PowerSeries.X_pow_dvd_iff.mpr
    ((PowerSeries.order_eq_nat.mp hd).2)
  have hmul :f.coeff g*v=u:= by
    apply mul_left_cancel₀ (a :=(zWv:zpm R)^d) (pow_ne_zero _ PowerSeries.X_ne_zero)
    simpa [hw,hv,mul_left_comm] using he
  exact isUnit_of_dvd_unit ⟨v,hmul.symm⟩ hu
private theorem rationalValue {N D:L[X]} (hD:D ≠0) (x :L) {w:Series}
    (hw:expand x N+expand x D *w=0) :
    ValueAt (-algebraMap L[X] (RatFunc L) N/algebraMap L[X] (RatFunc L) D)
      x (zbO w) := by
  let e :=expand x
  let v :RatFunc L := -algebraMap L[X] (RatFunc L) N/algebraMap L[X] (RatFunc L) D
  have hinj:Function.Injective e :=
    (Polynomial.coe_injective L).comp (taylorEquiv x).injective
  have hdn:e D ≠0:=(map_ne_zero_iff e hinj).mpr hD
  have hfrac:v.num*D = -N*v.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hD).mpr (by simp [v])
  have hneg:e (-N)=e D *w:= by
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_right hw).symm
  have heq :=congrArg e hfrac
  simp only [map_mul,hneg] at heq
  have hu:e v.num=w*e v.denom:= by
    apply mul_left_cancel₀ hdn
    simpa only [mul_assoc,mul_comm (e D) (e v.num)] using heq
  have hz (f :L[X]) :zbO (e f)=f.eval x :=
    taylor_coeff_zero _ _
  have hv :v.num.eval x=zbO w*v.denom.eval x := by
    simpa only [map_mul,hz] using congrArg zbO hu
  refine ⟨?_,hv⟩
  intro h
  rw [h,mul_zero] at hv
  exact (aeval_ne_zero_of_isCoprime v.isCoprime_num_denom x).elim (fun hn=>hn hv) (fun hn=>hn h)
end
end P5_7_3_3_4_1_7
end
