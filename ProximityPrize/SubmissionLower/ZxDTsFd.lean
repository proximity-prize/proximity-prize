import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.ZO7Azpb
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Finset → zJe, IsFractionRing.injective → zxb, Nat.add_sub_of_le → zp3, Nat.cast_zero → zQq, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y, Polynomial.map_injective → zTo, Polynomial.map_ne_zero_iff → zeI, Polynomial.map_sub → z3A, PowerSeries.C → zMG, RingHom.comp_apply → zQb
set_option autoImplicit true
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qBnMK6c
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna qps5rle
open P5 (K)
open cu (L FX)
open E7 (CurvePlace poleOrder)
open qb0hmCe (CurveModel SiteTarget.det SiteTarget.height)
open qFD8jve (aFA sheetPole seedPole)
open scoped Classical WithZero
variable {J:Input} {U:zJe K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
theorem complement (S:Sheet B C₀) (R:SiteTarget) :
    ∃ V,∀ γ∈S.marks,matchesTarget R B γ→targetDetAt R J γ V≠0:= by
  let F:=S.marks.image fun γ=>targetDen R J γ/targetNum R J γ
  obtain ⟨t,ht⟩:=F.exists_notMem
  refine ⟨![1,t],fun γ hγ hm hz => ?_⟩
  have h:targetNum R J γ*t=targetDen R J γ:= by
    simpa [targetDetAt] using sub_eq_zero.mp hz
  have hP:targetNum R J γ≠0:= by
    intro hp
    have hab:targetNum R J γ≠0∨targetDen R J γ≠0:=hm.1
    exact (hab.resolve_left (fun hn=>hn hp)) (by simpa [hp] using h.symm)
  apply ht (mem_image.mpr ⟨γ,hγ,?_⟩)
  exact (div_eq_iff hP).mpr (by rw [mul_comm,h])
theorem det_residue (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L)
    (γ:K) (hγ:γ∈S.marks) :
    (S.atPlace γ hγ (targetDet R (C₀.seed R.coord) V)).coeff 0=targetDetAt R J γ V:= by
  obtain ⟨z,hz,hres,_⟩:=S.arc γ hγ
  let a :=S.atPlace γ hγ
  have hseed :a (C₀.seed R.coord)=(z R.coord:SeedSeries) :=hz _
  let P:=zMG R.a+PowerSeries.C R.b*z R.coord
  let Q:=zMG R.c+PowerSeries.C R.d*z R.coord
  have h:a (targetDet R (C₀.seed R.coord) V) =
      ((P*zMG (V 1)-Q*zMG (V 0) :PowerSeries L) :SeedSeries) := by
    simp only [targetDet,O7,map_sub,map_mul,map_add,a.commutes,hseed,P,Q,
      PowerSeries.coe_C,
      LaurentSeries.algebraMap_apply]
  change (a _).coeff 0= _
  rw [h]
  change HahnSeries.coeff ((P*zMG (V 1)-Q*zMG (V 0) :PowerSeries L) :
    SeedSeries) ((0:ℕ) :ℤ)= _
  rw [LaurentSeries.coeff_coe_powerSeries,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [P,Q,targetDetAt,targetNum,targetDen,map_sub,map_mul,map_add,PowerSeries.constantCoeff_C,hres]
theorem coprime_eval {N D:L[X]} (h:IsCoprime N D) (x :L)
    (hD:D.eval x=0) :N.eval x≠0:= by
  intro hN
  obtain ⟨u,v,huv⟩:=h
  have he :=congrArg (fun f :L[X]=>f.eval x) huv
  simp only [eval_add,eval_mul,hN,hD,mul_zero,zero_add,eval_one,zero_ne_one] at he
theorem mark_scale (S:Sheet B C₀) (R:SiteTarget) {γ:K}
    (hγ:γ∈S.marks) (hm:matchesTarget R B γ) :
    ∃ scale :L,scale≠0∧(B.P γ).eval R.center=scale*targetNum R J γ ∧
      (B.Q γ).eval R.center=scale*targetDen R J γ:= by
  let a :=targetNum R J γ
  let b:=targetDen R J γ
  let u:=(B.P γ).eval R.center
  let v :=(B.Q γ).eval R.center
  have hab:a≠0∨b≠0:=hm.1
  have he :u*b=v*a :=hm.2
  have huv :u≠0∨v≠0:= by
    by_cases h:v=0
    · exact Or.inl (coprime_eval (B.coprime γ (S.Bp hγ)) R.center h)
    · exact Or.inr h
  change ∃ scale :L,scale≠0∧u=scale*a∧v=scale*b
  by_cases hb:b=0
  · have ha :=hab.resolve_right (fun hn=>hn hb)
    have hv :v=0:=(mul_eq_zero.mp (by simpa [hb] using he.symm)).resolve_right ha
    exact ⟨u/a,div_ne_zero (huv.resolve_right (fun hn=>hn hv)) ha,
      (div_mul_cancel₀ _ ha).symm,by simp [hv,hb]⟩
  · have hu:u=v/b*a := by
      rw [div_mul_eq_mul_div,eq_div_iff hb]
      exact he
    have hv :v≠0:= fun hz=>(huv.resolve_right (fun hn=>hn hz)) (by simp [hu,hz])
    exact ⟨v/b,div_ne_zero hv hb,hu,(div_mul_cancel₀ _ hb).symm⟩
theorem crossDen_eval (R:SiteTarget) (γ:K) (V:Fin 2→L) {scale :L}
    (hP: (B.P γ).eval R.center=scale*targetNum R J γ)
    (hQ: (B.Q γ).eval R.center=scale*targetDen R J γ) :
    (crossDen B γ V).eval R.center=scale*targetDetAt R J γ V:= by
  simp only [crossDen,eval_sub,eval_mul,eval_C,hP,hQ,targetDetAt]
  ring
theorem phys_inj:Function.Injective phys :=zxb L[X] FX
theorem reduced_test (x :L) {N D T A B:L[X]} {u:L}
    (hD:D ≠0) (hc:IsCoprime N D) (hu:u≠0)
    (hA:A.eval x=0) (hB:B.eval x≠0)
    (he :phys (C u)*(phys N/phys D)+phys T=phys A/phys B) :
    N.eval x=0↔T.eval x=0:= by
  have hd:=(map_ne_zero_iff phys phys_inj).mpr hD
  have hb:=(map_ne_zero_iff phys phys_inj).mpr (show B≠0 from fun h=>hB (by simp [h]))
  have hp: (C u*N+T*D)*B=A*D:= by
    apply phys_inj
    simp only [map_mul,map_add]
    apply (div_eq_div_iff hd hb).mp
    simpa only [add_div,mul_div_assoc,mul_div_cancel_right₀ _ hd] using he
  have hh:=congrArg (fun f :L[X]=>f.eval x) hp
  simp only [eval_mul,eval_add,eval_C,hA,zero_mul] at hh
  have h:=(mul_eq_zero.mp hh).resolve_right hB
  have hD₀:D.eval x≠0:= by
    intro hz
    exact hu ((mul_eq_zero.mp (by simpa only [hz,mul_zero,add_zero] using h)).resolve_right
      (coprime_eval hc x hz))
  exact ⟨fun hn=>(mul_eq_zero.mp (by simpa [hn] using h)).resolve_right hD₀,
    fun ht=>(mul_eq_zero.mp (by simpa [ht] using h)).resolve_left hu⟩
theorem height_of_bound (S:Sheet B C₀) (R:SiteTarget) {g:C₀.E[X][X]}
    (h : ∀ v :CurvePlace L C₀.E,
      aFA v.value g (sheetPole v.value S.f+S.d*seedPole C₀ R v.value)) :
    (∑ᶠ v :CurvePlace L C₀.E,poleOrder v.value (leadAt R.center g))≤S.h+S.d*R.height q:= by
  let V:=CurvePlace L C₀.E
  let H (v :V) :=sheetPole v.value S.f
  let seedCost (v :V) :=seedPole C₀ R v.value
  have hdiv :=aFU.of_children bRt.proof
    bRu.proof L C₀.E C₀.curve
  have hH :H.HasFiniteSupport:=agN.b27 hdiv _
  have hZ:seedCost.HasFiniteSupport∧(∑ᶠ v,seedCost v)≤R.height q:= by
    by_cases hr :R.b=0∧R.d=0
    · simp [seedCost,seedPole,SiteTarget.height,Function.HasFiniteSupport,hr]
    · exact ⟨by simpa [seedCost,seedPole,hr] using (hdiv (C₀.seed R.coord)).1,
        by simpa [seedCost,seedPole,SiteTarget.height,hr] using C₀.co6 R.coord⟩
  have hpoint (v :V) :poleOrder v.value (leadAt R.center g)≤H v+S.d*seedCost v := by
    have hle :v.value (leadAt R.center g)≤WithZero.exp ((H v+S.d*seedCost v :ℕ) :ℤ) := by
      unfold leadAt
      rw [eval_eq_sum,Polynomial.sum]
      apply v.value.map_sum_le
      intro i _
      rw [map_mul,map_pow]
      have hc:v.value (algebraMap L C₀.E R.center)≤1 := by
        by_cases hz :R.center=0
        · simp [hz]
        · exact (v.on_constants _ hz).le
      exact (mul_le_mul' (h v g.natDegree i) (pow_le_one₀ bot_le hc)).trans_eq (mul_one _)
    by_cases hz :leadAt R.center g=0
    · simp [hz,poleOrder]
    · have hv :=v.value.ne_zero_iff.mpr hz
      simpa only [poleOrder,Int.toNat_natCast] using Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp hv).mpr hle)
  have hR: (fun v :V=>S.d*seedCost v).HasFiniteSupport :=
    hZ.1.subset (Function.support_mul_subset_right _ _)
  calc
    _ ≤ ∑ᶠ v :V,(H v+S.d*seedCost v) :=
      finsum_le_finsum (hdiv _).1 (hH.add hR) hpoint
    _=S.h+S.d*(∑ᶠ v :V,seedCost v) := by
      rw [finsum_add_distrib hH hR,← mul_finsum]
      rfl
    _≤_:=Nat.add_le_add_left (Nat.mul_le_mul_left _ hZ.2) _
end
end qBnMK6c
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna
open qps5rle (physicalParameter siteMatrix O7)
open qBnMK6c (reciprocalMatrix)
open qgpYCte (ChartData changeOrdinate)
open cu (L)
open E7 (CurvePlace)
open qb0hmCe (CurveModel)
open qFD8jve (aFA sheetPole seedPole)
open scoped WithZero
open private adG cTA cTB efc from ProximityPrize.SubmissionLower.Y
open private gauss efe gauss_X coeff_gauss const_bound target_bound from ProximityPrize.SubmissionLower.ZlnMfEd
variable {E :Type} [Field E] [zZE L E]
private theorem parameter_value (v :CurvePlace L E) (x :L) :
    efc v.value (physicalParameter x)=1 := by
  change adG v.value (z7y (R:=E) - C (algebraMap L E x))=1
  simpa only [z3A,Polynomial.map_X,Polynomial.map_C] using
    cTB v (z7y (R:=L) - C x) (X_sub_C_ne_zero x)
private theorem site_bound (v :CurvePlace L E) (R:SiteTarget) (z :E)
    (V:Fin 2→L) (M:Matrix (Fin 2) (Fin 2) L) {b:ℕ}
    (ha :v.value (O7 R.a R.b z)≤WithZero.exp (b:ℤ))
    (hc:v.value (O7 R.c R.d z)≤WithZero.exp (b:ℤ)) (i j:Fin 2) :
    efc v.value (siteMatrix R z V M i j)≤WithZero.exp (b:ℤ) := by
  let w:=efc v.value
  let B:=WithZero.exp (b:ℤ)
  let A:Matrix (Fin 2) (Fin 2) E[X] :=
    !![C (O7 R.a R.b z),physicalParameter R.center*C (algebraMap L E (V 0));
       C (O7 R.c R.d z),physicalParameter R.center*C (algebraMap L E (V 1))]
  have hB:1≤B:=WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _)
  have hC (x :L) :w (C (algebraMap L E x))≤1 :=
    (cTA v.value _).le.trans (const_bound v x)
  have hτ (j:Fin 2) :w (physicalParameter R.center*C (algebraMap L E (V j)))≤B:= by
    rw [map_mul,show w (physicalParameter R.center)=1 from parameter_value v _,one_mul]
    exact (hC _).trans hB
  have hA (k :Fin 2) :w (A i k)≤B:= by
    fin_cases i <;> fin_cases k
    · exact (cTA v.value _).le.trans ha
    · exact hτ 0
    · exact (cTA v.value _).le.trans hc
    · exact hτ 1
  change w ((A*M.map (C.comp (algebraMap L E))) i j)≤B
  rw [Matrix.mul_apply]
  refine w.map_sum_le fun k _ => ?_
  rw [map_mul,Matrix.map_apply,zQb]
  exact (mul_le_mul' (hA k) (hC _)).trans_eq (mul_one B)
omit [zZE L E] in
private theorem fZo (v :Valuation E ℤᵐ⁰) {a b:E[X]} {x :E[X][X]} {B:ℤᵐ⁰}
    (hx :gauss v x=1) (ha :adG v a≤B) (hb:adG v b≤B) :
    gauss v (C a+C b*x)≤B:= by
  apply (gauss v).map_add_le
  · rwa [efe]
  · rwa [map_mul,hx,mul_one,efe]
variable {J:Input} {U:zJe P5.K} {W:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
private theorem chart_bound (S:Sheet W C₀) (R:SiteTarget) (V:Fin 2→L)
    (T:ChartData S R V) (v :CurvePlace L C₀.E) {h b:ℕ} (hf :aFA v.value S.f h)
    (ha :v.value (O7 R.a R.b (C₀.seed R.coord))≤WithZero.exp (b:ℤ))
    (hc:v.value (O7 R.c R.d (C₀.seed R.coord))≤WithZero.exp (b:ℤ)) :
    aFA v.value T.g (h+S.d*b) := by
  let w:=gauss v.value
  let H :=WithZero.exp (h:ℤ)
  let B:=WithZero.exp (b:ℤ)
  let A:=siteMatrix R (C₀.seed R.coord) V (reciprocalMatrix T.t)
  let x :C₀.E[X][X] :=z7y
  have hx :w x=1 :=gauss_X v.value
  let row (i:Fin 2) :=C (A i 0)+C (A i 1)*x
  have hr (i:Fin 2) :w (row i)≤B :=
    fZo v.value hx (site_bound v R _ V _ ha hc i 0) (site_bound v R _ V _ ha hc i 1)
  have hF:w (changeOrdinate S.f A)≤H*B^S.d:= by
    change w (∑ i∈range (S.d+1),C (S.f.coeff i)*row 0^i*row 1^(S.d - i))≤_
    refine w.map_sum_le fun i hi => ?_
    have hcoeff :w (C (S.f.coeff i))≤H := by
      rw [show w (C (S.f.coeff i))= _ from efe v.value _]
      exact Finset.sup_le fun j _=>hf i j
    rw [map_mul,map_mul,map_pow,map_pow]
    calc
      _≤H*B^i*B^(S.d - i) :=mul_le_mul'
        (mul_le_mul' hcoeff (pow_le_pow_left' (hr 0) _)) (pow_le_pow_left' (hr 1) _)
      _ = _:= by rw [mul_assoc,← pow_add,zp3 (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  have he :w (changeOrdinate S.f A)=w T.g:= by
    rw [← T.transformed,map_mul,show w (C (physicalParameter R.center^T.k))=1 from ?_,
      one_mul]
    rw [efe]
    exact (map_pow (efc v.value) (physicalParameter R.center) T.k).trans
      (by rw [parameter_value v,one_pow])
  rw [he] at hF
  intro i j
  simpa only [H,B,← WithZero.exp_nsmul,← WithZero.exp_add,Nat.cast_add,Nat.cast_mul,
    nsmul_eq_mul,mul_comm (b:ℤ)] using (coeff_gauss v.value T.g i j).trans hF
theorem Ca (S:Sheet W C₀) (R:SiteTarget) (V:Fin 2→L) (T:ChartData S R V) :
    (∀ v :CurvePlace L C₀.E,
      aFA v.value T.g (sheetPole v.value S.f+S.d*seedPole C₀ R v.value)) ∧
    (∀ γ∈S.marks,matchesTarget R W γ→aFA (S.place γ).value T.g 0) := by
  constructor
  · intro v
    apply chart_bound S R V T v (qrezXJe.sheet_bound v.value S.f)
    all_goals
      by_cases hz :R.b=0∧R.d=0
      · rw [seedPole,ite_eq_left hz]
        simpa only [O7,hz.1,hz.2,map_zero,zero_mul,add_zero,
          zQq,WithZero.exp_zero] using const_bound v _
      · apply target_bound
        rw [seedPole,ite_eq_right hz]
        exact WithZero.le_exp_of_log_le (Int.self_le_toNat _)
  · intro γ hγ _
    let v :=S.place γ
    obtain ⟨arc,ha,_,_⟩:=S.arc γ hγ
    have hseed :v.value (C₀.seed R.coord)≤WithZero.exp (0:ℤ) := by
      rw [WithZero.exp_zero,S.value γ hγ,ha]
      exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨arc R.coord,rfl⟩
    have hf :aFA v.value S.f 0:= by
      simpa only [aFA,zQq,WithZero.exp_zero,v] using S.integral γ hγ
    simpa only [Nat.mul_zero,Nat.add_zero] using
      chart_bound S R V T v hf (target_bound v hseed R.a R.b) (target_bound v hseed R.c R.d)
end
end P5_7_2_6Q3
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3
noncomputable section
open Polynomial qe6nVeb qE3Ebna
open P5 (K)
open cu (L FX)
open qb0hmCe (CurveModel SiteTarget.det)
open qFD8jve (aFA)
open qps5rle (SiteJet atArc finiteAt targetDet vSeed)
open qBnMK6c (targetNum targetDen targetDetAt crossDen chartDen reciprocalMatrix correction)
open qgpYCte (ChartData)
open qBnMK6c (complement det_residue mark_scale crossDen_eval reduced_test height_of_bound)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {J:Input} {U:zJe K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
    (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L),targetDet R (C₀.seed R.coord) V≠0 →
    (∀ γ∈S.marks,matchesTarget R B γ→(crossDen B γ V).eval R.center≠0) →
    Nonempty (ChartData S R V)
def c2 :Prop :=
  ∀ {J:Input} {U:zJe K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
    (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L) (T:ChartData S R V)
    (γ:K) (hγ:γ∈S.marks),matchesTarget R B γ→targetDetAt R J γ V≠0 →
    (crossDen B γ V).eval R.center≠0→aFA (S.place γ).value T.g 0 →
    ∃ A:SiteJet (atArc (S.atPlace γ hγ) T.g) R.center,
      phys (z7y (R:=L) - C R.center)*phys (chartDen R B γ V T.t)^2*A.delta =
        phys (C (targetDetAt R J γ V))*(phys (S.num γ)/phys (S.den γ)) +
          phys (correction S R γ V)
variable {J:Input} {U:zJe K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
private theorem transfer (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L)
    (T:ChartData S R V) (γ:K) (hγ:γ∈S.marks) (hm:matchesTarget R B γ)
    (hdet:targetDetAt R J γ V≠0) (δ:FX) (hδ:finiteAt R.center δ)
    (h:phys (z7y (R:=L) - C R.center)*phys (chartDen R B γ V T.t)^2*δ =
      phys (C (targetDetAt R J γ V))*(phys (S.num γ)/phys (S.den γ)) +
        phys (correction S R γ V)) :
    (S.num γ).eval R.center=0↔R.det=0∨S.direction γ R.coord=0:= by
  obtain ⟨N,D,hD,he⟩:=hδ
  have ht:=reduced_test R.center (S.den_ne γ hγ) (S.reduced γ hγ) hdet
    (A:=(Polynomial.X (R:=L) - C R.center)*chartDen R B γ V T.t^2*N) (by simp) hD (by
      rw [← h,he]
      simp only [map_mul,map_pow,mul_div_assoc])
  obtain ⟨scale,hscale,hP,hQ⟩:=mark_scale S R hγ hm
  have hv : (correction S R γ V).eval R.center =
      (scale*scale*targetDetAt R J γ V)*(R.det*S.direction γ R.coord) := by
    simp only [correction,eval_mul,eval_sub,eval_C,crossDen_eval R γ V hP hQ,hP,hQ,
      targetNum,targetDen,SiteTarget.det]
    ring
  rw [ht,hv]
  simp only [mul_eq_zero,hscale,hdet,false_or]
theorem of_children (shape :c1) (Ub:c2) :qgpYCte.c1 := by
  intro J U B q C₀ S R lg
  obtain ⟨V,hV⟩:=complement S R
  have hu (γ:K) (hγ:γ∈S.marks) (hm:matchesTarget R B γ) :
      (S.atPlace γ hγ (targetDet R (C₀.seed R.coord) V)).coeff 0≠0:= by
    rw [det_residue]
    exact hV γ hγ hm
  have hdet:targetDet R (C₀.seed R.coord) V≠0:= by
    obtain ⟨γ,hγ,hm⟩:=lg
    intro hz
    apply hu γ hγ hm
    simp [hz]
  have hden (γ:K) (hγ:γ∈S.marks) (hm:matchesTarget R B γ) :
      (crossDen B γ V).eval R.center≠0:= by
    obtain ⟨scale,hscale,hP,hQ⟩:=mark_scale S R hγ hm
    rw [crossDen_eval R γ V hP hQ]
    exact mul_ne_zero hscale (hV γ hγ hm)
  obtain ⟨T⟩:=shape S R V hdet hden
  obtain ⟨hb,hi⟩:=Ca S R V T
  refine ⟨{
    V:=V,M:=reciprocalMatrix T.t,matrix_ne := ?_,det_ne :=hdet
    k :=T.k,g:=T.g,transformed:=T.transformed,degree :=T.degree,lead_ne :=T.lead_ne
    lead_height:=height_of_bound S R hb,det_unit :=hu
    integral := ?_,jet := ?_ }⟩
  · simp [reciprocalMatrix,Matrix.det_fin_two_of]
  · intro γ hγ hm i j
    simp only [atArc,coeff_map,coe_mapRingHom]
    change vSeed (S.atPlace γ hγ ((T.g.coeff i).coeff j))≤1
    rw [← S.value]
    simpa only [zQq,WithZero.exp_zero] using hi γ hγ hm i j
  · intro γ hγ hm
    obtain ⟨A,hA⟩:=Ub S R V T γ hγ hm (hV γ hγ hm) (hden γ hγ hm) (hi γ hγ hm)
    exact ⟨A,fun h=>transfer S R V T γ hγ hm (hV γ hγ hm) A.delta h hA⟩
end
end P5_7_2_6Q3
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3_1
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna
open P5 (K)
open cu (L)
open qps5rle (leadAt O7 physicalParameter siteMatrix targetDet)
open qBnMK6c (chartDen crossDen crossNum reciprocalMatrix)
open qgpYCte (changeOrdinate)
open qwGrtCa (form transform transform_sum transform_inverse)
open qERExMc (strip_physical transform_comp transform_map transform_scale
  transform_degree transform_top)
open scoped Classical
variable {E :Type} [Field E]
private theorem transform_ne {f :E[X][X]} (hf :f≠0)
    {a b c d:E[X]} (hdet:a*d-b*c≠0) :
    transform a b c d f.natDegree f≠0:= by
  let j:E[X] →+* FractionRing E[X] :=algebraMap _ _
  have hj:=zxb E[X] (FractionRing E[X])
  have hdet' : j a*j d - j b*j c≠0:= by
    rw [← map_mul,← map_mul,← map_sub]
    exact (map_ne_zero_iff j hj).mpr hdet
  intro hz
  have he :=transform_inverse (j a) (j b) (j c) (j d) _ (inv_mul_cancel₀ hdet')
    (show (f.map j).natDegree≤f.natDegree from natDegree_map_le)
  rw [← transform_map,hz,Polynomial.map_zero,transform_sum] at he
  simp at he
  exact (zeI hj).mpr hf he.symm
private theorem strip_at (x :E) {H :E[X][X]} (hH :H≠0) :
    ∃ (k :ℕ) (H₀:E[X][X]),H=C ((z7y - C x)^k)*H₀ ∧
      H₀.map (evalRingHom x)≠0:= by
  let e :=(taylorEquiv x).toRingEquiv
  have hX:e (z7y - C x)=Polynomial.X:= by
    change taylor x (z7y - C x)=z7y
    simp [taylor_X,taylor_C]
  obtain ⟨k,U,he,hU⟩:=strip_physical (H.map e.toRingHom)
    ((zeI e.injective).mpr hH)
  let H₀:=U.map e.symm.toRingHom
  have hHU:H.map e.toRingHom=(C ((z7y - C x)^k)*H₀).map e.toRingHom:= by
    rw [Polynomial.map_mul,map_C,map_pow]
    change H.map e.toRingHom=C ((e (z7y - C x))^k)*H₀.map e.toRingHom
    rw [hX,he]
    congr 1
    apply Polynomial.ext
    intro i
    simp only [H₀,coeff_map]
    exact (e.apply_symm_apply (U.coeff i)).symm
  have heq :H₀.map (evalRingHom x)=U.map (evalRingHom (0:E)) := by
    ext i
    simp only [H₀,coeff_map,coe_evalRingHom]
    change (e.symm (U.coeff i)).eval x= _
    have h:=taylor_coeff_zero x (e.symm (U.coeff i))
    change (e (e.symm (U.coeff i))).coeff 0= _ at h
    simpa only [e.apply_symm_apply,coeff_zero_eq_eval_zero] using h.symm
  exact ⟨k,H₀,(zTo e.toRingHom e.injective) hHU,heq ▸ hU⟩
private theorem choose {J:Input} {U:zJe K} {B:DualWord J U}
    (marks :zJe K) (R:SiteTarget) (V:Fin 2→L)
    (hden : ∀ γ∈marks,matchesTarget R B γ→(crossDen B γ V).eval R.center≠0)
    [zZE L E] {P:E[X]} (hP:P≠0) :
    ∃ t:L,P.eval (algebraMap L E t)≠0 ∧
      ∀ γ∈marks,matchesTarget R B γ→(chartDen R B γ V t).eval R.center≠0:= by
  let a :=algebraMap L E
  let bad:=marks.image fun γ=>(crossNum R B γ /ₘ
    (z7y (R:=L) - C R.center)).eval R.center/(crossDen B γ V).eval R.center
  have hfinite : ((a ⁻¹' {z | P.IsRoot z})∪(bad:Set L)).Finite :=
    ((finite_setOfPred_isRoot hP).preimage a.injective.injOn).union bad.finite_toSet
  obtain ⟨t,ht⟩:=hfinite.exists_notMem
  refine ⟨t,fun hz=>ht (Or.inl hz),?_⟩
  intro γ hγ hm hz
  simp only [chartDen,eval_sub,eval_mul,eval_C,sub_eq_zero] at hz
  exact ht (Or.inr (mem_image.mpr ⟨γ,hγ,((eq_div_iff (hden γ hγ hm)).mpr hz.symm).symm⟩))
private theorem reciprocal_eq [zZE L E] (f :E[X][X]) (R:SiteTarget) (z :E)
    (V:Fin 2→L) (t:L) :
    let a :=physicalParameter (E :=E) R.center*C (algebraMap L E (V 0))
    let b:=C (O7 R.a R.b z)
    let c:=physicalParameter (E :=E) R.center*C (algebraMap L E (V 1))
    let d:=C (O7 R.c R.d z)
    changeOrdinate f (siteMatrix R z V (reciprocalMatrix t)) =
      transform (a*C (algebraMap L E t)+b) a (c*C (algebraMap L E t)+d) c f.natDegree f := by
  intro a b c d
  let T:=C (algebraMap L E t)
  let j:L →+* E[X] :=C.comp (algebraMap L E)
  have hm: (reciprocalMatrix t).map j = !![0,1; 1,T] := by
    calc
      _ = !![j 0,j 1; j 1,j t] :=Matrix.eta_fin_two _
      _ = _:= by
        rw [map_zero,map_one]
        rfl
  have he :siteMatrix R z V (reciprocalMatrix t) = !![a,b+a*T; c,d+c*T] := by
    change !![b,a; d,c]*(reciprocalMatrix t).map j= _
    rw [hm,Matrix.mul_fin_two]
    simp only [mul_zero,mul_one,zero_add]
  rw [he,changeOrdinate,transform_sum]
  apply sum_congr rfl
  intro i _
  change C (f.coeff i)*(C a+C (b+a*T)*z7y)^i *
      (C c+C (d+c*T)*z7y)^(f.natDegree-i)= _
  rw [add_comm b (a*T),add_comm d (c*T)]
  rfl
theorem proof :P5_7_2_6Q3.c1 := by
  intro J U B q M S R V hdet hden
  let m:=algebraMap L M.E
  let τ:=physicalParameter (E :=M.E) R.center
  let z :=M.seed R.coord
  let a :=τ*C (m (V 0))
  let b:=C (O7 R.a R.b z)
  let c:=τ*C (m (V 1))
  let d:=C (O7 R.c R.d z)
  have hd:a*d-b*c = -(τ*C (targetDet R z V)) := by
    dsimp only [a,b,c,d,m,targetDet]
    rw [map_sub,map_mul,map_mul]
    ring
  have hdet' : a*d-b*c≠0:= by
    rw [hd,neg_ne_zero]
    exact mul_ne_zero (X_sub_C_ne_zero _) (C_ne_zero.mpr hdet)
  let H :=transform a b c d S.d S.f
  obtain ⟨k,H₀,he,h₀⟩:=strip_at (m R.center) (H :=H)
    (transform_ne S.irreducible.ne_zero hdet')
  change H=C (τ^k)*H₀ at he
  let P:=H₀.map (evalRingHom (m R.center))
  obtain ⟨t,ht,hfinite⟩:=choose S.marks R V hden (P:=P) h₀
  let T:=C (m t)
  let g:=transform T 1 1 0 S.d H₀
  have hr :changeOrdinate S.f (siteMatrix R z V (reciprocalMatrix t))=C (τ^k)*g:= by
    rw [reciprocal_eq]
    change transform (a*T+b) a (c*T+d) c S.d S.f= _
    have hc:transform T 1 1 0 S.d H=transform (a*T+b) a (c*T+d) c S.d S.f := by
      dsimp only [H]
      rw [transform_comp]
      simp
    rw [← hc,he,transform_scale]
  have hdeg₀:P.natDegree≤S.d:= by
    have hdeg:H.natDegree=H₀.natDegree := by
      rw [he,natDegree_C_mul (pow_ne_zero _ (X_sub_C_ne_zero (m R.center)))]
    exact natDegree_map_le.trans (hdeg ▸ transform_degree a b c d S.d S.f)
  have htop: (g.coeff S.d).eval (m R.center)=P.eval (m t) := by
    have h:=congrArg (evalRingHom (m R.center)) (transform_top T 1 1 0 S.d H₀)
    rw [eval_eq_sum_range' (zB1 hdeg₀)]
    simpa only [g,T,P,map_sum,map_mul,map_pow,map_one,one_pow,mul_one,
      coeff_map,coe_evalRingHom,eval_C] using h
  have hdeg:g.natDegree=S.d:=le_antisymm (transform_degree T 1 1 0 S.d H₀)
    (le_natDegree_of_ne_zero (fun hz=>ht (htop.symm.trans (by rw [hz,eval_zero]))))
  have hlead:leadAt R.center g≠0:= by
    rw [leadAt,leadingCoeff,hdeg]
    exact fun hz=>ht (htop.symm.trans hz)
  exact ⟨⟨t,k,g,hr.symm,hdeg,hlead,hfinite⟩⟩
end
end P5_7_2_6Q3_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3_2
noncomputable section
open Polynomial Finset TrivSqZeroExt
open cu (L FX)
open qe6nVeb (phys)
open qE3Ebna (SiteTarget)
open qps5rle (atArc physicalParameter O7 siteMatrix residue)
open qBnMK6c (reciprocalMatrix)
open qgpYCte (changeOrdinate)
open qwGrtCa (transform transform_sum form)
open q1kuFjb (IntSeries Ua mapTwice map_liftAt expansion_coeff)
open qJai0ob (Dual scalar seriesJet pair evalAt)
open private transform_map from ProximityPrize.SubmissionLower.ZO7Azpb
open private constant jet_constant jet_linear τ from ProximityPrize.SubmissionLower.ZFdiUYb
open scoped WithZero
def param {A:Type*} [Ring A] (r :L →+* A) (x :L) :A[X] :=z7y - C (r x)
def siteChange {A:Type*} [za6 A] (r :L →+* A) (R:SiteTarget) (z :A)
    (V:Fin 2→L) (t:L) (n:ℕ) (f :A[X][X]) :A[X][X] :=
  let x :=param r R.center
  transform (C (r R.a+r R.b*z) + x*C (r (V 0))*C (r t)) (x*C (r (V 0)))
    (C (r R.c+r R.d*z) + x*C (r (V 1))*C (r t)) (x*C (r (V 1))) n f
private theorem siteChange_eq {E :Type} [Field E] [zZE L E] (R:SiteTarget) (z :E)
    (V:Fin 2→L) (t:L) (f :E[X][X]) :
    siteChange (algebraMap L E) R z V t f.natDegree f =
      changeOrdinate f (siteMatrix R z V (reciprocalMatrix t)) := by
  simp [siteChange,param,changeOrdinate,transform_sum,form,siteMatrix,reciprocalMatrix,
    Matrix.mul_apply,Fin.sum_univ_two,O7]
private theorem siteChange_map {A D:Type} [za6 A] [za6 D]
    (e :A →+* D) (r :L →+* A) (R:SiteTarget) (z :A) (V:Fin 2→L) (t:L)
    (n:ℕ) (f :A[X][X]) :
    mapTwice e (siteChange r R z V t n f)=siteChange (e.comp r) R (e z) V t n (mapTwice e f) := by
  simp only [mapTwice,coe_mapRingHom,siteChange,transform_map,param,Polynomial.map_X,
    z3A,Polynomial.map_C,map_add,
    map_mul,zQb]
private theorem map_param {A D:Type} [za6 A] [za6 D] (e :A →+* D)
    (r :L →+* A) (x :L) (k :ℕ) :
    mapTwice e (C (param r x^k))=C (param (e.comp r) x^k) := by
  simp [mapTwice,param,Polynomial.map_pow,z3A]
theorem aor {E :Type} [Field E] [zZE L E] (a :E →ₐ[L] LaurentSeries L)
    (f g:E[X][X]) (hf hg) (R:SiteTarget) (z :E) (z' : IntSeries)
    (hz : (z' : LaurentSeries L)=a z) (V:Fin 2→L) (t:L) (k :ℕ)
    (h:C (physicalParameter R.center^k)*g =
      changeOrdinate f (siteMatrix R z V (reciprocalMatrix t))) :
    C (param constant R.center^k)*Ua a g hg =
      siteChange constant R z' V t f.natDegree (Ua a f hf) := by
  let e :IntSeries →+* LaurentSeries L:=IntSeries.subtype
  have hconst:e.comp constant=a.toRingHom.comp (algebraMap L E) := by
    exact RingHom.ext (qFe6O4d.constant_coe a)
  have hz' : e z' = a.toRingHom z :=hz
  apply zTo (mapRingHom e) (zTo e Subtype.val_injective)
  change mapTwice e _=mapTwice e _
  rw [map_mul,map_param,map_liftAt,siteChange_map,map_liftAt,hconst,hz',
    ← siteChange_map,siteChange_eq,← h,map_mul]
  exact congrArg (· * mapTwice a.toRingHom g) (map_param a.toRingHom (algebraMap L E) R.center k).symm
theorem cXJ {E :Type} [Field E] [zZE L E] (a :E →ₐ[L] LaurentSeries L)
    (f :E[X][X]) (hf) : (Ua a f hf).natDegree=f.natDegree := by
  rw [← natDegree_map_eq_of_injective (f :=mapRingHom IntSeries.subtype)
    (zTo IntSeries.subtype Subtype.val_injective) (Ua a f hf)]
  change (mapTwice IntSeries.subtype (Ua a f hf)).natDegree=f.natDegree
  rw [map_liftAt]
  exact natDegree_map_eq_of_injective (f :=mapRingHom a.toRingHom)
    (zTo a.toRingHom a.injective) f
private theorem transform_eval {A D:Type*} [za6 A] [za6 D] (e :A →+* D)
    (f :A[X]) {n:ℕ} (hn:f.natDegree≤n) (a b c d:A) (w y :D)
    (h:e b+e a*w=(e d+e c*w)*y) :
    (transform a b c d n f).eval₂ e w=(e d+e c*w)^n*f.eval₂ e y := by
  rw [transform_sum,eval₂_eq_sum_range' e (zB1 hn),mul_sum]
  simp only [eval₂_finsetSum]
  apply sum_congr rfl
  intro i hi
  have hp: (e d+e c*w)^i*(e d+e c*w)^(n-i)=(e d+e c*w)^n:= by
    rw [← pow_add,zp3 (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  simp only [form,eval₂_mul,eval₂_add,eval₂_C,eval₂_pow,eval₂_X,h,mul_pow,← hp]
  ring
def column (x v t:FX) (A w:Dual) :Dual :=
  inl (x*v)+(A+inl (x*v*t))*w
theorem eval_chart (R:SiteTarget) (z :IntSeries) (V:Fin 2→L) (t:L)
    (f :IntSeries[X][X]) {n:ℕ} (hn:f.natDegree≤n) (w y :Dual) (z₀ z₁:L)
    (ha :seriesJet (constant R.a+constant R.b*z)=pair (scalar (R.a+R.b*z₀)) (scalar (R.b*z₁)))
    (hb:seriesJet (constant R.c+constant R.d*z)=pair (scalar (R.c+R.d*z₀)) (scalar (R.d*z₁)))
    (h:column (phys (z7y - C R.center)) (scalar (V 0)) (scalar t)
        (pair (scalar (R.a+R.b*z₀)) (scalar (R.b*z₁))) w =
      column (phys (z7y - C R.center)) (scalar (V 1)) (scalar t)
        (pair (scalar (R.c+R.d*z₀)) (scalar (R.d*z₁))) w*y) :
    evalAt seriesJet (inl τ) w (siteChange constant R z V t n f) =
      (column (phys (z7y - C R.center)) (scalar (V 1)) (scalar t)
        (pair (scalar (R.c+R.d*z₀)) (scalar (R.d*z₁))) w)^n*evalAt seriesJet (inl τ) y f := by
  have hp: (param constant R.center).eval₂ seriesJet (inl τ)=inl (phys (z7y - C R.center)) := by
    simp only [param,eval₂_sub,eval₂_X,eval₂_C,jet_constant,map_sub]
    exact ((inlHom FX FX).map_sub τ (scalar R.center)).symm
  simp only [siteChange,evalAt,coe_eval₂RingHom]
  rw [transform_eval (eval₂RingHom seriesJet (inl τ)) f hn _ _ _ _ w y]
  all_goals
    simp only [coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,hp,jet_constant,ha,hb,
      ← inl_mul,column]
  exact h
theorem eval_param (x :L) (k :ℕ) (w:Dual) :
    evalAt seriesJet (inl τ) w (C (param constant x^k))=inl (phys (z7y - C x)^k) := by
  simp only [evalAt,coe_eval₂RingHom,eval₂_C,eval₂_pow,param,eval₂_sub,eval₂_X,
    jet_constant,map_sub,← inl_pow]
  exact congrArg (· ^ k) ((inlHom FX FX).map_sub τ (scalar x)).symm
theorem residue_arc {E :Type} [Field E] [zZE L E]
    (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (k :ℤ) :
    residue (atArc a f) k=qb0hmCe.cLN a k f := by
  ext i j
  simp only [atArc,expansion_coeff,coeff_map,coe_mapRingHom]
  rfl
end
end P5_7_2_6Q3_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3_2
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L FX)
open qe6nVeb (Input DualWord phys)
open qE3Ebna (SiteTarget matchesTarget)
open qBnMK6c (crossNum crossDen chartDen targetNum targetDen)
open qJai0ob (pair pair_fst pair_snd)
open P5 (K)
theorem chart_cross {J:Input} {U:zJe K} {B:DualWord J U}
    (R:SiteTarget) (γ:K) (V:Fin 2→L) (t:L) (hm:matchesTarget R B γ) :
    (z7y - C R.center)*(chartDen R B γ V t+C t*crossDen B γ V)=crossNum R B γ:= by
  have he : (crossNum R B γ).eval R.center=0:= by
    simp only [crossNum,eval_sub,eval_mul,eval_C]
    rw [mul_comm (targetNum R J γ),mul_comm (targetDen R J γ)]
    exact sub_eq_zero.mpr hm.2.symm
  have h:=modByMonic_add_div (crossNum R B γ) (z7y - C R.center)
  rw [modByMonic_X_sub_C_eq_C_eval,he,C_0,zero_add] at h
  rw [chartDen,sub_add_cancel]
  exact h
def slopeAt (x D N A B a b v₀ v₁ P Q u:FX) :FX :=
  (x*D^2*u-N*(b*P-a*Q))/((A*v₁-B*v₀)*Q^2)
theorem column_transport (x D A B a b v₀ v₁ t P Q u:FX)
    (hD:D ≠0) (hQ:Q≠0) (hdet:A*v₁-B*v₀≠0)
    (h:x*(D+t*(P*v₁-Q*v₀))=A*Q-B*P) :
    let N :=P*v₁-Q*v₀
    let w:=pair (N/D) u
    let lo:=column x v₁ t (pair B b) w
    let hi:=column x v₀ t (pair A a) w
    lo.fst=(A*v₁-B*v₀)*Q/D ∧
      hi=lo*pair (P/Q) (slopeAt x D N A B a b v₀ v₁ P Q u) := by
  dsimp only
  have hlo: (column x v₁ t (pair B b) (pair ((P*v₁-Q*v₀)/D) u)).fst =
      (A*v₁-B*v₀)*Q/D:= by
    simp only [column,fst_add,fst_mul,fst_inl,pair_fst]
    field_simp [hD]
    linear_combination v₁*h
  have hhi: (column x v₀ t (pair A a) (pair ((P*v₁-Q*v₀)/D) u)).fst =
      (A*v₁-B*v₀)*P/D:= by
    simp only [column,fst_add,fst_mul,fst_inl,pair_fst]
    field_simp [hD]
    linear_combination v₀*h
  have hc: (A+x*v₀*t)-(B+x*v₁*t)*(P/Q)=x*D/Q:= by
    field_simp [hQ]
    linear_combination -h
  refine ⟨hlo,TrivSqZeroExt.ext ?_ ?_⟩
  · rw [fst_mul,hhi,hlo,pair_fst]
    field_simp [hQ]
  · rw [DualNumber.snd_mul,hlo,pair_fst,pair_snd]
    simp only [column,snd_add,DualNumber.snd_mul,fst_add,fst_inl,snd_inl,
      pair_fst,pair_snd,zero_add,add_zero]
    have he : (A*v₁-B*v₀)*Q/D *slopeAt x D (P*v₁-Q*v₀) A B a b v₀ v₁ P Q u =
        (x*D^2*u-(P*v₁-Q*v₀)*(b*P-a*Q))/(D*Q) := by
      unfold slopeAt
      field_simp [hdet,hD,hQ]
    rw [he,← sub_eq_zero]
    calc
      _=((A+x*v₀*t)-(B+x*v₁*t)*(P/Q))*u+(a-b*(P/Q))*((P*v₁-Q*v₀)/D) -
          (x*D^2*u-(P*v₁-Q*v₀)*(b*P-a*Q))/(D*Q) := by ring
      _=0:= by rw [hc]; field_simp [hD,hQ]; ring
end
end P5_7_2_6Q3_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace P5_7_2_6Q3_2
noncomputable section
open Polynomial TrivSqZeroExt
open cu (L FX)
open qe6nVeb (phys dcQ)
open qE3Ebna (Sheet SiteTarget)
open qps5rle (SiteJet atArc residue)
open qBnMK6c (crossNum crossDen chartDen correction targetNum targetDen targetDetAt)
open qb0hmCe (cLN)
open q1kuFjb (Ua)
open qFe6O4d (eval_phys)
open qJai0ob (Dual pair pair_fst pair_snd scalar evalAt seriesJet eval_seriesJet)
open private constant jet_linear τ from ProximityPrize.SubmissionLower.ZFdiUYb
open scoped WithZero
private theorem phys_ne {g:L[X]} (h:g≠0) :phys g≠0 :=
  (map_ne_zero_iff _ (zxb L[X] FX)).2 h
private theorem eval_ne {g:L[X]} {c:L} (h:g.eval c≠0) :phys g≠0 :=
  phys_ne fun hz=>h (by simp [hz])
private theorem phys_eq :P5_7_7.phys=phys :=rfl
private theorem arc_coeff {E :Type} [Field E] [zZE L E] (η:E →ₐ[L] LaurentSeries L)
    (f :E[X][X]) (h) (y u:FX) :
    evalAt seriesJet (inl τ) (pair y u) (Ua η f h) =
      pair ((cLN η 0 f).eval₂ phys y)
        ((cLN η 1 f).eval₂ phys y+u*(cLN η 0 f).derivative.eval₂ phys y) := by
  simpa only [eval_phys,phys_eq] using eval_seriesJet η f h τ y u
theorem proof :P5_7_2_6Q3.c2 := by
  intro J U B q C₀ S R V T γ hγ hm hdet _ hg
  let η:=S.atPlace γ hγ
  let x :=phys (z7y - C R.center)
  let D:=phys (chartDen R B γ V T.t)
  let P:=phys (B.P γ)
  let Q:=phys (B.Q γ)
  let v₀:=scalar (V 0)
  let v₁:=scalar (V 1)
  let t:=scalar T.t
  let m₀:=scalar (targetNum R J γ)
  let m₁:=scalar (targetDen R J γ)
  let s₀:=scalar (R.b*S.direction γ R.coord)
  let s₁:=scalar (R.d*S.direction γ R.coord)
  let N :=P*v₁-Q*v₀
  let det:=m₀*v₁-m₁*v₀
  let κ:=N*(s₁*P-s₀*Q)
  have hx :x≠0:=phys_ne (X_sub_C_ne_zero R.center)
  have hD₀:=T.finite_den γ hγ hm
  have hD:D ≠0:=eval_ne hD₀
  have hQ:Q≠0:=phys_ne (B.denominator γ (S.Bp hγ))
  have hdet' : phys (C (targetDetAt R J γ V))=det:= by
    change scalar (targetDetAt R J γ V)=det
    simp only [targetDetAt,det,m₀,m₁,v₀,v₁,map_mul,map_sub]
  have hd:det≠0:= by
    rw [← hdet']
    exact phys_ne (C_ne_zero.mpr hdet)
  have hN :phys (crossDen B γ V)=N := by
    simp only [crossDen,N,P,Q,v₀,v₁,scalar,zQb,phys_eq,map_mul,map_sub]
  have hκ:phys (correction S R γ V)=κ:= by
    simp only [correction,map_mul,map_sub,hN,κ,s₀,s₁,P,Q,scalar,zQb,phys_eq]
  have hcross :x*(D+t*N)=m₀*Q-m₁*P:= by
    simpa only [map_mul,map_add,map_sub,hN,crossNum,x,D,t,m₀,m₁,P,Q,
      scalar,zQb,phys_eq] using congrArg phys (chart_cross R γ V T.t hm)
  obtain ⟨arc,harc,hres,_⟩:=S.arc γ hγ
  let z' := (LaurentSeries.powerSeriesEquivSubring L) (arc R.coord)
  have hz : (z' : LaurentSeries L)=η (C₀.seed R.coord) := by
    rw [show z' = (LaurentSeries.powerSeriesEquivSubring L) (arc R.coord) from rfl,
      LaurentSeries.powerSeriesEquivSubring_coe_apply]
    exact (harc _).symm
  have hs :PowerSeries.coeff 1 (arc R.coord)=S.direction γ R.coord:= by
    rw [Sheet.direction,dite_eq_left hγ,harc]
    exact (LaurentSeries.coeff_coe_powerSeries (arc R.coord) 1).symm
  have ha :seriesJet (constant R.a+constant R.b*z')=pair m₀ s₀:= by
    simpa only [z',hres,hs,m₀,s₀,targetNum] using jet_linear (arc R.coord) R.a R.b
  have hb:seriesJet (constant R.c+constant R.d*z')=pair m₁ s₁:= by
    simpa only [z',hres,hs,m₁,s₁,targetDen] using jet_linear (arc R.coord) R.c R.d
  have hf i j:=(S.value γ hγ _).symm.trans_le (S.integral γ hγ i j)
  have hg' i j:=(S.value γ hγ _).symm.trans_le
    (by simpa only [zQq,WithZero.exp_zero] using hg i j)
  have hchart:=aor η S.f T.g hf hg' R _ z' hz V T.t T.k T.transformed
  let w:=N/D
  let y (u:FX) :=slopeAt x D N m₀ m₁ s₀ s₁ v₀ v₁ P Q u
  let lo (u:FX) :=column x v₁ t (pair m₁ s₁) (pair w u)
  let F (k :ℤ) :=(cLN η k S.f).eval₂ phys (P/Q)
  let G (k :ℤ) :=(cLN η k T.g).eval₂ phys w
  let f' := (cLN η 0 S.f).derivative.eval₂ phys (P/Q)
  let g' := (cLN η 0 T.g).derivative.eval₂ phys w
  have hF:F 0=0:=S.root γ hγ
  have hf' : f' ≠ 0:=S.simple γ hγ
  have hcol (u:FX) : (lo u).fst=det*Q/D ∧
      column x v₀ t (pair m₀ s₀) (pair w u)=lo u*pair (P/Q) (y u) :=
    column_transport x D m₀ m₁ s₀ s₁ v₀ v₁ t P Q u hD hQ hd hcross
  have hjet (u:FX) :inl (x^T.k)*pair (G 0) (G 1+u*g') =
      (lo u)^S.d*pair (F 0) (F 1+y u*f') := by
    have he :=congrArg (evalAt seriesJet (inl τ) (pair w u)) hchart
    rw [map_mul,eval_param,arc_coeff,
      eval_chart R z' V T.t _ (cXJ η S.f hf).le (pair w u) (pair (P/Q) (y u))
        (dcQ J γ R.coord) (S.direction γ R.coord) ha hb (hcol u).2,
      arc_coeff] at he
    exact he
  have hweight:x^T.k≠0:=pow_ne_zero _ hx
  have hG:G 0=0:= by
    have he :=congrArg fst (hjet 0)
    simp only [fst_mul,fst_inl,pair_fst,hF,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hweight
  have hlin (u:FX) :x^T.k*(G 1+u*g')=(det*Q/D)^S.d*(F 1+y u*f') := by
    have he :=congrArg snd (hjet u)
    simpa only [DualNumber.snd_mul,fst_inl,snd_inl,pair_fst,pair_snd,fst_pow,(hcol u).1,
      hF,hG,zero_mul,mul_zero,add_zero,zero_add] using he
  have hslope :y 1-y 0=x*D^2/(det*Q^2) := by
    change ((x*D^2*1-κ)/(det*Q^2))-((x*D^2*0-κ)/(det*Q^2))= _
    rw [← sub_div]
    congr 1
    ring
  have hgsep:g' ≠ 0:= by
    have he :x^T.k*g' = (det*Q/D)^S.d*((y 1-y 0)*f') := by
      linear_combination hlin 1 - hlin 0
    intro hz
    rw [hz,mul_zero,hslope,eq_comm] at he
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (mul_ne_zero hd hQ) hD))
      (mul_ne_zero (div_ne_zero (mul_ne_zero hx (pow_ne_zero _ hD))
        (mul_ne_zero hd (pow_ne_zero _ hQ))) hf') he
  let φ:=phys (S.num γ)/phys (S.den γ)
  let δ:=(det*φ+κ)/(x*D^2)
  have hδ:x*D^2*δ=det*φ+κ:=mul_div_cancel₀ _ (mul_ne_zero hx (pow_ne_zero _ hD))
  have hδ' : y δ=φ/Q^2 := by
    change (x*D^2*δ-κ)/(det*Q^2)= _
    rw [hδ]
    field_simp [hd,hQ]
    ring
  have hφ:φ = -(F 1/f')*Q^2 :=S.formula γ hγ
  have hzero :G 1+δ*g' = 0:= by
    have hh:F 1+y δ*f' = 0:= by
      rw [hδ',hφ]
      field_simp [hQ,hf']
      ring
    have he :=hlin δ
    rw [hh,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hweight
  let A:SiteJet (atArc η T.g) R.center :=
    ⟨w,δ,⟨crossDen B γ V,chartDen R B γ V T.t,hD₀,by rw [hN]⟩,
      by simpa only [residue_arc] using hG,
      by simpa only [residue_arc] using hgsep,
      by simpa only [residue_arc] using hzero⟩
  refine ⟨A,?_⟩
  rw [show A.delta=δ from rfl]
  exact (show x*D^2*δ=phys (C (targetDetAt R J γ V))*φ+phys (correction S R γ V) by
    rw [hdet',hκ,hδ])
end
end P5_7_2_6Q3_2
end
namespace P5_7_2_6Q3
theorem proof :qgpYCte.c1 :=
  P5_7_2_6Q3.of_children P5_7_2_6Q3_1.proof P5_7_2_6Q3_2.proof
end P5_7_2_6Q3
