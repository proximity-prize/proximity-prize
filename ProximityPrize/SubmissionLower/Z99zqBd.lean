import ProximityPrize.SubmissionLower.ZQ2Yete
set_option Elab.async false
open _root_ renaming Finset.range → z4x, Finsupp.some_apply → zZ7, Fintype.sum_option → zy6, MvPolynomial → z3y, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.mem_restrictSupport_iff → zUj, MvPolynomial.mem_support_iff → zuk, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.optionEquivLeft_coeff_some_coeff_none → zL1, MvPolynomial.uniqueAlgEquiv → zpe, Nat.add_le_add_right → zlr, Nat.add_mul → zNE, Nat.add_sub_of_le → zp3, Nat.le_of_lt_succ → zeh, Nat.mul_one → zMo, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coeff_map → z0b, Polynomial.coeff_zero → zO6, Polynomial.mapEquiv → zNc, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.monomial → zdM, Polynomial.ringHom_ext → z86, PowerSeries.C → zMG, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, Submodule.smul_mem → zc2
section
section
namespace qgpYCte
noncomputable section
open Polynomial qe6nVeb qE3Ebna
open P5 (K)
open cu (L)
open E7 (CurvePlace poleOrder)
open qb0hmCe (CurveModel SiteTarget.det SiteTarget.height)
open qps5rle (SiteJet atArc finiteAt leadAt physicalParameter siteMatrix targetDet vSeed)
open qBnMK6c (chartDen reciprocalMatrix)
open scoped Classical WithZero
def changeOrdinate {E :Type} [Field E] (f :E[X][X])
    (M:Matrix (Fin 2) (Fin 2) E[X]) :E[X][X] :=
  ∑ i∈z4x (f.natDegree+1),C (f.coeff i) *
    (C (M 0 0)+C (M 0 1)*z7y)^i *
    (C (M 1 0)+C (M 1 1)*z7y)^(f.natDegree-i)
private theorem linear_pow_degree {R:Type*} [Semiring R] (a b:R) (n:ℕ) :
  ((C a+C b*z7y)^n).natDegree≤n:= by
 have h: (C a+C b*z7y).natDegree≤1 :=
  natDegree_add_le_of_degree_le (by simp)
    (natDegree_mul_le.trans (by simpa only [natDegree_C,zero_add] using natDegree_X_le))
 simpa only [zMo] using natDegree_pow_le_of_le n h
private theorem linear_pow_coeff {R:Type*} [Semiring R] (a b:R) (n:ℕ) :
  ((C a+C b*z7y)^n).coeff n=b^n:= by
 have h:=coeff_pow_of_natDegree_le (m:=n) (linear_pow_degree a b 1)
 simpa [coeff_add,coeff_C_mul] using h
theorem changeOrdinate_coeff_top {E :Type} [Field E] (f :E[X][X])
   (M:Matrix (Fin 2) (Fin 2) E[X]) :
   (changeOrdinate f M).coeff f.natDegree =
     ∑ i∈z4x (f.natDegree+1),f.coeff i*(M 0 1)^i*(M 1 1)^(f.natDegree-i) := by
 rw [changeOrdinate,finsetSum_coeff]
 refine Finset.sum_congr rfl fun i hi => ?_
 have h:=coeff_mul_add_eq_of_natDegree_le
   (linear_pow_degree (M 0 0) (M 0 1) i)
   (linear_pow_degree (M 1 0) (M 1 1) (f.natDegree-i))
 rw [zp3 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
   linear_pow_coeff,linear_pow_coeff] at h
 rw [mul_assoc,coeff_C_mul,h,mul_assoc]
theorem changeOrdinate_degree {E :Type} [Field E] (f :E[X][X])
  (M:Matrix (Fin 2) (Fin 2) E[X])
  (h: (∑ i∈z4x (f.natDegree+1),
    f.coeff i*(M 0 1)^i*(M 1 1)^(f.natDegree-i))≠0) :
  (changeOrdinate f M).natDegree=f.natDegree := by
 refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rwa [changeOrdinate_coeff_top]))
 unfold changeOrdinate
 refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
 refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_C _).le
  (linear_pow_degree _ _ _)) (linear_pow_degree _ _ _)).trans ?_
 simpa only [zero_add] using (zp3 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).le
structure ChartData {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (R:SiteTarget) (V:Fin 2→L) where
 t:L
 k :ℕ
 g:C.E[X][X]
 transformed:z1z (physicalParameter R.center^k)*g =
   changeOrdinate S.f (siteMatrix R (C.seed R.coord) V (reciprocalMatrix t))
 degree :g.natDegree=S.d
 lead_ne :leadAt R.center g≠0
 finite_den : ∀ γ∈S.marks,matchesTarget R B γ→(chartDen R B γ V t).eval R.center≠0
structure SiteChart {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (R:SiteTarget) where
 V:Fin 2→L
 M:Matrix (Fin 2) (Fin 2) L
 matrix_ne :M.det≠0
 det_ne :targetDet R (C.seed R.coord) V≠0
 k :ℕ
 g:C.E[X][X]
 transformed:z1z (physicalParameter R.center^k)*g =
   changeOrdinate S.f (siteMatrix R (C.seed R.coord) V M)
 degree :g.natDegree=S.d
 lead_ne :leadAt R.center g≠0
 lead_height: (∑ᶠ v :CurvePlace L C.E,poleOrder v.value (leadAt R.center g)) ≤
   S.h+S.d*R.height q
 det_unit : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ →
   (S.atPlace γ hγ (targetDet R (C.seed R.coord) V)).coeff 0≠0
 integral : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ → ∀ i j,
   vSeed (((atArc (S.atPlace γ hγ) g).coeff i).coeff j)≤1
 jet : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ →
   ∃ A:SiteJet (atArc (S.atPlace γ hγ) g) R.center,
     finiteAt R.center A.delta →
     ((S.num γ).eval R.center=0↔R.det=0∨S.direction γ R.coord=0)
end
end qgpYCte
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBnMK6c
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna qps5rle
open P5 (K)
open cu (L FX)
open E7 (CurvePlace poleOrder)
open qb0hmCe (CurveModel SiteTarget.height)
open qFD8jve (aFA sheetPole seedPole)
open scoped Classical WithZero
variable {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane} {C₀:CurveModel q}
private theorem complement (S:Sheet B C₀) (R:SiteTarget) :
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
private theorem det_residue (S:Sheet B C₀) (R:SiteTarget) (V:Fin 2→L)
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
private theorem coprime_eval {N D:L[X]} (h:IsCoprime N D) (x :L)
  (hD:D.eval x=0) :N.eval x≠0:= by
 intro hN
 obtain ⟨u,v,huv⟩:=h
 have he :=congrArg (fun f :L[X]=>f.eval x) huv
 simp only [eval_add,eval_mul,hN,hD,mul_zero,zero_add,eval_one,zero_ne_one] at he
private theorem mark_scale (S:Sheet B C₀) (R:SiteTarget) {γ:K}
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
private theorem crossDen_eval (R:SiteTarget) (γ:K) (V:Fin 2→L) {scale :L}
  (hP: (B.P γ).eval R.center=scale*targetNum R J γ)
  (hQ: (B.Q γ).eval R.center=scale*targetDen R J γ) :
  (crossDen B γ V).eval R.center=scale*targetDetAt R J γ V:= by
 simp only [crossDen,eval_sub,eval_mul,eval_C,hP,hQ,targetDetAt]
 ring
private theorem phys_inj:Function.Injective phys :=IsFractionRing.injective L[X] FX
private theorem reduced_test (x :L) {N D T A B:L[X]} {u:L}
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
private theorem height_of_bound (S:Sheet B C₀) (R:SiteTarget) {g:C₀.E[X][X]}
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
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qj0Yp9c
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5_7_7 (Dg)
private theorem c4Q {R E :Type} [CommRing R] [Field E] (S:Subfield E)
   (f :R[X] →+* E) (hc : ∀ c,f (z1z c)∈S) (hx :f z7y∈S)
   (p:R[X]) :f p∈S:= by
 induction p using Polynomial.induction_on' with
 | add p q hp hq=>rw [map_add]; exact add_mem hp hq
 | monomial n c =>
   rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
   exact mul_mem (hc c) (pow_mem hx _)
theorem chart_fraction {J:Input} (C:Chart J) (t:EC J) (ht:t≠0) :
    ∃ u∈aho C,∃ v∈aho C,v≠0∧t=u/v := by
  let G:Set (EC J) := {amm J,seed J,numeratorU C,numeratorV C}
  let S:=IntermediateField.adjoin C.base G
  have hmem : ∀ g∈G,g∈S:= fun _ hg=>IntermediateField.subset_adjoin _ _ hg
  have hx :amm J∈S:=hmem _ (by simp [G])
  have hz :seed J∈S:=hmem _ (by simp [G])
  have hu:numeratorU C∈S:=hmem _ (by simp [G])
  have hv :numeratorV C∈S:=hmem _ (by simp [G])
  have hy :jU J false∈S:= by
    have he :numeratorV C/numeratorU C=jU J false := by
      unfold numeratorV numeratorU
      field_simp [show denominator C≠0 from C.ayD]
    exact he ▸ div_mem hv hu
  have hconst (c:L) :constant J c∈S:= by
    rw [← C.scalar_eq]
    exact S.algebraMap_mem (C.scalar c)
  have hroot (f :Dg) :a7W J f∈S :=
    c4Q S.toSubfield (a7W J)
      (fun f=>c4Q S.toSubfield ((a7W J).comp z1z)
        (fun g=>c4Q S.toSubfield (((a7W J).comp z1z).comp z1z)
          hconst hx g) hz f) hy f
  obtain ⟨u,v,_,hfrac⟩:=IsFractionRing.div_surjective (AdjoinRoot J.F) t
  obtain ⟨U,rfl⟩:=AdjoinRoot.mk_surjective u
  obtain ⟨V,rfl⟩:=AdjoinRoot.mk_surjective v
  change a7W J U/a7W J V=t at hfrac
  have hS:t∈S:=hfrac ▸ div_mem (hroot U) (hroot V)
  obtain ⟨u,hu,v,hv,h⟩:=(IntermediateField.mem_adjoin_iff_div.mp hS)
  exact ⟨u,hu,v,hv,fun hv0=>ht (by simp [h,hv0]),h⟩
theorem equation_vanish {J:Input} (C:Chart J) :m8 C (equation C)=0:= by
  let f :=(m8 C).comp (mapRingHom (mapRingHom (mapRingHom C.scalar)))
  have hf :f=a7W J:= by
    apply z86
    · intro g
      suffices he :f.comp z1z=(a7W J).comp z1z from
        zLs he g
      apply z86
      · intro h
        suffices he : (f.comp z1z).comp z1z =
            ((a7W J).comp z1z).comp z1z from zLs he h
        apply z86
        · intro a
          simpa only [f,m8,zQb,coe_mapRingHom,zrL,
            coe_eval₂RingHom,eval₂_C,Subfield.subtype_apply,constant] using C.scalar_eq a
        · simp only [f,m8,zQb,coe_mapRingHom,zrL,
            zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
          rfl
      · simp only [f,m8,zQb,coe_mapRingHom,zrL,
          zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
        rfl
    · simp only [f,m8,zQb,coe_mapRingHom,zSo,
        coe_eval₂RingHom,eval₂_X]
      rfl
  change f J.F=0
  rw [hf]
  exact (rootMap_eq_zero_iff J J.F).mpr dvd_rfl
theorem mono_mem {J:Input} (C:Chart J) {i j u v a b c:ℕ}
  (ha :u+v=a) (hb:i≤b+u*J.s) (hc:j≤ c) :mono C i j u v∈dO C a b c:= by
 have hu:a-v=u:= by omega
 exact Submodule.subset_span ⟨⟨⟨v,by omega⟩,⟨i,by simpa [hu] using Nat.lt_succ_of_le hb⟩,
  ⟨j,by omega⟩⟩,by simp [pieceMono,hu]⟩
private theorem piece_ordinate_succ {J:Input} (C:Chart J) (a b c:ℕ) :
    dO C a b c≤dO C (a+1) b c:= by
  apply Submodule.span_le.mpr
  rintro _ ⟨m,rfl⟩
  let i:=m.2.1.val
  let j:=m.2.2.val
  let v :=m.1.val
  let u:=a-v
  have ha :u+v=a :=zxt (zeh m.1.isLt)
  have hb:i≤b+u*J.s :=zeh m.2.1.isLt
  have hc:j≤ c:=zeh m.2.2.isLt
  have hU:=mono_mem C (a :=a+1) (b:=b) (c:=c) (u:=u+1) (v :=v) (i:=i)
    (j:=j) (by omega) (hb.trans (by rw [zNE]; omega)) hc
  have hV:=mono_mem C (a :=a+1) (b:=b) (c:=c) (u:=u) (v :=v+1) (i:=i)
    (j:=j) (by omega) hb hc
  have he :mono C i j u v =
      mono C i j (u+1) v+C.scalar C.tilt•mono C i j u (v+1) := by
    change mono C i j u v =
      mono C i j (u+1) v+(C.scalar C.tilt:EC J)*mono C i j u (v+1)
    rw [C.scalar_eq]
    calc
      _=mono C i j u v*(numeratorU C+constant J C.tilt*numeratorV C) := by
        rw [chart_identity,mul_one]
      _ = _:= by simp only [mono,pow_succ]; ring
  change mono C i j u v∈_
  rw [he]
  exact add_mem hU (zc2 _ _ hV)
theorem a6w {J:Input} (C:Chart J) {a b c a' b' c' : ℕ}
  (ha :a≤a') (hb:b≤b') (hc:c≤ c') :dO C a b c≤dO C a' b' c' := by
 have h:dO C a b c≤dO C a' b c :=
  (monotone_nat_of_le_succ (fun n=>piece_ordinate_succ C n b c)) ha
 refine h.trans (Submodule.span_le.mpr ?_)
 rintro _ ⟨m,rfl⟩
 exact mono_mem C (zxt (zeh m.1.isLt))
  ((zeh m.2.1.isLt).trans (zlr hb _))
  ((zeh m.2.2.isLt).trans hc)
theorem eLg {J:Input} (C:Chart J) {a b c d e f :ℕ} {x y :EC J}
   (hx :x∈dO C a b c) (hy :y∈dO C d e f) :
   x*y∈dO C (a+d) (b+e) (c+f) := by
 refine Submodule.span_induction₂ (p:= fun x y _ _=>x*y∈dO C (a+d) (b+e) (c+f))
   ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
 · rintro _ _ ⟨m,rfl⟩ ⟨n,rfl⟩
   have hm:=zxt (zeh m.1.isLt)
   have hn:=zxt (zeh n.1.isLt)
   have hP:=Nat.add_le_add (zeh m.2.1.isLt) (zeh n.2.1.isLt)
   have hS:=Nat.add_le_add (zeh m.2.2.isLt) (zeh n.2.2.isLt)
   have h:=mono_mem C (a :=a+d) (b:=b+e) (c:=c+f)
     (u:=(a-m.1.val)+(d-n.1.val)) (v :=m.1.val+n.1.val)
     (i:=m.2.1.val+n.2.1.val) (j:=m.2.2.val+n.2.2.val)
     (by omega) (by rw [zNE]; omega) hS
   convert h using 1
   simp only [pieceMono,mono,pow_add]
   ring
 · intro y hy; simp
 · intro x hx; simp
 · intro x y z hx hy hz h₁ h₂
   rw [add_mul]; exact add_mem h₁ h₂
 · intro x y z hx hy hz h₁ h₂
   rw [mul_add]; exact add_mem h₁ h₂
 · intro r x y hx hy h
   rw [smul_mul_assoc]; exact zc2 _ _ h
 · intro r x y hx hy h
   rw [mul_smul_comm]; exact zc2 _ _ h
private theorem chart_ring_exhaust {J:Input} (C:Chart J) {x :EC J}
    (hx :x∈aho C) : ∃ n:ℕ,x∈dO C n n n:= by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h:=mono_mem C (a :=0) (b:=1) (c:=0) (i:=1) (j:=0) (u:=0)
        (v :=0) (by omega) (by simp) (by omega)
      exact ⟨1,a6w C (by decide :0≤1) le_rfl (by decide :0≤1) (by simpa [mono] using h)⟩
    · have h:=mono_mem C (a :=0) (b:=0) (c:=1) (i:=0) (j:=1) (u:=0)
        (v :=0) (by omega) (by simp) (by omega)
      exact ⟨1,a6w C (by decide :0≤1) (by decide :0≤1) le_rfl (by simpa [mono] using h)⟩
    · have h:=mono_mem C (a :=1) (b:=1) (c:=1) (i:=0) (j:=0) (u:=1)
        (v :=0) (by omega) (by omega) (by omega)
      exact ⟨1,by simpa [mono] using h⟩
    · have h:=mono_mem C (a :=1) (b:=1) (c:=1) (i:=0) (j:=0) (u:=0)
        (v :=1) (by omega) (by omega) (by omega)
      exact ⟨1,by simpa [mono] using h⟩
  | algebraMap r =>
    have h: (1 :EC J)∈dO C 0 0 0:= by
      simpa [mono] using mono_mem C (a :=0) (b:=0) (c:=0) (i:=0) (j:=0)
        (u:=0) (v :=0) (by omega) (by simp) (by omega)
    exact ⟨0,by simpa only [Algebra.smul_def,mul_one] using (dO C 0 0 0).smul_mem r h⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨m,hm⟩:=hx'
    obtain ⟨n,hn⟩:=hy'
    have hm' := le_max_left m n
    have hn' := le_max_right m n
    exact ⟨max m n,add_mem (a6w C hm' hm' hm' hm) (a6w C hn' hn' hn' hn)⟩
  | mul x y hx hy hx' hy' =>
    obtain ⟨m,hm⟩:=hx'
    obtain ⟨n,hn⟩:=hy'
    exact ⟨m+n,eLg C hm hn⟩
theorem piece_cofinal {J:Input} (C:Chart J) (V:Submodule C.base (EC J))
  [FiniteDimensional C.base V] (hV:V≤(aho C).toSubmodule) :
  ∃ N :ℕ,∀ a b c:ℕ,N≤a→N≤b→N≤ c→V≤dO C a b c:= by
 classical
 let:Module.Free C.base V:=Module.Free.of_divisionRing C.base V
 let B:=Module.finBasis C.base V
 choose n hn using fun i=>chart_ring_exhaust C (hV (B i).property)
 let N :=Finset.univ.sup n
 refine ⟨N,fun a b c ha hb hc z hz => ?_⟩
 have hN (i) :n i≤N :=Finset.le_sup (Finset.mem_univ i)
 have hle :Submodule.span C.base (Set.range B)≤(dO C a b c).comap V.subtype := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact a6w C ((hN i).trans ha) ((hN i).trans hb) ((hN i).trans hc) (hn i)
 rw [B.span_eq] at hle
 exact hle (show (⟨z,hz⟩:V) ∈ ⊤ by trivial)
end
end qj0Yp9c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBTXDtb
noncomputable section
open Polynomial
open qj0Yp9c (fits)
abbrev Vars :=Option (Option Unit)
abbrev Exp:=Vars →₀ ℕ
abbrev Multi (K:Type) [CommSemiring K] :=z3y Vars K
variable {K:Type} [Field K]
private def bg6:z3y (Option Unit) K ≃+* K[X][X] :=
 (zpj K Unit).toRingEquiv.trans
   (zNc (zpe K Unit).toRingEquiv)
def expand:K[X][X][X] ≃+* Multi K :=
  (zNc bg6.symm).trans
    (zpj K (Option Unit)).toRingEquiv.symm
private theorem coeff_seed (f :z3y (Option Unit) K) (v :Option Unit →₀ ℕ) :
  ((bg6 f).coeff (v none)).coeff (v.some ())=f.coeff v := by
 change (((zpj K Unit f).map
  (zpe K Unit).toRingHom).coeff _).coeff _ = _
 rw [z0b]
 change ((zpe K Unit)
  ((zpj K Unit f).coeff _)).coeff _ = _
 rw [MvPolynomial.coeff_uniqueAlgEquiv,← Finsupp.unique_single v.some,
  zL1]
theorem coeff_expand (F:K[X][X][X]) (v :Exp) :
   (expand F).coeff v=(((F.coeff (v none)).coeff (v.some none)).coeff (v.some.some ())) := by
 have he : (zpj K (Option Unit)) (expand F) =
     F.map bg6.symm.toRingHom :=
   (zpj K (Option Unit)).toRingEquiv.apply_symm_apply _
 rw [← zL1,he,z0b]
 change (bg6.symm (F.coeff (v none))).coeff v.some= _
 simpa only [RingEquiv.apply_symm_apply] using
   (coeff_seed (bg6.symm (F.coeff (v none))) v.some).symm
def exponent (k j i:ℕ) :Exp :=
 ((Finsupp.single () i).optionElim j).optionElim k
@[simp] theorem exponent_y (k j i:ℕ) :exponent k j i none=k :=
  Finsupp.optionElim_apply_none ..
@[simp] theorem exponent_z (k j i:ℕ) :exponent k j i (some none)=j:= by
  simp [exponent]
@[simp] theorem exponent_x (k j i:ℕ) :exponent k j i (some (some ()))=i:= by
  simp [exponent]
theorem exponent_eta (v :Exp) :exponent (v none) (v.some none) (v.some.some ())=v := by
 ext t
 cases t with
 | none=>simp [exponent]
 | some t =>
   cases t with
   | none=>simp [exponent]
   | some t=>cases t; simp [exponent]
private theorem exponent_eq_iff (u v :Exp) :
   u=v↔u none=v none∧u.some none=v.some none∧u.some.some ()=v.some.some () := by
 constructor
 · rintro rfl; exact ⟨rfl,rfl,rfl⟩
 · rintro ⟨h₁,h₂,h₃⟩
   calc
     u=exponent (u none) (u.some none) (u.some.some ()) :=(exponent_eta u).symm
     _=exponent (v none) (v.some none) (v.some.some ()) := by rw [h₁,h₂,h₃]
     _=v :=exponent_eta v
theorem expand_monomial (k j i:ℕ) (d:K) :
   expand (zdM k (zdM j (zdM i d))) =
     MvPolynomial.monomial (exponent k j i) d:= by
 ext v
 simp only [coeff_expand,MvPolynomial.coeff_monomial,exponent_eq_iff,
   zZ7,exponent_y,exponent_z,exponent_x]
 by_cases hk :k=v none <;> by_cases hj:j=v (some none) <;>
   by_cases hi:i=v (some (some ())) <;> simp [Polynomial.coeff_monomial,hk,hj,hi]
private def weights (a b c:ℕ) :Vars→ℕ
 | none=>a
 | some none=>b
 | some (some _)=>c
private theorem c0Q (a b c:ℕ) (v :Exp) :
  Finsupp.weight (weights a b c) v=v none*a+v.some none*b+v.some.some ()*c:= by
 rw [Finsupp.weight_eq_sum,zy6,zy6]
 simp [weights,zZ7,smul_eq_mul,add_assoc]
def deg (a b c:ℕ) (F:Multi K) :ℕ :=
 F.weightedTotalDegree (weights a b c)
theorem deg_mul {P Q:Multi K} (hp:P≠0) (hq:Q≠0) (a b c:ℕ) :
  deg a b c (P*Q)=deg a b c P+deg a b c Q :=
 MvPolynomial.weightedTotalDegree_mul _ _ _ hp hq
def cV (s a b c:ℕ) :Set Exp :=
 {v | v none≤a∧v.some none≤ c∧v.some.some ()+v none*s≤b+a*s}
def space (K:Type) [Field K] (s a b c:ℕ) :Submodule K (Multi K) :=
 MvPolynomial.restrictSupport K (cV s a b c)
theorem mem_space {s a b c:ℕ} {P:Multi K} :
  P∈space K s a b c↔deg 1 0 0 P≤a∧deg 0 1 0 P≤ c∧deg s 0 1 P≤b+a*s := by
 simp only [space,zUj,Set.subset_def,Finset.mem_coe,
  cV,Set.mem_ofPred_eq,deg,MvPolynomial.weightedTotalDegree,Finset.sup_le_iff,
  c0Q,Nat.mul_zero,zMo,Nat.zero_add,add_comm,
  forall_and]
theorem fits_expand {s a b c:ℕ} {F:K[X][X][X]} :
    fits s a b c F↔expand F∈space K s a b c:= by
  rw [space,zUj]
  constructor
  · rintro ⟨ha,hc,hb⟩ v hv
    have hn:=MvPolynomial.mem_support_iff.mp hv
    rw [coeff_expand] at hn
    have hkj: (F.coeff (v none)).coeff (v.some none)≠0 :=
      fun he=>hn (by rw [he,zO6])
    have hk :F.coeff (v none)≠0:= fun he=>hkj (by rw [he,zO6])
    exact ⟨(le_natDegree_of_ne_zero hk).trans ha,(le_natDegree_of_ne_zero hkj).trans (hc _),
      (zlr (le_natDegree_of_ne_zero hn) _).trans (hb _ _ hkj)⟩
  · intro h
    have hterm (k j i:ℕ) (hn: (((F.coeff k).coeff j).coeff i)≠0) :
        k≤a∧j≤ c∧i+k*s≤b+a*s := by
      have he :exponent k j i∈(expand F).support := by
        simpa [zuk,coeff_expand] using hn
      simpa [cV] using h he
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_,fun k =>
      natDegree_le_iff_coeff_eq_zero.mpr ?_,fun k j hn => ?_⟩
    · intro k hk
      by_contra hn
      let j:=(F.coeff k).natDegree
      have hj: (F.coeff k).coeff j≠0:=leadingCoeff_ne_zero.mpr hn
      exact (not_le_of_gt hk) (hterm k j _ (leadingCoeff_ne_zero.mpr hj)).1
    · intro j hj
      by_contra hn
      exact (not_le_of_gt hj) (hterm k j _ (leadingCoeff_ne_zero.mpr hn)).2.1
    · exact (hterm k j _ (leadingCoeff_ne_zero.mpr hn)).2.2
theorem leading_bounds {F:K[X][X][X]} (hF:F≠0) (s :ℕ) :
  F.natDegree≤deg 1 0 0 (expand F)∧F.natDegree*s≤deg s 0 1 (expand F) := by
 let k :=F.natDegree
 let j:=(F.coeff k).natDegree
 let i:=((F.coeff k).coeff j).natDegree
 have h: (((F.coeff k).coeff j).coeff i)≠0 :=
  leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hF))
 have hv :exponent k j i∈(expand F).support := by
  simpa [zuk,coeff_expand] using h
 have h₁:=z6P (weights 1 0 0) hv
 have h₂:=z6P (weights s 0 1) hv
 simp only [c0Q,zZ7,exponent_y,exponent_z,exponent_x,
  zMo,Nat.mul_zero,Nat.add_zero] at h₁ h₂
 exact ⟨h₁,(Nat.le_add_right _ _).trans h₂⟩
theorem space_mul {s a b c d e f :ℕ} {P Q:Multi K}
   (hP:P∈space K s a b c) (hQ:Q∈space K s d e f) :
   P*Q∈space K s (a+d) (b+e) (c+f) := by
 by_cases hp:P=0
 · simp [hp]
 by_cases hq:Q=0
 · simp [hq]
 rw [mem_space] at hP hQ ⊢
 simp only [deg_mul hp hq,zNE]
 omega
theorem space_cancel {s a b c d e f :ℕ} {P Q:Multi K}
   (hp:P≠0) (ho:deg 1 0 0 P=a) (hz :deg 0 1 0 P=c)
   (hw:deg s 0 1 P=b+a*s) (h:P*Q∈space K s (a+d) (b+e) (c+f)) :
   Q∈space K s d e f := by
 by_cases hq:Q=0
 · simp [hq]
 rw [mem_space] at h ⊢
 simp only [deg_mul hp hq,ho,hz,hw,zNE] at h
 omega
end
end qBTXDtb
end
end
