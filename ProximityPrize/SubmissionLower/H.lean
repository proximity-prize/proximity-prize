import ProximityPrize.SubmissionLower.Y
import ProximityPrize.SubmissionLower.BK
set_option Elab.async false
open _root_ renaming AlgHom.comp_assoc→Qy,AlgHom.congr_fun→KH,AlgHom.id→C9,Algebra→ oj,Algebra.EssFiniteType→xm,Algebra.FormallySmooth→UP,Algebra.FormallyUnramified→Ar,Algebra.IsAlgebraic→UZ,Algebra.algebraMap→aU,Algebra.smul_def→Lf,AlgebraicIndependent→Mz,Cardinal.mk_fintype→RD,CharP.char_is_prime_of_two_le→SM,CommRing→n5,CommSemiring→zg,DFunLike.congr_fun→MK,DecidableEq→Kl,ExpChar→zc,Field→ oq,Filter.eventually_ge_atTop→Nj,Fin.sum_univ_three→Pj,Fin.val→C4,FiniteDimensional→x7,Finset→qy,Finset.induction_on→Te,Finset.mem_filter→Gj,Finset.mem_univ→vh,Finset.mul_sum→Nr,Finset.prod_insert→MS,Finset.range→pz,Finset.sum_add_distrib→G2,Finset.sum_congr→qm,Finset.sum_eq_single→Up,Finset.sum_eq_zero→GF,Finset.sum_erase_add→Ww,Finset.sum_filter→F9,Finset.sum_range_succ→VC,Finset.sup_le→LP,Finsupp.add_apply→SD,Finsupp.degree_eq_sum→PA,Finsupp.prod_fintype→Ok,Finsupp.single→LR,Finsupp.sum_fintype→zE,Finsupp.tsub_apply→RP,Finsupp.weight→vw,Finsupp.weight_apply→JK,Finsupp.weight_single→Au,Fintype→qz
open _root_ renaming Fintype.card→wY,Fintype.ofFinite→Kh,FractionRing→xW,Function.Injective→t9,Function.LeftInverse→Pv,Function.Surjective→t8,Function.comp_apply→zk,Function.iterate_succ_apply→Av,Ideal→lz,Ideal.Quotient.eq_zero_iff_mem→NX,Ideal.Quotient.factorₐ→Ob,Ideal.Quotient.mk→nX,Ideal.Quotient.mk_eq_mk_iff_sub_mem→Ts,Ideal.Quotient.mk_surjective→y5,Ideal.Quotient.mkₐ→u9,Ideal.comap_comap→TZ,Ideal.comap_isPrime→xu,Ideal.map_le_iff_le_comap→Vs,Ideal.map_map→t4,Ideal.map_mono→yQ,Ideal.map_span→sS,Ideal.mem_map_of_mem→ Iw,Ideal.mem_span_singleton_self→EK,Ideal.mem_sup_left→Qx,Ideal.mem_sup_right→G5,Ideal.pow_le_pow_right→LO,Ideal.pow_mem_pow→NZ,Ideal.quotientEquivAlgOfEq→OJ,Ideal.quotientMap→HZ,Ideal.quotientMapₐ→WD,Ideal.span→lJ,Ideal.span_singleton_le_iff_mem→Dz,Ideal.subset_span→qx,IsFractionRing.injective→Ea,IsLocalHom→Cy,IsLocalRing→MO,IsLocalRing.ResidueField→Df,IsLocalRing.maximalIdeal→ oK,IsLocalRing.maximalIdeal.isMaximal→PM,IsLocalization→xL,IsLocalization.AtPrime.to_map_mem_maximal_iff→Sd,IsLocalization.algebraMap_mem_map_algebraMap_iff→KA,IsLocalization.surj→TI,IsPurelyInseparable→PD,IsRelPrime→z9,IsScalarTower→zf,IsScalarTower.algebraMap_apply→FR,IsScalarTower.algebraMap_eq→t6
open _root_ renaming IsScalarTower.toAlgHom→Pk,LinearEquiv.ofInjective→Vl,LinearIndependent→Ee,LinearMap.mulLeft→WW,Localization.AtPrime→ oy,Localization.AtPrime.algebraOfLiesOver→Nq,Localization.AtPrime.map_eq_maximalIdeal→yo,Localization.localRingHom→Wl,Module.Finite→p7,Module.Flat→u5,Module.finrank→pL,Module.finrank_baseChange→SU,Module.length→pC,Module.length_eq_add_of_exact→UY,Module.length_eq_coheight→N0,Module.length_le_of_surjective→SL,Module.length_quotient→Kp,MulZeroClass.mul_zero→th,MvPolynomial→cy,MvPolynomial.C→qU,MvPolynomial.X→mD,MvPolynomial.aeval→sH,MvPolynomial.aeval_X→yJ,MvPolynomial.affineHilbertPolynomial→zS,MvPolynomial.algHom_ext→VH,MvPolynomial.algebraMap_def→Dv,MvPolynomial.algebraMap_eq→v9,MvPolynomial.as_sum→Mk,MvPolynomial.coeff_map→Gn,MvPolynomial.coeff_monomial→zh,MvPolynomial.coeff_sum→ze,MvPolynomial.constantCoeff→Dw,MvPolynomial.eval→ ox,MvPolynomial.eval_monomial→SC,MvPolynomial.eval₂Hom→z8,MvPolynomial.eval₂Hom_monomial→Re,MvPolynomial.homogeneousComponent→G8,MvPolynomial.isLocalization→Pr,MvPolynomial.le_totalDegree→Bf,MvPolynomial.map→nq,MvPolynomial.map_map→zm,MvPolynomial.monomial→ oZ,MvPolynomial.monomial_eq→Hw,MvPolynomial.pderiv→vi,MvPolynomial.pderiv_mul→FU,MvPolynomial.restrictSupport→t5,MvPolynomial.restrictSupport_eq_span→Kv,MvPolynomial.ringHom_ext→wR
open _root_ renaming MvPolynomial.weightedHomogeneousSubmodule→ In,MvPolynomial.weightedTotalDegree_mul_le→Ml,MvPolynomial.weightedTotalDegree_one→ IT,MvPolynomial.weightedTotalDegree_piSingle→ Il,Nat.add_comm→LQ,Nat.add_le_add→Fz,Nat.add_le_add_left→zi,Nat.add_mul→z7,Nat.ascFactorial_succ→WK,Nat.ascFactorial_zero→S1,Nat.card_coe_set_eq→RC,Nat.card_congr→J4,Nat.card_eq_fintype_card→TH,Nat.cast_add→EP,Nat.cast_mul→Ef,Nat.le_add_right→vZ,Nat.le_mul_of_pos_right→G4,Nat.lt_succ_of_le→Pc,Nat.mul_comm→Et,Nat.mul_le_mul_left→p9,Nat.mul_pos→GR,Nat.pos_of_ne_zero→Rm,Nat.strong_induction_on→NW,Nat.succ_pos→Np,Nat.zero_le→ IU,Or.inl→uJ,Or.inr→p6,Order.coheight→zd,Order.coheight_anti→Sv,Pi.single_eq_of_ne→Un,Polynomial→sI,Polynomial.C→uz,Polynomial.X→ II,Polynomial.aeval→JM,Polynomial.coeff_eq_zero_of_natDegree_lt→RJ,Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le→P7,Polynomial.evalRingHom→Mj,Polynomial.eval_C→JQ,Polynomial.eval_X→Pf,Polynomial.eval_add→Wm,Polynomial.eval_mul→S2,Polynomial.natDegree_C_mul_le→R9,Polynomial.preHilbertPoly→GY,Polynomial.taylor→KI,RingHom.comp_apply→yl,RingHom.congr_fun→xI,RingHom.ker→t7,Set.image_insert_eq→vH
open _root_ renaming Set.image_singleton→uh,Set.insert_subset_iff→Oc,Set.mem_ofPred_eq→VS,Set.mem_zero→Mw,Set.range→ oD,Submodule→t3,Submodule.Quotient.mk_eq_zero→yU,Submodule.factor→Eg,Submodule.factor_surjective→Gr,Submodule.map_comp→G9,Submodule.mkQ_apply→v8,Submodule.span_le→Qw,Submodule.sub_mem→QL,Submodule.sum_mem→Vz,Submonoid→G0,Subsingleton→Kc,Subtype.ext→qM,Subtype.val→NI,Subtype.val_injective→G7,UH.Exponent→zR,UH.lattice→nI,aR.Shape→c9,aR.Shape.plus→pU,aR.Shape.scale→pQ,aR.shape→p5,add_comm→yL,ap6.homogeneous→G6,charP_of_injective_ringHom→G3,congrArg→ oz,congrFun→yB,dN.GeoField→lV,dN.GeoJets→lI,dN.separant→qG,div_le_div_of_nonneg_right→VO,eq_neg_of_add_eq_zero_left→SW,inferInstance→vj,le_antisymm→GB,le_rfl→vl,le_sup_left→Gk,lt_of_le_of_ne→Kz,map_add→ oY,map_mul→ ov,map_natCast→JW,map_pow→uW,map_prod→Aa,map_sub→Du,map_sum→pG,map_zero→qJ
open _root_ renaming min_le_left→G1,min_le_right→Gi,mul_assoc→vG,mul_comm→FK,ne_top_of_le_ne_top→Vq,nonZeroDivisors→C5,one_smul→FQ,pow_succ→wB,pow_succ'→vk,pow_zero→FV,ringKrullDim→u8,succ_nsmul→Fa,tsub_add_cancel_of_le→NY,zero_add→wA
set_option autoImplicit true
section
namespace UH
open aR lB YV
open scoped Pointwise
theorem asK (p:c9) :0∈nI p:= by
 simp [nI]
theorem aON {p:c9} {e :zR} :
  e∈nI p↔(fun i=>(e i:ℝ))∈cap p:= by
 change (_∧_∧_) ↔
  (∀ i,0≤(e i:ℝ))∧((e 0:ℝ)+e 1+e 2+e 3≤p.b) ∧
    ((e 1 :ℝ)+2*e 2 + 3*e 3≤p.j)∧(e 3:ℝ)≤p.t
 simp only [Nat.cast_nonneg,implies_true,true_and]
 exact_mod_cast Iff.rfl
theorem b7i:nI ⟨0,0,0⟩=0:= by
 ext e
 rw [aON,auw,Mw ,Mw]
 constructor
 · intro he
   ext i
   change e i=0
   have hi: (e i:ℝ)=0:=yB he i
   exact_mod_cast hi
 · rintro rfl
   funext i
   simp
private theorem gun {x y A B:ℕ} (h:x+2*y≤A+B)
  (he :Even A∨Even B) :
  ∃ u≤x,∃ v≤y,u+2*v≤A∧(x - u)+2*(y - v)≤B:= by
 have hab: (A+B)/2=A/2+B/2 := by
  rcases he with ⟨s,hs⟩ | ⟨s,hs⟩ <;> omega
 let v :=min y (A/2)
 have hvy :v≤y :=G1 _ _
 have hvA:v≤A/2 :=Gi _ _
 have hvB:y - v≤B/2 := by
  dsimp [v]
  omega
 let u:=min x (A - 2*v)
 have hux :u≤x :=G1 _ _
 have huA:u≤A - 2*v :=Gi _ _
 refine ⟨u,hux,v,hvy,by omega,?_⟩
 dsimp [u]
 omega
theorem aOn {p q:c9} (hp:bF p) (hq:bF q)
    (hpj:Even p.j) (hpt:Even p.t) (hqj:Even q.j) :
    nI (p.plus q)=nI p+lattice q:= by
  apply Set.Subset.antisymm
  · intro e he
    have hb:e 0+e 1+e 2+e 3≤p.b+q.b:=he.1
    have hj:e 1+2*e 2 + 3*e 3≤p.j+q.j:=he.2.1
    have ht:e 3≤p.t+q.t:=he.2.2
    let z :=min (e 3) p.t
    have hze :z≤e 3:=G1 _ _
    have hzp:z≤p.t:=Gi _ _
    have hzq:e 3 - z≤q.t:= by dsimp [z]; omega
    have hpz :3*z≤p.j:= by have :=hp.2; omega
    have hqz :3*(e 3 - z)≤q.j:= by have :=hq.2; omega
    let A:=p.j-3*z
    let B:=q.j-3*(e 3 - z)
    have heven:Even A∨Even B:= by
      rcases le_total (e 3) p.t with h | h
      · have hz :z=e 3:=min_eq_left h
        exact p6 (by simpa [B,hz] using hqj)
      · have hz :z=p.t:=min_eq_right h
        apply uJ
        obtain ⟨a,ha⟩:=hpj
        obtain ⟨b,hb'⟩:=hpt
        refine ⟨a-3*b,?_⟩
        dsimp [A]
        omega
    obtain ⟨u,hu,v,hv,huvA,huvB⟩ :=
      gun (x :=e 1) (y :=e 2) (A:=A) (B:=B)
        (by dsimp [A,B]; omega) heven
    change u+2*v≤p.j-3*z at huvA
    change (e 1 - u)+2*(e 2 - v)≤q.j-3*(e 3 - z) at huvB
    have hsumP:u+v+z≤p.b:= by have :=hp.1; omega
    have hsumQ: (e 1 - u)+(e 2 - v)+(e 3 - z)≤q.b:= by have :=hq.1; omega
    let x :=min (e 0) (p.b - u - v - z)
    have hxe :x≤e 0:=G1 _ _
    have hxp:x≤p.b - u - v - z :=Gi _ _
    have hxq: (e 0 - x)+(e 1 - u)+(e 2 - v)+(e 3 - z)≤q.b:= by
      dsimp [x]
      omega
    let a :Exponent:=Finsupp.equivFunOnFinite.symm ![x,u,v,z]
    have ha (i:Fin 4) :a i=(![x,u,v,z] :Fin 4→ℕ) i:=rfl
    have haP:a∈nI p:= by
      change a 0+a 1+a 2+a 3≤p.b∧a 1+2*a 2 + 3*a 3≤p.j∧a 3≤p.t
      rw [ha 0,ha 1,ha 2,ha 3]
      change x+u+v+z≤p.b∧u+2*v+3*z≤p.j∧z≤p.t
      omega
    have hae :a≤e := by
      intro i
      fin_cases i <;> rw [ha] <;> assumption
    have haQ:e-a∈nI q:= by
      change (e-a) 0+(e-a) 1+(e-a) 2+(e-a) 3≤q.b ∧
        (e-a) 1+2*(e-a) 2 + 3*(e-a) 3≤q.j∧(e-a) 3≤q.t
      simp only [RP ,ha]
      change (e 0 - x)+(e 1 - u)+(e 2 - v)+(e 3 - z)≤q.b ∧
        (e 1 - u)+2*(e 2 - v)+3*(e 3 - z)≤q.j∧e 3 - z≤q.t
      omega
    exact Set.mem_add.mpr ⟨a,haP,e-a,haQ,add_tsub_cancel_of_le hae⟩
  · rintro e ⟨a,ha,b,hb,rfl⟩
    rw [aON] at ha hb ⊢
    rw [anN hp hq]
    exact Set.mem_add.mpr ⟨_,ha,_,hb,by ext i; simp [SD]⟩
theorem BP {p:c9} (hp:bF p) (n:ℕ) :bF (p.scale n) := by
 refine ⟨p9 n hp.1,?_⟩
 change 3*(n*p.t)≤n*p.j
 simpa only [Nat.mul_left_comm] using p9 n hp.2
theorem cWX {p:c9} (hp:bF p) (hj:Even p.j) (ht:Even p.t)
   (n:ℕ) :nI (p.scale n)=n•nI p:= by
 induction n with
 | zero =>
   simpa [pQ] using b7i
 | succ n ih =>
   have he :Even (p.scale n).j:= by
     change Even (n*p.j)
     exact hj.mul_left n
   have hs :p.scale (n+1)=p.plus (p.scale n) := by
     cases p
     simp [pQ,pU,z7,LQ]
   rw [hs,aOn hp (BP hp n) hj ht he,ih,succ_nsmul']
end UH
end
section
namespace UH
noncomputable section
open aR lB YV MeasureTheory Filter Set
open scoped ENNReal Topology
private def byg (e :zR) :Set M5 :=
 univ.pi fun i=>Ico (e i:ℝ) ((e i:ℝ)+1)
private theorem gGX {e f :zR} (h:e≠f) :
  Disjoint (byg e) (byg f) := by
 apply Set.disjoint_left.mpr
 intro x hx hy
 apply h
 ext i
 have hxe :=hx i (mem_univ i)
 have hxf :=hy i (mem_univ i)
 change (e i:ℝ)≤x i∧x i<(e i:ℝ)+1 at hxe
 change (f i:ℝ)≤x i∧x i<(f i:ℝ)+1 at hxf
 have hef : (e i:ℝ)<(f i:ℝ)+1 :=hxe.1.trans_lt hxf.2
 have hfe : (f i:ℝ)<(e i:ℝ)+1 :=hxf.1.trans_lt hxe.2
 exact le_antisymm (Nat.lt_succ_iff.mp (by exact_mod_cast hef))
  (Nat.lt_succ_iff.mp (by exact_mod_cast hfe))
private def Ax (p:c9) :Set M5 :=
 ⋃ e∈(afS p).toFinset,byg e
private theorem cvk (p:c9) :volume (Ax p)=((nI p).ncard:ℝ≥0∞) := by
 rw [Ax,measure_biUnion_finset
  (fun _ _ _ _ h=>gGX h)
  (fun _ _=>MeasurableSet.univ_pi fun _=>measurableSet_Ico)]
 have hvol (e :zR) :volume (byg e)=1 := by
  unfold byg
  rw [Real.volume_pi_Ico]
  simp
 simp only [hvol,Finset.sum_const,nsmul_one,Set.ncard_eq_toFinset_card _ (afS p)]
private theorem bWp (p:c9) :cap p⊆Ax p:= by
 intro x hx
 obtain ⟨hx,hb,hj,ht⟩:=hx
 let e :Exponent:=Finsupp.equivFunOnFinite.symm (fun i => ⌊x i⌋₊)
 have he (i:Fin 4) :e i = ⌊x i⌋₊ := rfl
 have hlo (i:Fin 4) : (e i:ℝ)≤x i:= by rw [he]; exact Nat.floor_le (hx i)
 have hhi (i:Fin 4) :x i<(e i:ℝ)+1 := by rw [he]; exact Nat.lt_floor_add_one _
 have hm:e∈nI p:= by
   apply aON.mpr
   exact ⟨fun _=>Nat.cast_nonneg _,by linarith [hlo 0,hlo 1,hlo 2,hlo 3],
     by linarith [hlo 1,hlo 2,hlo 3],(hlo 3).trans ht⟩
 exact mem_iUnion₂.mpr ⟨e,(afS p).mem_toFinset.mpr hm,fun i _=>⟨hlo i,hhi i⟩⟩
private def padding:Shape :=⟨6,6,1⟩
private theorem bWE (p:c9) :Ax p⊆cap (p.plus padding) := by
 intro x hx
 obtain ⟨e,he,hxe⟩:=mem_iUnion₂.mp hx
 have he' := aON.mp ((afS p).mem_toFinset.mp he)
 obtain ⟨hn,hb,hj,ht⟩:=he'
 have hlo (i:Fin 4) : (e i:ℝ)≤x i:=(hxe i (mem_univ i)).1
 have hhi (i:Fin 4) :x i<(e i:ℝ)+1 :=(hxe i (mem_univ i)).2
 refine ⟨fun i=>(hn i).trans (hlo i),?_,?_,?_⟩ <;>
  simp only [pU,padding,EP ,Nat.cast_ofNat,Nat.cast_one] <;>
  linarith [hhi 0,hhi 1,hhi 2,hhi 3]
private theorem gLj (p:c9) :volume (cap p) ≠ ∞ := by
 let box :Set M5:=Icc 0 fun _=>(p.b:ℝ)
 have hs :cap p⊆box := by
   intro x hx
   obtain ⟨hx,hb,_,_⟩:=hx
   refine ⟨hx,?_⟩
   intro i
   change x i≤(p.b:ℝ)
   have h0:=hx 0
   have h1 :=hx 1
   have h2 :=hx 2
   have h3:=hx 3
   fin_cases i
   · change x 0≤(p.b:ℝ)
     linarith
   · change x 1≤(p.b:ℝ)
     linarith
   · change x 2≤(p.b:ℝ)
     linarith
   · change x 3≤(p.b:ℝ)
     linarith
 have hfin:volume box ≠ ∞ := by
   change volume (Icc (0:M5) fun _=>(p.b:ℝ)) ≠ ∞
   rw [Real.volume_Icc_pi]
   exact ENNReal.prod_ne_top fun i _=>ENNReal.ofReal_ne_top
 exact (measure_lt_top_of_subset hs hfin).ne
private theorem cWY (p:c9) :
   (volume (cap p)).toReal≤((nI p).ncard:ℝ) ∧
     ((nI p).ncard:ℝ)≤(volume (cap (p.plus padding))).toReal:= by
 have hlo:=measure_mono (μ:=volume) (bWp p)
 have hhi:=measure_mono (μ:=volume) (bWE p)
 rw [cvk] at hlo hhi
 exact ⟨by simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo,
   by simpa using ENNReal.toReal_mono (gLj _) hhi⟩
private def byy (b j t:ℝ) :ℝ :=
 (8*b*j^2*t - 24*b*j*t^2+24*b*t^3-4*j^3*t+14*j^2*t^2 - 20*j*t^3+9*t^4)/32
private theorem djw (p:c9) (hp:bF p) :
  (volume (cap p)).toReal=byy p.b p.j p.t:= by
 have h:=ap7.bWq p hp
 unfold Dn at h
 push_cast at h
 unfold byy
 linarith
private theorem c6Q (R p:c9) (hR:bF R) (hp:bF p) :
   Tendsto (fun n:ℕ=>(volume (cap (R.plus (p.scale n)))).toReal/(n:ℝ)^4)
     atTop (𝓝 (volume (cap p)).toReal) := by
 have hcoord (r s :ℕ) :
     Tendsto (fun n:ℕ=>(s :ℝ)+(r :ℝ)/n) atTop (𝓝 (s :ℝ)) := by
   simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜:=ℝ) (r :ℝ)).const_add (s :ℝ)
 let f :ℝ×ℝ×ℝ→ℝ:= fun y=>byy y.1 y.2.1 y.2.2
 have hc:Continuous f := by unfold f byy; fun_prop
 have h:=hc.continuousAt.tendsto.comp
   ((hcoord R.b p.b).prodMk_nhds ((hcoord R.j p.j).prodMk_nhds (hcoord R.t p.t)))
 rw [djw p hp]
 apply h.congr'
 filter_upwards [Nj (1 :ℕ)] with n hn
 have h0: (n:ℝ)≠0:= by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
 rw [djw _ (Nc hR (BP hp n))]
 simp only [f,zk,pU,pQ,EP ,Ef]
 unfold byy
 field_simp
 ring
theorem euN (R p:c9) (hR:bF R) (hp:bF p) :
   Tendsto (fun n:ℕ=>((nI (R.plus (p.scale n))).ncard:ℝ)/(n:ℝ)^4)
     atTop (𝓝 (volume (cap p)).toReal) := by
 have hpad:bF padding:=⟨by decide,by decide⟩
 have hassoc (n:ℕ) : (R.plus (p.scale n)).plus padding=(R.plus padding).plus (p.scale n) := by
   cases R
   cases p
   simp [pU,pQ,Nat.add_assoc,LQ,Nat.add_left_comm]
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le (c6Q R p hR hp)
   (c6Q (R.plus padding) p (Nc hR hpad) hp)
 · intro n
   exact VO (cWY _).1 (by positivity)
 · intro n
   have hb:=VO (cWY (R.plus (p.scale n))).2
     (by positivity :0≤(n:ℝ)^4)
   simpa only [hassoc] using hb
end
end UH
end
section
namespace akO
noncomputable section
open aR UH MvPolynomial
abbrev Degree :=Fin 4→ℕ
abbrev Qm (k :Type) [oq k] (P:Fin 4→c9) :=
 gQ (fZ k P)
def auxiliary :Shape :=⟨6,6,2⟩
def eG (P:Fin 4→c9) (b:ℕ) (d:Degree) :Shape :=
  (((((auxiliary.scale b).plus ((P 0).scale (d 0))).plus
    ((P 1).scale (d 1))).plus ((P 2).scale (d 2))).plus ((P 3).scale (d 3)))
def shift (d:Degree) (i:Fin 4) (n:ℕ) :Degree :=d+Pi.single i n
def dO (k :Type) [oq k] (P:Fin 4→c9) (b:ℕ) (d:Degree) :
    t3 (fZ k P) (Qm k P) :=
  t5 (fZ k P) (nI (eG P b d))
def mo (k :Type) [oq k] (P:Fin 4→c9) (r :ℕ) :
    lz (Qm k P) :=
  lJ (ve k P '' {i:Fin 4 | i.val< r})
end
end akO
end
section
namespace akO
noncomputable section
open aR lB YV UH MvPolynomial
open scoped Pointwise
private theorem blE :bF auxiliary∧Even auxiliary.j∧Even auxiliary.t :=
 ⟨⟨by decide,by decide⟩,⟨3,rfl⟩,⟨1,rfl⟩⟩
private theorem a8h {p:c9} (hp:bF p∧Even p.j∧Even p.t)
   (n:ℕ) :bF (p.scale n)∧Even (p.scale n).j∧Even (p.scale n).t :=
 ⟨BP hp.1 n,hp.2.1.mul_left n,hp.2.2.mul_left n⟩
private theorem a6B {p q:c9} (hp:bF p∧Even p.j∧Even p.t)
   (hq:bF q∧Even q.j∧Even q.t) :
   bF (p.plus q)∧Even (p.plus q).j∧Even (p.plus q).t :=
 ⟨Nc hp.1 hq.1,hp.2.1.add hq.2.1,hp.2.2.add hq.2.2⟩
private theorem gpX (p q:c9) :p.plus q=q.plus p:= by
 cases p
 cases q
 simp [pU,LQ]
theorem ddE {P:Fin 4→c9}
  (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) (b:ℕ) (d:Degree) :
  bF (eG P b d)∧Even (eG P b d).j∧Even (eG P b d).t :=
 a6B (a6B (a6B (a6B
  (a8h blE b) (a8h (hP 0) (d 0)))
  (a8h (hP 1) (d 1))) (a8h (hP 2) (d 2)))
  (a8h (hP 3) (d 3))
theorem euO {P:Fin 4→c9}
   (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) (b:ℕ) (d:Degree) :
   nI (eG P b d)=((((b•nI auxiliary+d 0•nI (P 0)) +
     d 1•nI (P 1))+d 2•nI (P 2))+d 3•nI (P 3)) := by
 have hA:=a8h blE b
 have hS (i:Fin 4) :=a8h (hP i) (d i)
 have h0:=a6B hA (hS 0)
 have h1 :=a6B h0 (hS 1)
 have h2 :=a6B h1 (hS 2)
 have hadd {p q:c9} (hp:bF p∧Even p.j∧Even p.t)
     (hq:bF q∧Even q.j∧Even q.t) :nI (p.plus q)=nI p+lattice q :=
   aOn hp.1 hq.1 hp.2.1 hp.2.2 hq.2.1
 have hscale (i:Fin 4) :=cWX (hP i).1 (hP i).2.1 (hP i).2.2 (d i)
 unfold eG
 rw [hadd h2 (hS 3),hadd h1 (hS 2),hadd h0 (hS 1),hadd hA (hS 0),
   cWX blE.1 blE.2.1 blE.2.2 b,
   hscale 0,hscale 1,hscale 2,hscale 3]
theorem ddF (P:Fin 4→c9) (b:ℕ) (d:Degree) (i:Fin 4) (n:ℕ) :
  eG P b (shift d i n)=(eG P b d).plus ((P i).scale n) := by
 fin_cases i <;>
  simp [eG,shift,pU,pQ,Un,z7] <;>
  omega
variable {k :Type} [oq k] {P:Fin 4→c9}
instance c32 (b:ℕ) (d:Degree) :p7 (fZ k P) (dO k P b d) :=
 FiniteDimensional.of_finite_basis (basisRestrictSupport _ _) (afS _)
private theorem egc (i:Fin 4) :
  ve k P i∈t5 (fZ k P) (nI (P i)) := by
 classical
 unfold ve
 apply Vz
 intro e _
 exact (monomial_mem_restrictSupport _).mpr (uJ e.property)
theorem bFi (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t)
  (b:ℕ) (d:Degree) (i:Fin 4) {p:Qm k P} (hp:p∈dO k P b d) :
  ve k P i*p∈dO k P b (shift d i 1) := by
 have hd:=ddE hP b d
 have h:=Submodule.mul_mem_mul (egc (k :=k) (P:=P) i) hp
 change ve k P i*p∈t5 _ _ *t5 _ _ at h
 rw [← restrictSupport_add,← aOn (hP i).1 hd.1 (hP i).2.1 (hP i).2.2 hd.2.1] at h
 unfold dO
 rw [ddF,show (P i).scale 1=P i from by cases P i; simp [pQ]]
 rwa [gpX] at h
private theorem b7h {p q:c9} (hb:p.b≤q.b) (hj:p.j≤q.j) (ht:p.t≤q.t) :
 nI p⊆nI q:= fun _ h=>⟨h.1.trans hb,h.2.1.trans hj,h.2.2.trans ht⟩
theorem a6w {b c:ℕ} {d e :Degree} (hbc:b≤ c) (hde :d≤e) :
  dO k P b d≤dO k P c e := by
 unfold dO
 apply restrictSupport_mono
 have h0:=hde 0
 have h1 :=hde 1
 have h2 :=hde 2
 have h3:=hde 3
 apply b7h <;> simp only [eG,pU,pQ] <;> gcongr
theorem btB (p:Qm k P) : ∃ b:ℕ,p∈dO k P b (fun _=>0) := by
 refine ⟨p.totalDegree,?_⟩
 apply (mem_restrictSupport_iff _).mpr
 intro e he
 have hd:=Bf (show e∈p.support from he)
 rw [zE e (fun _ m=>m) (fun _=>rfl),Fin.sum_univ_four] at hd
 simp only [nI,VS ,eG,pU,pQ,auxiliary,
  Nat.zero_mul,Nat.add_zero]
 omega
theorem b3c (b:ℕ) (d:Degree) :
  pL (fZ k P) (dO k P b d)=(nI (eG P b d)).ncard:= by
 rw [dO,Module.finrank_eq_nat_card_basis (basisRestrictSupport _ _),RC]
end
end akO
end
section
set_option maxHeartbeats 800000
namespace akO
noncomputable section
open aR UH MvPolynomial
private theorem b58 {k σ D:Type} [oq k] [qz σ]
   [n5 D] [oj k D] [oj (xW (cy σ k)) D]
   [zf k (xW (cy σ k)) D]
   (f :cy σ k →ₐ[k] D)
   (c:σ→cy σ k)
   (hc : ∀ i,f (c i)=aU (xW (cy σ k)) D
     (aU (cy σ k) (xW (cy σ k)) (mD i)))
   (x :cy σ k) :IsAlgebraic (xW (cy σ k)) (f x) := by
 let B:=cy σ k
 let F:=xW B
 by_contra hx
 have hX:Mz k (fun i:σ=>aU B F (mD i)) :=
   (algebraicIndependent_X σ k).map'
     (f :=Pk k B F) (Ea B F)
 have hx' : Mz F (fun _:Unit=>f x) :=
   algebraicIndependent_unique_type_iff.mpr hx
 have h:=hX.sumElim_comp hx'
 have h' : Mz k (f ∘ Sum.elim (fun _:Unit=>x) c) := by
   convert h using 1
   funext i
   cases i with
   | inl _=>rfl
   | inr i=>exact hc i
 have hle :=(AlgebraicIndependent.of_comp f h').cardinalMk_le_trdeg
 rw [MvPolynomial.trdeg_of_isDomain,Cardinal.lift_id,RD (Unit ⊕ σ),
   RD σ,Fintype.card_sum,Fintype.card_unit] at hle
 have :1+Fintype.card σ≤wY σ:= by exact_mod_cast hle
 omega
theorem b4E (k :Type) [oq k] (P:Fin 4→c9) :
    p7 (fZ k P) (ap1 k P) := by
  classical
  let (i:Fin 4) :qz (nI (P i)) :=(afS (P i)).fintype
  let σ:=Σ i:Fin 4,nI (P i)
  let:qz σ:=inferInstanceAs (qz (Σ i:Fin 4,nI (P i)))
  let B:=xB k P
  let F:=fZ k P
  let J:=Su (ve k P)
  let D:=ap1 k P
  let q:Qm k P →ₐ[F] D:=u9 F J
  let p (i:Fin 4) :nI (P i) :=⟨0,asK _⟩
  let coord (i:Fin 4) :D:=q (mD i)
  let coeff (v :σ) :D:=aU F D (aU B F (mD v))
  let f :B →ₐ[k] D:=sH (fun v :σ=>if v.2.val=0 then coord v.1 else coeff v)
  let S:=f.toRingHom.range
  have hcoord (i:Fin 4) :coord i∈S:= by
    refine ⟨mD ⟨i,p i⟩,?_⟩
    change f (mD ⟨i,p i⟩)=coord i
    dsimp only [f]
    rw [yJ,ite_eq_left (show (p i).val=0 from rfl)]
  have hfree (i:Fin 4) (a :nI (P i)) (ha :a.val≠0) :coeff ⟨i,a⟩∈S:= by
    refine ⟨mD ⟨i,a⟩,?_⟩
    change f (mD ⟨i,a⟩)=coeff ⟨i,a⟩
    dsimp only [f]
    rw [yJ,ite_eq_right ha]
  have hcoeff (v :σ) :coeff v∈S:= by
    rcases v with ⟨i,a⟩
    by_cases ha :a.val=0
    · have hap:a=p i:=qM ha
      subst a
      let term (e :nI (P i)) :D :=
        coeff ⟨i,e⟩*e.val.prod (fun j n=>coord j^n)
      have ht (e :nI (P i)) :
          q (oZ e.val (aU B F (mD ⟨i,e⟩)))=term e := by
        rw [Hw ,ov,← v9,AlgHom.commutes,
          map_finsuppProd]
        simp only [term,coeff,coord,uW]
      have hz :q (ve k P i)=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (qx ⟨i,rfl⟩)
      have hsum:q (ve k P i) = ∑ e :nI (P i),term e := by
        rw [ve,pG]
        exact qm rfl fun e _=>ht e
      rw [hsum,← Ww _ _ (vh (p i)),
        show term (p i)=coeff ⟨i,p i⟩ by simp [term,p]] at hz
      rw [eq_neg_of_add_eq_zero_right hz]
      apply S.neg_mem (S.sum_mem fun e he => ?_)
      have hne :e.val≠0:= fun he0=>(Finset.mem_erase.mp he).1 (qM he0)
      exact S.mul_mem (hfree i e hne)
        (S.prod_mem fun j _=>S.pow_mem (hcoord j) _)
    · exact hfree i a ha
  choose liftCoeff hliftCoeff using hcoeff
  have halg (i:Fin 4) :IsAlgebraic F (coord i) := by
    obtain ⟨x,hx⟩:=hcoord i
    change f x=coord i at hx
    rw [← hx]
    exact b58 f liftCoeff hliftCoeff x
  have hadj:Algebra.adjoin F (oD coord) = ⊤ := by
    rw [show coord=q ∘ mD from rfl,Set.range_comp,Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X,Algebra.map_top,
      (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F J)]
  have h:=Algebra.isAlgebraic_adjoin_iff.mpr (Set.forall_mem_range.mpr halg)
  rw [hadj] at h
  let:Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.isAlgebraic_iff.mpr h)
  exact Algebra.IsIntegral.finite
end
end akO
end
section
namespace akO
noncomputable section
open aR UH
def aCV (F:Degree→ℝ) (i:Fin 4) (n:ℕ) (d:Degree) :ℝ :=
 F (shift d i n)-F d
def aHx (n:ℕ) (F:Degree→ℝ) (is :List (Fin 4)) :Degree→ℝ :=
 is.foldl (fun H i=>aCV H i n) F
private theorem le_shift (d:Degree) (i:Fin 4) (n:ℕ) :d≤ shift d i n :=
 fun _=>vZ _ _
private theorem aQg (d:Degree) (i:Fin 4) (n:ℕ) :
  shift d i (n+1)=shift (shift d i n) i 1 := by
 funext j
 by_cases h:j=i <;> simp [shift,h,Un,add_assoc]
private theorem shift_comm (d:Degree) (i j:Fin 4) (t n:ℕ) :
  shift (shift d j n) i t=shift (shift d i t) j n:= by
 unfold shift
 ac_rfl
private theorem b7R {F G:Degree→ℝ} {q:ℕ} {i:Fin 4}
   (h : ∀ d:Degree,(∀ j,q≤d j)→F (shift d i 1)-F d=G (shift d i 1))
   (n:ℕ) (d:Degree) (hd : ∀ j,q≤d j) :
   aCV F i n d = ∑ t∈pz n,G (shift d i (t+1)) := by
 induction n with
 | zero=>simp [aCV,shift]
 | succ n ih =>
   rw [VC,← ih,aCV,aCV,aQg d i n,
     ← h (shift d i n) (fun j=>(hd j).trans (le_shift d i n j))]
   ring
private theorem dWY {q:ℕ} {i:Fin 4} {U G:Degree→ℝ}
   (n:ℕ) (is :List (Fin 4))
   (h : ∀ d:Degree,(∀ j,q≤d j)→U d = ∑ t∈pz n,G (shift d i (t+1)))
   (d:Degree) (hd : ∀ j,q≤d j) :
   aHx n U is d =
     ∑ t∈pz n,aHx n G is (shift d i (t+1)) := by
 induction is generalizing U G d with
 | nil=>exact h d hd
 | cons j is ih =>
   apply ih (U:=aCV U j n) (G:=aCV G j n) _ d hd
   intro e he
   simp only [aCV,h (shift e j n) (fun l=>(he l).trans (le_shift e j n l)),
     h e he,← Finset.sum_sub_distrib,shift_comm e i j]
private theorem dAm {F G:Degree→ℝ} {q:ℕ} {i:Fin 4}
  (h : ∀ d:Degree,(∀ j,q≤d j)→F (shift d i 1)-F d=G (shift d i 1))
  (n:ℕ) (is :List (Fin 4)) (d:Degree) (hd : ∀ j,q≤d j) :
  aHx n F (i :: is) d =
    ∑ t∈pz n,aHx n G is (shift d i (t+1)) :=
 dWY n is (b7R h n) d hd
theorem b3Q (H :ℕ→Degree→ℝ) (C:ℝ) (q:ℕ)
    (hstep : ∀ (i:Fin 4) (d:Degree),(∀ j,q≤d j) →
      H i.val (shift d i 1) - H i.val d=H (i.val+1) (shift d i 1))
    (htop : ∀ d:Degree,(∀ j,q≤d j)→H 4 d=C)
    (n:ℕ) (d:Degree) (hd : ∀ j,q≤d j) :
    aHx n (H 0) [0,1, 2,3] d=C*(n:ℝ)^4 := by
  let tail:=List.finRange 4
  have htail (i:Fin 4) :tail.drop i.val=i :: tail.drop (i.val+1) := by
    fin_cases i <;> decide
  have hbox (r :ℕ) (hr :r≤4) : ∀ e :Degree,(∀ j,q≤e j) →
      aHx n (H r) (tail.drop r) e=C*(n:ℝ)^(4 - r) := by
    refine Nat.decreasingInduction' (m:=r) (n:=4)
      (P:= fun l => ∀ e :Degree,(∀ j,q≤e j) →
        aHx n (H l) (tail.drop l) e=C*(n:ℝ)^(4-l)) ?_ hr ?_
    · intro l hl _ ih e he
      let i:Fin 4 :=⟨l,hl⟩
      have ht:tail.drop l=i :: tail.drop (l+1) :=htail i
      rw [ht,dAm (hstep i) _ _ _ he]
      calc
        _ = ∑ _t∈pz n,C*(n:ℝ)^(4-(l+1)) :=
          qm rfl fun t _ =>
            ih (shift e i (t+1)) (fun j=>(he j).trans (le_shift e i (t+1) j))
        _ = _:= by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
          rw [show 4-l=(4-(l+1))+1 by omega,wB]
          ring
    · intro e he
      simpa [aHx,tail,show (List.finRange 4).drop 4=[] by decide] using htop e he
  exact hbox 0 (by decide) d hd
theorem gp1 (P:Fin 4→c9) (b n:ℕ) (F:c9→ℝ)
    (d:Degree) (is :List (Fin 4)) :
    aHx n (fun e=>F (eG P b e)) is d =
      is.foldl (fun G i=>aAk G ((P i).scale n)) F (eG P b d) := by
  induction is generalizing F with
  | nil=>rfl
  | cons i is ih =>
    have he :aCV (fun e=>F (eG P b e)) i n =
        fun e=>aAk F ((P i).scale n) (eG P b e) := by
      funext e
      simp only [aCV,ddF,aAk]
    change aHx n (aCV (fun e=>F (eG P b e)) i n) is d= _
    rw [he]
    exact ih _
end
end akO
end
section
namespace akM
noncomputable section
open Polynomial aR dN
abbrev aLR:=cy (Fin 4) lN
def aFg:af 4 →+* aLR :=
 nq (aU ao[X] lN)
abbrev a2V (aI:lz lI) :lz aLR :=
 aI.comap (nq (aU lN lV))
end
end akM
end
section
namespace akM
noncomputable section
open Polynomial MvPolynomial aR Ex dN BO lB
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem arU (w:Fin 4→ℕ) (i:Fin 4) (P:af 4)
  (h:W w P<w i) :vi i P=0:= by
 apply MvPolynomial.ext
 intro m
 rw [coeff_pderiv]
 have hz :P.coeff (m+Finsupp.single i 1)=0:= by
  by_contra hn
  have hm:=le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
  rw [oY ,Au,FQ] at hm
  omega
 simp [hz]
private theorem aQ9 (w:Fin 4→ℕ) (P:af 4) :
  W w (lX P)≤W w P:= by
 classical
 apply aJY
 intro m hm
 obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
 have h:j=m:= by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [zh,ite_eq_right hne])
 exact h ▸ hj
private theorem aa5 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    (P:af 4) {d:ℕ} (hP:W w P≤d) :W w (pK P)≤d+Δ:= by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((aQ9 w P).trans (hP.trans (vZ _ _)))
  · apply Vz
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [vG]
    apply (Po w _ _).trans
    by_cases h:w i.castSucc≤d
    · have hp:=(weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he :=hshift i
      exact (Ml _ _ _).trans
        ((Fz (abx w _) hp).trans (by omega))
    · rw [arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),th,
        weightedTotalDegree_zero]
      exact IU _
private theorem al0 (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
   {g P:af 4} {B d:ℕ} (hΔ:Δ≤B)
   (hg:W w g≤B) (hP:W w P≤d) :
   W w (u6 g P)≤d+2*B:= by
 have hsep (F:af 4) :W w (qG F)≤W w F :=
   weightedTotalDegree_pderiv_le w 3 F
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 apply QL
 · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   have h:=Fz ((hsep g).trans hg) (aa5 w Δ hshift P hP)
   exact (Ml _ _ _).trans (h.trans (by omega))
 · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
   have h:=Fz (aa5 w Δ hshift g hg) ((hsep P).trans hP)
   exact (Ml _ _ _).trans (h.trans (by omega))
private theorem bxy (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
   {g P:af 4} {B d:ℕ} (hΔ:Δ≤B)
   (hg:W w g≤B) (hP:W w P≤d) (n:ℕ) :
   W w (Uy g P n)≤d+(2*n)*B:= by
 induction n with
 | zero=>simpa [Uy] using hP
 | succ n ih =>
   rw [Uy,Function.iterate_succ_apply']
   change W w (u6 g (Uy g P n))≤_
   simpa only [Nat.mul_add,Nat.mul_one,z7,Nat.add_assoc] using
     al0 w Δ hshift hΔ hg ih
theorem bhQ {g P:af 4} {a b:c9} (hb:0<b.t) (hj:0<b.j)
   (hg:aO (p5 g) b) (hP:aO (p5 P) a) (n:ℕ) :
   aO (p5 (Uy g P n)) (a.plus (b.scale (2*n))) := by
 have h₁:W 1 g≤b.b:= by simpa only [p5 ,IT] using hg.1
 have h₂:W C4 g≤b.j:= by simpa only [p5 ,C6] using hg.2.1
 let w:Fin 4→ℕ:=Pi.single 3 1
 have h₃:W w g≤b.t:= by simpa only [w,p5 ,Il] using hg.2.2
 have hp₁:W 1 P≤a.b:= by simpa only [p5 ,IT] using hP.1
 have hp₂:W C4 P≤a.j:= by simpa only [p5 ,C6] using hP.2.1
 have hp₃:W w P≤a.t:= by simpa only [w,p5 ,Il] using hP.2.2
 have hs₁ : ∀ i:Fin 3,(1 :Fin 4→ℕ) i.succ≤(1 :Fin 4→ℕ) i.castSucc+0:= by
   intro i
   change (1 :ℕ)≤1
   exact vl
 have hs₂ : ∀ i:Fin 3,i.succ.val≤ i.castSucc.val+1 := fun _=>vl
 have hs₃ : ∀ i:Fin 3,w i.succ≤w i.castSucc+1 := by
   intro i
   fin_cases i <;> decide
 refine ⟨?_,?_,?_⟩
 · simpa only [p5 ,pU,pQ,IT,Et] using
     bxy 1 0 hs₁ (IU _) h₁ hp₁ n
 · simpa only [p5 ,pU,pQ,C6,Et] using
     bxy C4 1 hs₂ hj h₂ hp₂ n
 · simpa only [w,p5 ,pU,pQ,Il,Et] using
     bxy w 1 hs₃ hb h₃ hp₃ n
theorem a1n (f :af 4) :aO (p5 f) (m6 f) :=
 ⟨le_max_left _ _,vl,vl⟩
theorem bc7 (f :af 4) (r :ℕ) :
  aO (p5 ((qG^[r]) f)) (m6 f) := by
 have d:=a3t f r
 have a :=a1n f
 exact ⟨d.1.trans a.1,d.2.1.trans a.2.1,d.2.2.trans a.2.2⟩
end
end akM
end
section
namespace akM
noncomputable section
open Polynomial K1 aR dN BO
open scoped BigOperators
@[simp] private theorem ajn (P:af 4) (m:Fin 4 →₀ ℕ) :
    (lX P).coeff m=derivative (P.coeff m) := by
  classical
  rw [lX,ze]
  simp only [zh,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,qJ]
private theorem aCH (P Q:af 4) :
  lX (P+Q)=lX P+lX Q:= by
 ext m
 simp
private theorem a2H (P Q:af 4) :
  lX (P*Q)=lX P*Q+P*lX Q:= by
 classical
 apply MvPolynomial.ext
 intro m
 rw [ajn]
 change derivative ((P*Q).coeff m) =
  (lX P*Q).coeff m+(P*lX Q).coeff m
 simp only [ajn,MvPolynomial.coeff_mul,pG,derivative_mul,
  G2]
private theorem btt (P Q:af 4) :
  pK (P+Q)=pK P+pK Q:= by
 simp only [pK,aCH,oY ,mul_add,G2]
 abel
private theorem a6r (P Q:af 4) :
    pK (P*Q)=pK P*Q+P*pK Q:= by
  let a :Fin 3→af 4 := fun i =>
    qU (C ((i.val+1 :ℕ) :ao))*mD i.succ
  change lX (P*Q) +
      (∑ i:Fin 3,a i*vi i.castSucc (P*Q)) =
    pK P*Q+P*pK Q
  have hs : (∑ i:Fin 3,a i*vi i.castSucc (P*Q)) =
      (∑ i:Fin 3,a i*vi i.castSucc P)*Q +
        P*(∑ i:Fin 3,a i*vi i.castSucc Q) := by
    rw [Finset.sum_mul,Nr,← G2]
    apply qm rfl
    intro i _
    rw [FU]
    ring
  rw [a2H,hs]
  change _=(lX P+(∑ i:Fin 3,a i*vi i.castSucc P))*Q +
    P*(lX Q+(∑ i:Fin 3,a i*vi i.castSucc Q))
  ring
private def delta (g:af 4) :af 4 →+ af 4 where
 toFun:=u6 g
 map_add' P Q:= by
  simp only [u6,btt,qG,oY]
  ring
 map_zero' := by
  simp [u6,qG,pK,lX]
private theorem aT8 (g x y :af 4) :
  delta g (x*y)=delta g x*y + x*delta g y := by
 change u6 g (x*y)=u6 g x*y + x*u6 g y
 simp only [u6,a6r,qG,FU]
 ring
section Iterates
variable {R S:Type*} [n5 R] [n5 S]
variable (D:R →+ R) (ρ:R →+* S)
variable (hD : ∀ x y,D (x*y)=D x*y + x*D y)
private theorem iterate_map_add (n:ℕ) (x y :R) :
   (D^[n]) (x+y)=(D^[n]) x+(D^[n]) y := by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [Function.iterate_succ_apply',ih,map_add]
include hD
private theorem cVI (n:ℕ) (x y :R)
   (hy : ∀ k<n,ρ ((D^[k]) y)=0) :
   ρ ((D^[n]) (x*y))=ρ x*ρ ((D^[n]) y) := by
 induction n generalizing x y with
 | zero=>exact map_mul ρ _ _
 | succ n ih =>
   rw [Av _ _ (x*y),hD,iterate_map_add D,oY]
   rw [ih (D x) y (fun k hk=>hy k (Nat.lt_succ_of_lt hk)),hy n (Nat.lt_succ_self n),th,wA]
   have hy' : ∀ k<n,ρ ((D^[k]) (D y))=0:= by
     intro k hk
     exact hy (k+1) (Nat.succ_lt_succ hk)
   simpa only [Av] using ih x (D y) hy'
private theorem derivative_pow_succ (t:R) (n:ℕ) :
   D (t^(n+1))=((n+1 :ℕ) :R)*D t*t^n:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [wB t (n+1),hD,ih,wB t n]
   push_cast
   ring
private theorem epp (t:R) (ht:ρ t=0) (n:ℕ) :
    (∀ k<n,∀ a :R,ρ ((D^[k]) (a*t^n))=0) ∧
    ∀ a :R,ρ ((D^[n]) (a*t^n))=ρ a*(n.factorial:S)*(ρ (D t))^n:= by
  induction n with
  | zero=>simp
  | succ n ih =>
    have hstep (a :R) :
        D (a*t^(n+1)) =
          (D a*t+a*((n+1 :ℕ) :R)*D t)*t^n:= by
      rw [hD,derivative_pow_succ D hD,vk t n]
      ring
    constructor
    · intro k hk a
      cases k with
      | zero=>simp [map_mul,ht]
      | succ k =>
        rw [Av,hstep]
        exact ih.1 k (Nat.lt_of_succ_lt_succ hk) _
    · intro a
      rw [Av,hstep,ih.2]
      simp only [oY ,ov,ht,th,wA,JW,Nat.factorial_succ,
        Ef ,wB]
      ring
end Iterates
end
end akM
end
section
namespace aY1
noncomputable section
open IsLocalRing
abbrev Be {R:Type*} [n5 R] (q:lz R) [q.IsPrime] (J:lz R) :ℕ∞ :=
 pC (oy q)
  (oy q ⧸ J.map (aU R (oy q)))
section Length
variable {R S:Type*} [n5 R] [n5 S] [oj R S]
 (Q:lz S) [Q.IsPrime]
theorem exy {J:lz S} (hJ:J≤Q) :0<Be Q J:= by
 apply Module.length_pos_iff.mpr
 apply Ideal.Quotient.nontrivial_iff.mpr
 exact Vq (PM _).ne_top
  ((yQ hJ).trans_eq yo)
theorem bIB {J:lz S} :
   Be Q J=1 ↔
     J.map (aU S (oy Q))=oK (oy Q) := by
 rw [Be,Module.length_eq_one_iff,isSimpleModule_iff_isCoatom,← Ideal.isMaximal_def,
   IsLocalRing.isMaximal_iff]
theorem cYu {I J:lz S} (h:I≤J) :
  Be Q J≤Be Q I:= by
 simp only [Be,Kp]
 exact Sv (yQ h)
theorem b74 [u5 R S] (J:lz R) :
    Be Q (J.map (aU R S)) =
      Be (Q.comap (aU R S)) J *
        Be Q ((Q.comap (aU R S)).map (aU R S)) := by
  let q:= Q.comap (aU R S)
  let:q.IsPrime :=xu _ _
  let:Q.LiesOver q:=⟨rfl⟩
  let A:=oy q
  let B:=oy Q
  let:oj A B:=Nq q Q
  have :Cy (aU A B) := by
    change Cy (Wl q Q (aU R S) rfl)
    infer_instance
  have hmap (I:lz R) :
      (I.map (aU R A)).map (aU A B) =
        (I.map (aU R S)).map (aU S B) := by
    rw [t4 ,t4 ,← t6 R A B,
      ← t6 R S B]
  let I:=J.map (aU R A)
  change pC B (B ⧸ (J.map (aU R S)).map (aU S B)) =
    pC A (A ⧸ I) *
      pC B (B ⧸ (q.map (aU R S)).map (aU S B))
  rw [← hmap,← hmap,yo]
  exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq).trans
    (IsLocalRing.length_baseChange A B (A ⧸ I))
end Length
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem ccg {k l σ:Type*} [oq k] [oq l] [oj k l] :
  u5 (cy σ k) (cy σ l) := by
 have h:Algebra.IsPushout k (cy σ k) l (cy σ l) :=vj
 exact Module.Flat.isBaseChange k (cy σ k) l (cy σ l) h.out
theorem exx {R S:Type*} [n5 R] [n5 S] [oj R S]
  [u5 R S] (Q:lz S) [Q.IsPrime] (J:lz R) :
  Be (Q.comap (aU R S)) J≤Be Q (J.map (aU R S)) := by
 rw [b74]
 exact ENat.self_le_mul_right _ (exy Q (Ideal.map_le_iff_le_comap.mpr vl)).ne'
end
end aY1
end
section
namespace aY1
noncomputable section
open IsLocalRing Algebra
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
section FiniteScalarExtension
variable {k l σ:Type*} [oq k] [oq l] [oj k l] [x7 k l]
variable (Q:lz (cy σ l)) [Q.IsPrime]
theorem gpB [Algebra.IsSeparable k l] :
   Be Q ((Q.comap (aU (cy σ k) _)).map
     (aU (cy σ k) _))=1 := by
 let R:=cy σ k
 let S:=cy σ l
 let q:= Q.comap (aU R S)
 let:q.IsPrime :=xu _ _
 let:Q.LiesOver q:=⟨rfl⟩
 let A:=oy q
 let B:=oy Q
 let:oj A B:=Nq q Q
 let:Cy (aU A B) := by
   change Cy (Wl q Q (aU R S) rfl)
   infer_instance
 let e :=IsPushout.equiv k R l S
 have :p7 R S:=Module.Finite.of_surjective e.toLinearMap e.surjective
 have :Ar k l:=FormallyUnramified.of_isSeparable k l
 have :Ar R S:=FormallyUnramified.of_equiv e
 have :Ar R B:= by
   change Ar R (Localization Q.primeCompl)
   infer_instance
 have :Ar A B:=FormallyUnramified.of_restrictScalars R A B
 have :xm R B:= by
   change xm R (Localization Q.primeCompl)
   infer_instance
 have :xm A B:=EssFiniteType.of_comp R A B
 apply (bIB Q).mpr
 change (q.map (aU R S)).map (aU S B)=oK B
 rw [t4 ,← t6 R S B,
   t6 R A B,← t4 ,
   yo]
 exact FormallyUnramified.map_maximalIdeal
end FiniteScalarExtension
private theorem ddt {R S:Type*} [n5 R] [n5 S] (e :R ≃+* S) :
  pC R R=pC S S:= by
 rw [N0 ,N0]
 change zd (⊥ : lz R)=zd (⊥ : lz S)
 simpa using Order.coheight_orderIso e.idealComapOrderIso (⊥ : lz S)
section PurelyInseparable
variable {k l F:Type*} [oq k] [oq l] [oq F] [oj k l] [oj k F]
variable [PD k l]
private theorem gA0 [x7 k l]
   (p:ℕ) [zc k p] (hp:p.Prime)
   (h:pC (F ⊗[k] l) (F ⊗[k] l)<(p:ℕ∞)) :
   pC (F ⊗[k] l) (F ⊗[k] l)=1 := by
 let T:=F ⊗[k] l
 have :Kc (PrimeSpectrum T) :=
   (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k l F).injective.subsingleton
 have :Kc (MaximalSpectrum T) :=MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
 have :MO T:=IsLocalRing.of_singleton_maximalSpectrum
 have :Cy (aU F T) :=⟨fun x hx ↦ isUnit_iff_ne_zero.mpr fun hz ↦
   by simp [hz] at hx⟩
 obtain ⟨a,ha⟩:=IsPurelyInseparable.finrank_eq_pow k l p
 have hd:=IsLocalRing.length_restrictScalars F T T
 rw [Module.length_eq_finrank F T,SU,ha] at hd
 have hdvd: (pC T T).toNat∣p^a := by
   refine ⟨(pC (Df F) (Df T)).toNat,?_⟩
   simpa only [ENat.toNat_mul,ENat.toNat_natCast] using oz ENat.toNat hd
 obtain ⟨n,-,hn⟩:=(Nat.dvd_prime_pow hp).mp hdvd
 cases n with
 | zero=>exact (ENat.toNat_eq_iff (by decide : (1 :ℕ)≠0)).mp (by simpa using hn)
 | succ n =>
   have hle :p≤p^(n+1) :=Nat.le_pow (Np n)
   have hlt: (pC T T).toNat<p:= by
     exact ENat.natCast_lt_natCast.mp ((ENat.natCast_toNat_le_self _).trans_lt h)
   omega
end PurelyInseparable
section PolynomialFibre
variable {k l σ:Type*} [oq k] [oq l] [oj k l]
variable [PD k l]
variable (q:lz (cy σ k)) [q.IsPrime]
variable (Q:lz (cy σ l)) [Q.IsPrime] [Q.LiesOver q]
private abbrev b2Z {R S:Type*} [n5 R] [n5 S] [oj R S]
   (q:lz R) [q.IsPrime] :S →+* q.Fiber S :=
 (Algebra.TensorProduct.includeRight (R:=R) (A:=q.ResidueField) (B:=S)).toRingHom
set_option backward.isDefEq.respectTransparency false in
private theorem eaa {R S:Type*} [n5 R] [n5 S] [oj R S]
   (q:lz R) [q.IsPrime] (r :lz (q.Fiber S)) [r.IsPrime] :
   Be (r.comap (b2Z (S:=S) q)) (q.map (aU R S)) =
     pC (oy r) (oy r) := by
 let Q:=r.comap (b2Z (S:=S) q)
 have :Q.IsPrime :=xu _ _
 let B:=oy Q
 let I:=(q.map (aU R S)).map (aU S B)
 change pC B (B ⧸ I)= _
 have hsurj:t8 (aU B (B ⧸ I)) :=
   y5
 have hquot:=Module.length_eq_of_surjective (S:=B) (R:=B ⧸ I) (M:=B ⧸ I) hsurj
 let e :oy r ≃+* (B ⧸ I) :=
   (Ideal.Fiber.algEquivAux₂ (S:=S) q r).toRingEquiv
 have he :=ddt (R:=B ⧸ I) (S:=oy r) e.symm
 exact hquot.trans he
set_option backward.isDefEq.respectTransparency false in
private theorem ePJ :
    Be Q (q.map (aU (cy σ k) (cy σ l))) =
      pC (q.ResidueField ⊗[k] l) (q.ResidueField ⊗[k] l) := by
  let R:=cy σ k
  let S:=cy σ l
  let F:=q.ResidueField
  let T:=F ⊗[k] l
  let e₁:q.Fiber S ≃ₐ[F] T :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl:F ≃ₐ[F] F)
      ((IsPushout.equiv k R l S).symm)).trans
        (Algebra.TensorProduct.cancelBaseChange k R F F l)
  obtain ⟨z,hz⟩:=(PrimeSpectrum.primesOverOrderIsoFiber R S q).symm.surjective
    ⟨Q,vj,vj⟩
  let r :=z.asIdeal
  have :r.IsPrime :=z.isPrime
  have hQ:r.comap (b2Z (S:=S) q)= Q :=
    oz (fun w:q.primesOver S ↦ w.1) hz
  have hu:r.primeCompl≤IsUnit.submonoid (q.Fiber S) := by
    intro x hx
    obtain ⟨n,hn,y,hy⟩:=IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e₁ x)
    have hxy :x^n=aU F (q.Fiber S) y := by
      apply e₁.injective
      rw [uW,e₁.commutes,hy]
    have hy0:y≠0:= by
      intro hz
      apply hx
      exact (‹r.IsPrime›.pow_mem_iff_mem _ hn).mp (by simp [hxy,hz])
    change IsUnit x
    rw [← isUnit_pow_iff hn.ne',hxy]
    exact (isUnit_iff_ne_zero.mpr hy0).map (aU F (q.Fiber S))
  let e₂:=IsLocalization.atUnits (q.Fiber S) r.primeCompl (S:=oy r) hu
  subst Q
  have h₁:=eaa (R:=R) (S:=S) q r
  let e :oy r ≃+* T:=e₂.symm.toRingEquiv.trans e₁.toRingEquiv
  have h₂:=ddt (R:=oy r) (S:=T) e
  exact h₁.trans h₂
theorem ePI [x7 k l] (p:ℕ) [zc k p] (hp:p.Prime)
  (h:Be Q (q.map (aU (cy σ k) _))<(p:ℕ∞)) :
  Be Q (q.map (aU (cy σ k) _))=1 := by
 rw [ePJ q Q] at h ⊢
 exact gA0 p hp h
end PolynomialFibre
end
end aY1
end
section
namespace aY1
noncomputable section
open IsLocalRing
open aR dN akM
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem c4R {k E l σ:Type*} [oq k] [oq E] [oq l]
  [oj k E] [oj k l] [oj E l] [zf k E l] :
  zf (cy σ k) (cy σ E) (cy σ l) := by
 apply IsScalarTower.of_algebraMap_eq'
 apply RingHom.ext
 intro x
 simp only [Dv]
 change nq (aU k l) x =
  nq (aU E l) (nq (aU k E) x)
 rw [zm,t6 k E l]
private theorem eaQ {k l σ:Type*} [oq k] [oq l] [oj k l]
   [x7 k l] (Q:lz (cy σ l)) [Q.IsPrime]
   (p:ℕ) [zc k p] (hp:p.Prime)
   (h:Be Q ((Q.comap (aU (cy σ k) _)).map
     (aU (cy σ k) _))<(p:ℕ∞)) :
   Be Q ((Q.comap (aU (cy σ k) _)).map
     (aU (cy σ k) _))=1 := by
 let E :=separableClosure k l
 let R:=cy σ k
 let T:=cy σ E
 let S:=cy σ l
 let q:= Q.comap (aU T S)
 have :q.IsPrime :=xu _ _
 have :Q.LiesOver q:=⟨rfl⟩
 have :u5 T S:=ccg
 have :zf R T S:=c4R
 have hmap : ((q.comap (aU R T)).map (aU R T)).map (aU T S) =
     (Q.comap (aU R S)).map (aU R S) := by
   simp only [q,t4 ,TZ,← t6 R T S]
 rw [← hmap,b74,gpB (k :=k) q,one_mul] at h ⊢
 exact ePI q Q p hp h
private theorem ewh {k l σ:Type*} [oq k] [oq l] [oj k l]
   [UZ k l] (x :cy σ l) :
   ∃ (E :IntermediateField k l),x7 k E ∧
     ∃ y :cy σ E,aU (cy σ E) (cy σ l) y=x := by
 classical
 let s :=x.support.image x.coeff
 let E :=IntermediateField.adjoin k (s :Set l)
 have :x7 k E :=IntermediateField.finiteDimensional_adjoin
   (fun z _ ↦ Algebra.IsIntegral.isIntegral (R:=k) z)
 have hcoeff (m:σ →₀ ℕ) (hm:m∈x.support) :x.coeff m∈E :=
   IntermediateField.subset_adjoin k _ (Finset.mem_image.mpr ⟨m,hm,rfl⟩)
 let y :cy σ E :=
   ∑ m∈x.support.attach,oZ m.1 ⟨x.coeff m.1,hcoeff m.1 m.2⟩
 refine ⟨E,vj,y,?_⟩
 simp only [y,pG,Dv,MvPolynomial.map_monomial,
   IntermediateField.algebraMap_apply]
 rw [Finset.sum_attach x.support (fun m ↦ oZ m (x.coeff m))]
 exact (Mk x).symm
theorem cA7 {k l σ:Type*} [oq k] [oq l] [oj k l]
   [UZ k l] (Q:lz (cy σ l)) [Q.IsPrime]
   (p:ℕ) [zc k p] (hp:p.Prime)
   (h:Be Q ((Q.comap (aU (cy σ k) _)).map
     (aU (cy σ k) _))<(p:ℕ∞)) :
   Be Q ((Q.comap (aU (cy σ k) _)).map
     (aU (cy σ k) _))=1 := by
 let R:=cy σ k
 let S:=cy σ l
 let J:=(Q.comap (aU R S)).map (aU R S)
 let B:=oy Q
 apply (bIB Q).mpr
 rw [← yo]
 change J.map (aU S B)= Q.map (aU S B)
 refine GB (yQ Ideal.map_comap_le) ?_
 rw [Vs]
 intro x hx
 obtain ⟨E,hE,y,hy⟩:=ewh (k :=k) x
 let T:=cy σ E
 let q:= Q.comap (aU T S)
 let J₀:=(q.comap (aU R T)).map (aU R T)
 let A:=oy q
 have :q.IsPrime :=xu _ _
 have :Q.LiesOver q:=⟨rfl⟩
 let:oj A B:=Nq q Q
 have :zf R T S:=c4R
 have :u5 T S:=ccg
 have hmap :J₀.map (aU T S)=J:= by
   simp only [J₀,J,q,t4 ,TZ,← t6 R T S]
 have h₀:Be q J₀<(p:ℕ∞) :=(exx Q J₀).trans_lt (hmap ▸ h)
 have h₁:=(bIB q).mp (eaQ (k :=k) q p hp h₀)
 have hyq:y∈q:= by
   change aU T S y∈Q
   exact hy.symm ▸ hx
 have hymem:aU T A y∈J₀.map (aU T A) := by
   rw [h₁,← yo]
   exact Iw _ hyq
 have hmem:=Iw (aU A B) hymem
 rw [t4 ,← t6 T A B,
   t6 T S B,← t4 ,hmap] at hmem
 change aU S B x∈J.map (aU S B)
 rw [← hy]
 change (aU S B) ((aU T S) y)∈J.map (aU S B)
 rw [← FR T S B]
 rwa [← FR T A B] at hmem
end
end aY1
end
section
namespace bzx
noncomputable section
open aR dN akM IsLocalRing
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem gBN (a :af 4) :
  nq (aU lN lV) (aFg a)=bC a := by
 rw [aFg,bC,j8,zm]
section Chart
variable (aI:lz lI) [aI.IsPrime]
private abbrev A:=oy (a2V aI)
private abbrev agn:=(a2V aI).comap (aU (af 4) aLR)
local instance :IsLocalization.AtPrime (A aI) (agn aI) :=
 IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
  ((C5 (sI ao)).map (qU (σ:=Fin 4))) (A aI)
  (a2V aI)
private abbrev loc:=aU (af 4) (A aI)
private theorem exo (a :af 4) :
 loc aI a=aU aLR (A aI) (aFg a) :=rfl
omit [aI.IsPrime] in
private theorem source_mem (a :af 4) :a∈agn aI↔bC a∈aI:= by
 change (nq (aU lN lV) (aFg a)∈aI)↔_
 rw [gBN]
private theorem bCF {J:lz (af 4)} {a :af 4} (ha :loc aI a∈J.map (loc aI)) :
  ∃ d:af 4,bC d∉aI∧d*a∈J:= by
 obtain ⟨d,hd,hda⟩:=(KA
  (agn aI).primeCompl (A aI) J a).mp ha
 exact ⟨d,(not_congr (source_mem aI d)).mp hd,hda⟩
end Chart
end
end bzx
end
section
namespace bzE
noncomputable section
open aR dN rW aFT aY1
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem proof :aFT.c1 := by
 intro f Q P hz hlen
 have :P.IsPrime :=hz.isPrime
 change Be P (kC f Q)<(K1.p:ℕ∞) at hlen
 let J:lz PJ:=lJ {Q0 f,Q0 Q}
 have hJ:J.map Ow=kC f Q:= by
   simp only [J,kC,sS ,vH,uh,
     aQd]
 let const:K1.K →+* ale :=
   (aU lN ale).comp
     ((aU (sI ao) lN).comp (Polynomial.C.comp embed))
 have :CharP ale K1.p:=G3 const.injective K1.p
 have hp:=SM K1.K K1.p (by decide)
 have :zc ale K1.p := .prime hp
 have hle :kC f Q≤(P.comap Ow).map Ow:= by
   rw [← hJ]
   exact yQ (Ideal.map_le_iff_le_comap.mp (hJ.symm ▸ hz.le))
 have hsmall:Be P ((P.comap Ow).map Ow)<(K1.p:ℕ∞) :=
   (cYu P hle).trans_lt hlen
 have hone :Be P ((P.comap Ow).map Ow)=1 :=
   cA7 (k :=ale) P K1.p hp hsmall
 exact dWB (k :=ale) (E :=lV) (R:=PJ) P
   ((bIB P).mp hone)
end
end bzE
end
section
namespace aKp
noncomputable section
open Polynomial K1 aR dN BO lB
open scoped BigOperators
def rV (S:ao[X]) :KE := fun i=>j8 (jet S i)
theorem cZO:t9 rV:= by
 intro S T h
 have hzero :=yB h (0:Fin 4)
 simpa only [rV,jet,Fin.val_zero,hasseDeriv_zero',SZ.eq_iff]
  using hzero
theorem bDo {C:lz lI} (hp:C.IsPrime)
    (hdim:u8 (lI ⧸ C)=1) :
    ∃ (x :KE) (D:lI),C≤t7 (ox x) ∧
      yy D ⟨1,3,1⟩∧D∉C∧ox x D =0:= by
  classical
  obtain ⟨J,hJ,hCJ⟩:=Ideal.exists_le_maximal C hp.ne_top
  obtain ⟨x,hx⟩:=MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal lV hJ
  have hon :C≤t7 (ox x) := by
    intro P hP
    have h:=hCJ hP
    rw [hx,MvPolynomial.mem_vanishingIdeal_singleton_iff,MvPolynomial.aeval_eq_eval] at h
    exact h
  have hcut : ∃ i:Fin 4,mD i-MvPolynomial.C (x i)∉C:= by
    by_contra! hall
    let q:=nX C
    have hq:q=q.comp (MvPolynomial.C.comp (ox x)) := by
      apply wR
      · intro c
        simp
      · intro i
        simp only [yl,MvPolynomial.eval_X]
        exact sub_eq_zero.mp (by
          rw [← Du]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
    have hsurj:t8 (q.comp qU) := by
      intro b
      obtain ⟨P,rfl⟩:=y5 b
      exact ⟨ox x P,(xI hq P).symm⟩
    have hle :=ringKrullDim_le_of_surjective _ hsurj
    rw [hdim,ringKrullDim_eq_zero_of_field] at hle
    exact (by decide : ¬ (1 :WithBot ℕ∞)≤0) hle
  obtain ⟨i,hi⟩:=hcut
  let D:GeoJets :=mD i-MvPolynomial.C (x i)
  refine ⟨x,D,hon,⟨?_,?_,?_⟩,hi,by simp [D]⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · apply MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply QL
    · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ (Nat.le_of_lt_succ i.isLt)
    · exact MvPolynomial.C_mem_restrictWeightedDegree _ _ _
  · apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X,MvPolynomial.degreeOf_C,max_zero]
    split <;> decide
end
end aKp
end
section
namespace aKp
noncomputable section
open Polynomial K1 aR dN BO wH lB
def c2 :Prop :=
  ∀ (C:lz lI) (p:c9),C.IsPrime→ u8 (lI ⧸ C)=1 →
    aO ⟨1,3,1⟩ p →
    ∀ (D:lI),yy D p→D∉C →
      ∀ points :qy KE,
        (∀ x∈points,C≤t7 (ox x)∧ox x D =0) →
        6*points.card≤pN C (p.scale 6)
end
end aKp
end
section
namespace as4
open aR dN BO
abbrev akH (C:lz lI) (E :lI) :=
 lI ⧸ (C ⊔ lJ {E})
abbrev HG (C:lz lI) (a :c9) :=
 adi a ⧸
  (C.map (nq (aU lV (dV a))) ⊔
    lJ {adK a})
noncomputable def alw (a :c9) (c:uL a→lV) :GeoJets :=
 ∑ m∈Bz a,qU (c m) * ∏ i:Fin 4,mD i^(m i).val
end as4
end
section
namespace as4
open aR dN BO lB MvPolynomial
theorem ecE {D:lI} {p:c9} (hD:yy D p) (n:ℕ) :
   yy (D^n) (p.scale n) :=
 ⟨(totalDegree_pow D n).trans (p9 n hD.1),
   (weightedTotalDegree_pow_le _ D n).trans (p9 n hD.2.1),
   (degreeOf_pow_le _ D n).trans (p9 n hD.2.2)⟩
private noncomputable def exponent (a :c9) :uL a ↪ (Fin 4 →₀ ℕ) where
 toFun m:=Finsupp.equivFunOnFinite.symm fun i=>(m i).val
 inj' := by
  intro x y h
  funext i
  apply Fin.ext
  exact MK h i
theorem d33 {E :lI} {a :c9} (hE :yy E a) :
    ∃ c:uL a→lV,alw a c=E := by
  classical
  refine ⟨fun m=>E.coeff (exponent a m),?_⟩
  have hexp (m:uL a) (i:Fin 4) :exponent a m i=(m i).val :=rfl
  have hsupport :E.support⊆(Bz a).map (exponent a) := by
    intro s hs
    have hb: (∑ i:Fin 4,s i)≤a.b:= by
      simpa [zE] using (Bf hs).trans hE.1
    have hj: (∑ i:Fin 4,i.val*s i)≤a.j:= by
      simpa [JK,zE,nsmul_eq_mul,Et] using
        (le_weightedTotalDegree C4 hs).trans hE.2.1
    have ht:s 3≤a.t:=(monomial_le_degreeOf 3 hs).trans hE.2.2
    let m:uL a := fun i =>
      ⟨s i,Pc ((Finset.single_le_sum
        (f := fun j:Fin 4=>s j) (fun j _=>IU (s j)) (vh i)).trans hb)⟩
    refine Finset.mem_map.mpr ⟨m,?_,Finsupp.ext fun _=>rfl⟩
    exact Finset.mem_filter.mpr ⟨vh m,hb,hj,ht⟩
  have hsum:=Finset.sum_subset (f := fun s=>oZ s (E.coeff s)) hsupport (by
    intro s _ hs
    rw [notMem_support_iff.mp hs,qJ])
  rw [Finset.sum_map] at hsum
  calc
    alw a (fun m=>E.coeff (exponent a m)) =
        ∑ m∈Bz a,oZ (exponent a m) (E.coeff (exponent a m)) := by
      unfold alw
      apply qm rfl
      intro m _
      rw [Hw ,Ok _ _ (fun _=>FV _)]
      simp only [hexp]
    _=E :=hsum.symm.trans E.as_sum.symm
theorem bZr {C:lz lI} [C.IsPrime]
   (hdim:u8 (lI ⧸ C)=1) {E :lI} (hE :E∉C) :
   p7 lV (akH C E) := by
 have hlt:C<C ⊔ lJ {E} := by
   apply Kz Gk
   intro h
   exact hE (h ▸ G5 (EK E) :
     E∈C)
 have hd:=Ideal.ringKrullDim_quotient_succ_le_of_lt hlt
 rw [hdim] at hd
 apply (Module.finite_iff_krullDimLE_zero lV _).mpr
 apply Ring.krullDimLE_iff.mpr
 exact ENat.WithBot.add_le_add_one_right_iff.mp (by simpa using hd)
theorem c43 {C:lz lI} [C.IsPrime] {D:lI} (hD:D∉C) (n:ℕ) :
  D^n∉C:= by
 rw [← NX ,uW]
 exact pow_ne_zero n (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
private theorem eNu {C:lz lI} [C.IsPrime] {D:lI} (hD:D∉C)
    (n:ℕ) : (C ⊔ lJ {D^(n+1)}).colon {D} = C ⊔ lJ {D^n} := by
  ext x
  let q:=nX C
  have hqD:q D ≠0:=mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  rw [Submodule.mem_colon_singleton,smul_eq_mul]
  constructor
  · intro hx
    obtain ⟨c,hc,y,hy,hsum⟩:=Submodule.mem_sup.mp hx
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hy
    have heq :q D *q x=q D *(q (D^n)*q r) := by
      have h:=oz q hsum
      rw [oY ,Ideal.Quotient.eq_zero_iff_mem.mpr hc,wA,wB,
        ov,ov,ov] at h
      linear_combination -h
    have hdiff :x - D^n*r∈C:= by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [Du,ov,mul_left_cancel₀ hqD heq,sub_self]
    apply Submodule.mem_sup.mpr
    refine ⟨x - D^n*r,hdiff,D^n*r,Ideal.mem_span_singleton.mpr ⟨r,rfl⟩,?_⟩
    exact sub_add_cancel _ _
  · intro hx
    obtain ⟨c,hc,y,hy,rfl⟩:=Submodule.mem_sup.mp hx
    obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hy
    rw [add_mul]
    apply Ideal.add_mem _ (Qx (Ideal.mul_mem_right D C hc))
    apply G5
    exact Ideal.mem_span_singleton.mpr ⟨r,by rw [wB]; ac_rfl⟩
private theorem gxs {C:lz lI} (D:lI) (n:ℕ) :
   (C ⊔ lJ {D^(n+1)}) ⊔ lJ {D} = C ⊔ lJ {D} := by
 have hpow: (lJ {D^(n+1)} : lz lI)≤lJ {D} :=
   (Dz _).mpr
     (Ideal.mem_span_singleton.mpr ⟨D^n,by rw [wB,FK]⟩)
 rw [sup_assoc,sup_eq_right.mpr hpow]
set_option maxHeartbeats 800000 in
theorem ebh {C:lz lI} [C.IsPrime] {D:lI}
   (hdim:u8 (lI ⧸ C)=1) (hD:D∉C) (n:ℕ) :
   pL lV (akH C (D^n)) =
     n*pL lV (akH C D) := by
 induction n with
 | zero =>
   let:Kc (akH C (D^0)) :=
     Ideal.Quotient.subsingleton_iff.mpr (by rw [FV,Ideal.span_singleton_one,sup_top_eq])
   simpa only [Nat.zero_mul] using
     (Module.finrank_zero_of_subsingleton :pL lV (akH C (D^0))=0)
 | succ n ih =>
   let I:lz GeoJets :=C ⊔ lJ {D^(n+1)}
   let J:=I ⊔ lJ {D}
   let:p7 lV (lI ⧸ I) :=bZr hdim (c43 hD _)
   let q:=(Eg (Gk :I≤J)).restrictScalars lV
   let m:=(WI.Vp I D).restrictScalars lV
   have hex :Function.Exact m q:=WI.a7c I D
   have he :=(LinearMap.exact_iff.mp hex).symm
   have hr :=q.finrank_range_add_finrank_ker
   have hq:t8 q:=Gr (Gk :I≤J)
   have hm:t9 m:=WI.aPy I D
   rw [LinearMap.range_eq_top.mpr hq,finrank_top,← he,
     ← (Vl m hm).finrank_eq] at hr
   change pL lV (lI ⧸ ((C ⊔ lJ {D^(n+1)}) ⊔ lJ {D})) +
     pL lV (lI ⧸ (C ⊔ lJ {D^(n+1)}).colon {D}) =
     pL lV (akH C (D^(n+1))) at hr
   rw [gxs,eNu hD] at hr
   change pL lV (akH C D) +
     pL lV (akH C (D^n))= _ at hr
   rw [ih,yL,← Nat.succ_mul] at hr
   exact hr.symm
theorem dFv {C:lz lI} {D:lI}
   [p7 lV (akH C D)] (points :qy KE)
   (hp : ∀ x∈points,C≤t7 (ox x)∧ox x D =0) :
   points.card≤pL lV (akH C D) := by
 let I:lz GeoJets :=C ⊔ lJ {D}
 have hz : (points :Set KE)⊆zeroLocus lV I:= by
   intro x hx
   have hx' := hp x hx
   have hI:I≤t7 (ox x) :=
     sup_le hx'.1 ((Dz _).mpr hx'.2)
   intro E hE
   change ox x E=0
   exact hI hE
 have hf : (zeroLocus lV I).Finite :=finite_zeroLocus_of_finite_quotient I
 have hcard:=Set.ncard_le_ncard hz hf
 rw [Set.ncard_coe_finset] at hcard
 exact hcard.trans (ncard_zeroLocus_le_finrank_quotient I)
end as4
end
section
namespace as4
open aR dN BO lB
def c1 :Prop :=
  ∀ (C:lz lI) (a :c9),C.IsPrime→ u8 (lI ⧸ C)=1 →
    p7 (dV a) (HG C a)
def c2 :Prop :=
  ∀ (C:lz lI) (a :c9),C.IsPrime→ u8 (lI ⧸ C)=1 →
    p7 (dV a) (HG C a) →
    ∀ c:uL a→lV,alw a c∉C →
      p7 lV (akH C (alw a c)) →
      pL lV (akH C (alw a c))≤pN C a
theorem of_children (h₁:c1) (h₂:c2) :aKp.c2 := by
 intro C p hC hdim _ D hD hproper points hpoints
 let:C.IsPrime :=hC
 let:p7 lV (akH C D) :=bZr hdim hproper
 obtain ⟨c,hc⟩:=d33 (ecE hD 6)
 have hne :alw (p.scale 6) c∉C:=hc ▸ c43 hproper 6
 have hlength:=h₂ C (p.scale 6) hC hdim (h₁ C (p.scale 6) hC hdim) c hne
  (bZr hdim hne)
 rw [hc,ebh hdim hproper] at hlength
 exact (p9 6 (dFv points hpoints)).trans hlength
end as4
end
section
namespace bjz
open MvPolynomial
theorem bX4
    {k A D σ ι:Type*} [oq k] [n5 A] [IsDomain A] [n5 D]
    [oj k A] [oj k D] [qz ι]
    (q:A →ₐ[k] D) (v :ι→A) (hv :Ee k (q ∘ v))
    (r :ι→cy σ k) (H Q:cy σ A)
    (hne :Dw H≠0) (hq:q (Dw H)=0)
    (he : (∑ i,C (v i)*nq (aU k A) (r i))=H*Q) :
    ∀ i,r i=0:= by
  classical
  have h (n:ℕ) : ∀ m:σ →₀ ℕ,m.degree=n→Q.coeff m=0 ∧ ∀ i,(r i).coeff m=0:= by
    induction n using NW with
    | h n ih =>
      intro m hm
      have hprod: (H*Q).coeff m=Dw H*Q.coeff m:= by
        rw [coeff_mul,Up (0,m)]
        · rfl
        · intro p hp hne'
          have hadd:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hp₁:p.1≠0:= by
            intro hz
            apply hne'
            exact Prod.ext hz (by simpa [hz] using hadd)
          have hdeg₁ :0<p.1.degree :=
            Rm (fun hd=>hp₁ ((Finsupp.degree_eq_zero_iff _).mp hd))
          have hdegs :p.1.degree+p.2.degree=n:= by
            rw [← oY ,hadd,hm]
          rw [(ih p.2.degree (by omega) p.2 rfl).1,th]
        · exact fun hmiss=>(hmiss (Finset.HasAntidiagonal.mem_antidiagonal.mpr (wA m))).elim
      have hc:=oz (fun P:cy σ A=>P.coeff m) he
      simp only [ze,coeff_C_mul,Gn,hprod] at hc
      have hrel : ∑ i,(r i).coeff m•(q ∘ v) i=0:= by
        simpa only [pG,ov,AlgHom.commutes,hq,zero_mul,zk,
          Lf ,FK] using oz q hc
      have hzero :=Fintype.linearIndependent_iff.mp hv _ hrel
      simp only [hzero,qJ,th,Finset.sum_const_zero] at hc
      exact ⟨(mul_eq_zero.mp hc.symm).resolve_left hne,hzero⟩
  intro i
  ext m
  exact (h m.degree m rfl).2 i
end bjz
end
section
namespace bjz
noncomputable section
open aR dN BO as4 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def translate {σ k :Type*} [n5 k] (c:σ→k) :
  cy σ k →ₐ[k] cy σ k :=
 sH (fun i=>mD i+C (c i))
private theorem gDI {σ k :Type*} [n5 k] (c:σ→k) :
  t9 (translate c) := by
 have h: (translate (fun i => -c i)).comp (translate c)=C9 k _:= by
  ext i:1
  simp [translate,v9,add_assoc]
 have hinv :Pv (translate (fun i => -c i)) (translate c) :=
  fun p=>KH h p
 exact hinv.injective
private theorem ewd
    (C₀:lz lI) [C₀.IsPrime] (a :c9) (c:uL a→lV)
    (hproper :alw a c∉C₀)
    {ι:Type} [qz ι] (v :ι→lI)
    (hv :Ee lV
      (fun i=>nX (C₀ ⊔ lJ {alw a c}) (v i))) :
    Ee (dV a) (fun i =>
      (nX _ (nq (aU lV (dV a)) (v i))
        : HG C₀ a)) := by
  classical
  let k :=lV
  let R:=cy (uL a) k
  let F:=dV a
  let B:=cy (Fin 4) R
  let L:=adi a
  let j:lI →+* B:=nq (aU k R)
  let H₀:B := ∑ m∈Bz a,
    C (mD m) * ∏ i:Fin 4,mD i^(m i).val
  let I:=C₀.map j ⊔ lJ {H₀}
  let J:lz L:=C₀.map (nq (aU k F)) ⊔ lJ {adK a}
  let M:G0 B:=(C5 R).map qU
  have :xL M L:=Pr (C5 R) F
  have hC (z :R) :aU B L (C z)=C (aU R F z) := by
    rw [Dv,map_C]
  have hX (i:Fin 4) :aU B L (mD i)=mD i:= by
    rw [Dv,map_X]
  have hj (p:lI) :aU B L (j p) =
      nq (aU k F) p:= by
    rw [Dv]
    change nq (aU R F) (nq (aU k R) p)= _
    rw [zm]
    rfl
  have hH :aU B L H₀=adK a := by
    simp only [H₀,adK,pG,ov,Aa ,uW,hC,hX]
    rfl
  have hJ:I.map (aU B L)=J:= by
    simp only [I,J,Ideal.map_sup,t4 ,sS ,uh,hH]
    rw [show (aU B L).comp j=nq (aU k F) from RingHom.ext hj]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  change ∑ i,g i•nX J (nq (aU k F) (v i))=0 at hg
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite (C5 R) g
  choose r hr using hd
  have hr' (i:ι) :aU R F (r i)=aU R F (d:R)*g i:= by
    simpa only [Lf] using hr i
  have hsum: (∑ i,C (g i)*nq (aU k F) (v i))∈J:= by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hscalar (x :dV a) :
        aU (dV a) (L ⧸ J) x=nX J (C x) :=rfl
    simpa only [pG,ov,Lf ,hscalar] using hg
  have hclear :aU B L (∑ i,C (r i)*j (v i))∈I.map (aU B L) := by
    rw [hJ]
    convert J.mul_mem_left (C (aU R F (d:R))) hsum using 1
    simp only [pG,ov,hC,hj,hr',Nr,vG]
  obtain ⟨s,hs,hmem⟩:=(KA M L I _).mp hclear
  obtain ⟨d',hd',rfl⟩:=Submonoid.mem_map.mp hs
  let A:=lI ⧸ C₀
  let q₀:=nX C₀
  let t:=translate c
  let f₀:R →+* cy (uL a) A :=
    (nq (aU k A)).comp t.toRingHom
  let fX:Fin 4→cy (uL a) A :=
    fun i=>C (q₀ (mD i))
  let f :B →+* cy (uL a) A :=
    z8 f₀ fX
  have hfC (p:R) :f (C p)=nq (aU k A) (t p) :=
    eval₂Hom_C f₀ fX p
  have hfX (i:Fin 4) :f (mD i)=C (q₀ (mD i)) :=
    eval₂Hom_X' f₀ fX i
  have hfj (p:lI) :f (j p)=C (q₀ p) := by
    have he :f.comp j=MvPolynomial.C.comp q₀:= by
      apply wR
      · intro z
        change f (nq (aU k R) (C z))=C (q₀ (C z))
        rw [map_C,hfC,t.commutes]
        change nq (aU k A) (C z)= _
        rw [map_C]
        rfl
      · intro i
        change f (nq (aU k R) (mD i))=C (q₀ (mD i))
        rw [map_X,hfX]
    exact MK he p
  have hcut:Dw (f H₀)=q₀ (alw a c) := by
    have htX (m:uL a) :t (mD m)=mD m+C (c m) :=
      yJ _ _
    simp only [H₀,alw,pG,ov,Aa ,uW,
      hfC,hfX,htX,oY ,map_X,map_C,
      constantCoeff_X,constantCoeff_C,wA,q₀]
    rfl
  have hI:I≤(lJ {f H₀}).comap f := by
    apply sup_le
    · rw [Vs]
      intro p hp
      change f (j p)∈(lJ {f H₀} : lz _)
      rw [hfj,Ideal.Quotient.eq_zero_iff_mem.mpr hp,qJ]
      exact Ideal.zero_mem _
    · apply (Dz _).mpr
      exact EK _
  have hmultiple :f (C d' * ∑ i,C (r i)*j (v i))∈(lJ {f H₀} : lz _) :=
    hI hmem
  obtain ⟨Q,hQ⟩:=Ideal.mem_span_singleton.mp hmultiple
  let q:A →ₐ[k] akH C₀ (alw a c) :=
    Ob k (Gk :C₀≤C₀ ⊔ lJ {alw a c})
  have he : (∑ i,C (q₀ (v i))*nq (aU k A) (t (d' * r i))) =
      f H₀*Q:= by
    calc
      _=f (C d' * ∑ i,C (r i)*j (v i)) := by
        simp only [ov,pG,hfC,hfj,Nr]
        exact qm rfl (fun i _=> by ac_rfl)
      _ = _:=hQ
  have hE :q (Dw (f H₀))=0:= by
    rw [hcut]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (G5 (EK _))
  have hz :=bX4 q (fun i=>q₀ (v i)) hv
    (fun i=>t (d' * r i)) (f H₀) Q (by rw [hcut]; exact mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
    hE he
  have hd'₀:d' ≠ 0:=mem_nonZeroDivisors_iff_ne_zero.mp hd'
  have hd₀:aU R F (d:R)≠0:= by
    simpa only [qJ] using
      (Ea R F).ne (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  intro i
  have hdi:d' * r i=0:=gDI c ((hz i).trans (qJ t).symm)
  have hri:=(mul_eq_zero.mp hdi).resolve_left hd'₀
  exact (mul_eq_zero.mp ((hr' i).symm.trans (by rw [hri,qJ]))).resolve_left hd₀
theorem proof :as4.c2 := by
 classical
 intro C₀ a hprime _ hgeneric c hproper hfinite
 let:C₀.IsPrime :=hprime
 let:p7 (dV a) (HG C₀ a) :=hgeneric
 let:p7 lV (akH C₀ (alw a c)) :=hfinite
 let b:=Module.finBasis lV (akH C₀ (alw a c))
 choose v hv using fun i=>y5 (b i)
 have hli:=ewd C₀ a c hproper v
   (show Ee lV
     (fun i=>nX (C₀ ⊔ lJ {alw a c}) (v i)) by
     simpa only [hv] using b.linearIndependent)
 change _≤pL (dV a) (HG C₀ a)
 simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank
end
end bjz
end
section
namespace axf
noncomputable section
open aR dN E6 MvPolynomial
def TV (a b h:c9) (t:Fin 3→ℕ) :Shape :=
 ((a.scale (t 0)).plus (b.scale (t 1))).plus (h.scale (t 2))
def aup (aI:lz lI) (p:c9) :ℕ :=
  pL lV
    ((t5 lV (nE p)).map
      (u9 lV aI).toLinearMap)
def a5T (aI:lz lI) (a b h:c9) (t:Fin 3→ℕ) :ℕ :=
 aup aI (TV a b h t)
abbrev axX (a b h:c9) :=
 Σ l:Fin 3,nE (![a,b,h] l)
def Kn {σ:Type} (block :σ→Fin 3) (e :σ →₀ ℕ) :Fin 3→ℕ :=
 fun l=>e.sum fun v n=>if block v=l then n else 0
def aAp {σ:Type} (block :σ→Fin 3) (forbidden:qy (σ →₀ ℕ))
    (t:Fin 3→ℕ) :ℕ :=
  ({e | Kn block e=t ∧ ∀ f∈forbidden,¬ f≤e} : Set (σ →₀ ℕ)).ncard
end
end axf
end
section
namespace axf
noncomputable section
open MvPolynomial
open scoped BigOperators
def amw (P:cy (Fin 3) ℚ) (t:Fin 3→ℕ) (pad:ℕ) :sI ℚ :=
 P.eval₂ uz fun l=>uz (pad:ℚ)+Polynomial.C (t l:ℚ)* II
theorem cNa (P:cy (Fin 3) ℚ) (t:Fin 3→ℕ) (pad n:ℕ) :
   (amw P t pad).eval (n:ℚ) =
     ox (fun l=>((n*t l+pad:ℕ) :ℚ)) P:= by
 let f :=Mj (n:ℚ)
 have hf :f.comp uz=RingHom.id ℚ:= by ext r; simp [f]
 change f (amw P t pad)= _
 rw [amw,MvPolynomial.eval₂_comp_left,hf,MvPolynomial.eval₂_id]
 apply oz (fun x=>ox x P)
 funext l
 simp [f,zk,EP ,Ef ,yL,FK]
private theorem eOU {α:Type} (s :qy α)
   (q:α→sI ℚ) (d:α→ℕ) (hq : ∀ i∈s,(q i).natDegree≤d i) :
   (∏ i∈s,q i).natDegree ≤ ∑ i∈s,d i ∧
     (∏ i∈s,q i).coeff (∑ i∈s,d i) = ∏ i∈s,(q i).coeff (d i) := by
 classical
 induction s using Te with
 | empty=>simp
 | insert i s hi ih =>
   have hi' := hq i (Finset.mem_insert_self i s)
   obtain ⟨hd,hc⟩:=ih fun j hj=>hq j (Finset.mem_insert_of_mem hj)
   rw [MS hi,Finset.sum_insert hi,MS hi,
     Polynomial.coeff_mul_add_eq_of_natDegree_le hi' hd,hc]
   exact ⟨Polynomial.natDegree_mul_le.trans (Fz hi' hd),rfl⟩
private theorem c0P (e :Fin 3 →₀ ℕ) (r :ℚ) (t:Fin 3→ℕ) (pad:ℕ) :
    (amw (oZ e r) t pad).natDegree≤e.degree ∧
      (amw (oZ e r) t pad).coeff e.degree =
        ox (fun i=>(t i:ℚ)) (oZ e r) := by
  let f (i:Fin 3) :=uz (pad:ℚ)+Polynomial.C (t i:ℚ)* II
  have hf (i:Fin 3) : (f i).natDegree≤1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (R9 _ _).trans Polynomial.natDegree_X_le
  have hc (i:Fin 3) : (f i).coeff 1=(t i:ℚ) := by
    simp [f]
  have hp (i:Fin 3) : ((f i)^e i).natDegree≤e i:= by
    simpa using Polynomial.natDegree_pow_le_of_le (e i) (hf i)
  have hpc (i:Fin 3) : ((f i)^e i).coeff (e i)=(t i:ℚ)^e i:= by
    simpa [hc] using
      (Polynomial.coeff_pow_of_natDegree_le (m:=e i) (hf i))
  obtain ⟨hd,hcoeff⟩:=eOU e.support (fun i=>(f i)^e i) e
    (fun i _=>hp i)
  rw [amw,MvPolynomial.eval₂_monomial,SC]
  change (uz r * ∏ i∈e.support,(f i)^e i).natDegree≤_ ∧
    (uz r * ∏ i∈e.support,(f i)^e i).coeff
      (∑ i∈e.support,e i)=r * ∏ i∈e.support,(t i:ℚ)^e i
  exact ⟨(R9 _ _).trans hd,by
    rw [Polynomial.coeff_C_mul,hcoeff]
    simp only [hpc]⟩
private theorem c7k (P:cy (Fin 3) ℚ) (t:Fin 3→ℕ) (pad:ℕ) :
  amw P t pad = ∑ e∈P.support,amw (oZ e (P.coeff e)) t pad:= by
 unfold amw
 simp only [← MvPolynomial.coe_eval₂Hom]
 conv_lhs=>rw [P.as_sum]
 rw [pG]
theorem dVG (P:cy (Fin 3) ℚ) (t:Fin 3→ℕ) (pad:ℕ) :
  (amw P t pad).natDegree≤P.totalDegree := by
 rw [c7k]
 exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he =>
  (c0P e (P.coeff e) t pad).1.trans (Bf he)
theorem cGj (P:cy (Fin 3) ℚ) (t:Fin 3→ℕ) (pad:ℕ) {d:ℕ}
   (hd:P.totalDegree≤d) :
   (amw P t pad).coeff d =
     ox (fun i=>(t i:ℚ)) (G8 d P) := by
 classical
 rw [c7k,Polynomial.finsetSum_coeff,homogeneousComponent_apply,pG,
   F9]
 refine qm rfl fun e he => ?_
 obtain ⟨hdeg,hcoeff⟩:=c0P e (P.coeff e) t pad
 by_cases hed:e.degree=d
 · simpa [hed] using hcoeff
 · simp only [hed,↓reduceIte]
   exact RJ
     (hdeg.trans_lt (Kz ((Bf he).trans hd) hed))
private theorem d1r (P:cy (Fin 3) ℚ)
   (hp : ∀ t:Fin 3→ℕ,(∀ i,0<t i) →
     ox (fun i=>(t i:ℚ)) P=0) :P=0:= by
 let f :ℕ ↪ ℚ:=⟨fun n=>((n+1 :ℕ) :ℚ),by
   intro a b hab
   exact Nat.add_right_cancel (Nat.cast_injective (R:=ℚ) hab)⟩
 let s :=(pz (P.totalDegree+1)).map f
 apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _=>s)
 · intro i
   simpa [s] using Pc (degreeOf_le_totalDegree P i)
 · intro x hx
   have hx' (i:Fin 3) : ∃ n:ℕ,n∈pz (P.totalDegree+1)∧f n=x i :=
     Finset.mem_map.mp (hx i)
   choose t _ ht using hx'
   have hcast: (fun i=>(((t i+1 :ℕ) :ℚ)))=x :=funext ht
   rw [← hcast]
   exact hp (fun i=>t i+1) (fun _=>Np _)
theorem dVv (P:cy (Fin 3) ℚ) (d:ℕ)
  (h : ∀ t:Fin 3→ℕ,(∀ i,0<t i)→(amw P t 0).natDegree≤d) :
  P.totalDegree≤d:= by
 by_contra! hlt
 have hzero :G8 P.totalDegree P=0:= by
  apply d1r
  intro t ht
  rw [← cGj P t 0 vl]
  exact RJ ((h t ht).trans_lt hlt)
 have hsmall:P.totalDegree≤P.totalDegree - 1 := by
  apply LP
  intro e he
  change e.degree≤P.totalDegree - 1
  have hed:e.degree≤P.totalDegree :=Bf he
  suffices e.degree≠P.totalDegree by omega
  intro heq
  have hz :=oz (fun Q:cy (Fin 3) ℚ=>Q.coeff e) hzero
  exact (mem_support_iff.mp he) (by simpa [coeff_homogeneousComponent,heq] using hz)
 omega
def exponent (i j k :ℕ) :Fin 3 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![i,j,k]
private theorem bdB (i j k :ℕ) : (exponent i j k).degree=i+j+k := by
 simp [exponent,PA,Pj]
private theorem exponent_eq_iff {i j k u v w:ℕ} :
   exponent i j k=exponent u v w↔i=u∧j=v∧k=w:= by
 constructor
 · intro h
   exact ⟨oz (fun e :Fin 3 →₀ ℕ=>e 0) h,
    oz (fun e :Fin 3 →₀ ℕ=>e 1) h,oz (fun e :Fin 3 →₀ ℕ=>e 2) h⟩
 · rintro ⟨rfl,rfl,rfl⟩
   rfl
private theorem d5i {e :Fin 3 →₀ ℕ} (he :e.degree=2) :
   e=exponent 2 0 0∨e=exponent 0 2 0∨e=exponent 0 0 2 ∨
     e=exponent 1 1 0∨e=exponent 1 0 1∨e=exponent 0 1 1 := by
 have heq {i j k :ℕ} (h:e 0=i∧e 1=j∧e 2=k) :e=exponent i j k := by
   ext l
   fin_cases l
   · exact h.1
   · exact h.2.1
   · exact h.2.2
 have hs :e 0+e 1+e 2=2 := by
   simpa [PA,Pj] using he
 have hc :
     (e 0=2∧e 1=0∧e 2=0)∨(e 0=0∧e 1=2∧e 2=0) ∨
     (e 0=0∧e 1=0∧e 2=2)∨(e 0=1∧e 1=1∧e 2=0) ∨
     (e 0=1∧e 1=0∧e 2=1)∨(e 0=0∧e 1=1∧e 2=1) := by omega
 rcases hc with hc | hc | hc | hc | hc | hc
 · exact uJ (heq hc)
 · exact p6 (uJ (heq hc))
 · exact p6 (p6 (uJ (heq hc)))
 · exact p6 (p6 (p6 (uJ (heq hc))))
 · exact p6 (p6 (p6 (p6 (uJ (heq hc)))))
 · exact p6 (p6 (p6 (p6 (p6 (heq hc)))))
theorem d2s (P:cy (Fin 3) ℚ) (x :Fin 3→ℚ) :
    ox x (G8 2 P) =
      P.coeff (exponent 2 0 0)*(x 0)^2+P.coeff (exponent 0 2 0)*(x 1)^2 +
      P.coeff (exponent 0 0 2)*(x 2)^2 +
      P.coeff (exponent 1 1 0)*(x 0)*(x 1) +
      P.coeff (exponent 1 0 1)*(x 0)*(x 2) +
      P.coeff (exponent 0 1 1)*(x 1)*(x 2) := by
  classical
  let m (i j k :ℕ) :=oZ (exponent i j k) (P.coeff (exponent i j k))
  have hform :G8 2 P =
      m 2 0 0+m 0 2 0+m 0 0 2+m 1 1 0+m 1 0 1+m 0 1 1 := by
    ext e
    simp only [coeff_homogeneousComponent,m,AddMonoidAlgebra.coeff_add]
    by_cases he :e.degree=2
    · rcases d5i he with he | he | he | he | he | he <;>
        rw [he] <;> norm_num [bdB,exponent_eq_iff]
    · have hne (i j k :ℕ) (hd:i+j+k=2) :exponent i j k≠e := by
        intro h
        exact he (by rw [← h,bdB,hd])
      simp [he,hne 2 0 0 rfl,hne 0 2 0 rfl,hne 0 0 2 rfl,
        hne 1 1 0 rfl,hne 1 0 1 rfl,hne 0 1 1 rfl]
  have heval (i j k :ℕ) :
      ox x (m i j k) =
        P.coeff (exponent i j k)*(x 0^i*x 1^j*x 2^k) := by
    change ox x (oZ (exponent i j k) (P.coeff (exponent i j k)))= _
    rw [SC,Ok _ _ (fun _=>FV _)]
    simp [Fin.prod_univ_three,exponent,vG]
  simp [hform,heval,vG]
end
end axf
end
section
namespace axf
noncomputable section
open aR dN GJ E6 lB MvPolynomial
def bQt (p q:c9) :Prop :=
 p.b≤q.b∧p.j≤q.j∧p.t≤q.t
private theorem b7h {p q:c9} (hpq:bQt p q) :
  nE p⊆nE q:= by
 intro e he
 obtain ⟨hb,hj,ht⟩:=hpq
 exact ⟨he.1.trans (p9 6 hb),
  he.2.1.trans (p9 6 hj),he.2.2.trans (p9 6 ht)⟩
theorem cDy (aI:lz lI) {p q:c9} (hpq:bQt p q) :
  aup aI p≤aup aI q:= by
 let:=restrictSupport_finite (R:=lV) (Set.toFinite (nE q))
 exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono lV (b7h hpq)))
theorem bC9 {a b h:c9} (ha :bF a) (hb:bF b) (hh:bF h)
  (t:Fin 3→ℕ) :bF (TV a b h t) :=
 Nc (Nc (BP ha _) (BP hb _)) (BP hh _)
theorem cG6 {a b h:c9} (ha :vE a) (hb:vE b) (hh:vE h)
   {t:Fin 3→ℕ} (ht:0<t 0+t 1+t 2) :vE (TV a b h t) := by
 refine ⟨bC9 ha.1 hb.1 hh.1 t,?_⟩
 change 0<t 0*a.t+t 1*b.t+t 2*h.t
 by_cases h0:0<t 0
 · have :=GR h0 ha.2
   omega
 by_cases h1 :0<t 1
 · have :=GR h1 hb.2
   omega
 have :=GR (show 0<t 2 by omega) hh.2
 omega
theorem cG7 (a b h:c9) (t:Fin 3→ℕ) (n pad:ℕ) :
  TV a b h (fun l=>n*t l+pad) =
   ((TV a b h t).scale n).plus ((TV a b h (fun _=>1)).scale pad) := by
 cases a
 cases b
 cases h
 simp only [TV,pQ,pU,Nat.one_mul]
 congr 1 <;> ring
theorem dAg (aI:lz lI) {p q:c9}
    (hp:vE p) (hq:bF q) (n pad:ℕ) :
    aup aI (p.scale n)≤aup aI ((p.scale n).plus (q.scale pad)) ∧
      aup aI ((p.scale n).plus (q.scale pad)) ≤
        aup aI (p.scale (n+pad*q.b)) := by
  have ht:0<p.t:=hp.2
  have hj:0<p.j:= by have :=hp.1.2; omega
  have hb:0<p.b:=hj.trans_le hp.1.1
  have hqt:q.t≤q.b:= by have :=hq.1; have :=hq.2; omega
  constructor
  · apply cDy
    exact ⟨vZ ..,vZ ..,vZ ..⟩
  · apply cDy
    dsimp [bQt,pQ,pU]
    simp only [z7]
    exact ⟨zi (G4 _ hb) _,
      zi ((p9 _ hq.1).trans (G4 _ hj)) _,
      zi ((p9 _ hqt).trans (G4 _ ht)) _⟩
def aMu (aI:lz lI) (p:c9) :lz (cy (nE p) lV) :=
 aI.comap (monomialMap lV (nE p)).toRingHom
theorem cDz (aI:lz lI) {p:c9} (hp:bF p) (n:ℕ) :
   aup aI (p.scale n)=affineHilbertFunction (aMu aI p) n:= by
 let φ:=monomialMap lV (nE p)
 let I:=aMu aI p
 let g: (cy (nE p) lV ⧸ I) →ₐ[lV] (lI ⧸ aI) :=
   WD aI φ vl
 have hg:t9 g:=Ideal.quotientMap_injective
 have hcomp:g.toLinearMap.comp (u9 lV I).toLinearMap =
     (u9 lV aI).toLinearMap.comp φ.toLinearMap:= by
   ext x
   rfl
 unfold aup
 rw [← c0M hp,← G9,← hcomp,G9]
 exact (Submodule.equivMapOfInjective _ hg (quotientDegreeLE I n)).finrank_eq.symm
theorem cDx (aI:lz lI) {p:c9}
  (hdim:u8 (lI ⧸ aI)=2) (hp:vE p) :
  (zS (aMu aI p)).natDegree≤2 := by
 let φ:=monomialMap lV (nE p)
 have hφ:t8 φ:=monomialMap_surjective (euG hp)
 exact (natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ aI).trans_le
  (axg.beu (d:=2) hdim.le)
end
end axf
end
section
namespace axf
noncomputable section
open Filter aR dN GJ E6 lB MvPolynomial
def c1 :Prop :=
  ∀ (aI:lz lI) (a b h:c9),
    bF a→bF b→bF h →
    ∃ forbidden:qy (axX a b h →₀ ℕ),
      ∀ t:Fin 3→ℕ,
        a5T aI a b h t=aAp (fun v=>v.1) forbidden t
def c2 :Prop :=
  ∀ {σ:Type} [Finite σ] (block :σ→Fin 3),t8 block →
    ∀ forbidden:qy (σ →₀ ℕ),
      ∃ (P:cy (Fin 3) ℚ) (N :ℕ),
        ∀ t:Fin 3→ℕ,(∀ l,N≤t l) →
          ox (fun l=>(t l:ℚ)) P=(aAp block forbidden t:ℚ)
private theorem dN2 (a b h:c9) (t:Fin 3→ℕ) (n:ℕ) :
  TV a b h (fun l=>n*t l)=(TV a b h t).scale n:= by
 simpa [pQ,pU] using cG7 a b h t n 0
private theorem eM2 (aI:lz lI) {a b h:c9}
   (hdim:u8 (lI ⧸ aI)=2)
   (ha :vE a) (hb:vE b) (hh:vE h)
   (P:cy (Fin 3) ℚ) (N :ℕ)
   (hP : ∀ t:Fin 3→ℕ,(∀ l,N≤t l) →
     ox (fun l=>(t l:ℚ)) P=(a5T aI a b h t:ℚ)) :
   P.totalDegree≤2 := by
 apply dVv
 intro t ht
 let p:=TV a b h t
 have hp:vE p:=cG6 ha hb hh (by have :=ht 0; omega)
 have hpol:amw P t 0=zS (aMu aI p) := by
   apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
   filter_upwards [Nj N,eventually_eval_affineHilbertPolynomial (aMu aI p)]
     with n hn hH
   have htail (l:Fin 3) :N≤n*t l+0 :=
     hn.trans (G4 n (ht l))
   rw [cNa,hP _ htail,hH,a5T]
   simp only [Nat.add_zero,dN2]
   rw [cDz aI hp.1]
 rw [hpol]
 exact cDx aI hdim hp
private theorem bEc (aI:lz lI) {a b h:c9}
    (hdim:u8 (lI ⧸ aI)=2)
    (ha :vE a) (hb:vE b) (hh:vE h)
    (P:cy (Fin 3) ℚ) (N :ℕ) (hdeg:P.totalDegree≤2)
    (hP : ∀ t:Fin 3→ℕ,(∀ l,N≤t l) →
      ox (fun l=>(t l:ℚ)) P=(a5T aI a b h t:ℚ))
    (t:Fin 3→ℕ) (ht:0<t 0+t 1+t 2) :
    (zS (aMu aI (TV a b h t))).coeff 2 =
      (amw P t N).coeff 2 := by
  let p:=TV a b h t
  let q:=TV a b h (fun _=>1)
  let S:=zS (aMu aI p)
  let R:=amw P t N
  let d:=N*q.b
  have hp:vE p:=cG6 ha hb hh ht
  have hq:bF q:=bC9 ha.1 hb.1 hh.1 _
  have hSdeg:=cDx aI hdim hp
  have hRdeg:R.natDegree≤2 :=(dVG P t N).trans hdeg
  obtain ⟨M,hM⟩:=exists_eval_affineHilbertPolynomial (aMu aI p)
  have hS (n:ℕ) (hn:M≤n) :
      S.eval (n:ℚ)=(aup aI (p.scale n) :ℚ) := by
    exact (hM n hn).trans (oz Nat.cast (cDz aI hp.1 n).symm)
  have hR (n:ℕ) :
      R.eval (n:ℚ)=(aup aI ((p.scale n).plus (q.scale N)) :ℚ) := by
    rw [show R=amw P t N from rfl,cNa,
      hP _ (fun l=>Nat.le_add_left N (n*t l)),a5T,cG7]
  have hbounds : ∀ᶠ n:ℕ in atTop,
      S.eval (n:ℚ)≤R.eval (n:ℚ) ∧
        R.eval (n:ℚ)≤(KI (d:ℚ) S).eval (n:ℚ) := by
    filter_upwards [Nj M] with n hn
    have hs : (KI (d:ℚ) S).eval (n:ℚ)=S.eval ((n+d:ℕ) :ℚ) := by
      rw [Polynomial.taylor_apply,Polynomial.eval_comp]
      simp [EP]
    rw [hs,hS n hn,hR n,hS (n+d) (hn.trans (vZ n d))]
    obtain ⟨hlo,hhi⟩:=dAg aI hp hq n N
    exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
  have hlo:=P7 hSdeg hRdeg
    (hbounds.mono fun _ hn=>hn.1)
  have hshift: (KI (d:ℚ) S).natDegree≤2 := by
    simpa only [Polynomial.natDegree_taylor] using hSdeg
  have hhi:=P7 hRdeg hshift
    (hbounds.mono fun _ hn=>hn.2)
  rw [Polynomial.coeff_taylor_of_natDegree_le _ hSdeg] at hhi
  exact GB hlo hhi
theorem of_children (h1 :c1) (h2 :c2) :E6.c2 := by
 intro aI a b h _ hdim ha hb hh
 obtain ⟨forbidden,hcount⟩:=h1 aI a b h ha.1 hb.1 hh.1
 let block :axX a b h→Fin 3:= fun v=>v.1
 have hblock :t8 block := by
   intro l
   exact ⟨⟨l,⟨0,brA _⟩⟩,rfl⟩
 obtain ⟨P,N,hP⟩:=h2 block hblock forbidden
 have hval (t:Fin 3→ℕ) (ht : ∀ l,N≤t l) :
     ox (fun l=>(t l:ℚ)) P=(a5T aI a b h t:ℚ) := by
   rw [hcount]
   exact hP t ht
 have hdeg:=eM2 aI hdim ha hb hh P N hval
 refine ⟨P.coeff (exponent 2 0 0),P.coeff (exponent 0 2 0),P.coeff (exponent 0 0 2),
   P.coeff (exponent 1 1 0),P.coeff (exponent 1 0 1),P.coeff (exponent 0 1 1),?_⟩
 intro i j k hijk
 let t:Fin 3→ℕ := ![i,j,k]
 change (zS (aMu aI (TV a b h t))).coeff 2= _
 rw [bEc aI hdim ha hb hh P N hdeg hval t hijk,cGj P t N hdeg,
   d2s]
 rfl
end
end axf
end
section
namespace cyf
noncomputable section
open aR dN E6 axf Kd MvPolynomial
open lB (bF)
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem gL7 {σ:Type} (block :σ→Fin 3) (e :σ →₀ ℕ) :
  vw (step ∘ block) e=Kn block e := by
 funext i
 simp only [JK,Kn,Finsupp.sum,Finset.sum_apply,step,zk,
  Pi.smul_apply,Pi.single_apply]
 apply qm rfl
 intro v _
 split <;> simp_all [eq_comm]
private theorem dN0 (a b h:c9) (s t:Fin 3→ℕ) :
  TV a b h (s+t)=(TV a b h s).plus (TV a b h t) := by
 simp only [TV,pQ,pU,Pi.add_apply]
 congr 1 <;> ring
private theorem dN3 (a b h:c9) (i:Fin 3) (n:ℕ) :
  TV a b h (n•step i)=(![a,b,h] i).scale n:= by
 fin_cases i <;> simp [TV,pQ,pU,step,Pi.smul_apply]
private def a3R (a b h:c9) : (axX a b h →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
 vw fun v=>v.2.val
private theorem b2w {a b h:c9} (ha :bF a) (hb:bF b)
    (hh:bF h) (e :axX a b h →₀ ℕ) :
    a3R a b h e ∈
      nE (TV a b h (vw (step ∘ fun v=>v.1) e)) := by
  induction e using Finsupp.induction_linear with
  | zero=>simpa only [map_zero] using brA (TV a b h 0)
  | add e f he hf =>
      rw [oY ,oY ,dN0,
        a44 (bC9 ha hb hh _) (bC9 ha hb hh _)]
      exact Set.add_mem_add he hf
  | single v n =>
      rw [Au,zk,dN3]
      have hch (i:Fin 3) :bF (![a,b,h] i) := by
        fin_cases i
        exacts [ha,hb,hh]
      rw [brz (hch v.1),a3R,Au]
      induction n with
      | zero=>simp
      | succ n ih =>
          rw [Fa ,Fa]
          exact Set.add_mem_add ih v.2.property
private theorem b2v {a b h:c9} (i:Fin 3) (n:ℕ)
    {m:Fin 4 →₀ ℕ} (hm:m∈n•nE (![a,b,h] i)) :
    ∃ e :axX a b h →₀ ℕ,
      vw (step ∘ fun v=>v.1) e=n•step i∧a3R a b h e=m:= by
  induction n generalizing m with
  | zero =>
      rw [zero_smul,Mw] at hm
      subst m
      exact ⟨0,by simp,qJ _⟩
  | succ n ih =>
      rw [Fa] at hm
      obtain ⟨u,hu,v,hv,rfl⟩:=hm
      obtain ⟨e,he,hexp⟩:=ih hu
      let w:axX a b h:=⟨i,⟨v,hv⟩⟩
      refine ⟨e+Finsupp.single w 1,?_,?_⟩
      · rw [oY ,Au,FQ,he,Fa]
        rfl
      · rw [oY ,hexp,a3R,Au,FQ]
private theorem b2u {a b h:c9} (ha :bF a) (hb:bF b)
   (hh:bF h) (t:Fin 3→ℕ) {m:Fin 4 →₀ ℕ}
   (hm:m∈nE (TV a b h t)) :
   ∃ e :axX a b h →₀ ℕ,
     vw (step ∘ fun v=>v.1) e=t∧a3R a b h e=m:= by
 rw [TV,a44 (Nc (BP ha _) (BP hb _))
   (BP hh _),a44 (BP ha _) (BP hb _),
   brz ha,brz hb,brz hh] at hm
 obtain ⟨_,⟨u,hu,v,hv,rfl⟩,w,hw,rfl⟩:=hm
 obtain ⟨e₀,h₀,h₀'⟩:=b2v (a :=a) (b:=b) (h:=h) 0 (t 0) hu
 obtain ⟨e₁,h₁,h₁'⟩:=b2v (a :=a) (b:=b) (h:=h) 1 (t 1) hv
 obtain ⟨e₂,h₂,h₂'⟩:=b2v (a :=a) (b:=b) (h:=h) 2 (t 2) hw
 refine ⟨e₀+e₁+e₂,?_,by rw [oY ,oY ,h₀',h₁',h₂']⟩
 rw [oY ,oY ,h₀,h₁,h₂]
 funext i
 fin_cases i <;> simp [step]
private def K9 (a b h:c9) :
  cy (axX a b h) lV →ₐ[lV] GeoJets :=
 sH fun v=>oZ v.2.val 1
private theorem dcq (a b h:c9) (e :axX a b h →₀ ℕ) :
  K9 a b h (oZ e 1)=oZ (a3R a b h e) 1 := by
 rw [K9,aeval_monomial,Finsupp.prod,a3R,JK,Finsupp.sum]
 simp only [monomial_pow,one_pow,← monomial_sum_one,v9,C_mul_monomial,mul_one]
private theorem gnJ {a b h:c9} (ha :bF a) (hb:bF b)
   (hh:bF h) (t:Fin 3→ℕ) :
   (In lV (step ∘ fun v :axX a b h=>v.1) t).map
     (K9 a b h).toLinearMap =
     t5 lV (nE (TV a b h t)) := by
 have hS:In lV (step ∘ fun v :axX a b h=>v.1) t =
     t5 lV {e | vw (step ∘ fun v=>v.1) e=t} :=
   weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
 apply GB
 · rw [Submodule.map_le_iff_le_comap,hS,Kv,Qw]
   rintro _ ⟨e,he,rfl⟩
   change K9 a b h (oZ e 1) ∈
     t5 lV (nE (TV a b h t))
   rw [dcq,monomial_mem_restrictSupport]
   exact uJ ((show vw (step ∘ fun v=>v.1) e=t from he) ▸
     b2w ha hb hh e)
 · rw [Kv,Qw]
   rintro _ ⟨m,hm,rfl⟩
   obtain ⟨e,he,rfl⟩:=b2u ha hb hh t hm
   exact ⟨oZ e 1,isWeightedHomogeneous_monomial _ _ _ he,dcq a b h e⟩
private def dVf (σ:Type) [Finite σ] :MonomialOrder σ:= by
 let _:=Kh σ
 let _:LinearOrder σ:=LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
 have :WellFoundedGT σ:=Finite.to_wellFoundedGT
 exact MonomialOrder.degLex
theorem proof :axf.c1 := by
  classical
  intro aI a b h ha hb hh
  let σ:=axX a b h
  let block :σ→Fin 3:=Sigma.fst
  let S:=In lV (step ∘ block)
  let φ:=K9 a b h
  let C:=aI.comap φ
  let J:=(C.homogeneousCore S).toIdeal
  have hhom:J.IsHomogeneous S:=(C.homogeneousCore S).isHomogeneous
  have hgraded:aiD block J :=
    fun _ hp t=>weightedHomogeneousComponent_mem_of_mem _ _ hhom hp t
  let order :=dVf σ
  obtain ⟨forbidden,hf⟩:=order.exists_finset_standardExponents_iff J
  refine ⟨forbidden,fun t => ?_⟩
  let W:=(S t).map (u9 lV J).toLinearMap
  let f :=WD aI φ (Ideal.toIdeal_homogeneousCore_le S C)
  have hinj:t9 (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x,hx⟩ hx0
    obtain ⟨p,hp,rfl⟩:=Submodule.mem_map.mp hx
    change nX aI (φ p)=0 at hx0
    have hpsurface :φ p∈aI:=Ideal.Quotient.eq_zero_iff_mem.mp hx0
    have hpJ:p∈J:=Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t,hp⟩
      (show p∈C from hpsurface)
    exact qM (Ideal.Quotient.eq_zero_iff_mem.mpr hpJ)
  have himage :W.map f.toLinearMap =
      (t5 lV (nE (TV a b h t))).map
        (u9 lV aI).toLinearMap:= by
    rw [← gnJ ha hb hh]
    simp only [W,← G9,← AlgHom.comp_toLinearMap,f]
    rfl
  have hrank :pL lV W=a5T aI a b h t:= by
    change _=aup aI (TV a b h t)
    rw [aup,← himage,← LinearMap.range_domRestrict W f.toLinearMap]
    exact (Vl _ hinj).finrank_eq
  have hs :
      ({e | e∈order.standardExponents J∧vw (step ∘ block) e=t} :
        Set (σ →₀ ℕ)) =
      {e | Kn block e=t ∧ ∀ u∈forbidden,¬ u≤e} := by
    ext e
    simp only [VS ,hf,gL7,and_comm]
  have hcount:lO block J t=(aAp block forbidden t:ℚ) := by
    simpa only [hs,aAp] using aXV block order J hgraded t
  change (pL lV W:ℚ)= _ at hcount
  rw [hrank] at hcount
  exact_mod_cast hcount
end
end cyf
end
section
namespace cyg
noncomputable section
open Finset axf
open scoped BigOperators
private abbrev Block {σ:Type} (block :σ→Fin 3) (l:Fin 3) :=
 {v :σ // block v=l}
private abbrev Exact {σ:Type} (block :σ→Fin 3) (t:Fin 3→ℕ) :=
 {e :σ →₀ ℕ // Kn block e=t}
section Count
variable {σ:Type} [qz σ] (block :σ→Fin 3)
 [∀ l,qz (Block block l)]
private theorem degree_eq_sum (e :σ →₀ ℕ) (l:Fin 3) :
  Kn block e l = ∑ v :Block block l,e v := by
 change e.sum (fun v n=>if block v=l then n else 0)= _
 rw [zE _ _ (fun v=> by simp),← F9]
 exact sum_subtype _ (by simp) _
private theorem boQ (e f :σ →₀ ℕ) (l:Fin 3) :
  Kn block (e+f) l=Kn block e l+Kn block f l:= by
 simp only [degree_eq_sum,SD,G2]
private theorem degree_mono {e f :σ →₀ ℕ} (hef :e≤f) (l:Fin 3) :
  Kn block e l≤Kn block f l:= by
 simp only [degree_eq_sum]
 exact sum_le_sum fun v _=>Finsupp.le_def.mp hef v
private def cNn [Kl σ] (t:Fin 3→ℕ) :
    Exact block t ≃ ∀ l:Fin 3,(univ :qy (Block block l)).finsuppAntidiag (t l) where
  toFun e l:=⟨Finsupp.equivFunOnFinite.symm (fun v=>e.1 (v :σ)),by
    rw [mem_finsuppAntidiag]
    exact ⟨(degree_eq_sum block e.1 l).symm.trans (yB e.2 l),subset_univ _⟩⟩
  invFun f :=⟨Finsupp.equivFunOnFinite.symm (fun v=>(f (block v)).1 ⟨v,rfl⟩),by
    funext l
    rw [degree_eq_sum]
    calc
      _ = ∑ v :Block block l,(f l).1 v := by
        apply qm rfl
        rintro ⟨v,hv⟩ -
        subst l
        rfl
      _=t l:=(mem_finsuppAntidiag.mp (f l).2).1⟩
  left_inv e := by
    apply qM
    ext v
    rfl
  right_inv f := by
    funext l
    apply qM
    ext v
    obtain ⟨v,hv⟩:=v
    subst l
    rfl
private theorem d3F [Kl σ] (hblock :t8 block) (t:Fin 3→ℕ) :
    Nat.card (Exact block t) =
      ∏ l:Fin 3,(t l+(wY (Block block l) - 1)).choose
        (wY (Block block l) - 1) := by
  rw [J4 (cNn block t),TH,Fintype.card_pi]
  refine prod_congr rfl fun l _ => ?_
  rw [Fintype.card_coe,card_finsuppAntidiag_nat_eq_choose,card_univ]
  obtain ⟨v,hv⟩:=hblock l
  have hpos :0<wY (Block block l) :=
    Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
  have hadd:wY (Block block l)+t l - 1 =
      t l+(wY (Block block l) - 1) := by omega
  exact (Nat.choose_symm_of_eq_add hadd).trans (by rw [hadd])
private def coneEquiv (s :σ →₀ ℕ) (t:Fin 3→ℕ)
  (hs : ∀ l,Kn block s l≤t l) :
  {e :σ →₀ ℕ // Kn block e=t∧s≤e} ≃
    Exact block (fun l=>t l - Kn block s l) where
 toFun e :=⟨e.1 - s,by
  funext l
  have hadd:=oz (fun f=>Kn block f l) (NY e.2.2)
  rw [boQ,yB e.2.1 l] at hadd
  change Kn block (e.1 - s) l=t l - Kn block s l
  omega⟩
 invFun u:=⟨u.1+s,⟨by
  funext l
  rw [boQ,yB u.2 l]
  exact Nat.sub_add_cancel (hs l),le_add_self⟩⟩
 left_inv e :=qM (NY e.2.2)
 right_inv u:=qM (add_tsub_cancel_right u.1 s)
end Count
private theorem cNp {σ:Type} (block :σ→Fin 3) (t:Fin 3→ℕ)
    [qz (Exact block t)] (p: (σ →₀ ℕ)→Prop) [DecidablePred p] :
    #(univ.filter fun e :Exact block t=>p e.1) =
      ({e | Kn block e=t∧p e} : Set (σ →₀ ℕ)).ncard:= by
  rw [← RC]
  calc
    _=Nat.card ↥(univ.filter fun e :Exact block t=>p e.1) := by
      rw [TH,Fintype.card_coe]
    _ = _:=J4
      { toFun:= fun e=>⟨e.1.1,e.1.2,(mem_filter.mp e.2).2⟩
        invFun:= fun e=>⟨⟨e.1,e.2.1⟩,mem_filter.mpr ⟨vh _,e.2.2⟩⟩
        left_inv := fun e=>qM rfl
        right_inv := fun e=>qM rfl }
private theorem d1U (t:Fin 3→ℕ) (l:Fin 3) (d k :ℕ)
    (hk :k≤t l) :
    ox (fun l=>(t l:ℚ))
        (JM (mD l) (GY ℚ d k)) =
      ((t l - k+d).choose d:ℚ) := by
  change sH (fun i=>(t i:ℚ))
    (JM (mD l) (GY ℚ d k))= _
  rw [← Polynomial.aeval_algHom_apply,yJ]
  change (GY ℚ d k).eval (t l:ℚ)= _
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d (hk.trans (vZ _ _)),
    Nat.sub_add_comm hk]
theorem proof :axf.c2 := by
  classical
  intro σ hσ block hblock forbidden
  let:qz σ:=Kh σ
  let (l:Fin 3) :qz (Block block l) :=Kh _
  let d (l:Fin 3) :=wY (Block block l) - 1
  let N :=univ.sup (Kn block (forbidden.sup id))
  let P:cy (Fin 3) ℚ :=
    ∑ U∈forbidden.powerset,
      qU ((-1 :ℚ) ^ #U) *
        ∏ l:Fin 3,JM (mD l)
          (GY ℚ (d l) (Kn block (U.sup id) l))
  refine ⟨P,N,?_⟩
  intro t ht
  let:qz (Exact block t) :=Fintype.ofEquiv _ (cNn block t).symm
  let cone (s :σ →₀ ℕ) :qy (Exact block t) :=univ.filter fun e=>s≤e.1
  have hinter (U:qy (σ →₀ ℕ)) :U.inf cone=cone (U.sup id) := by
    ext e
    simp only [Finset.mem_inf,cone,Gj,vh,true_and,Finset.sup_le_iff,id]
  have havoid : (forbidden.inf fun s=>(cone s)ᶜ) =
      univ.filter (fun e :Exact block t => ∀ s∈forbidden,¬ s≤e.1) := by
    ext e
    simp only [Finset.mem_inf,mem_compl,cone,Gj,vh,true_and]
  have hcard: (#(forbidden.inf fun s=>(cone s)ᶜ) :ℚ) =
      (aAp block forbidden t:ℚ) := by
    rw [havoid]
    exact oz (fun n:ℕ=>(n:ℚ))
      (cNp block t (fun e => ∀ s∈forbidden,¬ s≤e))
  have hie :=oz (Int.cast:ℤ→ℚ)
    (inclusion_exclusion_card_inf_compl forbidden cone)
  push_cast at hie
  simp only [P,pG,ov,MvPolynomial.eval_C,Aa]
  rw [← hcard,hie]
  refine qm rfl fun U hU => ?_
  have hshift (l:Fin 3) :Kn block (U.sup id) l≤t l:= by
    exact (degree_mono block (sup_mono (mem_powerset.mp hU)) l).trans
      ((le_sup (f :=Kn block (forbidden.sup id)) (vh l)).trans (ht l))
  congr 1
  rw [hinter,show #(cone (U.sup id)) =
      Nat.card {e :σ →₀ ℕ // Kn block e=t∧U.sup id≤e} from
        cNp block t _,
    J4 (coneEquiv block (U.sup id) t hshift),d3F block hblock _]
  push_cast
  exact prod_congr rfl fun l _=>d1U t l _ _ (hshift l)
end
end cyg
end
section
namespace agL
noncomputable section
open aR dN
theorem aD7 {f Q:lI} {p:lz lI}
  (hf :f≠0) (hrel :z9 f Q) (hp: (lJ {f,Q}).IsMinimalPrime p) :
  p.height=2 := by
 let _:p.IsPrime :=hp.isPrime
 have hcount: ({f,Q} : Set lI).ncard≤2 :=
  (Set.ncard_insert_le _ _).trans (by simp)
 have hupper :p.height≤2 :=
  (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hcount)
 have hfmem:f∈p:=hp.le (qx (by simp))
 have hQmem:Q∈p:=hp.le (qx (by simp))
 have hpbot:p ≠ ⊥ := fun h=>hf (Ideal.mem_bot.mp (h ▸ hfmem))
 have hone :1≤p.height:= by
  have h:=Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpbot)
  simpa [Ideal.height_bot] using h
 have hnot:p.height≠1 := by
  intro h
  obtain ⟨z,hz⟩:=(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h).principal
  change p=lJ {z} at hz
  have hzf :z∣f :=Ideal.mem_span_singleton.mp (hz ▸ hfmem)
  have hzQ:z∣Q:=Ideal.mem_span_singleton.mp (hz ▸ hQmem)
  exact hp.isPrime.ne_top (hz.trans (Ideal.span_singleton_eq_top.mpr (hrel hzf hzQ)))
 exact le_antisymm hupper ((ENat.add_one_le_iff (by simp : (1 :ℕ∞) ≠ ⊤)).mpr
  (Kz  hone (Ne.symm hnot)))
private theorem evJ {R:Type*} [n5 R] [MO R] [IsNoetherianRing R]
    {x y :R} {n:ℕ} (hx :x∈oK R)
    (hh:1<(oK R).height)
    (hy :y∈oK R^n) :
    (n:ℕ∞)≤pC R (R ⧸ lJ {x,y}) := by
  let m:=oK R
  let A:lz R:=lJ {x}
  have hno (i:ℕ) : ¬ m^i≤A:= by
    intro h
    have hmin:m∈A.minimalPrimes := by
      refine ⟨⟨vj,(Dz m).mpr hx⟩,?_⟩
      intro P hP _
      exact fun z hz=>hP.1.mem_of_pow_mem i (hP.2 (h (NZ hz i)))
    let _:A.IsPrincipal:=⟨⟨x,rfl⟩⟩
    exact (not_le_of_gt hh)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  let I (i:ℕ) :lz R:=A ⊔ m^i
  have hstep (i:ℕ) :I (i+1)<I i:= by
    refine Kz (sup_le_sup_left (LO (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m^i≤A ⊔ m•m^i
      rw [smul_eq_mul,← vk]
      change m^i≤I (i+1)
      rw [he]
      exact le_sup_right
  have hcoheight (i:ℕ) : (i:ℕ∞)≤zd (I i:t3 R R) := by
    induction i with
    | zero=>simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (I (i+1) :t3 R R)<I i from hstep i))
  rw [Kp]
  apply (hcoheight n).trans
  apply Sv
  apply Ideal.span_le.mpr
  simp only [Oc,Set.singleton_subset_iff]
  exact ⟨Qx (EK x),G5 hy⟩
theorem bc1 {f Q:af 4} {p:lz lI} [p.IsPrime] {n:ℕ}
   (hheight:p.height=2)
   (hfp:bC f∈p) (hQ:afc p (bC Q) n) :
   (n:ℕ∞)≤oA (kC f Q) p ‹p.IsPrime› := by
 let L:=oy p
 let φ:=aU lI L
 have hheight' : (oK L).height=2 := by
   apply WithBot.coe_injective
   rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
     IsLocalization.AtPrime.ringKrullDim_eq_height p L,hheight]
 have hf :φ (bC f)∈oK L :=
   (Sd L p _).mpr hfp
 have hmap : (kC f Q).map φ =
     lJ {φ (bC f),φ (bC Q)} := by
   rw [kC,sS ,vH,uh]
 change (n:ℕ∞)≤pC L (L ⧸ (kC f Q).map φ)
 rw [hmap]
 exact evJ hf (hheight' ▸ (by decide : (1 :ℕ∞)<2)) hQ
end
end agL
end
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 160000
namespace aY2
noncomputable section
open aR dN BO GJ ap7
open MvPolynomial
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem quotient_isLocalization {A B:Type*} [n5 A] [n5 B]
    [oj A B] (M:G0 A) [xL M B] (I:lz A)
    (J' : lz B) (hJ:I.map (aU A B)=J') :
    let f :=HZ J' (aU A B) (Ideal.map_le_iff_le_comap.mp hJ.le)
    letI:=f.toAlgebra
    xL (M.map (nX I)) (B ⧸ J') := by
  subst J'
  dsimp only
  let J:=I.map (aU A B)
  let f :A ⧸ I →+* B ⧸ J :=
    HZ J (aU A B) Ideal.le_comap_map
  let _:=f.toAlgebra
  change xL (M.map (nX I)) (B ⧸ J)
  have hm (m:M) :nX I m∈M.map (nX I) :=
    Submonoid.mem_map_of_mem _ m.property
  refine (isLocalization_iff (M.map (nX I)) (B ⧸ J)).2 ⟨?_,?_,?_⟩
  · rintro ⟨_,m,hm,rfl⟩
    exact (IsLocalization.map_units B ⟨m,hm⟩).map (nX J)
  · intro z
    obtain ⟨z,rfl⟩:=y5 z
    obtain ⟨⟨r,m⟩,e⟩:=TI M z
    exact ⟨⟨nX I r,⟨nX I m,hm m⟩⟩,
      by
        change nX J z* nX J (aU A B m) =
          nX J (aU A B r)
        simpa only [ov] using oz (nX J) e⟩
  · intro x y e
    obtain ⟨x,rfl⟩:=y5 x
    obtain ⟨y,rfl⟩:=y5 y
    change nX J (aU A B x) =
      nX J (aU A B y) at e
    have he :aU A B (x - y)∈J:= by
      rw [Du,← Ts]
      exact e
    obtain ⟨m,hmM,hmem⟩:=(KA M B I _).mp he
    refine ⟨⟨nX I m,hm ⟨m,hmM⟩⟩,?_⟩
    rw [← ov,← ov,Ts ,← mul_sub]
    exact hmem
private def FT {R σ:Type*} [n5 R] [Kl σ]
    (p q:σ) (hpq:p≠q) (u v :cy {i // i≠p∧i≠q} R) :
    let ι:=rename (R:=R) (NI : {i // i≠p∧i≠q} → σ)
    (cy σ R ⧸ lJ {mD p+ι u,mD q+ι v}) ≃ₐ[R]
      cy {i // i≠p∧i≠q} R:= by
  let Free := {i // i≠p∧i≠q}
  let ι:=rename (R:=R) (NI :Free→σ)
  let I:lz (cy σ R) :=lJ {mD p+ι u,mD q+ι v}
  let value (i:σ) :cy Free R :=
    if h:i≠p∧i≠q then mD ⟨i,h⟩ else if i=p then -u else -v
  let f :cy σ R →ₐ[R] cy Free R:=sH value
  have hι:f.comp ι=C9 R _:= by
    apply VH
    intro i
    change f (ι (mD i))=mD i
    simp [f,ι,value,i.property]
  have hfr (w:cy Free R) :f (ι w)=w:=KH hι w
  have hfp:f (mD p) = -u:= by simp [f,value]
  have hfq:f (mD q) = -v := by simp [f,value,hpq.symm]
  have hI : ∀ x∈I,f x=0:= by
    have H :I≤t7 f.toRingHom:= by
      simp [I,Ideal.span_le,Oc,hfp,hfq,hfr]
    exact fun _ hx=>H hx
  let g:=Ideal.Quotient.liftₐ I f hI
  let j:=u9 R I
  change (cy σ R ⧸ I) ≃ₐ[R] cy Free R
  refine AlgEquiv.ofAlgHom g (j.comp ι) ?_ ?_
  · rw [← Qy ,show g.comp j=f from Ideal.Quotient.liftₐ_comp I f hI]
    exact hι
  · apply Ideal.Quotient.algHom_ext R
    simp only [Qy ,AlgHom.id_comp]
    ext i
    change j (ι (f (mD i)))=j (mD i)
    by_cases hi:i≠p∧i≠q
    · simp [f,value,hi,ι]
    · by_cases hip:i=p
      · subst i
        rw [hfp,map_neg,map_neg]
        have hz :j (mD p+ι u)=0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (qx (by simp))
        exact (SW (by simpa only [oY] using hz)).symm
      · have hiq:i=q:= by
          by_contra hn
          exact hi ⟨hip,hn⟩
        subst i
        rw [hfq,map_neg,map_neg]
        have hz :j (mD q+ι v)=0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (qx (by simp))
        exact (SW (by simpa only [oY] using hz)).symm
abbrev i9 (a h:c9) :lz (ae9 a h) :=
 lJ {a4d a h,a8j a h}
def ajd (a h:c9) :Type :=ae9 a h ⧸ i9 a h
instance (a h:c9) :n5 (ajd a h) :=
 inferInstanceAs (n5 (ae9 a h ⧸ i9 a h))
instance (a h:c9) :oj (VM a h) (ajd a h) :=
 inferInstanceAs (oj (VM a h) (ae9 a h ⧸ i9 a h))
instance (a h:c9) :oj lI (ajd a h) :=
 inferInstanceAs (oj lI (ae9 a h ⧸ i9 a h))
def grS (J:lz lI) (a h:c9) :
    (ajd a h ⧸ J.map (aU lI (ajd a h))) ≃ₐ[VM a h]
      axZ J a h:= by
  let F:=VM a h
  let L:=J.map (EG a h)
  let proj:ae9 a h →+* ajd a h:=nX (i9 a h)
  have hmap :J.map (aU lI (ajd a h))=L.map proj:= by
    rw [t4]
    rfl
  have e : (ajd a h ⧸ L.map proj) ≃ₐ[F] (ae9 a h ⧸ (i9 a h ⊔ L)) :=
    DoubleQuot.quotQuotEquivQuotSupₐ F (i9 a h) L
  exact (OJ F hmap).trans
    (e.trans (OJ F (sup_comm _ _)))
private def aYn (b:c9) :uL b:= fun _=>0
private abbrev jo (a h:c9) :=cy (aav a h) lV
private abbrev bzk (a h:c9) :=cy (Fin 4) (jo a h)
private def a4J {σ:Type*} (p:c9) (ι:uL p→σ) :
   cy (Fin 4) (cy σ lV) :=
 ∑ m∈Bz p,C (mD (ι m)) * ∏ i:Fin 4,mD i^(m i).val
private abbrev bq1 (a h:c9) :lz (bzk a h) :=
 lJ {a4J a Sum.inl,a4J h Sum.inr}
private theorem dMa (a h:c9) :
    u5 lI (bzk a h ⧸ bq1 a h) := by
  classical
  let σ:=aav a h
  let p:σ:=Sum.inl (aYn a)
  let q:σ:=Sum.inr (aYn h)
  have hpq:p≠q:=Sum.inl_ne_inr
  let Free := {i:σ // i≠p∧i≠q}
  let ι:=rename (R:=lI) (NI :Free→σ)
  let e :bzk a h ≃ₐ[lI] cy σ GeoJets :=
    AlgEquiv.ofRingEquiv (f :=(commAlgEquiv lV (Fin 4) σ).toRingEquiv) (by
      intro r
      have he : (commAlgEquiv lV (Fin 4) σ).toRingHom.comp
          (nq (C:lV →+* jo a h))=C:= by
        apply wR
        · intro c
          simp
        · intro i
          simp
      exact MK he r)
  have decompose (b:c9) (i:uL b→σ)
      (hi : ∀ m,m≠aYn b→i m≠p∧i m≠q) :
      ∃ u:cy Free lI,e (a4J b i)=mD (i (aYn b))+ι u:= by
    let value :σ→cy Free GeoJets :=
      fun j=>if hj:j≠p∧j≠q then mD ⟨j,hj⟩ else 0
    let rem:cy σ GeoJets :=
      ∑ m∈(Bz b).erase (aYn b),mD (i m)*C (∏ j:Fin 4,mD j^(m j).val)
    refine ⟨sH value rem,?_⟩
    have he (m:uL b) :
        e (C (mD (i m)) * ∏ j:Fin 4,mD j^(m j).val) =
          mD (i m)*C (∏ j:Fin 4,mD j^(m j).val) := by
      change commAlgEquiv lV (Fin 4) σ
        (C (mD (i m)) * ∏ j:Fin 4,mD j^(m j).val)= _
      simp
    have hz :aYn b∈Bz b:= by
      simp [Bz,aYn]
    simp only [a4J,pG,he]
    rw [← Ww _ _ hz,yL]
    have hrem:ι (sH value rem)=rem:= by
      simp only [rem,pG,ov,yJ,aeval_C,v9]
      exact qm rfl fun m hm=> by
        simp [ι,value,hi m (Finset.mem_erase.mp hm).1]
    rw [hrem]
    simp [aYn,rem]
  obtain ⟨u,hu⟩:=decompose a Sum.inl fun m hm =>
    ⟨fun he=>hm (Sum.inl.inj he),Sum.inl_ne_inr⟩
  obtain ⟨v,hv⟩:=decompose h Sum.inr fun m hm =>
    ⟨Sum.inr_ne_inl,fun he=>hm (Sum.inr.inj he)⟩
  have hI:lJ {mD p+ι u,mD q+ι v} = (bq1 a h).map e.toRingHom:= by
    simp [bq1,sS ,vH,uh,hu,hv,p,q]
  exact Module.Flat.of_linearEquiv
    (((Ideal.quotientEquivAlg _ _ e hI).trans (FT p q hpq u v)).toLinearEquiv)
theorem gG5 (a h:c9) :u5 lI (ajd a h) := by
  let A:=bzk a h
  let B:=ae9 a h
  let I:=bq1 a h
  let M:G0 A:=(C5 (jo a h)).map C
  have hloc:xL M B :=
    Pr _ (VM a h)
  have hsec (p:c9) (i:uL p→aav a h) :
      aU A B (a4J p i)=Uq p i:= by
    change nq (aU (jo a h) (VM a h))
      (a4J p i)= _
    simp only [a4J,Uq,pG,ov,Aa ,uW,
      MvPolynomial.map_C,MvPolynomial.map_X]
  have hI:I.map (aU A B)=i9 a h:= by
    simp only [I,bq1,sS ,vH,uh,hsec] <;> rfl
  let f : (A ⧸ I) →+* ajd a h :=
    HZ (i9 a h) (aU A B) (Ideal.map_le_iff_le_comap.mp hI.le)
  let _ := @RingHom.toAlgebra (A ⧸ I) (ajd a h) _ _ f
  let mkI:A →+* (A ⧸ I) :=nX I
  let M' : G0 (A ⧸ I) :=M.map mkI
  have hlocal:xL (R:=A ⧸ I) M' (ajd a h) := by
    have hl:=quotient_isLocalization M I (i9 a h) hI
    dsimp only at hl
    exact hl
  have hflat :=dMa a h
  have hflat' : u5 (A ⧸ I) (ajd a h) :=
    IsLocalization.flat (R:=A ⧸ I) _ M'
  have htower :zf lI (A ⧸ I) (ajd a h) := by
    refine IsScalarTower.of_algebraMap_eq (R:=lI) (S:=A ⧸ I)
      (A:=ajd a h) fun r => ?_
    change nX (i9 a h) (EG a h r) =
      f (nX I (nq C r))
    have he :EG a h r=aU A B (nq C r) := by
      change nq (aU lV (VM a h)) r =
        nq (aU (jo a h) (VM a h)) (nq C r)
      rw [t6 lV (jo a h) (VM a h),
        zm,v9]
    exact oz (nX (i9 a h)) he
  exact Module.Flat.trans lI (A ⧸ I) (ajd a h)
end
end aY2
end
section
namespace cyb
noncomputable section
open aR lB E6 ap6 MvPolynomial
open scoped Pointwise
variable {k :Type*} [oq k]
private abbrev ZA (a h:c9) (d:ℕ×ℕ) :Shape :=
 (a.scale d.1).plus (h.scale d.2)
private theorem dVj (a h:c9) (d e :ℕ×ℕ) :
  ZA a h (d+e)=(ZA a h d).plus (ZA a h e) := by
 cases a
 cases h
 simp [ZA,pQ,pU,z7,add_assoc,add_left_comm]
private theorem bOi {a h:c9} (ha :bF a) (hh:bF h)
   (d e :ℕ×ℕ) {m:Fin 4 →₀ ℕ}
   (hm:m∈nE (ZA a h (d+e))) :
   ∃ u∈nE (ZA a h d),
     ∃ v∈nE (ZA a h e),u+v=m:= by
 rw [dVj,a44
   (Nc (BP ha d.1) (BP hh d.2))
   (Nc (BP ha e.1) (BP hh e.2))] at hm
 exact hm
private theorem d5j {a h:c9} {m:Fin 4 →₀ ℕ}
  (hm:m∈nE (ZA a h 0)) :m=0:= by
 have hzero :ZA a h 0=⟨0,0,0⟩:= by
  simp [ZA,pQ,pU]
 rw [hzero] at hm
 have he : (fun i=>m i)∈rU ⟨0,0,0⟩:=hm
 rw [bFF,Set.mem_singleton_iff] at he
 ext i
 exact yB he i
private abbrev aDI (I:lz (cy (Fin 4) k)) (a h:c9)
  (d:ℕ×ℕ) (m:Fin 4 →₀ ℕ) (hm:m∈nE (ZA a h d)) :
  yH I a h :=
 G6 d (nX I (oZ m 1)) (bJw hm 1)
private theorem ewo (I:lz (cy (Fin 4) k)) (a h:c9)
  (hm: (0:Fin 4 →₀ ℕ)∈nE (ZA a h 0)) :
  aDI I a h 0 0 hm=1 := by
 apply (show t9 (yH I a h).val from G7)
 rw [show (yH I a h).val 1=AddMonoidAlgebra.single 0 1 from rfl]
 simp only [aDI,aJW,monomial_zero',map_one]
private theorem bIt (I:lz (cy (Fin 4) k)) (a h:c9)
   (d e :ℕ×ℕ) {u v :Fin 4 →₀ ℕ}
   (hu:u∈nE (ZA a h d))
   (hv :v∈nE (ZA a h e))
   (huv :u+v∈nE (ZA a h (d+e))) :
   aDI I a h (d+e) (u+v) huv =
     aDI I a h d u hu*aDI I a h e v hv := by
 apply (show t9 (yH I a h).val from G7)
 simp only [ov,aDI,aJW,AddMonoidAlgebra.single_mul_single]
 rw [← ov,monomial_mul_monomial,mul_one]
private theorem cUR (I:lz (cy (Fin 4) k)) (a h:c9)
  (d:ℕ×ℕ) (S:t3 k (yH I a h))
  (hmon : ∀ m hm,aDI I a h d m hm∈S)
  (x :Affine I) (hx :x∈box I a h d) :
  G6 d x hx∈S:= by
 obtain ⟨p,hp,rfl⟩:=hx
 let f :cy (Fin 4) k →ₗ[k] AddMonoidAlgebra (Affine I) (ℕ×ℕ) :=
  (AddMonoidAlgebra.lsingle d).comp (u9 k I).toLinearMap
 let v :=(yH I a h).val.toLinearMap
 have hle :t5 k (nE (ZA a h d))≤(S.map v).comap f := by
  rw [Kv]
  apply Submodule.span_le.mpr
  rintro _ ⟨m,hm,rfl⟩
  exact ⟨aDI I a h d m hm,hmon m hm,rfl⟩
 obtain ⟨r,hr,heq⟩:=hle hp
 have heq' : r=G6 d (nX I p) ⟨p,hp,rfl⟩ :=
  G7 heq
 exact heq' ▸ hr
private def ayt (I:lz (cy (Fin 4) k)) (a h:c9) :
  cy (nE a ⊕ nE h) k →ₐ[k] yH I a h :=
 sH (Sum.elim (aaX I a h) (abh I a h))
private theorem evd (I:lz (cy (Fin 4) k)) (a h:c9)
   (m:nE a) :aaX I a h m∈(ayt I a h).range :=
 ⟨mD (.inl m),by simp [ayt]⟩
private theorem fXw (I:lz (cy (Fin 4) k)) (a h:c9)
   (m:nE h) :abh I a h m∈(ayt I a h).range :=
 ⟨mD (.inr m),by simp [ayt]⟩
private theorem ewn (I:lz (cy (Fin 4) k))
    (a h:c9) (ha :bF a) (hh:bF h) (i j:ℕ) (m:Fin 4 →₀ ℕ)
    (hm:m∈nE (ZA a h (i,j))) :
    aDI I a h (i,j) m hm∈(ayt I a h).range := by
  induction i generalizing m with
  | zero =>
    induction j generalizing m with
    | zero =>
      obtain rfl :=d5j hm
      exact (ewo I a h hm).symm ▸ (ayt I a h).range.one_mem
    | succ j ih =>
      obtain ⟨u,hu,v,hv,rfl⟩:=bOi ha hh (0,j) (0,1) hm
      have hv' : v∈nE h:= by simpa only [ZA,a7U] using hv
      exact (bIt I a h (0,j) (0,1) hu hv hm).symm ▸
        (ayt I a h).range.mul_mem (ih u hu) (fXw I a h ⟨v,hv'⟩)
  | succ i ih =>
    obtain ⟨u,hu,v,hv,rfl⟩:=bOi ha hh (i,j) (1,0) hm
    have hv' : v∈nE a := by simpa only [ZA,a5e] using hv
    exact (bIt I a h (i,j) (1,0) hu hv hm).symm ▸
      (ayt I a h).range.mul_mem (ih u hu) (evd I a h ⟨v,hv'⟩)
private theorem fVk (I:lz (cy (Fin 4) k))
  (a h:c9) (ha :bF a) (hh:bF h) :IsNoetherianRing (yH I a h) := by
 classical
 apply isNoetherianRing_of_surjective _ _ (ayt I a h).toRingHom
 intro p
 change p∈(ayt I a h).range
 have hp:p = ∑ d∈p.val.coeff.support,G6 d (p.val.coeff d) (p.property d) := by
  apply (show t9 (yH I a h).val from G7)
  simp only [pG,aJW]
  exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
 rw [hp]
 apply (ayt I a h).range.sum_mem
 intro d _
 exact cUR I a h d (ayt I a h).range.toSubmodule
  (ewn I a h ha hh d.1 d.2) _ _
private theorem ewl (I:lz (cy (Fin 4) k))
  (a h:c9) (ha :bF a) (hh:bF h) (m:Fin 4 →₀ ℕ)
  (hm:m∈nE (ZA a h (1,1))) :
  aDI I a h (1,1) m hm∈irrelevant I a h:= by
 obtain ⟨u,hu,v,hv,rfl⟩:=bOi ha hh (1,0) (0,1) hm
 have hu' : u∈nE a := by simpa only [ZA,a5e] using hu
 have hv' : v∈nE h:= by simpa only [ZA,a7U] using hv
 exact (bIt I a h (1,0) (0,1) hu hv hm).symm ▸
  qx (s :=oD (Wi I a h)) ⟨(⟨u,hu'⟩,⟨v,hv'⟩),rfl⟩
private theorem ewm (I:lz (cy (Fin 4) k))
    (a h:c9) (ha :bF a) (hh:bF h) (i j:ℕ) (m:Fin 4 →₀ ℕ)
    (hm:m∈nE (ZA a h (i,j))) (n:ℕ) (hi:n≤ i) (hj:n≤j) :
    aDI I a h (i,j) m hm∈irrelevant I a h^n:= by
  induction n generalizing i j m with
  | zero=>rw [Submodule.pow_zero,Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    cases i with
    | zero=>omega
    | succ i =>
      cases j with
      | zero=>omega
      | succ j =>
        obtain ⟨u,hu,v,hv,rfl⟩:=bOi ha hh (i,j) (1,1) hm
        rw [Submodule.pow_succ]
        exact (bIt I a h (i,j) (1,1) hu hv hm).symm ▸
          Ideal.mul_mem_mul (ih i j u hu (by omega) (by omega))
            (ewl I a h ha hh v hv)
theorem proof :ap6.c1 := by
 intro k _ I a h ha hh
 refine ⟨fVk I a h ha hh,?_⟩
 intro i j x hx n hi hj
 exact cUR I a h (i,j) ((irrelevant I a h^n).restrictScalars k)
  (fun m hm=>ewm I a h ha hh i j m hm n hi hj) x hx
end
end cyb
end
section
namespace aKo
noncomputable section
open aR UH MvPolynomial
open scoped TensorProduct
section GD
variable {k :Type} [oq k] (P:Fin 4→c9) (f :Fin 4→ gQ k)
private abbrev rS:=Σ i:Fin 4,nI (P i)
private def center (a :rS P) :k :=
 (f a.1).coeff a.2.1
private def aCF (a :rS P) :sI (fZ k P) :=
 uz (aU k (fZ k P) (center P f a)) +
  II*uz
   (aU (xB k P) (fZ k P) (mD a))
def ahx (i:Fin 4) :abG.Total (fZ k P) := by
 classical
 letI:=(afS (P i)).fintype
 exact ∑ e :nI (P i),oZ e.val (aCF P f ⟨i,e⟩)
private def ajl:xB k P →+* sI (fZ k P) :=
 z8 (Polynomial.C.comp (aU k (fZ k P))) (aCF P f)
private theorem bXC:t9 (ajl P f) := by
  let shift:xB k P →ₐ[k] xB k P :=
    sH fun a=>C (center P f a)+MvPolynomial.X a
  let unshift:xB k P →ₐ[k] xB k P :=
    sH fun a=>mD a - C (center P f a)
  have hshift:unshift.comp shift=C9 k _:= by
    apply VH
    intro a
    simp [shift,unshift,v9]
  have hleft:Pv unshift shift:= fun p=>KH hshift p
  have heval : (Mj 1).comp (ajl P f) =
      (aU (xB k P) (fZ k P)).comp shift.toRingHom:= by
    apply wR
    · intro c
      change Polynomial.eval 1 (ajl P f (C c)) =
        aU (xB k P) (fZ k P) (shift (C c))
      rw [ajl,eval₂Hom_C,yl,JQ,algHom_C]
      exact FR k (xB k P) (fZ k P) c
    · intro a
      change Polynomial.eval 1 (ajl P f (mD a)) =
        aU (xB k P) (fZ k P)
          (sH (fun b=>C (center P f b)+MvPolynomial.X b) (mD a))
      rw [ajl,MvPolynomial.eval₂Hom_X',yJ]
      simp only [aCF,Wm,S2 ,JQ,
        Pf ,one_mul,oY]
      rw [FR k (xB k P) (fZ k P)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply Ea (xB k P) (fZ k P)
  exact (xI heval p).symm.trans
    ((oz (Mj 1) hpq).trans (xI heval q))
open abG in
private def aNZ:fZ k P →+* sU (fZ k P) :=
 IsFractionRing.lift (g:=(aU (sI (fZ k P))
    (sU (fZ k P))).comp (ajl P f))
  ((Ea (sI (fZ k P)) (sU (fZ k P))).comp
    (bXC P f))
open abG in
private theorem b4z (a :rS P) :
    aNZ P f (aU (xB k P) (fZ k P) (mD a)) =
      aU (sI (fZ k P)) (sU (fZ k P))
        (aCF P f a) := by
  rw [aNZ,IsFractionRing.lift_algebraMap]
  simp [ajl]
open abG in
theorem bZ0
   (hs : ∀ i,(↑(f i).support :Set zR)⊆nI (P i)) (i:Fin 4) :
   reduce (ahx P f i) =
     nq (aU k (fZ k P)) (f i) := by
 classical
 let:=(afS (P i)).fintype
 ext e
 simp only [ahx,reduce,pG,map_monomial,Gn,ze,zh,
   aCF,Polynomial.coe_evalRingHom,Wm,JQ,
   S2 ,Pf ,zero_mul,add_zero,center]
 by_cases he :e∈nI (P i)
 · rw [Up (⟨e,he⟩:nI (P i))]
   · simp
   · intro a _ ha
     have hne :a.val≠e := fun h=>ha (qM h)
     simp [hne]
   · simp
 · have hcoeff : (f i).coeff e=0 :=
     notMem_support_iff.mp fun h=>he (hs i h)
   rw [hcoeff,qJ]
   apply GF
   intro a _
   have hne :a.val≠e := fun h=>he (h ▸ a.prop)
   simp [hne]
open abG in
theorem bGF {L:Type} [oq L] [oj k L]
   (I:lz (gQ k)) [p7 k (gQ k ⧸ I)] :
   p7 L (gQ L ⧸ I.map (nq (aU k L))) ∧
   pL L (gQ L ⧸ I.map (nq (aU k L))) =
     pL k (gQ k ⧸ I) := by
 let e :=(cC2 (L:=L) I).toLinearEquiv
 exact ⟨Module.Finite.equiv e,e.finrank_eq.symm.trans SU⟩
open abG in
theorem bZZ (hf :p7 (fZ k P) (ap1 k P)) :
    p7 (sU (fZ k P)) (aw3 (ahx P f)) ∧
    pL (sU (fZ k P)) (aw3 (ahx P f)) =
      pL (fZ k P) (ap1 k P) := by
  let:oj (fZ k P) (sU (fZ k P)) :=
    (aNZ P f).toAlgebra
  have hrow (i:Fin 4) :
      nq (aU (fZ k P) (sU (fZ k P)))
          (ve k P i)=bC (ahx P f i) := by
    change nq (aNZ P f) (ve k P i)= _
    simp [ve,bC,ahx,b4z]
  have hid :
      (Su (ve k P)).map
          (nq (aU (fZ k P) (sU (fZ k P)))) =
        (H8 (ahx P f)).map bC:= by
    simp only [Su,H8,sS ,← Set.range_comp',hrow]
  have :=hf
  have hbase :=bGF (L:=sU (fZ k P))
    (Su (ve k P))
  rw [hid] at hbase
  exact hbase
end GD
end
end aKo
end
section
namespace agL
noncomputable section
open Polynomial aR dN
open scoped BigOperators
def Uz {n:ℕ} {A:Type*} [zg A] :
    cy (Fin n) A →+* cy (Fin n) (cy (Fin n) A) :=
  z8 (MvPolynomial.C.comp qU)
    (fun i=>qU (mD i)+MvPolynomial.X i)
private theorem cco {n:ℕ} {A:Type*} [zg A] (i:Fin n) (k :ℕ)
    (f :A) :
    (qU f+MvPolynomial.X i)^k =
      ∑ j∈pz (k+1),oZ (LR i j)
        (f^(k - j)*(k.choose j:A)) := by
  rw [yL,add_pow]
  apply qm rfl
  intro j _
  rw [MvPolynomial.X_pow_eq_monomial,← uW,← MvPolynomial.C_eq_coe_nat,
    vG,← ov,FK,MvPolynomial.C_mul_monomial,mul_one]
private theorem cs6 {n:ℕ} {A:Type*} [zg A]
    (m a :Fin n →₀ ℕ) (c:A) :
    (Uz (oZ m c)).coeff a =
      oZ (m-a) (c * ∏ i:Fin n,((m i).choose (a i) :A)) := by
  classical
  unfold Uz
  rw [Re,Finsupp.prod_pow,yl,
    MvPolynomial.coeff_C_mul]
  simp_rw [cco]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_prod]
  rw [ze]
  simp only [zh]
  have hindex (b:Fin n→ℕ) :
      (∑ i:Fin n,LR i (b i)) =
        Finsupp.equivFunOnFinite.symm b:= by
    simpa using (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm b))
  simp_rw [hindex]
  by_cases ha : ∀ i,a i≤ m i
  · have hmem: (a :Fin n→ℕ)∈Fintype.piFinset (fun i=>pz (m i+1)) :=
      Fintype.mem_piFinset.mpr fun i=>Finset.mem_range_succ_iff.mpr (ha i)
    rw [Finset.sum_eq_single_of_mem (a :Fin n→ℕ) hmem]
    · have hea :Finsupp.equivFunOnFinite.symm (a :Fin n→ℕ)=a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      simp only [hea,↓reduceIte]
      rw [Hw ,Finsupp.prod_pow,ov,Aa ,
        Finset.prod_mul_distrib]
      simp only [RP ,JW]
      ac_rfl
    · intro b _ hb
      have hba :Finsupp.equivFunOnFinite.symm b≠a := by
        intro h
        exact hb (by simpa using oz (fun x :Fin n →₀ ℕ=>(x :Fin n→ℕ)) h)
      simp [hba]
  · push Not at ha
    obtain ⟨i,hi⟩:=ha
    have hzero : (∏ k :Fin n,((m k).choose (a k) :A))=0 :=
      Finset.prod_eq_zero (vh i) (by simp [Nat.choose_eq_zero_of_lt hi])
    rw [hzero,th,qJ]
    suffices (∑ b∈Fintype.piFinset (fun i=>pz (m i+1)),
        if Finsupp.equivFunOnFinite.symm b=a then
          ∏ i:Fin n,(mD i:cy (Fin n) A)^(m i - b i) *
            ((m i).choose (b i) :cy (Fin n) A) else 0)=0 by
      rw [this,th]
    apply GF
    intro b hb
    have hn:Finsupp.equivFunOnFinite.symm b≠a := by
      intro h
      have hbi:=Fintype.mem_piFinset.mp hb i
      have he :b i=a i:= by
        simpa using oz (fun x :Fin n →₀ ℕ=>x i) h
      exact (not_lt_of_ge (Finset.mem_range_succ_iff.mp (he ▸ hbi))) hi
    simp [hn]
theorem taylor_coeff {n:ℕ} {A:Type*} [zg A] (F:cy (Fin n) A)
  (a :Fin n →₀ ℕ) : (Uz F).coeff a=BV a F:= by
 unfold BV
 conv_lhs=>rw [Mk F,pG,ze]
 exact qm rfl fun m _=>cs6 m a (F.coeff m)
theorem bft {n:ℕ} {A B:Type*} [zg A] [zg B]
  (φ:A →+* B) (a :Fin n →₀ ℕ) (P:cy (Fin n) A) :
  nq φ (BV a P)=BV a (nq φ P) := by
 have h: (nq (nq φ)).comp (Uz (n:=n)) =
    (Uz (A:=B)).comp (nq φ) := by
  apply wR <;> intro i <;> simp [Uz]
 have hc:=oz (fun F:cy (Fin n) (cy (Fin n) B)=>F.coeff a)
  (xI h P)
 simpa only [yl,Gn,taylor_coeff] using hc
theorem duA {n:ℕ} (a :Fin n →₀ ℕ) (P:af n) (S:ao[X]) :
   cK (BV a P) S=(Z8 P S).coeff a := by
 let e :af n →+* ao[X] :=ox (jet S)
 let shift:af n →+* af n :=
   z8 qU (fun i=>mD i+MvPolynomial.C (jet S i))
 have h: (nq e).comp Uz=shift:= by
   apply wR
   · intro c
     simp [e,shift,Uz]
   · intro i
     simp [e,shift,Uz,yL]
 change e (BV a P)=(shift P).coeff a
 have hc:=oz (fun F:af n=>F.coeff a) (xI h P)
 simpa only [yl,Gn,taylor_coeff] using hc
private theorem apx {a :Fin 4 →₀ ℕ} {P:af 4} {m:Fin 4 →₀ ℕ}
  (hm:m∈(BV a P).support) : ∃ v∈P.support,m=v-a := by
 classical
 by_contra! h
 apply (MvPolynomial.mem_support_iff.mp hm)
 unfold BV
 rw [ze]
 apply GF
 intro v hv
 simp [zh,Ne.symm (h v hv)]
private theorem dlP (w:Fin 4→ℕ) (v a :Fin 4 →₀ ℕ) :
  (v-a).sum (fun i k=>w i*k)≤v.sum (fun i k=>w i*k) := by
 simp only [zE _ _ (fun _=>Nat.mul_zero _)]
 exact Finset.sum_le_sum fun i _=>p9 _ (Nat.sub_le _ _)
theorem a4B (a :Fin 4 →₀ ℕ) {P:af 4} {B:c9}
   (hP:aO (p5 P) B) :aO (p5 (BV a P)) B:= by
 refine ⟨?_,?_,?_⟩
 · change (BV a P).totalDegree≤B.b
   apply LP
   intro m hm
   obtain ⟨v,hv,rfl⟩:=apx hm
   exact (by simpa only [one_mul] using dlP (fun _=>1) v a :
     (v-a).sum (fun _ k=>k)≤v.sum (fun _ k=>k)).trans
     ((Bf  hv).trans hP.1)
 · change qE (BV a P)≤B.j
   apply LP
   intro m hm
   obtain ⟨v,hv,rfl⟩:=apx hm
   exact (dlP C4 v a).trans ((Finset.le_sup (f := fun m =>
     m.sum (fun i k=>i.val*k)) hv).trans hP.2.1)
 · change (BV a P).degreeOf 3≤B.t
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro m hm
   obtain ⟨v,hv,rfl⟩:=apx hm
   exact (Nat.sub_le _ _).trans ((MvPolynomial.le_degreeOf_of_mem_support 3 hv).trans hP.2.2)
theorem a4A {n:ℕ} {a :Fin n →₀ ℕ} {P:af n} {S:ao[X]} {l:ℕ}
  (ha :EY a<l) (h:wU P S l) :cK (BV a P) S=0:= by
 rw [duA]
 by_contra hn
 exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hn))
end
end agL
end
section
namespace agL
noncomputable section
open aR dN
def c1 :Prop :=
  ∀ (F G:lI) (p:lz lI) (hp: (lJ {F,G}).IsMinimalPrime p),
    F≠0→ z9 F G →
    oA (lJ {F,G}) p hp.isPrime≤(↑(F.totalDegree*G.totalDegree) :ℕ∞)
def c2 :Prop :=
  ∀ (F:lI) (p:lz lI) [p.IsPrime] (d:ℕ),
    p.height=2 →
    (∀ a :Fin 4 →₀ ℕ,EY a<d→BV a F∈p) →
    afc p F d
end
end agL
end
section
namespace bRn
noncomputable section
open dN agL
open MvPolynomial
open scoped BigOperators
private theorem en1 {n:ℕ} {B:Type*} [n5 B]
  {J:lz B} {d:ℕ} (hJ:J^d = ⊥) {t:Fin n→B} (ht : ∀ i,t i∈J)
  (a :Fin n →₀ ℕ) (ha :d≤EY a) : (a.prod fun i k=>t i^k)=0:= by
 classical
 apply Ideal.mem_bot.mp
 rw [← hJ]
 apply LO ha
 have hp:=Ideal.prod_mem_prod (s :=a.support)
  (I:= fun i=>J^a i) (x := fun i=>t i^a i)
  (fun i _=>NZ (ht i) (a i))
 rw [Finset.prod_pow_eq_pow_sum] at hp
 exact hp
private theorem d2h {K B C:Type*} [n5 K] [n5 B] [n5 C]
    [oj K B] [oj K C] [UP K C] {n:ℕ}
    (φ:cy (Fin n) K →ₐ[K] B) (ρ:B →ₐ[K] C) (hρ:t8 ρ)
    (F:cy (Fin n) K) (d:ℕ) (hJ:t7 ρ.toRingHom^d = ⊥)
    (h : ∀ a :Fin n →₀ ℕ,EY a<d→ρ (φ (BV a F))=0) :
    φ F=0:= by
  classical
  let J:=t7 ρ.toRingHom
  have hnil:IsNilpotent J:=⟨d,hJ⟩
  let s :=Algebra.FormallySmooth.liftOfSurjective (C9 K C) ρ hρ hnil
  have hs (x :C) :ρ (s x)=x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (C9 K C) ρ hρ hnil x
  let r :=ρ.comp φ
  let t (i:Fin n) :B:=φ (mD i) - s (r (mD i))
  have ht (i:Fin n) :t i∈J:= by
    change ρ (φ (mD i) - s (r (mD i)))=0
    rw [Du,hs]
    exact sub_self _
  let ev :cy (Fin n) (cy (Fin n) K) →+* B :=
    z8 (s.toRingHom.comp r.toRingHom) t
  have heval :ev.comp Uz=φ.toRingHom:= by
    apply wR
    · intro c
      simp only [ev,yl,Uz,eval₂Hom_C]
      change s (r (qU c))=φ (qU c)
      rw [← v9,r.commutes,s.commutes,φ.commutes]
    · intro i
      simp [ev,Uz,t]
  have hzero :ev (Uz F)=0:= by
    conv_lhs=>rw [Mk (Uz F),pG]
    apply GF
    intro a _
    have he :ev (oZ a ((Uz F).coeff a)) =
        s (r ((Uz F).coeff a))*(a.prod fun i k=>t i^k) :=
      Re _ _ _ _
    rw [he]
    by_cases ha :EY a<d
    · have hr :r (BV a F)=0:=h a ha
      rw [taylor_coeff,hr,qJ,zero_mul]
    · rw [en1 hJ ht a (le_of_not_gt ha),th]
  exact (xI heval F).symm.trans hzero
private theorem exK {K A:Type*} [n5 K] [n5 A]
   [oj K A] [MO A] [UP K (Df A)]
   {n:ℕ} (loc:cy (Fin n) K →ₐ[K] A) (F:cy (Fin n) K) (d:ℕ)
   (h : ∀ a :Fin n →₀ ℕ,EY a<d→loc (BV a F)∈oK A) :
   loc F∈oK A^d:= by
 by_cases hd:d=0
 · simp [hd,Ideal.one_eq_top]
 let m:=oK A
 have hm:m^d≤ m:=Ideal.pow_le_self hd
 let ρ: (A ⧸ m^d) →ₐ[K] Df A:=Ob K hm
 have hρ:t8 ρ:=Ideal.Quotient.factor_surjective hm
 have hJ:t7 ρ.toRingHom^d = ⊥ := by
   change (t7 (Ideal.Quotient.factor hm))^d = ⊥
   rw [Ideal.Quotient.factor_ker,← Ideal.map_pow,Ideal.map_quotient_self]
 let φ:=(u9 K (m^d)).comp loc
 apply Ideal.Quotient.eq_zero_iff_mem.mp
 refine d2h φ ρ hρ F d hJ fun a ha => ?_
 exact Ideal.Quotient.eq_zero_iff_mem.mpr (h a ha)
theorem gK5 {K:Type*} [oq K] [PerfectField K] {n:ℕ}
  (F:cy (Fin n) K) (p:lz (cy (Fin n) K)) [p.IsPrime]
  (d:ℕ) (h : ∀ a :Fin n →₀ ℕ,EY a<d→BV a F∈p) :
  afc p F d:= by
 let L:=oy p
 have :xm (cy (Fin n) K) L :=
  .of_isLocalization L p.primeCompl
 have :xm K L := .comp K (cy (Fin n) K) L
 have :xm K (Df L) := by
  change xm K (L ⧸ oK L)
  infer_instance
 let loc:cy (Fin n) K →ₐ[K] L:=Pk K _ L
 refine exK loc F d fun a ha => ?_
 change aU (cy (Fin n) K) L (BV a F)∈oK L
 rw [← yo (I:=p)]
 exact Iw _ (h a ha)
theorem proof :agL.c2 := by
 intro F p hp d _ h
 exact gK5 F p d h
end
end bRn
end
section
namespace ap4
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private def arc :List Nat :=[0x1018140e088603220108906030180d0804020110904c30180c06031198d8704020100814322120904c28180c06030180c062331a0d8804020100,0x181c1810090603420108986030188d8804020918904c30180c06031198d8704020100814323120984c28180c06030180c062331a0d8804020100,0x20201810098603420110986030190d8804021118904c30180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100,0x1020201810098603620118986030190d8804021118985030180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100,0x10282418100c0603820118a06030198d8804021918985030180c060321a0d8804020100834423120984c30180c06030180c063331a0d8804020100,0x2030241a110c0644020120a060301a0e0804022120986030180c060321a0d8804020100844423120984c30180c06030180c163331a0d8804020100,0x3030301c120c0644021120c060301a100804022120986030180c061331a0d8804020100844423120984c30180c06030180c164331b0d8804020100,0x30383020120c0684021130c060311a100804122120986030180c062331b0e0804020100844424120985030180c06030180c264341b0d8804020101]
end ap4
end
section
namespace bRO
open cu Finset
open scoped BigOperators
private theorem ddK {M:Type} [AddCommMonoid M]
    (s :Shape) (f :ℕ→ℕ→M) :
    (∑ q∈pz (s.B+1),∑ j∈pz (min q s.J+1),f q j) =
      ∑ j∈pz (s.J+1),∑ q∈Ico j (s.B+1),f q j:= by
  calc
    _ = ∑ q∈pz (s.B+1),∑ j∈pz (s.J+1),
        if j≤q then f q j else 0:= by
      apply qm rfl
      intro q _
      rw [← F9]
      congr 1
      ext j
      simp only [mem_range,Gj,Nat.lt_succ_iff,le_min_iff]
      tauto
    _ = ∑ j∈pz (s.J+1),∑ q∈pz (s.B+1),
        if j≤q then f q j else 0:=sum_comm
    _ = _:= by
      apply qm rfl
      intro j _
      rw [← F9]
      congr 1
      ext q
      simp only [Gj,mem_range,mem_Ico]
      tauto
end bRO
end
section
namespace aqa
noncomputable section
open scoped BigOperators Pointwise
section PowerScaling
variable {R ι:Type*} [n5 R]
abbrev yC (I:lz R) :ℕ∞ := pC R (R ⧸ I)
private theorem eAg {I:lz R} {x y :R} :
   y∈I ⊔ lJ {x} ↔ ∃ z,y - x*z∈I:= by
 rw [Submodule.mem_sup]
 constructor
 · rintro ⟨a,ha,b,hb,rfl⟩
   obtain ⟨z,rfl⟩:=Ideal.mem_span_singleton.mp hb
   exact ⟨z,by simpa using ha⟩
 · rintro ⟨z,hz⟩
   exact ⟨y - x*z,hz,x*z,Ideal.mem_span_singleton.mpr ⟨z,rfl⟩,
     sub_add_cancel _ _⟩
private theorem gtG (I:lz R) (x :R)
    (hreg : ∀ y,x*y∈I→y∈I) (k :ℕ) :
    yC (I ⊔ lJ {x^k})=(k :ℕ∞)*yC (I ⊔ lJ {x}) := by
  let P:ℕ→ lz R:= fun t=>I ⊔ lJ {x^t}
  have hmem (t:ℕ) (y :R) :y∈P t ↔ ∃ z,y - x^t*z∈I :=
    eAg
  have hstep (t:ℕ) (y :R) :x*y∈P (t+1)↔y∈P t:= by
    rw [hmem,hmem]
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨z,hreg _ ?_⟩
      simpa only [vk,mul_sub,vG] using hz
    · rintro ⟨z,hz⟩
      refine ⟨z,?_⟩
      simpa only [vk,mul_sub,vG] using I.mul_mem_left x hz
  have hP1 :P 1=I ⊔ lJ {x} := by simp [P]
  rw [← hP1]
  change yC (P k)=(k :ℕ∞)*yC (P 1)
  induction k with
  | zero =>
    have htop:P 0 = ⊤ := by simp [P]
    rw [htop]
    simp [Module.length_eq_zero]
  | succ k ih =>
    have hmap : (P k :t3 R R) ≤
        Submodule.comap (WW R x) (P (k+1)) :=
      fun y hy=>(hstep k y).2 hy
    have hle :P (k+1)≤P 1 := by
      have hp:lJ {x^(k+1)} ≤ lJ {x^1} := by
        apply (Dz _).mpr
        exact Ideal.mem_span_singleton.mpr ⟨x^k,by simp [vk]⟩
      exact sup_le_sup_left hp _
    let f : (R ⧸ P k) →ₗ[R] (R ⧸ P (k+1)) :=
      (P k).mapQ (P (k+1)) (WW R x) hmap
    let g: (R ⧸ P (k+1)) →ₗ[R] (R ⧸ P 1) :=Eg hle
    have hf :t9 f := by
      rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
      intro y hy
      obtain ⟨r,rfl⟩:=(P k).mkQ_surjective y
      rw [show f ((P k).mkQ r)=(P (k+1)).mkQ (x*r) from rfl,
        v8 ,yU] at hy
      simpa only [v8 ,yU] using (hstep k r).mp hy
    have hex :Function.Exact f g:= by
      intro y
      obtain ⟨r,rfl⟩:=(P (k+1)).mkQ_surjective y
      change (P 1).mkQ r=0 ↔ ∃ t,f t=(P (k+1)).mkQ r
      rw [v8 ,yU,hmem]
      constructor
      · rintro ⟨z,hz⟩
        refine ⟨(P k).mkQ z,?_⟩
        change nX (P (k+1)) (x*z) =
          nX (P (k+1)) r
        have hz' : r - x*z∈I:= by simpa only [pow_one] using hz
        exact (Ideal.Quotient.eq.mpr (Submodule.mem_sup_left hz')).symm
      · rintro ⟨t,ht⟩
        obtain ⟨z,rfl⟩:=(P k).mkQ_surjective t
        change nX (P (k+1)) (x*z) =
          nX (P (k+1)) r at ht
        have hr :r - x*z∈P 1 :=hle (Ideal.Quotient.eq.mp ht.symm)
        obtain ⟨w,hw⟩:=(hmem 1 _).mp hr
        exact ⟨z+w,by simpa only [pow_one,mul_add,sub_sub] using hw⟩
    calc
      yC (P (k+1))=yC (P k)+yC (P 1) :=
        UY f g hf (Gr hle) hex
      _ = _:= by rw [ih,Nat.cast_succ,add_mul,one_mul]
private theorem deU (f :ι→R) (i:ι) :
   lJ (oD f)=K7 f i ⊔ lJ {f i} := by
 classical
 rw [K7,← Ideal.span_union]
 congr 1
 ext x
 constructor
 · rintro ⟨j,rfl⟩
   by_cases h:j=i
   · exact p6 (by simp [h])
   · exact uJ ⟨j,h,rfl⟩
 · rintro (⟨j,_,rfl⟩ | h)
   · exact ⟨j,rfl⟩
   · exact ⟨i,h.symm⟩
theorem c46 {n:ℕ} (f :Fin n→R) (b:Fin n→ℕ) (hb : ∀ i,0<b i)
    (hreg : ∀ (e :Fin n→ℕ),(∀ j,0<e j) → ∀ i y,
      f i*y∈K7 (fun j=>f j^e j) i →
      y∈K7 (fun j=>f j^e j) i) :
    yC (lJ (oD fun i=>f i^b i)) =
      (↑(∏ i,b i) :ℕ∞)*yC (lJ (oD f)) := by
  classical
  let e (s :qy (Fin n)) (j:Fin n) :ℕ:=if j∈s then b j else 1
  let F (s :qy (Fin n)) (j:Fin n) :R:=f j^e s j
  have he (s :qy (Fin n)) : ∀ j,0<e s j:= by
    intro j
    by_cases hj:j∈s <;> simp [e,hj,hb j]
  have hs (s :qy (Fin n)) :
      yC (lJ (oD (F s))) =
        (↑(∏ i∈s,b i) :ℕ∞)*yC (lJ (oD f)) := by
    induction s using Te with
    | empty=>simp [F,e]
    | @insert i s hi ih =>
      have hsame :K7 (F (insert i s)) i=K7 (F s) i:= by
        unfold K7
        congr 1
        exact Set.image_congr fun j hj=> by
          have hji:j≠i:=hj
          simp [F,e,hji]
      have hnew :F (insert i s) i=f i^b i:= by simp [F,e]
      have hold:F s i=f i:= by simp [F,e,hi]
      rw [deU _ i,hsame,hnew,
        gtG _ _ (hreg (e s) (he s) i) (b i),
        ← hold,← deU,ih,MS hi,Ef ,vG]
  simpa [F,e] using hs Finset.univ
theorem cek (f :ι→R) (e :ι→ℕ) (he : ∀ i,0<e i) :
   (lJ (oD fun i=>f i^e i)).radical =
     (lJ (oD f)).radical:= by
 apply GB
 · apply Ideal.radical_mono
   apply Ideal.span_le.mpr
   rintro _ ⟨i,rfl⟩
   have hi:f i∈lJ (oD f) :=qx (Set.mem_range_self i)
   exact Ideal.pow_mem_of_mem _ hi _ (he i)
 · apply (Ideal.radical_le_radical_iff).mpr
   apply Ideal.span_le.mpr
   rintro _ ⟨i,rfl⟩
   exact ⟨e i,qx ⟨i,rfl⟩⟩
end PowerScaling
section PowerLayers
variable {R:Type*} [n5 R]
theorem dNo {I J:lz R} (h:I≤J) :yC J≤yC I :=
 SL (Eg h) (Gr h)
private def monomial {ι:Type*} (f :ι→R) {k :ℕ} (m:Sym ι k) :R :=
 (m.val.map f).prod
private theorem gtv {ι:Type*} (f :ι→R) (k :ℕ) :
   lJ (oD (monomial f (k :=k)))=lJ (oD f)^k := by
 induction k with
 | zero =>
   rw [FV,Ideal.one_eq_top]
   apply (Ideal.eq_top_iff_one _).mpr
   exact qx ⟨Sym.nil,rfl⟩
 | succ k ih =>
   rw [vk,← ih,Ideal.span_mul_span]
   congr 1
   ext x
   constructor
   · rintro ⟨m,rfl⟩
     obtain ⟨i,m,rfl⟩:=m.exists_eq_cons_of_succ
     exact ⟨f i,⟨i,rfl⟩,monomial f m,⟨m,rfl⟩,by simp [monomial,Sym.coe_cons]⟩
   · rintro ⟨_,⟨i,rfl⟩,_,⟨m,rfl⟩,rfl⟩
     exact ⟨Sym.cons i m,by simp [monomial,Sym.coe_cons]⟩
private theorem dNq {n:ℕ} (f :Fin n→R) (k :ℕ) :
    yC (lJ (oD f)^(k+1)) ≤
      yC (lJ (oD f)^k) +
        (n.multichoose k :ℕ∞)*yC (lJ (oD f)) := by
  classical
  let I:=lJ (oD f)
  let A:t3 R R:=I ^(k+1)
  let B:t3 R R:=I ^k
  have hAB:A≤B:=LO (Nat.le_succ k)
  let g: (R ⧸ A) →ₗ[R] (R ⧸ B) :=Eg hAB
  let N :=LinearMap.ker g
  let m:=monomial f (k :=k)
  have hspan:lJ (oD m)=I ^k :=gtv f k
  have hm (u:Sym (Fin n) k) :m u∈I ^k :=hspan ▸ qx ⟨u,rfl⟩
  let v (u:Sym (Fin n) k) :N :=
    ⟨A.mkQ (m u),by
      change B.mkQ (m u)=0
      simpa only [v8 ,yU] using hm u⟩
  let L (u:Sym (Fin n) k) :R ⧸ I →ₗ[R] N :=
    (I:t3 R R).liftQ (LinearMap.id.smulRight (v u)) (by
      intro r hr
      change r•v u=0
      apply qM
      change A.mkQ (r*m u)=0
      rw [v8 ,yU]
      change r*m u∈I ^(k+1)
      rw [vk]
      exact Ideal.mul_mem_mul hr (hm u))
  let e : (Sym (Fin n) k →₀ R ⧸ I) →ₗ[R] N :=Finsupp.lsum R L
  have hsurj:t8 e := by
    have hgen: (I ^k :t3 R R) ≤
        (LinearMap.range (N.subtype.comp e)).comap A.mkQ:= by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨u,rfl⟩
      refine ⟨LR u ((I:t3 R R).mkQ 1),?_⟩
      simp only [LinearMap.comp_apply,e,Finsupp.lsum_single,L,Submodule.liftQ_apply,
        v8 ,LinearMap.smulRight_apply,LinearMap.id_apply,FQ]
      rfl
    intro z
    obtain ⟨r,hr⟩:=A.mkQ_surjective (z :R ⧸ A)
    have hzr :B.mkQ r=0:= by
      have hz :g z=0:=z.property
      simpa only [← hr,g,Submodule.factor_mk] using hz
    have hmem:r∈(I ^k :t3 R R) := by
      simpa only [v8 ,yU] using hzr
    obtain ⟨w,hw⟩:=hgen hmem
    exact ⟨w,qM (hw.trans hr)⟩
  have hlen:=SL e hsurj
  rw [Module.length_finsupp,ENat.card_eq_coe_fintype_card,Sym.card_sym_eq_multichoose,
    Fintype.card_fin] at hlen
  change pC R (R ⧸ A)≤pC R (R ⧸ B)+_
  rw [UY N.subtype g N.subtype_injective
    (Gr hAB) (LinearMap.exact_subtype_ker_map g),yL]
  exact add_le_add_right hlen _
theorem dNp {n:ℕ} (f :Fin n→R) {t:ℕ} (ht:0<t) :
   yC (lJ (oD f)^t) ≤
     ((t+n - 1).choose n:ℕ∞)*yC (lJ (oD f)) := by
 let I:=lJ (oD f)
 have h (k :ℕ) :yC (I ^k) ≤
     (∑ j∈pz k,(n.multichoose j:ℕ∞))*yC I:= by
   induction k with
   | zero=>simp [Module.length_eq_zero]
   | succ k ih =>
     rw [VC,add_mul]
     exact (dNq f k).trans (add_le_add ih vl)
 obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
 simpa only [← Nat.cast_sum,Nat.sum_range_multichoose,
   show k+1+n - 1=k+n by omega] using h (k+1)
end PowerLayers
section GrowthComparison
private theorem ascFactorial_le {n:ℕ} (hn:n=2∨n=3) {t:ℕ} (ht:0<t) :
    t.ascFactorial n≤t^n+5*t^(n - 1) := by
  rcases hn with rfl | rfl
  · calc
      t.ascFactorial 2=t^2+t:= by
        simp only [WK,S1]
        ring
      _≤t^2+5*t^(2 - 1) := by simp only [Nat.reduceSub,pow_one]; omega
  · have h:2*t≤2*t^2 := by
      apply p9
      simpa only [pow_two,Nat.mul_one] using p9 t ht
    calc
      t.ascFactorial 3=t^3+(3*t^2+2*t) := by
        simp only [WK,S1]
        ring
      _≤t^3+(3*t^2+2*t^2) :=zi (zi h _) _
      _=t^3+5*t^(3 - 1) := by ring
private theorem eNv {n:ℕ} (hn:n=2∨n=3) (M C:ℕ)
   (h : ∀ t:ℕ,0<t →
     (M*t+n - 1).choose n≤(t+n - 1).choose n*C) :
   M^n≤C:= by
 by_contra! hc
 let t:=5*C+1
 have ht:0<t:=Np _
 have hnpos :0<n:= by omega
 have hpow:0<t^(n - 1) :=Nat.pow_pos ht
 have hnat : (M*t).ascFactorial n≤C*t.ascFactorial n:= by
   simp only [Nat.ascFactorial_eq_factorial_mul_choose']
   exact (p9 _ (h t ht)).trans_eq (by ac_rfl)
 have hsmall:C*t.ascFactorial n<(C+1)*t^n:= calc
   C*t.ascFactorial n≤C*(t^n+5*t^(n - 1)) :=
     p9 _ (ascFactorial_le hn ht)
   _=C*t^n+(5*C)*t^(n - 1) := by ring
   _<C*t^n+t*t^(n - 1) :=
     Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hpow) _
   _=(C+1)*t^n:= by
     have he :n - 1+1=n:= by omega
     rw [← vk,he,add_mul,one_mul]
 have hlarge : (C+1)*t^n≤(M*t).ascFactorial n:= calc
   (C+1)*t^n≤M^n*t^n:=Nat.mul_le_mul_right _ hc
   _=(M*t)^n:=(mul_pow _ _ _).symm
   _≤(M*t).ascFactorial n:=Nat.pow_succ_le_ascFactorial _ _
 exact (not_lt_of_ge (hlarge.trans hnat)) hsmall
theorem dNn {R:Type*} [n5 R] {n M:ℕ}
   (hn:n=2∨n=3) (m:lz R) (f :Fin n→R)
   (hcontain:lJ (oD f)≤ m^M)
   (hgrow : ∀ t:ℕ,0<t→((t+n - 1).choose n:ℕ∞)≤yC (m^t)) :
   (↑(M^n) :ℕ∞)≤yC (lJ (oD f)) := by
 let I:=lJ (oD f)
 change (↑(M^n) :ℕ∞)≤yC I
 by_cases htop:yC I = ⊤
 · simp [htop]
 let C:=(yC I).toNat
 have hC: (C:ℕ∞)=yC I:=ENat.natCast_toNat htop
 rw [← hC,ENat.natCast_le_natCast]
 by_cases hM:M=0
 · have hn0:n≠0:= by omega
   simp [hM,zero_pow hn0]
 have hMpos :=Rm hM
 apply eNv hn M C
 intro t ht
 have hp:I ^t≤ m^(M*t) :=
   (Ideal.pow_right_mono hcontain t).trans_eq (pow_mul m M t).symm
 have h:=(hgrow (M*t) (GR hMpos ht)).trans
   ((dNo hp).trans (dNp f ht))
 change (↑((M*t+n - 1).choose n) :ℕ∞) ≤
   ↑((t+n - 1).choose n)*yC I at h
 rw [← hC,← ENat.natCast_mul] at h
 exact ENat.natCast_le_natCast.mp h
end GrowthComparison
end
end aqa
end
section
namespace Qt
open cu Finset
def aH3 (k B W j:ℕ) :ℕ :=
 min (B+1) ((W+j)/k+1) - j
end Qt
end
