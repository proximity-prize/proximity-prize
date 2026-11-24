import ProximityPrize.SubmissionLower.ZEe4bHc
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Function.Injective → zq4, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Ideal.height_add_one_le_of_lt_of_isPrime → zSK, Ideal.injective_lift_iff → zFS, Ideal.span → zye, Ideal.span_singleton_prime → zw5, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, IsFractionRing.liftAlgHom → zeU, IsFractionRing.lift_algebraMap → zoc, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, MvPolynomial.algHom_ext → zpH, MvPolynomial.rename → zHw, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.natDegree_C_mul_le → zRn, Polynomial.natDegree_mul_le_of_le → zJZ, Polynomial.natDegree_pow_le_of_le → zxc, PowerSeries → zpm, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.ker → zdq, RingHom.ker_isPrime → zgL, Set.range → zxp
section
namespace q5azJba
noncomputable section
open qQ9yWTb (Curve)


open cu (L)
open scoped WithZero
private theorem arc_kernel {q:Curve} (hq:Irreducible q) (a :Fin 2→zpm L)
   (he :MvPolynomial.eval₂ PowerSeries.C a q=0) {j:Fin 2}
   (hj:z2o 1 (a j)≠0) :
   zdq (zIe a).toRingHom=zye {q} := by
 let f :Curve →+* zpm L:=(zIe a).toRingHom
 let I:Ideal Curve :=zye {q}
 let J:=zdq f
 let P:=zdq ((zbO (R:=L)).comp f)
 have :I.IsPrime :=(zw5 hq.ne_zero).mpr (irreducible_iff_prime.mp hq)
 have :J.IsPrime :=zgL f
 have :P.IsPrime :=zgL ((zbO (R:=L)).comp f)
 have hIJ:I≤J:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr he)
 have hJP:J<P:= by
   apply lt_of_le_of_ne (show J≤P from fun b hb=> by
     change zbO (f b)=0
     rw [RingHom.mem_ker.mp hb,map_zero])
   intro hEq
   let b:Curve :=z9v j-MvPolynomial.C (zbO (a j))
   have hb:b∈P:= by
     change zbO ((zIe a) b)=0
     simp [b]
   have hz :f b=0:=RingHom.mem_ker.mp (hEq.symm ▸ hb:b∈J)
   apply hj
   have hh:=congrArg (z2o 1) hz
   simpa [f,b,PowerSeries.algebraMap_apply,PowerSeries.coeff_C] using hh
 by_contra hn
 have hlt:I<J:=lt_of_le_of_ne hIJ (Ne.symm hn)
 have hI:1≤I.height:=Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
   (mem_nonZeroDivisors_iff_ne_zero.mpr hq.ne_zero)
 have hP: (3:ℕ∞)≤P.height:= calc
   3=1+1+1 := by norm_num
   _≤(I.height+1)+1 := by gcongr
   _≤J.height+1 :=add_le_add_left (zSK hlt) _
   _≤P.height:=zSK hJP
 have hdim:ringKrullDim Curve=2 := by
   rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
   simp
 have hmax :=Ideal.height_le_ringKrullDim_of_isPrime (I:=P)
 rw [hdim] at hmax
 exact (by norm_num : ¬ (3:ℕ∞)≤2) (hP.trans (WithBot.coe_le_coe.mp hmax))
private theorem series_value (b:zpm L) (n:ℕ)
  (h : ∀ m<n,z2o m b=0) (hn:z2o n b≠0) :
  Valued.v (b:LaurentSeries L)=WithZero.exp (-(n:ℤ)) := by
 let z :ℤᵐ⁰:=Valued.v (b:LaurentSeries L)
 have hz :z≠0:=Valuation.ne_zero_iff _ |>.mpr fun he=> by
  have he' : b=0:=HahnSeries.ofPowerSeries_injective (he.trans (map_zero _).symm)
  simp [he'] at hn
 have hle :z≤WithZero.exp (-(n:ℤ)) :=(LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero _ b).mpr h
 have hgt:WithZero.exp (-((n+1 :ℕ) :ℤ))<z :=lt_of_not_ge fun h' =>
  hn ((LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero _ b).mp h' n (Nat.lt_succ_self _))
 exact hle.antisymm ((WithZero.le_log_iff_exp_le hz).mp (by
  have h' := WithZero.lt_log_of_exp_lt hgt
  omega))
theorem arc :q1kuFjb.c2 := by
  intro q hq Cq s hs
  obtain ⟨a,ha,he,j,hj⟩:=hs
  let I:Ideal Curve :=zye {q}
  have :I.IsPrime :=(zw5 hq.ne_zero).mpr (irreducible_iff_prime.mp hq)
  let A:=Curve ⧸ I
  let e :Curve →ₐ[L] Cq.E :=zIe Cq.seed
  let f :Curve →ₐ[L] zpm L:=zIe a
  have he' : zdq e.toRingHom=I:=Cq.equation
  have hf' : zdq f.toRingHom=I:=arc_kernel hq a he hj
  let er :A →ₐ[L] Cq.E :=zTA I e
    (fun _ h=>RingHom.mem_ker.mp (he'.symm ▸ h))
  let fr :A →ₐ[L] zpm L:=zTA I f
    (fun _ h=>RingHom.mem_ker.mp (hf'.symm ▸ h))
  let incl:zpm L →ₐ[L] LaurentSeries L :=
    ⟨HahnSeries.ofPowerSeries ℤ L,fun c=> by
      rw [PowerSeries.algebraMap_apply,Algebra.algebraMap_self,LaurentSeries.algebraMap_apply]
      exact PowerSeries.coe_C _⟩
  let inc:=incl.comp fr
  let F:=FractionRing A
  have her :zq4 er :=(zFS _).mpr he'
  have hfr :zq4 fr :=(zFS _).mpr hf'
  let E :F →ₐ[L] Cq.E :=zeU her
  have hinc:zq4 inc:= fun _ _ h=>hfr (HahnSeries.ofPowerSeries_injective h)
  let B:F →ₐ[L] LaurentSeries L:=zeU hinc
  let seed (i:Fin 2) :=algebraMap A F (zVv I (z9v i))
  have hE (i:Fin 2) :E (seed i)=Cq.seed i:= by
    change zIj (g:=er.toRingHom) her
      (algebraMap A F (zVv I (z9v i)))= _
    rw [zoc]
    exact zTw _ _
  have hB (i:Fin 2) :B (seed i)=(a i:LaurentSeries L) := by
    change zIj (g:=inc.toRingHom) hinc
      (algebraMap A F (zVv I (z9v i)))= _
    rw [zoc]
    exact congrArg incl (zTw _ _)
  have htop:E.fieldRange = ⊤ := by
    apply top_unique
    rw [← Cq.generates,IntermediateField.adjoin_le_iff]
    rintro _ ⟨i,rfl⟩
    exact ⟨seed i,hE i⟩
  let iso:=AlgEquiv.ofBijective E ⟨E.injective,AlgHom.fieldRange_eq_top.mp htop⟩
  let φ:Cq.E →ₐ[L] LaurentSeries L:=B.comp iso.symm.toAlgHom
  have hφ (i:Fin 2) :φ (Cq.seed i)=(a i:LaurentSeries L) := by
    rw [← hE i]
    exact (congrArg B (iso.symm_apply_apply (seed i))).trans (hB i)
  let v :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap φ.toRingHom
  refine ⟨⟨φ,⟨v,?_,?_⟩,fun _=>rfl,⟨a,hφ,ha,j,hj⟩⟩⟩
  · let u:=Cq.seed j-algebraMap L Cq.E (s j)
    have hu:v u=WithZero.exp (-1 :ℤ) := by
      change Valued.v (φ u)= _
      rw [show u=Cq.seed j-algebraMap L Cq.E (s j) from rfl,map_sub,hφ,φ.commutes,
        LaurentSeries.algebraMap_apply,← PowerSeries.coe_C,← PowerSeries.coe_sub]
      exact series_value _ 1 (by intro m hm; interval_cases m; simp [ha j])
        (by simpa [PowerSeries.coeff_C] using hj)
    intro z
    by_cases hz :z=0
    · exact ⟨0,(map_zero v).trans hz.symm⟩
    · refine ⟨u^(-WithZero.log z),?_⟩
      rw [map_zpow₀,hu,← WithZero.exp_zsmul]
      simpa using WithZero.exp_log hz
  · intro c hc
    change Valued.v (φ (algebraMap L Cq.E c))=1
    rw [φ.commutes,LaurentSeries.algebraMap_apply,← PowerSeries.coe_C,← WithZero.exp_zero]
    exact series_value _ 0 (fun _ hm=>(Nat.not_lt_zero _ hm).elim) (by simpa using hc)
end
end q5azJba
end
section
namespace q9Dxm8d
noncomputable section
open MvPolynomial qQ9yWTb qb0hmCe
open cu (L)
open E7
open agN
open scoped Polynomial
section Projection
variable {k E :Type} [Field k] [Field E] [Algebra k E]
private theorem linear_eval_degree {S:Type} [Field S] [Algebra k S]
   (q:z3y (Fin 2) k) (r :Fin 2→S[X])
   (hr : ∀ i,(r i).natDegree≤1) : (zIe r q).natDegree≤q.totalDegree := by
 classical
 conv_lhs=>rw [q.as_sum]
 rw [map_sum]
 refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
 have hd:=le_totalDegree hm
 rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two] at hd
 rw [MvPolynomial.aeval_monomial,Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two,
   IsScalarTower.algebraMap_apply k S S[X],Polynomial.algebraMap_eq]
 refine (zJZ (by simp) ?_:_≤0+(m 0+m 1)).trans ?_
 · exact zJZ
     (by simpa using zxc (m 0) (hr 0))
     (by simpa using zxc (m 1) (hr 1))
 · simpa using hd
private theorem projection_left (q:z3y (Fin 2) k) (hq:q≠0)
    (s :Fin 2→E) (he :zIe s q=0)
    (hg:IntermediateField.adjoin k (zxp s) = ⊤)
    (a b:k) (ha :a≠0)
    (hz :Transcendental k (a•s 0+b•s 1)) :
    let z :=a•s 0+b•s 1
    let S:=IntermediateField.adjoin k {z}
    zAa S E∧zsE S E≤q.totalDegree := by
  classical
  let z :=a•s 0+b•s 1
  let S:=IntermediateField.adjoin k {z}
  let zz :S:=⟨z,IntermediateField.mem_adjoin_simple_self k z⟩
  let w:=s 1
  let g:z3y (Fin 1) k →ₐ[k] S:=zIe fun _=>zz
  have hg' : zq4 g:= by
    let e :=MvPolynomial.uniqueAlgEquiv k (Fin 1)
    have h:S.val.comp g=(zEU z).comp e.toAlgHom:= by
      apply zpH
      intro i
      simp [g,zz,e,MvPolynomial.uniqueAlgEquiv_apply]
    have hinj:zq4 (S.val.comp g) := by
      rw [h]
      exact (transcendental_iff_injective.mp hz).comp e.injective
    exact fun _ _ hab=>hinj (congrArg S.val hab)
  let A:=algebraMap k S a
  let B:=algebraMap k S b
  let r :Fin 2→S[X] :=
    ![z1z A⁻¹*(z1z zz-Polynomial.C B*z7y),z7y]
  let φ:z3y (Fin 2) k →ₐ[k] z3y (Fin 2) k :=
    zIe ![znf a⁻¹*(z9v 1-MvPolynomial.C b*z9v 0),z9v 0]
  let ψ:z3y (Fin 2) k →ₐ[k] z3y (Fin 2) k :=
    zIe ![z9v 1,znf a*z9v 0+MvPolynomial.C b*z9v 1]
  have hψ:ψ.comp φ=AlgHom.id k _:= by
    apply zpH
    intro i
    fin_cases i
    · change ψ (φ (z9v 0))=z9v 0
      simp only [ψ,φ,zTw,Matrix.cons_val_zero,Matrix.cons_val_one,
        map_mul,map_sub,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,add_sub_cancel_right]
      rw [← mul_assoc,← map_mul,inv_mul_cancel₀ ha,map_one,one_mul]
    · simp [ψ,φ]
  have hφ:zq4 φ :=
    (show Function.LeftInverse ψ φ from fun x=>zmU hψ x).injective
  let e :=MvPolynomial.finSuccEquiv k 1
  let f :=Polynomial.mapAlgHom g
  have ex0:e (z9v 0)=Polynomial.X:=MvPolynomial.finSuccEquiv_X_zero
  have ex1 :e (z9v 1)=z1z (z9v 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(0:Fin 1))
  have ec (c:k) :e (znf c)=z1z (znf c) :=e.commutes c
  have hf :f.comp (e.toAlgHom.comp φ)=zIe r := by
    apply zpH
    intro i
    fin_cases i <;> simp [r,f,φ,g,A,B,ex0,ex1,ec]
  let Q:=zIe r q
  have hQ:Q≠0:= by
    have hI:zq4 (zIe r :z3y (Fin 2) k →ₐ[k] S[X]) := by
      rw [← hf]
      exact (Polynomial.map_injective _ hg').comp (e.injective.comp hφ)
    exact fun h=>hq (hI (h.trans (map_zero _).symm))
  have haE :algebraMap k E a≠0:=(map_ne_zero_iff _ (algebraMap k E).injective).2 ha
  have hs : (algebraMap k E a)⁻¹*(z-algebraMap k E b*w)=s 0:= by
    simp [z,w,Algebra.smul_def,haE]
  let v :S[X] →ₐ[k] E :=(zEU w).restrictScalars k
  have huv :v.comp (zIe r)=zIe s := by
    apply zpH
    intro i
    fin_cases i
    · simpa [v,r,zz,A,B,mul_sub,mul_assoc,← IsScalarTower.algebraMap_apply] using hs
    · simp [v,r,w]
  have hroot :zEU w Q=0 :=
    (zmU huv q).trans he
  have hi:IsIntegral S w:=(show IsAlgebraic S w from ⟨Q,hQ,hroot⟩).isIntegral
  let T:=IntermediateField.adjoin S {w}
  have htop:T = ⊤ := by
    apply (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp
    apply eq_top_iff.mpr
    rw [← hg,IntermediateField.adjoin_le_iff]
    rintro _ ⟨i,rfl⟩
    change s i∈T
    have hw:w∈T:=IntermediateField.mem_adjoin_simple_self S w
    fin_cases i
    · change s 0∈T
      rw [← hs]
      exact T.mul_mem (T.inv_mem (T.algebraMap_mem A))
        (T.sub_mem (T.algebraMap_mem zz) (T.mul_mem (T.algebraMap_mem B) hw))
    · exact hw
  have hF:zAa S T:=IntermediateField.adjoin.finiteDimensional hi
  have hd:zsE S T=(minpoly S w).natDegree :=
    IntermediateField.adjoin.finrank hi
  rw [htop] at hF hd
  let:=hF
  refine ⟨Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv,?_⟩
  rw [← IntermediateField.finrank_top',hd]
  refine (Polynomial.natDegree_le_of_dvd (minpoly.dvd S w hroot) hQ).trans ?_
  apply linear_eval_degree
  intro i
  fin_cases i
  · change (z1z A⁻¹*(z1z zz-Polynomial.C B*z7y)).natDegree≤1
    apply (zRn _ _).trans
    refine (Polynomial.natDegree_sub_le_of_le (m:=0) (n:=1) ?_ ?_).trans (by simp)
    · simp
    · exact (zRn B z7y).trans Polynomial.natDegree_X.le
  · simp [r]
private theorem projection (q:z3y (Fin 2) k) (hq:q≠0)
    (s :Fin 2→E) (he :zIe s q=0)
    (hg:IntermediateField.adjoin k (zxp s) = ⊤) (a :Fin 2→k)
    (hz :Transcendental k (O7 a s)) :
    zAa (IntermediateField.adjoin k {O7 a s}) E ∧
      zsE (IntermediateField.adjoin k {O7 a s}) E≤q.totalDegree := by
  have hz' : O7 a s=a 0•s 0+a 1•s 1 := by
    simp [O7,Fin.sum_univ_two]
  rw [hz'] at hz ⊢
  by_cases h0:a 0=0
  · have h1 :a 1≠0:= by
      intro h
      exact hz.ne_zero (by simp [h0,h])
    let e :=Equiv.swap (0:Fin 2) 1
    let u:=s ∘ e
    have hq' : zHw e q≠0 :=
      fun h=>hq ((MvPolynomial.renameEquiv k e).injective (h.trans (map_zero _).symm))
    have hEv : (zIe u).comp (zHw (R:=k) e) =
        MvPolynomial.aeval s := by
      apply zpH
      intro i
      simp [u,e]
    have hgen:IntermediateField.adjoin k (zxp u) = ⊤ := by
      rw [show zxp u=zxp s from e.surjective.range_comp s,hg]
    have hswap:a 1•u 0+a 0•u 1=a 0•s 0+a 1•s 1 := by
      simp [u,e,add_comm,Equiv.swap_apply_left,Equiv.swap_apply_right]
    obtain ⟨hf,hd⟩:=projection_left (zHw e q) hq' u
      ((zmU hEv q).trans he) hgen (a 1) (a 0) h1 (hswap.symm ▸ hz)
    rw [hswap] at hf hd
    exact ⟨hf,hd.trans_eq (MvPolynomial.totalDegree_renameEquiv e q)⟩
  · exact projection_left q hq s he hg _ _ h0 hz
end Projection
private theorem seed_transcendental {E :Type} [Field E] [Algebra L E]
   (q:Curve) (hq:Irreducible q) (s :Fin 2→E)
   (hk :zdq (zIe s).toRingHom=zye {q}) :
   ∃ i,Transcendental L (s i) := by
 classical
 by_contra! h
 have hc (i:Fin 2) : ∃ c:L,algebraMap L E c=s i:= by
   have hi:IsAlgebraic L (s i) :=not_not.mp (h i)
   have :=IntermediateField.isAlgebraic_adjoin_simple hi.isIntegral
   have he :=IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
     (IntermediateField.adjoin L {s i})
   exact IntermediateField.mem_bot.mp (he ▸ IntermediateField.mem_adjoin_simple_self L (s i))
 choose c hc using hc
 let r (i:Fin 2) :Curve :=z9v i - C (c i)
 have hr (i:Fin 2) :r i∈zye {q} := by
   rw [← hk,RingHom.mem_ker]
   simp [r,hc]
 let d:Curve →+* L:=eval ![c 0,c 1 + 1]
 have hd0:d (r 0)=0:= by simp [d,r]
 have hd1 :d (r 1)=1 := by simp [d,r]
 have hn:r 0≠0:= by
   intro h0
   change z9v 0 - C (c 0)=0 at h0
   simpa using congrArg MvPolynomial.totalDegree (sub_eq_zero.mp h0)
 obtain ⟨b,hb⟩:=Ideal.mem_span_singleton.mp (hr 0)
 have hb0:b≠0:= fun h=>hn (by simp [hb,h])
 have hqD:=totalDegree_pos_of_span_singleton_ne_top hq.ne_zero
   (mt Ideal.span_singleton_eq_top.mp hq.not_isUnit)
 have hD:=(totalDegree_sub_C_le (z9v 0:Curve) (c 0)).trans_eq (totalDegree_X _)
 change (r 0).totalDegree≤1 at hD
 rw [hb,totalDegree_mul_of_isDomain hq.ne_zero hb0] at hD
 have hu:IsUnit b:= by
   have hbD:b.totalDegree=0:= by omega
   have hbC:=totalDegree_eq_zero_iff_eq_C.mp hbD
   rw [hbC]
   exact (isUnit_iff_ne_zero.mpr (fun hx=>hb0 (by rw [hbC,hx,map_zero])) :
     IsUnit (b.coeff 0)).map C
 obtain ⟨w,hw⟩:=Ideal.mem_span_singleton.mp (show r 1∈zye {r 0} from by
   rw [hb,Ideal.span_singleton_mul_right_unit hu]
   exact hr 1)
 rw [hw,map_mul,hd0,zero_mul] at hd1
 exact zero_ne_one hd1
theorem proof :q1kuFjb.c1 := by
  classical
  intro q hq
  let I:Ideal Curve :=zye {q}
  let:I.IsPrime :=Ideal.isPrime_span_singleton_of_prime hq.prime
  let A:=Curve ⧸ I
  let E :=FractionRing A
  let j:=IsScalarTower.toAlgHom L A E
  let s (i:Fin 2) :E :=j (zVv I (z9v i))
  have he :zIe s=j.comp (zvR L I) := by
    apply zpH
    intro i
    simp [s]
    rfl
  have hk :zdq (zIe s).toRingHom=I:= by
    ext f
    rw [RingHom.mem_ker,he]
    change algebraMap A E (zVv I f)=0↔f∈I
    rw [map_eq_zero_iff _ (zxb A E),Ideal.Quotient.eq_zero_iff_mem]
  have hg:IntermediateField.adjoin L (zxp s) = ⊤ := by
    have htop: (zvR L I).range = ⊤ :=
      eq_top_iff.mpr fun x _=>(AlgHom.mem_range _).mpr (Ideal.Quotient.mk_surjective x)
    have hr :j.range=Algebra.adjoin L (zxp s) := by
      rw [← MvPolynomial.aeval_range,he,AlgHom.range_comp,htop,Algebra.map_top]
    have h:=IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (f :=AlgHom.id L E) (g:=j) rfl hr
    exact h.symm.trans (AlgHom.fieldRange_eq_top.mpr Function.surjective_id)
  have hqE :zIe s q=0 :=
    RingHom.mem_ker.mp (hk.symm ▸ Ideal.mem_span_singleton_self q)
  obtain ⟨i,hi⟩:=seed_transcendental q hq s hk
  have hS:CurveField L E := by
    let a :Fin 2→L:=Pi.single i 1
    have ha :O7 a s=s i:= by simp [a,O7]
    exact ⟨s i,hi,ha ▸ (projection q hq.ne_zero s hqE hg a (ha.symm ▸ hi)).1⟩
  have hdiv :axV L E :=aFU.of_children
    bRt.proof bRu.proof L E hS
  obtain ⟨a,ha,_⟩:=d4p hdiv s
  have hheight: (∑ᶠ v :CurvePlace L E,poleOrder v.value (O7 a s)) =
      Gb L E s :=finsum_congr ha
  have hz :Transcendental L (O7 a s) :=
    gDD (hheight.symm ▸ ((emC hS hdiv s).1 ⟨i,hi⟩))
  have hb:Gb L E s≤q.totalDegree := by
    rw [← hheight,(hdiv _).2.2.2 hz]
    exact (projection q hq.ne_zero s hqE hg a hz).2
  exact ⟨⟨E,s,hS,hk,hg,fun l =>
    (finsum_le_finsum (hdiv (s l)).1 (b27 hdiv s)
      (fun v=>Finset.le_sup (f := fun i=>poleOrder v.value (s i))
        (Finset.mem_univ l))).trans hb⟩,hb⟩
end
end q9Dxm8d
end
section
namespace qGWTmVd
noncomputable section
open Polynomial Finset q1kuFjb
open scoped Classical
variable {E :Type} [Field E]
theorem b5S {g:E[X][X]} (hg:g≠0) :headScalar g≠0 :=
 leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hg)
theorem head_mul (g h:E[X][X]) :headScalar (g*h)=headScalar g*headScalar h:= by
 change (g*h).leadingCoeff.leadingCoeff= _
 rw [leadingCoeff_mul,leadingCoeff_mul]
 rfl
@[simp] theorem head_C (a :E[X]) :headScalar (C a)=a.leadingCoeff := by
  simp [headScalar]
structure Factorization (g:E[X][X]) where
 amm:E[X]
 monic:amm.Monic
 n:ℕ
 f :Fin n→E[X][X]
 irreducible : ∀ j,Irreducible (f j)
 positive : ∀ j,0<(f j).natDegree
 normalized : ∀ j,headScalar (f j)=1
 product :g=C (C (headScalar g)*amm) * ∏ j,f j
private def normal (g:E[X][X]) :E[X][X] :=g*C (C (headScalar g)⁻¹)
private theorem normal_head {g:E[X][X]} (hg:g≠0) :headScalar (normal g)=1 := by
 rw [normal,head_mul,head_C,leadingCoeff_C,mul_inv_cancel₀ (b5S hg)]
private theorem normal_degree {g:E[X][X]} (hg:g≠0) : (normal g).natDegree=g.natDegree := by
 rw [normal,natDegree_mul hg (C_ne_zero.mpr (C_ne_zero.mpr (inv_ne_zero (b5S hg)))),
  natDegree_C,add_zero]
private theorem denormal {g:E[X][X]} (hg:g≠0) :
  g=C (C (headScalar g))*normal g:= by
 rw [normal,mul_left_comm,
  ← map_mul,← map_mul,mul_inv_cancel₀ (b5S hg),map_one,map_one,mul_one]
private theorem constant {g:E[X][X]} (hg:g≠0) (hd:g.natDegree=0) :
   ∃ P:E[X],P.Monic∧g=C (C (headScalar g)*P) := by
 let P:=g.coeff 0*C (headScalar g)⁻¹
 have hn:normal g=C P:= by
   unfold normal P
   rw [map_mul]
   exact congrArg (· * C (C (headScalar g)⁻¹)) (eq_C_of_natDegree_eq_zero hd)
 refine ⟨P,?_,?_⟩
 · simpa only [hn,head_C,Monic] using normal_head hg
 · calc
     g=C (C (headScalar g))*normal g:=denormal hg
     _ = _:= by rw [hn,← map_mul]
theorem factorize {g:E[X][X]} (hg:g≠0) :Nonempty (Factorization g) := by
  revert hg
  induction g using WfDvdMonoid.induction_on_irreducible with
  | zero=>exact fun h=>(h rfl).elim
  | unit g hu =>
    intro hn
    obtain ⟨P,hm,hp⟩:=constant hn (natDegree_eq_zero_of_isUnit hu)
    exact ⟨⟨P,hm,0,Fin.elim0,fun j=>j.elim0,fun j=>j.elim0,fun j=>j.elim0,
      by simpa using hp⟩⟩
  | mul a i ha hi ih =>
    intro _
    obtain ⟨S⟩:=ih ha
    by_cases hd:i.natDegree=0
    · obtain ⟨P,hm,hp⟩:=constant hi.ne_zero hd
      refine ⟨⟨S.amm*P,S.monic.mul hm,S.n,S.f,S.irreducible,S.positive,S.normalized,?_⟩⟩
      rw [head_mul,map_mul,map_mul (f :=C),map_mul (f :=C)]
      rw [show i*a=C (C (headScalar i)*P) *
        (C (C (headScalar a)*S.amm)*∏ j,S.f j) from congrArg₂ (· * ·) hp S.product]
      simp only [map_mul]
      ac_rfl
    · have hu:IsUnit (C (C (headScalar i)⁻¹) :E[X][X]) :=
        ((isUnit_iff_ne_zero.mpr (inv_ne_zero (b5S hi.ne_zero))).map
          ((C:E[X] →+* E[X][X]).comp (C:E →+* E[X])))
      refine ⟨⟨S.amm,S.monic,S.n+1,Fin.cons (normal i) S.f,
        Fin.cases ((irreducible_mul_isUnit hu).mpr hi) S.irreducible,
        Fin.cases (by simpa only [Fin.cons_zero,normal_degree hi.ne_zero] using
          Nat.pos_of_ne_zero hd) S.positive,
        Fin.cases (normal_head hi.ne_zero) S.normalized,?_⟩⟩
      rw [head_mul,Fin.prod_univ_succ,Fin.cons_zero]
      simp only [Fin.cons_succ,map_mul]
      rw [show i*a=(C (C (headScalar i))*normal i) *
        (C (C (headScalar a)*S.amm)*∏ j,S.f j) from congrArg₂ (· * ·) (denormal hi.ne_zero) S.product]
      simp only [map_mul]
      ac_rfl
theorem Factorization.degree {g:E[X][X]} (S:Factorization g) (hg:g≠0) :
  ∑ j,(S.f j).natDegree=g.natDegree := by
 have hf : ∀ j,S.f j≠0:= fun j=>(S.irreducible j).ne_zero
 have hp: (∏ j,S.f j)≠0:=Finset.prod_ne_zero_iff.mpr fun j _=>hf j
 conv_rhs=>rw [S.product]
 rw [natDegree_mul (C_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (b5S hg)) S.monic.ne_zero))
  hp,natDegree_C,zero_add,natDegree_prod _ _ (fun j _=>hf j)]
end
end qGWTmVd
end
section
namespace qbnx7gb
noncomputable section
open Polynomial qQ9yWTb qb0hmCe
open P5 (K)
open P5_7_1 (Input)
open qFD8jve (Vanishes)
open P5_7_7 (phys)
open cu (L FX)
variable {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C₀:CurveModel q}
private theorem coprime_eval {N D:L[X]} (h:IsCoprime N D) (a :L)
  (hD:D.eval a=0) :N.eval a≠0:= by
 intro hN
 obtain ⟨u,v,huv⟩:=h
 have he :=congrArg (fun f :L[X]=>f.eval a) huv
 simp only [eval_add,eval_mul,hN,hD,mul_zero,zero_add,eval_one,zero_ne_one] at he
private theorem scale {a b u v :L}
   (hab:a≠0∨b≠0) (huv :u≠0∨v≠0) (h:u*b=v*a) :
   ∃ k :L,k≠0∧u=k*a∧v=k*b:= by
 by_cases hb:b=0
 · have ha :=hab.resolve_right (fun hn=>hn hb)
   have hv :v=0:=(mul_eq_zero.mp (by simpa [hb] using h.symm)).resolve_right ha
   exact ⟨u/a,div_ne_zero (huv.resolve_right (fun hn=>hn hv)) ha,(div_mul_cancel₀ _ ha).symm,
     by simp [hv,hb]⟩
 · have hp:u=v/b*a := by
     rw [div_mul_eq_mul_div,eq_div_iff hb]
     exact h
   have hv :v≠0:= by
     intro hz
     exact (huv.resolve_right (fun hn=>hn hz)) (by simp [hp,hz])
   exact ⟨v/b,div_ne_zero hv hb,hp,(div_mul_cancel₀ _ hb).symm⟩
private theorem phys_inj:zq4 phys :=zxb L[X] FX
private theorem reduced_test {N D T:L[X]} {u:L}
    (hD:D ≠0) (hc:IsCoprime N D) (hu:u≠0)
    (hv :Vanishes (phys (C u)*(phys N/phys D)+phys T)) :
    N.coeff 0=0↔T.coeff 0=0:= by
  obtain ⟨A,B,hA,hB,he⟩:=hv
  have hd:=(map_ne_zero_iff phys phys_inj).mpr hD
  have hb:=(map_ne_zero_iff phys phys_inj).mpr (show B≠0 by
    intro h
    exact hB (by simp [h]))
  have hp: (C u*N+T*D)*B=A*D:= by
    apply phys_inj
    simp only [map_mul,map_add]
    apply (div_eq_div_iff hd hb).mp
    simpa only [add_div,mul_div_assoc,mul_div_cancel_right₀ _ hd] using he
  have hh:=congrArg (fun f :L[X]=>f.coeff 0) hp
  simp only [mul_coeff_zero,coeff_add,coeff_C_zero,hA,zero_mul] at hh
  have h:=(mul_eq_zero.mp hh).resolve_right hB
  have hD₀:D.coeff 0≠0:= by
    intro hz
    have hN₀:N.coeff 0≠0:= by
      simpa only [coeff_zero_eq_eval_zero] using
        (coprime_eval hc 0 (by simpa only [coeff_zero_eq_eval_zero] using hz))
    exact hu ((mul_eq_zero.mp (by simpa only [hz,mul_zero,add_zero] using h)).resolve_right hN₀)
  exact ⟨fun hn=>(mul_eq_zero.mp (by simpa [hn] using h)).resolve_right hD₀,
    fun ht=>(mul_eq_zero.mp (by simpa [ht] using h)).resolve_left hu⟩
end
end qbnx7gb
end
