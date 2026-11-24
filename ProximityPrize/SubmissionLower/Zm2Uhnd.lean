import ProximityPrize.SubmissionLower.ZE3M1Qc
import ProximityPrize.SubmissionLower.ZGggfqb
import ProximityPrize.SubmissionLower.ZMyjDge
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Fintype.card → zhP, Ideal.Quotient.mk → zVv, Ideal.quotientMap_mk → z5h, LinearIndependent → z14, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.ringHom_ext → zXT, Nat.mul_le_mul_right → ztf, PowerSeries.C → zMG, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.id → zz4, RingHom.ker → zdq, RingHom.ker_isPrime → zgL, Submodule.add_mem → zcy, Submodule.smul_mem → zc2, Submodule.zero_mem → z4M
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_3_2_1
noncomputable section
open Polynomial TrivSqZeroExt qAjZDhd P5_7_3_3_4_1_3_2
open private aug dualLift lift_on aug_lift from ProximityPrize.SubmissionLower.ZR3mCBd
open scoped WithZero
private theorem cNR {R F S:Type} [za6 R] [IsDomain R] [zrb F]
    [za6 S] [zZE S R] [zZE R F] [IsFractionRing R F] [zZE ℤ F]
    (d:Derivation S R R) :
    ∃ D:Derivation ℤ F F,∀ a,D (algebraMap R F a)=algebraMap R F (d a) := by
  let j:=algebraMap R F
  let f :R →+* TrivSqZeroExt F F :=
    { toFun:= fun a=>⟨j a,j (d a)⟩
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := fun a b=> by ext <;> simp
      map_mul' := fun a b=> by ext <;> simp [smul_eq_mul,mul_comm] }
  have hf : (aug F).comp f=(zz4 F).comp j:= by ext a; rfl
  let g:=dualLift f (zz4 F) hf
  have hg (a :F) : (g a).fst=a :=
    RingHom.congr_fun (aug_lift f (zz4 F) hf) a
  let h:F →+ F:=(sndHom F F).toAddMonoidHom.comp g.toAddMonoidHom
  let D:Derivation ℤ F F :=
    { toFun:=h
      map_add' := h.map_add
      map_smul' := fun n a=> by
        exact (congrArg h (int_smul_eq_zsmul (Algebra.toModule :Module ℤ F) n a)).trans
          (h.map_zsmul n a)
      map_one_eq_zero' := by change (g 1).snd=0; simp
      leibniz' := fun a b=> by
        change (g (a*b)).snd=a•(g b).snd+b•(g a).snd
        rw [map_mul,snd_mul,hg,hg,op_smul_eq_smul] }
  exact ⟨D,fun a=>congrArg snd (lift_on f (zz4 F) hf a)⟩
private theorem aNb {F:Type} [zrb F]
    (d:Derivation ℤ F F) (P:F[X]) :
    (Lv d P).natDegree≤P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  change d (P.coeff i)=0
  rw [coeff_eq_zero_of_natDegree_lt hi,map_zero]
private theorem polynomial_bound {F:Type} [zrb F]
    (d:Derivation ℤ F F) (P:F[X]) :
    infinity F (algebraMap F[X] (RatFunc F) (Lv d P)) ≤
      infinity F (algebraMap F[X] (RatFunc F) P) := by
  by_cases h:Lv d P=0
  · simp [h]
  have hP:P≠0:= fun hz=>h (hz ▸ map_zero (Lv d))
  classical
  rw [infinity,RatFunc.inftyValuation_apply,RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation.polynomial F h,RatFunc.inftyValuation.polynomial F hP,
    WithZero.exp_le_exp]
  exact_mod_cast aNb d P
private theorem quotient_bound {F:Type} [zrb F] [zZE ℤ (RatFunc F)]
    (D:Derivation ℤ (RatFunc F) (RatFunc F))
    (hp : ∀ P:F[X],infinity F (D (algebraMap F[X] (RatFunc F) P)) ≤
      infinity F (algebraMap F[X] (RatFunc F) P)) (b:RatFunc F) :
    infinity F (D b)≤ infinity F b:= by
  refine RatFunc.induction_on (P:= fun a=>infinity F (D a)≤ infinity F a) b ?_
  intro P Q hQ
  let v :=infinity F
  let x :=algebraMap F[X] (RatFunc F) P
  let y :=algebraMap F[X] (RatFunc F) Q
  have hy :v y≠0:= by
    exact fun h=>hQ ((map_eq_zero_iff _ (RatFunc.algebraMap_injective F)).mp
      (v.zero_iff.mp h))
  change v (D (x/y))≤v (x/y)
  have hxy :v (y*D x - x*D y)≤v y*v x := by
    apply v.map_sub_le
    · rw [map_mul]
      exact mul_le_mul_of_nonneg_left (hp P) zero_le
    · rw [map_mul,mul_comm (v y) (v x)]
      exact mul_le_mul_of_nonneg_left (hp Q) zero_le
  rw [D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,map_mul,map_pow,v.map_inv,
    v.map_div]
  calc
    _≤(v y)⁻¹^2*(v y*v x) :=mul_le_mul_of_nonneg_left hxy zero_le
    _=v x/v y := by
      rw [pow_two,mul_assoc ((v y)⁻¹),inv_mul_cancel_left₀ hy,div_eq_mul_inv,mul_comm]
theorem proof :P5_7_3_3_4_1_3_2.c1 := by
  intro k _
  let targetAlgebra :zZE ℤ (Generic k) :=inferInstance
  let F:=seedField k
  let:zZE ℤ F:=Ring.toIntAlgebra F
  let:zZE ℤ (Generic k) :=targetAlgebra
  let j:=algebraMap (PowerSeries k) F
  let e :=Polynomial.mapRingHom j
  obtain ⟨d,hd⟩:=cNR (F:=F) (PowerSeries.derivative (R:=k))
  obtain ⟨D,hD⟩:=cNR (F:=Generic k) (Lv d)
  refine ⟨D,?_,quotient_bound D (fun P => ?_)⟩
  · intro b
    change D (algebraMap F[X] (Generic k) (e b)) =
      algebraMap F[X] (Generic k) (e (seedDeriv b))
    rw [hD]
    apply congrArg (algebraMap F[X] (Generic k))
    ext i:1
    change d ((b.map j).coeff i)=((seedDeriv b).map j).coeff i
    rw [coeff_map,coeff_map]
    exact hd (b.coeff i)
  · rw [hD]
    exact polynomial_bound d P
end
end P5_7_3_3_4_1_3_2_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qISdf9a
noncomputable section
open Finset MvPolynomial
open P5 (K)
open quN7Z4a (Z7)
open qL2osVa
open cu (L FX)

open Cu akS
open scoped BigOperators
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
open private growth_count from ProximityPrize.SubmissionLower.ZGggfqb
variable {C₀:sQ} [Fact (Irreducible C₀)]
private abbrev Graph (C:MarkedSheet C₀) :=Cut C.sheet.n ⧸ zdq C.bee
private def arcEval {C:MarkedSheet C₀} {γ:K} (a :Arc C γ) :Graph C →ₐ[L] Series := by
  let e :Cut C.sheet.n →ₐ[L] Series :=aeval (Sum.elim a.seed a.parameter)
  let ι:=algebraMap Series SeriesField
  have he :ι.comp e.toRingHom=a.embedding.comp C.bee := by
    apply zXT
    · intro x
      change ι (e (znf x))=a.embedding (C.bee (znf x))
      rw [show C.bee (znf x)=zT C₀ x from eval₂Hom_C _ _ _,
        a.constant_eq,show e (znf x)=zMG x from aeval_C _ _]
    · intro i
      cases i with
      | inl i =>
        change ι (e (z9v (Sum.inl i))) =
          a.embedding (C.bee (z9v (Sum.inl i)))
        rw [show e (z9v (Sum.inl i))=a.seed i from aeval_X _ _,
          show C.bee (z9v (Sum.inl i))=Wt C₀ i
            from eval₂Hom_X' _ _ _,a.seed_eq]
      | inr i =>
        change ι (e (z9v (Sum.inr i))) =
          a.embedding (C.bee (z9v (Sum.inr i)))
        rw [show e (z9v (Sum.inr i))=a.parameter i from aeval_X _ _,
          show C.bee (z9v (Sum.inr i))=C.sheet.bY.coordinate i
            from eval₂Hom_X' _ _ _,a.parameter_eq]
  refine Ideal.Quotient.liftₐ _ e fun x hx=>(IsFractionRing.injective Series SeriesField) ?_
  change (ι.comp e.toRingHom) x=ι 0
  rw [he,RingHom.comp_apply,RingHom.mem_ker.mp hx,map_zero,map_zero]
private theorem arcEval_mk {C:MarkedSheet C₀} {γ:K} (a :Arc C γ) (q:Cut C.sheet.n) :
    arcEval a (zVv (zdq C.bee) q) =
      eval₂Hom zMG (Sum.elim a.seed a.parameter) q:= by
  rw [arcEval,Ideal.Quotient.liftₐ_apply,Ideal.Quotient.lift_mk]
  rfl
private theorem fx_compat (C:MarkedSheet C₀) (q:Cut C.sheet.n) :
    W8 C.sheet.bY (zDK (algebraMap L FX) q) =
      Mu C₀ (C.bee q) := by
  let f :=(W8 C.sheet.bY).comp (zDK (algebraMap L FX))
  let g:=(Mu C₀).comp C.bee
  have h:f=g:= by
    apply zXT
    · intro x
      simp [f,g,W8,MarkedSheet.bee,b1t]
    · intro i
      cases i <;> simp [f,g,W8,MarkedSheet.bee]
  exact DFunLike.congr_fun h q
private def fxGraph (C:MarkedSheet C₀) :Graph C →+* tu (EF C.sheet.bY) :=
  Ideal.quotientMap _ (zDK (algebraMap L FX)) fun q hq=> by
    change W8 C.sheet.bY (zDK (algebraMap L FX) q)=0
    rw [fx_compat,RingHom.mem_ker.mp hq,map_zero]
private def fxValue (C:MarkedSheet C₀) :
    tu (EF C.sheet.bY) →+* y7 C₀ :=
  (W8 C.sheet.bY).kerLift
private theorem transfer (C:MarkedSheet C₀) {ι:Type} [Fintype ι] (r :ι→Graph C)
    (hr :z14 L r) :z14 FX (fun i=>fxGraph C (r i)) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  let g:=C.bee.kerLift
  let m:=fxValue C
  have hg (x :L) :g (algebraMap L (Graph C) x)=zT C₀ x := by
    change C.bee.kerLift (zVv _ (znf x))= _
    rw [RingHom.kerLift_mk]
    exact eval₂Hom_C _ _ _
  have hm (x :FX) :m (algebraMap FX (tu (EF C.sheet.bY)) x)=Mr C₀ x := by
    change (W8 C.sheet.bY).kerLift (zVv _ (znf x))= _
    rw [RingHom.kerLift_mk]
    exact eval₂Hom_C _ _ _
  have hvalue (j:ι) :m (fxGraph C (r j))=Mu C₀ (g (r j)) := by
    obtain ⟨x,hx⟩:=Ideal.Quotient.mk_surjective (I:=zdq C.bee) (r j)
    rw [← hx,fxGraph,z5h]
    change (W8 C.sheet.bY).kerLift
      (zVv (zdq (W8 C.sheet.bY))
        (zDK (algebraMap L FX) x)) =
      Mu C₀ (C.bee.kerLift (zVv (zdq C.bee) x))
    rw [RingHom.kerLift_mk,RingHom.kerLift_mk]
    exact fx_compat C x
  have hterm (j:ι) :
      m (c j•fxGraph C (r j))=Mr C₀ (c j)*Mu C₀ (g (r j)) := by
    rw [Algebra.smul_def (A:=tu (EF C.sheet.bY)) (c j),map_mul,hm,hvalue]
  have he : (∑ j,Mr C₀ (c j)*Mu C₀ (g (r j)))=0:= by
    simpa only [map_sum,hterm,map_zero] using congrArg m hc
  exact clear_abscissa_relation (F:=L) (E :=oO C₀) (A:=Graph C)
    (zT C₀) g (RingHom.kerLift_injective _) hg r hr c he i
theorem proof :qL2osVa.c5:= by
  classical
  intro C₀ inst C A q V v hq hv
  let J:=zdq C.bee
  let:J.IsPrime :=zgL C.bee
  let mark (i : ↥V) :=A ⟨i,(hv i i.property).choose⟩
  let e (i : ↥V) :=arcEval (mark i)
  let t (i : ↥V) :=Z7 (C.z i) 0
  let s :Graph C:=zVv J (z9v (Sum.inl 0))
  let a :Graph C:=zVv J (rename Sum.inr q)
  have ha :a≠0:= by
    apply mt (Ideal.Quotient.eq_zero_iff_mem.mp)
    change C.bee (rename Sum.inr q)≠0
    rwa [MarkedSheet.bee,eval₂Hom_rename]
  have ht:Function.Injective t:= by
    intro i j he
    apply Subtype.ext
    have hmem (i : ↥V) : (i:K)∈C.T :=
      (mem_filter.mp (hv i i.property).choose).1
    exact C.injective (hmem i) (hmem j) ((algebraMap K L).injective he)
  have hs (i : ↥V) :zbO (e i s)=t i:= by
    dsimp only [e,s]
    rw [arcEval_mk,eval₂Hom_X']
    exact (mark i).seed_value 0
  let j (i : ↥V) :Fin 2 :=(mark i).zD.choose
  let u (i : ↥V) :Graph C:=zVv J
    (z9v (Sum.inl (j i))-MvPolynomial.C (Z7 (C.z i) (j i)))
  have hu (i : ↥V) :zbO (e i (u i))=0 ∧
      z2o 1 (e i (u i))≠0:= by
    dsimp only [e,u]
    rw [arcEval_mk,map_sub,eval₂Hom_X',eval₂Hom_C]
    change zbO ((mark i).seed (j i) -
      zMG (Z7 (C.z i) (j i)))=0 ∧
      z2o 1 ((mark i).seed (j i)-PowerSeries.C (Z7 (C.z i) (j i)))≠0
    simp only [map_sub,PowerSeries.constantCoeff_C,(mark i).seed_value,sub_self,
      PowerSeries.coeff_C,Nat.one_ne_zero,ite_false,sub_zero,true_and]
    exact (mark i).zD.choose_spec
  have hav (i : ↥V) (k :ℕ) (hk :k<v i) :z2o k (e i a)=0:= by
    dsimp only [e,a]
    rw [arcEval_mk,eval₂Hom_rename]
    exact (hv i i.property).choose_spec k hk
  obtain ⟨r,hr⟩:=jet_powers e (fun i : ↥V=>v i) a s t u ha ht hs hu hav
  let Q:=zDK (algebraMap L FX) q
  have hqa :fxGraph C a=zVv (EF C.sheet.bY)
      (aa4 C.sheet.n Q) := by
    change fxGraph C (zVv J (rename Sum.inr q))= _
    rw [fxGraph,z5h,map_rename]
    rfl
  have hrel (k :ℕ) :z14 FX
      (fun ij:Fin (k+1)×(Σ i : ↥V,Fin (v i)) =>
        (zVv (EF C.sheet.bY) (aa4 C.sheet.n Q)) ^
          (ij.1 :ℕ)*fxGraph C (r ij.2)) := by
    simpa only [map_mul,map_pow,hqa] using transfer C _ (hr k)
  have h:=growth_count (EF C.sheet.bY) (zgL (W8 _))
    C.sheet.height Q (fun i=>fxGraph C (r i)) hrel
  have hdegree :Q.totalDegree≤q.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hcard:zhP (Σ i : ↥V,Fin (v i)) = ∑ i∈V,v i:= by
    simp [Fintype.card_sigma,← Finset.sum_attach V]
  rw [hcard] at h
  exact h.trans (ztf _ hdegree)
end
end qISdf9a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qNqPG5b
noncomputable section
open Polynomial

open P5 (p)


open scoped BigOperators
section Span
variable {E :Type} [zrb E] (q:ℕ) [ExpChar E q] (z t:E)
private abbrev kJ:=(frobenius E q).fieldRange
private def monomials :Fin q×Fin q→E :=
  fun ij=>z^(ij.2 :ℕ)*t^(ij.1 :ℕ)
private abbrev monomialSpan:Submodule (kJ (E :=E) q) E :=
  Submodule.span _ (Set.range (monomials q z t))
private theorem monomial_mem (i j:ℕ) :z^i*t^j∈monomialSpan q z t:= by
  have hq:=expChar_pos E q
  have hm:z^(i % q)*t^(j % q)∈monomialSpan q z t :=
    Submodule.subset_span ⟨(⟨j % q,Nat.mod_lt _ hq⟩,⟨i % q,Nat.mod_lt _ hq⟩),rfl⟩
  let b:kJ (E :=E) q :=
    ⟨(z^(i/q)*t^(j/q))^q,⟨_,rfl⟩⟩
  have h:=(monomialSpan q z t).smul_mem b hm
  change (z^(i/q)*t^(j/q))^q*(z^(i % q)*t^(j % q))∈_ at h
  rw [mul_pow,← pow_mul,← pow_mul,mul_mul_mul_comm,← pow_add,← pow_add,
    Nat.mul_comm (i/q) q,Nat.mul_comm (j/q) q,add_comm (q*(i/q)),
    add_comm (q*(j/q)),Nat.mod_add_div,Nat.mod_add_div] at h
  exact h
private theorem one_mem_span: (1 :E)∈monomialSpan q z t:= by
  simpa only [pow_zero,mul_one] using monomial_mem q z t 0 0
private theorem mul_mem_span (a b:E) (ha :a∈monomialSpan q z t)
    (hb:b∈monomialSpan q z t) :a*b∈monomialSpan q z t:= by
  refine Submodule.span_induction₂ (p:= fun a b _ _=>a*b∈monomialSpan q z t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
    rw [monomials,monomials,mul_mul_mul_comm,← pow_add,← pow_add]
    exact monomial_mem q z t _ _
  · intro b _
    rw [zero_mul]
    exact z4M _
  · intro a _
    rw [mul_zero]
    exact z4M _
  · intro a b c _ _ _ ha hb
    rw [add_mul]
    exact zcy _ ha hb
  · intro a b c _ _ _ hb hc
    rw [mul_add]
    exact zcy _ hb hc
  · intro r a b _ _ h
    rw [smul_mul_assoc]
    exact zc2 _ r h
  · intro r a b _ _ h
    rw [mul_smul_comm]
    exact zc2 _ r h
private theorem c48 (a :E) :a^q∈monomialSpan q z t:= by
  let b:kJ (E :=E) q:=⟨a^q,⟨a,rfl⟩⟩
  have h:=(monomialSpan q z t).smul_mem b (one_mem_span q z t)
  change a^q*1∈_ at h
  simpa only [mul_one] using h
private def monomialField:Subfield E := by
  let S:=(monomialSpan q z t).toSubalgebra (one_mem_span q z t) (mul_mem_span q z t)
  refine (S.toIntermediateField fun a ha => ?_).toSubfield
  change a⁻¹∈S
  by_cases h:a=0
  · simpa only [h,inv_zero] using S.zero_mem
  have hq:=expChar_pos E q
  have he :a⁻¹=(a⁻¹)^q*a^(q-1) := calc
    _=a⁻¹*(a⁻¹*a)^(q-1) := by rw [inv_mul_cancel₀ h,one_pow,mul_one]
    _ = _:= by rw [mul_pow,← mul_assoc,← pow_succ',Nat.sub_add_cancel hq]
  rw [he]
  exact S.mul_mem (c48 q z t _) (S.pow_mem ha _)
private theorem expansion_of_mem {a :E} (ha :a∈monomialField q z t) :
    ∃ c:Fin q→Fin q→E,
      a = ∑ j,∑ i,c j i^q*z^(i:ℕ)*t^(j:ℕ) := by
  change a∈monomialSpan q z t at ha
  obtain ⟨b,hb⟩:=(Submodule.mem_span_range_iff_exists_fun (kJ (E :=E) q)).mp ha
  have h (ij:Fin q×Fin q) : ∃ c:E,c^q=(b ij:E) :=(b ij).property
  choose c hc using h
  refine ⟨fun j i=>c (j,i),hb.symm.trans ?_⟩
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _ => ?_
  change (b (j,i) :E)*(z^(i:ℕ)*t^(j:ℕ)) =
    c (j,i)^q*z^(i:ℕ)*t^(j:ℕ)
  rw [hc,mul_assoc]
end Span
private theorem bqo {R F E :Type} [za6 R] [IsDomain R] [zrb F]
    [zZE R F] [IsFractionRing R F] [zrb E]
    (S:Subfield E) (f :F →+* E) (h : ∀ r :R,f (algebraMap R F r)∈S) (a :F) :
    f a∈S:= by
  obtain ⟨r,s,-,rfl⟩:=IsFractionRing.div_surjective R a
  rw [map_div₀]
  exact S.div_mem (h r) (h s)
private theorem c4Q {R E :Type} [za6 R] [zrb E] (S:Subfield E)
    (f :R[X] →+* E) (hc : ∀ r :R,f (C r)∈S)
    (hx :f (Polynomial.X (R:=R))∈S) (a :R[X]) :f a∈S:= by
  induction a using Polynomial.induction_on' with
  | add u v hu hv=>simpa only [map_add] using S.add_mem hu hv
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact S.mul_mem (hc r) (S.pow_mem hx n)
end
end qNqPG5b
end
