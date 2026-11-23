import ProximityPrize.SubmissionLower.Zw100fa
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.smul_def → zd5, Fin.val_injective → z0e, Finsupp.finsetSum_apply → ze7, Fintype.card_fin → zgY, Function.Injective → zq4, LinearIndependent → z14, Module.Finite → zAa, Module.IsTorsionFree → zYo, Module.finrank → zsE, Module.finrank_pos → zRt, Nat.cast_zero → zQq, Polynomial.X → z7y, Polynomial.eval_C → zFf, Polynomial.eval_add → zvF, Polynomial.eval_mul → zbr, Polynomial.map_C → zrL, Polynomial.map_add → zS4, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m, Polynomial.map_sub → z3A
section
set_option backward.isDefEq.respectTransparency false
namespace qgcZtNc
noncomputable section
open Polynomial
open P5 (K)
open cu (L)
open E7 (CurvePlace)
open qBd5KZd (MarkedCurve Allowance small bounded weight integral roots avoids modulus)
open scoped WithZero
variable {E :Type} [Field E] [zZE L E]
private abbrev inclusion (v :CurvePlace L E) :v.value.valuationSubring →+* E :=
 v.value.valuationSubring.toSubring.subtype
private theorem j9 (v :CurvePlace L E) (P:E[X])
   (h : ∀ j,v.value (P.coeff j)≤1) :
   ∃ Q:v.value.valuationSubring[X],Q.map (inclusion v)=P :=
 (mem_lifts _).mp <| (lifts_iff_coeff_lifts _).mpr
   fun j=>⟨⟨_,h j⟩,rfl⟩
private theorem liftBi (v :CurvePlace L E) (P:E[X][X])
   (h : ∀ i j,v.value ((P.coeff i).coeff j)≤1) :
   ∃ Q:v.value.valuationSubring[X][X],Q.map (mapRingHom (inclusion v))=P :=
 (mem_lifts _).mp <| (lifts_iff_coeff_lifts _).mpr
   fun i=>j9 v _ (h i)
private def orderIdeal (v :CurvePlace L E) (q:ℕ) :Ideal v.value.valuationSubring where
 carrier := {x | small v (-(q:ℤ)) (x :E)}
 zero_mem' := by simp [small]
 add_mem' hx hy :=(v.value.map_add _ _).trans (max_le hx hy)
 smul_mem' a x hx := by
  change v.value ((a :E)*(x :E))≤WithZero.exp (-(q:ℤ))
  rw [map_mul]
  exact (mul_le_mul' a.property hx).trans_eq (one_mul _)
omit [zZE L E] in
private theorem evalWeight {D M:ℕ} {G:E[X][X]} {S:E[X]}
  (hG:weight D G<M) (hS:S.natDegree≤D) : (G.eval S).natDegree<M:= by
 classical
 rw [eval_eq_sum,Polynomial.sum]
 refine (natDegree_sum_le _ _).trans_lt (hG.trans_le' (Finset.sup_le fun i hi => ?_))
 exact (natDegree_mul_le.trans (Nat.add_le_add_left
  (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hS)) _)).trans
  (Finset.le_sup (f := fun k=>(G.coeff k).natDegree+k*D) hi)
private theorem localResultant (v :CurvePlace L E) (D q M:ℕ) (b:L)
    (S:E[X]) (f G H R:E[X][X])
    (hfpos :0<f.natDegree) (hSd:S.natDegree≤D)
    (hiS : ∀ j,v.value (S.coeff j)≤1)
    (hif : ∀ i j,v.value ((f.coeff i).coeff j)≤1)
    (hiG : ∀ i j,v.value ((G.coeff i).coeff j)≤1)
    (hiH : ∀ i j,v.value ((H.coeff i).coeff j)≤1)
    (hiR : ∀ i j,v.value ((R.coeff i).coeff j)≤1)
    (hz : ∀ j,small v (-(q:ℤ)) ((f.eval S).coeff j))
    (hw:weight D G<M) (heq :f*H=G+Polynomial.C (modulus b M)*R)
    (j:ℕ) :small v (-(q:ℤ)) ((f.resultant G).coeff j) := by
  let O:=v.value.valuationSubring
  let a :=inclusion v
  let ρ:=Ideal.Quotient.mk (orderIdeal v q)
  let x :O:=⟨algebraMap L E b,by
    change v.value (algebraMap L E b)≤1
    by_cases hb:b=0
    · simp [hb]
    · rw [v.on_constants b hb]⟩
  let m:O[X] :=(z7y-Polynomial.C x)^M
  obtain ⟨s,hs⟩:=j9 v S hiS
  obtain ⟨F,hF⟩:=liftBi v f hif
  obtain ⟨P,hP⟩:=liftBi v G hiG
  obtain ⟨U,hU⟩:=liftBi v H hiH
  obtain ⟨V,hV⟩:=liftBi v R hiR
  have ha :zq4 a :=(v.value.valuationSubring.toSubring).subtype_injective
  have hb:zq4 (mapRingHom a) :=zTo a ha
  have hs' : (mapRingHom a) s=S:=hs
  have hm: (mapRingHom a) m=modulus b M:= by
    change ((z7y-Polynomial.C x)^M).map a= _
    rw [z5m,z3A,Polynomial.map_X,zrL]
    rfl
  have hrel :F*U=P+Polynomial.C m*V:= by
    apply zTo (mapRingHom a) hb
    rw [zNl,zS4,zNl,zrL,hF,hP,hU,hV,hm]
    exact heq
  have hFe : (F.eval s).map a=f.eval S:= by
    change (mapRingHom a) (F.eval s)= _
    rw [← eval_map_apply,hF,hs']
  have hPe : (P.eval s).map a=G.eval S:= by
    change (mapRingHom a) (P.eval s)= _
    rw [← eval_map_apply,hP,hs']
  have hzF: (F.eval s).map ρ=0:= by
    ext i
    rw [coeff_map,coeff_zero,Ideal.Quotient.eq_zero_iff_mem]
    change small v (-(q:ℤ)) (a ((F.eval s).coeff i))
    rw [← coeff_map,hFe]
    exact hz i
  have hzP: (P.eval s).map ρ=0:= by
    have h:=congrArg (fun f :O[X][X]=>(f.eval s).map ρ) hrel
    have hval : (Polynomial.C m).eval s=m:=zFf
    simp only [zbr,zvF,hval,
      zNl,zS4,hzF,zero_mul] at h
    by_contra hn
    have :Nontrivial (↥O ⧸ orderIdeal v q) :=
      (subsingleton_or_nontrivial _).resolve_left fun h=> by
        have :=h
        exact hn (Subsingleton.elim _ _)
    have hdvd:m.map ρ∣(P.eval s).map ρ :=
      ⟨-(V.eval s).map ρ,by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left h.symm⟩
    have hmonic: (m.map ρ).Monic:=((monic_X_sub_C x).pow M).map ρ
    have hd:=hmonic.natDegree_le_of_dvd hn hdvd
    have hmd: (m.map ρ).natDegree=M:= by
      change (((z7y-Polynomial.C x)^M).map ρ).natDegree=M
      rw [z5m,z3A,Polynomial.map_X,zrL,
        (monic_X_sub_C (ρ x)).natDegree_pow,natDegree_X_sub_C,mul_one]
    rw [hmd] at hd
    have hdeg: ((P.eval s).map ρ).natDegree<M:= by
      refine natDegree_map_le.trans_lt ?_
      rw [← natDegree_map_eq_of_injective ha (P.eval s),hPe]
      exact evalWeight hw hSd
    exact hdeg.not_ge hd
  have hFd:F.natDegree=f.natDegree :=
    (natDegree_map_eq_of_injective hb F).symm.trans
      (congrArg natDegree hF)
  have hPd:P.natDegree=G.natDegree :=
    (natDegree_map_eq_of_injective hb P).symm.trans
      (congrArg natDegree hP)
  obtain ⟨A,B,_,_,hAB⟩ :=
    exists_mul_add_mul_eq_C_resultant F P le_rfl le_rfl (Or.inl (hFd.symm ▸ hfpos.ne'))
  have hzero : (F.resultant P).map ρ=0:= by
    have h:=congrArg (fun f :O[X][X]=>(f.eval s).map ρ) hAB
    simpa only [zvF,zbr,zFf,
      zS4,zNl,hzF,hzP,mul_zero,zero_mul,add_zero] using h.symm
  have ht: (F.resultant P).map a=f.resultant G:= by
    change (mapRingHom a) (F.resultant P)= _
    rw [← resultant_map_map,hF,hP,hFd,hPd]
  have hj:ρ ((F.resultant P).coeff j)=0:= by rw [← coeff_map,hzero,coeff_zero]
  have hsmall:=Ideal.Quotient.eq_zero_iff_mem.mp hj
  change small v (-(q:ℤ)) (a ((F.resultant P).coeff j)) at hsmall
  rwa [← coeff_map,ht] at hsmall
theorem markedResultant {T:Finset K} (C:MarkedCurve T) (S:T→C.E[X])
  (D q M:ℕ) (b:L) (f G H R:C.E[X][X]) (A B:Allowance C.E)
  (hfpos :0<f.natDegree) (hS:integral C S) (hSd : ∀ t,(S t).natDegree≤D)
  (hA:avoids C A) (hB:avoids C B) (hf :bounded A f)
  (hG:bounded (B+A) G) (hH :bounded B H) (hR:bounded (B+A) R)
  (hz :roots C S q f) (hw:weight D G<M)
  (heq :f*H=G+Polynomial.C (modulus b M)*R) (j:ℕ) :
  ∀ t,small (C.Ia t) (-(q:ℤ)) ((f.resultant G).coeff j) := by
 intro t
 have integrality {U:Allowance C.E} {P:C.E[X][X]} (ha :U (C.Ia t)=0)
    (hp:bounded U P) (i k :ℕ) : (C.Ia t).value ((P.coeff i).coeff k)≤1 := by
  have h:=hp i k (C.Ia t)
  change small (C.Ia t) (U (C.Ia t)) _ at h
  simpa only [small,ha,zQq,WithZero.exp_zero] using h
 have hsum: (B+A) (C.Ia t)=0:= by simp [hA t,hB t]
 apply localResultant (C.Ia t) D q M b (S t) f G H R hfpos (hSd t)
  (fun k=> by simpa only [small,WithZero.exp_zero] using hS t k)
  (integrality (hA t) hf) (integrality hsum hG) (integrality (hB t) hH)
  (integrality hsum hR) (hz t) hw heq
end
end qgcZtNc
end
section
namespace qtVXGJd
noncomputable section
open Finset qBd5KZd
open P5 (K)
open cu (L)
open E7 (CurvePlace axV poleOrder)
open aFU (DT DR)
open IntermediateField
open scoped Classical WithZero nonZeroDivisors algebraAdjoinAdjoin
variable {E :Type} [Field E] [zZE L E]
private theorem fresh_parameter {T:Finset K} (C:MarkedCurve T) :
    ∃ x :C.E,Transcendental L x∧zAa (adjoin L {x}) C.E ∧
      ∀ t,(C.Ia t).value x≤1 := by
  obtain ⟨y,hy,hyfin⟩:=C.curve
  let bad (t:T) (a :L) :=(C.Ia t).value (y-algebraMap L C.E a)<1
  have unique (t:T) {a b:L} (ha :bad t a) (hb:bad t b) :a=b:= by
    by_contra h
    have he : (y-algebraMap L C.E b)-(y-algebraMap L C.E a) =
        algebraMap L C.E (a-b) := by rw [map_sub]; ring
    have hv :=(C.Ia t).value.map_sub (y-algebraMap L C.E b) (y-algebraMap L C.E a)
    rw [he,(C.Ia t).on_constants _ (sub_ne_zero.mpr h)] at hv
    exact (hv.trans_lt (max_lt hb ha)).false
  let b (t:T) :L:=if h : ∃ a,bad t a then h.choose else 0
  obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (Finset.univ.image b)
  have hf (t:T) :1≤(C.Ia t).value (y-algebraMap L C.E a) := by
    apply le_of_not_gt
    intro h
    have hex : ∃ a,bad t a :=⟨a,h⟩
    have he :a=b t:=unique t h (by simpa only [b,dite_eq_left hex] using hex.choose_spec)
    exact ha (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,he.symm⟩)
  let c:=algebraMap L C.E a
  let x :=(y-c)⁻¹
  have hx :Transcendental L x := by
    intro h
    exact hy (by simpa only [c,sub_add_cancel] using
      (IsAlgebraic.inv_iff.mp h).add (isAlgebraic_algebraMap a))
  have he :adjoin L ({x} : Set C.E)=adjoin L {y} := by
    apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff,Set.singleton_subset_iff]
    · exact (adjoin L {y}).inv_mem (sub_mem (mem_adjoin_simple_self L y)
        ((adjoin L {y}).algebraMap_mem a))
    · change y∈adjoin L ({x} : Set C.E)
      have hyx :x⁻¹+c=y := by simp only [x,inv_inv,sub_add_cancel]
      rw [← hyx]
      exact add_mem ((adjoin L {x}).inv_mem (mem_adjoin_simple_self L x))
        ((adjoin L {x}).algebraMap_mem a)
  refine ⟨x,hx,he.symm ▸ hyfin,fun t => ?_⟩
  change (C.Ia t).value ((y-c)⁻¹)≤1
  rw [map_inv₀]
  exact inv_le_one_of_one_le₀ (hf t)
private theorem integral_basis {x :E} (hx :Transcendental L x)
   [zAa (adjoin L {x}) E] :
   ∃ b:Module.Basis (Fin (zsE (adjoin L {x}) E)) (adjoin L {x}) E,
     ∀ i,IsIntegral (DT L E x) (b i) := by
 let A:=DT L E x
 let B:=DR L E x
 let F:=adjoin L {x}
 have :zAa A B:=bRt.proof L E x hx inferInstance
 have :IsPrincipalIdealRing A:=aFU.bKh hx
 have :zYo A E := .trans_faithfulSMul A F E
 have :zYo A B:=IsIntegralClosure.isTorsionFree A E
 have :Module.Free A B:=inferInstance
 have :IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) E :=
   IsIntegralClosure.isLocalization A F E B
 let b:=Module.finBasis A B
 let e :=b.localizationLocalization F (nonZeroDivisors A) E
 have hr :zsE F E=zsE A B:= by
   rw [Module.finrank_eq_card_basis e,zgY]
 refine ⟨e.reindex (finCongr hr.symm),fun i => ?_⟩
 rw [Module.Basis.reindex_apply]
 change IsIntegral A ((b.localizationLocalization F (nonZeroDivisors A) E) _)
 rw [Module.Basis.localizationLocalization_apply]
 exact (b _).property
private theorem integral_bound {v :CurvePlace L E} {x z :E}
   (hx :v.value x≤1) (hz :IsIntegral (DT L E x) z) :
   v.value z≤1 := by
 let A:=DT L E x
 let w:=v.value
 have hA (a :A) :w (algebraMap A E a)≤1 := by
   obtain ⟨a,ha⟩:=a
   change w a≤1
   induction ha using Algebra.adjoin_induction with
   | mem y hy =>
     obtain rfl :=Set.mem_singleton_iff.mp hy
     exact hx
   | algebraMap c =>
     by_cases hc:c=0
     · simp [hc]
     · exact (v.on_constants c hc).le
   | add a b _ _ ha hb=>exact (w.map_add _ _).trans (max_le ha hb)
   | mul a b _ _ ha hb =>
     rw [map_mul]
     exact mul_le_one' ha hb
 let f :A →+* w.valuationSubring :=
   (algebraMap A E).codRestrict w.valuationSubring.toSubring hA
 let:zZE A w.valuationSubring :=f.toAlgebra
 let:IsScalarTower A w.valuationSubring E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
 exact (Valuation.integer.integers w).isIntegral_iff_v_le_one.mp (hz.tower_top)
private theorem small_nat {v :CurvePlace L E} {z :E} {n:ℕ} :
   small v n z↔poleOrder v.value z≤n:= by
 by_cases hz :z=0
 · simp [hz,poleOrder,small]
 rw [small,← WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hz),poleOrder]
 omega
private def poles (h:axV L E) (z :E) :Allowance E :=
 Finsupp.ofSupportFinite _ (h z).1
private theorem mass_poles (h:axV L E) (z :E) :
  mass (poles h z) = ∑ᶠ v :CurvePlace L E,poleOrder v.value z := by
 unfold mass
 rw [Finsupp.liftAddHom_apply,Finsupp.sum]
 exact (finsum_eq_finsetSum_of_support_subset _ (fun _ h=>Finsupp.mem_support_iff.mpr h)).symm
private theorem independent_products {x :E} (hx :Transcendental L x)
   {ι:Type} [Fintype ι] (b:Module.Basis ι (adjoin L {x}) E) (n:ℕ) :
   z14 L (fun ij:ι×Fin n=>x^ij.2.val*b ij.1) := by
 let F:=adjoin L {x}
 let z :F:=AdjoinSimple.gen L x
 have hz :Transcendental L z :=
   (transcendental_algebraMap_iff (algebraMap F E).injective).mp hx
 have hpow:z14 L (fun j:ℕ=>z^j) := by
   have h:=(Polynomial.basisMonomials L).linearIndependent.map'
     (Polynomial.aeval z).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hz))
   simpa [Function.comp_def,← Polynomial.C_mul_X_pow_eq_monomial] using h
 apply Fintype.linearIndependent_iff.mpr
 intro c hc ij
 have he : ∑ i:ι,(∑ j:Fin n,c (i,j)•z^j.val)•b i=0:= by
   rw [Fintype.sum_prod_type] at hc
   simpa only [zd5,map_sum,map_mul,map_pow,Finset.sum_mul,mul_assoc,
     IsScalarTower.algebraMap_apply L F E,show algebraMap F E z=x from rfl] using hc
 exact (Fintype.linearIndependent_iff.mp (hpow.comp _ z0e)) _
   ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ he ij.1) ij.2
theorem proof :qBd5KZd.c2 := by
  intro T C hfin
  obtain ⟨x,hx,hFx,hAway⟩:=fresh_parameter C
  let F:=adjoin L {x}
  let d:=zsE F C.E
  have :zAa F C.E :=hFx
  have hd:0<d:=zRt
  obtain ⟨b,hb⟩:=integral_basis hx
  have h:axV L C.E :=aFU.of_children
    bRt.proof bRu.proof L C.E C.curve
  let P:=poles h x
  let B:Allowance C.E := ∑ i:Fin d,poles h (b i)
  have hP:mass P=d:=(mass_poles h x).trans ((h x).2.2.2 hx)
  have hPaway :avoids C P:= fun t=>Nat.le_zero.mp
    (small_nat.mp (by simpa only [zQq,small,WithZero.exp_zero] using hAway t))
  have hBaway :avoids C B:= by
    intro t
    simp only [B,ze7]
    apply Finset.sum_eq_zero
    intro i _
    exact Nat.le_zero.mp (small_nat.mp (by
      simpa only [zQq,small,WithZero.exp_zero] using integral_bound (hAway t) (hb i)))
  refine ⟨mass B+d,fun v => ?_⟩
  by_cases hbudget:mass B≤v
  · let n:=(v - mass B)/d
    let A:Allowance C.E :=n•P+B
    have ha :mass A=n*d+mass B:= by
      change mass (n•P+B)= _
      rw [map_add,map_nsmul,hP,Nat.nsmul_eq_mul]
    refine ⟨A,?_,fun t=> by simp [A,hPaway t,hBaway t],?_⟩
    · rw [ha]
      exact (Nat.add_le_add_right (Nat.div_mul_le_self _ _) _).trans_eq (Nat.sub_add_cancel hbudget)
    have hmem (ij:Fin d×Fin n) :x^ij.2.val*b ij.1∈btN A:= by
      intro w
      have hp:small w (P w) x :=small_nat.mpr le_rfl
      have hb:small w (B w) (b ij.1) := by
        apply small_nat.mpr
        change (poles h (b ij.1)) w≤B w
        rw [show B w = ∑ i:Fin d,(poles h (b i)) w from ze7 _ _ _]
        exact Finset.single_le_sum (f := fun i:Fin d=>(poles h (b i)) w)
          (fun _ _=>Nat.zero_le _) (Finset.mem_univ ij.1)
      have hpow:=pow_le_pow_left' hp ij.2.val
      rw [← map_pow,← WithZero.exp_nsmul] at hpow
      have hj: (ij.2.val :ℤ)*(P w:ℤ)≤(n:ℤ)*(P w:ℤ) :=
        mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr ij.2.isLt.le) (Int.natCast_nonneg _)
      have hpow' : small w (n•(P w:ℤ)) (x^ij.2.val) :=
        hpow.trans (WithZero.exp_le_exp.mpr (by simpa only [nsmul_eq_mul] using hj))
      have hAw: (A w:ℤ)=n•(P w:ℤ)+(B w:ℤ) := by
        change ((n*P w+B w:ℕ) :ℤ)= _
        rw [Nat.cast_add,Nat.cast_mul]
        rfl
      change small w (A w) _
      rw [small,map_mul,hAw,WithZero.exp_add]
      exact mul_le_mul' hpow' hb
    let q:Fin d×Fin n→btN A:= fun i=>⟨_,hmem i⟩
    have hq:z14 L q :=
      (independent_products hx b n).of_comp (btN A).subtype
    have :=hfin A
    have hdim:n*d≤zsE L (btN A) := by
      simpa only [Fintype.card_prod,zgY,Nat.mul_comm d n] using hq.fintype_card_le_finrank
    have hr :=Nat.mod_add_div (v - mass B) d
    have hr' := Nat.mod_lt (v - mass B) hd
    rw [Nat.mul_comm d] at hr
    change (v - mass B) % d+n*d=v - mass B at hr
    omega
  · exact ⟨0,by simp,fun _=>rfl,by omega⟩
end
end qtVXGJd
end
section
namespace qyOEyfe
noncomputable section
open cu (L)
open E7 (CurveField CurvePlace axV poleOrder KB)
open XX (EO aoG)
open qBd5KZd (Allowance mass small btN)
open private eaZ from ProximityPrize.SubmissionLower.V
open private cfl bLs from ProximityPrize.SubmissionLower.A3
open private pole_le from ProximityPrize.SubmissionLower.Zw100fa
open scoped WithZero
variable {E :Type} [Field E] [zZE L E]
private theorem zeroOrder_pos (v :CurvePlace L E) {x :E} (hx :x≠0) :
  0<KB v.value x↔v.value x<1 := by
 rw [← WithZero.exp_zero (M:=ℤ),← WithZero.log_lt_iff_lt_exp (v.value.ne_zero_iff.mpr hx)]
 unfold KB
 omega
private theorem infinitePlaces (hE :CurveField L E) (hd:axV L E) :
   Infinite (CurvePlace L E) := by
 classical
 obtain ⟨t,ht,hfin⟩:=hE
 let x (a :L) :=t - algebraMap L E a
 have hx (a :L) :Transcendental L (x a) := fun ha=>ht (by
   simpa only [x,sub_add_cancel] using ha.add (isAlgebraic_algebraMap a))
 have hplace (a :L) : ∃ v :CurvePlace L E,v.value (x a)<1 := by
   let:=eaZ ⟨t,ht,hfin⟩ (hx a)
   obtain ⟨_,_,he,hf⟩:=hd (x a)
   have hp:0 < ∑ᶠ v :CurvePlace L E,KB v.value (x a) := by
     rw [← he,hf (hx a)]
     exact zRt
   by_contra! hn
   exact hp.ne' (finsum_eq_zero_of_forall_eq_zero fun v =>
     Nat.eq_zero_of_not_pos fun hw=>(hn v).not_gt ((zeroOrder_pos v (hx a).ne_zero).mp hw))
 choose v hv using hplace
 apply Infinite.of_injective v
 intro a b hab
 by_contra hne
 have hh:=(v a).value.map_sub_lt (hv a) (hab ▸ hv b)
 have he :x a - x b=algebraMap L E (b-a) := by dsimp only [x]; rw [map_sub]; abel
 rw [he,(v a).on_constants _ (sub_ne_zero.mpr (Ne.symm hne))] at hh
 exact (lt_irrefl _ hh)
private def residueEquiv (hE :CurveField L E) (v :CurvePlace L E) :
  L ≃ₐ[L] EO v := by
 refine AlgEquiv.ofBijective (Algebra.ofId L (EO v)) ⟨(algebraMap L _).injective,?_⟩
 intro y
 obtain ⟨x,rfl⟩:=IsLocalRing.residue_surjective y
 obtain ⟨u,hu⟩:=v.normalized (WithZero.exp (-1))
 have hu₀:u≠0:= fun h=>WithZero.exp_ne_zero (by rw [← hu,h,map_zero])
 have hu₁:v.value u≠1 := by rw [hu]; simp
 obtain ⟨c,hc⟩:=cfl hE v.value ⟨v.on_constants⟩ ⟨u,hu₀,hu₁⟩ x x.property
 have hz :=(bLs v.value (x-aoG v c)).mpr hc
 rw [map_sub,sub_eq_zero] at hz
 exact ⟨c,hz.symm⟩
private def integralLift {A:Allowance E} {v :CurvePlace L E} (hv :A v=0)
  (x :btN A) :v.value.valuationSubring :=⟨x,by
 change v.value (x :E)≤1
 have hx :small v (A v :ℤ) (x :E) :=x.property v
 simpa only [small,hv,zQq,WithZero.exp_zero] using hx⟩
private def bLp {A:Allowance E} {v :CurvePlace L E} (hv :A v=0) :
  btN A →ₗ[L] EO v where
 toFun x :=IsLocalRing.residue _ (integralLift hv x)
 map_add' x y :=(IsLocalRing.residue _).map_add (integralLift hv x) (integralLift hv y)
 map_smul' c x := by
  change IsLocalRing.residue _ (integralLift hv (c•x)) =
   c•(IsLocalRing.residue _ (integralLift hv x))
  rw [zd5,show algebraMap L (EO v) c =
   IsLocalRing.residue _ (aoG v c) from rfl,← map_mul]
  congr 1
  exact Subtype.ext (zd5 c (x :E))
private theorem mass_eq_sum (A:Allowance E) :mass A = ∑ᶠ v,A v := by
 rw [finsum_eq_finsetSum_of_support_subset _ (s :=A.support)
  (fun _ h=>Finsupp.mem_support_iff.mpr h),mass,Finsupp.liftAddHom_apply]
 rfl
private theorem zero_budget (hd:axV L E) {A:Allowance E}
  (x :btN A) {n:ℕ} (v :Fin n ↪ CurvePlace L E) (hx : (x :E)≠0)
  (hv : ∀ i,(v i).value x<1) :n≤ mass A:= by
 classical
 let z (w:CurvePlace L E) :=KB w.value x
 obtain ⟨hp,hz,he,_⟩:=hd x
 let S:=Finset.univ.map v
 have hzpos (w:CurvePlace L E) (hw:w∈S) :0<z w:= by
  obtain ⟨i,_,rfl⟩:=Finset.mem_map.mp hw
  exact (zeroOrder_pos _ hx).mpr (hv i)
 have hs :S⊆hz.toFinset := fun w hw=>hz.mem_toFinset.mpr (hzpos w hw).ne'
 calc
  n = ∑ w∈S,1 := by simp [S]
  _ ≤ ∑ w∈S,z w:=Finset.sum_le_sum hzpos
  _ ≤ ∑ w∈hz.toFinset,z w:=Finset.sum_le_sum_of_subset hs
  _ = ∑ᶠ w,z w:=(finsum_eq_finsetSum_of_support_subset _ fun _ hw=>hz.mem_toFinset.mpr hw).symm
  _ = ∑ᶠ w:CurvePlace L E,poleOrder w.value x :=he.symm
  _ ≤ ∑ᶠ w,A w:=finsum_le_finsum hp A.hasFiniteSupport (pole_le x.property)
  _=mass A:=(mass_eq_sum A).symm
theorem proof :qBd5KZd.c3:= by
 classical
 intro E _ _ hE A
 have hd:axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hE
 let:=infinitePlaces hE hd
 let s :Set (CurvePlace L E) :=Function.support A
 have hs :sᶜ.Infinite :=A.hasFiniteSupport.infinite_compl
 let w:Fin (mass A+1) ↪ (sᶜ:Set (CurvePlace L E)) :=
   (⟨Fin.val,z0e⟩:Fin (mass A+1) ↪ ℕ).trans (hs.natEmbedding _)
 let v :Fin (mass A+1) ↪ CurvePlace L E :=w.trans (Function.Embedding.subtype _)
 have hv (i:Fin (mass A+1)) :A (v i)=0:=not_not.mp (w i).property
 let f :btN A →ₗ[L] (Fin (mass A+1)→L) :=
   LinearMap.pi fun i=>(residueEquiv hE (v i)).symm.toLinearMap.comp (bLp (hv i))
 have hf :zq4 f :=LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
   intro x hx
   by_contra hne
   have hx₀: (x :E)≠0:= fun h=>hne (Subtype.ext h)
   have hz (i:Fin (mass A+1)) : (v i).value x<1 := by
     apply (bLs (v i).value (integralLift (hv i) x)).mp
     apply (residueEquiv hE (v i)).symm.injective
     rw [map_zero]
     exact congrFun hx i
   have h:=zero_budget hd x v hx₀ hz
   omega))
 refine ⟨FiniteDimensional.of_injective f hf,?_⟩
 simpa only [Module.finrank_fintype_fun_eq_card,zgY] using
   (LinearMap.finrank_le_finrank_of_injective hf)
end
end qyOEyfe
end
