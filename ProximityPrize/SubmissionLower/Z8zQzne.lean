import ProximityPrize.SubmissionLower.ZmJ5Lsb
import Mathlib.RingTheory.Smooth.Field
import ProximityPrize.SubmissionLower.ZcWZWSa
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.adjoin_range_eq_range_aeval → z5E, Field → zrb, Fin.sum_univ_four → zmL, Function.Injective → zq4, Ideal → znc, Ideal.span → zye, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.rename → zHw, MvPolynomial.ringHom_ext → zXT, Nat.add_le_add → z9f, Nat.cast_nonneg → zqJ, Nat.mul_le_mul_right → ztf, Polynomial → zM1, Polynomial.evalRingHom → zhy, Polynomial.hom_eval₂ → zly, Set.infinite_univ → z6P, Set.range → zxp
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option maxRecDepth 3000
namespace qPP0zte
noncomputable section
open K1 (p)
open gT (Ambient)
open P6_7 (RectTail)
open P6_7_2 (free)
open P6_7_2_3
open qu56FMb (s)
open TD (FP auN arC)
open scoped BigOperators
private theorem ref_box (b:RectTail) (o:Origin) :
    (refShape b o).B≤373∧(refShape b o).J≤81∧(refShape b o).U≤10309:= by
  cases b <;> fin_cases o <;> exact ⟨by decide,by decide,by decide⟩
private theorem last_free (b:RectTail) :
    (free b 5).B≤384∧(free b 5).J≤86∧(free b 5).U≤3570:= by
  cases b <;> exact ⟨by decide,by decide,by decide⟩
private theorem member_last {b:RectTail} {o:Origin} {Q:znc Ambient}
    (hf :MemberFits b o terminalStop Q) (k :Fin 4) :
    sectionMass Q k≤kK (auN (free b 5)) (refShape b o) k/25:= by
  refine (hf k).trans ((min_le_left _ _).trans ?_)
  change min _ _≤_
  exact min_le_right _ _
private theorem gEZ {a b c d A B C D:ℕ} (ha :a≤A) (hb:b≤B)
    (hc:c≤C) (hd:d≤D) :
    (a :ℚ)*b+(c:ℚ)*d≤((A*B+C*D:ℕ) :ℚ) := by
  exact_mod_cast z9f (Nat.mul_le_mul ha hb) (Nat.mul_le_mul hc hd)
private theorem masses {b:RectTail} {o:Origin} {Q:znc Ambient}
    (hf :MemberFits b o terminalStop Q) :
    sectionMass Q 0≤63182/25∧sectionMass Q 1≤1175744/25 ∧
      sectionMass Q 2≤5290266/25:= by
  obtain ⟨hB,hJ,hU⟩:=ref_box b o
  obtain ⟨hB',hJ',hU'⟩:=last_free b
  refine ⟨(member_last hf 0).trans ?_,(member_last hf 1).trans ?_,(member_last hf 2).trans ?_⟩ <;>
    apply div_le_div_of_nonneg_right _ (by norm_num) <;>
    simp [kK,Fin.sum_univ_three,auN,arC]
  · exact gEZ hB' hJ hJ' ((Nat.sub_le _ _).trans hB)
  · exact gEZ hJ' hU hU' hJ
  · exact gEZ hB' hU hU' hB
private theorem terminal_box (b:RectTail) :
    2*(s b).U≤357388∧(s b).B-(s b).J≤4079∧(s b).J≤1087:= by
  cases b <;> exact ⟨by decide,by decide,by decide⟩
private theorem Mo {u y j:ℕ} (hu:u≤357388) (hy :y≤4079) (hj:j≤1087) :
    (u:ℚ)*(63182/25)+(y :ℚ)*(1175744/25)+(j:ℚ)*(5290266/25)<(p:ℚ) := by
  have hn:u*63182+y*1175744+j*5290266<p*25:= by
    exact (z9f (z9f (ztf _ hu)
      (ztf _ hy)) (ztf _ hj)).trans_lt
      (show 357388*63182+4079*1175744+1087*5290266<0x7f000001*25 from by decide)
  have hq: (u:ℚ)*63182+(y :ℚ)*1175744+(j:ℚ)*5290266<(p:ℚ)*25:= by exact_mod_cast hn
  have hd:=(div_lt_iff₀ (by norm_num : (0:ℚ)<25)).mpr hq
  convert hd using 1
  ring
theorem budget_small {b:RectTail} {o:Origin} {Q:znc Ambient}
    (hf :MemberFits b o terminalStop Q) (k :Fin 3) :budget (s b) Q k<(p:ℚ) := by
  obtain ⟨h₀,h₁,h₂⟩:=masses hf
  obtain ⟨hu,hy,hj⟩:=terminal_box b
  let u:=if k=2 then 2*(s b).U else (s b).U
  have hu' : u≤357388:= by
    have hle : (s b).U≤2*(s b).U:= by omega
    by_cases hk :k=2
    · simpa only [u,ite_eq_left hk] using hu
    · simpa only [u,ite_eq_right hk] using hle.trans hu
  have hjb: (s b).J≤(s b).B:= by cases b <;> decide
  have he :budget (s b) Q k =
      (u:ℚ)*sectionMass Q 0+((s b).B-(s b).J:ℕ)*sectionMass Q 1 +
      (s b).J*sectionMass Q 2 := by
    simp [budget,u,Tl,FP,zmL,Nat.cast_sub hjb]
  rw [he]
  exact (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀ (zqJ _))
    (mul_le_mul_of_nonneg_left h₁ (zqJ _)))
    (mul_le_mul_of_nonneg_left h₂ (zqJ _))).trans_lt (Mo hu' hy hj)
end
end qPP0zte
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qPP0zte
noncomputable section
open Finset
open K1 (p)
open cu (FX Shape jz)
open gT (Ambient aQ rM iJ)
open pI (xN oU pN)
open OH
open P6_7_2_3 (sectionMass Tl)
open qu56FMb (RectCaps)
open TD (FP)
open private unflatten cSJ aue aqH bOX from ProximityPrize.SubmissionLower.AH
open private dXL from ProximityPrize.SubmissionLower.CR
open private ea0 from ProximityPrize.SubmissionLower.U
private theorem nested_caps {s :Shape} {f :Ambient} (hf :RectCaps s f) :
    oU (aqH f) ⟨0,s.B,s.J,2*s.U⟩:= by
  intro j i hij
  have hh (d:Fin 2 →₀ ℕ) (hd: (((aqH f).coeff j).coeff i).coeff d≠0) :
      i+j≤ s.B∧j≤ s.J∧d.degree≤2*s.U:= by
    let e :=(d.optionElim i).optionElim j
    let a :=e.mapDomain aue.symm
    have he :a.mapDomain aue=e := by
      ext z
      rw [Finsupp.mapDomain_equiv_apply,Finsupp.mapDomain_equiv_apply,Equiv.symm_symm,
        Equiv.apply_symm_apply]
    have hc:f.coeff a=(((aqH f).coeff j).coeff i).coeff d:= by
      rw [← MvPolynomial.coeff_rename_mapDomain aue aue.injective,he,
        ← cSJ]
      change (zHw aue f).coeff e =
        (unflatten.symm (unflatten (zHw aue f))).coeff e
      rw [RingEquiv.symm_apply_apply]
    have h0:aue 0=some (some 0) :=rfl
    have h1 :aue 1=some (some 1) :=rfl
    have h2 :aue 2=some none :=rfl
    have h3:aue 3=none :=rfl
    obtain ⟨h₀,h₁,h₂,h₃⟩:=hf a (MvPolynomial.mem_support_iff.mpr (hc.symm ▸ hd))
    simp only [a,e,Finsupp.mapDomain_equiv_apply,Equiv.symm_symm,h0,h1,h2,h3,
      Finsupp.optionElim_apply_some,Finsupp.optionElim_apply_none] at h₀ h₁ h₂ h₃
    rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]
    exact ⟨h₂,h₃,by omega⟩
  obtain ⟨d,hd⟩:=nonempty_iff_ne_empty.mpr
    (fun hz=>hij (MvPolynomial.support_eq_empty.mp hz))
  obtain ⟨hi,hj,_⟩:=hh d (MvPolynomial.mem_support_iff.mp hd)
  refine ⟨hi,hj,Finset.sup_le ?_⟩
  exact fun d hd=>(hh d (MvPolynomial.mem_support_iff.mp hd)).2.2
theorem plane_length {s :Shape} {Q:znc Ambient} {f :Ambient}
    (hs :s.J≤ s.B) (ha :xN Q) (hf :f∉Q) (hc:RectCaps s f) :
    Module.Finite aQ (N8 ⧸ bR 2 Q f) ∧
      (length (bR 2 Q f) :ℚ)≤budget s Q 2 := by
  obtain ⟨hn,hdim⟩:=cy7.proof Q ha
  obtain ⟨hp,hq⟩:=cza.proof Q ha.prime hn
  let: (Cr Q).IsPrime :=hp
  let:IsDomain (rM Q) :=inferInstanceAs (IsDomain (N8 ⧸ Cr Q))
  let g:=asi Q f
  have hg:g≠0:= by
    intro hz
    have hm:Q6 f∈Cr Q:=Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hm' : f∈(Cr Q).comap Q6:=hm
    exact hf (hq ▸ hm')
  have eq :PrincipalCut g ≃ₐ[aQ] (N8 ⧸ bR 2 Q f) := by
    have hm :
        (zye {Q6 f}).map (Ideal.Quotient.mkₐ aQ (Cr Q)) =
          zye {g} := by
      rw [Ideal.map_span,Set.image_singleton]
      rfl
    let C (L:znc (rM Q)) :=
      (rM Q ⧸ L) ≃ₐ[aQ] (N8 ⧸ bR 2 Q f)
    exact (congrArg C hm).mp (DoubleQuot.quotQuotEquivQuotSupₐ aQ (Cr Q)
      (zye {Q6 f}))
  let:Module.Finite aQ (PrincipalCut g) :=ea0 aQ _ hdim hg
  refine ⟨Module.Finite.of_surjective eq.toLinearMap eq.surjective,?_⟩
  obtain ⟨hx,hy,hz⟩:=dXL Q ha
  have :CharP aQ p:=charP_of_injective_ringHom
    ((algebraMap FX aQ).comp jz).injective p
  obtain ⟨D⟩:=bzU.proof p aQ (rM Q) hdim
    (zL Q 1) (zL Q 2) (zL Q 3)
    (by rw [hx]; exact ha.seed_size.1) (by rw [hx]; exact ha.seed_size.2)
  have hdeg:aHf aQ (rM Q) g ≤
      2*s.U*pN Q 0+(s.B-s.J)*pN Q 1+s.J*pN Q 2 := by
    rw [← hx,← hy,← hz,D.degree_eq g,D.degree_eq (zL Q 1),
      D.degree_eq (zL Q 2),D.line_eq]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q _
    have he :iJ (aqH f)=f := by rw [bOX]; exact aqH.symm_apply_apply f
    have hrow:=fZu Q (D.place q) (P:=aqH f) (s :=⟨0,s.B,s.J,2*s.U⟩)
      hs (nested_caps hc)
    rw [he] at hrow
    simpa only [g,Nat.add_mul,Nat.mul_assoc] using ztf (D.QZ q) hrow
  have hlength:=(cy9.proof aQ (rM Q) hdim g hg).trans hdeg
  rw [eq.toLinearEquiv.finrank_eq] at hlength
  simpa [budget,Tl,FP,sectionMass,zmL,Nat.cast_add,Nat.cast_mul,
    Nat.cast_sub hs,mul_assoc] using (Nat.cast_le (α:=ℚ)).mpr hlength
end
end qPP0zte
end
section
set_option autoImplicit true
namespace qkV7vfc
noncomputable section
open Polynomial
theorem sep_of_root {K κ:Type*} [zrb K] [zrb κ] [zZE K κ] (E :IntermediateField K κ)
    {R:Type*} [CommRing R] (ψ:R →+* E) (g:R[X]) (u:κ)
    (h0:g.eval₂ ((algebraMap E κ).comp ψ) u=0)
    (h1 : (derivative g).eval₂ ((algebraMap E κ).comp ψ) u≠0) :IsSeparable E u:= by
  have e : ∀ p:R[X],p.eval₂ ((algebraMap E κ).comp ψ) u=aeval u (p.map ψ) := fun p=> by
    rw [aeval_def,eval₂_map]
  rw [e] at h0 h1
  rw [← derivative_map] at h1
  generalize g.map ψ=p at h0 h1
  have hp:p≠0:= by rintro rfl; simp at h1
  have hint :IsIntegral E u:=(show IsAlgebraic E u from ⟨p,hp,h0⟩).isIntegral
  obtain ⟨q,hq⟩:=minpoly.dvd E u h0
  have h3:derivative (minpoly E u)≠0:= by
    intro h; apply h1; rw [hq,derivative_mul,h]; simp [minpoly.aeval]
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible hint)).2 h3
theorem clear_den {Ω R L:Type*} [zrb Ω] [CommRing R] [zrb L] (f :R →+* Ω) (ι:L →+* Ω)
    (hL : ∀ x :L,∃ r s :R,f s≠0∧ι x*f s=f r) (m:L[X]) :
    ∃ q:R,f q≠0 ∧ ∃ g:R[X],g.map f=C (f q)*m.map ι:= by
  induction m using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,ha,g,hg⟩:=hp
    obtain ⟨b,hb,h,hh⟩:=hq
    refine ⟨a*b,by rw [map_mul]; exact mul_ne_zero ha hb,C b*g+C a*h,?_⟩
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hg,hh,map_mul]
    ring
  | monomial n x =>
    obtain ⟨r,s,hs,hr⟩:=hL x
    refine ⟨s,hs,monomial n r,?_⟩
    rw [map_monomial,map_monomial,C_mul_monomial,← hr,mul_comm]
theorem hL_adjoin {K Ω ι:Type*} [zrb K] [zrb Ω] [zZE K Ω] (v :ι→Ω)
    (x :IntermediateField.adjoin K (zxp v)) :
    ∃ r s :z3y ι K,zIe v s≠0 ∧
      (x :Ω)*zIe v s=zIe v r := by
  obtain ⟨r,hr,s,hs,h⟩:=IntermediateField.mem_adjoin_iff_div.mp x.2
  rw [z5E] at hr hs
  obtain ⟨r',rfl⟩:=hr
  obtain ⟨s',rfl⟩:=hs
  by_cases h0:zIe v s' = 0
  · exact ⟨0,1,by simp,by simp [h,h0]⟩
  · exact ⟨r',s',h0,by rw [h]; exact div_mul_cancel₀ (zIe v r') h0⟩
theorem main {K κ Ω:Type*} [zrb K] [zrb κ] [zrb Ω] [zZE K κ] [Infinite K]
    [zZE K Ω] [zZE κ[X] Ω] [IsScalarTower K κ[X] Ω] [IsFractionRing κ[X] Ω] (a :Fin 2→κ)
    (u:Fin 4→κ) (hgen:IntermediateField.adjoin K (zxp u) = ⊤)
    (hnc : ¬ ∀ i,IsAlgebraic K (a i))
    (hsep : ∀ j,IsSeparable (IntermediateField.adjoin K (zxp
      ![algebraMap κ[X] Ω Polynomial.X,algebraMap κ[X] Ω (C (a 0)+Polynomial.X*C (a 1))]))
      (algebraMap κ[X] Ω (C (u j)))) :
    Algebra.FormallySmooth K κ:= by
  classical
  have hι:zq4 (algebraMap κ[X] (Ω)) :=
    zxb _ _
  let v :Fin 2→Ω :=
    ![algebraMap κ[X] (Ω) Polynomial.X,
      algebraMap κ[X] (Ω) (C (a 0)+Polynomial.X*C (a 1))]
  let φ:z3y (Fin 2) K →ₐ[K] κ[X] :=zIe ![Polynomial.X,C (a 0)+Polynomial.X*C (a 1)]
  have hφ: (algebraMap κ[X] (Ω)).comp φ.toRingHom =
      (zIe v :z3y (Fin 2) K →ₐ[K] _).toRingHom:= by
    have : (IsScalarTower.toAlgHom K κ[X] (Ω)).comp φ=zIe v := by
      apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [φ,v]
    rw [← this]; rfl
  have key : ∀ j,∃ g:zM1 (z3y (Fin 2) K),
      g.eval₂ φ.toRingHom (C (u j))=0 ∧
      (derivative g).eval₂ φ.toRingHom (C (u j))≠0:= by
    intro j
    obtain ⟨q,hq,g,hg⟩:=clear_den (zIe v :z3y (Fin 2) K →ₐ[K] _).toRingHom
      (algebraMap (IntermediateField.adjoin K (zxp v)) (Ω))
      (hL_adjoin v) (minpoly (IntermediateField.adjoin K (zxp v))
        (algebraMap κ[X] Ω (C (u j))))
    refine ⟨g,hι ?_,fun h => ?_⟩
    · rw [zly,hφ,map_zero,← eval_map,hg,eval_mul,
        eval_map_algebraMap,minpoly.aeval,mul_zero]
    · have h2 :=zly (derivative g) φ.toRingHom
        (algebraMap κ[X] (Ω)) (C (u j))
      rw [h,map_zero,hφ,← eval_map,← derivative_map,hg,derivative_C_mul,eval_mul,
        eval_C,derivative_map,eval_map_algebraMap] at h2
      exact mul_ne_zero (by simpa using hq)
        (Polynomial.Separable.aeval_derivative_ne_zero (hsep j) (minpoly.aeval _ _)) h2.symm
  choose g hg0 hg1 using key
  let D:Fin 4→κ[X] := fun j=>(derivative (g j)).eval₂ φ.toRingHom (C (u j))
  have hD : ∀ j,D j≠0:=hg1
  let t:K→κ:= fun c=>a 0+algebraMap K κ c*a 1
  let χ:K→z3y (Fin 2) K →ₐ[K] κ:= fun c =>
    zIe ![algebraMap K κ c,t c]
  have hev : ∀ c,(zhy (algebraMap K κ c)).comp φ.toRingHom =
      (χ c).toRingHom:= by
    intro c
    apply zXT
    · intro r; simp [φ,χ]
    · intro i; fin_cases i
      · simp [φ,χ]
      · simp [φ,χ,t]; exact mul_comm _ _
  have spec : ∀ c:K,(∀ j,(D j).eval (algebraMap K κ c)≠0) → ∀ j,
      IsSeparable (IntermediateField.adjoin K (zxp fun _:Unit=>t c)) (u j) := by
    intro c hc j
    set E :=IntermediateField.adjoin K (zxp fun _:Unit=>t c) with hE
    have hmem1 :algebraMap K κ c∈E :=E.algebraMap_mem c
    have hmem2 :t c∈E :=IntermediateField.subset_adjoin K _ ⟨(),rfl⟩
    let ψ:z3y (Fin 2) K →ₐ[K] E :=zIe ![⟨_,hmem1⟩,⟨t c,hmem2⟩]
    have hψ: (algebraMap E κ).comp ψ.toRingHom=(χ c).toRingHom:= by
      apply zXT
      · intro r; simp [ψ,χ]
      · intro i; fin_cases i <;> simp [ψ,χ]
    have h : ∀ p:zM1 (z3y (Fin 2) K),p.eval₂ (χ c).toRingHom (u j) =
        (p.eval₂ φ.toRingHom (C (u j))).eval (algebraMap K κ c) := by
      intro p
      have :=zly p φ.toRingHom (zhy (algebraMap K κ c)) (C (u j))
      rw [hev] at this
      simpa using this.symm
    apply sep_of_root E ψ.toRingHom (g j) (u j)
    · rw [hψ,h,hg0 j]; simp
    · rw [hψ,h]; exact hc j
  let Bad:Set K := {c | ∃ j,(D j).eval (algebraMap K κ c)=0}
  have hBad:Bad.Finite := by
    refine (Set.Finite.preimage (f :=algebraMap K κ) (algebraMap K κ).injective.injOn
      (Set.finite_iUnion fun j=>(D j).roots.toFinset.finite_toSet)).subset ?_
    rintro c ⟨j,hj⟩
    simp only [Set.mem_preimage,Set.mem_iUnion,Finset.mem_coe,Multiset.mem_toFinset]
    exact ⟨j,(mem_roots (hD j)).2 hj⟩
  obtain ⟨c1,hc1⟩:=((z6P (α:=K)).sdiff hBad).nonempty
  obtain ⟨c2,hc2⟩:=((z6P (α:=K)).sdiff (hBad.insert c1)).nonempty
  have hc2' : c2≠c1∧c2∉Bad:= by
    have :=hc2.2; simpa [not_or] using this
  have htr :Transcendental K (t c1)∨Transcendental K (t c2) := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1,h2⟩:=hcon
    simp only [Transcendental,not_not] at h1 h2
    apply hnc
    have m1 :t c1∈algebraicClosure K κ:=mem_algebraicClosure_iff.2 h1
    have m2 :t c2∈algebraicClosure K κ:=mem_algebraicClosure_iff.2 h2
    have hne :algebraMap K κ c1-algebraMap K κ c2≠0 :=
      sub_ne_zero.2 fun h=>hc2'.1 ((algebraMap K κ).injective h).symm
    have ma1 :a 1∈algebraicClosure K κ:= by
      have :a 1=(t c1 - t c2)/(algebraMap K κ c1-algebraMap K κ c2) := by
        simp only [t]; field_simp; ring
      rw [this]
      exact (algebraicClosure K κ).div_mem ((algebraicClosure K κ).sub_mem m1 m2)
        ((algebraicClosure K κ).sub_mem (algebraMap_mem _ _) (algebraMap_mem _ _))
    have ma0:a 0∈algebraicClosure K κ:= by
      have :a 0=t c1-algebraMap K κ c1*a 1 := by simp [t]
      rw [this]
      exact (algebraicClosure K κ).sub_mem m1
        ((algebraicClosure K κ).mul_mem (algebraMap_mem _ _) ma1)
    intro i
    fin_cases i
    · exact mem_algebraicClosure_iff.1 ma0
    · exact mem_algebraicClosure_iff.1 ma1
  obtain ⟨c,hcb,htc⟩ : ∃ c,c∉Bad∧Transcendental K (t c) := by
    rcases htr with h | h
    · exact ⟨c1,hc1.2,h⟩
    · exact ⟨c2,hc2'.2,h⟩
  have hs :=spec c (fun j hj=>hcb ⟨j,hj⟩)
  have hind:AlgebraicIndependent K (fun _:Unit=>t c) :=
    algebraicIndependent_unique_type_iff.mpr htc
  have :Algebra.IsSeparable (IntermediateField.adjoin K (zxp fun _:Unit=>t c)) κ:= by
    set E :=IntermediateField.adjoin K (zxp fun _:Unit=>t c)
    have h1 :IntermediateField.adjoin E (zxp u) = ⊤ := by
      have : (⊤ : IntermediateField K κ)≤(IntermediateField.adjoin E (zxp u)).restrictScalars K:= by
        rw [← hgen]
        exact IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin E _)
      exact eq_top_iff.2 fun x _=>this (IntermediateField.mem_top)
    have h3:IntermediateField.adjoin E (zxp u)≤ separableClosure E κ :=
      IntermediateField.adjoin_le_iff.2 (by rintro _ ⟨j,rfl⟩; exact hs j)
    have h2 :separableClosure E κ = ⊤ :=
      eq_top_iff.2 (calc (⊤ : IntermediateField E κ)= _:=h1.symm
        _≤_:=h3)
    exact (separableClosure.eq_top_iff E κ).1 h2
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hind
end
end qkV7vfc
end
section
set_option autoImplicit true
namespace qkV7vfc
noncomputable section
open cu (FX)
open gT (Ambient)
open ac3 (aYy)
open qcYgGze (CurveResidue seedValue)
def ρ (I:znc Ambient) [I.IsPrime] :Ambient →ₐ[FX] CurveResidue I :=
  { (IsLocalRing.residue (Localization.AtPrime I)).comp
      (algebraMap Ambient (Localization.AtPrime I)) with
    commutes' := fun r=> by
      change IsLocalRing.residue _ (algebraMap Ambient (Localization.AtPrime I)
        (algebraMap FX Ambient r))=algebraMap FX (CurveResidue I) r
      rw [← IsScalarTower.algebraMap_apply]; rfl }
theorem ρ_apply (I:znc Ambient) [I.IsPrime] (x :Ambient) :
    ρ I x=IsLocalRing.residue (Localization.AtPrime I)
      (algebraMap Ambient (Localization.AtPrime I) x) :=rfl
theorem ρ_eq_zero (I:znc Ambient) [I.IsPrime] (x :Ambient) :ρ I x=0↔x∈I:= by
  rw [ρ_apply]
  rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ I x
theorem gen (I:znc Ambient) [I.IsPrime] :
    IntermediateField.adjoin FX (zxp fun j:Fin 4=>ρ I (z9v j)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨y,rfl⟩:=IsLocalRing.residue_surjective z
  obtain ⟨⟨x,s⟩,rfl⟩:=IsLocalization.mk'_surjective I.primeCompl y
  have hx : ∀ x :Ambient,ρ I x∈IntermediateField.adjoin FX
      (zxp fun j:Fin 4=>ρ I (z9v j)) := fun x=> by
    have h1 :ρ I x=zIe (fun j:Fin 4=>ρ I (z9v j)) x :=
      congrArg (· x) (MvPolynomial.aeval_unique (ρ I))
    have h2 :zIe (fun j:Fin 4=>ρ I (z9v j)) x ∈
        Algebra.adjoin FX (zxp fun j:Fin 4=>ρ I (z9v j)) := by
      rw [z5E]; exact ⟨x,rfl⟩
    rw [h1]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ h2
  have hs :ρ I s≠0:= fun h=>s.2 ((ρ_eq_zero I s).1 h)
  have h3:=congrArg (IsLocalRing.residue (Localization.AtPrime I))
    (IsLocalization.mk'_spec (Localization.AtPrime I) x s)
  rw [map_mul] at h3
  have h4 :IsLocalRing.residue (Localization.AtPrime I)
      (IsLocalization.mk' (Localization.AtPrime I) x s)=ρ I x/ρ I s :=
    eq_div_of_mul_eq hs h3
  rw [h4]
  exact (IntermediateField.adjoin FX _).div_mem (hx x) (hx s)
theorem nc (I:znc Ambient) [I.IsPrime] (hnc : ¬ aYy I) :
    ¬ ∀ i,IsAlgebraic FX (seedValue I i) := by
  intro h
  apply hnc
  let ρb: (Ambient ⧸ I) →ₐ[FX] CurveResidue I :=
    Ideal.Quotient.liftₐ I (ρ I) fun x hx=>(ρ_eq_zero I x).2 hx
  have hinj:zq4 ρb:= by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((ρ_eq_zero I x).1 hy)
  intro i
  exact (isAlgebraic_algHom_iff ρb hinj).1 (h i)
theorem proof :qcYgGze.c2 := by
  intro I _ _ hnc hsep
  have :Infinite FX :=
    Infinite.of_injective (algebraMap (zM1 cu.L) FX) (zxb _ _)
  exact main (K:=FX) (Ω:=qcYgGze.SlopedResidue I) (seedValue I)
    (fun j=>ρ I (z9v j)) (gen I) (nc I hnc) fun j => @Algebra.IsSeparable.isSeparable _ _ _ _ _ hsep _
end
end qkV7vfc
end
