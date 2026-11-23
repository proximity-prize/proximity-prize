import ProximityPrize.SubmissionLower.ZvFuy6d
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open _root_ renaming Algebra.algebraMap→c9,CommRing→nI,DecompositionMonoid→ ox,Fin.sum_univ_two→ oK,Finset.filter_subset→pz,Finset.prod_dvd_prod_of_subset→ oY,Function.Injective→n5,Ideal.mem_span_singleton→pU,Ideal.span→ ov,IsDomain→ oj,IsRelPrime→lJ,Module.Finite→ oy,Module.Flat→nX,Multiset.toFinset_prod_dvd_prod→pG,MvPolynomial→lI,MvPolynomial.map→ oz,MvPolynomial.optionEquivRight→p5,Nat.mul_le_mul_left→ oZ,P5_8.Equation→aU,PolynomialDifferential.jetDegree→cy,PolynomialDifferential.jetTotalDegree→mD,PolynomialDifferential.separant→lz,ReedSolomon.HiddenDerivative.SourceColumn.interpolant→lV,StrongNormalizationMonoid→pL,Submodule→ oq,UniqueFactorizationMonoid→pQ,UniqueFactorizationMonoid.strongNormalizationMonoid→pC,apQ.initial→ oD,ringChar→nq
section
set_option autoImplicit true
namespace qyOiD7d
open i4 (K p)

open P5_8_3 (mem_nativeBand)
open PolynomialDifferential MvPolynomial
private theorem separant_not_dvd {F:aU} {i:Fin 3}
  (hF:F≠0) (hi:0<cy F i) (hc:cy F i< nq K) :
  ¬ F∣lz F i:= by
 have hn:=separant_ne_zero F i
  (jetDegreeCastsNeZero_of_ringChar (Or.inr hc) _ hi le_rfl)
 have hd:=jetDegree_separant_le_sub_one F i
 rintro ⟨S,he⟩
 have hS:S≠0:= fun h=>hn (by rw [he,h,mul_zero])
 unfold cy at hd hi
 rw [he,degreeOf_mul_eq hF hS] at hd
 omega
private theorem cNr (i:Fin 3) {F:aU} (hF:Prime F)
    (hsep : ¬ F∣lz F i) (a :ℕ) (ha :a< nq K)
    {S:aU} (hS : ¬ F∣S) :
    ¬ F∣jetDerivative (F^a*S) i a := by
  induction a generalizing S with
  | zero=>simpa only [pow_zero,one_mul,jetDerivative_zero] using hS
  | succ a ih =>
    let V:=((a+1 :ℕ) :aU)*(lz F i*S)+F*lz S i
    have hstep:lz (F^(a+1)*S) i=F^a*V:= by
      rw [lz ,pderiv_mul,pderiv_pow,Nat.add_sub_cancel,pow_succ F a]
      dsimp only [V,lz]
      ring
    have hu:IsUnit ((a+1 :ℕ) :aU) := by
      rw [← map_natCast (C:K →+* aU)]
      exact (isUnit_iff_ne_zero.mpr
        (natCast_ne_zero_of_ringChar_eq_zero_or_lt (Or.inr ha) (Nat.succ_pos _) le_rfl)).map C
    have hV : ¬ F∣V:= by
      intro hd
      have h:=(dvd_add_left (dvd_mul_right F (lz S i))).mp hd
      exact (hF.dvd_or_dvd (hu.dvd_mul_left.mp h)).elim hsep hS
    rw [jetDerivative_eq_iterate,Function.iterate_succ_apply]
    change ¬ F∣jetDerivative (lz (F^(a+1)*S) i) i a
    rw [hstep]
    exact ih (Nat.lt_of_succ_lt ha) hV
private theorem exact_power {F R:aU} {l:ℕ}
   (h : ¬ F^l∣R) : ∃ a<l,F^a∣R ∧ ¬ F^(a+1)∣R:= by
 induction l with
 | zero=>exact (h (by rw [pow_zero]; exact one_dvd _)).elim
 | succ a ih =>
   by_cases hd:F^a∣R
   · exact ⟨a,Nat.lt_succ_self a,hd,h⟩
   · obtain ⟨b,hb,hdiv,hnext⟩:=ih hd
     exact ⟨b,hb.trans (Nat.lt_succ_self a),hdiv,hnext⟩
theorem proof :P5_8_3.c3:= by
 intro F R l hF hpos hsmall hband hderiv
 obtain ⟨i,hi⟩ : ∃ i:Fin 3,0<cy F i:= by
  by_contra! hn
  have hw:=jetTotalDegree_le_mul F hn
  simp only [Nat.mul_zero] at hw
  exact (Nat.not_lt_of_ge hw) hpos
 have hchar :nq K=p:=ringChar.eq K p
 have hf :cy F i< nq K:= by
  rw [hchar]
  exact (jetDegree_le_total F i).trans_lt (hsmall.trans_lt (by decide))
 have hr :cy R i< nq K:= by
  rw [hchar]
  exact (jetDegree_le_total R i).trans_lt ((mem_nativeBand.mp hband).1.trans_lt (by decide))
 by_contra hnot
 obtain ⟨a,hal,⟨S,hRS⟩,hnext⟩:=exact_power hnot
 have hR:R≠0:= by
  rintro rfl
  exact hnot (dvd_zero _)
 have hS:S≠0:= fun h=>hR (by rw [hRS,h,mul_zero])
 have hquot : ¬ F∣S:= by
  rintro ⟨U,rfl⟩
  exact hnext ⟨U,hRS.trans (by rw [pow_succ F a,mul_assoc])⟩
 have hdeg:cy R i=a*cy F i+jetDegree S i:= by
  rw [hRS]
  simp only [cy ,degreeOf_mul_eq (pow_ne_zero _ hF.ne_zero) hS,
    degreeOf_pow_eq _ _ _ hF.ne_zero]
 have ha :a≤ cy R i:= by
  rw [hdeg]
  calc
    a=a*1 :=(Nat.mul_one a).symm
    _≤a*cy F i:=oZ a hi
    _≤_:=Nat.le_add_right _ _
 exact cNr i hF.prime (separant_not_dvd hF.ne_zero hi hf)
  a (ha.trans_lt hr) hquot (hRS ▸ hderiv i a hal)
end qyOiD7d
end
section
set_option autoImplicit true
namespace qVHZuid
noncomputable section
open i4 P5_8 PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance :pL Equation :=
 pC
private def cVd:aU →+* BL 2 :=
 (oz apQ.RG).comp
   (p5 K (Fin 3)).toAlgHom.toRingHom
private theorem initialHom_apply (F:aU) :cVd F=oD F :=
 (apQ.b6h F).symm
private theorem initial_unit {F:aU} (hn:F≠0) (hd:mD F=0) :
  IsUnit (cVd F) := by
 rw [initialHom_apply]
 have hdeg: (oD F).totalDegree=0 :=
  (congrArg Jn.B (P5_8_3.initial_caps F)).trans hd
 have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
 have hc: (oD F).coeff 0≠0:= by
  intro hz
  exact apQ.b6j hn (by rw [he,hz,map_zero])
 rw [he]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem proof :P5_8_3.c4 := by
  classical
  intro Q P hQ _
  obtain ⟨L,R,D,hrel,hL,hR⟩:=exists_reduced_factors Q hQ P
  have hDQ:D ∣Q:=⟨L,hL.symm⟩
  have hDP:D ∣P:=⟨R,hR.symm⟩
  have hD:=ne_zero_of_dvd_ne_zero hQ hDQ
  let fs :=normalizedFactors D
  let js :=fs.toFinset.filter (fun F=>0< mD F)
  let G:Equation := ∏ F∈js,F
  have hmem {F:aU} (hf :F∈js) :F∈normalizedFactors D :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hf).1
  have hprod:Associated fs.prod D:=prod_normalizedFactors hD
  have hG:G∣D :=
    (oY js fs.toFinset id (pz _ _)).trans
      ((pG fs).trans hprod.dvd)
  refine ⟨⟨G,D,L,R,hG,hL.symm,hR.symm,hrel,?_,?_⟩⟩
  · refine ⟨fs.card,?_⟩
    rw [← initialHom_apply,← initialHom_apply]
    refine (map_dvd cVd hprod.symm.dvd).trans ?_
    rw [map_multiset_prod]
    have hf (F:aU) (hm:F∈fs) :cVd F∣cVd G:= by
      by_cases hj:0< mD F
      · exact map_dvd cVd (Finset.dvd_prod_of_mem id
          (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hm,hj⟩:F∈js))
      · exact (initial_unit (ne_zero_of_mem_normalizedFactors hm) (Nat.eq_zero_of_not_pos hj)).dvd
    simpa only [Multiset.map_const',Multiset.prod_replicate] using
      (Multiset.prod_dvd_prod_of_dvd cVd (fun _=>cVd G) hf)
  · intro T l hall
    unfold G
    rw [← Finset.prod_pow]
    have hirr (F:aU) (hf :F∈js) :Irreducible F :=
      irreducible_of_normalized_factor F (hmem hf)
    apply Finset.prod_dvd_of_isRelPrime
    · intro F hf E he hne
      exact ((hirr F hf).isRelPrime_iff_not_dvd.mpr
        (fun hd=>hne (normalizedFactors_eq_of_dvd D F (hmem hf) E (hmem he) hd))).pow
    · intro F hf
      have hd:=dvd_of_mem_normalizedFactors (hmem hf)
      exact hall F (hirr F hf) (hd.trans hDQ) (hd.trans hDP) (Finset.mem_filter.mp hf).2
end
end qVHZuid
end
section
set_option autoImplicit true
namespace q0KdFsb
noncomputable section
open i4 apQ MvPolynomial RingTheory.Sequence
open scoped Pointwise Polynomial
private theorem regular_pair_iff {R:Type*} [nI R] [oj R]
   [ox R] {a b:R} (ha :a≠0) :
   IsWeaklyRegular R [a,b]↔lJ a b:= by
 rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff]
 have hreg:IsSMulRegular R a := fun _ _ h=>mul_left_cancel₀ ha h
 rw [and_iff_right hreg]
 have hI:a•(⊤ : oq R R)=(ov {a} : Ideal R) := by
   rw [← Submodule.ideal_span_singleton_smul]
   exact Ideal.mul_top (ov ({a} : Set R))
 unfold QuotSMulTop
 rw [hI,isSMulRegular_iff_right_eq_zero_of_smul]
 let q:=Ideal.Quotient.mk (ov {a})
 change (∀ x,b•x=0→x=0)↔lJ a b
 have hq (x :R) :q x=0↔a∣x := by
   rw [Ideal.Quotient.eq_zero_iff_mem,pU]
 constructor
 · intro h d hdA hdB
   obtain ⟨u,hu⟩:=hdA
   obtain ⟨v,hv⟩:=hdB
   have hm:a∣b*u:=⟨v,by rw [hv,hu]; ac_rfl⟩
   have hz :b•q u=0:=(hq _).mpr hm
   obtain ⟨w,hw⟩:=(hq _).mp (h _ hz)
   exact isUnit_iff_dvd_one.mpr ⟨w,mul_left_cancel₀ ha (calc
     a*1=d*u:= by rw [mul_one,hu]
     _=a*(d*w) := by rw [hw]; ac_rfl)⟩
 · intro h x hx
   obtain ⟨u,rfl⟩:=Ideal.Quotient.mk_surjective x
   exact (hq _).mpr (h.dvd_of_dvd_mul_left ((hq _).mp hx))
private theorem flat_relPrime {R S:Type*} [nI R] [nI S] [oj R]
   [oj S] [ox R] [ox S] [Algebra R S]
   [nX R S] (hinj:n5 (c9 R S))
   {a b:R} (h:lJ a b) :lJ (c9 R S a) (c9 R S b) := by
 by_cases ha :a=0
 · subst a
   rw [map_zero,isRelPrime_zero_left]
   exact (isRelPrime_zero_left.mp h).map (c9 R S)
 have ha' : c9 R S a≠0:= fun h0=>ha (hinj (h0.trans (map_zero _).symm))
 exact (regular_pair_iff ha').mp
   ((regular_pair_iff ha).mpr h |>.of_flat)
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem map_relPrime {R S σ:Type*} [nI R] [nI S] [oj R]
    [oj S] [pQ R] [pQ S] [Algebra R S]
    [nX R S] (hinj:n5 (c9 R S))
    {a b:lI σ R} (h:lJ a b) :
    lJ (oz (c9 R S) a) (oz (c9 R S) b) := by
  have :nX (lI σ R) (lI σ S) :=
    Module.Flat.isBaseChange R (lI σ R) S (lI σ S)
      (Algebra.IsPushout.out (R:=R) (S:=lI σ R) (R' := S)
        (S' := lI σ S))
  exact flat_relPrime (MvPolynomial.map_injective _ hinj) h
theorem proof :P5_8_3.c5:= by
 intro L R h
 let e :=p5 K (Fin 3)
 have he :lJ (e L) (e R) :=
  IsRelPrime.of_map e.symm (by simpa only [AlgEquiv.symm_apply_apply] using h)
 have :nX K[X] FX:=IsLocalization.flat _ (nonZeroDivisors K[X])
 have :nX K[X] nU:=Module.Flat.trans K[X] FX nU
 have hcenter :c9 K[X] nU=RG:=IsScalarTower.algebraMap_eq K[X] FX nU
 have hi:n5 (c9 K[X] nU) :=hcenter.symm ▸ bch
 rw [b6h,b6h,← hcenter]
 exact map_relPrime hi he
end
end q0KdFsb
end
section
set_option autoImplicit true
namespace qmRQvQa
noncomputable section
open i4 P5_8 P5_8_3 PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open private bYf from ProximityPrize.SubmissionLower.CS


set_option backward.isDefEq.respectTransparency false
theorem finiteWeighted {d:ℕ} (v :JetVariable d→ℕ) (hv : ∀ i,v i≠0) (T:ℕ) :
  oy K (restrictWeightedDegree v T:oq K (DifferentialPolynomial K d)) :=
 Module.Finite.iff_fg.mpr (restrictWeightedDegree_fg v hv T)
instance finiteRows (w:Node→K) (T:ℕ) :oy K (rows w T) := by
 let:=finiteWeighted (differentialWeight (d:=2) N) (by
   intro i
   cases i with
   | none=>decide
   | some j=>exact (differentialWeight_some_pos_of_order_lt_degree (by decide :2<N) j).ne') T
 exact Submodule.finiteDimensional_of_le
   (show rows w T≤ restrictWeightedDegree (differentialWeight N) T from
     fun _ h=>h.1.2)
private theorem matrix_dimension (a :ℕ) (s :Source) (hshape :Rz s)
    (hb:N*s.B≤ s.m*a) (hp:0<s.m*a) (w:Node→K)
    (V:oq K aU) [oy K V]
    (hV : ∀ R:aU,R∈nativeBand ⟨s.B,s.J,s.C⟩ →
      differentialWeightedDegree N R<s.m*a →
      (∀ i,SatisfiesLocalConstraints s.m (node i) (w i) R)→R∈V) :
    Fintype.card (apU a s)≤Vv a s w+Module.finrank K V:= by
  classical
  let cols :=column a s
  let M:=localConstraintMatrix s.m (fun i=>node i) w cols
  let f : (apU a s→K) →ₗ[K] Equation := {
    toFun:=lV cols
    map_add' v z := by
      simp only [lV,Pi.add_apply,map_add,Finset.sum_add_distrib]
    map_smul' c v := by
      simp only [lV,Pi.smul_apply,map_smul,
        Finset.smul_sum,RingHom.id_apply] }
  have hf (v :M.mulVecLin.ker) :f v.val∈V:= by
    have hsupp (u) (hu:u∈(f v.val).support) : ∃ i,u=(cols i).exponent:= by
      apply amZ.ef8 (RingHom.id K) cols v.val u
      change u∈(lV cols v.val).support at hu
      simpa only [MvPolynomial.map_id] using hu
    refine hV _ ?_ ?_ ?_
    · refine mem_nativeBand.mpr ⟨?_,?_,?_⟩
      · apply Finset.sup_le
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change totalJetDegree (cols i).exponent≤ s.B
        simpa [cols,column,Jet.q,oK,Nat.add_assoc] using
          (hshape.support _ i.1.property).1
      · apply Finset.sup_le
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change (cols i).exponent.weight i4.indexWeight≤ s.J
        simpa [cols,column,i4.indexWeight,SourceColumn.weight_exponent,oK,
          Jet.v,Nat.mul_comm] using (hshape.support _ i.1.property).2.1
      · apply MvPolynomial.degreeOf_le_iff.mpr
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change (cols i).exponent (some (1 :Fin 2).succ)≤ s.C
        rw [SourceColumn.exponent_succ]
        exact (hshape.support _ i.1.property).2.2
    · apply (Finset.sup_lt_iff hp).mpr
      intro u hu
      obtain ⟨i,rfl⟩:=hsupp u hu
      have hx :=i.2.isLt
      have hq:=(oZ N (hshape.support _ i.1.property).1).trans hb
      simp only [width,Jet.q,Jet.v,N] at hx hq
      rw [SourceColumn.weight_exponent]
      simp [cols,column,differentialWeight,oK,N]
      omega
    · exact (localConstraintMatrix_mulVec_eq_zero_iff s.m node w cols v.val).mp v.property
  let g:M.mulVecLin.ker →ₗ[K] V :=
    (f.comp M.mulVecLin.ker.subtype).codRestrict V hf
  have hg:n5 g:= by
    intro v z h
    have he :f v.val=f z.val :=congrArg Subtype.val h
    apply Subtype.ext
    funext i
    have hc:=congrArg (fun Q:aU=>Q.coeff (cols i).exponent) he
    change (lV cols v.val).coeff (cols i).exponent =
      (lV cols z.val).coeff (cols i).exponent at hc
    have ci:n5 cols :=bYf a s
    simpa only [SourceColumn.coeff_interpolant ci] using hc
  have hdim:=LinearMap.finrank_le_finrank_of_injective hg
  have hrank :=M.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  change Vv a s w+Module.finrank K M.mulVecLin.ker =
    Fintype.card (apU a s) at hrank
  exact hrank.ge.trans (Nat.add_le_add_left hdim _)
end
end qmRQvQa
end
