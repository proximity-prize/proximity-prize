import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZmCNKFc
import ProximityPrize.SubmissionLower.ZH0Zvwe
set_option Elab.async false
set_option maxHeartbeats 700000
section
set_option backward.isDefEq.respectTransparency false
namespace qvWbALd
noncomputable section
open Polynomial
open P5 (p)
open qRoCwuc (ConstantOddPart)
open private adG efd aMX from ProximityPrize.SubmissionLower.Y
open scoped WithZero
variable {F:Type} [Field F]
private theorem separable_irreducible [CharP F p] {f :F[X]}
  (hf :Irreducible f) (hd:f.natDegree<p) :f.Separable := by
 have hpos :=natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hf)
 have hn:f.natDegree - 1+1=f.natDegree := by omega
 have hc: (f.natDegree :F)≠0:= by
  rw [Ne,CharP.cast_eq_zero_iff F p]
  exact fun h=>(not_le_of_gt hd) (Nat.le_of_dvd hpos h)
 apply (separable_iff_derivative_ne_zero hf).mpr
 intro he
 have hz :=congrArg (fun g:F[X]=>g.coeff (f.natDegree - 1)) he
 have hcast:=congrArg (fun n:ℕ=>(n:F)) hn
 rw [Nat.cast_add,Nat.cast_one] at hcast
 rw [coeff_derivative,hn,coeff_natDegree,coeff_zero,hcast] at hz
 exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf.ne_zero) hc hz
private theorem separable_squarefree [CharP F p] (f :F[X]) (hs :Squarefree f)
   (hd:f.natDegree<p) :f.Separable := by
 induction f using WfDvdMonoid.induction_on_irreducible with
 | zero=>exact (hs.ne_zero rfl).elim
 | unit u hu =>
   exact ⟨↑hu.unit⁻¹,0,by simpa only [zero_mul,add_zero] using hu.val_inv_mul⟩
 | mul a b ha hb ih =>
   rw [natDegree_mul hb.ne_zero ha] at hd
   have hcop:IsCoprime b a :=(hb.isCoprime_or_dvd _).resolve_right fun h =>
     hb.not_isUnit (IsRelPrime.of_squarefree_mul hs dvd_rfl h)
   exact (separable_irreducible hb (by omega)).mul (ih hs.of_mul_right (by omega)) hcop
theorem odd_factor [CharP F p] {D:F[X]} (ht:D.natDegree<p)
   (hn : ¬ ConstantOddPart D) :
   ∃ Q G:F[X],Q.Monic∧D = Q^2*G∧G.leadingCoeff=D.leadingCoeff ∧
     0<G.natDegree∧G.Separable := by
 have hD:D ≠0:= fun h=>hn ⟨0,1,by simp [h]⟩
 obtain ⟨Q,R,he,hr⟩:=exists_sq_mul_squarefree D
 have hQ:Q≠0:= fun h=>hD (by simp [← he,h])
 let a := Q.leadingCoeff
 let q:=C a⁻¹*Q
 let g:=C (a^2)*R
 have ha :a≠0:=leadingCoeff_ne_zero.mpr hQ
 have hq:q.Monic:= by
   rw [show q= Q*C a⁻¹ by exact mul_comm ..]
   exact monic_mul_leadingCoeff_inv hQ
 have hd:D =q^2*g:= by
   rw [← he]; dsimp only [q,g]; rw [mul_pow,← map_pow,inv_pow]
   symm
   calc
     _=(C ((a^2)⁻¹)*C (a^2))*(Q^2*R) := by ring
     _= Q^2*R:= by rw [← map_mul,inv_mul_cancel₀ (pow_ne_zero _ ha),map_one,one_mul]
 have hpos :0<g.natDegree := by
   by_contra! hz
   have hg' := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hz)
   exact hn ⟨g.coeff 0,q,by rw [hd,mul_comm (q^2) g,← hg']⟩
 have hsf :Squarefree g:= by
   have hu:=(IsUnit.mk0 (a^2) (pow_ne_zero _ ha)).map (C:F →+* F[X])
   exact (show Associated R g from ⟨hu.unit,by rw [IsUnit.unit_spec]; exact mul_comm _ _⟩).squarefree_iff.mp hr
 have hle :g.natDegree≤D.natDegree :=natDegree_le_of_dvd
   ⟨q^2,hd.trans (mul_comm _ _)⟩ hD
 refine ⟨q,g,hq,hd,?_,hpos,separable_squarefree g hsf (hle.trans_lt ht)⟩
 conv_rhs=>rw [hd,leadingCoeff_mul,leadingCoeff_pow,hq.leadingCoeff,one_pow,one_mul]
theorem aNI (v :Valuation F ℤᵐ⁰) {D Q G:F[X]} (hq:Q.Monic)
  (he :D = Q^2*G) {B:ℤᵐ⁰} (hD : ∀ i,v (D.coeff i)≤B) (i:ℕ) :
  v (G.coeff i)≤B:= by
 have hq' : 1≤adG v Q:= by
  simpa only [hq.coeff_natDegree,map_one] using aMX v Q Q.natDegree
 have hD' : adG v D ≤B:=Finset.sup_le fun i _=>hD i
 rw [he,efd,pow_two,efd] at hD'
 exact (aMX v G i).trans ((le_mul_of_one_le_left'
  (one_le_mul_of_one_le_of_one_le hq' hq')).trans hD')
theorem square_factor_integral (v :Valuation F ℤᵐ⁰) {D Q G:F[X]}
  (he :D = Q^2*G) (hG:v G.leadingCoeff=1)
  (hD : ∀ i,v (D.coeff i)≤1) (i:ℕ) :v (Q.coeff i)≤1 := by
 have hg:1≤adG v G:= by
  simpa only [coeff_natDegree,hG] using aMX v G G.natDegree
 have hD' : adG v D ≤1 :=Finset.sup_le fun i _=>hD i
 rw [he,efd,pow_two,efd] at hD'
 by_contra! h
 have h1 :1<adG v Q:=h.trans_le (aMX v Q i)
 have h2 :1<adG v Q*adG v Q:= by
  simpa only [one_mul] using mul_lt_mul'' h1 h1 zero_le zero_le
 exact (not_lt_of_ge hD') (h2.trans_le (le_mul_of_one_le_right' hg))
end
end qvWbALd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qNqPG5b
noncomputable section
open Polynomial
open cu (L)
open P5 (K p)
open qbjv5ec (aQ lN EC)
open qcuqT2c (Simple zIn xIn cIn tIn)
open scoped BigOperators
open private monomialAdjoin monomialField expansion_of_mem bqo c4Q from ProximityPrize.SubmissionLower.ZmCNKFc
private def seedHom (y :EC) :aQ →+* Simple y :=
 (algebraMap lN (Simple y)).comp ((algebraMap aQ[X] lN).comp C)
private def scalarHom (y :EC) :L →+* Simple y :=
 (seedHom y).comp ((algebraMap L[X] aQ).comp C)
private theorem generic_mem (y :EC) (x :L) (S:Subfield (Simple y))
  (hc : ∀ a :L,cIn y a∈S) (hz :zIn y∈S) (ht:tIn y x∈S) (a :lN) :
  algebraMap lN (Simple y) a∈S:= by
 have hx :xIn y∈S:= by simpa only [tIn,sub_add_cancel] using S.add_mem ht (hc x)
 have hs (u:aQ) :seedHom y u∈S :=
  bqo S (seedHom y)
    (c4Q S ((seedHom y).comp (algebraMap L[X] aQ)) hc hz) u
 exact bqo S (algebraMap lN (Simple y))
  (c4Q S ((algebraMap lN (Simple y)).comp
    (algebraMap aQ[X] lN)) hs hx) a
theorem proof :qcuqT2c.c1 := by
 intro y hy x a
 let const:L →+* lN :=
   (algebraMap aQ[X] lN).comp
     (C.comp ((algebraMap L[X] aQ).comp C))
 let:ExpChar lN p:=expChar_of_injective_ringHom
   (const.comp (algebraMap K L)).injective p
 let:ExpChar (Simple y) p:=expChar_of_injective_algebraMap
   (algebraMap lN (Simple y)).injective p
 let:Algebra.IsSeparable lN (Simple y) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hy
 let S:=monomialField p (zIn y) (tIn y x)
 have c48 (u:Simple y) :u^p∈S :=
   (monomialAdjoin p (zIn y) (tIn y x)).algebraMap_mem ⟨u^p,u,rfl⟩
 have hc (b:L) :cIn y b∈S:= by
   obtain ⟨c,h⟩:=IsAlgClosed.exists_pow_nat_eq b (expChar_pos (Simple y) p)
   change scalarHom y b∈S
   rw [← h,map_pow]
   exact c48 _
 have hz :zIn y∈S:=IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
 have ht:tIn y x∈S :=
   IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
 let I:=S.toIntermediateField (generic_mem y x S hc hz ht)
 have hi:IntermediateField.adjoin lN ((· ^ p) '' (Set.univ :Set (Simple y)))≤I:= by
   apply IntermediateField.adjoin_le_iff.mpr
   rintro _ ⟨b,-,rfl⟩
   exact c48 b
 rw [← IntermediateField.adjoin_eq_adjoin_pow_expChar_of_isSeparable' lN (Simple y)
   Set.univ p,IntermediateField.adjoin_univ] at hi
 exact expansion_of_mem p (zIn y) (tIn y x) (hi (show a ∈ ⊤ from trivial))
end
end qNqPG5b
end
section
namespace qbY56ta
open Polynomial
open P5 (p)

open scoped WithZero
private theorem residue_sum_ne {K:Type} [Field K] {q:ℕ} [CharP K q]
    (hq:q.Prime) {u:K} (hu : ∀ x :K,x^q≠u)
    (a :Fin q→K) (i:Fin q) (hi:a i≠0) :
    (∑ l,a l^q*u^(l:ℕ))≠0:= by
  classical
  let f :K[X] :=Polynomial.X ^q - C u
  let:Fact (Irreducible f) :=⟨X_pow_sub_C_irreducible_of_prime hq hu⟩
  let:CharP (AdjoinRoot f) q :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective q
  let:Fact q.Prime :=⟨hq⟩
  let g:K[X] := ∑ l:Fin q,monomial (l:ℕ) (a l)
  have hc:g.coeff (i:ℕ)=a i:= by
    simp only [g,finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · exact coeff_monomial_same _ _
    · intro l _ hli
      exact coeff_monomial_of_ne _ (fun he=>hli (Fin.ext he.symm))
    · simp
  have hg:g≠0:= fun h=>hi (hc.symm.trans (by rw [h,coeff_zero]))
  have hd:g.natDegree<q:= by
    apply lt_of_le_of_lt
      (natDegree_sum_le_of_forall_le Finset.univ _ (n:=q - 1) fun l _ =>
        (natDegree_monomial_le (a l)).trans (Nat.le_sub_one_of_lt l.isLt))
    exact Nat.sub_lt hq.pos (by decide)
  have hm:AdjoinRoot.mk f g≠0:=AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (monic_X_pow_sub_C u hq.ne_zero) hg (by simpa only [f,natDegree_X_pow_sub_C] using hd)
  have hr : (AdjoinRoot.root f)^q=AdjoinRoot.of f u:=root_X_pow_sub_C_pow q u
  have he :AdjoinRoot.mk f g = ∑ l:Fin q,AdjoinRoot.of f (a l)*AdjoinRoot.root f^(l:ℕ) := by
    simp only [g,← C_mul_X_pow_eq_monomial,map_sum,map_mul,map_pow,AdjoinRoot.mk_C,
      AdjoinRoot.mk_X]
  intro hs
  apply pow_ne_zero q hm
  rw [he,sum_pow_char,← map_zero (AdjoinRoot.of f),← hs,map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_pow,pow_right_comm,hr,map_mul,map_pow,map_pow]
private theorem row_value {E :Type} [Field E] {q:ℕ} [CharP E q] (v :Valuation E ℤᵐ⁰)
   {z :E} (hz :v z=1) (hq:q.Prime)
   (hres : ∀ a :IsLocalRing.ResidueField v.valuationSubring,
     a^q≠IsLocalRing.residue v.valuationSubring ⟨z,hz.le⟩)
   (a :Fin q→E) (k :Fin q) (hk : ∀ i,v (a i)≤v (a k)) :
   v (∑ i,a i^q*z^(i:ℕ))=v (a k)^q:= by
 by_cases hb:a k=0
 · have ha (i:Fin q) :a i=0:=v.zero_iff.mp
     (le_antisymm ((hk i).trans_eq (v.zero_iff.mpr hb)) zero_le)
   simp only [ha,zero_pow hq.ne_zero,zero_mul,Finset.sum_const_zero,map_zero]
 let R:=v.valuationSubring
 let U:Fin q→R:= fun i=>⟨a i/a k,by
   change v (a i/a k)≤1
   rw [v.map_div,div_le_one₀ (v.pos_iff.mpr hb)]
   exact hk i⟩
 let zu:R:=⟨z,hz.le⟩
 let S:R := ∑ i:Fin q,U i^q*zu^(i:ℕ)
 let ρ:=IsLocalRing.residue R
 let:CharP R q:= by
   constructor
   intro n
   rw [← CharP.cast_eq_zero_iff E q n,← map_natCast R.subtype,
     map_eq_zero_iff R.subtype R.subtype_injective]
 let:CharP (IsLocalRing.ResidueField R) q :=
   CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
 have hU:U k=1 :=Subtype.ext (div_self hb)
 have hUk :ρ (U k)≠0:= by rw [hU,map_one]; exact one_ne_zero
 have hs :ρ S≠0:= by
   simp only [S,map_sum,map_mul,map_pow]
   exact residue_sum_ne hq hres (ρ ∘ U) k hUk
 have hsV:v (S:E)=1 :=le_antisymm S.property (le_of_not_gt fun h =>
   hs ((IsLocalRing.residue_eq_zero_iff S).2 (v.mem_maximalIdeal_iff.2 h)))
 have hS: (S:E) = ∑ i:Fin q,(a i/a k)^q*z^(i:ℕ) := by
   calc
     (S:E)=R.subtype S:=(ValuationSubring.subtype_apply S).symm
     _ = _:= by simp only [S,map_sum,map_mul,map_pow]; rfl
 have hscale : (∑ i:Fin q,a i^q*z^(i:ℕ))=a k^q*(S:E) := by
   rw [hS,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [← mul_assoc,← mul_pow,mul_comm (a k) (a i/a k),div_mul_cancel₀ _ hb]
 rw [hscale,map_mul,map_pow,hsV,mul_one]
private theorem row_index {q e :ℕ} (hq:q.Prime) (he0:0<e) (he :e<q)
    {j k :Fin q} {a b:ℤ}
    (h: (q:ℤ)*a-(j:ℕ)*(e :ℤ)=(q:ℤ)*b-(k :ℕ)*(e :ℤ)) :
    j=k := by
  have hprod: (q:ℤ)∣(e :ℤ)*((j:ℕ)-(k :ℕ) :ℤ) :=
    ⟨a - b,by linear_combination -h⟩
  have he' : ¬(q:ℤ)∣(e :ℤ) := fun h =>
    (Nat.not_le_of_lt he) (Nat.le_of_dvd he0 (Int.natCast_dvd_natCast.mp h))
  have hdiv :=((Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hprod).resolve_left he'
  have hdiff : ((j:ℕ)-(k :ℕ) :ℤ)=0:= by
    have hj:=j.isLt
    have hk :=k.isLt
    by_cases hle : (0:ℤ)≤((j:ℕ)-(k :ℕ) :ℤ)
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hle (by omega) hdiv
    · have hn:=Int.eq_zero_of_dvd_of_nonneg_of_lt (n:=(q:ℤ))
        (m := -((j:ℕ)-(k :ℕ) :ℤ)) (by omega) (by omega) (Int.dvd_neg.mpr hdiv)
      omega
  exact Fin.ext (by omega)
theorem proof :qcuqT2c.c2 := by
 classical
 intro E _ _ v z t hv c i j
 obtain ⟨e,he0,he,ht⟩:=hv.ramified
 have hp:p.Prime :=CharP.char_prime_of_ne_zero E ((he0.trans he).ne')
 have ht0:v t≠0:=ht.trans_ne WithZero.exp_ne_zero
 have htop (l:Fin p) : ∃ k :Fin p,∀ i,v (c l i)≤v (c l k) := by
   obtain ⟨k,_,hk⟩:=Finset.exists_max_image Finset.univ (fun i=>v (c l i))
     ⟨i,Finset.mem_univ i⟩
   exact ⟨k,fun i=>hk i (Finset.mem_univ i)⟩
 choose top htop using htop
 let F:Fin p→E := fun l=>(∑ i,c l i^p*z^(i:ℕ))*t^(l:ℕ)
 have hF (l:Fin p) :v (F l)=v (c l (top l))^p*v t^(l:ℕ) := by
   dsimp only [F]
   rw [map_mul,row_value v hv.seed_unit hp hv.seed_not_power (c l) (top l) (htop l),map_pow]
 have hterm :v (c j i^p*z^(i:ℕ)*t^(j:ℕ))≤v (F j) := by
   simp only [hF,map_mul,map_pow,hv.seed_unit,one_pow,mul_one]
   exact mul_le_mul_of_nonneg_right (pow_le_pow_left' (htop j i) p) zero_le
 have hsum (l:Fin p) :F l = ∑ i:Fin p,c l i^p*z^(i:ℕ)*t^(l:ℕ) :=
   by simp only [F,Finset.sum_mul]
 simp_rw [← hsum]
 obtain ⟨m,hm,hmax⟩:=Finset.exists_max_image Finset.univ (fun l=>v (F l))
   ⟨j,Finset.mem_univ j⟩
 refine hterm.trans ((hmax j (Finset.mem_univ j)).trans ?_)
 by_cases hm0:v (F m)=0
 · rw [hm0]
   exact zero_le
 have hlog (l:Fin p) (hl:v (F l)≠0) :
     WithZero.log (v (F l))=(p:ℤ)*WithZero.log (v (c l (top l)))-(l:ℕ)*(e :ℤ) := by
   have hc:v (c l (top l))≠0:= fun h=>hl (by
     rw [hF,h,zero_pow hp.ne_zero,zero_mul])
   rw [hF,WithZero.log_mul (pow_ne_zero _ hc) (pow_ne_zero _ ht0),
     WithZero.log_pow,WithZero.log_pow,ht,WithZero.log_exp]
   simp only [nsmul_eq_mul,mul_neg,sub_eq_add_neg]
 apply (v.map_sum_eq_of_lt hm ?_).ge
 intro l hl
 obtain ⟨hlu,hlm⟩:=Finset.mem_sdiff.mp hl
 apply lt_of_le_of_ne (hmax l hlu)
 intro heq
 have hl0:v (F l)≠0:=heq.trans_ne hm0
 have logs :=congrArg WithZero.log heq
 rw [hlog l hl0,hlog m hm0] at logs
 exact hlm (Finset.mem_singleton.mpr (row_index hp he0 he logs))
end qbY56ta
end
section
set_option backward.isDefEq.respectTransparency false
namespace qGA3mAd
noncomputable section
open IsDedekindDomain IsLocalRing Polynomial
open P5 (K p)
open qbjv5ec
open qcuqT2c
theorem proof :c3:= by
  intro y hy hdeg x a ha
  let A:=NodeRing x
  let E :=Simple y
  let B:=integralClosure A E
  let:IsScalarTower A B E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let:Algebra.IsSeparable lN E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hy
  let:Module.Finite lN E :=IntermediateField.finiteDimensional_adjoin
    (fun b hb=>(Set.mem_singleton_iff.mp hb).symm ▸ hy.isIntegral)
  let:IsDiscreteValuationRing A:=nodeDvr x
  let:Module.IsTorsionFree A E := .trans_faithfulSMul A lN E
  let:Module.Free A B:=IsIntegralClosure.module_free A lN E B
  let:Module.Finite A B:=IsIntegralClosure.finite A lN E B
  let:IsDedekindDomain B:=IsIntegralClosure.isDedekindDomain A lN E B
  let:IsFractionRing B E :=integralClosure.isFractionRing_of_finite_extension lN E
  let:Algebra.IsIntegral A B:=IsIntegralClosure.isIntegral_algebra A E
  have hB:Module.finrank A B<p:=(IsIntegralClosure.rank A lN E B).symm ▸ hdeg
  have hp:p.Prime :=(CharP.char_is_prime_or_zero K p).resolve_right (by decide)
  have ht0:algebraMap A B (nodeParameter x)≠0 :=
    fun h=>nodeParameter_ne_zero x (FaithfulSMul.algebraMap_injective A B (h.trans (map_zero _).symm))
  have hcoord (b:aQ[X]) :
      algebraMap B E (algebraMap A B (algebraMap aQ[X] A b)) =
        algebraMap lN E (algebraMap aQ[X] lN b) := by
    rw [← IsScalarTower.algebraMap_apply A B E,IsScalarTower.algebraMap_apply A lN E,
      ← IsScalarTower.algebraMap_apply aQ[X] A lN]
  have hz :algebraMap B E (algebraMap A B (nodeSeed x))=zIn y :=hcoord _
  have ht:algebraMap B E (algebraMap A B (nodeParameter x))=tIn y x := by
    rw [hcoord]
    simp only [uniformizer,map_sub]
    rfl
  have hvals (q:HeightOneSpectrum B) :q.valuation E a≤1 := by
    let:q.asIdeal.LiesOver (maximalIdeal A) :=
      ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩
    apply ha (q.valuation E)
    rw [← hz,← ht]
    exact tame_of_adic q (nodeMaximal x) ht0 (nodeSeed_isUnit x) hp hB
      (nodeSeed_not_power x hp.one_lt)
  obtain ⟨b,rfl⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one (R:=B) E a hvals
  exact b.property
end
end qGA3mAd
end
