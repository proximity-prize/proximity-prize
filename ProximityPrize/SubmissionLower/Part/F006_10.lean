import ProximityPrize.SubmissionLower.Part.F006_09
section Compact_PackedLegacy
section PackedLegacy_O8
namespace ProximityPrize.SubmissionLower.RCN281
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)

def yProjection (T:Type*) [Field T]:
   MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0]
def yEmbedding (T:Type*) [Field T]:
   Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
theorem y_only_vars {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (i:Fin 3) (hi:i∈S.vars):i=0:=by
 fin_cases i
 · rfl
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hZ)
theorem yProjection_reconstruct {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yEmbedding T (yProjection T S)=S:=by
 change ((yEmbedding T).comp (yProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yEmbedding,yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yEmbedding,yProjection]
 · rfl
theorem yProjection_nonzero {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yProjection T S≠0:=by
 intro hz
 apply hS
 rw [←yProjection_reconstruct S hR hZ,hz,map_zero]
theorem yProjection_natDegree_le {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T):
   (yProjection T S).natDegree ≤ S.degreeOf 0:=by
 classical
 have hsum:yProjection T S=
     ∑ d∈S.support,yProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro d hd
 have hmono:(yProjection T (MvPolynomial.monomial d (S.coeff d))).natDegree ≤
     d 0:=by
   have heq:MvPolynomial.monomial d (S.coeff d)=
       MvPolynomial.C (S.coeff d)*MvPolynomial.X 0^d 0*
         MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
     exact RCN080.monomial_fin3 d (S.coeff d)
   rw [heq]
   by_cases h1:d 1=0 <;> by_cases h2:d 2=0 <;>
     simp [yProjection,h1,h2]
   have hc:(Polynomial.C (S.coeff d)).natDegree ≤ 0:=by simp
   have hx:((Polynomial.X:Polynomial T)^d 0).natDegree ≤ d 0:=by simp
   simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hc hx
 exact hmono.trans (MvPolynomial.monomial_le_degreeOf 0 hd)
theorem yProjection_eval {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (v:Fin 3 → T):
   (yProjection T S).eval (v 0)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 0)).comp (yProjection T)) S=
   (MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yProjection]
 · rfl
def yWeights:Fin 4 → ℕ:=![0,1,0,0]
def zWeights:Fin 4 → ℕ:=![0,0,0,1]
theorem degreeY_le_yWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 1 ≤ MvPolynomial.weightedTotalDegree yWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree yWeights hd
 rw [weight_fin4] at h
 simpa [yWeights] using h
theorem degreeZ_le_zWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 3 ≤ MvPolynomial.weightedTotalDegree zWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree zWeights hd
 rw [weight_fin4] at h
 simpa [zWeights] using h
theorem singular_seedless_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,
     specialization K S 0 (singularAuxiliary Q)=0):
   Gamma.card ≤ singularListCap:=by
 classical
 let phi:=polynomialEmbedding K
 let J:=singularAuxiliary Q
 have hcaps:=seedless_degree_caps K Q hbox
 have hJne:J≠0:=singularAuxiliary_nonzero Q hQ prime
   (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
 have hJR:J.degreeOf 2=0:=singularAuxiliary_R_degree Q hQ prime
   (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
 have hQY:MvPolynomial.weightedTotalDegree yWeights Q ≤ yTotalCap:=by
   apply (weightedTotalDegree_le_iff yWeights Q yTotalCap).mpr
   intro d hd
   have hh:=(hbox hd).1
   rw [weight_fin4]
   simpa [yWeights] using (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ:MvPolynomial.weightedTotalDegree zWeights Q ≤ 0:=by
   apply (weightedTotalDegree_le_iff zWeights Q 0).mpr
   intro d hd
   have hh:=(hbox hd).2.2.1
   rw [weight_fin4]
   simpa [zWeights,hh]
 have hJYw:=singularAuxiliary_weight_le yWeights Q hQ slopeCap
   (by norm_num [slopeCap]) hcaps.2.1
 have hJZw:=singularAuxiliary_weight_le zWeights Q hQ slopeCap
   (by norm_num [slopeCap]) hcaps.2.1
 have hJY:J.degreeOf 1 ≤ singularListCap:=
   (degreeY_le_yWeight K J).trans (hJYw.trans (by
     unfold singularListCap
     exact Nat.mul_le_mul_left _ hQY))
 have hJZ:J.degreeOf 3=0:=Nat.eq_zero_of_le_zero
   ((degreeZ_le_zWeight K J).trans (hJZw.trans (by
     simpa only [Nat.mul_zero] using Nat.mul_le_mul_left (2*slopeCap-1) hQZ)))
 let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
 have hAne:A≠0:=surfaceMap_ne_zero phi (polynomialEmbedding_injective K) J hJne
 have hAR:A.degreeOf 1=0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
 have hAZ:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
 let q:Polynomial (GenericField K):=yProjection (GenericField K) A
 have hq:q≠0:=yProjection_nonzero A hAne hAR hAZ
 have hroots:∀ z∈Gamma.image phi,z∈q.roots:=by
   intro z hz
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S)=0
   have hv:seedlessPoint phi S 0=phi S:=by
     simp [seedlessPoint_value]
   change (yProjection (GenericField K) A).eval (phi S)=0
   rw [←hv,yProjection_eval A hAR hAZ (seedlessPoint phi S)]
   rw [seedlessPoint_surface_evaluation,eval_polynomialPoint_eq_specialization,
     hsolutions S hS]
   simp
 have hcard:(Gamma.image phi).card=Gamma.card:=
   Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
 rw [←hcard]
 calc
   (Gamma.image phi).card ≤ q.roots.toFinset.card:=by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _ ≤ q.roots.card:=Multiset.toFinset_card_le _
   _ ≤ q.natDegree:=Polynomial.card_roots' q
   _ ≤ A.degreeOf 0:=yProjection_natDegree_le A
   _ ≤ J.degreeOf 1:=surfaceMap_degreeOf_le phi J 0
   _ ≤ singularListCap:=hJY
def singularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)):Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => specialization K S 0 (singularAuxiliary Q)=0)
def regularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (F:↥(positiveRFactors Q)):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => RegularSolution F.1 S 0)
theorem seedless_solution_cover
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0):
   Gamma.card ≤ (singularPolynomials K Q Gamma).card+
     ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularPolynomials K Q Gamma)
 have hcover:Gamma ⊆ singularPolynomials K Q Gamma ∪ regularUnion:=by
   intro S hS
   obtain hsing | ⟨F,hF,hreg⟩:=solution_regular_or_auxiliary
     Q hQ S 0 (hsolutions S hS)
   · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hsing⟩)
   · apply Finset.mem_union_right
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hS,hreg⟩⟩
 calc
   Gamma.card ≤ (singularPolynomials K Q Gamma ∪ regularUnion).card:=
     Finset.card_le_card hcover
   _ ≤ (singularPolynomials K Q Gamma).card+regularUnion.card:=
     Finset.card_union_le _ _
   _ ≤ (singularPolynomials K Q Gamma).card+
       ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=
     Nat.add_le_add_left Finset.card_biUnion_le _
theorem seedless_list_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hlegacy:Q∈RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0)
   (hagreement:∀ S∈Gamma,agreements ≤
     (nodes.filter (fun i => S.eval (x i)=received i)).card):
   Gamma.card ≤ listBudget:=by
 classical
 have hcaps:=seedless_degree_caps K Q hbox
 have hsing:(singularPolynomials K Q Gamma).card ≤ singularListCap:=
   singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
     (fun S hS => (Finset.mem_filter.mp hS).2)
 have hreg (F:↥(positiveRFactors Q)):
     (regularPolynomials K Q Gamma F).card*gap ≤
       (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=by
   have hdata:=directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF:=(positiveRFactors_spec Q F.1 F.2).2.1
   have hFZ:F.1.degreeOf 3=0:=Nat.eq_zero_of_le_zero
     ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub:regularPolynomials K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
   exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (regularPolynomials K Q Gamma F)
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => (Finset.mem_filter.mp hS).2.1)
     (fun S hS => (Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
 have hsumY:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
 have hsumR:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
 have hsumY':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1) ≤ Q.degreeOf 1:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumY
 have hsumR':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2) ≤ Q.degreeOf 2:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumR
 have hregularScaled:
     (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap ≤
       regularListNumerator:=by
   calc
     _=∑ F:↥(positiveRFactors Q),
         (regularPolynomials K Q Gamma F).card*gap:=by rw [Finset.sum_mul]
     _ ≤ ∑ F:↥(positiveRFactors Q),
         (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=
       Finset.sum_le_sum (fun F _ => hreg F)
     _=(n-w)*(capY*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2)+
         capR*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1)):=by
       rw [←Finset.mul_sum,Finset.sum_add_distrib,
         ←Finset.mul_sum, ←Finset.mul_sum]
     _ ≤ (n-w)*(capY*slopeCap+capR*yTotalCap):=by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _=regularListNumerator:=rfl
 have hcover:=seedless_solution_cover K Q hQ Gamma hsolutions
 have hscaled:=Nat.mul_le_mul_right gap hcover
 have htotal:Gamma.card*gap ≤ listNumerator:=by
   calc
     Gamma.card*gap ≤
         ((singularPolynomials K Q Gamma).card+
           ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=
       hscaled
     _=(singularPolynomials K Q Gamma).card*gap+
         (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=by
       ring
     _ ≤ singularListCap*gap+regularListNumerator:=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _=listNumerator:=by simp only [listNumerator];ring
 by_contra hnot
 have hlarge:listBudget < Gamma.card:=Nat.lt_of_not_ge hnot
 have hgap:0 < gap:=by norm_num [gap,agreements,n,errors,w]
 have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra:listBudget*gap < listNumerator:=hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
end ProximityPrize.SubmissionLower.RCN281
end PackedLegacy_O8

/-! Packed from ProximityPrize.SubmissionLower.H7. -/
section PackedLegacy_H7
namespace ProximityPrize.SubmissionLower.RCN020
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
def ZeroCoordinateBound (C:LinearCode ι F) (w:ℕ):Prop:=
 ∀ c:ι → F,c∈C → c≠0 →
   (Finset.univ.filter (fun i => c i=0)).card ≤ w
def scalarList (C:LinearCode ι F) (u:ι → F) (e:ℕ):
   Finset (ι → F):=by
 classical
 exact Finset.univ.filter (fun c => c∈C∧
   Fintype.card ι-e ≤ (Finset.univ.filter (fun i => c i=u i)).card)
end Proofs
end ProximityPrize.SubmissionLower.RCN020
end PackedLegacy_H7

/-! Packed from ProximityPrize.SubmissionLower.H6. -/
section PackedLegacy_H6
namespace ProximityPrize.SubmissionLower.RCN019
open scoped BigOperators
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
 {r:ℕ}
def rowPolynomial (v:Fin r → F):Polynomial F:=
 ∑ j:Fin r,Polynomial.monomial j.val (v j)
theorem rowPolynomial_coeff (v:Fin r → F) (j:Fin r):
   (rowPolynomial v).coeff j.val=v j:=by
 classical
 rw [rowPolynomial,Polynomial.finsetSum_coeff]
 calc
   (∑ k:Fin r,(Polynomial.monomial k.val (v k)).coeff j.val)=
       (Polynomial.monomial j.val (v j)).coeff j.val:=by
     apply Finset.sum_eq_single j
     · intro k _ hkj
       have hval:k.val≠j.val:=fun hh => hkj (Fin.ext hh)
       simp [Polynomial.coeff_monomial,hval,Ne.symm hval]
     · intro hnot
       exact (hnot (Finset.mem_univ j)).elim
   _=v j:=by simp [Polynomial.coeff_monomial]
theorem rowPolynomial_injective:
   Function.Injective (rowPolynomial:(Fin r → F) → Polynomial F):=by
 intro v u heq
 funext j
 have hc:=congrArg (fun P:Polynomial F => P.coeff j.val) heq
 simpa only [rowPolynomial_coeff] using hc
theorem rowPolynomial_natDegree_le (v:Fin r → F):
   (rowPolynomial v).natDegree ≤ r-1:=by
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro j _
 have hterm:=Polynomial.natDegree_monomial_le (v j) (m:=j.val)
 have hj:=j.isLt
 exact hterm.trans (by omega)
def momentProjection (t:F) (v:ι → Fin r → F):ι → F:=
 fun i => (rowPolynomial (v i)).eval t
theorem momentProjection_apply (t:F) (v:ι → Fin r → F) (i:ι):
   momentProjection t v i=∑ j:Fin r,t^j.val*v i j:=by
 change (Polynomial.evalRingHom t)
     (∑ j:Fin r,Polynomial.monomial j.val (v i j))=_
 rw [map_sum]
 apply Finset.sum_congr rfl
 intro j _
 change (Polynomial.monomial j.val (v i j)).eval t=t^j.val*v i j
 rw [Polynomial.eval_monomial,mul_comm]
theorem exists_nonzero_coordinate_difference
   (v u:ι → Fin r → F) (hne:v≠u):
   ∃ P:Polynomial F,P≠0∧P.natDegree ≤ r-1∧
     ∀ t:F,momentProjection t v=momentProjection t u → P.eval t=0:=by
 classical
 obtain ⟨i,hi⟩:∃ i:ι,v i≠u i:=by
   by_contra hno
   push_neg at hno
   exact hne (funext hno)
 refine ⟨rowPolynomial (v i)-rowPolynomial (u i),?_,?_,?_⟩
 · apply sub_ne_zero.mpr
   intro hh
   exact hi (rowPolynomial_injective hh)
 · exact (Polynomial.natDegree_sub_le _ _).trans
     (max_le (rowPolynomial_natDegree_le _) (rowPolynomial_natDegree_le _))
 · intro t ht
   rw [Polynomial.eval_sub]
   exact sub_eq_zero.mpr (congrFun ht i)
def pairCollisionSeeds (pair:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact Finset.univ.filter (fun t => ∃ v∈pair,∃ u∈pair,
   v≠u∧momentProjection t v=momentProjection t u)
theorem mem_pairCollisionSeeds_iff
   (pair:Finset (ι → Fin r → F)) (t:F):
   t∈pairCollisionSeeds pair ↔ ∃ v∈pair,∃ u∈pair,
     v≠u∧momentProjection t v=momentProjection t u:=by
 classical
 simp only [pairCollisionSeeds,Finset.mem_filter,Finset.mem_univ,true_and]
theorem pairCollisionSeeds_card_le
   (pair:Finset (ι → Fin r → F)) (hpair:pair.card=2):
   (pairCollisionSeeds pair).card ≤ r-1:=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 obtain ⟨v,u,hne,rfl⟩:=Finset.card_eq_two.mp hpair
 obtain ⟨P,hP,hdegree,heval⟩:=exists_nonzero_coordinate_difference v u hne
 have hcard:(pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F))).card ≤
     P.natDegree:=by
   apply Polynomial.card_le_degree_of_subset_roots
   intro t ht
   apply (Polynomial.mem_roots hP).mpr
   apply heval t
   have ht':t∈pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F)):=ht
   obtain ⟨a,ha,b,hb,hab,habproj⟩:=
     (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mp ht'
   simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
   rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
   · exact (hab rfl).elim
   · exact habproj
   · exact habproj.symm
   · exact (hab rfl).elim
 exact hcard.trans hdegree
def allCollisionSeeds (L:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact (L.powersetCard 2).biUnion pairCollisionSeeds
theorem allCollisionSeeds_card_le (L:Finset (ι → Fin r → F)):
   (allCollisionSeeds L).card ≤ (r-1)*L.card.choose 2:=by
 classical
 calc
   (allCollisionSeeds L).card ≤
       ∑ pair∈L.powersetCard 2,(pairCollisionSeeds pair).card:=
     Finset.card_biUnion_le
   _ ≤ ∑ _pair∈L.powersetCard 2,(r-1):=by
     apply Finset.sum_le_sum
     intro pair hpair
     exact pairCollisionSeeds_card_le pair (Finset.mem_powersetCard.mp hpair).2
   _=(L.powersetCard 2).card*(r-1):=by simp
   _=(r-1)*L.card.choose 2:=by
     rw [Finset.card_powersetCard,Nat.mul_comm]
theorem exists_separating_moment_parameter
   (L:Finset (ι → Fin r → F))
   (hfield:(r-1)*L.card.choose 2 < Fintype.card F):
   ∃ t:F,Set.InjOn (momentProjection (ι:=ι) (r:=r) t)
     (L:Set (ι → Fin r → F)):=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 have hsmall:(allCollisionSeeds L).card < Fintype.card F:=
   (allCollisionSeeds_card_le L).trans_lt hfield
 obtain ⟨t,ht⟩:∃ t:F,t∉allCollisionSeeds L:=by
   by_contra hno
   have hsub:Finset.univ ⊆ allCollisionSeeds L:=by
     intro t _
     by_contra ht
     exact hno ⟨t,ht⟩
   have hc:=Finset.card_le_card hsub
   rw [Finset.card_univ] at hc
   omega
 refine ⟨t,?_⟩
 intro v hv u hu hproj
 change v∈L at hv
 change u∈L at hu
 by_contra hne
 apply ht
 apply Finset.mem_biUnion.mpr
 refine ⟨{v,u},?_,?_⟩
 · apply Finset.mem_powersetCard.mpr
   constructor
   · intro c hc
     simp only [Finset.mem_insert,Finset.mem_singleton] at hc
     rcases hc with rfl | rfl
     · exact hv
     · exact hu
   · simp [hne]
 · apply (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mpr
   exact ⟨v,by simp,u,by simp,hne,hproj⟩
theorem momentProjection_mem_code
   (C:LinearCode ι F) (t:F) (v:ι → Fin r → F)
   (hrows:∀ j:Fin r,(fun i => v i j)∈C):
   momentProjection t v∈C:=by
 classical
 have heq:momentProjection t v=
     ∑ j:Fin r,t^j.val • (fun i => v i j):=by
   funext i
   rw [momentProjection_apply]
   simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
 rw [heq]
 exact C.sum_mem (fun j _ => C.smul_mem (t^j.val) (hrows j))
theorem momentProjection_preserves_agreements
   (t:F) (v u:ι → Fin r → F):
   (Finset.univ.filter (fun i => v i=u i)) ⊆
     Finset.univ.filter (fun i => momentProjection t v i=momentProjection t u i):=by
 classical
 intro i hi
 refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
 have hv:=(Finset.mem_filter.mp hi).2
 change (rowPolynomial (v i)).eval t=(rowPolynomial (u i)).eval t
 rw [hv]
end Proofs
end ProximityPrize.SubmissionLower.RCN019
end PackedLegacy_H6

/-! Packed from ProximityPrize.SubmissionLower.H5. -/
section PackedLegacy_H5
namespace ProximityPrize.SubmissionLower.RCN018
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section DraftProofs
section RadiusCell
variable {ι A:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [DecidableEq A]
theorem agreement_card_ge_of_closeCodewordsRel
   (C:Set (ι → A)) (y c:ι → A) (δ:ℝ) (e:ℕ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ))
   (hc:c∈Code.closeCodewordsRel C y δ):
   Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => c i=y i)).card:=by
 classical
 have hball:=(Code.mem_closeCodewordsRel_iff.mp hc).2
 simp only [Code.relHammingDist_coe] at hball
 have hn:(0:ℝ) < (Fintype.card ι:ℝ):=by
   exact_mod_cast Fintype.card_pos
 have hdistR:(hammingDist y c:ℝ) < ((e+1:ℕ):ℝ):=
   ((div_le_iff₀ hn).mp hball).trans_lt hcell
 have hdist:hammingDist y c ≤ e:=by
   have hlt:hammingDist y c < e+1:=by exact_mod_cast hdistR
   omega
 have hagree:Code.agree c y+hammingDist y c=Fintype.card ι:=by
   rw [hammingDist_comm]
   exact Code.agree_add_hammingDist (u:=c) (v:=y)
 change Fintype.card ι-e ≤ Code.agree c y
 omega
end RadiusCell
section GenericCode
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
def sixteenIndexEquiv:Fin 2 × Fin 8 ≃ Fin 16:=finProdFinEquiv
def flattenSymbol (v:Fin 2 → Fin 8 → F) (j:Fin 16):F:=
 v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2
def unflattenSymbol (v:Fin 16 → F) (a:Fin 2) (b:Fin 8):F:=
 v (sixteenIndexEquiv (a,b))
theorem unflatten_flattenSymbol (v:Fin 2 → Fin 8 → F):
   unflattenSymbol (flattenSymbol v)=v:=by
 funext a b
 simp only [unflattenSymbol,flattenSymbol,Equiv.symm_apply_apply]
theorem flatten_unflattenSymbol (v:Fin 16 → F):
   flattenSymbol (unflattenSymbol v)=v:=by
 funext j
 change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j))=v j
 rw [Equiv.apply_symm_apply]
def squaredEightSymbolEquiv:(Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
 toFun:=flattenSymbol
 invFun:=unflattenSymbol
 left_inv:=unflatten_flattenSymbol
 right_inv:=flatten_unflattenSymbol
def flattenWord (v:ι → Fin 2 → Fin 8 → F):ι → Fin 16 → F:=
 fun i => squaredEightSymbolEquiv (v i)
theorem flattenWord_injective:
   Function.Injective (flattenWord:(ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F):=by
 intro v u h
 funext i
 exact squaredEightSymbolEquiv.injective (congrFun h i)
theorem flattenWord_agreement_iff
   (v u:ι → Fin 2 → Fin 8 → F) (i:ι):
   flattenWord v i=flattenWord u i ↔ v i=u i:=by
 constructor
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i) at hh
   exact (squaredEightSymbolEquiv (F:=F)).injective hh
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i)
   exact congrArg (squaredEightSymbolEquiv (F:=F)) hh
theorem flattenWord_agreement_card (v u:ι → Fin 2 → Fin 8 → F):
   (Finset.univ.filter (fun i => flattenWord v i=flattenWord u i)).card=
     (Finset.univ.filter (fun i => v i=u i)).card:=by
 classical
 congr 1
 ext i
 simp only [Finset.mem_filter,flattenWord_agreement_iff]
theorem squared_eight_rows
   (C:LinearCode ι F) (v:ι → Fin 2 → Fin 8 → F)
   (hv:v∈((C^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode ι F (Fin 2 → Fin 8 → F))):
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈C:=by
 intro a b
 have houter:=
   (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
     (C^⋈ (Fin 8)) v).mp hv a
 exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b
end GenericCode
theorem irs_code_mem_iff_rows
   (v:IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field):
   v∈IRSProfile.code ↔
     ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode:=by
 change (∀ b:Fin IRSProfile.interleaving,
   (fun i => v i b)∈ReedSolomon.code IRSProfile.domain
     (IRSProfile.totalDimension/IRSProfile.interleaving)) ↔ _
 rw [IRSProfile.totalDimension_div_interleaving]
 rfl
theorem irs_squared_carrier_eq:
   (((IRSProfile.code^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field
       (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)))=
   ((((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))):=by
 ext v
 change (∀ a:Fin 2,(fun i => v i a)∈IRSProfile.code) ↔
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈IRSProfile.baseCode
 constructor
 · intro hv a b
   exact (irs_code_mem_iff_rows _).mp (hv a) b
 · intro hv a
   exact (irs_code_mem_iff_rows _).mpr (hv a)
end DraftProofs
end ProximityPrize.SubmissionLower.RCN018
end PackedLegacy_H5

/-! Packed from ProximityPrize.SubmissionLower.F0. -/
section PackedLegacy_F0
namespace ProximityPrize.SubmissionLower.RCN280
open scoped Classical NNReal
open ProximityPrize.Benchmark RCN279 RCN281 RCN019 RCN018 RCN319
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem irs_scalar_finite_list_card_le
   (received:IRSProfile.Index → IRSProfile.Field)
   (L:Finset (IRSProfile.Index → IRSProfile.Field))
   (hcode:∀ c∈L,c∈IRSProfile.baseCode)
   (hclose:∀ c∈L,agreements ≤
     (Finset.univ.filter (fun i => c i=received i)).card):
   L.card ≤ listBudget:=by
 classical
 let D:=↥L
 let codeword:D → IRSProfile.baseCode:=fun c => ⟨c.1,hcode c.1 c.2⟩
 let selected:D → Polynomial IRSProfile.Field:=fun c => ReedSolomon.toPolynomial (codeword c)
 let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
 have hselected:Function.Injective selected:=by
   intro c d h
   apply Subtype.ext
   funext i
   have hh:=congrArg (fun P:Polynomial IRSProfile.Field =>
     P.eval (IRSProfile.domain i)) h
   simpa only [selected,ReedSolomon.toPolynomial_eval_at_domain] using hh
 have hcard:Gamma.card=L.card:=by
   rw [show Gamma=Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected,Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q,hQ,hbox,hlegacy,hvanish⟩:=
   exists_frozen_seedless_vanishing_interpolant received
 have hdegree:∀ P∈Gamma,P.natDegree ≤ w:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg:(selected c).degree < ((w+1:ℕ):WithBot ℕ):=by
     have hh:=Polynomial.mem_degreeLT.mp hp
     change (selected c).degree <
       ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
     rw [show IRSProfile.baseDimension=w+1 by
       norm_num [IRSProfile.baseDimension,w]] at hh
     exact hh
   by_cases hz:selected c=0
   · simp [hz]
   · rw [←Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution:∀ P∈Gamma,specialization IRSProfile.Field P 0 Q=0:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   let A:=Finset.univ.filter (fun i => c.1 i=received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement:∀ P∈Gamma,agreements ≤
     (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i)=received i)).card:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have heq:Finset.univ.filter
       (fun i => (selected c).eval (IRSProfile.domain i)=received i)=
       Finset.univ.filter (fun i => c.1 i=received i):=by
     apply Finset.filter_congr
     intro i hi
     rw [ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound:=seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,n]) hdegree hsolution hagreement
 rwa [hcard] at hbound
theorem sixteen_row_separation:
   15*(listBudget+1).choose 2 < Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field=(2130706433:ℕ)^6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_le_of_interleaved_list
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e B:ℕ)
   (hfinite:∀ (received:ι → Fin 16 → F)
       (L:Finset (ι → Fin 16 → F)),
     (∀ v∈L,∀ j:Fin 16,(fun i => v i j)∈C) →
     (∀ v∈L,Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => v i=received i)).card) →
     L.card ≤ B)
   (delta:ℝ)
   (hcell:delta*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) delta ≤ (B:ℕ∞):=by
 classical
 letI:DecidableEq (ι → Fin 2 → Fin 8 → F):=Classical.decEq _
 letI:DecidableEq (ι → Fin 16 → F):=Classical.decEq _
 apply Code.Lambda_le_of_forall_finset_card_le
 intro received L hL
 let projected:Finset (ι → Fin 16 → F):=L.image flattenWord
 have hinj:Set.InjOn flattenWord (L:Set (ι → Fin 2 → Fin 8 → F)):=
   fun _ _ _ _ hh => flattenWord_injective hh
 have hcard:projected.card=L.card:=Finset.card_image_of_injOn hinj
 have hrows:∀ v∈projected,∀ j:Fin 16,(fun i => v i j)∈C:=by
   intro v hv j
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hL c hc)).1
   change (fun i => c i (sixteenIndexEquiv.symm j).1
     (sixteenIndexEquiv.symm j).2)∈C
   exact squared_eight_rows C c hcode _ _
 have hclose:∀ v∈projected,Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => v i=flattenWord received i)).card:=by
   intro v hv
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   rw [flattenWord_agreement_card]
   exact agreement_card_ge_of_closeCodewordsRel _ received c delta e hcell (hL c hc)
 have hbound:=hfinite (flattenWord received) projected hrows hclose
 rwa [hcard] at hbound
theorem squared_eight_lambda_seedless
   (delta:ℝ)
   (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ) <
     ((errors+1:ℕ):ℝ)):
   Code.Lambda
     (((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin 8 → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
     delta ≤ (listBudget:ℕ∞):=by
 apply squared_eight_lambda_le_of_interleaved_list
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀ v∈L,agreements ≤
     (Finset.univ.filter (fun i => v i=received i)).card:=by
   intro v hv
   have hc : Fintype.card IRSProfile.Index = n := Fintype.card_fin _
   have he : n - errors = agreements := by decide +kernel
   have hh := hclose v hv
   rw [hc, he] at hh
   exact hh
 classical
 letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show listBudget+1 ≤ L.card by omega)
 have hsepD:15*D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact sixteen_row_separation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field):=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c∈projected,c∈IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c∈projected,agreements ≤
     (Finset.univ.filter (fun i => c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=irs_scalar_finite_list_card_le
   (momentProjection t received) projected hcode hnear
 rw [hprojcard,hDcard] at hbound
 omega
theorem irs_squared_lambda_seedless
   (delta:ℝ≥0)
   (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ) <
     ((errors+1:ℕ):ℝ)):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (delta:ℝ) ≤ (listBudget:ℕ∞):=by
 rw [irs_squared_carrier_eq]
 exact squared_eight_lambda_seedless (delta:ℝ) hcell
end
end ProximityPrize.SubmissionLower.RCN280
end PackedLegacy_F0

/-! Packed from ProximityPrize.SubmissionLower.O7. -/
section PackedLegacy_O7
namespace ProximityPrize.SubmissionLower.RCN278
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
def radius6630:ℝ≥0:=claimedRadius 319467 1048576
def errors6630:ℕ:=79866
def score6630:ℕ:=6710
theorem radius6630_floor:
   ⌊(radius6630:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=
     errors6630:=by
 norm_num [radius6630,claimedRadius,errors6630,IRSProfile.Index]
end
end ProximityPrize.SubmissionLower.RCN278
end PackedLegacy_O7

/-! Packed from ProximityPrize.SubmissionLower.P1. -/
section PackedLegacy_P1
namespace ProximityPrize.SubmissionLower.RCN284
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
def radius:ℝ≥0:=RCN278.radius6630
def errors:ℕ:=RCN278.errors6630
def mcaBudget:ℕ:=274980727511395087
theorem field_cardinality:
   Fintype.card IRSProfile.Field=(2130706433:ℕ)^6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem irs_code_eq_base_interleaved:
   IRSProfile.code=
     (IRSProfile.baseCode^⋈ (Fin IRSProfile.interleaving):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin IRSProfile.interleaving → IRSProfile.Field)):=by
 ext v
 change v∈IRSProfile.code ↔
   ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode
 exact RCN018.irs_code_mem_iff_rows v
theorem nat_div_le_inv_pow {m q t:ℕ} (hm:0 < m)
   (hq:m*2^t ≤ q):
   (m:ENNReal)/(q:ENNReal) ≤ 1/2^t:=by
 have hm0:(m:ENNReal)≠0:=by exact_mod_cast hm.ne'
 have hmtop:(m:ENNReal)≠⊤:=ENNReal.natCast_ne_top m
 have hqE:((m*2^t:ℕ):ENNReal) ≤ (q:ENNReal):=by
   exact_mod_cast hq
 have hcast:((m*2^t:ℕ):ENNReal)=(m:ENNReal)*2^t:=by
   push_cast
   ring
 calc
   (m:ENNReal)/(q:ENNReal) ≤
       (m:ENNReal)/((m*2^t:ℕ):ENNReal):=
     ENNReal.div_le_div_left hqE _
   _=(m:ENNReal)/((m:ENNReal)*2^t):=by rw [hcast]
   _=(m:ENNReal)*1/((m:ENNReal)*2^t):=by rw [mul_one]
   _=1/2^t:=ENNReal.mul_div_mul_left 1 (2^t) hm0 hmtop
theorem field_capacity_split:
   2^(128:ℕ)*
       (mcaBudget+RCN281.listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [field_cardinality]
 norm_num [mcaBudget,RCN281.listBudget]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors by
     simpa only [radius,errors] using
       RCN278.radius6630_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,RCN278.errors6630] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=
     base_mca_le_of_alignment halign
   _=(mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
         IRSProfile.Field))
     (radius:ℝ) ≤
       (RCN281.listBudget:ℕ∞):=by
 apply RCN280.irs_squared_lambda_seedless
 norm_num [radius,RCN278.radius6630,claimedRadius,
   RCN279.errors,IRSProfile.Index]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0)/2^(128:ℕ):=by
 rw [←ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code^⋈ (Fin 2):
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal)+
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
     add_le_add (mca_le_of_alignment halign) hList
   _=((mcaBudget+RCN281.listBudget:ℕ):ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [←ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal)/2^(128:ℕ):=by
     apply nat_div_le_inv_pow
     · norm_num [mcaBudget,RCN281.listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
end
end ProximityPrize.SubmissionLower.RCN284
end PackedLegacy_P1

end Compact_PackedLegacy

