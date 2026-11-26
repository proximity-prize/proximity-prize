import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdA2
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdB4
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.DdCS
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Johnson_Agreement
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_PairwiseIntersection
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Polynomial_FractionFieldResultant
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_LinearAlgebra_FiniteDimensional
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Ideal
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_BoxIntegral_UnitPartition
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Measure
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Visible
import ProximityPrize.SubmissionLower.LibraryMathlib_Combinatorics_Pigeonhole
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Finsupp_Interval
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Set_Card_Arithmetic
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Sym_NatCard
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_CosetCover
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Norm
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_TensorProduct_Free
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FunctionField
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_RatFunc_Ostrowski
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Adjoin_Polynomial_Bivariate
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_Factorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Finiteness_Descent
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_Equalizer
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_GradedAlgebra_Radical
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_IsPrincipalPowQuotient
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Localization_NormTrace
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_OrderOfVanishing_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Inertia
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Regular_Flat
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Surjective
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Unramified
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_Discrete_RankOne
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.LibraryMathlib_Topology_Algebra_MvPolynomial
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_DdB6
set_option Elab.async false




























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 12000
open _root_ renaming CharP.cast_eq_zero_iff→v9,DFunLike.congr_fun→xu,Equiv.apply_symm_apply→vk,Equiv.optionCongr→qU,Fin.last→cy,Fin.lastCases→t8,Finset.card_le_card→uJ,Finset.single_le_sum→wR,Finset.sum_add_distrib→wY,Finset.sum_le_sum→t3,Function.Injective→qJ,Irreducible→ oz,Multiset.count_le_of_le→vj,Multiset.prod_eq_zero_iff→uh,Multiset.toFinset_prod_dvd_prod→t6,MvPolynomial.X→nX,MvPolynomial.aeval→n5,MvPolynomial.aeval_eq_eval→ oy,MvPolynomial.aeval_monomialPoint→t9,MvPolynomial.affineHilbertPolynomial→pL,MvPolynomial.cappedDegreeMixedVolume→sH,MvPolynomial.degreeOf_def→u9,MvPolynomial.degreeOf_le_totalDegree→vH,MvPolynomial.degrees_map_le→xW,MvPolynomial.eval→lI,MvPolynomial.map→ oq,MvPolynomial.map_injective→vG,MvPolynomial.mem_vanishingIdeal_iff→pC,MvPolynomial.monomialLift→p9,MvPolynomial.monomialPoint→ oD,MvPolynomial.optionEquivRight→x7,MvPolynomial.ringHom_ext→wA,MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd→qm,MvPolynomial.support_map_of_injective→xI,MvPolynomial.totalDegree_monomialLift_le_one→vw,MvPolynomial.vanishingIdeal→pz,MvPolynomial.weightedTotalDegree_le_of_dvd→vl,MvPolynomial.weightedTotalDegree_piSingle→u8,MvPolynomial.weightedTotalDegree_rename_of_injective→vh,Nat.add_le_add_left→u5,Nat.mul_le_mul_left→nI,Nat.mul_le_mul_right→qM,Nat.mul_one→th,Nat.pos_of_ne_zero→pU,Nat.sub_le_sub_right→sS,Pi.single→p7,Polynomial.coeff_map→uz,Polynomial.eval₂_eq_eval_map→wB
open _root_ renaming Polynomial.hasseDeriv→pG,Polynomial.map_zero→xm,Polynomial.taylor_coeff→v8,PolynomialDifferential.DifferentialPolynomial→aU,PolynomialDifferential.JetVariable→lV,PolynomialDifferential.differentialSpecialization→lz,PolynomialDifferential.differentialSpecializationHom→p6,PolynomialDifferential.jetDegree→mD,PolynomialDifferential.jetTotalDegree→ ov,PolynomialDifferential.rationalTaylorPolynomial→sI,PolynomialDifferential.separant→nq,StrongNormalizationMonoid→t7,UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors→qz,UniqueFactorizationMonoid.normalizedFactors→qx,UniqueFactorizationMonoid.prod_normalizedFactors→p5,UniqueFactorizationMonoid.strongNormalizationMonoid→t5,aeA.view→pQ,congrArg→ oK,finSuccEquivLast→qy,i4.center→c9,i4.embed→lJ,i4.indexWeight→qG,le_max_left→vi,le_max_right→xL,le_rfl→ oY,map_dvd→ oZ,map_mul→ oj,map_multiset_prod→uW,map_zero→ ox,ne_zero_of_dvd_ne_zero→vZ,zero_dvd_iff→t4
set_option autoImplicit true
section
namespace a9N
noncomputable section
open scoped BigOperators
private theorem beA {a b c C t d:ℕ} (hc:0<c) (hC:c≤C)
  (ht:a*t≤2*b) (hd:d+a*c^2≤(2*c - 1)*b) :
  d+a*c^2+a*((C - c)*t)≤(2*C - 1)*b:= by
 have hincr :=nI (C - c) ht
 have he :2*C - 1=(2*c - 1)+2*(C - c) := by omega
 rw [he,Nat.add_mul]
 rw [show a*((C - c)*t)=(C - c)*(a*t) by ring,
  show 2*(C - c)*b=(C - c)*(2*b) by ring]
 exact Nat.add_le_add hd hincr
theorem bAW {ι:Type*} (T:Finset ι) (b c d:ι→ℕ) (B a cap:ℕ)
    (hb : ∑ i∈T,b i≤B) (hc : ∑ i∈T,c i≤ cap) (hB:a*cap≤B)
    (hbase : ∀ i∈T,a*c i≤b i)
    (hzero : ∀ i∈T,c i=0→d i≤b i)
    (hpos : ∀ i∈T,0<c i→d i+a*(c i)^2≤(2*c i - 1)*b i) :
    ∑ i∈T,d i≤ max B ((2*cap - 1)*B-a*cap^2) := by
  let C := ∑ i∈T,c i
  have hci (i:ι) (hi:i∈T) :c i≤C:=wR (fun j _=>Nat.zero_le (c j)) hi
  by_cases hC:C=0
  · have h:=(Finset.sum_le_sum fun i hi=>hzero i hi (by have :=hci i hi; omega)).trans hb
    exact h.trans (vi  _ _)
  have hCpos :=pU hC
  have hterm (i:ι) (hi:i∈T) :d i+a*(C*c i)≤(2*C - 1)*b i:= by
    by_cases hi₀:c i=0
    · rw [hi₀,Nat.mul_zero,Nat.mul_zero,Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using qM (b i) (show 1≤2*C - 1 by omega))
    · have h:=beA (pU hi₀) (hci i hi)
        ((hbase i hi).trans (by omega :b i≤2*b i)) (hpos i hi (pU hi₀))
      have he :C=c i+(C - c i) := by have :=hci i hi; omega
      have hweight:a*(C*c i)=a*(c i)^2+a*((C - c i)*c i) := by
        calc
          _=a*((c i+(C - c i))*c i) :=oK (fun n=>a*(n*c i)) he
          _ = _:= by ring
      rw [hweight,← Nat.add_assoc]
      exact h
  have hs : (∑ i∈T,(d i+a*(C*c i)))≤(2*C - 1)*B :=
    (t3 hterm).trans (by
      rw [← Finset.mul_sum]
      exact nI _ hb)
  have hjoint: (∑ i∈T,d i)+a*C ^2≤(2*C - 1)*B:= by
    simp only [wY ,← Nat.mul_assoc,← Finset.mul_sum] at hs
    change (∑ i∈T,d i)+(a*C)*C≤_ at hs
    rwa [Nat.mul_assoc,← pow_two] at hs
  have ha :a*(cap+C)≤2*B:= by
    calc
      _≤a*(cap+cap) :=nI _ (u5 hc cap)
      _=2*(a*cap) := by ring
      _≤_:=nI 2 hB
  have hfinal:=beA hCpos hc ha hjoint
  have he :cap=C+(cap - C) := by omega
  have hsq:a*C ^2+a*((cap - C)*(cap+C))=a*cap^2 := by
    calc
      _=a*C ^2+a*((cap - C)*((C+(cap - C))+C)) := by
        exact oK (fun n=>a*C ^2+a*((cap - C)*(n+C))) he
      _=a*(C+(cap - C))^2 := by ring
      _ = _:= by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc,hsq] using hfinal)).trans
    (xL  _ _)
end
end a9N
end
section
namespace byX
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open i4 Polynomial PolynomialDifferential
open scoped BigOperators
def Yb (G:aU K 1) :aU nU 1 :=
 oq lJ G
def initial :aU K 1 →+* BL 1 :=
  (n5 (R:=nU) (fun i:Option (Fin 2) =>
    i.elim (MvPolynomial.C c9) nX)).toRingHom.comp
    (oq lJ)
def sep (G:aU K 1) :BL 1 :=
 initialJetSeparant c9 (Yb G)
def denominator (G:aU K 1) :BL 1 :=
 sep G^t₁
private def RG:(Polynomial K) →+* nU :=
 (algebraMap FX nU).comp (algebraMap (Polynomial K) FX)
private theorem bch:qJ RG :=
 (algebraMap FX nU).injective.comp (IsFractionRing.injective (Polynomial K) FX)
theorem b6i:qJ initial := by
 have h:initial=(oq RG).comp
     (x7 K (Fin 2)).toRingHom:= by
   apply wA
   · intro a
     simp [initial,RG,lJ]
   · intro j
     cases j <;> simp [initial,RG,c9]
 rw [h]
 exact (vG _ bch).comp
   (x7 K (Fin 2)).injective
theorem eov (G:aU K 1) :
   (initial G).totalDegree≤ov G :=
 (totalDegree_initialJetEquation_le c9 (Yb G)).trans
   (jetTotalDegree_map_le lJ G)
theorem cVi (G:aU K 1) :
  (initial G).degreeOf (cy 1)≤ mD G (cy 1) := by
 apply (degreeOf_initialJetEquation_le c9 (Yb G)).trans
 simpa only [Yb,mD,u9] using
  vj (some (cy 1))
    (xW (p:=G) (f :=lJ))
private theorem ayP:TaylorExponentSufficient 1 k t₁ :=
 taylorExponentSufficient_firstOrder_tight N
private def cpv (z :nU) (l i:ℕ) :nU :=
 (l.choose i:nU)*z^(l-i)
private theorem cGn {m:ℕ} (z :nU) (a :Fin m→nU) (i:ℕ) :
   (taylor z (∑ l:Fin m,monomial l.val (a l))).coeff i =
     ∑ l:Fin m,cpv z l.val i*a l:= by
 rw [map_sum,Polynomial.finsetSum_coeff]
 apply Finset.sum_congr rfl
 intro l _
 rw [v8 ,Polynomial.hasseDeriv_monomial,Polynomial.eval_monomial]
 unfold cpv
 ring
private theorem fUe {P:(Polynomial nU)} (hP:P.degree<k) (i:ℕ) :
  awb (fun j=>P.coeff j.val) i=(taylor c9 P).coeff i:= by
 have hnat :P.natDegree<k := by
  by_cases hz :P=0
  · simpa only [hz,Polynomial.natDegree_zero] using (by decide :0<k)
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hP
 have hsum:P = ∑ l:Fin k,monomial l.val (P.coeff l.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun j=>monomial j (P.coeff j))]
  exact P.as_sum_range' _ hnat
 exact (cGn c9 (fun j:Fin k=>P.coeff j.val) i).symm.trans
  (oK (fun P:(Polynomial nU)=>(taylor c9 P).coeff i) hsum.symm)
private def CJ (G:aU K 1) (l:Fin k) :BL 1 :=
 commonTaylorNumerator c9 (Yb G) t₁ l.val
private def combine {m:ℕ} (P:Fin m→BL 1) (i:ℕ) :BL 1 :=
 ∑ l:Fin m,MvPolynomial.C (cpv (-center) l.val i)*P l
def bY (G:aU K 1) (g:BL 1) :Chart 1 :=
 ⟨g,denominator G,fun i=>combine (CJ G) i.val⟩
private theorem b0p (s :Source) (G:aU K 1)
  (hT:ov G≤H s) (hI:mD G (cy 1)≤I₁ s) :
  aOa s (denominator G) := by
 have ht: (sep G).totalDegree≤H s - 1 :=
  (totalDegree_initialJetSeparant_le c9 (Yb G)).trans
    (sS ((jetTotalDegree_map_le lJ G).trans hT) 1)
 have hi: (sep G).degreeOf (cy 1)≤I₁ s - 1 := by
  rw [sep,← pderiv_last_initialJetEquation]
  exact (MvPolynomial.degreeOf_pderiv_le_sub_one _ _).trans
    (sS ((cVi G).trans hI) 1)
 have hdt: (denominator G).totalDegree≤a₁ s :=
  (MvPolynomial.totalDegree_pow _ _).trans
    ((nI _ ht).trans (Nat.le_add_left _ _))
 refine ⟨hdt,le_min ((vH _ _).trans hdt) ?_⟩
 exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
  ((nI _ hi).trans (by unfold k; omega))
private theorem eJn (s :Source) (G:aU K 1)
    (hIpos :0<I₁ s) (hT:ov G≤H s)
    (hI:mD G (cy 1)≤I₁ s) (l:Fin k) :
    aOa s (CJ G l) := by
  have htd: (CJ G l).totalDegree≤a₁ s :=
    (totalDegree_commonTaylorNumerator_le c9 (Yb G) (ayP l)).trans
      (u5 (nI t₁
        (sS ((jetTotalDegree_map_le lJ G).trans hT) 1)) 1)
  refine ⟨htd,le_min ((vH _ _).trans htd) ?_⟩
  have hm: (Yb G).degreeOf (some (1 :Fin 2))≤I₁ s := by
    rw [show (1 :Fin 2)=cy 1 from rfl]
    apply le_trans _ hI
    simpa only [Yb,mD,u9] using
      (vj (some (cy 1))
        (xW (p:=G) (f :=lJ)))
  exact (degreeOf_commonTaylorNumerator_firstOrder_le c9 (Yb G)
    (I₁ s) k t₁ ayP hm l).trans (by
      have hl:=l.isLt
      omega)
private theorem dNV (s :Source) {m:ℕ} (P:Fin m→BL 1)
   (h : ∀ l,aOa s (P l)) (i:ℕ) :aOa s (combine P i) := by
 unfold aOa combine
 constructor
 · apply MvPolynomial.totalDegree_finsetSum_le
   intro l _
   exact (MvPolynomial.totalDegree_mul _ _).trans (by
     simpa only [MvPolynomial.totalDegree_C,zero_add] using (h l).1)
 · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
   apply Finset.sup_le
   intro l _
   exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
     simpa only [MvPolynomial.degreeOf_C,zero_add] using (h l).2)
theorem dIk (s :Source) (G:aU K 1)
  (hIpos :0<I₁ s) (hT:ov G≤H s)
  (hI:mD G (cy 1)≤I₁ s) (g:BL 1) :
  aOa s (bY G g).denominator ∧ ∀ i,aOa s ((bY G g).numerator i) := by
 simp only [bY]
 exact ⟨b0p s G hT hI,fun i:Fin k =>
  dNV s (m:=k) (CJ G) (eJn s G hIpos hT hI) i.val⟩
private theorem d2a {m:ℕ} (u:Fin 2→nU) (P:Fin m→BL 1)
   (d:nU) (hd:d≠0) (a :Fin m→nU) (h : ∀ l,lI u (P l)=d*a l)
   (i:ℕ) :lI u (combine P i)/d =
     (taylor (-center) (∑ l:Fin m,monomial l.val (a l))).coeff i:= by
 rw [cGn,combine,map_sum,div_eq_mul_inv,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro l _
 rw [oj,MvPolynomial.eval_C,h]
 field_simp
set_option maxRecDepth 200000 in
private theorem c2Z (G:aU K 1) (g:BL 1)
    (u:Fin 2→nU) (hu:lI u (denominator G)≠0) (i:Fin k) :
    (bY G g).output u i =
      (sI c9 (Yb G) k u).coeff i.val := by
  have hS:n5 u (sep G)≠0:= by
    intro hz
    apply hu
    change lI u (sep G^t₁)=0
    rw [map_pow,← oy ,hz,zero_pow (by decide :t₁≠0)]
  have he (l:Fin k) :lI u (CJ G l) =
      lI u (denominator G) *
        rationalTaylorCoefficient c9 (Yb G) u l.val := by
    simpa only [CJ,denominator,sep,map_pow,oy] using
      aeval_commonTaylorNumerator c9 (Yb G) u (ayP l) hS
  simp only [Chart.output,bY,sI,Polynomial.centeredCoefficientPrefix]
  exact d2a (m:=k) u (CJ G) (lI u (denominator G)) hu
    (fun l:Fin k=>rationalTaylorCoefficient c9 (Yb G) u l.val) he i.val
set_option maxRecDepth 200000 in
theorem bct (G:aU K 1) {g:BL 1}
  (hg:oz g) (hS : ¬ g∣denominator G) :aAQ (bY G g) := by
 refine ⟨hg,hS,?_⟩
 intro u hu j
 have hd:lI u (denominator G)≠0:=hu.2
 let P:=sI c9 (Yb G) k u
 have hout: (bY G g).output u=fun i=>P.coeff i.val := by
  funext i
  exact c2Z G g u hd i
 have hP:P.degree<k :=Polynomial.degree_centeredCoefficientPrefix_lt _ _ _
 rw [hout,fUe hP]
 have h:=congrFun (polynomialJet_rationalTaylorPolynomial c9 (Yb G)
  (show 1<k by decide) u) j
 change Polynomial.hasseCoeffAt c9 j.val P=u j at h
 rw [Polynomial.hasseCoeffAt_apply,← v8] at h
 exact h
def mark (f :(Polynomial K)) :Fin 2→nU :=
 polynomialJet c9 (f.map lJ)
private theorem d2z (f :(Polynomial K)) : (f.map lJ).eval c9=RG f := by
 rw [Polynomial.eval_map]
 change Polynomial.eval₂RingHom lJ c9 f=RG f
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RG,lJ]
 · simp [RG,c9]
private theorem cM6 (G:aU K 1) (f :(Polynomial K)) :
   jetEvaluation (Yb G) c9 (mark f) =
     RG (lz G f) := by
 rw [mark,← eval_differentialSpecialization,Yb,
   ← map_differentialSpecialization,d2z]
theorem eos (G:aU K 1) (f :(Polynomial K))
  (h:lz G f=0) :lI (mark f) (initial G)=0:= by
 change lI (mark f) (initialJetEquation c9 (Yb G))=0
 rw [← oy ,aeval_initialJetEquation,cM6,h,ox]
private theorem ddu (G:aU K 1) (f :(Polynomial K))
  (h:lz (nq G (cy 1)) f≠0) :
  lI (mark f) (sep G)≠0:= by
 rw [← oy ,sep,aeval_initialJetSeparant,Yb,← map_separant]
 exact fun hz=>h (bch ((cM6 _ _).symm.trans (hz.trans (ox _).symm)))
theorem b0r (G:aU K 1) (f :(Polynomial K))
  (h:lz (nq G (cy 1)) f≠0) :
  lI (mark f) (denominator G)≠0:= by
 rw [denominator,map_pow]
 exact pow_ne_zero _ (ddu G f h)
theorem dIp (G:aU K 1) (g:BL 1) (f :(Polynomial K))
  (hf :f.degree<k) (h:lz G f=0)
  (hs :lz (nq G (cy 1)) f≠0)
  (hg:lI (mark f) g=0) :Gp f∈(bY G g).aN8:= by
 let _:CharP nU p:=charP_of_injective_ringHom embed.injective p
 have hpiv : ∀ i:ℕ,1< i→i<k→(i.choose 1 :nU)≠0:= by
  intro i hlo hhi hz
  rw [Nat.choose_one_right] at hz
  have hdiv :=(v9 nU p i).mp hz
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (hhi.trans (by decide :k<p))) hdiv
 have hsol:lz (Yb G) (f.map lJ)=0:= by
  rw [Yb,← map_differentialSpecialization,h,xm]
 have hsep:jetEvaluation (nq (Yb G) (cy 1)) c9 (mark f)≠0:= by
  rw [← aeval_initialJetSeparant,oy]
  exact ddu G f hs
 have hdeg: (f.map lJ).degree<k :=Polynomial.degree_map_le.trans_lt hf
 have hr :=rationalTaylorPolynomial_polynomialJet c9 (Yb G) (f.map lJ)
  hsol hsep hdeg hpiv
 refine ⟨mark f,⟨hg,b0r G f hs⟩,?_⟩
 funext i
 rw [c2Z G g (mark f) (b0r G f hs),mark,hr,uz]
 rfl
end
end byX
end
section
namespace a9N
noncomputable section
open i4 Polynomial PolynomialDifferential MvPolynomial yP.Xf
def FT (G:aU K 2) :aU K 1 :=
 let P:=Wz 1 G
 let c:=P.natDegree
 if c=0 then P.coeff 0 else P.resultant P.derivative c (c - 1)
def aoj (a :ℕ) (w:lV 1→ℕ) (v :lV 2) :ℕ :=
 (aks 1 v).elim a w
private def ajm:K →+* (Polynomial aR.ao) :=
 Polynomial.C.comp aR.embed
private theorem bXD:qJ ajm :=
 Polynomial.C_injective.comp (RingHom.injective aR.embed)
private def azy :lV 1 ≃ Fin 3:=(finSuccEquiv 2).symm
private def a4F:lV 2 ≃ Fin 4 :=
 ((aks 1).trans (qU azy)).trans finSuccEquivLast.symm
private def aOF:aU K 1 →+* aR.af 3 :=
 (oq ajm).comp (rename (R:=K) azy).toRingHom
private theorem eyB:qJ aOF :=
 (vG ajm bXD).comp (rename_injective _ azy.injective)
private def row (G:aU K 2) :aR.af 4 :=
 oq ajm (rename a4F G)
private def rowWeight (a :ℕ) (w:lV 1→ℕ) (j:Fin 4) :ℕ :=
 (qy j).elim a (w ∘ azy.symm)
private theorem c86 (a :ℕ) (w:lV 1→ℕ) :
 rowWeight a w (cy 3)=a := by simp only [rowWeight,finSuccEquivLast_last,Option.elim_none]
private theorem bvo (a :ℕ) (w:lV 1→ℕ) (G:aU K 2) :
   (row G).weightedTotalDegree (rowWeight a w)=G.weightedTotalDegree (aoj a w) := by
 have hm: (row G).weightedTotalDegree (rowWeight a w) =
     (rename a4F G).weightedTotalDegree (rowWeight a w) := by
   rw [row]; simp only [weightedTotalDegree,xI _ bXD]
 rw [hm,vh a4F.injective]
 congr 1
 funext v
 change (qy (finSuccEquivLast.symm
   (qU azy (aks 1 v)))).elim a (w ∘ azy.symm)= _
 rw [vk]
 unfold aoj
 cases aks 1 v <;> simp
private theorem cY9 (a :ℕ) (w:lV 1→ℕ) (R:aU K 1) :
   (aOF R).weightedTotalDegree (fun j=>rowWeight a w j.castSucc)=R.weightedTotalDegree w:= by
 have hm: (aOF R).weightedTotalDegree (fun j=>rowWeight a w j.castSucc) =
     (rename azy R).weightedTotalDegree (fun j=>rowWeight a w j.castSucc) := by
   change (oq ajm (rename azy R)).weightedTotalDegree _ = _
   simp only [weightedTotalDegree,xI _ bXD]
 rw [hm,vh azy.injective]
 congr 1
 funext v
 simp [rowWeight,finSuccEquivLast_castSucc]
private theorem cvi (G:aU K 2) :
    pQ (row G)=(Wz 1 G).map aOF:= by
  have he :aeA.view.toRingHom.comp ((oq ajm).comp (rename (R:=K) a4F).toRingHom) =
      (Polynomial.mapRingHom aOF).comp (Wz 1).toRingHom:= by
    apply wA
    · intro x
      simp [pQ,Wz,HC,aOF]
    · intro v
      change pQ (row (nX v)) =
        (Wz 1 (nX v)).map aOF
      have hX:row (nX v)=nX (a4F v) := by simp [row]
      rw [hX]
      change optionEquivLeft (Polynomial aR.ao) (Fin 3)
          (rename qy (nX (a4F v))) =
        (optionEquivLeft K (lV 1) (rename (aks 1) (nX v))).map
          aOF
      simp only [rename_X]
      rw [show qy (a4F v)=qU azy
        (aks 1 v) from vk _ _]
      cases aks 1 v with
      | none=>simp
      | some j =>
        simp only [Equiv.optionCongr_apply,Option.map_some,optionEquivLeft_X_some,Polynomial.map_C]
        congr 1
        change nX (azy j)=oq ajm
          (rename azy (nX j))
        simp
  exact xu he G
private theorem a8c (G:aU K 2) :
  (pQ (row G)).natDegree=(Wz 1 G).natDegree := by
 rw [cvi,natDegree_map_eq_of_injective eyB]
private theorem c9d (G:aU K 2) :
   aeA.elimination (row G)=aOF (FT G) := by
 unfold aeA.elimination FT
 simp only [a8c]
 split_ifs
 · rw [cvi,uz]
 · rw [cvi,derivative_map,resultant_map_map]
theorem b1q (a :ℕ) (w:lV 1→ℕ) (G:aU K 2) :
   let c:=mD G (cy 2)
   a*c≤G.weightedTotalDegree (aoj a w) ∧
   (c=0→(FT G).weightedTotalDegree w≤G.weightedTotalDegree (aoj a w)) ∧
   (0<c→(FT G).weightedTotalDegree w+a*c^2 ≤
     (2*c-1)*G.weightedTotalDegree (aoj a w)) := by
 have hc:=a8c G
 rw [ctL] at hc
 have hb:=aeA.biB (rowWeight a w) (row G)
   (pQ (row G)).natDegree oY
 rw [c86,hc,bvo] at hb
 refine ⟨(Nat.le_add_left _ _).trans hb,?_,?_⟩
 · intro hz
   have h:=aeA.cLA (rowWeight a w) (row G) (hc.trans hz)
   rwa [c9d,cY9,bvo] at h
 · intro hp
   have h:=aeA.cLz (rowWeight a w) (row G) (hc.symm ▸ hp)
   dsimp only at h
   rwa [c9d,cY9,c86,hc,bvo] at h
end
end a9N
end
section
namespace a9N
noncomputable section
open i4 Polynomial PolynomialDifferential MvPolynomial yP.Xf UniqueFactorizationMonoid
open scoped BigOperators
private theorem d0W {G:aU K 2} (hG:oz G)
    (hchar :mD G (cy 2)<p) :FT G≠0:= by
  let P:=Wz 1 G
  let c:=P.natDegree
  have hi:oz P:=(MulEquiv.irreducible_iff (Wz 1).toMulEquiv).mpr hG
  change (if c=0 then P.coeff 0 else P.resultant P.derivative c (c-1))≠0
  by_cases h:c=0
  · have hn:=leadingCoeff_ne_zero.mpr hi.ne_zero
    change P.coeff c≠0 at hn
    simpa only [h,ite_true] using hn
  · have hlt:c<p:=(ctL 1 G).trans_lt hchar
    have hcast: (c:K)≠0:= by
      intro hz
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (pU h)
        ((v9 K p c).mp hz))
    have hc: (c:aU K 1)≠0:= by
      simpa only [map_natCast,ox] using (MvPolynomial.C_injective _ K).ne hcast
    have hder :P.derivative≠0:= by
      intro hz
      have hindex :c - 1+1=c:= by omega
      have hz' := oK (fun R:Polynomial (aU K 1)=>R.coeff (c-1)) hz
      rw [coeff_derivative,← Nat.cast_succ,Nat.succ_eq_add_one,hindex,coeff_zero] at hz'
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero) hc hz'
    simpa only [ite_eq_right h] using resultant_derivative_ne_zero_of_irreducible P hi hder
private theorem d0Y (G:aU K 2) (f :(Polynomial K))
   (hG:lz G f=0)
   (hsep:lz (nq G (cy 2)) f=0) :
   lz (FT G) f=0:= by
 let P:=Wz 1 G
 let ψ:=(p6 (d:=1) f).toRingHom
 have he :P.eval₂ ψ (pG 2 f)=0:=(bxT 1 G f).trans hG
 change ψ (if P.natDegree=0 then P.coeff 0 else
   P.resultant P.derivative P.natDegree (P.natDegree - 1))=0
 by_cases hc:P.natDegree=0
 · rw [ite_eq_left hc]
   have h:=oK (fun R:Polynomial (aU K 1) =>
     R.eval₂ ψ (pG 2 f)) (eq_C_of_natDegree_eq_zero hc)
   change P.eval₂ ψ (pG 2 f)= _ at h
   rw [Polynomial.eval₂_C] at h
   exact h.symm.trans he
 · rw [ite_eq_right hc]
   have hd:P.derivative.eval₂ ψ (pG 2 f)=0:= by
     change (Wz 1 G).derivative.eval₂ ψ _=0
     rw [dhw,bxT]
     exact hsep
   exact map_resultant_eq_zero_of_common_root ψ P P.derivative oY
     (natDegree_derivative_le P) (Or.inl hc) (pG 2 f)
     ((wB ψ).symm.trans he) ((wB ψ).symm.trans hd)
private theorem eoz :aoj 1 jetDegreeWeight=jetDegreeWeight:= by
 funext v
 rcases v with _ | j
 · simp [aoj]
 · induction j using t8 with
   | last=>simp only [aoj,bO5,Option.elim_none,jetDegreeWeight_some]
   | cast j=>simp [aoj]
private theorem eoy :aoj 2 qG=i4.indexWeight:= by
 funext v
 rcases v with _ | j
 · simp [aoj,qG]
 · induction j using t8 with
   | last =>
     rw [aoj,bO5]
     rfl
   | cast j=>simp [aoj,i4.indexWeight]
private theorem eIq:qG=(p7 (some (cy 1)) 1 :lV 1→ℕ) := by
  funext v
  rcases v with _ | j
  · simp [qG]
  · induction j using t8 with
    | last =>
      change 1=(p7 (some (cy 1)) 1 :lV 1→ℕ) (some (cy 1))
      simp only [Pi.single_eq_same]
    | cast j =>
      have hne :some j.castSucc≠some (cy 1) :=
        (Option.some_injective _).ne (Fin.castSucc_ne_last j)
      rw [Pi.single_eq_of_ne hne]
      change j.val=0
      omega
theorem proof :i4.c5:= by
  classical
  intro s hs Q hQ
  obtain ⟨hq,hb,hj,hc⟩:=hQ
  let _:t7 (aU K 2) :=
    t5
  let A:=qx Q
  let T:=A.toFinset
  let c (G:aU K 2) :=mD G (cy 2)
  let Q₁:aU K 1 := ∏ G∈T,FT G
  have hmem (G) (hG:G∈T) :G∈A:=Multiset.mem_toFinset.mp hG
  have hirr (G) (hG:G∈T) :oz G :=
    irreducible_of_normalized_factor G (hmem G hG)
  have hdvd: (∏ G∈T,G)∣Q :=
    (t6 A).trans (p5 hq).dvd
  have hcSum : ∑ G∈T,c G≤ s.C:= by
    let w:lV 2→ℕ:=p7 (some (cy 2)) 1
    have hh:=qm w T id hq hdvd
    exact (by simpa only [w,id_eq,weightedTotalDegree_piSingle,jetDegree,c] using hh :
      (∑ G∈T,c G)≤jetDegree Q (Fin.last 2)).trans hc
  have h2 :2≤ s.B:= by have :=hs.top_pos; have :=hs.index_top; have :=hs.aQV; omega
  have hC:s.C<p:= calc
    s.C≤ s.B:= by have :=hs.index_top; have :=hs.aQV; omega
    _=s.B*1 :=(th _).symm
    _≤ s.B*(s.B - 1) :=nI _ (by omega)
    _≤ max N (s.B*(s.B-1)) :=xL _ _
    _<p:=hs.characteristic
  have he (G) (hG:G∈T) :FT G≠0 :=
    d0W (hirr G hG)
      (((wR (fun i _=>Nat.zero_le (c i)) hG).trans hcSum).trans_lt hC)
  have hweight (a B:ℕ) (w:lV 1→ℕ)
      (hB:a*s.C≤B) (hQw:Q.weightedTotalDegree (aoj a w)≤B) :
      Q₁.weightedTotalDegree w≤ max B ((2*s.C-1)*B-a*s.C^2) := by
    rw [show Q₁ = ∏ G∈T,FT G from rfl,weightedTotalDegree_prod w T _ he]
    apply bAW T (fun G=>G.weightedTotalDegree (aoj a w)) c
      (fun G=>(FT G).weightedTotalDegree w) B a s.C
      ((qm _ T id hq hdvd).trans hQw) hcSum hB
    · exact fun G _=>(b1q a w G).1
    · exact fun G _=>(b1q a w G).2.1
    · exact fun G _=>(b1q a w G).2.2
  refine ⟨Q₁,⟨Finset.prod_ne_zero_iff.mpr he,?_,?_⟩,?_⟩
  · simpa only [ov,H,one_mul] using
      hweight 1 s.B jetDegreeWeight (by have :=hs.index_top; have :=hs.aQV; omega)
        (by simpa only [eoz,ov ] using hb)
  · have hh:=hweight 2 s.J i4.indexWeight hs.index_top (by rwa [eoy])
    simpa only [eIq,u8 ,mD ,I₁] using hh
  · intro f _ hf hsing
    let ψ:=(p6 (d:=2) f).toRingHom
    change ψ Q=0 at hf
    have hz :=oZ ψ (p5 hq).symm.dvd
    change ψ Q∣ψ A.prod at hz
    rw [hf,t4 ,uW,uh,Multiset.mem_map] at hz
    obtain ⟨G,hG,hg⟩:=hz
    have hgT:G∈T:=Multiset.mem_toFinset.mpr hG
    have hsep:lz (nq G (cy 2)) f=0:= by
      by_contra hne
      exact hsing ⟨G,hirr G hgT,qz hG,hg,hne⟩
    have hroot :=d0Y G f hg hsep
    change (p6 (d:=1) f).toRingHom (∏ G∈T,FT G)=0
    rw [map_prod]
    exact Finset.prod_eq_zero hgT hroot
end
end a9N
end
section
namespace byX
noncomputable section
open i4 Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance :t7 (aU K 1) :=
 t5
local instance :t7 (BL 1) :=
 t5
private theorem cfE {G G' : aU K 1} {f :(Polynomial K)}
   (ha :Associated G G') (hG:lz G f=0)
   (hS:lz (nq G (cy 1)) f≠0) :
   lz G' f=0 ∧
     lz (nq G' (cy 1)) f≠0:= by
 obtain ⟨u,rfl⟩:=ha
 let ev :=p6 f (d:=1)
 have hu:ev (u:aU K 1)≠0 :=
   (u.isUnit.map ev).ne_zero
 change ev G=0 at hG
 change ev (nq G (cy 1))≠0 at hS
 change ev (G*u)=0∧ev (nq (G*u) (cy 1))≠0
 refine ⟨by rw [oj,hG,zero_mul],?_⟩
 rw [nq,MvPolynomial.pderiv_mul,map_add,oj,oj,hG,zero_mul,add_zero]
 exact mul_ne_zero hS hu
private theorem cfC {P:BL 1} (hP:P≠0) (u:Fin 2→nU)
  (h:lI u P=0) :
  ∃ g∈qx P,lI u g=0:= by
 have hd:=oZ (lI u) (p5 hP).symm.dvd
 rw [h,t4 ,uW,uh,Multiset.mem_map] at hd
 exact hd
private theorem eNe {g:BL 1} (hg:oz g) :
  1≤g.totalDegree := by
 by_contra! h
 have hc:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.lt_one_iff.mp h)
 have hcoef :g.coeff 0≠0:= fun hz=>hg.ne_zero (by rw [hc,hz,ox])
 exact hg.not_isUnit (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
  ⟨g.coeff 0,isUnit_iff_ne_zero.mpr hcoef,hc⟩)
theorem proof :i4.c6:= by
  classical
  intro s hs Q hQ
  have hIpos :0<I₁ s := by
    have hC:=hs.top_pos
    have hJ:=hs.index_top
    exact (show 0<s.J by omega).trans_le (vi _ _)
  let A:=(qx Q).toFinset
  let B (G:aU K 1) :=
    (qx (initial G)).toFinset.filter fun g => ¬ g∣denominator G
  let T:=A.sigma B
  let n:=T.card
  let e :Fin n ≃ ↥T:=(Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let entry (i:Fin n) :=(e i).val
  let F:Family 1 :=⟨n,fun i=>bY (entry i).1 (entry i).2⟩
  have hmember (i:Fin n) : (entry i).1∈A∧(entry i).2∈B (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hG (i:Fin n) : (entry i).1∣Q :=
    qz (Multiset.mem_toFinset.mp (hmember i).1)
  have hg (i:Fin n) :oz (entry i).2 ∧ ¬ (entry i).2∣denominator (entry i).1 := by
    obtain ⟨hm,hd⟩:=Finset.mem_filter.mp (hmember i).2
    exact ⟨irreducible_of_normalized_factor _ (Multiset.mem_toFinset.mp hm),hd⟩
  have hQ' : initial Q≠0 :=
    fun hz=>hQ.1 (b6i (hz.trans (ox initial).symm))
  have hd: (∏ a∈T,a.2)∣initial Q:= by
    have hA: (∏ G∈A,G)∣Q :=
      (t6 _).trans (p5 hQ.1).dvd
    have hm:=oZ initial hA
    rw [map_prod] at hm
    change (∏ a∈A.sigma B,a.2)∣initial Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hGA => ?_)).trans hm
    have hne :initial G≠0:=vZ hQ'
      (oZ initial (qz (Multiset.mem_toFinset.mp hGA)))
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((t6 _).trans (p5 hne).dvd)
  have heq (d:BL 1→ℕ) :
      (∑ i:Fin n,d (entry i).2) = ∑ a∈T,d a.2 := by
    calc
      _ = ∑ a : ↥T,d a.val.2 :=e.sum_comp (fun a : ↥T=>d a.val.2)
      _ = _:=Finset.sum_coe_sort T (fun a=>d a.2)
  have ht: (∑ i:Fin n,(entry i).2.totalDegree)≤H s := by
    rw [heq]
    have h:=qm
      (1 :Fin 2→ℕ) T (fun a=>a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_one] at h
    exact h.trans ((eov Q).trans hQ.2.1)
  have hi: (∑ i:Fin n,(entry i).2.degreeOf (cy 1))≤I₁ s := by
    rw [heq]
    have h:=qm
      (p7 (cy 1) 1) T (fun a=>a.2) hQ' hd
    simp only [u8] at h
    exact h.trans ((cVi Q).trans hQ.2.2)
  have hn:n≤H s := by
    calc
      n = ∑ _:Fin n,1 := by simp
      _ ≤ ∑ i:Fin n,(entry i).2.totalDegree :=
        t3 fun i _=>eNe (hg i).1
      _≤H s :=ht
  refine ⟨F,⟨hn,fun i=>bct _ (hg i).1 (hg i).2,ht,hi,?_⟩,?_⟩
  · intro i
    have hT:ov (entry i).1≤H s :=
      (vl jetDegreeWeight (hG i) hQ.1).trans hQ.2.1
    have hI:mD (entry i).1 (cy 1)≤I₁ s := by
      have hb:=vl
        (p7 (some (cy 1)) 1) (hG i) hQ.1
      simp only [u8] at hb
      exact hb.trans hQ.2.2
    exact dIk s _ hIpos hT hI _
  · intro f hf hreg
    obtain ⟨G,hGir,hGdvd,hGroot,hGsep⟩:=hreg
    obtain ⟨G',hGA,hGassoc⟩:=exists_mem_normalizedFactors_of_dvd hQ.1 hGir hGdvd
    obtain ⟨hroot,hsep⟩:=cfE hGassoc hGroot hGsep
    have hne :initial G' ≠ 0:=vZ hQ'
      (oZ initial (qz hGA))
    obtain ⟨g,hgM,hgroot⟩:=cfC hne (mark f) (eos G' f hroot)
    have hgden : ¬ g∣denominator G' := by
      intro hdvd
      have hm:=oZ (lI (mark f)) hdvd
      rw [hgroot,t4] at hm
      exact b0r G' f hsep hm
    have ht: (⟨G',g⟩:Sigma fun _:aU K 1=>BL 1)∈T :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGA,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgM,hgden⟩⟩
    let a : ↥T:=⟨⟨G',g⟩,ht⟩
    refine ⟨e.symm a,?_⟩
    change Gp f∈(bY (e (e.symm a)).val.1 (e (e.symm a)).val.2).aN8
    rw [e.apply_symm_apply]
    exact dIp G' g f hf hroot hsep hgroot
end
end byX
end
section
namespace cxf
open Polynomial PolynomialDifferential MvPolynomial
open i4 yP.Xf
private theorem fVx (Q:aU K 1) (f :(Polynomial K)) :
    lz Q f=0 →
    lz (nq Q (cy 1)) f≠0 →
    ae8 Q f := by
  let φ:=p6 (d:=1) f
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro _ hsep
    change φ (pderiv (some (cy 1)) 0)≠0 at hsep
    exact (hsep (by simp only [ox])).elim
  | unit u hu =>
    intro hroot _
    change φ u=0 at hroot
    exact ((hu.map φ.toRingHom).ne_zero hroot).elim
  | mul a i _ hi ih =>
    intro hroot hsep
    change φ (i*a)=0 at hroot
    change φ (pderiv (some (cy 1)) (i*a))≠0 at hsep
    rw [oj,mul_eq_zero] at hroot
    rw [pderiv_mul,map_add,oj,oj] at hsep
    rcases hroot with h_i | h_a
    · have hiSep:φ (pderiv (some (cy 1)) i)≠0:= by
        intro hz
        exact hsep (by rw [hz,h_i,zero_mul,zero_mul,add_zero])
      exact ⟨i,hi,dvd_mul_right i a,h_i,hiSep⟩
    · have haSep:φ (pderiv (some (cy 1)) a)≠0:= by
        intro hz
        exact hsep (by rw [hz,h_a,mul_zero,mul_zero,add_zero])
      obtain ⟨g,hg,hdvd,hzero,hnonzero⟩:=ih h_a haSep
      exact ⟨g,hg,hdvd.trans (dvd_mul_left a i),hzero,hnonzero⟩
private theorem emz {s :Source} (hs :Rz s) :
  2≤H s∧H s<p:= by
 have hB:2≤ s.B:= by
  have :=hs.top_pos
  have :=hs.index_top
  have :=hs.aQV
  omega
 have hC:2*s.C - 1≤ s.B - 1 := by
  have :=hs.index_top
  have :=hs.aQV
  omega
 have hBprod:s.B≤ s.B*(s.B - 1) := by
  calc
    s.B=s.B*1 :=(th _).symm
    _≤ s.B*(s.B - 1) :=nI _ (by omega)
 have hc:=(xL N (s.B*(s.B - 1))).trans_lt hs.characteristic
 have hmax :H s≤ s.B*(s.B - 1) := by
  unfold H
  apply max_le hBprod
  exact (Nat.sub_le _ _).trans
    ((qM s.B hC).trans_eq (Nat.mul_comm _ _))
 exact ⟨hB.trans (vi _ _),hmax.trans_lt hc⟩
theorem proof :i4.c8:= by
  classical
  intro s hs Q hQ
  obtain ⟨hQ,hweight,_⟩:=hQ
  obtain ⟨hH,hHp⟩:=emz hs
  suffices ∃ R:aU K 0,R≠0∧ov R≤H s*(H s - 1) ∧
      ∀ f :(Polynomial K),lz Q f=0 → ¬ae8 Q f →
        lz R f=0 by
    obtain ⟨R,hR,hRdeg,hRroot⟩:=this
    refine ⟨orderZeroAsPolynomial R,?_,?_,?_⟩
    · intro hz
      apply hR
      apply c2A
      simpa only [orderZeroAsPolynomial,ox ,xm] using hz
    · exact (eHs R).trans_le hRdeg
    · intro f _ hroot hnreg
      exact (orderZeroAsPolynomial_eval R f).trans (hRroot f hroot hnreg)
  by_cases hb:mD (Pe 0 Q) (cy 1)=0
  · have hGone :=fVD 0 Q hb
    have hsplit :=(dfk 0 Q).trans hweight
    have hlow:ov (avu 0 Q)≤H s := by omega
    have hbudget:H s≤H s*(H s - 1) :=
      (th _).symm.le.trans (nI _ (by omega))
    refine ⟨avu 0 Q,cY6 0 Q,hlow.trans hbudget,?_⟩
    intro f hroot _
    rcases c8V 0 Q hQ f hroot with hc | hr
    · exact hc
    · rw [hGone] at hr
      exact (one_ne_zero (by simpa only [lz ,map_one] using hr)).elim
  · have hbpos :0< mD (Pe 0 Q) (cy 1) :=pU hb
    have hchar :ringChar K=0∨mD Q (cy 1)< ringChar K:= by
      right
      rw [ringChar.eq K p]
      exact (jetDegree_le_total Q (cy 1)).trans_lt (hweight.trans_lt hHp)
    refine ⟨a3N 0 Q,d3N 0 Q hchar,
      d3P 0 Q (H s) hweight
        (hbpos.trans_le (jetDegree_le_total (Pe 0 Q) (cy 1))),?_⟩
    intro f hroot hnreg
    rcases fX4 0 Q hQ f hroot hbpos with hreg | hex
    · have hdvd:Pe 0 Q∣Q:= by
        obtain ⟨R,hR⟩:=radicalPrimPart_dvd_self none (HC 0 Q)
        refine ⟨(HC 0).symm R,?_⟩
        simpa [Pe] using oK (HC 0).symm hR
      obtain ⟨g,hg,hgdvd,hzero,hsep⟩ :=
        fVx (Pe 0 Q) f hreg.1 hreg.2
      exact (hnreg ⟨g,hg,hgdvd.trans hdvd,hzero,hsep⟩).elim
    · exact hex
end cxf
end
section
namespace cxe
noncomputable section
open i4 MvPolynomial
open scoped BigOperators
open yz (bK6)
open MN (aM6)
def DX {r :ℕ} (T:Chart r) :Ideal (BL r) :=
 Ideal.span {T.equation}
theorem bFh {r :ℕ} {T:Chart r} (hT:aAQ T) :
   (DX T).IsPrime :=
 (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
private theorem cZ9 {r :ℕ} (T:Chart r) (u:Fin (r+1)→nU) :
  u∈T.aa0↔u∈zeroLocus nU (DX T)∧n5 u T.denominator≠0:= by
 rw [DX,zeroLocus_span]
 simp only [Chart.aa0,Set.mem_ofPred_eq,Set.mem_singleton_iff,forall_eq,oy]
theorem cYM {r :ℕ} {T:Chart r} (hT:aAQ T) :
   pz nU T.aa0=DX T:= by
 have hp:=bFh hT
 ext g
 rw [pC]
 constructor
 · intro hg
   have hmul :T.denominator*g∈pz nU (zeroLocus nU (DX T)) := by
     apply mem_vanishingIdeal_iff.mpr
     intro u hu
     rw [oj]
     by_cases hd:n5 u T.denominator=0
     · rw [hd,zero_mul]
     · rw [hg u ((cZ9 T u).2 ⟨hu,hd⟩),mul_zero]
   rw [vanishingIdeal_zeroLocus_eq_radical,hp.isRadical.radical] at hmul
   exact (hp.mem_or_mem hmul).resolve_left
     (fun hd=>hT.nonvanishing (Ideal.mem_span_singleton.mp hd))
 · intro hg u hu
   exact ((cZ9 T u).1 hu).1 g hg
private def KT {r :ℕ} (j:Fin (r+1)) :jo :=
 ∑ i:Fin i4.k,C ((i.val.choose j.val :nU)*c9^(i.val-j.val))*nX i
private def JH (r :ℕ) :BL r →ₐ[nU] jo :=
 n5 KT
private theorem cAS {r :ℕ} (y :Fin i4.k→nU) (g:BL r) :
  n5 y (JH r g)=n5 (fun j=>awb y j.val) g:= by
 have h: (n5 y).comp (JH r)=n5 (fun j=>awb y j.val) := by
  apply algHom_ext
  intro j
  simp only [AlgHom.comp_apply,JH,aeval_X,KT,map_sum,oj,aeval_C,
   Algebra.algebraMap_self,RingHom.id_apply,awb]
 exact xu h g
theorem enI {r :ℕ} {T:Chart r} (hT:aAQ T) :
    r≤(pL T.ideal).natDegree := by
  have heq :T.ideal.comap (JH r)=DX T:= by
    rw [← cYM hT]
    ext g
    change JH r g∈pz nU T.aN8↔g∈pz nU T.aa0
    simp only [pC]
    constructor
    · intro h u hu
      have hjet: (fun j:Fin (r+1)=>awb (T.output u) j.val)=u :=
        funext (hT.recover u hu)
      simpa only [cAS,hjet] using h (T.output u) ⟨u,hu,rfl⟩
    · rintro h _ ⟨u,hu,rfl⟩
      rw [cAS,funext (hT.recover u hu)]
      exact h u hu
  have hdim:=natDegree_affineHilbertPolynomial_span_singleton_add_one
    hT.irreducible.ne_zero (bFh hT).ne_top
  rw [Nat.card_fin] at hdim
  have h:=natDegree_affineHilbertPolynomial_le_of_injective
    (Ideal.quotientMapₐ T.ideal (JH r) oY) Ideal.quotientMap_injective
  rw [heq] at h
  change (pL (DX T)).natDegree+1=r+1 at hdim
  omega
private theorem dR1 {T:Chart 1} (hT:aAQ T) {a d:ℕ}
    (ha :0<a) (hd:0<d)
    (hD:T.denominator∈restrictCappedDegree (Fin 2) nU 1 a d)
    (hN : ∀ j,T.numerator j∈restrictCappedDegree (Fin 2) nU 1 a d) :
    T.ideal.IsPrime∧(pL T.ideal).natDegree=1 ∧
      affineDegree T.ideal≤(sH T.equation.totalDegree
        (T.equation.degreeOf (cy 1)) a d:ℕ) := by
  let E :=cappedDegreeExponents (Fin 2) 1 a d
  let φ:=monomialMap nU E
  let P:=(DX T).comap φ
  let A:=oD E '' T.aa0
  have hA:P=pz nU A:= by
    ext g
    change φ g∈DX T↔g∈pz nU A
    rw [← cYM hT,pC,pC]
    constructor
    · rintro h _ ⟨u,hu,rfl⟩
      rw [t9]
      exact h u hu
    · intro h u hu
      simpa only [t9] using h (oD E u) ⟨u,hu,rfl⟩
  have hp:P.IsPrime :=(bFh hT).comap φ.toRingHom
  have hdim: (pL P).natDegree=1 := by
    have h:=natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ (monomialMap_cappedDegreeExponents_surjective ha hd) hT.irreducible.ne_zero
      (bFh hT).ne_top
    rw [Nat.card_fin] at h
    change (pL P).natDegree+1=2 at h
    omega
  obtain ⟨δ,hδ,hdeg⟩:=aM6 P hp hdim
  have hone :1≤affineDegree P:= by
    rw [hdeg]
    exact_mod_cast hδ
  let D:=p9 T.denominator hD
  let N (j:Fin i4.k) :=p9 (T.numerator j) (hN j)
  have eval_lift (u:Fin 2→nU) (g:BL 1) (hg:g∈restrictSupport nU E) :
      eval (oD E u) (p9 g hg)=eval u g:= by
    simpa only [oy ,monomialMap_monomialLift] using
      t9 u (p9 g hg)
  have eval_D (u:Fin 2→nU) :
      eval (oD E u) D =eval u T.denominator :=
    eval_lift u T.denominator hD
  have eval_N (u:Fin 2→nU) (j:Fin i4.k) :
      eval (oD E u) (N j)=eval u (T.numerator j) :=
    eval_lift u (T.numerator j) (hN j)
  have hden (z) (hz :z∈A) :eval z D ≠0:= by
    obtain ⟨u,hu,rfl⟩:=hz
    rw [eval_D]
    exact hu.2
  obtain ⟨Q,hQ,hdQ,hbQ,hcover⟩ :=
    bK6 A P hA hp hdim hone D N
      (vw _ _) (fun j=>vw _ _) hden
  have hle :Q≤T.ideal:= by
    intro g hg
    rw [Chart.ideal,pC]
    rintro _ ⟨u,hu,rfl⟩
    have hz :=hcover (oD E u) ⟨u,hu,rfl⟩ g hg
    change n5 (fun i=>eval u (T.numerator i)/eval u T.denominator) g=0
    simpa only [eval_D,eval_N] using hz
  have hlower :=enI hT
  have heq :Q=T.ideal:= by
    refine le_antisymm hle fun g hg => ?_
    by_contra hn
    have hdrop:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hQ hn oY).1
    have hsub:Q ⊔ Ideal.span {g} ≤ T.ideal :=
      sup_le hle ((Ideal.span_singleton_le_iff_mem T.ideal).mpr hg)
    have h:=natDegree_affineHilbertPolynomial_le_of_le hsub
    omega
  subst Q
  refine ⟨hQ,le_antisymm hdQ hlower,hbQ.trans ?_⟩
  exact affineDegree_comap_cappedDegree_span_singleton_le ha hd hT.irreducible.ne_zero
    (ana.aVQ T.equation oY oY)
private theorem dIm (s :Source) :
  0<a₁ s∧0<d₁ s∧d₁ s≤a₁ s := by
 have ha :0<a₁ s := by unfold a₁; omega
 have hk :1< i4.k := by decide
 have h:0<t₁*(I₁ s - 1)+i4.k - 1 := by omega
 exact ⟨ha,by rw [d₁]; exact lt_min ha h,min_le_left _ _⟩
theorem proof :i4.c7:= by
 intro s _ F hF
 obtain ⟨ha,hd,hda⟩:=dIm s
 have hlocal (i:Fin F.count) :=dR1 (hF.bct i) ha hd
   (ana.aVQ _ (hF.bands i).1.1 (hF.bands i).1.2)
   (fun j=>ana.aVQ _ ((hF.bands i).2 j).1 ((hF.bands i).2 j).2)
 refine ⟨fun i=>(hlocal i).1,fun i=>(hlocal i).2.1,?_⟩
 let cap (i:Fin F.count) :=sH (F.bY i).equation.totalDegree
   ((F.bY i).equation.degreeOf (cy 1)) (a₁ s) (d₁ s)
 have hsum : ∑ i,cap i≤R₁ s := by
   simp only [cap,sH,wY ,← Finset.sum_mul]
   rw [R₁,Nat.add_sub_assoc (nI _ hda),← Nat.mul_sub_left_distrib]
   exact Nat.add_le_add (qM _ hF.total) (qM _ hF.index)
 calc
   (∑ i,affineDegree (F.bY i).ideal) ≤ ∑ i,(cap i:ℚ) :=
     t3 fun i _=>(hlocal i).2.2
   _=((∑ i,cap i:ℕ) :ℚ) := by rw [Nat.cast_sum]
   _≤(R₁ s :ℚ) :=Nat.cast_le.mpr hsum
end
end cxe
end
section
namespace DdP1
noncomputable section
open Finset

open scoped BigOperators
end
end DdP1
end
section
set_option backward.isDefEq.respectTransparency false
namespace DdP1
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
end
end DdP1
end

end Merged6967_DdB6

section Merged6967_DdZZ0RELd
set_option Elab.async false


set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit true
namespace P5_8
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open scoped BigOperators
abbrev A:=P5.dw
abbrev Equation :=apQ.Equation
def small:Source :=
  ⟨61,83,25,11,(aH1 83 25 11).filter
    (fun j=>j.b+j.c≤25-(j.q - 76)/2)⟩
def bo8:Source :=⟨4600,6251,1959,979,aH1 6251 1959 979⟩
def Moments (s :Source) (T S V:ℕ) :Prop :=
 s.E.card=T∧(∑ j∈s.E,j.q)=S∧(∑ j∈s.E,j.v)=V
structure Jn where
 B:ℕ
 J:ℕ
 C:ℕ
def caps (Q:Equation) :Jn :=
 ⟨jetTotalDegree Q,Q.weightedTotalDegree indexWeight,jetDegree Q (Fin.last 2)⟩
def Jn.repair (s :Jn) :Jn :=
 let c:=min s.C (min s.B (s.J/2))
 ⟨s.B,min s.J (s.B+c),c⟩
def Jn.wD (s a :Jn) :Jn :=
 ⟨s.B-a.B,s.J-a.J,s.C-a.C⟩
def tetra (n:ℕ) :ℕ:=n*(n - 1)*(n - 2)/6
def aMt (s :Jn) :ℕ :=
  let z :=min s.B (min (s.J/2) s.C)
  let d:=min (z+1) (s.J+1 - s.B)
  tetra (s.B+3) - tetra (s.B+3 - d) +
    (z+1 - d)*(s.J+1 - d - z)*(2*s.B+2 - s.J)/2
def donorCaps :Jn:=⟨6251,1959,979⟩
def smallCaps :Jn:=⟨83,25,11⟩
def chartCaps :Jn:=⟨a₀ small,D small,e small⟩
def Gq (a :Jn) :ℕ :=
  ∑ i∈Finset.range (donorCaps.B/a.B),
    let l:=i+1
    if l*a.J≤donorCaps.J∧l*a.C≤donorCaps.C then
      aMt (donorCaps.wD ⟨l*a.B,l*a.J,l*a.C⟩)
    else 0
def ke (L R:BL 2) :Ideal (BL 2) :=Ideal.span {L,R}
def chartOpen (P:Ideal (BL 2)) (T:Chart 2) :Set (Fin 3→nU) :=
 {x | x∈zeroLocus nU P∧MvPolynomial.eval x T.denominator≠0}
structure ProperCharts (L R:BL 2) where
 count:ℕ
 component:Fin count→ Ideal (BL 2)
 distinct :Function.Injective component
 minimal : ∀ i,component i∈(ke L R).minimalPrimes
 bY:Fin count→Chart 2
 den_reg : ∀ i,(bY i).denominator∉component i
 bands : ∀ i,bHP small (bY i).denominator ∧
   ∀ j,bHP small ((bY i).numerator j)
 recover : ∀ i x,x∈chartOpen (component i) (bY i) →
   ∀ j:Fin 3,awb ((bY i).output x) j.val=x j
def ProperCharts.image {L R:BL 2} (F:ProperCharts L R) (i:Fin F.count) :=
 (F.bY i).output '' chartOpen (F.component i) (F.bY i)
def ProperCharts.ideal {L R:BL 2} (F:ProperCharts L R) (i:Fin F.count) :
    Ideal jo:=vanishingIdeal nU (F.image i)
def mixedTerm (x y z :Jn) :ℕ:=x.C*(y.J - y.C)*(2*z.B - z.J)
def tW (a b u:Jn) :ℕ :=
  (mixedTerm a b u+mixedTerm a u b+mixedTerm b a u +
    mixedTerm b u a+mixedTerm u a b+mixedTerm u b a)/2
def properDegree (a :Jn) :ℕ :=
 tW (smallCaps.wD a).repair (donorCaps.wD a).repair chartCaps
def componentCap (a :Jn) :ℕ:=(83-a.B)*(6251-a.B)
def tariffShape (a :Jn) :Source :=
 ⟨1,max 2 (max a.B a.J),max 2 a.J,max 1 a.C,∅⟩
end
end P5_8

end Merged6967_DdZZ0RELd

section Merged6967_Fast053
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace K1_14_3_7
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped Polynomial
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
private abbrev toSeed : Seeds →+* SeedField := algebraMap _ _
private abbrev toClosure : SeedField →+* SeedClosure := algebraMap _ _
private theorem toSeed_injective : Function.Injective toSeed :=
  IsFractionRing.injective Seeds SeedField
private theorem seedGeneric_injective : Function.Injective seedGeneric :=
  toClosure.injective.comp toSeed_injective
private theorem pair_pow_le {S : Type*} [CommRing S] (I J : Ideal S) (n j : ℕ) :
    (I ⊔ J) ^ (n+j) ≤ I ^ n ⊔ J ^ (j+1) := by
  rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans
      (Ideal.mul_le_left.trans ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans
      (Ideal.mul_le_right.trans ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega
private theorem leading_dvd_of_contact {S : Type*} [CommRing S]
    (a b : S) (G : Polynomial S) (k : ℕ)
    (h : G ∈ (Ideal.span ({C a, Polynomial.X - C b} : Set (Polynomial S))) ^ k) :
    a ^ (k - G.natDegree) ∣ G.leadingCoeff := by
  let j := G.natDegree
  change a ^ (k-j) ∣ G.coeff j
  by_cases hj : k ≤ j
  · simp [Nat.sub_eq_zero_of_le hj]
  let B : (Polynomial S) := Polynomial.X - C b
  have hpair : Ideal.span ({C a, B} : Set (Polynomial S)) =
      Ideal.span {C a} ⊔ Ideal.span {B} := by
    rw [← Ideal.span_union, Set.singleton_union]
  change G ∈ Ideal.span ({C a, B} : Set (Polynomial S)) ^ k at h
  rw [hpair] at h
  have hle := pair_pow_le (Ideal.span ({C a} : Set (Polynomial S))) (Ideal.span {B}) (k-j) j
  rw [Nat.sub_add_cancel (by omega : j ≤ k)] at hle
  have hsum : G ∈ Ideal.span ({C (a ^ (k-j))} : Set (Polynomial S)) ⊔
      Ideal.span {B ^ (j+1)} := by
    simpa only [Ideal.span_singleton_pow, ← C_pow] using hle h
  obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.mp hsum
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hr
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hs
  let I : Ideal S := Ideal.span {a ^ (k-j)}
  let π := Ideal.Quotient.mk I
  let φ := Polynomial.mapRingHom π
  have hπ : π (a ^ (k-j)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let B' : (Polynomial (S ⧸ I)) := Polynomial.X - C (π b)
  have hφC : φ (C (a ^ (k-j))) = 0 := by
    change (C (a ^ (k-j))).map π = 0
    rw [Polynomial.map_C, hπ, C_0]
  have hφB : φ B = B' := by
    change B.map π = B'
    simp only [B, B', Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hmap : φ G = B' ^ (j+1) * φ d := by
    rw [← hrs, he, hd, map_add, map_mul, hφC, zero_mul, zero_add, map_mul, map_pow, hφB]
  have hzero : φ G = 0 := by
    by_contra hn
    have : Nontrivial (S ⧸ I) := by
      rcases subsingleton_or_nontrivial (S ⧸ I) with hsub | hnon
      · have := hsub
        exact False.elim (hn (Subsingleton.elim _ _))
      · exact hnon
    have hm : B'.Monic := monic_X_sub_C _
    have hdeg : (B' ^ (j+1)).natDegree = j+1 := by
      rw [hm.natDegree_pow, show B'.natDegree = 1 from natDegree_X_sub_C _, mul_one]
    have hlt : (φ G).natDegree < (B' ^ (j+1)).natDegree := by
      rw [hdeg]
      exact Nat.lt_succ_of_le (natDegree_map_le (p := G) (f := π))
    exact (hm.pow _).not_dvd_of_natDegree_lt hn hlt ⟨φ d, hmap⟩
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (G.coeff j) = 0
  rw [← coeff_map, show G.map π = 0 from hzero, coeff_zero]
private theorem fibre_leading_dvd {q : Surface} {y v : SeedClosure}
    (hq : OnSeedFibre q y v) {P : Jet} {k : ℕ} (h : OrderAt q P k) :
    (Polynomial.X - C y) ^ (k - P.natDegree) ∣ P.leadingCoeff.map seedGeneric := by
  have hi : Function.Injective (Polynomial.mapRingHom seedGeneric) :=
    Polynomial.map_injective _ seedGeneric_injective
  have hc := leading_dvd_of_contact (Polynomial.X - C y) (C v) (fibreRow P) k (h y v hq)
  unfold fibreRow at hc
  rw [natDegree_map_eq_of_injective hi, leadingCoeff_map_of_injective hi] at hc
  exact hc
private theorem minpoly_pow_dvd {y : SeedClosure} (hy : IsSeparable SeedField y)
    {n : ℕ} {g : (Polynomial SeedField)} (h : (Polynomial.X - C y) ^ n ∣ g.map toClosure) :
    minpoly SeedField y ^ n ∣ g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    by_cases hg : g = 0
    · simp [hg]
    have hgmap : g.map toClosure ≠ 0 :=
      (Polynomial.map_ne_zero_iff toClosure.injective).mpr hg
    have hlin : Polynomial.X - C y ∣ g.map toClosure :=
      (dvd_pow_self _ (by omega : n+1 ≠ 0)).trans h
    have hroot : (g.map toClosure).IsRoot y := dvd_iff_isRoot.mp hlin
    have hmin : minpoly SeedField y ∣ g := by
      apply minpoly.dvd
      simpa only [IsRoot.def, eval_map, aeval_def] using hroot
    obtain ⟨g', rfl⟩ := hmin
    have hsep : ((minpoly SeedField y).map toClosure).Separable :=
      Polynomial.Separable.map hy
    have hle := rootMultiplicity_le_one_of_separable hsep y
    rw [Polynomial.map_mul] at hgmap h
    have hmul := (le_rootMultiplicity_iff (a := y) hgmap).mpr h
    rw [rootMultiplicity_mul hgmap] at hmul
    have hg'map : g'.map toClosure ≠ 0 := right_ne_zero_of_mul hgmap
    have hrest : (Polynomial.X - C y) ^ n ∣ g'.map toClosure :=
      (le_rootMultiplicity_iff (a := y) hg'map).mp (by omega)
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih hrest)
@[instance_reducible] private def seedGCD : NormalizedGCDMonoid Seeds := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (σ := Fin 2)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds)
  exact UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
private theorem primitive_model (g : (Polynomial SeedField)) (hg : g ≠ 0) :
    ∃ f : Equation, f.IsPrimitive ∧ Associated (f.map toSeed) g := by
  classical
  let := seedGCD
  let D : Equation := IsLocalization.integerNormalization (nonZeroDivisors Seeds) g
  obtain ⟨a, ha, hD⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors Seeds) g
  have hD0 : D ≠ 0 :=
    (IsFractionRing.integerNormalization_eq_zero_iff (A := Seeds) (p := g)).not.mpr hg
  have hcontent : IsUnit (C (toSeed D.content)) := by
    apply isUnit_C.mpr
    exact ((map_ne_zero_iff toSeed toSeed_injective).mpr (content_eq_zero_iff.not.mpr hD0)).isUnit
  have ha' : IsUnit (C (toSeed a)) :=
    isUnit_C.mpr ((map_ne_zero_iff toSeed toSeed_injective).mpr (nonZeroDivisors.ne_zero ha)).isUnit
  have hscale : C (toSeed D.content) * D.primPart.map toSeed = C (toSeed a) * g := by
    calc
      _ = D.map toSeed := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← D.eq_C_content_mul_primPart]
      _ = _ := by
        simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hD
  refine ⟨D.primPart, D.isPrimitive_primPart, ?_⟩
  have hunit : Associated (C (toSeed a) * g) g := associated_unit_mul_left _ _ ha'
  rw [← hscale] at hunit
  exact (associated_unit_mul_right _ _ hcontent).trans hunit
private theorem eval_at_fibre_C (f : Equation) (y v : SeedClosure) :
    seedFibreEval y v (C f) = aeval y (f.map toSeed) := by
  change (eval₂RingHom (eval₂RingHom seedGeneric y) v) (C f) = _
  rw [coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, aeval_def, eval₂_map]
  rfl
/-- The squarefree projected equation records one copy of the minimal
polynomial of each distinct chosen ordinate. -/
def ordinateProduct {E : Type*} [Field E] [Algebra SeedField E]
    (qs : Finset Surface) (y : ↥qs → E) : Polynomial SeedField := by
  classical
  exact ∏ u ∈ qs.attach.image (fun q=>minpoly SeedField (y q)), u

theorem projected_from_points (qs : Finset Surface) (hqs : qs.Nonempty)
    (y v : ↥qs → SeedClosure) (hpoint : ∀ q,OnSeedFibre q.val (y q) (v q))
    (hy : ∀ q,IsSeparable SeedField (y q)) :
    ∃ f : Equation, ProjectedProduct qs f ∧
      Associated (f.map (algebraMap Seeds SeedField)) (ordinateProduct qs y) := by
  classical
  let m (q : ↥qs) := minpoly SeedField (y q)
  let factors : Finset ((Polynomial SeedField)) := qs.attach.image m
  have hmem (q : ↥qs) : m q ∈ factors :=
    Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  have hpre {u : (Polynomial SeedField)} (hu : u ∈ factors) : ∃ q : ↥qs, m q = u := by
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hu
    exact ⟨q, hq⟩
  have hmonic (u : (Polynomial SeedField)) (hu : u ∈ factors) : u.Monic := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.monic (hy q).isIntegral
  have hirr (u : (Polynomial SeedField)) (hu : u ∈ factors) : Irreducible u := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.irreducible (hy q).isIntegral
  have hpair (u : (Polynomial SeedField)) (hu : u ∈ factors) (w : (Polynomial SeedField)) (hw : w ∈ factors)
      (hne : u ≠ w) : IsCoprime u w := by
    apply (hirr u hu).coprime_iff_not_dvd.mpr
    intro hd
    exact hne (eq_of_monic_of_associated (hmonic u hu) (hmonic w hw)
      (associated_of_dvd_dvd hd ((hirr u hu).dvd_symm (hirr w hw) hd)))
  let g : (Polynomial SeedField) := ∏ u ∈ factors, u
  have hg : g ≠ 0 := (monic_prod_of_monic _ _ hmonic).ne_zero
  have hsep : g.Separable := by
    apply separable_prod' hpair
    intro u hu
    obtain ⟨q, rfl⟩ := hpre hu
    exact hy q
  have hm_dvd (q : ↥qs) : m q ∣ g := Finset.dvd_prod_of_mem id (hmem q)
  obtain ⟨f, hprim, hassoc⟩ := primitive_model g hg
  have hfmap : f.map toSeed ≠ 0 :=
    (Polynomial.map_ne_zero_iff toSeed_injective).mpr hprim.ne_zero
  refine ⟨f, ⟨?_, hprim, hsep.of_dvd hassoc.dvd, ?_, ?_⟩,hassoc⟩
  · obtain ⟨q, hq⟩ := hqs
    have hdeg := natDegree_le_of_dvd ((hm_dvd ⟨q, hq⟩).trans hassoc.dvd') hfmap
    rw [natDegree_map_eq_of_injective toSeed_injective] at hdeg
    exact (hirr _ (hmem ⟨q, hq⟩)).natDegree_pos.trans_le hdeg
  · intro q hq
    let q' : ↥qs := ⟨q, hq⟩
    rw [← hpoint q', RingHom.mem_ker, eval_at_fibre_C]
    exact minpoly.dvd_iff.mp ((hm_dvd q').trans hassoc.dvd')
  · intro P k _ horder
    let n := k - P.natDegree
    have hdiv : g ^ n ∣ P.leadingCoeff.map toSeed := by
      rw [show g ^ n = ∏ u ∈ factors, u ^ n from (Finset.prod_pow factors n id).symm]
      apply Finset.prod_dvd_of_coprime
      · intro u hu w hw hne
        exact (hpair u hu w hw hne).pow
      · intro u hu
        obtain ⟨q, rfl⟩ := hpre hu
        have hc := fibre_leading_dvd (hpoint q) (horder q q.property)
        rw [show seedGeneric = toClosure.comp toSeed from rfl, ← Polynomial.map_map] at hc
        exact minpoly_pow_dvd (hy q) hc
    let := seedGCD
    have hpow (e : ℕ) : (f ^ e).IsPrimitive := by
      induction e with
      | zero => simpa only [pow_zero] using (isPrimitive_one : (1 : Equation).IsPrimitive)
      | succ e ih => rw [pow_succ]; exact ih.mul hprim
    apply (hpow n).dvd_of_fraction_map_dvd_fraction_map (K := SeedField)
    rw [Polynomial.map_pow]
    exact hassoc.pow_pow.dvd.trans hdiv

theorem proof : K1_14_3.c7 := by
  classical
  intro qs hqs hparents
  choose y v hpoint hy _hv using fun q : ↥qs => (hparents q q.property).seed_side
  obtain ⟨f,product,_⟩ := projected_from_points qs hqs y v hpoint hy
  exact ⟨f,product⟩
end
end K1_14_3_7
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
private def bfPlane (r o : ℕ) : ℕ :=
  let lo := 48 - (r : ℤ)
  min (bandCount 48 lo 48 10)
    (sumRange 49 fun b =>
      min (pairBound 48 lo b) (sumRange (48 - b + 1) (lineBound 48 lo (o : ℤ) b)))
private structure BfEvaluator where
  get : ℕ → ℕ → ℕ
  correct : ∀ r o, bfPlane r o = get r o
end K1_13_1_1
end
section
namespace K1_13_6_3
noncomputable section
open K1_13 K1_13_6 Polynomial
open scoped BigOperators
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) GeoField
abbrev CoeffIdeal := Ideal CoeffRing
abbrev JetIdeal := Ideal GeoJets
abbrev dimension {k σ : Type*} [Field k] [Finite σ] (P : Ideal (MvPolynomial σ k)) :=
  (MvPolynomial.affineHilbertPolynomial P).natDegree
def geomConstants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
def genericArgument : GeoField := genericCoeffs Polynomial.X
def coeffPoint (S : (Polynomial Geom)) (i : Fin taylorLength) : Geom := S.coeff i
def jetLinear {k : Type*} [Field k] (a : k) (i : ℕ) :
    MvPolynomial (Fin taylorLength) k :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C ((j.val.choose i : k) * a ^ (j.val - i)) * MvPolynomial.X j
def extendIdeal (A : CoeffIdeal) : Ideal FreshCoeffRing :=
  A.map (MvPolynomial.map geomConstants)
def freshJetMap : GeoJets →+* FreshCoeffRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => jetLinear genericArgument i.val)
def freshImage (A : CoeffIdeal) : JetIdeal :=
  (extendIdeal A).comap freshJetMap
def FreshRegular (f : Row 4) (A : CoeffIdeal) : Prop :=
  ∃ r : ℕ, toGeneric ((separant^[r]) f) ∈ freshImage A ∧
    toGeneric (separant ((separant^[r]) f)) ∉ freshImage A
def FreshBirational (A : CoeffIdeal) : Prop :=
  ∀ h : FreshCoeffRing, ∃ u v : GeoJets,
    freshJetMap v ∉ extendIdeal A ∧
    h * freshJetMap v - freshJetMap u ∈ extendIdeal A
abbrev JetField (P : JetIdeal) := FractionRing (GeoJets ⧸ P)
def onComponent (P : JetIdeal) : GeoJets →+* JetField P :=
  (algebraMap (GeoJets ⧸ P) (JetField P)).comp (Ideal.Quotient.mk P)
def componentConstants (P : JetIdeal) : Geom →+* JetField P :=
  ((onComponent P).comp MvPolynomial.C).comp geomConstants
def coefficientKernel {F : Type*} [Field F] (k : Geom →+* F) (U : (Polynomial F)) : CoeffIdeal :=
  RingHom.ker (MvPolynomial.eval₂Hom k (fun i => U.coeff i.val))
def trajectory {F : Type*} [Field F] (k : Geom →+* F) (P : Row 4) (U : (Polynomial F)) : (Polynomial F) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom k) (fun i => hasseDeriv i.val U) P
structure SimpleCut (g : Row 4) (surface P : JetIdeal) : Prop where
  proper : toGeneric (membershipTest g) ∉ surface
  minimal : (divisorIdeal surface (membershipTest g)).IsMinimalPrime P
  one : cycleLength (divisorIdeal surface (membershipTest g)) P minimal.isPrime = 1
  next : toGeneric (nextTest g) ∈ P
structure Integrated (f Q g : Row 4) (P : JetIdeal) [P.IsPrime]
    (U : (Polynomial (JetField P))) : Prop where
  degree : U.natDegree < taylorLength
  initial : ∀ i : Fin 4,
    (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
      onComponent P (MvPolynomial.X i)
  factor : trajectory (componentConstants P) f U = 0
  cutter : trajectory (componentConstants P) Q U = 0
  chart : trajectory (componentConstants P) g U = 0
  specializes : ∀ S : (Polynomial Geom), S.natDegree < taylorLength → P ≤ markIdeal S →
    atJet (separant g) S ≠ 0 →
    coeffPoint S ∈ MvPolynomial.zeroLocus Geom (coefficientKernel (componentConstants P) U)
structure FreshModel (f : Row 4) (A : CoeffIdeal) : Prop where
  prime : A.IsPrime
  extended_prime : (extendIdeal A).IsPrime
  regular : FreshRegular f A
  birational : FreshBirational A
def cycleWeight (J P : JetIdeal) : ℕ := by
  classical
  exact if hp : P.IsPrime then (cycleLength J P hp).toNat else 0
end
end K1_13_6_3
end
section
set_option autoImplicit false
namespace K1_13_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open scoped BigOperators
def markPoint (s : K → (Polynomial K)) (γ : K) : Fin taylorLength → Geom :=
  coeffPoint (extend (s γ))
def valueCut (x a : K) : CoeffRing := jetLinear (embed x) 0 - MvPolynomial.C (embed a)
theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  unfold valueCut jetLinear
  apply (totalDegree_sub _ _).trans
  simp only [totalDegree_C, Nat.max_zero]
  exact totalDegree_finsetSum_le (fun j _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add]))
theorem valueCut_eval {s : K → (Polynomial K)} {γ x a : K} (h : (s γ).natDegree < taylorLength) :
    aeval (markPoint s γ) (valueCut x a) = 0 ↔ (s γ).eval x = a := by
  have heval : aeval (markPoint s γ) (jetLinear (embed x) 0) = embed ((s γ).eval x) := by
    rw [Polynomial.eval_eq_sum_range' h, ← Fin.sum_univ_eq_sum_range, map_sum]
    simp only [jetLinear, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self_apply, Nat.choose_zero_right,
      Nat.cast_one, Nat.sub_zero, one_mul, markPoint, coeffPoint, Polynomial.coeff_map, mul_comm]
  rw [valueCut, map_sub, heval, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, sub_eq_zero, embed.injective.eq_iff]
def degreeAllowance (A : CoeffIdeal) : ℕ := ⌊affineDegree A⌋₊
theorem degreeAllowance_le (A : CoeffIdeal) : (degreeAllowance A : ℚ) ≤ affineDegree A :=
  Nat.floor_le (affineDegree_nonneg A)
private theorem degree_at_point {A : CoeffIdeal} (hp : A.IsPrime)
    {x : Fin taylorLength → Geom} (hx : x ∈ zeroLocus Geom A) : 1 ≤ affineDegree A := by
  classical
  generalize hd : dimension A = d
  induction d using Nat.strong_induction_on generalizing A with
  | ind d ih =>
    by_cases hd0 : d = 0
    · obtain ⟨hf, hdeg⟩ := finite_zeroLocus_and_ncard_le_affineDegree
        (K := Geom) A (hd.trans hd0)
      have hcard : 1 ≤ (zeroLocus Geom A).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hf
      exact (by exact_mod_cast hcard : (1 : ℚ) ≤ _).trans hdeg
    have hcut : ∃ i, MvPolynomial.X i - MvPolynomial.C (x i) ∉ A := by
      by_contra! hall
      let φ := Ideal.Quotient.mk A
      have hmaps : φ = φ.comp (MvPolynomial.C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, MvPolynomial.eval_X]
          exact sub_eq_zero.mp (by
            rw [← map_sub]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj : Function.Surjective (algebraMap Geom (CoeffRing ⧸ A)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      let _ : Module.Finite Geom (CoeffRing ⧸ A) :=
        Module.Finite.of_surjective (Algebra.linearMap Geom (CoeffRing ⧸ A)) hsurj
      exact hd0 (hd.symm.trans (by simp [dimension, affineHilbertPolynomial_eq_C_finrank]))
    obtain ⟨i, hi⟩ := hcut
    let cut : CoeffRing := MvPolynomial.X i - MvPolynomial.C (x i)
    have hdeg : cut.totalDegree ≤ 1 := (totalDegree_sub _ _).trans (by simp)
    have hzero : x ∈ zeroLocus Geom (A ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, by simp [cut]⟩
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      _ (1 : CoeffRing) _ hzero (by simp)
    have hm := (Ideal.mem_retainedMinimalPrimes.mp hB).1
    let _ := hp
    have hdim := principalCut_natDegree_affineHilbertPolynomial_add_one hi hm
    change dimension B + 1 = dimension A at hdim
    have hBdeg := ih (dimension B) (by omega) hm.isPrime hxB rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : CoeffRing) hi hdeg
    have hle := Finset.single_le_sum (f := affineDegree) (fun B _ => affineDegree_nonneg B) hB
    simpa only [Nat.cast_one, one_mul] using hBdeg.trans (hle.trans hsum)
def marksOn (Γ : Finset K) (s : K → (Polynomial K)) (A : CoeffIdeal) : Finset K := by
  classical
  exact Γ.filter fun γ => markPoint s γ ∈ zeroLocus Geom A
theorem mem_marksOn {Γ : Finset K} {s : K → (Polynomial K)} {A : CoeffIdeal} {γ : K} :
    γ ∈ marksOn Γ s A ↔ γ ∈ Γ ∧ markPoint s γ ∈ zeroLocus Geom A := by
  classical
  simp [marksOn]
theorem degreeAllowance_pos {Γ : Finset K} {s : K → (Polynomial K)} {A : CoeffIdeal}
    (hp : A.IsPrime) (h : (marksOn Γ s A).Nonempty) : 0 < degreeAllowance A := by
  obtain ⟨γ, hγ⟩ := h
  exact Nat.floor_pos.mpr (degree_at_point hp (mem_marksOn.mp hγ).2)
def piecesOf {Γ : Finset K} (T : Finset CoeffIdeal) (part : CoeffIdeal → Finset K)
    (hpart : ∀ A ∈ T, part A ⊆ Γ) : Pieces Γ :=
  ⟨T.card, fun i => part (T.equivFin.symm i),
    fun i => hpart _ (T.equivFin.symm i).property, fun i => degreeAllowance (T.equivFin.symm i)⟩
theorem mem_piecesOf {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} {γ : K} :
    γ ∈ (piecesOf T part hpart).union ↔ ∃ A ∈ T, γ ∈ part A := by
  classical
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨T.equivFin.symm i, (T.equivFin.symm i).property, hi⟩
  · rintro ⟨A, hA, hγ⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨T.equivFin ⟨A, hA⟩, Finset.mem_univ _, ?_⟩
    simpa [piecesOf] using hγ
theorem piecesOf_total {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    (piecesOf T part hpart).total = ∑ A ∈ T, degreeAllowance A := by
  change ∑ i : Fin T.card, degreeAllowance (T.equivFin.symm i) = _
  calc
    _ = ∑ A : T, degreeAllowance A := Fintype.sum_equiv T.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_attach T degreeAllowance
theorem piecesOf_le_degree {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    ((piecesOf T part hpart).total : ℚ) ≤ ∑ A ∈ T, affineDegree A := by
  rw [piecesOf_total, Nat.cast_sum]
  exact Finset.sum_le_sum fun A _ => degreeAllowance_le A
private theorem proper_cut {Γ : Finset K} {s : K → (Polynomial K)} {A : CoeffIdeal} {x a : K}
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A)
    (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a) : valueCut x a ∉ A := by
  obtain ⟨γ, hγ, hmiss⟩ := hmiss
  exact fun hmem => hmiss (valueCut_eval (hdegree γ hγ) |>.mp (hpoints γ hγ _ hmem))
private theorem mark_on_cut {s : K → (Polynomial K)} {A : CoeffIdeal} {x a γ : K}
    (hdegree : (s γ).natDegree < taylorLength) (hpoint : markPoint s γ ∈ zeroLocus Geom A)
    (hvalue : (s γ).eval x = a) :
    markPoint s γ ∈ zeroLocus Geom (A ⊔ Ideal.span {valueCut x a}) :=
  mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint, (valueCut_eval hdegree).mpr hvalue⟩
theorem curveSections_of_prime {Γ : Finset K} {s : K → (Polynomial K)} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 1)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    CurveSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss
  let cut := valueCut x a
  let J := A ⊔ Ideal.span {cut}
  let H := Γ.filter fun γ => (s γ).eval x = a
  have hproper := proper_cut hdegree hpoints hmiss
  have hJdim : dimension J = 0 := by
    have hd := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).1
    change dimension J ≤ dimension A - 1 at hd
    omega
  have hJdeg : affineDegree J ≤ affineDegree A := by
    have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).2
    have ha : (affineHilbertPolynomial A).natDegree = 1 := hdim
    have hj : (affineHilbertPolynomial J).natDegree = 0 := hJdim
    simpa [affineDegree, ha, hj, J, cut, Polynomial.leadingCoeff] using h
  obtain ⟨hfinite, hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) J hJdim
  have hsub : (H.image (markPoint s) : Set _) ⊆ zeroLocus Geom J := by
    intro p hp
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hΓ, hv⟩ := Finset.mem_filter.mp hγ
    exact mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hv
  have hcount := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn
    (hdistinct.mono (Finset.filter_subset _ _))] at hcount
  exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hJdeg))
theorem surfaceSections_of_prime {Γ : Finset K} {s : K → (Polynomial K)} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 2)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    SurfaceSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss H
  let J := A ⊔ Ideal.span {valueCut x a}
  let T := J.minimalPrimesFinset.filter (fun B => (marksOn H s B).Nonempty)
  have hproper := proper_cut hdegree hpoints hmiss
  have hsubset (B : CoeffIdeal) (_ : B ∈ T) : marksOn H s B ⊆ H :=
    fun _ h => (mem_marksOn.mp h).1
  have hprime (B : CoeffIdeal) (hB : B ∈ T) : J.IsMinimalPrime B :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
  refine ⟨piecesOf T (marksOn H s) hsubset, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hΓ, hvalue⟩ := Finset.mem_filter.mp hγ
    have hzero : markPoint s γ ∈ zeroLocus Geom J :=
      mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hvalue
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      J (1 : CoeffRing) _ hzero (by simp)
    have hmarks : γ ∈ marksOn H s B := mem_marksOn.mpr ⟨hγ, hxB⟩
    exact mem_piecesOf.mpr ⟨B, Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hB).1, ⟨γ, hmarks⟩⟩, hmarks⟩
  · intro i
    let B := T.equivFin.symm i
    have hm := hprime B B.property
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hm
    change dimension (B : CoeffIdeal) + 1 = dimension A at hd
    have hdimB : dimension (B : CoeffIdeal) = 1 := by omega
    apply curveSections_of_prime hm.isPrime hdimB
    · exact fun γ hγ => hdegree γ (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1
    · exact hdistinct.mono (fun γ hγ => (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1)
    · exact fun _ hγ => (mem_marksOn.mp hγ).2
  · intro i
    let B := T.equivFin.symm i
    exact degreeAllowance_pos (hprime B B.property).isPrime
      (Finset.mem_filter.mp B.property).2
  · apply Nat.le_floor
    have hsum := principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
    exact piecesOf_le_degree.trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun B _ _ => affineDegree_nonneg B)).trans
      (by simpa only [Nat.cast_one, one_mul] using hsum))
end
end K1_13_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (f Q : Row 4) (surface : JetIdeal) (r : ℕ) (P : JetIdeal)
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    CanonicalChart f surface r →
    cycleLength (intersectionIdeal f Q) surface hz.isPrime < (K1.p : ℕ∞) →
    let g := (separant^[r]) f
    Invariant g surface → SimpleCut g surface P → Invariant g P
def c3 : Prop :=
  (∀ (f Q : Row 4) (surface : JetIdeal) (r : ℕ) (P : JetIdeal) (hp : P.IsPrime)
      (U : (Polynomial (JetField P))),
    (intersectionIdeal f Q).IsMinimalPrime surface →
    (∀ T, (intersectionIdeal f Q).IsMinimalPrime T → dimension T = 2) →
    let g := (separant^[r]) f
    toGeneric (separant g) ∉ P → (P = surface ∨ SimpleCut g surface P) →
    @Integrated f Q g P hp U →
    let A := coefficientKernel (componentConstants P) U
    FreshModel f A ∧
      ((dimension A = 1 ∧ freshImage A = P ∧ SimpleCut g surface P) ∨
        (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A)))) ∧
  (∀ f : Row 4, Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A})
def c4 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime → dimension A = 1 →
    FreshBirational A → affineDegree A = affineDegree (freshImage A)
end
end K1_13_6_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3
variable {k σ τ : Type*} [Field k]
def boundaryIdeal (A : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  Ideal.span {g | ∃ f ∈ A, homogeneousComponent f.totalDegree f = g}
def boundaryWeight (J P : Ideal (MvPolynomial σ k)) : ℕ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let L := Localization.AtPrime P
    (Module.length L (L ⧸ J.map (algebraMap (MvPolynomial σ k) L))).toNat
  else 0
def residueDegree (φ : MvPolynomial τ k →+* MvPolynomial σ k)
    (P : Ideal (MvPolynomial σ k)) : ℕ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    letI : (P.comap φ).IsPrime := Ideal.IsPrime.comap φ
    let f : FractionRing (MvPolynomial τ k ⧸ P.comap φ) →+*
        FractionRing (MvPolynomial σ k ⧸ P) :=
      IsFractionRing.map (Ideal.quotientMap_injective (I := P) (f := φ))
    letI := f.toAlgebra
    Module.finrank (FractionRing (MvPolynomial τ k ⧸ P.comap φ))
      (FractionRing (MvPolynomial σ k ⧸ P))
  else 0
def IsLinearProjection (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) : Prop :=
  ∀ i, (φ (MvPolynomial.X i)).IsHomogeneous 1
def IsBirationalOn (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (A : Ideal (MvPolynomial σ k)) : Prop :=
  ∀ h : MvPolynomial σ k, ∃ u v : MvPolynomial τ k, φ v ∉ A ∧ h * φ v - φ u ∈ A
def freshProjection : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
theorem freshProjection_linear : IsLinearProjection freshProjection := by
  intro i
  rw [freshProjection, aeval_X, jetLinear]
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C _ _).mul (isHomogeneous_X _ j)
end
end K1_13_6_3_5
end
section
set_option autoImplicit false
namespace K1_13_6_3_6
noncomputable section
open K1_13_6 K1_13_6_3
open scoped BigOperators
section Quotients
variable {R : Type} [CommRing R]
def quotientMul (I : Ideal R) (g : R) :
    (R ⧸ I.colon {g}) →ₗ[R] (R ⧸ I) :=
  (I.colon {g}).liftQ (LinearMap.toSpanSingleton R (R ⧸ I) (Ideal.Quotient.mk I g))
    fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      change Ideal.Quotient.mk I a * Ideal.Quotient.mk I g = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mp ha)
@[simp]
theorem quotientMul_mk (I : Ideal R) (g a : R) :
    quotientMul I g (Ideal.Quotient.mk (I.colon {g}) a) = Ideal.Quotient.mk I (a * g) := by
  change quotientMul I g (Submodule.Quotient.mk a) = _
  rw [quotientMul, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
  exact (map_mul (Ideal.Quotient.mk I) a g).symm
theorem quotientMul_injective (I : Ideal R) (g : R) : Function.Injective (quotientMul I g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [quotientMul_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mpr ha)
theorem quotientMul_exact (I : Ideal R) (g : R) :
    Function.Exact (quotientMul I g)
      (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {g})) := by
  rw [LinearMap.exact_iff]
  ext y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  change (Ideal.Quotient.mk (I ⊔ Ideal.span {g}) b = 0 ↔ _)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hb
    obtain ⟨i, hi, j, hj, hsum⟩ := Submodule.mem_sup.mp hb
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp hj
    refine ⟨Ideal.Quotient.mk (I.colon {g}) x, ?_⟩
    rw [quotientMul_mk, Ideal.Quotient.eq, ← hsum]
    convert I.neg_mem hi using 1
    ring
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [quotientMul_mk, Ideal.Quotient.eq] at ha
    have hx : x * g ∈ I ⊔ Ideal.span {g} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨x, mul_comm x g⟩)
    simpa using (I ⊔ Ideal.span {g}).sub_mem hx (Ideal.mem_sup_left ha)
theorem colon_map_localization {S : Type} [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S] (I : Ideal R) (g : R) :
    (I.colon {g}).map (algebraMap R S) = (I.map (algebraMap R S)).colon {algebraMap R S g} := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  rw [Submodule.mem_colon_singleton, smul_eq_mul,
    mul_comm _ (algebraMap R S g), IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc, mul_comm g]
end Quotients
theorem length_step (I P : JetIdeal) (hp : P.IsPrime) (g : GeoJets) :
    cycleLength I P hp =
      cycleLength (I.colon {g}) P hp + cycleLength (I ⊔ Ideal.span {g}) P hp := by
  have := hp
  let L := Localization.AtPrime P
  let r := algebraMap GeoJets L
  let J := I.map r
  let a := r g
  have h := Module.length_eq_add_of_exact (quotientMul J a)
    (Submodule.factor (le_sup_left : J ≤ J ⊔ Ideal.span {a}))
    (quotientMul_injective J a) (Submodule.factor_surjective le_sup_left)
    (quotientMul_exact J a)
  change Module.length L (L ⧸ I.map r) =
    Module.length L (L ⧸ (I.colon {g}).map r) + Module.length L (L ⧸ (I ⊔ Ideal.span {g}).map r)
  rw [colon_map_localization P.primeCompl, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact h
theorem length_eq_zero_of_not_le {I P : JetIdeal} (hp : P.IsPrime) (h : ¬ I ≤ P) :
    cycleLength I P hp = 0 := by
  have := hp
  let L := Localization.AtPrime P
  have htop : I.map (algebraMap GeoJets L) = ⊤ := by
    by_contra ht
    exact h (Set.disjoint_compl_left_iff_subset.mp
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mp ht))
  change Module.length L (L ⧸ I.map (algebraMap GeoJets L)) = 0
  simp [htop, Module.length_eq_zero]
theorem length_self (P : JetIdeal) (hp : P.IsPrime) : cycleLength P P hp = 1 := by
  have := hp
  let L := Localization.AtPrime P
  change Module.length L (L ⧸ P.map (algebraMap GeoJets L)) = 1
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  have h : IsSimpleModule L (L ⧸ IsLocalRing.maximalIdeal L) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
  exact Module.length_eq_one _ _
theorem length_pos {I P : JetIdeal} (hp : P.IsPrime) (h : I ≤ P) :
    1 ≤ cycleLength I P hp := by
  have := hp
  let L := Localization.AtPrime P
  have htop : I.map (algebraMap GeoJets L) ≠ ⊤ :=
    ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mpr
      (Set.disjoint_compl_left_iff_subset.mpr h))
  have := Ideal.Quotient.nontrivial_iff.mpr htop
  exact Order.one_le_iff_ne_zero.mpr (Module.length_pos (R := L)).ne'
theorem exists_prime_colon (I : JetIdeal) (hI : I ≠ ⊤) :
    ∃ g : GeoJets, g ∉ I ∧ (I.colon {g}).IsPrime := by
  let _ := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨A, hA, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
    GeoJets (1 : GeoJets ⧸ I) one_ne_zero
  obtain ⟨hp, x, hx⟩ := isAssociatedPrime_iff.mp hA
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  have heq : A = I.colon {g} := by
    ext a
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I g = 0 ↔ a * g ∈ I
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [heq] at hp
  refine ⟨g, fun hg => hp.ne_top ?_, hp⟩
  simpa only [Submodule.colon_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe] using hg
end
end K1_13_6_3_6
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_3_5
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ (k σ : Type) [Field k] [Finite σ] (A : Ideal (MvPolynomial σ k)),
    A.IsPrime → dimension A = 2 →
    (∀ P, (boundaryIdeal A).IsMinimalPrime P →
      dimension P = 2 ∧ P.IsHomogeneous (homogeneousSubmodule σ k)) ∧
    affineDegree A = ∑ P ∈ (boundaryIdeal A).minimalPrimesFinset,
      (boundaryWeight (boundaryIdeal A) P : ℚ) * affineDegree P
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime →
    affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A ∧
    ∀ P, (boundaryIdeal (extendIdeal A)).IsMinimalPrime P →
      ∃ R, (boundaryIdeal A).IsMinimalPrime R ∧ extendIdeal R = P
def c3 : Prop :=
  ∀ R : CoeffIdeal, R.IsPrime → (extendIdeal R).IsPrime →
    R.IsHomogeneous (homogeneousSubmodule (Fin K1_13.taylorLength) K1_13.Geom) →
    dimension R = 2 →
    dimension (freshImage R) = 2 ∧
    2 * affineDegree (extendIdeal R) ≤
      133671 * (residueDegree freshJetMap (extendIdeal R) : ℚ) *
        affineDegree (freshImage R)
def c4 : Prop :=
  ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → dimension A = 2 → IsBirationalOn φ A →
      dimension (A.comap φ) = 2 ∧
      ∀ P, (boundaryIdeal A).IsMinimalPrime P → dimension (P.comap φ) = 2 →
        (boundaryIdeal (A.comap φ)).IsMinimalPrime (P.comap φ)
def c5 : Prop := by
  classical
  exact ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → IsBirationalOn φ A →
    ∀ Q : Ideal (MvPolynomial τ k), (boundaryIdeal (A.comap φ)).IsMinimalPrime Q →
      (∑ P ∈ (boundaryIdeal A).minimalPrimesFinset.filter (fun P => P.comap φ = Q),
        boundaryWeight (boundaryIdeal A) P * residueDegree φ.toRingHom P) ≤
      boundaryWeight (boundaryIdeal (A.comap φ)) Q
end
end K1_13_6_3_5
end
section
set_option autoImplicit false
namespace K1_13_6_3_4
noncomputable section
open K1_13_6_3 MvPolynomial
def boundaryIdeal {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span {q | ∃ (p : MvPolynomial σ k) (n : ℕ),
    p ∈ I ∧ p.totalDegree ≤ n ∧ q = homogeneousComponent n p}
def boundaryChart {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) (i : σ) :
    Ideal (MvPolynomial σ k) :=
  boundaryIdeal I ⊔ Ideal.span {MvPolynomial.X i - 1}
def NoBoundaryZero {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (ℓ : MvPolynomial σ k) : Prop :=
  ∀ b : σ → k, b ∈ zeroLocus k (boundaryIdeal I) → eval b ℓ = 0 → b = 0
def ValueReduction {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (ℓ : MvPolynomial σ k) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ quotientDegreeLE I (n + 1),
    ∃ a ∈ quotientDegreeLE I n, ∃ b ∈ quotientDegreeLE I n,
      z = a + Ideal.Quotient.mk I ℓ * b
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_4_2
noncomputable section
open MvPolynomial K1_13_6_3_4
open scoped MonomialOrder
variable {k σ : Type*} [Field k]
theorem component_mul_homogeneous {p q : MvPolynomial σ k} {d : ℕ}
    (hq : q.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (p * q) =
      if d ≤ n then homogeneousComponent (n - d) p * q else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent p, Finset.sum_mul, map_sum]
  simp only [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous _ _).mul hq)]
  by_cases hd : d ≤ n
  · rw [ite_eq_left hd]
    by_cases hr : n - d ∈ Finset.range (p.totalDegree + 1)
    · rw [Finset.sum_eq_single_of_mem (n - d) hr]
      · simp [Nat.sub_add_cancel hd]
      · intro b _ hb
        rw [ite_eq_right (by omega)]
    · have hlt : p.totalDegree < n - d := by
        rw [Finset.mem_range] at hr
        omega
      rw [homogeneousComponent_eq_zero _ _ hlt, zero_mul]
      exact Finset.sum_eq_zero fun b hb => ite_eq_right (by
        have := Finset.mem_range.mp hb
        omega)
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun b _ => ite_eq_right (by omega)
theorem lift_boundary_component (I : Ideal (MvPolynomial σ k)) {q : MvPolynomial σ k}
    (hq : q ∈ boundaryIdeal I) (n : ℕ) :
    ∃ p ∈ I, p.totalDegree ≤ n ∧ homogeneousComponent n p = homogeneousComponent n q := by
  revert n
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨p, d, hp, hd, rfl⟩ := hq
    intro n
    by_cases h : n = d
    · subst n
      exact ⟨p, hp, hd, (homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous d p)).symm⟩
    · exact ⟨0, I.zero_mem, by simp, by
        rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous d p), ite_eq_right h, map_zero]⟩
  | zero => exact fun _ => ⟨0, I.zero_mem, by simp, rfl⟩
  | add q r _ _ hq hr =>
    intro n
    obtain ⟨p, hp, hn, he⟩ := hq n
    obtain ⟨s, hs, hm, hf⟩ := hr n
    exact ⟨p + s, I.add_mem hp hs, (totalDegree_add _ _).trans (max_le hn hm), by
      rw [map_add, map_add, he, hf]⟩
  | smul a q _ hq =>
    intro n
    change ∃ p ∈ I, p.totalDegree ≤ n ∧ homogeneousComponent n p = homogeneousComponent n (a * q)
    induction a using MvPolynomial.induction_on' with
    | monomial e c =>
      rw [mul_comm, component_mul_homogeneous (isHomogeneous_monomial c rfl)]
      split_ifs with h
      · obtain ⟨p, hp, hn, he⟩ := hq (n - e.degree)
        refine ⟨p * monomial e c, I.mul_mem_right _ hp,
          (totalDegree_mul _ _).trans ?_, ?_⟩
        · have hmono := (isHomogeneous_monomial c (rfl : e.degree = e.degree)).totalDegree_le
          omega
        · rw [component_mul_homogeneous (isHomogeneous_monomial c rfl), ite_eq_left h, he]
      · exact ⟨0, I.zero_mem, by simp, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨p, hp, hn, he⟩ := ha
      obtain ⟨s, hs, hm, hf⟩ := hb
      exact ⟨p + s, I.add_mem hp hs, (totalDegree_add _ _).trans (max_le hn hm), by
        rw [add_mul, map_add, map_add, he, hf]⟩
theorem boundary_component_mem (I : Ideal (MvPolynomial σ k)) {q : MvPolynomial σ k}
    (hq : q ∈ boundaryIdeal I) (n : ℕ) : homogeneousComponent n q ∈ boundaryIdeal I := by
  obtain ⟨p, hp, hd, he⟩ := lift_boundary_component I hq n
  exact Ideal.subset_span ⟨p, n, hp, hd, he.symm⟩
private theorem leading_component [LinearOrder σ] [WellFoundedGT σ]
    {p : MvPolynomial σ k} (hp : p ≠ 0) :
    (homogeneousComponent p.totalDegree p) ≠ 0 ∧
      MonomialOrder.degLex.degree (homogeneousComponent p.totalDegree p) =
        MonomialOrder.degLex.degree p := by
  let m := MonomialOrder.degLex (σ := σ)
  have hmem := m.degree_mem_support hp
  have htop : m.degree p ∈ (homogeneousComponent p.totalDegree p).support := by
    rw [support_homogeneousComponent, Finset.mem_filter]
    exact ⟨hmem, degree_degLexDegree⟩
  have hne : (homogeneousComponent p.totalDegree p) ≠ 0 := by
    intro h
    simp [h] at htop
  refine ⟨hne, m.toSyn.injective (le_antisymm ?_ (m.le_degree htop))⟩
  apply m.le_degree
  have h := m.degree_mem_support hne
  rw [support_homogeneousComponent, Finset.mem_filter] at h
  exact h.1
theorem hilbertPolynomial_boundary [LinearOrder σ] [WellFoundedGT σ] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (boundaryIdeal I) = affineHilbertPolynomial I := by
  have he : MonomialOrder.degLex.standardExponents (boundaryIdeal I) =
      MonomialOrder.degLex.standardExponents I := by
    ext e
    constructor
    · intro h p hp hp₀ hle
      obtain ⟨hq, hd⟩ := leading_component hp₀
      exact h _ (Ideal.subset_span ⟨p, p.totalDegree, hp, le_rfl, rfl⟩) hq (hd.symm ▸ hle)
    · intro h q hq hq₀ hle
      obtain ⟨p, hp, hn, htop⟩ := lift_boundary_component I hq q.totalDegree
      obtain ⟨hne, hd⟩ := leading_component hq₀
      have heq : p.totalDegree = q.totalDegree := by
        by_contra h
        rw [homogeneousComponent_eq_zero _ _ (lt_of_le_of_ne hn h)] at htop
        exact hne htop.symm
      have hp₀ : p ≠ 0 := fun h => hne (by simpa [h] using htop.symm)
      have hd' := (leading_component hp₀).2
      rw [heq, htop, hd] at hd'
      exact h p hp hp₀ (hd'.symm ▸ hle)
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
  intro n hn
  rw [affineHilbertFunction_eq_standard_count, he, ← affineHilbertFunction_eq_standard_count]
  exact hN n hn
end
end K1_13_5_4_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_4_2
noncomputable section
open MvPolynomial K1_13_6_3_4
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]
private theorem linear_cut_regular (I : Ideal (MvPolynomial σ k)) (i : σ) :
    IsLeftRegular (Ideal.Quotient.mk (boundaryIdeal I) (MvPolynomial.X i - 1)) := by
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
  have h (n : ℕ) : homogeneousComponent n p ∈ boundaryIdeal I := by
    induction n with
    | zero =>
      have h₀ := boundary_component_mem I hz 0
      rw [sub_mul, one_mul, map_sub, mul_comm (MvPolynomial.X i),
        component_mul_homogeneous (isHomogeneous_X k i), ite_eq_right (by omega), zero_sub] at h₀
      exact neg_mem_iff.mp h₀
    | succ n ih =>
      have hn := boundary_component_mem I hz (n + 1)
      rw [sub_mul, one_mul, map_sub, mul_comm (MvPolynomial.X i),
        component_mul_homogeneous (isHomogeneous_X k i), ite_eq_left (by omega),
        Nat.add_sub_cancel] at hn
      exact (Submodule.sub_mem_iff_right (boundaryIdeal I) (Ideal.mul_mem_right _ _ ih)).mp hn
  rw [Ideal.Quotient.eq_zero_iff_mem, ← sum_homogeneousComponent p]
  exact (boundaryIdeal I).sum_mem fun n _ => h n
theorem boundaryChart_dimension [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ k)) (hI : (affineHilbertPolynomial I).natDegree = 1) (i : σ) :
    (affineHilbertPolynomial (boundaryChart I i)).natDegree = 0 := by
  have hdeg : (MvPolynomial.X i - 1 : MvPolynomial σ k).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (totalDegree_X i).le (by simp))
  have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (linear_cut_regular I i) hdeg).1
  rw [hilbertPolynomial_boundary I, hI] at h
  exact Nat.eq_zero_of_le_zero h
private theorem drop_component {p : MvPolynomial σ k} {n : ℕ} (h : p.totalDegree ≤ n + 1) :
    (p - homogeneousComponent (n + 1) p).totalDegree ≤ n := by
  refine Finset.sup_le fun d hd => ?_
  change d.degree ≤ n
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hd
  by_contra! hnd
  have hs : n + 1 ≤ d.degree := Nat.succ_le_of_lt hnd
  rcases eq_or_lt_of_le hs with he | hlt
  · simp [← he] at hd
  · have hp := coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt h hlt)
    simp [hp] at hd
theorem valueReduction_of_geometric [Finite σ] [IsAlgClosed K] (I : Ideal (MvPolynomial σ k))
    {l : MvPolynomial σ k} (hl : l.IsHomogeneous 1)
    (hfree : ∀ x : σ → K, x ∈ zeroLocus K (boundaryIdeal I) → aeval x l = 0 → x = 0) :
    ValueReduction I l := by
  let J := boundaryIdeal I ⊔ Ideal.span {l}
  have hrad : idealOfVars σ k ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    rw [aeval_X, hfree x (zeroLocus_anti_mono (le_sup_left : boundaryIdeal I ≤ J) hx)
      (hx l (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l)))]
    rfl
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ k)
  refine ⟨N, fun n hn z hz => ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hz
  have hm : homogeneousComponent (n + 1) p ∈ J := by
    apply hN
    apply (mem_pow_idealOfVars_iff N _).2
    intro e he
    have heq : e.degree = n + 1 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp he) ((homogeneousComponent_isHomogeneous (n + 1) p).coeff_eq_zero hne)
    omega
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  obtain ⟨u, hu, hdu, huc⟩ := lift_boundary_component I hq (n + 1)
  have hc : homogeneousComponent (n + 1) (p - u - l * homogeneousComponent n s) = 0 := by
    have ht := congrArg (homogeneousComponent (n + 1)) he
    rw [homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
      map_add, component_mul_homogeneous hl, ite_eq_left (by omega), Nat.add_sub_cancel] at ht
    rw [map_sub, map_sub, huc, ← ht, add_sub_cancel_left, mul_comm l,
      homogeneousComponent_eq_self ((homogeneousComponent_isHomogeneous _ _).mul hl), sub_self]
  let a := p - u - l * homogeneousComponent n s
  have ha : a.totalDegree ≤ n + 1 :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le hp hdu))
      ((totalDegree_mul _ _).trans (by
        have hs := (homogeneousComponent_isHomogeneous n s).totalDegree_le
        have hld := hl.totalDegree_le
        omega)))
  have ha' : a.totalDegree ≤ n := by simpa [a, hc] using drop_component ha
  refine ⟨Ideal.Quotient.mk I a, mk_mem_quotientDegreeLE ha',
    Ideal.Quotient.mk I (homogeneousComponent n s),
    mk_mem_quotientDegreeLE ((homogeneousComponent_isHomogeneous _ _).totalDegree_le), ?_⟩
  rw [← map_mul, ← map_add]
  dsimp only [a]
  rw [sub_add_cancel, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hu, sub_zero]
end
end K1_13_5_4_4_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial WithZero
variable (k L : Type) [Field k] [Field L] [Algebra k L]
def CurveField : Prop :=
  ∃ t : L, Transcendental k t ∧ Module.Finite (IntermediateField.adjoin k {t}) L
structure CurvePlace where
  value : Valuation L ℤᵐ⁰
  normalized : Function.Surjective value
  on_constants : ∀ c : k, c ≠ 0 → value (algebraMap k L c) = 1
variable {L} in
def poleOrder (v : Valuation L ℤᵐ⁰) (x : L) : ℕ :=
  (WithZero.log (v x)).toNat
variable {L} in
def zeroOrder (v : Valuation L ℤᵐ⁰) (x : L) : ℕ :=
  (-WithZero.log (v x)).toNat
variable {L} in
def tuplePole {σ : Type} [Fintype σ] (v : Valuation L ℤᵐ⁰) (u : σ → L) : ℕ :=
  Finset.univ.sup (fun i => poleOrder v (u i))
def tupleHeight {σ : Type} [Fintype σ] (u : σ → L) : ℕ :=
  ∑ᶠ v : CurvePlace k L, tuplePole v.value u
def PrincipalDivisors : Prop :=
  ∀ x : L,
    (fun v : CurvePlace k L => poleOrder v.value x).HasFiniteSupport ∧
    (fun v : CurvePlace k L => zeroOrder v.value x).HasFiniteSupport ∧
    (∑ᶠ v : CurvePlace k L, poleOrder v.value x) =
      (∑ᶠ v : CurvePlace k L, zeroOrder v.value x) ∧
    (Transcendental k x →
      (∑ᶠ v : CurvePlace k L, poleOrder v.value x) =
        Module.finrank (IntermediateField.adjoin k {x}) L)
variable {L} in
def coneEval {σ : Type} (u : σ → L) : MvPolynomial σ k →+* (Polynomial L) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
    (fun i => Polynomial.C (u i) * Polynomial.X)
variable {L} in
def coneIdeal {σ : Type} (u : σ → L) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (coneEval k u)
variable {L} in
def ratios {σ : Type} (u : σ → L) (i₀ : σ) (i : σ) : L := u i / u i₀
variable {L} in
def ratioField {σ : Type} (u : σ → L) (i₀ : σ) : IntermediateField k L :=
  IntermediateField.adjoin k (Set.range (ratios u i₀))
variable {L} in
def coefficientTuple {F : Type} [Field F] {N : ℕ} (j : F →+* L) (f : (Polynomial F))
    (i : Fin N) : L := j (f.coeff i.val)
variable {L} in
def jetTuple {F : Type} [Field F] {n : ℕ} (j : F →+* L) (a : L) (f : (Polynomial F))
    (i : Fin n) : L := (Polynomial.hasseDeriv i.val f).eval₂ j a
structure FreshCurve (R : CoeffIdeal) where
  Old : Type
  Fresh : Type
  [oldField : Field Old]
  [freshField : Field Fresh]
  [oldAlgebra : Algebra Geom Old]
  [freshAlgebra : Algebra GeoField Fresh]
  oldCurve : CurveField Geom Old
  freshCurve : CurveField GeoField Fresh
  includeOld : Old →+* Fresh
  constants : includeOld.comp (algebraMap Geom Old) =
    (algebraMap GeoField Fresh).comp geomConstants
  independent : Function.Injective
    (Polynomial.eval₂RingHom includeOld (algebraMap GeoField Fresh genericArgument))
  polynomial : (Polynomial Old)
  monic : polynomial.Monic
  degree_le : polynomial.natDegree ≤ 133671
  equation : extendIdeal R =
    coneIdeal GeoField (coefficientTuple (N := taylorLength) includeOld polynomial)
  generates : IntermediateField.adjoin GeoField
    (Set.range (coefficientTuple (N := taylorLength) includeOld polynomial)) = ⊤
  nonconstant : ∃ i : Fin taylorLength,
    Transcendental GeoField (coefficientTuple includeOld polynomial i)
attribute [instance] FreshCurve.oldField FreshCurve.freshField
  FreshCurve.oldAlgebra FreshCurve.freshAlgebra
variable {L} in
def FreshCurve.center {R : CoeffIdeal} (D : FreshCurve R) : D.Fresh :=
  algebraMap GeoField D.Fresh genericArgument
variable {L} in
def FreshCurve.coefficients {R : CoeffIdeal} (D : FreshCurve R) :
    Fin taylorLength → D.Fresh :=
  coefficientTuple D.includeOld D.polynomial
variable {L} in
def FreshCurve.jets {R : CoeffIdeal} (D : FreshCurve R) {n : ℕ} :
    Fin n → D.Fresh :=
  jetTuple D.includeOld D.center D.polynomial
variable {L} in
def FreshGauss {F : Type} [Field F] (j : F →+* L) (a : L)
    (v : Valuation L ℤᵐ⁰) : Prop :=
  (∀ x : F, x ≠ 0 → v (j x) = 1) ∨
  (∀ g : (Polynomial F), v (g.eval₂ j a) = g.support.sup (fun i => v (j (g.coeff i))))
structure JetFactors {F : Type} [Field F] (f : (Polynomial F)) where
  count : ℕ
  factor : Fin count → (Polynomial F)
  multiplicity : Fin count → ℕ
  monic : ∀ i, (factor i).Monic
  separable : ∀ i, (factor i).Separable
  coprime : ∀ i j, i ≠ j → IsCoprime (factor i) (factor j)
  positive : ∀ i, 0 < multiplicity i
  le_degree : ∀ i, multiplicity i ≤ f.natDegree
  first_scalar : ∀ i, (multiplicity i : F) ≠ 0
  second_scalar : ∀ i, 2 ≤ multiplicity i → ((multiplicity i).choose 2 : F) ≠ 0
  product_eq : f = ∏ i, factor i ^ multiplicity i
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial
private theorem cast_ne_zero_of_pos_lt {F : Type} [Field F] {p n : ℕ} [CharP F p]
    (hpos : 0 < n) (hlt : n < p) : (n : F) ≠ 0 := by
  intro h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p n).mp h))
private theorem separable_of_small_degree {F : Type} [Field F] {p : ℕ} [CharP F p]
    {q : (Polynomial F)} (hirr : Irreducible q) (hdeg : q.natDegree < p) : q.Separable := by
  apply (Polynomial.separable_iff_derivative_ne_zero hirr).mpr
  have hstep : q.natDegree - 1 + 1 = q.natDegree := by have := hirr.natDegree_pos; omega
  intro hz
  have hc := congrArg (fun x : (Polynomial F) => x.coeff (q.natDegree - 1)) hz
  rw [coeff_derivative, ← Nat.cast_succ, hstep, coeff_natDegree, coeff_zero] at hc
  apply mul_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero)
    (cast_ne_zero_of_pos_lt hirr.natDegree_pos hdeg)
  simpa only [Nat.succ_eq_add_one, hstep] using hc
def factorsOfMonic {F : Type} [Field F] {p : ℕ} [CharP F p] {f : (Polynomial F)}
    (hf : f.Monic) (hdeg : f.natDegree < p) (htwo : 2 < p) : JetFactors f := by
  classical
  let S := (normalizedFactors f).toFinset
  let e := (Fintype.equivFin S).symm
  let q := fun i => (e i).val
  let m := fun i => (normalizedFactors f).count (q i)
  have hmem (i : Fin (Fintype.card S)) : q i ∈ normalizedFactors f :=
    Multiset.mem_toFinset.mp (e i).property
  have hdata (i : Fin (Fintype.card S)) :
      Irreducible (q i) ∧ (q i).Monic ∧ q i ∣ f :=
    (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp (hmem i)
  have hprod : (∏ i, q i ^ m i) = f := calc
    _ = ∏ x : S, x.val ^ (normalizedFactors f).count x.val :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = (normalizedFactors f).prod := by
      exact (Finset.prod_coe_sort S (fun x => x ^ (normalizedFactors f).count x)).trans
        (Finset.prod_multiset_count _).symm
    _ = f := by
      simpa only [hf.leadingCoeff, Polynomial.C_1, one_mul]
        using Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  have hsum : f.natDegree = ∑ i, m i * (q i).natDegree := by
    rw [← hprod, Polynomial.natDegree_prod_of_monic Finset.univ (fun i => q i ^ m i)
      (fun i _ => (hdata i).2.1.pow _)]
    exact Finset.sum_congr rfl fun i _ => (hdata i).2.1.natDegree_pow _
  have hm_pos (i : Fin (Fintype.card S)) : 0 < m i := Multiset.count_pos.mpr (hmem i)
  have hm_le (i : Fin (Fintype.card S)) : m i ≤ f.natDegree := calc
    m i = m i * 1 := (Nat.mul_one _).symm
    _ ≤ m i * (q i).natDegree := Nat.mul_le_mul_left _ (hdata i).1.natDegree_pos
    _ ≤ f.natDegree := by
      rw [hsum]
      exact Finset.single_le_sum (f := fun j => m j * (q j).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hm_cast (i : Fin (Fintype.card S)) : (m i : F) ≠ 0 :=
    cast_ne_zero_of_pos_lt (hm_pos i) ((hm_le i).trans_lt hdeg)
  refine ⟨_, q, m, fun i => (hdata i).2.1, ?_, ?_, hm_pos, hm_le, hm_cast, ?_, hprod.symm⟩
  · intro i
    exact separable_of_small_degree (hdata i).1
      ((natDegree_le_of_dvd (hdata i).2.2 hf.ne_zero).trans_lt hdeg)
  · intro i j hij
    apply (hdata i).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have heq := eq_of_monic_of_associated (hdata i).2.1 (hdata j).2.1
      ((hdata i).1.associated_of_dvd (hdata j).1 hdiv)
    exact hij (e.injective (Subtype.ext heq))
  · intro i hi
    have : NeZero (2 : F) := ⟨by
      exact_mod_cast (cast_ne_zero_of_pos_lt (F := F) (by decide : 0 < 2) htwo)⟩
    have hm₁ : ((m i - 1 : ℕ) : F) ≠ 0 :=
      cast_ne_zero_of_pos_lt (by omega) ((Nat.sub_le _ _).trans_lt ((hm_le i).trans_lt hdeg))
    have hm₁' : (m i : F) - 1 ≠ 0 := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ m i), Nat.cast_one] using hm₁
    rw [Nat.cast_choose_two]
    exact div_ne_zero (mul_ne_zero (hm_cast i) hm₁') (NeZero.ne _)
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace K1_13_6_3_5_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ R : CoeffIdeal, R.IsPrime → (extendIdeal R).IsPrime →
    R.IsHomogeneous (homogeneousSubmodule (Fin taylorLength) Geom) →
    dimension R = 2 → Nonempty (FreshCurve R)
def c2 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L],
    CurveField k L → PrincipalDivisors k L
def c3 : Prop :=
  ∀ (k L σ : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] [Fintype σ],
    CurveField k L → PrincipalDivisors k L →
    ∀ (u : σ → L) (i : σ), u i ≠ 0 →
      ((∃ j, Transcendental k (ratios u i j)) ↔ 0 < tupleHeight k L (ratios u i)) ∧
      (0 < tupleHeight k L (ratios u i) →
        dimension (coneIdeal k u) = 2 ∧
        (tupleHeight k L (ratios u i) : ℚ) =
          (Module.finrank (ratioField k u i) L : ℚ) * affineDegree (coneIdeal k u))
def c4 : Prop :=
  ∀ (k L σ τ : Type) [Field k] [Field L] [Algebra k L],
    ∀ (u : σ → L) (i : σ) (v : τ → L) (j : τ)
      (φ : MvPolynomial τ k →+* MvPolynomial σ k),
      u i ≠ 0 → v j ≠ 0 → ratioField k u i = ⊤ →
      (coneEval k u).comp φ = coneEval k v →
      residueDegree φ (coneIdeal k u) = Module.finrank (ratioField k v j) L
def c5 : Prop :=
  ∀ (R : CoeffIdeal) (D : FreshCurve R) (v : CurvePlace GeoField D.Fresh),
    FreshGauss D.includeOld D.center v.value
def c6 : Prop :=
  ∀ (F L : Type) [Field F] [Field L]
    (j : F →+* L) (a : L) (f : (Polynomial F)) (B : JetFactors f)
    (v : Valuation L ℤᵐ⁰) (N : ℕ),
    f.natDegree < N → v a = 1 →
    Function.Injective (Polynomial.eval₂RingHom j a) →
    FreshGauss j a v →
      tuplePole v (coefficientTuple (N := N) j f) =
        ∑ r, B.multiplicity r * poleOrder v ((B.factor r).eval₂ j a) ∧
      tuplePole v (ratios (jetTuple (n := 3) j a f) 0) =
        ∑ r, min (B.multiplicity r) 2 * zeroOrder v ((B.factor r).eval₂ j a)
private theorem hasFiniteSupport_tuplePole {k L σ : Type}
    [Field k] [Field L] [Algebra k L] [Fintype σ]
    (h : PrincipalDivisors k L) (u : σ → L) :
    (fun v : CurvePlace k L => tuplePole v.value u).HasFiniteSupport := by
  have hf : (⋃ i : σ, Function.support (fun v : CurvePlace k L =>
      poleOrder v.value (u i))).Finite := Set.finite_iUnion fun i => (h (u i)).1
  apply hf.subset
  intro v hv
  simp only [Set.mem_iUnion, Function.mem_support] at hv ⊢
  by_contra! hz
  exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun i _ => hz i)
theorem tupleHeight_le_of_inclusion {k L σ τ : Type}
    [Field k] [Field L] [Algebra k L] [Fintype σ] [Fintype τ]
    (h : PrincipalDivisors k L) (u : σ → L) (w : τ → L) (e : σ → τ)
    (he : ∀ i, u i = w (e i)) :
    tupleHeight k L u ≤ tupleHeight k L w := by
  apply finsum_le_finsum (hasFiniteSupport_tuplePole h u) (hasFiniteSupport_tuplePole h w)
  intro v
  unfold tuplePole
  apply Finset.sup_le
  intro i _
  rw [he i]
  exact Finset.le_sup (s := Finset.univ) (f := fun j => poleOrder v.value (w j))
    (Finset.mem_univ (e i))
theorem finsum_weighted {α σ : Type} [Fintype σ] (c : σ → ℕ) (f : σ → α → ℕ)
    (hf : ∀ i, (f i).HasFiniteSupport) :
    (∑ᶠ v, ∑ i, c i * f i v) = ∑ i, c i * ∑ᶠ v, f i v := by
  classical
  let s : Set α := ⋃ i, Function.support (f i)
  have hs : s.Finite := Set.finite_iUnion hf
  have hi (i : σ) : Function.support (f i) ⊆ (hs.toFinset : Set α) := by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun j => Function.support (f j)) i
  have ha : Function.support (fun v => ∑ i, c i * f i v) ⊆ (hs.toFinset : Set α) := by
    intro v hv
    by_contra h
    exact hv (Finset.sum_eq_zero fun i _ => by
      have hz : f i v = 0 := by
        by_contra hn
        exact h (hi i hn)
      simp [hz])
  rw [finsum_eq_finsetSum_of_support_subset _ ha, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [finsum_eq_finsetSum_of_support_subset _ (hi i), Finset.mul_sum]
private theorem jet_eval_sum {F L : Type} [Field F] [Field L]
    (j : F →+* L) (a : L) (f : (Polynomial F)) {N : ℕ} (hn : f.natDegree < N) (i : ℕ) :
    (Polynomial.hasseDeriv i f).eval₂ j a =
      ∑ x : Fin N, ((x.val.choose i : L) * a ^ (x.val - i)) * j (f.coeff x.val) := by
  rw [Polynomial.hasseDeriv_apply, f.sum_over_range' (fun _ => by simp) _ hn,
    Polynomial.eval₂_finsetSum, Fin.sum_univ_eq_sum_range (fun x =>
      ((x.choose i : L) * a ^ (x - i)) * j (f.coeff x))]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Polynomial.eval₂_monomial, map_mul, map_natCast]
  ring
private theorem cone_eval_hasse {k F L : Type} [Field k] [Field F] [Field L] [Algebra k L]
    (j : F →+* L) (a : k) (f : (Polynomial F)) {N n : ℕ} (hdeg : f.natDegree < N) :
    (coneEval k (coefficientTuple (N := N) j f)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin n =>
        ∑ r : Fin N, MvPolynomial.C ((r.val.choose i.val : k) * a ^ (r.val - i.val)) *
          MvPolynomial.X r)) =
      coneEval k (jetTuple (n := n) j (algebraMap k L a) f) := by
  let u : Fin N → L := coefficientTuple j f
  let v : Fin n → L := jetTuple j (algebraMap k L a) f
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coneEval]
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
    have he (r : Fin N) :
        (coneEval k u)
          (MvPolynomial.C ((r.val.choose i.val : k) * a ^ (r.val - i.val)) *
            MvPolynomial.X r) =
          Polynomial.C (((r.val.choose i.val : L) * (algebraMap k L a) ^ (r.val - i.val)) *
            u r) * Polynomial.X := by
      simp [coneEval, mul_assoc]
    rw [show (coneEval k v) (MvPolynomial.X i) =
      Polynomial.C (v i) * Polynomial.X from MvPolynomial.eval₂Hom_X' _ _ _]
    rw [show v i =
      ∑ r : Fin N, ((r.val.choose i.val : L) * (algebraMap k L a) ^ (r.val - i.val)) *
        u r from jet_eval_sum j _ f hdeg i.val]
    rw [map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => he r
theorem cone_eval_jets {R : CoeffIdeal} (D : FreshCurve R) :
    (coneEval GeoField D.coefficients).comp freshJetMap = coneEval GeoField (D.jets (n := 4)) :=
  cone_eval_hasse D.includeOld genericArgument D.polynomial (Nat.lt_succ_iff.mpr D.degree_le)
theorem jet_zero_nonzero {R : CoeffIdeal} (D : FreshCurve R) {n : ℕ} (i : Fin n)
    (hi : i.val = 0) : D.jets i ≠ 0 := by
  unfold FreshCurve.jets jetTuple
  rw [hi, Polynomial.hasseDeriv_zero']
  change (Polynomial.eval₂RingHom D.includeOld D.center) D.polynomial ≠ 0
  exact fun h => D.monic.ne_zero (D.independent (h.trans (map_zero _).symm))
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_2
open K1_13_6_3_5_3
variable (k L : Type) [Field k] [Field L] [Algebra k L]
abbrev ParameterRing (x : L) := Algebra.adjoin k ({x} : Set L)
abbrev Normalization (x : L) := integralClosure (ParameterRing k L x) L
def origin (x : L) : Ideal (ParameterRing k L x) :=
  Ideal.span {⟨x, Algebra.self_mem_adjoin_singleton k x⟩}
abbrev ZeroPlaces (x : L) :=
  {v : CurvePlace k L // zeroOrder v.value x ≠ 0}
end K1_13_6_3_5_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_2
noncomputable section
open K1_13_6_3_5_3 IntermediateField
open scoped WithZero Polynomial algebraAdjoinAdjoin nonZeroDivisors
def c1 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (x : L), Transcendental k x → Module.Finite (IntermediateField.adjoin k {x}) L →
      Module.Finite (ParameterRing k L x) (Normalization k L x)
def c2 : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L),
    Transcendental k x → IsDedekindDomain (Normalization k L x) →
    IsFractionRing (Normalization k L x) L →
    ∃ e : ZeroPlaces k L x ≃ (origin k L x).primesOver (Normalization k L x),
      ∀ v, zeroOrder v.val.value x = (e v).val.ramificationIdx (ParameterRing k L x)
variable {k L : Type} [Field k] [Field L] [Algebra k L]
private theorem finite_parameter (h : CurveField k L) {x : L}
    (hx : Transcendental k x) : Module.Finite (IntermediateField.adjoin k {x}) L := by
  obtain ⟨t, ht, hfin⟩ := h
  have ht' : IsAlgebraic (IntermediateField.adjoin k {x}) t :=
    isAlgebraic_adjoin_iff.mpr (.adjoin_singleton ht hx
      (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic x)))
  let Kxt := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t})
  let Ktx := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x})
  let : Algebra (IntermediateField.adjoin k {x}) Kxt :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t}).algebra
  let : Module (IntermediateField.adjoin k {x}) Kxt := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {x}) Kxt := Algebra.toSMul
  let : Algebra (IntermediateField.adjoin k {t}) Ktx :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x}).algebra
  let : Module (IntermediateField.adjoin k {t}) Ktx := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {t}) Ktx := Algebra.toSMul
  have : Module.Finite (IntermediateField.adjoin k {x}) Kxt :=
    IntermediateField.adjoin.finiteDimensional ht'.isIntegral
  have : Module.Finite Kxt L := by
    unfold Kxt
    rw [adjoin_simple_comm]
    have : IsScalarTower (IntermediateField.adjoin k {t}) Ktx L := isScalarTower_mid' _
    exact .right (IntermediateField.adjoin k {t}) Ktx L
  have : IsScalarTower (IntermediateField.adjoin k {x}) Kxt L := isScalarTower_mid' _
  exact Module.Finite.trans Kxt L
theorem parameterRing_pid {x : L} (hx : Transcendental k x) :
    IsPrincipalIdealRing (ParameterRing k L x) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k x hx).toRingHom
    (Polynomial.algEquivOfTranscendental k x hx).surjective
private def originEquiv {x : L} (hx : Transcendental k x) :
    (ParameterRing k L x ⧸ origin k L x) ≃ₐ[k] k := by
  let e := Polynomial.algEquivOfTranscendental k x hx
  refine (Ideal.quotientEquivAlg (Ideal.span {Polynomial.X}) (origin k L x) e ?_).symm.trans ?_
  · rw [Ideal.map_span, Set.image_singleton]
    unfold origin
    change Ideal.span {⟨x, Algebra.self_mem_adjoin_singleton k x⟩} = Ideal.span {e Polynomial.X}
    simp only [e, Polynomial.algEquivOfTranscendental_apply_X]
  · rw [show (Ideal.span {Polynomial.X} : Ideal (Polynomial k)) =
        Ideal.span {Polynomial.X - Polynomial.C (0 : k)} by rw [map_zero, sub_zero]]
    exact Polynomial.quotientSpanXSubCAlgEquiv (0 : k)
theorem origin_isMaximal {x : L} (hx : Transcendental k x) :
    (origin k L x).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ ((originEquiv hx).toRingEquiv.isField (Field.toIsField k))
private theorem normalization_dedekind {x : L} (hx : Transcendental k x)
    [Module.Finite (IntermediateField.adjoin k {x}) L]
    [Module.Finite (ParameterRing k L x) (Normalization k L x)] :
    IsDedekindDomain (Normalization k L x) := by
  let A := ParameterRing k L x
  let B := Normalization k L x
  let K := IntermediateField.adjoin k {x}
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : IsNoetherianRing B :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower A (show IsNoetherian A B from inferInstance))
  exact
    { (inferInstance : IsNoetherianRing B),
      Ring.DimensionLEOne.of_isIntegral A B,
      integralClosure.isIntegrallyClosedOfFiniteExtension K with }
private theorem sum_origin_indices [IsAlgClosed k] {x : L} (hx : Transcendental k x)
    [Module.Finite (IntermediateField.adjoin k {x}) L]
    [Module.Finite (ParameterRing k L x) (Normalization k L x)] :
    (∑ᶠ P : (origin k L x).primesOver (Normalization k L x),
      P.val.ramificationIdx (ParameterRing k L x)) =
      Module.finrank (IntermediateField.adjoin k {x}) L := by
  classical
  let A := ParameterRing k L x
  let B := Normalization k L x
  let K := IntermediateField.adjoin k {x}
  let p := origin k L x
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : IsDedekindDomain B := normalization_dedekind hx
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : p.IsMaximal := origin_isMaximal hx
  have : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  have : Module.Free A B := by infer_instance
  have hdeg (P : p.primesOver B) : P.val.inertiaDeg A = 1 := by
    have : P.val.IsPrime := P.property.1
    have : P.val.LiesOver p := P.property.2
    have : P.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.val p
    have hp : Function.Surjective (algebraMap k (A ⧸ p)) := by
      intro y
      let e := originEquiv hx
      exact ⟨e y, by rw [← e.symm.commutes, Algebra.algebraMap_self_apply, e.symm_apply_apply]⟩
    have : Algebra.IsIntegral k (A ⧸ p) :=
      ⟨fun y => by obtain ⟨z, rfl⟩ := hp y; exact isIntegral_algebraMap⟩
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    have : Algebra.IsIntegral k (B ⧸ P.val) := .trans (A ⧸ p)
    have hsurj : Function.Surjective (algebraMap (A ⧸ p) (B ⧸ P.val)) := by
      intro y
      obtain ⟨z, hz⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := k) (K := B ⧸ P.val)).surjective y
      exact ⟨algebraMap k (A ⧸ p) z, (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hz⟩
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P.val, Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨RingHom.injective _, hsurj⟩
  have hrank : Module.finrank A B = Module.finrank K L := by
    have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
      IsIntegralClosure.isLocalization A K L B
    let b := Module.Basis.localizationLocalization K (nonZeroDivisors A) L (Module.Free.chooseBasis A B)
    rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]
  change (∑ᶠ P : p.primesOver B, P.val.ramificationIdx A) = Module.finrank K L
  rw [finsum_eq_sum_of_fintype, ← hrank, ← Ideal.sum_ramification_inertia_eq_finrank p B]
  exact Finset.sum_congr rfl fun P _ => by rw [hdeg, mul_one]
private theorem zero_sum [IsAlgClosed k] (h1 : c1) (h2 : c2) (h : CurveField k L)
    {x : L} (hx : Transcendental k x) :
    (fun v : CurvePlace k L => zeroOrder v.value x).HasFiniteSupport ∧
      (∑ᶠ v : CurvePlace k L, zeroOrder v.value x) =
        Module.finrank (IntermediateField.adjoin k {x}) L := by
  classical
  have : Module.Finite (IntermediateField.adjoin k {x}) L := finite_parameter h hx
  have : Module.Finite (ParameterRing k L x) (Normalization k L x) := h1 k L x hx inferInstance
  have : IsDedekindDomain (Normalization k L x) := normalization_dedekind hx
  have : IsFractionRing (Normalization k L x) L :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin k {x}) L
  have : (origin k L x).IsMaximal := origin_isMaximal hx
  obtain ⟨e, he⟩ := h2 k L x hx inferInstance inferInstance
  have : Fintype (ZeroPlaces k L x) := Fintype.ofEquiv _ e.symm
  let f := fun v : CurvePlace k L => zeroOrder v.value x
  have hf : Finite (Function.support f) := by
    change Finite (ZeroPlaces k L x)
    infer_instance
  refine ⟨Set.finite_coe_iff.mp hf, ?_⟩
  change finsum f = _
  calc
    finsum f = ∑ᶠ v : ZeroPlaces k L x, f v.val := by
      change finsum f = ∑ᶠ v : Function.support f, f v.val
      rw [finsum_set_coe_eq_finsum_mem (f := f), finsum_mem_support]
    _ = ∑ᶠ P : (origin k L x).primesOver (Normalization k L x),
          P.val.ramificationIdx (ParameterRing k L x) :=
      finsum_eq_of_bijective e e.bijective he
    _ = _ := sum_origin_indices hx
private theorem adjoin_inv (x : L) :
    IntermediateField.adjoin k ({x⁻¹} : Set L) = IntermediateField.adjoin k {x} := by
  apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
  · apply Set.singleton_subset_iff.mpr
    change x ∈ IntermediateField.adjoin k ({x⁻¹} : Set L)
    simpa only [inv_inv] using
      (IntermediateField.adjoin k ({x⁻¹} : Set L)).inv_mem (mem_adjoin_simple_self k x⁻¹)
private theorem zeroOrder_inv (v : Valuation L ℤᵐ⁰) (x : L) :
    zeroOrder v x⁻¹ = poleOrder v x := by
  simp [zeroOrder, poleOrder, map_inv₀, WithZero.log_inv]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_3_5_3.c2 := by
  intro k L _ _ _ _ h x
  by_cases hx : Transcendental k x
  · have hxi : Transcendental k x⁻¹ := fun hi => hx (IsAlgebraic.inv_iff.mp hi)
    obtain ⟨hz, hsz⟩ := zero_sum h1 h2 h hx
    obtain ⟨hp, hsp⟩ := zero_sum h1 h2 h hxi
    simp_rw [zeroOrder_inv] at hp hsp
    rw [adjoin_inv] at hsp
    exact ⟨hp, hz, hsp.trans hsz.symm, fun _ => hsp⟩
  · have ha : IsAlgebraic k x := not_not.mp hx
    have : Algebra.IsAlgebraic k (IntermediateField.adjoin k {x}) :=
      IntermediateField.isAlgebraic_adjoin_simple ha.isIntegral
    have : Algebra.IsIntegral k (IntermediateField.adjoin k {x}) := inferInstance
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := k) (K := IntermediateField.adjoin k {x})).surjective (AdjoinSimple.gen k x)
    have hcx : algebraMap k L c = x :=
      congrArg (algebraMap (IntermediateField.adjoin k {x}) L) hc
    have hzero (v : CurvePlace k L) : v.value x = 0 ∨ v.value x = 1 := by
      rw [← hcx]
      by_cases h0 : c = 0
      · simp [h0]
      · exact Or.inr (v.on_constants c h0)
    have hp : (fun v : CurvePlace k L => poleOrder v.value x) = 0 := by
      funext v
      rcases hzero v with hv | hv <;> simp [poleOrder, hv]
    have hz : (fun v : CurvePlace k L => zeroOrder v.value x) = 0 := by
      funext v
      rcases hzero v with hv | hv <;> simp [zeroOrder, hv]
    simp [hp, hz, Function.HasFiniteSupport, hx]
end
end K1_13_6_3_5_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial
variable {k σ : Type*} [Field k]
def closureMap (A : Ideal (MvPolynomial σ k)) :
    MvPolynomial (Option σ) k →ₐ[k] Polynomial (MvPolynomial σ k ⧸ A) :=
  aeval fun i => Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) * Polynomial.X
def closureIdeal (A : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial (Option σ) k) :=
  RingHom.ker (closureMap A).toRingHom
def atInfinity : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => i.elim 0 MvPolynomial.X
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
theorem closureIdeal_prime (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) :
    (closureIdeal A).IsPrime := by
  let _ : A.IsPrime := hA
  exact RingHom.ker_isPrime (closureMap A).toRingHom
theorem not_mem_closureIdeal (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) :
    MvPolynomial.X none ∉ closureIdeal A := by
  let _ : A.IsPrime := hA
  change closureMap A (MvPolynomial.X none) ≠ 0
  simp [closureMap]
theorem coeff_closureMap (A : Ideal (MvPolynomial σ k))
    (f : MvPolynomial (Option σ) k) (n : ℕ) :
    (closureMap A f).coeff n =
      Ideal.Quotient.mk A ((aeval fun i : Option σ => i.elim 1 MvPolynomial.X)
        (homogeneousComponent n f)) := by
  let e : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
    aeval fun i => i.elim 1 MvPolynomial.X
  change (closureMap A f).coeff n = Ideal.Quotient.mk A (e (homogeneousComponent n f))
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp [map_add, Polynomial.coeff_add, hf, hg]
  | monomial d r =>
    have hm : closureMap A (monomial d r) =
        Polynomial.C (Ideal.Quotient.mk A (e (monomial d r))) *
          Polynomial.X ^ d.degree := by
      classical
      simp only [closureMap, e, aeval_monomial, Polynomial.algebraMap_apply,
        Finsupp.prod, Finsupp.degree_apply]
      simp only [Ideal.Quotient.mk_algebraMap, map_mul, map_prod, map_pow]
      have hprod :
          (∏ i ∈ d.support,
            (Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) * Polynomial.X) ^ d i) =
          ∏ i ∈ d.support,
            Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) ^ d i *
              Polynomial.X ^ d i := by
        exact Finset.prod_congr rfl fun i _ =>
          mul_pow (Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)))
            (Polynomial.X : Polynomial (MvPolynomial σ k ⧸ A)) (d i)
      rw [hprod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ac_rfl
    rw [hm, Polynomial.coeff_C_mul_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    split_ifs <;> simp_all
theorem decompose_apply (f : MvPolynomial σ k) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ k) f n : MvPolynomial σ k) =
      homogeneousComponent n f := by
  simpa only [DirectSum.Decomposition.decompose'_eq] using decomposition.decompose'_apply f n
theorem closureIdeal_homogeneous (A : Ideal (MvPolynomial σ k)) :
    (closureIdeal A).IsHomogeneous (homogeneousSubmodule (Option σ) k) := by
  intro n f hf
  rw [decompose_apply]
  change closureMap A f = 0 at hf
  change closureMap A (homogeneousComponent n f) = 0
  ext m
  rw [coeff_closureMap, homogeneousComponent_of_mem (homogeneousComponent_mem n f)]
  split_ifs with hmn
  · subst m
    rw [← coeff_closureMap, hf, Polynomial.coeff_zero]
  · simp
private theorem atInfinity_rename (f : MvPolynomial σ k) :
    atInfinity (rename some f) = f := by
  have h : (atInfinity (k := k) (σ := σ)).comp (rename some) = AlgHom.id k _ := by
    ext i
    simp [atInfinity]
  exact DFunLike.congr_fun h f
theorem atInfinity_surjective :
    Function.Surjective (atInfinity (k := k) (σ := σ)) :=
  fun f => ⟨rename some f, atInfinity_rename f⟩
theorem atInfinity_eq_coeff_zero (f : MvPolynomial (Option σ) k) :
    atInfinity f = (optionEquivLeft k σ f).coeff 0 := by
  let e : Polynomial (MvPolynomial σ k) →ₐ[k] MvPolynomial σ k :=
    (Polynomial.aeval 0).restrictScalars k
  have h : (atInfinity (k := k) (σ := σ)) = e.comp (optionEquivLeft k σ).toAlgHom := by
    ext i
    cases i <;> simp [e, atInfinity, optionEquivLeft_X_none, optionEquivLeft_X_some]
  rw [h]
  change Polynomial.aeval (0 : MvPolynomial σ k) (optionEquivLeft k σ f) = _
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coeff_zero_eq_eval_zero]
theorem hilbertFunction_comap_atInfinity [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction (I.comap (atInfinity (k := k) (σ := σ))) n =
      affineHilbertFunction I n := by
  let q := Ideal.quotientMapₐ I (atInfinity (k := k) (σ := σ)) le_rfl
  let g : quotientDegreeLE (I.comap (atInfinity (k := k) (σ := σ))) n →ₗ[k]
      quotientDegreeLE I n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun x => by
      obtain ⟨f, hf, hfx⟩ := mem_quotientDegreeLE.mp x.property
      change q x.val ∈ _
      rw [← hfx]
      refine mk_mem_quotientDegreeLE (p := atInfinity f) ?_
      rw [atInfinity_eq_coeff_zero]
      exact (totalDegree_coeff_optionEquivLeft_le k σ f 0).trans hf
  have he : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨f, hf, hfy⟩ := mem_quotientDegreeLE.mp y.property
      refine ⟨⟨Ideal.Quotient.mk _ (rename some f),
        mk_mem_quotientDegreeLE ((totalDegree_rename_le some f).trans hf)⟩,
        Subtype.ext ?_⟩
      change Ideal.Quotient.mk I (atInfinity (rename some f)) = y.val
      rw [atInfinity_rename, hfy]
  exact (LinearEquiv.ofBijective g he).finrank_eq
theorem hilbertPolynomial_comap_atInfinity [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (I.comap (atInfinity (k := k) (σ := σ))) =
      affineHilbertPolynomial I := by
  symm
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  exact eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
    (fun n hn => by rw [hN n hn, hilbertFunction_comap_atInfinity])
theorem boundaryIdeal_homogeneous (A : Ideal (MvPolynomial σ k)) :
    (boundaryIdeal A).IsHomogeneous (homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨f, _, rfl⟩
  exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
theorem minimalPrime_homogeneous {I P : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hP : I.IsMinimalPrime P) :
    P.IsHomogeneous (homogeneousSubmodule σ k) := by
  let Q := (P.homogeneousCore (homogeneousSubmodule σ k)).toIdeal
  have hQP : Q ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  have hIQ : I ≤ Q :=
    (Ideal.homogeneousCore.gc (𝒜 := homogeneousSubmodule σ k) ⟨I, hI⟩ P).mp hP.le
  have he : Q = P := le_antisymm hQP (hP.2 ⟨hP.isPrime.homogeneousCore, hIQ⟩ hQP)
  exact he ▸ (P.homogeneousCore (homogeneousSubmodule σ k)).isHomogeneous
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
def linearValue (a : σ → k) (r : σ → L) : L :=
  ∑ j, a j • r j
def lineProjection (i : σ) (a : σ → k) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval ![MvPolynomial.X i, ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j]
def ChartIntegral (r : σ → L) (z : L) : Prop :=
  (∀ j, IsIntegral (Algebra.adjoin k {z}) (r j)) ∧
  (∀ j, IsIntegral (Algebra.adjoin k {z⁻¹}) (r j / z))
def onCoordinateRings (P : Ideal (MvPolynomial σ k))
    (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k) :
    (MvPolynomial (Fin 2) k ⧸ P.comap φ.toRingHom) →ₐ[k] (MvPolynomial σ k ⧸ P) :=
  Ideal.quotientMapₐ P φ le_rfl
theorem adjoin_line_le_ratioField (u : σ → L) (i : σ) (a : σ → k) :
    IntermediateField.adjoin k {linearValue a (ratios u i)} ≤ ratioField k u i := by
  apply IntermediateField.adjoin_le_iff.2
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]
  exact (ratioField k u i).sum_mem fun j _ =>
    (ratioField k u i).smul_mem (IntermediateField.mem_adjoin_of_mem k (Set.mem_range_self j))
def projectiveDegree (u : σ → L) (i : σ) (a : σ → k) : ℕ :=
  letI := (IntermediateField.inclusion (adjoin_line_le_ratioField u i a)).toAlgebra
  Module.finrank (IntermediateField.adjoin k {linearValue a (ratios u i)})
    (ratioField k u i)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5_3
open scoped WithZero
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
theorem finite_of_transcendental (h : CurveField k L) {z : L} (hz : Transcendental k z) :
    Module.Finite (IntermediateField.adjoin k {z}) L := by
  obtain ⟨t, ht, hfin⟩ := h
  let E := IntermediateField.adjoin k {t}
  let e : RatFunc k ≃ₐ[k] E := RatFunc.algEquivOfTranscendental t ht
  let g : RatFunc k →ₐ[k] L := E.val.comp e.toAlgHom
  let : Algebra (RatFunc k) L := g.toRingHom.toAlgebra
  have : IsScalarTower k (RatFunc k) L := IsScalarTower.of_algebraMap_eq
    fun x => (g.commutes x).symm
  have : Module.Finite E L := hfin
  have : FunctionField k L :=
    ((Module.finBasis E L).mapCoeffs e.symm fun c x => by
      rw [Algebra.smul_def, Algebra.smul_def]
      change (e (e.symm c) : L) * x = (c : L) * x
      rw [e.apply_symm_apply]).finiteDimensional_of_finite
  exact FunctionField.finiteDimensional_of_adjoin_transcendental hz
theorem finiteSupport_tuplePole (h : PrincipalDivisors k L) (r : σ → L) :
    (fun v : CurvePlace k L => tuplePole v.value r).HasFiniteSupport := by
  have hf : (⋃ j : σ, Function.support (fun v : CurvePlace k L =>
      poleOrder v.value (r j))).Finite := Set.finite_iUnion fun j => (h (r j)).1
  apply hf.subset
  intro v hv
  simp only [Set.mem_iUnion, Function.mem_support] at hv ⊢
  by_contra! hz
  exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun j _ => hz j)
theorem poleOrder_eq_zero_iff (v : Valuation L ℤᵐ⁰) (x : L) :
    poleOrder v x = 0 ↔ v x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, poleOrder]
  have hv := (v.ne_zero_iff).2 hx
  rw [poleOrder, Int.toNat_eq_zero]
  simpa only [WithZero.exp_zero] using (WithZero.log_le_iff_le_exp (a := 0) hv)
private theorem poleOrder_mono_value (v : Valuation L ℤᵐ⁰) {x y : L} (h : v x ≤ v y) :
    poleOrder v x ≤ poleOrder v y := by
  by_cases hx : x = 0
  · simp [poleOrder, hx]
  have hvx := (v.ne_zero_iff).2 hx
  have hvy : v y ≠ 0 := ne_of_gt ((zero_lt_iff.mpr hvx).trans_le h)
  exact Int.toNat_le_toNat ((WithZero.log_le_log hvx hvy).2 h)
private theorem poleOrder_constant (v : CurvePlace k L) (c : k) :
    poleOrder v.value (algebraMap k L c) = 0 := by
  apply (poleOrder_eq_zero_iff _ _).2
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.on_constants c hc).le
private theorem exists_constant [IsAlgClosed k] {x : L} (hx : ¬ Transcendental k x) :
    ∃ c : k, algebraMap k L c = x := by
  have halg : IsAlgebraic k x := not_not.mp hx
  have := IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have he := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
    (IntermediateField.adjoin k {x})
  exact IntermediateField.mem_bot.mp (he ▸ IntermediateField.mem_adjoin_simple_self k x)
theorem transcendental_of_pole_sum_pos [IsAlgClosed k] {z : L}
    (hp : 0 < ∑ᶠ v : CurvePlace k L, poleOrder v.value z) : Transcendental k z := by
  by_contra hc
  obtain ⟨c, rfl⟩ := exists_constant hc
  simp [poleOrder_constant] at hp
theorem height_pos_iff [IsAlgClosed k] (hf : CurveField k L) (h : PrincipalDivisors k L)
    (r : σ → L) : (∃ j, Transcendental k (r j)) ↔ 0 < tupleHeight k L r := by
  constructor
  · rintro ⟨j, hj⟩
    have := finite_of_transcendental hf hj
    have hle : (∑ᶠ v : CurvePlace k L, poleOrder v.value (r j)) ≤ tupleHeight k L r :=
      finsum_le_finsum (h (r j)).1 (finiteSupport_tuplePole h r) fun v =>
        Finset.le_sup (s := Finset.univ) (f := fun l => poleOrder v.value (r l))
          (Finset.mem_univ j)
    rw [(h (r j)).2.2.2 hj] at hle
    exact (Module.finrank_pos (R := IntermediateField.adjoin k {r j}) (M := L)).trans_le hle
  · intro hp
    by_contra! hn
    have hzero (v : CurvePlace k L) : tuplePole v.value r = 0 := by
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      obtain ⟨c, hc⟩ := exists_constant (hn j)
      rw [← hc]
      exact poleOrder_constant v c
    simp [tupleHeight, hzero] at hp
private def maxValue (v : CurvePlace k L) (r : σ → L) : ℤᵐ⁰ :=
  max 1 (Finset.univ.sup fun j => v.value (r j))
private theorem value_le_max (v : CurvePlace k L) (r : σ → L) (j : σ) :
    v.value (r j) ≤ maxValue v r :=
  (Finset.le_sup (s := Finset.univ) (f := fun j => v.value (r j))
    (Finset.mem_univ j)).trans (le_max_right _ _)
private theorem value_smul_le (v : CurvePlace k L) (c : k) (x : L) :
    v.value (c • x) ≤ v.value x := by
  by_cases hc : c = 0
  · simp [hc]
  rw [Algebra.smul_def, map_mul, v.on_constants c hc, one_mul]
private theorem linearValue_le_max (v : CurvePlace k L) (r : σ → L) (a : σ → k) :
    v.value (linearValue a r) ≤ maxValue v r := by
  apply v.value.map_sum_le
  intro j _
  exact (value_smul_le v (a j) (r j)).trans (value_le_max v r j)
private def cancellation (v : CurvePlace k L) (r : σ → L) : Submodule k (σ → k) where
  carrier := {a | v.value (linearValue a r) < maxValue v r}
  zero_mem' := by
    change v.value (linearValue (0 : σ → k) r) < maxValue v r
    rw [show linearValue (0 : σ → k) r = 0 by simp [linearValue], map_zero]
    exact zero_lt_one.trans_le (le_max_left _ _)
  add_mem' := by
    intro a b ha hb
    change v.value (linearValue (a + b) r) < maxValue v r
    have he : linearValue (a + b) r = linearValue a r + linearValue b r := by
      simp [linearValue, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [he]
    exact v.value.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    change v.value (linearValue (c • a) r) < maxValue v r
    have he : linearValue (c • a) r = c • linearValue a r := by
      simp [linearValue, Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]
    rw [he]
    exact (value_smul_le v c (linearValue a r)).trans_lt ha
theorem exists_linearValue_preserving [IsAlgClosed k] (h : PrincipalDivisors k L) (r : σ → L) :
    ∃ a : σ → k, (∀ v : CurvePlace k L,
      poleOrder v.value (linearValue a r) = tuplePole v.value r) ∧
      ∀ (v : CurvePlace k L) j, v.value (r j) ≤ max 1 (v.value (linearValue a r)) := by
  classical
  let s := (finiteSupport_tuplePole h r).toFinset
  have hs (v : CurvePlace k L) : v ∈ s ↔ tuplePole v.value r ≠ 0 := by
    exact (finiteSupport_tuplePole h r).mem_toFinset
  have hmax (v : CurvePlace k L) (hv : v ∈ s) :
      ∃ j, maxValue v r = v.value (r j) := by
    have hsup : 1 < Finset.univ.sup (fun j => v.value (r j)) := by
      by_contra! hl
      apply (hs v).mp hv
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      exact (poleOrder_eq_zero_iff _ _).2
        ((Finset.le_sup (s := Finset.univ) (f := fun j => v.value (r j))
          (Finset.mem_univ j)).trans hl)
    have hne : (Finset.univ : Finset σ).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sup_empty] at hsup
      exact (not_lt_of_ge zero_le) hsup
    obtain ⟨j, _, hj⟩ := Finset.sup_mem_of_nonempty (f := fun j => v.value (r j)) hne
    exact ⟨j, (max_eq_right hsup.le).trans hj.symm⟩
  have hproper (v : s) : cancellation v.val r ≠ ⊤ := by
    obtain ⟨j, hj⟩ := hmax v.val v.prop
    intro ht
    have hm : (Pi.single j (1 : k)) ∈ cancellation v.val r := by rw [ht]; trivial
    change v.val.value (linearValue (Pi.single j (1 : k)) r) < maxValue v.val r at hm
    simp [hj, linearValue] at hm
  have hcover : (⋃ v : s, (cancellation v.val r : Set (σ → k))) ≠ Set.univ := by
    intro he
    obtain ⟨v, hv⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ he
    exact hproper v hv
  obtain ⟨a, ha⟩ := Set.nonempty_compl.2 hcover
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at ha
  refine ⟨a, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ s
    · have hnot := ha ⟨v, hv⟩
      change ¬ v.value (linearValue a r) < maxValue v r at hnot
      have he := (linearValue_le_max v r a).antisymm (le_of_not_gt hnot)
      refine le_antisymm ?_ ?_
      · obtain ⟨j, hj⟩ := hmax v hv
        exact (poleOrder_mono_value _ (he.trans hj).le).trans
          (Finset.le_sup (s := Finset.univ) (f := fun j => poleOrder v.value (r j))
            (Finset.mem_univ j))
      · apply Finset.sup_le
        intro j _
        exact poleOrder_mono_value _ ((value_le_max v r j).trans he.ge)
    · have hz : tuplePole v.value r = 0 := by simpa only [hs, not_ne_iff] using hv
      have hle (j : σ) : v.value (r j) ≤ 1 :=
        (poleOrder_eq_zero_iff _ _).1 ((Finset.sup_eq_bot_iff _ _).1 hz _ (Finset.mem_univ j))
      rw [hz]
      apply (poleOrder_eq_zero_iff _ _).2
      exact v.value.map_sum_le fun j _ => (value_smul_le v (a j) (r j)).trans (hle j)
  · intro v j
    by_cases hv : v ∈ s
    · have hnot := ha ⟨v, hv⟩
      change ¬ v.value (linearValue a r) < maxValue v r at hnot
      exact (value_le_max v r j).trans ((le_of_not_gt hnot).trans (le_max_right _ _))
    · have hz : tuplePole v.value r = 0 := by simpa only [hs, not_ne_iff] using hv
      exact ((poleOrder_eq_zero_iff _ _).1
        ((Finset.sup_eq_bot_iff _ _).1 hz _ (Finset.mem_univ j))).trans (le_max_left _ _)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
theorem lineProjection_linear (i : σ) (a : σ → k) :
    IsLinearProjection (lineProjection i a) := by
  intro j
  rw [lineProjection, aeval_X]
  fin_cases j
  · exact isHomogeneous_X k i
  · apply IsHomogeneous.sum
    intro l _
    exact (isHomogeneous_C _ _).mul (isHomogeneous_X _ l)
omit [Fintype σ] in
private theorem coneEval_monomial (u : σ → L) (d : σ →₀ ℕ) (c : k) :
    coneEval k u (monomial d c) = Polynomial.monomial d.degree (aeval u (monomial d c)) := by
  rw [coneEval, coe_eval₂Hom, eval₂_monomial, aeval_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, Finsupp.degree_apply]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
omit [Fintype σ] in
theorem coneIdeal_homogeneous (u : σ → L) :
    (coneIdeal k u).IsHomogeneous (homogeneousSubmodule σ k) := by
  classical
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro n p hp
  change p ∈ RingHom.ker (coneEval k u) at hp
  change GradedRing.proj (homogeneousSubmodule σ k) n p ∈ RingHom.ker (coneEval k u)
  rw [GradedRing.proj_apply]
  have hproj : (DirectSum.decompose (homogeneousSubmodule σ k) p n : MvPolynomial σ k) =
      homogeneousComponent n p := decomposition.decompose'_apply p n
  rw [hproj, RingHom.mem_ker]
  have hs (f : MvPolynomial σ k) {m : ℕ} (hf : f.IsHomogeneous m) :
      coneEval k u f = Polynomial.monomial m (aeval u f) := by
    conv_lhs => rw [f.as_sum, map_sum]
    conv_rhs => rw [f.as_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d.degree = m := by
      by_contra hne
      exact (mem_support_iff.mp hd) (hf.coeff_eq_zero hne)
    rw [coneEval_monomial, hd']
  have hcoeff : (coneEval k u p).coeff n = aeval u (homogeneousComponent n p) := by
    nth_rewrite 1 [← p.sum_homogeneousComponent]
    rw [map_sum, Polynomial.finsetSum_coeff]
    simp_rw [hs _ (homogeneousComponent_isHomogeneous _ _), Polynomial.coeff_monomial, Finsupp.single_apply]
    by_cases hn : n ∈ Finset.range (p.totalDegree + 1)
    · simp [hn]
    · have hdeg : p.totalDegree < n := by
        simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
      simp [hn, homogeneousComponent_eq_zero n p hdeg]
  rw [hs _ (homogeneousComponent_isHomogeneous _ _), ← hcoeff, RingHom.mem_ker.mp hp]
  simp
private theorem cone_finrank_tower (E F : IntermediateField k L) (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toAlgebra
    Module.finrank E F * Module.finrank F L = Module.finrank E L := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.finrank_mul_finrank E F L
theorem residueDegree_mul_finrank (u : σ → L) (i : σ) (a : σ → k) :
    projectiveDegree u i a * Module.finrank (ratioField k u i) L =
      Module.finrank (IntermediateField.adjoin k {linearValue a (ratios u i)}) L :=
  cone_finrank_tower _ _ (adjoin_line_le_ratioField u i a)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial K1_13_6_3_6
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
theorem component_mul {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) (p : MvPolynomial σ k) (i : ℕ) :
    homogeneousComponent i (p * g) =
      if b ≤ i then homogeneousComponent (i - b) p * g else 0 := by
  simpa only [decompose_apply] using
    DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ k) i (a := p) hg
private def truncate (n : ℕ) (p : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p
private theorem totalDegree_truncate (n : ℕ) (p : MvPolynomial σ k) :
    (truncate n p).totalDegree ≤ n := by
  rw [← mem_restrictTotalDegree]
  apply Submodule.sum_mem
  intro i hi
  rw [mem_restrictTotalDegree]
  exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
private theorem component_truncate (n : ℕ) (p : MvPolynomial σ k) (i : ℕ) :
    homogeneousComponent i (truncate n p) = if i ≤ n then homogeneousComponent i p else 0 := by
  classical
  simp only [truncate, map_sum,
    fun j => homogeneousComponent_of_mem (m := i) (homogeneousComponent_mem j p)]
  simp [Finset.sum_ite_eq]
private theorem truncate_mul_mod {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    {p f g : MvPolynomial σ k} {b n : ℕ}
    (hp : p.totalDegree ≤ n) (hg : g.IsHomogeneous b) (hbn : b ≤ n)
    (hm : p - f * g ∈ I) : p - truncate (n - b) f * g ∈ I := by
  rw [mem_iff_homogeneousComponent_mem hI]
  intro i
  rw [map_sub]
  by_cases hi : i ≤ n
  · have hh := homogeneousComponent_mem_of_mem hI hm i
    rw [map_sub, component_mul hg] at hh
    rw [component_mul hg]
    by_cases hbi : b ≤ i
    · have hle : i - b ≤ n - b := Nat.sub_le_sub_right hi b
      simpa only [ite_eq_left hbi, component_truncate, ite_eq_left hle] using hh
    · simpa only [ite_eq_right hbi] using hh
  · have ht : (truncate (n - b) f * g).totalDegree ≤ n :=
      (totalDegree_mul _ _).trans (by
        have ht₀ := totalDegree_truncate (n - b) f
        have hg₀ := hg.totalDegree_le
        omega)
    rw [homogeneousComponent_eq_zero i p (by omega),
      homogeneousComponent_eq_zero i (truncate (n - b) f * g) (by omega),
      sub_zero]
    exact I.zero_mem
theorem hilbertFunction_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b n : ℕ}
    (hg : g.IsHomogeneous b) (hbn : b ≤ n) :
    affineHilbertFunction (I ⊔ Ideal.span {g}) n +
      affineHilbertFunction (I.colon {g}) (n - b) = affineHilbertFunction I n := by
  let J : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {g}
  let A : Ideal (MvPolynomial σ k) := I.colon {g}
  let q := Ideal.Quotient.factorₐ k (show I ≤ J from le_sup_left)
  let cut : quotientDegreeLE I n →ₗ[k] quotientDegreeLE J n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change q y.val ∈ _
      rw [← hpy]
      exact mk_mem_quotientDegreeLE hp
  have hcut : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let mul := (quotientMul I g).restrictScalars k
  let emb : quotientDegreeLE A (n - b) →ₗ[k] quotientDegreeLE I n :=
    (mul.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change quotientMul I g y.val ∈ _
      rw [← hpy, quotientMul_mk]
      have hd := hg.totalDegree_le
      exact mk_mem_quotientDegreeLE ((totalDegree_mul p g).trans (by omega))
  have hemb (y : quotientDegreeLE A (n - b)) : emb y ∈ LinearMap.ker cut := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change q (quotientMul I g y.val) = 0
    have hex := (LinearMap.exact_iff.mp (quotientMul_exact I g))
    have hm : quotientMul I g y.val ∈
        LinearMap.range (quotientMul I g) := LinearMap.mem_range_self _ _
    rw [← hex] at hm
    exact hm
  let e := emb.codRestrict (LinearMap.ker cut) hemb
  have he : Function.Bijective e := by
    constructor
    · intro x y he
      exact Subtype.ext (quotientMul_injective I g
        (congrArg (fun z => z.val.val) he))
    · intro y
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.val.property
      have hy : q y.val.val = 0 := congrArg Subtype.val y.property
      rw [← hpy] at hy
      have hm : p ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.mp hm
      obtain ⟨f, rfl⟩ := Ideal.mem_span_singleton.mp hx
      have hd : p - f * g ∈ I := by
        rwa [← hax, mul_comm g f, add_sub_cancel_right]
      refine ⟨⟨Ideal.Quotient.mk A (truncate (n - b) f),
        mk_mem_quotientDegreeLE (totalDegree_truncate _ _)⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change quotientMul I g (Ideal.Quotient.mk A (truncate (n - b) f)) = y.val.val
      rw [quotientMul_mk, ← hpy, Ideal.Quotient.eq]
      simpa only [neg_sub] using I.neg_mem (truncate_mul_mod hI hp hg hbn hd)
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut, finrank_top,
    ← (LinearEquiv.ofBijective e he).finrank_eq] at hrank
  exact hrank
theorem hilbertPolynomial_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) :
    affineHilbertPolynomial (I ⊔ Ideal.span {g}) +
      Polynomial.taylor (-(b : ℚ)) (affineHilbertPolynomial (I.colon {g})) =
      affineHilbertPolynomial I := by
  obtain ⟨N₀, h₀⟩ := exists_eval_affineHilbertPolynomial (I.colon {g})
  obtain ⟨N₁, h₁⟩ := exists_eval_affineHilbertPolynomial (I ⊔ Ideal.span {g})
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max (N₀ + b) N₁)
  intro N h
  have hN := (le_max_left (N₀ + b) N₁).trans h
  have hb : b ≤ N := by omega
  rw [Polynomial.eval_add, Polynomial.taylor_eval,
    h₁ N ((le_max_right (N₀ + b) N₁).trans h), ← sub_eq_add_neg, ← Nat.cast_sub hb,
    h₀ (N - b) (by omega)]
  exact_mod_cast hilbertFunction_cyclic hI hg hb
theorem coeff_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) {d : ℕ} (hd : (affineHilbertPolynomial I).natDegree ≤ d) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {g})).coeff d +
      (affineHilbertPolynomial (I.colon {g})).coeff d =
        (affineHilbertPolynomial I).coeff d := by
  have hA := (natDegree_affineHilbertPolynomial_le_of_le
    (Ideal.le_colon : I ≤ I.colon {g})).trans hd
  simpa only [Polynomial.coeff_add, Polynomial.coeff_taylor_of_natDegree_le _ hA] using
    congrArg (fun p : Polynomial ℚ => p.coeff d) (hilbertPolynomial_cyclic hI hg)
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5_3
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
abbrev ConeRing (I : Ideal (MvPolynomial σ k)) := MvPolynomial σ k ⧸ I
abbrev ConeFrac (I : Ideal (MvPolynomial σ k)) := FractionRing (ConeRing I)
def conePoint (I : Ideal (MvPolynomial σ k)) (i : σ) : ConeFrac I :=
  algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I (MvPolynomial.X i))
def chartField (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ) :
    IntermediateField k (ConeFrac I) :=
  ratioField k (conePoint I) a
def chartPoint (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a i : σ) : chartField I a :=
  ⟨ratios (conePoint I) a i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
theorem conePoint_ne_zero {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) : conePoint I a ≠ 0 :=
  fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp
    ((IsFractionRing.injective (ConeRing I) (ConeFrac I)).eq_iff.mp
      (h.trans (map_zero (algebraMap (ConeRing I) (ConeFrac I))).symm)))
@[simp] theorem chartPoint_coe (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a i : σ) :
    (chartPoint I a i : ConeFrac I) = conePoint I i / conePoint I a := rfl
theorem chartPoint_anchor {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) : chartPoint I a a = 1 := by
  apply Subtype.ext
  simp [conePoint_ne_zero ha]
theorem chart_generates (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ) :
    IntermediateField.adjoin k (Set.range (chartPoint I a)) = ⊤ := by
  apply (chartField I a).lift_injective
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  rw [← Set.range_comp]
  rfl
private theorem eval₂_scaled {A : Type} [CommRing A] (f : k →+* A)
    (u : σ → A) (z : A) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    p.eval₂ f (fun i => u i * z) = p.eval₂ f u * z ^ d := by
  classical
  simp only [eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]
  congr 2
  have hd : m.degree = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  exact congrArg (fun n => z ^ n) hd
private theorem coneEval_homogeneous {L : Type} [Field L] [Algebra k L]
    (u : σ → L) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    coneEval k u p = Polynomial.C (p.eval₂ (algebraMap k L) u) * Polynomial.X ^ d := by
  rw [coneEval, coe_eval₂Hom, eval₂_scaled _ _ _ hp]
  congr 1
  exact (hom_eval₂ p _ (Polynomial.C : L →+* (Polynomial L)) u).symm
private theorem coneEval_coeff {L : Type} [Field L] [Algebra k L]
    (u : σ → L) (p : MvPolynomial σ k) (d : ℕ) :
    (coneEval k u p).coeff d =
      (homogeneousComponent d p).eval₂ (algebraMap k L) u := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent (φ := p)]
  simp only [map_sum, Polynomial.finsetSum_coeff,
    coneEval_homogeneous u (homogeneousComponent_isHomogeneous _ _),
    Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d < p.totalDegree + 1
  · rw [Finset.sum_eq_single d]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp [hd]
  · rw [homogeneousComponent_eq_zero d p (by omega), eval₂_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j ≠ d := by
      rw [Finset.mem_range] at hj
      omega
    simp [Ne.symm hne]
private theorem is_mem_iff_chart_eval {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    p ∈ I ↔ p.eval₂ (algebraMap k (chartField I a)) (chartPoint I a) = 0 := by
  let j := (chartField I a).val
  let q : MvPolynomial σ k →+* ConeFrac I :=
    (algebraMap (ConeRing I) (ConeFrac I)).comp (Ideal.Quotient.mk I)
  have hq : q = MvPolynomial.eval₂Hom (algebraMap k (ConeFrac I)) (conePoint I) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C]
      rfl
    · intro i
      rw [eval₂Hom_X']
      rfl
  have he : q p =
      j (p.eval₂ (algebraMap k (chartField I a)) (chartPoint I a)) * conePoint I a ^ d := by
    have hx (i : σ) : j.toRingHom (chartPoint I a i) * conePoint I a = conePoint I i := by
      change (conePoint I i / conePoint I a) * conePoint I a = _
      exact div_mul_cancel₀ _ (conePoint_ne_zero ha)
    have hj : j.toRingHom.comp (algebraMap k (chartField I a)) = algebraMap k (ConeFrac I) :=
      IsScalarTower.algebraMap_eq k (chartField I a) (ConeFrac I) |>.symm
    rw [hq, coe_eval₂Hom]
    change _ = j.toRingHom _ * _
    rw [hom_eval₂, hj, ← eval₂_scaled _ _ _ hp, funext hx]
  have hk : p ∈ I ↔ q p = 0 := by
    change p ∈ I ↔ algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I p) = 0
    rw [← map_zero (algebraMap (ConeRing I) (ConeFrac I)),
      (IsFractionRing.injective (ConeRing I) (ConeFrac I)).eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [hk, he, mul_eq_zero, or_iff_left (pow_ne_zero _ (conePoint_ne_zero ha)),
    map_eq_zero_iff j j.injective]
theorem coneIdeal_chart {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (ha : MvPolynomial.X a ∉ I) :
    coneIdeal k (chartPoint I a) = I := by
  classical
  ext p
  change coneEval k (chartPoint I a) p = 0 ↔ p ∈ I
  rw [Polynomial.ext_iff]
  simp only [Polynomial.coeff_zero, coneEval_coeff, ← is_mem_iff_chart_eval ha
    (homogeneousComponent_isHomogeneous _ _)]
  exact (mem_iff_homogeneousComponent_mem hI p).symm
theorem homogeneous_map {E : Type} [Field E] (f : k →+* E)
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :
    (I.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ E) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hS, Ideal.map_span, Set.image_image]
  apply Ideal.homogeneous_span
  rintro _ ⟨v, _, rfl⟩
  obtain ⟨d, hd⟩ : SetLike.IsHomogeneousElem (homogeneousSubmodule σ k)
      (v : MvPolynomial σ k) := v.property
  exact ⟨d, IsHomogeneous.map hd f⟩
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L],
    CurveField k L → ∀ V : ValuationSubring L, V ≠ ⊤ →
    (∀ c : k, algebraMap k L c ∈ V) →
    ∃ w : CurvePlace k L, w.value.valuationSubring = V
def c2 : Prop :=
  ∀ (k L σ : Type) [Field k] [Field L] [Algebra k L] [Fintype σ]
    (u : σ → L) (i : σ) (a : σ → k), u i ≠ 0 →
    let z := linearValue a (ratios u i)
    Transcendental k z → ChartIntegral (k := k) (ratios u i) z →
      (coneIdeal k u).comap (lineProjection i a).toRingHom = ⊥ ∧
        (onCoordinateRings (coneIdeal k u) (lineProjection i a)).Finite
def c3 : Prop :=
  ∀ (k σ : Type) [Field k] [Fintype σ]
    (P : Ideal (MvPolynomial σ k))
    (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k),
    P.IsPrime → P.IsHomogeneous (homogeneousSubmodule σ k) →
    IsLinearProjection φ → P.comap φ.toRingHom = ⊥ →
    (onCoordinateRings P φ).Finite →
    affineDegree P = (residueDegree φ.toRingHom P : ℚ)
def c4 : Prop :=
  ∀ (k L σ : Type) [Field k] [Field L] [Algebra k L] [Fintype σ]
    (u : σ → L) (i : σ) (a : σ → k), u i ≠ 0 →
    Transcendental k (linearValue a (ratios u i)) →
    Module.Finite (IntermediateField.adjoin k {linearValue a (ratios u i)}) L →
    (coneIdeal k u).comap (lineProjection i a).toRingHom = ⊥ →
    residueDegree (lineProjection i a).toRingHom (coneIdeal k u) = projectiveDegree u i a
private theorem integral_of_places (h : c1) {k L : Type} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] (hL : CurveField k L) {x t : L}
    (hx : ∀ w : CurvePlace k L, w.value t ≤ 1 → w.value x ≤ 1) :
    IsIntegral (Algebra.adjoin k {t}) x := by
  let A := Algebra.adjoin k {t}
  let B := (integralClosure A L).toSubring
  by_contra hni
  obtain ⟨V, hBV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := B) (show x ∉ B from hni)
  have hne : V ≠ ⊤ := by
    intro ht
    apply hxV
    rw [ht]
    trivial
  have hmem (y : L) (hy : y ∈ A) : y ∈ V :=
    hBV (show y ∈ B from isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
  obtain ⟨w, hw⟩ := h k L hL V hne fun c => hmem _ (A.algebraMap_mem c)
  have htV := hmem t (Algebra.subset_adjoin (Set.mem_singleton t))
  apply hxV
  rw [← hw] at htV ⊢
  exact hx w htV
private theorem integral_on_charts (h : c1) {k L σ : Type} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] [Fintype σ] (hL : CurveField k L) {r : σ → L} {z : L}
    (hz : z ≠ 0)
    (hbound : ∀ (w : CurvePlace k L) j, w.value (r j) ≤ max 1 (w.value z)) :
    ChartIntegral (k := k) r z := by
  constructor
  · intro j
    exact integral_of_places h hL fun w hw =>
      (hbound w j).trans (max_eq_left hw).le
  · intro j
    apply integral_of_places h hL
    intro w hw
    have hval : 1 ≤ w.value z := (w.value.one_le_val_iff hz).2 hw
    rw [map_div₀, div_le_iff₀ ((w.value.pos_iff).2 hz), one_mul]
    exact (hbound w j).trans (max_eq_right hval).le
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) :
    K1_13_6_3_5_3.c3 := by
  intro k L σ _ _ _ _ _ hL hdiv u i hi
  refine ⟨height_pos_iff hL hdiv _, ?_⟩
  intro hp
  obtain ⟨a, ha, hbound⟩ := exists_linearValue_preserving hdiv (ratios u i)
  let z := linearValue a (ratios u i)
  have hheight : (∑ᶠ v : CurvePlace k L, poleOrder v.value z) =
      tupleHeight k L (ratios u i) := finsum_congr ha
  have hz : Transcendental k z := transcendental_of_pole_sum_pos (hheight.symm ▸ hp)
  have hcharts := integral_on_charts h1 hL hz.ne_zero hbound
  obtain ⟨hker, hfin⟩ := h2 k L σ u i a hi hz hcharts
  let P := coneIdeal k u
  let φ := lineProjection i a
  have hdeg := h3 k σ P φ (RingHom.ker_isPrime _) (coneIdeal_homogeneous u)
    (lineProjection_linear i a) hker hfin
  have hr := h4 k L σ u i a hi hz (finite_of_transcendental hL hz) hker
  constructor
  · have hinj : Function.Injective (onCoordinateRings P φ) := Ideal.quotientMap_injective
    have hh := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective
      (onCoordinateRings P φ) hfin hinj
    rw [hker, natDegree_affineHilbertPolynomial_bot, Nat.card_fin] at hh
    exact hh
  · rw [hdeg, hr, ← Nat.cast_mul, mul_comm (Module.finrank _ L) (projectiveDegree u i a),
      residueDegree_mul_finrank, ← (hdiv z).2.2.2 hz, hheight]
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 Polynomial
def componentRow (P : JetIdeal) : Row 4 →+* JetField P :=
  (onComponent P).comp (MvPolynomial.map genericCoeffs)
abbrev ContractedRing (P : JetIdeal) := ↥(componentRow P).range
abbrev ContractedField (P : JetIdeal) := FractionRing (ContractedRing P)
def rowAt (P : JetIdeal) : Row 4 →+* ContractedField P :=
  (algebraMap (ContractedRing P) (ContractedField P)).comp (componentRow P).rangeRestrict
def constantsAt (P : JetIdeal) : Geom →+* ContractedField P :=
  (rowAt P).comp (MvPolynomial.C.comp Polynomial.C)
instance contractedAlgebra (P : JetIdeal) : Algebra Geom (ContractedField P) :=
  (constantsAt P).toAlgebra
def toComponent (P : JetIdeal) [P.IsPrime] : ContractedField P →+* JetField P :=
  IsFractionRing.lift (g := (componentRow P).range.subtype) Subtype.val_injective
def abscissa {F : Type} [CommRing F] (e : Row 4 →+* F) : F :=
  e (MvPolynomial.C Polynomial.X)
def jetCoordinate {F : Type} [CommRing F] (e : Row 4 →+* F) (i : Fin 4) : F :=
  e (MvPolynomial.X i)
def fromTaylor {F : Type} [CommRing F] {M : ℕ} (x : F) (jets : Fin M → F) : (Polynomial F) :=
  ∑ i : Fin M, Polynomial.C (jets i) * (Polynomial.X (R := F) - Polynomial.C x) ^ i.val
def dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (y : F) (n : ℕ) : F :=
  ((D : F → F)^[n]) y / (n.factorial : F)
def differentialTaylor {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (x y : F) : (Polynomial F) :=
  fromTaylor x (fun i : Fin taylorLength => dividedIterate D y i.val)
def chartTaylor {F : Type} [Field F] (e : Row 4 →+* F) (g : Row 4) : (Polynomial F) :=
  fromTaylor (abscissa e)
    (fun i : Fin taylorLength => e (jetNumerator g i.val) / e (separant g) ^ (2 * i.val) / (i.val.factorial : F))
end
end K1_13_6_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_3
noncomputable section
open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_3_3
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
variable (P : Ideal (MvPolynomial σ k))
variable (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k)
abbrev planeIdeal : Ideal (MvPolynomial (Fin 2) k) := P.comap φ.toRingHom
private def truncate {τ : Type} (n : ℕ) (p : MvPolynomial τ k) : MvPolynomial τ k :=
  ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p
private theorem truncate_eq {τ : Type} {p : MvPolynomial τ k} {n : ℕ}
    (hp : p.totalDegree ≤ n) : truncate n p = p := by
  symm
  calc
    p = ∑ i ∈ Finset.range (p.totalDegree + 1), homogeneousComponent i p :=
      (sum_homogeneousComponent p).symm
    _ = truncate n p := ?_
  unfold truncate
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hp))
  intro i _ hi
  exact homogeneousComponent_eq_zero i p (by simpa using hi)
private theorem truncate_degree {τ : Type} (n : ℕ) (p : MvPolynomial τ k) :
    (truncate n p).totalDegree ≤ n := by
  rw [← mem_restrictTotalDegree]
  apply Submodule.sum_mem
  intro i hi
  rw [mem_restrictTotalDegree]
  exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
private theorem truncate_component {τ : Type} (n i : ℕ) (p : MvPolynomial τ k) :
    homogeneousComponent i (truncate n p) = if i ≤ n then homogeneousComponent i p else 0 := by
  classical
  simp only [truncate, map_sum,
    fun j => homogeneousComponent_of_mem (m := i) (homogeneousComponent_mem j p)]
  simp [Finset.sum_ite_eq]
private theorem projection_homogeneous (hφ : IsLinearProjection φ)
    {p : MvPolynomial (Fin 2) k} {i : ℕ} (hp : p.IsHomogeneous i) :
    (φ p).IsHomogeneous i := by
  rw [DFunLike.congr_fun (aeval_unique φ) p, aeval_def, algebraMap_eq]
  simpa only [one_mul] using hp.eval₂ C (φ ∘ MvPolynomial.X) (isHomogeneous_C _) hφ
private theorem projection_component (hφ : IsLinearProjection φ)
    (p : MvPolynomial (Fin 2) k) (i : ℕ) :
    homogeneousComponent i (φ p) = φ (homogeneousComponent i p) := by
  classical
  conv_lhs => rw [← truncate_eq (p := p) le_rfl]
  simp only [truncate, map_sum, fun j => homogeneousComponent_of_mem (m := i)
    (projection_homogeneous φ hφ (homogeneousComponent_isHomogeneous j p))]
  by_cases hi : i ≤ p.totalDegree
  · simp [Finset.sum_ite_eq, hi]
  · rw [homogeneousComponent_eq_zero i p (by omega), map_zero]
    simp [Finset.sum_ite_eq, hi]
private theorem filtered_of_generators
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k)) (hφ : IsLinearProjection φ)
    {ι : Type} [Fintype ι] (b : ι → MvPolynomial σ k) (d : ι → ℕ)
    (hb : ∀ j, (b j).IsHomogeneous (d j))
    (hgen : ∀ y : MvPolynomial σ k ⧸ P,
      ∃ a : ι → MvPolynomial (Fin 2) k,
        ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y)
    (n : ℕ) {y : MvPolynomial σ k ⧸ P} (hy : y ∈ quotientDegreeLE P n) :
    ∃ a : ι → MvPolynomial (Fin 2) k, (∀ j, (a j).totalDegree ≤ n) ∧
      ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y := by
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hy
  obtain ⟨a, ha⟩ := hgen (Ideal.Quotient.mk P p)
  rw [← map_sum, Ideal.Quotient.eq] at ha
  let a' := fun j => if d j ≤ n then truncate (n - d j) (a j) else 0
  have ha' (j : ι) : (a' j).totalDegree ≤ n := by
    by_cases hd : d j ≤ n
    · simpa only [a', ite_eq_left hd] using (truncate_degree (n - d j) (a j)).trans (Nat.sub_le ..)
    · simp [a', hd]
  refine ⟨a', ha', ?_⟩
  rw [← map_sum, Ideal.Quotient.eq, mem_iff_homogeneousComponent_mem hP]
  intro i
  rw [map_sub, map_sum]
  by_cases hi : i ≤ n
  · have he (j : ι) : homogeneousComponent i (φ (a' j) * b j) =
        homogeneousComponent i (φ (a j) * b j) := by
      rw [K1_13_6_3_5_1.component_mul (hb j), K1_13_6_3_5_1.component_mul (hb j)]
      by_cases hd : d j ≤ i
      · simp only [ite_eq_left hd, a', ite_eq_left (hd.trans hi), projection_component φ hφ,
          truncate_component, ite_eq_left (Nat.sub_le_sub_right hi _)]
      · rw [ite_eq_right hd, ite_eq_right hd]
    simpa only [map_sub, map_sum, he] using homogeneousComponent_mem_of_mem hP ha i
  · have he (j : ι) :
        homogeneousComponent i (φ (a' j) * b j) = 0 := by
      rw [K1_13_6_3_5_1.component_mul (hb j)]
      by_cases hd : d j ≤ i
      · rw [ite_eq_left hd]
        by_cases hj : d j ≤ n
        · simp only [a', ite_eq_left hj, projection_component φ hφ, truncate_component,
            ite_eq_right (by omega : ¬ i - d j ≤ n - d j), map_zero, zero_mul]
        · simp [a', hj]
      · rw [ite_eq_right hd]
    simp [he, homogeneousComponent_eq_zero i p (by omega : p.totalDegree < i)]
theorem exists_filtered_generators
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k)) (hφ : IsLinearProjection φ)
    (hf : (onCoordinateRings P φ).Finite) :
    ∃ (m : ℕ) (b : Fin m → MvPolynomial σ k),
      ∀ (n : ℕ) (y : MvPolynomial σ k ⧸ P), y ∈ quotientDegreeLE P n →
        ∃ a : Fin m → MvPolynomial (Fin 2) k, (∀ j, (a j).totalDegree ≤ n) ∧
          ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y := by
  classical
  let g := onCoordinateRings P φ
  let := g.toRingHom.toAlgebra
  have hfin : Module.Finite (MvPolynomial (Fin 2) k ⧸ planeIdeal P φ)
      (MvPolynomial σ k ⧸ P) := hf
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose f hf using fun i : s => Ideal.Quotient.mk_surjective (I := P) (i : MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD⟩ := Finite.exists_le (fun j => (f j).totalDegree)
  let ι := s × Fin (D + 1)
  let b : ι → MvPolynomial σ k := fun j => homogeneousComponent j.2 (f j.1)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨_, b ∘ e, filtered_of_generators P φ hP hφ _ (fun j => (e j).2)
    (fun j => homogeneousComponent_isHomogeneous _ _) ?_⟩
  intro y
  have hy : y ∈ Submodule.span (MvPolynomial (Fin 2) k ⧸ planeIdeal P φ)
      (Set.range (fun i : s => (i : MvPolynomial σ k ⧸ P))) := by
    rw [Subtype.range_coe_subtype, Finset.setOfPred_mem, hs]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  choose a ha using fun j => Ideal.Quotient.mk_surjective (I := planeIdeal P φ) (c j)
  refine ⟨fun j => a (e j).1, ?_⟩
  change (∑ j, Ideal.Quotient.mk P (φ (a (e j).1) * b (e j))) = y
  rw [Equiv.sum_comp e (fun j : ι => Ideal.Quotient.mk P (φ (a j.1) * b j))]
  rw [Fintype.sum_prod_type]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j _
  have hsum : ∑ l : Fin (D + 1), homogeneousComponent l (f j) = f j := by
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => homogeneousComponent l (f j))]
    exact truncate_eq (hD j)
  simp only [b, ← map_sum, ← Finset.mul_sum, hsum, map_mul, hf]
  rw [Algebra.smul_def, ← ha j]
  rfl
end
end K1_13_6_3_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_4
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 K1_13_6_3_5_3_3
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
private def scale {L : Type} [Field L] (b : L) (hb : b ≠ 0) :
    (Polynomial L) ≃ₐ[L] (Polynomial L) :=
  Polynomial.algEquivOfCompEqX (Polynomial.C b⁻¹ * Polynomial.X)
    (Polynomial.C b * Polynomial.X)
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
private theorem coneEval_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    coneEval k (fun i => w i / b) = (scale b hb).toRingHom.comp (coneEval k w) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coneEval, scale, Polynomial.algebraMap_eq]
  · intro i
    simp only [RingHom.comp_apply, coneEval, MvPolynomial.eval₂Hom_X']
    change Polynomial.C (w i / b) * Polynomial.X =
      Polynomial.aeval (Polynomial.C b⁻¹ * Polynomial.X) (Polynomial.C (w i) * Polynomial.X)
    rw [map_mul, Polynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.aeval_X, ← mul_assoc,
      ← Polynomial.C_mul, div_eq_mul_inv]
private def coneRat {k L σ : Type} [Field k] [Field L] [Algebra k L] (w : σ → L) :
    MvPolynomial σ k →+* RatFunc L :=
  (algebraMap (Polynomial L) (RatFunc L)).comp (coneEval k w)
private theorem coneRat_C {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (c : k) :
    coneRat w (MvPolynomial.C c) = RatFunc.C (algebraMap k L c) := by
  simp [coneRat, coneEval]
private theorem coneRat_X {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) :
    coneRat (k := k) w (MvPolynomial.X i) = RatFunc.C (w i) * RatFunc.X := by
  simp [coneRat, coneEval]
private theorem coneRat_ker_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    RingHom.ker (coneRat (k := k) (fun i => w i / b)) = coneIdeal k w := by
  rw [coneRat, RingHom.ker_comp_of_injective _ (RatFunc.algebraMap_injective L),
    coneEval_div w b hb]
  exact RingHom.ker_comp_of_injective (coneEval k w)
    (f := (scale b hb).toRingHom) (scale b hb).injective
private def fractionEval {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) :
    FractionRing (A ⧸ P) →+* K :=
  IsFractionRing.lift (RingHom.lift_injective_of_ker_le_ideal P
    (fun _ ha => RingHom.mem_ker.mp (h.symm ▸ ha)) h.le)
private theorem fractionEval_mk {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) (a : A) :
    fractionEval P e h
      (algebraMap (A ⧸ P) (FractionRing (A ⧸ P)) (Ideal.Quotient.mk P a)) = e a := by
  rw [fractionEval, IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
private theorem fractionEval_range_le {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P)
    (S : Subfield K) (he : ∀ a, e a ∈ S) :
    (fractionEval P e h).fieldRange ≤ S := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A ⧸ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [map_div₀, fractionEval_mk, fractionEval_mk]
  exact S.div_mem (he a) (he b)
private theorem ratFunc_mem {F K : Type} [Field F] [Field K]
    (g : RatFunc F →+* K) (S : Subfield K)
    (hC : ∀ a, g (RatFunc.C a) ∈ S) (hX : g RatFunc.X ∈ S) (z : RatFunc F) : g z ∈ S := by
  have hp (p : (Polynomial F)) : g (algebraMap (Polynomial F) (RatFunc F) p) ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [RatFunc.algebraMap_monomial, map_mul, map_pow]
        exact S.mul_mem (hC a) (S.pow_mem hX n)
  induction z using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀]
      exact S.div_mem (hp p) (hp q)
private theorem ratFunc_map_poly {F L : Type} [Field F] [Field L] [Algebra F L]
    (p : (Polynomial F)) :
    algebraMap (RatFunc F) (RatFunc L) (algebraMap (Polynomial F) (RatFunc F) p) =
      algebraMap (Polynomial L) (RatFunc L) (p.map (algebraMap F L)) := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) (RatFunc F) (RatFunc L),
    IsScalarTower.algebraMap_apply (Polynomial F) (Polynomial L) (RatFunc L)]
  rfl
private theorem ratFunc_map_C {F L : Type} [Field F] [Field L] [Algebra F L] (c : F) :
    algebraMap (RatFunc F) (RatFunc L) (RatFunc.C c) = RatFunc.C (algebraMap F L c) := by
  simpa only [RatFunc.algebraMap_C, Polynomial.map_C] using
    ratFunc_map_poly (L := L) (Polynomial.C c)
private theorem ratFunc_map_X {F L : Type} [Field F] [Field L] [Algebra F L] :
    algebraMap (RatFunc F) (RatFunc L) RatFunc.X = RatFunc.X := by
  simpa only [RatFunc.algebraMap_X, Polynomial.map_X] using
    ratFunc_map_poly (L := L) (Polynomial.X : (Polynomial F))
private theorem ratFunc_map_comp {E F L : Type} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra F L] [Algebra E L] [IsScalarTower E F L] :
    (algebraMap (RatFunc F) (RatFunc L)).comp (algebraMap (RatFunc E) (RatFunc F)) =
      algebraMap (RatFunc E) (RatFunc L) := by
  apply IsFractionRing.ringHom_ext (A := (Polynomial E))
  intro p
  rw [RingHom.comp_apply, ratFunc_map_poly, ratFunc_map_poly, ratFunc_map_poly,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq E F L]
private theorem fractionEquiv {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) (hi : w i = 1) (F : IntermediateField k L)
    (hF : IntermediateField.adjoin k (Set.range w) = F)
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] (hP : RingHom.ker (coneRat w) = P) :
    ∃ e : FractionRing (MvPolynomial σ k ⧸ P) ≃+* RatFunc F,
      (algebraMap (RatFunc F) (RatFunc L)).comp e.toRingHom = fractionEval P (coneRat w) hP := by
  let f := fractionEval P (coneRat w) hP
  let g := algebraMap (RatFunc F) (RatFunc L)
  have he (p : MvPolynomial σ k) : coneRat w p ∈ f.fieldRange :=
    ⟨_, fractionEval_mk P (coneRat w) hP p⟩
  have hcoord (j : σ) : RatFunc.C (w j) * RatFunc.X ∈ f.fieldRange := by
    simpa only [coneRat_X] using he (MvPolynomial.X j)
  have hX : RatFunc.X ∈ f.fieldRange := by
    simpa only [hi, map_one, one_mul] using hcoord i
  have hconstants (c : F) : RatFunc.C (c : L) ∈ f.fieldRange := by
    let S : IntermediateField k L :=
      (f.fieldRange.comap RatFunc.C).toIntermediateField (fun b => by
        change RatFunc.C (algebraMap k L b) ∈ f.fieldRange
        simpa only [coneRat_C] using he (MvPolynomial.C b))
    have hle : F ≤ S := by
      rw [← hF, IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      change RatFunc.C (w j) ∈ f.fieldRange
      have h := f.fieldRange.div_mem (hcoord j) hX
      rwa [mul_div_cancel_right₀ _ RatFunc.X_ne_zero] at h
    exact hle c.property
  have hg : g.fieldRange = f.fieldRange := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ratFunc_mem g f.fieldRange (fun c => ?_) ?_ z
      · rw [show g (RatFunc.C c) = RatFunc.C (c : L) from ratFunc_map_C c]
        exact hconstants c
      · exact ratFunc_map_X (F := F) (L := L) ▸ hX
    · apply fractionEval_range_le
      intro p
      induction p using MvPolynomial.induction_on with
      | C b =>
          rw [coneRat_C]
          exact ⟨RatFunc.C (algebraMap k F b), ratFunc_map_C _⟩
      | add p q hp hq =>
          rw [map_add]
          exact g.fieldRange.add_mem hp hq
      | mul_X p j hp =>
          rw [map_mul, coneRat_X]
          refine g.fieldRange.mul_mem hp (g.fieldRange.mul_mem ?_ ⟨RatFunc.X, ratFunc_map_X⟩)
          have hj : w j ∈ F := hF ▸ IntermediateField.mem_adjoin_of_mem k (Set.mem_range_self j)
          exact ⟨RatFunc.C ⟨w j, hj⟩, ratFunc_map_C _⟩
  refine ⟨f.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hg.symm).trans g.rangeRestrictFieldEquiv.symm), ?_⟩
  ext1 x
  change g (g.rangeRestrictFieldEquiv.symm _) = f x
  exact RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
private theorem finrank_cone {E F L KU KV : Type}
    [Field E] [Field F] [Field L] [Field KU] [Field KV]
    [Algebra E F] [Algebra F L] [Algebra E L] [IsScalarTower E F L]
    (f : KV →+* KU) (eV : KV ≃+* RatFunc E) (eU : KU ≃+* RatFunc F)
    (h : ((algebraMap (RatFunc F) (RatFunc L)).comp eU.toRingHom).comp f =
      (algebraMap (RatFunc E) (RatFunc L)).comp eV.toRingHom) :
    letI := f.toAlgebra
    Module.finrank KV KU = Module.finrank E F := by
  let _ : Algebra KV KU := f.toAlgebra
  have hcomm : (algebraMap (RatFunc E) (RatFunc F)).comp eV.toRingHom =
      eU.toRingHom.comp f := by
    ext1 x
    apply (algebraMap (RatFunc F) (RatFunc L)).injective
    change ((algebraMap (RatFunc F) (RatFunc L)).comp (algebraMap (RatFunc E) (RatFunc F)))
      (eV x) = (algebraMap (RatFunc F) (RatFunc L)) (eU (f x))
    rw [ratFunc_map_comp]
    exact (RingHom.congr_fun h x).symm
  calc
    _ = Module.finrank (RatFunc E) (RatFunc F) := Algebra.finrank_eq_of_equiv_equiv eV eU hcomm
    _ = Module.finrank (Polynomial E) (Polynomial F) := IsFractionRing.finrank_eq (Polynomial E) (RatFunc E) (Polynomial F) (RatFunc F)
    _ = Module.finrank E F := congrArg Cardinal.toNat (rank_polynomial_polynomial E F)
set_option maxHeartbeats 1000000 in
theorem proof : K1_13_6_3_5_3_3.c4 := by
  classical
  intro k L σ _ _ _ _ u i a hi _hz _hfinite _hcomap
  let U := ratios u i
  let z := linearValue a U
  let V : Fin 2 → L := ![1, z]
  let E := IntermediateField.adjoin k {z}
  let F := ratioField k u i
  let φ := (lineProjection i a).toRingHom
  let P := coneIdeal k u
  let Q := P.comap φ
  let _ : P.IsPrime := RingHom.ker_isPrime (coneEval k u)
  let _ : Q.IsPrime := Ideal.IsPrime.comap φ
  have hU : U i = 1 := div_self hi
  have hV : V 0 = 1 := rfl
  have hE : IntermediateField.adjoin k (Set.range V) = E := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      fin_cases j
      · exact E.one_mem
      · exact IntermediateField.mem_adjoin_of_mem k (Set.mem_singleton z)
    · apply IntermediateField.adjoin_le_iff.mpr
      intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact IntermediateField.mem_adjoin_of_mem k ⟨1, rfl⟩
  have hnorm : (coneRat (k := k) U).comp φ = coneRat V := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change coneRat U (lineProjection i a (MvPolynomial.C b)) = coneRat V (MvPolynomial.C b)
      simp [coneRat_C]
    · intro j
      change coneRat U (lineProjection i a (MvPolynomial.X j)) = coneRat V (MvPolynomial.X j)
      rw [lineProjection, MvPolynomial.aeval_X]
      fin_cases j
      · change coneRat U (MvPolynomial.X i) = coneRat V (MvPolynomial.X 0)
        rw [coneRat_X, coneRat_X, hU, hV]
      · change coneRat U (∑ l, MvPolynomial.C (a l) * MvPolynomial.X l) =
          coneRat V (MvPolynomial.X 1)
        rw [coneRat_X]
        change coneRat U (∑ l, MvPolynomial.C (a l) * MvPolynomial.X l) =
          RatFunc.C (∑ l, a l • U l) * RatFunc.X
        rw [map_sum, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        rw [map_mul, coneRat_C, coneRat_X, Algebra.smul_def, map_mul, mul_assoc]
  have hP : RingHom.ker (coneRat (k := k) U) = P := coneRat_ker_div u (u i) hi
  have hQ : RingHom.ker (coneRat (k := k) V) = Q := by
    rw [← hnorm, ← RingHom.comap_ker, hP]
  let KU := FractionRing (MvPolynomial σ k ⧸ P)
  let KV := FractionRing (MvPolynomial (Fin 2) k ⧸ Q)
  let fU : KU →+* RatFunc L := fractionEval P (coneRat U) hP
  let fV : KV →+* RatFunc L := fractionEval Q (coneRat V) hQ
  let f : KV →+* KU :=
    IsFractionRing.map (Ideal.quotientMap_injective (I := P) (f := φ))
  let _ : Algebra KV KU := f.toAlgebra
  have hsquare : fU.comp f = fV := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin 2) k ⧸ Q)
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hf : f (algebraMap (MvPolynomial (Fin 2) k ⧸ Q) KV (Ideal.Quotient.mk Q p)) =
        algebraMap (MvPolynomial σ k ⧸ P) KU (Ideal.Quotient.mk P (φ p)) := by
      change IsLocalization.map _ (Ideal.quotientMap P φ le_rfl) _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    rw [RingHom.comp_apply, hf]
    exact (fractionEval_mk P (coneRat U) hP (φ p)).trans
      ((RingHom.congr_fun hnorm p).trans (fractionEval_mk Q (coneRat V) hQ p).symm)
  obtain ⟨eU, heU⟩ := fractionEquiv U i hU F rfl P hP
  obtain ⟨eV, heV⟩ := fractionEquiv V 0 hV E hE Q hQ
  let _ : Algebra E F := (IntermediateField.inclusion (adjoin_line_le_ratioField u i a)).toAlgebra
  let _ : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold residueDegree
  rw [dite_eq_left (show P.IsPrime from inferInstance)]
  change Module.finrank KV KU = Module.finrank E F
  apply finrank_cone (L := L) f eV eU
  rw [heU, heV]
  exact hsquare
end
end K1_13_6_3_5_3_3_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5_3
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
private theorem trdeg_fraction (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F] :
    Algebra.trdeg k F = Algebra.trdeg k A := by
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic _ A⁰
  rw [← trdeg_add_eq k A (A := F), trdeg_eq_zero (R := A) (A := F), add_zero]
private theorem trdeg_of_finite {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra k A] [Algebra k B] (g : B →ₐ[k] A) (hg : Function.Injective g)
    (hfinite : g.Finite) : Algebra.trdeg k A = Algebra.trdeg k B := by
  let algebra := g.toRingHom.toAlgebra
  let := algebra
  let : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  let : Module.Finite B A := hfinite
  have : Algebra.IsAlgebraic B A := Algebra.IsIntegral.isAlgebraic
  simpa only [trdeg_eq_zero (R := B) (A := A), add_zero] using
    (trdeg_add_eq k B (A := A)).symm
private theorem trdeg_cone [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    Algebra.trdeg k (ConeFrac I) = (dimension I : Cardinal) := by
  obtain ⟨d, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k (ConeRing I)
  have hdim := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfinite hg
  rw [Nat.card_fin] at hdim
  calc
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k (ConeRing I) := trdeg_fraction _ _
    _ = Algebra.trdeg k (MvPolynomial (Fin d) k) := trdeg_of_finite g hg hfinite
    _ = (d : Cardinal) := by simp [MvPolynomial.trdeg_of_isDomain]
    _ = (dimension I : Cardinal) := congrArg (fun n : ℕ => (n : Cardinal)) hdim.symm
private theorem trdeg_cone_chart (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ)
    (heq : coneIdeal k (chartPoint I a) = I) (ha : MvPolynomial.X a ∉ I) :
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k (chartField I a) + 1 := by
  let L := chartField I a
  let F := FractionRing (Polynomial L)
  let f : MvPolynomial σ k →ₐ[k] (Polynomial L) :=
    MvPolynomial.aeval (fun i => Polynomial.C (chartPoint I a i) * Polynomial.X)
  have hf : RingHom.ker f = I := heq
  let g : ConeRing I →ₐ[k] (Polynomial L) :=
    Ideal.Quotient.liftₐ I f (fun p hp => show p ∈ RingHom.ker f from hf.symm ▸ hp)
  have hg : Function.Injective g :=
    (Ideal.injective_lift_iff _).mpr hf
  let emb : (Polynomial L) →ₐ[k] F := (Algebra.ofId (Polynomial L) F).restrictScalars k
  let u := emb.comp g
  have hu : Function.Injective u := (IsFractionRing.injective (Polynomial L) F).comp hg
  let j : ConeFrac I →ₐ[k] F := IsFractionRing.liftAlgHom hu
  have hj (i : σ) : j (conePoint I i) =
      emb (Polynomial.C (chartPoint I a i) * Polynomial.X) := by
    change IsFractionRing.lift (g := u.toRingHom) hu
      (algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I (MvPolynomial.X i))) = _
    rw [IsFractionRing.lift_algebraMap]
    change emb (f (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  have hx : j (conePoint I a) = emb Polynomial.X := by
    rw [hj, chartPoint_anchor ha, map_one, one_mul]
  have hz : emb Polynomial.X ≠ 0 := by
    rw [← hx]
    exact (map_eq_zero j).not.mpr (conePoint_ne_zero ha)
  let const : L →ₐ[k] F := (Algebra.ofId L F).restrictScalars k
  have hC (c : L) : const c = emb (Polynomial.C c) :=
    IsScalarTower.algebraMap_apply L (Polynomial L) F c
  have hc (i : σ) :
      const (chartPoint I a i) = j (conePoint I i / conePoint I a) := by
    rw [map_div₀, hj, hx, map_mul, mul_div_cancel_right₀ _ hz]
    exact hC _
  have hconst : ∀ x : L, const x ∈ j.fieldRange := by
    have hle : IntermediateField.adjoin k (Set.range (chartPoint I a)) ≤
        j.fieldRange.comap const := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (hc i).symm⟩
    rw [chart_generates] at hle
    exact fun x => hle (show x ∈ (⊤ : IntermediateField k L) from trivial)
  have hpoly (p : (Polynomial L)) : emb p ∈ j.fieldRange := by
    refine Polynomial.induction_on' (motive := fun p : (Polynomial L) => emb p ∈ j.fieldRange) p ?_ ?_
    · intro p q hp hq
      rw [map_add]
      exact j.fieldRange.add_mem hp hq
    · intro n c
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, ← hx, ← hC]
      have hmem : j (conePoint I a) ∈ j.fieldRange := ⟨conePoint I a, rfl⟩
      exact j.fieldRange.mul_mem (hconst c) (j.fieldRange.pow_mem hmem n)
  have hsurj : Function.Surjective j := by
    intro z
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial L) z
    exact j.fieldRange.div_mem (hpoly p) (hpoly q)
  have : FaithfulSMul k L :=
    (faithfulSMul_iff_algebraMap_injective k L).mpr (algebraMap k L).injective
  calc
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k F :=
      (AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩).trdeg_eq
    _ = Algebra.trdeg k (Polynomial L) := trdeg_fraction (Polynomial L) F
    _ = Algebra.trdeg k L + 1 := by
      simpa only [Polynomial.trdeg_of_isDomain] using (trdeg_add_eq k L (A := (Polynomial L))).symm
theorem chart_curve [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ k)) (ha : MvPolynomial.X a ∉ I)
    (hdim : dimension I = 2) :
    CurveField k (chartField I a) ∧ ∃ i, Transcendental k (chartPoint I a i) := by
  let L := chartField I a
  have hh := trdeg_cone_chart I a (coneIdeal_chart hhom ha) ha
  rw [trdeg_cone I, hdim] at hh
  change (2 : Cardinal) = Algebra.trdeg k L + 1 at hh
  have htr : Algebra.trdeg k L = 1 := by
    have hone : (1 : Cardinal) + 1 = 2 := by norm_num
    rw [← hone] at hh
    exact Cardinal.eq_of_add_eq_add_right hh.symm (by simp)
  have hex : ∃ i, Transcendental k (chartPoint I a i) := by
    by_contra! hall
    have halg := (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
      (F := k) (S := Set.range (chartPoint I a))).mpr (by rintro _ ⟨i, rfl⟩; exact not_not.mp (hall i))
    rw [chart_generates] at halg
    have : Algebra.IsAlgebraic k L :=
      (IntermediateField.topEquiv (F := k) (E := L)).isAlgebraic
    rw [trdeg_eq_zero (R := k) (A := L)] at htr
    exact zero_ne_one htr
  refine ⟨?_, hex⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨chartPoint I a i, hi, ?_⟩
  let K := IntermediateField.adjoin k {chartPoint I a i}
  have hai : AlgebraicIndependent k (fun _ : Fin 1 => chartPoint I a i) :=
    (algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hi
  have hb := hai.isTranscendenceBasis_of_trdeg_le_of_finite (by
    change Algebra.trdeg k L ≤ Cardinal.mk (Fin 1)
    simp [htr])
  have hrange : Set.range (fun _ : Fin 1 => chartPoint I a i) = {chartPoint I a i} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  have halg : Algebra.IsAlgebraic K L := by
    change Algebra.IsAlgebraic (IntermediateField.adjoin k {chartPoint I a i}) L
    rw [← hrange]
    exact hb.isAlgebraic_field
  have htop : IntermediateField.adjoin K (Set.range (chartPoint I a)) = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, chart_generates, sup_top_eq,
      IntermediateField.restrictScalars_top]
  have hf := IntermediateField.finiteDimensional_adjoin (K := K)
    (S := Set.range (chartPoint I a)) (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  rw [htop] at hf
  let e := IntermediateField.topEquiv (F := K) (E := L)
  exact Module.Finite.of_surjective e.toLinearMap e.surjective
theorem exists_anchor {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (hd : dimension I = 2) :
    ∃ a : Fin n, MvPolynomial.X a ∉ I ∧ ∀ i : Fin n, a < i → MvPolynomial.X i ∈ I := by
  classical
  let s := Finset.univ.filter fun i : Fin n => MvPolynomial.X i ∉ I
  have hs : s.Nonempty := by
    by_contra hn
    have hz (i : Fin n) : MvPolynomial.X i ∈ I := by
      by_contra hx
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    have hsurj : Function.Surjective (algebraMap k (ConeRing I)) := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨constantCoeff p, ?_⟩
      have he : Ideal.Quotient.mk I =
          eval₂Hom (algebraMap k (ConeRing I)) (fun _ => 0) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          rw [eval₂Hom_C]
          rfl
        · intro i
          rw [eval₂Hom_X', Ideal.Quotient.eq_zero_iff_mem]
          exact hz i
      rw [eval₂Hom_zero'] at he
      exact (RingHom.congr_fun he p).symm
    let : Module.Finite k (ConeRing I) :=
      Module.Finite.of_surjective (Algebra.linearMap k (ConeRing I)) hsurj
    rw [dimension, affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C] at hd
    omega
  refine ⟨s.max' hs, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, ?_⟩
  intro i hi
  by_contra hz
  exact (not_le_of_gt hi) (Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩))
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_3_3
noncomputable section
open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_3_3
attribute [local instance] MvPolynomial.gradedAlgebra
theorem proof : K1_13_6_3_5_3_3.c3 := by
  classical
  intro k σ _ _ P φ hprime hP hφ hker hfin
  let Q := planeIdeal P φ
  let A := MvPolynomial (Fin 2) k ⧸ Q
  let B := MvPolynomial σ k ⧸ P
  let F := FractionRing A
  let E := FractionRing B
  let g : A →ₐ[k] B := onCoordinateRings P φ
  have : P.IsPrime := hprime
  have : Q.IsPrime := Ideal.IsPrime.comap φ.toRingHom
  have hg : Function.Injective g := Ideal.quotientMap_injective
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  let f : F →+* E := IsFractionRing.map (show Function.Injective g.toRingHom from hg)
  let : Algebra F E := f.toAlgebra
  let i : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  let j : B →ₐ[k] E := IsScalarTower.toAlgHom k B E
  have hi : Function.Injective i := IsFractionRing.injective A F
  have hj : Function.Injective j := IsFractionRing.injective B E
  have hcomm (a : A) : j (g a) = algebraMap F E (i a) := by
    change algebraMap B E (g a) = f (algebraMap A F a)
    symm
    apply IsLocalization.map_eq
  have : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap k E a = j (g (algebraMap k A a)) := ((j.comp g).commutes a).symm
      _ = algebraMap F E (algebraMap k F a) := by rw [hcomm, i.commutes]
  obtain ⟨m, v₀, hv₀⟩ := exists_filtered_generators P φ hP hφ hfin
  let v : Fin m → B := fun l => Ideal.Quotient.mk P (v₀ l)
  have hv (n : ℕ) (x : B) (hx : x ∈ quotientDegreeLE P n) :
      ∃ a : Fin m → A, (∀ l, a l ∈ quotientDegreeLE Q n) ∧ ∑ l, g (a l) * v l = x := by
    obtain ⟨a, ha, he⟩ := hv₀ n x hx
    refine ⟨(Ideal.Quotient.mk Q) ∘ a, fun l => mk_mem_quotientDegreeLE (ha l), ?_⟩
    change (∑ l, Ideal.Quotient.mk P (φ (a l)) * Ideal.Quotient.mk P (v₀ l)) = x
    simpa only [map_mul] using he
  let V := Submodule.span F (Set.range (j ∘ v))
  have hV (x : B) : j x ∈ V := by
    obtain ⟨n, hn⟩ := exists_mem_quotientDegreeLE P x
    obtain ⟨a, _, rfl⟩ := hv n x hn
    rw [map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_mul, hcomm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))
  have htop : V = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective B x
    obtain ⟨c, a, ha, he⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul A p
      (nonZeroDivisors.ne_zero hq)
    have hq' : j q ≠ 0 := (map_ne_zero_iff j hj).mpr (nonZeroDivisors.ne_zero hq)
    have ha' : i a ≠ 0 := (map_ne_zero_iff i hi).mpr ha
    change j p / j q ∈ V
    have hfrac : j p / j q = j c / algebraMap F E (i a) := by
      apply (div_eq_div_iff hq' ((map_ne_zero (algebraMap F E)).2 ha')).mpr
      have h := congrArg j he
      change j (g a * p) = j (q * c) at h
      simpa only [map_mul, hcomm, mul_comm] using h
    rw [hfrac, div_eq_inv_mul, ← map_inv₀, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hV c)
  have : Module.Finite F V := Module.Finite.span_of_finite F (Set.finite_range _)
  have : FiniteDimensional F E := Module.Finite.of_surjective V.subtype
    (fun x => ⟨⟨x, htop.symm ▸ Submodule.mem_top⟩, rfl⟩)
  let e := Module.Basis.ofSpan htop.ge
  let := FiniteDimensional.fintypeBasisIndex e
  have he (r : _) : ∃ u : B, j u = e r := by
    obtain ⟨l, hl⟩ := Module.Basis.ofSpan_subset htop.ge (Set.mem_range_self r)
    exact ⟨v l, hl⟩
  choose u hu using he
  have hg₁ (l : Fin 2) : g (Ideal.Quotient.mk Q (MvPolynomial.X l)) ∈ quotientDegreeLE P 1 :=
    mk_mem_quotientDegreeLE (hφ l).totalDegree_le
  obtain ⟨C₁, h₁⟩ := lower_bound g i j hi hcomm hg₁ e u hu
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun z : Fin m × _ => e.equivFun (j (v z.1)) z.2)
  have hb (l : Fin m) (r : _) : ∃ b : A, i b = i d * e.equivFun (j (v l)) r := by
    obtain ⟨b, hb⟩ := hd (l, r)
    refine ⟨b, ?_⟩
    change algebraMap A F b = algebraMap A F (d : A) * e.equivFun (j (v l)) r
    simpa only [Algebra.smul_def] using hb
  choose b hb using hb
  have hd' : i d ≠ 0 := (map_ne_zero_iff i hi).mpr (nonZeroDivisors.ne_zero d.property)
  obtain ⟨C₂, h₂⟩ := upper_bound g i j hi hj hcomm e v hv hd' b hb
  have hr : Module.finrank F E = Fintype.card _ := Module.finrank_eq_card_basis e
  rw [← hr] at h₁ h₂
  have hdeg := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective g hfin hg
  have h := degree_of_bounds (Module.finrank_pos (R := F) (M := E)).ne' hdeg h₁ h₂
  have hplane : affineDegree Q = 1 := by
    rw [show Q = ⊥ from hker, affineDegree_bot]
  rw [hplane, mul_one] at h
  rw [residueDegree, dite_eq_left hprime]
  exact h
end
end K1_13_6_3_5_3_3_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_4
noncomputable section
open Filter MvPolynomial Polynomial
open scoped BigOperators
variable {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]
variable {I : Ideal (MvPolynomial σ k)} {J : Ideal (MvPolynomial τ k)}
private abbrev Piece (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (n : ℕ) :=
  (quotientDegreeLE J n).map g.toLinearMap
private theorem degreeShift [IsDomain (MvPolynomial σ k ⧸ I)]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (i : τ) {ℓ : MvPolynomial σ k}
    (hℓ : g (Ideal.Quotient.mk J (MvPolynomial.X i)) = Ideal.Quotient.mk I ℓ)
    (hb : ∀ x, ∃ a b, g b ≠ 0 ∧ g b * x = g a)
    (hr : ValueReduction I ℓ) :
    ∃ C : ℕ, ∀ n : ℕ, affineHilbertFunction I n ≤ affineHilbertFunction J (n + C) := by
  classical
  obtain ⟨N, hred⟩ := hr
  let B := Module.finBasis k (quotientDegreeLE I N)
  choose a b hb₀ hab using fun j ↦ hb (B j : MvPolynomial σ k ⧸ I)
  let d := ∏ j, b j
  let other := fun j ↦ ∏ r ∈ Finset.univ.erase j, b r
  have hd (j : Fin (Module.finrank k (quotientDegreeLE I N))) : d = other j * b j := by
    exact (Finset.prod_erase_mul _ b (Finset.mem_univ j)).symm
  have hd₀ : g d ≠ 0 := by
    rw [show g d = ∏ j, g (b j) by simp [d, map_prod]]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb₀ j
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (other j * a j)
  obtain ⟨C, hC⟩ := Finite.exists_le levels
  have hbase (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientDegreeLE I N) :
      g d * x ∈ Piece g C := by
    let z : quotientDegreeLE I N := ⟨x, hx⟩
    have hz : (∑ j, (B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) = x := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg (quotientDegreeLE I N).subtype (B.sum_repr z)
    rw [← hz, Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hmul : g d * (B j : MvPolynomial σ k ⧸ I) = g (other j * a j) := by
      rw [hd j, map_mul, mul_assoc, hab j, ← map_mul]
    rw [show g d * ((B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) =
      (B.repr z j) • (g d * (B j : MvPolynomial σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d) (B j : MvPolynomial σ k ⧸ I), hmul]
    apply Submodule.smul_mem
    exact Submodule.mem_map.mpr ⟨_, quotientDegreeLE_mono J (hC j) (hlevels j), rfl⟩
  have hstep (n : ℕ) (hn : N ≤ n) (ih : ∀ x ∈ quotientDegreeLE I n, g d * x ∈ Piece g (n + C)) :
      ∀ x ∈ quotientDegreeLE I (n + 1), g d * x ∈ Piece g (n + 1 + C) := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hred n hn x hx
    obtain ⟨s, hs, he⟩ := Submodule.mem_map.mp (ih v hv)
    change g s = g d * v at he
    rw [mul_add, mul_left_comm (g d), ← hℓ]
    apply Submodule.add_mem
    · exact Submodule.map_mono (quotientDegreeLE_mono J (by omega)) (ih u hu)
    · change g _ * (g d * v) ∈ _
      rw [← he, ← map_mul]
      exact Submodule.mem_map.mpr ⟨_, by
        simpa only [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using
          mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs, rfl⟩
  have hall (n : ℕ) : ∀ x ∈ quotientDegreeLE I n, g d * x ∈ Piece g (n + C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (quotientDegreeLE_mono I (Nat.zero_le N) hx)
    | succ n ih =>
      by_cases hn : N ≤ n
      · exact hstep n hn ih
      · intro x hx
        exact Submodule.map_mono (quotientDegreeLE_mono J (Nat.le_add_left C _))
          (hbase x (quotientDegreeLE_mono I (by omega) hx))
  refine ⟨C, fun n ↦ ?_⟩
  let mult := (LinearMap.mulLeft k (g d)).comp (quotientDegreeLE I n).subtype
  let m : quotientDegreeLE I n →ₗ[k] Piece g (n + C) :=
    mult.codRestrict (Piece g (n + C)) (fun x ↦ hall n x x.property)
  have hm : Function.Injective m := by
    intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀ hd₀
    exact congrArg Subtype.val hxy
  have hfin : Module.Finite k (Piece g (n + C)) := by
    unfold Piece
    infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hm).trans
    (Submodule.finrank_map_le _ _)
theorem degree_eq_of_valueReduction [IsDomain (MvPolynomial σ k ⧸ I)]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (i : τ) {ℓ : MvPolynomial σ k}
    (hℓ : g (Ideal.Quotient.mk J (MvPolynomial.X i)) = Ideal.Quotient.mk I ℓ)
    (hlin : ∀ j, g (Ideal.Quotient.mk J (MvPolynomial.X j)) ∈ quotientDegreeLE I 1)
    (hb : ∀ x, ∃ a b, g b ≠ 0 ∧ g b * x = g a)
    (hr : ValueReduction I ℓ) : affineDegree I = affineDegree J := by
  obtain ⟨C, hupper⟩ := degreeShift g i hℓ hb hr
  have hlower (n : ℕ) : affineHilbertFunction J n ≤ affineHilbertFunction I n := by
    simpa only [one_mul] using affineHilbertFunction_le_of_injective g hg hlin n
  let P := affineHilbertPolynomial I
  let Q := affineHilbertPolynomial J
  have hshift : Tendsto (fun n : ℕ ↦ n + C) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_right n C) tendsto_id
  have hbound : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ (taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I,
      hshift.eventually (eventually_eval_affineHilbertPolynomial J)] with n hn hnC
    rw [taylor_eval, ← Nat.cast_add, hn, hnC]
    exact_mod_cast hupper n
  have hbound' : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I,
      eventually_eval_affineHilbertPolynomial J] with n hn hn'
    rw [hn, hn']
    exact_mod_cast hlower n
  have hle := natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hbound
  have hge := natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg J) hbound'
  have hdeg : P.natDegree = Q.natDegree :=
    (hle.1.trans_eq (natDegree_taylor Q _)).antisymm hge.1
  have hlc : P.leadingCoeff = Q.leadingCoeff := by
    apply le_antisymm _ (hge.2 hdeg.symm)
    simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (natDegree_taylor Q _).symm)
  change (P.natDegree.factorial : ℚ) * P.leadingCoeff =
    (Q.natDegree.factorial : ℚ) * Q.leadingCoeff
  rw [hdeg, hlc]
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 80000
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
open Algebra.TensorProduct
variable {k E σ : Type} [Field k] [Field E] [Algebra k E]
abbrev scalarExtension (I : Ideal (MvPolynomial σ k)) :=
  I.map (MvPolynomial.map (algebraMap k E))
def coneRingInclude (I : Ideal (MvPolynomial σ k)) :
    ConeRing I →+* ConeRing (scalarExtension (E := E) I) :=
  Ideal.quotientMap _ (MvPolynomial.map (algebraMap k E)) Ideal.le_comap_map
private def quotientTensor (I : Ideal (MvPolynomial σ k)) :
    E ⊗[k] ConeRing I ≃ₐ[E] ConeRing (scalarExtension (E := E) I) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let ι : MvPolynomial σ k →ₐ[k] E ⊗[k] MvPolynomial σ k := includeRight
  have hcomp : e.toRingHom.comp ι.toRingHom = MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm
set_option backward.isDefEq.respectTransparency false in
private theorem quotientTensor_tmul (I : Ideal (MvPolynomial σ k))
    (z : E) (p : MvPolynomial σ k) :
    quotientTensor I (z ⊗ₜ[k] Ideal.Quotient.mk I p) =
      z • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap k E) p) := by
  simp [quotientTensor]
  exact map_smul (Ideal.Quotient.mkₐ E (scalarExtension (E := E) I)).toLinearMap z _
theorem coneRing_eval_injective (I : Ideal (MvPolynomial σ k)) {z : E}
    (hz : Transcendental k z) :
    Function.Injective (Polynomial.eval₂RingHom (coneRingInclude (E := E) I)
      (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)) := by
  let A := ConeRing I
  let j : (Polynomial k) →ₐ[k] E := Polynomial.aeval z
  let b : (Polynomial A) ≃ₐ[k] A ⊗[k] (Polynomial k) := polyEquivTensor k A
  let m : A ⊗[k] (Polynomial k) →ₐ[k] A ⊗[k] E := Algebra.TensorProduct.map (AlgHom.id k A) j
  let c : A ⊗[k] E ≃ₐ[k] E ⊗[k] A := Algebra.TensorProduct.comm k A E
  let e := quotientTensor (E := E) I
  let H : (Polynomial A) →+* ConeRing (scalarExtension (E := E) I) :=
    e.toRingHom.comp (c.toRingHom.comp (m.toRingHom.comp b.toRingHom))
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
      (transcendental_iff_injective.mp hz)
  have hH : H = Polynomial.eval₂RingHom (coneRingInclude (E := E) I)
      (algebraMap E (ConeRing (scalarExtension (E := E) I)) z) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      change e (c (m (b (Polynomial.C (Ideal.Quotient.mk I p))))) = _
      have hC : c (m (b (Polynomial.C (Ideal.Quotient.mk I p)))) =
          (1 : E) ⊗ₜ[k] Ideal.Quotient.mk I p := by simp [b, c, m, j]
      rw [hC, show e _ = _ from quotientTensor_tmul (E := E) I 1 p, one_smul,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · change e (c (m (b Polynomial.X))) = _
      have hX : c (m (b Polynomial.X)) = z ⊗ₜ[k] Ideal.Quotient.mk I 1 := by
        simp [b, c, m, j]
      rw [hX, show e _ = _ from quotientTensor_tmul I z 1]
      simp only [map_one]
      change z • (1 : ConeRing (scalarExtension (E := E) I)) =
        (Polynomial.X : (Polynomial A)).eval₂ (coneRingInclude (E := E) I)
          (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)
      rw [Polynomial.eval₂_X]
      exact (Algebra.algebraMap_eq_smul_one (A := ConeRing (scalarExtension (E := E) I)) z).symm
  rw [← hH]
  exact e.injective.comp (c.injective.comp (hm.comp b.injective))
theorem coneRingInclude_injective (I : Ideal (MvPolynomial σ k)) {z : E}
    (hz : Transcendental k z) : Function.Injective (coneRingInclude (E := E) I) := by
  rw [← Polynomial.eval₂RingHom_comp_C (coneRingInclude (E := E) I)
    (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)]
  exact (coneRing_eval_injective I hz).comp Polynomial.C_injective
theorem coneFrac_eval_injective (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    [(scalarExtension (E := E) I).IsPrime] {z : E} (hz : Transcendental k z) :
    Function.Injective (Polynomial.eval₂RingHom
      (IsFractionRing.map (coneRingInclude_injective I hz) :
        ConeFrac I →+* ConeFrac (scalarExtension (E := E) I))
      (algebraMap E (ConeFrac (scalarExtension (E := E) I)) z)) := by
  let A := ConeRing I
  let : IsDomain A := (Ideal.Quotient.isDomain_iff_prime I).2 inferInstance
  let B := ConeRing (scalarExtension (E := E) I)
  let C := ConeFrac (scalarExtension (E := E) I)
  let j : ConeFrac I →+* C := IsFractionRing.map (coneRingInclude_injective I hz)
  let x := algebraMap E C z
  let f : A →+* B := coneRingInclude (E := E) I
  have hcomp : j.comp (algebraMap A (ConeFrac I)) = (algebraMap B C).comp f :=
    IsLocalization.map_comp (M := A⁰) (T := B⁰) _
  have he (p : (Polynomial A)) :
      p.eval₂ (j.comp (algebraMap A (ConeFrac I))) x =
        algebraMap B C (p.eval₂ f (algebraMap E B z)) := by
    rw [Polynomial.hom_eval₂, ← hcomp, ← IsScalarTower.algebraMap_apply E B C]
  change Function.Injective (Polynomial.eval₂RingHom j x)
  intro p q hpq
  have hp : (p - q).eval₂ j x = 0 :=
    (Polynomial.eval₂_sub (p := p) (q := q) j (x := x)).trans (sub_eq_zero.mpr hpq)
  have heval := (he (IsLocalization.integerNormalization A⁰ (p - q))).symm.trans
    (IsLocalization.integerNormalization_eval₂_eq_zero A⁰ j (p - q) hp)
  have hzero : (IsLocalization.integerNormalization A⁰ (p - q)).eval₂ f (algebraMap E B z) = 0 :=
    (IsFractionRing.injective B C) (heval.trans (map_zero (algebraMap B C)).symm)
  have hnorm : IsLocalization.integerNormalization A⁰ (p - q) = 0 := by
    apply coneRing_eval_injective I hz
    change (IsLocalization.integerNormalization A⁰ (p - q)).eval₂ f (algebraMap E B z) =
      (0 : (Polynomial A)).eval₂ f (algebraMap E B z)
    exact hzero.trans (Polynomial.eval₂_zero _ _).symm
  exact sub_eq_zero.mp ((IsFractionRing.integerNormalization_eq_zero_iff (A := A)).mp hnorm)
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3
open scoped BigOperators Polynomial
private def universalPolynomial : (Polynomial CoeffRing) :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (MvPolynomial.X j)
private def universalTrajectory (R : Row 4) : (Polynomial CoeffRing) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C)
    (fun i => Polynomial.hasseDeriv i.val universalPolynomial) R
private def coeffEval {F : Type*} [Field F] (k : Geom →+* F) (U : (Polynomial F)) :
    CoeffRing →+* F :=
  MvPolynomial.eval₂Hom k (fun j => U.coeff j.val)
private theorem map_universalPolynomial {F : Type*} [Field F]
    (k : Geom →+* F) {U : (Polynomial F)} (hd : U.natDegree < taylorLength) :
    universalPolynomial.map (coeffEval k U) = U := by
  rw [← Polynomial.coe_mapRingHom]
  simp only [universalPolynomial, map_sum, Polynomial.coe_mapRingHom, Polynomial.map_monomial,
    coeffEval, MvPolynomial.eval₂Hom_X']
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (U.coeff n))]
  exact (U.as_sum_range' _ hd).symm
private theorem map_universalTrajectory {F : Type*} [Field F]
    (k : Geom →+* F) {U : (Polynomial F)} (hd : U.natDegree < taylorLength) (R : Row 4) :
    (universalTrajectory R).map (coeffEval k U) = trajectory k R U := by
  rw [← Polynomial.coe_mapRingHom]
  rw [universalTrajectory, MvPolynomial.hom_eval₂, trajectory]
  refine congrArg₂ (fun f g => MvPolynomial.eval₂ f g R) ?_ ?_
  · rw [Polynomial.mapRingHom_comp]
    congr 1
    ext a
    simp [coeffEval]
  · funext i
    rw [Polynomial.coe_mapRingHom, ← Polynomial.hasseDeriv_map, map_universalPolynomial k hd]
private def evaluateFresh : (Polynomial CoeffRing) →+* FreshCoeffRing :=
  Polynomial.eval₂RingHom (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
private theorem evaluateFresh_hasse (i : ℕ) :
    evaluateFresh (Polynomial.hasseDeriv i universalPolynomial) =
      jetLinear genericArgument i := by
  classical
  simp only [universalPolynomial, map_sum, jetLinear]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.hasseDeriv_monomial]
  simp only [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    map_mul, map_natCast, MvPolynomial.map_X]
  rw [map_pow]
  ac_rfl
private theorem evaluateFresh_trajectory (R : Row 4) :
    evaluateFresh (universalTrajectory R) = freshJetMap (toGeneric R) := by
  change (evaluateFresh.comp
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
        (fun i : Fin 4 => Polynomial.hasseDeriv i.val universalPolynomial))) R =
    (freshJetMap.comp (MvPolynomial.map genericCoeffs)) R
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, freshJetMap]
    change Polynomial.eval₂ (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
        (a.map MvPolynomial.C) = MvPolynomial.C (genericCoeffs a)
    have hm : (MvPolynomial.map geomConstants).comp (MvPolynomial.C : Geom →+* CoeffRing) =
        (MvPolynomial.C : GeoField →+* FreshCoeffRing).comp geomConstants := by
      apply RingHom.ext
      simp
    rw [Polynomial.eval₂_map, hm, ← Polynomial.hom_eval₂]
    have hx : Polynomial.eval₂RingHom geomConstants genericArgument = genericCoeffs := by
      apply Polynomial.ringHom_ext
      · intro b
        exact Polynomial.eval₂_C _ _
      · exact Polynomial.eval₂_X _ _
    change MvPolynomial.C ((Polynomial.eval₂RingHom geomConstants genericArgument) a) = _
    rw [hx]
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
      freshJetMap] using evaluateFresh_hasse i.val
private theorem fresh_mem_of_trajectory_zero {F : Type*} [Field F] (k : Geom →+* F)
    {U : (Polynomial F)} (hd : U.natDegree < taylorLength) (R : Row 4)
    (hR : trajectory k R U = 0) :
    toGeneric R ∈ freshImage (coefficientKernel k U) := by
  change freshJetMap (toGeneric R) ∈ extendIdeal (coefficientKernel k U)
  rw [← evaluateFresh_trajectory]
  let T := universalTrajectory R
  have hz : T.map (coeffEval k U) = 0 := (map_universalTrajectory k hd R).trans hR
  have hc (n : ℕ) : T.coeff n ∈ coefficientKernel k U := by
    change coeffEval k U (T.coeff n) = 0
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
      congrArg (fun V : (Polynomial F) => V.coeff n) hz
  change evaluateFresh T ∈ _
  rw [congrArg evaluateFresh T.as_sum_range, map_sum]
  apply Ideal.sum_mem
  intro n _
  rw [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc n))
private def oldCoeffs (P : JetIdeal) : GeoField →+* JetField P :=
  (onComponent P).comp MvPolynomial.C
private def oldEval (P : JetIdeal) (U : (Polynomial (JetField P))) : FreshCoeffRing →+* JetField P :=
  MvPolynomial.eval₂Hom (oldCoeffs P) (fun j => U.coeff j.val)
private theorem oldEval_jetLinear (P : JetIdeal) [P.IsPrime] {U : (Polynomial (JetField P))}
    (hd : U.natDegree < taylorLength) (i : ℕ) :
    oldEval P U (jetLinear genericArgument i) =
      (Polynomial.hasseDeriv i U).eval (oldCoeffs P genericArgument) := by
  have hsum : U = ∑ j : Fin taylorLength, Polynomial.monomial j.val (U.coeff j.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (U.coeff n))]
    exact U.as_sum_range' _ hd
  rw [congrArg (fun V => (Polynomial.hasseDeriv i V).eval (oldCoeffs P genericArgument)) hsum]
  simp only [jetLinear, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, map_mul, oldEval,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_natCast, map_pow]
  ring
private theorem fresh_le_source {f Q g : Row 4} {P : JetIdeal} [P.IsPrime]
    {U : (Polynomial (JetField P))} (h : Integrated f Q g P U) :
    freshImage (coefficientKernel (componentConstants P) U) ≤ P := by
  have hmap : (oldEval P U).comp (MvPolynomial.map geomConstants) =
      coeffEval (componentConstants P) U := by
    ext a <;> simp [oldEval, oldCoeffs, coeffEval, componentConstants]
  have hkill : extendIdeal (coefficientKernel (componentConstants P) U) ≤
      RingHom.ker (oldEval P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (DFunLike.congr_fun hmap a).trans ha
  have hcomp : (oldEval P U).comp freshJetMap = onComponent P := by
    ext a
    · simp [oldEval, freshJetMap, oldCoeffs]
    · rw [RingHom.comp_apply, freshJetMap, MvPolynomial.eval₂Hom_X',
        oldEval_jetLinear P h.degree]
      exact h.initial a
  intro a ha
  have hz : onComponent P a = 0 :=
    (DFunLike.congr_fun hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (GeoJets ⧸ P) (JetField P)
  exact hz.trans (map_zero _).symm
theorem trajectory_to_fresh {f Q g : Row 4} {P : JetIdeal} [P.IsPrime]
    {U : (Polynomial (JetField P))} (h : Integrated f Q g P U)
    (hsep : toGeneric (separant g) ∉ P) :
    let A := coefficientKernel (componentConstants P) U
    intersectionIdeal f Q ≤ freshImage A ∧ freshImage A ≤ P ∧
      toGeneric g ∈ freshImage A ∧ toGeneric (separant g) ∉ freshImage A := by
  dsimp only
  have hle := fresh_le_source h
  refine ⟨?_, hle, fresh_mem_of_trajectory_zero _ h.degree _ h.chart, fun hs => hsep (hle hs)⟩
  rw [intersectionIdeal, Ideal.span_le]
  rintro _ (hs | hs)
  · exact hs ▸ fresh_mem_of_trajectory_zero _ h.degree _ h.factor
  · rcases hs with rfl
    exact fresh_mem_of_trajectory_zero _ h.degree _ h.cutter
end
end K1_13_6_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13 K1_13_6
abbrev SepField := separableClosure GenericField GeoField
abbrev SepJets := MvPolynomial (Fin 4) SepField
def sepToGeo : SepJets →+* GeoJets :=
  MvPolynomial.map (algebraMap SepField GeoField)
def rowToSep : Row 4 →+* SepJets :=
  MvPolynomial.map ((algebraMap GenericField SepField).comp (algebraMap (Polynomial Geom) GenericField))
@[simp] theorem sepToGeo_rowToSep (U : Row 4) : sepToGeo (rowToSep U) = toGeneric U := by
  rw [sepToGeo, rowToSep, MvPolynomial.map_map, toGeneric, genericCoeffs,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq GenericField SepField GeoField]
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13_6 K1_13_6_3
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 2000
set_option linter.style.haveILetI false
namespace K1_13_6_3_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped BigOperators
theorem eval₂_scale {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (f : k →+* K) (x : σ → K) (t : K) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : eval₂ f (fun i ↦ t * x i) p = t ^ n * eval₂ f x p := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (t * x i) ^ d i) = t ^ n * ∏ i : σ, x i ^ d i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring
theorem eval_scale_zero {k σ : Type*} [Field k] [Fintype σ]
    (x : σ → k) (t : k) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) (hx : eval x p = 0) : eval (fun i ↦ t * x i) p = 0 :=
  (eval₂_scale (RingHom.id k) x t hp).trans (mul_eq_zero_of_right _ hx)
theorem map_boundary_generator {k K σ : Type*} [Field k] [Field K]
    (f : k →+* K) (A : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ k}
    {n : ℕ} (hp : p ∈ A) (hn : p.totalDegree ≤ n) :
    MvPolynomial.map f (homogeneousComponent n p) ∈ boundaryIdeal (A.map (MvPolynomial.map f)) := by
  have he : MvPolynomial.map f (homogeneousComponent n p) =
      homogeneousComponent n (MvPolynomial.map f p) := by
    ext d
    by_cases hd : d.degree = n <;> simp only [coeff_homogeneousComponent, coeff_map, hd, ite_true, ite_false, map_zero]
  have hd : (MvPolynomial.map f p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (support_map_subset f p)
  exact Ideal.subset_span ⟨MvPolynomial.map f p, n, Ideal.mem_map_of_mem _ hp, hd.trans hn, he⟩
theorem linear_sum_homogeneous {k σ : Type*} [Field k] [Fintype σ] (c : σ → k) :
    (∑ j : σ, MvPolynomial.C (c j) * MvPolynomial.X j).IsHomogeneous 1 :=
  (homogeneousSubmodule σ k 1).sum_mem fun j _ ↦ isHomogeneous_C_mul_X (c j) j
theorem jetLinear_homogeneous (a : GeoField) (r : ℕ) : (jetLinear a r).IsHomogeneous 1 :=
  linear_sum_homogeneous fun j : Fin taylorLength ↦ (j.val.choose r : GeoField) * a ^ (j.val - r)
private theorem normalize_boundary (A : CoeffIdeal) {x : Fin taylorLength → GeoField}
    (hx : x ∈ zeroLocus GeoField (boundaryIdeal (extendIdeal A)))
    {i : Fin taylorLength} (hi : x i ≠ 0) :
    letI : Algebra Geom GeoField := geomConstants.toAlgebra
    (fun j ↦ (x i)⁻¹ * x j) ∈ zeroLocus GeoField (boundaryChart A i) := by
  letI : Algebra Geom GeoField := geomConstants.toAlgebra
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  change boundaryChart A i ≤ RingHom.ker (eval₂Hom geomConstants b)
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    have he := hx (MvPolynomial.map geomConstants (homogeneousComponent n p))
      (map_boundary_generator geomConstants A hp hn)
    change (MvPolynomial.map geomConstants (homogeneousComponent n p)).eval x = 0 at he
    rw [eval_map] at he
    change eval₂ geomConstants b (homogeneousComponent n p) = 0
    rw [eval₂_scale geomConstants x ((x i)⁻¹) (homogeneousComponent_isHomogeneous ..), he,
      mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ geomConstants b (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
theorem finite_chart_coordinates {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Finite σ] (J : Ideal (MvPolynomial σ k)) (hJ : dimension J = 0)
    {x : σ → K} (hx : x ∈ zeroLocus K J) (j : σ) : ∃ c : k, algebraMap k K c = x j := by
  letI : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] K := Ideal.Quotient.liftₐ J (aeval x) hx
  have h : IsIntegral k (x j) := by
    have hJX := (Algebra.IsIntegral.isIntegral (R := k) (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
    change IsIntegral k (aeval x (MvPolynomial.X j)) at hJX
    simpa only [aeval_X] using hJX
  apply h.mem_range_algHom_of_minpoly_splits (K := k) _ (Algebra.ofId k K)
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
    IsAlgClosed.splits (minpoly k (x j))
theorem polynomial_value_ne_zero {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (f : Polynomial k →+* K) (hf : Function.Injective f) (d : σ → ℕ) (hd : Function.Injective d)
    (a : σ → k) {i : σ} (hi : a i ≠ 0) :
    (∑ j : σ, f Polynomial.X ^ d j * f (Polynomial.C (a j))) ≠ 0 := by
  classical
  let P : Polynomial k := ∑ j : σ, Polynomial.monomial (d j) (a j)
  have hcoeff : P.coeff (d i) = a i := by
    rw [show P.coeff (d i) = ∑ j : σ, (Polynomial.monomial (d j) (a j)).coeff (d i) by
      exact map_sum (Polynomial.lcoeff k (d i)) _ _]
    rw [Finset.sum_eq_single i]
    · exact Polynomial.coeff_monomial_same _ _
    · intro j _ hj
      exact Polynomial.coeff_monomial_of_ne _ (fun h ↦ hj (hd h.symm))
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hp : P ≠ 0 := by
    intro he
    exact hi (by rw [← hcoeff, he, Polynomial.coeff_zero])
  have he : f P = ∑ j : σ, f Polynomial.X ^ d j * f (Polynomial.C (a j)) := by
    simp only [P, map_sum, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, mul_comm]
  rw [← he]
  exact fun h ↦ hp (hf (h.trans f.map_zero.symm))
private theorem fresh_value_ne_zero {a : Fin taylorLength → Geom} {i : Fin taylorLength}
    (hi : a i ≠ 0) : eval (geomConstants ∘ a) (jetLinear genericArgument 0) ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
  have hne := polynomial_value_ne_zero genericCoeffs hinj Fin.val Fin.val_injective a hi
  intro h
  apply hne
  rw [← h]
  unfold jetLinear
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul, eval_C, eval_X, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Function.comp_apply, genericArgument, geomConstants, RingHom.comp_apply]
theorem noBoundaryZero_of_charts (A : CoeffIdeal)
    (hA : ∀ i, dimension (boundaryChart A i) = 0) :
    NoBoundaryZero (extendIdeal A) (jetLinear genericArgument 0) := by
  classical
  letI : Algebra Geom GeoField := geomConstants.toAlgebra
  intro x hx hval
  funext i
  change x i = 0
  by_contra hi
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  have hb : b ∈ zeroLocus GeoField (boundaryChart A i) := normalize_boundary A hx hi
  choose a ha using fun j ↦ finite_chart_coordinates (boundaryChart A i) (hA i) hb j
  have he : geomConstants ∘ a = b := funext ha
  have hai : a i ≠ 0 := by
    intro ha₀
    have hz := ha i
    change geomConstants (a i) = (x i)⁻¹ * x i at hz
    rw [ha₀, map_zero, inv_mul_cancel₀ hi] at hz
    exact zero_ne_one hz
  apply fresh_value_ne_zero hai
  rw [he]
  exact eval_scale_zero x ((x i)⁻¹) (jetLinear_homogeneous genericArgument 0) hval
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
def c1 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime →
    (extendIdeal A).IsPrime ∧ dimension (extendIdeal A) = dimension A ∧
      (extendIdeal A).comap (MvPolynomial.map geomConstants) = A
def c2 : Prop :=
  ∀ (g : Row 4) (i : Fin taylorLength), ∃ (u : GeoJets) (e : ℕ),
    ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
      toGeneric g ∈ freshImage A → toGeneric (separant g) ∉ freshImage A →
      MvPolynomial.X i * freshJetMap (toGeneric (separant g)) ^ e -
        freshJetMap u ∈ extendIdeal A
end
end K1_13_6_3_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_2_1
open K1_13_6_3_5_3_2 IntermediateField
open scoped algebraAdjoinAdjoin Polynomial
noncomputable section
private def frobeniusRange (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] (p n : ℕ) [ExpChar k p] [ExpChar A p] : Subalgebra k A :=
  { (iterateFrobenius A p n).range.toSubsemiring with
    algebraMap_mem' r := by
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq r (expChar_pow_pos k p n)
      exact ⟨algebraMap k A s, by rw [iterateFrobenius_def, ← map_pow, hs]⟩ }
private theorem finite_over_frobeniusRange (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] (p n : ℕ) [ExpChar k p] [ExpChar A p]
    (z : A) (hz : Algebra.adjoin k ({z} : Set A) = ⊤) :
    Module.Finite (frobeniusRange k A p n) A := by
  let S := frobeniusRange k A p n
  let T := Algebra.adjoin S ({z} : Set A)
  have hi : IsIntegral S z := by
    apply IsIntegral.of_pow (expChar_pow_pos A p n)
    let s : S := ⟨z ^ p ^ n, ⟨z, rfl⟩⟩
    exact isIntegral_algebraMap (x := s)
  have ht : T = ⊤ := by
    have hle : Algebra.adjoin k ({z} : Set A) ≤ T.restrictScalars k :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton S z))
    rw [hz] at hle
    exact le_antisymm le_top fun a _ => hle (Algebra.mem_top (R := k) (x := a))
  have hfg : T.toSubmodule.FG := hi.fg_adjoin_singleton
  rw [ht, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩
theorem proof : K1_13_6_3_5_3_2.c1 := by
  intro k L _ _ _ _ x hx hfin
  let A := ParameterRing k L x
  let K := IntermediateField.adjoin k ({x} : Set L)
  let E := separableClosure K L
  let B := Normalization k L x
  let C := integralClosure A E
  have : Module.Finite K L := hfin
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  let p := ringExpChar L
  have : ExpChar L p := ringExpChar.expChar L
  have : ExpChar k p := (algebraMap k L).expChar (algebraMap k L).injective p
  have : ExpChar A p := (algebraMap A L).expChar Subtype.val_injective p
  have : ExpChar E p := (algebraMap E L).expChar (algebraMap E L).injective p
  let n := IsPurelyInseparable.exponent E L
  let S := frobeniusRange k A p n
  let z : A := ⟨x, Algebra.self_mem_adjoin_singleton k x⟩
  have hz : Algebra.adjoin k ({z} : Set A) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    intro a
    obtain ⟨f, hf⟩ := (Polynomial.algEquivOfTranscendental k x hx).surjective a
    exact ⟨f, hf⟩
  have : Module.Finite S A := finite_over_frobeniusRange k A p n z hz
  let σ : A →+* S := (iterateFrobenius A p n).rangeRestrict
  let e : A ≃+* S := RingEquiv.ofBijective σ
    ⟨fun _ _ h => iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have : RingHomInvPair (e : A →+* S) (e.symm : S →+* A) := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair (e.symm : S →+* A) (e : A →+* S) := RingHomInvPair.of_ringEquiv e.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv A e
  have : Module.Finite S C := Module.Finite.trans A C
  have : IsNoetherian S C := inferInstance
  let F : L →+* E := IsPurelyInseparable.iterateFrobenius E L p (n := n) le_rfl
  have hF (b : L) : algebraMap E L (F b) = b ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b : B) : F b.val ∈ integralClosure A E := by
    change IsIntegral A (F b.val)
    apply (IntermediateField.coe_isIntegral_iff (R := A)).mp
    change IsIntegral A (algebraMap E L (F b.val))
    rw [hF]
    exact (show IsIntegral A b.val from b.property).pow _
  let g : B →+* C :=
    (F.comp (integralClosure A L).val.toRingHom).codRestrict (integralClosure A E).toSubring hmem
  let f : B →ₛₗ[(e : A →+* S)] C :=
    { g with
      map_smul' a b := by
        apply Subtype.ext
        apply (algebraMap E L).injective
        change algebraMap E L (F (algebraMap A L a * b.val)) =
          algebraMap E L (algebraMap A E (a ^ p ^ n) * F b.val)
        rw [hF, mul_pow, map_mul, ← IsScalarTower.algebraMap_apply A E L, map_pow, hF] }
  apply Module.Finite.of_injective f
  intro b b' hb
  apply Subtype.ext
  apply iterateFrobenius_inj L p n
  change b.val ^ p ^ n = b'.val ^ p ^ n
  rw [← hF, ← hF]
  exact congrArg (fun c : C => algebraMap E L c.val) hb
end
end K1_13_6_3_5_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3
def c1 : Prop :=
  ∀ (f Q : Row 4) (surface : JetIdeal)
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    cycleLength (intersectionIdeal f Q) surface hz.isPrime < (K1.p : ℕ∞) →
    (surface.comap sepToGeo).map sepToGeo = surface
def c2 : Prop :=
  ∀ (g : Row 4) (surface : JetIdeal), surface.IsPrime → Invariant g surface →
    ∃ D : Derivation ℤ SepJets SepJets,
      (∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U)) ∧
      (∀ u ∈ surface.comap sepToGeo, D u ∈ surface.comap sepToGeo)
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
open K1_13_6_3_5
variable {U V R S : Type} [CommRing U] [CommRing V] [CommRing R] [CommRing S]
structure SectionPresentation (J : Ideal U) (w : R) where
  toQuotient : R →+* U ⧸ J
  surjective : Function.Surjective toQuotient
  ker_eq : RingHom.ker toQuotient = Ideal.span {w}
def Compatible (g : U →+* V) (f : R →+* S) {J : Ideal U} {I : Ideal V} {w : R}
    (r : SectionPresentation J w) (s : SectionPresentation I (f w)) : Prop :=
  ∃ m : U ⧸ J →+* V ⧸ I,
    m.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk I).comp g ∧
    m.comp r.toQuotient = s.toQuotient.comp f
structure ConeModel {k σ τ : Type} [Field k]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (A : Ideal (MvPolynomial σ k)) where
  F : Type
  [field : Field F]
  [algebra : Algebra k F]
  target : Subalgebra k F
  source : Subalgebra k F
  le : target ≤ source
  targetNoetherian : IsNoetherianRing target
  sourceNoetherian : IsNoetherianRing source
  fraction : IsFractionRing target F
  w : target
  w_ne : w ≠ 0
  targetSection : SectionPresentation (boundaryIdeal (A.comap φ)) w
  sourceSection : SectionPresentation (boundaryIdeal A) (Subalgebra.inclusion le w)
  compatible : Compatible φ.toRingHom (Subalgebra.inclusion le).toRingHom
    targetSection sourceSection
abbrev LocalSection (J p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime p ⧸ J.map (algebraMap R (Localization.AtPrime p))
def weight (J p : Ideal R) : ℕ := by
  classical
  exact if hp : p.IsPrime then
    letI := hp
    (Module.length (Localization.AtPrime p) (LocalSection J p)).toNat
  else 0
def degree (f : R →+* S) (p : Ideal S) : ℕ := by
  classical
  exact if hp : p.IsPrime then
    letI := hp
    letI : (p.comap f).IsPrime := Ideal.IsPrime.comap f
    let g : FractionRing (R ⧸ p.comap f) →+* FractionRing (S ⧸ p) :=
      IsFractionRing.map (Ideal.quotientMap_injective (I := p) (f := f))
    letI := g.toAlgebra
    Module.finrank (FractionRing (R ⧸ p.comap f)) (FractionRing (S ⧸ p))
  else 0
def fibrePrimes [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R) :
    Finset (Ideal S) := by
  classical
  exact J.minimalPrimesFinset.filter (fun p => p.comap f = q)
def fibreWeight [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R) : ℕ :=
  ∑ p ∈ fibrePrimes f J q, weight J p * degree f p
theorem fibre_prime [IsNoetherianRing S] {f : R →+* S} {J : Ideal S} {q : Ideal R}
    (p : fibrePrimes f J q) : (p : Ideal S).IsPrime :=
  (Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp p.property).1).isPrime
theorem fibre_comap [IsNoetherianRing S] {f : R →+* S} {J : Ideal S} {q : Ideal R}
    (p : fibrePrimes f J q) : q = (p : Ideal S).comap f :=
  (Finset.mem_filter.mp p.property).2.symm
def branchLength [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R)
    [q.IsPrime] (p : fibrePrimes f J q) : ℕ∞ :=
  letI : (p : Ideal S).IsPrime := fibre_prime p
  letI := (Localization.localRingHom q (p : Ideal S) f (fibre_comap p)).toAlgebra
  Module.length (Localization.AtPrime q) (LocalSection J (p : Ideal S))
abbrev FractionSubalgebra (L : Type) [CommRing L] := Subalgebra L (FractionRing L)
abbrev SectionQuotient (x : R) (B : Type) [CommRing B] [Algebra R B] :=
  B ⧸ Ideal.span {algebraMap R B x}
def sectionLength (x : R) (B : Type) [CommRing B] [Algebra R B] : ℕ∞ :=
  Module.length R (SectionQuotient x B)
end
end K1_13_6_3_5_5
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
namespace K1_13_6_3_4
noncomputable section
open K1_13_6 K1_13_6_3 MvPolynomial
def c1 : Prop :=
  ∀ A : CoeffIdeal, affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → dimension A = 1 →
    ∀ i : Fin K1_13.taylorLength, dimension (boundaryChart A i) = 0
def c3 : Prop :=
  ∀ I : Ideal FreshCoeffRing,
    NoBoundaryZero I (jetLinear genericArgument 0) →
    ValueReduction I (jetLinear genericArgument 0)
private def jetAlg : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  aeval (fun i : Fin 4 ↦ jetLinear genericArgument i.val)
private theorem jetAlg_apply (p : GeoJets) : jetAlg p = freshJetMap p := rfl
private def jetQuot (A : CoeffIdeal) :
    (GeoJets ⧸ freshImage A) →ₐ[GeoField] (FreshCoeffRing ⧸ extendIdeal A) :=
  Ideal.quotientMapₐ (extendIdeal A) jetAlg (by
    intro p hp
    exact hp)
private theorem jetQuot_mk (A : CoeffIdeal) (p : GeoJets) :
    jetQuot A (Ideal.Quotient.mk (freshImage A) p) = Ideal.Quotient.mk (extendIdeal A) (freshJetMap p) := rfl
private theorem jetQuot_X (A : CoeffIdeal) (j : Fin 4) :
    jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (extendIdeal A) (jetLinear genericArgument j.val) := by
  rw [jetQuot_mk, ← jetAlg_apply]
  exact congrArg (Ideal.Quotient.mk (extendIdeal A)) (aeval_X _ _)
private theorem jetQuot_injective (A : CoeffIdeal) : Function.Injective (jetQuot A) := by
  apply (injective_iff_map_eq_zero (jetQuot A)).mpr
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [jetQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
private theorem birational_quotient {A : CoeffIdeal} (hb : FreshBirational A)
    (x : FreshCoeffRing ⧸ extendIdeal A) :
    ∃ a b, jetQuot A b ≠ 0 ∧ jetQuot A b * x = jetQuot A a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨u, v, hv, huv⟩ := hb p
  refine ⟨Ideal.Quotient.mk _ u, Ideal.Quotient.mk _ v, ?_, ?_⟩
  · rwa [jetQuot_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [jetQuot_mk, jetQuot_mk, mul_comm, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr huv
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_3.c4 := by
  intro A hA hExt hdim hb
  letI := hExt
  have hred := h3 (extendIdeal A) (noBoundaryZero_of_charts A (h2 A hA hdim))
  have hlin (j : Fin 4) :
      jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X j)) ∈
        quotientDegreeLE (extendIdeal A) 1 := by
    rw [jetQuot_X]
    exact mk_mem_quotientDegreeLE (jetLinear_homogeneous genericArgument j.val).totalDegree_le
  have hz : jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X 0)) =
      Ideal.Quotient.mk (extendIdeal A) (jetLinear genericArgument 0) := jetQuot_X A 0
  have he := degree_eq_of_valueReduction (jetQuot A) (jetQuot_injective A) 0 hz hlin
    (birational_quotient hb) hred
  have hext : affineDegree (extendIdeal A) = affineDegree A := by
    unfold affineDegree
    rw [h1 A]
  exact hext.symm.trans he
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_6
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial RingTheory.Sequence
open scoped TensorProduct Pointwise
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem geometryCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp
    (IsFractionRing.injective (K := GenericField) _)
theorem totalDegree_toGeneric (f : Row 4) :
    (toGeneric f).totalDegree = f.totalDegree := by
  unfold totalDegree toGeneric
  rw [support_map_of_injective _ geometryCoeffs_injective]
theorem toGeneric_ne_zero {f : Row 4} (hf : f ≠ 0) : toGeneric f ≠ 0 :=
  fun h => hf (MvPolynomial.map_injective _ geometryCoeffs_injective (h.trans (map_zero _).symm))
theorem geometry_flat :
    Module.Flat (MvPolynomial (Fin 4) GenericField) GeoJets := by
  let R := GenericField
  let B := MvPolynomial (Fin 4) R
  let E := GeoField
  let e : B ⊗[R] E ≃ₐ[B] GeoJets :=
    { __ := ((Algebra.TensorProduct.comm R B E).trans
        ((algebraTensorAlgEquiv (σ := Fin 4) R E).restrictScalars R)).toRingEquiv
      commutes' := fun b => by
        change algebraTensorAlgEquiv R E (1 ⊗ₜ[R] b) = algebraMap B GeoJets b
        simpa only [algebraTensorAlgEquiv_tmul, one_smul] using
          congrFun (congrArg DFunLike.coe (MvPolynomial.algebraMap_def (σ := Fin 4)
            (R := GenericField) (S := GeoField)).symm) b }
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
theorem weaklyRegular_pair_iff {R : Type} [CommRing R] (f Q : R) :
    IsWeaklyRegular R [f, Q] ↔
      IsLeftRegular f ∧ IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f}) Q) := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  have h : f • (⊤ : Submodule R R) = (Ideal.span {f} : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  exact and_congr_right' ((Submodule.quotEquivOfEq _ _ h).isSMulRegular_congr Q)
end
end K1_13_6_3_6
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_4
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5
variable {k σ : Type*} [Field k]
theorem component_mem_boundary {I : Ideal (MvPolynomial σ k)}
    {p : MvPolynomial σ k} {n : ℕ} (hp : p ∈ I) (hn : p.totalDegree ≤ n) :
    homogeneousComponent n p ∈ boundaryIdeal I := by
  rcases hn.eq_or_lt with rfl | hn
  · exact Ideal.subset_span ⟨p, hp, rfl⟩
  · rw [homogeneousComponent_eq_zero _ _ hn]
    exact (boundaryIdeal I).zero_mem
private abbrev equations (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k) :=
  I.restrictScalars k ⊓ restrictTotalDegree σ k n
private theorem equations_finite [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (equations I n) :=
  Module.Finite.of_injective (Submodule.inclusion inf_le_right) (Submodule.inclusion_injective _)
private def leadingMap (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    equations I n →ₗ[k] MvPolynomial σ k :=
  (homogeneousComponent n).domRestrict (equations I n)
private theorem range_le (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range (leadingMap I n) ≤ LinearMap.range (leadingMap (boundaryIdeal I) n) := by
  rintro _ ⟨p, rfl⟩
  have hp := (Submodule.mem_inf.mp p.property).1
  have hdeg := (mem_restrictTotalDegree σ n (p : MvPolynomial σ k)).mp
    (Submodule.mem_inf.mp p.property).2
  have hh := homogeneousComponent_isHomogeneous n (p : MvPolynomial σ k)
  refine ⟨⟨homogeneousComponent n p, Submodule.mem_inf.mpr ⟨
    component_mem_boundary hp hdeg, (mem_restrictTotalDegree σ n _).mpr hh.totalDegree_le⟩⟩, ?_⟩
  exact homogeneousComponent_eq_self hh
private theorem leading_zero_iff {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) p = 0 ↔ p.totalDegree ≤ n := by
  constructor
  · intro hz
    apply Finset.sup_le
    intro d hd
    have hle : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
    have hne : d.degree ≠ n + 1 := by
      intro he
      apply mem_support_iff.mp hd
      simpa [coeff_homogeneousComponent, he] using
        congrArg (fun q : MvPolynomial σ k ↦ q.coeff d) hz
    exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)
  · intro h
    exact homogeneousComponent_eq_zero _ _ (Nat.lt_succ_of_le h)
private theorem finrank_leading_ker_succ (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (LinearMap.ker (leadingMap I (n + 1))) =
      Module.finrank k (equations I n) := by
  have hle : equations I n ≤ equations I (n + 1) := by
    rintro p ⟨hp, hd⟩
    exact ⟨hp, (mem_restrictTotalDegree σ (n + 1) p).mpr
      (((mem_restrictTotalDegree σ n p).mp hd).trans (Nat.le_succ n))⟩
  have he : LinearMap.ker (leadingMap I (n + 1)) =
      (equations I n).comap (equations I (n + 1)).subtype := by
    ext p
    have hp := (Submodule.mem_inf.mp p.property).1
    have hdeg := (mem_restrictTotalDegree σ (n + 1) (p : MvPolynomial σ k)).mp
      (Submodule.mem_inf.mp p.property).2
    rw [LinearMap.mem_ker]
    change homogeneousComponent (n + 1) (p : MvPolynomial σ k) = 0 ↔
      (p : MvPolynomial σ k) ∈ equations I n
    rw [Submodule.mem_inf, mem_restrictTotalDegree, leading_zero_iff hdeg]
    exact ⟨fun h ↦ ⟨hp, h⟩, And.right⟩
  rw [he]
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
private theorem finrank_leading_ker_zero (I : Ideal (MvPolynomial σ k)) :
    Module.finrank k (LinearMap.ker (leadingMap I 0)) = 0 := by
  have hker : LinearMap.ker (leadingMap I 0) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    apply Subtype.ext
    have hdeg := (mem_restrictTotalDegree σ 0 (p : MvPolynomial σ k)).mp
      (Submodule.mem_inf.mp p.property).2
    change homogeneousComponent 0 (p : MvPolynomial σ k) = 0 at hp
    rw [homogeneousComponent_zero] at hp
    exact (totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)).trans hp
  rw [hker, finrank_bot]
private theorem finrank_equations_le [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (equations I n) ≤ Module.finrank k (equations (boundaryIdeal I) n) := by
  have (J : Ideal (MvPolynomial σ k)) (d : ℕ) := equations_finite J d
  have step (d : ℕ) :=
    Submodule.finrank_mono (range_le I d)
  induction n with
  | zero =>
    have hI := (leadingMap I 0).finrank_range_add_finrank_ker
    have hB := (leadingMap (boundaryIdeal I) 0).finrank_range_add_finrank_ker
    rw [finrank_leading_ker_zero, add_zero] at hI hB
    exact hI ▸ hB ▸ step 0
  | succ n ih =>
    have hI := (leadingMap I (n + 1)).finrank_range_add_finrank_ker
    have hB := (leadingMap (boundaryIdeal I) (n + 1)).finrank_range_add_finrank_ker
    rw [finrank_leading_ker_succ] at hI hB
    exact hI ▸ hB ▸ Nat.add_le_add (step (n + 1)) ih
private theorem hilbert_add_finrank_equations [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction I n + Module.finrank k (equations I n) =
      Module.finrank k (restrictTotalDegree σ k n) := by
  let f := (Ideal.Quotient.mkₐ k I).toLinearMap.domRestrict (restrictTotalDegree σ k n)
  have hker : LinearMap.ker f = (equations I n).comap (restrictTotalDegree σ k n).subtype := by
    ext p
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (p : MvPolynomial σ k) = 0 ↔
      (p : MvPolynomial σ k) ∈ equations I n
    rw [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_inf]
    exact ⟨fun hp ↦ ⟨hp, p.property⟩, And.left⟩
  have hr : LinearMap.range f = quotientDegreeLE I n := LinearMap.range_domRestrict _ _
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hker, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  exact h
theorem boundary_dimension_le [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    dimension (boundaryIdeal I) ≤ dimension I := by
  apply natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) (c := 1) (by decide)
  apply Filter.Eventually.of_forall
  intro n
  simp only [one_mul]
  have hI := hilbert_add_finrank_equations I n
  have hB := hilbert_add_finrank_equations (boundaryIdeal I) n
  have hle := finrank_equations_le I n
  omega
end
end K1_13_6_3_5_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
private theorem local_residue_rank {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal S) [p.IsPrime] (q : Ideal R) [q.IsPrime]
    (h : q = p.comap f) :
    letI := (Localization.localRingHom q p f h).toAlgebra
    letI : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
      Localization.isLocalHom_localRingHom q p f h
    Module.finrank q.ResidueField p.ResidueField = degree f p := by
  subst q
  let q := p.comap f
  let _ : q.IsPrime := Ideal.IsPrime.comap f
  let _ := (Localization.localRingHom q p f rfl).toAlgebra
  let _ : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
    Localization.isLocalHom_localRingHom q p f rfl
  change Module.finrank q.ResidueField p.ResidueField = degree f p
  rw [degree, dite_eq_left (show p.IsPrime from inferInstance)]
  let fq : (R ⧸ q) →+* (S ⧸ p) := Ideal.quotientMap p f le_rfl
  let ff : FractionRing (R ⧸ q) →+* FractionRing (S ⧸ p) :=
    IsFractionRing.map (Ideal.quotientMap_injective (I := p) (f := f))
  let _ := ff.toAlgebra
  let i := FractionRing.algEquiv (R ⧸ q) q.ResidueField
  let j := FractionRing.algEquiv (S ⧸ p) p.ResidueField
  have hcomm :
      (algebraMap q.ResidueField p.ResidueField).comp i.toRingHom = j.toRingHom.comp ff := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ q)
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hi : i (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)) =
        algebraMap R q.ResidueField r :=
      i.commutes _
    have hf : ff (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)) =
        algebraMap (S ⧸ p) (FractionRing (S ⧸ p)) (Ideal.Quotient.mk p (f r)) := by
      change IsLocalization.map _ fq _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    change algebraMap q.ResidueField p.ResidueField
        (i (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r))) =
      j (ff (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)))
    rw [hi, hf, j.commutes]
    change Ideal.ResidueField.map q p f rfl (algebraMap R q.ResidueField r) = _
    exact Ideal.ResidueField.map_algebraMap q p f rfl r
  change Module.finrank (q.ResidueField) (p.ResidueField) =
    Module.finrank (FractionRing (R ⧸ q)) (FractionRing (S ⧸ p))
  exact (congrArg Cardinal.toNat (Algebra.rank_eq_of_equiv_equiv
    i.toRingEquiv j.toRingEquiv hcomm)).symm
theorem branchLength_toNat {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) (J : Ideal S) (q : Ideal R) [q.IsPrime]
    (p : fibrePrimes f J q) :
    (branchLength f J q p).toNat = weight J (p : Ideal S) * degree f (p : Ideal S) := by
  classical
  let hp := fibre_prime p
  let T := Localization.AtPrime (p : Ideal S)
  let L := Localization.AtPrime q
  let e := Localization.localRingHom q (p : Ideal S) f (fibre_comap p)
  let _ : Algebra L T := e.toAlgebra
  let _ : IsLocalHom (algebraMap L T) :=
    Localization.isLocalHom_localRingHom q (p : Ideal S) f (fibre_comap p)
  change (Module.length L (LocalSection J (p : Ideal S))).toNat = _
  rw [IsLocalRing.length_restrictScalars L T, ENat.toNat_mul, weight, dite_eq_left hp,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  change (Module.length T (LocalSection J (p : Ideal S))).toNat *
    Module.finrank q.ResidueField (p : Ideal S).ResidueField = _
  exact congrArg ((Module.length T (LocalSection J (p : Ideal S))).toNat * ·)
    (local_residue_rank f (p : Ideal S) q (fibre_comap p))
end
end K1_13_6_3_5_5
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_4_3
noncomputable section
open K1_13_6_3 K1_13_6_3_4 MvPolynomial
open Finset.HasAntidiagonal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
private theorem decompose_apply (a : MvPolynomial σ k) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ k) a n : MvPolynomial σ k) =
      homogeneousComponent n a :=
  decomposition.decompose'_apply a n
private theorem component_mul (a b : MvPolynomial σ k) (n : ℕ) :
    homogeneousComponent n (a * b) = ∑ ij ∈ antidiagonal n,
      homogeneousComponent ij.1 a * homogeneousComponent ij.2 b := by
  let grades := homogeneousSubmodule σ k
  calc
    homogeneousComponent n (a * b) = (DirectSum.decompose grades (a * b) n : MvPolynomial σ k) :=
      (decompose_apply (a * b) n).symm
    _ = ∑ ij ∈ antidiagonal n,
          (DirectSum.decompose grades a ij.1 : MvPolynomial σ k) *
            (DirectSum.decompose grades b ij.2 : MvPolynomial σ k) := by
      rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
    _ = _ := by simp only [grades, decompose_apply]
private theorem component_mul_of_homogeneous {a b : MvPolynomial σ k} {i j : ℕ}
    (ha : a.IsHomogeneous i) :
    homogeneousComponent (i + j) (a * b) = a * homogeneousComponent j b := by
  simpa only [decompose_apply, Nat.add_sub_cancel_left] using
    (DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := homogeneousSubmodule σ k) (b := b) ha (Nat.le_add_right i j))
private theorem lift_boundary_component (I : Ideal (MvPolynomial σ k))
    {q : MvPolynomial σ k} (hq : q ∈ boundaryIdeal I) :
    ∀ n, ∃ r ∈ I, r.totalDegree ≤ n ∧ homogeneousComponent n r = homogeneousComponent n q := by
  unfold boundaryIdeal at hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨p, m, hp, hdeg, rfl⟩ := hq
    intro n
    by_cases h : n = m
    · subst n
      exact ⟨p, hp, hdeg, (homogeneousComponent_eq_self
        (homogeneousComponent_isHomogeneous m p)).symm⟩
    · refine ⟨0, I.zero_mem, by simp, ?_⟩
      rw [map_zero, homogeneousComponent_of_mem (homogeneousComponent_mem m p), ite_eq_right h]
  | zero => exact fun n ↦ ⟨0, I.zero_mem, by simp, rfl⟩
  | add a b _ _ ha hb =>
    intro n
    obtain ⟨r, hr, hrd, hre⟩ := ha n
    obtain ⟨s, hs, hsd, hse⟩ := hb n
    exact ⟨r + s, I.add_mem hr hs, (totalDegree_add r s).trans (max_le hrd hsd),
      by rw [map_add, map_add, hre, hse]⟩
  | smul a b _ hb =>
    classical
    intro n
    choose r hrI hrDegree hrComponent using hb
    change ∃ p ∈ I, p.totalDegree ≤ n ∧
      homogeneousComponent n p = homogeneousComponent n (a * b)
    refine ⟨∑ ij ∈ antidiagonal n, homogeneousComponent ij.1 a * r ij.2,
      I.sum_mem (fun ij _ ↦ I.mul_mem_left _ (hrI ij.2)), ?_, ?_⟩
    · rw [← mem_restrictTotalDegree]
      apply Submodule.sum_mem
      intro ij hij
      rw [mem_restrictTotalDegree, ← mem_antidiagonal.mp hij]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add
        (homogeneousComponent_isHomogeneous ij.1 a).totalDegree_le (hrDegree ij.2))
    · rw [map_sum, component_mul a b n]
      refine Finset.sum_congr rfl fun ij hij ↦ ?_
      rw [← mem_antidiagonal.mp hij,
        component_mul_of_homogeneous (homogeneousComponent_isHomogeneous ij.1 a), hrComponent]
private theorem coordinate_power_mem [Finite σ] [IsAlgClosed k]
    {I : Ideal (MvPolynomial σ k)} {ℓ : MvPolynomial σ k} (h : NoBoundaryZero I ℓ) (i : σ) :
    ∃ e : ℕ, MvPolynomial.X i ^ e ∈ boundaryIdeal I ⊔ Ideal.span {ℓ} := by
  let J := boundaryIdeal I ⊔ Ideal.span {ℓ}
  have hx : MvPolynomial.X i ∈ vanishingIdeal k (zeroLocus k J) := by
    intro b hb
    have hbI := zeroLocus_anti_mono (show boundaryIdeal I ≤ J from le_sup_left) hb
    have hright : Ideal.span ({ℓ} : Set (MvPolynomial σ k)) ≤ J := le_sup_right
    have hbℓ : eval b ℓ = 0 := hb ℓ (hright (Ideal.subset_span (by simp)))
    simp only [aeval_X, h b hbI hbℓ, Pi.zero_apply]
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact Ideal.mem_radical_iff.mp hx
private theorem homogeneous_mem_of_coordinate_powers [Fintype σ]
    {J : Ideal (MvPolynomial σ k)} (e : σ → ℕ) (he : ∀ i, MvPolynomial.X i ^ e i ∈ J)
    {n : ℕ} (hn : (∑ i, e i) < n) {q : MvPolynomial σ k} (hq : q.IsHomogeneous n) : q ∈ J := by
  classical
  rw [← q.support_sum_monomial_coeff]
  apply J.sum_mem
  intro d hd
  have hdDegree : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hq.coeff_eq_zero h)
  obtain ⟨i, hi⟩ : ∃ i, e i ≤ d i := by
    by_contra! h
    have hsum : (∑ i, d i) ≤ ∑ i, e i := Finset.sum_le_sum fun i _ ↦ (h i).le
    rw [← Finsupp.degree_eq_sum, hdDegree] at hsum
    exact (not_le_of_gt hn) hsum
  have hsingle : Finsupp.single i (e i) ≤ d := Finsupp.single_le_iff.mpr hi
  let d' := d - Finsupp.single i (e i)
  have hd' : d' + Finsupp.single i (e i) = d := tsub_add_cancel_of_le hsingle
  have hmon := J.mul_mem_left (monomial d' (q.coeff d)) (he i)
  rwa [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, mul_one, hd'] at hmon
private theorem degree_le_of_component_zero {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) (hzero : homogeneousComponent (n + 1) p = 0) :
    p.totalDegree ≤ n := by
  unfold totalDegree
  refine Finset.sup_le fun d hd ↦ ?_
  have hle : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
  have hne : d.degree ≠ n + 1 := by
    intro h
    have hcoeff := congrArg (fun q : MvPolynomial σ k ↦ q.coeff d) hzero
    change (homogeneousComponent (n + 1) p).coeff d = 0 at hcoeff
    exact (mem_support_iff.mp hd) (by simpa only [coeff_homogeneousComponent, ite_eq_left h] using hcoeff)
  change d.degree ≤ n
  omega
theorem value_reduction [Fintype σ] [IsAlgClosed k]
    {I : Ideal (MvPolynomial σ k)} {ℓ : MvPolynomial σ k}
    (hℓ : ℓ.IsHomogeneous 1) (h : NoBoundaryZero I ℓ) : ValueReduction I ℓ := by
  classical
  choose e he using coordinate_power_mem h
  refine ⟨∑ i, e i, ?_⟩
  intro n hn z hz
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hz
  have htop : homogeneousComponent (n + 1) p ∈ boundaryIdeal I ⊔ Ideal.span {ℓ} :=
    homogeneous_mem_of_coordinate_powers e he (Nat.lt_succ_of_le hn)
      (homogeneousComponent_isHomogeneous (n + 1) p)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp htop
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hv
  obtain ⟨r, hrI, hrDegree, hr⟩ := lift_boundary_component I hu (n + 1)
  have hmul (f : MvPolynomial σ k) : homogeneousComponent (n + 1) (ℓ * f) =
      ℓ * homogeneousComponent n f := by
    rw [Nat.add_comm n 1, component_mul_of_homogeneous hℓ]
  have htop_eq : homogeneousComponent (n + 1) p =
      homogeneousComponent (n + 1) r + ℓ * homogeneousComponent n b := by
    have hcomp := congrArg (homogeneousComponent (n + 1)) huv
    simpa only [map_add, ← hr, hmul,
      homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous (n + 1) p)] using hcomp.symm
  let b' := homogeneousComponent n b
  have hb' : b'.IsHomogeneous n := homogeneousComponent_isHomogeneous n b
  let a := p - (r + ℓ * b')
  have hab : (r + ℓ * b').totalDegree ≤ n + 1 :=
    (totalDegree_add _ _).trans (max_le hrDegree ((totalDegree_mul _ _).trans
      ((Nat.add_le_add hℓ.totalDegree_le hb'.totalDegree_le).trans_eq (Nat.add_comm 1 n))))
  have ha : a.totalDegree ≤ n := by
    apply degree_le_of_component_zero
    · rw [← mem_restrictTotalDegree] at hp hab ⊢
      exact (restrictTotalDegree σ k (n + 1)).sub_mem hp hab
    · simp only [a, b', map_sub, map_add, hmul, homogeneousComponent_eq_self hb',
        ← htop_eq, sub_self]
  refine ⟨Ideal.Quotient.mk I a, mk_mem_quotientDegreeLE ha,
    Ideal.Quotient.mk I b', mk_mem_quotientDegreeLE hb'.totalDegree_le, ?_⟩
  have hrzero : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrI
  calc
    Ideal.Quotient.mk I p = Ideal.Quotient.mk I (a + (r + ℓ * b')) :=
      congrArg (Ideal.Quotient.mk I) (sub_add_cancel p (r + ℓ * b')).symm
    _ = _ := by rw [map_add, map_add, hrzero, zero_add, map_mul]
theorem proof : K1_13_6_3_4.c3 := by
  intro I h
  exact value_reduction (jetLinear_homogeneous genericArgument 0) h
end
end K1_13_6_3_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_3_1
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {k L σ : Type*} [Field k] [Field L] [Algebra k L]
private abbrev baseIdeal (L : Type*) [Field L] [Algebra k L]
    (I : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ L) :=
  I.map (MvPolynomial.map (algebraMap k L))
private def baseQuot (I : Ideal (MvPolynomial σ k)) :
    L ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[L] MvPolynomial σ L ⧸ baseIdeal L I := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (MvPolynomial σ k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap k L) p = e (1 ⊗ₜ[k] p)
  simp [e]
private theorem baseQuot_tmul (I : Ideal (MvPolynomial σ k)) (a : L)
    (p : MvPolynomial σ k) :
    baseQuot I (a ⊗ₜ[k] Ideal.Quotient.mk I p) =
      a • Ideal.Quotient.mk (baseIdeal L I) (MvPolynomial.map (algebraMap k L) p) := by
  unfold baseQuot
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact map_smul (Ideal.Quotient.mkₐ L (baseIdeal L I)) a _
private theorem baseIdeal_comap (I : Ideal (MvPolynomial σ k)) :
    (baseIdeal L I).comap (MvPolynomial.map (algebraMap k L)) = I := by
  refine le_antisymm (fun p hp => ?_) Ideal.le_comap_map
  have hz : Ideal.Quotient.mk (baseIdeal L I) (MvPolynomial.map (algebraMap k L) p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he : baseQuot I ((1 : L) ⊗ₜ[k] Ideal.Quotient.mk I p) = baseQuot I 0 := by
    simp [baseQuot_tmul, hz]
  have hi := Algebra.TensorProduct.includeRight_injective
    (B := MvPolynomial σ k ⧸ I) (RingHom.injective (algebraMap k L))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  change (1 : L) ⊗ₜ[k] Ideal.Quotient.mk I p = (1 : L) ⊗ₜ[k] 0
  rw [TensorProduct.tmul_zero]
  exact (baseQuot I).injective he
section Prime
variable [Finite σ] [IsAlgClosed k]
private def pointEval (I : Ideal (MvPolynomial σ k)) (x : σ → k)
    (hx : x ∈ zeroLocus k I) : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (aeval x) (mem_zeroLocus_iff.mp hx)
private theorem exists_point (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    (u v : MvPolynomial σ k ⧸ I) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x : σ → k, ∃ hx : x ∈ zeroLocus k I,
      pointEval I x hx u ≠ 0 ∧ pointEval I x hx v ≠ 0 := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hpq : p * q ∉ I := fun h => (hI.mem_or_mem h).elim
    (fun hp => hu (Ideal.Quotient.eq_zero_iff_mem.mpr hp))
    (fun hq => hv (Ideal.Quotient.eq_zero_iff_mem.mpr hq))
  have hvan : vanishingIdeal k (zeroLocus k I) = I := by
    rw [vanishingIdeal_zeroLocus_eq_radical, hI.radical]
  have hx : ∃ x ∈ zeroLocus k I, aeval x (p * q) ≠ 0 := by
    by_contra! h
    exact hpq (hvan ▸ mem_vanishingIdeal_iff.mpr h)
  obtain ⟨x, hx, h⟩ := hx
  rw [map_mul, mul_ne_zero_iff] at h
  exact ⟨x, hx, h⟩
private theorem tensor_mul_ne_zero (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    {a b : L ⊗[k] (MvPolynomial σ k ⧸ I)} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  classical
  let B := Module.Free.chooseBasis k L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := MvPolynomial σ k ⧸ I) B
  have nonzero_coord (w : L ⊗[k] (MvPolynomial σ k ⧸ I)) (hw : w ≠ 0) :
      ∃ i, e w i ≠ 0 := by
    by_contra! h
    exact hw (e.injective (by simpa only [map_zero] using Finsupp.ext h))
  obtain ⟨i, hi⟩ := nonzero_coord a ha
  obtain ⟨j, hj⟩ := nonzero_coord b hb
  obtain ⟨x, hx, ha', hb'⟩ := exists_point I hI (e a i) (e b j) hi hj
  let f := pointEval I x hx
  let m := Algebra.TensorProduct.map (AlgHom.id k L) f
  let d := TensorProduct.equivFinsuppOfBasisLeft (N := k) B
  have coord (w : L ⊗[k] (MvPolynomial σ k ⧸ I)) (l : Module.Free.ChooseBasisIndex k L) :
      d (m w) l = f (e w l) := by
    induction w using TensorProduct.inductionOn with
    | tmul c u =>
      simp [d, e, m, map_smul]
    | add y z hy hz => simp [hy, hz]
  have nonzero_image (w : L ⊗[k] (MvPolynomial σ k ⧸ I))
      (l : Module.Free.ChooseBasisIndex k L) (hw : f (e w l) ≠ 0) : m w ≠ 0 := by
    intro h
    exact hw (by rw [← coord, h]; simp)
  let r := Algebra.TensorProduct.rid (R := k) (S := k) (A := L)
  intro hab
  have h := congrArg (fun w => r (m w)) hab
  have hprod : r (m a) * r (m b) = 0 := by simpa only [map_mul, map_zero] using h
  exact (mul_ne_zero (fun h => nonzero_image a i ha' (r.injective (h.trans r.map_zero.symm)))
    (fun h => nonzero_image b j hb' (r.injective (h.trans r.map_zero.symm)))) hprod
private theorem baseIdeal_prime (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) :
    (baseIdeal L I).IsPrime := by
  refine ⟨fun h => hI.ne_top ((baseIdeal_comap (L := L) I).symm.trans (by rw [h, Ideal.comap_top])),
    fun {p q} hpq => ?_⟩
  by_contra! h
  let e := (baseQuot (L := L) I).symm
  let a := e (Ideal.Quotient.mk (baseIdeal L I) p)
  let b := e (Ideal.Quotient.mk (baseIdeal L I) q)
  have ha : a ≠ 0 := fun hz =>
    h.1 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
  have hb : b ≠ 0 := fun hz =>
    h.2 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
  apply tensor_mul_ne_zero I hI ha hb
  rw [← map_mul e, ← map_mul (Ideal.Quotient.mk (baseIdeal L I)),
    Ideal.Quotient.eq_zero_iff_mem.mpr hpq, map_zero]
end Prime
section Hilbert
variable [Finite σ]
private theorem baseIdeal_hilbertFunction (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction (baseIdeal L I) n = affineHilbertFunction I n := by
  classical
  let W := quotientDegreeLE I n
  let V := quotientDegreeLE (baseIdeal L I) n
  let f : L ⊗[k] W →ₗ[L] MvPolynomial σ L ⧸ baseIdeal L I :=
    (baseQuot I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (a : L) (z : W) : f (a ⊗ₜ[k] z) = baseQuot I (a ⊗ₜ[k] z.val) := rfl
  have hinj : Function.Injective f := (baseQuot I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective)
  have hrange : LinearMap.range f = V := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul a z =>
        obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp z.property
        rw [hcalc, ← he, baseQuot_tmul]
        apply V.smul_mem
        apply mk_mem_quotientDegreeLE
        exact (Finset.sup_mono (support_map_subset (algebraMap k L) p)).trans hp
      | add y z hy hz => simpa only [map_add] using V.add_mem hy hz
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hy
      nth_rw 1 [p.as_sum]
      rw [map_sum]
      apply Submodule.sum_mem
      intro m hm
      have hdeg := (le_totalDegree hm).trans hp
      let z : W := ⟨Ideal.Quotient.mk I (monomial m 1),
        mk_mem_quotientDegreeLE ((totalDegree_monomial_le m (1 : k)).trans hdeg)⟩
      refine ⟨p.coeff m ⊗ₜ[k] z, ?_⟩
      rw [hcalc, show z.val = Ideal.Quotient.mk I (monomial m 1) from rfl, baseQuot_tmul]
      rw [MvPolynomial.map_monomial, map_one]
      change p.coeff m • Ideal.Quotient.mkₐ L (baseIdeal L I) (monomial m 1) =
        Ideal.Quotient.mkₐ L (baseIdeal L I) (monomial m (p.coeff m))
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  let e := (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let B := Module.Free.chooseBasis k W
  change Module.finrank L V = Module.finrank k W
  rw [Module.finrank_eq_nat_card_basis ((B.baseChange L).map e), Module.finrank_eq_nat_card_basis B]
private theorem baseIdeal_hilbertPolynomial (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (baseIdeal L I) = affineHilbertPolynomial I := by
  obtain ⟨n₀, hn₀⟩ := exists_eval_affineHilbertPolynomial I
  refine (eq_affineHilbertPolynomial_of_eval_eq (N₀ := n₀) fun n hn => ?_).symm
  rw [hn₀ n hn, baseIdeal_hilbertFunction]
end Hilbert
open K1_13 K1_13_6 K1_13_6_3
theorem proof : K1_13_6_3_3.c1 := by
  intro A hA
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  exact ⟨baseIdeal_prime A hA, congrArg Polynomial.natDegree (baseIdeal_hilbertPolynomial A),
    baseIdeal_comap A⟩
end
end K1_13_6_3_3_1
end
section
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace K1_13_5_4_2_2_1
noncomputable section
open K1_13_5_4_2_2 K1_13_5_4_4_2 K1_13_6_3_4 MvPolynomial
variable {k σ : Type} [Field k] [Finite σ]
theorem linearForm_homogeneous (a : σ → k) : (linearForm a).IsHomogeneous 1 := by
  classical
  unfold linearForm
  exact (homogeneousSubmodule σ k 1).sum_mem fun i _ => isHomogeneous_C_mul_X (a i) i
private def pairing (z : σ → k) : (σ → k) →ₗ[k] k := by
  classical
  letI := Fintype.ofFinite σ
  exact ∑ i, z i • LinearMap.proj i
private theorem pairing_eval (z a : σ → k) : pairing z a = eval z (linearForm a) := by
  classical
  simp [pairing, linearForm, mul_comm]
private theorem pairing_ker_ne_top (z : σ → k) {i : σ} (hi : z i ≠ 0) :
    LinearMap.ker (pairing z) ≠ ⊤ := by
  classical
  letI := Fintype.ofFinite σ
  intro h
  have hz : pairing z (Pi.single i 1) = 0 := LinearMap.mem_ker.mp (h ▸ Submodule.mem_top)
  have hs : pairing z (Pi.single i 1) = z i := by
    simp only [pairing, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact hi (hs.symm.trans hz)
private theorem eval_scale (x : σ → k) (c : k)
    {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n) :
    eval (fun i => c * x i) p = c ^ n * eval x p := by
  classical
  letI := Fintype.ofFinite σ
  change eval₂ (RingHom.id k) (fun i => c * x i) p = c ^ n * eval₂ (RingHom.id k) x p
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (c * x i) ^ d i) = c ^ n * ∏ i : σ, x i ^ d i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring
private theorem normalize_boundary (I : Ideal (MvPolynomial σ k))
    {x : σ → k} (hx : x ∈ zeroLocus k (boundaryIdeal I)) {i : σ} (hi : x i ≠ 0) :
    (fun j => (x i)⁻¹ * x j) ∈ zeroLocus k (boundaryChart I i) := by
  let y : σ → k := fun j => (x i)⁻¹ * x j
  change boundaryChart I i ≤ RingHom.ker (eval y)
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    apply RingHom.mem_ker.mpr
    change eval (fun j => (x i)⁻¹ * x j) (homogeneousComponent n p) = 0
    rw [eval_scale x (x i)⁻¹ (homogeneousComponent_isHomogeneous n p)]
    have hz : eval x (homogeneousComponent n p) = 0 :=
      hx _ (Ideal.subset_span ⟨p, n, hp, hn, rfl⟩)
    rw [hz, mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    apply RingHom.mem_ker.mpr
    rw [map_sub, eval_X, map_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
omit [Finite σ] in
private theorem boundary_chart_coordinate (I : Ideal (MvPolynomial σ k)) {i : σ}
    (z : zeroLocus k (boundaryChart I i)) : z.val i = 1 := by
  have h : eval z.val (MvPolynomial.X i - 1) = 0 :=
    z.property _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  exact sub_eq_zero.mp (by simpa using h)
theorem exists_boundary_exclusions [IsAlgClosed k] (I : Ideal (MvPolynomial σ k))
    (hI : (affineHilbertPolynomial I).natDegree = 1) :
    ∃ bad : Finset (Submodule k (σ → k)), (∀ B ∈ bad, B ≠ ⊤) ∧
      ∀ a : σ → k, (∀ B ∈ bad, a ∉ B) → NoBoundaryZero I (linearForm a) := by
  classical
  letI := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  letI : WellFoundedGT σ := Finite.to_wellFoundedGT
  let P (i : σ) := zeroLocus k (boundaryChart I i)
  letI (i : σ) : Fintype (P i) :=
    ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero _).mpr
      (boundaryChart_dimension I hI i)).fintype
  let obstruction (p : Σ i, P i) := LinearMap.ker (pairing p.2.val)
  refine ⟨Finset.univ.image obstruction, ?_, ?_⟩
  · intro B hB
    obtain ⟨⟨i, z⟩, _, rfl⟩ := Finset.mem_image.mp hB
    apply pairing_ker_ne_top z.val (i := i)
    rw [boundary_chart_coordinate I z]
    exact one_ne_zero
  · intro a ha x hx hz
    funext i
    change x i = 0
    by_contra hi
    let z : P i := ⟨_, normalize_boundary I hx hi⟩
    apply ha (obstruction ⟨i, z⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    change pairing z.val a = 0
    rw [pairing_eval]
    change eval (fun j => (x i)⁻¹ * x j) (linearForm a) = 0
    rw [eval_scale x (x i)⁻¹ (linearForm_homogeneous a), hz, mul_zero]
end
end K1_13_5_4_2_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
open K1_13_6_3_5
def c1 : Prop :=
  ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → IsBirationalOn φ A →
      Nonempty (ConeModel φ A)
def c2 : Prop :=
  ∀ (U V R S : Type) [CommRing U] [CommRing V] [CommRing R] [CommRing S]
    [IsNoetherianRing V] [IsNoetherianRing S]
    (g : U →+* V) (f : R →+* S) (J : Ideal U) (I : Ideal V) (w : R)
    (r : SectionPresentation J w) (s : SectionPresentation I (f w)),
    Compatible g f r s →
    ∀ Q : Ideal U, J.IsMinimalPrime Q →
      ∃ q : Ideal R, (Ideal.span {w}).IsMinimalPrime q ∧
        weight J Q = weight (Ideal.span {w}) q ∧
        fibreWeight g I Q = fibreWeight f (Ideal.span {f w}) q
def c3 : Prop :=
  ∀ (L : Type) [CommRing L] [IsDomain L] [IsNoetherianRing L] [IsLocalRing L]
    [Ring.KrullDimLE 1 L] (x : L), x ≠ 0 →
    ∀ (B : FractionSubalgebra L) (s : Finset (SectionQuotient x B)),
      Module.length L (Submodule.span L (s : Set (SectionQuotient x B))) ≤ Ring.ord L x
def c4 : Prop :=
  ∀ (R S F : Type) [CommRing R] [IsDomain R] [CommRing S] [IsNoetherianRing S]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (f : R →+* S) (e : S →+* F), Function.Injective e →
    e.comp f = algebraMap R F →
    ∀ (w : R) (q : Ideal R) [q.IsPrime],
      ∃ B : FractionSubalgebra (Localization.AtPrime q),
        (∑ p : fibrePrimes f (Ideal.span {f w}) q, branchLength f (Ideal.span {f w}) q p) ≤
          sectionLength (algebraMap R (Localization.AtPrime q) w) B
private theorem length_le_of_finite_spans {L M : Type} [Ring L] [AddCommGroup M] [Module L M]
    (n : ℕ∞) (h : ∀ s : Finset M, Module.length L (Submodule.span L (s : Set M)) ≤ n) :
    Module.length L M ≤ n := by
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro t
  have hstep (i : Fin t.length) : ∃ z ∈ t i.succ, z ∉ t i.castSucc :=
    Set.not_subset.mp (t.step i).not_ge
  choose z hz hnot using hstep
  let s := Finset.univ.image z
  let N := Submodule.span L (s : Set M)
  let u : LTSeries (Submodule L N) :=
    { length := t.length
      toFun := fun i => (t i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (t.step i).le) ?_
        intro he
        let a : N := ⟨z i, Submodule.subset_span (Finset.mem_image_of_mem z (Finset.mem_univ i))⟩
        have ha : a ∈ (t i.succ).comap N.subtype := hz i
        exact hnot i (show a ∈ (t i.castSucc).comap N.subtype from he.symm ▸ ha) }
  calc
    _ = (u.length : WithBot ℕ∞) := rfl
    _ ≤ Order.krullDim (Submodule L N) := Order.LTSeries.length_le_krullDim u
    _ = (Module.length L N : WithBot ℕ∞) := (Module.coe_length L N).symm
    _ ≤ _ := WithBot.coe_le_coe.mpr (h s)
private theorem finiteSumToNat6967 {α : Type*} {s : Finset α} {f : α → ℕ∞}
    (hs : (∑ a ∈ s, f a) ≠ ⊤) :
    ENat.toNat (∑ a ∈ s, f a) = ∑ a ∈ s, ENat.toNat (f a) := by
  rw [← ENat.natCast_inj, ENat.natCast_toNat hs, Nat.cast_sum]
  exact Finset.sum_congr rfl fun a ha =>
    (ENat.natCast_toNat (WithTop.sum_ne_top.mp hs a ha)).symm
private theorem principal_fibre_bound (h3 : c3) (h4 : c4)
    {R S F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [Field F] [Algebra R F] [IsFractionRing R F]
    (f : R →+* S) (e : S →+* F) (he : Function.Injective e)
    (hcomp : e.comp f = algebraMap R F)
    (w : R) (hw : w ≠ 0) (q : Ideal R) (hq : (Ideal.span {w}).IsMinimalPrime q) :
    fibreWeight f (Ideal.span {f w}) q ≤ weight (Ideal.span {w}) q := by
  classical
  let _ := hq.isPrime
  let L := Localization.AtPrime q
  let x := algebraMap R L w
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using (IsLocalization.injective L q.primeCompl_le_nonZeroDivisors).ne hw
  have hdim : Ring.KrullDimLE 1 L := by
    constructor
    change ringKrullDim L ≤ (1 : ℕ)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q L]
    exact WithBot.coe_le_coe.mpr
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq)
  let _ := hdim
  have hfinite : Ring.ord L x ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  obtain ⟨B, hB⟩ := h4 R S F f e he hcomp w q
  let I : Ideal S := Ideal.span {f w}
  have hsum : (∑ p : fibrePrimes f I q, branchLength f I q p) ≤ Ring.ord L x :=
    hB.trans (length_le_of_finite_spans _ (h3 L x hx B))
  have hsumFinite : (∑ p : fibrePrimes f I q, branchLength f I q p) ≠ ⊤ :=
    (lt_of_le_of_lt hsum hfinite.lt_top).ne
  have hnat := ENat.toNat_le_toNat hsum hfinite
  rw [finiteSumToNat6967 hsumFinite] at hnat
  have hweight : (Ring.ord L x).toNat = weight (Ideal.span {w}) q := by
    rw [weight, dite_eq_left hq.isPrime]
    change _ = (Module.length L (L ⧸ (Ideal.span {w}).map (algebraMap R L))).toNat
    have hmap : (Ideal.span {w}).map (algebraMap R L) = Ideal.span {x} := by
      rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun J : Ideal L => (Module.length L (L ⧸ J)).toNat) hmap.symm
  rw [hweight] at hnat
  change fibreWeight f I q ≤ _
  unfold fibreWeight
  rw [← Finset.sum_coe_sort]
  simpa only [branchLength_toNat f I q] using hnat
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) :
    K1_13_6_3_5.c5 := by
  classical
  intro k σ τ _ _ _ φ hφ A hA hbir Q hQ
  obtain ⟨M⟩ := h1 k σ τ φ hφ A hA hbir
  let _ := M.field
  let _ := M.algebra
  let _ := M.targetNoetherian
  let _ := M.sourceNoetherian
  let _ := M.fraction
  let f := (Subalgebra.inclusion M.le).toRingHom
  let e := M.source.val.toRingHom
  obtain ⟨q, hq, hweight, hsum⟩ :=
    h2 _ _ M.target M.source φ.toRingHom f _ _ M.w
      M.targetSection M.sourceSection M.compatible Q hQ
  change fibreWeight φ.toRingHom (boundaryIdeal A) Q ≤
    weight (boundaryIdeal (A.comap φ)) Q
  rw [hsum, hweight]
  exact principal_fibre_bound h3 h4 f e Subtype.val_injective rfl M.w M.w_ne q hq
end
end K1_13_6_3_5_5
end
section
namespace K1_8
noncomputable section
open Polynomial K1
structure AmplitudeDirection (U V : Bivar) where
  α : Fin 2 → (Polynomial K)
  β : Fin 2 → (Polynomial K)
  a : (Polynomial K)
  b : (Polynomial K)
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  scalar_coprime : IsCoprime a b
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  direction : sameDirection U V (threeU a β) (threeV b α)
end
end K1_8
end

end Merged6967_Fast053

section Merged6967_Fast054
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_6
open K1 Polynomial Matrix
open FrobeniusLocator
def c1 : Prop :=
  ∀ (F : Type) [Field F] (h L s : ℕ) (P : Fin 2 → (Polynomial (Polynomial F))),
    h + s = L → 0 < s →
    (∀ b, (P b).natDegree ≤ h) →
    PrimitiveVector.IsPrimitive (pairCoordinates P h) →
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P L s)) ∧
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → (Fin 2 × Fin L),
        (maximalMinors (shifts P L s) rows).natDegree = s * H
def c2 : Prop :=
  ∀ (F : Type) [Field F] (L w s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) (Polynomial F)) (W : Matrix (Fin 2 × Fin L) (Fin s) (Polynomial F)),
    1 ≤ p →
    GenericLayer.genericRank M + s = 2 * L →
    W.transpose * M = 0 →
    (∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p) →
    PrimitiveVector.IsPrimitive (maximalMinors W) →
    ∀ rows : Fin s → (Fin 2 × Fin L), (maximalMinors W rows).natDegree ≤ L * (p + 1) - s
end K1_6
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_6_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1_6
private theorem exists_shift_minor {R E : Type} [CommRing R] [Field E]
    (P : Fin 2 → (Polynomial R)) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (f : R → E) (hf : f 0 = 0) (b : Fin 2) (j : Fin (h + 1))
    (hj : f ((P b).coeff j.val) ≠ 0) :
    ∃ rows : Fin s → Fin 2 × Fin (h + s),
      maximalMinors ((shifts P (h + s) s).map f) rows ≠ 0 := by
  classical
  let S := (Finset.range (h + 1)).filter (fun d => f ((P b).coeff d) ≠ 0)
  have hS : S.Nonempty := ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩⟩
  let d := S.max' hS
  have hd : d ∈ S := S.max'_mem hS
  have hdle : d ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  have hdne : f ((P b).coeff d) ≠ 0 := (Finset.mem_filter.mp hd).2
  have hlarge : ∀ k, d < k → f ((P b).coeff k) = 0 := by
    intro k hk
    by_cases hkh : k < h + 1
    · by_contra hne
      exact (not_le_of_gt hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh, hne⟩))
    · have hk' : (P b).natDegree < k := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', hf]
  let rows (i : Fin s) : Fin 2 × Fin (h + s) := (b, ⟨d + i.val, by omega⟩)
  let A := ((shifts P (h + s) s).map f).submatrix rows id
  have htri : A.IsUpperTriangular := by
    intro i j hij
    change j.val < i.val at hij
    change f ((P b * Polynomial.X ^ j.val).coeff (d + i.val)) = 0
    rw [Polynomial.coeff_mul_X_pow', ite_eq_left (by omega)]
    exact hlarge _ (by omega)
  have hdiag (i : Fin s) : A i i = f ((P b).coeff d) := by
    change f ((P b * Polynomial.X ^ i.val).coeff (d + i.val)) = _
    rw [Polynomial.coeff_mul_X_pow]
  refine ⟨rows, ?_⟩
  change A.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Fin.prod_const]
  exact pow_ne_zero _ hdne
private theorem primitive_shift_minors {F : Type} [Field F]
    (P : Fin 2 → (Polynomial (Polynomial F))) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (hprimitive : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P (h + s) s)) := by
  classical
  let W := shifts P (h + s) s
  let I := Ideal.span (Set.range (maximalMinors W))
  change I = ⊤
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let : M.IsMaximal := hM
  let : Field ((Polynomial F) ⧸ M) := Ideal.Quotient.field M
  let φ := Ideal.Quotient.mk M
  have hsurvives : ∃ i, φ (pairCoordinates P h i) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout _).mp hprimitive
    have heq := congrArg φ ha
    simp only [map_sum, map_mul, hn, mul_zero, Finset.sum_const_zero, map_one] at heq
    exact zero_ne_one heq
  obtain ⟨⟨b, j⟩, hj⟩ := hsurvives
  obtain ⟨rows, hrows⟩ := exists_shift_minor P h s hdegree φ (map_zero φ) b j hj
  have hz : φ (maximalMinors W rows) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hIM (Ideal.subset_span (Set.mem_range_self rows)))
  apply hrows
  have heq := φ.map_det (W.submatrix rows id)
  rw [RingHom.mapMatrix_apply] at heq
  exact heq.symm.trans hz
private theorem coeff_det_uniform {F : Type*} [Field F] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) (Polynomial F)) (H : ℕ) (hdegree : ∀ i j, (A i j).natDegree ≤ H) :
    A.det.coeff (s * H) = (A.map (fun q => q.coeff H)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin, Matrix.map_apply] using
    Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin s))
      (fun i => A (σ i) i) H (fun i _ => hdegree (σ i) i)
private theorem shift_minors_height {F : Type} [Field F]
    (P : Fin 2 → (Polynomial (Polynomial F))) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (hprimitive : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → Fin 2 × Fin (h + s),
        (maximalMinors (shifts P (h + s) s) rows).natDegree = s * H := by
  classical
  let q := pairCoordinates P h
  let S := (Finset.univ : Finset (Fin 2 × Fin (h + 1))).filter (fun i => q i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := PrimitiveVector.exists_eval_ne_zero q hprimitive 0
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro hz
    exact hi (by rw [hz, Polynomial.eval_zero])
  let H := S.sup (fun i => (q i).natDegree)
  have hbound : ∀ b j, ((P b).coeff j).natDegree ≤ H := by
    intro b j
    by_cases hj : j < h + 1
    · let i : Fin 2 × Fin (h + 1) := (b, ⟨j, hj⟩)
      change (q i).natDegree ≤ H
      by_cases hi : q i = 0
      · simp [hi]
      · exact Finset.le_sup (s := S) (f := fun k => (q k).natDegree)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · have hj' : (P b).natDegree < j := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj']
      simp
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup S hS (fun k => (q k).natDegree)
  have htop : (q i).coeff H ≠ 0 := by
    change H = (q i).natDegree at hmax
    rw [hmax, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Finset.mem_filter.mp hi).2
  obtain ⟨rows, hrows⟩ := exists_shift_minor P h s hdegree (fun p => p.coeff H)
    (Polynomial.coeff_zero _) i.1 i.2 htop
  let A := (shifts P (h + s) s).submatrix rows id
  have hA (i j : Fin s) : (A i j).natDegree ≤ H := by
    change ((P (rows i).1 * Polynomial.X ^ j.val).coeff (rows i).2.val).natDegree ≤ H
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs
    · exact hbound _ _
    · simp
  have hcoeff : A.det.coeff (s * H) ≠ 0 := by
    rw [coeff_det_uniform A H hA]
    exact hrows
  have hupper : A.det.natDegree ≤ s * H := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      FrobeniusLocator.natDegree_det_le_row_sum A (fun _ => H) hA
  exact ⟨H, hbound, rows, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff⟩
theorem proof : K1_6.c1 := by
  intro F inst h L s P hL _ hdegree hprimitive
  subst L
  exact ⟨primitive_shift_minors P h s hdegree hprimitive,
    shift_minors_height P h s hdegree hprimitive⟩
end
end K1_6_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_6_2
open Polynomial Matrix
open FrobeniusLocator
open scoped BigOperators
theorem proof : K1_6.c2 := by
  intro F _ L w s p M W hp hrank hkernel hdegree hprim rows
  classical
  let E := GenericLayer.GenericField F
  let φ := algebraMap (Polynomial F) E
  have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial F) E
  let r := GenericLayer.genericRank M
  obtain ⟨B⟩ := GenericLayer.exists_generic_basis M
  have hcard : Fintype.card (Fin r ⊕ Fin s) = Fintype.card (Fin 2 × Fin L) := by
    simpa [Fintype.card_sum, Fintype.card_prod, r] using hrank
  let e : (Fin r ⊕ Fin s) ≃ (Fin 2 × Fin L) := Fintype.equivOfCardEq hcard
  let C := M.submatrix e B.cols
  let V := W.submatrix e id
  have hC : ∀ a, (C.map φ).mulVec a = 0 → a = 0 := by
    have hdet : ((M.submatrix B.rows B.cols).map φ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← φ.map_det]
      exact fun hz => B.minor_ne (hφ (hz.trans (map_zero φ).symm))
    intro a ha
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have hi := congrFun ha (e.symm (B.rows i))
    simpa only [C, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.apply_symm_apply, Pi.zero_apply] using hi
  have hVC : (V.map φ).transpose * (C.map φ) = 0 := by
    ext i j
    have hij := congrArg φ (congrFun (congrFun hkernel i) (B.cols j))
    change (∑ k : Fin r ⊕ Fin s, φ (W (e k) i) * φ (M (e k) (B.cols j))) = 0
    rw [Equiv.sum_comp e (fun k => φ (W k i) * φ (M k (B.cols j)))]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      map_sum, map_mul, map_zero] using hij
  have hminor (I : Fin s → (Fin r ⊕ Fin s)) :
      (V.submatrix I id).det = K1_6.maximalMinors W (e ∘ I) := rfl
  have hminor' (J : Fin s → (Fin 2 × Fin L)) :
      (V.submatrix (e.symm ∘ J) id).det = K1_6.maximalMinors W J := by
    rw [hminor]
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have hprimV : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) := by
    have hrange : Set.range (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) =
        Set.range (K1_6.maximalMinors W) := by
      ext z
      constructor
      · rintro ⟨I, rfl⟩
        exact ⟨e ∘ I, (hminor I).symm⟩
      · rintro ⟨J, rfl⟩
        exact ⟨e.symm ∘ J, hminor' J⟩
    unfold PrimitiveVector.IsPrimitive at hprim ⊢
    rwa [hrange]
  let d (i : Fin r ⊕ Fin s) := if (e i).1 = 0 then 1 else p
  have hpositive : ∀ i, 1 ≤ d i := by
    intro i
    dsimp [d]
    split_ifs <;> omega
  have hsum : (∑ i, d i) = L * (p + 1) := by
    dsimp [d]
    rw [Equiv.sum_comp e (fun i : Fin 2 × Fin L => if i.1 = 0 then 1 else p)]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Nat.mul_add, Nat.add_comm]
  have hbound := primitive_minor_degree φ hφ C V hVC hC hprimV d hpositive
    (fun i j => hdegree (e i) (B.cols j)) (e.symm ∘ rows)
  rwa [hminor', hsum] at hbound
end K1_6_2
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
private def budgetGCheck (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => budgetGCheck p n && p n
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem jetIndex_formula (m : Fin 4 →₀ ℕ) :
    m.weight jetIndex = m 1 + 2 * m 2 + 3 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, jetIndex, Nat.mul_comm]
theorem degree_formula (m : Fin 4 →₀ ℕ) :
    m.degree = m 0 + m 1 + m 2 + m 3 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_four]
theorem sumRange_eq_fin (n : ℕ) (f : ℕ → ℕ) : sumRange n f = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range f, sumRange_eq_sum]
theorem bandSpace_finite (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Module.Finite Geom (bandSpace d lo hi top) :=
  restrictSupport_finite ((Finsupp.finite_of_degree_le d).subset fun _ h => Nat.le_of_eq h.1)
private def exponents (a b c f : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c, f]
@[simp] private theorem exponents_apply (a b c f : ℕ) (j : Fin 4) :
    exponents a b c f j = ![a, b, c, f] j := by simp [exponents]
private theorem exponents_coords (m : Fin 4 →₀ ℕ) :
    exponents (m 0) (m 1) (m 2) (m 3) = m := by
  ext i
  fin_cases i <;> simp
private theorem interval_iff (lo hi : ℤ) (j : ℕ) :
    j < intervalSize lo hi ↔ lo + (j : ℤ) ≤ hi := by
  unfold intervalSize
  omega
private abbrev BandSlots (d : ℕ) (lo hi : ℤ) (top : ℕ) :=
  Σ f : Fin (min d top + 1),
    Σ c : Fin (min (d - f.val) ((hi - 3 * f.val) / 2).toNat + 1),
      Fin (intervalSize (max 0 (lo - 2 * c.val - 3 * f.val))
        (min ((d : ℤ) - f.val - c.val) (hi - 2 * c.val - 3 * f.val)))
private def bandEncoding (d : ℕ) (lo hi : ℤ) (top : ℕ) (p : BandSlots d lo hi top) :
    {m : Fin 4 →₀ ℕ // BandExponent d lo hi top m} := by
  obtain ⟨f, c, j⟩ := p
  let lower : ℤ := max 0 (lo - 2 * c.val - 3 * f.val)
  let upper : ℤ := min ((d : ℤ) - f.val - c.val) (hi - 2 * c.val - 3 * f.val)
  let b := lower.toNat + j.val
  have h0 : 0 ≤ lower := le_max_left _ _
  have hj : lower + (j.val : ℤ) ≤ upper := (interval_iff _ _ _).mp j.isLt
  have hb : (b : ℤ) = lower + (j.val : ℤ) := by dsimp [b]; omega
  have hlow := le_max_right (0 : ℤ) (lo - 2 * c.val - 3 * f.val)
  have hf := f.isLt
  have h : b + c.val + f.val ≤ d := by dsimp [upper] at hj; omega
  refine ⟨exponents (d - (b + c.val + f.val)) b c f, ?_⟩
  simp only [BandExponent, degree_formula, jetIndex_formula, exponents_apply]
  change d - (b + c.val + f.val) + b + c.val + f.val = d ∧
    lo ≤ (b + 2 * c.val + 3 * f.val : ℕ) ∧
    (b + 2 * c.val + 3 * f.val : ℕ) ≤ hi ∧ f.val ≤ top
  dsimp only [upper] at hj
  change lo - 2 * c.val - 3 * f.val ≤ lower at hlow
  omega
private theorem bandEncoding_bijective (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Function.Bijective (bandEncoding d lo hi top) := by
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨c, hc⟩, ⟨j, hj⟩⟩ ⟨⟨f', hf'⟩, ⟨c', hc'⟩, ⟨j', hj'⟩⟩ h
    have ef : f = f' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 3) h
    have ec : c = c' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 2) h
    subst f'
    subst c'
    have ej : j = j' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 1) h
    subst j'
    rfl
  · intro m
    obtain ⟨hd, hl, hu, htop⟩ := m.property
    let a := m.val 0
    let b := m.val 1
    let c := m.val 2
    let f := m.val 3
    change f ≤ top at htop
    rw [degree_formula] at hd
    change a + b + c + f = d at hd
    rw [jetIndex_formula] at hl hu
    change lo ≤ (b + 2 * c + 3 * f : ℕ) at hl
    change (b + 2 * c + 3 * f : ℕ) ≤ hi at hu
    have hf : f < min d top + 1 := by omega
    have hc : c < min (d - f) ((hi - 3 * f) / 2).toNat + 1 := by omega
    let lower : ℤ := max 0 (lo - 2 * c - 3 * f)
    let upper : ℤ := min ((d : ℤ) - f - c) (hi - 2 * c - 3 * f)
    let j := b - lower.toNat
    have h0 : 0 ≤ lower := le_max_left _ _
    have hb : lower.toNat + j = b := by
      dsimp [lower, j]
      omega
    have hj : j < intervalSize lower upper := (interval_iff _ _ _).mpr (by
      dsimp [upper] at *
      omega)
    refine ⟨⟨⟨f, hf⟩, ⟨c, hc⟩, ⟨j, hj⟩⟩, Subtype.ext ?_⟩
    change exponents (d - (lower.toNat + j + c + f)) (lower.toNat + j) c f = m.val
    rw [hb, show d - (b + c + f) = a by omega]
    exact exponents_coords m.val
theorem finrank_bandSpace (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Module.finrank Geom (bandSpace d lo hi top) = bandCount d lo hi top := by
  let e := Equiv.ofBijective (bandEncoding d lo hi top) (bandEncoding_bijective d lo hi top)
  let b := basisRestrictSupport Geom {m | BandExponent d lo hi top m}
  calc
    _ = Fintype.card (BandSlots d lo hi top) := Module.finrank_eq_card_basis (b.reindex e.symm)
    _ = _ := by simp only [BandSlots, bandCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin]
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
noncomputable section
set_option maxHeartbeats 1000000
@[simp] theorem backShift_X_zero : backShift (MvPolynomial.X 0) = valueForm := by
  simp [backShift]
theorem backShift_X_of_ne (j : Fin 4) (h : j ≠ 0) :
    backShift (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [backShift, h]
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped Pointwise BigOperators
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
theorem bandSpace_mul {d e a b : ℕ} {lo hi low high : ℤ} {P Q : Form}
    (hp : P ∈ bandSpace d lo hi a) (hq : Q ∈ bandSpace e low high b) :
    P * Q ∈ bandSpace (d + e) (lo + low) (hi + high) (a + b) := by
  classical
  apply (mem_restrictSupport_iff Geom).mpr
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  obtain ⟨hdu, hlu, hhu, htu⟩ := (mem_restrictSupport_iff Geom).mp hp hu
  obtain ⟨hdv, hlv, hhv, htv⟩ := (mem_restrictSupport_iff Geom).mp hq hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [map_add, hdu, hdv]
  · simpa only [map_add, Nat.cast_add] using add_le_add hlu hlv
  · simpa only [map_add, Nat.cast_add] using add_le_add hhu hhv
  · exact Nat.add_le_add htu htv
private abbrev x₀ : Form := MvPolynomial.X 0
private abbrev x₁ : Form := MvPolynomial.X 1
private abbrev x₂ : Form := MvPolynomial.X 2
private abbrev x₃ : Form := MvPolynomial.X 3
theorem monomial_band (a b c f : ℕ) {d top : ℕ} {lo hi : ℤ}
    (hd : a + b + c + f = d) (hlo : lo ≤ (b + 2 * c + 3 * f : ℕ))
    (hhi : (b + 2 * c + 3 * f : ℕ) ≤ hi) (hf : f ≤ top) :
    x₀ ^ a * x₁ ^ b * x₂ ^ c * x₃ ^ f ∈ bandSpace d lo hi top := by
  let u : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![a, b, c, f]
  have hval (i : Fin 4) : u i = ![a, b, c, f] i := by simp [u]
  have he : BandExponent d lo hi top u := by
    simpa [BandExponent, degree_formula, jetIndex_formula, hval] using ⟨hd, hlo, hhi, hf⟩
  have hm : monomial u (1 : Geom) ∈ bandSpace d lo hi top :=
    (monomial_mem_restrictSupport Geom).mpr (Or.inl he)
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    MvPolynomial.C_1, one_mul] at hm
  simpa [hval] using hm
theorem capX (i : Fin 4) :
    MvPolynomial.X (R := Geom) i ∈ restrictWeightedOrder targetOrder (targetOrder i) :=
  X_mem_restrictWeightedOrder _ _ le_rfl
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
noncomputable section
set_option maxHeartbeats 1800000
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
end
end K1_13_1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem genericCutLength_sliceIdeal (surface : Ideal GeoJets) (a h : Shape) :
    genericCutLength (sliceIdeal surface h) a = surfaceDegree surface a h := by
  classical
  let H₀ := MvPolynomial (SectionIndex h) GeoField
  let H := SectionField h
  let B := MvPolynomial (PairSectionIndex a h) GeoField
  let N := MvPolynomial (SectionIndex a) H₀
  let S := MvPolynomial (SectionIndex a) H
  let F := PairSectionField a h
  let T := CutField H a
  let M : Submonoid N := (nonZeroDivisors H₀).map MvPolynomial.C
  have : IsLocalization M S := MvPolynomial.isLocalization (nonZeroDivisors H₀) H
  have hcomap : (nonZeroDivisors S).comap (algebraMap N S) = nonZeroDivisors N := by
    have hinj : Function.Injective (algebraMap N S) :=
      MvPolynomial.map_injective _ (IsFractionRing.injective H₀ H)
    ext z
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  have : IsFractionRing N T := by
    change IsLocalization (nonZeroDivisors N) T
    rw [← hcomap]
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units M
      (nonZeroDivisors S) T (fun _ hu => hu.mem_nonZeroDivisors)
  let s : B ≃+* N := (sumAlgEquiv GeoField (SectionIndex a) (SectionIndex h)).toRingEquiv
  let e : F ≃+* T := IsFractionRing.ringEquivOfRingEquiv s
  let r := MvPolynomial.mapEquiv (Fin 4) e
  let mapF : GeoJets →+* MvPolynomial (Fin 4) F := MvPolynomial.map (algebraMap GeoField F)
  let mapT : SectionJets h →+* MvPolynomial (Fin 4) T := MvPolynomial.map (algebraMap H T)
  have ebase (x : B) :
      e (algebraMap B F x) = algebraMap S T (algebraMap N S (s x)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap s x
  have eC (c : GeoField) :
      e (algebraMap GeoField F c) = algebraMap H T (algebraMap GeoField H c) := by
    change e (algebraMap B F (MvPolynomial.C c)) = _
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.C c))) = _
    rw [sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rfl
  have eX₁ (m : SectionIndex a) :
      e (algebraMap B F (MvPolynomial.X (Sum.inl m))) = algebraMap S T (MvPolynomial.X m) := by
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.X (Sum.inl m)))) = _
    rw [sumAlgEquiv_X_inl, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
  have eX₂ (m : SectionIndex h) :
      e (algebraMap B F (MvPolynomial.X (Sum.inr m))) = algebraMap H T (algebraMap H₀ H (MvPolynomial.X m)) := by
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.X (Sum.inr m)))) = _
    rw [sumAlgEquiv_X_inr, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rfl
  have hr₀ : r.toRingHom.comp mapF = mapT.comp (sliceMap h) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [r, mapF, mapT, sliceMap, eC]
      rfl
    · intro i
      simp [r, mapF, mapT, sliceMap]
  have hr₁ : r.toRingHom (sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h)) =
      cutPolynomial H a := by
    simp [r, sectionWith, cutPolynomial]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun c : T => MvPolynomial.C c * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val)
      (eX₁ m)
  have hr₂ : r.toRingHom (sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)) =
      mapT (genericSection h) := by
    simp [r, mapT, sectionWith, genericSection]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun c : T => MvPolynomial.C c * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val)
      (eX₂ m)
  let J := surface.map mapF ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  let J' := (sliceIdeal surface h).map mapT ⊔ Ideal.span {cutPolynomial H a}
  have hJ : J' = J.map r.toRingHom := by
    simp only [J, J', sliceIdeal, Ideal.span_insert, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, Ideal.map_map, hr₀, hr₁, hr₂]
    let baseIdeal := surface.map (mapT.comp (sliceMap h))
    let first := Ideal.span {cutPolynomial H a}
    let second := Ideal.span {mapT (genericSection h)}
    change (baseIdeal ⊔ second) ⊔ first = baseIdeal ⊔ (first ⊔ second)
    calc
      _ = baseIdeal ⊔ (second ⊔ first) := sup_assoc _ _ _
      _ = _ := congrArg (baseIdeal ⊔ ·) (sup_comm _ _)
  let j := Ideal.quotientEquiv J J' r hJ
  have hc : (algebraMap T (MvPolynomial (Fin 4) T ⧸ J')).comp e.toRingHom =
      j.toRingHom.comp (algebraMap F (MvPolynomial (Fin 4) F ⧸ J)) := by
    apply RingHom.ext
    intro c
    change Ideal.Quotient.mk J' (MvPolynomial.C (e c)) = j (Ideal.Quotient.mk J (MvPolynomial.C c))
    rw [show j (Ideal.Quotient.mk J (MvPolynomial.C c)) = Ideal.Quotient.mk J' (r (MvPolynomial.C c)) from rfl]
    simp [r]
  exact (Algebra.finrank_eq_of_equiv_equiv e j hc).symm
end
end K1_13_6_1_4_1
end
section
namespace K1_13_6_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
abbrev JetPoint := Fin 4 → GeoField
abbrev GeoJets5 := MvPolynomial (Fin 5) GeoField
def actualPoint (S : (Polynomial Geom)) : JetPoint := fun i => genericCoeffs (jet S i)
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def member : GeoJets := toGeneric (membershipTest b.g)
def next : GeoJets := toGeneric (nextTest b.g)
def Contains (p : JetPoint) : Prop :=
  b.curve ≤ RingHom.ker (MvPolynomial.eval p) ∧ MvPolynomial.eval p b.sigma ≠ 0
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
end Branch
def OldBox {n : ℕ} (old : Fin 4 → Fin n) (p : Shape)
    (D : MvPolynomial (Fin n) GeoField) : Prop :=
  ∀ m ∈ D.support,
    (∑ i : Fin 4, m (old i)) ≤ p.b ∧
    (∑ i : Fin 4, i.val * m (old i)) ≤ p.j ∧ m (old 3) ≤ p.t
abbrev Box4 := OldBox (id : Fin 4 → Fin 4)
def Box5 (p : Shape) (d : ℕ) (D : GeoJets5) : Prop :=
  OldBox Fin.castSucc p D ∧ ∀ m ∈ D.support, m (Fin.last 4) ≤ d
def graphBox (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
def Chart4 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box4 (chart (taylorLength + 1) p) b.member ∧
    Box4 (chart (taylorLength + 2) p) b.next ∧
    ∀ x a : K, ∃ D, Box4 (chart (taylorLength + 2) p) D ∧
      ∀ S : (Polynomial K), S.natDegree ≤ 133671 → b.Contains (actualPoint (extend S)) →
        (MvPolynomial.eval (actualPoint (extend S)) D = 0 ↔ S.eval x = a)
end
end K1_13_6_2
end
section
namespace K1_13_6_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
theorem actualPoint_injective : Function.Injective actualPoint := by
  intro S T h
  have h₀ := congrFun h (0 : Fin 4)
  exact genericCoeffs_injective (by simpa [actualPoint, jet, hasseDeriv_zero'] using h₀)
namespace Branch
variable {f Q : Row 4} {l : ℕ}
end Branch
def Demand (A : Finset K) (s : K → (Polynomial K)) (T : Finset K) : Prop := by
  classical
  exact T.card = 1 ∨ ∃ x a, (∃ γ ∈ A, (s γ).eval x ≠ a) ∧
    T = A.filter (fun γ => (s γ).eval x = a)
theorem maximal_demand (A : Finset K) (s : K → (Polynomial K)) (hA : A.Nonempty) :
    ∃ T ⊆ A, 0 < T.card ∧ CurveSections A s T.card ∧ Demand A s T := by
  classical
  let candidates := A.powerset.filter (Demand A s)
  obtain ⟨γ, hγ⟩ := hA
  have hsingle : {γ} ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hγ),
      Or.inl (Finset.card_singleton γ)⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_, hsingle⟩
  have hpositive : 1 ≤ T.card := by simpa using hmax _ hsingle
  refine ⟨T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1, hpositive, ?_,
    (Finset.mem_filter.mp hT).2⟩
  intro x a ha
  exact hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    Or.inr ⟨x, a, ha, rfl⟩⟩)
end
end K1_13_6_2
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6
open scoped BigOperators
def ChamberBox (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j ∧ 0 < p.t
def capExponents (p : Shape) : Set (Fin 4 →₀ ℕ) :=
  {m | m.degree ≤ 2 * p.b ∧ (∑ i : Fin 4, i.val * m i) ≤ 2 * p.j ∧ m 3 ≤ 2 * p.t}
instance (p : Shape) : Finite (capExponents p) :=
  ((Finsupp.finite_of_degree_le (2 * p.b)).subset (fun _ hm => hm.1 :
    capExponents p ⊆ {m | m.degree ≤ 2 * p.b})).to_subtype
abbrev dimension (J : Ideal GeoJets) := (MvPolynomial.affineHilbertPolynomial J).natDegree
def capCoeff (J : Ideal GeoJets) (d : ℕ) (p : Shape) : ℚ :=
  (MvPolynomial.affineHilbertPolynomial
    (J.comap (MvPolynomial.monomialMap GeoField (capExponents p)).toRingHom)).coeff d
def polarize (H : Shape → ℚ) : List Shape → Shape → ℚ
  | [] => H
  | p :: rest => fun x => polarize H rest (x.plus p) - polarize H rest x
def mixedDegree (J : Ideal GeoJets) (boxes : List Shape) : ℚ :=
  polarize (capCoeff J boxes.length) boxes ⟨3, 3, 1⟩ / 2 ^ boxes.length
def localWeight (J P : Ideal GeoJets) : ℕ := by
  classical
  exact if hp : P.IsPrime then (cycleLength J P hp).toNat else 0
def pointIdeal (x : K1_13_6_2.JetPoint) : Ideal GeoJets := RingHom.ker (MvPolynomial.eval x)
end
end K1_13_6_2_3
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
lemma chart_box (L : ℕ) (p : Shape) (hL : 0 < L) : ChamberBox (chart L p) := by
  refine ⟨(K1_13_7_1.chart_chamber L p).1, (K1_13_7_1.chart_chamber L p).2, ?_⟩
  unfold chart
  have h : 3 ≤ 2 * L * (p.j - 3) + L + 3 := by omega
  exact lt_min (by omega) (Nat.div_pos h (by decide))
lemma generic_box {P : Row 4} {p : Shape} (hP : InBox (shape P) p) : Box4 p (toGeneric P) := by
  intro m hm
  have hm' := MvPolynomial.support_map_subset genericCoeffs P hm
  have hb := (MvPolynomial.le_totalDegree hm').trans hP.1
  have hj := (Finset.le_sup (f := fun m : Fin 4 →₀ ℕ => m.sum fun i a => i.val * a) hm').trans hP.2.1
  refine ⟨?_, ?_, (MvPolynomial.monomial_le_degreeOf 3 hm').trans hP.2.2⟩
  · simpa [Finsupp.degree_apply, Finsupp.sum_fintype] using hb
  · simpa [Finsupp.sum_fintype] using hj
lemma regular_cut {J : Ideal GeoJets} (hJ : J.IsPrime) {D : GeoJets} (hD : D ∉ J) :
    IsLeftRegular (Ideal.Quotient.mk J D) := by
  have := hJ
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
lemma cut_dimension {J : Ideal GeoJets} {D : GeoJets} (hD : IsLeftRegular (Ideal.Quotient.mk J D)) :
    dimension (J ⊔ Ideal.span {D}) ≤ dimension J - 1 :=
  (MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hD le_rfl).1
lemma dimension_bot : dimension (⊥ : Ideal GeoJets) = 4 := by
  simp [MvPolynomial.natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card]
lemma pair_regular (f Q : Row 4) (h : IsRelPrime (toGeneric f) (toGeneric Q)) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {toGeneric f}) (toGeneric Q)) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left hx))
lemma intersection_eq (f Q : Row 4) :
    intersectionIdeal f Q = Ideal.span {toGeneric f} ⊔ Ideal.span {toGeneric Q} := by
  rw [intersectionIdeal, ← Ideal.span_union]
  rfl
lemma surface_dimension {f Q : Row 4} (hf : toGeneric f ≠ 0)
    (hproper : IsRelPrime (toGeneric f) (toGeneric Q))
    {S : Ideal GeoJets} (hZ : (intersectionIdeal f Q).IsMinimalPrime S) : dimension S = 2 := by
  have := hZ.isPrime
  rw [intersection_eq] at hZ
  obtain ⟨P, hP, hPZ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hZ.le)
  have := hP.isPrime
  have hPdim := MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf hP
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hPdim
  have hPle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP
  have hPbot : P ≠ ⊥ := by
    intro heq
    exact hf (Ideal.mem_bot.mp (heq ▸ hP.le (Ideal.mem_span_singleton_self (toGeneric f))))
  have hPheight : P.height = 1 := le_antisymm hPle (by
    simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hPbot))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight).principal
  change P = Ideal.span {a} at ha
  have hQ : toGeneric Q ∉ P := by
    intro hQ
    have hfa : a ∣ toGeneric f := Ideal.mem_span_singleton.mp (ha ▸ hP.le (Ideal.mem_span_singleton_self _))
    have hQa : a ∣ toGeneric Q := Ideal.mem_span_singleton.mp (ha ▸ hQ)
    exact Ideal.IsPrime.ne_top' (ha.trans (Ideal.span_singleton_eq_top.mpr (hproper hfa hQa)))
  have hmin : S ∈ (P ⊔ Ideal.span {toGeneric Q}).minimalPrimes := by
    refine ⟨⟨hZ.isPrime, sup_le hPZ (le_sup_right.trans hZ.le)⟩, fun U hU hUZ => ?_⟩
    exact hZ.2 ⟨hU.1, sup_le (hP.le.trans (le_sup_left.trans hU.2)) (le_sup_right.trans hU.2)⟩ hUZ
  have h := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hQ hmin
  change dimension S + 1 = dimension P at h
  change dimension P + 1 = 4 at hPdim
  omega
lemma positive_length {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) :
    0 < cycleLength J P hP.isPrime ∧ cycleLength J P hP.isPrime ≠ ⊤ := by
  have := hP.isPrime
  let A := Localization.AtPrime P
  let L := J.map (algebraMap GeoJets A)
  change 0 < Module.length A (A ⧸ L) ∧ Module.length A (A ⧸ L) ≠ ⊤
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    rw [show L = J.map (algebraMap GeoJets A) from rfl,
      IsLocalization.minimalPrimes_map P.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hP
  have hL : L ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hmin.le))
  have : Nontrivial (A ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact ⟨Module.length_pos, Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := L))⟩)⟩
lemma weight_cast {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) :
    (localWeight J P : ℕ∞) = cycleLength J P hP.isPrime := by
  rw [localWeight, dite_eq_left hP.isPrime, ENat.natCast_toNat (positive_length hP).2]
lemma weight_pos {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) : 0 < localWeight J P := by
  exact ENat.natCast_lt_natCast.mp ((weight_cast hP).symm ▸ (positive_length hP).1)
lemma point_injective : Function.Injective pointIdeal := by
  intro x y heq
  funext i
  have hm : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    simp [pointIdeal, RingHom.mem_ker]
  rw [heq] at hm
  exact (sub_eq_zero.mp (by simpa [pointIdeal, RingHom.mem_ker] using hm)).symm
lemma aeval_surjective (x : JetPoint) :
    Function.Surjective (MvPolynomial.aeval x : GeoJets →ₐ[GeoField] GeoField) :=
  fun a => ⟨MvPolynomial.C a, by simp⟩
lemma point_prime (x : JetPoint) : (pointIdeal x).IsPrime := RingHom.ker_isPrime _
lemma point_dimension (x : JetPoint) : dimension (pointIdeal x) = 0 := by
  let φ : GeoJets →ₐ[GeoField] GeoField := MvPolynomial.aeval x
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := φ) (aeval_surjective x)
  have : Module.Finite GeoField (GeoJets ⧸ pointIdeal x) := Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
  exact MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mpr inferInstance
lemma point_degree (x : JetPoint) : mixedDegree (pointIdeal x) [] = 1 := by
  let φ := MvPolynomial.monomialMap GeoField (capExponents ⟨3, 3, 1⟩)
  have hsφ : Function.Surjective φ := by
    apply MvPolynomial.monomialMap_surjective
    intro i
    fin_cases i <;> simp [capExponents, Fin.sum_univ_four]
  let ψ := (MvPolynomial.aeval x).comp φ
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := ψ) ((aeval_surjective x).comp hsφ)
  have : Module.Finite GeoField (_ ⧸ RingHom.ker ψ) :=
    Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
  change (MvPolynomial.affineHilbertPolynomial (RingHom.ker ψ)).coeff 0 / (2 : ℚ) ^ 0 = 1
  rw [MvPolynomial.affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero,
    e.toLinearEquiv.finrank_eq, Module.finrank_self]
  norm_num
lemma point_proper_section {C : Ideal GeoJets} (hC : dimension C = 1) {p : Shape}
    (hp : ChamberBox p) (x : JetPoint) (hx : C ≤ pointIdeal x) :
    ∃ D : GeoJets, Box4 p D ∧ D ∉ C ∧ MvPolynomial.eval x D = 0 := by
  have h : ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (x i) ∉ C := by
    by_contra! hall
    let constants := (Ideal.Quotient.mk C).comp MvPolynomial.C
    have heq : constants.comp (MvPolynomial.eval x) = Ideal.Quotient.mk C := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [constants]
      · intro i
        have hi := Ideal.Quotient.eq_zero_iff_mem.mpr (hall i)
        rw [map_sub, sub_eq_zero] at hi
        simpa [constants] using hi.symm
    have hincl : pointIdeal x ≤ C := by
      intro D hD
      have hz : MvPolynomial.eval x D = 0 := hD
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← DFunLike.congr_fun heq D, RingHom.comp_apply, hz, map_zero]
    have hd := point_dimension x
    rw [le_antisymm hx hincl, hd] at hC
    omega
  obtain ⟨i, hi⟩ := h
  refine ⟨MvPolynomial.X i - MvPolynomial.C (x i), ?_, hi, by simp⟩
  intro m hm
  have hm' := MvPolynomial.support_sub (Fin 4) (MvPolynomial.X i) (MvPolynomial.C (x i)) hm
  rw [Finset.mem_union] at hm'
  obtain hX | hConst := hm'
  · rw [MvPolynomial.support_X] at hX
    have he := Finset.mem_singleton.mp hX
    subst m
    have hb : 1 ≤ p.b := by have := hp.1; have := hp.2.1; have := hp.2.2; omega
    have hj : i.val ≤ p.j := by have := i.isLt; have := hp.2.1; have := hp.2.2; omega
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finsupp.single_apply] using hb
    · simpa [Finsupp.single_apply] using hj
    · simp only [id_eq, Finsupp.single_apply]
      split <;> have := hp.2.2 <;> omega
  · have he : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hConst) (by simp [MvPolynomial.coeff_C, Ne.symm h])
    subst m
    simp
end
end K1_13_6_2_3
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
def c1 : Prop :=
  ∀ p : Shape, ChamberBox p →
    capCoeff (⊥ : Ideal GeoJets) 4 p = 16 * (volume32 p : ℚ) / 32
def c2 : Prop :=
  ∀ (J : Ideal GeoJets) (p : Shape) (boxes : List Shape),
    ChamberBox p → (∀ q ∈ boxes, ChamberBox q) → dimension J ≤ boxes.length + 1 →
    ∀ D : GeoJets, Box4 p D → IsLeftRegular (Ideal.Quotient.mk J D) →
      mixedDegree (J ⊔ Ideal.span {D}) boxes ≤ mixedDegree J (p :: boxes)
def c3 : Prop :=
  ∀ (J : Ideal GeoJets) (boxes : List Shape),
    (∀ q ∈ boxes, ChamberBox q) → dimension J ≤ boxes.length →
    ∀ S : Finset (Ideal GeoJets), (∀ P ∈ S, J.IsMinimalPrime P) →
      (∑ P ∈ S, (localWeight J P : ℚ) * mixedDegree P boxes) ≤ mixedDegree J boxes
private lemma chamber_plus {x y : Shape} (hx : ChamberBox x) (hy : ChamberBox y) :
    ChamberBox (x.plus y) := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  refine ⟨Nat.add_le_add hx₁ hy₁, ?_, Nat.add_pos_left hx₃ _⟩
  change 3 * (x.t + y.t) ≤ x.j + y.j
  omega
end
end K1_13_6_2_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6_2_3
open scoped Pointwise
theorem cap_coords (p : Shape) (e : Fin 4 →₀ ℕ) :
    e ∈ capExponents p ↔
      e 0 + e 1 + e 2 + e 3 ≤ 2 * p.b ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ 2 * p.j ∧ e 3 ≤ 2 * p.t := by
  unfold capExponents
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_four, add_assoc]
theorem zero_mem_cap (p : Shape) : 0 ∈ capExponents p := by
  simp [cap_coords]
theorem cap_add {p q : Shape} (hp : ChamberBox p) (hq : ChamberBox q) :
    capExponents p + capExponents q = capExponents (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [cap_coords, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb, hpj, _⟩ := hp
    obtain ⟨hqb, hqj, _⟩ := hq
    rw [cap_coords] at he
    simp only [Shape.plus] at he
    let z := min (e 3) (2 * p.t)
    let z' := e 3 - z
    have hz : z + z' = e 3 ∧ z ≤ 2 * p.t ∧ z' ≤ 2 * q.t := by dsimp [z, z']; omega
    let w := 2 * p.j - 3 * z
    let w' := 2 * q.j - 3 * z'
    have hw : w + 3 * z = 2 * p.j ∧ w' + 3 * z' = 2 * q.j := by
      dsimp [w, w']
      omega
    have hhalf : (w + w') / 2 = w / 2 + w' / 2 := by
      by_cases h : e 3 ≤ 2 * p.t
      · have hz' : z' = 0 := by dsimp [z, z']; omega
        omega
      · have hze : z = 2 * p.t := min_eq_right (by omega)
        omega
    let y := min (e 2) (w / 2)
    let y' := e 2 - y
    have hy : y + y' = e 2 ∧ 2 * y ≤ w ∧ 2 * y' ≤ w' := by dsimp [y, y']; omega
    let x := min (e 1) (w - 2 * y)
    let x' := e 1 - x
    have hx : x + x' = e 1 ∧ x + 2 * y ≤ w ∧ x' + 2 * y' ≤ w' := by
      dsimp [x, x']
      omega
    let u := min (e 0) (2 * p.b - (x + y + z))
    let u' := e 0 - u
    have hu : u + u' = e 0 ∧ u + x + y + z ≤ 2 * p.b ∧
        u' + x' + y' + z' ≤ 2 * q.b := by
      dsimp [u, u']
      omega
    let a : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u, x, y, z]
    let b : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u', x', y', z']
    refine ⟨a, (cap_coords p a).mpr ?_, b, (cap_coords q b).mpr ?_, ?_⟩
    · change u + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧ z ≤ 2 * p.t
      omega
    · change u' + x' + y' + z' ≤ 2 * q.b ∧ x' + 2 * y' + 3 * z' ≤ 2 * q.j ∧ z' ≤ 2 * q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
theorem nsmul_cap (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    n • capExponents p = capExponents (p.scale n) := by
  induction n with
  | zero =>
      rw [zero_smul]
      ext e
      simp only [Set.mem_zero, cap_coords, Shape.scale, zero_mul, mul_zero]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h, _, _⟩
        ext i
        fin_cases i
        · change e 0 = 0; omega
        · change e 1 = 0; omega
        · change e 2 = 0; omega
        · change e 3 = 0; omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Shape.scale]
      have hscaled : ChamberBox (p.scale n) := by
        obtain ⟨hb, hj, ht⟩ := hp
        refine ⟨Nat.mul_le_mul_left n hb, ?_, Nat.mul_pos (Nat.pos_of_ne_zero hn) ht⟩
        change 3 * (n * p.t) ≤ n * p.j
        rw [Nat.mul_left_comm 3 n]
        exact Nat.mul_le_mul_left n hj
      rw [succ_nsmul, ih, cap_add hscaled hp]
      congr 1
      cases p
      simp [Shape.plus, Shape.scale, Nat.succ_mul]
end K1_13_6_2_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6_2_3 Finset
open scoped BigOperators
noncomputable section
private def slices (b j t : ℕ) :=
  Σ z : Fin (2 * t + 1), Σ y : Fin ((2 * j - 3 * z.val) / 2 + 1),
    Σ x : Fin (2 * j - 3 * z.val - 2 * y.val + 1),
      Fin (2 * b - (z.val + y.val + x.val) + 1)
private def cap_slices (p : Shape) (hp : ChamberBox p) :
    capExponents p ≃ slices p.b p.j p.t where
  toFun e := by
    have he := (cap_coords p e.val).mp e.property
    have hb := he.1
    have hj := he.2.1
    have ht := he.2.2
    let z : Fin (2 * p.t + 1) := ⟨e.val 3, by omega⟩
    let y : Fin ((2 * p.j - 3 * z.val) / 2 + 1) := ⟨e.val 2, by dsimp [z]; omega⟩
    let x : Fin (2 * p.j - 3 * z.val - 2 * y.val + 1) := ⟨e.val 1, by dsimp [z, y]; omega⟩
    exact ⟨z, y, x, ⟨e.val 0, by dsimp [z, y, x]; omega⟩⟩
  invFun a := by
    rcases a with ⟨z, y, x, u⟩
    have hz := z.isLt
    have hy := y.isLt
    have hx := x.isLt
    have hu := u.isLt
    have hb := hp.1
    have hj := hp.2.1
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val, x.val, y.val, z.val], (cap_coords p _).mpr ?_⟩
    change u.val + x.val + y.val + z.val ≤ 2 * p.b ∧
      x.val + 2 * y.val + 3 * z.val ≤ 2 * p.j ∧ z.val ≤ 2 * p.t
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv a := by
    rcases a with ⟨⟨z, hz⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨u, hu⟩⟩
    rfl
theorem sum_affine (a d : ℚ) (n : ℕ) :
    (∑ x ∈ range n, (a + d * (x : ℚ))) = n * a + d * n * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
def slice (W C : ℕ) : ℚ :=
  ((C : ℚ) + 1 - (W : ℚ) / 2) *
    ((W / 2 : ℕ) + (1 : ℚ)) * ((W / 2 : ℕ) + (1 : ℚ) + (W % 2 : ℕ))
theorem slice_count (W C : ℕ) (h : W ≤ C) :
    (∑ y ∈ range (W / 2 + 1), ∑ x ∈ range (W - 2 * y + 1),
      ((C - (y + x) + 1 : ℕ) : ℚ)) = slice W C := by
  calc
    _ = ∑ y ∈ range (W / 2 + 1),
        (((C : ℚ) + 1 - (W : ℚ) / 2) * ((W : ℚ) + 1 - 2 * (y : ℚ))) := by
      apply sum_congr rfl
      intro y hy
      have hy' := mem_range.mp hy
      calc
        _ = ∑ x ∈ range (W - 2 * y + 1), ((C : ℚ) - y + 1 + (-1) * (x : ℚ)) := by
          apply sum_congr rfl
          intro x hx
          have hx' := mem_range.mp hx
          have hxy : y + x ≤ C := by omega
          push_cast [Nat.cast_sub hxy]
          ring
        _ = _ := by
          rw [sum_affine]
          have h2y : 2 * y ≤ W := by omega
          push_cast [Nat.cast_sub h2y]
          ring
    _ = _ := by
      rw [← mul_sum]
      have hlin (y : ℕ) : (W : ℚ) + 1 - 2 * (y : ℚ) = (W : ℚ) + 1 + (-2) * (y : ℚ) := by
        ring
      simp_rw [hlin]
      rw [sum_affine]
      have hW : (W : ℚ) = 2 * ((W / 2 : ℕ) : ℚ) + ((W % 2 : ℕ) : ℚ) := by
        exact_mod_cast (show W = 2 * (W / 2) + W % 2 by omega)
      unfold slice
      push_cast
      rw [hW]
      ring
private theorem cap_count (p : Shape) (hp : ChamberBox p) :
    ((capExponents p).ncard : ℚ) =
      ∑ z ∈ range (2 * p.t + 1), slice (2 * p.j - 3 * z) (2 * p.b - z) := by
  classical
  let : Fintype (slices p.b p.j p.t) := by unfold slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cap_slices p hp), Nat.card_eq_fintype_card]
  change (Fintype.card (Σ z : Fin (2 * p.t + 1), Σ y : Fin ((2 * p.j - 3 * z.val) / 2 + 1),
    Σ x : Fin (2 * p.j - 3 * z.val - 2 * y.val + 1),
      Fin (2 * p.b - (z.val + y.val + x.val) + 1)) : ℚ) = _
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun z => ∑ y : Fin ((2 * p.j - 3 * z) / 2 + 1),
    ∑ x : Fin (2 * p.j - 3 * z - 2 * y.val + 1), ((2 * p.b - (z + y.val + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro z _
  have hW : 2 * p.j - 3 * z ≤ 2 * p.b - z := by have := hp.1; omega
  rw [← slice_count _ _ hW]
  rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin (2 * p.j - 3 * z - 2 * y + 1),
    ((2 * p.b - (z + y + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro y _
  rw [Fin.sum_univ_eq_sum_range (fun x => ((2 * p.b - (z + y + x) + 1 : ℕ) : ℚ))]
  simp only [Nat.sub_sub, Nat.add_assoc]
def evenSlice (b j i : ℚ) : ℚ := (j - 3 * i + 1) ^ 2 * (2 * b + 1 - j + i)
def oddSlice (b j i : ℚ) : ℚ :=
  (j - 3 * i - 1) * (j - 3 * i) * (2 * b + 3 / 2 - j + i)
private theorem slice_even (b j i : ℕ) (hi : 3 * i ≤ j) (hb : j ≤ b) :
    slice (2 * j - 3 * (2 * i)) (2 * b - 2 * i) = evenSlice b j i := by
  have hW : 2 * j - 3 * (2 * i) = 2 * (j - 3 * i) := by omega
  have hC : 2 * i ≤ 2 * b := by omega
  rw [hW]
  simp only [slice, evenSlice, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.mul_mod_right, Nat.cast_zero, add_zero]
  push_cast [Nat.cast_sub hi, Nat.cast_sub hC]
  ring
private theorem slice_odd (b j i : ℕ) (hi : 3 * i + 3 ≤ j) (hb : j ≤ b) :
    slice (2 * j - 3 * (2 * i + 1)) (2 * b - (2 * i + 1)) = oddSlice b j i := by
  have hW : 3 * (2 * i + 1) ≤ 2 * j := by omega
  have hC : 2 * i + 1 ≤ 2 * b := by omega
  have hdiv : (2 * j - 3 * (2 * i + 1)) / 2 = j - (3 * i + 2) := by omega
  have hmod : (2 * j - 3 * (2 * i + 1)) % 2 = 1 := by omega
  simp only [slice, oddSlice, hdiv, hmod]
  push_cast [Nat.cast_sub hW, Nat.cast_sub hC, Nat.cast_sub (show 3 * i + 2 ≤ j by omega)]
  ring
theorem sum_pair (f : ℕ → ℚ) (n : ℕ) :
    (∑ z ∈ range (2 * n), f z) = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega]
    rw [sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring
def pair (b j i : ℚ) : ℚ := evenSlice b j i + oddSlice b j i
def pairedSum (b j n : ℚ) : ℚ :=
  let f := pair b j
  n * f 0 + n * (n - 1) / 2 * (f 1 - f 0) +
    n * (n - 1) * (n - 2) / 6 * (f 2 - 2 * f 1 + f 0) +
    n * (n - 1) * (n - 2) * (n - 3) / 24 * (f 3 - 3 * f 2 + 3 * f 1 - f 0)
theorem paired_sum (b j : ℚ) (n : ℕ) :
    (∑ i ∈ range n, pair b j i) = pairedSum b j n := by
  induction n with
  | zero => simp [pairedSum]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    dsimp [pairedSum, pair, evenSlice, oddSlice]
    ring
private theorem count_formula (p : Shape) (hp : ChamberBox p) :
    ((capExponents p).ncard : ℚ) = pairedSum p.b p.j p.t + evenSlice p.b p.j p.t := by
  rw [cap_count p hp, sum_range_succ, sum_pair, slice_even _ _ _ hp.2.1 hp.1, ← paired_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [slice_even _ _ _ (by have := hp.2.1; omega) hp.1,
    slice_odd _ _ _ (by have := hp.2.1; omega) hp.1]
  rfl
def latticePolynomial (p : Shape) : Polynomial ℚ :=
  let b : ℚ := p.b
  let j : ℚ := p.j
  let t : ℚ := p.t
  Polynomial.C (16 * (volume32 p : ℚ) / 32) * Polynomial.X ^ 4 +
    Polynomial.C (2*b*j^2 + 2*b*j*t - 3*b*t^2 - j^3 + (3/2)*j^2*t -
      (11/2)*j*t^2 + (13/2)*t^3) * Polynomial.X ^ 3 +
    Polynomial.C (4*b*j - b*t - j^2 + 2*j*t - (5/2)*t^2) * Polynomial.X ^ 2 +
    Polynomial.C (2*b + j - t/2) * Polynomial.X ^ 1 + Polynomial.C 1
theorem latticePolynomial_coeff (p : Shape) :
    (latticePolynomial p).coeff 4 = 16 * (volume32 p : ℚ) / 32 := by
  simp only [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  norm_num
theorem latticePolynomial_eval (p : Shape) (hp : ChamberBox p) (n : ℕ) (hn : 0 < n) :
    (latticePolynomial p).eval (n : ℚ) = ((capExponents (p.scale n)).ncard : ℚ) := by
  have hscaled : ChamberBox (p.scale n) := by
    obtain ⟨hb, hj, ht⟩ := hp
    refine ⟨Nat.mul_le_mul_left n hb, ?_, Nat.mul_pos hn ht⟩
    change 3 * (n * p.t) ≤ n * p.j
    rw [Nat.mul_left_comm 3 n]
    exact Nat.mul_le_mul_left n hj
  rw [count_formula _ hscaled]
  simp only [latticePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, pairedSum, pair, evenSlice, oddSlice, Shape.scale, volume32]
  push_cast
  ring
end
end K1_13_6_2_3_1
end
section
namespace K1_13_6_2_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_6_2 K1_13_7_1
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem topPartial_bound (w : Fin 4 → ℕ) (P : Row 4) :
    W w (separant P) ≤ W w P - w 3 :=
  weightedTotalDegree_pderiv_le_sub w 3 P
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + (B - w 3) + Δ := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h : w 3 ≤ d
    · have hp := (topPartial_bound w P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift g hg) hp).trans (by omega))
    · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero, weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem step_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) (a : ℕ) :
    W w (clearedStep g a P) ≤ d + (2 * (B - w 3) + Δ) := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (flow_bound w Δ hshift hB hg hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [← map_natCast (MvPolynomial.C : (Polynomial Geom) →+* Row 4)]
    exact (Nat.add_le_add ((weight_const_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep))
      hP).trans (by omega)
theorem jet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (jetNumerator g n) ≤ w 0 + n * (2 * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [jetNumerator, zero_mul, add_zero] using weight_X_le (R := (Polynomial Geom)) w 0
  | succ n ih =>
    simpa only [jetNumerator, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound w Δ hshift hB hg ih (2 * n)
theorem oldBox_of_fits {P : GeoJets} {p : Shape} (h : GeoFits P p) : Box4 p P := by
  intro m hm
  have h₁ := le_weightedTotalDegree (1 : Fin 4 → ℕ) hm
  have h₂ := (le_weightedTotalDegree Fin.val hm).trans h.2.1
  have h₃ := (le_weightedTotalDegree (Pi.single (3 : Fin 4) (1 : ℕ)) hm).trans
    (by simpa only [weightedTotalDegree_piSingle] using h.2.2)
  rw [weightedTotalDegree_one] at h₁
  refine ⟨?_, ?_, ?_⟩
  · have ht := h₁.trans h.1
    rw [Finsupp.weight_eq_sum] at ht
    simpa only [id_eq, Pi.one_apply, smul_eq_mul, mul_one] using ht
  · rw [Finsupp.weight_eq_sum] at h₂
    simpa only [id_eq, smul_eq_mul, Nat.mul_comm] using h₂
  · simpa only [id_eq, Finsupp.weight_single_one_apply] using h₃
private def topWeight : Fin 4 → ℕ := Pi.single 3 1
theorem fits_chart_of_weights (P : Row 4) (p : Shape) (L : ℕ)
    (hb : W 1 P ≤ 1 + 2 * L * (p.b - 1))
    (hj : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
    (ht : W topWeight P ≤ 2 * L * (p.t - 1) + L + 1) :
    GeoFits (toGeneric P) (chart L p) := by
  apply toGeneric_fits
  refine ⟨?_, ?_, ?_⟩
  · change P.totalDegree ≤ max _ _
    exact (by simpa only [weightedTotalDegree_one] using hb :
      P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
  · change indexDegree P ≤ _
    rwa [indexDegree_eq]
  · change P.degreeOf 3 ≤ min _ _
    apply le_min
    · simpa only [topWeight, weightedTotalDegree_piSingle] using ht
    · have h := (top_le_index P).trans hj
      omega
theorem three_weights {g P : Row 4} {p : Shape} {L : ℕ} (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t)
    (bound : ∀ (w : Fin 4 → ℕ) (Δ d₀ B : ℕ),
      (∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) → (∀ i, w i ≤ d₀) →
      w 3 ≤ B → W w g ≤ B → W w P ≤ d₀ + 2 * L * (B - w 3) + L * Δ) :
    GeoFits (toGeneric P) (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  have h₃ : W topWeight g ≤ p.t := by
    simpa only [topWeight, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, topWeight i.succ ≤ topWeight i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, topWeight i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : topWeight 3 = 1 := by decide
  apply fits_chart_of_weights
  · have h := bound 1 0 1 p.b (fun _ => by simp) (fun _ => le_rfl) hb h₁
    simpa only [Pi.one_apply, mul_zero, add_zero] using h
  · have h := bound Fin.val 1 3 p.j (fun _ => by rfl)
      (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂
    change W Fin.val P ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
    simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
  · have h := bound topWeight 1 1 p.t hshift hw (hw3.symm ▸ ht) h₃
    simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
theorem separant_pow_bound (w : Fin 4 → ℕ) {g : Row 4} {B : ℕ} (hg : W w g ≤ B) (a : ℕ) :
    W w (separant g ^ a) ≤ a * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans
    (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
theorem jet_fits {g : Row 4} {p : Shape} (hB : InBox (shape g) p) (hp : Chamber p)
    (ht : 0 < p.t) {n L : ℕ} (hn : n ≤ L) :
    GeoFits (toGeneric (jetNumerator g n)) (chart L p) := by
  apply three_weights hB hp ht
  intro w Δ d₀ B hshift hw hwB hg
  calc
    _ ≤ w 0 + n * (2 * (B - w 3) + Δ) := jet_bound w Δ hshift hwB hg n
    _ ≤ d₀ + L * (2 * (B - w 3) + Δ) :=
      Nat.add_le_add (hw 0) (Nat.mul_le_mul_right _ hn)
    _ = _ := by ring
end
end K1_13_6_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6 K1_13_6_2_3 MvPolynomial
open scoped Pointwise
noncomputable section
private theorem monomial_preimage (S : Set (Fin 4 →₀ ℕ)) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ n • S) :
    ∃ P : MvPolynomial S GeoField, P.totalDegree ≤ n ∧
      monomialMap GeoField S P = monomial e 1 := by
  induction n generalizing e with
  | zero =>
      simp only [zero_smul, Set.mem_zero] at he
      subst e
      exact ⟨1, by simp, by simp⟩
  | succ n ih =>
      rw [succ_nsmul] at he
      obtain ⟨a, ha, b, hb, rfl⟩ := he
      obtain ⟨P, hn, hP⟩ := ih a ha
      refine ⟨P * MvPolynomial.X ⟨b, hb⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
      · simpa only [totalDegree_X] using Nat.add_le_add_right hn 1
      · rw [map_mul, hP, monomialMap_X, monomial_mul_monomial, mul_one]
private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega
theorem cap_hilbert_count (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    affineHilbertFunction
        ((⊥ : Ideal GeoJets).comap (monomialMap GeoField (capExponents p)).toRingHom) n =
      (capExponents (p.scale n)).ncard := by
  classical
  let φ := monomialMap GeoField (capExponents p)
  let I := RingHom.ker φ.toRingHom
  let g : (MvPolynomial (capExponents p) GeoField ⧸ I) ≃ₐ[GeoField] GeoJets :=
    Ideal.quotientKerAlgEquivOfSurjective (f := φ) (cap_surjective p hp)
  have hg (P : MvPolynomial (capExponents p) GeoField) : g (Ideal.Quotient.mk I P) = φ P :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (f := φ) (cap_surjective p hp) P
  let M := restrictSupport GeoField (capExponents (p.scale n))
  have hmap : (quotientDegreeLE I n).map g.toLinearEquiv.toLinearMap = M := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hv
      change g (Ideal.Quotient.mk I P) ∈ M
      rw [hg]
      dsimp [M]
      rw [← nsmul_cap p hp n]
      exact monomialMap_mem_restrictSupport_nsmul (zero_mem_cap p) hP
    · dsimp [M]
      rw [restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      rw [← nsmul_cap p hp n] at he
      obtain ⟨P, hN, hP⟩ := monomial_preimage _ n e he
      refine ⟨Ideal.Quotient.mk I P, mk_mem_quotientDegreeLE hN, ?_⟩
      change g (Ideal.Quotient.mk I P) = monomial e 1
      rw [hg]
      exact hP
  change affineHilbertFunction I n = _
  calc
    _ = Module.finrank GeoField ((quotientDegreeLE I n).map g.toLinearEquiv.toLinearMap) :=
      (g.toLinearEquiv.finrank_map_eq _).symm
    _ = Module.finrank GeoField M := by rw [hmap]
    _ = _ := by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _), Nat.card_coe_set_eq]
theorem proof : K1_13_6_2_3.c1 := by
  intro p hp
  let I := (⊥ : Ideal GeoJets).comap (monomialMap GeoField (capExponents p)).toRingHom
  have hP : affineHilbertPolynomial I = latticePolynomial p := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_eval_affineHilbertPolynomial I, Filter.eventually_ge_atTop 1]
      with n hn hn₁
    rw [hn, cap_hilbert_count p hp n, latticePolynomial_eval p hp n hn₁]
  change (affineHilbertPolynomial I).coeff 4 = _
  rw [hP, latticePolynomial_coeff]
end
end K1_13_6_2_3_1
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
abbrev Exponent := Fin 5 →₀ ℕ
abbrev Boxes := Fin 5 → Shape × ℕ
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def Allowed (a : Shape × ℕ) (m : Exponent) : Prop :=
  (∑ i : Fin 4, m i.castSucc) ≤ a.1.b ∧
  (∑ i : Fin 4, i.val * m i.castSucc) ≤ a.1.j ∧
  m (Fin.castSucc (3 : Fin 4)) ≤ a.1.t ∧ m (Fin.last 4) ≤ a.2
def latticePoints (a : Shape × ℕ) : Set Exponent :=
  {m | Allowed (a.1.scale 2, 2 * a.2) m}
instance latticePointsFinite (a : Shape × ℕ) : Finite (latticePoints a) := by
  apply Set.Finite.to_subtype
  refine (Finsupp.finite_of_degree_le (2 * a.1.b + 2 * a.2)).subset ?_
  intro m hm
  change m.degree ≤ _
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
  exact Nat.add_le_add hm.1 hm.2.2.2
def Admissible (B : Boxes) : Prop :=
  (∀ i, Chamber (B i).1) ∧ (∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ latticePoints (B i))
def diagonalExponents (B : Boxes) (t : Fin 5 → ℕ) : Set Exponent :=
  {m | ∃ u : (i : Fin 5) → Fin (t i) → Exponent,
    (∀ i j, u i j ∈ latticePoints (B i)) ∧ m = ∑ i, ∑ j, u i j}
instance diagonalExponentsFinite (B : Boxes) (t : Fin 5 → ℕ) :
    Finite (diagonalExponents B t) := by
  let addExponents (u : (i : Fin 5) → Fin (t i) → latticePoints (B i)) : Exponent :=
    ∑ i, ∑ j, (u i j).val
  have heq : diagonalExponents B t = Set.range addExponents := by
    ext m
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i j => ⟨u i j, hu i j⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨fun i j => (u i j).val, fun i j => (u i j).property, rfl⟩
  rw [heq]
  exact (Set.finite_range _).to_subtype
def mixedDegree (B : Boxes) (P : Ideal GeoJets5) (I : Finset (Fin 5)) : ℚ :=
  (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
    (MvPolynomial.affineHilbertPolynomial (Ideal.comap
      (MvPolynomial.monomialMap GeoField (diagonalExponents B (fun i => if i ∈ J then 2 else 1)))
      P)).coeff I.card) / (2 : ℚ) ^ I.card
def OfDim (P : Ideal GeoJets5) (d : ℕ) : Prop :=
  ringKrullDim (GeoJets5 ⧸ P) = ((d : ℕ∞) : WithBot ℕ∞)
def DimLE (P : Ideal GeoJets5) (d : ℕ) : Prop :=
  ringKrullDim (GeoJets5 ⧸ P) ≤ ((d : ℕ∞) : WithBot ℕ∞)
def sectionIdeal (P : Ideal GeoJets5) (D : GeoJets5) : Ideal GeoJets5 :=
  P ⊔ Ideal.span {D}
def LengthAt (J P : Ideal GeoJets5) (hp : P.IsPrime) : ℕ∞ :=
  letI := hp
  let A := Localization.AtPrime P
  Module.length A (A ⧸ J.map (algebraMap GeoJets5 A))
structure Component (P : Ideal GeoJets5) (D : GeoJets5) (C : Ideal GeoJets5) (w : ℕ) : Prop where
  minimal : (sectionIdeal P D).IsMinimalPrime C
  length_le : (w : ℕ∞) ≤ LengthAt (sectionIdeal P D) C minimal.isPrime
def ProperCutComparison : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5),
      i ∉ I → DimLE P (I.card + 1) →
      ∀ (D : GeoJets5), Box5 (B i).1 (B i).2 D → IsLeftRegular (Ideal.Quotient.mk P D) →
        mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I)
def CycleComparison : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (J : Ideal GeoJets5) (I : Finset (Fin 5)), DimLE J I.card →
      ∀ {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ),
        Set.InjOn C (S : Set ι) →
        (∀ a ∈ S, ∃ h : J.IsMinimalPrime (C a), (w a : ℕ∞) ≤ LengthAt J (C a) h.isPrime) →
        (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I
def DivisorBound : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5),
      P.IsPrime → i ∉ I → OfDim P (I.card + 1) →
      ∀ (D : GeoJets5), Box5 (B i).1 (B i).2 D → D ∉ P →
        ∀ {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ),
          Set.InjOn C (S : Set ι) → (∀ a ∈ S, Component P D (C a) (w a)) →
          (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B P (insert i I)
def oldEmbedding : GeoJets →+* GeoJets5 :=
  (MvPolynomial.rename Fin.castSucc).toRingHom
def cylinder (P : Ideal GeoJets) : Ideal GeoJets5 := P.map oldEmbedding
def pointIdeal (z : Fin 5 → GeoField) : Ideal GeoJets5 :=
  RingHom.ker (MvPolynomial.eval z)
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13_6 K1_13_6_2
open scoped BigOperators
theorem box5_iff {a : K1_13.Shape × ℕ} {D : GeoJets5} :
    Box5 a.1 a.2 D ↔ ∀ m ∈ D.support, Allowed a m := by
  constructor
  · intro h m hm
    exact ⟨(h.1 m hm).1, (h.1 m hm).2.1, (h.1 m hm).2.2, h.2 m hm⟩
  · intro h
    exact ⟨fun m hm => ⟨(h m hm).1, (h m hm).2.1, (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2⟩
theorem allowed_zero (a : K1_13.Shape × ℕ) : Allowed a 0 := by
  simp [Allowed]
theorem allowed_coordinate {a : K1_13.Shape × ℕ}
    (h : 1 ≤ a.1.b ∧ 3 ≤ a.1.j ∧ 1 ≤ a.1.t ∧ 1 ≤ a.2) (i : Fin 5) :
    Allowed a (Finsupp.single i 1) := by
  obtain ⟨hb, hj, ht, hd⟩ := h
  let m : Exponent := Finsupp.single i 1
  have hold : (∑ j : Fin 4, m j.castSucc) ≤ 1 := calc
    _ ≤ ∑ j : Fin 5, m j := by
      rw [Fin.sum_univ_castSucc (n := 4)]
      exact Nat.le_add_right _ _
    _ = 1 := by
      rw [← Finsupp.degree_eq_sum]
      exact Finsupp.degree_single i 1
  have hindex : (∑ j : Fin 4, j.val * m j.castSucc) ≤ 3 := calc
    _ ≤ ∑ j : Fin 4, 3 * m j.castSucc := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ 3 := by rw [← Finset.mul_sum]; omega
  have hsingle (j : Fin 5) : m j ≤ 1 := by
    simp only [m, Finsupp.single_apply]
    split <;> decide
  exact ⟨hold.trans hb, hindex.trans hj, (hsingle _).trans ht, (hsingle _).trans hd⟩
private theorem constant_box (a : K1_13.Shape × ℕ) (s : GeoField) :
    Box5 a.1 a.2 (MvPolynomial.C s) := by
  classical
  apply box5_iff.mpr
  intro m hm
  by_cases hs : s = 0
  · simp [hs] at hm
  · rw [MvPolynomial.support_C, ite_eq_right hs, Finset.mem_singleton] at hm
    exact hm ▸ allowed_zero a
private theorem coordinate_box {a : K1_13.Shape × ℕ}
    (h : 1 ≤ a.1.b ∧ 3 ≤ a.1.j ∧ 1 ≤ a.1.t ∧ 1 ≤ a.2)
    (z : Fin 5 → GeoField) (i : Fin 5) :
    Box5 a.1 a.2 (MvPolynomial.X i - MvPolynomial.C (z i)) := by
  apply box5_iff.mpr
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hX | hC
  · rw [MvPolynomial.support_X, Finset.mem_singleton] at hX
    exact hX ▸ allowed_coordinate h i
  · exact box5_iff.mp (constant_box a (z i)) m hC
theorem eval_surjective (z : Fin 5 → GeoField) :
    Function.Surjective (MvPolynomial.eval z) :=
  fun a => ⟨MvPolynomial.C a, MvPolynomial.eval_C _⟩
theorem pointIdeal_injective : Function.Injective pointIdeal := by
  intro x y h
  funext i
  have hx : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    simp [pointIdeal, RingHom.mem_ker]
  have hy := RingHom.mem_ker.mp (h ▸ hx : _ ∈ pointIdeal y)
  rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] at hy
  exact hy.symm
private theorem point_degree (B : Boxes) (z : Fin 5 → GeoField) :
    mixedDegree B (pointIdeal z) ∅ = 1 := by
  let A := diagonalExponents B (fun _ => 1)
  let φ := (MvPolynomial.aeval z).comp (MvPolynomial.monomialMap GeoField A)
  have hφ : Function.Surjective φ := fun a => ⟨MvPolynomial.C a, φ.commutes a⟩
  have heq : (pointIdeal z).comap (MvPolynomial.monomialMap GeoField A) = RingHom.ker φ := rfl
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  unfold mixedDegree
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, tsub_self,
    pow_zero, one_mul, div_one]
  change (MvPolynomial.affineHilbertPolynomial
    ((pointIdeal z).comap (MvPolynomial.monomialMap GeoField A))).coeff 0 = 1
  rw [heq, MvPolynomial.affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero,
    e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
theorem one_le_length {J C : Ideal GeoJets5} (h : J.IsMinimalPrime C) :
    (1 : ℕ∞) ≤ LengthAt J C h.isPrime := by
  let := h.isPrime
  let A := Localization.AtPrime C
  have hne : J.map (algebraMap GeoJets5 A) ≠ ⊤ := by
    have hle := Ideal.map_mono (f := algebraMap GeoJets5 A) h.le
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal C A] at hle
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  let : Nontrivial (A ⧸ J.map (algebraMap GeoJets5 A)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Order.one_le_iff_ne_zero.mpr Module.length_pos.ne'
theorem point_component {C : Ideal GeoJets5} (hprime : C.IsPrime) (hdim : OfDim C 1)
    {z : Fin 5 → GeoField} (hz : C ≤ pointIdeal z) {D : GeoJets5} (hproper : D ∉ C)
    (hD : MvPolynomial.eval z D = 0) : Component C D (pointIdeal z) 1 := by
  let := hprime
  let : (pointIdeal z).IsPrime := RingHom.ker_isPrime (MvPolynomial.eval z)
  let : Ring.KrullDimLE 1 (GeoJets5 ⧸ C) := Ring.krullDimLE_iff.mpr (le_of_eq hdim)
  have hmin : (sectionIdeal C D).IsMinimalPrime (pointIdeal z) := by
    refine ⟨⟨RingHom.ker_isPrime _, sup_le hz ((Ideal.span_singleton_le_iff_mem _).mpr hD)⟩, ?_⟩
    intro P hP hPle
    have := hP.1
    have hCP : C ≤ P := le_sup_left.trans hP.2
    have hDJ : D ∈ sectionIdeal C D :=
      (le_sup_right : Ideal.span {D} ≤ sectionIdeal C D) (Ideal.subset_span (by simp))
    have hDP : D ∈ P := hP.2 hDJ
    let π := Ideal.Quotient.mk C
    have hne : P.map π ≠ ⊥ := by
      intro h
      have hmem := Ideal.mem_map_of_mem π hDP
      rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
      exact hproper hmem
    have hmax : (P.map π).IsMaximal :=
      (Ideal.isPrime_map_quotientMk_of_isPrime hCP).isMaximal_of_ne_bot hne
    have htop := (Ideal.isPrime_map_quotientMk_of_isPrime
      (p := pointIdeal z) hz).ne_top
    have hEq := hmax.eq_of_le htop (Ideal.map_mono (f := π) hPle)
    have hEq' := congrArg (Ideal.comap π) hEq
    rw [Ideal.comap_map_mk hCP, Ideal.comap_map_mk hz] at hEq'
    exact hEq'.ge
  exact ⟨hmin, one_le_length hmin⟩
theorem exists_coordinate_cut {C : Ideal GeoJets5} {z : Fin 5 → GeoField}
    (h : C < pointIdeal z) :
    ∃ i : Fin 5, MvPolynomial.X i - MvPolynomial.C (z i) ∉ C := by
  by_contra! hmem
  let π := Ideal.Quotient.mk C
  have hmaps : π = π.comp (MvPolynomial.C.comp (MvPolynomial.eval z)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      have heq := Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
      rw [map_sub, sub_eq_zero] at heq
      simpa using heq
  apply not_le_of_gt h
  intro D hD
  have hz : MvPolynomial.eval z D = 0 := RingHom.mem_ker.mp hD
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π D = 0
  calc
    π D = π (MvPolynomial.C (MvPolynomial.eval z D)) := RingHom.congr_fun hmaps D
    _ = 0 := by rw [hz, map_zero, map_zero]
theorem point_bound (H : DivisorBound)
    (B : Boxes) (hB : Admissible B)
    (ha : 1 ≤ (B 4).1.b ∧ 3 ≤ (B 4).1.j ∧ 1 ≤ (B 4).1.t ∧ 1 ≤ (B 4).2)
    (C : Ideal GeoJets5) (hprime : C.IsPrime) (hdim : OfDim C 1)
    (U : Finset (Fin 5 → GeoField)) (hU : ∀ z ∈ U, C ≤ pointIdeal z)
    (hslice : U.card ≤ 1 ∨ ∃ D, Box5 (B 4).1 (B 4).2 D ∧ D ∉ C ∧
      ∀ z ∈ U, MvPolynomial.eval z D = 0) :
    (U.card : ℚ) ≤ mixedDegree B C {4} := by
  classical
  have cut_bound (D : GeoJets5) (hB' : Box5 (B 4).1 (B 4).2 D) (hproper : D ∉ C)
      (hD : ∀ z ∈ U, MvPolynomial.eval z D = 0) : (U.card : ℚ) ≤ mixedDegree B C {4} := by
    have hb := H B hB C ∅ 4 hprime (by simp) hdim D hB' hproper U pointIdeal (fun _ => 1)
      pointIdeal_injective.injOn (fun z hz => point_component hprime hdim (hU z hz) hproper (hD z hz))
    simpa [point_degree] using hb
  rcases hslice with hone | ⟨D, hD, hp, hz⟩
  · by_cases hempty : U = ∅
    · apply cut_bound (MvPolynomial.C 1) (constant_box (B 4) 1)
      · rw [map_one]
        exact (Ideal.ne_top_iff_one C).mp hprime.ne_top
      · simp [hempty]
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hlt : C < pointIdeal z := by
      refine lt_of_le_of_ne (hU z hz) ?_
      intro h
      rw [h, OfDim, pointIdeal] at hdim
      have e := (MvPolynomial.eval z).quotientKerEquivOfSurjective (eval_surjective z)
      rw [e.ringKrullDim, ringKrullDim_eq_zero_of_field] at hdim
      exact (by decide : (0 : WithBot ℕ∞) ≠ 1) hdim
    obtain ⟨i, hi⟩ := exists_coordinate_cut hlt
    apply cut_bound _ (coordinate_box ha z i) hi
    intro y hy
    have hyz := Finset.card_le_one.mp hone y hy z hz
    subst y
    simp
  · exact cut_bound D hD hp hz
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
abbrev lift4 : Row 4 →ₐ[(Polynomial Geom)] Row 5 := MvPolynomial.rename Fin.castSucc
abbrev generic5 : Row 5 →+* GeoJets5 := MvPolynomial.map genericCoeffs
def coefficientDerivative5 (P : Row 5) : Row 5 :=
  ∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))
def fixedFlow (P : Row 5) : Row 5 :=
  coefficientDerivative5 P +
    ∑ i : Fin 4, MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
      MvPolynomial.X i.succ * MvPolynomial.pderiv i.castSucc P
def rawGraph (g : Row 4) : Row 5 :=
  lift4 (partialFlow g) +
    MvPolynomial.C (4 : (Polynomial Geom)) * lift4 (separant g) * MvPolynomial.X (Fin.last 4)
def fifthFlow (g : Row 4) : Row 5 :=
  MvPolynomial.C (Polynomial.C (-(4 : Geom)⁻¹)) * fixedFlow (rawGraph g)
def numerator (g : Row 4) : ℕ → Row 5
  | 0 => MvPolynomial.C (24 : (Polynomial Geom)) * MvPolynomial.X (Fin.last 4)
  | k+1 =>
    let S := lift4 (separant g)
    let P := numerator g k
    S * fixedFlow P + fifthFlow g * MvPolynomial.pderiv (Fin.last 4) P -
      (k : Row 5) * fixedFlow S * P
def denominator (g : Row 4) (k : ℕ) : Row 5 := lift4 (separant g) ^ k
def padded (g : Row 4) (k i : ℕ) : Row 5 :=
  if hi : i < 4 then
    MvPolynomial.C (Polynomial.C (i.factorial : Geom)) *
      lift4 (MvPolynomial.X ⟨i, hi⟩) * denominator g k
  else numerator g (i - 4) * denominator g (k - (i - 4))
theorem padded_last (g : Row 4) (k : ℕ) : padded g k (k + 4) = numerator g k := by
  rw [padded, dite_eq_right (by omega : ¬ k + 4 < 4)]
  simp [denominator]
end
end K1_13_6_2_2
end
section
namespace K1_13_6_2_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
variable {f Q : Row 4} {l : ℕ}
@[simp] private theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
abbrev ordinary (T : (Polynomial Geom)) (i : ℕ) : GeoField :=
  genericCoeffs ((derivative (R := Geom))^[i] T)
theorem ordinary_eq_hasse (T : (Polynomial Geom)) (i : ℕ) :
    (derivative (R := Geom))^[i] T =
      Polynomial.C (i.factorial : Geom) * hasseDeriv i T := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
abbrev const : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
abbrev centre : GeoField := genericCoeffs Polynomial.X
def taylorScalar (x : Geom) (i : ℕ) : GeoField :=
  (i.factorial : GeoField)⁻¹ * (const x - centre)^i
theorem factorial_ne_zero {i : ℕ} (hi : i < K1.p) : (i.factorial : GeoField) ≠ 0 := by
  let e := const.comp K1_13.embed
  let : CharP GeoField K1.p := charP_of_injective_ringHom e.injective K1.p
  induction i with
  | zero => simp
  | succ i ih =>
    have he : ((i+1 : ℕ) : GeoField) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hi) (Nat.le_of_dvd (Nat.succ_pos i)
        ((CharP.cast_eq_zero_iff GeoField K1.p (i+1)).mp hz))
    simpa only [Nat.factorial_succ, Nat.cast_mul] using
      mul_ne_zero he (ih (Nat.lt_of_succ_lt hi))
theorem box_C_mul {p : Shape} {d : ℕ} {P : GeoJets5} (hP : Box5 p d P)
    (a : GeoField) : Box5 p d (MvPolynomial.C a * P) := by
  have hsub : (MvPolynomial.C a * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
  exact ⟨fun m hm => hP.1 m (hsub hm), fun m hm => hP.2 m (hsub hm)⟩
theorem box_sum {α : Type*} {p : Shape} {d : ℕ} (I : Finset α) (P : α → GeoJets5)
    (hP : ∀ i ∈ I, Box5 p d (P i)) : Box5 p d (∑ i ∈ I, P i) := by
  classical
  have hsub m (hm : m ∈ (∑ i ∈ I, P i).support) : ∃ i ∈ I, m ∈ (P i).support :=
    Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  constructor
  · intro m hm
    obtain ⟨i, hi, hmi⟩ := hsub m hm
    exact (hP i hi).1 m hmi
  · intro m hm
    obtain ⟨i, hi, hmi⟩ := hsub m hm
    exact (hP i hi).2 m hmi
theorem box_sub {p : Shape} {d : ℕ} {A B : GeoJets5}
    (hA : Box5 p d A) (hB : Box5 p d B) : Box5 p d (A - B) := by
  classical
  have hsub := MvPolynomial.support_sub (Fin 5) A B
  constructor
  · intro m hm
    rcases Finset.mem_union.mp (hsub hm) with ha | hb
    · exact hA.1 m ha
    · exact hB.1 m hb
  · intro m hm
    rcases Finset.mem_union.mp (hsub hm) with ha | hb
    · exact hA.2 m ha
    · exact hB.2 m hb
end
end K1_13_6_2_2
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3
open scoped BigOperators
def step {ι : Type} [DecidableEq ι] (i : ι) : ι → ℕ := Pi.single i 1
def Graded {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι)
    (I : Ideal (MvPolynomial σ GeoField)) : Prop :=
  ∀ f ∈ I, ∀ a : ι → ℕ, MvPolynomial.weightedHomogeneousComponent (step ∘ slot) a f ∈ I
def hilbert {ι σ : Type} [DecidableEq ι] (slot : σ → ι)
    (I : Ideal (MvPolynomial σ GeoField)) (a : ι → ℕ) : ℚ :=
  (Module.finrank GeoField
    ((MvPolynomial.weightedHomogeneousSubmodule GeoField (step ∘ slot) a).map
      (Ideal.Quotient.mkₐ GeoField I).toLinearMap) : ℕ)
def deltas {ι : Type} [DecidableEq ι] : List ι → ((ι → ℕ) → ℚ) → (ι → ℕ) → ℚ
  | [], H => H
  | i :: rest, H => fun a => deltas rest H (a + step i) - deltas rest H a
def outside {σ : Type} (A : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {e | ∀ b ∈ A, ¬ b ≤ e}
def sliceCount {ι σ : Type} [DecidableEq ι] (slot : σ → ι)
    (A : Finset (σ →₀ ℕ)) (a : ι → ℕ) : ℚ :=
  ({e | e ∈ outside A ∧ Finsupp.weight (step ∘ slot) e = a}.ncard : ℕ)
abbrev CapVar {ι : Type} (shapes : ι → Shape) := (i : ι) × capExponents (shapes i)
def capSlot {ι : Type} (shapes : ι → Shape) : CapVar shapes → ι := Sigma.fst
def capMap {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets) :
    MvPolynomial (CapVar shapes) GeoField →ₐ[GeoField] MvPolynomial ι (GeoJets ⧸ J) :=
  MvPolynomial.aeval fun v =>
    MvPolynomial.monomial (Finsupp.single v.1 1)
      (Ideal.Quotient.mk J (MvPolynomial.monomial v.2.val 1))
def capIdeal {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets) :
    Ideal (MvPolynomial (CapVar shapes) GeoField) :=
  RingHom.ker (capMap shapes J).toRingHom
def shapeSum {ι : Type} [Fintype ι] (shapes : ι → Shape) (a : ι → ℕ) : Shape :=
  ⟨∑ i, a i * (shapes i).b, ∑ i, a i * (shapes i).j, ∑ i, a i * (shapes i).t⟩
def productExponents {ι : Type} [DecidableEq ι] (shapes : ι → Shape) (a : ι → ℕ) :
    Set (Fin 4 →₀ ℕ) :=
  {m | ∃ e : CapVar shapes →₀ ℕ,
    Finsupp.weight (step ∘ capSlot shapes) e = a ∧
    Finsupp.weight (fun v : CapVar shapes => v.2.val) e = m}
def supportRank (J : Ideal GeoJets) (A : Set (Fin 4 →₀ ℕ)) : ℕ :=
  Module.finrank GeoField
    ((MvPolynomial.restrictSupport GeoField A).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap)
abbrev cut (J : Ideal GeoJets) (D : GeoJets) : Ideal GeoJets := J ⊔ Ideal.span {D}
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_4
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
theorem cylinder_injective : Function.Injective cylinder := by
  let retr : GeoJets5 →ₐ[GeoField] GeoJets :=
    MvPolynomial.killCompl (Fin.castSucc_injective 4)
  have hr : retr.toRingHom.comp oldEmbedding = RingHom.id GeoJets :=
    congrArg AlgHom.toRingHom (MvPolynomial.killCompl_comp_rename (Fin.castSucc_injective 4))
  intro P Q h
  have hh := congrArg (Ideal.map retr.toRingHom) h
  simpa only [cylinder, Ideal.map_map, hr, Ideal.map_id] using hh
theorem ambient_dim : DimLE (⊥ : Ideal GeoJets5) 5 := by
  unfold DimLE
  rw [(RingEquiv.quotientBot GeoJets5).ringKrullDim]
  change ringKrullDim (MvPolynomial (Fin 5) GeoField) ≤ _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_eq_fintype_card, Fintype.card_fin, WithBot.coe_natCast]
theorem old_section_box {P : Row 4} {p : Shape} (hP : InBox (shape P) p) :
    Box5 p 0 (oldEmbedding (toGeneric P)) := by
  apply (box5_iff (a := (p, 0))).mpr
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (toGeneric P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 4)] at hm
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
  have haP := MvPolynomial.support_map_subset genericCoeffs P ha
  unfold Allowed
  simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 4)]
  have hlast : Fin.last 4 ∉ Set.range (Fin.castSucc : Fin 4 → Fin 5) := by
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last i hi
  refine ⟨?_, ?_, (MvPolynomial.monomial_le_degreeOf _ haP).trans hP.2.2,
    le_of_eq (Finsupp.mapDomain_of_notMem_range _ _ hlast)⟩
  · have hdegree := MvPolynomial.le_totalDegree haP
    change a.degree ≤ P.totalDegree at hdegree
    rw [Finsupp.degree_eq_sum] at hdegree
    exact hdegree.trans hP.1
  · have hindex : a.sum (fun i n => i.val * n) ≤ (shape P).j :=
      Finset.le_sup (f := fun m => m.sum (fun i n => i.val * n)) haP
    rw [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)] at hindex
    exact hindex.trans hP.2.1
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators nonZeroDivisors
def c1 : Prop := ProperCutComparison
def c2 : Prop := CycleComparison
theorem dim_le_after_section {P : Ideal GeoJets5} {D : GeoJets5} {d : ℕ}
    (hr : IsLeftRegular (Ideal.Quotient.mk P D)) (h : DimLE P (d + 1)) :
    DimLE (sectionIdeal P D) d := by
  have hle : P ≤ sectionIdeal P D := le_sup_left
  let π := Ideal.Quotient.factor hle
  have hπ : π (Ideal.Quotient.mk P D) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.subset_span (by simp))
  have hnd : Ideal.Quotient.mk P D ∈ (GeoJets5 ⧸ P)⁰ :=
    mem_nonZeroDivisors_iff_left.mpr fun a ha => hr (ha.trans (mul_zero _).symm)
  have hd := ringKrullDim_succ_le_of_surjective π (Ideal.Quotient.factor_surjective hle) hnd hπ
  unfold DimLE at h ⊢
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  exact hd.trans (by simpa only [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one] using h)
theorem divisor_bound (hcut : ProperCutComparison) (hcycle : CycleComparison) :
    DivisorBound := by
  intro B hB P I i hP hi hd D hD hprop ι S C w hinj hcomp
  let := hP
  have hr : IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle : DimLE P (I.card + 1) := le_of_eq hd
  exact (hcycle B hB (sectionIdeal P D) I (dim_le_after_section hr hdle) S C w hinj
    (fun a ha => ⟨(hcomp a ha).minimal, (hcomp a ha).length_le⟩)).trans
    (hcut B hB P I i hi hdle D hD hr)
theorem chart_chamber (L : ℕ) (p : Shape) : Chamber (liftedChart L p) := by
  let H := 4 + (L - 5) * (p.j - 2)
  change H ≤ max _ H ∧ 3 * min _ (H / 3) ≤ H
  refine ⟨le_max_right _ _, ?_⟩
  have h := min_le_right (2 + (L - 5) * p.t) (H / 3)
  omega
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13_6 MvPolynomial
theorem standard_rank {ι σ : Type} [Fintype ι] [DecidableEq ι]
    (slot : σ → ι) (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (a : ι → ℕ) :
    hilbert slot I a =
      ({e | e ∈ m.standardExponents I ∧ Finsupp.weight (step ∘ slot) e = a}.ncard : ℕ) := by
  classical
  let w := step ∘ slot
  let E : Set (σ →₀ ℕ) := {e | e ∈ m.standardExponents I ∧ Finsupp.weight w e = a}
  let S := restrictSupport GeoField E
  let T := weightedHomogeneousSubmodule GeoField w a
  let mk := (Ideal.Quotient.mkₐ GeoField I).toLinearMap
  have hST : S ≤ T := by
    intro f hf e he
    exact (hf (mem_support_iff.mpr he)).2
  let φ : S →ₗ[GeoField] T.map mk := (mk.domRestrict S).codRestrict (T.map mk)
    (fun f => Submodule.mem_map.mpr ⟨f, hST f.2, rfl⟩)
  have hinj : Function.Injective φ := by
    intro f g hfg
    have heq : mk f = mk g := congrArg Subtype.val hfg
    apply Subtype.ext
    exact m.eq_of_mem_standardSpace_of_sub_mem
      (fun e he => (f.2 he).1) (fun e he => (g.2 he).1) (Ideal.Quotient.eq.mp heq)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨f, hf, heq⟩ := Submodule.mem_map.mp x.2
    obtain ⟨q, hq, hfq, _⟩ := m.exists_mem_standardSpace_sub_mem I f
    let q' := weightedHomogeneousComponent w a q
    have hq' : q' ∈ S := by
      intro e he
      have hc := mem_support_iff.mp he
      change (weightedHomogeneousComponent w a q).coeff e ≠ 0 at hc
      rw [coeff_weightedHomogeneousComponent] at hc
      by_cases ha : Finsupp.weight w e = a
      · rw [ite_eq_left ha] at hc
        exact ⟨hq (mem_support_iff.mpr hc), ha⟩
      · simp [ha] at hc
    have hproj : weightedHomogeneousComponent w a f = f :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
    have hsub : f - q' ∈ I := by
      have h := hI (f - q) hfq a
      change weightedHomogeneousComponent w a (f - q) ∈ I at h
      rw [map_sub, hproj] at h
      exact h
    exact ⟨⟨q', hq'⟩, Subtype.ext ((Ideal.Quotient.eq.mpr hsub).symm.trans heq)⟩
  have heq := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  change ((Module.finrank GeoField (T.map mk) : ℕ) : ℚ) = (E.ncard : ℕ)
  rw [← heq, Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField E), Nat.card_coe_set_eq]
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_2_2
noncomputable section
open K1_13 MvPolynomial
open scoped Polynomial
abbrev Dual (A : Type*) [CommRing A] := TrivSqZeroExt A A
def coefficientJet {A : Type*} [CommRing A] (e : (Polynomial Geom) →+* A) : (Polynomial Geom) →+* Dual A where
  toFun c := (e c, e (Polynomial.derivative c))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' c d := by
    apply TrivSqZeroExt.ext
    · change e (c + d) = e c + e d
      exact map_add _ _ _
    · change e (Polynomial.derivative (c + d)) =
        e (Polynomial.derivative c) + e (Polynomial.derivative d)
      simp only [map_add]
  map_mul' c d := by
    apply TrivSqZeroExt.ext
    · change e (c * d) = e c * e d
      exact map_mul _ _ _
    · change e (Polynomial.derivative (c * d)) =
        e c * e (Polynomial.derivative d) + e (Polynomial.derivative c) * e d
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, add_comm]
def coefficientDiff {n : ℕ} (P : Row n) : Row n :=
  ∑ m ∈ P.support, monomial m (Polynomial.derivative (P.coeff m))
@[simp] private theorem coeff_coefficientDiff {n : ℕ} (P : Row n) (m : Fin n →₀ ℕ) :
    (coefficientDiff P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDiff, coeff_sum]
  simp only [coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero]
private theorem coefficientDiff_C {n : ℕ} (c : (Polynomial Geom)) :
    coefficientDiff (C c : Row n) = C (Polynomial.derivative c) := by
  classical
  ext m
  rw [coeff_coefficientDiff]
  by_cases hm : 0 = m <;> simp [coeff_C, hm]
private theorem coefficientDiff_add {n : ℕ} (P Q : Row n) :
    coefficientDiff (P + Q) = coefficientDiff P + coefficientDiff Q := by
  ext m
  simp
private theorem coefficientDiff_mul_X {n : ℕ} (P : Row n) (j : Fin n) :
    coefficientDiff (P * MvPolynomial.X j) = coefficientDiff P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDiff, coeff_mul_X', coeff_mul_X']
  split_ifs <;> simp
theorem dual_chain {n : ℕ} {A : Type*} [CommRing A]
    (e : Row n →+* A) (j : Row n →+* Dual A)
    (hfst : ∀ P, (j P).fst = e P)
    (hC : ∀ c, (j (C c)).snd = e (C (Polynomial.derivative c))) (P : Row n) :
    (j P).snd = e (coefficientDiff P) + ∑ i, (j (MvPolynomial.X i)).snd * e (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [hC, coefficientDiff_C]
  | add P Q hP hQ =>
    simp only [map_add, TrivSqZeroExt.snd_add, coefficientDiff_add, hP, hQ,
      mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P l ih =>
    rw [map_mul]
    change (j P).fst * (j (MvPolynomial.X l)).snd + (j P).snd * (j (MvPolynomial.X l)).fst = _
    rw [hfst, hfst, ih, coefficientDiff_mul_X, map_mul]
    simp only [pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    have left : (∑ i, (j (MvPolynomial.X i)).snd * (e (pderiv i P) * e (MvPolynomial.X l))) =
        (∑ i, (j (MvPolynomial.X i)).snd * e (pderiv i P)) * e (MvPolynomial.X l) := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, (j (MvPolynomial.X i)).snd * (e P * e (pderiv i (MvPolynomial.X l)))) =
        (j (MvPolynomial.X l)).snd * e P := by
      simp [pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
end
end K1_13_6_2_2_2
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 Filter
def c1 : Prop :=
  ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (A B : Finset (σ →₀ ℕ)), outside B ⊆ outside A →
    let H := fun a => sliceCount slot A a - sliceCount slot B a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a
def c2 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape),
    (∀ i, ChamberBox (shapes i)) → ∀ a : ι → ℕ,
      productExponents shapes a = capExponents (shapeSum shapes a)
def c3 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets),
    Graded (capSlot shapes) (capIdeal shapes J) ∧ ∀ a : ι → ℕ,
      hilbert (capSlot shapes) (capIdeal shapes J) a = (supportRank J (productExponents shapes a) : ℚ)
def c4 : Prop :=
  ∀ (J : Ideal GeoJets) (p : Shape) (n : ℕ),
    MvPolynomial.affineHilbertFunction
      (J.comap (MvPolynomial.monomialMap GeoField (capExponents p)).toRingHom) n =
    supportRank J (productExponents (fun _ : Unit => p) (fun _ => n))
def c5 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι),
    (∀ i, ChamberBox (shapes i)) → base ∉ used → used.Nodup → dimension J ≤ used.length →
    (∀ q : Shape, ChamberBox q → ∀ n,
      MvPolynomial.affineHilbertFunction
        (J.comap (MvPolynomial.monomialMap GeoField (capExponents q)).toRingHom) n =
      supportRank J (capExponents (q.scale n))) →
    let H := fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ)
    ∀ P : MvPolynomial ι ℚ, (∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) →
      ∀ᶠ a in atTop,
        deltas used H a = polarize (capCoeff J used.length) (used.map shapes) (shapes base)
def c6 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (i : ι)
    (J : Ideal GeoJets) (D : GeoJets),
    Box4 (shapes i) D → IsLeftRegular (Ideal.Quotient.mk J D) →
    let slot := capSlot shapes
    let I := capIdeal shapes J
    let I₁ := capIdeal shapes (cut J D)
    let I₂ := capIdeal shapes (cut J (D ^ 2))
    Graded slot I → Graded slot I₂ →
    ∃ B C : Ideal (MvPolynomial (CapVar shapes) GeoField),
      Graded slot B ∧ Graded slot C ∧ B ≤ I₂ ∧ C ≤ I₁ ∧
      (∀ a : ι → ℕ, hilbert slot B (a + step i) + hilbert slot I a = hilbert slot I (a + step i)) ∧
      ∀ a : ι → ℕ, hilbert slot C (a + step i) + hilbert slot I₁ a = hilbert slot I₂ (a + step i)
private lemma deltas_sub {ι : Type} [DecidableEq ι] (used : List ι)
    (H G : (ι → ℕ) → ℚ) (a : ι → ℕ) :
    deltas used (fun b => H b - G b) a = deltas used H a - deltas used G a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih]; ring
private lemma deltas_shift {ι : Type} [DecidableEq ι] (used : List ι)
    (H : (ι → ℕ) → ℚ) (a v : ι → ℕ) :
    deltas used (fun b => H (b + v)) a = deltas used H (a + v) := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih, add_right_comm a (step i) v]
private lemma eventually_shift {ι : Type} {Q : (ι → ℕ) → Prop} (v : ι → ℕ)
    (h : ∀ᶠ a in atTop, Q a) : ∀ᶠ a in atTop, Q (a + v) := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨u, fun a ha => hu (a + v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma spend {ι : Type} [DecidableEq ι] (used : List ι) (v : ι → ℕ)
    (B C G H : (ι → ℕ) → ℚ) (heq : ∀ a, B (a + v) + H a = G (a + v))
    (hpos : ∀ᶠ a in atTop, 0 ≤ deltas used (fun b => B b - C b) a) :
    ∀ᶠ a in atTop, deltas used C (a + v) ≤ deltas used G (a + v) - deltas used H a := by
  have hid : (fun a => B (a + v)) = fun a => G (a + v) - H a := by
    funext a
    linarith [heq a]
  filter_upwards [eventually_shift v hpos] with a ha
  rw [deltas_sub] at ha
  rw [← deltas_shift used B, hid, deltas_sub, deltas_shift] at ha
  linarith
private lemma graded_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι) :
    Graded slot (⊤ : Ideal (MvPolynomial σ GeoField)) := by
  intro f hf a
  exact Submodule.mem_top
private lemma hilbert_top {ι σ : Type} [DecidableEq ι] (slot : σ → ι) (a : ι → ℕ) :
    hilbert slot (⊤ : Ideal (MvPolynomial σ GeoField)) a = 0 := by
  have : Subsingleton (MvPolynomial σ GeoField ⧸ (⊤ : Ideal (MvPolynomial σ GeoField))) :=
    (Ideal.Quotient.subsingleton_iff).2 rfl
  simp [hilbert, Module.finrank_eq_zero_of_subsingleton]
private theorem hilbert_difference (h1 : c1)
    {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (hK : Graded slot K) (hle : I ≤ K) :
    let H := fun a => hilbert slot I a - hilbert slot K a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff K
  have hAB : outside B ⊆ outside A := by
    intro e he
    exact (hA e).mp (fun f hf => (hB e).mpr he f (hle hf))
  have eqI : hilbert slot I = sliceCount slot A := by
    funext a
    rw [standard_rank slot m I hI a]
    simp only [sliceCount, hA, outside, Set.mem_ofPred_eq]
  have eqK : hilbert slot K = sliceCount slot B := by
    funext a
    rw [standard_rank slot m K hK a]
    simp only [sliceCount, hB, outside, Set.mem_ofPred_eq]
  rw [eqI, eqK]
  exact h1 slot A B hAB
private theorem read_cap (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι) (hsh : ∀ i, ChamberBox (shapes i))
    (hb : base ∉ used) (hn : used.Nodup) (hd : dimension J ≤ used.length) :
    ∀ᶠ a in atTop, deltas used (hilbert (capSlot shapes) (capIdeal shapes J)) a =
      polarize (capCoeff J used.length) (used.map shapes) (shapes base) := by
  let slot := capSlot shapes
  let I := capIdeal shapes J
  have hI := (h3 shapes J).1
  have hall := (hilbert_difference h1 slot I ⊤ hI (graded_top slot) le_top).1
  rw [show (fun a => hilbert slot I a - hilbert slot ⊤ a) = hilbert slot I by
    funext a; simp [hilbert_top]] at hall
  obtain ⟨P, hP⟩ := hall
  have hrank : hilbert slot I = fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ) := by
    funext a
    rw [(h3 shapes J).2 a, h2 shapes hsh a]
  rw [hrank] at hP ⊢
  refine h5 shapes J base used hsh hb hn hd (fun q hq n => ?_) P hP
  rw [h4, h2 (fun _ : Unit => q) (fun _ => hq)]
  simp [shapeSum, Shape.scale]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_13_6_2_3.c2 := by
  classical
  intro J p boxes hp hboxes hdim D hD hreg
  let ι := Option (Option (Fin boxes.length))
  let base : ι := none
  let i : ι := some none
  let emb : Fin boxes.length → ι := fun k => some (some k)
  let rest := (List.finRange boxes.length).map emb
  let shapes : ι → Shape
    | none => ⟨3, 3, 1⟩
    | some none => p
    | some (some k) => boxes.get k
  have hsh (k : ι) : ChamberBox (shapes k) := by
    cases k with
    | none =>
      change ChamberBox ⟨3, 3, 1⟩
      exact ⟨by decide, by decide, by decide⟩
    | some k => cases k with
      | none => exact hp
      | some k => exact hboxes _ (List.get_mem _ _)
  have hbase : base ∉ rest := by simp [base, rest, emb]
  have hi : i ∉ rest := by
    intro h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp h
    change (some (some k) : Option (Option (Fin boxes.length))) = some none at hk
    have hinner : (some k : Option (Fin boxes.length)) = none := Option.some.inj hk
    cases hinner
  have hn : rest.Nodup := (List.nodup_finRange _).map
    (fun _ _ h => Option.some.inj (Option.some.inj h))
  have hbase' : base ∉ i :: rest := by simp [base, i, rest, emb]
  have hn' : (i :: rest).Nodup := List.nodup_cons.mpr ⟨hi, hn⟩
  have hmap : rest.map shapes = boxes := by
    simp [rest, List.map_map, Function.comp_def, emb, shapes]
  have hlen : rest.length = boxes.length := by simp [rest]
  let slot := capSlot shapes
  let I := capIdeal shapes J
  let I₁ := capIdeal shapes (cut J D)
  let I₂ := capIdeal shapes (cut J (D ^ 2))
  have hgraded₂ := (h3 shapes (cut J (D ^ 2))).1
  obtain ⟨B, C, hB, hC, hBI, hCI, heqB, heqC⟩ := h6 shapes i J D hD hreg (h3 shapes J).1 hgraded₂
  have hposB := (hilbert_difference h1 slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC := (hilbert_difference h1 slot C I₁ hC (h3 shapes (cut J D)).1 hCI).2 rest
  have hspendB := spend rest (step i) (hilbert slot B) (hilbert slot I₂) (hilbert slot I)
    (hilbert slot I) heqB hposB
  have hspendC := spend rest (step i) (hilbert slot C) (hilbert slot I₁) (hilbert slot I₂)
    (hilbert slot I₁) heqC hposC
  have hd₁ : dimension (cut J D) ≤ rest.length := by
    have hdrop : dimension (cut J D) ≤ dimension J - 1 := cut_dimension hreg
    omega
  have hd₀ : dimension J ≤ (i :: rest).length := by simpa [hlen] using hdim
  have hr₀ := read_cap h1 h2 h3 h4 h5 shapes J base (i :: rest) hsh hbase' hn' hd₀
  have hr₁ := read_cap h1 h2 h3 h4 h5 shapes (cut J D) base rest hsh hbase hn hd₁
  have hfinal : ∀ᶠ _a in (atTop : Filter (ι → ℕ)),
      2 * polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ ≤
        polarize (capCoeff J (p :: boxes).length) (p :: boxes) ⟨3, 3, 1⟩ := by
    filter_upwards [hspendB, hspendC, hr₀, hr₁, eventually_shift (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons, hmap, List.length_cons, hlen] at h₀
    rw [hlen, hmap] at h₁ h₁'
    change deltas rest (hilbert slot I) (a + step i) - deltas rest (hilbert slot I) a =
      polarize (capCoeff J (boxes.length + 1)) (p :: boxes) ⟨3, 3, 1⟩ at h₀
    change deltas rest (hilbert slot I₁) a =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁
    change deltas rest (hilbert slot I₁) (a + step i) =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁'
    simp only [List.length_cons]
    linarith [hb, hc, h₀, h₁, h₁']
  obtain ⟨_, hfinal⟩ := hfinal.exists
  unfold mixedDegree
  rw [List.length_cons, pow_succ, mul_comm ((2 : ℚ)^boxes.length) 2, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2 (by simpa [mul_comm] using hfinal)
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_2 MvPolynomial
open scoped Polynomial
abbrev Chart (g : Row 4) := Localization.Away (separant g)
abbrev incl (g : Row 4) : Row 4 →+* Chart g := algebraMap _ _
abbrev S (g : Row 4) : Chart g := incl g (separant g)
abbrev invS (g : Row 4) : Chart g := IsLocalization.Away.invSelf (separant g)
theorem S_mul_invS (g : Row 4) : S g * invS g = 1 :=
  IsLocalization.Away.mul_invSelf _
abbrev constants (g : Row 4) : (Polynomial Geom) →+* Chart g := (incl g).comp C
abbrev negQuarter : Geom := -(4 : Geom)⁻¹
theorem negQuarter_mul_four : negQuarter * (4 : Geom) = -1 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have h : (4 : Geom) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff Geom K1.p 4).mp hz
    exact (by decide : ¬ 4 % K1.p = 0) (Nat.dvd_iff_mod_eq_zero.mp hd)
  rw [negQuarter, neg_mul, inv_mul_cancel₀ h]
abbrev q (g : Row 4) : Chart g := constants g (Polynomial.C negQuarter)
private theorem q_mul_four (g : Row 4) : q g * 4 = -1 := by
  let e := (constants g).comp Polynomial.C
  change e negQuarter * 4 = -1
  calc
    _ = e negQuarter * e 4 := by rw [map_ofNat]
    _ = e (negQuarter * 4) := (map_mul _ _ _).symm
    _ = _ := by rw [negQuarter_mul_four, map_neg, map_one]
def W (g : Row 4) : Chart g := q g * incl g (partialFlow g) * invS g
private theorem four_mul_W (g : Row 4) : 4 * W g = -(incl g (partialFlow g) * invS g) := by
  unfold W
  calc
    _ = (q g * 4) * (incl g (partialFlow g) * invS g) := by ring
    _ = _ := by rw [q_mul_four, neg_one_mul]
def graphMap (g : Row 4) : Row 5 →+* Chart g :=
  eval₂Hom (constants g) (Fin.lastCases (W g) (fun i => incl g (MvPolynomial.X i)))
@[simp] theorem graphMap_C (g : Row 4) (a : (Polynomial Geom)) :
    graphMap g (C a) = constants g a := eval₂Hom_C _ _ _
@[simp] theorem graphMap_X_last (g : Row 4) :
    graphMap g (MvPolynomial.X (Fin.last 4)) = W g :=
  (eval₂Hom_X' _ _ _).trans Fin.lastCases_last
@[simp] theorem graphMap_X_old (g : Row 4) (i : Fin 4) :
    graphMap g (MvPolynomial.X i.castSucc) = incl g (MvPolynomial.X i) := by simp [graphMap]
@[simp] theorem graphMap_lift (g P : Row 4) : graphMap g (lift4 P) = incl g P := by
  have h : (graphMap g).comp lift4.toRingHom = incl g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h P
private def oldJet (g : Row 4) : Row 4 →+* Dual (Chart g) :=
  eval₂Hom (coefficientJet (constants g))
    (fun i => (incl g (MvPolynomial.X i),
      Fin.lastCases (4 * W g)
        (fun j : Fin 3 => (j.val + 1 : ℕ) * incl g (MvPolynomial.X j.succ)) i))
private theorem oldJet_C (g : Row 4) (a : (Polynomial Geom)) :
    oldJet g (C a) = (constants g a, constants g (Polynomial.derivative a)) :=
  eval₂Hom_C _ _ _
private theorem oldJet_X (g : Row 4) (i : Fin 4) :
    oldJet g (MvPolynomial.X i) = (incl g (MvPolynomial.X i),
      Fin.lastCases (4 * W g)
        (fun j : Fin 3 => (j.val + 1 : ℕ) * incl g (MvPolynomial.X j.succ)) i) :=
  eval₂Hom_X' _ _ _
private theorem oldJet_fst (g P : Row 4) : (oldJet g P).fst = incl g P := by
  have h : (TrivSqZeroExt.fstHom (Chart g) (Chart g) (Chart g)).toRingHom.comp
      (oldJet g) = incl g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (oldJet g (C a)).fst = incl g (C a)
      rw [oldJet_C, TrivSqZeroExt.fst_mk]
      rfl
    · intro i
      change (oldJet g (MvPolynomial.X i)).fst = incl g (MvPolynomial.X i)
      rw [oldJet_X, TrivSqZeroExt.fst_mk]
  exact DFunLike.congr_fun h P
private def localJet (g : Row 4) : Chart g →+* Dual (Chart g) :=
  IsLocalization.Away.lift (separant g) (g := oldJet g)
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
      rw [oldJet_fst]
      exact IsLocalization.Away.algebraMap_isUnit _))
@[simp] private theorem localJet_incl (g P : Row 4) :
    localJet g (incl g P) = oldJet g P := IsLocalization.Away.lift_eq _ _ _
private theorem localJet_fst (g : Row 4) (a : Chart g) : (localJet g a).fst = a := by
  have h : (TrivSqZeroExt.fstHom (Chart g) (Chart g) (Chart g)).toRingHom.comp
      (localJet g) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (separant g))
    apply RingHom.ext
    intro P
    change (localJet g (incl g P)).fst = incl g P
    rw [localJet_incl, oldJet_fst]
  exact DFunLike.congr_fun h a
def D (g : Row 4) : Chart g →+ Chart g :=
  (TrivSqZeroExt.sndHom (R := Chart g) (M := Chart g)).toAddMonoidHom.comp
    (localJet g).toAddMonoidHom
theorem D_mul (g : Row 4) (a b : Chart g) : D g (a * b) = a * D g b + D g a * b := by
  change (localJet g (a * b)).snd = _
  rw [map_mul]
  change (localJet g a).fst * D g b + D g a * (localJet g b).fst = _
  rw [localJet_fst, localJet_fst]
@[simp] theorem D_natCast (g : Row 4) (n : ℕ) : D g (n : Chart g) = 0 := by
  have h : D g 1 = 0 := by
    change (localJet g 1).snd = 0
    rw [map_one]
    rfl
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, h, add_zero]
@[simp] theorem D_X_old (g : Row 4) (i : Fin 3) :
    D g (incl g (MvPolynomial.X i.castSucc)) = (i.val + 1 : ℕ) * incl g (MvPolynomial.X i.succ) := by
  change (localJet g (incl g (MvPolynomial.X i.castSucc))).snd = _
  rw [localJet_incl, oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_castSucc]
@[simp] theorem D_X_last (g : Row 4) :
    D g (incl g (MvPolynomial.X (Fin.last 3))) = 4 * W g := by
  change (localJet g (incl g (MvPolynomial.X (Fin.last 3)))).snd = _
  rw [localJet_incl, oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_last]
theorem D_incl_C (g : Row 4) (c : (Polynomial Geom)) :
    D g (constants g c) = constants g (Polynomial.derivative c) := by
  change (localJet g (incl g (C c))).snd = _
  rw [localJet_incl, oldJet_C, TrivSqZeroExt.snd_mk]
theorem D_incl (g P : Row 4) : S g * D g (incl g P) = incl g (flowNumerator g P) := by
  have h := dual_chain (incl g) (oldJet g) (oldJet_fst g) (by
    intro c
    rw [oldJet_C, TrivSqZeroExt.snd_mk]
    rfl) P
  have hs : D g (incl g P) =
      incl g (partialFlow P) + 4 * W g * incl g (separant P) := by
    change (localJet g (incl g P)).snd = _
    rw [localJet_incl, h, Fin.sum_univ_castSucc]
    simp only [oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_castSucc, Fin.lastCases_last,
      partialFlow, separant, map_add, map_sum, map_mul, map_natCast, ← add_assoc]
    rfl
  rw [hs, four_mul_W, flowNumerator, map_sub, map_mul, map_mul, mul_add]
  have hm : S g * (incl g (partialFlow g) * invS g) = incl g (partialFlow g) := by
    rw [← mul_left_comm, S_mul_invS, mul_one]
  linear_combination -incl g (separant P) * hm
private theorem D_graphMap_X (g : Row 4) (i : Fin 4) :
    D g (graphMap g (MvPolynomial.X i.castSucc)) = (i.val + 1 : ℕ) * graphMap g (MvPolynomial.X i.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change D g (graphMap g (MvPolynomial.X (Fin.last 3).castSucc)) =
      4 * graphMap g (MvPolynomial.X (Fin.last 4))
    rw [graphMap_X_old, graphMap_X_last, D_X_last]
  · rw [graphMap_X_old, Fin.succ_castSucc, graphMap_X_old, D_X_old]
    rfl
theorem D_graphMap (g : Row 4) (P : Row 5) :
    D g (graphMap g P) = graphMap g (fixedFlow P) +
      D g (W g) * graphMap g (pderiv (Fin.last 4) P) := by
  have h := dual_chain (graphMap g) ((localJet g).comp (graphMap g))
    (fun p => localJet_fst g (graphMap g p)) (by
      intro c
      change D g (graphMap g (C c)) = graphMap g (C (Polynomial.derivative c))
      rw [graphMap_C, graphMap_C, D_incl_C]) P
  change D g (graphMap g P) = graphMap g (coefficientDerivative5 P) +
    ∑ i, D g (graphMap g (MvPolynomial.X i)) * graphMap g (pderiv i P) at h
  rw [h, Fin.sum_univ_castSucc, graphMap_X_last, ← add_assoc]
  simp only [D_graphMap_X, fixedFlow, map_add, map_sum, map_mul, map_natCast]
private theorem graph_zero (g : Row 4) : graphMap g (rawGraph g) = 0 := by
  rw [rawGraph, map_add, map_mul, map_mul, graphMap_lift, graphMap_lift, graphMap_X_last,
    graphMap_C, map_ofNat]
  change incl g (partialFlow g) + 4 * S g * W g = 0
  have hm : S g * (incl g (partialFlow g) * invS g) = incl g (partialFlow g) := by
    rw [← mul_left_comm, S_mul_invS, mul_one]
  rw [mul_comm (4 : Chart g) (S g), mul_assoc, four_mul_W, mul_neg, hm, add_neg_cancel]
@[simp] private theorem pderiv_last_lift (P : Row 4) :
    pderiv (Fin.last 4) (lift4 P) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨i, _, hi⟩ := mem_vars_rename Fin.castSucc P hv
  exact Fin.castSucc_ne_last i hi
private theorem pderiv_graph (g : Row 4) :
    pderiv (Fin.last 4) (rawGraph g) = C (4 : (Polynomial Geom)) * lift4 (separant g) := by
  rw [rawGraph, map_add, pderiv_last_lift, zero_add, pderiv_mul, pderiv_C_mul,
    pderiv_last_lift, mul_zero, zero_mul, pderiv_X_self, mul_one, zero_add]
private theorem D_W (g : Row 4) : S g * D g (W g) = graphMap g (fifthFlow g) := by
  have h := congrArg (D g) (graph_zero g)
  rw [map_zero, D_graphMap, pderiv_graph, map_mul, graphMap_C, map_ofNat, graphMap_lift] at h
  change graphMap g (fixedFlow (rawGraph g)) + D g (W g) * (4 * S g) = 0 at h
  rw [fifthFlow, map_mul, graphMap_C]
  change S g * D g (W g) = q g * graphMap g (fixedFlow (rawGraph g))
  linear_combination -q g * h + S g * D g (W g) * q_mul_four g
theorem D_graphMap_sigma (g : Row 4) :
    D g (S g) = graphMap g (fixedFlow (lift4 (separant g))) := by
  simpa only [graphMap_lift, pderiv_last_lift, map_zero, mul_zero, add_zero] using
    D_graphMap g (lift4 (separant g))
theorem lifted_step (g : Row 4) (T : Row 5) (n : ℕ) :
    graphMap g (lift4 (separant g) * fixedFlow T + fifthFlow g * pderiv (Fin.last 4) T -
      (n : Row 5) * fixedFlow (lift4 (separant g)) * T) =
      S g * D g (graphMap g T) - (n : Chart g) * D g (S g) * graphMap g T := by
  simp only [map_sub, map_add, map_mul, map_natCast, graphMap_lift,
    ← D_graphMap_sigma, ← D_W, D_graphMap]
  ring
end
end K1_13_6_2_2_2
end
section
namespace K1_13_6_2_4_3
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
open scoped BigOperators
def sumCap (B : Boxes) (t : Fin 5 → ℕ) : Shape × ℕ :=
  (⟨∑ i, t i * (B i).1.b, ∑ i, t i * (B i).1.j, ∑ i, t i * (B i).1.t⟩,
    ∑ i, t i * (B i).2)
def scaleCap (a : Shape × ℕ) (n : ℕ) : Shape × ℕ :=
  (a.1.scale n, n * a.2)
theorem sumCap_chamber (B : Boxes) (hB : ∀ i, Chamber (B i).1) (t : Fin 5 → ℕ) :
    Chamber (sumCap B t).1 := by
  unfold Chamber sumCap
  dsimp only
  constructor
  · exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hB i).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left (t i) (hB i).2)
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators
private theorem dim_le_of_integral_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun chain => ?_
  obtain ⟨q, hq⟩ := hf.comap_surjective hinj chain.head
  have : q.asIdeal.LiesOver chain.head.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hq.symm⟩
  obtain ⟨lifted, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp chain q.asIdeal
  exact le_iSup_of_le lifted (by rw [hlen])
theorem hilbert_degree_le {σ : Type*} [Finite σ] {P : Ideal (MvPolynomial σ GeoField)} {d : ℕ}
    (hd : ringKrullDim (MvPolynomial σ GeoField ⧸ P) ≤ ((d : ℕ∞) : WithBot ℕ∞)) :
    (affineHilbertPolynomial P).natDegree ≤ d := by
  by_cases hP : P = ⊤
  · simp [hP, affineHilbertPolynomial_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg GeoField (MvPolynomial σ GeoField ⧸ P)
  rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hinj, Nat.card_fin]
  have hdim := (dim_le_of_integral_injective g.toRingHom hfin.to_isIntegral hinj).trans hd
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field] using hdim
private theorem zero_in_box (a : Shape × ℕ) : (0 : Exponent) ∈ latticePoints a := by
  change Allowed (a.1.scale 2, 2 * a.2) 0
  simp [Allowed]
theorem diagonal_surjective {B : Boxes} (hB : Admissible B) {t : Fin 5 → ℕ}
    (ht : ∀ i, 0 < t i) : Function.Surjective (monomialMap GeoField (diagonalExponents B t)) := by
  classical
  apply monomialMap_surjective
  intro v
  obtain ⟨i, hi⟩ := hB.2 v
  let j₀ : Fin (t i) := ⟨0, ht i⟩
  let u (k : Fin 5) (j : Fin (t k)) : Exponent :=
    if h : k = i then if h ▸ j = j₀ then Finsupp.single v 1 else 0 else 0
  refine ⟨u, ?_, ?_⟩
  · intro k j
    by_cases hk : k = i
    · subst k
      by_cases hj : j = j₀
      · simpa [u, hj] using hi
      · simpa [u, hj] using zero_in_box (B i)
    · simpa [u, hk] using zero_in_box (B k)
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j₀]
      · simp [u]
      · intro j _ hj
        simp [u, hj]
      · simp
    · intro k _ hk
      simp [u, hk]
    · simp
theorem diagonal_degree_le {B : Boxes} (hB : Admissible B) {P : Ideal GeoJets5} {d : ℕ}
    (hP : DimLE P d) {t : Fin 5 → ℕ} (ht : ∀ i, 0 < t i) :
    (affineHilbertPolynomial (P.comap (monomialMap GeoField (diagonalExponents B t)))).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let g := (Ideal.Quotient.mk P).comp f.toRingHom
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp (diagonal_surjective hB ht)
  have hker : RingHom.ker g = P.comap f := by
    ext x
    change Ideal.Quotient.mk P (f x) = 0 ↔ f x ∈ P
    exact Ideal.Quotient.eq_zero_iff_mem
  apply hilbert_degree_le
  rw [← hker, (g.quotientKerEquivOfSurjective hg).ringKrullDim]
  exact hP
end
end K1_13_6_2_4_2
end
section
namespace K1_13_6_2_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3
open scoped BigOperators
def c1 : Prop :=
  ∀ (J : Ideal GeoJets) (d : ℕ), dimension J ≤ d →
    ∀ p : Shape, ChamberBox p →
      capCoeff J d p =
        ∑ P ∈ J.minimalPrimesFinset, (localWeight J P : ℚ) * capCoeff P d p
def c2 : Prop :=
  ∀ (P : Ideal GeoJets) (boxes : List Shape), P.IsPrime →
    (∀ q ∈ boxes, ChamberBox q) → dimension P = boxes.length → 2 ≤ boxes.length →
      0 ≤ mixedDegree P boxes
private abbrev baseline : Shape := ⟨3, 3, 1⟩
private lemma baseline_box : ChamberBox baseline := ⟨by decide, by decide, by decide⟩
private lemma chamber_plus {p q : Shape} (hp : ChamberBox p) (hq : ChamberBox q) :
    ChamberBox (p.plus q) := by
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  obtain ⟨hq₁, hq₂, hq₃⟩ := hq
  refine ⟨Nat.add_le_add hp₁ hq₁, ?_, Nat.add_pos_left hp₃ _⟩
  change 3 * (p.t + q.t) ≤ p.j + q.j
  omega
private lemma polarize_congr {H G : Shape → ℚ} (h : ∀ p, ChamberBox p → H p = G p)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q) {p : Shape}
    (hp : ChamberBox p) : polarize H boxes p = polarize G boxes p := by
  induction boxes generalizing p with
  | nil => exact h p hp
  | cons q boxes ih =>
    have hq := hboxes q List.mem_cons_self
    have hr := fun r hr => hboxes r (List.mem_cons_of_mem _ hr)
    simp only [polarize, ih hr (chamber_plus hp hq), ih hr hp]
private lemma polarize_sum {ι : Type*} (S : Finset ι) (w : ι → ℚ) (H : ι → Shape → ℚ)
    (boxes : List Shape) (p : Shape) :
    polarize (fun x => ∑ i ∈ S, w i * H i x) boxes p =
      ∑ i ∈ S, w i * polarize (H i) boxes p := by
  induction boxes generalizing p with
  | nil => rfl
  | cons q boxes ih =>
    simp only [polarize, ih, ← Finset.sum_sub_distrib, mul_sub]
private lemma polarize_zero (boxes : List Shape) (p : Shape) :
    polarize (fun _ => 0) boxes p = 0 := by
  induction boxes generalizing p with
  | nil => rfl
  | cons q boxes ih => simp only [polarize, ih, sub_self]
private abbrev capMap (p : Shape) := MvPolynomial.monomialMap GeoField (capExponents p)
private lemma capMap_surjective {p : Shape} (hp : ChamberBox p) :
    Function.Surjective (capMap p) := by
  obtain ⟨hb, hj, ht⟩ := hp
  apply MvPolynomial.monomialMap_surjective
  intro i
  fin_cases i <;> simp [capExponents, Fin.sum_univ_four] <;> omega
private lemma cap_dimension (J : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (MvPolynomial.affineHilbertPolynomial (J.comap (capMap p).toRingHom)).natDegree =
      dimension J :=
  MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective
    (capMap p) (capMap_surjective hp) J
private lemma mixed_zero_of_lt {J : Ideal GeoJets} {boxes : List Shape}
    (hboxes : ∀ p ∈ boxes, ChamberBox p) (hd : dimension J < boxes.length) :
    mixedDegree J boxes = 0 := by
  have hz (p : Shape) (hp : ChamberBox p) : capCoeff J boxes.length p = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((cap_dimension J hp).trans_lt hd)
  unfold mixedDegree
  rw [polarize_congr hz hboxes baseline_box, polarize_zero, zero_div]
private lemma capCoeff_le_of_subset (J : Ideal GeoJets) {p q : Shape}
    (hp : ChamberBox p) (hq : ChamberBox q) (hsub : capExponents p ⊆ capExponents q)
    {d : ℕ} (hd : dimension J ≤ d) :
    capCoeff J d p ≤ capCoeff J d q := by
  let incl (i : capExponents p) : capExponents q := ⟨i.val, hsub i.property⟩
  let f := MvPolynomial.rename (R := GeoField) incl
  have hf : (capMap q).comp f = capMap p := by
    ext i
    simp [f, incl, MvPolynomial.monomialMap_X]
  let I := J.comap (capMap p).toRingHom
  let K := J.comap (capMap q).toRingHom
  have heq : K.comap f.toRingHom = I := by
    change (J.comap (capMap q).toRingHom).comap f.toRingHom = _
    rw [Ideal.comap_comap]
    change J.comap ((capMap q).comp f).toRingHom = I
    rw [hf]
  let g := Ideal.quotientMapₐ K f heq.ge
  have hg : Function.Injective g := Ideal.quotientMap_injective' (H := heq.ge) heq.le
  have hgen (i : capExponents p) :
      g (Ideal.Quotient.mk I (MvPolynomial.X i)) ∈ MvPolynomial.quotientDegreeLE K 1 := by
    rw [show g (Ideal.Quotient.mk I (MvPolynomial.X i)) =
        Ideal.Quotient.mk K (MvPolynomial.X (incl i)) by
          change Ideal.quotientMap K f.toRingHom heq.ge
            (Ideal.Quotient.mk I (MvPolynomial.X i)) = _
          rw [Ideal.quotientMap_mk]
          change Ideal.Quotient.mk K (MvPolynomial.rename incl (MvPolynomial.X i)) = _
          rw [MvPolynomial.rename_X]]
    exact MvPolynomial.mk_X_mem_quotientDegreeLE K _
  change (MvPolynomial.affineHilbertPolynomial I).coeff d ≤
    (MvPolynomial.affineHilbertPolynomial K).coeff d
  refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    ((cap_dimension J hp).trans_le hd) ((cap_dimension J hq).trans_le hd) ?_
  filter_upwards [MvPolynomial.eventually_eval_affineHilbertPolynomial I,
    MvPolynomial.eventually_eval_affineHilbertPolynomial K] with n hI hK
  rw [hI, hK]
  exact_mod_cast (by simpa only [one_mul] using
    MvPolynomial.affineHilbertFunction_le_of_injective g hg hgen n :
      MvPolynomial.affineHilbertFunction I n ≤ MvPolynomial.affineHilbertFunction K n)
private lemma mixed_nonneg (h2 : c2) {P : Ideal GeoJets} (hP : P.IsPrime)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q)
    (hd : dimension P ≤ boxes.length) :
    0 ≤ mixedDegree P boxes := by
  rcases hd.lt_or_eq with hlt | heq
  · rw [mixed_zero_of_lt hboxes hlt]
  · cases boxes with
    | nil =>
      change 0 ≤ capCoeff P 0 baseline / (2 : ℚ) ^ 0
      apply div_nonneg _ (by norm_num)
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((cap_dimension P baseline_box).trans_le heq.le)
        (MvPolynomial.eventually_eval_affineHilbertPolynomial_nonneg _)
    | cons p boxes =>
      cases boxes with
      | nil =>
        have hp := hboxes p List.mem_cons_self
        have hsub : capExponents baseline ⊆ capExponents (baseline.plus p) := by
          intro m hm
          exact ⟨hm.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
            hm.2.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
            hm.2.2.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _))⟩
        change 0 ≤ (capCoeff P 1 (baseline.plus p) - capCoeff P 1 baseline) / (2 : ℚ) ^ 1
        exact div_nonneg (sub_nonneg.mpr
          (capCoeff_le_of_subset P baseline_box (chamber_plus baseline_box hp) hsub heq.le))
          (by norm_num)
      | cons q boxes =>
        exact h2 P (p :: q :: boxes) hP hboxes heq (by simp)
private lemma mixed_cycle (h1 : c1) (J : Ideal GeoJets) (boxes : List Shape)
    (hboxes : ∀ q ∈ boxes, ChamberBox q) (hd : dimension J ≤ boxes.length) :
    mixedDegree J boxes =
      ∑ P ∈ J.minimalPrimesFinset, (localWeight J P : ℚ) * mixedDegree P boxes := by
  unfold mixedDegree
  rw [polarize_congr (h1 J boxes.length hd) hboxes baseline_box,
    polarize_sum, Finset.sum_div]
  simp only [mul_div_assoc]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_3.c3 := by
  classical
  intro J boxes hboxes hd S hS
  rw [mixed_cycle h1 J boxes hboxes hd]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hS P hP)) ?_
  intro P hP _
  have hmin : J.IsMinimalPrime P := Ideal.mem_minimalPrimesFinset.mp hP
  have hdim := (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hmin.le).trans hd
  exact mul_nonneg (Nat.cast_nonneg _) (mixed_nonneg h2 hmin.isPrime hboxes hdim)
end
end K1_13_6_2_3_3
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
open scoped BigOperators
def capPlus (x y : Shape × ℕ) : Shape × ℕ := (x.1.plus y.1, x.2 + y.2)
def volumeProduct (x : Shape × ℕ) : ℚ := (volume32 x.1 : ℚ) * x.2
def diagonal (J : Finset (Fin 5)) (i : Fin 5) : ℕ := if i ∈ J then 2 else 1
private theorem diagonal_sum_insert (w : Fin 5 → ℕ) {i : Fin 5} {J : Finset (Fin 5)}
    (hi : i ∉ J) :
    (∑ k, diagonal (insert i J) k * w k) =
      (∑ k, diagonal J k * w k) + w i := by
  calc
    _ = ∑ k, (diagonal J k * w k + if k = i then w i else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = i
      · subst k
        simp [diagonal, hi, two_mul]
      · simp [diagonal, h]
    _ = _ := by simp [Finset.sum_add_distrib]
private theorem sumCap_insert (B : Boxes) {i : Fin 5} {J : Finset (Fin 5)} (hi : i ∉ J) :
    sumCap B (diagonal (insert i J)) = capPlus (sumCap B (diagonal J)) (B i) := by
  simp only [sumCap, capPlus, Shape.plus, diagonal_sum_insert _ hi]
def alt (B : Boxes) (s : Finset (Fin 5)) (F : Shape × ℕ → ℚ) : ℚ :=
  ∑ J ∈ s.powerset, (-1 : ℚ) ^ (s.card - J.card) * F (sumCap B (diagonal J))
def capDiff (a : Shape × ℕ) (F : Shape × ℕ → ℚ) (x : Shape × ℕ) : ℚ :=
  F (capPlus x a) - F x
theorem alt_empty (B : Boxes) (F : Shape × ℕ → ℚ) :
    alt B ∅ F = F (sumCap B (diagonal ∅)) := by
  simp [alt]
theorem alt_insert (B : Boxes) {s : Finset (Fin 5)} {i : Fin 5}
    (hi : i ∉ s) (F : Shape × ℕ → ℚ) :
    alt B (insert i s) F = alt B s (capDiff (B i) F) := by
  have hJ (J) (hJ : J ∈ s.powerset) : i ∉ J :=
    Finset.notMem_of_mem_powerset_of_notMem hJ hi
  have hdisj : Disjoint s.powerset (s.powerset.image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro J hJs hJi
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hJi
    exact hJ _ hJs (Finset.mem_insert_self _ _)
  have hinj : Set.InjOn (insert i) (s.powerset : Set (Finset (Fin 5))) :=
    fun J hJs T hTs h => by
      simpa [Finset.erase_insert (hJ J hJs), Finset.erase_insert (hJ T hTs)] using
        congrArg (fun U : Finset (Fin 5) => U.erase i) h
  unfold alt
  rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJs
  have hcard := Finset.card_le_card (Finset.mem_powerset.mp hJs)
  have hstep : s.card + 1 - J.card = s.card - J.card + 1 := by omega
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem (hJ J hJs), hstep,
    pow_succ, sumCap_insert B (hJ J hJs)]
  simp only [Nat.add_sub_add_right, capDiff]
  ring
private def signed4 (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
theorem signed4_le (p q r s : Shape) : (signed4 p q r s : ℚ) ≤ mixed32 p q r s := by
  have h : signed4 p q r s ≤ ((signed4 p q r s).toNat : ℤ) := by omega
  exact_mod_cast h
private def shapeVolume (x : Shape) : ℚ := (volume32 x : ℚ)
private def shapeShift (a : Shape) (F : Shape → ℚ) (x : Shape) : ℚ := F (x.plus a)
private def shapeDiff (a : Shape) (F : Shape → ℚ) (x : Shape) : ℚ := F (x.plus a) - F x
private theorem shapeDiff_shift (a b : Shape) (F : Shape → ℚ) :
    shapeDiff b (shapeShift a F) = shapeShift a (shapeDiff b F) := by
  funext x
  have h : (x.plus b).plus a = (x.plus a).plus b := by
    simp [Shape.plus, Nat.add_comm, Nat.add_left_comm]
  simp only [shapeDiff, shapeShift, h]
private def constantInterval (F : Shape → ℚ) (x : Shape × ℕ) : ℚ := F x.1
private def linearInterval (F : Shape → ℚ) (x : Shape × ℕ) : ℚ := F x.1 * x.2
private theorem capDiff_add (a : Shape × ℕ) (F G : Shape × ℕ → ℚ) :
    capDiff a (fun x => F x + G x) = fun x => capDiff a F x + capDiff a G x := by
  funext x
  unfold capDiff
  ring
private theorem capDiff_smul (a : Shape × ℕ) (d : ℚ) (F : Shape × ℕ → ℚ) :
    capDiff a (fun x => d * F x) = fun x => d * capDiff a F x := by
  funext x
  unfold capDiff
  ring
private theorem capDiff_constantInterval (a : Shape) (d : ℕ) (F : Shape → ℚ) :
    capDiff (a, d) (constantInterval F) = constantInterval (shapeDiff a F) := rfl
private theorem capDiff_linearInterval (a : Shape) (d : ℕ) (F : Shape → ℚ) :
    capDiff (a, d) (linearInterval F) =
      fun x => linearInterval (shapeDiff a F) x + (d : ℚ) * constantInterval (shapeShift a F) x := by
  funext x
  simp only [capDiff, linearInterval, capPlus, Nat.cast_add, constantInterval, shapeDiff, shapeShift]
  ring
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
private theorem fourth_difference (p q r s : Shape) :
    shapeDiff s (shapeDiff r (shapeDiff q (shapeDiff p shapeVolume))) =
      fun _ => (signed4 p q r s : ℚ) := by
  funext x
  simp only [shapeDiff, shapeVolume, signed4, difference, volume32, Shape.plus]
  push_cast
  ring
theorem five_differences (p q g a b : Shape) (d e : ℕ) (x : Shape × ℕ) :
    capDiff (b, e) (capDiff (a, d) (capDiff (g, 1) (capDiff (q, 0)
      (capDiff (p, 0) volumeProduct)))) x =
      (signed4 p q a b : ℚ) + (d : ℚ) * (signed4 p q g b : ℚ) +
        (e : ℚ) * (signed4 p q g a : ℚ) := by
  change capDiff (b, e) (capDiff (a, d) (capDiff (g, 1) (capDiff (q, 0)
    (capDiff (p, 0) (linearInterval shapeVolume))))) x = _
  simp only [capDiff_linearInterval, capDiff_add, capDiff_smul, capDiff_constantInterval,
    Nat.cast_zero, zero_mul, add_zero, shapeDiff_shift, fourth_difference]
  simp only [linearInterval, constantInterval, shapeShift, shapeDiff, sub_self, zero_mul,
    zero_add, Nat.cast_one, one_mul]
  ring
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped Polynomial
abbrev Grade := Exponent
abbrev Form := MvPolynomial (Fin 5) ℚ
abbrev Generator (B : Boxes) := (i : Fin 5) × latticePoints (B i)
abbrev SlotRing (B : Boxes) := MvPolynomial (Generator B) GeoField
instance (B : Boxes) : Finite (Generator B) := by
  infer_instance
def unitGrade (i : Fin 5) : Grade := Finsupp.single i 1
def squarefree (I : Finset (Fin 5)) : Grade := ∑ i ∈ I, unitGrade i
def slotWeight {σ : Type} (slot : σ → Fin 5) (v : σ) : Grade := unitGrade (slot v)
abbrev piece {σ : Type} (slot : σ → Fin 5) :=
  weightedHomogeneousSubmodule GeoField (slotWeight slot)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def gradedHilbert {σ : Type} (slot : σ → Fin 5) (J : Ideal (MvPolynomial σ GeoField))
    (t : Grade) : ℕ :=
  Module.finrank GeoField ((piece slot t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap)
def slot (B : Boxes) : Generator B → Fin 5 := Sigma.fst
def taggedMap (B : Boxes) : SlotRing B →ₐ[GeoField] GeoJets5 :=
  aeval fun v => monomial v.2.val 1
def gradedIdeal (B : Boxes) (P : Ideal GeoJets5) : Ideal (SlotRing B) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).toIdeal
def diagonalIdeal (B : Boxes) (P : Ideal GeoJets5) (t : Grade) :=
  P.comap (monomialMap GeoField (diagonalExponents B t))
def outside {σ : Type} (A : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {a | ∀ b ∈ A, ¬ b ≤ a}
def sliceCount {σ : Type} (s : σ → Fin 5) (A : Finset (σ →₀ ℕ)) (t : Grade) : ℕ :=
  {a ∈ outside A | Finsupp.weight (slotWeight s) a = t}.ncard
def Represents (p : Form) (h : Grade → ℚ) : Prop :=
  ∃ N : ℕ, ∀ t : Grade, (∀ j, N ≤ t j) → eval (fun j => (t j : ℚ)) p = h t
def TopNonnegative (p : Form) : Prop :=
  ∀ a : Grade, p.totalDegree ≤ a.degree → 0 ≤ p.coeff a
def line (t : Grade) : Form →+* (Polynomial ℚ) :=
  eval₂Hom Polynomial.C (fun j => Polynomial.C (t j : ℚ) * Polynomial.X)
def positiveDiagonal (J : Finset (Fin 5)) : Grade :=
  Finsupp.equivFunOnFinite.symm fun i => if i ∈ J then 2 else 1
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem gradedIdeal_homogeneous (B : Boxes) (P : Ideal GeoJets5) :
    (gradedIdeal B P).IsHomogeneous (piece (slot B)) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).isHomogeneous
theorem gradedIdeal_mono (B : Boxes) {P Q : Ideal GeoJets5} (h : P ≤ Q) :
    gradedIdeal B P ≤ gradedIdeal B Q :=
  Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem mem_gradedIdeal_of_grade {B : Boxes} {P : Ideal GeoJets5} {a : SlotRing B}
    {t : Grade} (ha : a ∈ piece (slot B) t) :
    a ∈ gradedIdeal B P ↔ taggedMap B a ∈ P := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (piece (slot B)) (P.comap (taggedMap B)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, ha⟩ h
theorem component_mul_of_grade {σ : Type} (s : σ → Fin 5)
    {g : MvPolynomial σ GeoField} {e : Grade} (hg : g ∈ piece s e)
    (a : MvPolynomial σ GeoField) (t : Grade) :
    weightedHomogeneousComponent (slotWeight s) (t + e) (a * g) =
      weightedHomogeneousComponent (slotWeight s) t a * g := by
  induction a using MvPolynomial.induction_on' with
  | monomial b r =>
    have hb := isWeightedHomogeneous_monomial (slotWeight s) b r rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight s) e := hg
    simp only [weightedHomogeneousComponent_of_mem (hb.mul hg'),
      weightedHomogeneousComponent_of_mem hb, add_right_cancel_iff]
    split <;> simp_all
  | add a b ha hb => simp [add_mul, ha, hb]
theorem homogeneous_colon {σ : Type} (s : σ → Fin 5)
    {J : Ideal (MvPolynomial σ GeoField)} (hJ : J.IsHomogeneous (piece s))
    {g : MvPolynomial σ GeoField} {e : Grade} (hg : g ∈ piece s e) :
    (J.colon {g}).IsHomogeneous (piece s) := by
  intro t a ha
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at ha ⊢
  have hp : (DirectSum.decompose (piece s) a t : MvPolynomial σ GeoField) =
      weightedHomogeneousComponent (slotWeight s) t a :=
    weightedDecomposition.decompose'_apply GeoField (slotWeight s) a t
  rw [hp, ← component_mul_of_grade s hg a t]
  exact weightedHomogeneousComponent_mem_of_mem _ _ hJ ha _
private theorem gradedIdeal_colon {B : Boxes} {P Q : Ideal GeoJets5} {g : SlotRing B}
    {e : Grade} (hg : g ∈ piece (slot B) e)
    (h : ∀ a : GeoJets5, a * taggedMap B g ∈ P ↔ a ∈ Q) :
    (gradedIdeal B P).colon {g} = gradedIdeal B Q := by
  ext a
  rw [mem_iff_weightedHomogeneousComponent_mem _ _
      (homogeneous_colon (slot B) (gradedIdeal_homogeneous B P) hg),
    mem_iff_weightedHomogeneousComponent_mem _ _ (gradedIdeal_homogeneous B Q)]
  apply forall_congr'
  intro t
  let z := weightedHomogeneousComponent (slotWeight (slot B)) t a
  have hz : z ∈ piece (slot B) t := weightedHomogeneousComponent_mem _ _ _
  have hg' : g.IsWeightedHomogeneous (slotWeight (slot B)) e := hg
  have hzg : z * g ∈ piece (slot B) (t + e) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
  change z ∈ (gradedIdeal B P).colon {g} ↔ z ∈ gradedIdeal B Q
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_gradedIdeal_of_grade hzg,
    mem_gradedIdeal_of_grade hz, map_mul, h]
private theorem allowed_scaled {a : Shape × ℕ} {m : Exponent} (h : Allowed a m) :
    m ∈ latticePoints a := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  change Allowed (a.1.scale 2, 2 * a.2) m
  simp only [Allowed, Shape.scale]
  exact ⟨by omega, by omega, by omega, by omega⟩
private theorem allowed_add_scaled {a : Shape × ℕ} {m n : Exponent}
    (hm : Allowed a m) (hn : Allowed a n) : m + n ∈ latticePoints a := by
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := hn
  change Allowed (a.1.scale 2, 2 * a.2) (m + n)
  simp only [Allowed, Shape.scale, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib]
  exact ⟨by omega, by omega, by omega, by omega⟩
private theorem exists_slot_lift (B : Boxes) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ latticePoints (B i)) :
    ∃ g : SlotRing B, g ∈ piece (slot B) (unitGrade i) ∧ taggedMap B g = D := by
  classical
  let gen (m : D.support) : Generator B := ⟨i, ⟨m, hD m m.property⟩⟩
  refine ⟨∑ m : D.support, C (D.coeff m) * MvPolynomial.X (gen m), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro m _
    have hc : (C (D.coeff m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) 0 :=
      isWeightedHomogeneous_C _ _
    have hx : (MvPolynomial.X (gen m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) (unitGrade i) :=
      isWeightedHomogeneous_X GeoField (slotWeight (slot B)) (gen m)
    rw [mem_weightedHomogeneousSubmodule]
    simpa only [zero_add] using hc.mul hx
  · simp only [map_sum, map_mul, taggedMap, aeval_C, algebraMap_eq, aeval_X,
      C_mul_monomial, mul_one, gen]
    rw [Finset.sum_coe_sort D.support (fun m => monomial m (D.coeff m))]
    exact D.support_sum_monomial_coeff
theorem regular_colon {P : Ideal GeoJets5} {D : GeoJets5}
    (h : IsLeftRegular (Ideal.Quotient.mk P D)) (a : GeoJets5) :
    a * D ∈ P ↔ a ∈ P := by
  constructor
  · intro ha
    rw [← Ideal.Quotient.eq_zero_iff_mem] at ha ⊢
    apply h
    change Ideal.Quotient.mk P D * Ideal.Quotient.mk P a = Ideal.Quotient.mk P D * 0
    rw [mul_zero, mul_comm, ← map_mul, ha]
  · exact P.mul_mem_right D
theorem square_colon {P : Ideal GeoJets5} {D : GeoJets5}
    (h : IsLeftRegular (Ideal.Quotient.mk P D)) (a : GeoJets5) :
    a * D ∈ sectionIdeal P (D ^ 2) ↔ a ∈ sectionIdeal P D := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
    have he : (a - c * D) * D = x := by
      rw [sub_mul, ← hxy, ← hc]
      ring
    have hm : a - c * D ∈ P := (regular_colon h _).mp (by rw [he]; exact hx)
    exact Submodule.mem_sup.mpr
      ⟨a - c * D, hm, c * D, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, sub_add_cancel _ _⟩
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact Submodule.mem_sup.mpr ⟨x * D, P.mul_mem_right D hx, c * D * D,
      Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩, by rw [← add_mul, hxy]⟩
theorem exists_regular_lifts (B : Boxes) (P : Ideal GeoJets5) (i : Fin 5) (D : GeoJets5)
    (hD : Box5 (B i).1 (B i).2 D) (hr : IsLeftRegular (Ideal.Quotient.mk P D)) :
    ∃ f g : SlotRing B,
      f ∈ piece (slot B) (unitGrade i) ∧ g ∈ piece (slot B) (unitGrade i) ∧
      (gradedIdeal B P).colon {f} = gradedIdeal B P ∧
      gradedIdeal B P ⊔ Ideal.span {f} ≤ gradedIdeal B (sectionIdeal P (D ^ 2)) ∧
      (gradedIdeal B (sectionIdeal P (D ^ 2))).colon {g} = gradedIdeal B (sectionIdeal P D) ∧
      gradedIdeal B (sectionIdeal P (D ^ 2)) ⊔ Ideal.span {g} ≤ gradedIdeal B (sectionIdeal P D) := by
  classical
  have hs (m : Exponent) (hm : m ∈ D.support) : Allowed (B i) m :=
    ⟨(hD.1 m hm).1, (hD.1 m hm).2.1, (hD.1 m hm).2.2, hD.2 m hm⟩
  have hs₂ (m : Exponent) (hm : m ∈ (D ^ 2).support) : m ∈ latticePoints (B i) := by
    rw [pow_two] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul D D hm)
    exact allowed_add_scaled (hs a ha) (hs b hb)
  obtain ⟨f, hf, hfmap⟩ := exists_slot_lift B i (D ^ 2) hs₂
  obtain ⟨g, hg, hgmap⟩ := exists_slot_lift B i D (fun m hm => allowed_scaled (hs m hm))
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · apply gradedIdeal_colon hf
    intro a
    rw [hfmap]
    have h : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
      rw [map_pow]
      exact IsLeftRegular.pow 2 hr
    exact regular_colon h a
  · refine sup_le (gradedIdeal_mono B le_sup_left) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [mem_gradedIdeal_of_grade hf, hfmap]
    exact (le_sup_right : Ideal.span {D ^ 2} ≤ sectionIdeal P (D ^ 2))
      (Ideal.mem_span_singleton_self _)
  · apply gradedIdeal_colon hg
    intro a
    rw [hgmap]
    exact square_colon hr a
  · refine sup_le (gradedIdeal_mono B (sup_le le_sup_left ?_))
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D, (pow_two D).symm⟩)).trans le_sup_right
    · rw [mem_gradedIdeal_of_grade hg, hgmap]
      exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.mem_span_singleton_self _)
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators Pointwise
theorem zero_mem_latticePoints (a : Shape × ℕ) : 0 ∈ latticePoints a := by
  simp [latticePoints, Allowed]
theorem zero_mem_diagonalExponents (B : Boxes) (t : Fin 5 → ℕ) :
    0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => zero_mem_latticePoints (B i), by simp⟩
private theorem nsmul_monomial_preimage {S : Set Exponent} {n : ℕ} {m : Exponent}
    (hm : m ∈ n • S) :
    ∃ P : MvPolynomial S GeoField,
      P.totalDegree ≤ n ∧ monomialMap GeoField S P = monomial m 1 := by
  induction n generalizing m with
  | zero =>
    rw [zero_smul, Set.mem_zero] at hm
    subst m
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul'] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    obtain ⟨P, hdeg, hP⟩ := ih hb
    refine ⟨MvPolynomial.X ⟨a, ha⟩ * P, ?_, ?_⟩
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
    · rw [map_mul, monomialMap_X, hP, monomial_mul_monomial, one_mul]
theorem monomial_hilbert_count (S : Set Exponent) (h0 : 0 ∈ S) (n : ℕ) :
    affineHilbertFunction (Ideal.comap (monomialMap GeoField S) ⊥) n = (n • S).ncard := by
  classical
  let φ := monomialMap GeoField S
  let j := Ideal.kerLiftAlg φ
  let V := quotientDegreeLE (RingHom.ker φ) n
  have hmap : V.map j.toLinearMap = restrictSupport GeoField (n • S) := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hv
      exact monomialMap_mem_restrictSupport_nsmul h0 hP
    · rw [restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨P, hP, hφ⟩ := nsmul_monomial_preimage hm
      exact ⟨_, mk_mem_quotientDegreeLE hP, hφ⟩
  rw [← RingHom.ker_eq_comap_bot]
  change Module.finrank GeoField V = _
  calc
    _ = Module.finrank GeoField (V.map j.toLinearMap) :=
      (Submodule.equivMapOfInjective _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq
    _ = _ := by
      rw [hmap, Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),
        Nat.card_coe_set_eq]
private def exponentEquiv : Exponent ≃ (Fin 4 →₀ ℕ) × ℕ :=
  Finsupp.equivFunOnFinite.trans
    ((Fin.snocEquiv (fun _ : Fin 5 => ℕ)).symm.trans
      ((Equiv.prodComm ℕ (Fin 4 → ℕ)).trans
        (Equiv.prodCongr Finsupp.equivFunOnFinite.symm (Equiv.refl ℕ))))
theorem lattice_count (a : Shape × ℕ) :
    (latticePoints a).ncard = (K1_13_6_2_3.capExponents a.1).ncard * (2 * a.2 + 1) := by
  classical
  let e : latticePoints a ≃ K1_13_6_2_3.capExponents a.1 × Fin (2 * a.2 + 1) :=
    { toFun := fun m => ⟨⟨(exponentEquiv m).1, by
        simpa [exponentEquiv, K1_13_6_2_3.capExponents, Finsupp.degree_eq_sum, Fin.init,
          Shape.scale]
          using And.intro m.property.1 (And.intro m.property.2.1 m.property.2.2.1)⟩,
        ⟨(exponentEquiv m).2, Nat.lt_succ_of_le m.property.2.2.2⟩⟩
      invFun := fun x => ⟨exponentEquiv.symm (x.1, x.2), by
        have hx := x.1.property
        change (x.1.val.degree ≤ _) ∧ _ at hx
        simp only [Finsupp.degree_eq_sum] at hx
        change (∑ i : Fin 4, Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) i.castSucc) ≤ 2 * a.1.b ∧
          (∑ i : Fin 4, i.val * Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) i.castSucc) ≤ 2 * a.1.j ∧
          Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) (Fin.castSucc (3 : Fin 4)) ≤ 2 * a.1.t ∧
          Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) (Fin.last 4) ≤ 2 * a.2
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
          And.intro hx.1 (And.intro hx.2.1 (And.intro hx.2.2 (Nat.le_of_lt_succ x.2.isLt)))⟩
      left_inv := fun m => Subtype.ext (exponentEquiv.symm_apply_apply m)
      right_inv := fun x => Prod.ext
        (Subtype.ext (congrArg Prod.fst (exponentEquiv.apply_symm_apply (x.1, (x.2 : ℕ)))))
        (Fin.ext (congrArg Prod.snd (exponentEquiv.apply_symm_apply (x.1, (x.2 : ℕ))))) }
  simpa only [Nat.card_coe_set_eq, Nat.card_prod, Nat.card_fin] using Nat.card_congr e
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3
open scoped BigOperators
def sumShape {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) : Shape :=
  ⟨∑ i, w i * (boxes i).b, ∑ i, w i * (boxes i).j, ∑ i, w i * (boxes i).t⟩
def capPiece (P : Ideal GeoJets) (p : Shape) : Submodule GeoField (GeoJets ⧸ P) :=
  (MvPolynomial.restrictSupport GeoField (capExponents p)).map
    (Ideal.Quotient.mkₐ GeoField P).toLinearMap
def standardCount {k m : ℕ} (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (w : Fin k → ℕ) : ℕ :=
  {e : Fin m →₀ ℕ | (∀ b ∈ bad, ¬ b ≤ e) ∧
    ∀ i, ∑ j ∈ Finset.univ.filter (fun j => slot j = i), e j = w i}.ncard
end
end K1_13_6_2_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_1 MvPolynomial Polynomial Filter
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (P : Ideal GeoJets) (k : ℕ) (boxes : Fin k → Shape),
    P.IsPrime → (∀ i, ChamberBox (boxes i)) →
    ∃ (m : ℕ) (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ)),
      ∀ w, Module.finrank GeoField (capPiece P (sumShape boxes w)) = standardCount slot bad w
def c2 : Prop :=
  ∀ (k m : ℕ) (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ)),
    ∃ (T r : ℕ) (f : Fin r → Fin k → ℕ → ℚ),
      (∀ a i, Monotone (f a i)) ∧ (∀ a i n, 0 ≤ f a i n) ∧
      ∀ (w : Fin k → ℕ), (∀ i, T ≤ w i) →
        (standardCount slot bad w : ℚ) = ∑ a, ∏ i, f a i (w i)
private def shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (n : ℕ) : Fin k → ℕ :=
  Function.update w i (w i + n)
private def diff {k : ℕ} (F : (Fin k → ℕ) → ℚ) (dirs : List (Fin k)) (n : ℕ)
    (w : Fin k → ℕ) : ℚ :=
  match dirs with
  | [] => F w
  | i :: rest => diff F rest n (shift w i n) - diff F rest n w
private theorem le_shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (n : ℕ) (j : Fin k) :
    w j ≤ shift w i n j := by
  by_cases h : j = i
  · subst j
    simp [shift]
  · simp [shift, Function.update_of_ne h]
private theorem diff_congr {k : ℕ} {F G : (Fin k → ℕ) → ℚ} {T : ℕ}
    (h : ∀ w, (∀ i, T ≤ w i) → F w = G w)
    (dirs : List (Fin k)) (n : ℕ) (w : Fin k → ℕ) (hw : ∀ i, T ≤ w i) :
    diff F dirs n w = diff G dirs n w := by
  induction dirs generalizing w with
  | nil => exact h w hw
  | cons i rest ih =>
    rw [diff, diff, ih w hw, ih (shift w i n) (fun j => (hw j).trans (le_shift w i n j))]
private theorem diff_sum {k r : ℕ} (F : Fin r → (Fin k → ℕ) → ℚ)
    (dirs : List (Fin k)) (n : ℕ) (w : Fin k → ℕ) :
    diff (fun v => ∑ a, F a v) dirs n w = ∑ a, diff (F a) dirs n w := by
  induction dirs generalizing w with
  | nil => rfl
  | cons i rest ih =>
    simp only [diff, ih, Finset.sum_sub_distrib]
private theorem diff_prod {k : ℕ} (f : Fin k → ℕ → ℚ) (dirs : List (Fin k))
    (hd : dirs.Nodup) (n : ℕ) (w : Fin k → ℕ) :
    diff (fun v => ∏ i, f i (v i)) dirs n w =
      ∏ i, if i ∈ dirs then f i (w i + n) - f i (w i) else f i (w i) := by
  induction dirs generalizing w with
  | nil => simp [diff]
  | cons i rest ih =>
    obtain ⟨hi, hr⟩ := List.nodup_cons.mp hd
    simp only [diff, ih hr]
    let g (v : Fin k → ℕ) (j : Fin k) :=
      if j ∈ rest then f j (v j + n) - f j (v j) else f j (v j)
    let s := (Finset.univ : Finset (Fin k)).erase i
    have hs : ∏ j ∈ s, g (shift w i n) j = ∏ j ∈ s, g w j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [g, shift, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    let h (j : Fin k) :=
      if j ∈ i :: rest then f j (w j + n) - f j (w j) else f j (w j)
    have hh : ∏ j ∈ s, h j = ∏ j ∈ s, g w j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [h, g, Finset.ne_of_mem_erase hj]
    change (∏ j, g (shift w i n) j) - (∏ j, g w j) = ∏ j, h j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    change g (shift w i n) i * (∏ j ∈ s, g (shift w i n) j) -
      g w i * (∏ j ∈ s, g w j) = h i * (∏ j ∈ s, h j)
    rw [hs, hh, ← sub_mul]
    simp [g, h, shift, hi]
private theorem standard_diff_nonneg (h : c2) {k m : ℕ}
    (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (dirs : List (Fin k)) (hd : dirs.Nodup) :
    ∃ T : ℕ, ∀ n (w : Fin k → ℕ), (∀ i, T ≤ w i) →
      0 ≤ diff (fun v => (standardCount slot bad v : ℚ)) dirs n w := by
  obtain ⟨T, r, f, hmono, hnonneg, hcount⟩ := h k m slot bad
  refine ⟨T, fun n w hw => ?_⟩
  rw [diff_congr hcount dirs n w hw, diff_sum]
  apply Finset.sum_nonneg
  intro a _
  rw [diff_prod (f a) dirs hd n w]
  apply Finset.prod_nonneg
  intro i _
  split
  · exact sub_nonneg.mpr (hmono a i (Nat.le_add_right _ _))
  · exact hnonneg a i (w i)
private abbrev capMap (p : Shape) := monomialMap GeoField (capExponents p)
private abbrev capIdeal (P : Ideal GeoJets) (p : Shape) := P.comap (capMap p).toRingHom
private lemma cap_dimension (P : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (affineHilbertPolynomial (capIdeal P p)).natDegree = dimension P := by
  have hsurj : Function.Surjective (capMap p) := by
    apply monomialMap_surjective
    obtain ⟨hb, hj, ht⟩ := hp
    intro i
    fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega
  exact natDegree_affineHilbertPolynomial_comap_of_surjective (capMap p) hsurj P
private lemma monomial_preimage (S : Set (Fin 4 →₀ ℕ)) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ n • S) :
    ∃ f : MvPolynomial S GeoField, f.totalDegree ≤ n ∧ monomialMap GeoField S f = monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨a, ha, b, hb, rfl⟩ := he
    obtain ⟨f, hn, hf⟩ := ih a ha
    refine ⟨f * MvPolynomial.X ⟨b, hb⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
    · simpa only [totalDegree_X] using Nat.add_le_add_right hn 1
    · rw [map_mul, hf, monomialMap_X, MvPolynomial.monomial_mul_monomial, mul_one]
private theorem capPiece_scale (P : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) (n : ℕ) :
    Module.finrank GeoField (capPiece P (p.scale n)) = affineHilbertFunction (capIdeal P p) n := by
  let I := capIdeal P p
  let g := Ideal.quotientMapₐ P (capMap p) (le_rfl : I ≤ capIdeal P p)
  have hg : Function.Injective g := Ideal.quotientMap_injective
  let V := quotientDegreeLE I n
  have hmap : V.map g.toLinearMap = capPiece P (p.scale n) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f, hf, rfl⟩ := mem_quotientDegreeLE.mp hx
      change Ideal.Quotient.mk P (capMap p f) ∈ capPiece P (p.scale n)
      refine ⟨capMap p f, ?_, rfl⟩
      rw [← nsmul_cap p hp n]
      exact monomialMap_mem_restrictSupport_nsmul (zero_mem_cap p) hf
    · unfold capPiece
      rw [Submodule.map_le_iff_le_comap, restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      rw [← nsmul_cap p hp n] at he
      obtain ⟨f, hf, hφ⟩ := monomial_preimage _ n e he
      have hmk : Ideal.Quotient.mk I f ∈ V := mk_mem_quotientDegreeLE hf
      exact ⟨Ideal.Quotient.mk I f, hmk, by
        change Ideal.Quotient.mk P (capMap p f) = Ideal.Quotient.mk P (monomial e 1)
        rw [hφ]⟩
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ hg V).finrank_eq.symm
private lemma capPiece_mono (P : Ideal GeoJets) {p q : Shape} (h : InBox p q) :
    Module.finrank GeoField (capPiece P p) ≤ Module.finrank GeoField (capPiece P q) := by
  have := restrictSupport_finite (R := GeoField) (Set.toFinite (capExponents q))
  have : Module.Finite GeoField (capPiece P q) := by unfold capPiece; infer_instance
  apply Submodule.finrank_mono
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  exact ⟨he.1.trans (Nat.mul_le_mul_left 2 h.1),
    he.2.1.trans (Nat.mul_le_mul_left 2 h.2.1), he.2.2.trans (Nat.mul_le_mul_left 2 h.2.2)⟩
private lemma sumShape_chamber {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ)
    (hb : ∀ i, ChamberBox (boxes i)) (hw : ∃ i, 0 < w i) : ChamberBox (sumShape boxes w) := by
  obtain ⟨i, hi⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · change (∑ j, w j * (boxes j).j) ≤ ∑ j, w j * (boxes j).b
    exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (w j) (hb j).1)
  · change 3 * (∑ j, w j * (boxes j).t) ≤ ∑ j, w j * (boxes j).j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (hb j).2.1
  · change 0 < ∑ j, w j * (boxes j).t
    exact (Nat.mul_pos hi (hb i).2.2).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (w j * (boxes j).t)) (Finset.mem_univ i))
private lemma sumShape_shift {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) (i : Fin k) :
    sumShape boxes (shift w i 1) = (sumShape boxes w).plus (boxes i) := by
  have h (a : Fin k → ℕ) :
      (∑ j, shift w i 1 j * a j) = (∑ j, w j * a j) + a i := by
    calc
      _ = ∑ j, (w j * a j + if j = i then a i else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [shift, Nat.add_mul]
        · simp [shift, hj]
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [sumShape, Shape.plus, h]
private lemma sumShape_ray {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) (N T : ℕ) :
    sumShape boxes (fun i => N * w i + T) =
      ((sumShape boxes w).scale N).plus (sumShape boxes (fun _ => T)) := by
  simp only [sumShape, Shape.scale, Shape.plus, Nat.add_mul, Finset.sum_add_distrib,
    Nat.mul_assoc, Finset.mul_sum]
private lemma cast_ray_shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (N T : ℕ) :
    shift (fun j => N * w j + T) i N = fun j => N * shift w i 1 j + T := by
  funext j
  by_cases h : j = i
  · subst j
    simp [shift, Nat.mul_add, Nat.add_right_comm]
  · simp [shift, Function.update_of_ne h]
private lemma capPiece_ray_bounds {k : ℕ} (P : Ideal GeoJets) (boxes : Fin k → Shape)
    (w : Fin k → ℕ) (hp : ChamberBox (sumShape boxes w)) (T : ℕ) :
    ∃ C : ℕ, ∀ N,
      affineHilbertFunction (capIdeal P (sumShape boxes w)) N ≤
        Module.finrank GeoField (capPiece P (sumShape boxes (fun i => N * w i + T))) ∧
      Module.finrank GeoField (capPiece P (sumShape boxes (fun i => N * w i + T))) ≤
        affineHilbertFunction (capIdeal P (sumShape boxes w)) (N + C) := by
  let p := sumShape boxes w
  let q := sumShape boxes (fun _ => T)
  let C := q.b + q.j + q.t
  have hbox : InBox q (p.scale C) := by
    obtain ⟨hb, hj, ht⟩ := hp
    have hj' : 0 < p.j := by change 3 * p.t ≤ p.j at hj; change 0 < p.t at ht; omega
    have hb' : 0 < p.b := hj'.trans_le hb
    exact ⟨(show q.b ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ hb'),
      (show q.j ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ hj'),
      (show q.t ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ ht)⟩
  refine ⟨C, fun N => ?_⟩
  rw [← capPiece_scale P hp N, ← capPiece_scale P hp (N + C), sumShape_ray]
  constructor
  · exact capPiece_mono P ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · apply capPiece_mono P
    obtain ⟨hb, hj, ht⟩ := hbox
    exact ⟨by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hb (N * p.b),
      by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hj (N * p.j),
      by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left ht (N * p.t)⟩
private theorem diff_bounds {k : ℕ} (P : Ideal GeoJets) (boxes : Fin k → Shape)
    (hb : ∀ i, ChamberBox (boxes i)) (d T : ℕ) (hd : dimension P ≤ d)
    (dirs : List (Fin k)) (w : Fin k → ℕ) (hw : ∃ i, 0 < w i) :
    ∃ L U : (Polynomial ℚ), L.natDegree ≤ d ∧ U.natDegree ≤ d ∧
      L.coeff d = diff (fun v => capCoeff P d (sumShape boxes v)) dirs 1 w ∧
      U.coeff d = diff (fun v => capCoeff P d (sumShape boxes v)) dirs 1 w ∧
      ∀ᶠ N : ℕ in atTop,
        L.eval (N : ℚ) ≤ diff (fun v => (Module.finrank GeoField (capPiece P (sumShape boxes v)) : ℚ))
          dirs N (fun i => N * w i + T) ∧
        diff (fun v => (Module.finrank GeoField (capPiece P (sumShape boxes v)) : ℚ))
          dirs N (fun i => N * w i + T) ≤ U.eval (N : ℚ) := by
  induction dirs generalizing w with
  | nil =>
    let p := sumShape boxes w
    let I := capIdeal P p
    let L := affineHilbertPolynomial I
    have hp := sumShape_chamber boxes w hb hw
    have hL : L.natDegree ≤ d := (cap_dimension P hp).trans_le hd
    obtain ⟨C, hC⟩ := capPiece_ray_bounds P boxes w hp T
    refine ⟨L, taylor (C : ℚ) L, hL, (natDegree_taylor _ _).trans_le hL, rfl,
      coeff_taylor_of_natDegree_le _ hL, ?_⟩
    obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial I
    filter_upwards [eventually_ge_atTop N₀] with N hN
    change (affineHilbertPolynomial I).eval (N : ℚ) ≤ _ ∧
      _ ≤ (taylor (C : ℚ) (affineHilbertPolynomial I)).eval (N : ℚ)
    rw [taylor_eval, ← Nat.cast_add, hN₀ N hN, hN₀ (N + C) (hN.trans (Nat.le_add_right _ _))]
    simp only [diff]
    exact ⟨by exact_mod_cast (hC N).1, by exact_mod_cast (hC N).2⟩
  | cons i dirs ih =>
    have hwi : ∃ j, 0 < shift w i 1 j := by
      obtain ⟨j, hj⟩ := hw
      exact ⟨j, hj.trans_le (le_shift w i 1 j)⟩
    obtain ⟨L₁, U₁, hL₁, hU₁, hcL₁, hcU₁, he₁⟩ := ih (shift w i 1) hwi
    obtain ⟨L₀, U₀, hL₀, hU₀, hcL₀, hcU₀, he₀⟩ := ih w hw
    refine ⟨L₁ - U₀, U₁ - L₀, (natDegree_sub_le _ _).trans (max_le hL₁ hU₀),
      (natDegree_sub_le _ _).trans (max_le hU₁ hL₀), ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_sub, hcL₁, hcU₀, diff]
    · rw [Polynomial.coeff_sub, hcU₁, hcL₀, diff]
    · filter_upwards [he₁, he₀] with N a b
      simp only [diff, cast_ray_shift, Polynomial.eval_sub]
      exact ⟨sub_le_sub a.1 b.2, sub_le_sub a.2 b.1⟩
private lemma diff_polarize {k : ℕ} (boxes : Fin k → Shape) (H : Shape → ℚ)
    (dirs : List (Fin k)) (w : Fin k → ℕ) :
    diff (fun v => H (sumShape boxes v)) dirs 1 w =
      polarize H (dirs.map boxes) (sumShape boxes w) := by
  induction dirs generalizing w with
  | nil => rfl
  | cons i rest ih =>
    simp only [diff, ih, List.map_cons, polarize, sumShape_shift]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_3_3.c2 := by
  intro P boxes hp hb hd _
  let p : Shape := ⟨3, 3, 1⟩
  let B : Fin (boxes.length + 1) → Shape := Fin.cons p boxes.get
  let dirs : List (Fin (boxes.length + 1)) := List.ofFn (fun i : Fin boxes.length => i.succ)
  let w : Fin (boxes.length + 1) → ℕ := Pi.single 0 1
  have hB (i : Fin (boxes.length + 1)) : ChamberBox (B i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change ChamberBox p
      exact ⟨by decide, by decide, by decide⟩
    · exact hb _ (List.get_mem _ _)
  have hdirs : dirs.Nodup := List.nodup_ofFn_ofInjective (Fin.succ_injective _)
  have hmap : dirs.map B = boxes := by
    rw [List.map_ofFn]
    exact List.ofFn_get boxes
  have hw : ∃ i, 0 < w i := ⟨0, by simp [w]⟩
  have hbase : sumShape B w = p := by
    simp [sumShape, w, Pi.single_apply, Finset.sum_ite_eq', B]
  obtain ⟨m, slot, bad, hcount⟩ := h1 P _ B hp hB
  obtain ⟨T, hpos⟩ := standard_diff_nonneg h2 slot bad dirs hdirs
  obtain ⟨_, U, _, hU, _, hc, hu⟩ := diff_bounds P B hB boxes.length T hd.le dirs w hw
  have hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ U.eval (N : ℚ) := by
    filter_upwards [hu] with N hN
    refine le_trans ?_ hN.2
    rw [diff_congr (T := 0) (fun v _ => by rw [hcount]) dirs N _ (fun _ => Nat.zero_le _)]
    exact hpos N _ (fun _ => Nat.le_add_left _ _)
  have hcoeff := coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg hU hnonneg
  rw [hc, diff_polarize, hmap, hbase] at hcoeff
  exact div_nonneg hcoeff (by positivity)
end
end K1_13_6_2_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_2
open K1_13 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_6_2_3_2
open scoped BigOperators Pointwise
private theorem slot_degree_ne_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (e : CapVar shapes →₀ ℕ) (i : ι) :
    Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 ↔
      ∃ v : CapVar shapes, v.1 = i ∧ e v ≠ 0 := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Function.comp_apply,
    capSlot, step, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Nat.cast_id]
  rw [← Nat.pos_iff_ne_zero, Finset.sum_pos_iff]
  constructor
  · rintro ⟨v, _, hv⟩
    by_cases hvi : v.1 = i
    · exact ⟨v, hvi, Nat.ne_of_gt (by simpa [hvi] using hv)⟩
    · rw [Pi.single_eq_of_ne (Ne.symm hvi)] at hv
      simp at hv
  · rintro ⟨v, hvi, hv⟩
    exact ⟨v, Finsupp.mem_support_iff.mpr hv, by simpa [hvi] using Nat.pos_of_ne_zero hv⟩
private theorem productExponents_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape) :
    productExponents shapes 0 = 0 := by
  ext m
  simp only [Set.mem_zero, productExponents, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have he : e = 0 := by
      ext v
      rw [Finsupp.zero_apply]
      by_contra hv
      have hslot := (slot_degree_ne_zero shapes e v.1).mpr ⟨v, rfl, hv⟩
      simp [hdeg] at hslot
    simpa [he] using hexp.symm
  · rintro rfl
    exact ⟨0, map_zero _, map_zero _⟩
private theorem productExponents_add_step {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (a : ι → ℕ) (i : ι) :
    productExponents shapes (a + step i) =
      productExponents shapes a + capExponents (shapes i) := by
  ext m
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have hne : Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 := by
      simp [hdeg, step]
    obtain ⟨v, hvi, hv⟩ := (slot_degree_ne_zero shapes e i).mp hne
    let e' := e - Finsupp.single v 1
    have hdeg' : Finsupp.weight (step ∘ capSlot shapes) e' + step i = a + step i := by
      have h := Finsupp.weight_sub_single_add (w := step ∘ capSlot shapes) hv
      calc
        _ = Finsupp.weight (step ∘ capSlot shapes) e := by
          simpa only [e', Function.comp_apply, capSlot, hvi] using h
        _ = _ := hdeg
    refine ⟨Finsupp.weight (fun u : CapVar shapes => u.2.val) e',
      ⟨e', add_right_cancel hdeg', rfl⟩, v.2.val, ?_, ?_⟩
    · simpa only [hvi] using v.2.property
    · exact (Finsupp.weight_sub_single_add hv).trans hexp
  · rintro ⟨m', ⟨e, hdeg, hexp⟩, w, hw, rfl⟩
    let v : CapVar shapes := ⟨i, ⟨w, hw⟩⟩
    refine ⟨e + Finsupp.single v 1, ?_, ?_⟩
    · rw [map_add, Finsupp.weight_single, one_smul, hdeg] <;> rfl
    · simp only [map_add, Finsupp.weight_single, one_smul, hexp, v]
private theorem capExponents_zero : capExponents ⟨0, 0, 0⟩ = 0 := by
  ext m
  simp only [cap_coords, Set.mem_zero, Nat.mul_zero]
  constructor
  · intro hm
    have h := hm.1
    ext k
    fin_cases k
    · change m 0 = 0; omega
    · change m 1 = 0; omega
    · change m 2 = 0; omega
    · change m 3 = 0; omega
  · rintro rfl
    simp
private theorem sum_add_step_mul {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (i : ι) (f : ι → ℕ) :
    (∑ k, (a + step i) k * f k) = (∑ k, a k * f k) + f i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_eq_single i]
  · simp [step]
  · intro k hki
    simp [step, Pi.single_eq_of_ne hki]
private theorem shapeSum_add_step {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape)
    (a : ι → ℕ) (i : ι) :
    shapeSum shapes (a + step i) = (shapeSum shapes a).plus (shapes i) := by
  simp only [shapeSum, Shape.plus, sum_add_step_mul]
private theorem exists_nonzero_slot {ι : Type} (a : ι → ℕ) (ha : a ≠ 0) :
    ∃ i, a i ≠ 0 := by
  by_contra! h
  exact ha (funext h)
private theorem chamber_shapeSum {ι : Type} [Fintype ι] (shapes : ι → Shape)
    (hsh : ∀ i, ChamberBox (shapes i)) (a : ι → ℕ) (ha : a ≠ 0) :
    ChamberBox (shapeSum shapes a) := by
  refine ⟨Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left (a i) (hsh i).1, ?_, ?_⟩
  · dsimp [shapeSum]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.mul_left_comm 3 (a i)]
    exact Nat.mul_le_mul_left (a i) (hsh i).2.1
  · obtain ⟨i, hi⟩ := exists_nonzero_slot a ha
    exact (Nat.mul_pos (Nat.pos_of_ne_zero hi) (hsh i).2.2).trans_le
      (Finset.single_le_sum (f := fun k => a k * (shapes k).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
theorem proof : K1_13_6_2_3_2.c2 := by
  intro ι _ _ shapes hsh a
  induction a using WellFounded.induction (measure (fun b : ι → ℕ => ∑ i, b i)).wf with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha, productExponents_zero]
      simpa [shapeSum] using capExponents_zero.symm
    · obtain ⟨i, hi⟩ := exists_nonzero_slot a ha
      let b := a - step i
      have hab : b + step i = a := by
        funext k
        change a k - step i k + step i k = a k
        apply Nat.sub_add_cancel
        by_cases hki : k = i
        · subst k
          simpa [step] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [step, Pi.single_eq_of_ne hki]
      have hsum : (∑ k, a k) = (∑ k, b k) + 1 := by
        rw [← hab]
        simpa only [Nat.mul_one] using sum_add_step_mul b i (fun _ => 1)
      have hlt : (∑ k, b k) < ∑ k, a k := by omega
      rw [← hab, productExponents_add_step, shapeSum_add_step]
      by_cases hb : b = 0
      · rw [hb, productExponents_zero, zero_add]
        cases shapes i
        simp [shapeSum, Shape.plus]
      · rw [ih b hlt, cap_add (chamber_shapeSum shapes hsh b hb) (hsh i)]
end K1_13_6_2_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {ι : Type}
def ray (P : MvPolynomial ι ℚ) (u v : ι → ℕ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun i => Polynomial.C (v i : ℚ) * Polynomial.X +
    Polynomial.C (u i : ℚ)) P
theorem ray_eval (P : MvPolynomial ι ℚ) (u v : ι → ℕ) (n : ℕ) :
    (ray P u v).eval (n : ℚ) = MvPolynomial.eval (fun i => ((u i + n * v i : ℕ) : ℚ)) P := by
  let φ : Polynomial ℚ →ₐ[ℚ] ℚ := Polynomial.aeval (n : ℚ)
  change φ (ray P u v) = _
  rw [ray, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
  have he : (fun i => φ (Polynomial.C (v i : ℚ) * Polynomial.X +
      Polynomial.C (u i : ℚ))) = (fun i => ((u i + n * v i : ℕ) : ℚ)) := by
    funext i
    simp [φ, Polynomial.aeval_def, mul_comm, add_comm]
  rw [he]
private theorem prod_top (f : ι → Polynomial ℚ) (e : ι →₀ ℕ)
    (h : ∀ i, (f i).natDegree ≤ 1) (s : Finset ι) :
    (∏ i ∈ s, f i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
    (∏ i ∈ s, f i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff 1 ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have hpow : ((f i) ^ e i).natDegree ≤ e i := by
      simpa using Polynomial.natDegree_pow_le_of_le (e i) (h i)
    refine ⟨(Polynomial.natDegree_mul_le).trans (Nat.add_le_add hpow ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2]
    rw [show (f i ^ e i).coeff (e i) = (f i).coeff 1 ^ e i by
      simpa only [mul_one] using Polynomial.coeff_pow_of_natDegree_le (m := e i) (h i)]
private theorem affine_top (f : ι → Polynomial ℚ) (h : ∀ i, (f i).natDegree ≤ 1)
    (P : MvPolynomial ι ℚ) (d : ℕ) (hd : P.totalDegree ≤ d) :
    (MvPolynomial.aeval f P).coeff d =
      MvPolynomial.eval (fun i => (f i).coeff 1) (homogeneousComponent d P) := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hle : e.degree ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  rw [MvPolynomial.aeval_monomial, ← Polynomial.C_eq_algebraMap, Polynomial.coeff_C_mul]
  by_cases hEq : e.degree = d
  · rw [ite_eq_left hEq, ← hEq, Finsupp.degree_apply, MvPolynomial.eval_monomial]
    congr 1
    exact (prod_top f e h e.support).2
  · rw [ite_eq_right hEq, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    exact (prod_top f e h e.support).1.trans_lt (lt_of_le_of_ne hle hEq)
theorem ray_top (P : MvPolynomial ι ℚ) (u v : ι → ℕ) {d : ℕ} (hd : P.totalDegree ≤ d) :
    (ray P u v).coeff d = MvPolynomial.eval (fun i => (v i : ℚ)) (homogeneousComponent d P) := by
  unfold ray
  rw [affine_top _ (fun i => ?_) P d hd]
  · simp [Polynomial.coeff_add]
  · apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simpa using Polynomial.natDegree_C_mul_X_pow_le (v i : ℚ) 1) (by simp)
theorem totalDegree_le_of_ray_degree (P : MvPolynomial ι ℚ) (u : ι → ℕ) (d : ℕ)
    (h : ∀ v : ι → ℕ, (∀ i, 0 < v i) → (ray P u v).natDegree ≤ d) :
    P.totalDegree ≤ d := by
  classical
  by_contra! hd
  let f (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro m n hmn
    change ((m + 1 : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) at hmn
    have hmn' : m + 1 = n + 1 := by exact_mod_cast hmn
    omega
  have hvanish : homogeneousComponent P.totalDegree P = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range f)
      (fun _ => Set.infinite_range_of_injective hf)
    intro x hx
    choose w hw using fun i : ι => hx i (Set.mem_univ i)
    let v : ι → ℕ := fun i => w i + 1
    have hv : (fun i => (v i : ℚ)) = x := _root_.funext hw
    rw [← hv, ← ray_top P u v le_rfl, map_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h v (fun i => Nat.succ_pos (w i))).trans_lt hd)
  have hlt : P.totalDegree < P.totalDegree := by
    change P.support.sup (fun e => e.degree) < P.totalDegree
    refine (Finset.sup_lt_iff (Nat.zero_lt_of_lt hd)).2 fun e he' => ?_
    have hz := congrArg (fun Q : MvPolynomial ι ℚ => Q.coeff e) hvanish
    by_contra! heq
    have hEq : e.degree = P.totalDegree := le_antisymm (MvPolynomial.le_totalDegree he') heq
    rw [coeff_homogeneousComponent, ite_eq_left hEq, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hz
    exact MvPolynomial.mem_support_iff.mp he' hz
  exact (lt_irrefl _ hlt)
end
end K1_13_6_2_3_2_5
end
section
namespace K1_13_6_2_3_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial
open scoped BigOperators
private theorem weight_mapDomain {α β : Type} (f : α → β) (w : β → Fin 4 →₀ ℕ)
    (e : α →₀ ℕ) : Finsupp.weight w (e.mapDomain f) = Finsupp.weight (w ∘ f) e := by
  simp only [Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul ..)
private theorem unit_weight (p : Shape) (e : CapVar (fun _ : Unit => p) →₀ ℕ) :
    Finsupp.weight (step ∘ capSlot (fun _ : Unit => p)) e = fun _ => e.degree := by
  have h : step ∘ capSlot (fun _ : Unit => p) = fun _ _ => (1 : ℕ) := by
    funext v i
    obtain ⟨⟨⟩, v⟩ := v
    cases i
    simp [capSlot, step]
  rw [h, Finsupp.weight_apply, Finsupp.degree_apply]
  funext i
  simp [Finsupp.sum, Finset.sum_apply]
private theorem monomialMap_monomial_one (p : Shape) (e : capExponents p →₀ ℕ) :
    monomialMap GeoField (capExponents p) (monomial e 1) =
      monomial (Finsupp.weight Subtype.val e) 1 := by
  rw [monomialMap, aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, monomial_pow, one_pow]
  let M := monomialOneHom GeoField (Fin 4)
  change (∏ i ∈ e.support, M (Multiplicative.ofAdd (e i • i.val))) =
    M (Multiplicative.ofAdd (∑ i ∈ e.support, e i • i.val))
  rw [ofAdd_sum, map_prod]
private theorem image_weight_degreeLE (p : Shape) (n : ℕ) :
    Finsupp.weight (fun i : capExponents p => i.val) '' {e | e.degree ≤ n} =
      productExponents (fun _ : Unit => p) (fun _ => n) := by
  classical
  let tag : capExponents p → CapVar (fun _ : Unit => p) := fun i => ⟨(), i⟩
  let untag : CapVar (fun _ : Unit => p) → capExponents p := fun v => v.2
  let zeroVar : CapVar (fun _ : Unit => p) := ⟨(), ⟨0, by simp [capExponents]⟩⟩
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    change e.degree ≤ n at he
    refine ⟨e.mapDomain tag + Finsupp.single zeroVar (n - e.degree), ?_, ?_⟩
    · rw [unit_weight, map_add, Finsupp.degree_mapDomain, Finsupp.degree_single,
        Nat.add_sub_of_le he]
    · rw [map_add, weight_mapDomain, Finsupp.weight_single]
      change Finsupp.weight (fun i : capExponents p => i.val) e + (n - e.degree) •
        (0 : Fin 4 →₀ ℕ) = Finsupp.weight (fun i : capExponents p => i.val) e
      rw [smul_zero, add_zero]
  · rintro ⟨e, hdegree, rfl⟩
    refine ⟨e.mapDomain untag, ?_, weight_mapDomain untag Subtype.val e⟩
    change (e.mapDomain untag).degree ≤ n
    rw [Finsupp.degree_mapDomain]
    rw [unit_weight] at hdegree
    exact (congrFun hdegree ()).le
private theorem map_restrictTotalDegree (p : Shape) (n : ℕ) :
    (restrictTotalDegree (capExponents p) GeoField n).map
      (monomialMap GeoField (capExponents p)).toLinearMap =
      restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n)) := by
  classical
  let D : Set (capExponents p →₀ ℕ) := {e | e.degree ≤ n}
  let A := productExponents (fun _ : Unit => p) (fun _ => n)
  let f := (monomialMap GeoField (capExponents p)).toLinearMap
  change (restrictSupport GeoField D).map f = restrictSupport GeoField A
  have hgens : (fun e => f (monomial e 1)) '' D = (fun m => monomial m (1 : GeoField)) '' A := by
    rw [show A = Finsupp.weight Subtype.val '' D from (image_weight_degreeLE p n).symm,
      Set.image_image]
    apply Set.image_congr'
    intro e
    change monomialMap GeoField (capExponents p) (monomial e 1) =
      monomial (Finsupp.weight Subtype.val e) 1
    exact monomialMap_monomial_one p e
  rw [restrictSupport_eq_span GeoField D, restrictSupport_eq_span GeoField A,
    Submodule.map_span, Set.image_image, hgens]
theorem proof : K1_13_6_2_3_2.c4 := by
  intro J p n
  let f := monomialMap GeoField (capExponents p)
  let I := J.comap f.toRingHom
  let g : MvPolynomial (capExponents p) GeoField ⧸ I →ₐ[GeoField] GeoJets ⧸ J :=
    Ideal.quotientMapₐ J f le_rfl
  let L := g.toLinearMap.domRestrict (quotientDegreeLE I n)
  have hL : Function.Injective L := by
    intro x y hxy
    exact Subtype.ext (Ideal.quotientMap_injective (I := J) (f := f.toRingHom) hxy)
  have hcomp : g.comp (Ideal.Quotient.mkₐ GeoField I) = (Ideal.Quotient.mkₐ GeoField J).comp f :=
    Ideal.quotient_map_comp_mkₐ J f le_rfl
  have hmap : (restrictTotalDegree (capExponents p) GeoField n).map f.toLinearMap =
      restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n)) :=
    map_restrictTotalDegree p n
  have hrange : LinearMap.range L =
      (restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n))).map
        (Ideal.Quotient.mkₐ GeoField J).toLinearMap := by
    dsimp only [L]
    rw [LinearMap.range_domRestrict, quotientDegreeLE, ← Submodule.map_comp,
      ← AlgHom.comp_toLinearMap, hcomp, AlgHom.comp_toLinearMap, Submodule.map_comp, hmap]
  change Module.finrank GeoField (quotientDegreeLE I n) = _
  rw [← LinearMap.finrank_range_of_inj hL, hrange, supportRank]
end
end K1_13_6_2_3_2_4
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial Filter
open scoped BigOperators
variable {ι : Type} [Fintype ι]
theorem shapeSum_add (shapes : ι → Shape) (a b : ι → ℕ) :
    shapeSum shapes (a + b) = (shapeSum shapes a).plus (shapeSum shapes b) := by
  simp [shapeSum, Shape.plus, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem shapeSum_step [DecidableEq ι] (shapes : ι → Shape) (i : ι) :
    shapeSum shapes (step i) = shapes i := by
  simp [shapeSum, step, Pi.single_apply, ite_mul]
private theorem shapeSum_scale (shapes : ι → Shape) (n : ℕ) (v : ι → ℕ) :
    shapeSum shapes (fun i => n * v i) = (shapeSum shapes v).scale n := by
  simp [shapeSum, Shape.scale, mul_assoc, Finset.mul_sum]
private theorem shapeSum_chamber (shapes : ι → Shape) (hs : ∀ i, ChamberBox (shapes i))
    (v : ι → ℕ) (base : ι) (hv : 0 < v base) : ChamberBox (shapeSum shapes v) := by
  refine ⟨Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hs i).1), ?_, ?_⟩
  · change 3 * (∑ i, v i * (shapes i).t) ≤ ∑ i, v i * (shapes i).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [Nat.mul_left_comm 3]
      exact Nat.mul_le_mul_left _ (hs i).2.1
  · exact (Nat.mul_pos hv (hs base).2.2).trans_le
      (Finset.single_le_sum (f := fun i => v i * (shapes i).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ base))
private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;>
    norm_num [K1_13_6_2_3_1.cap_coords, Finsupp.single_apply] <;> omega
private theorem supportRank_le (J : Ideal GeoJets) {p q : Shape} (h : InBox p q) :
    supportRank J (capExponents p) ≤ supportRank J (capExponents q) := by
  have hsub : capExponents p ⊆ capExponents q := fun _ he =>
    ⟨he.1.trans (Nat.mul_le_mul_left _ h.1), he.2.1.trans (Nat.mul_le_mul_left _ h.2.1),
      he.2.2.trans (Nat.mul_le_mul_left _ h.2.2)⟩
  have : Module.Finite GeoField (restrictSupport GeoField (capExponents q)) :=
    Module.Finite.of_basis (basisRestrictSupport GeoField _)
  exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono GeoField hsub))
private theorem shape_bounds (p q : Shape) (hq : ChamberBox q) :
    ∃ C : ℕ, ∀ n, InBox (q.scale n) (p.plus (q.scale n)) ∧
      InBox (p.plus (q.scale n)) (q.scale (n + C)) := by
  let C := p.b + p.j + p.t
  have ⟨hb, hj, ht⟩ := hq
  have bound (a b : ℕ) (ha : a ≤ C) (hpos : 0 < b) (n : ℕ) :
      a + n * b ≤ (n + C) * b := by
    rw [Nat.add_mul, add_comm a]
    exact Nat.add_le_add_left (ha.trans (Nat.le_mul_of_pos_right _ hpos)) _
  refine ⟨C, fun n => ⟨⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _⟩,
    ⟨bound p.b q.b (by dsimp [C]; omega) (by omega) n,
     bound p.j q.j (by dsimp [C]; omega) (by omega) n,
     bound p.t q.t (by dsimp [C]; omega) ht n⟩⟩⟩
theorem ray_compare (shapes : ι → Shape) (J : Ideal GeoJets) (base : ι)
    (hs : ∀ i, ChamberBox (shapes i))
    (hfil : ∀ q : Shape, ChamberBox q → ∀ n,
      affineHilbertFunction
        (J.comap (monomialMap GeoField (capExponents q)).toRingHom) n =
      supportRank J (capExponents (q.scale n)))
    (P : MvPolynomial ι ℚ) (u : ι → ℕ)
    (hu : ∀ a ≥ u, MvPolynomial.eval (fun i => (a i : ℚ)) P =
      (supportRank J (capExponents (shapeSum shapes a)) : ℚ))
    (v : ι → ℕ) (hv : 0 < v base) (d : ℕ) (hd : dimension J ≤ d) :
    (ray P u v).natDegree ≤ dimension J ∧
    (ray P u v).coeff d = capCoeff J d (shapeSum shapes v) := by
  let q := shapeSum shapes v
  have hq : ChamberBox q := shapeSum_chamber shapes hs v base hv
  let I := J.comap (monomialMap GeoField (capExponents q)).toRingHom
  let Q := affineHilbertPolynomial I
  have hQ : Q.natDegree = dimension J :=
    natDegree_affineHilbertPolynomial_comap_of_surjective _ (cap_surjective q hq) J
  obtain ⟨C, hC⟩ := shape_bounds (shapeSum shapes u) q hq
  have hR (n : ℕ) : (ray P u v).eval (n : ℚ) =
      (supportRank J (capExponents ((shapeSum shapes u).plus (q.scale n))) : ℚ) := by
    rw [ray_eval]
    change MvPolynomial.eval (fun i => (((u + fun j => n * v j) i : ℕ) : ℚ)) P = _
    rw [hu (u + fun i => n * v i) (fun i => Nat.le_add_right _ _), shapeSum_add, shapeSum_scale]
  have hshift : Tendsto (fun n : ℕ => n + C) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n C) tendsto_id
  have hlo : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ (ray P u v).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with n hn
    rw [show Q.eval (n : ℚ) = (affineHilbertFunction I n : ℚ) from hn, hfil q hq n, hR]
    exact_mod_cast supportRank_le J (hC n).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (ray P u v).eval (n : ℚ) ≤ (Polynomial.taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [hshift.eventually (eventually_eval_affineHilbertPolynomial I)] with n hn
    rw [Polynomial.taylor_eval, ← Nat.cast_add, show Q.eval ((n + C : ℕ) : ℚ) =
      (affineHilbertFunction I (n + C) : ℚ) from hn, hfil q hq (n + C), hR]
    exact_mod_cast supportRank_le J (hC n).2
  have hT : (Polynomial.taylor (C : ℚ) Q).natDegree = dimension J :=
    (Polynomial.natDegree_taylor Q _).trans hQ
  have hdeg : (ray P u v).natDegree ≤ dimension J :=
    (Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Eventually.of_forall fun n => by rw [hR]; positivity) hhi).1.trans_eq hT
  have hl := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hQ.trans_le hd) (hdeg.trans hd) hlo
  have hh := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hdeg.trans hd) (hT.trans_le hd) hhi
  rw [Polynomial.coeff_taylor_of_natDegree_le _ (hQ.trans_le hd)] at hh
  exact ⟨hdeg, le_antisymm hh hl⟩
end
end K1_13_6_2_3_2_5
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
theorem eq_of_grid {p q : Form} {N : ℕ}
    (h : ∀ t : Grade, (∀ j, N ≤ t j) →
        eval (fun j => (t j : ℚ)) p = eval (fun j => (t j : ℚ)) q) : p = q := by
  let s : Fin 5 → Set ℚ := fun _ => Set.range fun n : ℕ => ((N + n : ℕ) : ℚ)
  refine MvPolynomial.funext_set s (fun _ => Set.infinite_range_of_injective ?_) ?_
  · intro a b hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)
  · intro x hx
    choose n hn using fun j => hx j (Set.mem_univ j)
    let t : Grade := Finsupp.equivFunOnFinite.symm fun j => N + n j
    have hx' : (fun j => (t j : ℚ)) = x := funext hn
    rw [← hx']
    exact h t (fun j => Nat.le_add_right N (n j))
theorem squarefree_apply (I : Finset (Fin 5)) (i : Fin 5) :
    squarefree I i = if i ∈ I then 1 else 0 := by
  classical
  simp [squarefree, unitGrade, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
theorem squarefree_degree (I : Finset (Fin 5)) : (squarefree I).degree = I.card := by
  classical
  simp [Finsupp.degree_eq_sum, squarefree_apply]
theorem squarefree_insert {I : Finset (Fin 5)} {i : Fin 5} (hi : i ∉ I) :
    squarefree (insert i I) = squarefree I + unitGrade i := by
  simp [squarefree, Finset.sum_insert hi, add_comm]
theorem line_eval (p : Form) (t : Grade) (N : ℕ) :
    (line t p).eval (N : ℚ) = eval (fun j => ((N • t) j : ℚ)) p := by
  let L := (Polynomial.evalRingHom (N : ℚ)).comp (line t)
  let R := eval (fun j => ((N • t) j : ℚ))
  have h : L = R := by
    ext j
    · simp [L, R, line]
    · simp [L, R, line, Finsupp.smul_apply, Nat.cast_mul, mul_comm]
  exact DFunLike.congr_fun h p
theorem line_of_diagonal_agreement (B : Boxes) (P : Ideal GeoJets5) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (t : Grade) (ht : ∀ j, 0 < t j)
    (hdiag : ∀ N, gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N) :
    line t p = affineHilbertPolynomial (diagonalIdeal B P t) := by
  obtain ⟨N₀, hN₀⟩ := hp
  refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := N₀) fun N hN => ?_
  rw [line_eval, hN₀ _ (fun j => hN.trans (Nat.le_mul_of_pos_right N (ht j)))]
  exact congrArg (fun n : ℕ => (n : ℚ)) (hdiag N)
theorem line_monomial (t a : Grade) (r : ℚ) :
    line t (monomial a r) =
      Polynomial.C (eval (fun j => (t j : ℚ)) (monomial a r)) * Polynomial.X ^ a.degree := by
  simp only [line, eval₂Hom_monomial, eval_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  rw [← mul_assoc, ← map_mul]
theorem line_coeff (p : Form) (t : Grade) (d : ℕ) :
    (line t p).coeff d = eval (fun j => (t j : ℚ)) (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [line_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases h : a.degree = d
    · subst d
      simp [homogeneousComponent_eq_self (isHomogeneous_monomial r rfl)]
    · simp [Ne.symm h, homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]
theorem totalDegree_le_of_lines {p : Form} {d : ℕ}
    (h : ∀ t : Grade, (∀ j, 0 < t j) → (line t p).natDegree ≤ d) :
    p.totalDegree ≤ d := by
  refine Finset.sup_le fun a ha => ?_
  by_contra! hda
  have hh : homogeneousComponent a.degree p = 0 := by
    refine eq_of_grid (N := 1) fun t ht => ?_
    rw [map_zero, ← line_coeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h t ht).trans_lt hda)
  have hcoeff := congrArg (fun q : Form => q.coeff a) hh
  simp [coeff_homogeneousComponent, Finsupp.degree_apply] at hcoeff
  exact (mem_support_iff.mp ha) hcoeff
theorem positiveDiagonal_apply (J : Finset (Fin 5)) (j : Fin 5) :
    positiveDiagonal J j = if j ∈ J then 2 else 1 := rfl
private theorem cube_prod (I : Finset (Fin 5)) (f : Fin 5 → ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) * ∏ j ∈ J, f j) =
      ∏ j ∈ I, (f j - 1) := by
  classical
  rw [Finset.prod_sub f (fun _ => (1 : ℚ))]
  refine Finset.sum_bij (fun J _ => I \ J) ?_ ?_ ?_ ?_
  · intro J hJ
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro J hJ K hK h
    simpa [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hK)] using
      congrArg (fun U => I \ U) h
  · intro J hJ
    exact ⟨I \ J, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ)⟩
  · intro J hJ
    simp [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ),
      Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
private theorem cube_monomial (I : Finset (Fin 5)) (a : Grade) (r : ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      eval (fun j => (positiveDiagonal J j : ℚ)) (monomial a r)) =
      r * ∏ j ∈ I, ((2 : ℚ) ^ a j - 1) := by
  rw [← cube_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [eval_monomial, Finsupp.prod_pow]
  have he (j : Fin 5) : ((positiveDiagonal J j : ℕ) : ℚ) ^ a j =
      if j ∈ J then (2 : ℚ) ^ a j else 1 := by
    by_cases h : j ∈ J <;> simp [positiveDiagonal_apply, h]
  simp_rw [he]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  ring
private theorem cube_monomial_top (I : Finset (Fin 5)) {a : Grade} (ha : a.degree = I.card)
    (r : ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      eval (fun j => (positiveDiagonal J j : ℚ)) (monomial a r)) =
      (monomial a r).coeff (squarefree I) := by
  classical
  rw [cube_monomial]
  by_cases h : squarefree I ≤ a
  · have he : squarefree I = a := by
      obtain ⟨b, hab⟩ := le_iff_exists_add.mp h
      have hd := congrArg Finsupp.degree hab
      rw [ha, map_add, squarefree_degree] at hd
      have hb : b.degree = 0 := by omega
      rw [hab, (Finsupp.degree_eq_zero_iff _).mp hb, add_zero]
    subst a
    rw [show (∏ j ∈ I, ((2 : ℚ) ^ squarefree I j - 1)) = 1 from
      Finset.prod_eq_one (fun j hj => by norm_num [squarefree_apply, hj])]
    simp
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hm : j ∈ I ∧ a j = 0 := by
      by_cases hi : j ∈ I <;> simp [squarefree_apply, hi] at hj ⊢
      exact hj
    rw [Finset.prod_eq_zero hm.1 (by simp [hm.2]), mul_zero, coeff_monomial]
    exact (ite_eq_right (fun he => h he.ge)).symm
theorem cube_extract (I : Finset (Fin 5)) (p : Form) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      (line (positiveDiagonal J) p).coeff I.card) = p.coeff (squarefree I) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    simp_rw [line_coeff, homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    by_cases h : I.card = a.degree
    · simpa only [ite_eq_left h] using cube_monomial_top I h.symm r
    · have hne : a ≠ squarefree I := fun h' => h (by rw [h', squarefree_degree])
      simp [h, coeff_monomial, Finsupp.single_apply, hne]
  | add p q hp hq =>
    simp [map_add, Polynomial.coeff_add, mul_add, Finset.sum_add_distrib, hp, hq]
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_2_3_2_6
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial
def rawCapMap {ι : Type} (shapes : ι → Shape) :
    MvPolynomial (CapVar shapes) GeoField →ₐ[GeoField] MvPolynomial ι GeoJets :=
  aeval fun v => monomial (Finsupp.single v.1 1) (monomial v.2.val 1)
theorem mem_capIdeal {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets)
    (f : MvPolynomial (CapVar shapes) GeoField) :
    f ∈ capIdeal shapes J ↔ ∀ e, (rawCapMap shapes f).coeff e ∈ J := by
  have hmap : capMap shapes J = (mapAlgHom (Ideal.Quotient.mkₐ GeoField J)).comp
      (rawCapMap shapes) := by
    apply algHom_ext
    intro v
    simp only [capMap, rawCapMap, AlgHom.comp_apply, aeval_X, mapAlgHom_apply, map_monomial]
    rfl
  change capMap shapes J f = 0 ↔ _
  rw [hmap, AlgHom.comp_apply, mapAlgHom_apply]
  constructor
  · intro h e
    have he := congrArg (fun q : MvPolynomial ι (GeoJets ⧸ J) => q.coeff e) h
    rw [coeff_map] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using he)
  · intro h
    ext e
    rw [coeff_map]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (h e)
theorem box_support {p : Shape} {D : GeoJets} (hD : Box4 p D) :
    ∀ e ∈ D.support, e ∈ capExponents p := by
  intro e he
  obtain ⟨hb, hj, ht⟩ := hD e he
  simp only [id_eq] at hb hj ht
  change e.degree ≤ 2 * p.b ∧ _ ∧ _
  rw [Finsupp.degree_eq_sum]
  exact ⟨by omega, by omega, by omega⟩
theorem box_sq_support {p : Shape} {D : GeoJets} (hD : Box4 p D) :
    ∀ e ∈ (D ^ 2).support, e ∈ capExponents p := by
  intro e he
  rw [MvPolynomial.mem_support_iff, pow_two, coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hu : D.coeff u ≠ 0 := fun h => hc (by simp [h])
  have hv : D.coeff v ≠ 0 := fun h => hc (by simp [h])
  obtain ⟨hub, huj, hut⟩ := hD u (MvPolynomial.mem_support_iff.mpr hu)
  obtain ⟨hvb, hvj, hvt⟩ := hD v (MvPolynomial.mem_support_iff.mpr hv)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
  rw [← huv]
  simp only [capExponents, Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.add_apply,
    mul_add, Finset.sum_add_distrib]
  simp only [id_eq] at hub huj hut hvb hvj hvt
  exact ⟨by omega, by omega, by omega⟩
theorem exists_lift {ι : Type} [DecidableEq ι] (shapes : ι → Shape) (i : ι)
    (D : GeoJets) (hD : ∀ e ∈ D.support, e ∈ capExponents (shapes i)) :
    ∃ L : MvPolynomial (CapVar shapes) GeoField,
      IsWeightedHomogeneous (step ∘ capSlot shapes) L (step i) ∧
      rawCapMap shapes L = monomial (Finsupp.single i 1) D := by
  classical
  let v (e : ↥D.support) : CapVar shapes := ⟨i, ⟨e, hD e e.2⟩⟩
  let L : MvPolynomial (CapVar shapes) GeoField :=
    ∑ e ∈ D.support.attach, D.coeff e • MvPolynomial.X (v e)
  refine ⟨L, ?_, ?_⟩
  · change L ∈ weightedHomogeneousSubmodule GeoField (step ∘ capSlot shapes) (step i)
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.smul_mem _ _ (isWeightedHomogeneous_X GeoField (step ∘ capSlot shapes) (v e))
  · simp only [L, map_sum, map_smul, rawCapMap, aeval_X, v, smul_monomial, smul_eq_mul, mul_one]
    rw [← map_sum (monomial (Finsupp.single i 1))]
    congr 1
    rw [Finset.sum_attach D.support (fun e => monomial e (D.coeff e))]
    exact D.as_sum.symm
theorem capIdeal_mono {ι : Type} (shapes : ι → Shape) {J K : Ideal GeoJets}
    (h : J ≤ K) : capIdeal shapes J ≤ capIdeal shapes K := by
  intro f hf
  exact (mem_capIdeal shapes K f).mpr fun e => h ((mem_capIdeal shapes J f).mp hf e)
theorem lift_mem {ι : Type} {shapes : ι → Shape} {i : ι} {D : GeoJets}
    {J : Ideal GeoJets} {L : MvPolynomial (CapVar shapes) GeoField}
    (hL : rawCapMap shapes L = monomial (Finsupp.single i 1) D)
    (hD : D ∈ J) : L ∈ capIdeal shapes J := by
  classical
  rw [mem_capIdeal, hL]
  intro e
  rw [coeff_monomial]
  split_ifs
  · exact hD
  · exact J.zero_mem
theorem lift_mul_mem_iff {ι : Type} {shapes : ι → Shape} {i : ι} {D : GeoJets}
    {J K : Ideal GeoJets} {L : MvPolynomial (CapVar shapes) GeoField}
    (hL : rawCapMap shapes L = monomial (Finsupp.single i 1) D)
    (hD : ∀ x, D * x ∈ J ↔ x ∈ K) (f : MvPolynomial (CapVar shapes) GeoField) :
    L * f ∈ capIdeal shapes J ↔ f ∈ capIdeal shapes K := by
  classical
  rw [mem_capIdeal, mem_capIdeal, map_mul, hL]
  constructor
  · intro h e
    apply (hD _).mp
    rw [← coeff_monomial_mul e (Finsupp.single i 1) D (rawCapMap shapes f)]
    exact h _
  · intro h e
    rw [coeff_monomial_mul']
    split_ifs
    · exact (hD _).mpr (h _)
    · exact J.zero_mem
private theorem mem_cut_iff (J : Ideal GeoJets) (D x : GeoJets) :
    x ∈ cut J D ↔ ∃ r : GeoJets ⧸ J, Ideal.Quotient.mk J x = Ideal.Quotient.mk J D * r := by
  rw [show cut J D = Ideal.span {D} ⊔ J from sup_comm _ _, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨r, b, hb, rfl⟩
    refine ⟨Ideal.Quotient.mk J r, ?_⟩
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_mul, mul_comm]
  · rintro ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨a, x - a * D, Ideal.Quotient.eq.mp ?_, by abel⟩
    rw [map_mul, mul_comm]
    exact hr
theorem square_mul_mem_iff (J : Ideal GeoJets) (D : GeoJets)
    (hD : IsLeftRegular (Ideal.Quotient.mk J D)) (x : GeoJets) :
    D ^ 2 * x ∈ J ↔ x ∈ J := by
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_mul, pow_two]
  exact (hD.mul hD).mul_left_eq_zero_iff
theorem cut_square_mul_mem_iff (J : Ideal GeoJets) (D : GeoJets)
    (hD : IsLeftRegular (Ideal.Quotient.mk J D)) (x : GeoJets) :
    D * x ∈ cut J (D ^ 2) ↔ x ∈ cut J D := by
  simp only [mem_cut_iff, map_mul, pow_two, mul_assoc]
  exact exists_congr fun _ => Function.Injective.eq_iff hD
end
end K1_13_6_2_3_2_6
end
section
namespace K1_13_6_2_4_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
theorem four_ne_zero : (4 : GeoField) ≠ 0 := by
  let e := (genericCoeffs.comp Polynomial.C).comp K1_13.embed
  let : CharP GeoField K1.p := charP_of_injective_ringHom e.injective K1.p
  intro hz
  have hd := (CharP.cast_eq_zero_iff GeoField K1.p 4).mp (by simpa using hz)
  exact (not_le_of_gt (show 4 < K1.p by decide)) (Nat.le_of_dvd (by decide) hd)
def substituteLast (x : GeoJets) : GeoJets5 →+* GeoJets :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.lastCases x MvPolynomial.X)
theorem substituteLast_old (x : GeoJets) :
    (substituteLast x).comp oldEmbedding = RingHom.id GeoJets := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [substituteLast, oldEmbedding]
  · intro i
    simp [substituteLast, oldEmbedding]
end
end K1_13_6_2_4_5
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (B : Boxes), (∀ i, Chamber (B i).1) → ∀ (t : Fin 5 → ℕ) (n : ℕ),
    n • diagonalExponents B t = latticePoints (scaleCap (sumCap B t) n)
def c2 : Prop :=
  ∀ p : Shape, Chamber p →
    ∃ H : Polynomial ℚ, H.natDegree ≤ 4 ∧
      H.coeff 4 = (volume32 p : ℚ) / 2 ∧
      ∀ n : ℕ, H.eval (n : ℚ) = (K1_13_6_2_3.capExponents (p.scale n)).ncard
theorem diagonal_coeff (h1 : c1) (h2 : c2)
    (B : Boxes) (hB : ∀ i, Chamber (B i).1) (t : Fin 5 → ℕ) :
    (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField (diagonalExponents B t))
      ⊥)).coeff 5 = volumeProduct (sumCap B t) := by
  let a := sumCap B t
  obtain ⟨H, hdeg, hcoeff, hH⟩ := h2 a.1 (sumCap_chamber B hB t)
  let F := H * (Polynomial.C (2 * (a.2 : ℚ)) * Polynomial.X + 1)
  have heq : F = affineHilbertPolynomial
      (Ideal.comap (monomialMap GeoField (diagonalExponents B t)) ⊥) := by
    apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := 0)
    intro n _
    rw [monomial_hilbert_count _ (zero_mem_diagonalExponents B t), h1 B hB t n,
      lattice_count]
    simp only [F, scaleCap, a, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, hH, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    ring
  rw [← heq]
  have h5 := Polynomial.coeff_eq_zero_of_natDegree_lt (p := H) (n := 5) (by omega)
  simp only [F, mul_add, mul_one, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C, h5, add_zero, hcoeff, volumeProduct, a]
  ring
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
theorem diagonal_degree_le (B : Boxes) (P : Ideal GeoJets5) (t : Grade) {d : ℕ}
    (hd : DimLE P d) : (affineHilbertPolynomial (diagonalIdeal B P t)).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let φ := Ideal.quotientMapₐ P f le_rfl
  exact (natDegree_affineHilbertPolynomial_le_of_injective φ Ideal.quotientMap_injective).trans
    (K1_13_6_2_4_2.hilbert_degree_le hd)
theorem gradedIdeal_degree_le (B : Boxes) (P : Ideal GeoJets5) {d : ℕ} (hd : DimLE P d)
    {p : Form} (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    p.totalDegree ≤ d := by
  apply totalDegree_le_of_lines
  intro t ht
  rw [line_of_diagonal_agreement B P hp t ht (hdiag t ht)]
  exact diagonal_degree_le B P t hd
theorem mixedDegree_eq (B : Boxes) (P : Ideal GeoJets5) (I : Finset (Fin 5)) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    mixedDegree B P I = p.coeff (squarefree I) / (2 : ℚ) ^ I.card := by
  unfold mixedDegree
  rw [← cube_extract I p]
  congr 1
  refine Finset.sum_congr rfl fun J _ => ?_
  have ht (j : Fin 5) : 0 < positiveDiagonal J j := by
    rw [positiveDiagonal_apply]
    split <;> decide
  have he := line_of_diagonal_agreement B P hp (positiveDiagonal J) ht
    (hdiag (positiveDiagonal J) ht)
  rw [he]
  rfl
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13
open scoped BigOperators
def multiOrder {n : ℕ} (a : Fin n →₀ ℕ) : ℕ :=
  a.sum (fun _ k => k)
def hassePartial {n : ℕ} {A : Type*} [CommSemiring A]
    (a : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) A) : MvPolynomial (Fin n) A :=
  ∑ m ∈ P.support, MvPolynomial.monomial (m - a) (P.coeff m * ∏ i : Fin n, ((m i).choose (a i) : A))
def VanishesTo {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (f : R) (d : ℕ) : Prop :=
  let L := Localization.AtPrime p
  algebraMap R L f ∈ IsLocalRing.maximalIdeal L ^ d
end
end K1_13_6_1_2
end

end Merged6967_Fast054

section Merged6967_Fast056
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
end K1_13_1_1
end
section
set_option Elab.async false
namespace K1_13_2_3_3
open K1_13_2 K1_13_2_3 Finset
open K1_13_2_3_1 (denPrefix denPrefix_of_nonpos)
open scoped BigOperators
private def offsets (s : ℕ) : ℕ := 4650 - s
private def flag (n j : ℤ) : Flag := ⟨1650,1650 - j, 1650,550, n - j⟩
private def active (j : ℤ) : ℤ := denominator 1650 - denominator (1649 - j)
private def removed (n : ℤ) : ℤ := (n - 1) / 4 + 1
private def target (n j : ℤ) : ℤ :=
  smallCount 1650 (n - 1 - j) - denominator ((n - 3 * removed n) - 1 - j) -
    denominator ((removed n - 1) - 1 - j) -
    denominator ((removed n - 2) - 1 - j) -
    denominator ((removed n - 3) - 1 - j)
private theorem cumulative_denominator (d u : ℤ) (hd : 2 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u :=
  (cumulative_eq_small d u hd (by omega)).trans (smallCount_eq_denominator d u hu)
private theorem initial_eq (s : Fin 4013) (j : Fin 4650) (hs : 2510 ≤ s.val) :
    initialFlag (s, j) = flag (offsets s.val) j.val := by
  have hn : (offsets s.val : ℤ) = 4650 - (s.val : ℤ) := by unfold offsets; omega
  change K1_13_2.Flag.mk (min (s.val : ℤ) 1650) (-((j.val : ℤ) - 1650)) 1650 550
    (3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650)) = _
  rw [min_eq_right (show (1650 : ℤ) ≤ s.val by omega), flag, hn]
  congr 1 <;> ring
private theorem old_eq (n j : ℤ) (hj : 0 ≤ j) : oldCount (flag n j) = active j := by
  have hcap (u : ℤ) (hu : u ≤ 1650) : cappedCount 1650 u 550 = denominator u := by
    change cumulative 1650 u - cumulative 1099 (u - 1653) = denominator u
    rw [cumulative_denominator 1650 u (by decide) hu]
    simp [cumulative, show u - 1653 < 0 by omega]
  change cappedCount 1650 1650 550 - cappedCount 1650 (min 1650 (1650 - j - 1)) 550 = _
  rw [min_eq_right (by omega), hcap 1650 (by decide), hcap (1650 - j - 1) (by omega), active,
    show 1650 - j - 1 = 1649 - j by ring]
private theorem target_original (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140) :
    targetCount (flag n j) =
      cumulative 1650 (n - 1 - j) -
      cumulative (1650 - removed n) ((n - 3 * removed n) - 1 - j) -
      cumulative 1650 (1649 - j) + cumulative (1650 - removed n) (1649 - j) := by
  unfold targetCount flag
  dsimp only
  rw [show n - j - 1 - (1650 - j) + 1650 = n - 1 by ring,
    ite_eq_right (by omega), min_eq_right (by omega), ← removed]
  rw [show n - j - 1 = n - 1 - j by ring,
    show n - 1 - j - 3 * removed n = (n - 3 * removed n) - 1 - j by ring,
    show 1650 - j - 1 = 1649 - j by ring]
private theorem target_eq (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140) (hj : 0 ≤ j) :
    targetCount (flag n j) = target n j := by
  have hr : 160 ≤ removed n ∧ removed n ≤ 535 := by unfold removed; omega
  have hd : 2 ≤ 1650 - removed n := by omega
  rw [target_original n j hn₁ hn₂, cumulative_eq_small 1650 (n - 1 - j) (by decide) (by omega),
    cumulative_denominator (1650 - removed n) _ hd (by unfold removed; omega),
    cumulative_denominator 1650 (1649 - j) (by decide) (by omega),
    cumulative_eq_small (1650 - removed n) (1649 - j) hd (by omega)]
  have hres :
      smallCount (1650 - removed n) (1649 - j) =
        denominator (1649 - j) - denominator ((removed n - 1) - 1 - j) -
          denominator ((removed n - 2) - 1 - j) - denominator ((removed n - 3) - 1 - j) := by
    unfold smallCount
    rw [show 1649 - j - (1650 - removed n) - 1 = (removed n - 1) - 1 - j by ring,
      show 1649 - j - (1650 - removed n) - 2 = (removed n - 2) - 1 - j by ring,
      show 1649 - j - (1650 - removed n) - 3 = (removed n - 3) - 1 - j by ring]
  rw [hres, target]
  ring
private theorem active_nonneg (j : ℤ) (hj : 0 ≤ j) : 0 ≤ active j :=
  sub_nonneg.mpr (denominator_mono_to _ _ (by omega) (by decide))
private theorem target_nonneg (n j : ℤ) (hn₁ : 638 ≤ n) (hn₂ : n ≤ 2140)
    (hj : 0 ≤ j) (hjn : j < n) : 0 ≤ target n j := by
  by_cases hn : n ≤ 1650
  ·
    let u := n - 1 - j
    let t := removed n - 1 - j
    have htu : t + 478 ≤ u := by dsimp [t, u, removed]; omega
    have htmax : t ≤ 412 := by dsimp [t, removed]; omega
    have hu₁ : 0 ≤ u := by dsimp [u]; omega
    have hu₂ : u ≤ 1650 := by dsimp [u]; omega
    have ht (v : ℤ) (hv : v ≤ t) : denominator v ≤ denominator t :=
      denominator_mono_to _ _ hv (by omega)
    have hbig : 4 * denominator t ≤ denominator u := by
      by_cases h : 0 ≤ t
      · exact (denominator_quadruple t h).trans (denominator_mono_to _ _ (by omega) hu₂)
      · rw [denominator_of_neg t (by omega), mul_zero, ← denominator_of_neg (-1) (by decide)]
        exact denominator_mono_to _ _ (by omega) hu₂
    have h₁ := ht ((n - 3 * removed n) - 1 - j) (by dsimp [t, removed]; omega)
    have h₂ := ht ((removed n - 1) - 1 - j) (by dsimp [t]; omega)
    have h₃ := ht ((removed n - 2) - 1 - j) (by dsimp [t]; omega)
    have h₄ := ht ((removed n - 3) - 1 - j) (by dsimp [t]; omega)
    unfold target
    rw [smallCount_eq_denominator 1650 u hu₂]
    omega
  · rw [← target_eq n j hn₁ hn₂ hj, target_original n j hn₁ hn₂]
    have h₁ : cumulative 1650 (1649 - j) ≤ cumulative 1650 (n - 1 - j) :=
      K1_13_2_3.cumulative_mono 1650 (by omega)
    have hd : 0 ≤ 1650 - removed n := by unfold removed; omega
    have hm : Monotone (cumulative (1650 - removed n)) := by
      simpa only [Int.toNat_of_nonneg hd] using
        K1_13_2_3.cumulative_mono (1650 - removed n).toNat
    have h₂ := hm (show (n - 3 * removed n) - 1 - j ≤ 1649 - j by unfold removed; omega)
    omega
private def packedCuts : List ℕ :=
  [1884877150839,1492194651746,942438537804,1570711722551,1492155854371,
   1560874277390,922171043323,780298540519,1471922525652,778910935489,
   778910390703,1488933185949,1466373428620,1471742129531,1466015503722,
   1282763565401,1466015503690,1454562252090,1463151842603,727278331164,
   709921952013,1276991850751,640642880754,638428270820,1414291165399,
   1259115981003,314223174847,1256585316531,1256584717480,314146179229,
   1256582320274,311689515144,1246690353278,1177429774453,293274685548,
   146601559140,292630437979,1170521474132,1170450030668,141872603205,
   69827855423,70901579832,558482097203,279206961197,554118418472,
   69260558371,34495008799]
private def lowOnes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, bits => bits % 2 + lowOnes k (bits / 2)
private def cut (n : ℕ) : ℕ :=
  let k := 2140 - n
  let code := (packedCuts[k / 32]?).getD 0
  min n (code % 1024 - lowOnes (k % 32) (code / 1024))
private def upper (n j : ℕ) : ℤ :=
  if j < cut n then active j else if j < n then target n j else 0
private theorem cast_toNat_le {x y : ℤ} (hy : 0 ≤ y) (hxy : x ≤ y) :
    (x.toNat : ℤ) ≤ y := by omega
private theorem block_le_upper (s : Fin 4013) (j : Fin 4650) (hs : 2510 ≤ s.val) :
    (baseline (s, j) : ℤ) ≤ upper (offsets s.val) j.val := by
  let n := offsets s.val
  have hn₁ : 638 ≤ n := by dsimp [n, offsets]; omega
  have hn₂ : n ≤ 2140 := by dsimp [n, offsets]; omega
  have hc : cut n ≤ n := min_le_left _ _
  have hf : initialFlag (s, j) = flag n j.val := initial_eq s j hs
  change (baseline (s, j) : ℤ) ≤ upper n j.val
  by_cases hj : j.val < n
  · have horder : ¬ (flag n j.val).order ≤ 0 := by change ¬ (n : ℤ) - j.val ≤ 0; omega
    have hactive :
        { flag n j.val with upper := min (flag n j.val).upper (2999 - offset (s,j)) } =
          flag n j.val := by
      have hu : (1650 : ℤ) ≤ 2999 - offset (s,j) := by unfold offset; dsimp; omega
      simp only [flag, min_eq_left hu]
    rw [baseline, blockBound, hf]
    dsimp only
    rw [ite_eq_right horder, hactive]
    by_cases hcut : j.val < cut n
    · rw [upper, ite_eq_left hcut, ← old_eq n j.val (by omega)]
      apply cast_toNat_le
      · rw [old_eq n j.val (by omega)]
        exact active_nonneg _ (by omega)
      · exact min_le_left _ _
    · rw [upper, ite_eq_right hcut, ite_eq_left hj]
      apply cast_toNat_le (target_nonneg n j.val (by omega) (by omega) (by omega) (by omega))
      apply (min_le_right _ _).trans
      rw [← target_eq n j.val (by omega) (by omega) (by omega)]
      have hk : kernelLower (flag n j.val) =
          oldCount (flag n j.val) - targetCount (flag n j.val) := by simp [kernelLower, flag]
      have hm := (le_max_left (kernelLower (flag n j.val))
        (kernelLower (residualFlag (flag n j.val) (fun _ => 0)))).trans (le_max_right 0 _)
      rw [hk] at hm
      omega
  · have horder : (initialFlag (s,j)).order ≤ 0 := by rw [hf]; change (n : ℤ) - j.val ≤ 0; omega
    have hcut : ¬ j.val < cut n := by omega
    simp [baseline, blockBound, horder, upper, hcut, hj]
private def activePrefix (j : ℤ) : ℤ :=
  j * (24 * denominator 1650) - denPrefix 1650 + denPrefix (1650 - j)
private def targetTail (n j : ℤ) : ℤ :=
  smallPrefix 1650 (n - j) - denPrefix ((n - 3 * removed n) - j) -
    denPrefix ((removed n - 1) - j) -
    denPrefix ((removed n - 2) - j) -
    denPrefix ((removed n - 3) - j)
private theorem activePrefix_step (j : ℤ) : activePrefix (j + 1) - activePrefix j = 24 * active j := by
  unfold activePrefix active
  linear_combination (norm := ring_nf) -prefix_offset_step 1650 j
private theorem targetTail_step (n j : ℤ) :
    targetTail n j - targetTail n (j + 1) = 24 * target n j := by
  unfold targetTail target
  linear_combination (norm := ring_nf) smallPrefix_offset_step 1650 n j -
    prefix_offset_step (n - 3 * removed n) j - prefix_offset_step (removed n - 1) j -
    prefix_offset_step (removed n - 2) j - prefix_offset_step (removed n - 3) j
private theorem targetTail_end (n : ℕ) : targetTail n n = 0 := by
  simp only [targetTail, sub_self, smallPrefix_of_nonpos 1650 0 (by decide) (by decide),
    denPrefix_of_nonpos ((n : ℤ) - 3 * removed n - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 1 - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 2 - n) (by unfold removed; omega),
    denPrefix_of_nonpos (removed n - 3 - n) (by unfold removed; omega)]
private def rowBudget (n : ℕ) : ℤ := activePrefix (cut n) + targetTail n (cut n)
private theorem scaled_sum (f p : ℤ → ℤ) (h : ∀ j, p (j + 1) - p j = 24 * f j)
    (a : ℤ) (n : ℕ) : 24 * (∑ j ∈ range n, f (a + j)) = p (a + n) - p a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ, ← h, ← add_assoc]
    ring
private theorem sum_upper (n : ℕ) (hn : n ≤ 4650) :
    24 * (∑ j ∈ range 4650, upper n j) = rowBudget n := by
  let c := cut n
  have hc : c ≤ n := min_le_left _ _
  have htrunc : (∑ j ∈ range 4650, upper n j) = ∑ j ∈ range n, upper n j := by
    symm
    apply sum_subset (range_mono hn)
    intro j _ h
    rw [mem_range] at h
    have hcut : ¬ j < cut n := by change ¬ j < c; omega
    simp [upper, h, hcut]
  have hsplit (f : ℕ → ℤ) : (∑ j ∈ range n, f j) =
      (∑ j ∈ range c, f j) + ∑ j ∈ range (n - c), f (c + j) := by
    conv_lhs => rw [← Nat.add_sub_of_le hc, sum_range_add]
  rw [htrunc, hsplit, mul_add]
  have hactive : (∑ j ∈ range c, upper n j) = ∑ j ∈ range c, active j := by
    exact sum_congr rfl fun j hj => by rw [upper, ite_eq_left (mem_range.mp hj)]
  have htarget : (∑ j ∈ range (n - c), upper n (c + j)) =
      ∑ j ∈ range (n - c), target n ((c : ℤ) + j) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [upper, ite_eq_right (show ¬ c + j < cut n by change ¬ c + j < c; omega),
      ite_eq_left (by omega), Nat.cast_add]
  have h₁ := scaled_sum active activePrefix activePrefix_step 0 c
  have hzero : activePrefix 0 = 0 := by simp [activePrefix]
  simp only [zero_add, hzero, sub_zero] at h₁
  have h₂ := scaled_sum (target n) (fun j => -targetTail n j)
    (fun j => by linear_combination targetTail_step n j) c (n - c)
  have hend : (c : ℤ) + (↑(n - c) : ℤ) = n := by omega
  simp only [hend, targetTail_end, neg_zero, zero_sub, neg_neg] at h₂
  rw [hactive, htarget, h₁, h₂]
  rfl
private theorem grade_bound (s : Fin 4013) (hs : 2510 ≤ s.val) :
    24 * (∑ j : Fin 4650, (baseline (s,j) : ℤ)) ≤ rowBudget (offsets s.val) := by
  have h := mul_le_mul_of_nonneg_left
    (sum_le_sum (s := (univ : Finset (Fin 4650))) (fun j _ => block_le_upper s j hs))
    (show (0 : ℤ) ≤ 24 by decide)
  rw [Fin.sum_univ_eq_sum_range (upper (offsets s.val)), sum_upper _ (by unfold offsets; omega)] at h
  exact h
private def total (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => total start k + rowBudget (2140 - (start + k))
private theorem total_eq (n : ℕ) : total 0 n = ∑ k ∈ range n, rowBudget (2140 - k) := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, sum_range_succ, ih, zero_add]
private theorem total_add (start a b : ℕ) :
    total start (a + b) = total start a + total (start + a) b := by
  induction b with
  | zero => simp [total]
  | succ b ih =>
    rw [Nat.add_succ, total, ih, total]
    simp only [add_assoc]
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem check₀ : total 0 256 = 366834691880448 := by decide +kernel
private theorem check₁ : total 256 256 = 0xdc3ec39aa670 := by decide +kernel
private theorem check₂ : total 512 256 = 0x849854bf9218 := by decide +kernel
private theorem check₃ : total 768 256 = 77485223947464 := by decide +kernel
private theorem check₄ : total 1024 256 = 34445829248736 := by decide +kernel
private theorem check₅ : total 1280 223 = 0x9dd6637e808 := by decide +kernel
end
private theorem total_check : total 0 1503 = 877564171950648 := by
  calc
    _ = total 0 256 + total 256 256 + total 512 256 +
        total 768 256 + total 1024 256 + total 1280 223 := by
      rw [← total_add 0 256 256, ← total_add 0 512 256, ← total_add 0 768 256,
        ← total_add 0 1024 256, ← total_add 0 1280 223]
    _ = _ := by
      rw [check₀, check₁, check₂, check₃, check₄, check₅]
      decide
private theorem sum_grades :
    (∑ s : Fin 4013, if 2510 ≤ s.val then rowBudget (offsets s.val) else 0) = total 0 1503 := by
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => if 2510 ≤ s then rowBudget (offsets s) else 0),
    show (4013 : ℕ) = 2510 + 1503 by decide, sum_range_add, total_eq]
  have hzero : (∑ s ∈ range 2510, if 2510 ≤ s then rowBudget (offsets s) else 0) = 0 := by
    apply sum_eq_zero
    intro s hs
    rw [ite_eq_right (not_le.mpr (mem_range.mp hs))]
  rw [hzero, zero_add]
  apply sum_congr rfl
  intro k _
  rw [ite_eq_left (by omega), show offsets (2510 + k) = 2140 - k by unfold offsets; omega]
theorem proof : K1_13_2_3.c3 := by
  have h : 24 * (baselineSum 2510 4013 : ℤ) ≤ 877564171950648 := by
    unfold baselineSum baselineSumOn
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Nat.cast_sum]
    rw [mul_sum, ← total_check, ← sum_grades]
    apply sum_le_sum
    intro s _
    by_cases hs : 2510 ≤ s.val
    · simpa only [hs, s.isLt, and_self, ite_true] using grade_bound s hs
    · simp [hs]
  unfold K1_13_2_3.c3
  omega
end K1_13_2_3_3
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Generator (a h : Shape) := latticeIndices a ⊕ latticeIndices h
abbrev BigradedPolynomial (a h : Shape) := MvPolynomial (Generator a h) (Coeff a h)
def weight {α β : Type} : α ⊕ β → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))
abbrev grade {k α β : Type} [CommSemiring k] (d : ℕ × ℕ) :
    Submodule k (MvPolynomial (α ⊕ β) k) :=
  weightedHomogeneousSubmodule k weight d
def generatorExponent {a h : Shape} : Generator a h → Fin 4 →₀ ℕ :=
  Sum.elim Subtype.val Subtype.val
def dehom (surface : Ideal GeoJets) (a h : Shape) :
    BigradedPolynomial a h →ₐ[Coeff a h] SurfaceRing surface a h :=
  (Ideal.Quotient.mkₐ _ _).comp (aeval fun v => monomial (generatorExponent v) 1)
def relations (surface : Ideal GeoJets) (a h : Shape) : Ideal (BigradedPolynomial a h) :=
  ((RingHom.ker (dehom surface a h).toRingHom).homogeneousCore grade).toIdeal
def boxExponent {p : Shape} (m : SectionIndex p) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (m i).val)
theorem boxExponent_mem (p : Shape) (m : boxMonomials (p.scale 6)) :
    boxExponent m.val ∈ latticeIndices p := by
  change (fun i => boxExponent m.val i) ∈ exponents (p.scale 6)
  simpa only [boxExponent, Finsupp.coe_equivFunOnFinite_symm] using
    (mem_exponents_iff _ m.val).2 m.property
def leftForm (a h : Shape) : BigradedPolynomial a h :=
  ∑ m ∈ (boxMonomials (a.scale 6)).attach,
    C (algebraMap
        (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
        (MvPolynomial.X (Sum.inl m.val))) *
      MvPolynomial.X (Sum.inl ⟨boxExponent m.val, boxExponent_mem a m⟩)
def rightForm (a h : Shape) : BigradedPolynomial a h :=
  ∑ m ∈ (boxMonomials (h.scale 6)).attach,
    C (algebraMap
        (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
        (MvPolynomial.X (Sum.inr m.val))) *
      MvPolynomial.X (Sum.inr ⟨boxExponent m.val, boxExponent_mem h m⟩)
def firstCut (surface : Ideal GeoJets) (a h : Shape) : Ideal (BigradedPolynomial a h) :=
  relations surface a h ⊔ Ideal.span {leftForm a h}
def chart {k α β : Type} [CommSemiring k] (x : α) (y : β) :
    MvPolynomial (α ⊕ β) k :=
  MvPolynomial.X (Sum.inl x) * MvPolynomial.X (Sum.inr y)
end
end K1_13_6_1_4_2_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1 K1_13_6_1_4_2_1_2 MvPolynomial
abbrev Base (surface : Ideal GeoJets) := GeoJets ⧸ surface
abbrev FunctionField (surface : Ideal GeoJets) := FractionRing (Base surface)
def monomialAt (surface : Ideal GeoJets) (x : Fin 4 →₀ ℕ) : Base surface :=
  Ideal.Quotient.mk surface (monomial x 1)
def monomialFraction (surface : Ideal GeoJets) (x : Fin 4 →₀ ℕ) : FunctionField surface :=
  algebraMap (Base surface) (FunctionField surface) (monomialAt surface x)
def chartValue (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Generator a h → FunctionField surface :=
  Sum.elim (fun x => monomialFraction surface x.val / monomialFraction surface e.1.val)
    (fun y => monomialFraction surface y.val / monomialFraction surface e.2.val)
def chartAlgebra (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Subalgebra GeoField (FunctionField surface) :=
  Algebra.adjoin GeoField (Set.range (chartValue surface a h e))
instance (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : Algebra.FiniteType GeoField (chartAlgebra surface a h e) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
def chartCoord (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h) (i : Generator a h) : chartAlgebra surface a h e :=
  ⟨chartValue surface a h e i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
def zeroCoord (p : Shape) : latticeIndices p := ⟨0, latticeIndices_zero p⟩
def sectionCoord (p : Shape) (m : boxMonomials (p.scale 6)) : latticeIndices p :=
  ⟨boxExponent m.val, boxExponent_mem p m⟩
def ratioValue {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra k E] (φ : rees I a h →ₐ[k] E) :
    Generator a h → E :=
  Sum.elim
    (fun x => φ (leftGen I a h x) /
      φ (leftGen I a h e.1))
    (fun y => φ (rightGen I a h y) /
      φ (rightGen I a h e.2))
end
end K1_13_6_1_4_2_1_2_2
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem leftForm_grade (a h : Shape) : leftForm a h ∈ grade (1, 0) := by
  apply Submodule.sum_mem
  intro m _
  exact (isWeightedHomogeneous_X (Coeff a h) weight
    (Sum.inl ⟨boxExponent m.val, boxExponent_mem a m⟩ : Generator a h)).C_mul _
theorem rightForm_grade (a h : Shape) : rightForm a h ∈ grade (0, 1) := by
  apply Submodule.sum_mem
  intro m _
  exact (isWeightedHomogeneous_X (Coeff a h) weight
    (Sum.inr ⟨boxExponent m.val, boxExponent_mem h m⟩ : Generator a h)).C_mul _
private theorem box_monomial {k : Type} [CommRing k] {p : Shape} (m : SectionIndex p) :
    (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) k) ^ (m i).val) =
      monomial (boxExponent m) 1 := by
  have he : Finsupp.indicator Finset.univ (fun i _ => (m i).val) = boxExponent m := by
    ext i
    simp [Finsupp.indicator_apply, boxExponent]
  rw [prod_X_pow, he]
theorem dehom_left (surface : Ideal GeoJets) (a h : Shape) :
    dehom surface a h (leftForm a h) =
      Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h) := by
  unfold leftForm leftSection sectionWith dehom
  simp only [AlgHom.comp_apply, map_sum, map_mul, aeval_C, aeval_X,
    generatorExponent, Sum.elim_inl, MvPolynomial.algebraMap_eq, box_monomial, Ideal.Quotient.mkₐ_eq_mk]
  exact Finset.sum_attach (boxMonomials (a.scale 6)) fun m =>
    Ideal.Quotient.mk (extendIdeal surface a h) (C (algebraMap
      (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
      (MvPolynomial.X (Sum.inl m)))) *
    Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m) 1)
theorem dehom_right (surface : Ideal GeoJets) (a h : Shape) :
    dehom surface a h (rightForm a h) =
      Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h) := by
  unfold rightForm rightSection sectionWith dehom
  simp only [AlgHom.comp_apply, map_sum, map_mul, aeval_C, aeval_X,
    generatorExponent, Sum.elim_inr, MvPolynomial.algebraMap_eq, box_monomial, Ideal.Quotient.mkₐ_eq_mk]
  exact Finset.sum_attach (boxMonomials (h.scale 6)) fun m =>
    Ideal.Quotient.mk (extendIdeal surface a h) (C (algebraMap
      (MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField) (Coeff a h)
      (MvPolynomial.X (Sum.inr m)))) *
    Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m) 1)
theorem relations_homogeneous (surface : Ideal GeoJets) (a h : Shape) :
    (relations surface a h).IsHomogeneous grade :=
  ((RingHom.ker (dehom surface a h).toRingHom).homogeneousCore grade).isHomogeneous
theorem dehom_eq_zero_of_mem_relations {surface : Ideal GeoJets} {a h : Shape}
    {f : BigradedPolynomial a h} (hf : f ∈ relations surface a h) :
    dehom surface a h f = 0 :=
  Ideal.toIdeal_homogeneousCore_le grade _ hf
theorem mem_relations_of_dehom_eq_zero {surface : Ideal GeoJets} {a h : Shape}
    {d : ℕ × ℕ} {f : BigradedPolynomial a h} (hm : f ∈ grade d)
    (hf : dehom surface a h f = 0) : f ∈ relations surface a h :=
  Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hm⟩ hf
private def boxAt (a h : Shape) (d : ℕ × ℕ) : Shape :=
  (a.scale d.1).plus (h.scale d.2)
private theorem boxAt_add (a h : Shape) (s t : ℕ × ℕ) :
    boxAt a h (s + t) = (boxAt a h s).plus (boxAt a h t) := by
  cases a
  cases h
  simp [boxAt, Shape.scale, Shape.plus, Nat.add_mul, add_assoc, add_left_comm]
private theorem boxAt_chamber {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d : ℕ × ℕ) : Chamber (boxAt a h d) :=
  chamber_plus (K1_13_6_1_4_2.chamber_scale ha d.1) (K1_13_6_1_4_2.chamber_scale hh d.2)
private theorem boxAt_zero (a h : Shape) :
    latticeIndices (boxAt a h 0) = {0} := by
  have hz : boxAt a h 0 = ⟨0, 0, 0⟩ := by simp [boxAt, Shape.scale, Shape.plus]
  rw [hz]
  ext e
  change (fun i => e i) ∈ exponents ⟨0, 0, 0⟩ ↔ e ∈ ({0} : Set (Fin 4 →₀ ℕ))
  rw [exponents_zero, Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro he
    ext i
    exact congrFun he i
  · rintro rfl
    rfl
private theorem boxAt_left (a h : Shape) : boxAt a h (1, 0) = a := by
  cases a
  simp [boxAt, Shape.plus, Shape.scale]
private theorem boxAt_right (a h : Shape) : boxAt a h (0, 1) = h := by
  cases h
  simp [boxAt, Shape.plus, Shape.scale]
private theorem exponent_mem_box {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d : Generator a h →₀ ℕ) :
    Finsupp.weight generatorExponent d ∈ latticeIndices (boxAt a h (Finsupp.weight weight d)) := by
  have hplus (u v : ℕ × ℕ) : latticeIndices (boxAt a h (u + v)) =
      latticeIndices (boxAt a h u) + latticeIndices (boxAt a h v) := by
    rw [boxAt_add, latticeIndices_plus (boxAt_chamber ha hh _) (boxAt_chamber ha hh _)]
  have hgen (v : Generator a h) : generatorExponent v ∈ latticeIndices (boxAt a h (weight v)) := by
    cases v with
    | inl x => exact (boxAt_left a h).symm ▸ x.property
    | inr y => exact (boxAt_right a h).symm ▸ y.property
  induction d using Finsupp.induction_linear with
  | zero => simp [boxAt_zero]
  | add u v hu hv => simpa only [map_add, hplus] using Set.add_mem_add hu hv
  | single v n =>
    rw [Finsupp.weight_single, Finsupp.weight_single]
    induction n with
    | zero => simp [boxAt_zero]
    | succ n ih => simpa only [succ_nsmul, hplus] using Set.add_mem_add ih (hgen v)
set_option maxHeartbeats 800000 in
private theorem exponent_lift {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (i j : ℕ) {e : Fin 4 →₀ ℕ} (he : e ∈ latticeIndices (boxAt a h (i, j))) :
    ∃ d : Generator a h →₀ ℕ,
      Finsupp.weight weight d = (i, j) ∧ Finsupp.weight generatorExponent d = e := by
  have hplus (u v : ℕ × ℕ) : latticeIndices (boxAt a h (u + v)) =
      latticeIndices (boxAt a h u) + latticeIndices (boxAt a h v) := by
    rw [boxAt_add, latticeIndices_plus (boxAt_chamber ha hh _) (boxAt_chamber ha hh _)]
  induction i generalizing j e with
  | zero =>
    induction j generalizing e with
    | zero =>
      have he' : e = 0 := Set.mem_singleton_iff.mp ((boxAt_zero a h) ▸ he)
      exact ⟨0, rfl, by simp [he']⟩
    | succ j ih =>
      have hm : e ∈ latticeIndices (boxAt a h (0, j)) + latticeIndices h := by
        have hsum := hplus (0, j) (0, 1)
        rw [boxAt_right] at hsum
        rw [← hsum]
        exact he
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      obtain ⟨d, hd, hdu⟩ := ih (e := u) hu
      refine ⟨d + Finsupp.single (Sum.inr ⟨v, hv⟩) 1, ?_, ?_⟩
      · (rw [map_add, hd, Finsupp.weight_single]; rfl)
      · (rw [map_add, hdu, Finsupp.weight_single, one_nsmul]; rfl)
  | succ i ih =>
    have hm : e ∈ latticeIndices (boxAt a h (i, j)) + latticeIndices a := by
      have hsum := hplus (i, j) (1, 0)
      rw [boxAt_left] at hsum
      rw [← hsum]
      exact he
    obtain ⟨u, hu, v, hv, rfl⟩ := hm
    obtain ⟨d, hd, hdu⟩ := ih j (e := u) hu
    refine ⟨d + Finsupp.single (Sum.inl ⟨v, hv⟩) 1, ?_, ?_⟩
    · (rw [map_add, hd, Finsupp.weight_single]; rfl)
    · (rw [map_add, hdu, Finsupp.weight_single, one_nsmul]; rfl)
private theorem dehom_monomial (surface : Ideal GeoJets) (a h : Shape)
    (d : Generator a h →₀ ℕ) (c : Coeff a h) :
    dehom surface a h (monomial d c) =
      Ideal.Quotient.mk (extendIdeal surface a h) (monomial (Finsupp.weight generatorExponent d) c) := by
  unfold dehom
  rw [AlgHom.comp_apply, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, MvPolynomial.algebraMap_eq,
    C_mul_monomial, mul_one]
  rfl
theorem dehom_grade (surface : Ideal GeoJets) {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (i j : ℕ) : (grade (i, j)).map (dehom surface a h).toLinearMap = biPiece surface a h i j := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    change dehom surface a h f ∈ biPiece surface a h i j
    rw [f.as_sum, map_sum]
    apply Submodule.sum_mem
    intro d hd
    have hweight : Finsupp.weight weight d = (i, j) := hf (mem_support_iff.mp hd)
    have hexp := exponent_mem_box ha hh d
    rw [hweight] at hexp
    rw [dehom_monomial]
    refine ⟨_, ?_, rfl⟩
    intro e he
    have he' : Finsupp.weight generatorExponent d = e := by
      change e ∈ (monomial (Finsupp.weight generatorExponent d) (f.coeff d)).support at he
      have hne := mem_support_iff.mp he
      rw [coeff_monomial] at hne
      split at hne
      next hEq => exact hEq
      next => exact (hne rfl).elim
    exact he' ▸ hexp
  · unfold biPiece piece
    rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨d, hd, hde⟩ := exponent_lift ha hh i j he
    refine ⟨monomial d 1, isWeightedHomogeneous_monomial _ _ _ hd, ?_⟩
    change dehom surface a h (monomial d 1) = _
    rw [dehom_monomial, hde]
    rfl
end
end K1_13_6_1_4_2_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1 K1_13_6_1_4_2_1_2 MvPolynomial
abbrev LeftLabels (a : Shape) := (boxMonomials (a.scale 6) : Type)
abbrev RightLabels (h : Shape) := (boxMonomials (h.scale 6) : Type)
abbrev Parameters (a h : Shape) := PairSectionIndex (a.scale 6) (h.scale 6)
def parameter (a h : Shape) (i : Parameters a h) : Coeff a h :=
  algebraMap (MvPolynomial (Parameters a h) GeoField) (Coeff a h) (MvPolynomial.X i)
theorem sectionCoord_surjective (p : Shape) : Function.Surjective (sectionCoord p) := by
  intro x
  have hx : (fun i => x.val i) ∈ exponents (p.scale 6) := x.property
  rw [exponents_eq_image] at hx
  obtain ⟨m, hm, he⟩ := hx
  refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
  ext i
  exact congrFun he i
private theorem homogeneous_sum {k ι : Type} [Field k] {I : Ideal (MvPolynomial (Fin 4) k)}
    {a h : Shape} (d : ℕ × ℕ) (s : Finset ι) (w : ι → k) (x : ι → Affine I)
    (hx : ∀ i, x i ∈ box I a h d) (y : Affine I) (hy : y ∈ box I a h d)
    (heq : y = ∑ i ∈ s, w i • x i) :
    homogeneous d y hy = ∑ i ∈ s, w i • homogeneous d (x i) (hx i) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single d y = (rees I a h).val _
  rw [map_sum]
  simp_rw [map_smul, val_homogeneous, ← AddMonoidAlgebra.lsingle_apply (R := k),
    ← map_smul, ← map_sum, ← heq]
theorem leftHom_sum (surface : Ideal GeoJets) (a h : Shape) :
    leftHom surface a h = ∑ m : LeftLabels a,
      parameter a h (Sum.inl m.val) • leftGen (baseIdeal surface a h) a h (sectionCoord a m) := by
  classical
  unfold leftHom
  apply homogeneous_sum (I := baseIdeal surface a h) (a := a) (h := h) (d := (1, 0))
  change Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h) = _
  rw [← dehom_left surface a h]
  simp only [leftForm, Finset.attach_eq_univ, map_sum, map_mul, dehom, AlgHom.comp_apply,
    aeval_C, aeval_X, generatorExponent, Sum.elim_inl, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (Algebra.smul_def (parameter a h (Sum.inl m.val))
    (Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m.val) 1))).symm
theorem rightHom_sum (surface : Ideal GeoJets) (a h : Shape) :
    rightHom surface a h = ∑ m : RightLabels h,
      parameter a h (Sum.inr m.val) • rightGen (baseIdeal surface a h) a h (sectionCoord h m) := by
  classical
  unfold rightHom
  apply homogeneous_sum (I := baseIdeal surface a h) (a := a) (h := h) (d := (0, 1))
  change Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h) = _
  rw [← dehom_right surface a h]
  simp only [rightForm, Finset.attach_eq_univ, map_sum, map_mul, dehom, AlgHom.comp_apply,
    aeval_C, aeval_X, generatorExponent, Sum.elim_inr, Ideal.Quotient.mkₐ_eq_mk,
    MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact (Algebra.smul_def (parameter a h (Sum.inr m.val))
    (Ideal.Quotient.mk (extendIdeal surface a h) (monomial (boxExponent m.val) 1))).symm
theorem shift_eq_pair (surface : Ideal GeoJets) (a h : Shape) :
    shift (baseIdeal surface a h) a h =
      pairGen (baseIdeal surface a h) a h (zeroCoord a, zeroCoord h) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single (1, 1) (1 : SurfaceRing surface a h) =
    (rees (baseIdeal surface a h) a h).val
      (leftGen (baseIdeal surface a h) a h (zeroCoord a) *
      rightGen (baseIdeal surface a h) a h (zeroCoord h))
  simp only [map_mul, leftGen, rightGen, val_homogeneous, zeroCoord, monomial_zero', map_one,
    AddMonoidAlgebra.single_mul_single, mul_one]
  rfl
end
end K1_13_6_1_4_2_1_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_2 MvPolynomial
def affineBaseChange (surface : Ideal GeoJets) (a h : Shape) :
    Base surface →ₐ[GeoField] SurfaceRing surface a h :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId GeoField (Coeff a h)))
    Ideal.le_comap_map
private theorem affineBaseChange_mk (surface : Ideal GeoJets) (a h : Shape) (q : GeoJets) :
    affineBaseChange surface a h (Ideal.Quotient.mk surface q) =
      Ideal.Quotient.mk (extendIdeal surface a h)
        (MvPolynomial.map (algebraMap GeoField (Coeff a h)) q) := rfl
def reesBaseChange (surface : Ideal GeoJets) (a h : Shape) :
    rees surface a h →ₐ[GeoField] Rees surface a h := by
  let f := affineBaseChange surface a h
  let g := (AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) f).comp (rees surface a h).val
  refine g.codRestrict ((rees (baseIdeal surface a h) a h).restrictScalars GeoField) ?_
  intro p d
  change (AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) f p.val).coeff d ∈ _
  rw [AddMonoidAlgebra.coeff_mapAlgHom]
  obtain ⟨q, hq, he⟩ := p.property d
  refine ⟨MvPolynomial.map (algebraMap GeoField (Coeff a h)) q, ?_, ?_⟩
  · intro m hm
    exact hq (support_map_subset _ _ hm)
  · rw [← he]
    rfl
@[simp] theorem reesBaseChange_left (surface : Ideal GeoJets) (a h : Shape) (x : latticeIndices a) :
    reesBaseChange surface a h (leftGen surface a h x) =
      leftGen (baseIdeal surface a h) a h x := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) (affineBaseChange surface a h)
    (AddMonoidAlgebra.single (1, 0) (monomialAt surface x.val)) = _
  rw [AddMonoidAlgebra.mapAlgHom_single]
  change AddMonoidAlgebra.single (1, 0) _ =
    AddMonoidAlgebra.single (1, 0) (Ideal.Quotient.mk (extendIdeal surface a h) (monomial x.val 1))
  apply congrArg (AddMonoidAlgebra.single (1, 0))
  rw [monomialAt, affineBaseChange_mk, MvPolynomial.map_monomial, map_one]
@[simp] theorem reesBaseChange_right (surface : Ideal GeoJets) (a h : Shape) (y : latticeIndices h) :
    reesBaseChange surface a h (rightGen surface a h y) =
      rightGen (baseIdeal surface a h) a h y := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapAlgHom (ℕ × ℕ) (affineBaseChange surface a h)
    (AddMonoidAlgebra.single (0, 1) (monomialAt surface y.val)) = _
  rw [AddMonoidAlgebra.mapAlgHom_single]
  change AddMonoidAlgebra.single (0, 1) _ =
    AddMonoidAlgebra.single (0, 1) (Ideal.Quotient.mk (extendIdeal surface a h) (monomial y.val 1))
  apply congrArg (AddMonoidAlgebra.single (0, 1))
  rw [monomialAt, affineBaseChange_mk, MvPolynomial.map_monomial, map_one]
@[simp] theorem reesBaseChange_pair (surface : Ideal GeoJets) (a h : Shape)
    (e : latticeIndices a × latticeIndices h) :
    reesBaseChange surface a h (pairGen surface a h e) =
      pairGen (baseIdeal surface a h) a h e := by
  simp [pairGen]
end
end K1_13_6_1_4_2_1_2_2
end
section
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13_6 K1_13_6_1_4_2 Algebra
open scoped nonZeroDivisors
theorem affineDimension (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = d ∧ trdeg k A = (d : Cardinal) := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let N := MvPolynomial (Fin d) k
  letI : Algebra N A := g.toRingHom.toAlgebra
  letI : IsScalarTower k N A := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  letI : FaithfulSMul N A := (faithfulSMul_iff_algebraMap_injective N A).mpr hg
  letI : Module.Finite N A := hfin
  letI : Algebra.IsIntegral N A := Algebra.IsIntegral.of_finite N A
  let p := PrimeSpectrum.comap (algebraMap N A)
  have hmono : StrictMono p := by
    intro x y hxy
    letI : x.asIdeal.IsPrime := x.2
    exact Ideal.IsIntegral.under_lt_under (R := N) hxy
  have hdim : ringKrullDim A = ringKrullDim N := by
    refine (Order.krullDim_le_of_strictMono p hmono).antisymm ?_
    change Order.krullDim (PrimeSpectrum N) ≤ Order.krullDim (PrimeSpectrum A)
    rw [Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    apply iSup_le
    intro l
    obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective N A l.head
    letI : P.asIdeal.IsPrime := P.2
    letI : P.asIdeal.LiesOver l.head.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact hL ▸ le_iSup (fun L : LTSeries (PrimeSpectrum A) => (L.length : ℕ∞)) L
  refine ⟨d, ?_, ?_⟩
  · simp [hdim, N, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  · letI : Algebra.IsAlgebraic N A := Algebra.IsAlgebraic.of_finite N A
    simpa [N, trdeg_eq_zero (R := N) (A := A), Cardinal.mk_fin] using
      (trdeg_add_eq (A := A) k N).symm
theorem chart_trdeg (surface : Ideal GeoJets) [surface.IsPrime] (a h : K1_13.Shape)
    (e : latticeIndices a × latticeIndices h)
    (hdim : ringKrullDim (Base surface) = 2) :
    trdeg GeoField (chartAlgebra surface a h e) ≤ 2 := by
  obtain ⟨d, hd, ht⟩ := affineDimension GeoField (Base surface)
  have hd' : d = 2 := by exact_mod_cast hd.symm.trans hdim
  have hfield : trdeg GeoField (FunctionField surface) = 2 := by
    letI : Algebra.IsAlgebraic (Base surface) (FunctionField surface) :=
      IsLocalization.isAlgebraic _ (Base surface)⁰
    rw [← trdeg_add_eq GeoField (Base surface) (A := FunctionField surface),
      trdeg_eq_zero (R := Base surface) (A := FunctionField surface), add_zero, ht, hd']
    rfl
  exact (trdeg_le_of_injective (chartAlgebra surface a h e).val Subtype.val_injective).trans hfield.le
end
end K1_13_6_1_4_2_1_2_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_2_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2
  K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_2 MvPolynomial
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra GeoField E]
    (φ : rees surface a h →ₐ[GeoField] E), φ (pairGen surface a h e) ≠ 0 →
    monomialFraction surface e.1.val ≠ 0 ∧ monomialFraction surface e.2.val ≠ 0 ∧
      ∃ f : chartAlgebra surface a h e →ₐ[GeoField] E,
        ∀ i, f (chartCoord surface a h e i) = ratioValue surface a h e φ i
def c2 : Prop :=
  ∀ {k A E σ τ : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field E] [Algebra k E] [Fintype σ] [Fintype τ]
    (t : σ ⊕ τ → E), AlgebraicIndependent k t →
    Algebra.trdeg k A ≤ 2 →
    ∀ (b : A), b ≠ 0 → ∀ f : A →ₐ[k] E, f b = 0 →
    ∀ (i : σ) (j : τ),
    ∀ (u : σ → A) (v : τ → A), u i = 1 → v j = 1 →
    (∑ m, t (Sum.inl m) * f (u m)) = 0 →
    (∑ m, t (Sum.inr m) * f (v m)) = 0 → False
private theorem no_boundary_point (h1 : c1) (h2 : c2)
    (surface : Ideal GeoJets) [surface.IsPrime] (a h : Shape)
    (hdim : ringKrullDim (Base surface) = 2) (e : latticeIndices a × latticeIndices h)
    {E : Type} [Field E] [Algebra (Coeff a h) E] [Algebra GeoField E]
    [IsScalarTower GeoField (Coeff a h) E]
    (φ : Rees surface a h →ₐ[Coeff a h] E)
    (hchart : φ (pairGen (baseIdeal surface a h) a h e) ≠ 0)
    (hleft : φ (leftHom surface a h) = 0) (hright : φ (rightHom surface a h) = 0)
    (hshift : φ (shift (baseIdeal surface a h) a h) = 0) : False := by
  classical
  let ψ := (φ.restrictScalars GeoField).comp (reesBaseChange surface a h)
  have hψ : ψ (pairGen surface a h e) ≠ 0 := by simpa [ψ] using hchart
  obtain ⟨hα, hβ, f, hratio⟩ := h1 surface a h e ψ hψ
  have hcoord (i : K1_13_6_1_4_2_1_1.Generator a h) :
      f (chartCoord surface a h e i) = ratioValue (baseIdeal surface a h) a h e φ i := by
    rw [hratio]
    cases i with
    | inl x =>
      change ψ (leftGen surface a h x) / ψ (leftGen surface a h e.1) =
        φ (leftGen (baseIdeal surface a h) a h x) / φ (leftGen (baseIdeal surface a h) a h e.1)
      simp [ψ]
    | inr y =>
      change ψ (rightGen surface a h y) / ψ (rightGen surface a h e.2) =
        φ (rightGen (baseIdeal surface a h) a h y) / φ (rightGen (baseIdeal surface a h) a h e.2)
      simp [ψ]
  let b := chartCoord surface a h e (Sum.inl (zeroCoord a)) *
    chartCoord surface a h e (Sum.inr (zeroCoord h))
  have hb : b ≠ 0 := by
    intro hz
    have hzero : monomialFraction surface 0 = 1 := by simp [monomialFraction, monomialAt]
    have hv := congrArg Subtype.val hz
    change (monomialFraction surface 0 / monomialFraction surface e.1.val) *
      (monomialFraction surface 0 / monomialFraction surface e.2.val) = 0 at hv
    rw [hzero] at hv
    exact mul_ne_zero (div_ne_zero one_ne_zero hα) (div_ne_zero one_ne_zero hβ) hv
  have hbzero : f b = 0 := by
    dsimp only [b]
    rw [map_mul, hcoord, hcoord]
    simp only [ratioValue, Sum.elim_inl, Sum.elim_inr, ← mul_div_mul_comm, ← map_mul]
    change φ (pairGen (baseIdeal surface a h) a h (zeroCoord a, zeroCoord h)) /
      φ (pairGen (baseIdeal surface a h) a h e) = 0
    rw [← shift_eq_pair, hshift, zero_div]
  let P := MvPolynomial (Parameters a h) GeoField
  let F := Coeff a h
  let t (l : LeftLabels a ⊕ RightLabels h) : E :=
    algebraMap F E (parameter a h (Sum.map Subtype.val Subtype.val l))
  have htFull : AlgebraicIndependent GeoField (fun l : Parameters a h =>
      algebraMap F E (parameter a h l)) :=
    ((algebraicIndependent_X (Parameters a h) GeoField).map'
      (f := IsScalarTower.toAlgHom GeoField P F) (IsFractionRing.injective P F)).map'
        (f := IsScalarTower.toAlgHom GeoField F E) (algebraMap F E).injective
  have ht : AlgebraicIndependent GeoField t :=
    htFull.comp (Sum.map Subtype.val Subtype.val)
      (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
  let u (m : LeftLabels a) := chartCoord surface a h e (Sum.inl (sectionCoord a m))
  let v (m : RightLabels h) := chartCoord surface a h e (Sum.inr (sectionCoord h m))
  obtain ⟨i, hi⟩ := sectionCoord_surjective a e.1
  obtain ⟨j, hj⟩ := sectionCoord_surjective h e.2
  have hui : u i = 1 := by
    apply Subtype.ext
    change chartValue surface a h e (Sum.inl (sectionCoord a i)) = 1
    simp [hi, chartValue, hα]
  have hvj : v j = 1 := by
    apply Subtype.ext
    change chartValue surface a h e (Sum.inr (sectionCoord h j)) = 1
    simp [hj, chartValue, hβ]
  have hu : (∑ m, t (Sum.inl m) * f (u m)) = 0 := by
    rw [leftHom_sum] at hleft
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] at hleft
    calc
      _ = (∑ m : LeftLabels a, t (Sum.inl m) *
          φ (leftGen (baseIdeal surface a h) a h (sectionCoord a m))) /
            φ (leftGen (baseIdeal surface a h) a h e.1) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun m _ => ?_
        dsimp only [u]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _ = 0 := by rw [show (∑ m, t (Sum.inl m) *
        φ (leftGen (baseIdeal surface a h) a h (sectionCoord a m))) = 0 from hleft, zero_div]
  have hv : (∑ m, t (Sum.inr m) * f (v m)) = 0 := by
    rw [rightHom_sum] at hright
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] at hright
    calc
      _ = (∑ m : RightLabels h, t (Sum.inr m) *
          φ (rightGen (baseIdeal surface a h) a h (sectionCoord h m))) /
            φ (rightGen (baseIdeal surface a h) a h e.2) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun m _ => ?_
        dsimp only [v]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _ = 0 := by rw [show (∑ m, t (Sum.inr m) *
        φ (rightGen (baseIdeal surface a h) a h (sectionCoord h m))) = 0 from hright, zero_div]
  exact h2 t ht (chart_trdeg surface a h e hdim)
    b hb f hbzero i j u v hui hvj hu hv
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1_2.c2 := by
  intro surface a h hsurface hdim _ _ e
  let : surface.IsPrime := hsurface
  let I := homBoundaryIdeal surface a h
  change pairGen (baseIdeal surface a h) a h e ∈ I.radical
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.mpr fun {J} hJ => ?_
  obtain ⟨hIJ, hprime⟩ := hJ
  let : J.IsPrime := hprime
  by_contra hchart
  let F := Coeff a h
  let D := Rees surface a h ⧸ J
  let : CommRing D := Ideal.Quotient.commRing (R := Rees surface a h) J
  let : IsDomain D := Ideal.Quotient.isDomain J
  let : Algebra F D := inferInstanceAs (Algebra (Coeff a h) (Rees surface a h ⧸ J))
  let E := FractionRing D
  let : Field E := inferInstanceAs (Field (FractionRing D))
  let : Algebra D E := inferInstanceAs (Algebra D (FractionRing D))
  let : Algebra F E := inferInstanceAs (Algebra F (FractionRing D))
  let : IsScalarTower F D E := inferInstanceAs (IsScalarTower F D (FractionRing D))
  let : Algebra GeoField E := Algebra.compHom E (algebraMap GeoField F)
  let : SMul GeoField E := Algebra.toSMul
  let : SMul GeoField F := Algebra.toSMul
  let : SMul F E := Algebra.toSMul
  let : IsScalarTower GeoField F E := IsScalarTower.of_algebraMap_eq' rfl
  let φ : Rees surface a h →ₐ[F] E :=
    (IsScalarTower.toAlgHom F D E).comp (Ideal.Quotient.mkₐ F J)
  have hvanish (x : Rees surface a h) (hx : x ∈ I) : φ x = 0 := by
    change algebraMap D E (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx), map_zero]
  have hnonzero : φ (pairGen (baseIdeal surface a h) a h e) ≠ 0 := by
    intro hz
    apply hchart
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective D E
    change algebraMap D E (Ideal.Quotient.mk J (pairGen (baseIdeal surface a h) a h e)) = 0 at hz
    rw [map_zero]
    exact hz
  exact no_boundary_point h1 h2 surface a h hdim e φ hnonzero
    (hvanish _ (Ideal.mem_sup_left (Ideal.subset_span (by simp))))
    (hvanish _ (Ideal.mem_sup_left (Ideal.subset_span (by simp))))
    (hvanish _ (Ideal.mem_sup_right (Ideal.subset_span (by simp))))
end
end K1_13_6_1_4_2_1_2_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_2_1_2_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_1_1
  K1_13_6_1_4_2_1_2 K1_13_6_1_4_2_1_2_2
private theorem away_fraction {k R F : Type*} [CommRing k] [CommRing R] [Field F]
    [Algebra k R] [Algebra k F] (b x : R) (g : R →ₐ[k] F) (hb : g b ≠ 0) :
    IsLocalization.Away.liftAlgHom (S := Localization.Away b) b (f := g) hb.isUnit
      (IsLocalization.mk' (Localization.Away b) x ⟨b, Submonoid.mem_powers b⟩) =
        g x / g b := by
  let f : Localization.Away b →ₐ[k] F := IsLocalization.Away.liftAlgHom b (f := g) hb.isUnit
  have hf (y : R) : f (algebraMap R (Localization.Away b) y) = g y :=
    IsLocalization.Away.lift_eq b (g := g.toRingHom) hb.isUnit y
  change f _ = _
  apply (eq_div_iff hb).2
  simpa only [map_mul, hf] using
    congrArg f (IsLocalization.mk'_spec (Localization.Away b) x ⟨b, Submonoid.mem_powers b⟩)
private theorem evaluate_adjoin {k R K L E ι : Type*}
    [CommRing k] [CommRing R] [CommRing K] [Field L] [Field E]
    [Algebra k R] [Algebra k K] [Algebra k L] [Algebra k E]
    (j : R →ₐ[k] L) (hj : Function.Injective j)
    (b : R) (φ : R →ₐ[k] E) (hb : φ b ≠ 0)
    (c : K →ₐ[k] L) (r : ι → K) (n : ι → R)
    (hr : ∀ t, c (r t) * j b = j (n t)) :
    ∃ f : Algebra.adjoin k (Set.range r) →ₐ[k] E,
      ∀ t, f ⟨r t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = φ (n t) / φ b := by
  let S := Localization.Away b
  let fraction (x : R) : S := IsLocalization.mk' S x ⟨b, Submonoid.mem_powers b⟩
  have hjb : j b ≠ 0 := by
    intro hz
    have h : b = 0 := hj (hz.trans (map_zero j).symm)
    exact hb (h ▸ map_zero φ)
  let lift : S →ₐ[k] L := IsLocalization.Away.liftAlgHom b (f := j) hjb.isUnit
  have hlift (x : R) : lift (algebraMap R S x) = j x :=
    IsLocalization.Away.lift_eq b (g := j.toRingHom) hjb.isUnit x
  have hinj : Function.Injective lift := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers b) lift.toRingHom).2
    intro x y
    change algebraMap R S x = algebraMap R S y ↔
      lift (algebraMap R S x) = lift (algebraMap R S y)
    rw [hlift, hlift]
    constructor
    · exact fun h => (hlift x).symm.trans ((congrArg lift h).trans (hlift y))
    · exact fun h => congrArg (algebraMap R S) (hj h)
  have hlift_fraction (t : ι) : lift (fraction (n t)) = c (r t) :=
    (away_fraction b (n t) j hjb).trans ((eq_div_iff hjb).2 (hr t)).symm
  let chart := Algebra.adjoin k (Set.range r)
  have hchart : chart ≤ lift.range.comap c := by
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    exact ⟨fraction (n t), hlift_fraction t⟩
  let g : chart →ₐ[k] lift.range :=
    (c.comp chart.val).codRestrict lift.range fun x => hchart x.property
  let u : S ≃ₐ[k] lift.range := AlgEquiv.ofInjective lift hinj
  let ev : S →ₐ[k] E := IsLocalization.Away.liftAlgHom b (f := φ) hb.isUnit
  refine ⟨(ev.comp u.symm.toAlgHom).comp g, fun t => ?_⟩
  have ht : g ⟨r t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = u (fraction (n t)) :=
    Subtype.ext (hlift_fraction t).symm
  change ev (u.symm (g ⟨r t, _⟩)) = _
  rw [ht, AlgEquiv.symm_apply_apply]
  exact away_fraction b (n t) φ hb
theorem proof : K1_13_6_1_4_2_1_2_2.c1 := by
  intro surface hprime a h e E hE hAlgebra φ hφ
  let : surface.IsPrime := hprime
  let : Field E := hE
  let : Algebra GeoField E := hAlgebra
  let A := AddMonoidAlgebra (Base surface) (ℕ × ℕ)
  let L := FractionRing A
  let embed := IsScalarTower.toAlgHom GeoField A L
  let j := embed.comp (rees surface a h).val
  have hj : Function.Injective j := (IsFractionRing.injective A L).comp Subtype.val_injective
  let constant : Base surface →ₐ[GeoField] L := embed.comp AddMonoidAlgebra.singleZeroAlgHom
  have hconstant : Function.Injective constant := by
    intro x y hxy
    have hs : (AddMonoidAlgebra.single 0 x : A) = AddMonoidAlgebra.single 0 y :=
      IsFractionRing.injective A L hxy
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using
      congrArg (fun p : A => p.coeff 0) hs
  let c : FunctionField surface →ₐ[GeoField] L := IsFractionRing.liftAlgHom hconstant
  have hconstant_monomial (x : Fin 4 →₀ ℕ) :
      c (monomialFraction surface x) =
        embed (AddMonoidAlgebra.single 0 (monomialAt surface x)) :=
    IsFractionRing.lift_algebraMap (g := constant.toRingHom) hconstant _
  let degree (d : ℕ × ℕ) := embed (AddMonoidAlgebra.single d 1)
  have homogeneous_image (d : ℕ × ℕ) (x : Fin 4 →₀ ℕ)
      (hx : monomialAt surface x ∈ box surface a h d) :
      j (homogeneous d (monomialAt surface x) hx) =
        c (monomialFraction surface x) * degree d := by
    change embed (AddMonoidAlgebra.single d (monomialAt surface x)) =
      c (monomialFraction surface x) * embed (AddMonoidAlgebra.single d 1)
    rw [hconstant_monomial, ← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have hleft (x : latticeIndices a) :
      j (leftGen surface a h x) = c (monomialFraction surface x.val) * degree (1, 0) :=
    homogeneous_image (1, 0) x.val _
  have hright (y : latticeIndices h) :
      j (rightGen surface a h y) = c (monomialFraction surface y.val) * degree (0, 1) :=
    homogeneous_image (0, 1) y.val _
  have hp : φ (leftGen surface a h e.1) * φ (rightGen surface a h e.2) ≠ 0 := by
    simpa only [pairGen, map_mul] using hφ
  obtain ⟨hφleft, hφright⟩ := mul_ne_zero_iff.mp hp
  have coeff_ne_zero (x : Fin 4 →₀ ℕ) (p : rees surface a h) (d : ℕ × ℕ)
      (hj' : j p = c (monomialFraction surface x) * degree d) (hp' : φ p ≠ 0) :
      monomialFraction surface x ≠ 0 := by
    intro hz
    have heq : j p = j 0 := by rw [hj', hz, map_zero, zero_mul, map_zero]
    have hzero : p = 0 := hj heq
    exact hp' (hzero ▸ map_zero φ)
  have hα := coeff_ne_zero e.1.val (leftGen surface a h e.1) (1, 0) (hleft e.1) hφleft
  have hβ := coeff_ne_zero e.2.val (rightGen surface a h e.2) (0, 1) (hright e.2) hφright
  have left_ratio (x : latticeIndices a) :
      c (monomialFraction surface x.val / monomialFraction surface e.1.val) *
        j (leftGen surface a h e.1) = j (leftGen surface a h x) := by
    rw [map_div₀, hleft, hleft, ← mul_assoc, div_mul_cancel₀ _ ((map_ne_zero c).2 hα)]
  have right_ratio (y : latticeIndices h) :
      c (monomialFraction surface y.val / monomialFraction surface e.2.val) *
        j (rightGen surface a h e.2) = j (rightGen surface a h y) := by
    rw [map_div₀, hright, hright, ← mul_assoc, div_mul_cancel₀ _ ((map_ne_zero c).2 hβ)]
  let n : Generator a h → rees surface a h :=
    Sum.elim (fun x => pairGen surface a h (x, e.2)) (fun y => pairGen surface a h (e.1, y))
  have hratio (i : Generator a h) :
      c (chartValue surface a h e i) * j (pairGen surface a h e) = j (n i) := by
    cases i with
    | inl x =>
      simp only [chartValue, n, Sum.elim_inl, pairGen, map_mul]
      rw [← mul_assoc, left_ratio]
    | inr y =>
      simp only [chartValue, n, Sum.elim_inr, pairGen, map_mul]
      rw [mul_left_comm, right_ratio]
  obtain ⟨f, hf⟩ := evaluate_adjoin j hj (pairGen surface a h e) φ hφ c
    (chartValue surface a h e) n hratio
  refine ⟨hα, hβ, f, fun i => (hf i).trans ?_⟩
  cases i with
  | inl x =>
    simp only [n, ratioValue, Sum.elim_inl, pairGen, map_mul]
    exact mul_div_mul_right _ _ hφright
  | inr y =>
    simp only [n, ratioValue, Sum.elim_inr, pairGen, map_mul]
    exact mul_div_mul_left _ _ hφleft
end
end K1_13_6_1_4_2_1_2_2_1
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem component_mul {k α β : Type} [CommSemiring k]
    {g : MvPolynomial (α ⊕ β) k} {e : ℕ × ℕ} (hg : g ∈ grade e)
    (p : MvPolynomial (α ⊕ β) k) (d : ℕ × ℕ) :
    weightedHomogeneousComponent weight (d + e) (p * g) =
      weightedHomogeneousComponent weight d p * g := by
  induction p using MvPolynomial.induction_on' with
  | monomial b r =>
    have hb := isWeightedHomogeneous_monomial weight b r rfl
    simp only [weightedHomogeneousComponent_of_mem (hb.mul hg),
      weightedHomogeneousComponent_of_mem hb, add_right_cancel_iff]
    split <;> simp_all
  | add a b ha hb => simp [add_mul, ha, hb]
theorem homogeneous_colon {k α β : Type} [CommRing k]
    {I : Ideal (MvPolynomial (α ⊕ β) k)} (hI : I.IsHomogeneous grade)
    {g : MvPolynomial (α ⊕ β) k} {e : ℕ × ℕ} (hg : g ∈ grade e) :
    (I.colon {g}).IsHomogeneous grade := by
  intro d p hp
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hp ⊢
  have he : (DirectSum.decompose grade p d : MvPolynomial (α ⊕ β) k) =
      weightedHomogeneousComponent weight d p :=
    weightedDecomposition.decompose'_apply k weight p d
  rw [he, ← component_mul hg]
  exact weightedHomogeneousComponent_mem_of_mem _ _ hI hp _
section Noetherian
variable {k α β : Type} [Field k] [Fintype α] [Fintype β]
private abbrev P := MvPolynomial (α ⊕ β) k
private theorem chart_pow_dvd_monomial (d : α ⊕ β →₀ ℕ) (r : k) (n : ℕ)
    (hleft : Fintype.card α * n < (Finsupp.weight weight d).1)
    (hright : Fintype.card β * n < (Finsupp.weight weight d).2) :
    ∃ x : α, ∃ y : β, (chart x y : P (k := k)) ^ n ∣ monomial d r := by
  classical
  have hs₁ : (Finsupp.weight weight d).1 = ∑ x : α, d (Sum.inl x) := by
    simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type, weight, Prod.fst_sum]
  have hs₂ : (Finsupp.weight weight d).2 = ∑ y : β, d (Sum.inr y) := by
    simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type, weight, Prod.snd_sum]
  have hx : ∃ x : α, n ≤ d (Sum.inl x) := by
    by_contra! hnone
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun x _ => (hnone x).le
    rw [hs₁] at hleft
    exact (not_le_of_gt hleft) (by simpa using hsum)
  have hy : ∃ y : β, n ≤ d (Sum.inr y) := by
    by_contra! hnone
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun y _ => (hnone y).le
    rw [hs₂] at hright
    exact (not_le_of_gt hright) (by simpa using hsum)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  let t := Finsupp.single (Sum.inl x) n + Finsupp.single (Sum.inr y) n
  have ht : t ≤ d := by
    intro z
    rcases z with z | z
    · by_cases h : z = x
      · subst z
        simpa [t, Finsupp.single_apply] using hx
      · simp [t, h]
    · by_cases h : z = y
      · subst z
        simpa [t, Finsupp.single_apply] using hy
      · simp [t, h]
  refine ⟨x, y, monomial (d - t) r, ?_⟩
  rw [chart, mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul, ← show t = _ from rfl, monomial_mul_monomial, one_mul,
    add_comm t, tsub_add_cancel_of_le ht]
private theorem uniform_chart_power (I K : Ideal (P (k := k) (α := α) (β := β)))
    (hlocal : ∀ x : α, ∀ y : β, ∀ p ∈ K, ∃ n : ℕ, chart x y ^ n * p ∈ I) :
    ∃ n : ℕ, ∀ x : α, ∀ y : β, ∀ p ∈ K, chart x y ^ n * p ∈ I := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian K
  have hg (v : α × β × ↥s) : ∃ n : ℕ, chart v.1 v.2.1 ^ n * v.2.2.val ∈ I :=
    hlocal v.1 v.2.1 _ (hs ▸ Ideal.subset_span v.2.2.property)
  choose n hn using hg
  let N := Finset.univ.sup n
  refine ⟨N, fun x y p hp => ?_⟩
  have hf : K ≤ I.colon {chart x y ^ N} := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro q hq
    change q ∈ I.colon {chart x y ^ N}
    apply Submodule.mem_colon_singleton.mpr
    let v : α × β × ↥s := (x, y, ⟨q, hq⟩)
    have hnv : n v ≤ N := Finset.le_sup (Finset.mem_univ v)
    have hq' : chart x y ^ n v * q ∈ I := hn v
    rw [smul_eq_mul, mul_comm,
      show N = N - n v + n v from (Nat.sub_add_cancel hnv).symm,
      pow_add, mul_assoc]
    exact I.mul_mem_left _ hq'
  exact mul_comm p _ ▸ (Submodule.mem_colon_singleton.mp (hf hp))
theorem high_degree_of_charts (I K : Ideal (P (k := k) (α := α) (β := β)))
    (hK : K.IsHomogeneous grade)
    (hlocal : ∀ x : α, ∀ y : β, ∀ p ∈ K, ∃ n : ℕ, chart x y ^ n * p ∈ I) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ p ∈ K, p ∈ grade (i, j) → p ∈ I := by
  classical
  obtain ⟨n, hn⟩ := uniform_chart_power I K hlocal
  let S : Set (P (k := k) (α := α) (β := β)) :=
    {p | p ∈ K ∧ ∃ e : ℕ × ℕ, p ∈ grade e}
  have hS : Ideal.span S = K := by
    apply le_antisymm (Ideal.span_le.mpr fun p (hp : p ∈ S) => hp.1)
    have hle : (K.homogeneousCore grade).toIdeal ≤ Ideal.span S := by
      change Ideal.span _ ≤ _
      apply Ideal.span_mono
      rintro _ ⟨⟨q, hq⟩, hmem, rfl⟩
      exact ⟨hmem, hq⟩
    simpa only [hK.toIdeal_homogeneousCore_eq_self] using hle
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (hS.symm ▸ IsNoetherian.noetherian K)
  have hsg (q : ↥s) : ∃ d : ℕ × ℕ, q.val ∈ grade d := (hsS q.property).2
  choose e he using hsg
  let B := Finset.univ.sup fun q : ↥s => max (e q).1 (e q).2
  let N := (Fintype.card α + Fintype.card β) * n + B + 1
  refine ⟨N, fun i j hi hj p hp hpg => ?_⟩
  let proj := weightedHomogeneousComponent weight (i, j) (R := k) (σ := α ⊕ β)
  have hgen (q : ↥s) (u : P (k := k) (α := α) (β := β)) : proj (u * q.val) ∈ I := by
    have hbound := Finset.le_sup (f := fun q : ↥s => max (e q).1 (e q).2) (Finset.mem_univ q)
    have hb₁ : (e q).1 ≤ B := (le_max_left _ _).trans hbound
    have hb₂ : (e q).2 ≤ B := (le_max_right _ _).trans hbound
    induction u using MvPolynomial.induction_on' with
    | add u v hu hv => simpa only [add_mul, map_add] using I.add_mem hu hv
    | monomial d c =>
      have hm := isWeightedHomogeneous_monomial weight d c rfl
      change weightedHomogeneousComponent weight (i, j) (monomial d c * q.val) ∈ I
      rw [weightedHomogeneousComponent_of_mem (hm.mul (he q))]
      split
      next h =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        change i = (Finsupp.weight weight d).1 + (e q).1 at h₁
        change j = (Finsupp.weight weight d).2 + (e q).2 at h₂
        have hc₁ := Nat.mul_le_mul_right n (Nat.le_add_right (Fintype.card α) (Fintype.card β))
        have hc₂ := Nat.mul_le_mul_right n (Nat.le_add_left (Fintype.card β) (Fintype.card α))
        dsimp only [N] at hi hj
        obtain ⟨x, y, t, ht⟩ := chart_pow_dvd_monomial d c n
          (by omega : _ < (Finsupp.weight weight d).1) (by omega : _ < (Finsupp.weight weight d).2)
        rw [ht, mul_comm (_ ^ n), mul_assoc]
        exact I.mul_mem_left t (hn x y _ (hsS q.property).1)
      next => exact I.zero_mem
  have hmem : p ∈ Submodule.span (P (k := k) (α := α) (β := β)) (↑s : Set _) := by
    rw [← hs]
    change p ∈ Ideal.span S
    rwa [hS]
  have hproj : ∀ u : P (k := k) (α := α) (β := β), proj (u * p) ∈ I := by
    refine Submodule.span_induction (p := fun q _ => ∀ u, proj (u * q) ∈ I)
      (fun q hq u => hgen ⟨q, hq⟩ u) ?_ ?_ ?_ hmem
    · intro u
      simp
    · intro x y hx hy hpx hpy u
      simpa only [mul_add, map_add] using I.add_mem (hpx u) (hpy u)
    · intro c x hx hpx u
      simpa only [smul_eq_mul, mul_assoc] using hpx (u * c)
  simpa only [one_mul, proj, weightedHomogeneousComponent_eq_self hpg] using hproj 1
end Noetherian
end
end K1_13_6_1_4_2_1_1
end
section
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_2_1_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.weightedGradedAlgebra MvPolynomial.algebraMvPolynomial
private def block {α β : Type} : α ⊕ β → Bool := Sum.elim (fun _ => false) (fun _ => true)
private def degree : (Bool →₀ ℕ) →+ ℕ × ℕ where
  toFun d := (d false, d true)
  map_zero' := rfl
  map_add' _ _ := rfl
private theorem degree_apply (d : Bool →₀ ℕ) : degree d = (d false, d true) := rfl
private theorem degree_injective : Function.Injective degree := by
  intro u v hv
  ext b
  cases b
  · exact congrArg Prod.fst hv
  · exact congrArg Prod.snd hv
private theorem degree_weight {α β : Type} (d : α ⊕ β →₀ ℕ) :
    degree (Finsupp.weight (fun i => Finsupp.single (block i) 1) d) = Finsupp.weight weight d := by
  have h : degree.comp (Finsupp.weight (fun i : α ⊕ β => Finsupp.single (block i) 1)) =
      Finsupp.weight (R := ℕ) (weight : α ⊕ β → ℕ × ℕ) := by
    apply Finsupp.addHom_ext
    intro v n
    cases v <;> simp [degree_apply, block, weight, Finsupp.weight_single]
  exact DFunLike.congr_fun h d
private def homogenize {k B α β : Type} [CommRing k] [CommRing B] [Algebra k B]
    (f : MvPolynomial (α ⊕ β) k →ₐ[k] B) :
    MvPolynomial (α ⊕ β) k →ₐ[k] MvPolynomial Bool B :=
  aeval fun v => monomial (Finsupp.single (block v) 1) (f (MvPolynomial.X v))
private theorem coeff_homogenize {k B α β : Type} [CommRing k] [CommRing B] [Algebra k B]
    (f : MvPolynomial (α ⊕ β) k →ₐ[k] B) (p : MvPolynomial (α ⊕ β) k) (b : Bool →₀ ℕ) :
    (homogenize f p).coeff b = f (weightedHomogeneousComponent weight (degree b) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    change (homogenize f p).coeff b + (homogenize f q).coeff b = _
    rw [hp, hq]
  | monomial d c =>
    let w := fun v : α ⊕ β => Finsupp.single (block v) (1 : ℕ)
    have hm : homogenize f (monomial d c) =
        monomial (Finsupp.weight w d) (f (monomial d c)) := by
      unfold homogenize
      rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
      simp only [monomial_pow, ← monomial_sum_prod]
      change C (algebraMap k B c) * monomial _ _ = _
      rw [C_mul_monomial]
      congr 1
      symm
      have hmono : monomial d c = C c * (d.prod fun i n => (MvPolynomial.X i : MvPolynomial (α ⊕ β) k) ^ n) :=
        monomial_eq
      have hC : f (C c) = algebraMap k B c := f.commutes c
      rw [congrArg f hmono, map_mul, hC, Finsupp.prod, map_prod]
      simp only [map_pow]
    have hh : monomial d c ∈ weightedHomogeneousSubmodule k weight (Finsupp.weight weight d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    rw [hm, coeff_monomial, weightedHomogeneousComponent_of_mem hh]
    by_cases he : degree b = Finsupp.weight weight d
    · have he' : Finsupp.weight w d = b := degree_injective ((degree_weight d).trans he.symm)
      simp [he, he']
    · have he' : Finsupp.weight w d ≠ b := fun h => he ((congrArg degree h).symm.trans (degree_weight d))
      simp [he, he']
private abbrev Target := Bool ⊕ Fin 4
private def jetInclude (k : Type) [CommRing k] :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial Target k :=
  rename Sum.inr
private def model (k : Type) [CommRing k] (a h : Shape) :
    MvPolynomial (Generator a h) k →ₐ[k] MvPolynomial Target k :=
  aeval fun v => MvPolynomial.X (Sum.inl (block v)) *
    jetInclude k (monomial (generatorExponent v) 1)
private def targetIdeal (k : Type) [CommRing k] [Algebra GeoField k]
    (surface : Ideal GeoJets) : Ideal (MvPolynomial Target k) :=
  surface.map ((jetInclude k).toRingHom.comp (MvPolynomial.map (algebraMap GeoField k)))
def modelRelations (k : Type) [CommRing k] [Algebra GeoField k]
    (surface : Ideal GeoJets) (a h : Shape) : Ideal (MvPolynomial (Generator a h) k) :=
  (targetIdeal k surface).comap (model k a h).toRingHom
private def affineEval {k : Type} [CommRing k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    MvPolynomial (Generator a h) k →ₐ[k] (MvPolynomial (Fin 4) k ⧸ I) :=
  (Ideal.Quotient.mkₐ _ _).comp (aeval fun v => monomial (generatorExponent v) 1)
private theorem homogeneous_core_eq_model {k : Type} [CommRing k]
    (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    ((RingHom.ker (affineEval I a h).toRingHom).homogeneousCore grade).toIdeal =
      (I.map (jetInclude k).toRingHom).comap (model k a h).toRingHom := by
  classical
  let Q := MvPolynomial (Fin 4) k ⧸ I
  let e := sumAlgEquiv k Bool (Fin 4)
  let q : MvPolynomial (Fin 4) k →+* Q := Ideal.Quotient.mk I
  let g : MvPolynomial Target k →+* MvPolynomial Bool Q := (MvPolynomial.map q).comp e.toRingHom
  have hcomp : e.toRingHom.comp (jetInclude k).toRingHom = (C : MvPolynomial (Fin 4) k →+* _) :=
    congrArg AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr (R := k) (S₁ := Bool) (S₂ := Fin 4))
  have hk : RingHom.ker g = I.map (jetInclude k).toRingHom := by
    change RingHom.ker ((MvPolynomial.map q).comp e.toRingHom) = _
    rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← hcomp, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  have hg : g.comp (model k a h).toRingHom = (homogenize (affineEval I a h)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change g (model k a h (C c)) = homogenize (affineEval I a h) (C c)
      rw [model, aeval_C, homogenize, aeval_C]
      change MvPolynomial.map q (e (C c)) = C (algebraMap k Q c)
      rw [sumAlgEquiv_C_inl, MvPolynomial.map_C]
      rfl
    · intro v
      change g (model k a h (MvPolynomial.X v)) = homogenize (affineEval I a h) (MvPolynomial.X v)
      rw [model, aeval_X, homogenize, aeval_X]
      have hi := DFunLike.congr_fun hcomp (monomial (generatorExponent v) (1 : k))
      change e (jetInclude k (monomial (generatorExponent v) 1)) = _ at hi
      change MvPolynomial.map q (e (_ * _)) = _
      rw [map_mul, sumAlgEquiv_X_inl, hi, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, mul_comm]
      change C (q _) * monomial _ 1 = _
      rw [C_mul_monomial, mul_one]
      simp only [affineEval, AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk, q]
  rw [← hk, RingHom.comap_ker, hg]
  let J := (RingHom.ker (affineEval I a h).toRingHom).homogeneousCore grade
  change J.toIdeal = _
  ext p
  rw [mem_iff_weightedHomogeneousComponent_mem _ _ J.isHomogeneous, RingHom.mem_ker]
  constructor
  · intro hp
    ext1 b
    change (homogenize (affineEval I a h) p).coeff b = 0
    rw [coeff_homogenize]
    exact Ideal.toIdeal_homogeneousCore_le grade _ (hp (degree b))
  · intro hp d
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, weightedHomogeneousComponent_mem _ _ _⟩
    let b := Finsupp.single false d.1 + Finsupp.single true d.2
    have hb : degree b = d := by simp [b, degree_apply]
    have hz := congrArg (fun z : MvPolynomial Bool Q => z.coeff b) hp
    change (homogenize (affineEval I a h) p).coeff b = 0 at hz
    rw [coeff_homogenize, hb] at hz
    exact RingHom.mem_ker.mpr hz
theorem relations_eq_model (surface : Ideal GeoJets) (a h : Shape) :
    relations surface a h = modelRelations (Coeff a h) surface a h := by
  unfold modelRelations targetIdeal
  rw [← Ideal.map_map]
  exact homogeneous_core_eq_model (extendIdeal surface a h) a h
private theorem model_map {k L : Type} [CommRing k] [CommRing L] (g : k →+* L) (a h : Shape) :
    (MvPolynomial.map g).comp (model k a h).toRingHom =
      (model L a h).toRingHom.comp (MvPolynomial.map g) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [model, MvPolynomial.algebraMap_eq]
  · intro i
    simp [model, jetInclude, MvPolynomial.map_rename]
private theorem targetIdeal_map {k L : Type} [CommRing k] [CommRing L]
    [Algebra GeoField k] [Algebra GeoField L] (g : k →+* L)
    (hg : g.comp (algebraMap GeoField k) = algebraMap GeoField L) (surface : Ideal GeoJets) :
    (targetIdeal k surface).map (MvPolynomial.map g) = targetIdeal L surface := by
  unfold targetIdeal
  rw [Ideal.map_map, ← RingHom.comp_assoc, show (MvPolynomial.map g).comp
    (jetInclude k).toRingHom = (jetInclude L).toRingHom.comp (MvPolynomial.map g) from
      MvPolynomial.map_comp_rename g Sum.inr, RingHom.comp_assoc]
  congr 2
  exact (RingHom.ext fun p => MvPolynomial.map_map _ g p).trans (congrArg MvPolynomial.map hg)
theorem commAlgEquiv_comp_map_C (k σ τ : Type) [CommRing k] :
    (commAlgEquiv k σ τ).toRingHom.comp (MvPolynomial.map C) =
      (C : MvPolynomial σ k →+* MvPolynomial τ (MvPolynomial σ k)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp
theorem modelRelations_polynomial (τ : Type) (surface : Ideal GeoJets) (a h : Shape) :
    modelRelations (MvPolynomial τ GeoField) surface a h =
      (modelRelations GeoField surface a h).map (MvPolynomial.map C) := by
  let k := GeoField
  let P := MvPolynomial τ k
  let e := commAlgEquiv k (Generator a h) τ
  let E := commAlgEquiv k Target τ
  let f := (model k a h).toRingHom
  let g := (model P a h).toRingHom
  have hcomm : E.toRingHom.comp g = (MvPolynomial.map f).comp e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change E (model P a h (C c)) = MvPolynomial.map f (e (C c))
      rw [model, aeval_C, MvPolynomial.algebraMap_eq, commAlgEquiv_C, commAlgEquiv_C,
        MvPolynomial.map_map]
      have hC : f.comp (C (σ := Generator a h)) = C (σ := Target) := by
        apply RingHom.ext
        intro r
        change model k a h (C r) = C r
        simp [model, MvPolynomial.algebraMap_eq]
      rw [hC]
    · intro i
      change E (model P a h (MvPolynomial.X i)) =
        MvPolynomial.map f (e (MvPolynomial.X i))
      have hi := DFunLike.congr_fun (model_map (C : k →+* P) a h) (MvPolynomial.X i)
      change MvPolynomial.map C (model k a h (MvPolynomial.X i)) =
        model P a h (MvPolynomial.map C (MvPolynomial.X i)) at hi
      rw [MvPolynomial.map_X] at hi
      rw [← hi, commAlgEquiv_X, MvPolynomial.map_C]
      exact DFunLike.congr_fun (commAlgEquiv_comp_map_C k Target τ) _
  have hI : (targetIdeal P surface).map E.toRingHom =
      (targetIdeal k surface).map (C (σ := τ)) := by
    rw [← targetIdeal_map (k := k) (L := P) C (by ext; simp [k, P, MvPolynomial.algebraMap_eq]),
      Ideal.map_map, commAlgEquiv_comp_map_C]
  have hJ : ((modelRelations k surface a h).map (MvPolynomial.map C)).map e.toRingHom =
      (modelRelations k surface a h).map (C (σ := τ)) := by
    rw [Ideal.map_map, commAlgEquiv_comp_map_C]
  change (targetIdeal P surface).comap g = _
  rw [← Ideal.comap_map_of_bijective E.toRingHom E.bijective (I := targetIdeal P surface),
    hI, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  rw [← Ideal.comap_map_of_bijective e.toRingHom e.bijective
    (I := (modelRelations k surface a h).map (MvPolynomial.map C)), hJ]
  congr 1
  ext p
  simp only [Ideal.mem_comap, MvPolynomial.mem_map_C_iff, MvPolynomial.coeff_map]
  rfl
private theorem comap_of_localization {A B A' B' : Type} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
    (g : A →+* B) (h : A' →+* B') (M : Submonoid A)
    [IsLocalization M A'] [IsLocalization (M.map g) B']
    (hcomm : h.comp (algebraMap A A') = (algebraMap B B').comp g) (I : Ideal B) :
    (I.map (algebraMap B B')).comap h = (I.comap g).map (algebraMap A A') := by
  have he : h = IsLocalization.map B' g M.le_comap_map := by
    apply IsLocalization.ringHom_ext M
    rw [hcomm, IsLocalization.map_comp]
  ext p
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M p
  rw [Ideal.mem_comap, he, IsLocalization.map_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, he⟩
    exact ⟨d, hd, by simpa only [Ideal.mem_comap, map_mul] using he⟩
  · rintro ⟨d, hd, he⟩
    exact ⟨g d, Submonoid.mem_map_of_mem _ hd, by simpa only [Ideal.mem_comap, map_mul] using he⟩
abbrev CoeffPoly (a h : Shape) := MvPolynomial (PairSectionIndex (a.scale 6) (h.scale 6)) GeoField
abbrev IntegralForms (a h : Shape) := MvPolynomial (Generator a h) (CoeffPoly a h)
theorem modelRelations_fraction (surface : Ideal GeoJets) (a h : Shape) :
    modelRelations (Coeff a h) surface a h =
      (modelRelations (CoeffPoly a h) surface a h).map
        (algebraMap (IntegralForms a h) (BigradedPolynomial a h)) := by
  let P := CoeffPoly a h
  let F := Coeff a h
  let M := (nonZeroDivisors P).map (C (σ := Generator a h))
  let f := (model P a h).toRingHom
  have hC (p : P) : f (C p) = C p := by
    change model P a h (C p) = C p
    simp [model, MvPolynomial.algebraMap_eq]
  have hM : M.map f = (nonZeroDivisors P).map (C (σ := Target)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, (hC r).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨C r, ⟨r, hr, rfl⟩, hC r⟩
  have : IsLocalization (M.map f) (MvPolynomial Target F) := hM ▸ MvPolynomial.isLocalization _ _
  have hcomm := model_map (algebraMap P F) a h
  rw [modelRelations, ← targetIdeal_map (algebraMap P F)
    (IsScalarTower.algebraMap_eq GeoField P F).symm]
  exact comap_of_localization f (model F a h).toRingHom M hcomm.symm _
end
end K1_13_6_1_4_2_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_2_2_2
noncomputable section
open Algebra MvPolynomial
open scoped BigOperators
private theorem boundary_trdeg {k A E : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Field E] [Algebra k E]
    (hdim : trdeg k A ≤ 2) (b : A) (hb : b ≠ 0) (f : A →ₐ[k] E) (hfb : f b = 0) :
    trdeg k (A ⧸ RingHom.ker f) ≤ 1 := by
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  obtain ⟨d, hA, htA⟩ := K1_13_6_1_4_2_1_2_2.affineDimension k A
  obtain ⟨e, hQ, htQ⟩ := K1_13_6_1_4_2_1_2_2.affineDimension k (A ⧸ P)
  have hd : d ≤ 2 := by
    rw [htA] at hdim
    exact_mod_cast hdim
  have hbq : Ideal.Quotient.mk P b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hfb
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hb) hbq
  have hcast : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    simpa only [hQ, hA, Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one]
      using hdrop
  have hle : e + 1 ≤ d := by exact_mod_cast hcast
  have he : e ≤ 1 := by omega
  rw [htQ]
  exact_mod_cast he
private def blockLift {D I J : Type} [CommRing D] [Fintype I] [DecidableEq I]
    (i : I) (tag : {m : I // m ≠ i} → J) (w : I → D) (m : I) : MvPolynomial J D :=
  if hm : m ≠ i then MvPolynomial.X (tag ⟨m, hm⟩)
  else -∑ x, MvPolynomial.X (tag x) * C (w x)
private theorem eval_blockLift {D E I J : Type} [CommRing D] [CommRing E]
    [Fintype I] [DecidableEq I]
    (f : D →+* E) (z : J → E) (i : I) (tag : {m : I // m ≠ i} → J)
    (w : I → D) (p : I → E) (hw : f (w i) = 1)
    (hvar : ∀ x, z (tag x) = p x.val) (hz : (∑ m, p m * f (w m)) = 0)
    (m : I) : eval₂Hom f z (blockLift i tag w m) = p m := by
  by_cases hm : m ≠ i
  · rw [blockLift, dite_eq_left hm, eval₂Hom_X']
    exact hvar ⟨m, hm⟩
  · have heq : m = i := not_ne_iff.mp hm
    subst m
    rw [blockLift, dite_eq_right hm]
    simp only [map_neg, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, hvar]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hw, mul_one] at hz
    exact (eq_neg_of_add_eq_zero_left hz).symm
theorem proof : K1_13_6_1_4_2_1_2_2.c2 := by
  classical
  intro k A E σ τ _ _ _ _ _ _ _ _ _ t ht hd b hb f hfb i j u v hui hvj hu hv
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  let D := A ⧸ P
  let J := {m : σ // m ≠ i} ⊕ {m : τ // m ≠ j}
  let g : D →ₐ[k] E := Ideal.kerLiftAlg f
  let u' (m : σ) : D := Ideal.Quotient.mk P (u m)
  let v' (m : τ) : D := Ideal.Quotient.mk P (v m)
  let z : J → E := t ∘ Sum.map Subtype.val Subtype.val
  let ev : MvPolynomial J D →ₐ[k] E :=
    { eval₂Hom g.toRingHom z with
      commutes' := fun a => by
        change eval₂Hom g.toRingHom z (C (algebraMap k D a)) = _
        rw [eval₂Hom_C]
        exact g.commutes a }
  let s : σ ⊕ τ → MvPolynomial J D :=
    Sum.elim (blockLift i Sum.inl u') (blockLift j Sum.inr v')
  have hcomp : ev ∘ s = t := by
    funext l
    cases l with
    | inl m =>
      exact eval_blockLift g.toRingHom z i Sum.inl u' (fun x => t (Sum.inl x))
        (by change f (u i) = 1; rw [hui, map_one]) (fun _ => rfl) hu m
    | inr m =>
      exact eval_blockLift g.toRingHom z j Sum.inr v' (fun x => t (Sum.inr x))
        (by change f (v j) = 1; rw [hvj, map_one]) (fun _ => rfl) hv m
  have hs : AlgebraicIndependent k s :=
    AlgebraicIndependent.of_comp ev (hcomp.symm ▸ ht)
  have hD : trdeg k D ≤ 1 := boundary_trdeg hd b hb f hfb
  let : FaithfulSMul D (MvPolynomial J D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (C_injective J D)
  have hdim : trdeg k (MvPolynomial J D) = trdeg k D + Cardinal.mk J := by
    rw [← trdeg_add_eq k D (A := MvPolynomial J D), MvPolynomial.trdeg_of_isDomain,
      Cardinal.lift_id]
  have hle : Cardinal.mk (σ ⊕ τ) ≤ 1 + Cardinal.mk J := by
    refine hs.cardinalMk_le_trdeg.trans ?_
    rw [hdim]
    gcongr
  have hcard : Fintype.card (σ ⊕ τ) ≤ 1 + Fintype.card J := by
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
    exact_mod_cast hle
  have hσ := Fintype.card_congr (Equiv.optionSubtypeNe i)
  have hτ := Fintype.card_congr (Equiv.optionSubtypeNe j)
  simp only [Fintype.card_option] at hσ hτ
  simp only [J, Fintype.card_sum] at hcard
  omega
end
end K1_13_6_1_4_2_1_2_2_2
end
section
namespace K1_13_6_1_4_2_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h)
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∀ (x : latticeIndices a) (y : latticeIndices h) (p : BigradedPolynomial a h),
      p * rightForm a h ∈ firstCut surface a h →
      ∃ n : ℕ, chart x y ^ n * p ∈ firstCut surface a h
private theorem dehom_mul_left (surface : Ideal GeoJets) (a h : Shape)
    (p : BigradedPolynomial a h) :
    dehom surface a h (p * leftForm a h) =
      leftMul surface a h (dehom surface a h p) := by
  rw [map_mul, dehom_left, leftMul, LinearMap.mulLeft_apply]
  exact mul_comm (dehom surface a h p)
    (Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h))
private theorem dehom_mul_right (surface : Ideal GeoJets) (a h : Shape)
    (p : BigradedPolynomial a h) :
    dehom surface a h (p * rightForm a h) =
      rightMul surface a h (dehom surface a h p) := by
  rw [map_mul, dehom_right, rightMul, LinearMap.mulLeft_apply]
  exact mul_comm (dehom surface a h p)
    (Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h))
private theorem muls_commute (surface : Ideal GeoJets) (a h : Shape)
    (x : SurfaceRing surface a h) :
    rightMul surface a h (leftMul surface a h x) =
      leftMul surface a h (rightMul surface a h x) := by
  simp only [leftMul, rightMul, LinearMap.mulLeft_apply]
  exact mul_left_comm _ _ x
private theorem lift_piece (surface : Ideal GeoJets) {a h : Shape}
    (ha : FullChamber a) (hh : FullChamber h) {i j : ℕ}
    {w : SurfaceRing surface a h} (hw : w ∈ biPiece surface a h i j) :
    ∃ p : BigradedPolynomial a h, p ∈ grade (i, j) ∧ dehom surface a h p = w := by
  rw [← dehom_grade surface ha.1 hh.1] at hw
  exact hw
private theorem dehom_mem_piece (surface : Ideal GeoJets) {a h : Shape}
    (ha : FullChamber a) (hh : FullChamber h) {i j : ℕ}
    {p : BigradedPolynomial a h} (hp : p ∈ grade (i, j)) :
    dehom surface a h p ∈ biPiece surface a h i j := by
  rw [← dehom_grade surface ha.1 hh.1]
  exact ⟨p, hp, rfl⟩
private theorem firstCut_homogeneous (surface : Ideal GeoJets) (a h : Shape) :
    (firstCut surface a h).IsHomogeneous grade := by
  unfold firstCut
  apply (relations_homogeneous surface a h).sup
  apply Ideal.homogeneous_span
  rintro _ ⟨⟩
  exact ⟨(1, 0), leftForm_grade a h⟩
private theorem exists_high_intersection (h2 : c2) (surface : Ideal GeoJets) (a h : Shape)
    (hs : surface.IsPrime) (hd : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hh : FullChamber h) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h)) := by
  classical
  let : Fintype (latticeIndices a) := Fintype.ofFinite _
  let : Fintype (latticeIndices h) := Fintype.ofFinite _
  let I := firstCut surface a h
  let K := I.colon {rightForm a h}
  have hI := firstCut_homogeneous surface a h
  have hK : K.IsHomogeneous grade := homogeneous_colon hI (rightForm_grade a h)
  have hlocal (x : latticeIndices a) (y : latticeIndices h) (p : BigradedPolynomial a h)
      (hp : p ∈ K) : ∃ n : ℕ, chart x y ^ n * p ∈ I :=
    h2 surface a h hs hd ha hh x y p (Submodule.mem_colon_singleton.mp hp)
  obtain ⟨N, hN⟩ := high_degree_of_charts I K hK hlocal
  refine ⟨N, fun i j hi hj => le_antisymm ?_ ?_⟩
  · rintro w ⟨hw₁, hw₂⟩
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.mp hw₁
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hw₂
    obtain ⟨p, hp, hpu⟩ := lift_piece surface ha hh hu
    obtain ⟨q, hq, hqv⟩ := lift_piece surface ha hh hv
    have hpL : p * leftForm a h ∈ grade (i + 1, j + 1) :=
      IsWeightedHomogeneous.mul hp (leftForm_grade a h)
    have hqR : q * rightForm a h ∈ grade (i + 1, j + 1) :=
      IsWeightedHomogeneous.mul hq (rightForm_grade a h)
    have hsubloc : q * rightForm a h - p * leftForm a h ∈ relations surface a h := by
      have hgrade : q * rightForm a h - p * leftForm a h ∈ grade (i + 1, j + 1) :=
        Submodule.sub_mem (grade (k := Coeff a h) (α := latticeIndices a)
          (β := latticeIndices h) (i + 1, j + 1)) hqR hpL
      apply mem_relations_of_dehom_eq_zero hgrade
      rw [map_sub, dehom_mul_right, dehom_mul_left, hqv, hpu, hve, hue, sub_self]
    have hpLcut : p * leftForm a h ∈ I :=
      Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨p, rfl⟩)
    have hqK : q ∈ K := by
      apply Submodule.mem_colon_singleton.mpr
      change q * rightForm a h ∈ I
      rw [← sub_add_cancel (q * rightForm a h) (p * leftForm a h)]
      exact I.add_mem (Submodule.mem_sup_left hsubloc) hpLcut
    have hqI := hN (i + 1) j (hi.trans (Nat.le_succ i)) hj q hqK hq
    obtain ⟨r, hr, s, hspan, hsum⟩ := Submodule.mem_sup.mp hqI
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hspan
    let z := weightedHomogeneousComponent weight (i, j) t
    have hz : z ∈ grade (i, j) := weightedHomogeneousComponent_mem _ _ _
    have hcomp := congrArg (weightedHomogeneousComponent weight ((i, j) + (1, 0))) hsum
    have hq' : q ∈ grade ((i, j) + (1, 0)) := hq
    rw [map_add, component_mul (leftForm_grade a h),
      weightedHomogeneousComponent_eq_self hq'] at hcomp
    have hrel := weightedHomogeneousComponent_mem_of_mem _ _
      (relations_homogeneous surface a h) hr ((i, j) + (1, 0))
    have hdiv : leftMul surface a h (dehom surface a h z) = v := by
      have he := congrArg (dehom surface a h) hcomp
      rw [map_add, dehom_eq_zero_of_mem_relations hrel, zero_add, dehom_mul_left, hqv] at he
      exact he
    refine Submodule.mem_map.mpr ⟨dehom surface a h z, dehom_mem_piece surface ha hh hz, ?_⟩
    rw [LinearMap.comp_apply, ← hve, ← hdiv]
    exact (muls_commute surface a h _).symm
  · rintro w hw
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.mp hw
    obtain ⟨p, hp, hpu⟩ := lift_piece surface ha hh hu
    have hpL : p * leftForm a h ∈ grade (i + 1, j) :=
      IsWeightedHomogeneous.mul hp (leftForm_grade a h)
    have hpR : p * rightForm a h ∈ grade (i, j + 1) :=
      IsWeightedHomogeneous.mul hp (rightForm_grade a h)
    refine ⟨Submodule.mem_map.mpr ⟨_, dehom_mem_piece surface ha hh hpR, ?_⟩,
      Submodule.mem_map.mpr ⟨_, dehom_mem_piece surface ha hh hpL, ?_⟩⟩
    · rw [dehom_mul_right, hpu]
      exact hue
    · rw [dehom_mul_left, hpu, ← hue, LinearMap.comp_apply]
      exact muls_commute surface a h u
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1.c1 := by
  intro surface a h hs hd ha hh
  obtain ⟨hl, hr⟩ := h1 surface a h hs hd ha hh
  exact ⟨hl, hr, exists_high_intersection h2 surface a h hs hd ha hh⟩
end
end K1_13_6_1_4_2_1_1
end
section
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_2_1_1_2
noncomputable section
open K1_13 (Shape)
open K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_6_1_4_2_1 K1_13_6_1_4_2_1_1
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def coordinate {γ : Type} (b : Shape) (i : latticeIndices b → γ)
    (m : SectionIndex (b.scale 6)) : MvPolynomial γ GeoField :=
  if hm : m ∈ boxMonomials (b.scale 6) then
    MvPolynomial.X (i ⟨boxExponent m, boxExponent_mem b ⟨m, hm⟩⟩)
  else 0
private def integralForm {γ τ : Type} (b : Shape) (i : latticeIndices b → γ)
    (j : SectionIndex (b.scale 6) → τ) : MvPolynomial γ (MvPolynomial τ GeoField) :=
  ∑ m ∈ boxMonomials (b.scale 6), C (MvPolynomial.X (j m)) *
    MvPolynomial.map C (coordinate b i m)
private abbrev leftIntegral (a h : Shape) : IntegralForms a h := integralForm a Sum.inl Sum.inl
private abbrev rightIntegral (a h : Shape) : IntegralForms a h := integralForm h Sum.inr Sum.inr
private theorem integralForm_map {γ τ : Type} (b : Shape) (i : latticeIndices b → γ)
    (j : SectionIndex (b.scale 6) → τ) :
    let P := MvPolynomial τ GeoField
    let F := FractionRing P
    MvPolynomial.map (algebraMap P F) (integralForm b i j) =
      ∑ m ∈ (boxMonomials (b.scale 6)).attach,
        C (algebraMap P F (MvPolynomial.X (j m.val))) *
          MvPolynomial.X (i ⟨boxExponent m.val, boxExponent_mem b m⟩) := by
  dsimp only
  unfold integralForm
  rw [map_sum]
  rw [← Finset.sum_attach (boxMonomials (b.scale 6))]
  apply Finset.sum_congr rfl
  intro m _
  simp [coordinate, m.property]
private theorem coordinate_covers {γ : Type} (b : Shape) (i : latticeIndices b → γ)
    (y : latticeIndices b) : ∃ m ∈ boxMonomials (b.scale 6), coordinate b i m = MvPolynomial.X (i y) := by
  have hy : (fun j => y.val j) ∈ exponents (b.scale 6) := y.property
  rw [exponents_eq_image] at hy
  obtain ⟨m, hm, he⟩ := hy
  have hey : (⟨boxExponent m, boxExponent_mem b ⟨m, hm⟩⟩ : latticeIndices b) = y := by
    apply Subtype.ext
    ext j
    simpa [boxExponent] using congrFun he j
  have hm' : m ∈ boxMonomials (b.scale 6) := hm
  exact ⟨m, hm', by simp only [coordinate, dite_eq_left hm', hey]⟩
private theorem integral_cancel (surface : Ideal GeoJets) (a h : Shape)
    (x : latticeIndices a) (y : latticeIndices h) (p : IntegralForms a h)
    (hp : p * rightIntegral a h ∈
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h}) :
    ∃ n : ℕ, chart x y ^ n * p ∈
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h} := by
  let α := SectionIndex (a.scale 6)
  let β := SectionIndex (h.scale 6)
  let σ := Generator a h
  let J := modelRelations GeoField surface a h
  let Q := MvPolynomial σ GeoField ⧸ J
  let : CommRing Q := inferInstanceAs (CommRing (MvPolynomial σ GeoField ⧸ J))
  let q : MvPolynomial σ GeoField →+* Q := Ideal.Quotient.mk J
  let e := commAlgEquiv GeoField σ (α ⊕ β)
  let f := (MvPolynomial.map q).comp e.toRingHom
  let E := (renameEquiv Q (Equiv.sumComm α β)).trans (sumAlgEquiv Q β α)
  let g := E.toRingHom.comp f
  have hf : RingHom.ker f = modelRelations (CoeffPoly a h) surface a h := by
    change RingHom.ker ((MvPolynomial.map q).comp e.toRingHom) = _
    rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker,
      modelRelations_polynomial, ← commAlgEquiv_comp_map_C GeoField σ (α ⊕ β),
      ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  have hg : RingHom.ker g = modelRelations (CoeffPoly a h) surface a h := by
    rw [show g = E.toRingHom.comp f from rfl, ← hf]
    ext z
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change E (f z) = 0 ↔ f z = 0
    rw [← map_zero E]
    exact E.injective.eq_iff
  have hconst (v : MvPolynomial σ GeoField) :
      g (MvPolynomial.map C v) = C (C (q v)) := by
    change E (MvPolynomial.map q (e (MvPolynomial.map C v))) = _
    have hv := DFunLike.congr_fun (commAlgEquiv_comp_map_C GeoField σ (α ⊕ β)) v
    change e (MvPolynomial.map C v) = C v at hv
    rw [hv, MvPolynomial.map_C]
    simp [E, renameEquiv_apply, sumAlgEquiv_C_inl]
  have hleft (m : α) : g (C (MvPolynomial.X (Sum.inl m))) = C (MvPolynomial.X m) := by
    change E (MvPolynomial.map q (e (C (MvPolynomial.X (Sum.inl m))))) = _
    rw [commAlgEquiv_C_X, MvPolynomial.map_X]
    simp [E, renameEquiv_apply, sumAlgEquiv_X_inr]
  have hright (m : β) : g (C (MvPolynomial.X (Sum.inr m))) = MvPolynomial.X m := by
    change E (MvPolynomial.map q (e (C (MvPolynomial.X (Sum.inr m))))) = _
    rw [commAlgEquiv_C_X, MvPolynomial.map_X]
    simp [E, renameEquiv_apply, sumAlgEquiv_X_inl]
  let l : MvPolynomial α Q := ∑ m ∈ boxMonomials (a.scale 6),
    C (q (coordinate a Sum.inl m)) * MvPolynomial.X m
  let w : β → Q := fun m => q (coordinate h Sum.inr m)
  have hl : g (leftIntegral a h) = C l := by
    simp only [leftIntegral, integralForm, map_sum, map_mul, hleft, hconst, l]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hr : g (rightIntegral a h) = ∑ m ∈ boxMonomials (h.scale 6), C (C (w m)) * MvPolynomial.X m := by
    simp only [rightIntegral, integralForm, map_sum, map_mul, hright, hconst, w]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  obtain ⟨m, hm, he⟩ := coordinate_covers h (Sum.inr : latticeIndices h → σ) y
  have hchart : g (chart x y) = C (C (q (MvPolynomial.X (Sum.inl x)) * w m)) := by
    have hh := hconst (chart x y : MvPolynomial σ GeoField)
    simpa only [chart, map_mul, MvPolynomial.map_X, w, he] using hh
  have hsurj : Function.Surjective g :=
    E.surjective.comp ((MvPolynomial.map_surjective q Ideal.Quotient.mk_surjective).comp e.surjective)
  have hcut : (Ideal.span {C l}).comap g =
      modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h} := by
    rw [← hl, Ideal.comap_span_singleton_of_surjective g hsurj, hg]
  rw [← hcut, Ideal.mem_comap, map_mul, hr] at hp
  obtain ⟨n, hn⟩ := cancel_chart l _ w m hm (q (MvPolynomial.X (Sum.inl x))) (g p) hp
  refine ⟨n, ?_⟩
  rwa [← hcut, Ideal.mem_comap, map_mul, map_pow, hchart]
theorem proof : K1_13_6_1_4_2_1_1.c2 := by
  intro surface a h _ _ _ _ x y p hp
  let A := IntegralForms a h
  let B := BigradedPolynomial a h
  let M := (nonZeroDivisors (CoeffPoly a h)).map (C (σ := Generator a h))
  let g := algebraMap A B
  let I := modelRelations (CoeffPoly a h) surface a h ⊔ Ideal.span {leftIntegral a h}
  have : IsLocalization M B := MvPolynomial.isLocalization _ _
  have hl : g (leftIntegral a h) = leftForm a h := integralForm_map a Sum.inl Sum.inl
  have hr : g (rightIntegral a h) = rightForm a h := integralForm_map h Sum.inr Sum.inr
  have hz : g (chart x y) = chart x y := by
    change MvPolynomial.map (algebraMap (CoeffPoly a h) (Coeff a h)) (chart x y) = _
    simp [chart]
  have hI : I.map g = firstCut surface a h := by
    simp only [I, firstCut, Ideal.map_sup, Ideal.map_span, Set.image_singleton, hl,
      relations_eq_model, modelRelations_fraction, g]
    rfl
  have hreg : ∀ q : A, q * rightIntegral a h ∈ I → ∃ n : ℕ, chart x y ^ n * q ∈ I :=
    integral_cancel surface a h x y
  have hmem : p * g (rightIntegral a h) ∈ I.map g := by rwa [hr, hI]
  have hres : ∃ n : ℕ, g (chart x y) ^ n * p ∈ I.map g :=
    cancel_localization M I (chart x y) (rightIntegral a h) hreg p hmem
  rwa [hz, hI] at hres
end
end K1_13_6_1_4_2_1_1_2
end
section
namespace K1_13_2_3_6
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end
end K1_13_2_3_6
end
section
namespace K1_13_2_3_5
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open K1_13_2_3
open K1_13_2_3_5 (unpack)
end K1_13_2_3_5
end
section
namespace K1_13_2_3_4
open K1_13_2 K1_13_2_3
open scoped BigOperators
private theorem initial_eq (i : BlockIndex) :
    initialFlag i = windowFlag i.1.val i.2.val := by
  simp only [initialFlag, windowFlag, offset]
  congr 1 <;> ring
private theorem residual_cubic (F : Flag) (k : ℕ) :
    residualFlag F (Powers.expand ⟨0, 0, k⟩) = cubicFlag F k := by
  simp [residualFlag_expand, cubicFlag]
private theorem rank_window (i : BlockIndex) (hi : w1.Contains i) (p : Fin 11 → ℕ) :
    blockBound i p =
      (oldCount (initialFlag i) -
        max 0 (max (kernelLower (initialFlag i))
          (kernelLower (residualFlag (initialFlag i) p)))).toNat := by
  have hj := hi.2.2.2.1
  have hd := hi.2.2.2.2.2
  change i.2.val ≤ 1581 at hj
  change i.1.val + i.2.val ≤ 3070 at hd
  have ho : ¬ (initialFlag i).order ≤ 0 := by
    simp only [initialFlag, offset]
    omega
  have hu : min (initialFlag i).upper (2999 - offset i) = (initialFlag i).upper := by
    apply min_eq_left
    simp only [initialFlag, offset]
    omega
  have ha : { initialFlag i with upper := min (initialFlag i).upper (2999 - offset i) } =
      initialFlag i := by
    rw [hu]
  unfold blockBound
  dsimp only
  rw [ite_eq_right ho, ha, min_eq_right]
  exact sub_le_self _ (le_max_left _ _)
private theorem savings_eq (i : BlockIndex) (hi : w1.Contains i) (k : ℕ) :
    savings i ⟨0, 0, k⟩ = cubicSavings i.1.val i.2.val k := by
  by_cases hk : k = 0
  · subst k
    have hz : (Powers.expand ⟨0, 0, 0⟩) = fun _ => 0 := by
      ext i
      fin_cases i <;> rfl
    simp [savings, baseline, cubicSavings, hz]
  unfold savings baseline cubicSavings
  rw [ite_eq_right hk, rank_window i hi, rank_window i hi, residual_cubic]
  have hz : residualFlag (initialFlag i) (fun _ => 0) = initialFlag i := by
    cases initialFlag i
    simp [residualFlag]
  rw [hz, max_self, ← max_assoc, initial_eq]
private theorem rowSum_eq (s q code n : ℕ) :
    rowSum s q code n = ∑ j : Fin n, entry s (q + j.val) (rowPower code j.val) := by
  induction n generalizing q code with
  | zero => simp [rowSum]
  | succ n ih =>
    rw [rowSum, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.add_zero, rowPower, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show q + (j.val + 1) = q + 1 + j.val by omega]
private theorem rowsSum_eq (s : ℕ) (rows : List ℕ) :
    rowsSum s rows =
      ∑ r : Fin rows.length, ∑ q : Fin 71,
        entry (s + r.val) q.val (rowPower (rows[r.val]) q.val) := by
  induction rows generalizing s with
  | nil => simp [rowsSum]
  | cons code rows ih =>
    rw [rowsSum, rowSum_eq, ih]
    let f (r : Fin (rows.length + 1)) : ℕ :=
      ∑ q : Fin 71, entry (s + r.val) q.val (rowPower (code :: rows)[r.val] q.val)
    change _ = ∑ r, f r
    rw [Fin.sum_univ_succ f]
    simp only [f, Fin.val_zero, Nat.add_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ, Nat.zero_add, Nat.add_right_comm]
    simp only [Nat.add_assoc]
theorem rowsSum_append (s : ℕ) (a b : List ℕ) :
    rowsSum s (a ++ b) = rowsSum s a + rowsSum (s + a.length) b := by
  induction a generalizing s with
  | nil => simp [rowsSum]
  | cons code rows ih =>
    simp [rowsSum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
private def sample (n : ℕ) (hn : n ≤ 589) (a : Fin n × Fin 71) : BlockIndex :=
  (⟨1419 + a.1.val, by have h := a.1.isLt; omega⟩,
    ⟨3000 + a.2.val - (1419 + a.1.val), by have h := a.2.isLt; omega⟩)
private def sampleEmbedding (n : ℕ) (hn : n ≤ 589) : Fin n × Fin 71 ↪ BlockIndex where
  toFun := sample n hn
  inj' := by
    intro x y h
    have hs := congrArg (fun i : BlockIndex => i.1.val) h
    have hj := congrArg (fun i : BlockIndex => i.2.val) h
    change 1419 + x.1.val = 1419 + y.1.val at hs
    change 3000 + x.2.val - (1419 + x.1.val) =
      3000 + y.2.val - (1419 + y.1.val) at hj
    have hx := x.1.isLt
    have hy := y.1.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
private theorem entry_eq (n : ℕ) (hn : n ≤ 589) (r : Fin n) (q : Fin 71) (k : ℕ) :
    (if w1.Contains (sample n hn (r,q)) then savings (sample n hn (r,q)) ⟨0, 0, k⟩ else 0) =
      entry (1419 + r.val) q.val k := by
  have hr := r.isLt
  have hq := q.isLt
  have hw : w1.Contains (sample n hn (r,q)) ↔
      993 ≤ 3000 + q.val - (1419 + r.val) ∧ 3000 + q.val - (1419 + r.val) ≤ 1581 := by
    simp only [w1, Window.Contains, sample]
    omega
  unfold entry
  by_cases h : w1.Contains (sample n hn (r,q))
  · rw [ite_eq_left h, ite_eq_left (hw.mp h), savings_eq _ h]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun hj => h (hw.mpr hj))]
private theorem sum_le_univ {α β : Type} [Fintype α] [Fintype β]
    (f : α ↪ β) (v : β → ℕ) : (∑ a : α, v (f a)) ≤ ∑ b : β, v b := by
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
theorem rows_bound (rows : List ℕ) (hn : rows.length ≤ 589) :
    ∃ p : BlockIndex → Powers, rowsSum 1419 rows ≤ savingsSum w1 p := by
  let f := sampleEmbedding rows.length hn
  let small : Fin rows.length × Fin 71 → Powers :=
    fun a => ⟨0, 0, rowPower (rows[a.1.val]) a.2.val⟩
  let p := Function.extend f small (fun _ => ⟨0, 0, 0⟩)
  refine ⟨p, le_trans ?_ (sum_le_univ f
    (fun i => if w1.Contains i then savings i (p i) else 0))⟩
  rw [rowsSum_eq, ← Finset.univ_product_univ, Finset.sum_product]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  change entry (1419 + r.val) q.val (rowPower rows[r.val] q.val) =
    (if w1.Contains (f (r,q)) then savings (f (r,q)) (p (f (r,q))) else 0)
  rw [show p (f (r,q)) = small (r,q) from f.injective.extend_apply _ _ _]
  exact (entry_eq _ hn r q _).symm
end K1_13_2_3_4
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_1 K1_13_6
theorem factorial_cast_ne_zero {n : ℕ} (h : n < K1.p) : (n.factorial : Geom) ≠ 0 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro hz
  have hp := CharP.char_is_prime_of_two_le Geom K1.p (by decide)
  exact (not_le_of_gt h) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz))
private theorem topView_X (i : Fin 4) :
    topView (MvPolynomial.X i) =
      if h : i = 3 then Polynomial.X else Polynomial.C (MvPolynomial.X (i.castPred h)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    simp [topView, hlast, optionEquivLeft_X_none, show Fin.last 3 = (3 : Fin 4) by rfl]
  · have h : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
    simp [topView, optionEquivLeft_X_some, h]
theorem topView_separant (f : Row 4) :
    topView (separant f) = derivative (topView f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [separant, topView, optionEquivLeft_C]
  | add f g hf hg =>
    simp only [separant, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f i ih =>
    simp only [separant, pderiv_mul, map_add, map_mul] at ih ⊢
    rw [derivative_mul, ih, topView_X]
    by_cases h : i = 3
    · subst i
      simp
    · simp only [dite_eq_right h, pderiv_X_of_ne h, map_zero, derivative_C, mul_zero, add_zero]
def topAt (S : (Polynomial Geom)) (f : Row 4) : (Polynomial (Polynomial Geom)) :=
  (topView f).map (MvPolynomial.eval (jet S))
theorem eval_topAt (S : (Polynomial Geom)) (f : Row 4) :
    (topAt S f).eval (jet S (3 : Fin 4)) = atJet f S := by
  let e := (Polynomial.evalRingHom (jet S (3 : Fin 4))).comp
    ((Polynomial.mapRingHom (MvPolynomial.eval (jet S))).comp topView.toRingHom)
  change e f = (MvPolynomial.eval (jet S)) f
  have he : e = MvPolynomial.eval (jet S) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, topView, optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [e, topView_X, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [e, topView_X, show j.castSucc ≠ (3 : Fin 4) from Fin.castSucc_ne_last j, jet]
  rw [he]
theorem topAt_coeff (S : (Polynomial Geom)) (f : Row 4) :
    (topAt S f).coeff (shape f).t = topLead f S := by
  rw [topAt, Polynomial.coeff_map, ← eval_anchorLead, atJet, anchorLead,
    Polynomial.leadingCoeff, topView_degree]
theorem derivative_degree (f : Row 4) (j : ℕ) :
    (shape ((separant^[j]) f)).t ≤ (shape f).t - j := by
  rw [← topView_degree, ← topView_degree]
  have h : topView ((separant^[j]) f) = derivative^[j] (topView f) := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [Function.iterate_succ_apply', topView_separant, ih]
  rw [h]
  exact natDegree_iterate_derivative _ _
theorem derivative_in_box (f : Row 4) (j : ℕ) :
    InBox (shape ((separant^[j]) f)) (shape f) := by
  have h (w : Fin 4 → ℕ) :
      ((separant^[j]) f).weightedTotalDegree w ≤ f.weightedTotalDegree w := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', separant]
      exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
  exact ⟨by simpa only [shape, weightedTotalDegree_one] using h 1,
    by simpa only [shape, indexDegree_eq] using h Fin.val,
    (derivative_degree f j).trans (Nat.sub_le _ _)⟩
end
end K1_13_7_1
end
section
namespace K1_13_7
noncomputable section
open Polynomial K1_13
def RegularAt (f : Row 4) (S : (Polynomial Geom)) : Prop :=
  atJet (MvPolynomial.pderiv (3 : Fin 4) f) S ≠ 0
def LowerCaps (P : Row 3) (b j : ℕ) : Prop :=
  P.totalDegree ≤ b ∧ indexDegree P ≤ j
abbrev GenericX := FractionRing (Polynomial Geom)
abbrev GeometricX := AlgebraicClosure GenericX
abbrev Lower := MvPolynomial (Fin 3) GeometricX
abbrev LowerPoint := Fin 3 → GeometricX
abbrev genericCoeff : (Polynomial Geom) →+* GeometricX :=
  (algebraMap GenericX GeometricX).comp (algebraMap (Polynomial Geom) GenericX)
def genericRow (P : Row 3) : Lower := MvPolynomial.map genericCoeff P
def lowerPoint (S : (Polynomial Geom)) : LowerPoint :=
  fun i => genericCoeff (jet S i)
def ProperLowerPair (P Q : Row 3) : Prop :=
  P ≠ 0 ∧ Q ≠ 0 ∧ IsRelPrime (genericRow P) (genericRow Q)
def pointIdeal (y : LowerPoint) : Ideal Lower :=
  RingHom.ker (MvPolynomial.eval y)
def pairIdeal (P Q : Row 3) : Ideal Lower :=
  Ideal.span {genericRow P, genericRow Q}
def tripleIdeal (P Q R : Row 3) : Ideal Lower :=
  Ideal.span {genericRow P, genericRow Q, genericRow R}
def localColength (q : PrimeSpectrum Lower) (J : Ideal Lower) : ℕ∞ :=
  let A := Localization.AtPrime q.asIdeal
  Module.length A (A ⧸ J.map (algebraMap Lower A))
def HighCurve (P Q : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum Lower,
    q.asIdeal ∈ (pairIdeal P Q).minimalPrimes ∧ q.asIdeal.height = 2 ∧
      q.asIdeal ≤ pointIdeal y ∧
      293711590 ≤ localColength q (pairIdeal P Q) ∧
      localColength q (pairIdeal P Q) < ⊤
def IsolatedFat (P Q R : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum Lower,
    q.asIdeal = pointIdeal y ∧ q.asIdeal ∈ (tripleIdeal P Q R).minimalPrimes ∧
      (↑(41481 * (41481 - 33184 + 1) * 1037 : ℕ) : ℕ∞) ≤
        localColength q (tripleIdeal P Q R) ∧
      localColength q (tripleIdeal P Q R) < ⊤
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
def isolatedPrice : ℕ :=
  let q : Shape := ⟨952630000, 322000000, 0⟩
  ceilDiv (3 * q.j ^ 2 * (2 * q.b - q.j)) (4 * 41481 * (41481 - 33184 + 1) * 1037)
end
end K1_13_7
end
section
set_option autoImplicit false
namespace K1_13_7_6
noncomputable section
open K1_13_7 MvPolynomial
def cap (b j : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | e.degree ≤ b ∧ e 1 + 2 * e 2 ≤ j}
instance capFinite (b j : ℕ) : Finite (cap b j) :=
  ((Finsupp.finite_of_degree_le b).subset (fun _ h => h.1 :
    cap b j ⊆ {e | e.degree ≤ b})).to_subtype
abbrev totalCap : ℕ := 952630000
abbrev halfIndexCap : ℕ := 161000000
abbrev chartExponents := cap totalCap (2 * halfIndexCap)
abbrev chartMap := monomialMap GeometricX chartExponents
def chartDegree {σ : Type} [Finite σ]
    (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower) (p : PrimeSpectrum Lower) : ℚ :=
  affineDegree (p.asIdeal.comap φ)
def zeroPrime : PrimeSpectrum Lower := ⟨⊥, inferInstance⟩
def cutIdeal (p : PrimeSpectrum Lower) (f : Lower) : Ideal Lower :=
  p.asIdeal ⊔ Ideal.span {f}
def cutCost (D : PrimeSpectrum Lower → ℚ) (p : PrimeSpectrum Lower) (f : Lower)
    (qs : Finset (PrimeSpectrum Lower)) : ℚ :=
  ∑ q ∈ qs, (localColength q (cutIdeal p f)).toNat * D q
end
end K1_13_7_6
end
section
set_option autoImplicit false
namespace K1_13_7_6
noncomputable section
open MvPolynomial
private theorem degree_fin_three (e : Fin 3 →₀ ℕ) : e.degree = e 0 + e 1 + e 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
private def capFibers (b m : ℕ) (hb : 2 * m ≤ b) :
    cap b (2 * m) ≃ Σ z : Fin (m + 1),
      cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z)) where
  toFun e := by
    have htotal := e.property.1
    rw [degree_fin_three] at htotal
    have hindex := e.property.2
    let z : Fin (m + 1) := ⟨e.val 2, by omega⟩
    refine ⟨z, ⟨Finsupp.equivFunOnFinite.symm ![e.val 0, e.val 1], ?_⟩⟩
    rw [mem_cappedDegreeExponents, degree_fin_two]
    change e.val 0 + e.val 1 ≤ b - e.val 2 ∧ e.val 1 ≤ 2 * (m - e.val 2)
    omega
  invFun p := by
    obtain ⟨z, u⟩ := p
    have htotal := u.property.1
    rw [degree_fin_two] at htotal
    have hindex := u.property.2
    have hz := z.isLt
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val], ?_⟩
    change (Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val]).degree ≤ b ∧ _
    rw [degree_fin_three]
    change u.val 0 + u.val 1 + z.val ≤ b ∧ u.val 1 + 2 * z.val ≤ 2 * m
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, u⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
private theorem fiber_card (b m z : ℕ) (hb : 2 * m ≤ b) (hz : z ≤ m) :
    (cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z))).ncard =
      (2 * (m - z) + 1) * (b + 1 - m) := by
  have hc : 2 * (m - z) ≤ b - z := by omega
  have h := two_mul_ncard_cappedDegreeExponents_fin_two (b - z) (2 * (m - z)) hc
  have hfactor : 2 * (b - z) + 2 - 2 * (m - z) = (b + 1 - m) * 2 := by omega
  rw [hfactor, ← mul_assoc, ← mul_comm 2] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 2 by decide) h
private theorem sum_odd_reverse (m : ℕ) :
    (∑ z ∈ Finset.range (m + 1), (2 * (m - z) + 1)) = (m + 1) ^ 2 := by
  calc
    _ = ∑ z ∈ Finset.range (m + 1), (2 * z + 1) := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun z => 2 * z + 1) (m + 1)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        Nat.nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum, mul_comm 2, Finset.sum_range_id_mul_two]
      simp only [Nat.add_sub_cancel]
      ring
theorem cap_ncard (b m : ℕ) (hb : 2 * m ≤ b) :
    (cap b (2 * m)).ncard = (m + 1) ^ 2 * (b + 1 - m) := by
  classical
  let (z : Fin (m + 1)) : Fintype
      (cappedDegreeExponents (Fin 2) 1 (b - z) (2 * (m - z))) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_congr (capFibers b m hb), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  calc
    _ = ∑ z : Fin (m + 1), (2 * (m - z.val) + 1) * (b + 1 - m) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, fiber_card b m z hb (by omega)]
    _ = _ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun z => 2 * (m - z) + 1),
        sum_odd_reverse]
end
end K1_13_7_6
end
section
namespace K1_13_7_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_7
def liftLower (q : Row 3) : Row 4 := MvPolynomial.rename Fin.castSucc q
def lowerFlow (q : Row 3) : Row 4 := partialFlow (liftLower q)
structure LiftedSurface (f : Row 4) (q : Row 3) (surface : Ideal GeoJets) : Prop where
  minimal : (intersectionIdeal f (liftLower q)).IsMinimalPrime surface
  leading : toGeneric (liftLower (K1_13_1.anchorLead f)) ∉ surface
  regular : toGeneric (separant f) ∉ surface
structure ReducedCut (f : Row 4) (D q : Row 3) : Prop where
  ne_zero : q ≠ 0
  divides : q ∣ D
  caps : LowerCaps q 35007 12106
  reduced : Squarefree (genericRow q)
  proper : IsRelPrime (toGeneric f) (toGeneric (liftLower q))
  roots : ∀ S : (Polynomial Geom), atJet D S = 0 → atJet q S = 0
  flow_box : InBox (shape (lowerFlow q)) ⟨35007, 12107, 1⟩
  simple : ∀ surface, (h : LiftedSurface f q surface) → surface.height = 2 ∧
    cycleLength (intersectionIdeal f (liftLower q)) surface h.minimal.isPrime = 1
  invariant : ∀ surface, LiftedSurface f q surface → toGeneric (lowerFlow q) ∈ surface → Invariant f surface
def evalTrajectory {L : Type} [Field L] [Algebra Geom L] (P : Row 4) (S : (Polynomial L)) : (Polynomial L) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (algebraMap Geom L))
    (fun i => Polynomial.hasseDeriv i.val S) P
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ 133671 → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
def ProperMark (f : Row 4) (q : Row 3) (E : Row 4) (S : (Polynomial Geom)) : Prop :=
  ∃ surface, LiftedSurface f q surface ∧ surface ≤ markIdeal S ∧
    (toGeneric E ∉ surface ∨ toGeneric (lowerFlow q) ∉ surface)
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
def universalPolynomial : (Polynomial CoeffRing) :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val
def universalEval (f : Row 4) : (Polynomial CoeffRing) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f
def coefficientPointIdeal (S : (Polynomial Geom)) : Ideal CoeffRing :=
  RingHom.ker (MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val))
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
def IntegratedMark (f : Row 4) (S : (Polynomial Geom)) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S
def ThreefoldSections (Γ : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter (fun γ => (s γ).eval x = a)
    ∃ C : Pieces H, H ⊆ C.union ∧ C.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d
def ThreefoldPieces {Γ : Finset K} (C : Pieces Γ) (s : K → (Polynomial K)) : Prop :=
  ∀ i, ThreefoldSections (C.piece i) s (C.degree i)
end
end K1_13_7_2
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial K1_13 K1_13_7
open scoped BigOperators
def multiOrder (a : Fin 3 →₀ ℕ) : ℕ :=
  a.sum (fun _ k => k)
def hassePartial {A : Type*} [CommSemiring A]
    (a : Fin 3 →₀ ℕ) (F : MvPolynomial (Fin 3) A) : MvPolynomial (Fin 3) A :=
  ∑ m ∈ F.support,
    MvPolynomial.monomial (m - a) (F.coeff m * ∏ i : Fin 3, ((m i).choose (a i) : A))
def VanishesTo (q : PrimeSpectrum Lower) (F : Lower) (d : ℕ) : Prop :=
  let A := Localization.AtPrime q.asIdeal
  algebraMap Lower A F ∈ IsLocalRing.maximalIdeal A ^ d
end
end K1_13_7_4
end

end Merged6967_Fast056

section Merged6967_R6960Front6960ListRank
set_option Elab.async false








set_option Elab.async false

-- merged module R6960Front6960ListCells7
section Merged_R6960Front6960ListCells7

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_70_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(3, 0), (4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_70_1 : (CJ0.blockMatrix source 70 ((1 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_70_1) (Fast.bands [(0, 61, 10), (1, 62, 8), (2, 63, 6), (3, 64, 4), (4, 65, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_70_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3, 0), (3, 1), (3, 2), (4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833, 2130595889, 2130291329], [0, 0, 0, 0, 1176, 4464, 12690], [0, 0, 2130706385, 2130706341, 2130706257], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130688009, 2130602657], [0, 0, 0, 0, 0, 1128, 4277], [0, 0, 0, 2130706386, 2130706343], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130689137], [0, 0, 0, 0, 0, 0, 1081], [0, 0, 0, 0, 2130706387], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130122693], [0, 0, 0, 0, 0, 0, 32430], [0, 0, 0, 0, 2130705398], [], [1]]
  ]
private theorem cell_70_2 : (CJ0.blockMatrix source 70 ((2 : ℤ)-24)).rank ≤ 21 :=
  Fast.cell (z := matrix_70_2) (Fast.bands [(46, 46, 1), (47, 47, 2), (48, 48, 3), (49, 50, 3), (50, 52, 3), (51, 54, 3), (52, 56, 3), (53, 58, 3), (54, 60, 3), (55, 62, 3), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_70 (u : ℕ) : ℕ :=
  match u with
  | 1 => 18
  | 2 => 21
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact cell_70_1
  · exact cell_70_2
  · exact (block_rank_le 70 _).trans (rank_le_nominal 70 _)

theorem grade_70 : (∑ u ∈ Finset.range (81-70), (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank) ≤ 120 := by
  refine (Finset.sum_le_sum fun u _ => bound_70 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_70)]
  decide +kernel

private def matrix_71_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(4, 0)]
  vectors := [
    [[], [], [], [], [1]]
  ]
private theorem cell_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_71_0) (Fast.bands [(0, 62, 10), (1, 63, 8), (2, 64, 6), (3, 65, 4), (4, 66, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(3, 0), (4, 0), (5, 0), (6, 0), (8, 0), (10, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_71_1 : (CJ0.blockMatrix source 71 ((1 : ℤ)-24)).rank ≤ 16 :=
  Fast.cell (z := matrix_71_1) (Fast.bands [(0, 63, 9), (1, 64, 7), (2, 65, 5), (3, 66, 3), (4, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833, 2130595889], [0, 0, 0, 0, 1176, 4464], [0, 0, 2130706385, 2130706341], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130688009], [0, 0, 0, 0, 0, 1128], [0, 0, 0, 2130706386], [0, 1]]
  ]
private theorem cell_71_2 : (CJ0.blockMatrix source 71 ((2 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_71_2) (Fast.bands [(47, 47, 1), (48, 48, 2), (49, 49, 3), (50, 51, 3), (51, 53, 3), (52, 55, 3), (53, 57, 3), (54, 59, 3), (55, 61, 3), (56, 63, 3), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_71 (u : ℕ) : ℕ :=
  match u with
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact cell_71_0
  · exact cell_71_1
  · exact cell_71_2
  · exact (block_rank_le 71 _).trans (rank_le_nominal 71 _)

theorem grade_71 : (∑ u ∈ Finset.range (81-71), (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank) ≤ 94 := by
  refine (Finset.sum_le_sum fun u _ => bound_71 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_71)]
  decide +kernel

private def matrix_72_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(4, 0), (6, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]]
  ]
private theorem cell_72_0 : (CJ0.blockMatrix source 72 ((0 : ℤ)-24)).rank ≤ 9 :=
  Fast.cell (z := matrix_72_0) (Fast.bands [(0, 64, 9), (1, 65, 7), (2, 66, 5), (3, 67, 3), (4, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100, 14700, 37632], [0, 0, 2130706382, 2130706334, 2130706241, 2130706061], [1]],
    [[0, 0, 0, 0, 0, 1275, 4900, 14112], [0, 0, 0, 2130706383, 2130706336, 2130706245], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1225, 4704], [0, 0, 0, 0, 2130706384, 2130706338], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 1176], [0, 0, 0, 0, 0, 2130706385], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 39200, 223440], [0, 0, 0, 0, 2130705257, 2130701921], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 36848], [0, 0, 0, 0, 0, 2130705305], [], [0, 1]]
  ]
private theorem cell_72_1 : (CJ0.blockMatrix source 72 ((1 : ℤ)-24)).rank ≤ 14 :=
  Fast.cell (z := matrix_72_1) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 51, 2), (51, 53, 2), (52, 55, 2), (53, 57, 2), (54, 59, 2), (55, 61, 2), (56, 63, 2), (57, 65, 2), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833], [0, 0, 0, 0, 1176], [0, 0, 2130706385], [1]]
  ]
private theorem cell_72_2 : (CJ0.blockMatrix source 72 ((2 : ℤ)-24)).rank ≤ 15 :=
  Fast.cell (z := matrix_72_2) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 50, 3), (51, 52, 3), (52, 54, 3), (53, 56, 3), (54, 58, 3), (55, 60, 3), (56, 62, 3), (57, 64, 3), (58, 66, 3), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_72 (u : ℕ) : ℕ :=
  match u with
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 72 u

private theorem bound_72 (u : ℕ) :
    (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank ≤ allowance_72 u := by
  unfold allowance_72
  split
  · exact cell_72_0
  · exact cell_72_1
  · exact cell_72_2
  · exact (block_rank_le 72 _).trans (rank_le_nominal 72 _)

theorem grade_72 : (∑ u ∈ Finset.range (81-72), (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank) ≤ 72 := by
  refine (Finset.sum_le_sum fun u _ => bound_72 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_72)]
  decide +kernel

private def matrix_73_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_73_0 : (CJ0.blockMatrix source 73 ((0 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_73_0) (Fast.bands [(0, 66, 8), (1, 67, 6), (2, 68, 4), (3, 69, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_73_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2, 0), (2, 1), (2, 2), (3, 0)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100, 14700], [0, 0, 2130706382, 2130706334, 2130706241], [1]],
    [[0, 0, 0, 0, 0, 1275, 4900], [0, 0, 0, 2130706383, 2130706336], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1225], [0, 0, 0, 0, 2130706384], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 39200], [0, 0, 0, 0, 2130705257], [], [1]]
  ]
private theorem cell_73_1 : (CJ0.blockMatrix source 73 ((1 : ℤ)-24)).rank ≤ 12 :=
  Fast.cell (z := matrix_73_1) (Fast.bands [(49, 49, 1), (50, 50, 2), (51, 52, 2), (52, 54, 2), (53, 56, 2), (54, 58, 2), (55, 60, 2), (56, 62, 2), (57, 64, 2), (58, 66, 2), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_73 (u : ℕ) : ℕ :=
  match u with
  | 0 => 8
  | 1 => 12
  | u => nominal 73 u

private theorem bound_73 (u : ℕ) :
    (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank ≤ allowance_73 u := by
  unfold allowance_73
  split
  · exact cell_73_0
  · exact cell_73_1
  · exact (block_rank_le 73 _).trans (rank_le_nominal 73 _)

theorem grade_73 : (∑ u ∈ Finset.range (81-73), (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank) ≤ 54 := by
  refine (Finset.sum_le_sum fun u _ => bound_73 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_73)]
  decide +kernel

private def matrix_74_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(4, 0), (6, 0), (8, 0), (10, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_74_0 : (CJ0.blockMatrix source 74 ((0 : ℤ)-24)).rank ≤ 7 :=
  Fast.cell (z := matrix_74_0) (Fast.bands [(0, 68, 7), (1, 69, 5), (2, 70, 3), (3, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_74_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2, 0), (2, 1)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100], [0, 0, 2130706382, 2130706334], [1]],
    [[0, 0, 0, 0, 0, 1275], [0, 0, 0, 2130706383], [0, 1]]
  ]
private theorem cell_74_1 : (CJ0.blockMatrix source 74 ((1 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_74_1) (Fast.bands [(50, 50, 1), (51, 51, 2), (52, 53, 2), (53, 55, 2), (54, 57, 2), (55, 59, 2), (56, 61, 2), (57, 63, 2), (58, 65, 2), (59, 67, 2), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_74 (u : ℕ) : ℕ :=
  match u with
  | 0 => 7
  | 1 => 10
  | u => nominal 74 u

private theorem bound_74 (u : ℕ) :
    (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank ≤ allowance_74 u := by
  unfold allowance_74
  split
  · exact cell_74_0
  · exact cell_74_1
  · exact (block_rank_le 74 _).trans (rank_le_nominal 74 _)

theorem grade_74 : (∑ u ∈ Finset.range (81-74), (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank) ≤ 39 := by
  refine (Finset.sum_le_sum fun u _ => bound_74 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_74)]
  decide +kernel

private def matrix_75_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(4, 0), (6, 0), (8, 0), (10, 0), (12, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_75_0 : (CJ0.blockMatrix source 75 ((0 : ℤ)-24)).rank ≤ 6 :=
  Fast.cell (z := matrix_75_0) (Fast.bands [(0, 70, 6), (1, 71, 4), (2, 72, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_75_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2, 0)]
  vectors := [
    [[0, 0, 0, 0, 1326], [0, 0, 2130706382], [1]]
  ]
private theorem cell_75_1 : (CJ0.blockMatrix source 75 ((1 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_75_1) (Fast.bands [(51, 51, 1), (52, 52, 2), (53, 54, 2), (54, 56, 2), (55, 58, 2), (56, 60, 2), (57, 62, 2), (58, 64, 2), (59, 66, 2), (60, 68, 2), (61, 70, 2), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_75 (u : ℕ) : ℕ :=
  match u with
  | 0 => 6
  | 1 => 8
  | u => nominal 75 u

private theorem bound_75 (u : ℕ) :
    (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank ≤ allowance_75 u := by
  unfold allowance_75
  split
  · exact cell_75_0
  · exact cell_75_1
  · exact (block_rank_le 75 _).trans (rank_le_nominal 75 _)

theorem grade_75 : (∑ u ∈ Finset.range (81-75), (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank) ≤ 27 := by
  refine (Finset.sum_le_sum fun u _ => bound_75 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_75)]
  decide +kernel

private def matrix_76_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1, 0), (1, 1), (1, 2), (2, 0)]
  vectors := [
    [[0, 0, 2130706379, 2130706327, 2130706225], [1]],
    [[0, 0, 0, 2130706380, 2130706329], [0, 1]],
    [[0, 0, 0, 0, 2130706381], [0, 0, 1]],
    [[0, 0, 0, 0, 2130705107], [], [1]]
  ]
private theorem cell_76_0 : (CJ0.blockMatrix source 76 ((0 : ℤ)-24)).rank ≤ 5 :=
  Fast.cell (z := matrix_76_0) (Fast.bands [(52, 52, 1), (53, 54, 1), (54, 56, 1), (55, 58, 1), (56, 60, 1), (57, 62, 1), (58, 64, 1), (59, 66, 1), (60, 68, 1), (61, 70, 1), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_76 (u : ℕ) : ℕ :=
  match u with
  | 0 => 5
  | u => nominal 76 u

private theorem bound_76 (u : ℕ) :
    (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank ≤ allowance_76 u := by
  unfold allowance_76
  split
  · exact cell_76_0
  · exact (block_rank_le 76 _).trans (rank_le_nominal 76 _)

theorem grade_76 : (∑ u ∈ Finset.range (81-76), (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank) ≤ 18 := by
  refine (Finset.sum_le_sum fun u _ => bound_76 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_76)]
  decide +kernel

private def matrix_77_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1, 0), (1, 1)]
  vectors := [
    [[0, 0, 2130706379, 2130706327], [1]],
    [[0, 0, 0, 2130706380], [0, 1]]
  ]
private theorem cell_77_0 : (CJ0.blockMatrix source 77 ((0 : ℤ)-24)).rank ≤ 4 :=
  Fast.cell (z := matrix_77_0) (Fast.bands [(53, 53, 1), (54, 55, 1), (55, 57, 1), (56, 59, 1), (57, 61, 1), (58, 63, 1), (59, 65, 1), (60, 67, 1), (61, 69, 1), (62, 71, 1), (63, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_77 (u : ℕ) : ℕ :=
  match u with
  | 0 => 4
  | u => nominal 77 u

private theorem bound_77 (u : ℕ) :
    (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank ≤ allowance_77 u := by
  unfold allowance_77
  split
  · exact cell_77_0
  · exact (block_rank_le 77 _).trans (rank_le_nominal 77 _)

theorem grade_77 : (∑ u ∈ Finset.range (81-77), (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank) ≤ 11 := by
  refine (Finset.sum_le_sum fun u _ => bound_77 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_77)]
  decide +kernel

private def matrix_78_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1, 0)]
  vectors := [
    [[0, 0, 2130706379], [1]]
  ]
private theorem cell_78_0 : (CJ0.blockMatrix source 78 ((0 : ℤ)-24)).rank ≤ 3 :=
  Fast.cell (z := matrix_78_0) (Fast.bands [(54, 54, 1), (55, 56, 1), (56, 58, 1), (57, 60, 1), (58, 62, 1), (59, 64, 1), (60, 66, 1), (61, 68, 1), (62, 70, 1), (63, 72, 1), (64, 74, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_78 (u : ℕ) : ℕ :=
  match u with
  | 0 => 3
  | u => nominal 78 u

private theorem bound_78 (u : ℕ) :
    (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank ≤ allowance_78 u := by
  unfold allowance_78
  split
  · exact cell_78_0
  · exact (block_rank_le 78 _).trans (rank_le_nominal 78 _)

theorem grade_78 : (∑ u ∈ Finset.range (81-78), (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank) ≤ 6 := by
  refine (Finset.sum_le_sum fun u _ => bound_78 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_78)]
  decide +kernel

end Front6960ListBank

end Merged_R6960Front6960ListCells7

-- merged module R6960Front6960ListRank
section Merged_R6960Front6960ListRank

set_option Elab.async false

namespace Front6960ListBank
open scoped BigOperators

private def rankTable : List ℕ := [57, 168, 330, 540, 795, 1092, 1428, 1800, 2205, 2640, 3102, 3542, 3960, 4356, 4730, 5040, 5289, 5480, 5616, 5700, 5735, 5724, 5670, 5576, 5445, 5280, 5115, 4950, 4785, 4620, 4455, 4290, 4125, 3960, 3796, 3633, 3471, 3311, 3153, 2997, 2844, 2694, 2547, 2404, 2265, 2129, 1998, 1870, 1747, 1627, 1513, 1401, 1296, 1193, 1096, 1002, 914, 828, 749, 672, 601, 533, 471, 411, 358, 307, 262, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6]

private theorem grades (q : Fin 79) :
    (∑ u ∈ Finset.range (81-q.val), (CJ0.blockMatrix source q.val ((u : ℤ)-24)).rank) ≤
      rankTable[q.val]'(by simpa [rankTable] using q.isLt) := by
  fin_cases q
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67
  · exact grade_68
  · exact grade_69
  · exact grade_70
  · exact grade_71
  · exact grade_72
  · exact grade_73
  · exact grade_74
  · exact grade_75
  · exact grade_76
  · exact grade_77
  · exact grade_78

theorem prefix_bound : CJ0.prefixRank source 79 ≤ 184686 := by
  unfold CJ0.prefixRank
  change (∑ q ∈ Finset.range 79, ∑ u ∈ Finset.range (81-q),
    (CJ0.blockMatrix source q ((u : ℤ)-24)).rank) ≤ _
  rw [← Fin.sum_univ_eq_sum_range]
  apply (Finset.sum_le_sum fun q _ => grades q).trans_eq
  decide +kernel

#print axioms prefix_bound
end Front6960ListBank

end Merged_R6960Front6960ListRank

end Merged6967_R6960Front6960ListRank

section Merged6967_R6960MarkedRoot
set_option Elab.async false




set_option Elab.async false

-- merged module R6960BranchCollisions
section Merged_R6960BranchCollisions
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Lower6960.BranchCollisions
open Polynomial Finset
open ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open CurvatureSquares (mulBox)
open scoped Polynomial BigOperators
variable {K : Type} [Field K] [DecidableEq K]
omit [DecidableEq K] in
theorem divisor_corank {f g d : (Polynomial K)} {m n : ℕ}
    (hf : f≠0) (df : d∣f) (dg : d∣g) (fm : f.natDegree≤m) (gn : g.natDegree≤n) :
    d.natDegree≤m+n-(sylvester f g m n).rank := by
  obtain ⟨a,fa⟩ := df
  obtain ⟨b,gb⟩ := dg
  have prod : d*a≠0 := fa ▸ hf
  have dn := left_ne_zero_of_mul prod
  have an := right_ne_zero_of_mul prod
  have afit : a.natDegree+d.natDegree≤m := by
    rw [Nat.add_comm,←natDegree_mul dn an,←fa]; exact fm
  let U := mulBox (L:=K) a d.natDegree m (fun _=>afit)
  have bfit (hb : (-b)≠0) : (-b).natDegree+d.natDegree≤n := by
    have bn : b≠0 := fun hz=>hb (by simp [hz])
    rw [gb,natDegree_mul dn bn] at gn
    rw [natDegree_neg]; omega
  let V := mulBox (L:=K) (-b) d.natDegree n bfit
  let S := sylvesterMap f g fm gn
  let B := U.prod V
  have ker (u : degreeLT K d.natDegree) : B u∈LinearMap.ker S := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f*(-b*(u:(Polynomial K)))+g*(a*(u:(Polynomial K)))=0
    rw [fa,gb]; ring
  let L := B.codRestrict (LinearMap.ker S) ker
  have inj : Function.Injective L := by
    intro x y eq
    apply Subtype.ext
    exact mul_left_cancel₀ an (congrArg (fun v : LinearMap.ker S=>(v.val.1 : (Polynomial K))) eq)
  let := Module.Finite.of_basis (degreeLT.basis K m)
  let := Module.Finite.of_basis (degreeLT.basis K n)
  have h := LinearMap.finrank_le_finrank_of_injective (f:=L) inj
  have dim (t : ℕ) : Module.finrank K (degreeLT K t)=t := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K t)
  rw [dim] at h
  have rank := S.finrank_range_add_finrank_ker
  rw [Module.finrank_prod,dim,dim] at rank
  have eq : (sylvester f g m n).rank=Module.finrank K (LinearMap.range S) := by
    let dom := ((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv
    rw [Matrix.rank_eq_finrank_range_toLin _ (degreeLT.basis K _) dom,
      ←toMatrix_sylvesterMap' f g fm gn, Matrix.toLin_toMatrix]
  rw [eq]; omega
def collisionMass (f branch : (Polynomial K)) (points : Finset K) : ℕ :=
  ∑ x ∈ points, if 2≤branch.rootMultiplicity x then f.rootMultiplicity x else 0
theorem collision_le_twice_gcd {f branch : (Polynomial K)} (nonzero : branch≠0)
    (divisor : f∣branch) (points : Finset K) :
    collisionMass f branch points ≤ 2*(gcd f branch.derivative).natDegree := by
  have fn : f≠0 := fun z=>nonzero (zero_dvd_iff.mp (z ▸ divisor))
  have gn : gcd f branch.derivative≠0 := fun z=>fn (zero_dvd_iff.mp (z ▸ gcd_dvd_left f branch.derivative))
  apply le_trans _ (Nat.mul_le_mul_left 2
    (sum_rootMultiplicity_le_natDegree (gcd f branch.derivative) points))
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · let k := min (f.rootMultiplicity x) (branch.rootMultiplicity x-1)
    have kf : ((Polynomial.X : (Polynomial K))-C x)^k∣f := (le_rootMultiplicity_iff fn).mp (min_le_left ..)
    have kb : ((Polynomial.X : (Polynomial K))-C x)^k∣branch.derivative :=
      (pow_dvd_pow _ (min_le_right ..)).trans
        (pow_sub_one_dvd_derivative_of_pow_dvd (branch.pow_rootMultiplicity_dvd x))
    have lower : k≤(gcd f branch.derivative).rootMultiplicity x :=
      (le_rootMultiplicity_iff gn).mpr (dvd_gcd kf kb)
    have hle : f.rootMultiplicity x≤branch.rootMultiplicity x :=
      (le_rootMultiplicity_iff nonzero).mpr ((f.pow_rootMultiplicity_dvd x).trans divisor)
    dsimp [k] at lower
    omega
  · omega
theorem stratum {F B : Polynomial (Polynomial K)} (divisor : F∣B)
    (T : Finset K) (places : K→Finset K)
    (good : ∀z∈T,B.map (evalRingHom z)≠0)
    (sep : F.resultant B.derivative F.natDegree (B.natDegree-1)≠0)
    {u v : ℕ} (fu : ∀ j,(F.coeff j).natDegree≤u) (bv : ∀ j,(B.coeff j).natDegree≤v) :
    (∑ z∈T, collisionMass (F.map (evalRingHom z)) (B.map (evalRingHom z)) (places z)) ≤
      2*((B.natDegree-1)*u+F.natDegree*v) := by
  have point (z : K) (hz : z∈T) := good z hz
  have single (z : K) (hz : z∈T) := collision_le_twice_gcd (point z hz)
    (map_dvd (mapRingHom (evalRingHom z)) divisor) (places z)
  have per (z : K) (hz : z∈T) : collisionMass (F.map (evalRingHom z)) (B.map (evalRingHom z)) (places z)
      ≤ 2*(F.natDegree+(B.natDegree-1) -
        (sylvester (F.map (evalRingHom z)) (B.derivative.map (evalRingHom z)) F.natDegree (B.natDegree-1)).rank) := by
    have d := single z hz
    change collisionMass (F.map _) (B.map _) _ ≤ 2*(gcd (F.map _) (B.map _).derivative).natDegree at d
    rw [derivative_map] at d
    have fn : F.map (evalRingHom z)≠0 := by
      intro eq
      apply point z hz
      obtain ⟨a,ha⟩ := divisor
      simp [ha,eq,Polynomial.map_mul]
    exact d.trans (Nat.mul_le_mul_left 2 (divisor_corank fn (gcd_dvd_left ..) (gcd_dvd_right ..)
      natDegree_map_le (natDegree_map_le.trans (natDegree_derivative_le _))))
  have total := sum_le_sum per
  rw [←mul_sum] at total
  have cor := sum_sylvester_coranks_le_resultant_natDegree F B.derivative F.natDegree (B.natDegree-1) T sep
  have fee := natDegree_resultant_le_of_coeff_natDegree_le F B.derivative F.natDegree (B.natDegree-1) u v fu
    (fun j=>by rw [coeff_derivative,mul_comm,show ((j:(Polynomial K))+1)=C ((j:K)+1) by simp]
               exact (natDegree_C_mul_le ..).trans (bv _))
  exact total.trans (Nat.mul_le_mul_left 2 (cor.trans fee))
#print axioms stratum
omit [DecidableEq K] in
private theorem nonzero_resultant {F B : Polynomial (Polynomial K)} (dvd : F∣B)
    (sep : (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable) :
    F.resultant B.derivative F.natDegree (B.natDegree-1)≠0 := by
  let a:=algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have inj : Function.Injective a := IsFractionRing.injective _ _
  have hf : F.map a≠0 := fun hz=>sep.ne_zero (zero_dvd_iff.mp (by
    have h := Polynomial.map_dvd a dvd
    rwa [hz] at h))
  have cop : IsCoprime (F.map a) (B.derivative.map a) := by
    rw [←derivative_map]
    exact (show IsCoprime (B.map a) (B.map a).derivative from sep).of_isCoprime_of_dvd_left
      (Polynomial.map_dvd a dvd)
  have actual := resultant_ne_zero (F.map a) (B.derivative.map a) cop
  have bound := natDegree_derivative_le B
  have padded : (F.map a).resultant (B.derivative.map a) F.natDegree (B.natDegree-1) ≠ 0 := by
    rw [←Nat.add_sub_of_le bound,←natDegree_map_eq_of_injective inj B.derivative,
      ←natDegree_map_eq_of_injective inj F,
      resultant_add_right_deg _ _ _ _ _ le_rfl,coeff_natDegree]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf)) actual
  rw [resultant_map_map] at padded
  exact fun hz=>padded (by rw [hz,map_zero])
theorem weighted {ι : Type*} [Fintype ι] (F : ι→Polynomial (Polynomial K)) (w : ι→ℕ)
    (positive : ∀ i, 0<w i) (B : Polynomial (Polynomial K)) (prod : B=∏i,F i)
    (sep : (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable)
    (T : Finset K) (places : K→Finset K) (good : ∀ z∈T,B.map (evalRingHom z)≠0)
    {s t : ℕ} (xcap : (∑ i,w i*(F i).natDegree)≤2*s)
    (zcap : (∑ i,w i*CurvatureSquares.height (F i))≤2*t) :
    (∑ i,w i*(∑ z∈T,collisionMass ((F i).map (evalRingHom z)) (B.map (evalRingHom z)) (places z)))
       ≤ 16*s*t := by
  classical
  let u := ∑i,CurvatureSquares.height (F i)
  have xsum : (∑ i,(F i).natDegree)≤2*s :=
    (sum_le_sum (fun i _=>Nat.le_mul_of_pos_left _ (positive i))).trans xcap
  have bcap : B.natDegree≤2*s := by rw [prod]; exact (natDegree_prod_le ..).trans xsum
  have ucap : u≤2*t :=
    (sum_le_sum (fun i _=>Nat.le_mul_of_pos_left _ (positive i))).trans zcap
  have total : CurvatureSquares.height B≤u := by
    dsimp only [CurvatureSquares.height,u]
    rw [prod,map_prod]
    exact natDegree_prod_le ..
  let v := fun i=>CurvatureSquares.height (F i)
  have calc1 (i : ι) : (∑ z∈T,collisionMass ((F i).map (evalRingHom z)) (B.map (evalRingHom z)) (places z))
        ≤ 2*((B.natDegree-1)*v i+(F i).natDegree*u) := by
    have div : F i∣B := prod ▸ dvd_prod_of_mem F (mem_univ i)
    exact stratum div T places good (nonzero_resultant div sep)
      (CurvatureSquares.coeff_height (F i)) (fun j=>(CurvatureSquares.coeff_height B j).trans total)
  calc _ ≤ ∑ i,w i*(2*((B.natDegree-1)*v i+(F i).natDegree*u)) :=
             sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (calc1 i))
       _ = ∑ i, ((2*(B.natDegree-1))*(w i*v i)+(2*u)*(w i*(F i).natDegree)) := by
             apply sum_congr rfl; intro i _; ring
       _ = 2*(B.natDegree-1)*(∑i,w i*v i)+2*u*(∑i,w i*(F i).natDegree) := by
             rw [sum_add_distrib,←mul_sum,←mul_sum]
       _ ≤ (2*(2*s))*(2*t)+(2*(2*t))*(2*s) :=
             Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) zcap)
               (Nat.mul_le_mul (Nat.mul_le_mul_left _ ucap) xcap)
       _ = 16*s*t := by ring
#print axioms weighted
omit [DecidableEq K] in
theorem tame_separable (p : ℕ) [CharP (FractionRing (Polynomial K)) p]
    {B : Polynomial (Polynomial K)} (sf : Squarefree B) (small : B.natDegree<p) :
    (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable := by
  let a:=algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have inj : Function.Injective a := IsFractionRing.injective _ _
  apply CurvatureSquares.separable_kernel B sf
  intro q _ div pos
  have bound := (natDegree_le_of_dvd div sf.ne_zero).trans_lt small
  have degree := natDegree_map_eq_of_injective inj q
  have ne := CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char p (q.map a)
    (by simpa only [degree] using pos) (by simpa only [degree] using bound)
  intro h
  exact ne (by rw [derivative_map,h,Polynomial.map_zero])
#print axioms tame_separable
end Lower6960.BranchCollisions

end
end Merged_R6960BranchCollisions

-- merged module R6960MarkedRoot
section Merged_R6960MarkedRoot
noncomputable section
set_option Elab.async false
namespace Lower6960.MarkedRoot
open Polynomial Finset
open scoped Polynomial
variable {K : Type} [Field K] [DecidableEq K]
theorem sheet {F : (Polynomial K)} (degree : 2≤F.natDegree) (y : K) (root : F.eval y=0)
    (simple : F.derivative.eval y≠0) :
    ∃ H Q : (Polynomial K),F=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      let e:=AdjoinRoot.mk F H
      e^2=e ∧ e≠0 ∧ e≠1 := by
  have fn : F≠0 := by intro eq; simp [eq] at degree
  obtain ⟨Q,eq⟩ := dvd_iff_isRoot.mpr root
  have qn : Q≠0 := fun h=>fn (by rw [eq,h,mul_zero])
  have qdeg : F.natDegree=1+Q.natDegree := by
    rw [eq,natDegree_mul (X_sub_C_ne_zero _) qn,natDegree_X_sub_C]
  have qy : Q.eval y≠0 := by
    rw [eq,derivative_mul] at simple
    simpa using simple
  let H:=C (Q.eval y)⁻¹*Q
  have value : H.eval y=1 := by simp [H,qy]
  have hd : H.natDegree=Q.natDegree := natDegree_C_mul (inv_ne_zero qy)
  have hn : H≠0 := by intro h; simp [h] at value
  have div : Polynomial.X-C y∣H-1 := dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,value])
  obtain ⟨G,fac⟩ := div
  have rel : F∣H*(H-1) := by
    refine ⟨C (Q.eval y)⁻¹*G,?_⟩
    rw [fac,eq]; unfold H; ring
  let e:=AdjoinRoot.mk F H
  have idemp : e^2=e := by
    have zero := AdjoinRoot.mk_eq_zero.mpr rel
    rw [map_mul,map_sub,map_one] at zero
    change e*(e-1)=0 at zero
    linear_combination zero
  refine ⟨H,Q,eq,value,dvd_mul_left ..,idemp,?_,?_⟩
  · intro zero
    have h := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp zero) hn
    omega
  · intro one
    have zero : AdjoinRoot.mk F (H-1)=0 := by rw [map_sub,map_one,one,sub_self]
    have dv := AdjoinRoot.mk_eq_zero.mp zero
    by_cases h : H-1=0
    · have he := sub_eq_zero.mp h
      rw [he,natDegree_one] at hd; omega
    · have hle := natDegree_le_of_dvd dv h
      have upper := natDegree_sub_le H 1
      rw [natDegree_one,_root_.max_zero] at upper; omega
theorem good_marks (F : Polynomial (Polynomial K)) (p : ℕ) [CharP (FractionRing (Polynomial K)) p]
    (ir : Irreducible F) (large : 2≤F.natDegree) (tame : F.natDegree<p)
    (v : ℕ) (seed : ∀j,(F.coeff j).natDegree≤v)
    (T : Finset K) (word : K→K) (root : ∀z∈T,(F.map (evalRingHom z)).eval (word z)=0) :
    ∃ bad ⊆ T, bad.card≤(2*F.natDegree-1)*v ∧
      ∀ z∈T, z∉bad → let f:=F.map (evalRingHom z)
        f.natDegree=F.natDegree ∧ f.Separable ∧
        ∃ H Q : (Polynomial K), f=(Polynomial.X-C (word z))*Q ∧ H.eval (word z)=1 ∧ Q∣H ∧
          let e:=AdjoinRoot.mk f H
          e^2=e ∧ e≠0 ∧ e≠1 := by
  classical
  let R:=F.resultant F.derivative F.natDegree (F.natDegree-1)
  have rn : R≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField F
    (BranchCollisions.tame_separable p ir.squarefree tame)
  have deg := natDegree_resultant_le_of_coeff_natDegree_le F F.derivative F.natDegree
    (F.natDegree-1) v v seed (fun j=>by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial K))+1)=C ((j:K)+1) by simp]
      exact (natDegree_C_mul_le _ _).trans (seed _))
  let bad:=T.filter fun z=>R.eval z=0
  have incl : bad⊆R.roots.toFinset := fun z hz => Multiset.mem_toFinset.mpr
    ((mem_roots rn).mpr (mem_filter.mp hz).2)
  refine ⟨bad,filter_subset _ _,?_,?_⟩
  · refine ((card_le_card incl).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))).trans ?_
    exact deg.trans_eq (by rw [←Nat.add_mul]; congr 1; omega)
  · intro z hz keep
    have unit : (evalRingHom z) R≠0 := fun h=>keep (mem_filter.mpr ⟨hz,h⟩)
    have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl unit
    have sep := separable_map_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl (by omega) unit
    exact ⟨full,sep,sheet (full ▸ large) (word z) (root z hz)
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
        le_rfl (by omega) unit (word z) (root z hz))⟩
#print axioms good_marks
end Lower6960.MarkedRoot

end
end Merged_R6960MarkedRoot

end Merged6967_R6960MarkedRoot

section Merged6967_R6960MarkedSheet
set_option Elab.async false




set_option Elab.async false

-- merged module R6960CubicOdd
section Merged_R6960CubicOdd
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Lower6960.CubicOdd
open Polynomial Finset CurvatureSquares ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators Polynomial
def disc {R : Type*} [CommRing R] (a b c d : R) : R :=
  b^2*c^2-4*a*c^3-4*b^3*d-27*a^2*d^2+18*a*b*c*d
theorem disc_at_root {R : Type*} [CommRing R] (a b c d s : R)
    (root : a*s^3+b*s^2+c*s+d=0) :
    disc a b c d=((b+a*s)^2-4*a*(c+(b+a*s)*s))*(a*s^2+(b+a*s)*s+(c+(b+a*s)*s))^2 := by
  have eq : d=-(a*s^3+b*s^2+c*s) := by linear_combination root
  rw [eq]; unfold disc; ring
variable {L : Type} [Field L]
theorem complement_degree (a b c s : (Polynomial L)) {W d : ℕ} (room : 3*d≤W)
    (sa : a.natDegree≤W-3*d) (sb : b.natDegree≤W-2*d)
    (sc : c.natDegree≤W-d) (ss : s.natDegree≤d) :
    ((b+a*s)^2-4*a*(c+(b+a*s)*s)).natDegree ≤ 2*W-4*d := by
  have q1 : (b+a*s).natDegree≤W-2*d := (natDegree_add_le ..).trans
    (max_le sb ((natDegree_mul_le ..).trans (by omega)))
  have q0 : (c+(b+a*s)*s).natDegree≤W-d := (natDegree_add_le ..).trans
    (max_le sc ((natDegree_mul_le ..).trans (by omega)))
  apply (natDegree_sub_le ..).trans (max_le ?_ ?_)
  · rw [natDegree_pow]; omega
  · have const : (4*a).natDegree ≤ a.natDegree := natDegree_C_mul_le (4:L) a
    exact (natDegree_mul_le ..).trans (by omega)
variable [DecidableEq L]
theorem cancel_squares (H G R D : (Polynomial L)) (hn : H≠0) (eqn : H^2*G=R^2*D) :
    ∃ h t : (Polynomial L), G=h^2*t ∧ t.natDegree≤D.natDegree := by
  by_cases rn : R=0
  · have z : G=0 := by simpa [rn,hn] using eqn
    exact ⟨0,0,by simp [z],by simp⟩
  let l := GCDMonoid.gcd R H
  let u := R/l
  let v := H/l
  have ln : l≠0 := gcd_ne_zero_of_right hn
  have hu : l*u=R := EuclideanDomain.mul_div_cancel' ln (gcd_dvd_left _ _)
  have hv : l*v=H := EuclideanDomain.mul_div_cancel' ln (gcd_dvd_right _ _)
  have un : u≠0 := left_div_gcd_ne_zero rn
  have red : v^2*G=u^2*D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ln)
    simpa only [←mul_assoc,←mul_pow,hu,hv] using (show (l*v)^2*G=(l*u)^2*D by rw [hu,hv]; exact eqn)
  have cop : IsCoprime u v := isCoprime_div_gcd_div_gcd hn
  obtain ⟨t,ht⟩ := (cop.pow (m:=2) (n:=2)).dvd_of_dvd_mul_left (show u^2∣v^2*G from ⟨D,red⟩)
  have dt : D=v^2*t := by
    apply mul_left_cancel₀ (pow_ne_zero 2 un)
    calc u^2*D = v^2*G := red.symm
         _ = u^2*(v^2*t) := by rw [ht]; ring
  refine ⟨u,t,ht,?_⟩
  by_cases tn : t=0
  · simp [tn]
  · have vn : v≠0 := right_div_gcd_ne_zero hn
    rw [dt,natDegree_mul (pow_ne_zero _ vn) tn]
    omega
theorem marked_corank (Q : Polynomial (Polynomial L)) {r v t : ℕ} (hr : 0<r) (deg : Q.natDegree≤r)
    (seed : ∀ i,(Q.coeff i).natDegree≤v)
    (sep : Q.resultant Q.derivative r (r-1)≠0) (T : Finset L)
    (marks : ∀ z∈T, ∃ h a : (Polynomial L), Q.map (evalRingHom z)=h^2*a ∧ a.natDegree≤t) :
    T.card*((r-t+1)/2) ≤ (2*r-1)*v := by
  have each (z) (hz : z∈T) : (r-t+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,a,eq,da⟩:=marks z hz
    have fit : (h^2*a).natDegree≤r := by rw [←eq]; exact natDegree_map_le.trans deg
    rw [←derivative_map,eq]
    exact CurvatureSquares.cofactor_corank (L:=L) (r:=r) (e:=t) h a hr da fit
  have bound:=Finset.sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at bound
  have fee:=Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed (fun i=>by
    rw [coeff_derivative,mul_comm,show ((i:(Polynomial L))+1)=C ((i:L)+1) by simp]
    exact (natDegree_C_mul_le ..).trans (seed _))
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have sum_fee : T.card*((r-t+1)/2) ≤ r*v+(r-1)*v :=
    (bound.trans upper).trans (fee.trans_eq (Nat.add_comm ..))
  calc _ ≤ _ := sum_fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega
theorem first_band (r v marks : ℕ) (large : 278868≤r)
    (count : marks*((r-278468+1)/2)≤(2*r-1)*(4*v)) : marks+4*v≤11200*v := by
  let k := (r-278468+1)/2
  have pos : 0<k := by dsimp [k]; omega
  have rate : (2*r-1)*4≤11196*k := by dsimp [k]; omega
  have cap : marks*k≤(11196*v)*k := calc
    _ ≤ (2*r-1)*(4*v) := count
    _ = ((2*r-1)*4)*v := by ring
    _ ≤ (11196*k)*v := Nat.mul_le_mul_right v rate
    _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right cap pos
  omega
private abbrev sp (z : L) := Polynomial.mapRingHom (evalRingHom z)
open CurvatureSquares (root_count)
theorem high_odd_cubics (A B C₁ D H G : Polynomial (Polynomial L)) (c : (Polynomial L)) (r v : ℕ)
    (factor : disc A B C₁ D=Polynomial.C c*H^2*G)
    (large : 278868≤r) (height : G.natDegree≤r)
    (seed : ∀ j,(G.coeff j).natDegree≤4*v)
    (sep : G.resultant G.derivative r (r-1)≠0)
    (j : ℕ) (proper : (disc A B C₁ D).coeff j≠0) (price : ((disc A B C₁ D).coeff j).natDegree≤4*v)
    (degrees : A.natDegree≤406446-3*133606 ∧ B.natDegree≤406446-2*133606 ∧ C₁.natDegree≤406446-133606)
    (T : Finset L) (words : ∀ z∈T,∃ s : (Polynomial L),s.natDegree≤133606 ∧
      sp z A*s^3+sp z B*s^2+sp z C₁*s+sp z D=0) :
    T.card≤11200*v := by
  classical
  let bad := T.filter (fun z => ((disc A B C₁ D).coeff j).eval z=0)
  have ex : bad.card≤4*v := (root_count (S:=bad) (z:=id) (fun _ _ _ _ h=>h)
    ((disc A B C₁ D).coeff j) proper (fun z hz=> (mem_filter.mp hz).2)).trans price
  have marks (z) (hz : z∈T \ bad) : ∃ h t : (Polynomial L),
      G.map (evalRingHom z)=h^2*t ∧ t.natDegree≤278468 := by
    obtain ⟨mem,nb⟩:=mem_sdiff.mp hz
    obtain ⟨s,ds,root⟩:=words z mem
    have nonzero : sp z (disc A B C₁ D) ≠ 0 := by
      intro eq
      apply nb
      apply mem_filter.mpr ⟨mem,?_⟩
      change (disc A B C₁ D).map (evalRingHom z)=0 at eq
      simpa only [coeff_map,coe_evalRingHom,coeff_zero] using congrArg (fun P : (Polynomial L)=>P.coeff j) eq
    have eval_factor := congrArg (sp z) factor
    simp only [map_mul,map_pow] at eval_factor
    have scalar : sp z (Polynomial.C c) = Polynomial.C (c.eval z) := Polynomial.map_C ..
    rw [scalar] at eval_factor
    have nn := nonzero
    rw [eval_factor] at nn
    have cn : c.eval z≠0 := fun eq => nn (by simp [eq])
    have hn : sp z H≠0 := fun eq => nn (by simp [eq])
    have mapped : sp z (disc A B C₁ D)=disc (sp z A) (sp z B) (sp z C₁) (sp z D) := by simp [disc]
    rw [mapped,disc_at_root _ _ _ _ _ root] at eval_factor
    let t := (sp z B+sp z A*s)^2-4*sp z A*(sp z C₁+(sp z B+sp z A*s)*s)
    let R := sp z A*s^2+(sp z B+sp z A*s)*s+(sp z C₁+(sp z B+sp z A*s)*s)
    change t*R^2=Polynomial.C (c.eval z)*(sp z H)^2*sp z G at eval_factor
    have eq : (sp z H)^2*sp z G = R^2*(Polynomial.C (c.eval z)⁻¹*t) := by
      calc _ = (Polynomial.C (c.eval z)⁻¹*Polynomial.C (c.eval z))*((sp z H)^2*sp z G) := by
                 rw [←map_mul,inv_mul_cancel₀ cn,map_one,one_mul]
           _ = Polynomial.C (c.eval z)⁻¹*(t*R^2) := by rw [eval_factor]; ring
           _ = _ := by ring
    obtain ⟨u,e,ue,de⟩:=cancel_squares _ _ _ _ hn eq
    refine ⟨u,e,ue,de.trans ((natDegree_C_mul_le ..).trans ?_)⟩
    exact complement_degree (W:=406446) (d:=133606) _ _ _ _ (by decide)
      (natDegree_map_le.trans degrees.1) (natDegree_map_le.trans degrees.2.1)
      (natDegree_map_le.trans degrees.2.2) ds
  have paid:=first_band r v (T \ bad).card large (marked_corank G (by omega) height seed sep _ marks)
  have total := card_sdiff_add_card_eq_card (show bad⊆T from filter_subset _ _)
  omega
#print axioms high_odd_cubics
#print axioms disc_at_root
#print axioms complement_degree
#print axioms cancel_squares
#print axioms marked_corank
#print axioms first_band
end Lower6960.CubicOdd

end
end Merged_R6960CubicOdd

-- merged module R6960CubicJump
section Merged_R6960CubicJump
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Lower6960.CubicJump
open Polynomial Finset CurvatureSquares ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators Polynomial
theorem sum_losses {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd : L → ℕ) {r v : ℕ}
    (hr : 0 < r) (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z) :
    (∑ z ∈ T, (r-odd z+1)/2) ≤ (2*r-1)*v := by
  have each (z) (hz : z ∈ T) : (r-odd z+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,a,eq,da⟩ := fact z hz
    have fit : (h^2*a).natDegree ≤ r := by rw [←eq]; exact natDegree_map_le.trans height
    rw [←derivative_map,eq]
    exact CurvatureSquares.cofactor_corank (L:=L) (r:=r) (e:=odd z) h a hr da fit
  have bound := Finset.sum_le_sum each
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have fee := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed
    (fun j => by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial L))+1)=C ((j:L)+1) by simp]
      exact (natDegree_C_mul_le ..).trans (seed _))
  calc _ ≤ _ := (bound.trans upper).trans fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega
theorem marked_price {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd jump : L → ℕ) {r q s m v : ℕ}
    (large : 812 ≤ r) (thin : 1600*q ≤ r) (ramification : 2*s ≤ r+2*q+2) (weight : m ≤ 140915)
    (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ 4*v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z)
    (fibre : ∀ z ∈ T, odd z ≤ 2*(jump z + (2*s)/3))
    (global : (∑ z ∈ T, jump z) ≤ (6*m+s)*v) : T.card ≤ 6495*v := by
  let losses := fun z => (r-odd z+1)/2
  have det : (∑ z ∈ T, losses z) ≤ (2*r-1)*(4*v) :=
    sum_losses Q T odd (by omega) height seed sep fact
  let debit := 3*r-4*s
  have pos : 0 < debit := by dsimp [debit]; omega
  have local_bound (z) (mem : z ∈ T) : debit ≤ 6*(jump z+losses z) := by
    have := fibre z mem
    dsimp [debit,losses]
    omega
  have total := Finset.sum_le_sum local_bound
  simp only [sum_const,nsmul_eq_mul,←Finset.mul_sum,Finset.sum_add_distrib] at total
  have rate : 6*((6*m+s)+4*(2*r-1)) ≤ 6495*debit := by dsimp [debit]; omega
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc T.card*debit ≤ 6*((∑ z ∈ T, jump z)+(∑ z ∈ T, losses z)) := total
       _ ≤ 6*((6*m+s)*v+(2*r-1)*(4*v)) := Nat.mul_le_mul_left _ (Nat.add_le_add global det)
       _ = (6*((6*m+s)+4*(2*r-1)))*v := by ring
       _ ≤ (6495*debit)*v := Nat.mul_le_mul_right v rate
       _ = _ := by ring
theorem partition (r q : ℕ) :
    8*(r+q)+5 ≤ 6500 ∨ (0<q ∧ 4*r ≤ 6477*q) ∨ (812≤r ∧ 1600*q≤r) := by omega
#print axioms partition
#print axioms sum_losses
#print axioms marked_price
end Lower6960.CubicJump

end
end Merged_R6960CubicJump

-- merged module R6960CoverBudget
section Merged_R6960CoverBudget

/-! Whole-family arithmetic for the normalized-cover paper proof. -/
namespace Lower6960.CoverBudget

def triangular (f : ℕ) := f*(f-1)/2

def rate (e : ℕ) :=
  triangular e + 2*e-1 + (8*triangular e+e+1)*(e-1)

def constantCurveRate (e f : ℕ) :=
  2*e-1 + triangular f + (9*triangular f-f+4)*(e-1)

/-- The constant-field reduction cannot exceed the displayed primitive rate
in the profile range. The table is only 45 by 24. -/
theorem table :
    ∀ e : Fin 48, 3≤e.val →
      (12*e.val≤rate e.val) ∧
      (rate e.val≤31000 ↔ e.val≤20) ∧
      ∀ f : Fin 24, 2≤f.val → 2*f.val≤e.val →
        constantCurveRate e.val f.val≤rate e.val := by decide +kernel

theorem matched_shallow_uniform :
    (rate 18)*(2400*2130706433) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_four :
    rate 24*(2400+2130706433*1119) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_five :
    266695718139456639 <
      rate 25*(2400+2130706433*1029) + 48 + 143456202788540 + 143313454876987920 := by decide +kernel

#print axioms table
#print axioms grade_twenty_four
end Lower6960.CoverBudget

end Merged_R6960CoverBudget

-- merged module R6960MarkedSheet
section Merged_R6960MarkedSheet
open scoped BigOperators
open Finset
namespace Lower6960.MarkedSheet
theorem omission {G I : Type*} [Group G] [Fintype G] [Fintype I] [MulAction G I]
    [MulAction.IsPretransitive G I] [DecidableEq I] (S : Finset I) (point : I) :
    Fintype.card I * (∑ g : G, if g • point ∉ S then 1 else 0 : ℕ) =
      Fintype.card G * (Fintype.card I - S.card) := by
  classical
  let misses (x : I) : ℕ := ∑ g : G, if g • x ∉ S then 1 else 0
  have const (x : I) : misses x = misses point := by
    obtain ⟨h,ho⟩ := MulAction.exists_smul_eq G point x
    rw [←ho]
    dsimp only [misses]
    simp_rw [←mul_smul]
    exact Equiv.sum_comp (Equiv.mulRight h) (fun g : G => if g • point ∉ S then (1:ℕ) else 0)
  have row (g : G) : (∑ x : I, if g • x ∉ S then 1 else 0 : ℕ) = Fintype.card I-S.card := by
    calc _ = ∑ x : I, if x ∉ S then (1:ℕ) else 0 :=
                Equiv.sum_comp (MulAction.toPerm g) (fun x : I => if x ∉ S then (1:ℕ) else 0)
         _ = (univ \ S).card := by
                simp only [Finset.sum_boole, Finset.sdiff_eq_filter, Nat.cast_id]
         _ = _ := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  calc _ = ∑ _x : I, misses point := by simp only [sum_const,card_univ,nsmul_eq_mul]; rfl
       _ = ∑ x : I, misses x := Finset.sum_congr rfl (fun x _ => (const x).symm)
       _ = ∑ g : G, ∑ x : I, if g • x ∉ S then 1 else 0 := Finset.sum_comm
       _ = _ := by simp_rw [row]; simp
def rate (e : ℕ) := (9*e-6)*(e-1)+2*e-1
theorem good_price (labels a e n s t loss torsion image : ℕ)
    (size : 0<a) (degree : s≤n*a) (positive : 0<e)
    (marked : labels*a≤loss+torsion+e*image)
    (collisions : loss≤8*s*t) (sections : torsion+image≤n+a*t) :
    labels≤(8*n+e)*t+e*n := by
  have h1 : 8*s*t≤8*(n*a)*t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left 8 degree)
  have h2 : torsion+e*image≤e*(n+a*t) := calc
    _ ≤ e*torsion+e*image := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ positive) _
    _ = e*(torsion+image) := (Nat.mul_add ..).symm
    _ ≤ _ := Nat.mul_le_mul_left e sections
  refine Nat.le_of_mul_le_mul_right ?_ size
  calc labels*a ≤ loss+(torsion+e*image) := by simpa only [Nat.add_assoc] using marked
       _ ≤ 8*(n*a)*t+e*(n+a*t) := Nat.add_le_add (collisions.trans h1) h2
       _ = ((8*n+e)*t)*a+e*n := by ring
       _ ≤ ((8*n+e)*t)*a+(e*n)*a := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ size) _
       _ = _ := (Nat.add_mul ..).symm
theorem endpoint :
    rate 47 = 19275 ∧
    (∀ e : Fin 48, 3≤e.val → 12*e.val≤rate e.val ∧ rate e.val≤rate 47) ∧
    143313454876987920 + 143456202788540 + (rate 47)*(2400*2130706433) +
      47*46 + 48 < 266695718139456639 := by decide +kernel
#print axioms omission
#print axioms good_price
#print axioms endpoint
private def paidOrder : Array ℕ := #[0,1167,1162,1157,1152,1147,1142,1137,1132,1126,1121,1115,1110,1104,1099,1093,1087,1081,1075,1069,1063,1056,1050,1043,1037,1030,1023,1015,1008,1000,993,984,976,967,958,949,939,928,917,905,891,874,835,757,649,516,362,189,0]
theorem graded_endpoint :
    (∀ e : Fin 48, 3≤e.val →
      rate e.val * (2130706433+1) * (paidOrder[e.val]!-1) + e.val*(e.val-1) ≤
        27250435559936982) ∧
    rate 42 * (2130706433+1) * (paidOrder[42]!-1) + 42*41 = 27250435559936982 ∧
    95520157607632002 + 143314245927361932 + 143456202788540 + 48 +
      27250435559936982 = 266228295297719504 := by decide +kernel
#print axioms graded_endpoint
end Lower6960.MarkedSheet

end Merged_R6960MarkedSheet

end Merged6967_R6960MarkedSheet
