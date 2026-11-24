import ProximityPrize.SubmissionLower.A3
import ProximityPrize.SubmissionLower.CS
import ProximityPrize.SubmissionLower.D3
set_option Elab.async false
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
private def RG:K[X] →+* nU :=
 (algebraMap FX nU).comp (algebraMap K[X] FX)
private theorem bch:qJ RG :=
 (algebraMap FX nU).injective.comp (IsFractionRing.injective K[X] FX)
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
private theorem fUe {P:nU[X]} (hP:P.degree<k) (i:ℕ) :
  awb (fun j=>P.coeff j.val) i=(taylor c9 P).coeff i:= by
 have hnat :P.natDegree<k := by
  by_cases hz :P=0
  · simpa only [hz,Polynomial.natDegree_zero] using (by decide :0<k)
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hP
 have hsum:P = ∑ l:Fin k,monomial l.val (P.coeff l.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun j=>monomial j (P.coeff j))]
  exact P.as_sum_range' _ hnat
 exact (cGn c9 (fun j:Fin k=>P.coeff j.val) i).symm.trans
  (oK (fun P:nU[X]=>(taylor c9 P).coeff i) hsum.symm)
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
    (I₁ s) k t₁ ayP hIpos hm l).trans (by
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
def mark (f :K[X]) :Fin 2→nU :=
 polynomialJet c9 (f.map lJ)
private theorem d2z (f :K[X]) : (f.map lJ).eval c9=RG f := by
 rw [Polynomial.eval_map]
 change Polynomial.eval₂RingHom lJ c9 f=RG f
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RG,lJ]
 · simp [RG,c9]
private theorem cM6 (G:aU K 1) (f :K[X]) :
   jetEvaluation (Yb G) c9 (mark f) =
     RG (lz G f) := by
 rw [mark,← eval_differentialSpecialization,Yb,
   ← map_differentialSpecialization,d2z]
theorem eos (G:aU K 1) (f :K[X])
  (h:lz G f=0) :lI (mark f) (initial G)=0:= by
 change lI (mark f) (initialJetEquation c9 (Yb G))=0
 rw [← oy ,aeval_initialJetEquation,cM6,h,ox]
private theorem ddu (G:aU K 1) (f :K[X])
  (h:lz (nq G (cy 1)) f≠0) :
  lI (mark f) (sep G)≠0:= by
 rw [← oy ,sep,aeval_initialJetSeparant,Yb,← map_separant]
 exact fun hz=>h (bch ((cM6 _ _).symm.trans (hz.trans (ox _).symm)))
theorem b0r (G:aU K 1) (f :K[X])
  (h:lz (nq G (cy 1)) f≠0) :
  lI (mark f) (denominator G)≠0:= by
 rw [denominator,map_pow]
 exact pow_ne_zero _ (ddu G f h)
theorem dIp (G:aU K 1) (g:BL 1) (f :K[X])
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
private def ajm:K →+* aR.ao[X] :=
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
      change optionEquivLeft aR.ao[X] (Fin 3)
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
private theorem d0Y (G:aU K 2) (f :K[X])
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
private theorem cfE {G G' : aU K 1} {f :K[X]}
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
private theorem fVx (Q:aU K 1) (f :K[X]) :
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
      ∀ f :K[X],lz Q f=0 → ¬ae8 Q f →
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
open private bK6 from ProximityPrize.SubmissionLower.BG
open private aM6 from ProximityPrize.SubmissionLower.Z3EWiUc
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
namespace P1
noncomputable section
open Finset

open scoped BigOperators
private def E0 (c b:ℕ) :=72 - (b+c)+1
private def bbW (c:ℕ) :=range (21 - 2*c+1)
private def po (c:ℕ) := ∑ b∈bbW c,E0 c b
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
theorem dth {A h cap} (hlist:i4.axW A cap) {u deleted} (M:FJ h u deleted)
    (Γ:Finset K) (F:bje A M Γ) (hw:M.iF≤0) :
    Γ.card≤ cap:= by
  classical
  obtain ⟨hfinite,hprice⟩:=hlist M.word
  have hsub:Γ.image F.scalar⊆hfinite.toFinset := by
    intro P hP
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hP
    have mark :=F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.aic with hz | hd
      · rw [hz,Polynomial.degree_zero]
        exact WithBot.bot_lt_coe k
      · have hn: (F.scalar γ).natDegree<k := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.dw.trans
      apply uJ
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet,Finset.mem_filter,Finset.mem_univ,true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card=(Γ.image F.scalar).card:=(Finset.card_image_of_injOn F.distinct).symm
    _≤hfinite.toFinset.card:=uJ hsub
    _ = _:=(Set.ncard_eq_toFinset_card _ hfinite).symm
    _≤ cap:=hprice
end
end P1
end
