import ProximityPrize.SubmissionLower.ZUt8KUb
set_option Elab.async false
open _root_ renaming CommSemiring→ ov,Finsupp.single→lI,Irreducible→ oD,MvPolynomial.C→aU,MvPolynomial.X→nI,MvPolynomial.degreeOf_eq_sup→p6,MvPolynomial.eval→ oj,MvPolynomial.eval₂Hom→pU,MvPolynomial.eval₂Hom_X'→pz,MvPolynomial.map→lz,MvPolynomial.mapEquiv→ oq,MvPolynomial.map_map→pC,MvPolynomial.weightedTotalDegree→p5,MvPolynomial.weightedTotalDegree_piSingle→nq,Nat.add_le_add_right→p7,Nat.mul_comm→ oz,Polynomial.C→lV,Polynomial.coeToPowerSeries.ringHom_apply→ ox,Polynomial.coe_C→ oY,Polynomial.derivative→p9,Polynomial.hasseDeriv→cy,PowerSeries→ oZ,PowerSeries.C→lJ,PowerSeries.coeff→ oy,PowerSeries.map→ oK,PowerSeries.map_C→mD,RingHom.comp_apply→n5,Submodule.mem_bot→pQ,Submodule.mem_top→pG,Submodule.subset_span→pL,frobenius→nX,q7IA62d.seedDerivative→c9
section
set_option autoImplicit true
namespace q7IA62d
noncomputable section
open Polynomial
open scoped BigOperators
open P5 (p)
open cu (L)
open jA (jK ko mA gY bC)
open acZ (Bu agr bJg bfD)
open Rk (aIY)
open private multiples mem_multiples from ProximityPrize.SubmissionLower.S
open private bno byG from ProximityPrize.SubmissionLower.S
open private line b7T cYc ct4 c40 from ProximityPrize.SubmissionLower.A3
theorem source_le_necessary {h D Crt word t W} (hw:W≤ cutoff t) :
  source (h:=h) (D:=D) Crt word t W≤necessary Crt word t:= by
 intro P hP
 apply pL
 exact ⟨W,0,P,hP,by simpa using hw,by simp [c9,bJg]⟩
private theorem jetWeight_eq (h:ℕ) (b:mA →₀ ℕ) :
  kO h b=b.weight (fun j=>j.elim 0 (fun i=>131071+h - i.val)) := by
 rw [kO,Finsupp.weight_apply]
 congr 1
 funext j e
 cases j <;> simp [oz]
theorem necessary_le_ambient {h D Crt word t} :
    necessary (h:=h) (D:=D) Crt word t≤Aw h t (cutoff t) := by
  apply Submodule.span_le.mpr
  rintro Q ⟨W,a,P,hP,hW,rfl⟩
  obtain ⟨hB,hJ,hC,hU,hcut⟩:=mem_ambient.mp (Submodule.mem_inf.mp hP).1
  have hdeg (v :mA→ℕ) :=bfD v (lI none a) P
  refine mem_ambient.mpr ⟨(hdeg _).trans hB,(hdeg _).trans hJ,?_,?_,?_⟩
  · simpa only [c9,nq] using
      (hdeg (Pi.single (some (2 :Fin 3)) 1)).trans
        (by simpa only [nq] using hC)
  · simpa only [gY,c9,nq] using
      (hdeg (Pi.single (none :mA) 1)).trans
        (by simpa only [gY,nq] using hU)
  · intro b hb
    obtain ⟨v,hv⟩:=bno P a b
    have hv' : (c9 a P).coeff b =
        P.coeff (lI none a+b)*lV v := by
      simpa only [c9,← aIY] using hv
    have hs :lI (none :mA) a+b∈P.support := by
      rw [MvPolynomial.mem_support_iff] at hb ⊢
      exact fun hz=>hb (by rw [hv',hz,zero_mul])
    have hbefore :=hcut _ hs
    change _+kO h (lI none a+b)≤W+clearance h t at hbefore
    change _+kO h b≤ cutoff t+clearance h t
    rw [jetWeight_eq,byG _ rfl,← jetWeight_eq] at hbefore
    have hd: ((c9 a P).coeff b).natDegree ≤
        (P.coeff (lI none a+b)).natDegree := by
      rw [hv']
      simpa only [natDegree_C,add_zero] using natDegree_mul_le
        (p:=P.coeff (lI none a+b)) (q:=lV v)
    exact ((p7 hd _).trans hbefore).trans
      (p7 (le_trans (Nat.le_add_right _ _) hW) _)
private theorem jetWeight_increase {h d:ℕ} (hd:h≤d) (a :mA →₀ ℕ) :
    kO d a=kO h a+(d-h)*a.weight (fun i=>i.elim 0 (fun _=>1)) := by
  rw [jetWeight_eq,jetWeight_eq]
  have hw: (fun j:mA=>j.elim 0 (fun i=>131071+d - i.val)) =
      (fun j:mA=>j.elim 0 (fun i=>131071+h - i.val)) +
        (d - h)•(fun j:mA=>j.elim 0 (fun _=>1)) := by
    funext j
    cases j with
    | none=>simp
    | some i =>
      change 131071+d-i.val=(131071+h-i.val)+(d-h)*1
      have hi:=i.isLt
      omega
  rw [hw]
  simp only [Finsupp.weight_eq_sum,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem caps_mono {h d t W P} (hd:h≤d) (hp:CapsCut h t W P) :
  CapsCut d t W P:= by
 obtain ⟨hB,hJ,hC,hU,hw⟩:=hp
 refine ⟨hB,hJ,hC,hU,?_⟩
 intro a ha
 change _+kO d a≤W+clearance d t
 rw [jetWeight_increase hd,← add_assoc]
 have hb:=(MvPolynomial.le_weightedTotalDegree _ ha).trans hB
 have hb' := Nat.mul_le_mul_left (d-h) (hb.trans (Nat.le_add_right _ t.shape.J))
 have hc:clearance d t=clearance h t+(d-h)*(t.shape.B+t.shape.J) := by
  unfold clearance
  conv_lhs=>rw [← Nat.add_sub_of_le hd]
  rw [Nat.mul_add,oz (d-h)]
 rw [hc,← add_assoc]
 exact Nat.add_le_add (hw _ ha) hb'
theorem gpj (N :Submodule L jK) (hne : ∃ Q∈N,Q≠0)
    {P:jK} (hP:P≠0) :
    ∃ Q∈N,Q≠0 ∧
      ∀ f :ko,oD f→f∣bC P→f∣bC Q →
        ∀ R∈N,f∣bC R:= by
  classical
  let _:StrongNormalizationMonoid ko :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad:=(UniqueFactorizationMonoid.normalizedFactors (bC P)).toFinset.filter
    (fun f => ∃ Q∈N,¬ f∣bC Q)
  let sub:Option ↥bad→Submodule L N
    | none => ⊥
    | some f=>((multiples f.val).restrictScalars L).comap (Bu.comp N.subtype)
  have hproper (i:Option ↥bad) :sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q,hQ,hn⟩:=hne
      intro h
      have hm: (⟨Q,hQ⟩:N)∈sub none :=h ▸ pG
      exact hn (congrArg Subtype.val ((pQ L).mp hm))
    | some f =>
      obtain ⟨Q,hQ,hnd⟩:=(Finset.mem_filter.mp f.property).2
      intro h
      have hm: (⟨Q,hQ⟩:N)∈sub (some f) :=h ▸ pG
      exact hnd (mem_multiples.mp hm)
  obtain ⟨Q,hQ⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (ι:=Option ↥bad) (K:=L) (M:=N) sub hproper
  refine ⟨Q.val,Q.property,?_,fun f hf hdf hdq R hR => ?_⟩
  · intro h
    exact hQ none ((pQ L).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨g,hg,hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (agr hP) hf hdf
    have hg' : g∈bad:=Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hg,R,hR,fun h=>hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hQ (some ⟨g,hg'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdq))
theorem forced_power {h D Crt word t f} (hf :oD f) (hs :0<gY f)
  (hsmall:gY f<p)
  (hall : ∀ Q∈necessary (h:=h) (D:=D) Crt word t,f∣bC Q)
  {W P} (hW:W≤ cutoff t) (hP:P∈source Crt word t W) :
  f^(1+(cutoff t-W)/(3*h))∣bC P:= by
 apply c40 (line none) (b7T none)
  (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf) (ct4 hs hsmall)
 intro a ha
 rw [cYc]
 apply hall
 apply pL
 refine ⟨W,a,P,hP,?_,rfl⟩
 have ham:a≤(cutoff t-W)/(3*h) := by omega
 have hm:=(Nat.mul_le_mul_right (3*h) ham).trans (Nat.div_mul_le_self (cutoff t-W) (3*h))
 rw [oz a] at hm
 omega
end
end q7IA62d
end
section
set_option autoImplicit true
namespace q7IA62d
noncomputable section
open Polynomial
open P5 (K p)


open cu (L jz)
open jA (jK ko iP VP mA qV bC ED jW
 vC lP gY)
private def σP:L[X] ≃+* L[X] :=Polynomial.mapEquiv (frobeniusEquiv L p)
private def σF:iP ≃+* iP:=IsFractionRing.ringEquivOfRingEquiv σP
private def conjugate :jK ≃+* jK:=oq mA σP
private def conjugateGeneric:ko ≃+* ko:=oq mA σF
private theorem σP_apply (a :L[X]) :σP a=a.map (nX L p) :=rfl
private theorem σF_apply (a :L[X]) :σF (qV a)=qV (σP a) :=
 IsFractionRing.ringEquivOfRingEquiv_algebraMap σP a
private theorem efL (P:jK) :
  bC (conjugate P)=conjugateGeneric (bC P) := by
 change lz qV (lz σP.toRingHom P) =
  lz σF.toRingHom (lz qV P)
 have he :qV.comp σP.toRingHom=σF.toRingHom.comp qV :=
  RingHom.ext fun a=>(σF_apply a).symm
 rw [pC,pC,he]
private theorem support_map {R S:Type*} [ov R] [ov S]
  (σ:R ≃+* S) (P:VP R) :
  (oq mA σ P).support=P.support :=
 MvPolynomial.support_map_of_injective P σ.injective
private theorem degree_map {R S:Type*} [ov R] [ov S]
  (σ:R ≃+* S) (P:VP R) (i:mA) :
  (oq mA σ P).degreeOf i=P.degreeOf i:= by
 rw [p6,p6,support_map]
private theorem conjugate_caps {h t W} {P:jK} (hc:CapsCut h t W P) :
   CapsCut h t W (conjugate P) := by
 have hs :=support_map σP P
 change (conjugate P).support=P.support at hs
 obtain ⟨hB,hJ,hC,hU,hcut⟩:=hc
 refine ⟨?_,?_,?_,?_,?_⟩
 · simpa only [vC,p5 ,hs] using hB
 · simpa only [lP,p5 ,hs] using hJ
 · exact (degree_map σP P _).trans_le hC
 · exact (degree_map σP P _).trans_le hU
 · intro a ha
   rw [hs] at ha
   have hd: ((conjugate P).coeff a).natDegree=(P.coeff a).natDegree := by
    change ((lz σP.toRingHom P).coeff a).natDegree= _
    rw [MvPolynomial.coeff_map]
    exact natDegree_map (nX L p)
   simpa only [hd] using hcut a ha
private theorem σF_seed (z :K) :σF.toRingHom (jz z)=jz z^p:= by
 change σF (qV (C (algebraMap K L z)))= _
 rw [σF_apply,σP_apply,map_C]
 exact map_pow (qV.comp lV) (algebraMap K L z) p
private theorem eval_conjugate {z z' : iP} {S:L[X]} {G:ko}
   (hz :σF.toRingHom z=z') (hS:S.map (nX L p)=S)
   (h:oj (ED z (jW S)) G=0) :
   oj (ED z' (jW S)) (conjugateGeneric G)=0:= by
 have ha :σF.toRingHom ∘ ED z (jW S)=ED z' (jW S) := by
   funext i
   cases i with
   | none=>exact hz
   | some j =>
     change σF (qV (cy j.val S))=qV (cy j.val S)
     rw [σF_apply,σP_apply,← Polynomial.hasseDeriv_map,hS]
 change oj (ED z' (jW S)) (lz σF.toRingHom G)=0
 rw [← ha,← MvPolynomial.map_eval,h,map_zero]
def NoMovingTop (P Q:jK) :Prop :=
  ∀ f :ko,oD f→0<f.degreeOf (some 2) →
    f∣bC P→f∣bC Q→ gY f=0
private theorem conjugate_noMoving {P Q:jK} (h:NoMovingTop P Q) :
   NoMovingTop (conjugate P) (conjugate Q) := by
 intro f hf ht hp hq
 rw [efL] at hp hq
 have hdeg (i:mA) : (conjugateGeneric.symm f).degreeOf i=f.degreeOf i :=
   degree_map σF.symm f i
 have hdvd (R:jK) (hr :f∣conjugateGeneric (bC R)) :
     conjugateGeneric.symm f∣bC R:= by
   simpa only [RingEquiv.symm_apply_apply] using map_dvd conjugateGeneric.symm hr
 have hs :=h (conjugateGeneric.symm f)
   ((MulEquiv.irreducible_iff (f :=conjugateGeneric.symm.toMulEquiv)).mpr hf)
   (by rw [hdeg]; exact ht) (hdvd P hp) (hdvd Q hq)
 exact (hdeg none).symm.trans hs
end
end q7IA62d
end
section
set_option autoImplicit true
namespace q3hrY0a
noncomputable section
open cu (L)
open DP (jF zG)
open jA (jK mA kS jH)
open Rk (aIY)
open aA0
open q7IA62d (forward a6h Yd)
open scoped Polynomial PowerSeries
open private aCE bCT dMb cHr from ProximityPrize.SubmissionLower.A1
private def a7x (H :L[X]) (R:atU) (i:Fin 3) :bbm :=
  aU (cy i.val R) +
    ∑ j:Fin 3,if j.val≤ i.val then
      aU (cy (i.val - j.val) (jH H)) *
        nI j else 0
private def abg (H :L[X]) (R:atU) :jK →+* bbm :=
 pU
  (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap L kS)))
  (fun i:mA=>i.elim (aU (lV seed)) (a7x H R))
private theorem c8C (H :L[X]) (R:atU) (p:L[X]) :
  abg H R (aU p)=aU (jH p) := by
 simp [abg,jH]
private def bic (H :L[X]) (R:atU) :jK →+* oZ bbm :=
 (PowerSeries.rescale (aU (jH H^3))).comp
   ((oK (abg H R)).comp (Polynomial.coeToPowerSeries.ringHom.comp aEP))
set_option maxHeartbeats 800000 in
private theorem eDY (H₀:L[X]) (R:atU) :
    ∃ M:bbm →+* oZ bbm,
      M.comp (abg H₀ R)=bic H₀ R ∧
        M (aU (jH H₀))=lJ (aU (jH H₀)) := by
  classical
  let H :=jH H₀
  choose d hd using fun j:Fin 3 =>
    d5a (H^3) (cy j.val R)
  let D:Fin 3→ oZ bbm:= fun j=>oK aU (d j)
  let A:= fun p:atU=>lJ (aU (σ:=Fin 3) p)
  let Δ:=cHr (A H) (A (cy 1 H))
    (A (cy 2 H)) D
  let M:=pU (aCE (H^3))
    (fun j=>lJ (nI j)+Δ j)
  have hres (j:Fin 3) :
      aCE (H^3) (cy j.val R) =
        A (cy j.val R)+(A H)^3*D j:= by
    have hj:=congrArg (oK (aU (σ:=Fin 3))) (hd j)
    simpa [aCE,A,D,mD] using hj
  have hMC (p:atU) :M (aU p)=aCE (H^3) p:= by
    simp only [M,MvPolynomial.eval₂Hom_C]
  have hMX (j:Fin 3) :M (nI j)=lJ (nI j)+Δ j:= by
    simp only [M,pz]
  have hH (j:ℕ) :aCE (H^3) (cy j H) =
      A (cy j H) :=dMb _ H₀ j
  have hH₀:aCE (H^3) H=A H :=bCT _ H₀
  have hH₁:aCE (H^3) (p9 H)=A (p9 H) := by
    simpa only [Polynomial.hasseDeriv_one'] using hH 1
  refine ⟨M,?_,?_⟩
  · apply MvPolynomial.ringHom_ext
    · intro p
      simp only [n5 ,bic,c8C,hMC,bCT,
        gox,ox ,oY ,
        mD,bLl]
    · intro j
      cases j with
      | none =>
        simp only [n5 ,bic,abg,pz ,
          Option.elim,hMC,aCE,d5b,goy,map_add,map_mul,
          ox ,Polynomial.coe_X,oY ,
          mD,PowerSeries.map_X,bLl,c8o]
        exact add_comm _ _
      | some j =>
        have hjet:M (a7x H₀ R j)=lJ (a7x H₀ R j) := by
          simp only [a7x,← show H=jH H₀ from rfl,map_add,map_sum,apply_ite,
            map_zero,map_mul,hMC,hMX,hres,hH]
          fin_cases j <;>
            norm_num [Fin.sum_univ_three,Δ,cHr,A,hH₀,hH₁,
              Polynomial.hasseDeriv_zero'] <;> ring
        simpa only [n5 ,bic,abg,pz ,
          Option.elim,goz,ox ,
          oY ,mD,bLl] using hjet
  · rw [hMC,bCT]
private theorem dMC {h} (D:jF h) (R:atU)
  (a :ℕ) (P:jK) :
  oy a (bic (D.block 0) R P) =
    abg (D.block 0) R (Yd D a P) := by
 simp only [bic,n5 ,PowerSeries.coeff_rescale,PowerSeries.coeff_map,
  ox ,Polynomial.coeff_coe,cGk,
  Yd,c9,← aIY,map_mul,c8C,jH,
  map_pow,pow_mul]
theorem c4E {h} {D:jF h} (Crt:zG D)
  (r a :ℕ) (P:jK)
  (hP:aU (jH (D.block 0))^r∣forward Crt P) :
  aU (jH (D.block 0))^r∣forward Crt (Yd D a P) := by
 let R:=a6h Crt
 obtain ⟨M,hM,hH⟩:=eDY (D.block 0) R
 change aU (jH (D.block 0))^r∣abg (D.block 0) R P at hP
 obtain ⟨Q,hQ⟩:=hP
 refine ⟨oy a (M Q),?_⟩
 change abg (D.block 0) R (Yd D a P)= _
 rw [← dMC,← DFunLike.congr_fun hM P]
 change oy a (M (abg (D.block 0) R P))= _
 rw [hQ,map_mul,map_pow,hH,← map_pow,PowerSeries.coeff_C_mul]
end
end q3hrY0a
end
