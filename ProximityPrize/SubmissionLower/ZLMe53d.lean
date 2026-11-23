import ProximityPrize.SubmissionLower.ZrgYIVd
set_option Elab.async false
open _root_ renaming AlgHom.coe_toRingHom → zlv, AlgHom.toRingHom_eq_coe → ziQ, DFunLike.congr_fun → zmU, Finset.range → z4x, Function.Injective → zq4, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.C_dvd_iff_dvd_coeff → zXG, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.monomial_le_degreeOf → zKk, MvPolynomial.optionEquivLeft → zpj, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y, Polynomial.coe_mapRingHom → zKC, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, Submodule.sum_mem → zo3
section
set_option autoImplicit true
namespace qxRGmlc
noncomputable section
open Polynomial
open aR (ao Shape)
open jA (kS jK mA Jn gY)
open NR (Lq O8)
open aFN (canonical GV aTo)
open qzLARrc (projectivity bjM LocalCoeff LocalSlot localParameter localColumn localImage)
open private cV aJI from ProximityPrize.SubmissionLower.S
open scoped Polynomial
private abbrev incl:ao →+* kS:=algebraMap _ _
private abbrev seed :kS:=algebraMap ao[X] kS z7y
private theorem projective_facts {k d e :ao} (hk :k≠0) (hd:d≠0) :
    let z :=projectivity k d e
    let D:=incl k - incl e*z
    D ≠0∧incl d*z=D *seed∧Transcendental ao z := by
  dsimp only
  let z :=projectivity k d e
  let D:=incl k - incl e*z
  let Q:ao[X] :=C d+C e*z7y
  let f :ao[X] →+* kS:=algebraMap _ _
  have hQ:Q≠0:= by
    intro h
    exact hd (by simpa [Q] using congrArg (evalRingHom 0) h)
  have hfC (x :ao) :f (C x)=incl x :=
    (IsScalarTower.algebraMap_apply ao ao[X] kS x).symm
  have hden:incl d+incl e*seed≠0:= by
    have h:=(zxb ao[X] kS).ne hQ
    change f Q≠f 0 at h
    simpa only [Q,map_add,map_mul,hfC,map_zero,seed] using h
  have hmul :z*(incl d+incl e*seed)=incl k*seed :=
    div_mul_cancel₀ _ hden
  have hDmul :D *(incl d+incl e*seed)=incl k*incl d:= by
    dsimp only [D]
    linear_combination -incl e*hmul
  have hD:D ≠0:= by
    intro hz
    rw [hz,zero_mul] at hDmul
    exact mul_ne_zero (map_ne_zero incl |>.mpr hk) (map_ne_zero incl |>.mpr hd) hDmul.symm
  have hrel :incl d*z=D *seed := by
    dsimp only [D]
    linear_combination hmul
  refine ⟨hD,hrel,fun hz => ?_⟩
  have hza :z∈algebraicClosure ao kS:=mem_algebraicClosure_iff.mpr hz
  have hm (x :ao) :incl x∈algebraicClosure ao kS :=
    (algebraicClosure ao kS).algebraMap_mem x
  have hs :seed∈algebraicClosure ao kS:= by
    have hseed :incl d*z/D =seed :=(div_eq_iff hD).mpr (hrel.trans (mul_comm _ _))
    rw [← hseed]
    exact div_mem (mul_mem (hm d) hza) (sub_mem (hm k) (mul_mem (hm e) hza))
  have hinj:zq4 (aeval seed :ao[X] →ₐ[ao] kS) := by
    have heq : (aeval seed :ao[X] →ₐ[ao] kS).toRingHom=f := by
      apply z86
      · intro x
        simp [hfC]
      · simp [f,seed]
    change zq4 ((aeval seed :ao[X] →ₐ[ao] kS).toRingHom)
    rw [heq]
    exact zxb ao[X] kS
  exact (transcendental_iff_injective.mpr hinj) (mem_algebraicClosure_iff.mp hs)
private abbrev cutCoeff (L:ℕ) :ao[X] →+* LocalCoeff L:=Ideal.Quotient.mk _
private abbrev cut (L:ℕ) :jK →+* bjM L:=zDK (cutCoeff L)
private def specialize (z :kS) :jK →+* Lq :=
 (eval₂RingHom (zDK (mapRingHom incl)) (znf (C z))).comp
   (zpj ao[X] (Fin 3)).toRingEquiv.toRingHom
private theorem specialize_coeff (z :kS) (F:jK)
   (m:Fin 3 →₀ ℕ) (i:ℕ) :
   let P:=zpj ao[X] (Fin 3) F
   let Q := ∑ j∈P.support,monomial j (((P.coeff j).coeff m).coeff i)
   ((specialize z F).coeff m).coeff i=aeval z Q:= by
 classical
 dsimp only
 let P:=zpj ao[X] (Fin 3) F
 change (((eval₂RingHom (zDK (mapRingHom incl)) (znf (C z)) P).coeff
   m).coeff i)= _
 rw [show (eval₂RingHom (zDK (mapRingHom incl)) (znf (C z)))
     P= _ from eval₂_eq_sum]
 simp only [Polynomial.sum,map_sum,MvPolynomial.coeff_sum,finsetSum_coeff]
 apply Finset.sum_congr rfl
 intro j _
 rw [← map_pow,← map_pow,mul_comm,MvPolynomial.coeff_C_mul,coeff_C_mul,
   MvPolynomial.coeff_map]
 simp [P,aeval_monomial,mul_comm]
private theorem slice_coeff (P: (z3y (Fin 3) ao[X])[X])
   (m:Fin 3 →₀ ℕ) (i j:ℕ) :
   (∑ k∈P.support,monomial k (((P.coeff k).coeff m).coeff i)).coeff j =
     ((P.coeff j).coeff m).coeff i:= by
 classical
 simp only [finsetSum_coeff,coeff_monomial]
 rw [Finset.sum_eq_single j]
 · simp
 · intro b _ hb
   simp [hb]
 · intro hj
   simp [notMem_support_iff.mp hj]
private theorem cut_zero_iff {z :kS} (hz :Transcendental ao z) (L:ℕ) (F:jK) :
   cut L F=0↔znf (z7y ^L:kS[X])∣specialize z F:= by
 have hc (p:ao[X]) :cutCoeff L p=0↔z7y ^L∣p :=
   Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
 rw [← MvPolynomial.C_dvd_iff_map_hom_eq_zero _ _ hc,
   zXG,zXG]
 simp only [X_pow_dvd_iff]
 constructor
 · intro h m i hi
   rw [specialize_coeff]
   refine (congrArg (aeval z :ao[X] →ₐ[ao] kS) (Polynomial.ext fun j => ?_)).trans
     (map_zero _)
   rw [slice_coeff,coeff_zero,MvPolynomial.optionEquivLeft_coeff_coeff]
   exact h _ _ hi
 · intro h n i hi
   have h' := h n.some i hi
   rw [specialize_coeff] at h'
   have h0:=(transcendental_iff_injective.mp hz) (h'.trans (map_zero _).symm)
   have hh:=congrArg (fun p:ao[X]=>p.coeff (n none)) h0
   rwa [slice_coeff,MvPolynomial.optionEquivLeft_coeff_some_coeff_none,coeff_zero] at hh
private theorem bOe (z :kS) (P:ao[X]) :
 specialize z (znf P)=znf (P.map incl) := by simp [specialize]
private theorem de4 (z :kS) (j:Option (Fin 3)) :
 specialize z (z9v j) =
  j.elim (znf (C z)) MvPolynomial.X:= by cases j <;> simp [specialize]
private def translateRaw (α:ao) :Lq ≃+* Lq :=
 MvPolynomial.mapEquiv _ (taylorEquiv (incl α)).toRingEquiv
@[simp] private theorem translateRaw_C (α:ao) (p:kS[X]) :
   translateRaw α (znf p)=znf (taylor (incl α) p) :=
  zpw _ _
@[simp] private theorem translateRaw_X (α:ao) (j:Fin 3) :
   translateRaw α (z9v j)=z9v j :=
  MvPolynomial.map_X _ _
@[simp] private theorem translatePole (α:ao) :
   taylor (incl α) (O8 α)=Polynomial.X:= by simp [O8]
private theorem bxZ (L:ℕ) (α:ao) (z :kS) (F:jK) :
    (znf (O8 α) :Lq)^L∣canonical (O8 α) (GV z F) ↔
      znf (z7y ^L:kS[X]) ∣
        translateRaw α (canonical (O8 α) (GV z F)) := by
  rw [← map_dvd_iff (translateRaw α),map_pow]
  rw [translateRaw_C,translatePole,← map_pow]
private abbrev Exp:=mA →₀ ℕ
private def binary (k d e :ao) (U n:ℕ) :ao[X] :=
 (C d*z7y)^n*(C k - C e*z7y)^(U - n)
private theorem binary_degree (k d e :ao) {U n:ℕ} (hn:n≤U) :
    (binary k d e U n).natDegree≤U:= by
  have hd: (C d*z7y).natDegree≤1 :=(natDegree_C_mul_le ..).trans natDegree_X_le
  have hc: (C k).natDegree≤1 := by simp
  have he : (C k - C e*z7y).natDegree≤1 := by
    simpa using natDegree_sub_le_of_le hc ((natDegree_C_mul_le e z7y).trans natDegree_X_le)
  exact natDegree_mul_le.trans
    ((add_le_add (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left n hd))
      (natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (U - n) he))).trans_eq
        (Nat.add_sub_of_le hn))
private def seedPoly {R:Type*} [CommRing R] (f :ao →+* R) :
  ao[X] →+* z3y mA R :=
 eval₂RingHom (MvPolynomial.C.comp f) (z9v none)
private def Bo {R:Type*} [CommRing R] (t:R) (i:Fin 3) :z3y mA R :=
 let v :=znf t
 ![z9v none+v*z9v (some 0),
   z9v (some 0)+v*z9v (some 1),
   z9v (some 1)+v*z9v (some 2)] i
private def jetPart {R:Type*} [CommRing R] (t:R) (m:Exp) :z3y mA R :=
 Bo t 0^m (some 0)*Bo t 1^m (some 1)*Bo t 2^m (some 2)
private def term (α k d e :ao) (U:ℕ) (m:Exp) :ao[X] →ₗ[ao] jK :=
 (((LinearMap.id :ao[X] →ₗ[ao[X]] ao[X]).smulRight
   (seedPoly C (binary k d e U (m none)) *
     jetPart z7y m)).restrictScalars ao).comp (taylor α)
private theorem term_apply (α k d e :ao) (U:ℕ) (m:Exp) (P:ao[X]) :
    term α k d e U m P =
      znf (taylor α P) *
        (seedPoly C (binary k d e U (m none))*jetPart z7y m) := by
  change taylor α P•(_:jK)= _
  rw [Algebra.smul_def,MvPolynomial.algebraMap_eq]
private def BA (α k d e :ao) (U:ℕ) :jK →ₗ[ao] jK :=
 (Finsupp.lsum ao (term α k d e U)).comp (AddMonoidAlgebra.coeffLinearEquiv ao).toLinearMap
private theorem bXk (α k d e :ao) (U:ℕ) (F:jK) :
  BA α k d e U F = ∑ m∈F.support,term α k d e U m (F.coeff m) :=
 rfl
private theorem cut_jet (L:ℕ) (i:Fin 3) :
  cut L (Bo (z7y:ao[X]) i)=Bo (localParameter L) i:= by
 fin_cases i <;> simp [Bo,localParameter]
private theorem cut_phys (L:ℕ) (P:ao[X]) :
    cutCoeff L P =
      ∑ i:Fin L,
        cutCoeff L (C ((P %ₘ (z7y ^L)).coeff i))*localParameter L^i.val := by
  have hzero :cutCoeff L (z7y ^L)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hrem:=congrArg (cutCoeff L) (modByMonic_add_div P (z7y ^L))
  simp only [map_add,map_mul,hzero,zero_mul,add_zero] at hrem
  have hs :=congrArg (cutCoeff L)
    (sum_modByMonic_coeff (p:=P) (monic_X_pow (R:=ao) L)
      (n:=L) (by rw [degree_X_pow]))
  rw [← hrem,← hs]
  simp [localParameter,← C_mul_X_pow_eq_monomial]
private theorem cut_seed (L:ℕ) (P:ao[X]) :
  cut L (seedPoly C P)=seedPoly ((cutCoeff L).comp C) P:= by
 have h: (cut L).comp (seedPoly C)=seedPoly ((cutCoeff L).comp C) := by
  apply z86
  · intro x
    simp [seedPoly]
  · simp [seedPoly]
 exact zmU h P
set_option maxHeartbeats 600000 in
private theorem mem_term {a :Shape} {U:ℕ} (α k d e :ao) {F:jK}
   (hF:Jn a F) (hU:gY F≤U) {m:Exp} (hm:m∈F.support) (P:ao[X]) :
   cut (a.b+a.j) (term α k d e U m P)∈localImage a U:= by
 classical
 obtain ⟨hB,hJ,hT,_⟩:=aJI hF hm
 have hn:m none≤U:=(zKk _ hm).trans hU
 let L:=a.b+a.j
 let q:Fin (a.b+1) :=⟨cV m,zB1 hB⟩
 have hq:q.val=m (some 0)+m (some 1)+m (some 2) :=rfl
 let c:Fin (min q.val (min a.t (a.j/2))+1) :=⟨m (some 2),by
   simp only [Nat.lt_succ_iff,le_min_iff]
   omega⟩
 let b:Fin (min (q.val - c.val) (a.j - 2*c.val)+1) :=⟨m (some 1),by
   change m (some 1)< min (q.val - m (some 2)) (a.j - 2*m (some 2))+1
   simp only [Nat.lt_succ_iff,le_min_iff]
   omega⟩
 have hvalue :q.val - c.val - b.val=m (some 0) := by
   change q.val - m (some 2) - m (some 1)=m (some 0)
   omega
 let H :=binary k d e U (m none)
 have hH :H = ∑ j∈z4x (U + 1),C (H.coeff j)*z7y ^j :=
   as_sum_range_C_mul_X_pow' H (zB1 (binary_degree k d e hn))
 let G:=taylor α P
 let t:bjM L:=znf (localParameter L)
 let z :bjM L:=z9v none
 let J:=jetPart (localParameter L) m
 rw [term_apply]
 simp only [jetPart,map_mul,zpw,cut_seed,map_pow,cut_jet]
 change znf (cutCoeff L G)*(seedPoly ((cutCoeff L).comp C) H*J)∈_
 rw [cut_phys L G,hH]
 simp only [map_sum,map_mul,map_pow,seedPoly,coe_eval₂RingHom,eval₂_C,eval₂_X,
   zQb,Finset.sum_mul,Finset.mul_sum]
 refine zo3 _ fun j hj=>zo3 _ fun i _ => ?_
 let I:LocalSlot a U:=⟨i,⟨j,Finset.mem_range.mp hj⟩,⟨q,c,b⟩⟩
 have hcol:localColumn a U I∈localImage a U :=
   Submodule.subset_span (Set.mem_range_self I)
 have h:=(localImage a U).smul_mem ((G %ₘ (z7y ^L)).coeff i*H.coeff j) hcol
 have hsmul (x :ao) :
     (algebraMap ao (bjM L)) x=znf (cutCoeff L (C x)) :=rfl
 have heq :localColumn a U I=t^i.val*z^j*J:= by
   unfold localColumn
   change _ *_ *_^(q.val - c.val - b.val)*_ *_ = _
   simp [hvalue,t,z,J,jetPart,Bo,I,c,b,L,mul_assoc]
 rw [Algebra.smul_def,hsmul,heq,map_mul,map_mul,map_mul] at h
 convert h using 1
 dsimp only [t,z]
 ring
private theorem mem_cleared {a :Shape} {U:ℕ} (α k d e :ao) {F:jK}
  (hF:Jn a F) (hU:gY F≤U) :
  cut (a.b+a.j) (BA α k d e U F)∈localImage a U:= by
 rw [bXk,map_sum]
 exact zo3 _ fun m hm=>mem_term α k d e hF hU hm _
private abbrev amd:kS →+* Lq:=MvPolynomial.C.comp C
private theorem gt3 (z :kS) (P:ao[X]) :
  specialize z (seedPoly C P)=amd (aeval z P) := by
 have h: (specialize z).comp (seedPoly C) =
    amd.comp (aeval z :ao[X] →ₐ[ao] kS).toRingHom:= by
  apply z86
  · intro x
    simp [seedPoly,bOe]
  · simp [seedPoly,de4]
 exact zmU h P
private def rawSub (α:ao) (z :kS) :jK →+* Lq :=
 (translateRaw α).toRingHom.comp ((canonical (O8 α)).comp (GV z))
private theorem taylorAlg_apply (α:ao) (p:ao[X]) :
 taylorAlgHom α p=taylor α p:=rfl
private theorem rawSub_eq (α:ao) (z :kS) :
    rawSub α z =
      MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp ((mapRingHom incl).comp (taylorAlgHom α).toRingHom))
        (fun i:mA=>i.elim (amd seed)
          (fun j=>specialize z (Bo (z7y:ao[X]) j))) := by
  apply MvPolynomial.ringHom_ext
  · intro p
    simp only [rawSub,zQb,GV,MvPolynomial.eval₂Hom_C,canonical,
      RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,translateRaw_C,
      zKC,ziQ,zlv,
      taylorAlg_apply]
    rw [map_taylor]
  · intro i
    cases i with
    | none=>simp [rawSub,GV,canonical,amd,seed]
    | some j =>
      fin_cases j <;> simp [rawSub,GV,canonical,aTo,Bo,
        bOe,de4]
      exact add_comm _ _
private theorem eval_binary (k d e :ao) {z D:kS}
  (hD:D =incl k - incl e*z) (hrel :incl d*z=D *seed)
  {U n:ℕ} (hn:n≤U) :
  aeval z (binary k d e U n)=D^U*seed^n:= by
 simp only [binary,map_mul,map_sub,map_pow,aeval_C,aeval_X,← hD]
 change (incl d*z)^n*D^(U - n)= _
 rw [hrel,mul_pow,mul_right_comm,← pow_add,Nat.add_sub_of_le hn]
private theorem aq2 (α k d e :ao) {z D:kS}
  (hD:D =incl k - incl e*z) (hrel :incl d*z=D *seed)
  {F:jK} {U:ℕ} (hU:gY F≤U) :
  specialize z (BA α k d e U F)=amd (D^U)*rawSub α z F:= by
 have hsum:=F.as_sum
 conv_rhs=>rw [hsum]
 simp only [bXk,map_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro m hm
 have hn:m none≤U:=(zKk _ hm).trans hU
 rw [term_apply,rawSub_eq,MvPolynomial.eval₂Hom_monomial,
  Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fintype.prod_option,Fin.prod_univ_three]
 simp only [jetPart,map_mul,map_pow,bOe,gt3,eval_binary k d e hD hrel hn,
  zQb,Option.elim_none,Option.elim_some,
  zKC,ziQ,zlv,taylorAlg_apply]
 ring
private def cutLinear (L:ℕ) :jK →ₗ[ao] bjM L :=
 (MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ ao _:ao[X] →ₐ[ao] _)).toLinearMap
theorem proof :qzLARrc.c1 := by
 intro a U α k d e hk hd V hV
 let L:=a.b+a.j
 let z :=projectivity k d e
 let D:=incl k - incl e*z
 obtain ⟨hD,hrel,hz⟩:=projective_facts (e :=e) hk hd
 let g:=((cutLinear L).comp (BA α k d e U)).comp V.subtype
 refine ⟨g.codRestrict (localImage a U) (fun F => ?_),fun F => ?_⟩
 · obtain ⟨hF,hU⟩:=hV F.val F.property
   exact mem_cleared α k d e hF hU
 · rw [← Submodule.coe_eq_zero]
   change cut L (BA α k d e U F.val)=0↔_
   rw [cut_zero_iff hz,aq2 α k d e (D:=D) rfl hrel (hV _ F.property).2,
     bxZ L α z]
   have hu:IsUnit (amd (D^U)) :=
     (isUnit_iff_ne_zero.mpr (pow_ne_zero U hD)).map amd
   exact hu.dvd_mul_left
end
end qxRGmlc
end
section
set_option autoImplicit true
namespace qA0rFHd
noncomputable section
open aR (ao Shape)
open aFN (Slot aTo)
open qzLARrc (LocalCoeff localParameter flagRank)
abbrev WindowRow (a :Shape) :=z3y (Fin 3) (LocalCoeff (a.b+a.j))
abbrev PhysicalExponent (a :Shape) :=Fin (a.b+a.j)
abbrev WindowSlot (a :Shape) (lo hi:ℕ) :=
 PhysicalExponent a×(Σ q : {q:Fin (hi+1) // lo≤q.val},Slot a q.val.val)
def windowColumn (a :Shape) {lo hi:ℕ} (i:WindowSlot a lo hi) :WindowRow a :=
  let t:=localParameter (a.b+a.j)
  let q:=i.2.1.val.val
  let s :=i.2.2
  znf t^i.1.val*(1+aTo t 0)^(q - s.1.val - s.2.val) *
    aTo t 1^s.2.val*aTo t 2^s.1.val
def seedWindow (a :Shape) (lo hi:ℕ) :Submodule ao (WindowRow a) :=
 Submodule.span ao (Set.range (windowColumn a (lo:=lo) (hi:=hi)))
def homogeneousColumn (a :Shape) (q:ℕ) (x :PhysicalExponent a)
    (s :Slot a q) :WindowRow a :=
  let t:=localParameter (a.b+a.j)
  znf t^x.val*aTo t 0^(q - s.1.val - s.2.val) *
    aTo t 1^s.2.val*aTo t 2^s.1.val
abbrev HomogeneousSlot (a :Shape) (q w:ℕ) :=
 PhysicalExponent a × {s :Slot a q // q - s.1.val - s.2.val≤w}
def homogeneousImage (a :Shape) (q w:ℕ) :Submodule ao (WindowRow a) :=
  Submodule.span ao (Set.range (fun i:HomogeneousSlot a q w =>
    homogeneousColumn a q i.1 i.2.val))
def reciprocalImage (a :Shape) (hi w:ℕ) :Submodule ao (WindowRow a) :=
 (z4x (hi+1)).sup (fun q=>homogeneousImage a q (min q w))
def Ni (a :Shape) (q w:ℕ) :ℕ :=
 ∑ i∈z4x (a.b+2*a.j),flagRank a q ((i:ℤ)-(a.j:ℤ)) w
end
end qA0rFHd
end
section
namespace qmb8rCe
open aR (ao Shape)
open aFN (Slot)
open qlc9qed (Bank)
open qzLARrc (derivativeIndex)
open scoped BigOperators
abbrev box :=Bank.cheap.box
noncomputable def cutMatrix (a :Shape) (q d h:ℕ) :
   Matrix (Slot a q) (Slot a q) ao :=
 fun r s =>
   if d≤ s.1.val+s.2.val∧derivativeIndex r<h ∧
       r.1.val≤ s.1.val∧s.1.val - r.1.val≤ r.2.val then
     (Nat.choose s.1.val r.1.val :ao) *
       (Nat.choose s.2.val (r.2.val-(s.1.val - r.1.val)) :ao)
   else 0
noncomputable def rankCut (a :Shape) (q d h:ℕ) :ℕ:=(cutMatrix a q d h).rank
def sumN (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>sumN f n+f n
theorem sumN_eq (f :ℕ→ℕ) (n:ℕ) :sumN f n = ∑ i∈z4x n,f i:= by
 induction n with
 | zero=>simp [sumN]
 | succ n ih=>rw [sumN,Finset.sum_range_succ,ih]
def cap (a :Shape) (q d h:ℕ) :ℕ :=
  sumN (fun n =>
    min (min a.t (min n (a.j - n))+1-(n-(q - d)))
        (min a.t (min n (h - 1 - n))+1))
    (min (q+1) (min (a.j+1 - d) h))
def factor (a :Shape) (U q:ℕ) :ℕ:=U + a.b+1 - 2*q
def fullCost (a :Shape) (U q:ℕ) :ℕ :=
  sumN (fun c=>sumN (fun b=>(a.b - q+(b+2*c))*(factor a U q+(b+c)))
    (min (q-c) (a.j-2*c)+1)) (min q (min a.t (a.j/2))+1)
def mass (a :Shape) (q d:ℕ) :ℕ:=sumN (fun h=>cap a q d (h+1)) a.j
def partCost (a :Shape) (U q:ℕ) :ℕ :=
 let m:=min q a.j
 factor a U q*mass a m 0+sumN (fun d=>mass a m (d+1)) m
end qmb8rCe
end
