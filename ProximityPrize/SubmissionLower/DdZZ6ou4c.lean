import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZDBuLfd
import ProximityPrize.SubmissionLower.DdZW31ykd
import ProximityPrize.SubmissionLower.DdZdwiBha
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.Fast073

section Merged6967_DdZZ6ou4c
set_option Elab.async false





set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Fin.sum_univ_succ → zCS, Int.reduceAdd → z10, Int.reduceDiv → zS8, Int.reduceMod → z6y, Int.reduceSub → zci, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.sub_le_sub_right → zIu, Polynomial → zM1, Polynomial.C → z1z, Polynomial.coeff_C → zFI, RingHom.injective → zyB, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace P6_8_2
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative gR
open aR (ao embed extend af jet Z8 wU)
open i4 (K Node node N gap close)
open P5_8 (bo8 Equation)
open P5_8_3 (rows)
open P6_8 (A)
open anj (line bdm bfX)
open bzr (cX8)
open qC8CERb (coeffForm specialize Yw shift_jetDerivative coeff_iterate_zero atJet_eq_const)
def lastCut:ℕ:=bo8.m*A - 1
def step:ℕ:=gap A+2
private def Bounded (F:zM1 (Polynomial ao)) (b:ℕ) :Prop :=
  ∀ j,(F.coeff j).natDegree≤b+step*j
private theorem afg {F G:zM1 (Polynomial ao)} {a b:ℕ}
    (hF:Bounded F a) (hG:Bounded G b) :Bounded (F*G) (a+b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum,Nat.mul_add]
  omega
private theorem aCs (f :(Polynomial ao)) {a :ℕ} (hf :f.natDegree≤a) :
    Bounded (z1z f) a := by
  intro j
  by_cases h:j=0
  · simpa [h] using hf
  · simp [zFI,h]
private theorem bmr {ι:Type*} (s :Finset ι)
    (f :ι→zM1 (Polynomial ao)) (b:ι→ℕ) (hf : ∀ i∈s,Bounded (f i) (b i)) :
    Bounded (∏ i∈s,f i) (∑ i∈s,b i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using aCs (1 :(Polynomial ao)) (a :=0) (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact afg (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk=>hf k (Finset.mem_insert_of_mem hk))
private theorem aMs {f :zM1 (Polynomial ao)} {b:ℕ} (hf :Bounded f b) (n:ℕ) :
    Bounded (f^n) (b*n) := by
  induction n with
  | zero=>simpa using aCs (1 :(Polynomial ao)) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private abbrev weight (i:Fin 3) :ℕ:=N - i.val
private theorem avr (P:af 3) (S U:(Polynomial ao)) (T:ℕ)
    (hP : ∀ e∈P.support,(P.coeff e).natDegree+e.sum (fun i k=>weight i*k)≤T)
    (hS:S.natDegree≤N) (hU:U.natDegree≤A+2) (j:ℕ) :
    ((line P S U).coeff j).natDegree≤T+step*j:= by
  let F (i:Fin 3) :zM1 (Polynomial ao) :=
    z1z (jet S i)+Polynomial.C (jet U i)*Polynomial.X
  have hF (i:Fin 3) :Bounded (F i) (weight i) := by
    intro k
    have hs : (jet S i).natDegree≤weight i :=
      (natDegree_hasseDeriv_le S i.val).trans (zIu hS _)
    have hu: (jet U i).natDegree≤weight i+step:= by
      refine (natDegree_hasseDeriv_le U i.val).trans ((zIu hU _).trans ?_)
      have hi:=i.isLt
      change 179761 - i.val≤(131071 - i.val)+48690
      omega
    change ((z1z (jet S i)+Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree≤weight i+step*k
    rw [Polynomial.coeff_add,zFI,Polynomial.coeff_C_mul_X]
    by_cases h0:k=0
    · simpa [h0] using hs
    · by_cases h1 :k=1
      · simpa [h1] using hu
      · simp [h0,h1]
  unfold line
  rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm :=afg (aCs (P.coeff m) le_rfl)
    (bmr m.support (fun i=>F i^m i) (fun i=>weight i*m i)
      (fun i _=>aMs (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
set_option maxRecDepth 12000 in
theorem paid_root {w:Node→K} {T:ℕ} {R:Equation} {i:Fin 3} {r :ℕ}
    (hR:R∈rows w T) (hcut:T+r*step≤lastCut) {f :(Polynomial K)}
    (hf :f∈close A w) :differentialSpecialization (jetDerivative R i r) f=0:= by
  classical
  let P:=coeffForm (MvPolynomial.map embed R)
  let S:=extend f
  have hS:S.natDegree≤N := by
    apply Polynomial.natDegree_map_le.trans
    by_cases h:f=0
    · simp [h]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt h).2 hf.1)
  obtain ⟨s,hsub,hs⟩:=Finset.exists_subset_card_eq hf.2
  let x (k :Node) :ao:=embed (node k)
  let L:=mL x s
  have horder :wU P S (r+1) := by
    apply bfX P S L (S8 x s).ne_zero
    intro V hV j hj
    have hU: (L*V).natDegree≤A+2 :=
      natDegree_mul_le.trans (by
        change (mL x s).natDegree+V.natDegree≤A+2
        rw [ZQ,hs]
        exact z3b hV _)
    have hd: ((line P S (L*V)).coeff j).natDegree<bo8.m*s.card:= by
      have hle :T+step*j≤lastCut:= by
        rw [Nat.mul_comm r step] at hcut
        exact (z3b (Nat.mul_le_mul_left step (Nat.lt_succ_iff.mp hj)) T).trans hcut
      rw [hs]
      exact ((avr P S _ T (Yw hR) hS hU j).trans hle).trans_lt
        (Nat.sub_lt (Nat.mul_pos (by decide :0<bo8.m) (by decide :0<A)) Nat.one_pos)
    have hx :Function.Injective x :=(zyB embed).comp node.injective
    apply cX8 _ s x hx bo8.m _ j hd
    intro k hk c
    have hhit :=(Finset.mem_filter.mp (hsub hk)).2
    have hag: (S+c•(L*V)).eval (x k)=embed (w k) := by
      have hL:L.eval (x k)=0:=arK x s k hk
      rw [eval_add,eval_smul,eval_mul,hL,zero_mul,smul_zero,add_zero]
      change (f.map embed).eval (embed (node k))= _
      rw [eval_map,eval₂_hom,hhit]
    have hr :R ∈ ⨅ k :Node,(localConstraintAt (d:=2) bo8.m (node k) (w k)).ker :=hR.2
    have hc:SatisfiesLocalConstraints bo8.m (node k) (w k) R :=
      ((Submodule.mem_iInf _).mp hr k)
    rw [bdm,specialize]
    exact X_sub_C_pow_dvd_differentialSpecialization_of_contact _ _ _ _ hag
      (hc.map embed _ _ _ _)
  apply (Polynomial.map_injective embed (zyB embed))
  rw [map_differentialSpecialization,Polynomial.map_zero,← specialize,atJet_eq_const,
    shift_jetDerivative]
  apply coeff_iterate_zero i (Z8 P S) (D:=r+1) _ r 0 (by simp)
  intro e he
  by_contra hne
  exact (not_le_of_gt he) (horder e (MvPolynomial.mem_support_iff.mpr hne))
end
end P6_8_2
end
section
set_option autoImplicit true
namespace P6_8_2
noncomputable section
open i4 PolynomialDifferential MvPolynomial Finset ReedSolomon.HiddenDerivative
open ProximityPrize.Benchmark UniqueFactorizationMonoid
open P5_8 (Equation small smallCaps bo8 donorCaps donor_shape Jn caps Gq)
open P5_8_3 (rows nativeBand dM powerCaps layerBound layerCost mem_nativeBand actual_caps initial_caps repair_band c54)
open P6_8 (A Allocation DonorSurplus donorMargin)
open scoped Polynomial BigOperators
open P5_8_3 (mem_rows derivative_band initial_mul)
open P5_8_3 (cofactor_eq group_cutoffs)
open qmRQvQa (matrix_dimension)
open qmRQvQa (S6 telescope caps_pow)
set_option maxHeartbeats 500000
set_option maxRecDepth 1800
private def necessary (w:Node→K) :Set Equation :=
  {P | ∃ (T:ℕ) (R:Equation) (i:Fin 3) (r :ℕ),
    R∈rows w T∧T+r*step≤lastCut∧P=jetDerivative R i r}
private def necessarySpace (w:Node→K) :Submodule K Equation :=
  Submodule.span K (necessary w)
private def powerAt (T:ℕ) :ℕ:=(lastCut - T)/step+1
private theorem choose_row {w:Node→K} {Q:Equation} (hQ:ato small Q)
    (hnonzero : ∃ P∈necessarySpace w,P≠0) :
    ∃ P∈necessarySpace w,P≠0 ∧
      ∀ F:Equation,Irreducible F→F∣Q→0<jetTotalDegree F→F∣P →
        ∀ R∈necessarySpace w,F∣R:= by
  classical
  let S:=necessarySpace w
  let _:StrongNormalizationMonoid Equation :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let factors :=normalizedFactors Q
  let bad:=factors.toFinset.filter
    (fun F=>0<jetTotalDegree F ∧ ∃ R∈S,¬ F∣R)
  have hprod: (∏ F∈bad,F)∣Q :=
    ((Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod factors)).trans (prod_normalizedFactors hQ.1).dvd
  have hcard:bad.card≤83:= calc
    bad.card = ∑ _F∈bad,(1 :ℕ) := by simp
    _ ≤ ∑ F∈bad,jetTotalDegree F :=
      Finset.sum_le_sum fun F hF=>(Finset.mem_filter.mp hF).2.1
    _≤jetTotalDegree Q :=
      sum_weightedTotalDegree_le_of_prod_dvd jetDegreeWeight bad id hQ.1 hprod
    _≤83:=hQ.2.1
  have hfield :83≤Nat.card K:= by
    rw [Nat.card_eq_fintype_card]
    exact (show 83≤Fintype.card Node by rw [IRSProfile.card_index]; decide).trans
      (Fintype.card_le_of_injective node node.injective)
  let blocked (F:Equation) :Submodule K S :=
    ((Ideal.span ({F} : Set Equation)).restrictScalars K).comap S.subtype
  have hmem (F:Equation) (R:S) :R∈blocked F↔F∣(R:Equation) :=
    Ideal.mem_span_singleton
  have hpick : ∃ P:S,(P:Equation)≠0 ∧ ∀ F∈bad,¬ F∣(P:Equation) := by
    rcases bad.eq_empty_or_nonempty with hbad | ⟨F,hF⟩
    · obtain ⟨P,hP,hP0⟩:=hnonzero
      exact ⟨⟨P,hP⟩,hP0,by simp [hbad]⟩
    · have hproper (G:Equation) (hG:G∈bad) :blocked G ≠ ⊤ := by
        obtain ⟨R,hR,hnd⟩:=(Finset.mem_filter.mp hG).2.2
        intro he
        exact hnd ((hmem G ⟨R,hR⟩).mp (he ▸ Submodule.mem_top))
      obtain ⟨P,hP⟩:=Submodule.exists_forall_notMem_of_card_le bad blocked hproper
        (hcard.trans hfield)
      have hav (G:Equation) (hG:G∈bad) : ¬ G∣(P:Equation) :=
        fun hd=>hP G hG ((hmem G P).mpr hd)
      exact ⟨P,fun hz=>hav F hF (hz ▸ dvd_zero F),hav⟩
  obtain ⟨P,hP0,hP⟩:=hpick
  refine ⟨P.val,P.property,hP0,?_⟩
  intro F hF hdQ hdeg hdP R hR
  by_contra hn
  obtain ⟨G,hG,ha⟩:=exists_mem_normalizedFactors_of_dvd hQ.1 hF hdQ
  have hdegG:0<jetTotalDegree G :=
    hdeg.trans_le (weightedTotalDegree_le_of_dvd jetDegreeWeight ha.dvd
      (ne_zero_of_mem_normalizedFactors hG))
  have hbad:G∈bad:=Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr hG,hdegG,R,hR,fun hd=>hn (ha.dvd.trans hd)⟩
  exact hP G hbad (ha.dvd_iff_dvd_left.mp hdP)
private theorem necessary_band (w:Node→K) :necessarySpace w≤nativeBand donorCaps := by
  apply Submodule.span_le.mpr
  rintro P ⟨T,R,i,r,hR,_,rfl⟩
  exact derivative_band ((mem_rows.mp hR).1) i r
private theorem necessary_root {w:Node→K} {P:Equation} (hP:P∈necessarySpace w)
    {f :(Polynomial K)} (hf :f∈close A w) :differentialSpecialization P f=0:= by
  have hle :necessarySpace w≤(differentialSpecializationHom (d:=2) f).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T,R,i,r,hR,hp,rfl⟩
    exact paid_root hR hp hf
  exact hle hP
private theorem necessary_nonzero {w:Node→K} (hs :DonorSurplus w) :
    ∃ P∈necessarySpace w,P≠0:= by
  have hp:0<donorMargin:= by decide
  have hr :Vv A bo8 w<Fintype.card (apU A bo8) :=
    (Nat.lt_add_of_pos_right hp).trans_le hs
  obtain ⟨P,hP,hT,hloc⟩:=interpolant donor_shape P6_8.donor_width w hr
  refine ⟨P,zBO ⟨lastCut,P,0,0,?_,?_,(jetDerivative_zero ..).symm⟩,hP.1⟩
  · exact mem_rows.mpr ⟨mem_nativeBand.mpr hP.2,Nat.le_sub_one_of_lt hT,hloc⟩
  · simp
private theorem bound_cost (a :Jn) (l:ℕ) :layerBound a l≤layerCost a l:= by
  by_cases hf :dM (powerCaps a l) donorCaps
  · simpa only [layerBound,layerCost,ite_eq_left hf] using qfaXGOd.proof (donorCaps.wD (powerCaps a l))
  · simp only [layerBound,layerCost,ite_eq_right hf,le_refl]
private theorem cutoff_cost (a :Jn) (ha :0<a.B) :
    (∑ T∈range (lastCut+1),layerCost a (powerAt T))≤ step*Gq a := by
  rw [cofactor_eq a ha]
  refine group_cutoffs lastCut step (donorCaps.B/a.B) (by decide) (fun i=>layerCost a (i+1)) ?_
  intro i hi
  exact ite_eq_right (fun h=>(Nat.not_succ_le_self i)
    (((Nat.le_div_iff_mul_le ha).mpr h.1).trans hi))
private theorem cutoff_rank (w:Node→K) (G:Equation) (hG:G≠0)
    (hs :DonorSurplus w) (hd : ∀ T≤lastCut,∀ R∈rows w T,G^powerAt T∣R) :
    donorMargin ≤ ∑ T∈range (lastCut+1),layerBound (caps G) (powerAt T) := by
  have h:=matrix_dimension A bo8 donor_shape (by decide) (by decide) w (rows w lastCut)
    (fun _ hc hw hl=>mem_rows.mpr ⟨hc,Nat.le_sub_one_of_lt hw,hl⟩)
  have hdim:=Nat.le_of_add_le_add_left (hs.trans h)
  refine hdim.trans (telescope w lastCut (fun T=>layerBound (caps G) (powerAt T)) ?_)
  intro T hT
  rw [layerBound,← caps_pow G hG]
  exact S6 w T _ (pow_ne_zero _ hG) (hd T hT)
theorem proof :P6_8.c2 := by
  intro w Q hQ hroot hs
  obtain ⟨P,hP,hPn,havoid⟩:=choose_row hQ (necessary_nonzero hs)
  obtain ⟨d⟩:=qVHZuid.proof Q P hQ.1 hPn
  have hn:d.divisor≠0:= fun hz=>hQ.1 (d.azo.trans (by rw [hz,zero_mul]))
  have hR:d.right≠0:= fun hz=>hPn (d.az7.trans (by rw [hz,mul_zero]))
  have hG:=ne_zero_of_dvd_ne_zero hn d.common_dvd
  have hGQ:d.common∣Q:=d.common_dvd.trans ⟨d.left,d.azo⟩
  have hCaps :dM (caps d.common) smallCaps :=(apQ.eHq hQ hGQ).2
  obtain ⟨hcB,hcJ,hJC⟩:=actual_caps (apQ.initial d.common)
  rw [initial_caps] at hcB hcJ hJC
  have hpower (T:ℕ) (ht:T≤lastCut) (R:Equation) (hR:R∈rows w T) :
      d.common^powerAt T∣R:= by
    apply d.combine
    intro F hF hFQ hFP hpos
    apply qyOiD7d.proof F R (powerAt T) hF hpos (apQ.eHq hQ hFQ).2.1 (mem_rows.mp hR).1
    intro i r hr
    have hmul :=(Nat.le_div_iff_mul_le (show 0<step by decide)).mp
      (Nat.le_of_lt_succ (show r<(lastCut - T)/step+1 from hr))
    have hpaid :T+r*step≤lastCut:= by omega
    exact havoid F hF hFQ hpos hFP _ (zBO ⟨T,R,i,r,hR,hpaid,rfl⟩)
  have halloc:Allocation (caps d.common) := by
    refine ⟨hCaps.1,hCaps.2.1,hCaps.2.2,hcB,hcJ,hJC,fun hb => ?_⟩
    exact (cutoff_rank w d.common hG hs hpower).trans
      ((sum_le_sum fun T _=>bound_cost (caps d.common) (powerAt T)).trans (cutoff_cost _ hb))
  have hl:=(congrArg apQ.initial d.azo).trans (initial_mul _ _)
  have hr :=(congrArg apQ.initial d.az7).trans (initial_mul _ _)
  refine ⟨⟨d.common,hG,halloc,d.divisor,d.left,d.azo,d.support,
    apQ.initial d.right,apQ.b6j hR,q0KdFsb.proof _ _ d.coprime,?_,?_,?_⟩⟩
  · apply repair_band
    rw [initial_caps]
    exact c54 hQ.1 d.common_dvd d.azo hQ.2
  · apply repair_band
    rw [initial_caps]
    exact c54 hPn d.common_dvd d.az7 (mem_nativeBand.mp (necessary_band w hP))
  · intro f hf hgf
    have hg:zY9 (apQ.ahT f) (apQ.initial d.common)≠0:= by
      rw [apQ.bHS]
      exact (map_ne_zero_iff _ apQ.bch).mpr hgf
    obtain ⟨l,hd⟩:=d.support
    have hd' := map_dvd (zY9 (apQ.ahT f)) hd
    rw [map_pow] at hd'
    have hdn:=ne_zero_of_dvd_ne_zero (pow_ne_zero l hg) hd'
    have hzL:=congrArg (zY9 (apQ.ahT f)) hl
    have hzR:=congrArg (zY9 (apQ.ahT f)) hr
    rw [apQ.bHS,hroot f hf,map_zero,map_mul] at hzL
    rw [apQ.bHS,necessary_root hP hf,map_zero,map_mul] at hzR
    exact ⟨(mul_eq_zero.mp hzL.symm).resolve_left hdn,(mul_eq_zero.mp hzR.symm).resolve_left hdn⟩
end
end P6_8_2
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset P5_8_2 qxVnKgd
def aoV (a b c d y :ℤ) :ℤ:=a+b*y+c*y^2+d*(y%2)
def prim (a b c d y :ℤ) :ℤ :=
  6*a*y+3*b*y*(y-1)+c*y*(y-1)*(2*y-1)+6*d*(y/2)
def delta (a b c d l u:ℤ) :ℤ:=prim a b c d u - prim a b c d l
private theorem prim_step (a b c d y :ℤ) :
    prim a b c d (y+1)=prim a b c d y+6*aoV a b c d y := by
  unfold prim aoV
  rw [show (y+1)/2=y/2+y%2 by omega]
  ring
private theorem prim_sum (a b c d l:ℤ) (n:ℕ) :
    6*(∑ i∈range n,aoV a b c d (l+i))=delta a b c d l (l+n) := by
  induction n with
  | zero=>simp [delta]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ,← add_assoc]
    simp only [delta,prim_step]
    ring
theorem inner (f :ℤ→ℤ) {l u:ℤ} (a b c d:ℤ) (hlu:l≤u+1)
    (hf : ∀ y∈Icc l u,4*f y=aoV a b c d y) :
    24*(∑ y∈Icc l u,f y)=delta a b c d l (u+1) := by
  have h:=prim_sum a b c d l (u+1-l).toNat
  rw [← sum_Icc_shift,← sum_congr rfl hf,← mul_sum,
    Int.toNat_of_nonneg (show 0≤u+1-l by omega),
    show l+(u+1-l)=u+1 by ring] at h
  linear_combination h
theorem four_H {x :ℤ} (hx :0≤x) :4*H x=x*(x+2)+x%2 := by
  generalize hq:x/2=q
  have hq' : 0≤q:= by omega
  rcases (show x=2*q∨x=2*q+1 by omega) with rfl | rfl
  · rw [H_even hq',show (2*q)%2=0 by omega]
    ring
  · rw [H_odd hq',show (2*q+1)%2=1 by omega]
    ring
def kA (f :ℤ→ℤ) (l:ℤ) (n:ℕ) :ℤ := ∑ i∈range n,f (l+i)
theorem band_split (f :ℤ→ℤ) (l:ℤ) (m n:ℕ) :
    kA f l (m+n)=kA f l m+kA f (l+m) n:= by
  unfold kA
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.cast_add,← add_assoc]
private theorem gvP (f :ℕ→ℤ) (n:ℕ) :
    (∑ i∈range n,f i) =
      (∑ i∈range ((n+3)/4),f (4*i))+(∑ i∈range ((n+2)/4),f (4*i+1)) +
      (∑ i∈range ((n+1)/4),f (4*i+2))+(∑ i∈range (n/4),f (4*i+3)) := by
  have h :
      (∑ x∈(univ :Finset (Fin 4)).sigma (fun r=>range ((n+3-r.val)/4)),
        f (4*x.2+x.1.val)) = ∑ i∈range n,f i:= by
    refine sum_bij (fun x _=>4*x.2+x.1.val) ?_ ?_ ?_ (fun _ _=>rfl)
    · rintro ⟨r,i⟩ hi
      have hr :=r.isLt
      have hi:=mem_range.mp (mem_sigma.mp hi).2
      exact mem_range.mpr (by dsimp at *; omega)
    · rintro ⟨r,i⟩ _ ⟨s,j⟩ _ hij
      have hr :=r.isLt
      have hs :=s.isLt
      change 4*i+r.val = 4*j+s.val at hij
      have hrs :r=s :=Fin.ext (by omega)
      have hij' : i=j:= by omega
      subst s
      subst j
      rfl
    · intro i hi
      have hi:=mem_range.mp hi
      refine ⟨⟨⟨i%4,by omega⟩,i/4⟩,mem_sigma.mpr ⟨mem_univ _,mem_range.mpr ?_⟩,?_⟩
      · dsimp
        omega
      · dsimp
        omega
  rw [sum_sigma,zCS,zCS,zCS,
    zCS,Fin.sum_univ_zero,add_zero] at h
  rw [← h]
  have h0: (n+3-0)/4=(n+3)/4 := by omega
  have h1 : (n+3-1)/4=(n+2)/4 := by omega
  have h2 : (n+3-2)/4=(n+1)/4 := by omega
  have h3: (n+3-3)/4=n/4 := by omega
  change (∑ i∈range ((n+3-0)/4),f (4*i+0)) +
      ((∑ i∈range ((n+3-1)/4),f (4*i+1)) +
        ((∑ i∈range ((n+3-2)/4),f (4*i+2))+(∑ i∈range ((n+3-3)/4),f (4*i+3))))= _
  rw [h0,h1,h2,h3]
  simp only [add_zero,add_assoc]
theorem quarter (f :ℕ→ℤ) (n:ℕ) (a b c d value :ℤ)
    (hv :sumFormula a b c d n=288*value)
    (hf : ∀ i∈range n,24*f i=poly a b c d i) :
    (∑ i∈range n,f i)=value := by
  have h:=gvl a b c d n
  rw [← sum_congr rfl hf,← mul_sum,hv] at h
  omega
theorem band_value (f :ℤ→ℤ) (l:ℤ) (n:ℕ) {v0 v1 v2 v3 v :ℤ}
    (h0: (∑ i∈range ((n+3)/4),f (l+0+4*(i:ℤ)))=v0)
    (h1 : (∑ i∈range ((n+2)/4),f (l+1+4*(i:ℤ)))=v1)
    (h2 : (∑ i∈range ((n+1)/4),f (l+2+4*(i:ℤ)))=v2)
    (h3: (∑ i∈range (n/4),f (l+3+4*(i:ℤ)))=v3)
    (hv :v0+v1+v2+v3=v) :kA f l n=v := by
  rw [kA,gvP]
  have hs (i r :ℕ) :l+(↑(4*i+r) :ℤ)=l+r+4*(i:ℤ) := by
    push_cast
    ring
  simp only [hs,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,add_zero] at h0 ⊢
  rw [h0,h1,h2,h3,hv]
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset qxVnKgd
def II (x :ℤ) :ℤ := ∑ y∈Icc 1 x,low x x y
def lI (x :ℤ) :ℤ := ∑ y∈Icc (max 0 (2*x-1959)) (x-1),low x y y
def pG (x :ℤ) :ℤ :=
  ∑ y∈Icc (max 1 (x-1651)) (min (3919-2*x) ((3919-x)/2)),high x y 0 0
def one (x y :ℤ) :ℤ:=high x y (2*x+y-3919) 0
def uW (x :ℤ) :ℤ := ∑ y∈Icc (max (3920-2*x) (x-1651)) ((3919-x)/2),one x y
def y5 (x :ℤ) :ℤ := ∑ y∈Icc (3920-2*x) ((3919-x)/2),one x y
theorem low0 (x r :ℤ) (hx :0≤x) (hr :max 0 (x-979)=r) :
    24*II x=delta (2*(x+1)*(x+2)-4*r^2) (-2) (-1) (-1) 1 (x+1) := by
  unfold II
  apply inner _ _ _ _ _ (by omega)
  intro y hy
  have hy :=mem_Icc.mp hy
  unfold low aoV
  rw [hr]
  linear_combination 2*twice_T (by omega :0≤x+1) - four_H (by omega :0≤y)
theorem cYR (x r l:ℤ) (hx :0≤x∧x≤1958)
    (hr :max 0 (x-979)=r) (hl:max 0 (2*x-1959)=l) :
    24*lI x=delta (4-4*r^2) 4 1 (-1) l x := by
  unfold lI
  rw [hl]
  have h₀:0≤l:= by omega
  have h₁:l≤x-1+1 := by omega
  have h:=inner (fun y=>low x y y) (4-4*r^2) 4 1 (-1) h₁ ?_
  · rw [sub_add_cancel] at h
    exact h
  · intro y hy
    have hy :=mem_Icc.mp hy
    unfold low aoV
    rw [hr]
    linear_combination 2*twice_T (by omega :0≤y+1) - four_H (by omega :0≤y)
theorem high3 (x l u:ℤ) (hx :1≤x∧x≤1856)
    (hl:max 1 (x-1651)=l) (hu:min (3919-2*x) ((3919-x)/2)=u) :
    24*pG x=delta (3845520-x*(x+2)-x%2) (-2) (-1) (-1) l (u+1) := by
  unfold pG
  rw [hl,hu]
  have h₀:1≤l:= by omega
  apply inner _ _ _ _ _ (by omega)
  intro y hy
  have hy :=mem_Icc.mp hy
  unfold high aoV
  dsimp
  simp only [sub_zero]
  linear_combination -four_H (by omega :0≤x) - four_H (by omega :0≤y)
def oneA (x :ℤ) :ℤ :=
  let n:=4899-2*x
  let v :=7838-3*x
  let w:=3919-2*x
  4*n*(n+1)-v*(v+2)-w*(w+2)-x%2-1
def oneB (x :ℤ) :ℤ:=4*(7838-3*x)-8*(4899-2*x)
private theorem high_one (x l:ℤ) (hx :1307≤x∧x≤1959)
    (hl:3920-2*x≤l) (hu:l≤(3919-x)/2+1) :
    24*(∑ y∈Icc l ((3919-x)/2),one x y) =
      delta (oneA x) (oneB x) 0 0 l ((3919-x)/2+1) := by
  apply inner _ _ _ _ _ hu
  intro y hy
  have hy :=mem_Icc.mp hy
  have hp:x-2*(2*x+y-3919)-0=7838-3*x-2*y := by ring
  have ho:y-(2*x+y-3919)-0=3919-2*x := by ring
  unfold one high oneA oneB aoV
  dsimp
  rw [hp,ho]
  have h:=four_H (by omega :0≤7838-3*x-2*y)
  have h' := four_H (by omega :0≤3919-2*x)
  rw [show (7838-3*x-2*y)%2=x%2 by omega] at h
  rw [show (3919-2*x)%2=1 by omega] at h'
  linear_combination -h-h'
theorem high4 (x l:ℤ) (hx :1307≤x∧x≤1959)
    (hl:max (3920-2*x) (x-1651)=l) :
    24*uW x=delta (oneA x) (oneB x) 0 0 l ((3919-x)/2+1) := by
  unfold uW
  rw [hl]
  exact high_one x l hx (by omega) (by omega)
theorem high5 (x :ℤ) (hx :1307≤x∧x≤1959) :
    24*y5 x=delta (oneA x) (oneB x) 0 0 (3920-2*x) ((3919-x)/2+1) :=
  high_one x _ hx (by omega) (by omega)
theorem half0 (a i:ℤ) : (a+4*i)/2=a/2+2*i:= by omega
theorem half1 (a i:ℤ) : (a+4*i+1)/2=(a+1)/2+2*i:= by omega
theorem half2 (a i:ℤ) : (2*(a+4*i)-1959)/2=a+4*i-980:= by omega
theorem half4 (a i:ℤ) : (a+4*i-1651)/2=(a-1651)/2+2*i:= by omega
theorem half5 (a i:ℤ) : (3919-2*(a+4*i)+1)/2=1960-(a+4*i) := by omega
theorem half6 (a i:ℤ) : (3919-(a+4*i))/2=(3919-a)/2-2*i:= by omega
theorem parity4 (a i:ℤ) : (a+4*i)%2=a%2 := by omega
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset P5_8_2 qxVnKgd
private theorem half_neg2 (a i:ℤ) : (a-2*i+1)/2=(a+1)/2-i:= by omega
local notation "part!" a "," b "," c "," d "," v=>quarter _ _ a b c d v (by decide)
private theorem b0:kA II 0 980=0x166827d66a := by
  have h (x :ℤ) (hx :0≤x∧x≤979) :=low0 x 0 hx.1 (by omega)
  refine band_value _ _ _
    ((part! 0,56,432,640,0x591458846) ?_)
    ((part! 48,392,912,640,0x5971ac344) ?_)
    ((part! 216,968,1392,640,0x59cf4929f) ?_)
    ((part! 552,1784,1872,640,0x5a2d2f841) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half1,z10,zci,zS8]
    ring
private theorem b1 :kA II 980 979=0xd21942f432 := by
  have h (x :ℤ) (hx :980≤x∧x≤1958) :=low0 x (x-979) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x2328a0668,0x6dee738,93744,(-896),0x3485baac61) ?_)
    ((part! 0x23441d708,0x6df9da8,93072,(-896),0x34929a6b79) ?_)
    ((part! 0x235f9d520,0x6e052c8,92400,(-896),0x349f75981e) ?_)
    ((part! 0x237b20050,0x6e10698,91728,(-896),0x346178443a) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half1,z10,zci,zS8]
    ring
private theorem b2 :kA lI 0 980=0x47e0a569f := by
  have h (x :ℤ) (hx :0≤x∧x≤979) :=cYR x 0 0 (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0,40,144,128,0x11dc0dfd2) ?_)
    ((part! 24,136,240,128,0x11eec11e7) ?_)
    ((part! 72,280,336,128,0x120182e75) ?_)
    ((part! 168,472,432,128,0x121453671) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half0,z10,zci,zS8]
    ring
private theorem b3:kA lI 980 979=0xd70c1c767:= by
  have h (x :ℤ) (hx :980≤x∧x≤1958) :=cYR x (x-979) (2*x-1959) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x70b694f8,22932056,(-281904),640,0x35df2291f) ?_)
    ((part! 0x710dcac8,22791224,(-281424),640,0x35cc6f615) ?_)
    ((part! 0x71647728,22650632,(-280944),640,0x35b9ad79d) ?_)
    ((part! 0x71ba9a60,22510280,(-280464),640,0x35a6dd096) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half0,half2,z10,zS8]
    ring
private theorem b4 :kA pG 1 1306=0x12a8abab70c:= by
  have h (x :ℤ) (hx :1≤x∧x≤1306) :=high3 x 1 ((3919-x)/2) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x703dd3e88,(-211540),(-234924),208,0x4ac33f2f40) ?_)
    ((part! 0x703dc2b30,(-352420),(-234708),208,0x4ab6c3adfe) ?_)
    ((part! 0x703dabc10,(-446308),(-234612),208,0x4a8e9602af) ?_)
    ((part! 0x703d895c0,(-586972),(-234396),208,0x4a8221d71f) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half6,half_neg2,z10,zci,zS8,z6y]
    ring
private theorem b5:kA pG 1307 346=0x1a3a90fab7:= by
  have h (x :ℤ) (hx :1307≤x∧x≤1652) :=high3 x 1 (3919-2*x) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x2da670bf8,(-0x61b77b0),(-124704),1792,0x69b34cc95) ?_)
    ((part! 0x2d8e02e40,(-0x61c6a20),(-123360),1792,0x695d0a210) ?_)
    ((part! 0x2d758d738,(-0x61d5990),(-122016),1792,0x687707450) ?_)
    ((part! 0x2d5d18198,(-0x61e46c0),(-120672),1792,0x6821b17c2) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half5,z10,zci,zS8,z6y]
    ring
private theorem b6:kA pG 1653 204=0x2dffb44aa := by
  have h (x :ℤ) (hx :1653≤x∧x≤1856) :=high3 x (x-1651) (3919-2*x) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0xd73d4f68,(-0x6941688),658224,2304,0xbb5ff91e) ?_)
    ((part! 0xd598f8e0,(-0x68f0f88),659952,2304,0xb91cfdc5) ?_)
    ((part! 0xd3f5c810,(-0x68a0498),661680,2304,0xb6dd43c1) ?_)
    ((part! 0xd253f6b8,(-0x684f6d8),663408,2304,0xb4a10a06) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half4,half5,z10,zci,zS8,z6y]
    ring
private theorem b7:kA uW 1307 551=0x4d06eb1da := by
  have h (x :ℤ) (hx :1307≤x∧x≤1857) :=high4 x (3920-2*x) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 2558448,15366360,93840,(-1152),0x133eb0237) ?_)
    ((part! 5132544,15428736,92928,(-1152),0x1344d4c20) ?_)
    ((part! 10264944,15459336,92112,(-1152),0x13505f5a9) ?_)
    ((part! 12870000,15520800,91200,(-1152),0x133306dda) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
private theorem b8:kA uW 1858 102=0x6213ca59:= by
  have h (x :ℤ) (hx :1858≤x∧x≤1959) :=high4 x (x-1651) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x3499f140,(-49102608),627168,(-2304),0x195a63a6) ?_)
    ((part! 0x33df9d88,(-48791832),625488,(-2304),0x18cad95f) ?_)
    ((part! 0x3325b510,(-48477168),623712,(-2304),0x183c3a9e) ?_)
    ((part! 0x326dbeb0,(-48168072),622032,(-2304),0x17b252b6) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
private theorem b9:kA y5 1307 653=0x54dcf32e1 := by
  have h (x :ℤ) (hx :1307≤x∧x≤1959) :=high5 x hx
  refine band_value _ _ _
    ((part! 2558448,15366360,93840,(-1152),0x1538a0882) ?_)
    ((part! 5132544,15428736,92928,(-1152),0x1535bbca0) ?_)
    ((part! 10264944,15459336,92112,(-1152),0x1538a6f05) ?_)
    ((part! 12870000,15520800,91200,(-1152),0x1535efeba) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
theorem total1 :qxVnKgd.c1 := by
  change (0xe8816aca9c:ℤ) ≤ ∑ x∈(Icc (0:ℤ) 1958).sigma (fun q=>Icc 1 q),score 0 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (0:ℤ) 1958,II x
  rw [sum_Icc_shift]
  change _≤kA II 0 (980+979)
  rw [band_split II 0 980 979,show (0 + ↑(980:ℕ) :ℤ)=980 by decide,b0,b1] <;> decide
theorem total2 :qxVnKgd.c2 := by
  change (0x11eecc1e06:ℤ) ≤ ∑ x∈(Icc (0:ℤ) 1958).sigma (fun q=>Icc (max 0 (2*q-1959)) (q-1)),score 1 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (0:ℤ) 1958,lI x
  rw [sum_Icc_shift]
  change _≤kA lI 0 (980+979)
  rw [band_split lI 0 980 979,show (0 + ↑(980:ℕ) :ℤ)=980 by decide,b2,b3] <;> decide
theorem total3:qxVnKgd.c3:= by
  change (0x147a546f66d:ℤ) ≤ ∑ x∈(Icc (1:ℤ) 1856).sigma (fun p=>Icc (max 1 (p-1651)) (min (3919-2*p) ((3919-p)/2))),score 3 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1:ℤ) 1856,pG x
  rw [sum_Icc_shift]
  change _≤kA pG 1 (1306+(346+204))
  rw [band_split pG 1 1306 (346+204),show (1 + ↑(1306:ℕ) :ℤ)=1307 by decide,
    band_split pG 1307 346 204,show (1307 + ↑(346:ℕ) :ℤ)=1653 by decide,b4,b5,b6] <;> decide
theorem total4 :qxVnKgd.c4 := by
  change (0x532827c33:ℤ) ≤ ∑ x∈(Icc (1307:ℤ) 1959).sigma (fun p=>Icc (max (3920-2*p) (p-1651)) ((3919-p)/2)),score 4 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1307:ℤ) 1959,uW x
  rw [sum_Icc_shift]
  change _≤kA uW 1307 (551+102)
  rw [band_split uW 1307 551 102,show (1307 + ↑(551:ℕ) :ℤ)=1858 by decide,b7,b8] <;> decide
theorem total5:qxVnKgd.c5:= by
  change (0x54dcf32e1 :ℤ) ≤ ∑ x∈(Icc (1307:ℤ) 1959).sigma (fun p=>Icc (3920-2*p) ((3919-p)/2)),score 5 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1307:ℤ) 1959,y5 x
  rw [sum_Icc_shift]
  change _≤kA y5 1307 653
  rw [b9]
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
theorem proof :P6_8.c1 :=
  qxVnKgd.of_children total1 total2 total3 total4 total5
end P6_8_1
end

end Merged6967_DdZZ6ou4c

section Merged6967_Fast075
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_3_2
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 K1_13_7_5_3_3_3 MvPolynomial
open scoped Pointwise
variable {A : Fin 4 → Finset Exponent}
private def relIdeal (I : Ideal (Row A)) : Ideal (model A) where
  carrier := {f | ∀ d, (f : Ambient A).coeff d ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg d
    exact I.add_mem (hf d) (hg d)
  smul_mem' := by
    classical
    intro f g hg d
    change ((f : Ambient A) * (g : Ambient A)).coeff d ∈ I
    rw [coeff_mul]
    exact I.sum_mem fun e _ => I.mul_mem_left _ (hg e.2)
private theorem mem_relIdeal_of_val {I : Ideal (Row A)} {f : model A} {d : Exponent}
    {p : Row A} (h : (f : Ambient A) = monomial d p) (hp : p ∈ I) : f ∈ relIdeal I := by
  classical
  intro k
  rw [h, coeff_monomial]
  split_ifs
  · exact hp
  · exact I.zero_mem
private def cut (i : Fin 4) : model A :=
  tag (Finsupp.single i 1) (p := genericEquation A i) (by
    have h : (1 : Row A) ∈ piece A 0 := by
      have h0 : (0 : Exponent) ∈ exponentSet A 0 := by simp [exponentSet]
      exact Submodule.subset_span ⟨⟨0, h0⟩, rfl⟩
    simpa [shift, Finsupp.single_eq_pi_single] using equation_mul_mem_piece i h)
private def target (A : Fin 4 → Finset Exponent) (i : Fin 4) : Ideal (model A) :=
  Ideal.span {cut i} ⊔ relIdeal (prefixIdeal A i.val)
private theorem mem_target {i : Fin 4} {f : model A} :
    f ∈ target A i ↔ ∃ r : model A, f - cut i * r ∈ relIdeal (prefixIdeal A i.val) := by
  rw [target, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨r, b, hb, rfl⟩
    exact ⟨r, by simpa [mul_comm r (cut i)] using hb⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, _, hr, by rw [mul_comm r, add_sub_cancel]⟩
private theorem extract {i : Fin 4} {d : Degree} {p : Row A}
    (hp : p ∈ piece A (shift d i 1))
    (h : tag (stamp (shift d i 1)) hp ∈ target A i) :
    ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val := by
  obtain ⟨r, hr⟩ := mem_target.mp h
  refine ⟨(r : Ambient A).coeff (stamp d), coeff_mem r (stamp d), ?_⟩
  have H := hr (stamp (shift d i 1))
  change (monomial (stamp (shift d i 1)) p -
    monomial (Finsupp.single i 1) (genericEquation A i) * (r : Ambient A)).coeff
      (stamp (shift d i 1)) ∈ prefixIdeal A i.val at H
  rw [MvPolynomial.coeff_sub, coeff_monomial, ite_eq_left rfl, stamp_shift,
    add_comm (stamp d), coeff_monomial_mul] at H
  exact H
private theorem chart_degree (d : Degree) (i : Fin 4) (m : ℕ) :
    stamp (fun _ => m) + stamp (shift d i 1) =
      Finsupp.single i 1 + stamp (d + fun _ => m) := by
  rw [stamp_shift]
  ext j
  change m + (d j + (Finsupp.single i 1 : Exponent) j) = (Finsupp.single i 1 : Exponent) j + (d j + m)
  omega
private theorem monomial_mul_sub {R : Type*} [CommRing R] (a b c d : Exponent)
    (h : a + b = c + d) (p q r s : R) :
    (monomial a p : MvPolynomial (Fin 4) R) * monomial b q - monomial c r * monomial d s =
      monomial (c + d) (p * q - r * s) := by
  simp only [monomial_mul_monomial, h, map_sub]
private theorem chart_lift (h : ChartLifting A) (i : Fin 4) (d : Degree) {p : Row A}
    (hp : p ∈ piece A (shift d i 1)) (hrel : p ∈ prefixIdeal A (i.val + 1)) (a : Chart A) :
    ∃ m : ℕ, chart a ^ m * tag (stamp (shift d i 1)) hp ∈ target A i := by
  obtain ⟨m, r, hr, hrel'⟩ := h i d p hp hrel a
  let dm : Degree := d + (fun _ : Fin 4 => m)
  have hr' : r ∈ piece A (stamp dm) := by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact hr
  let t : model A := tag (A := A) (p := r) (stamp dm) hr'
  let g : model A := tag (A := A) (p := p) (stamp (shift d i 1)) hp
  let f : model A := chart a ^ m * g - cut i * t
  refine ⟨m, (mem_target (A := A) (i := i) (f := chart a ^ m * g)).mpr ⟨t, ?_⟩⟩
  change f ∈ relIdeal (prefixIdeal A i.val)
  refine mem_relIdeal_of_val (A := A) (I := prefixIdeal A i.val) (f := f)
    (d := Finsupp.single i 1 + stamp dm)
    (p := chartPower a m * p - genericEquation A i * r) ?_ hrel'
  calc
    (f : Ambient A) =
        ((chart a ^ m : model A) : Ambient A) * monomial (stamp (shift d i 1)) p -
          monomial (Finsupp.single i 1) (genericEquation A i) * monomial (stamp dm) r := rfl
    _ = _ := by
      rw [chart_pow_val]
      exact monomial_mul_sub _ _ _ _ (chart_degree d i m) (chartPower a m) p (genericEquation A i) r
private theorem pow_mul_mem_of_le {R : Type*} [CommRing R] (J : Ideal R) (x f : R)
    {l m : ℕ} (h : l ≤ m) (hl : x ^ l * f ∈ J) : x ^ m * f ∈ J := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm l k, pow_add, mul_assoc]
  exact J.mul_mem_left _ hl
private theorem uniform_power {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) (x : R) : ∃ M : ℕ, ∀ f : R,
      (∃ m : ℕ, x ^ m * f ∈ J) → x ^ M * f ∈ J := by
  let C : ℕ →o Submodule R R :=
    ⟨fun m => J.colon {x ^ m}, fun l m hlm f hf => by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] at hf ⊢
      exact pow_mul_mem_of_le J x f hlm hf⟩
  obtain ⟨M, hM⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) C
  refine ⟨M, fun f ⟨m, hm⟩ => ?_⟩
  have hle : C m ≤ C M := by
    rcases le_total m M with hl | hl
    · exact C.monotone hl
    · exact (hM m hl).ge
  have hmem : f ∈ C m := by
    change f ∈ J.colon {x ^ m}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] using hm
  have hmem' : f ∈ J.colon {x ^ M} := hle hmem
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f] using hmem'
private def gens (A : Fin 4 → Finset Exponent) (i : Fin 4) (b : ℕ) : Set (model A) :=
  {f | ∃ (d : Degree) (p : Row A) (hp : p ∈ piece A (shift d i 1)),
    (∀ j, d j ≤ b) ∧ p ∈ prefixIdeal A (i.val + 1) ∧ f = tag (stamp (shift d i 1)) hp}
private theorem bounded_gens (i : Fin 4) : ∃ B : ℕ, ∀ (d : Degree) {p : Row A}
    (hp : p ∈ piece A (shift d i 1)), p ∈ prefixIdeal A (i.val + 1) →
      tag (stamp (shift d i 1)) hp ∈ Ideal.span (gens A i B) := by
  classical
  let C : ℕ →o Submodule (model A) (model A) :=
    ⟨fun b => Ideal.span (gens A i b), fun _ _ hn => Ideal.span_mono (by
      rintro _ ⟨d, p, hp, hd, hrel, rfl⟩
      exact ⟨d, p, hp, fun j => (hd j).trans hn, hrel, rfl⟩)⟩
  obtain ⟨B, hB⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance C
  refine ⟨B, fun d p hp hrel => ?_⟩
  have h : tag (stamp (shift d i 1)) hp ∈ C (max B (Finset.univ.sup d)) :=
    Ideal.subset_span ⟨d, p, hp, fun j => (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _),
      hrel, rfl⟩
  rwa [← hB _ (le_max_left _ _)] at h
private theorem proj_mul_tag {f : model A} {d e : Exponent} {p : Row A}
    (hp : p ∈ piece A e) : proj (d + e) (f * tag e hp) = proj d f * tag e hp := by
  apply Subtype.ext
  change monomial (d + e) (((f : Ambient A) * monomial e p).coeff (d + e)) =
    monomial d ((f : Ambient A).coeff d) * monomial e p
  rw [monomial_mul_monomial, coeff_mul_monomial]
private theorem proj_add (d : Exponent) (f g : model A) :
    proj d (f + g) = proj d f + proj d g := by
  apply Subtype.ext
  change monomial d (((f : Ambient A) + (g : Ambient A)).coeff d) =
    monomial d ((f : Ambient A).coeff d) + monomial d ((g : Ambient A).coeff d)
  change monomial d ((f : Ambient A).coeff d + (g : Ambient A).coeff d) = _
  exact map_add (monomial d) _ _
private theorem stable_cut (hz : ∀ i, 0 ∈ A i) (h : ChartLifting A) (i : Fin 4) :
    ∃ b : ℕ, ∀ (d : Degree), (∀ j, b ≤ d j) →
      ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
        ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val := by
  classical
  obtain ⟨B, hB⟩ := bounded_gens (A := A) i
  choose M hM using fun a : Chart A => uniform_power (target A i) (chart a)
  let m := Finset.univ.sup M
  let N := Finset.univ.sup fun j => (A j).card * m
  have hkill (g : model A) (hg : g ∈ gens A i B) :
      chartIdeal A m ≤ (target A i).colon {g} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change chart a ^ m ∈ (target A i).colon {g}
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    obtain ⟨d, p, hp, _, hrel, rfl⟩ := hg
    apply pow_mul_mem_of_le _ _ _ (show M a ≤ m from Finset.le_sup (Finset.mem_univ a))
    exact hM a _ (chart_lift h i d hp hrel a)
  have hhigh (f : model A) (hf : f ∈ Ideal.span (gens A i B)) :
      ∀ (q : model A) (e : Exponent), (∀ j, B + 1 + N ≤ e j) → proj e (q * f) ∈ target A i := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      intro q e he
      obtain ⟨d, p, hp, hd, hrel, rfl⟩ := hg
      let k := stamp (shift d i 1)
      have hk (j : Fin 4) : k j ≤ B + 1 := by
        change d j + (Pi.single i 1 : Degree) j ≤ B + 1
        by_cases hij : j = i
        · subst j
          simpa only [Pi.single_eq_same] using Nat.succ_le_succ (hd i)
        · rw [Pi.single_eq_of_ne hij, add_zero]
          exact (hd j).trans (Nat.le_succ B)
      have hle : k ≤ e := fun j => (hk j).trans ((Nat.le_add_right _ _).trans (he j))
      have hsub : e - k + k = e := tsub_add_cancel_of_le hle
      have hs (j : Fin 4) : (A j).card * m ≤ (e - k) j := by
        have hN : (A j).card * m ≤ N :=
          Finset.le_sup (f := fun j => (A j).card * m) (Finset.mem_univ j)
        change (A j).card * m ≤ e j - k j
        have := hk j
        have := he j
        omega
      have hm := Submodule.mem_colon_singleton.mp (hkill _ ⟨d, p, hp, hd, hrel, rfl⟩
        (tag_mem_chartIdeal hz hs (coeff_mem q (e - k))))
      rw [← hsub]
      exact (proj_mul_tag (f := q) (d := e - k) (e := k) (show p ∈ piece A k from hp)).symm ▸ hm
    | zero =>
      intro q e he
      rw [mul_zero]
      have hz' : proj e (0 : model A) = 0 := by
        apply Subtype.ext
        change monomial e ((0 : Ambient A).coeff e) = 0
        simp
      rw [hz']
      exact (target A i).zero_mem
    | add f g _ _ hf hg =>
      intro q e he
      rw [mul_add, proj_add]
      exact (target A i).add_mem (hf q e he) (hg q e he)
    | smul r f _ hf =>
      intro q e he
      simpa only [smul_eq_mul, mul_assoc] using hf (q * r) e he
  refine ⟨B + 1 + N, fun d hd p hp hrel => extract hp ?_⟩
  have H := hhigh _ (hB d hp hrel) 1 (stamp (shift d i 1)) (fun j =>
    (hd j).trans (Nat.le_add_right _ _))
  rw [one_mul] at H
  convert H using 1
  apply Subtype.ext
  change monomial (stamp (shift d i 1)) p =
    monomial (stamp (shift d i 1)) ((monomial (stamp (shift d i 1)) p).coeff (stamp (shift d i 1)))
  rw [coeff_monomial, ite_eq_left rfl]
theorem proof : K1_13_7_5_3_3_3.c2 := by
  classical
  intro A hz h
  choose b hb using stable_cut hz h
  exact ⟨Finset.univ.sup b, fun i d hd => hb i d (fun j =>
    (Finset.le_sup (Finset.mem_univ i)).trans (hd j))⟩
end
end K1_13_7_5_3_3_3_2
end
section
namespace K1_14_2_2_7_3_3_1_4
theorem proof : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_3R_3_1_3_5.proof
end K1_14_2_2_7_3_3_1_4
end
section
namespace K1_14_2_2_7_2_3
theorem proof : K1_14_2_2_7_2.c3 :=
  of_place_laws K1_14_3R_3_1_3_1.proof K1_14_3R_3_1_3_2.proof
    K1_14_3R_3_1_3_3.proof K1_14_3R_3_1_3_4.proof K1_14_3R_3_1_3_5.proof
end K1_14_2_2_7_2_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 2000
namespace K1_13_7_1_2_2_1_1
noncomputable section
open K1_13_6_3_4 K1_13_7_1 K1_13_7_1_2_2_1 K1_13_7_2_5_4_1 MvPolynomial
variable {k E σ : Type} [Field k] [Field E] [Algebra k E]
private theorem map_component (p : MvPolynomial σ k) (n : ℕ) :
    MvPolynomial.map (algebraMap k E) (homogeneousComponent n p) =
      homogeneousComponent n (MvPolynomial.map (algebraMap k E) p) := by
  ext d
  by_cases hd : d.degree = n <;>
    simp only [MvPolynomial.coeff_map, coeff_homogeneousComponent, hd, ite_true, ite_false, map_zero]
private theorem ideal_eq_of_le_of_hilbert_eq [Finite σ]
    {A B : Ideal (MvPolynomial σ E)} (hAB : A ≤ B)
    (h : affineHilbertPolynomial A = affineHilbertPolynomial B) : A = B := by
  obtain ⟨a, ha⟩ := exists_eval_affineHilbertPolynomial A
  obtain ⟨b, hb⟩ := exists_eval_affineHilbertPolynomial B
  refine le_antisymm hAB ?_
  intro p hp
  let n := max p.totalDegree (max a b)
  let V := quotientDegreeLE A n
  let W := quotientDegreeLE B n
  let q := (Ideal.Quotient.factorₐ E hAB).toLinearMap
  have hq (x : V) : q x ∈ W := by
    obtain ⟨r, hr, he⟩ := mem_quotientDegreeLE.mp x.property
    rw [← he]
    exact mk_mem_quotientDegreeLE hr
  let f : V →ₗ[E] W := (q.domRestrict V).codRestrict W hq
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, he⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk A r, mk_mem_quotientDegreeLE hr⟩, Subtype.ext he⟩
  have he : Module.finrank E V = Module.finrank E W := by
    have hna : a ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    have hnb : b ≤ n := (le_max_right _ _).trans (le_max_right _ _)
    have he := (ha n hna).symm.trans ((congrArg (Polynomial.eval (n : ℚ)) h).trans (hb n hnb))
    change ((Module.finrank E V : ℕ) : ℚ) = (Module.finrank E W : ℚ) at he
    exact_mod_cast he
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he (f := f)).mpr hsurj
  let x : V := ⟨Ideal.Quotient.mk A p, mk_mem_quotientDegreeLE (le_max_left _ _)⟩
  have hx : f x = f 0 := by
    rw [map_zero]
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val (hinj hx))
private theorem boundary_map (I : Ideal (MvPolynomial TaylorIndex k)) :
    boundaryIdeal (I.map (MvPolynomial.map (algebraMap k E))) =
      (boundaryIdeal I).map (MvPolynomial.map (algebraMap k E)) := by
  let f : MvPolynomial TaylorIndex k →+* MvPolynomial TaylorIndex E :=
    MvPolynomial.map (algebraMap k E)
  symm
  apply ideal_eq_of_le_of_hilbert_eq
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    change f (homogeneousComponent n p) ∈ boundaryIdeal (I.map f)
    rw [map_component]
    apply Ideal.subset_span
    exact ⟨f p, n, Ideal.mem_map_of_mem _ hp,
      (Finset.sup_mono (support_map_subset (algebraMap k E) p)).trans hn, rfl⟩
  · rw [K1_13_5_5_2.hilbertPolynomial_map, K1_13_5_4_4_2.hilbertPolynomial_boundary,
      K1_13_5_4_4_2.hilbertPolynomial_boundary, K1_13_5_5_2.hilbertPolynomial_map]
private theorem affine_regular {t : Option TaylorIndex → E} (ht : AlgebraicIndependent k t)
    (I : Ideal (MvPolynomial TaylorIndex k)) :
    IsLeftRegular (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k E)))
      (affinePolynomial t)) := by
  classical
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  let a : Option TaylorIndex → MvPolynomial TaylorIndex k :=
    fun i => i.elim 1 MvPolynomial.X
  have he : (∑ i, C (t i) * MvPolynomial.map (algebraMap k E) (a i)) = affinePolynomial t := by
    simp [Fintype.sum_option, a, affinePolynomial]
  obtain ⟨m, hm⟩ := generic_torsion ht I a none p (he.symm ▸ hx)
  simpa [a] using hm
private def slope (t : Option TaylorIndex → E) : MvPolynomial TaylorIndex E :=
  ∑ i, C (t (some i)) * MvPolynomial.X i
private theorem linear_sum_homogeneous {σ F : Type} [Fintype σ] [Field F] (a : σ → F) :
    (∑ i, C (a i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ F 1).sum_mem fun i _ => isHomogeneous_C_mul_X _ i
private theorem slope_homogeneous (t : Option TaylorIndex → E) : (slope t).IsHomogeneous 1 :=
  linear_sum_homogeneous (fun i : TaylorIndex => t (some i))
private theorem generic_slope_eventually_regular {t : Option TaylorIndex → E}
    (ht : AlgebraicIndependent k t) (I : Ideal (MvPolynomial TaylorIndex k)) :
    EventuallyRegularHomogeneous
      (boundaryIdeal (I.map (MvPolynomial.map (algebraMap k E)))) (slope t) := by
  let J := I.map (MvPolynomial.map (algebraMap k E))
  let B := boundaryIdeal J
  apply K1_13_7_2_5_4_1_1.proof B (slope t) (boundary_homogeneous J) (slope_homogeneous t)
  intro P hP hi hℓ
  obtain ⟨i, hi⟩ := hi
  obtain ⟨x, he⟩ := (isAssociatedPrime_iff.mp hP).2
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmul : slope t * p ∈ B := by
    rw [he, Submodule.mem_colon_singleton, Submodule.mem_bot] at hℓ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hℓ
  have hgen := generic_torsion (ht.comp some (Option.some_injective TaylorIndex))
    (boundaryIdeal I) MvPolynomial.X i p
  simp only [MvPolynomial.map_X, Function.comp_apply, ← boundary_map] at hgen
  obtain ⟨m, hm⟩ := hgen hmul
  have hpow : MvPolynomial.X i ^ m ∈ P := by
    rw [he, Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk B (MvPolynomial.X i ^ m) * Ideal.Quotient.mk B p = 0
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  exact hi (hP.isPrime.mem_of_pow_mem _ hpow)
private theorem degree_drop {p : MvPolynomial σ E} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) (h : homogeneousComponent (n + 1) p = 0) :
    p.totalDegree ≤ n := by
  apply Finset.sup_le
  intro d hd
  have hle := (le_totalDegree hd).trans hp
  have hne : d.degree ≠ n + 1 := by
    intro he
    apply mem_support_iff.mp hd
    simpa [coeff_homogeneousComponent, he] using congrArg (fun q : MvPolynomial σ E => q.coeff d) h
  exact Nat.le_of_lt_succ (lt_of_le_of_ne (show d.degree ≤ n + 1 from hle) hne)
private theorem strict_filtered {t : Option TaylorIndex → E}
    {J : Ideal (MvPolynomial TaylorIndex E)}
    (h : EventuallyRegularHomogeneous (boundaryIdeal J) (slope t)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ quotientDegreeLE J (n + 1),
      Ideal.Quotient.mk J (affinePolynomial t) * x ∈ quotientDegreeLE J (n + 1) →
      x ∈ quotientDegreeLE J n := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn x hx hfx => ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hx
  obtain ⟨q, hq, hqeq⟩ := mem_quotientDegreeLE.mp hfx
  have hrel : affinePolynomial t * p - q ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqeq, sub_self]
  have hform : affinePolynomial t = C (t none) + slope t := rfl
  have hlin := (slope_homogeneous t).totalDegree_le
  have hdeg : (affinePolynomial t * p - q).totalDegree ≤ n + 2 := by
    have hfd : (affinePolynomial t).totalDegree ≤ 1 := by
      rw [hform]
      exact (totalDegree_add _ _).trans (max_le (by simp) hlin)
    exact (totalDegree_sub _ _).trans (max_le
      ((totalDegree_mul _ _).trans (by omega)) (by omega))
  have hcomp : homogeneousComponent (n + 2) (affinePolynomial t * p - q) =
      slope t * homogeneousComponent (n + 1) p := by
    rw [hform, add_mul, map_sub, map_add,
      homogeneousComponent_eq_zero _ q (by omega), sub_zero,
      homogeneousComponent_eq_zero _ (C (t none) * p) (by
        apply (totalDegree_mul _ _).trans_lt
        simp only [totalDegree_C, zero_add]
        omega), zero_add, component_mul_linear (slope_homogeneous t)]
  have hlead : slope t * homogeneousComponent (n + 1) p ∈ boundaryIdeal J := by
    rw [← hcomp]
    exact Ideal.subset_span ⟨_, n + 2, hrel, hdeg, rfl⟩
  have hmem := hN (n + 1) (by omega) _ (homogeneousComponent_isHomogeneous _ _) hlead
  obtain ⟨r, hr, hrd, htop⟩ := K1_13_5_4_4_2.lift_boundary_component J hmem (n + 1)
  have hd : (p - r).totalDegree ≤ n :=
    degree_drop ((totalDegree_sub _ _).trans (max_le hp hrd)) (by
      rw [map_sub, htop, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
        sub_self])
  have hq' : Ideal.Quotient.mk J (p - r) = Ideal.Quotient.mk J p := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hr, sub_zero]
  rw [← hq']
  exact mk_mem_quotientDegreeLE hd
theorem proof : K1_13_7_1_2_2_1.c1 := by
  intro k E _ _ _ t ht I
  exact ⟨affine_regular ht I, strict_filtered (generic_slope_eventually_regular ht I)⟩
end
end K1_13_7_1_2_2_1_1
end

end Merged6967_Fast075

section Merged6967_PortLowBase
set_option Elab.async false




set_option Elab.async false

-- merged module PortHighBase
section Merged_PortHighBase

-- merged module PortBase
section Merged_PortBase
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at h hr ⊢
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
theorem type_one_bad_count_of_syndromes {F ι : Type}
    [Field F] [Fintype ι] [DecidableEq ι] (x u v : ι → F) (hx : Function.Injective x)
    (k a p : ℕ) (hk : k ≤ Fintype.card ι) (hp : 1 < p)
    (htype : Principal.TypeOneSyndromes x u v k p)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k a γ) :
    Γ.card ≤ 1 :=
  Principal.type_one_bad_count x hx u v k a p hk hp htype Γ hΓ
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t + 1) → F) (hc : (coefficientBlocks p x u v L t).mulVec c = 0) :
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0 := by
  funext i
  have h0 := congrFun hc (0, i.2)
  have h1 := congrFun hc (1, i.2)
  have h2 := congrFun hc (2, i.2)
  have h3 := congrFun hc (3, i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientBlocks, Fin.reduceEq,
    ite_true, ite_false, Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi : i.1 = 0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R := F) * C (∑ j, syndrome x v (i.2.val + j.val) * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h0, h1, map_zero, mul_zero, add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R := F) ^ p * C (∑ j, syndrome x v (i.2.val + j.val) ^ p * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h2, h3, map_zero, mul_zero, add_zero]
theorem constantRankCount {E : Type} [Field E]
    (φ : (Polynomial F) →+* E) (hφ : Function.Injective φ) (p : ℕ) [ExpChar F p] (hp : 1 ≤ p)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A) (hL : k + L = A)
    (ht : A + t = Fintype.card ι)
    (r : ℕ) (hgeneric : ((stacked p x u v L t).map φ).rank = r)
    (hconstant : (coefficientBlocks p x u v L t).rank = r)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k A γ) : Γ.card ≤ p * r := by
  let M := stacked p x u v L t
  let C₀ := coefficientBlocks p x u v L t
  let W := LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h := LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientBlocks p x u v L t).rank + Module.finrank F W = _ at h
    rw [hconstant, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j)) = 0 :=
    coefficientKernel_annihilates p x u v L t c hc
  have hminor : (NormalFiber.pivot B).det.natDegree ≤ p * r := by
    have h := NormalFiber.minor_degree_le φ M r B (fun _ => p) (by
      intro i j
      exact (stacked_entry_natDegree p x u v L t i j).trans (by split_ifs <;> omega))
    simpa [Nat.mul_comm] using h
  exact Principal.constant_kernel_count p x hx hfixed u v k A L t (p * r) hkA hL ht
    _ B.minor_ne hminor (Principal.constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW)
    Γ hΓ
open K1_1
def nativeMoments (u : Words) : Fin 2 → ℕ → Frac :=
  fun b j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) b j)
theorem independent_nativeMoments (u : Words)
    (h : ¬ TypeAtMostOne u) : IndependentMoments (nativeMoments u) k := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective (Polynomial K) Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j
end
end P0
end

end Merged_PortBase

-- merged module PortHighBase
section Merged_PortHighBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K k p node twist agreement t heightCap highPrefix)
open K1_14 (L FX Seeds Equation Jet Shape Band Banks liftPoly graphEval atX
  triangle slots shapeSum sourceDebit seedHasse SeedBound)
open K1_14_3 (Surface Parent NoMovingCommon Compatible RowCaps ProjectedProduct)
open scoped BigOperators
def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,6,188,1024,1422,290,28962⟩
  else if w ≤ 8249 then ⟨8249,4,96,582,809,165,11805⟩
  else if w ≤ 23999 then ⟨23999,4,46,582,809,165,8216⟩
  else ⟨heightCap, 4,35,582,809,165,7295⟩
def freeShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨55,76,17,1036⟩,⟨82,113,25,1601⟩] i
  else ![⟨34,47,10,515⟩,⟨58,80,17,940⟩] i
def movingShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨138,191,39,4990⟩,⟨203,282,58,7726⟩] i
  else ![⟨67,93,18,1857⟩,⟨124,172,35,3138⟩] i
def reserve (i : Fin 2) : ℕ := ![0,5] i
def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩
def fullShape (w : ℤ) : Shape :=
  { terminalShape w with U := if w ≤ 3554 then 141471 else 59515 }
def fullCutoff (s : Shape) : ℕ := s.m * agreement - 1
def reserveCutoff (w : ℤ) (s : Shape) (i : Fin 2) : ℕ :=
  fullCutoff s - 2 * w.toNat * reserve i
structure BufferedPair (w : ℤ) (rows : Banks) (i : Fin 2) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows (freeShape w i) (reserveCutoff w (freeShape w i) i)
  moving_mem : moving ∈ rows (movingShape w i) (reserveCutoff w (movingShape w i) i)
  no_moving : NoMovingCommon free moving
def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ Compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def rawWidth (w : ℤ) (q j : ℕ) : ℕ :=
  (band w).multiplicity * agreement + j - q * (131071 - w.toNat)
def rawVolume (w : ℤ) : ℕ :=
  triangle (band w).subbankSeeds * shapeSum (terminalShape w) (rawWidth w)
def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + (fullCutoff (terminalShape w) - W) / (2 * w.toNat) - j
def TerminalDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < (band w).multiplicity * agreement, ∀ P ∈ rows (terminalShape w) W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff
def seedGain (w : ℤ) : ℕ :=
  let b := band w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShape w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r * v) - slots U ((r + 1) * v)) * (rawWidth w q j - 2 * w.toNat * (j + r))
def curveFactor (d : ℕ) : ℕ := t / (agreement - d) + 1
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, PairPass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K p node twist agreement )
open K1_14 (L FX Seeds Equation Banks liftPoly graphEval atX atMark
  seedEmbedding SeedBound frobenius_coefficient_exception_count)
open scoped BigOperators
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset Polynomial
open P0 (agreement)
open K1_14 (FX Jet Equation shapeSum slots triangle SeedBound)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_pow )
open K1_14_4 (shapeSum_swap gradeWidth_card position_sum)
open K1_14_4 (gradeMap mem_filtered finrank_le_grades)
private def gradeCapacity (w : ℤ) (W j : ℕ) : ℕ :=
  let b := band w
  gradeWidth (131071 - w.toNat) b.jetBound W j *
    slots b.subbankSeeds (forcedPower w W j * (b.seedBound + 1))
private def cutoffCapacity (w : ℤ) (W : ℕ) : ℕ :=
  ∑ j ∈ range ((band w).vBound + 1), gradeCapacity w W j
private theorem cutoffCapacity_eq (w : ℤ) (W : ℕ) (hk : 0 < 131071 - w.toNat) :
    cutoffCapacity w W =
      shapeSum (terminalShape w) (fun q j =>
        if q * (131071 - w.toNat) ≤ W + j then
          slots (band w).subbankSeeds (forcedPower w W j * ((band w).seedBound + 1))
        else 0) := by
  rw [← shapeSum_swap]
  unfold cutoffCapacity
  apply sum_congr rfl
  intro j _
  rw [gradeCapacity, gradeWidth_card _ _ _ _ hk, sum_mul]
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp
theorem sum_cutoffCapacity_add_seedGain (w : ℤ) (hlo : 2481 ≤ w) (hhi : w ≤ 32766) :
    (∑ W ∈ range ((band w).multiplicity * agreement), cutoffCapacity w W) + seedGain w =
      rawVolume w := by
  let b := band w
  let k := 131071 - w.toNat
  let top := b.multiplicity * agreement
  have hk : 0 < k := by dsimp [k]; omega
  have hs : 0 < 2 * w.toNat := by omega
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range top, shapeSum (terminalShape w) (F W)) =
        shapeSum (terminalShape w) (fun q j => ∑ W ∈ range top, F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  change (∑ W ∈ range top, cutoffCapacity w W) + seedGain w = rawVolume w
  simp_rw [cutoffCapacity_eq w _ hk]
  rw [hswap]
  simp only [seedGain, rawVolume, shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hjk : j ≤ q * k := hjq.trans (by
    simpa using Nat.mul_le_mul_left q (show 1 ≤ k by omega))
  exact position_sum top (2 * w.toNat) (q * k) j b.subbankSeeds (b.seedBound + 1)
    hjk hs (by omega)
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P0 (K I node agreement)
open K1_14_6 (occupancy)
structure FixedWord (w : I → K) (T : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩
theorem incidence_arithmetic (errors m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x) (he : 0 < errors)
    (hsecond : (m*x)^2 ≤ (x+errors) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+errors)*cap) :
    gap*m ≤ errors*cap + gap := by
  have hcancel : m*x^2 ≤ (x+errors) * (x + (m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsecond
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := Int.ofNat_sub (by omega)
  have hX : ((x - gap : ℕ) : ℤ) = (x : ℤ)-gap := Int.ofNat_sub hx
  have hcancelZ := Int.ofNat_le.mpr hcancel
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*errors - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*errors*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (errors : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*errors < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*errors - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*errors := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*errors*x ≤ (cap : ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible, bigger]
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ P0.t * cap + (agreement - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (agreement - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : agreement ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := agreement - common.card
  let t := d - common.card
  have ht : t = x - (agreement - d) := by dsimp [t, x]; omega
  have hx : agreement - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + P0.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (180217 - common.card) + 81927
    have hbound : common.card ≤ 180217 := hcommon.trans hd.le
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic P0.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset MvPolynomial
open P0 (K I node agreement)
open K1_14_6 (LinearCover LinearRing ClosedField mixedDegree)
open K1_14_6 (card_le_sum_cover curve_degree_nat)
open K1_14_6.LinearCover (slice «section» cut_data zero_dim_count)
open scoped BigOperators Polynomial
private theorem curve_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < agreement)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hδdeg⟩ := curve_degree_nat P hP hdim
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ δ := by
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := LinearCover.section C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := LinearCover.cut_data C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((LinearCover.slice C V Q).card : ℚ) ≤ affineDegree Q := by
      have hQdim := (dims Q hQ).2
      rw [hdim] at hQdim
      exact LinearCover.zero_dim_count C ((filter_subset _ _).trans ((filter_subset _ _).trans hU))
        Q (by omega) (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((LinearCover.slice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    have hbound := hsumQ.trans ((sum_le_sum hone).trans (degree.trans_eq hδdeg))
    exact_mod_cast hbound
  have hcount := section_capacity hword hd δ hsection
  let gap := agreement - d
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hfactor : P0.t < gap * curveFactor d := by
    change P0.t < gap * (P0.t / gap + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have heq := Nat.mod_add_div P0.t gap
    have hr := Nat.mod_lt P0.t hgap
    omega
  suffices hcard : U.card ≤ curveFactor d * δ by
    rw [hδdeg, ← Nat.cast_mul]
    exact_mod_cast hcard
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left gap (show curveFactor d * δ + 1 ≤ U.card by omega)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hfactor hδ
  change gap * U.card ≤ P0.t * δ + gap at hcount
  omega
end
end P0_10
end
section
namespace P0_10
noncomputable section
open P0
open K1_14 (Equation SeedBound atMark)
open K1_14_6 (mixedDegree)
end
end P0_10
end
section
set_option backward.isDefEq.respectTransparency false
namespace P0_10_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10 (AdjacentChart)
open K1_14 (L liftPoly)
open K1_14_1 Polynomial
open scoped Polynomial
open K1_14_1_1 (blockContribution)
set_option maxHeartbeats 800000 in
theorem crt_lift {h : ℕ} (D : PoleData h) : Nonempty (CRTLift D) := by
  choose d N hN using blockContribution D
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2⟩⟩
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I K node)
open K1_14 (L Shape Jet liftPoly jetAt shapeSum)
open K1_14_1 K1_14_1_5 Polynomial
open K1_14_1_2 (span_vanish composed composed_degree specialized_poles composed_contact)
open scoped Polynomial BigOperators
open K1_14_1_5 (finrank_ambient trueWidth trueWidth_eq_add)
private theorem zero_of_poles_and_hits {h A : ℕ} {D : PoleData h}
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    {s : Shape} {W : ℕ} {Q : (Polynomial L)}
    (hdeg : Q.natDegree ≤ W+(s.B+s.J)*(2*h))
    (hpole : poleProduct D ^ (s.B+s.J) ∣ Q)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hcontact : ∀ k ∈ hits, (Polynomial.X-C (nodeL k)) ^ s.m ∣ Q)
    (hW : W < s.m*A) : Q = 0 := by
  by_contra hne
  obtain ⟨T, hT⟩ := hpole
  have hTne : T ≠ 0 := by intro he; simp [hT, he] at hne
  have hmonic : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
  have hDdeg : (poleProduct D).natDegree = 2*h := by
    rw [poleProduct, natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hTdeg : T.natDegree ≤ W := by
    rw [hT, natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne, natDegree_pow, hDdeg] at hdeg
    omega
  have hroot (k : I) : IsCoprime (Polynomial.X-C (nodeL k)) (poleProduct D) := by
    refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    simpa [IsRoot, poleProduct] using mul_ne_zero (hnode 0 k) (hnode 1 k)
  have hcontacts (k : I) (hk : k ∈ hits) : (Polynomial.X-C (nodeL k)) ^ s.m ∣ T :=
    ((hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hcontact k hk))
  have hinj : Function.Injective nodeL := (algebraMap K L).injective.comp node.injective
  have hh := K1_11.eq_zero_of_many_contacts hits nodeL hinj s.m T hcontacts
    (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard)))
  exact hTne hh
theorem contact_vanish {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    (z : K) (S : (Polynomial K)) (hres : MarkResidues D z S)
    (hdeg : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hhits : ∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k)
    (s : Shape) (W : ℕ) (hW : W < s.m*A) (P : Jet)
    (hP : P ∈ evaluated Crt word s W) : jetAt P z S = 0 := by
  apply span_vanish z S _ hP
  intro Q hQ
  obtain ⟨⟨ha, hc⟩, hp⟩ := hQ
  exact zero_of_poles_and_hits hnode (composed_degree ha _ _ hdeg)
    (specialized_poles Crt hres hp) hits hcard
    (fun k hk => composed_contact hc _ _ k (hhits k hk)) hW
theorem ambient_bound {h : ℕ} (hhi : h ≤ 131071) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) :
    rawVolumeAt h s W + poleCredit h s ≤ Module.finrank L (ambient h s W) := by
  rw [finrank_ambient]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W + 1 + j - q * (131071 - h)) +
        2 * h * shapeSum s (fun q _ => s.B + s.J - q) := by
    unfold shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add hhi hw (by simpa using hq) (by simpa using hj)
  simp only [hsum, rawVolumeAt, poleCredit, Nat.mul_add, Nat.mul_assoc, Nat.le_refl]
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L Shape Jet)
open K1_14_1 Polynomial
open K1_14_1_4 (Bounded forward_apply rawBlock_degree quotient_positions rawOrdinate rawVelocity
  substitute_C substitute_X)
open scoped Polynomial BigOperators
open K1_14_1_4 (bounded_mono bounded_add bounded_sum bounded_mul bounded_jetConstant bounded_y bounded_v bounded_pow crt_degree ambient_degree)
open K1_14_1_4 (rawPosition specialized_center specialized_leading specialized doubleMap)
private theorem forward_bounded {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    {s W P} (hp : P ∈ ambient h s W) :
    Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) (forward Crt P) := by
  let u := 131071-h
  let v := u-1
  have huv : v+1 = u := by dsimp [u, v]; omega
  have hd : 131071+h = 2*h+u := by dsimp [u]; omega
  have hy : Bounded u v (2*h+u) (rawOrdinate D Crt) :=
    bounded_add (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_y u v))
      (bounded_jetConstant ((crt_degree D Crt).trans (by omega)))
  have hv : Bounded u v (2*h+v) (rawVelocity D Crt) := by
    have hh' : (rawBlock D).derivative.natDegree ≤ 2*h-1 :=
      (natDegree_derivative_le _).trans (by rw [rawBlock_degree])
    refine bounded_add (bounded_add
      (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_v u v)) ?_) ?_
    · exact bounded_mono (bounded_mul (bounded_jetConstant hh') (bounded_y u v)) (by omega)
    · exact bounded_jetConstant (((natDegree_derivative_le _).trans
        (Nat.sub_le_sub_right (crt_degree D Crt) 1)).trans (by omega))
  change Bounded u v _ (forward Crt P)
  rw [forward_apply, P.as_sum_support_C_mul_X_pow, map_sum]
  apply bounded_sum
  intro j hj
  rw [map_mul, map_pow, (P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C, substitute_X]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X, RingHom.comp_apply]
  apply bounded_sum
  intro i hi
  have hdeg := ambient_degree hp (mem_support_iff.mp hi)
  have hw : ((P.coeff j).coeff i).natDegree + (2*h+u)*i + (2*h+v)*j ≤
      W+(s.B+s.J)*(2*h) := by
    have hjmul : j*(2*h+u) = (2*h+v)*j+j := by
      rw [show 2*h+u = (2*h+v)+1 by omega, Nat.mul_add, Nat.mul_one, Nat.mul_comm j (2*h+v)]
    rw [hd, Nat.add_mul, hjmul, Nat.mul_comm i (2*h+u)] at hdeg
    omega
  apply bounded_mono (bounded_mul (bounded_mul ?_ (bounded_pow hy i)) (bounded_pow hv j)) hw
  exact bounded_jetConstant natDegree_map_le

/-- Remove the actual CRT pole divisor while keeping the bound on every
physical coefficient of the quotient. -/
theorem complete_raw_bounded {h} (hpos : 0<h) (hh : h≤131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) {s W P} (mem : P∈complete Crt word s W) :
    ∃ Q : RawSource, forward Crt P = jetConstant ((rawBlock D)^(s.B+s.J))*Q ∧
      Bounded (131071-h) (131071-h-1) W Q := by
  obtain ⟨Q,eq⟩ := mem.2
  refine ⟨Q,eq,?_⟩
  intro j i a nz
  have qn : (Q.coeff j).coeff i≠0 := by
    intro zero;exact nz (by rw [zero,coeff_zero])
  have product : ((forward Crt P).coeff j).coeff i =
      (rawBlock D)^(s.B+s.J)*(Q.coeff j).coeff i := by
    rw [eq]
    change ((C (C ((rawBlock D)^(s.B+s.J)))*Q).coeff j).coeff i=_
    rw [coeff_C_mul,coeff_C_mul]
  have nonzero : ((forward Crt P).coeff j).coeff i ≠ 0 := by
    rw [product]
    exact mul_ne_zero ((K1_14_1_4.rawBlock_monic D).pow (s.B+s.J)).ne_zero qn
  have cap := forward_bounded hpos hh Crt mem.1.1 j i
    (((forward Crt P).coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr nonzero)
  rw [product,((K1_14_1_4.rawBlock_monic D).pow _).natDegree_mul' qn,
    natDegree_pow,rawBlock_degree] at cap
  have small := le_natDegree_of_ne_zero nz
  omega

theorem rawPosition_zero {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hw : W < (131071-h)*i+(131071-h-1)*j) : rawPosition Crt j i P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (rawPosition Crt j i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    apply LinearMap.mem_ker.mpr
    rcases hA.2 with ⟨Q, hQ⟩
    have hz := quotient_positions s W (forward_bounded hpos hh Crt hA.1.1) hQ j i hw
    change ((specialized Crt (centerEval A)).coeff j).coeff i = 0
    rw [specialized_center, hQ]
    simp only [map_mul, doubleMap, coe_mapRingHom, Polynomial.map_C, jetConstant,
      RingHom.comp_apply, coeff_C_mul, coeff_map, hz, map_zero, mul_zero]
  exact LinearMap.mem_ker.mp (hsub hP)
theorem leading_bound {h : ℕ} (hl : 0 < h) (hh : h ≤ 131070)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (P : Jet) (hP : P ∈ evaluated Crt word s W) (hn : P ≠ 0) :
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree := by
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  change (i+j)*(131071-h) ≤ W+j
  have huv : 131071-h = (131071-h-1)+1 := by omega
  have he : (i+j)*(131071-h) = (131071-h)*i+(131071-h-1)*j+j := by
    have hj : j*(131071-h) = (131071-h-1)*j+j := by
      calc
        j*(131071-h) = j*((131071-h-1)+1) := congrArg (j*·) huv
        _ = (131071-h-1)*j+j := by ring
    rw [Nat.add_mul, hj, Nat.mul_comm i]
    omega
  rw [he]
  by_contra! hw
  have hz := rawPosition_zero hl hh Crt word hP j i (by omega)
  obtain ⟨hj, hi, hn'⟩ := specialized_leading Crt hn
  change ((specialized Crt P).coeff j).coeff i = 0 at hz
  have hj' : (specialized Crt P).natDegree = j := hj
  have hi' : (specialized Crt P).leadingCoeff.natDegree = i := hi
  rw [← hj', coeff_natDegree, ← hi', coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')) hz
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L FX Shape Jet shapeSum triangle seedHasse)
open K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial BigOperators
open K1_14_1_6 (Low localSpan generators nodeMap localSpan_finrank)
open K1_14_1_3 (evaluatedHasse evaluatedHasse_eq centerEval_clear)
theorem physical_bound (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (ambient h s W) ≤
      physicalDebit s + Module.finrank L (contacted h word s W) := by
  classical
  by_cases hzero : Module.finrank L (ambient h s W) = 0
  · simp [hzero]
  have : Module.Finite L (ambient h s W) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have : Module.Finite L (localSpan s) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s))
  let f : ambient h s W →ₗ[L] (I → localSpan s) :=
    LinearMap.pi (K1_14_1_6.nodeMap h word s W)
  let g : LinearMap.ker f →ₗ[L] contacted h word s W :=
    LinearMap.codRestrict (contacted h word s W)
      ((ambient h s W).subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨P.val.property, ?_⟩
        intro i a b j e hab
        have hz := LinearMap.mem_ker.mp P.property
        exact congrArg (fun z : I → localSpan s => (z i).val (Low.mk j b a e hab)) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : contacted h word s W => R.val) hPQ
  have hle : contacted h word s W ≤ ambient h s W := inf_le_left
  have : Module.Finite L (contacted h word s W) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hnull := f.finrank_range_add_finrank_ker
  have htarget : Module.finrank L (I → localSpan s) ≤ physicalDebit s := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _ : I, Module.finrank L (localSpan s)) ≤
          ∑ _ : I, (shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))) * triangle s.U :=
        Finset.sum_le_sum (fun _ _ => localSpan_finrank s)
      _ = physicalDebit s := by
        rw [Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul, physicalDebit]
        ac_rfl
  have hrange := (LinearMap.range f).finrank_le.trans htarget
  omega
theorem evaluated_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {P : Jet} (hP : P ∈ evaluated Crt word s W) (i : Fin 2) (r : ℕ) :
    seedHasse i r P ∈ evaluated Crt word s (W+2*h*r) := by
  let target := evaluated Crt word s (W+2*h*r)
  have hsub : evaluated Crt word s W ≤ target.comap (evaluatedHasse i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      change evaluatedHasse i r (centerEval Q) ∈ target
      have hmem : cleared D i r Q ∈ complete Crt word s (W+2*h*r) :=
        ⟨⟨ambient_cleared D hQ.1.1 i r, K1_14_1_3_1.proof h D word s Q hQ.1.2 i r⟩,
          K1_14_1_3_2.proof h D Crt s Q hQ.2 i r⟩
      have he : centerEval (cleared D i r Q) ∈ target :=
        Submodule.subset_span ⟨cleared D i r Q, hmem, rfl⟩
      rw [centerEval_clear] at he
      have hn : algebraMap (Polynomial L) FX (D.block i ^ (2*r)) ≠ 0 := by
        rw [← map_zero (algebraMap (Polynomial L) FX)]
        exact (IsFractionRing.injective (Polynomial L) FX).ne (pow_ne_zero (2*r) (D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp he)
  rw [← evaluatedHasse_eq]
  exact hsub hP
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1_1
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_3 Polynomial
open scoped BigOperators Polynomial
open K1_14_1_7_3 (generic_den generic_centre)
theorem regular_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) : Nonempty (RegularDeformation D Crt) := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, ?_⟩⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]
  · apply simplePoles hh hp D _
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb
end
end P0_10_1_1
end
section
namespace P0_10_5
open K1_14 (Shape slots shapeSum sourceDebit)
open Finset
open scoped BigOperators
open K1_14_5 (shape_sum_flip)
def cut (s : Shape) (v lo t : ℕ) : ℕ :=
  min (s.B + 1)
    ((s.m * P0.agreement + (t - min t (s.U / v)) - 2 * lo * t - 1) / (131071 - lo) + 1)
def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)
end P0_10_5
end
section
namespace P0_10_5
open K1_14 (Shape slots triangle)
open Finset
open scoped BigOperators
private def ValidCut (s : Shape) (v lo t : ℕ) : Prop :=
  let k := cut s v lo t
  min t s.J ≤ k ∧ (k-1) * (131071-lo) + 2*lo*t < s.m*P0.agreement + (t - min t (s.U/v))
private instance (s : Shape) (v lo t : ℕ) : Decidable (ValidCut s v lo t) := by
  unfold ValidCut
  infer_instance
private def moments (s : Shape) (v i : ℕ) : ℕ × ℕ × ℕ :=
  let R := s.U / v
  let n := min R i
  let a := weight s v 0
  let b := v*v
  let s₁ := n*(n-1)/2
  let s₂ := n*(n-1)*(2*n-1)/6
  let last := if R < i then slots s.U (R*v) else 0
  ⟨a*n - b*s₁ + last, a*s₁ - b*s₂ + last*R, a*s₂ - b*s₁*s₁ + last*R*R⟩
private def MomentStep (s : Shape) (v r : ℕ) : Prop :=
  let w := weight s v r
  let p := moments s v r
  let q := moments s v (r+1)
  q.1 = p.1 + w ∧ q.2.1 = p.2.1 + w*r ∧ q.2.2 = p.2.2 + w*r*r
private instance (s : Shape) (v r : ℕ) : Decidable (MomentStep s v r) := by
  unfold MomentStep
  infer_instance
structure Row where
  ok : Bool
  base : ℤ
  slope : ℤ
def Row.add (x y : Row) : Row := ⟨x.ok && y.ok, x.base + y.base, x.slope + y.slope⟩
theorem Row.eq_of_check {x y : Row}
    (h : ((x.ok == y.ok) && (x.base == y.base) && (x.slope == y.slope)) = true) : x = y := by
  cases x
  cases y
  simp only [Bool.and_eq_true, beq_iff_eq, Row.mk.injEq] at h ⊢
  tauto
def scan (f : ℕ → Row) (a : ℕ) : ℕ → Row
  | 0 => ⟨true, 0, 0⟩
  | n+1 => (scan f a n).add (f (a+n))
private theorem scan_add (f : ℕ → Row) (a n m : ℕ) :
    scan f a (n+m) = (scan f a n).add (scan f (a+n) m) := by
  induction m with
  | zero => cases scan f a n; simp [scan, Row.add]
  | succ m ih =>
    change (scan f a (n+m)).add (f (a+(n+m))) =
      (scan f a n).add ((scan f (a+n) m).add (f ((a+n)+m)))
    rw [ih]
    simp only [Row.add, Bool.and_assoc, add_assoc]
theorem joinRows {f : ℕ → Row} (a n m : ℕ) (x y : Row) {z : Row}
    (hx : scan f a n = x) (hy : scan f (a+n) m = y) (hz : x.add y = z) :
    scan f a (n+m) = z := by rw [scan_add, hx, hy, hz]
theorem scan_sum (f : ℕ → Row) (a n : ℕ) (slope : Bool) :
    (if slope then (scan f a n).slope else (scan f a n).base) =
      ∑ i ∈ range n, if slope then (f (a+i)).slope else (f (a+i)).base := by
  cases slope <;> induction n with
  | zero => simp [scan]
  | succ n ih => simp_all only [scan, Row.add, Bool.false_eq_true, ite_false, ite_true,
      sum_range_succ]
end P0_10_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2_5 Polynomial
open K1_14_3 (Slice)
open K1_14_2_2_3 (seedPresentation specializeJets mapGenericJets_eq)
local instance : Algebra (MvPolynomial (Fin 2) Seeds) FibreRing :=
  MvPolynomial.algebraMvPolynomial
end
end K1_14_2_2_2_5_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_2_5
open K1_14_3_2 (ProperPair)
theorem properPair_height {P Q : Jet} (h : ProperPair P Q)
    (I : Ideal Jet) [I.IsPrime] (hP : P ∈ I) (hQ : Q ∈ I) : 2 ≤ I.height := by
  have hne : I ≠ ⊥ := fun e => h.left_ne (by simpa [e] using hP)
  obtain ⟨D, hD, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hne
  let J : Ideal Jet := Ideal.span {D}
  have : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hJ₀ : J ≠ ⊥ := fun e => hp.ne_zero (Ideal.span_singleton_eq_bot.mp e)
  have hJ₁ : 1 ≤ J.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
  have hJI : J < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro e
    exact h.no_common D hp.irreducible
      (Ideal.mem_span_singleton.mp (e ▸ hP : P ∈ J))
      (Ideal.mem_span_singleton.mp (e ▸ hQ : Q ∈ J))
  calc
    2 = 1 + 1 := by decide
    _ ≤ J.height + 1 := add_le_add hJ₁ le_rfl
    _ ≤ I.height := Ideal.height_add_one_le_of_lt_of_isPrime hJI
end
end K1_14_2_2_2_5_1
end

end Merged_PortHighBase

end Merged_PortHighBase

-- merged module PortLowBase
section Merged_PortLowBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9
noncomputable section
open Polynomial
open P0 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox Fits Contact remaining
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
abbrev physicalDegree : ℕ := k - 1 + P0.lowCutoff.toNat
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
structure PoleData (Γ : Finset K) (s : K → (Polynomial K)) where
  H : (Polynomial Geom)
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ P0.lowCutoff.toNat
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ k - 1 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : (Polynomial Geom)
  q : (Polynomial Geom)
  a₀ : (Polynomial Geom)
  a₁ : (Polynomial Geom)
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f anchorCutoff
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
end
end P0_9
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open P0_9 (physicalDegree anchorCutoff)
open PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight physicalDegree) ≤ anchorCutoff
end
end P0_9_1
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators
open K1_13_1_1 (exponent_le_of_mem_translation_monomial)
private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 90)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 90 ≤ u none) :
    localConstraintAt 90 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 90 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 90 0 0 (truncateX Q) = localConstraintAt 90 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 90 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 90 <;> simp [hx]
    · by_cases hx : u none < 90 <;> simp [hx, coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]
end
end P0_9_1
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace P0_9_1
open K1_13 (Geom)
open PolynomialDifferential
open scoped BigOperators
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x
@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]
@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]
private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]
private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n
private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]
end P0_9_1
end
section
namespace P0_9_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P0 (I K node)
open MvPolynomial (mem_support_iff)
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133551) ≤ 3000 * 180217 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133551)
    ?_ (3000 * 180217 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133551) j).ne'
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
theorem weight_eq_sum (m : Fin 4 →₀ ℕ) (weight : Fin 4 → ℕ) :
    m.weight weight = m.sum (fun i a => weight i * a) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
theorem pointContact {m : ℕ} (x y : Geom) (Q : SourcePolynomial) (S : (Polynomial Geom))
    (hS : S.eval x = y) (hQ : SatisfiesLocalConstraints m x y Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ differentialSpecialization Q S := by
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q S x y hS hQ
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13_2 (SourceExponent topWeight)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open scoped BigOperators
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P0 (I K node)
open scoped BigOperators
theorem high_monomial_vanishes (e : SourceExponent) (c : Geom) (he : 3000 ≤ e none) :
    localConstraintAt 3000 0 0 (MvPolynomial.monomial e c) = 0 := by
  change MvPolynomial.weightedTruncation (localContactWeight 3) 3000
    (MvPolynomial.bind₁ (unscaledLocalImage 3 0 0) (MvPolynomial.monomial e c)) = 0
  apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
  refine MvPolynomial.bind₁_mem_restrictWeightedOrder
    (w := fun v : JetVariable 3 => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [unscaledLocalImage, map_zero, zero_add, Option.elim_none] using
        (MvPolynomial.X_mem_restrictWeightedOrder (R := Geom)
          (localContactWeight 3) (localT 3) (m := 1) (by rfl))
    | some j => simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))
theorem map_independent_family {V W : Type*} [AddCommGroup V] [Module Geom V]
    [AddCommGroup W] [Module Geom W] {n : ℕ} (f : V →ₗ[Geom] W)
    (hf : Function.Injective f) (P : W → Prop) (hP : ∀ x, P (f x))
    (hn : n ≤ Module.finrank Geom V) :
    ∃ e : Fin n → W, LinearIndependent Geom e ∧ ∀ i, P (e i) := by
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank hn
  exact ⟨f ∘ e, he.map' f (LinearMap.ker_eq_bot_of_injective hf), fun i => hP (e i)⟩
end
end P0_9_2
end
section
namespace P0_9_3
noncomputable section
open P0 (I K)
open P0_9 (TrueWeightLE primaryBox primaryCutoff )
open K1_13 (Row InBox shape Contact)
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node)
open P0_9 (TrueWeightLE physicalDegree primaryBox primaryCutoff  )
open K1_13 (Geom embed Row InBox shape indexDegree Contact jet atJet)
open K1_13_3 (Symbol symbolAt)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
def jetEval (S : (Polynomial Geom)) : Row 4 →ₗ[Geom] (Polynomial Geom) :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars Geom
theorem jetEval_apply (S : (Polynomial Geom)) (P : Row 4) : jetEval S P = atJet P S := by
  rfl
theorem dvd_smul_poly (d P : (Polynomial Geom)) (c : Geom) (h : d ∣ P) :
    d ∣ c • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact h.mul_left _
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
def coefficientArray (T : ℕ) :
    Row 4 →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      ((MvPolynomial.lcoeff (Polynomial Geom) (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : Row 4 →ₗ[(Polynomial Geom)] (Polynomial Geom)).restrictScalars Geom)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
def symbolLinear (x : Geom) : Row 4 →ₗ[Geom] Symbol :=
  ({ symbolAt x with
      commutes' := by
        intro a
        change MvPolynomial.map (evalRingHom x) (MvPolynomial.C (Polynomial.C a)) =
          MvPolynomial.C a
        simp } : Row 4 →ₐ[Geom] Symbol).toLinearMap
def linearFactor (x : Geom) : (Polynomial Geom) := (Polynomial.X : (Polynomial Geom)) - Polynomial.C x
theorem linearFactor_ne (x : Geom) : linearFactor x ≠ 0 := X_sub_C_ne_zero x
theorem linearFactor_degree (x : Geom) : (linearFactor x).natDegree = 1 :=
  natDegree_X_sub_C x
theorem divide_specialization (P : Row 4) (x : Geom) (hP : symbolAt x P = 0) :
    ∃ Q : Row 4, MvPolynomial.C (linearFactor x) * Q = P := by
  let Q : Row 4 := AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (divByMonicHom (linearFactor x)) (AddMonoidAlgebra.coeff P))
  refine ⟨Q, MvPolynomial.ext _ _ fun m => ?_⟩
  have hroot : (P.coeff m).eval x = 0 := by
    have h := congrArg (fun B : Symbol => B.coeff m) hP
    change (symbolAt x P).coeff m = (0 : Symbol).coeff m at h
    rw [symbolAt, MvPolynomial.coeff_map] at h
    exact h
  rw [MvPolynomial.coeff_C_mul]
  change (linearFactor x) * ((P.coeff m) /ₘ (linearFactor x)) = P.coeff m
  exact mul_divByMonic_eq_iff_isRoot.mpr hroot
theorem support_linear_mul (x : Geom) (P : Row 4) :
    (MvPolynomial.C (linearFactor x) * P).support = P.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff.trans (and_iff_right (linearFactor_ne x))
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node agreement)
open P0_9 ( SmallFactor  TrueWeightLE physicalDegree primaryBox
  primaryCutoff   )
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree remaining)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
theorem exists_fresh {n : ℕ} (f : Fin n → Row 4) :
    ∃ x : Geom, (∀ i : I, x ≠ embed (node i)) ∧
      ∀ i, (symbolAt x (f i)).support = (f i).support := by
  classical
  let nodes : Finset Geom := Finset.univ.image (fun i : I => embed (node i))
  let roots : Finset Geom := Finset.univ.biUnion (fun i : Fin n =>
    (f i).support.biUnion (fun m => ((f i).coeff m).roots.toFinset))
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (nodes ∪ roots)
  rw [Finset.mem_union, not_or] at hx
  refine ⟨x, ?_, fun i => Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
  · intro i h
    exact hx.1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at ⊢
    change (MvPolynomial.map (evalRingHom x) (f i)).coeff m ≠ 0
    rw [MvPolynomial.coeff_map]
    intro heval
    have hroot : x ∈ ((f i).coeff m).roots :=
      (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hm)).mpr heval
    exact hx.2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨m, hm, Multiset.mem_toFinset.mpr hroot⟩⟩)
theorem specialization_bounds (x : Geom) (P : Row 4)
    (hP : InBox (shape P) primaryBox) :
    (symbolAt x P).totalDegree ≤ 4012 ∧ symbolIndex (symbolAt x P) ≤ 1650 := by
  have h : (symbolAt x P).support ⊆ P.support := MvPolynomial.support_map_subset _ _
  exact ⟨(Finset.sup_mono h).trans hP.1, (Finset.sup_mono h).trans hP.2.1⟩
theorem sum_by_layer (W E : ℕ) (hE : 0 < E) (cost : ℕ → ℕ) :
    (∑ T ∈ Finset.range (W + 1), cost ((W - T) / E)) ≤
      E * ∑ k ∈ Finset.range (1 + W / E), cost k := by
  let S := Finset.range (W + 1)
  let R := Finset.range (1 + W / E)
  let U := Finset.range E
  let pair (T : ℕ) : ℕ × ℕ := ((W - T) / E, (W - T) % E)
  have hmem : ∀ T ∈ S, pair T ∈ R ×ˢ U := by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T) / E < 1 + W / E
        have h : (W - T) / E ≤ W / E := Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj : Set.InjOn pair (↑S : Set ℕ) := by
    intro T hT V hV h
    have hT' : T < W + 1 := Finset.mem_range.mp hT
    have hV' : V < W + 1 := Finset.mem_range.mp hV
    have he : W - T = W - V := by
      have ht := Nat.mod_add_div (W - T) E
      have hv := Nat.mod_add_div (W - V) E
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change (W - T) / E = (W - V) / E at hfst
      change (W - T) % E = (W - V) % E at hsnd
      rw [hsnd, hfst, hv] at ht
      exact ht.symm
    omega
  calc
    _ ≤ ∑ p ∈ R ×ˢ U, cost p.1 := by
      refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
      intro p hp
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      exact hmem T hT
    _ = _ := by rw [Finset.sum_product, Finset.mul_sum]; simp [U, R]
end
end P0_9_3
end
section
namespace P0_9_3_2
noncomputable section
open Polynomial
open P0_9 (SmallFactor  TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree shiftJet jet)
private abbrev Exponent := Fin 4 →₀ ℕ
def translateTop : Row 4 →+* Polynomial (Row 4) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = 3 then Polynomial.X else 0
def topHasse (a : ℕ) (P : Row 4) : Row 4 :=
  (translateTop P).coeff a
private theorem translate_independent (m : Exponent) (c : (Polynomial Geom)) (hm : m 3 = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ 3 := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]
private theorem translate_top_pow_coeff (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (3 : Fin 4) : Row 4) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : (Polynomial Geom)) * MvPolynomial.X 3 ^ (n - a) := by
  rw [add_comm, ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]
theorem erase_top_add (u : Exponent) :
    u.erase 3 + Finsupp.single 3 (u 3) = u := by
  ext i
  by_cases hi : i = 3
  · subst i
    simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]
private theorem topHasse_monomial (a : ℕ) (u : Exponent) (c : (Polynomial Geom)) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase 3 + Finsupp.single 3 (u 3 - a)) (↑((u 3).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase 3) c * MvPolynomial.X 3 ^ (u 3) := by
    rw [← MvPolynomial.monomial_add_single, erase_top_add]
  have hx : translateTop (MvPolynomial.X 3) =
      Polynomial.C (MvPolynomial.X 3) + Polynomial.X := by simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase 3) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]
theorem apply_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a : Exponent) 3 = m 3 + a := by simp
theorem topHasse_coeff (a : ℕ) (P : Row 4) (m : Exponent) :
    (topHasse a P).coeff m =
      ↑((m 3 + a).choose a) * P.coeff (m + Finsupp.single 3 a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u 3
    · have hcancel : (u.erase 3 + Finsupp.single 3 (u 3 - a)) + Finsupp.single 3 a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_top_add]
      have heq : u.erase 3 + Finsupp.single 3 (u 3 - a) = m ↔
          u = m + Finsupp.single 3 a := by
        constructor
        · intro h
          rw [← h, hcancel]
        · intro h
          exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single 3 a
      · have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        simp only [h3, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single 3 a := by
        intro h
        have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]
theorem source_support {a : ℕ} {P : Row 4} {m : Exponent}
    (hm : m ∈ (topHasse a P).support) : m + Finsupp.single 3 a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
theorem sum_add_top (w : Fin 4 → ℕ) (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w 3 * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]
theorem total_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_top (fun _ => 1) m a
private def shiftHom (S : (Polynomial Geom)) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
private theorem translate_shift (S : (Polynomial Geom)) :
    translateTop.comp (shiftHom S) = (Polynomial.mapRingHom (shiftHom S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateTop, shiftHom]
  · intro i
    simp only [RingHom.comp_apply, shiftHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = 3
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]
theorem topHasse_order (a d : ℕ) (P : Row 4) (S : (Polynomial Geom))
    (h : OrderAt P S d) : OrderAt (topHasse a P) S (d - a) := by
  have he := RingHom.congr_fun (translate_shift S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a =
      shiftHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  rw [total_add_top] at hd
  omega
theorem topHasse_zero (P : Row 4) : topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]
private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc
    _ = (V ^ a * W).coeff 0 := by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]
theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc
      _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))
end
end P0_9_3_2
end

end Merged_PortLowBase

end Merged6967_PortLowBase
