import ProximityPrize.SubmissionLower.ZRlaVZc
import ProximityPrize.SubmissionLower.ZDBuLfd
import ProximityPrize.SubmissionLower.ZdwiBha
import ProximityPrize.SubmissionLower.ZvOdgMc
import ProximityPrize.SubmissionLower.ZW31ykd
set_option Elab.async false
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
open private line bdm bfX from ProximityPrize.SubmissionLower.CS
open private cX8 from ProximityPrize.SubmissionLower.A2
open private coeffForm specialize Yw shift_jetDerivative coeff_iterate_zero atJet_eq_const from ProximityPrize.SubmissionLower.ZDBuLfd
def lastCut:ℕ:=bo8.m*A - 1
def step:ℕ:=gap A+2
private def Bounded (F:zM1 ao[X]) (b:ℕ) :Prop :=
  ∀ j,(F.coeff j).natDegree≤b+step*j
private theorem afg {F G:zM1 ao[X]} {a b:ℕ}
    (hF:Bounded F a) (hG:Bounded G b) :Bounded (F*G) (a+b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum,Nat.mul_add]
  omega
private theorem aCs (f :ao[X]) {a :ℕ} (hf :f.natDegree≤a) :
    Bounded (z1z f) a := by
  intro j
  by_cases h:j=0
  · simpa [h] using hf
  · simp [zFI,h]
private theorem bmr {ι:Type*} (s :Finset ι)
    (f :ι→zM1 ao[X]) (b:ι→ℕ) (hf : ∀ i∈s,Bounded (f i) (b i)) :
    Bounded (∏ i∈s,f i) (∑ i∈s,b i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact afg (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk=>hf k (Finset.mem_insert_of_mem hk))
private theorem aMs {f :zM1 ao[X]} {b:ℕ} (hf :Bounded f b) (n:ℕ) :
    Bounded (f^n) (b*n) := by
  induction n with
  | zero=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private abbrev weight (i:Fin 3) :ℕ:=N - i.val
private theorem avr (P:af 3) (S U:ao[X]) (T:ℕ)
    (hP : ∀ e∈P.support,(P.coeff e).natDegree+e.sum (fun i k=>weight i*k)≤T)
    (hS:S.natDegree≤N) (hU:U.natDegree≤A+2) (j:ℕ) :
    ((line P S U).coeff j).natDegree≤T+step*j:= by
  let F (i:Fin 3) :zM1 ao[X] :=
    z1z (jet S i)+Polynomial.C (jet U i)*Polynomial.X
  have hF (i:Fin 3) :Bounded (F i) (weight i) := by
    intro k
    have hs : (jet S i).natDegree≤weight i :=
      (natDegree_hasseDeriv_le S i.val).trans (zIu hS _)
    have hu: (jet U i).natDegree≤weight i+step:= by
      refine (natDegree_hasseDeriv_le U i.val).trans ((zIu hU _).trans ?_)
      have hi:=i.isLt
      change 179829 - i.val≤(131071 - i.val)+48758
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
    (hR:R∈rows w T) (hcut:T+r*step≤lastCut) {f :K[X]}
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
open private mem_rows derivative_band initial_mul from ProximityPrize.SubmissionLower.ZvFuy6d
open private cofactor_eq group_cutoffs from ProximityPrize.SubmissionLower.ZkuTDfa
open private matrix_dimension from ProximityPrize.SubmissionLower.ZZ4xzRc
open private S6 telescope caps_pow from ProximityPrize.SubmissionLower.ZvOdgMc
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
    {f :K[X]} (hf :f∈close A w) :differentialSpecialization P f=0:= by
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
