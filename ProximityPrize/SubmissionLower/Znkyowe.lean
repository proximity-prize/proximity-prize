import ProximityPrize.SubmissionLower.ZYOgAFe
set_option Elab.async false
section
namespace q2pGZyc
noncomputable section
open Polynomial



private theorem bOH {R:Type*} [CommRing R] (P:R[X][X]) (i j:ℕ) :
   ((Bivariate.swap P).coeff j).coeff i=(P.coeff i).coeff j:= by
 induction P using Polynomial.induction_on' with
 | add A B ha hb=>simp only [map_add,coeff_add,ha,hb]
 | monomial n A =>
   induction A using Polynomial.induction_on' with
   | add A B ha hb=>simp only [map_add,coeff_add,ha,hb]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:n=i <;> by_cases hj:m=j <;> simp [coeff_monomial,hi,hj]
end
end q2pGZyc
end
section
namespace qGnV2ac
noncomputable section
open Polynomial
open P5 (K p)
open P5_7_7 (Dg embed seedDerivative seedPullback)
open cu (L)
private theorem p_large :1<p:= by decide
private theorem p_pos :0<p:=Nat.zero_lt_of_lt p_large
private def aUs {R:Type*} [CommSemiring R] (n:ℕ) :
  R[X][X] →+* R[X][X] :=
 mapRingHom (expand R n).toRingHom
private theorem pullback_eq (F:Dg) (r :ℕ) :
 seedPullback F r=aUs (p^r) F:=rfl
private theorem expandSeed_coeff {R:Type*} [CommSemiring R] (n:ℕ) (F:R[X][X]) (i:ℕ) :
  (aUs n F).coeff i=expand R n (F.coeff i) :=
 coeff_map _ _
private theorem expandSeed_degree {R:Type*} [CommSemiring R] {n:ℕ}
  (hn:0<n) (F:R[X][X]) : (aUs n F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (expand_injective hn) F
theorem pullback_coeff (F:Dg) (r i j:ℕ) :
  ((seedPullback F r).coeff i).coeff (j*(p^r))=(F.coeff i).coeff j:= by
 rw [pullback_eq,expandSeed_coeff,coeff_expand_mul (pow_pos p_pos _)]
theorem powered_seeds {T:Finset K} {z :K→K} (r :ℕ)
   (hz :Set.InjOn z (T:Set K)) :Set.InjOn (fun γ=>z γ^(p^r)) (T:Set K) :=
 (iterateFrobenius_inj K p r).comp_injOn hz
theorem coeff_seedDerivative (F:Dg) (i:ℕ) :
   (seedDerivative F).coeff i=(F.coeff i).derivative := by
 classical
 rw [seedDerivative,Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
 · exact coeff_monomial_same _ _
 · exact fun j _ h=>coeff_monomial_of_ne _ h.symm
 · intro h
   rw [notMem_support_iff.mp h,derivative_zero,monomial_zero_right,coeff_zero]
private theorem expand_unit {R:Type*} [CommRing R] [IsDomain R]
  {q:R[X]} {n:ℕ} (hn:0<n) (hq:IsUnit (expand R n q)) :IsUnit q:= by
 obtain ⟨a,ha,he⟩:=Polynomial.isUnit_iff.mp hq
 exact Polynomial.isUnit_iff.mpr ⟨a,ha,expand_injective hn ((expand_C n a).trans he)⟩
private theorem expandSeed_unit {R:Type*} [CommRing R] [IsDomain R]
  {F:R[X][X]} {n:ℕ} (hn:0<n) (hF:IsUnit (aUs n F)) :IsUnit F:= by
 obtain ⟨a,ha,he⟩:=Polynomial.isUnit_iff.mp hF
 have hd:F.natDegree=0 :=
  (expandSeed_degree hn F).symm.trans (natDegree_eq_zero_of_isUnit hF)
 rw [eq_C_of_natDegree_eq_zero hd,isUnit_C]
 apply expand_unit hn
 rwa [← expandSeed_coeff,← he,coeff_C_zero]
private theorem expandSeed_irred {R:Type*} [CommRing R] [IsDomain R]
  {F:R[X][X]} {n:ℕ} (hn:0<n) (hF:Irreducible (aUs n F)) :
  Irreducible F:= by
 refine ⟨fun h=>hF.not_isUnit (h.map (aUs n)),fun a b hab => ?_⟩
 have hm:aUs n F=aUs n a*aUs n b:=hab ▸ map_mul _ _ _
 exact (hF.isUnit_or_isUnit hm).imp (expandSeed_unit hn) (expandSeed_unit hn)
private theorem embed_expandSeed (F:Dg) (n:ℕ) :
  embed (aUs n F)=aUs n (embed F) := by
 ext i
 simp only [expandSeed_coeff,embed,coe_mapRingHom,coeff_map,map_expand]
theorem pullback_atPair (F:Dg) (r :ℕ) (z :K) (P Q:L[X]) :
  atPair (seedPullback F r) z P Q=atPair F (z^(p^r)) P Q:= by
 unfold atPair
 rw [pullback_eq,embed_expandSeed]
 simp only [aUs,coe_mapRingHom,eval₂_map,map_pow]
 congr 1
 exact RingHom.ext fun f=>expand_eval _ f _
private theorem expandSeed_comp {R:Type*} [CommSemiring R] (F:R[X][X]) (a b:ℕ) :
  aUs a (aUs b F)=aUs (a*b) F:= by
 ext i
 rw [expandSeed_coeff,expandSeed_coeff,expandSeed_coeff,expand_expand]
private theorem step (F:Dg) (d:seedDerivative F=0) :
   ∃ G:Dg,aUs p G=F:= by
 classical
 let G:=F.sum fun i b=>monomial i (b.contract p)
 have hG (i:ℕ) :G.coeff i=(F.coeff i).contract p:= by
   change (F.sum fun j b=>monomial j (b.contract p)).coeff i= _
   rw [Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
   · exact coeff_monomial_same _ _
   · exact fun j _ h=>coeff_monomial_of_ne _ h.symm
   · intro h
     rw [notMem_support_iff.mp h,← C_0,contract_C,C_0,monomial_zero_right,coeff_zero]
 refine ⟨G,Polynomial.ext fun i => ?_⟩
 rw [expandSeed_coeff,hG]
 apply expand_contract _ ?_ p_pos.ne'
 rw [← coeff_seedDerivative,d,coeff_zero]
theorem raw_moving {F:Dg} (h:0<P5_7_7.gY (embed F)) :
  ∃ i,0<(F.coeff i).natDegree := by
 by_contra! he
 have hb:=(P5_7_7.bv9 (embed F) 0).mpr (fun i=> by
  exact (show ((embed F).coeff i).natDegree≤(F.coeff i).natDegree from by
    unfold embed
    rw [coe_mapRingHom,coeff_map,coe_mapRingHom]
    exact natDegree_map_le).trans (he i))
 omega
theorem compress (F:Dg) (h:ℕ) (hi:Irreducible F)
    (hei:Irreducible (embed F)) (hh : ∀ i,(F.coeff i).natDegree≤h)
    (hp : ∃ i,0<(F.coeff i).natDegree) :
    ∃ G:Dg,∃ r :ℕ,F=seedPullback G r ∧
      G.natDegree=F.natDegree∧Irreducible G∧Irreducible (embed G) ∧
      (∀ i,(G.coeff i).natDegree≤h)∧seedDerivative G≠0:= by
  induction h using Nat.strong_induction_on generalizing F with
  | h h ih =>
    by_cases hd:seedDerivative F=0
    · obtain ⟨G,he⟩:=step F hd
      have hc (i:ℕ) : (F.coeff i).natDegree=(G.coeff i).natDegree*p:= by
        rw [← he,expandSeed_coeff,natDegree_expand]
      have hg (i:ℕ) : (G.coeff i).natDegree≤h/p :=
        (Nat.le_div_iff_mul_le p_pos).mpr ((hc i).symm ▸ hh i)
      obtain ⟨i,hpos⟩:=hp
      have hgpos :0<(G.coeff i).natDegree := by
        rw [hc] at hpos
        exact Nat.pos_of_mul_pos_right hpos
      have hlt:h/p<h:=Nat.div_lt_self (hpos.trans_le (hh i)) p_large
      have hgi:Irreducible G:=expandSeed_irred p_pos (he.symm ▸ hi)
      have hge :Irreducible (embed G) :=expandSeed_irred p_pos
        ((embed_expandSeed G p) ▸ (he.symm ▸ hei))
      obtain ⟨E,r,her,hed,hei,heie,heh,hder⟩ :=
        ih (h/p) hlt G hgi hge hg ⟨i,hgpos⟩
      refine ⟨E,r+1,?_,?_,hei,heie,fun j=>(heh j).trans hlt.le,hder⟩
      · rw [← he,her,pullback_eq,pullback_eq,expandSeed_comp,pow_succ']
      · rw [← he,expandSeed_degree p_pos,hed]
    · refine ⟨F,0,?_,rfl,hi,hei,hh,hd⟩
      rw [pullback_eq,pow_zero]
      ext i
      rw [expandSeed_coeff,expand_one]
end
end qGnV2ac
end
