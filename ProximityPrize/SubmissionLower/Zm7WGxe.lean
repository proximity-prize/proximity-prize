import ProximityPrize.SubmissionLower.ZHSmgre
import ProximityPrize.SubmissionLower.Zy3W3oe
set_option Elab.async false
open _root_ renaming qWdRihc.Bounded→aU,qWdRihc.discriminant→c9,qWdRihc.specialize→cy,zero_add→lz
set_option autoImplicit true
namespace qWdRihc
noncomputable section
open Polynomial
open P5 (K p)
open cu (L j9)
open P5_7_2 (fO jX row)
def c1 :Prop :=
  ∀ (H :ℕ) (Δ:nC),Δ≠0→aU Δ (2*H)→Δ.natDegree<p →
    ∃ (s :i5) (q R:nC),
      s≠0∧s.natDegree≤2*H∧aU q H∧aU R (2*H) ∧
      (∀ z :L,cy z q≠0) ∧
      Δ=C s*q^2*R ∧
      (R=1∨(0<R.natDegree∧R.natDegree<p ∧
        IsCoprime (ek R) (ek R).derivative))
def c2 :Prop :=
  ∀ (H :ℕ) (T:Finset K) (z :K→L),Set.InjOn z (T:Set K) →
    ∀ (s :i5) (q R:nC),aU R (2*H) →
      0<R.natDegree→R.natDegree<p →
      IsCoprime (ek R) (ek R).derivative →
      (∀ γ∈T,s.eval (z γ)≠0∧cy (z γ) q≠0 ∧
        ∃ w:L[X],w^2=C (s.eval (z γ))*(cy (z γ) q)^2*cy (z γ) R) →
      T.card≤10*H
def c3:Prop :=
  ∀ (J:UJ) (H :ℕ) (a b q:nC) (s :i5),
    a≠0→aU a H→aU b H→aU q H →
    s≠0→s.natDegree≤2*H →
    (∀ γ∈J.CF,
      (cy (J.z γ) a*j9 (J.scalar γ) - cy (J.z γ) b)^2 =
        C (s.eval (J.z γ))*(cy (J.z γ) q)^2) →
    ∃ U V:Finset K,J.CF=U∪V∧asT J U (4*H)∧asT J V (4*H)
private theorem bBM {P Q:nC} {i j:ℕ} (hP:aU P i) (hQ:aU Q j) :
  aU (P*Q) (i+j) := by
 intro k
 rw [coeff_mul]
 apply natDegree_sum_le_of_forall_le
 intro a _
 exact natDegree_mul_le_of_le (hP a.1) (hQ a.2)
private theorem bound_neg {P:nC} {H :ℕ} (hP:aU P H) :aU (-P) H := by
 intro i
 simpa only [coeff_neg,natDegree_neg] using hP i
private theorem bound_const (c:L) :aU (C (C c) :nC) 0:= by
 intro i
 by_cases hi:i=0 <;> simp [coeff_C,hi]
private theorem disc_bound {a b c:nC} {H :ℕ}
  (ha :aU a H) (hb:aU b H) (hc:aU c H) :
  aU (c9 a b c) (2*H) := by
 have hm:=bBM (bBM (bound_const (4 :L)) ha) hc
 change aU ((4 :nC)*a*c) (0+H+H) at hm
 intro i
 rw [c9,coeff_sub,pow_two]
 apply (natDegree_sub_le _ _).trans
 have h:=bBM hb hb i
 have h' := hm i
 exact max_le (h.trans_eq (by omega)) (h'.trans_eq (by omega))
private theorem disc_degree {a b c:nC} {m:ℕ}
  (ha :a.natDegree< m) (hb:b.natDegree< m) (hc:c.natDegree< m)
  (hm:2*m≤p) : (c9 a b c).natDegree<p:= by
 apply (natDegree_sub_le _ _).trans_lt
 have h₁: (b^2).natDegree≤2*b.natDegree :=natDegree_pow_le
 have hconst: (4 :nC).natDegree=0:= by change (C (C (4 :L))).natDegree=0; simp
 have h₂: ((4 :nC)*a*c).natDegree≤a.natDegree+c.natDegree := by
  apply natDegree_mul_le_of_le _ le_rfl
  exact natDegree_mul_le.trans (by rw [hconst,lz])
 exact max_lt (h₁.trans_lt (by omega)) (h₂.trans_lt (by omega))
private theorem zeros_le (T:Finset K) (z :K→L) (hi:Set.InjOn z (T:Set K))
  {s :i5} (hs :s≠0) (hz : ∀ γ∈T,s.eval (z γ)=0) :T.card≤ s.natDegree := by
 classical
 calc
  _=(T.image z).card:=(Finset.card_image_of_injOn hi).symm
  _≤_:=Polynomial.card_le_degree_of_subset_roots (by
    intro x hx
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    exact (Polynomial.mem_roots hs).mpr (hz γ hγ))
private theorem small_square (J:UJ) {a b c:nC} {γ:K} (hr :Zk J a b c γ) :
  (cy (J.z γ) (2*a)*j9 (J.scalar γ) - cy (J.z γ) (-b))^2 =
    cy (J.z γ) (c9 a b c) := by
 dsimp only [Zk] at hr
 simp only [c9,map_mul,map_pow,map_ofNat,map_neg,map_sub]
 linear_combination 4*cy (J.z γ) a*hr
private theorem cover_count (cover :c3) (J:UJ) {H :ℕ} {a b q:nC} {s :i5}
    (ha :a≠0) (hA:aU a H) (hB:aU b H) (hQ:aU q H)
    (hs :s≠0) (hsd:s.natDegree≤2*H)
    (hr : ∀ γ∈J.CF,
      (cy (J.z γ) a*j9 (J.scalar γ) - cy (J.z γ) b)^2 =
        C (s.eval (J.z γ))*(cy (J.z γ) q)^2) :
    J.CF.card≤48*H+2 := by
  classical
  obtain ⟨U,V,he,hU,hV⟩:=cover J H a b q s ha hA hB hQ hs hsd hr
  have hu:U⊆J.CF:= by rw [he]; exact Finset.subset_union_left
  have hv :V⊆J.CF:= by rw [he]; exact Finset.subset_union_right
  have hx :=exceptional_count J U hu _ hU
  have hy :=exceptional_count J V hv _ hV
  have hz :=Finset.card_union_le U V
  rw [he]
  omega
private theorem zero_rhs_count (cover :c3) (J:UJ) {H :ℕ} {a b:nC}
  (ha :a≠0) (hA:aU a H) (hB:aU b H)
  (hr : ∀ γ∈J.CF,
    (cy (J.z γ) a*j9 (J.scalar γ) - cy (J.z γ) b)^2=0) :
  J.CF.card≤48*H+2 := by
 refine cover_count cover J (q:=0) (s :=1) ha hA hB (by intro i; simp) one_ne_zero
  (by simp) ?_
 intro γ hγ
 simpa using hr γ hγ
private theorem root_count (decmp:c1) (ramified:c2) (cover :c3)
    (J:UJ) {H :ℕ} {a b c:nC}
    (hn:a≠0∨b≠0∨c≠0)
    (ha :aU a H) (hb:aU b H) (hc:aU c H)
    (hd: (c9 a b c).natDegree<p)
    (hr : ∀ γ∈J.CF,Zk J a b c γ) :J.CF.card≤64*H+4 := by
  classical
  by_cases ha0:a=0
  · by_cases hb0:b=0
    · have hc0:=(hn.resolve_left (fun h=>h ha0)).resolve_left (fun h=>h hb0)
      have hz : ∀ γ∈J.CF,c.leadingCoeff.eval (J.z γ)=0:= by
        intro γ hγ
        have hh:=hr γ hγ
        simp only [Zk,ha0,hb0,map_zero,zero_mul,lz] at hh
        have he :=congrArg (fun P:L[X]=>P.coeff c.natDegree) hh
        simpa only [cy ,coe_mapRingHom,coeff_map,coeff_natDegree,
          coe_evalRingHom,coeff_zero] using he
      have hf :=(zeros_le J.CF J.z J.seed_injective (leadingCoeff_ne_zero.mpr hc0) hz).trans
        (by simpa only [coeff_natDegree] using hc c.natDegree)
      omega
    · have hf :=zero_rhs_count cover J hb0 hb (bound_neg hc) (by
        intro γ hγ
        have hh:=hr γ hγ
        simp only [Zk,ha0,map_zero,zero_mul,lz] at hh
        rw [map_neg,sub_neg_eq_add,hh,zero_pow (by decide :2≠0)])
      omega
  let Δ:=c9 a b c
  have h2 : (2 :nC)≠0:= by
    let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
    have hp: (2 :L)≠0:= by
      rw [← Nat.cast_two,Ne,CharP.cast_eq_zero_iff L p]
      decide
    change C (C (2 :L))≠0
    exact C_ne_zero.mpr (C_ne_zero.mpr hp)
  have hd0:2*a≠0:=mul_ne_zero h2 ha0
  have hda :aU (2*a) H := by
    simpa only [lz ,Polynomial.C_ofNat] using bBM (bound_const (2 :L)) ha
  have hnb:=bound_neg hb
  by_cases hz :Δ=0
  · have hcount:=zero_rhs_count cover J hd0 hda hnb (by
      intro γ hγ
      simpa only [← show Δ=c9 a b c from rfl,hz,map_zero]
        using small_square J (hr γ hγ))
    omega
  obtain ⟨s,q,R,hs,hsd,hq,hR,hunit,hfact,hRcase⟩:=decmp H Δ hz (disc_bound ha hb hc) hd
  let U:=J.CF.filter fun γ=>s.eval (J.z γ)≠0
  have hU:U⊆J.CF:=Finset.filter_subset _ _
  let V:=J.CF \ U
  have hV:V⊆J.CF:=Finset.sdiff_subset
  have hnz (γ:K) (hγ:γ∈U) :s.eval (J.z γ)≠0:=(Finset.mem_filter.mp hγ).2
  have hpaid :V.card≤2*H :=
    (zeros_le V J.z (J.seed_injective.mono hV) hs (by
      intro γ hγ
      obtain ⟨hγJ,hγU⟩:=Finset.mem_sdiff.mp hγ
      by_contra hh
      exact hγU (Finset.mem_filter.mpr ⟨hγJ,hh⟩))).trans hsd
  have hmark (γ:K) (hγ:γ∈U) :
      (cy (J.z γ) (2*a)*j9 (J.scalar γ) - cy (J.z γ) (-b))^2 =
        C (s.eval (J.z γ))*(cy (J.z γ) q)^2*cy (J.z γ) R:= by
    refine (small_square J (hr γ (hU hγ))).trans ?_
    change cy (J.z γ) Δ= _
    simp only [hfact,map_mul,map_pow,cy ,coe_mapRingHom,Polynomial.map_C,
      coe_evalRingHom]
  have hpart:=Finset.card_sdiff_add_card_eq_card hU
  change V.card+U.card=J.CF.card at hpart
  rcases hRcase with rfl | ⟨hdeg,hchar,hsep⟩
  · let J' := J.restrict U hU
    have hh:U.card≤48*H+2 :=
      cover_count cover J' hd0 hda hnb hq hs hsd (by
        intro γ hγ
        simpa only [J',UJ.restrict,map_one,mul_one] using hmark γ hγ)
    omega
  · have hh:=ramified H U J.z (J.seed_injective.mono hU) s q R hR hdeg hchar hsep (by
      intro γ hγ
      exact ⟨hnz γ hγ,hunit _,_,hmark γ hγ⟩)
    omega
private theorem near_guards (b:fO) :
  131071+(jX b).hi≤d∧0x21ba040087f84≤(row b).Z1 := by
 fin_cases b <;> decide
end
end qWdRihc
