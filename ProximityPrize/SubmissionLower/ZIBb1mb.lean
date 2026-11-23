import ProximityPrize.SubmissionLower.CE
import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.ZV6zyia
set_option Elab.async false
set_option autoImplicit true
namespace P6_6_7_3
noncomputable section
open P6_6 P6_6_7
open aR (af Shape shape aO cK extend)
open dN (GeoJets bC kC oA)
open BO (bfW)
open agL (BV EY bft afc aD7)
open lB (amo)
open MvPolynomial (weightedTotalDegree_prod weightedTotalDegree_one weightedTotalDegree_piSingle)
open private aDq from ProximityPrize.SubmissionLower.BF
open scoped BigOperators
theorem cDD {x y z :Shape} (h:aO x y) (k :aO y z) :aO x z :=
  ⟨h.1.trans k.1,h.2.1.trans k.2.1,h.2.2.trans k.2.2⟩
private theorem literal_fits {R:af 4} {p:Shape} (h:aO (shape R) p) :
    aO (shape R) (literalBody p).iU:= by
  obtain ⟨htj,hjb⟩:=aDq R
  have htb: (shape R).t≤(shape R).b:=MvPolynomial.degreeOf_le_totalDegree _ _
  have hj: (shape R).j≤ min p.j (3*p.b) :=
    le_min h.2.1 (hjb.trans (Nat.mul_le_mul_left 3 h.1))
  have ht: (shape R).t≤ min p.j (3*p.b)/3 :=
    (Nat.le_div_iff_mul_le (by decide :0<3)).mpr
      (by simpa only [Nat.mul_comm] using htj.trans hj)
  exact ⟨h.1.trans (le_max_left _ _),hj,le_min h.2.2 (le_min (htb.trans h.1) ht)⟩
theorem charter {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    chartIndices C cs⊆C.S:= by
  cases cs with
  | union _=>exact Finset.Subset.rfl
  | own i =>
    intro k hk
    have hi:i∈C.S:=h.guard.1
    exact (Finset.mem_singleton.mp hk).symm ▸ hi
private theorem prod_shape {n:ℕ} (f :Fin n→af 4) (S:Finset (Fin n))
    (hn : ∀ k∈S,f k≠0) :shape (factorProd f S)=wD (shape ∘ f) S:= by
  have hb:=weightedTotalDegree_prod (1 :Fin 4→ℕ) S f hn
  have hj:=weightedTotalDegree_prod (Fin.val :Fin 4→ℕ) S f hn
  have ht:=weightedTotalDegree_prod (Pi.single (3:Fin 4) 1) S f hn
  simp only [weightedTotalDegree_one] at hb
  simp only [← Ex.C6] at hj
  simp only [weightedTotalDegree_piSingle] at ht
  simp only [factorProd,Ds.wD,shape,Function.comp_apply]
  rw [hb,hj,ht]
theorem bW2 {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    aO (shape (GW C cs)) (chartBody C R cs) ∧
      ∀ k∈chartIndices C cs,aO (shape (C.f k)) (chartBody C R cs) := by
  have hn (k) (hk :k∈chartIndices C cs) :=(C.marks.factors k (charter h hk)).1.ne_zero
  have hp:aO (shape (GW C cs)) (chartBody C R cs) := by
    cases cs with
    | union l =>
      change aO (shape (factorProd C.f C.S)) (remainingChart C.v)
      apply literal_fits
      rw [prod_shape C.f C.S hn]
      obtain ⟨hb,hj,ht⟩:=C.fits
      exact ⟨by have :=hb; simp only [Shape.plus] at this; exact Nat.le_sub_of_add_le' this,
        by have :=hj; simp only [Shape.plus] at this; exact Nat.le_sub_of_add_le' this,
        by have :=ht; simp only [Shape.plus] at this; exact Nat.le_sub_of_add_le' this⟩
    | own k =>
      change aO (shape (∏ i∈({k} : Finset _),C.f i)) (shape R).iU
      rw [Finset.prod_singleton]
      exact cDD (anm.bNR h.factor.1.ne_zero h.guard.2.1.dvd')
        (akM.a1n R)
  refine ⟨hp,fun k hk=>cDD (anm.bNR ?_ (Finset.dvd_prod_of_mem C.f hk)) hp⟩
  exact Finset.prod_ne_zero_iff.mpr hn
theorem order_mem (R:af 4) (z :Ideal GeoJets) {a :Fin 4 →₀ ℕ}
    (ha :EY a<genericOrder R z) :bC (BV a R)∈z := by
  classical
  exact Nat.findGreatest_spec
    (P:= fun d => ∀ a,EY a<d→bC (BV a R)∈z)
    (Nat.zero_le _) (fun _ hx=>(Nat.not_lt_zero _ hx).elim) a ha
theorem chart_product_vanishes {C:Context} {R G ell cs} (h:PairInput C R G ell cs)
    {γ:P6.K} (hγ:γ∈C.Δ) (ho:0<ord C R γ) :
    cK (GW C cs) (extend (C.s γ))=0:= by
  have hex : ∃ k∈chartIndices C cs,cK (C.f k) (extend (C.s γ))=0:= by
    cases cs with
    | union _=>exact C.marks.Eh γ hγ
    | own k =>
      have hor :aR.wU R (extend (C.s γ)) (ord C R γ) := by
        classical
        exact Nat.findGreatest_spec (Nat.zero_le _) (fun _ _=>Nat.zero_le _)
      refine ⟨k,Finset.mem_singleton_self _,?_⟩
      have hd:=map_dvd (MvPolynomial.eval (aR.jet (extend (C.s γ)))) h.guard.2.1.dvd
      change cK R (extend (C.s γ))∣cK (C.f k) (extend (C.s γ)) at hd
      rw [bfW ho hor] at hd
      exact zero_dvd_iff.mp hd
  obtain ⟨k,hk,hv⟩:=hex
  have hd:=map_dvd (MvPolynomial.eval (aR.jet (extend (C.s γ))))
    (Finset.dvd_prod_of_mem C.f hk)
  change cK (C.f k) (extend (C.s γ))∣cK (GW C cs) (extend (C.s γ)) at hd
  rw [hv] at hd
  exact zero_dvd_iff.mp hd
theorem agr {R:af 4} (hR:R≠0) :bC R≠0:= by
  intro hz
  apply hR
  exact lB.aFf (hz.trans (map_zero _).symm)
theorem first_fits {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    aO (shape R) (firstBody C R cs) := by
  cases cs with
  | union l=>exact literal_fits h.guard.2.2
  | own i=>exact akM.a1n R
theorem top_fits {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    (shape R).t≤topBound C R cs := by
  cases cs with
  | union l=>exact h.guard.2.2.2.2
  | own i=>exact le_rfl
theorem char_fits {C:Context} {R G ell cs} (h:PairInput C R G ell cs) :
    (shape R).b≤4025∧(shape G).b≤4025:= by
  constructor
  · cases cs with
    | union l=>exact h.guard.2.2.1.trans (Nat.sub_le ..)
    | own i =>
      exact (anm.bNR (C.marks.factors i h.guard.1).1.ne_zero
        h.guard.2.1.dvd).1.trans
        ((C.marks.factors i h.guard.1).2.2.1.1.trans (by decide))
  · exact h.H6.1.trans (max_le (Nat.sub_le ..) ((min_le_left _ _).trans
      ((Nat.sub_le ..).trans (by decide :1710≤4025))))
theorem local_weight {R G:af 4} (hR:Irreducible R) (hG : ¬ R∣G)
    {z :Ideal GeoJets} (hz : (kC R G).IsMinimalPrime z)
    {ell:ℕ} (he :ell≤genericOrder G z) :
    ∃ v :ℕ,v≤(shape R).b*(shape G).b ∧
      oA (kC R G) z hz.isPrime=(v :ℕ∞) ∧
      ell*genericOrder R z≤v := by
  let:=hz.isPrime
  have hR0:=agr hR.ne_zero
  have hrel :=amo R G hR hG
  have hheight:=aD7 hR0 hrel hz
  have hdeg (P:af 4) : (bC P).totalDegree≤(shape P).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hb:oA (kC R G) z hz.isPrime ≤
      (↑((shape R).b*(shape G).b) :ℕ∞) :=
    (bRm.proof _ _ _ hz hR0 hrel).trans
      (by exact_mod_cast Nat.mul_le_mul (hdeg R) (hdeg G))
  have hlen:oA (kC R G) z hz.isPrime =
      (↑(oA (kC R G) z hz.isPrime).toNat :ℕ∞) :=
    (ENat.natCast_toNat (ne_of_lt (hb.trans_lt (ENat.natCast_lt_top _)))).symm
  have vanish (P:af 4) {k :ℕ} (hk :k≤genericOrder P z) :
      afc z (bC P) k := by
    apply bRn.proof _ z k hheight
    intro a ha
    change BV a (MvPolynomial.map dN.j8 P)∈z
    rw [← bft]
    exact order_mem P z (ha.trans_le hk)
  have hv :=OO.bsc hheight (vanish R le_rfl) (vanish G he)
  rw [hlen] at hb hv
  exact ⟨_,by exact_mod_cast hb,hlen,by
    rw [Nat.mul_comm]
    exact_mod_cast hv⟩
end
end P6_6_7_3
