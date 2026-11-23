import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZwiFoca
import ProximityPrize.SubmissionLower.ZNc08Oa
import ProximityPrize.SubmissionLower.ZIBb1mb
set_option Elab.async false
set_option autoImplicit true
namespace qAIBbfd
noncomputable section
open Polynomial Finset P6_6 P6_6_7
open P6_6_7_3 (cDD charter GW bW2)
open aR (af Shape aO shape extend Dd)
open dN (GeoJets bC Ch An separant)
open BO (Ue)
open vS (VE JV bTT)
open aY3 (a6c)
open Dr (ChamberBox aGY bHn dimension tW cb6)
open wH (qg)
open lB (Tn)
open private b0H from ProximityPrize.SubmissionLower.BE
open private cc1 from ProximityPrize.SubmissionLower.E4
private theorem bnH :Dr.c2 :=
  Kd.of_children
    aKr.proof bzz.proof aKs.proof
    bzA.proof ap8.proof bjA.proof
private theorem bnG:Dr.c3 :=
  bzB.of_children bar.proof
    (aRS.of_children cyo.proof cyp.proof)
private theorem section_card {T:Ideal GeoJets} (hT:T.IsPrime) (hd:dimension T=1)
    {p:Shape} (hp:ChamberBox p) {w M s} (hm:Messages w M s)
    {D:GeoJets} (hD:VE p D) (hne :D∉T)
    (hz : ∀ γ∈M,T≤Ch (extend (s γ))∧An (extend (s γ)) D =0) :
    (M.card:ℚ)≤tW T [p] := by
  classical
  let pt (γ:P6.K) :=JV (extend (s γ))
  have hinj:Set.InjOn pt (M:Set P6.K) := fun _ ha _ hb he =>
    hm.distinct ha hb (Polynomial.map_injective aR.embed aR.embed.injective
      (bTT he))
  rw [← card_image_of_injOn hinj]
  exact cc1 bnH bnG hT hd hp hD hne (M.image pt) (by
    intro x hx
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
    exact hz γ hγ)
private theorem degree_nonneg {T:Ideal GeoJets} (hd:dimension T=1)
    {p:Shape} (hp:ChamberBox p) :0≤tW T [p] := by
  simpa only [sum_empty] using bnG T [p]
    (fun q hq=>(List.mem_singleton.mp hq).symm ▸ hp) (by simp [hd]) ∅ (by simp)
private theorem chartChamber {p:Shape} {L:ℕ} (hL:4≤L) :
    ChamberBox (weightedChart L p) := by
  unfold weightedChart
  split_ifs
  · let j:=3+(L-4)*(p.j - 2)
    change j≤ max _ j∧3*min (L-3) (j/3)≤j∧0< min (L-3) (j/3)
    refine ⟨le_max_right _ _,?_,?_⟩
    · have :=min_le_right (L-3) (j/3)
      omega
    · exact lt_min (by omega) (Nat.div_pos (Nat.le_add_right ..) (by decide))
  · exact aGY L p (by omega)
private theorem charge {n a b c t e :ℕ} {d p:ℚ}
    (hn:a+b=n) (ha :e*a≤t*c+e) (hc: (c:ℚ)≤d)
    (hb: (b:ℚ)≤p) (hp:1≤p) :
    (e :ℚ)*n≤(t:ℚ)*d+2*(e :ℚ)*p:= by
  have ha' : (e :ℚ)*a≤(t:ℚ)*c+e := by exact_mod_cast ha
  rw [← hn,Nat.cast_add,mul_add]
  linarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg t: (0:ℚ)≤t),
    mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg e : (0:ℚ)≤e),
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg e : (0:ℚ)≤e)]
private theorem ceY {T:Ideal GeoJets} (hT:T.IsPrime) (hd:dimension T=1)
    {p:Shape} (hp:ChamberBox p) {w M s} (hm:Messages w M s)
    (hM:M.Nonempty) (hon : ∀ γ∈M,T≤Ch (extend (s γ)))
    {g:af 4} (hg:aO (shape g) p) (hgT:bC g∈T)
    (hs :aO (shape (separant g)) p) (hsT:bC (separant g)∉T) :
    (mV:ℚ)*M.card≤(P6.t:ℚ)*tW T [weightedChart bf p] +
      2*(mV:ℚ)*tW T [p] := by
  classical
  let q:=weightedChart bf p
  have hL:4≤bf := by decide
  have hLp:bf≤K1.p:= by decide
  have hq:ChamberBox q:=chartChamber hL
  have hqn:=degree_nonneg hd hq
  let d := ⌊tW T [q]⌋₊
  let reg (γ:P6.K) :=qg g (extend (s γ))
  let A:=M.filter reg
  let B:=M.filter (fun γ => ¬ reg γ)
  have hsep:separant g≠0:= fun hz=>hsT (by simp [hz,bC])
  have hA:=P6_6_5.bv5 (hm.mono (filter_subset reg M)) d (by
    intro i hmiss
    obtain ⟨D,hD,hev⟩:=value_cut hL hLp hg ⟨hp.1,hp.2.1⟩ hp.2.2 hsep (P6.node i) (w i)
    have he (γ) (hγ:γ∈A) :
        An (extend (s γ)) D =0↔(s γ).eval (P6.node i)=w i:= by
      obtain ⟨hmγ,hr⟩:=mem_filter.mp hγ
      exact hev _ (Nat.lt_succ_of_le (hm.degree γ hmγ)) (Ue.mp (hon γ hmγ hgT)) hr
    have hproper :D∉T:= by
      obtain ⟨γ,hγ,hne⟩:=hmiss
      exact fun h=>hne ((he γ hγ).mp (hon γ (filter_subset reg M hγ) h))
    let U:=A.filter fun γ=>(s γ).eval (P6.node i)=w i
    have hUA:U⊆A:=filter_subset _ _
    have hUM:=hUA.trans (filter_subset reg M)
    exact Nat.le_floor (section_card hT hd hq (hm.mono hUM) (a6c hD) hproper
      (fun γ hγ=>⟨hon γ (hUM hγ),(he γ (hUA hγ)).mpr (mem_filter.mp hγ).2⟩)))
  have hB:=section_card hT hd hp (hm.mono (filter_subset _ M)) (bHn hs) hsT (by
    intro γ (hγ:γ∈B)
    obtain ⟨hγ,hn⟩:=mem_filter.mp hγ
    exact ⟨hon γ hγ,Ue.mpr (not_ne_iff.mp hn)⟩)
  obtain ⟨γ,hγ⟩:=hM
  obtain ⟨D,hD,hproper,hz⟩:=cb6 hd hp
    (JV (extend (s γ))) (hon γ hγ)
  have hone : (1 :ℚ)≤tW T [p] := by
    simpa only [card_singleton,Nat.cast_one] using
      section_card hT hd hp (hm.mono (singleton_subset_iff.mpr hγ)) hD hproper (by
        intro x hx
        rw [mem_singleton.mp hx]
        exact ⟨hon γ hγ,hz⟩)
  exact charge (card_filter_add_card_filter_not reg) hA (Nat.floor_le hqn) hB hone
private theorem A9 {C:Context} {R G ell cs} (hp:PairInput C R G ell cs) :
    ChamberBox (chartBody C R cs) := by
  have hi: (chartIndices C cs).Nonempty := by
    cases cs with
    | union _ =>
      obtain ⟨γ,hγ⟩:=C.nonempty
      obtain ⟨i,hi,_⟩:=C.marks.Eh γ hγ
      exact ⟨i,hi⟩
    | own i=>exact ⟨i,mem_singleton_self _⟩
  obtain ⟨i,hi⟩:=hi
  have ht:=(C.marks.factors i (charter hp hi)).2.1.trans_le ((bW2 hp).2 i hi).2.2
  refine ⟨?_,?_,ht⟩
  · cases cs <;> exact le_max_right _ _
  · cases cs with
    | own _=>exact (Tn R).2
    | union _ =>
      let j:=min (rawResidual m6 C.v).j (3*(rawResidual m6 C.v).b)
      change 3*min _ (min _ (j/3))≤j
      exact (Nat.mul_le_mul_left 3 ((min_le_right _ _).trans (min_le_right _ _))).trans
        (Nat.mul_div_le j 3)
theorem aTZ {C:Context} {R G ell cs} (hp:PairInput C R G ell cs)
    {T:Ideal GeoJets} {M:Finset P6.K} (hT:T.IsPrime)
    (hd:ringKrullDim (GeoJets ⧸ T)=1) (hM:M⊆C.Δ)
    (hon : ∀ γ∈M,T≤Ch (extend (C.s γ)))
    (hR : ∀ γ∈M,bC R∈Ch (extend (C.s γ))) :
    let p:=chartBody C R cs
    (mV:ℚ)*M.card≤(P6.t:ℚ)*tW T [weightedChart bf p] +
      2*(mV:ℚ)*tW T [p] := by
  classical
  let p:=chartBody C R cs
  change (mV:ℚ)*M.card≤(P6.t:ℚ)*tW T [weightedChart bf p] +
    2*(mV:ℚ)*tW T [p]
  let:=hT
  have hd' : dimension T=1 := by
    have he :=(b0H T).symm.trans hd
    exact_mod_cast he
  have hp' := A9 hp
  have hq:ChamberBox (weightedChart bf p) :=chartChamber (by decide)
  have hpn:=degree_nonneg hd' hp'
  have hfirst:=mul_nonneg (Nat.cast_nonneg P6.t) (degree_nonneg hd' hq)
  have hsecond:=mul_nonneg (mul_nonneg (by decide : (0:ℚ)≤2) (Nat.cast_nonneg mV)) hpn
  by_cases hne :M.Nonempty
  · have hm:=C.messages.mono hM
    by_cases hf : ∃ i∈chartIndices C cs,bC (C.f i)∈T
    · obtain ⟨i,hi,hfi⟩:=hf
      have hi' := charter hp hi
      obtain ⟨γ,hγ⟩:=hne
      have hsmall:=C.marks.factors i hi'
      have htop:=hsmall.2.2.1.2.2.trans_lt (by decide :16<K1.p)
      have hmark :Dd (C.f i) (extend (C.s γ)) :=
        ⟨Ue.mp (hon γ hγ hfi),C.marks.leading γ (hM hγ) i hi'⟩
      obtain ⟨a,ha,hs⟩:=bAm.bmF htop hmark hfi (hon γ hγ)
      have hfit :=(bW2 hp).2 i hi
      have hb:aO (shape (C.f i)).iU p :=
        ⟨max_le hfit.1 (hfit.2.1.trans hp'.1),hfit.2⟩
      exact ceY hT hd' hp' hm ⟨γ,hγ⟩ hon
        (cDD (akM.bc7 (C.f i) a) hb) (ha.2.1 a le_rfl)
        (cDD hs hb) ha.2.2
    · have hprod:bC (GW C cs)∉T:= by
        intro h
        change MvPolynomial.map dN.j8 (∏ i∈chartIndices C cs,C.f i)∈T at h
        rw [map_prod] at h
        exact hf (Ideal.IsPrime.prod_mem_iff.mp h)
      have hvan (γ) (hγ:γ∈M) :
          bC (GW C cs)∈Ch (extend (C.s γ)) := by
        have hex : ∃ i∈chartIndices C cs,bC (C.f i)∈Ch (extend (C.s γ)) := by
          cases cs with
          | union _ =>
            obtain ⟨i,hi,hv⟩:=C.marks.Eh γ (hM hγ)
            exact ⟨i,hi,Ue.mpr hv⟩
          | own i =>
            exact ⟨i,mem_singleton_self _,Ideal.mem_of_dvd _
              (map_dvd (MvPolynomial.map dN.j8) hp.guard.2.1.dvd) (hR γ hγ)⟩
        change MvPolynomial.map dN.j8 (∏ i∈chartIndices C cs,C.f i) ∈
          Ch (extend (C.s γ))
        rw [map_prod]
        let: (Ch (extend (C.s γ))).IsPrime :=RingHom.ker_isPrime (An _)
        exact Ideal.IsPrime.prod_mem_iff.mpr hex
      have hcnt:=section_card hT hd' hp' hm (bHn (bW2 hp).1) hprod
        (fun γ hγ=>⟨hon γ hγ,hvan γ hγ⟩)
      exact (mul_le_mul_of_nonneg_left hcnt (Nat.cast_nonneg mV)).trans (by
        linarith [mul_nonneg (Nat.cast_nonneg mV) hpn])
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty,Nat.cast_zero,mul_zero]
    exact add_nonneg hfirst hsecond
theorem proof :q8NBBre.c2 := by
  intro C R G ell cs hp T M hT hd hR hM hon
  exact aTZ hp hT hd hM hon (fun γ hγ=>hon γ hγ hR)
end
end qAIBbfd
