import ProximityPrize.SubmissionLower.ZYvV56c
import ProximityPrize.SubmissionLower.ZbvbtFa
import ProximityPrize.SubmissionLower.ZvBUXCd
import ProximityPrize.SubmissionLower.ZBgX9Tc
import ProximityPrize.SubmissionLower.ZikdUgd
import ProximityPrize.SubmissionLower.ZggSAoc
import ProximityPrize.SubmissionLower.ZYJm62d
import ProximityPrize.SubmissionLower.Zx4Q3Zd
set_option Elab.async false
open _root_ renaming Finset → zJe, MvPolynomial.zeroLocus → zSD, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_ofNat → zWE, Nat.cast_sum → zCt, Nat.lt_succ_of_le → zB1, RingHom.ker_isPrime → zgL
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace qMiJnMd
noncomputable section
open Polynomial Finset P6_6 P6_6_7 qCj6p1d
open P6 (K)
open aR (af ao Shape shape aO cK extend bY qP)
open dN hiding vU ZV
open BO (Ue bsq)
open agL (BV EY)
open vS (bzb cZX g9 tC)
open Dr (aQG AN tW aPQ aCR bEk
  aIc aIT bHn)
open B8 (Admissible bA1 qK bJT blp)
open agM (diagonal Vw)
open rW (kT n8 aYK Gp dimension lA Yg
  Zv CX rV)
open as6 (epq)
open WI (agr cJU)
open lB (bF amo Tn afz)
open NU (RW azm b99)
open aeM (FH)
open bjX (ccZ bZB cKZ)
open qAzl5me (MemberCurve TerminalAt memberTest ZV)
open q3yAizc (weighted_box gxK)
open q5l8jMe (invariant_of_simple integrate c2l)
open P6_6_7_3 (local_weight order_mem)
open MvPolynomial (affineDegree affineDegree_nonneg)
open private hasse_zero from ProximityPrize.SubmissionLower.ZX4kd1a
open private hasse_weight hasse_one from ProximityPrize.SubmissionLower.ZiWgK3c
open private SZ from ProximityPrize.SubmissionLower.BI
open private b3Z from ProximityPrize.SubmissionLower.V
open private cDS from ProximityPrize.SubmissionLower.V
open private b30 bGZ cKK from ProximityPrize.SubmissionLower.V
open private c7d c7g from ProximityPrize.SubmissionLower.L
open private classify from ProximityPrize.SubmissionLower.ZggSAoc
open private mark_capacity scale from ProximityPrize.SubmissionLower.Zx4Q3Zd
open private fiber_bound from ProximityPrize.SubmissionLower.ZikdUgd
open private slice4 slice5 label_bound charge from ProximityPrize.SubmissionLower.ZkoLWnc
open private aYw aYw.mk dlW product_admissible joint_admissible unclips bIi from ProximityPrize.SubmissionLower.Zsty7Cb
open private NU.btG from ProximityPrize.SubmissionLower.CE
open private NU.cKY NU.bEc from ProximityPrize.SubmissionLower.Z3BdPPe


open private agM.bEc from ProximityPrize.SubmissionLower.BI
open private alt aCd bT8 DB cSx from ProximityPrize.SubmissionLower.BI
open private dju c4r from ProximityPrize.SubmissionLower.CE
open private thin thin_degree raw_shift from ProximityPrize.SubmissionLower.ZnczBaa
open private count from ProximityPrize.SubmissionLower.ZYJm62d


private def marks {C:Context} {R:af 4} (A:Charts C R) :zJe K:= by
  classical exact C.Δ.filter fun γ=>xN C R γ∧stratum A γ = .taylor
private def charged {C:Context} {R:af 4} (A:Charts C R) (T:zJe K) :ℚ :=
  (feeScale :ℚ) * ∑ γ∈T,(genericOrder R (A.aI γ) :ℚ)
private def ProperParent (R:af 4) (P:n8) :Prop :=
  ∃ r,YR R P r∧bC (memTest ((separant^[r]) R))∉P
private def mass (C:Context) (R:af 4) (proper :Bool) :ℚ:= by
  classical
  let J:=kC R (an1 C)
  exact ∑ P∈J.minimalPrimesFinset.filter (fun P=>ProperParent R P↔proper=true),
    (Yg J P:ℚ)*affineDegree P
private abbrev memberB (a :Shape) :ℕ:=(weightedChart (bf+1) a).b
private def family (C:Context) (R:af 4) (γ:K) (B:kT) :Prop :=
  aYK R B ∧
    (∀ j:Fin aR.bf,bf≤j.val→MvPolynomial.X j∈B) ∧
    Gp (extend (C.s γ))∈zSD ao B
private def curveW {C:Context} {R:af 4} (A:Charts C R) (γ:K) :Prop :=
  ∃ B,family C R γ B∧dimension B=1 ∧
    ∃ h:MemberCurve (chartAt A γ) (A.aI γ) (lA B),
      lA B≤Ch (extend (C.s γ))∧h.simple
private def promotedW {C:Context} {R:af 4} (A:Charts C R) (γ:K) :Prop :=
  ∃ B,family C R γ B∧dimension B=2 ∧
    (kC R (an1 C)).IsMinimalPrime (lA B) ∧
    ¬ ProperParent R (lA B) ∧
    (∀ u,EY u<genericOrder R (A.aI γ)→bC (BV u R)∈lA B)
private theorem on_chart {C:Context} {R:af 4} {A:Charts C R} {γ:K} (hγ:γ∈marks A) :
    let g:=chartAt A γ
    (kC R (an1 C)).IsMinimalPrime (A.aI γ) ∧
    A.aI γ≤Ch (extend (C.s γ)) ∧
    YR R (A.aI γ) (A.index (A.aI γ)) ∧
    cK (separant g) (extend (C.s γ))≠0∧Invariant g (A.aI γ) ∧
    bC (memberTest g)∉A.aI γ:= by
  classical
  let g:=chartAt A γ
  obtain ⟨hΔ,ha,ht⟩:=mem_filter.mp hγ
  obtain ⟨hZ,hmark,hchart⟩:=A.valid γ hΔ ha
  change (if cK (separant g) (extend (C.s γ))=0 then Stratum.boundary
    else if ¬ Invariant g (A.aI γ) then .zD
    else if bC (memberTest g)∈A.aI γ then .fresh else .taylor) = .taylor at ht
  split_ifs at ht with hreg hinv he
  exact ⟨hZ,hmark,hchart,hreg,hinv,he⟩
private theorem fresh_sum_bound {C:Context} {R:af 4} (h:Input C R)
    {A:Charts C R} {T:zJe K} (hT:T⊆C.Δ)
    {Pset :zJe n8}
    (hw : ∀ γ∈T,∃ B:kT,aYK R B∧dimension B=2 ∧
      (kC R (an1 C)).IsMinimalPrime (lA B) ∧
      lA B∈Pset ∧
      rV C.s γ∈zSD ao B ∧
      ∀ u,EY u<genericOrder R (A.aI γ)→bC (BV u R)∈lA B) :
    ∑ γ∈T,(genericOrder R (A.aI γ) :ℚ) ≤
      2*(gZ:ℚ) * ∑ P∈Pset,(Yg (kC R (an1 C)) P:ℚ)*affineDegree P:= by
  classical
  let J:=kC R (an1 C)
  let B (γ:K) :kT:=if hγ:γ∈T then (hw γ hγ).choose else ⊥
  have hb (γ) (hγ:γ∈T) :aYK R (B γ)∧dimension (B γ)=2 ∧
      J.IsMinimalPrime (lA (B γ))∧lA (B γ)∈Pset ∧
      rV C.s γ∈zSD ao (B γ) ∧
      ∀ u,EY u<genericOrder R (A.aI γ)→bC (BV u R)∈lA (B γ) := by
    simpa only [B,dite_eq_left hγ] using (hw γ hγ).choose_spec
  let img (γ:K) :=lA (B γ); let L:=T.image img
  let fib (P:n8) :=T.filter fun γ=>img γ=P
  let deg (P:n8) :=(Yg J P:ℚ)*affineDegree P
  have hR:=agr h.factor.1.ne_zero
  have hrel :=amo R (an1 C) h.factor.1 h.proper
  have hloc (P:n8) (hP:P∈L) :
      ∑ γ∈fib P,(genericOrder R (A.aI γ) :ℚ)≤2*(gZ:ℚ)*deg P:= by
    obtain ⟨δ,hδ,he⟩:=mem_image.mp hP
    obtain ⟨hm,hd,hp,_,_,_⟩:=hb δ hδ
    have hpos :=cJU _ hp.isPrime.ne_top (aQG hR hrel hp)
    have hcard:=mark_capacity (C.messages.mono ((filter_subset _ _).trans hT)) hm hd
      (Γ:=fib P) (fun γ hγ=> by
        obtain ⟨hγT,heq⟩:=mem_filter.mp hγ; obtain ⟨hn,_,_,_,hx,_⟩:=hb γ hγT
        have hEq:B γ=B δ:=P0_9_6_3.freshImage_injective R ⟨hn.prime,hn.regular⟩ ⟨hm.prime,hm.regular⟩ (heq.trans he.symm)
        exact hEq ▸ hx) hpos
    change lA (B δ)=P at he
    rw [he] at hcard
    have hwt (γ) (hγ:γ∈fib P) :genericOrder R (A.aI γ)≤Yg J P:= by
      obtain ⟨hγT,hEq⟩:=mem_filter.mp hγ; obtain ⟨_,_,hp',_,_,hr⟩:=hb γ hγT
      change lA (B γ)=P at hEq; rw [hEq] at hp' hr
      have hc (u:Fin 4 →₀ ℕ) (hu:EY u<1) :bC (BV u (an1 C))∈P:= by
        have hu0:u=0:=(Finsupp.degree_eq_zero_iff _).mp (Nat.lt_one_iff.mp hu)
        rw [hu0,hasse_zero]; exact hp'.le (Ideal.subset_span (by simp))
      simpa only [one_mul] using qnODzma.dlP hR hrel hp' hr hc
    calc _ ≤ ∑ _γ∈fib P,(Yg J P:ℚ) :=sum_le_sum fun γ hγ=> by exact_mod_cast hwt γ hγ
      _=((fib P).card:ℚ)*Yg J P:= by simp
      _≤(2*(gZ:ℚ)*affineDegree P)*Yg J P :=
          mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ = _:= by unfold deg; ring
  calc _ = ∑ P∈L,∑ γ∈fib P,(genericOrder R (A.aI γ) :ℚ) :=
        (sum_fiberwise_of_maps_to (fun _ hγ=>mem_image_of_mem img hγ) _).symm
    _ ≤ ∑ P∈L,2*(gZ:ℚ)*deg P:=sum_le_sum hloc
    _=2*(gZ:ℚ) * ∑ P∈L,deg P:=(mul_sum ..).symm
    _≤_:=mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
        (fun P hP=> by obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hP; exact (hb γ hγ).2.2.2.1)
        (fun P _ _=>mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P))) (by positivity)
theorem fresh_bound {C:Context} {R:af 4} (h:Input C R) (A:Charts C R) :
    (feeScale :ℤ)*weight A .fresh≤fresh32 (shape R) (remainingChart C.v) := by
  classical
  let T:=C.Δ.filter fun γ=>xN C R γ∧stratum A γ = .fresh
  have h1 :=fresh_sum_bound h (A:=A) (T:=T) (filter_subset _ _)
    (Pset :=(kC R (an1 C)).minimalPrimesFinset) (fun γ hγ=> by
      obtain ⟨hΔ,ha,hf⟩:=mem_filter.mp hγ
      obtain ⟨hp,hm,hc⟩:=A.valid γ hΔ ha; let _:=hp.isPrime
      let P:=A.aI γ; let a :=A.index P; let g:=chartAt A γ; let S:=extend (C.s γ)
      have hs :cK (separant g) S≠0:= fun hz=> by simp [stratum,g,S,hz] at hf
      have hi:Invariant g P:=by_contra fun hn=> by
        simp [stratum,← show g=chartAt A γ from rfl,← show S=extend (C.s γ) from rfl,
          ← show P=A.aI γ from rfl,hs,hn] at hf
      have he :bC (memTest g)∈P:=by_contra fun hn=> by
        simp [stratum,← show g=chartAt A γ from rfl,← show S=extend (C.s γ) from rfl,
          ← show P=A.aI γ from rfl,hs,hi,hn] at hf
      obtain ⟨U,hU,_,hcont⟩:=integrate h.factor.2.2 h.cutterWeight
        (epq (c2l h.factor.2.2) a) hp.le (hc.2.1 a le_rfl) hc.2.2 he hi
      let B:=Zv (CX P) U; have hB:B.IsPrime :=zgL _
      obtain ⟨hext,hd,_⟩:=bRp.proof B hB
      obtain ⟨hcontain,hold,hg,hsep⟩:=bas.gDB hU hc.2.2
      have hEq:lA B=P:=Minimal.eq_of_le hp ⟨b30 hext,hcontain⟩ hold
      have hdim:=aQG (agr h.factor.1.ne_zero)
        (amo R (an1 C) h.factor.1 h.proper) hp
      have hdeg:S.natDegree<aR.bf := by
        simpa only [S,extend,natDegree_map] using (C.messages.degree γ hΔ).trans_lt (by decide :gZ<aR.bf)
      refine ⟨B,⟨hB,hext,⟨a,hg,hsep⟩,bGZ bRq.proof hB hext hg hsep⟩,
        by rw [← hd,← cKK bRq.proof hB hext hg hsep,hEq]; exact hdim,
        hEq.symm ▸ hp,Ideal.mem_minimalPrimesFinset.mpr (hEq.symm ▸ hp),hU.specializes S hdeg hm hs,
        fun u hu=>b3Z _ hU.degree _ (hcont _ (hasse_weight u h.factor.2.2) (order_mem R P hu))⟩)
  have h2 : (∑ γ∈T,genericOrder R (A.aI γ))≤2*gZ*(shape R).b*(remainingChart C.v).b:= by
    have hq : ∑ γ∈T,(genericOrder R (A.aI γ) :ℚ)≤2*(gZ:ℚ)*(shape R).b*(remainingChart C.v).b:= by
      rw [mul_assoc (2*(gZ:ℚ))]
      exact h1.trans (mul_le_mul_of_nonneg_left (cycle_budget h) (by positivity))
    exact_mod_cast hq
  rw [show weight A .fresh = ∑ γ∈T,genericOrder R (A.aI γ) by simp only [weight,T,sum_filter]]
  exact scale (shape R) (remainingChart C.v) h2
private theorem fresh_test_mem {F:Type} [Field F] (k :ao →+* F) {U:F[X]}
    (hd:U.natDegree<aR.bf) (g:af 4) (hg:rW.jW k g U=0)
    (n:ℕ) (hn:U.natDegree<n) :
    bC (su g n)∈lA (Zv k U) := by
  let _:Algebra ao F:=k.toAlgebra
  have hz :=bat.bpF false g (by intro h; cases h) U hg n
  rw [c7d,iterate_derivative_eq_zero hn,mul_zero] at hz
  exact b3Z k hd _ hz
private theorem iterate_weight {R:af 4} (h:tB R aWx) (j:ℕ) :
    tB ((separant^[j]) R) aWx := by
  induction j with
  | zero=>exact h
  | succ j ih=>rw [Function.iterate_succ_apply',separant,← hasse_one]; exact hasse_weight _ ih
private theorem d29 (g:af 4) (U:ao[X]) (hg:cK g U=0)
    (n:ℕ) (hU:U.natDegree<n) :cK (su g n) U=0:= by
  rw [arh _ _ hg,iterate_derivative_eq_zero hU,mul_zero]
private theorem stable_of_not_terminal {C:Context} {R:af 4} {A:Charts C R} {γ:K}
    (hγ:γ∈marks A) (hn : ¬ TerminalAt (chartAt A γ) (A.aI γ) (extend (C.s γ))) :
    ∃ P,∃ hm:MemberCurve (chartAt A γ) (A.aI γ) P,
      P≤Ch (extend (C.s γ))∧hm.simple∧bC (ZV (chartAt A γ))∈P:= by
  classical
  let g:=chartAt A γ; let U₀:=extend (C.s γ)
  obtain ⟨_,hmark,hchart,_,_,hpr⟩:=on_chart hγ
  have hd0:U₀.natDegree<bf := by
    rw [show U₀.natDegree=(C.s γ).natDegree from natDegree_map _]
    exact zB1 (C.messages.degree γ (mem_filter.mp hγ).1)
  have hev :cK (memberTest g) U₀=0 :=
    d29 g U₀ (Ue.mp (hmark (hchart.2.1 _ le_rfl))) bf hd0
  obtain ⟨P,hp,hpoint⟩:=bsq hmark hev
  let hm:MemberCurve g (A.aI γ) P:=⟨hpr,hp⟩
  exact ⟨P,hm,hpoint,by_contra fun hh=>hn ⟨P,hm,hpoint,Or.inl hh⟩,
    by_contra fun hh=>hn ⟨P,hm,hpoint,Or.inr hh⟩⟩
private theorem continued {C:Context} {R:af 4} (h:Input C R) {A:Charts C R} {γ:K}
    (hγ:γ∈marks A) (hn : ¬ TerminalAt (chartAt A γ) (A.aI γ) (extend (C.s γ))) :
    curveW A γ∨promotedW A γ:= by
  classical
  let r :=A.index (A.aI γ); let surf :=A.aI γ; let g:=chartAt A γ
  let G:=an1 C; let U₀:=extend (C.s γ)
  obtain ⟨hZ,_,hchart,hreg,hI,_⟩:=on_chart hγ
  obtain ⟨P,hm,hpoint,hone,hnext⟩:=stable_of_not_terminal hγ hn
  let _:=hm.minimal.isPrime
  have hΔ:=(mem_filter.mp hγ).1
  have hGb: (shape G).b≤133:=h.H6.1.trans
    (max_le (Nat.sub_le ..) ((min_le_left _ _).trans ((Nat.sub_le ..).trans (by decide))))
  have hsmall:oA (kC R G) surf hZ.isPrime<(K1.p:ℕ∞) := by
    obtain ⟨v,hv,hlen,_⟩:=local_weight h.factor.1 h.proper hZ (Nat.zero_le _)
    rw [hlen]; exact_mod_cast (hv.trans (Nat.mul_le_mul h.ahD.1 hGb)).trans_lt (by decide :Wk.b*133<K1.p)
  have hs :bC (separant g)∉P:= fun hp=>hreg (Ue.mp (hpoint hp))
  have hi:=invariant_of_simple hZ hsmall hI hm hone hs hnext
  have hle :surf≤P:=le_sup_left.trans hm.minimal.le
  obtain ⟨U,hU,hshort,hcont⟩:=integrate h.factor.2.2 h.cutterWeight
    (epq (c2l h.factor.2.2) r) (hZ.le.trans hle)
    (hle (hchart.2.1 r le_rfl)) hs (hm.minimal.le (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))) hi
  let k :=CX P; let B:=Zv k U; let J:=lA B
  have hpB:B.IsPrime :=zgL _
  obtain ⟨hext,hdim,_⟩:=bRp.proof B hpB
  obtain ⟨hcontain,hold,hBg,hBs⟩:=bas.gDB hU hs
  have hdimJ:=(cKK bRq.proof hpB hext hBg hBs).trans hdim
  have hfam:family C R γ B:= by
    have hd:U₀.natDegree<aR.bf := by
      rw [show U₀.natDegree=(C.s γ).natDegree from natDegree_map _]
      exact (zB1 (C.messages.degree γ hΔ)).trans_le (by decide)
    refine ⟨⟨hpB,hext,⟨r,hBg,hBs⟩,bGZ bRq.proof hpB hext hBg hBs⟩,
      fun j hj => ?_,hU.specializes U₀ hd hpoint hreg⟩
    change MvPolynomial.eval₂Hom k (fun i:Fin aR.bf=>U.coeff i.val) (MvPolynomial.X j)=0
    rw [MvPolynomial.eval₂Hom_X']; exact Polynomial.coeff_eq_zero_of_natDegree_lt (hshort.trans_le hj)
  have hcyc (S:n8) (hS: (kC R G).IsMinimalPrime S) :dimension S=2 :=
    aQG (agr h.factor.1.ne_zero) (amo R G h.factor.1 h.proper) hS
  have hdP:1≤dimension P:= by
    let _:=hZ.isPrime
    have hc:=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hm.proper hm.minimal
    change dimension P+1=dimension surf at hc; rw [hcyc surf hZ] at hc; omega
  rcases classify hm.minimal.isPrime (b30 hext) hcyc hdP hcontain hold with ⟨hd1,hp⟩ | ⟨hd2,hmin⟩
  · exact Or.inl ⟨B,hfam,hdimJ.symm.trans hd1,hp.symm ▸ ⟨hm,hpoint,hone⟩⟩
  have hcan:YR R J r :=
    ⟨hchart.1,fun j hj=>b3Z k hU.degree _
      (hcont _ (iterate_weight h.factor.2.2 j) (hle (hchart.2.1 j hj))),hBs⟩
  have hmem:bC (memTest ((separant^[r]) R))∈J :=
    fresh_test_mem k hU.degree ((separant^[r]) R) hU.bY bf hshort
  refine Or.inr ⟨B,hfam,hdimJ.symm.trans hd2,hmin,?_,?_⟩
  · rintro ⟨a,ha,hn⟩
    have hea :=cDS ha hcan
    subst a
    exact hn hmem
  · intro u hu
    exact b3Z k hU.degree _
      (hcont _ (hasse_weight _ h.factor.2.2) (hle (order_mem R surf hu)))
private def aRQ (p:Shape) :Prop :=
  let u:=bf+1; let v :=bf+2
  3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
    3*(2+(u - 5)*p.t)≤(qP u p).j∧3*(2+(v - 5)*p.t)≤(qP v p).j ∧
    2*u≤(qP u p).t∧2*v≤(qP v p).t
private def boxes (p q:Shape) :B8.lS:= fun i =>
  if i=0 then (p,0) else if i=1 then (q,0) else if i=2 then (tC p,1)
  else if i=3 then (qP (bf+1) p,bf+1)
  else (qP (bf+2) p,bf+2)
private theorem terminal_bound {C:Context} {R:af 4} (h:Input C R)
    {A:Charts C R} {M:zJe K} (hM:M⊆marks A)
    (hterm : ∀ γ∈M,TerminalAt (chartAt A γ) (A.aI γ) (extend (C.s γ))) (dR:Bool) :
    let a :=cap R
    charged A M≤(mV:ℚ)*(pair32 dR a a (remainingChart C.v) :ℚ) +
      32*(mV:ℚ)*memberB a*mass C R true := by
  classical
  intro a
  let Q:=Branch R (an1 C) 1
  have mkBr (γ:M) : ∃ b:Q,b.aI=A.aI γ∧b.g=chartAt A γ∧b.dY (extend (C.s γ)) := by
    obtain ⟨hz,hon,hc,hr,_,_⟩:=on_chart (hM γ.property)
    obtain ⟨P,hp,hP,ht⟩:=hterm γ γ.property
    have hreg:An (extend (C.s γ)) (sigma (chartAt A γ))≠0:= by
      rw [afz]; exact fun he=>hr (SZ (he.trans (map_zero _).symm))
    exact ⟨⟨A.aI γ,hz,by simpa only [one_mul] using (gH h hz).2.2,chartAt A γ,P,hp,
      fun hs=>hreg (hP hs),fun hs=>ht.resolve_left (fun hn=>hn hs)⟩,rfl,rfl,
      hP,Ue.mp (hon (hc.2.1 _ le_rfl)),hreg⟩
  let b (γ:M) :Q:=(mkBr γ).choose
  have spec (γ:M) :=(mkBr γ).choose_spec
  let F:=M.attach.image b
  let L (c:Q) :=M.filter (fun γ => ∃ hm:γ∈M,b ⟨γ,hm⟩=c)
  have hsub (c:Q) :L c⊆C.Δ:=(filter_subset _ _).trans (hM.trans (filter_subset _ _))
  have hon (c:Q) (γ) (hγ:γ∈L c) :c.dY (extend (C.s γ)) := by
    obtain ⟨hm,he⟩:=(mem_filter.mp hγ).2; exact he ▸ (spec ⟨γ,hm⟩).2.2
  have hdata (c:Q) (hc:c∈F) :ProperParent R c.aI∧c.g=(separant^[A.index c.aI]) R ∧
      aO (shape c.g) a∧0<(shape c.g).t∧Nonempty (dmL c.g a) := by
    obtain ⟨γ,_,rfl⟩:=mem_image.mp hc; obtain ⟨hz,hg,_⟩:=spec γ
    obtain ⟨_,_,hcan,hr,_,hp⟩:=on_chart (hM γ.property)
    have hfit :aO (shape (b γ).g) a :=hg.symm ▸ akM.bc7 R (A.index (A.aI γ))
    have hpos :0<(shape (b γ).g).t:= by
      by_contra! ht0
      exact (hg.symm ▸ hr) (by rw [separant,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero (Nat.le_zero.mp ht0)]; exact map_zero _)
    have hch:Nonempty (dmL (b γ).g a) := by
      by_cases ht1 :a.t=1
      · exact qyN3hZb.proof (b γ).g a (Tn R) hfit hpos ht1
      · exact qQEcrEc.proof (b γ).g a (Tn R) hfit hpos ht1
    exact ⟨hz.symm ▸ ⟨A.index (A.aI γ),hcan,hp⟩,by rw [hz,hg],hfit,hpos,hch⟩
  have hsame :SameChart F:= fun c hc d hd hz=> by rw [(hdata c hc).2.1,(hdata d hd).2.1,hz]
  have avail (c:Q) : ∃ D⊆L c,(c.Simple→D =L c) ∧
      (c∈F → ¬ c.Simple→agC (L c) C.s D.card∧bzb (L c) C.s D) := by
    by_cases hs :c.Simple
    · exact ⟨L c,Subset.rfl,fun _=>rfl,fun _ hn=>(hn hs).elim⟩
    by_cases hc:c∈F
    · obtain ⟨γ,_,he⟩:=mem_image.mp hc
      obtain ⟨D,hD,_,sct,cut⟩:=cZX (L c) C.s ⟨γ.val,mem_filter.mpr ⟨γ.property,γ.property,he⟩⟩
      exact ⟨D,hD,fun hh=>(hs hh).elim,fun _ _=>⟨sct,cut⟩⟩
    · exact ⟨∅,empty_subset _,fun hh=>(hs hh).elim,fun hh _=>(hc hh).elim⟩
  choose D hD hsimple hmult using avail
  have hcase (c:Q) (hc:c∈F) : (c.Simple∧D c=L c)∨bzb (L c) C.s (D c) := by
    by_cases hs :c.Simple
    · exact Or.inl ⟨hs,hsimple c hs⟩
    · exact Or.inr (hmult c hc hs).2
  have hR:=agr h.factor.1.ne_zero
  have hrel :=amo R (an1 C) h.factor.1 h.proper
  let J:=kC R (an1 C); let S:=F.image Branch.aI
  let V (z :Ideal GeoJets) :=F.filter fun c=>c.aI=z
  have hS (z) (hz :z∈S) :J.IsMinimalPrime z∧ProperParent R z := by
    obtain ⟨c,hc,rfl⟩:=mem_image.mp hz; exact ⟨c.base,(hdata c hc).1⟩
  have hadd: (additiveCost F:ℚ)≤ memberB a*mass C R true := by
    rw [additiveCost,zCt]
    change _≤((memberBox a).b:ℚ) * ∑ z∈J.minimalPrimesFinset.filter (fun z=>ProperParent R z↔true=true),
      (Yg J z :ℚ)*affineDegree z
    rw [mul_sum]
    calc _ = ∑ z∈S,∑ c∈V z,((c.weight*c.extra :ℕ) :ℚ) :=
          (sum_fiberwise_of_maps_to (fun _ hc=>mem_image_of_mem _ hc) _).symm
      _ ≤ ∑ z∈S,((memberBox a).b:ℚ)*((Yg J z :ℚ)*affineDegree z) :=sum_le_sum fun z hz =>
          fiber_bound (hS z hz).1 (aQG hR hrel (hS z hz).1) _ (fun c hc=>(mem_filter.mp hc).2)
            (fun c hc d hd he=>hsame c (mem_filter.mp hc).1 d (mem_filter.mp hd).1 he)
            (fun c hc=>⟨(hdata c (mem_filter.mp hc).1).2.2.2.2.some.toMember4⟩)
      _≤_:=sum_le_sum_of_subset_of_nonneg
          (fun z hz=>mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr (hS z hz).1,by simpa using (hS z hz).2⟩)
          (fun z _ _=>mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg _)))
  have hdem:32*(demandCost F D:ℚ)≤(pair32 dR a a (remainingChart C.v) :ℚ) := by
    let q:=remainingChart C.v; have hq:bF q:=(P6_6_8_3.remaining_fits C.v).2
    have hfalse :32*(demandCost F D:ℚ)≤(pair32 false a a q:ℚ) := by
      let mb:=memberBox a; let sb:=sliceBox a
      have hmb:Dr.ChamberBox mb:=weighted_box (by decide)
      have hsb:Dr.ChamberBox sb:=weighted_box (by decide)
      have hb : ∀ x∈[mb,sb],bF x := by simp [show bF mb from ⟨hmb.1,hmb.2.1⟩,show bF sb from ⟨hsb.1,hsb.2.1⟩]
      have hgrp: (demandCost F D:ℚ) = ∑ z∈S,(genericOrder R z :ℚ) * ∑ c∈V z,((c.demandWeight*(D c).card:ℕ) :ℚ) := by
        simp only [demandCost,zCt,z2R,Branch.weight,one_mul]
        rw [← sum_fiberwise_of_maps_to (fun c hc=>mem_image_of_mem Branch.aI hc)
          (fun c=>(genericOrder R c.aI:ℚ)*((c.demandWeight:ℚ)*((D c).card:ℚ)))]
        exact sum_congr rfl fun z _=> by rw [mul_sum]; exact sum_congr rfl fun c hc=> by rw [(mem_filter.mp hc).2]
      rw [hgrp]
      have h1 : (∑ z∈S,(genericOrder R z :ℚ) * ∑ c∈V z,((c.demandWeight*(D c).card:ℕ) :ℚ)) ≤
          ∑ z∈S,(AN J z :ℚ)*tW z [mb,sb] :=sum_le_sum fun z hz=> by
        obtain ⟨c,hc,rfl⟩:=mem_image.mp hz
        have hss :=gxK C c (aQG hR hrel c.base) hmb hsb
          (hdata c hc).2.2.2.2.some.toMember4 _ D
          (fun d hd=>⟨(mem_filter.mp hd).2,hsame d (mem_filter.mp hd).1 c hc (mem_filter.mp hd).2⟩)
          (fun d hd=> by
            have hdF:=(mem_filter.mp hd).1
            exact ⟨slice4 d (hdata d hdF).2.2.2.2.some (hsub d) (hD d) (hon d) (hcase d hdF),
              (hD d).trans (hsub d),fun γ hγ=>hon d γ (hD d hγ)⟩)
        exact mul_le_mul (by exact_mod_cast (gH h (hS _ hz).1).1) hss (sum_nonneg fun _ _=>zqJ _) (by positivity)
      let H :Ideal GeoJets :=Ideal.span {bC R}
      have hregR:IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (bC R)) :=
        aPQ (by infer_instance) (by simpa using hR)
      have hregG:=aIT R (an1 C) hrel
      have hH :dimension H≤3:= by simpa [H,bEk] using aCR hregR
      have hJ:J=H ⊔ Ideal.span {bC (an1 C)} := aIc R (an1 C)
      have hdJ:dimension J≤2 := by rw [hJ]; exact (aCR hregG).trans (by change dimension H - 1≤2; omega)
      have h2 : (∑ z∈S,(AN J z :ℚ)*tW z [mb,sb])≤(wP a q mb sb:ℚ)/32 := calc
        _≤tW J [mb,sb] :=qZqYIua.retain_cycle J [mb,sb] hb (by simp) (by simpa using hdJ) S (fun z hz=>(hS z hz).1)
        _≤tW H [q,mb,sb] := by
            rw [hJ]; exact bau.proof H q [mb,sb] hq hb (by simp) (by simpa using hH) _ (bHn h.H6) hregG
        _≤_:=qZqYIua.literal_bound R a q mb sb h.factor.1.ne_zero (akM.a1n R) hq ⟨hmb.1,hmb.2.1⟩ ⟨hsb.1,hsb.2.1⟩
      change _≤(wP a q mb sb:ℚ)
      rw [mul_comm]; exact (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp (h1.trans h2)
    cases dR
    · exact hfalse
    · by_cases ht1 : (shape R).t=1
      · have ha1 :a.t=1 :=ht1
        have heq :pair32 true a a q=pair32 false a a q:= by simp [pair32,ha1]
        change 32*(demandCost F D:ℚ)≤(pair32 true a a q:ℚ)
        rw [heq]; exact hfalse
      · have ht:1<(shape R).t:= by have :=h.positive; omega
        have hbt: (a.t != 1)=true := by change ((shape R).t != 1)=true; simpa using Nat.ne_of_gt ht
        let B:=boxes a q; let fSec:=B8.i9 ⊥ (qK (bC R))
        have hbnz (i:Fin 5) (hi:i≠0) :B i=qsnQ6jb.boxes q a i:= by
          simp only [B,boxes,qsnQ6jb.boxes,ite_eq_right hi]
        have hP:Admissible B:=⟨fun i=> by
            by_cases hi:i=0
            · subst i; exact Tn R
            · rw [hbnz i hi]; exact (product_admissible q a hq).1 i,
          fun v=>⟨4,by
            obtain ⟨hb,hj,ht',hd'⟩:=bIi q a; rw [hbnz 4 (by decide)]
            apply blp
            change 1≤2*(qsnQ6jb.boxes q a 4).1.b∧3≤2*(qsnQ6jb.boxes q a 4).1.j ∧
              1≤2*(qsnQ6jb.boxes q a 4).1.t∧1≤2*(qsnQ6jb.boxes q a 4).2
            omega⟩⟩
        have h5 (c:Q) (hc:c∈F) :Nonempty (Member5 c.g a)∧bMD a c C.s (D c) ∧
            D c⊆C.Δ ∧ ∀ γ∈D c,c.dY (extend (C.s γ)) := by
          obtain ⟨ch⟩:=qBCdrib.proof c.g a (Tn R) (hdata c hc).2.2.1 (hdata c hc).2.2.2.1 ht
          exact ⟨⟨ch.toMember5⟩,slice5 c ch (hsub c) (hD c) (hon c) (hcase c hc),
            (hD c).trans (hsub c),fun γ hγ=>hon c γ (hD c hγ)⟩
        have hreg5:IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal g9) (qK (bC R))) := by
          apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
          rw [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_bot]
          exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne hR
        have hall: (insert (0:Fin 5) {1, 2,3,4} : Finset (Fin 5))=Finset.univ := by decide
        have hpol (Fn:Shape×ℕ→ℚ) :
            (∑ J∈(Finset.univ :Finset (Fin 5)).powerset,(-1 :ℚ)^(5-J.card)*Fn (Vw B (fun i=>if i∈J then 2 else 1))) =
              DB (qP (bf+2) a,bf+2)
                (DB (qP (bf+1) a,bf+1)
                  (DB (tC a,1) (DB (q,0) (DB (a,0) Fn))))
                (Vw B (diagonal ∅)) := by
          change alt B Finset.univ Fn= _
          have hu: (Finset.univ :Finset (Fin 5))=insert 0 (insert 1 (insert 2 (insert 3 (insert 4 ∅)))) := by decide
          rw [hu,aCd _ (by decide),aCd _ (by decide),aCd _ (by decide),
            aCd _ (by decide),aCd _ (by decide),bT8]; rfl
        by_cases hg:aRQ a
        · have hJ:NU.Admissible B:= by
            have hj:=joint_admissible q a hq hg
            refine ⟨fun i => ?_,hj.2⟩
            by_cases hi:i=0
            · subst i; exact ⟨Tn R,Nat.zero_le _⟩
            · rw [hbnz i hi]; exact hj.1 i
          obtain ⟨hgu,hmu,hsu⟩:=unclips hg
          have h1 :=dlW (aYw.mk (aKL.proof B hJ) (@aZB.proof B hJ))
            (NU.btG (NU.cKY aKL.proof aZB.proof) B hJ)
            qEAwGBc.proof qfClb8d.proof h.factor.1 h.proper (b99 h.H6) F D hsame h5
            (fun _ hE=> by rw [hgu] at hE; exact hE) (fun _ hE=> by rw [hmu] at hE; exact hE)
            (fun _ hE=> by rw [hsu] at hE; exact hE)
          have h2 :=aKL.proof B hJ ⊥ {1, 2,3,4} 0 (by decide) bA1 _ (b99 (first_box R)) hreg5
          rw [hall] at h2
          have h3:32*RW B ⊥ Finset.univ=(pair32 true a a q:ℚ) := by
            unfold RW; simp only [card_univ,Fintype.card_fin]
            rw [show (2 :ℚ)^5=32 by norm_num,← mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num)]
            simp only [NU.bEc bAn.proof B hJ.1]
            change alt B Finset.univ azm= _
            rw [show alt B Finset.univ azm= _ from hpol azm,dju]
            dsimp only [aRQ] at hg
            simp only [show NU.direction=NU.aD ⟨1,4, 2⟩ by rfl,c4r,
              pair32,hbt,Bool.and_true,ite_true,ite_eq_left hg,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast]; rfl
          rw [← h3]; exact mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
        · have h1 :=dlW (aYw.mk (ccZ B hP) (@bZB B hP))
            (B8.btG cKZ B hP (bIi q a))
            qEAwGBc.proof qfClb8d.proof h.factor.1 h.proper (bJT h.H6) F D hsame h5
            (fun _ hE=>ac7.FH.ctq hE) (fun _ hE=>ac7.FH.ctq hE)
            (fun _ hE=>ac7.FH.ctq hE)
          have h2 :=ccZ B hP ⊥ {1, 2,3,4} 0 (by decide) bA1 _ (bJT (first_box R)) hreg5
          rw [hall] at h2
          have h3:32*B8.tW B ⊥ Finset.univ=(pair32 true a a q:ℚ) := by
            unfold B8.tW; simp only [card_univ,Fintype.card_fin]
            rw [show (2 :ℚ)^5=32 by norm_num,← mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num)]
            simp only [agM.bEc cys.proof cyt.proof B hP.1,hpol,cSx]
            dsimp only [aRQ] at hg
            simp only [pair32,hbt,Bool.and_true,ite_true,ite_eq_right hg,Int.cast_add,Int.cast_mul,Int.cast_natCast]; rfl
          rw [← h3]; exact mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
  have hsum: (∑ γ∈M,genericOrder R (A.aI γ)) = ∑ c∈F,c.weight*(L c).card:= by
    let w (γ:K) :=genericOrder R (A.aI γ)
    calc _ = ∑ γ∈M.attach,w γ:=(sum_attach M w).symm
      _ = ∑ c∈F,∑ γ∈M.attach.filter (fun γ=>b γ=c),w γ :=
          (sum_fiberwise_of_maps_to (fun γ _=>mem_image_of_mem b (mem_attach _ γ)) (fun γ=>w γ)).symm
      _ = _:=sum_congr rfl fun c _=> by
          have hc: (M.attach.filter (fun γ=>b γ=c)).card=(L c).card:= by
            rw [filter_attach']; simp only [card_map,card_attach,L]
          rw [← hc]
          calc _ = ∑ γ∈M.attach.filter (fun γ=>b γ=c),c.weight:=sum_congr rfl fun γ hγ=> by
                dsimp only [w]
                rw [← (spec γ).1]
                change genericOrder R (b γ).aI=c.weight
                rw [(mem_filter.mp hγ).2,Branch.weight,one_mul]
            _ = _:= by simp [Nat.mul_comm]
  have hp: (mV:ℚ)*((∑ c∈F,c.weight*(L c).card:ℕ) :ℚ) ≤
      (mV:ℚ)*(demandCost F D:ℚ)+mV*(additiveCost F:ℚ) := by
    exact_mod_cast charge F L D fun c hc=>label_bound c (hsub c) ⟨hsimple c,fun hn=>(hmult c hc hn).1⟩
  have hsc:charged A M=32*(mV:ℚ)*((∑ c∈F,c.weight*(L c).card:ℕ) :ℚ) := by
    rw [← hsum,charged,zCt]; simp only [feeScale,z2R,zWE]
  rw [hsc]
  have hL:=mul_le_mul_of_nonneg_left hp (show (0:ℚ)≤32 by norm_num)
  have hM' := mul_le_mul_of_nonneg_left hdem (zqJ (α:=ℚ) mV)
  have hA' := mul_le_mul_of_nonneg_left hadd (show (0:ℚ)≤32*mV by positivity)
  linarith only [hL,hM',hA']
private theorem curve_bound {C:Context} {R:af 4} (h:Input C R)
    {A:Charts C R} {T:zJe K} (hT:T⊆marks A) (hw : ∀ γ∈T,curveW A γ) :
    charged A T≤32*((P6.t:ℚ)+mV)*memberB (cap R)*mass C R true := by
  classical
  let J:=kC R (an1 C); let b:ℚ:=memberB (cap R)
  let jX:ℚ:=(P6.t:ℚ)+mV; let deg (z :n8) :=(Yg J z :ℚ)*affineDegree z
  let B (γ:K) :kT:=if hγ:γ∈T then (hw γ hγ).choose else ⊥
  have data (γ) (hγ:γ∈T) :family C R γ (B γ)∧dimension (B γ)=1 ∧
      ∃ hc:MemberCurve (chartAt A γ) (A.aI γ) (lA (B γ)),
        lA (B γ)≤Ch (extend (C.s γ))∧hc.simple := by
    simpa only [B,dite_eq_left hγ] using (hw γ hγ).choose_spec
  let surfs :=T.image A.aI; let fib (z :n8) :=T.filter fun γ=>A.aI γ=z
  have hsub:T⊆C.Δ:=hT.trans (filter_subset _ _)
  have eqRow (r :ℕ) (hr :r<(shape R).t) :
      ∃ E :af 4,(bC E).totalDegree≤ memberB (cap R) ∧
        ∃ e :ℕ,memberTest ((separant^[r]) R)=separant ((separant^[r]) R)^e*E := by
    let p:=cap R; let g:=(separant^[r]) R; have hp:=Tn R
    have hg:aO (shape g) p:=akM.bc7 R r
    by_cases ht1 :p.t=1
    · have hgt: (shape g).t=1 := by
        have htop: (shape R).t=1 :=ht1; have hz :r=0:= by omega
        simp only [g,hz,Function.iterate_zero_apply,htop]
      have hb1 :1≤p.b:= by have h1 :p.j≤p.b:=hp.1; have h2 :3*p.t≤p.j:=hp.2; have h3:p.t=1 :=ht1; omega
      refine ⟨thin g (bf-3),?_,bf+3,?_⟩
      · rw [memberB,weightedChart,ite_eq_left ht1]; exact (thin_degree hg hb1 _).trans (le_max_left _ _)
      · change su g bf= _
        have hlin:=bat.exb hgt
        have heq :=raw_shift g hlin (bf-3)
        rw [show bf-3+3=bf by decide] at heq
        rw [c7g g hlin,heq,← mul_assoc,← pow_add]
    · exact ⟨memberTest g,by
        rw [memberB,weightedChart,ite_eq_right ht1]
        exact (aY3.bH1 hg hp (Nat.zero_lt_of_lt hr) (Nat.le_succ bf)).1,
        0,by rw [pow_zero,one_mul]⟩
  have hloc (z :n8) (hz :z∈surfs) :
      ∑ γ∈fib z,(mV:ℚ)*(genericOrder R (A.aI γ) :ℚ)≤jX*b*deg z := by
    obtain ⟨δ,hδ,he⟩:=mem_image.mp hz
    obtain ⟨hp,_,hchart,_,_,_⟩:=on_chart (hT hδ); rw [he] at hp hchart
    obtain ⟨E,hE,htest⟩:=eqRow (A.index z) hchart.1
    let V:=fib z; let F:=V.image B; let lbl (D:kT) :=V.filter fun γ=>B γ=D
    have facts (D:kT) (hD:D∈F) :
        (aYK R D ∧dimension D =1)∧bC E∉z∧(AX z E).IsMinimalPrime (lA D) := by
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hD; obtain ⟨hγT,hγz⟩:=mem_filter.mp hγ
      obtain ⟨hf,hd,hm,hpt,_⟩:=data γ hγT; obtain ⟨_,_,_,hreg,_,_⟩:=on_chart (hT hγT)
      have hs :bC (separant (chartAt A γ))∉lA (B γ) := fun hb=>hreg (Ue.mp (hpt hb))
      simp only [chartAt,hγz] at hm hs; exact ⟨⟨hf.1,hd⟩,q7twcKc.b85 (E :=E) hm hs htest⟩
    have hpr :bC E∉z :=(facts (B δ) (mem_image_of_mem B (mem_filter.mpr ⟨hδ,he⟩))).2.1
    have hinj:Set.InjOn lA (F:Set kT) := fun D hD D' hD' hEq =>
      P0_9_6_3.freshImage_injective R ⟨(facts D hD).1.1.prime,(facts D hD).1.1.regular⟩
        ⟨(facts D' hD').1.1.prime,(facts D' hD').1.1.regular⟩ hEq
    have hdegs : ∑ D∈F,affineDegree D ≤b*affineDegree z := by
      let _:=hp.isPrime
      calc _ = ∑ D∈F,affineDegree (lA D) :=sum_congr rfl fun D hD =>
            NS.of_children cyx.proof cyy.proof cyz.proof D
              (facts D hD).1.1.prime (facts D hD).1.1.extended_prime (facts D hD).1.2 (facts D hD).1.1.birational
        _ = ∑ P∈F.image lA,affineDegree P:=(sum_image hinj).symm
        _≤_:=(sum_le_sum_of_subset_of_nonneg (fun P hP=> by
            obtain ⟨D,hD,rfl⟩:=mem_image.mp hP; exact Ideal.mem_minimalPrimesFinset.mpr (facts D hD).2.2)
            (fun P _ _=>affineDegree_nonneg P)).trans (MvPolynomial.principalCut_sum_affineDegree_minimalPrimes_le hpr hE)
    have hcard: (mV:ℚ)*V.card≤jX*(b*affineDegree z) := calc
      _ = ∑ D∈F,∑ _γ∈lbl D,(mV:ℚ) := by
          rw [sum_fiberwise_of_maps_to (fun _ hγ=>mem_image_of_mem B hγ),sum_const,nsmul_eq_mul,mul_comm]
      _ ≤ ∑ D∈F,jX*affineDegree D:=sum_le_sum fun D hD => by
          obtain ⟨γ,hγ,hEq⟩:=mem_image.mp hD; rw [sum_const,nsmul_eq_mul,mul_comm]
          exact count ((filter_subset _ _).trans ((filter_subset _ _).trans hsub))
            (facts D hD).1.1.prime (facts D hD).1.2 ⟨γ,mem_filter.mpr ⟨hγ,hEq⟩⟩
            (fun α hα=>(mem_filter.mp hα).2 ▸ (data α (mem_filter.mp (mem_filter.mp hα).1).1).1.2.2)
      _≤_:= by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdegs (by unfold jX; positivity)
    calc _=(mV:ℚ)*V.card*(genericOrder R z :ℚ) := by
          rw [sum_congr rfl fun γ hγ=> by rw [(mem_filter.mp hγ).2],sum_const,nsmul_eq_mul]; ring
      _≤(jX*(b*affineDegree z))*(Yg J z :ℚ) :=
          mul_le_mul hcard (by exact_mod_cast (gH h hp).2.1) (Nat.cast_nonneg _)
            (mul_nonneg (by unfold jX; positivity) (mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg z)))
      _ = _:= by unfold deg; ring
  have hmass : ∑ z∈surfs,deg z≤ mass C R true :=sum_le_sum_of_subset_of_nonneg (fun z hz=> by
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz; obtain ⟨hp,_,hc,_,_,ht⟩:=on_chart (hT hγ)
    exact mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr hp,⟨fun _=>rfl,fun _=>⟨A.index (A.aI γ),hc,ht⟩⟩⟩)
    (fun z _ _=>mul_nonneg (zqJ _) (affineDegree_nonneg z))
  simp only [charged,feeScale,z2R,zWE,mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc _ = ∑ z∈surfs,∑ γ∈fib z,(mV:ℚ)*(genericOrder R (A.aI γ) :ℚ) := by
        rw [mul_sum,← sum_fiberwise_of_maps_to (fun _ hγ=>mem_image_of_mem A.aI hγ)]
    _ ≤ ∑ z∈surfs,jX*b*deg z :=sum_le_sum hloc
    _=jX*(b * ∑ z∈surfs,deg z) := by rw [← mul_sum,mul_assoc]
    _≤_:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)) (by unfold jX; positivity)
theorem taylor_bound {C:Context} {R:af 4} (h:Input C R) (A:Charts C R) (dR:Bool) :
    let a :=cap R; let p:=remainingChart C.v
    (feeScale :ℤ)*weight A .taylor≤taylor32 dR a a p:= by
  classical
  intro a p
  let all:=marks A
  let T:=all.filter fun γ=>TerminalAt (chartAt A γ) (A.aI γ) (extend (C.s γ))
  let W:=all.filter fun γ => ¬ TerminalAt (chartAt A γ) (A.aI γ) (extend (C.s γ))
  let U:=W.filter (curveW A); let V:=W.filter fun γ => ¬ curveW A γ
  have hT:=terminal_bound h (A:=A) (M:=T) (filter_subset _ _) (fun _ hγ=>(mem_filter.mp hγ).2) dR
  have hU:=curve_bound h (A:=A) (T:=U) ((filter_subset _ _).trans (filter_subset _ _)) (fun _ hγ=>(mem_filter.mp hγ).2)
  have hV:charged A V≤(feeScale :ℚ)*(2*(gZ:ℚ))*mass C R false := by
    rw [charged,mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (zqJ _)
    exact fresh_sum_bound h (A:=A) (T:=V)
      ((filter_subset _ _).trans ((filter_subset _ _).trans (filter_subset _ _)))
      (Pset :=(kC R (an1 C)).minimalPrimesFinset.filter (fun P=>ProperParent R P↔false=true))
      (fun γ hγ=> by
        obtain ⟨hW,hnc⟩:=mem_filter.mp hγ; obtain ⟨hm,hnt⟩:=mem_filter.mp hW
        obtain ⟨B,hfam,hd,hmin,hnp,hord⟩:=(continued h hm hnt).resolve_left hnc
        exact ⟨B,hfam.1,hd,hmin,mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr hmin,by simpa using hnp⟩,hfam.2.2,hord⟩)
  have hpart:charged A T+charged A U + charged A V=(feeScale :ℚ)*(weight A .taylor :ℚ) := by
    have sp (S:zJe K) (q:K→Prop) [DecidablePred q] :
        charged A (S.filter q)+charged A (S.filter fun γ => ¬ q γ)=charged A S:= by
      rw [charged,charged,charged,← mul_add,sum_filter_add_sum_filter_not]
    rw [add_assoc,sp W (curveW A),sp all]
    dsimp only [all]
    rw [charged,weight,zCt,marks,sum_filter]
    simp only [Nat.cast_ite,Nat.cast_zero]
  have hb: (gZ:ℚ)≤ memberB a := by
    have hch:a.j≤a.b∧3*a.t≤a.j:=Tn R
    have hL:gZ+1=bf :=rfl
    have hj:3≤a.j:= by have :0<a.t:=h.positive; omega
    have hle :gZ≤ memberB a := by
      unfold memberB weightedChart
      split_ifs with ht'
      · apply le_trans _ (le_max_right _ _)
        have hm:=Nat.mul_le_mul_left (bf+1-4) (show 1≤a.j - 2 by omega)
        rw [mul_one] at hm; change gZ≤3+(bf+1-4)*(a.j - 2); omega
      · apply le_trans _ (le_max_right _ _)
        have :=Nat.le_add_left (bf+1) (2*(bf+1)*(a.j-3)); omega
    exact_mod_cast hle
  have hk :0≤ mass C R false :=sum_nonneg fun _ _=>mul_nonneg (zqJ _) (affineDegree_nonneg _)
  have hv : (feeScale :ℚ)*(2*(gZ:ℚ))*mass C R false ≤
      32*((P6.t:ℚ)+2*mV)*memberB a*mass C R false := by
    simp only [feeScale,z2R,zWE]
    have h1 :32*(mV:ℚ)*(2*(gZ:ℚ))*mass C R false ≤
        32*(mV:ℚ)*(2*(memberB a :ℚ))*mass C R false := by gcongr
    have h2 :32*(2*(mV:ℚ))*memberB a*mass C R false ≤
        32*((P6.t:ℚ)+2*mV)*memberB a*mass C R false := by
      gcongr; exact le_add_of_nonneg_left (zqJ _)
    linarith only [h1,h2]
  have hmass :mass C R true+mass C R false≤(a.b:ℚ)*p.b:= by
    have hsum:mass C R true+mass C R false =
        ∑ P∈(kC R (an1 C)).minimalPrimesFinset,
          (Yg (kC R (an1 C)) P:ℚ)*affineDegree P:= by
      simpa only [mass,Bool.true_eq,Bool.false_eq_true,iff_true,iff_false] using
        (sum_filter_add_sum_filter_not (kC R (an1 C)).minimalPrimesFinset (ProperParent R)
          (fun P=>(Yg (kC R (an1 C)) P:ℚ)*affineDegree P))
    rw [hsum]
    exact (cycle_budget h).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_left _ _: (shape R).b≤a.b)) (zqJ _))
  have hmain:=add_le_add (add_le_add hT hU) (hV.trans hv); rw [hpart] at hmain
  have hfin: (feeScale :ℚ)*(weight A .taylor :ℚ) ≤
      (mV:ℚ)*(pair32 dR a a p:ℚ)+32*((P6.t:ℚ)+2*mV)*a.b*p.b*memberB a :=
    calc _≤(mV:ℚ)*(pair32 dR a a p:ℚ) +
            (32*((P6.t:ℚ)+2*mV)*memberB a)*(mass C R true+mass C R false) := by linarith only [hmain]
      _≤(mV:ℚ)*(pair32 dR a a p:ℚ) +
            (32*((P6.t:ℚ)+2*mV)*memberB a)*((a.b:ℚ)*p.b) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ = _:= by ring
  rw [taylor32]; exact_mod_cast hfin
end
end qMiJnMd
