import ProximityPrize.SubmissionLower.ZHNB5Ae
set_option Elab.async false
open _root_ renaming LinearIndependent → z14, LinearMap.finrank_range_add_finrank_ker → z7i, LinearMap.pi → z9H, Module.Finite → zAa, Module.Finite.of_injective → zfv, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.monomial_le_degreeOf → zKk, Polynomial.X → z7y, Polynomial.mapRingHom → zhd
section
set_option autoImplicit true
namespace qje58fc
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
open cu (L)
open jA (jK kS jH)
open NR (TT)
open aFO
open private fS2 dL1 from ProximityPrize.SubmissionLower.S
open private b3L bDq from ProximityPrize.SubmissionLower.S
private theorem derivative_ne {H :L[X]} (hm:H.Monic) (hp:0<H.natDegree)
  (hd:H.natDegree<K1.p) :H.derivative≠0:= by
 let:CharP L K1.p:=charP_of_injective_ringHom aR.embed.injective K1.p
 have hcast: (H.natDegree :L)≠0:= by
  intro hz
  exact (not_le_of_gt hd) (Nat.le_of_dvd hp ((CharP.cast_eq_zero_iff L K1.p _).mp hz))
 intro hz
 let n:=H.natDegree-1
 have hn:n+1=H.natDegree :=Nat.sub_add_cancel hp
 have he :=congrArg (fun f :L[X]=>f.coeff n) hz
 rw [coeff_derivative,hn,coeff_natDegree,hm.leadingCoeff,one_mul,coeff_zero] at he
 apply hcast
 rw [← hn,Nat.cast_add,Nat.cast_one]
 exact he
private theorem fW0 {H q A B:L[X]} {R:kS[X]}
   {N :I6[X]} {D:I6} (hm:H.Monic)
   (hs :cAj H 1 q A B N D 0) (hR:R.natDegree<H.natDegree)
   (hc:jH H∣bu4 1 A B*R+bu5 q) :
   awc N D 0=R:= by
 have hgen:jH H∣bu4 1 A B*awc N D 0+bu5 q:= by
   simpa only [cpt] using hs.generic_congruence
 have hunit :IsCoprime (bu4 1 A B) (jH H) := by
   simpa only [cpt] using hs.generic_unit
 have hsub:jH H∣awc N D 0-R:= by
   apply hunit.symm.dvd_of_dvd_mul_left
   simpa only [add_sub_add_right_eq_sub,← mul_sub] using dvd_sub hgen hc
 have hdeg: (awc N D 0).natDegree<H.natDegree := by
   exact ((natDegree_C_mul_le _ _).trans natDegree_map_le).trans_lt
     (by simpa only [cps] using hs.small)
 apply sub_eq_zero.mp
 by_contra hz
 have hl:=natDegree_le_of_dvd hsub hz
 rw [jH,hm.natDegree_map] at hl
 exact (not_le_of_gt ((natDegree_sub_le _ _).trans_lt (max_lt hdeg hR))) hl
theorem deform {H q A B:L[X]} {R:kS[X]} {n r :ℕ}
    (V:Submodule L jK) [zAa L V]
    (hm:H.Monic) (hp:0<H.natDegree) (hd:H.natDegree<K1.p)
    (hA:IsCoprime A H) (hq:IsCoprime q H)
    (hR:R.natDegree<H.natDegree)
    (hc:jH H∣bu4 1 A B*R+bu5 q)
    (hbound : ∀ (H' : L[X]) (S:kS[X]),H'.Monic→H'.Separable →
      H'.natDegree=H.natDegree→ IsCoprime A H' → IsCoprime q H' →
      (jH H' ∣ bu4 1 A B*S+bu5 q) →
      TT V (testSpace H' S (jH H') n)≤ r) :
    TT V (testSpace H R (jH H) n)≤ r := by
  classical
  obtain ⟨N,D,hres⟩:=cxQ.proof H 1 q A B hm hp
  let:Module.Free L ↥V:=Module.Free.of_divisionRing (K:=L) (V := ↥V)
  let basis :=Module.finBasis L V
  let F:= fun j=>(basis j:jK)
  obtain ⟨k,M,hM⟩:=cxR.proof H hm hp N D n (zsE L V) F
  have hmatch (ε:L) (hD:Wv ε D ≠0) :
      TT V (testSpace (Q8 H ε) (awc N D ε)
        (jH (Q8 H ε)) n)=(M.map (evalRingHom ε)).rank := by
    apply dL1 _ _ basis
    intro v
    have hv : (basis.equivFun.symm v :jK) = ∑ j,v j•F j:= by
      rw [basis.equivFun_symm_apply]
      simp [F]
    rw [mem_testSpace,hv]
    exact hM ε hD v
  have hz :=hres 0 isCoprime_one_left (by simpa using hA)
  have hD {ε:L} (h: (Wv ε D).eval 0≠0) :Wv ε D ≠0 :=
    fun he=>h (by rw [he,eval_zero])
  have hrz :=hmatch 0 (hD hz.at_zero)
  rw [cpt,fW0 hm hz hR hc] at hrz
  rw [hrz]
  let bad:=b3L H A∪b3L H q∪b3L H H.derivative
  apply fS2 M bad r
  intro ε hε
  change ε∉_∪_∪_ at hε
  simp only [Finset.mem_union,not_or] at hε
  have nonzero {f :L[X]} (hf :IsCoprime f H) :f≠0:= by
    rintro rfl
    exact not_isUnit_of_natDegree_pos _ hp (isCoprime_zero_left.mp hf)
  have hA' := bDq (nonzero hA) hε.1.1
  have hq' := bDq (nonzero hq) hε.1.2
  have hsep: (Q8 H ε).Separable := by
    rw [Polynomial.separable_def,show (Q8 H ε).derivative=H.derivative by
      simp [Q8]]
    exact (bDq (derivative_ne hm hp hd) hε.2).symm
  have he :=hres ε isCoprime_one_left hA'
  rw [← hmatch ε (hD he.at_zero)]
  exact hbound _ _ (gqo hm hp ε) hsep (cps _ _)
    hA' hq' he.generic_congruence
end
end qje58fc
end
section
set_option autoImplicit true
namespace qje58fc
noncomputable section
open Polynomial
open scoped Polynomial BigOperators
open cu (L)
open jA (jK kS mA jH)
open NR (O8)
open aFN (canonical aTo GV)
open aFO (bu4 bu5)
open q7IA62d (Lq)
open private sW bbH dsy aVo emi cM8 from ProximityPrize.SubmissionLower.S
set_option backward.isDefEq.respectTransparency false
private theorem restore_canonical {H :L[X]} {R:kS[X]}
    (α:L) (z :kS) (u v :kS[X])
    (hH :jH H=O8 α*u) (hR:R=C z+O8 α*v)
    (F:jK) :
    restoreMap H R F =
      sW (aVo u) (aVo v) (canonical (O8 α) (GV z F)) := by
  let f :jK →+* Lq :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (zhd (algebraMap L kS)))
      (fun i:mA=>i.elim
        (znf (C (algebraMap L[X] kS z7y)))
        (fun i:Fin 3 =>
          znf (hasseDeriv i.val R) +
            ∑ j:Fin 3,if j.val≤ i.val then
              znf (hasseDeriv (i.val - j.val) (jH H))*MvPolynomial.X j else 0))
  let g:=(sW (aVo u) (aVo v)).comp
    ((canonical (O8 α)).comp (GV z))
  have h:f=g:= by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f,g,sW,canonical,GV]
    · intro i
      cases i with
      | none=>simp [f,g,sW,canonical,GV]
      | some i =>
        fin_cases i <;>
          simp [f,g,sW,bbH,canonical,aTo,GV,aVo,
            Fin.sum_univ_three,hH,hR,O8,hasseDeriv_zero,hasseDeriv_C,
            emi] <;> ring
  exact DFunLike.congr_fun h F
private theorem center_of_congruence {H q A B:L[X]} {R:kS[X]}
  {α:L} (hr :H.IsRoot α) (hA:A.eval α≠0)
  (hc:jH H∣bu4 1 A B*R+bu5 q) :
  R.eval (algebraMap L kS α)=seedValue (-(q.eval α)) (A.eval α) (B.eval α) := by
 let den:=C (A.eval α)+Polynomial.X*C (B.eval α)
 have hden:den≠0:= by
  intro hz
  have he :=congrArg (evalRingHom (0:L)) hz
  apply hA
  simpa [den] using he
 have hd:algebraMap L[X] kS den≠0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective L[X] kS)).mpr hden
 unfold seedValue
 apply (eq_div_iff hd).mpr
 have he :=Polynomial.eval_dvd (x :=algebraMap L kS α) hc
 simp only [bu4,bu5,jH,Polynomial.map_one,one_mul,
  Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map_apply,
  show H.eval α=0 from hr,map_zero,zero_dvd_iff] at he
 have hC (a :L) :algebraMap L[X] kS (C a)=algebraMap L kS a := by
  rw [← Polynomial.algebraMap_eq,← IsScalarTower.algebraMap_apply]
 simp only [den,map_mul,map_add,hC,map_neg]
 linear_combination he
theorem normalize {H q A B:L[X]} {R:kS[X]} {n:ℕ} {α:L}
    (hr :H.IsRoot α) (hs :H.derivative.eval α≠0) (hA:IsCoprime A H)
    (hc:jH H∣bu4 1 A B*R+bu5 q) :
    testSpace H R (O8 α) n =
      testSpace (z7y-C α)
        (C (seedValue (-(q.eval α)) (A.eval α) (B.eval α))) (O8 α) n:= by
  let z :=seedValue (-(q.eval α)) (A.eval α) (B.eval α)
  let u:=(H /ₘ (z7y-C α)).map (algebraMap L kS)
  have hH :jH H=O8 α*u:= by
    have h:=congrArg (zhd (algebraMap L kS))
      (mul_divByMonic_eq_iff_isRoot.mpr hr).symm
    simpa [jH,O8,u] using h
  have hcop:IsCoprime (O8 α) u:= by
    have h:=isCoprime_of_is_root_of_eval_derivative_ne_zero H α hs
    simpa [O8,u] using h.map (zhd (algebraMap L kS))
  have hz :=center_of_congruence hr (cM8 hA hr) hc
  obtain ⟨v,hv⟩:O8 α∣R - C z :=
    dvd_iff_isRoot.mpr (by simp [IsRoot,hz,z])
  have hR:R=C z+O8 α*v := by linear_combination hv
  have hlin:jH (z7y-C α)=O8 α*1 := by simp [jH,O8]
  ext F
  change F∈testSpace H R (O8 α) n ↔
    F∈testSpace (z7y-C α) (C z) (O8 α) n
  rw [mem_testSpace,mem_testSpace,
    restore_canonical α z u v hH hR,restore_canonical α z 1 0 hlin (by simp)]
  exact (dsy _ n _ _ (by simpa [aVo,hasseDeriv_zero] using hcop) _).trans
    (dsy _ n _ _ (by
      change IsCoprime (O8 α) (hasseDeriv 0 1)
      rw [hasseDeriv_zero]
      exact isCoprime_one_right) _).symm
theorem coprime_at_root {A H :L[X]} {α:L} (hA:IsCoprime A H) (hr :H.IsRoot α) :
 A.eval α≠0:=cM8 hA hr
end
end qje58fc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace qAzyIze
noncomputable section
open Polynomial Finset q7IA62d
open cu (L FX)
open jA (ko iP bC)
open DP (jF zG)

open private en2 from ProximityPrize.SubmissionLower.Z
theorem column_caps {h t W P} (hP:P∈Aw h t W) {a :Exp} (ha :a∈P.support) :
  capColumns t a := by
 obtain ⟨hB,hJ,hC,hU,_⟩:=mem_ambient.mp hP
 exact ⟨(z6P _ ha).trans hB,
  (z6P _ ha).trans hJ,
  (zKk _ ha).trans hC,
  (zKk _ ha).trans hU⟩
private instance finite_ambient (h) (t:P5_7_2.TopRow) (W) :zAa L (Aw h t W) := by
  classical
  let E :=jA.mA→Fin (max t.shape.B t.shape.U + 1)
  let T:=W+clearance h t
  let f :Aw h t W →ₗ[L] ((E×Fin (T+1))→L) :=
    z9H fun x=>(coord (Finsupp.equivFunOnFinite.symm fun i=>(x.1 i).val) x.2.val).comp
      (Aw h t W).subtype
  apply zfv f
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨P,hP⟩ hz
  apply Subtype.ext
  by_contra hn
  obtain ⟨a,ha⟩:=Finset.nonempty_iff_ne_empty.mpr
    (fun he=>hn (MvPolynomial.support_eq_empty.mp he))
  obtain ⟨hB,_,_,hU⟩:=column_caps hP ha
  rw [jet_total] at hB
  have haE (i:jA.mA) :a i< max t.shape.B t.shape.U + 1 := by
    cases i with
    | none=>exact Nat.lt_succ_of_le (hU.trans (le_max_right _ _))
    | some i =>
      have hb:=le_max_left t.shape.B t.shape.U
      fin_cases i
      · change a (some 0)<_
        omega
      · change a (some 1)<_
        omega
      · change a (some 2)<_
        omega
  have hh:=(mem_ambient.mp hP).2.2.2.2 a ha
  have hdeg: (P.coeff a).natDegree<T+1 := by
    change _+kO h a≤T at hh
    omega
  let i:E×Fin (T+1) :=⟨fun j=>⟨a j,haE j⟩,⟨_,hdeg⟩⟩
  have hz' := congrFun hz i
  change (P.coeff (Finsupp.equivFunOnFinite.symm (fun j=>a j))).coeff
    (P.coeff a).natDegree=0 at hz'
  have he :Finsupp.equivFunOnFinite.symm (fun j=>a j)=a :=
    Finsupp.equivFunOnFinite.symm_apply_apply a
  rw [he,coeff_natDegree] at hz'
  exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp ha)) hz'
private instance finite_source {h} {D:jF h} (Crt:zG D) word t W :
   zAa L (source Crt word t W) := by
 let:zAa L (Aw h t W) :=finite_ambient h t W
 exact zfv (Submodule.inclusion inf_le_left)
   (Submodule.inclusion_injective
     (inf_le_left:source Crt word t W≤Aw h t W))
private def bd (h:ℕ) (t:P5_7_2.TopRow) (W:ℕ) (a :Exp) :=
 W+clearance h t - kO h a
private def boundary {h} {D:jF h} (Crt:zG D) word t W :
  source Crt word t W →ₗ[L] (Exp→L) :=
 z9H fun a=>(coord a (bd h t W a)).comp (source Crt word t W).subtype
private theorem bVx {h} {D:jF h} {Crt:zG D} {word t W}
  (P: (boundary Crt word t W).ker) {a :Exp} (ha :a∈P.val.val.support) :
  (P.val.val.coeff a).natDegree+kO h a<W+clearance h t:= by
 have hcut:=(mem_ambient.mp P.val.property.1).2.2.2.2 a ha
 change _+kO h a≤_ at hcut
 by_contra! hn
 have he : (P.val.val.coeff a).natDegree=bd h t W a := by unfold bd; omega
 have hz :=congrFun (LinearMap.mem_ker.mp P.property) a
 change (P.val.val.coeff a).coeff (bd h t W a)=0 at hz
 rw [← he,coeff_natDegree] at hz
 exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp ha)) hz
private theorem boundary_rank {h} {D:jF h} (Crt:zG D) word t W :
   zsE L (boundary Crt word t W).range ≤
     zsE iP (genericSpan (source Crt word t W)) := by
 classical
 let V:=source Crt word t W
 let F:=boundary Crt word t W
 let S:=genericSpan V
 let:zAa iP S:= by
   let A:=V.map acZ.Bu
   have hA:zAa L A:=inferInstance
   change zAa iP (Submodule.span iP (A:Set ko))
   exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp hA).span (A:=iP))
 let b:=Module.finBasis L F.range
 have hex (k :Fin (zsE L F.range)) : ∃ P:V,F P=(b k :Exp→L) :=(b k).property
 choose P hP using hex
 have hli:z14 L (fun k a=>((P k).val.coeff a).coeff (bd h t W a)) := by
   change z14 L (F ∘ P)
   rw [show F ∘ P=fun k=>((b k :F.range) :Exp→L) from funext hP]
   exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
 have hdeg (k) (a :Exp) : ((P k).val.coeff a).natDegree≤bd h t W a := by
   by_cases ha :a∈(P k).val.support
   · have hw:=(mem_ambient.mp (P k).property.1).2.2.2.2 a ha
     change _+kO h a≤_ at hw
     unfold bd
     omega
   · simp [MvPolynomial.notMem_support_iff.mp ha]
 let v (k :Fin (zsE L F.range)) :S :=
   ⟨bC (P k).val,Submodule.subset_span ⟨_,(P k).property,rfl⟩⟩
 have hv :z14 iP v := by
   let l:S →ₗ[iP] (Exp→iP) :=
     z9H fun a=>(MvPolynomial.lcoeff iP a).comp S.subtype
   apply LinearIndependent.of_comp l
   have he :l ∘ v=fun k a=>algebraMap L[X] FX ((P k).val.coeff a) := by
     funext k a
     exact MvPolynomial.coeff_map jA.qV (P k).val a
   rw [he]
   exact en2 _ _ hdeg hli
 simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
private theorem rank_zero {h} {D:jF h} (Crt:zG D) word t
   (Ly : ∀ P∈source Crt word t 0,
     (∀ a∈P.support,(P.coeff a).natDegree+kO h a<clearance h t)→P=0) :
   zsE L (source Crt word t 0) ≤
     zsE iP (genericSpan (source Crt word t 0)) := by
 let F:=boundary Crt word t 0
 have hk :F.ker = ⊥ := LinearMap.ker_eq_bot'.mpr fun P hp =>
   Subtype.ext (Ly P.val P.property fun a ha=> by
     simpa only [Nat.zero_add] using bVx (⟨P,LinearMap.mem_ker.mpr hp⟩:F.ker) ha)
 have hr :=z7i
   (K:=L) (V:=source Crt word t 0) (V₂:=Exp→L) F
 rw [hk,finrank_bot,add_zero] at hr
 exact hr.ge.trans (boundary_rank Crt word t 0)
private theorem mem_previous {h} {D:jF h} {Crt:zG D} {word t W}
  (P: (boundary Crt word t (W+1)).ker) :P.val.val∈source Crt word t W:= by
 obtain ⟨hB,hJ,hC,hU,_⟩:=mem_ambient.mp P.val.property.1
 refine ⟨mem_ambient.mpr ⟨hB,hJ,hC,hU,?_⟩,P.val.property.2⟩
 intro a ha
 have hl:=bVx P ha
 rw [Nat.add_right_comm W 1 (clearance h t)] at hl
 exact Nat.le_of_lt_succ hl
private theorem ker_step {h} {D:jF h} (Crt:zG D) word t (W:ℕ) :
   zsE L (boundary Crt word t (W+1)).ker ≤
     zsE L (source Crt word t W) := by
 let F:=boundary Crt word t (W+1)
 have hmp:F.ker.map (source Crt word t (W+1)).subtype≤ source Crt word t W:= by
   rintro _ ⟨P,hP,rfl⟩
   exact mem_previous (⟨P,hP⟩:F.ker)
 exact (Submodule.finrank_map_subtype_eq _ _).ge.trans (Submodule.finrank_mono hmp)
private theorem cev {h} {D:jF h} (Crt:zG D) word t (W:ℕ) :
    zsE L (source Crt word t (W+1)) ≤
      zsE L (source Crt word t W) +
        zsE iP (genericSpan (source Crt word t (W+1))) := by
  let F:=boundary Crt word t (W+1)
  have hr :=z7i
    (K:=L) (V:=source Crt word t (W+1)) (V₂:=Exp→L) F
  exact hr.ge.trans ((Nat.add_comm _ _).le.trans
    (Nat.add_le_add (ker_step Crt word t W) (boundary_rank Crt word t (W+1))))
private theorem telescope_nat (a b:ℕ→ℕ) (h0:a 0≤b 0)
   (hs : ∀ W,a (W+1)≤a W+b (W+1)) (W:ℕ) :
   a W ≤ ∑ w∈range (W+1),b w:= by
 induction W with
 | zero=>simpa only [Nat.zero_add,Finset.sum_range_one] using h0
 | succ W ih =>
   rw [Finset.sum_range_succ]
   exact (hs W).trans (Nat.add_le_add_right ih _)
theorem telescope {h} {D:jF h} (Crt:zG D) word t (W:ℕ)
  (Ly : ∀ P∈source Crt word t 0,
    (∀ a∈P.support,(P.coeff a).natDegree+kO h a<clearance h t)→P=0) :
  zsE L (source Crt word t W) ≤
    ∑ w∈range (W+1),zsE iP (genericSpan (source Crt word t w)) :=
 telescope_nat (fun w=>zsE L (source Crt word t w))
  (fun w=>zsE iP (genericSpan (source Crt word t w)))
  (rank_zero Crt word t Ly) (cev Crt word t) W
end
end qAzyIze
end
