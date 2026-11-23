import ProximityPrize.SubmissionLower.Zt2VnXa
import ProximityPrize.SubmissionLower.ZuoZ7sd
import ProximityPrize.SubmissionLower.ZaOaNGc
set_option Elab.async false
open _root_ renaming Fin.succ → z7H, Finset.sup_le_iff → zUp, Finsupp.mapDomain_apply_of_injective → zm3, Finsupp.optionElim_some → zX5, Finsupp.sum_fintype → z9d, Function.Injective → zq4, MvPolynomial → z3y, MvPolynomial.optionEquivRight → zyD, MvPolynomial.weightedTotalDegree_zero → z4a, Nat.zero_le → zD0, Polynomial.coeff_map → z0b
set_option maxHeartbeats 800000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qLKC7de
noncomputable section
open Polynomial MvPolynomial Finset
open P5 (K p twist)
open P5_7_1 (TopRow topLift atTop topConjugate)
open qaySLPd (orient topLabel)
open qwWTALb (X3 YN cut view_map up)
open qCQTZAc (degreeBound cheapHeight FixedData Singular)
open qkLbbMe (af keep)
open cu (L FX jz)
open private coefficient_zero_ne squarefree_equiv map_cut_ne from ProximityPrize.SubmissionLower.ZPMTD6c
open private flat deg deg_le_iff coeff_origin b0v gMe from ProximityPrize.SubmissionLower.Z7B8rOc
open private conjugate_at_zero cut_at_zero from ProximityPrize.SubmissionLower.Zt2VnXa
private theorem cut_ne {B:TopRow} (hB:FixedData B)
   (hd: (YN L[X] B).natDegree≤12) :cut B≠0:= by
 let f :=YN L[X] B
 let ι:X3 →+* z3y (Fin 3) FX:=MvPolynomial.map (algebraMap L[X] FX)
 have hi:zq4 ι :=
   MvPolynomial.map_injective _ (IsFractionRing.injective L[X] FX)
 have he :f.map ι=YN FX (topLift B) :=view_map (algebraMap L[X] FX) B
 change (if f.natDegree=0 then f.coeff 0
   else f.resultant f.derivative f.natDegree (f.natDegree - 1))≠0
 by_cases hz :f.natDegree=0
 · rw [ite_eq_left hz]
   exact coefficient_zero_ne f (fun h=>hB.ne ((YN L[X]).injective
     (h.trans (map_zero (YN L[X])).symm))) hz
 rw [ite_eq_right hz]
 let R:=z3y (Fin 3) FX
 let:CharP FX p:=charP_of_injective_ringHom jz.injective p
 let:CharP R p:=charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 3) FX) p
 have hs :Squarefree (f.map ι) :=
   he.symm ▸ squarefree_equiv (YN FX).toMulEquiv hB.squarefree
 have hp:12<p:= by decide
 have hsmall:f.natDegree<p:=hd.trans_lt hp
 let gR:IsGCDMonoid R:=⟨UniqueFactorizationMonoid.toGCDMonoid R⟩
 exact @map_cut_ne X3 R inferInstance inferInstance inferInstance gR inferInstance ι hi f hs hsmall
private theorem cvg {B:TopRow} (h:FixedData B) : (YN L[X] B).natDegree≤12 := by
 rw [show YN L[X] B=aeA.view (r :=3) B from rfl,aeA.gLc]
 exact MvPolynomial.degreeOf_le_iff.mpr fun m hm=>(h.support m hm).2.2.1
private theorem aM7 {B:TopRow} (hB:FixedData B) {x :ℕ} {w:Fin 3→ℕ} {b:ℕ}
   (h : ∀ j,deg x w ((YN L[X] B).coeff j)≤b) :deg x w (cut B)≤23*b:= by
 classical
 let f :=YN L[X] B
 let c:=f.natDegree
 let w' : Option (Fin 3)→ℕ:= fun i=>i.elim x w
 have hc:c≤12 :=cvg hB
 have hd (j:ℕ) :deg x w (f.derivative.coeff j)≤b:= by
   change (flat (f.derivative.coeff j)).weightedTotalDegree w' ≤ b
   rw [Polynomial.coeff_derivative,← Nat.cast_succ,map_mul flat,map_natCast flat,
     ← map_natCast (MvPolynomial.C:L →+* z3y (Option (Fin 3)) L)]
   exact (weightedTotalDegree_mul_le _ _ _).trans
     (by simpa only [weightedTotalDegree_C,Nat.add_zero] using h (j+1))
 change deg x w (if c=0 then f.coeff 0 else f.resultant f.derivative c (c-1))≤_
 by_cases h0:c=0
 · rw [ite_eq_left h0]
   exact (h 0).trans (Nat.le_mul_of_pos_left _ (by decide))
 rw [ite_eq_right h0]
 let φ:=flat.toRingHom
 change (φ (f.resultant f.derivative c (c-1))).weightedTotalDegree w' ≤ _
 rw [← resultant_map_map f f.derivative c (c-1) φ]
 refine le_trans (b0v w' _ ?_) (Nat.mul_le_mul_right _ (by omega :c+(c-1)≤23))
 intro i j
 refine Fin.addCases ?_ ?_ j
 · intro k
   simp only [sylvester,Matrix.of_apply,Fin.addCases_left]
   split
   · rw [z0b]
     exact hd _
   · rw [z4a]
     exact zD0 _
 · intro k
   simp only [sylvester,Matrix.of_apply,Fin.addCases_right]
   split
   · rw [z0b]
     exact h _
   · rw [z4a]
     exact zD0 _
private abbrev wJets :Fin 3→ℕ := ![0,1,1]
private abbrev wSeed :Fin 3→ℕ := ![1,0,0]
private abbrev wPhys :Fin 3→ℕ := ![0,degreeBound,degreeBound-1]
private theorem cF7 {B:TopRow} (hB:FixedData B) (j:ℕ) :
   let f :=(YN L[X] B).coeff j
   deg 0 wJets f≤87∧deg 0 wSeed f≤0∧deg 1 wPhys f≤ cheapHeight:= by
 refine ⟨(deg_le_iff _ _ _ _).mpr ?_,(deg_le_iff _ _ _ _).mpr ?_,
   (deg_le_iff _ _ _ _).mpr ?_⟩ <;>
   intro m hm <;>
   obtain ⟨e,he,hc,hl,_⟩:=coeff_origin B j m hm <;>
   have h0:=hl 0 <;> have h1 :=hl 1 <;> have h2 :=hl 2 <;>
   change e 0=m 0 at h0 <;> change e 1=m 1 at h1 <;> change e 2=m 2 at h2
 · simpa [gMe,wJets,← h1,← h2] using
     (Nat.le_add_right (e 1+e 2) (e 3)).trans (hB.support e he).1
 · simpa [gMe,wSeed,← h0] using (hB.support e he).2.2.2
 · have hw:=hB.weight e he
   rw [gMe]
   change 1*_+(0*m 0+degreeBound*m 1+(degreeBound-1)*m 2)≤_
   rw [← hc,← h1,← h2]
   simpa [add_assoc] using
     (Nat.le_add_right _ _).trans hw
private theorem cut_row {B:TopRow} (hB:FixedData B) :
    ∃ R:af,rename z7H R=cut B∧R≠0 ∧
      ∀ e∈R.support,e 0+e 1≤23*87 ∧
        (R.coeff e).natDegree+degreeBound*e 0+(degreeBound-1)*e 1≤23*cheapHeight:= by
  have hJ:=(deg_le_iff _ _ _ _).mp (aM7 hB fun j=>(cF7 hB j).1)
  have hS:=(deg_le_iff _ _ _ _).mp (aM7 hB fun j=>(cF7 hB j).2.1)
  have hW:=(deg_le_iff _ _ _ _).mp (aM7 hB fun j=>(cF7 hB j).2.2)
  have hz : (cut B).degreeOf 0=0:=Nat.eq_zero_of_le_zero
    (MvPolynomial.degreeOf_le_iff.mpr fun e he=> by
      simpa [gMe,wSeed] using hS e he)
  have hv : ((cut B).vars :Set (Fin 3))⊆Set.range Fin.succ:= by
    intro i hi
    fin_cases i
    · exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi hz).elim
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  have hinj:zq4 (z7H:Fin 2→Fin 3) :=Fin.succ_injective _
  obtain ⟨R,hr⟩:=exists_rename_eq_of_vars_subset_range (cut B) z7H hinj hv
  refine ⟨R,hr,fun he=>cut_ne hB (cvg hB) (hr ▸ (he ▸ map_zero _)),?_⟩
  intro e he
  have hc:=coeff_rename_mapDomain z7H hinj R e
  have hm:e.mapDomain z7H∈(cut B).support := by
    rw [← hr,MvPolynomial.mem_support_iff,hc]
    exact MvPolynomial.mem_support_iff.mp he
  have h1 :=zm3 hinj e (0:Fin 2)
  have h2 :=zm3 hinj e (1 :Fin 2)
  change (e.mapDomain z7H) 1=e 0 at h1
  change (e.mapDomain z7H) 2=e 1 at h2
  exact ⟨by simpa [gMe,wJets,h1,h2] using hJ _ hm,by
    simpa [gMe,wPhys,← hr,hc,h1,h2,add_assoc] using hW _ hm⟩
theorem FT (B:TopRow) (hB:FixedData B) :
    ∃ R:af,R≠0∧(∀ e∈R.support,e 0+e 1≤23*87 ∧
      (R.coeff e).natDegree+degreeBound*e 0+(degreeBound-1)*e 1≤23*cheapHeight) ∧
      ∀ (z :K) (S:K[X]),S.map twist=S→Singular B z S →
        atTop (rename keep R) 0 S=0:= by
  obtain ⟨R,hR,hne,hc⟩:=cut_row hB
  refine ⟨R,hne,hc,?_⟩
  intro z S hS hs
  obtain ⟨i,h0,h1⟩:=hs
  have h:atTop B z S=0∧atTop (MvPolynomial.pderiv 3 B) z S=0:= by
    fin_cases i
    · simpa [orient,topLabel] using And.intro h0 h1
    · refine ⟨conjugate_at_zero hS (by simpa [orient,topLabel] using h0),
        conjugate_at_zero hS ?_⟩
      simpa [orient,topLabel,topConjugate,MvPolynomial.pderiv_map] using h1
  have hr :rename keep R=up (cut B) := by
    rw [show keep=Fin.castSucc ∘ z7H from rfl,← rename_rename,hR]
    rfl
  have hz :atTop (rename keep R) z S=0:=hr.symm ▸ cut_at_zero h.1 h.2
  rw [atTop,eval₂_rename] at hz ⊢
  convert hz using 2
  funext j
  fin_cases j <;> rfl
end
end qLKC7de
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qLKC7de
noncomputable section
open Polynomial Finset PolynomialDifferential
open qkLbbMe (af flatten)
open qCQTZAc (degreeBound)
open cu (L)
open scoped Classical
local notation "D" => degreeBound
theorem flatten_caps {B:af} {d W:ℕ}
    (h : ∀ e∈B.support,e 0+e 1≤d ∧
      (B.coeff e).natDegree+D *e 0+(D - 1)*e 1≤W) :
    jetTotalDegree (flatten B)≤d∧differentialWeightedDegree D (flatten B)≤W:= by
  constructor
  · have hweight:jetDegreeWeight (d:=1)=(fun v=>v.elim 0 (fun _=>1)) := by
      funext v
      cases v <;> rfl
    rw [jetTotalDegree,hweight,← MvPolynomial.totalDegree_optionEquivRight]
    change (zyD L (Fin 2)
      ((zyD L (Fin 2)).symm B)).totalDegree≤d
    rw [AlgEquiv.apply_symm_apply,MvPolynomial.totalDegree,zUp]
    intro e he
    rw [z9d e (fun (_:Fin 2) (n:ℕ)=>n) (fun _=>rfl),Fin.sum_univ_two]
    exact (h e he).1
  · rw [differentialWeightedDegree,MvPolynomial.weightedTotalDegree,zUp]
    intro e he
    have hc: (B.coeff e.some).coeff (e none)=(flatten B).coeff e := by
      simpa only [flatten,ana.flatten,AlgEquiv.apply_symm_apply,zX5]
        using MvPolynomial.optionEquivRight_coeff_coeff (flatten B) e.some (e none)
    have hs :e none∈(B.coeff e.some).support := by
      rw [Polynomial.mem_support_iff,hc]
      exact MvPolynomial.mem_support_iff.mp he
    have hw: (e.some).weight (fun i:Fin 2=>D - i.val) =
        D *e.some 0+(D - 1)*e.some 1 := by
      rw [Finsupp.weight_apply,z9d _ _ (fun i=>zero_smul ℕ (D - i.val)),
        Fin.sum_univ_two]
      simp only [smul_eq_mul,Fin.val_zero,Nat.sub_zero,Fin.val_one]
      ac_rfl
    have hweight:differentialWeight (d:=1) D =
        (fun v=>v.elim 1 (fun i=>D - i.val)) := by
      funext v
      cases v <;> rfl
    rw [hweight]
    conv_lhs=>rw [← zX5 e]
    rw [Finsupp.weight_optionElim,one_mul,hw]
    exact (Nat.add_le_add_right (le_natDegree_of_mem_supp _ hs) _).trans
      (by simpa only [Nat.add_assoc] using
        (h e.some (MvPolynomial.mem_support_iff.mpr (Polynomial.support_nonempty.mp ⟨_,hs⟩))).2)
end
end qLKC7de
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qLKC7de
noncomputable section
open Polynomial Finset PolynomialDifferential
open P5 (p K twist)
open qkLbbMe (flatten solves)

open qCQTZAc (degreeBound cheapHeight)
open cu (L j9)
open scoped Classical
open private Good Good.singular Good.regular Good.eval_zero Good.initial_ne dX card_grid jet_mem_grid cast_ne_zero from ProximityPrize.SubmissionLower.ZuoZ7sd
local instance :CharP L p :=
 charP_of_injective_ringHom (algebraMap K L).injective p
local notation "D" => degreeBound
private abbrev Eqn:=DifferentialPolynomial L 1
private theorem eq_of_jet {Q S U a} (h:Good Q S a) (h' : Good Q U a)
   (hS:S.degree≤D) (hU:U.degree≤D)
   (hbin : ∀ k i:ℕ,0<k→k+i≤D→((k+i).choose i:L)≠0)
   (hjet:polynomialJet (d:=1) a S=polynomialJet a U) :S=U:= by
 induction h with
 | @regular Q S a i ha hs hn =>
     cases h' with
     | regular _ hu _ =>
         refine eq_of_polynomialJet_eq_of_isHighestActiveJet Q
           (isHighestActiveJet_of_highestActiveJet_eq_some ha) a hS hU
           (hs.trans hu.symm)
           (by simpa only [restrictJet_polynomialJet] using congrArg (restrictJet i) hjet)
           (fun k hk hkd=>IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
             (mul_ne_zero (hbin k i hk hkd) hn))
     | singular ha' _ hn' =>
         cases Option.some.inj (ha.symm.trans ha')
         exact (hn (hjet ▸ Good.eval_zero hn')).elim
 | @singular Q S a i ha _ next ih =>
     cases h' with
     | regular ha' _ hn' =>
         cases Option.some.inj (ha.symm.trans ha')
         exact (hn' (hjet ▸ Good.eval_zero next)).elim
     | singular ha' _ hn' =>
         cases Option.some.inj (ha.symm.trans ha')
         exact ih hn' hS hjet
private theorem good_off_roots (Q:Eqn) (S:L[X]) (hS:S.natDegree≤D)
    {W:ℕ} (hQ:Q≠0) (hc : ∀ i,JetDegreeCastsNeZero Q i)
    (hw:differentialWeightedDegree D Q≤W) (hs :differentialSpecialization Q S=0) :
    ∃ R:L[X],R≠0∧R.natDegree≤W ∧ ∀ a,R.eval a≠0→Good Q S a := by
  induction Q using (singularStep_wellFounded (F:=L) (d:=1)).induction with
  | _ Q ih =>
    cases ha :highestActiveJet Q with
    | none=>exact (hQ (eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none
        ha hs)).elim
    | some i =>
      by_cases hz :differentialSpecialization (separant Q i) S=0
      · have hstep:=singularStep_separant Q ha
        obtain ⟨hne,hcast⟩:=singularStep_preserves hc hstep
        have hw' := (differentialWeightedDegree_le_of_singularStep hstep).trans hw
        obtain ⟨R,hR,hdeg,hgood⟩:=ih _ hstep hne hcast hw' hz
        exact ⟨R,hR,hdeg,fun a ha' => Good.singular ha hs (hgood a ha')⟩
      · refine ⟨_,hz,(natDegree_differentialSpecialization_separant_le Q i S hS).trans hw,
          fun a hn=>Good.regular ha hs ?_⟩
        rwa [← eval_differentialSpecialization]
private theorem count {α:Type*} (Q:Eqn) (hQ:Q≠0) {d W:ℕ} (hW:W<p)
    (hw:differentialWeightedDegree D Q≤W) (hd:jetTotalDegree Q≤d)
    (centers :Finset L) (hcard:centers.card=p)
    (hgrid : ∀ a∈centers,∀ S:K[X],S.map twist=S →
      ∀ i:Fin 2,polynomialJet a (j9 S) i∈centers)
    (T:Finset α) (S:α→K[X]) (hinj:Set.InjOn S (T:Set α))
    (hS : ∀ γ∈T,(S γ).natDegree≤D ∧(S γ).map twist=S γ ∧
      differentialSpecialization Q (j9 (S γ))=0) :
    T.card*(p-W)≤p*p*d:= by
  have hcast (i:Fin 2) :JetDegreeCastsNeZero Q i:= by
    intro n hn hb
    have hdeg:jetDegree Q i≤differentialWeightedDegree D Q :=
      MvPolynomial.degreeOf_le_weightedTotalDegree _ _ (by fin_cases i <;> decide) _
    exact cast_ne_zero hn (hb.trans (hdeg.trans hw) |>.trans_lt hW)
  let F:=j9 ∘ S
  have hF (γ:α) (hγ:γ∈T) : (F γ).natDegree≤D :=
    Polynomial.natDegree_map_le.trans (hS γ hγ).1
  have hbin (k i:ℕ) (hk :0<k) (hki:k+i≤D) : ((k+i).choose i:L)≠0:= by
    intro hz
    have hsmall:D <p:= by decide
    have hi:i≤k+i:=Nat.le_add_left _ _
    have hdiv : (k+i).choose i∣(k+i).factorial:= by
      rw [← Nat.choose_mul_factorial_mul_factorial hi]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    exact (not_le_of_gt (hki.trans_lt hsmall)) ((Fact.out:p.Prime).dvd_factorial.mp
      (((CharP.cast_eq_zero_iff L p _).mp hz).trans hdiv))
  let r (γ:α) (a :L) :=Good Q (F γ) a
  have hex (γ:α) (hγ:γ∈T) :
      ∃ R:L[X],R≠0∧R.natDegree≤W ∧ ∀ a,R.eval a≠0→ r γ a := by
    exact good_off_roots Q (F γ) (hF γ hγ) hQ hcast hw (hS γ hγ).2.2
  choose! R hR hRdeg hgood using hex
  have hcount:T.card*(centers.card-W)≤ centers.card*(p*d) := by
    refine card_mul_le_card_mul r (fun γ hγ => ?_) (fun a ha => ?_)
    · let bad:=(R γ).roots.toFinset
      have hb:bad.card≤W :=
        (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hRdeg γ hγ))
      calc
        _≤ centers.card - bad.card:=Nat.sub_le_sub_left hb _
        _≤(centers \ bad).card:=le_card_sdiff _ _
        _≤_:=card_le_card fun a ha=> by
          obtain ⟨ha,hn⟩:=mem_sdiff.mp ha
          exact mem_filter.mpr ⟨ha,hgood γ hγ a (by
            rwa [Multiset.mem_toFinset,mem_roots (hR γ hγ),IsRoot.def] at hn)⟩
    · by_cases hzero :initialJetEquation a Q=0
      · rw [bipartiteBelow,filter_false_of_mem fun γ _ h=>Good.initial_ne h hzero,
          card_empty]
        exact zD0 _
      · let fiber :=T.bipartiteBelow r a
        let Ju:=(Fintype.piFinset fun _:Fin 2=>centers).filter
          fun j=>MvPolynomial.eval j (initialJetEquation a Q)=0
        let jet (γ:α) :Fin 2→L:=polynomialJet a (F γ)
        have hmem {γ:α} (h:γ∈fiber) :γ∈T∧r γ a :=
          (mem_bipartiteBelow r).mp h
        have hmaps :Set.MapsTo jet (fiber :Set α) (Ju:Set (Fin 2→L)) := by
          intro γ hγ
          obtain ⟨hγ,hc⟩:=hmem hγ
          change jet γ∈Ju
          refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr
            (hgrid a ha (S γ) (hS γ hγ).2.1),?_⟩
          rw [← MvPolynomial.coe_aeval_eq_eval]
          change MvPolynomial.aeval (jet γ) (initialJetEquation a Q)=0
          exact (aeval_initialJetEquation a Q (jet γ)).trans (Good.eval_zero hc)
        have hinj' : Set.InjOn jet (fiber :Set α) := by
          intro γ hγ η hη he
          obtain ⟨hγ,hg⟩:=hmem hγ
          obtain ⟨hη,hh⟩:=hmem hη
          have hs :=eq_of_jet hg hh (degree_le_of_natDegree_le (hF γ hγ))
            (degree_le_of_natDegree_le (hF η hη)) hbin he
          exact hinj hγ hη (Polynomial.map_injective _ (algebraMap K L).injective hs)
        refine (card_le_card_of_injOn jet hmaps hinj').trans ?_
        have hp:0<p:= by decide
        have h:=schwartz_zippel_counting (initialJetEquation a Q) hzero
          (fun _=>centers) d p ((totalDegree_initialJetEquation_le a Q).trans hd) hp
          (fun _=>hcard.ge)
        have hprod: (∏ _:Fin 2,centers.card)=p*p:= by
          rw [Fin.prod_univ_two,hcard]
        rw [hprod] at h
        apply Nat.le_of_mul_le_mul_right _ hp
        simpa only [Ju,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  rw [hcard] at hcount
  simpa only [Nat.mul_assoc] using hcount
theorem proof :qCQTZAc.c1 := by
 intro B hB T z S hinj hS
 obtain ⟨R,hR,hcaps,hsol⟩:=FT B hB
 obtain ⟨hd,hw⟩:=flatten_caps hcaps
 have hne :flatten R≠0:= fun h =>
  hR ((zyD L (Fin 2)).symm.injective (h.trans (map_zero _).symm))
 have hW:23*cheapHeight<p:= by decide
 change T.card≤p*p*(23*87)/(p - 23*cheapHeight)
 apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hW)).mpr
 apply count (flatten R) hne hW hw hd dX card_grid
  (fun _ ha U hu=>jet_mem_grid U hu ha) T S hinj
 intro γ hγ
 obtain ⟨hdeg,hf,hs⟩:=hS γ hγ
 exact ⟨hdeg,hf,solves R _ (hsol (z γ) _ hf hs)⟩
end
end qLKC7de
end
