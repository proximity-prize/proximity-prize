import ProximityPrize.SubmissionLower.AY
import ProximityPrize.SubmissionLower.CU
set_option Elab.async false
open _root_ renaming Finsupp.single → zhf, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.natDegree_C_mul_X_pow_le → zMG, Polynomial.natDegree_add_le_of_degree_le → zUG, RingHom.ker → zdq, RingHom.ker_eq_comap_bot → zPx
set_option autoImplicit true
section
namespace bAo
noncomputable section
open aR wH K1_13_7_6 MvPolynomial
open scoped Pointwise
private theorem biS (b j:ℕ) :0∈cap b j:= by
 simp [cap]
private abbrev capMap (b j:ℕ) :=monomialMap cH (cap b (2*j))
theorem aye {b j:ℕ} (hb:1≤b) (hj:1≤j) :
  Function.Surjective (capMap b j) := by
 apply monomialMap_surjective
 intro i
 change (zhf i 1).degree≤b ∧
  zhf i 1 1+2*zhf i 1 2≤2*j
 fin_cases i <;> norm_num [Finsupp.degree_single,Finsupp.single_apply] <;> omega
private theorem dEP (b j b' j' : ℕ) :
  cap b j+cap b' j' ⊆ cap (b+b') (j+j') := by
 rintro _ ⟨e,he,e',he',rfl⟩
 change e.degree≤b∧e 1+2*e 2≤j at he
 change e'.degree≤b' ∧ e' 1+2*e' 2≤j' at he'
 change (e+e').degree≤b+b' ∧
  (e+e') 1+2*(e+e') 2≤j+j'
 simp only [map_add,Finsupp.add_apply]
 omega
private theorem eFy (b j n:ℕ) :n•cap b j⊆cap (b*n) (j*n) := by
 induction n with
 | zero =>
    rw [zero_smul,Set.zero_subset]
    exact biS _ _
 | succ n ih =>
    rw [succ_nsmul,Nat.mul_succ,Nat.mul_succ]
    exact (Set.add_subset_add ih subset_rfl).trans (dEP _ _ _ _)
private theorem b6d (e :Fin 3 →₀ ℕ) :
  (e.sum fun i a=>i.val*a)=e 1+2*e 2 := by
 rw [Finsupp.sum_fintype _ _ (fun _=> by simp),Fin.sum_univ_three]
 simp
private theorem efC {b j:ℕ} (P:af 3) (hP:Gh P b (2*j)) :
  fW P∈restrictSupport cH (cap b (2*j)) := by
 intro e he
 have he' : e∈P.support :=support_map_subset _ _ he
 refine ⟨(le_totalDegree he').trans hP.1,?_⟩
 rw [← b6d]
 exact (Finset.le_sup (f := fun m:Fin 3 →₀ ℕ=>m.sum fun i a=>i.val*a) he').trans hP.2
theorem bmH {b j:ℕ} (P:af 3) (hP:Gh P b (2*j)) :
   ∃ L:MvPolynomial (cap b (2*j)) cH,
     (capMap b j) L=fW P∧L.totalDegree≤1 := by
 let h:=efC P hP
 exact ⟨monomialLift (fW P) h,monomialMap_monomialLift (fW P) h,
   totalDegree_monomialLift_le_one (fW P) h⟩
private theorem dH2 (b j n:ℕ) :
    affineHilbertFunction (zdq (capMap b j)) n ≤
      (cap (b*n) ((2*j)*n)).ncard:= by
  let S:=cap (b*n) ((2*j)*n)
  let M:=restrictSupport cH S
  let:Module.Finite cH M:=restrictSupport_finite (Set.toFinite S)
  have hmap (L:MvPolynomial (cap b (2*j)) cH) (hL:L.totalDegree≤n) :
      (capMap b j) L∈M :=
    restrictSupport_mono cH (eFy _ _ n)
      (monomialMap_mem_restrictSupport_nsmul (biS _ _) hL)
  calc
    affineHilbertFunction (zdq (capMap b j)) n ≤
        Module.finrank cH (M.map (Ideal.Quotient.mkₐ cH ⊥).toLinearMap) := by
      rw [zPx]
      exact affineHilbertFunction_comap_le_finrank_map (capMap b j) ⊥ M hmap
    _≤Module.finrank cH M:=Submodule.finrank_map_le _ _
    _=S.ncard:= by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport cH S),Nat.card_coe_set_eq]
theorem bWj {b j:ℕ} (hj:1≤j) (hb:2*j≤b) :
   aGW (capMap b j) zeroPrime≤6*(j:ℚ)^2*(b - j:ℚ) := by
 let a :ℚ:=j
 let c:ℚ:=b - j
 let H :zM1 ℚ:=z1z (a^2*c)*z7y ^3 +
   z1z (a^2+2*a*c)*z7y ^2 +
   z1z (2*a+c)*z7y ^1+Polynomial.C 1
 have hdim: (affineHilbertPolynomial (zdq (capMap b j))).natDegree=3:= by
   rw [natDegree_affineHilbertPolynomial_ker_of_surjective (capMap b j) (aye (by omega) hj),
     Nat.card_eq_fintype_card,Fintype.card_fin]
 have hH :H.natDegree≤3:= by
   dsimp only [H]
   apply zUG _ (by simp)
   apply zUG _
     ((zMG _ _).trans (by decide))
   apply zUG (zMG _ _)
   exact (zMG _ _).trans (by decide)
 have hB : ∀ n:ℕ,2*(j*n)≤b*n:= fun n=> by
   rw [← Nat.mul_assoc]
   exact Nat.mul_le_mul_right n hb
 have hfit : ∀ n:ℕ,(affineHilbertFunction (zdq (capMap b j)) n:ℚ)≤H.eval (n:ℚ) := by
   intro n
   have h:=dH2 b j n
   rw [Nat.mul_assoc,dE8 _ _ (hB n)] at h
   refine (Nat.cast_le.mpr h).trans_eq ?_
   have hsub:j*n≤b*n+1 := by have :=hB n; omega
   push_cast [Nat.cast_sub hsub]
   simp only [H,a,c,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
     Polynomial.eval_C,Polynomial.eval_X]
   ring
 change affineDegree ((⊥ : Ideal Lower).comap (capMap b j))≤_
 rw [← zPx]
 refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim hH
   (Filter.Eventually.of_forall hfit)).trans_eq ?_
 have hC:H.coeff 3=a^2*c:= by
   simp only [H,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,map_one,
     Polynomial.coeff_one]
   norm_num
 rw [hC]
 change (6:ℚ)*((j:ℚ)^2*((b:ℚ)-(j:ℚ)))= _
 ring
end
end bAo
end
section
namespace dnT
noncomputable section
open aR dN wH lB agP
open Rl (He)
open Ex (C6)
open MvPolynomial UniqueFactorizationMonoid
open private b4J cXz from ProximityPrize.SubmissionLower.L
private theorem c7I {b j:ℕ} (D:af 3) (hD:D ≠0) (hcap:Gh D b j) :
    ∃ q:af 3,q≠0∧q∣D ∧Gh q b j∧Squarefree q ∧
      (∀ S:zM1 ao,cK D S=0→cK q S=0) := by
  let:StrongNormalizationMonoid (af 3) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let q:=radical D
  have hd:q∣D:=radical_dvd_self (a :=D)
  have hq:q≠0:= fun hz=>hD (zero_dvd_iff.mp (hz ▸ hd))
  refine ⟨q,hq,hd,?_,squarefree_radical,?_⟩
  · obtain ⟨R,hR⟩:=hd
    have hRn:R≠0:= fun hz=>hD (by simp [hR,hz])
    refine ⟨?_,?_⟩
    · have h:=hcap.1
      rw [hR,totalDegree_mul_of_isDomain hq hRn] at h
      omega
    · have h:=hcap.2
      rw [hR,C6,weightedTotalDegree_mul _ _ _ hq hRn,← C6,
        ← C6] at h
      omega
  · obtain ⟨m,hm⟩:=exists_dvd_radical_self_pow hD
    intro S hS
    let ev :=MvPolynomial.eval (jet S:Fin 3→zM1 ao)
    have hh:=map_dvd ev hm
    rw [map_pow,show ev D =0 from hS] at hh
    exact eq_zero_of_pow_eq_zero (zero_dvd_iff.mp hh)
private theorem c5N {f :af 4} (hf :Irreducible f) (ht:0<(shape f).t) {q:af 3} (hq:q≠0) :
  IsRelPrime (bC f) (bC (He q)) := by
 apply (isRelPrime_iff_no_prime_factors (fun hz=>hf.ne_zero
  (b4J 4 (by simpa [bC] using hz)))).mpr
 intro r hrf hrq hr
 obtain ⟨a,ha,he⟩:=bYh hr hf.ne_zero hrf
 have had {x :af 4} (h:r∣bC x) :a∣x := by
  apply Ideal.mem_span_singleton.mp
  rw [← he]
  exact Ideal.mem_span_singleton.mpr h
 have haf :a∣f :=had hrf
 have hfa :f∣a :=(ha.irreducible.associated_of_dvd hf haf).dvd'
 obtain ⟨R,hR⟩:=hfa.trans (had hrq)
 have hRn:R≠0:= fun hz=>cXz hq (by simp [hR,hz])
 have hdeg:=bZ5 q
 rw [hR,← weightedTotalDegree_piSingle,weightedTotalDegree_mul _ _ _ hf.ne_zero hRn,
  weightedTotalDegree_piSingle,weightedTotalDegree_piSingle] at hdeg
 change 0<f.degreeOf 3 at ht
 omega
end
end dnT
end
