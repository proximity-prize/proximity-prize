import ProximityPrize.SubmissionLower.ZkT0QFc
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 900000
namespace qowZxPd
noncomputable section
open aR (af ao)
open oR (AR separant Ev)
open we (eT cH fW Yk GD JC Of D7)
open aeC
open bjy (bOL bhP)
open aFQ
open P6_6 (gZ bf tB M8)
open P6_6_5 (Fb)
open qSCPCwb (Dm BW Lx aGt azC)
open Polynomial
open private cSH bLG dgI from ProximityPrize.SubmissionLower.BG
open private cTL from ProximityPrize.SubmissionLower.A2
open private b9V from ProximityPrize.SubmissionLower.CT
open private cTd cVh from ProximityPrize.SubmissionLower.C
open private cqu dfd from ProximityPrize.SubmissionLower.C
open private bLf from ProximityPrize.SubmissionLower.ZkT0QFc
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem cpE (f :af 3) (P:Ideal (eT 3))
    [P.IsPrime] (h:Lx f P=1) (x :af 3) (hx :fW x∈P) :
    ∃ s :af 3,fW s∉P∧s*x∈Ideal.span {f,Dm f} := by
  let q:=P.comap (algebraMap (af 3) (eT 3))
  have :q.IsPrime :=Ideal.comap_isPrime _ _
  have :P.LiesOver q:=⟨rfl⟩
  let A:=Localization.AtPrime q
  let B:=Localization.AtPrime P
  let _:Algebra A B:=Localization.AtPrime.algebraOfLiesOver q P
  have :Module.Flat (af 3) (eT 3) :=cSH
  have :IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P (algebraMap (af 3) (eT 3)) rfl)
    infer_instance
  have :Module.FaithfullyFlat A B:=Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J:Ideal (af 3) :=Ideal.span {f,Dm f}
  have hJ:J.map (algebraMap (af 3) (eT 3))=BW f := by
    simp only [J,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,bLG,
      BW]
  have hJB: (J.map (algebraMap (af 3) A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B:= by
    rw [Ideal.map_map,← IsScalarTower.algebraMap_eq (af 3) A B,
      IsScalarTower.algebraMap_eq (af 3) (eT 3) B,← Ideal.map_map,hJ]
    classical
    unfold Lx at h
    rwa [dite_eq_left ‹P.IsPrime›,Module.length_eq_one_iff,isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def,IsLocalRing.isMaximal_iff] at h
  have hxB:algebraMap A B (algebraMap (af 3) A x)∈IsLocalRing.maximalIdeal B:= by
    rw [← IsScalarTower.algebraMap_apply (af 3) A B,
      IsScalarTower.algebraMap_apply (af 3) (eT 3) B,← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by rwa [bLG])
  rw [← hJB] at hxB
  have hxA:algebraMap (af 3) A x∈J.map (algebraMap (af 3) A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B:=B) (J.map (algebraMap (af 3) A))]
    exact hxB
  obtain ⟨s,hs,hsx⟩:=(IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
  refine ⟨s,?_,hsx⟩
  change algebraMap (af 3) (eT 3) s∉P at hs
  rwa [bLG] at hs
theorem gAt {f :af 3} {P:Ideal (eT 3)} (hp:P.IsPrime)
    (hle :BW f≤P) (hsep:fW (separant f)∉P)
    (hInv :aGt f P) :aqG f P:= by
  let:=hp
  have hf :fW f∈P:=hle (Ideal.subset_span (by simp))
  have hc:fW (Dm f)∈P:=hle (Ideal.subset_span (by simp))
  have hprod:=(b9V f P (bf-3) hc).mp hInv.2
  have hcut:=(hp.mem_or_mem hprod).resolve_left hsep
  have hgen : ∀ z∈(Ideal.span {f,Dm f} : Ideal (af 3)),
      fW (Ev f z)∈P:= by
    intro z hz
    obtain ⟨a,b,rfl⟩:=Ideal.mem_span_pair.mp hz
    rw [bOL,bhP,bhP,dgI,
      mul_zero,add_zero]
    simp only [fW,map_add,map_mul]
    exact P.add_mem (P.mul_mem_left _ hf)
      (P.add_mem (P.mul_mem_left _ hc) (P.mul_mem_left _ hcut))
  intro x hx
  obtain ⟨s,hs,hsx⟩:=cpE f P hInv.1 x hx
  have hd:=hgen (s*x) hsx
  rw [bhP] at hd
  simp only [fW,map_add,map_mul] at hd
  change fW (Ev f s)*fW x +
    fW s*fW (Ev f x)∈P at hd
  have hz :=P.sub_mem hd (P.mul_mem_left (fW (Ev f s)) hx)
  rw [add_sub_cancel_left] at hz
  exact (hp.mem_or_mem hz).resolve_left hs
theorem c1T {f :af 3} {P:Ideal (eT 3)} (h:aqG f P)
    (hc:fW (Dm f)∈P) {j:ℕ} (hj:bf-3≤j) :
    fW (AR f j)∈P:= by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le hj
  clear hj
  induction i with
  | zero=>exact hc
  | succ i hi =>
    exact (b9V f P _ hi).mpr (P.mul_mem_left _ (h _ hi))
private theorem dOy {f :af 3} {P:Ideal (eT 3)}
    (hf :Irreducible f) (hwhole : ¬ Fb f)
    (hmin:P∈(BW f).minimalPrimes) :
    (MvPolynomial.affineHilbertPolynomial P).natDegree=1 := by
  let F:=fW f
  let G:=fW (Dm f)
  have hF:F≠0:= by
    simpa only [F,fW,map_zero] using
      (MvPolynomial.map_injective _ Yk).ne hf.ne_zero
  have hregular :=cTL hf (show ¬ f∣Dm f from hwhole)
  change P∈(Ideal.span {F,G}).minimalPrimes at hmin
  rw [Ideal.span_insert] at hmin
  have hp:=hmin.isPrime
  obtain ⟨D,hD,hDP⟩:=Ideal.exists_minimalPrimes_le (le_sup_left.trans hmin.le)
  let:=hD.isPrime
  have hGD:G∉D:= by
    intro hG
    obtain ⟨a,ha,hGa⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hD hG
    exact ha (Ideal.mem_span_singleton.mpr (hregular a (Ideal.mem_span_singleton.mp hGa)))
  have hcut:P∈(D ⊔ Ideal.span {G}).minimalPrimes :=
    ⟨⟨hp,sup_le hDP (le_sup_right.trans hmin.le)⟩,fun J hJ hJP =>
      hmin.2 ⟨hJ.1,(sup_le_sup_right hD.le _).trans hJ.2⟩ hJP⟩
  have hsurface :=
    MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  rw [Nat.card_fin] at hsurface
  have hcurve :=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  omega
private theorem ctW {A:Type*} [CommRing A] (k :ao →+* A) (f :af 3)
    (U:A[X]) (hU:U.natDegree≤gZ) {D:ℕ} (hf :tB f D) :
    (jW k f U).natDegree≤D:= by
  classical
  rw [jW,MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm=>(natDegree_mul_le).trans ?_
  apply le_trans _ (hf m hm)
  apply Nat.add_le_add natDegree_map_le
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans
    (Nat.sub_le_sub_right hU _)) |>.trans_eq (Nat.mul_comm _ _)
theorem guE {f :af 3} {P:Ideal (eT 3)}
    (hf :tB f M8) (hc:BW f≤P)
    (h:aqG f P) {y :Fin 3→cH} (hy :y∈D7 f P) :
    (aac f (Bt y)).natDegree≤gZ ∧
      Of f (aac f (Bt y))=0:= by
  have hrow:fW f∈P:=hc (Ideal.subset_span (by simp))
  have hcut:fW (Dm f)∈P:=hc (Ideal.subset_span (by simp))
  have hold:we.BW f≤P:= by
    rw [we.BW,Ideal.span_insert]
    exact sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hrow)
      ((Ideal.span_singleton_le_iff_mem P).mpr (c1T h hcut (by change 133423≤133669; decide)))
  have hU: (aot f P).natDegree≤gZ:= by
    rw [aot,natDegree_taylor,natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hsmall:3≤j:= by
      change 133425<j at hj
      omega
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hsmall
    rw [Nat.add_comm 3 n,aMK,bCW]
    have hn:bf-3≤n:= by
      change 133425<3+n at hj
      change 133423≤n
      omega
    have hz :Ub f P (n+3)=0:= by
      rw [Ub,bm2 f P (c1T h hcut hn),mul_zero,zero_mul,zero_mul]
    split_ifs with hj'
    · exact hz
    · rfl
  refine ⟨by rw [← cqu hy]; exact natDegree_map_le.trans hU,?_⟩
  have hOne :delta h (1 :Chart f P)=0:= by
    simpa only [map_one] using bD2 h (1 :ao)
  have hShift:taylor (KM f P (MvPolynomial.C Polynomial.X)) (aot f P) =
      aMK f P:= by
    rw [aot,taylor_taylor,add_neg_cancel,taylor_zero]
  have hidentity :=cTd (delta h) hOne (aT8 h) (constants (KM f P))
    (bD2 h) _ (dVV h) f (aot f P) (aMK f P) hShift
    (dGI h hold) (cVh hold)
    ((ctW _ _ _ hU hf).trans_lt (by change 0x10fa678<0x7f000001; decide))
    (fun n hn hp=> by
      rw [← map_natCast (constants (KM f P))]
      exact (b9C hn hp).isUnit.map _)
  rw [← dfd hy,hidentity,Polynomial.map_zero]
private theorem gqV (f :af 3) (P:Ideal (eT 3))
    (h : ∀ y∈D7 f P,(aac f (Bt y)).natDegree≤gZ)
    (a :GD) (ha :a∈MvPolynomial.zeroLocus cH (aHk f P)) :
    (JC a).natDegree≤gZ:= by
  have tail (j:Fin aR.bf) (hj:gZ<j.val) :a j=0:= by
    have hjQ:MvPolynomial.X j∈aHk f P:= by
      rintro _ ⟨y,hy,rfl⟩
      rw [MvPolynomial.aeval_X]
      exact coeff_eq_zero_of_natDegree_lt ((h y hy).trans_lt hj)
    simpa only [MvPolynomial.aeval_X] using ha _ hjQ
  unfold JC
  apply natDegree_sum_le_of_forall_le
  intro j _
  by_cases hj:gZ<j.val
  · rw [tail j hj,monomial_zero_right,natDegree_zero]
    exact Nat.zero_le _
  · exact (natDegree_monomial_le _).trans (Nat.le_of_not_gt hj)
theorem proof :qSCPCwb.c2 := by
  intro v _ n f hf a ha hs
  rcases a with ⟨i,P⟩
  obtain ⟨hw,hm⟩:=azC.mp ha
  obtain ⟨hmin,hsep⟩:=Ideal.mem_retainedMinimalPrimes.mp hm
  have hp:=hmin.isPrime
  have hle :=hmin.le
  have hstable :=gAt hp hle hsep hs
  have hdim:=dOy (hf.irreducible i) hw hmin
  obtain ⟨hprime,hcurve⟩:=cxX.proof (f i) P hp hsep hdim
  have hTaylor := fun y hy=>guE (hf.weight i) hle hstable (y :=y) hy
  refine ⟨aHk (f i) P,⟨⟨hprime,hcurve,deO _ _ (fun y hy =>
    (hTaylor y hy).2),?_⟩,gqV _ _ (fun y hy=>(hTaylor y hy).1)⟩,?_⟩
  · obtain ⟨y,hy⟩:=c7O (f i) P hp hsep
    refine ⟨aWP (f i) y,cb0 _ _ hy,?_⟩
    intro hz
    apply hy.2
    rw [← cNc (f i),← bCY,
      hz,Polynomial.eval_zero]
  · intro S hS hy
    have hr :=bLf ha hy
    have hS' : S.natDegree≤133671 :=hS.trans (by change 133425≤133671; decide)
    rw [← c7y (f i) S hS' hr]
    exact cb0 _ _ hy
end
end qowZxPd
