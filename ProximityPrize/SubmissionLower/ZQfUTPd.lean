import ProximityPrize.SubmissionLower.ZocsBpe
set_option Elab.async false
open _root_ renaming Fin.addCases_left → zgb, Fin.addCases_right → z5m, IsFractionRing.injective → zxb, Nat.cast_succ → zg0, Nat.mul_add → zws, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Nat.succ_eq_add_one → zJf
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
namespace qrezXJe
noncomputable section
open Polynomial Finset
open scoped WithZero
open P5 (K p)
open cu (L)
open qFD8jve (aFA polarResultant)
open E7 (CurvePlace)
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private efc adG cTA efd aMX from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E]
theorem cast_ne_zero {n:ℕ} [CharP E p] (hn:0<n) (hp:n<p) : (n:E)≠0 :=
  fun h=>hp.not_ge (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff E p n).mp h))
theorem bD9 [CharP E p] {G:E[X]} (hn:0<G.natDegree)
    (hp:G.natDegree<p) :G.derivative.natDegree=G.natDegree-1 := by
  apply le_antisymm (natDegree_derivative_le _)
  apply le_natDegree_of_ne_zero
  have hi:G.natDegree-1+1=G.natDegree := by omega
  rw [coeff_derivative,← zg0,zJf,hi,← leadingCoeff]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hn))
    (cast_ne_zero hn hp)
private theorem fXo (F G:E[X][X]) (m n D B H :ℕ)
    (hF : ∀ i,F.coeff i≠0→(F.coeff i).natDegree+D*i≤B)
    (hG : ∀ i,G.coeff i≠0→(G.coeff i).natDegree+D*i≤H) :
    (F.resultant G m n).natDegree≤ m*H+n*B-D*(m*n) := by
  classical
  let M:=F.sylvester G m n
  let cap:Fin (m+n)→ℕ:=Fin.addCases (fun j=>H+D*j.val) (fun j=>B+D*j.val)
  have hentry (i j:Fin (m+n)) (hne :M i j≠0) : (M i j).natDegree+D*i.val≤ cap j:= by
    cases j using Fin.addCases with
    | left j =>
      simp only [M,sylvester,Matrix.of_apply,zgb] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh:=hG _ hne
        have he :D*(i.val-j.val)+D*j.val=D*i.val := by
          rw [← zws,zxt h.1]
        simp only [cap,zgb]
        omega
      · exact (hne rfl).elim
    | right j =>
      simp only [M,sylvester,Matrix.of_apply,z5m] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh:=hF _ hne
        have he :D*(i.val-j.val)+D*j.val=D*i.val := by
          rw [← zws,zxt h.1]
        simp only [cap,z5m]
        omega
      · exact (hne rfl).elim
  let s :=(∑ j:Fin m,D*j.val) + ∑ j:Fin n,D*j.val
  have hcap : ∑ j,cap j=m*H+n*B+s := by
    simp only [cap,s,Fin.sum_univ_add,zgb,z5m,
      sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  have hsum : ∑ i:Fin (m+n),D*i.val=D*(m*n)+s := by
    simp only [s,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,zws,
      sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  change M.det.natDegree≤_
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have ht: (∏ j,M (σ j) j).natDegree≤ m*H+n*B-D*(m*n) := by
    by_cases hz : ∃ j,M (σ j) j=0
    · obtain ⟨j,hj⟩:=hz
      have hzero : (∏ k,M (σ k) k)=0 :=
        Finset.prod_eq_zero (f := fun k=>M (σ k) k) (Finset.mem_univ j) hj
      rw [hzero,natDegree_zero]
      exact Nat.zero_le _
    · push Not at hz
      have h:=sum_le_sum (s :=univ) fun j _=>hentry (σ j) j (hz j)
      rw [sum_add_distrib,Equiv.sum_comp σ (fun i=>D*i.val),hcap,hsum] at h
      exact (natDegree_prod_le _ _).trans (by omega)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs] using ht
variable [Algebra L E]
theorem branch_exists (f :E[X][X]) (D W:ℕ)
    (hi:Irreducible f) (hd:0<f.natDegree) (hp:f.natDegree<p)
    (hw : ∀ i,f.coeff i≠0→(f.coeff i).natDegree+i*D ≤W) :
    ∃ r :L,branch f r≠0∧(branch f r).natDegree≤2*f.natDegree*W-f.natDegree*f.natDegree*D ∧
      ∀ (w:CurvePlace L E) (b:ℕ),aFA w.value f b →
        polyBound w.value (branch f r) (2*f.natDegree*b) := by
  classical
  let d:=f.natDegree
  let i:E[X] →+* FractionRing E[X] :=algebraMap _ _
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
  let _:CharP E[X] p:=inferInstance
  let _:CharP (FractionRing E[X]) p:=charP_of_injective_ringHom
    (zxb E[X] (FractionRing E[X])) p
  have hinj:=zxb E[X] (FractionRing E[X])
  have hfi:Irreducible (f.map i) :=
    ((hi.isPrimitive hd.ne').irreducible_iff_irreducible_map_fraction_map
      (K:=FractionRing E[X])).mp hi
  have hd' : (f.map i).natDegree=d:=natDegree_map_eq_of_injective hinj _
  have hpos :0<(f.map i).natDegree :=hd'.symm ▸ hd
  have hder : (f.map i).derivative.natDegree=d-1 :=
    (bD9 hpos (hd'.symm ▸ hp)).trans (congrArg (·-1) hd')
  have hres :polarResultant f≠0:= by
    have hsep:=(separable_iff_derivative_ne_zero hfi).mpr (fun hz =>
      (cast_ne_zero hpos (hd'.symm ▸ hp)) (by
        have h:=coeff_derivative (f.map i) ((f.map i).natDegree-1)
        rw [hz,coeff_zero,← zg0,zJf,
          zxt hpos,← leadingCoeff] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (leadingCoeff_ne_zero.mpr hfi.ne_zero)))
    have hn:=resultant_ne_zero _ _ hsep
    rw [hd',hder,derivative_map,resultant_map_map] at hn
    change i (polarResultant f)≠0 at hn
    exact fun hz=>hn (by rw [hz,map_zero])
  let ref :L→E[X] := fun r=>C (algebraMap L E r)
  have href :Function.Injective ref :=C_injective.comp (algebraMap L E).injective
  have hfinit : (ref ⁻¹' (f.roots.toFinset :Set E[X])).Finite :=
    f.roots.toFinset.finite_toSet.preimage href.injOn
  obtain ⟨r,hr⟩:=hfinit.exists_notMem
  have hval :f.eval (ref r)≠0:= fun h=>hr (Multiset.mem_toFinset.mpr
    ((mem_roots hi.ne_zero).mpr h))
  refine ⟨r,mul_ne_zero hres hval,?_,?_⟩
  · have hf (j:ℕ) (hj:f.coeff j≠0) : (f.coeff j).natDegree+D*j≤W:= by
      simpa only [Nat.mul_comm D j] using hw j hj
    have hg (j:ℕ) (hj:f.derivative.coeff j≠0) :
        (f.derivative.coeff j).natDegree+D*j≤W-D:= by
      have hc:f.coeff (j+1)≠0:= fun hz=>hj (by simp [coeff_derivative,hz])
      have hh:=hf (j+1) hc
      rw [zws,Nat.mul_one] at hh
      have hdeg: (f.derivative.coeff j).natDegree≤(f.coeff (j+1)).natDegree := by
        rw [coeff_derivative,← zg0,← C_eq_natCast]
        exact natDegree_mul_C_le _ _
      omega
    have hD:d*D ≤W:=(Nat.le_add_left _ _).trans (hw _ (leadingCoeff_ne_zero.mpr hi.ne_zero))
    have hR:=fXo f f.derivative d (d-1) D W (W-D) hf hg
    have hvaldeg: (f.eval (ref r)).natDegree≤W:= by
      rw [eval_eq_sum_range]
      apply natDegree_sum_le_of_forall_le
      intro j _
      simp only [ref,← map_pow]
      apply (natDegree_mul_C_le _ _).trans
      by_cases hj:f.coeff j=0
      · simp [hj]
      · exact (Nat.le_add_right _ _).trans (hw j hj)
    have d_eq :d=(d-1)+1 := by dsimp [d]; omega
    change (polarResultant f*f.eval (ref r)).natDegree≤_
    have hm: (d-1)*W+W=d*W:= by
      simpa only [Nat.add_mul,one_mul] using congrArg (· * W) d_eq.symm
    have hDW:D ≤W :=
      (by simpa only [one_mul] using Nat.mul_le_mul_right D (show 1≤d from hd) :D ≤d*D).trans hD
    have hdd:d*D+D*(d*(d-1))=d*d*D:= by
      calc
        _=d*D*((d-1)+1) := by ring
        _ = _:= by rw [← d_eq]; ring
    have hcast:d*(W-D)+(d-1)*W=(d*W+(d-1)*W)-d*D:= by
      rw [Nat.mul_sub,Nat.sub_add_comm (zBI _ hDW)]
    rw [hcast,Nat.sub_sub,hdd] at hR
    have hw' : d*d*D ≤d*W:= by
      rw [Nat.mul_assoc]
      exact zBI _ hD
    have hR' : (polarResultant f).natDegree+W≤2*d*W-d*d*D:= by
      change (f.resultant f.derivative d (d-1)).natDegree+W≤_
      rw [show 2*d*W=d*W+(d-1)*W+W by rw [add_assoc,hm]; ring]
      omega
    exact (natDegree_mul_le.trans (Nat.add_le_add_left hvaldeg _)).trans hR'
  · intro w b hb
    let v :=efc w.value
    let u:ℤᵐ⁰:=WithZero.exp (b:ℤ)
    have hF (j:ℕ) :v (f.coeff j)≤u:=Finset.sup_le fun k _=>hb j k
    have hG (j:ℕ) :v (f.derivative.coeff j)≤u:= by
      rw [coeff_derivative,map_mul,← zg0,← C_eq_natCast]
      change _ *adG w.value (C ((j+1 :ℕ) :E))≤_
      rw [cTA]
      exact (mul_le_mul' (hF _) (cast_le_one (v :=w.value) (j+1))).trans_eq (mul_one _)
    have hresv :v (polarResultant f)≤u^(d+(d-1)) :=
      resultant_val_le v f f.derivative _ _ _ hF hG
    have hunit :v (ref r)≤1 := by
      change adG w.value (C (algebraMap L E r))≤1
      rw [cTA]
      by_cases hr0:r=0
      · simp [hr0]
      · rw [w.on_constants r hr0]
    have hfv :v (f.eval (ref r))≤u:= by
      rw [eval_eq_sum_range]
      apply v.map_sum_le
      intro j _
      rw [map_mul,map_pow]
      calc
        _≤u*(1 :ℤᵐ⁰)^j:=mul_le_mul' (hF _) (pow_le_pow_left' hunit j)
        _ = _:= by simp
    intro j
    apply (aMX w.value _ j).trans
    change v (branch f r)≤_
    rw [branch,map_mul]
    calc
      _≤u^(d+(d-1))*u:=mul_le_mul' hresv hfv
      _ = _:= by
        rw [← pow_succ,show d+(d-1)+1=2*d by dsimp [d]; omega]
        simp [u,d,← WithZero.exp_nsmul,mul_comm]
open UniqueFactorizationMonoid in
theorem scaled_radical (B:E[X]) (hn:B≠0) (hp:B.natDegree<p) :
    ∃ G:E[X],G.leadingCoeff=B.leadingCoeff∧G.Separable∧G∣B ∧
      (∃ n:ℕ,B∣G^n) ∧
      ∀ (w:CurvePlace L E) (b:ℕ),polyBound w.value B b→polyBound w.value G b:= by
  classical
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
  let R:=radical B
  let G:=R*C B.leadingCoeff
  have hfactor {P:E[X]} (hP:P∈primeFactors B) :
      Irreducible P∧P.Monic∧P∣B :=
    (Polynomial.mem_normalizedFactors_iff hn).mp (mem_primeFactors.mp hP)
  have hRm:R.Monic:=monic_prod_of_monic _ _ fun _ hi=>(hfactor hi).2.1
  have hRs :R.Separable := by
    apply separable_prod'
    · exact fun i hi j hj hij=>(pairwise_primeFactors_isRelPrime hi hj hij).isCoprime
    · intro P hP
      obtain ⟨hir,_,hdvd⟩:=hfactor hP
      have hpd:=(natDegree_le_of_dvd hdvd hn).trans_lt hp
      have hpos :=hir.natDegree_pos
      apply (separable_iff_derivative_ne_zero hir).mpr
      intro hz
      have he :=coeff_derivative P (P.natDegree-1)
      rw [hz,coeff_zero,← zg0,zJf,zxt hpos,
        ← leadingCoeff] at he
      exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hir.ne_zero) (cast_ne_zero hpos hpd)) he.symm
  have hu:IsUnit (C B.leadingCoeff) :=isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr hn))
  have hgl:G.leadingCoeff=B.leadingCoeff := by
    change (R*C B.leadingCoeff).leadingCoeff=B.leadingCoeff
    rw [leadingCoeff_mul,hRm.leadingCoeff,leadingCoeff_C,one_mul]
  have hgd:G∣B:=hu.mul_right_dvd.mpr radical_dvd_self
  obtain ⟨n,hpow⟩:=exists_dvd_radical_self_pow hn
  have hGpow:B∣G^n:=hpow.trans (pow_dvd_pow_of_dvd (dvd_mul_right _ _) _)
  refine ⟨G,hgl,hRs.mul_unit hu,hgd,⟨n,hGpow⟩,?_⟩
  intro w b hb i
  obtain ⟨Q,hQ⟩:=hgd
  have hQm:Q.Monic:= by
    have h:=congrArg leadingCoeff hQ
    rw [leadingCoeff_mul,hgl] at h
    exact mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hn) (by simpa using h.symm)
  have h1 :1≤adG w.value Q:= by
    have h:=aMX w.value Q Q.natDegree
    change w.value Q.leadingCoeff≤_ at h
    rwa [hQm.leadingCoeff,map_one] at h
  calc
    _≤adG w.value G:=aMX w.value G i
    _≤adG w.value G*adG w.value Q :=
      le_mul_of_one_le_right zero_le h1
    _=adG w.value B:= by rw [← efd,← hQ]
    _≤_:=Finset.sup_le fun j _=>hb j
end
end qrezXJe
