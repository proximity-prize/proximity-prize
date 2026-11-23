import ProximityPrize.SubmissionLower.ZkEhKoc
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace qISdf9a
open PowerSeries
open scoped BigOperators
private theorem bHQ {F B M ι:Type} [Field F] [CommRing B] [IsDomain B]
    [Algebra F B] [AddCommGroup M] [Module F M] [Fintype ι]
    (f :B →ₗ[F] M) (r :ι→B) (a :B) (ha :a≠0)
    (hf : ∀ x,f (a*x)=0) (hr :LinearIndependent F (f ∘ r)) (k :ℕ) :
    LinearIndependent F (fun ij:Fin (k+1)×ι=>a^(ij.1 :ℕ)*r ij.2) := by
  classical
  induction k with
  | zero =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i,j⟩ => ?_
    have hi:i=0:=Fin.eq_zero _
    subst i
    rw [Fintype.sum_prod_type] at hc
    change (∑ i:Fin 1,∑ j,c (i,j)•(a^(i:ℕ)*r j))=0 at hc
    rw [Fin.sum_univ_one] at hc
    have hh: (∑ j,c (0,j)•(f ∘ r) j)=0:= by
      simpa only [Fin.val_zero,pow_zero,one_mul,map_sum,map_smul,map_zero,
        Function.comp_apply] using congrArg f hc
    exact Fintype.linearIndependent_iff.mp hr _ hh j
  | succ k ih =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i,j⟩ => ?_
    have hsplit :
        (∑ u:ι,c (0,u)•r u) +
          a*(∑ ij:Fin (k+1)×ι,c (ij.1.succ,ij.2)•(a^(ij.1 :ℕ)*r ij.2))=0:= by
      rw [Fintype.sum_prod_type,Fin.sum_univ_succ] at hc
      simpa only [Fintype.sum_prod_type,Fin.val_zero,Fin.val_succ,pow_zero,one_mul,
        pow_succ',Finset.mul_sum,mul_smul_comm,mul_assoc] using hc
    have hh: (∑ u,c (0,u)•(f ∘ r) u)=0:= by
      simpa only [map_add,map_sum,map_smul,map_zero,hf,add_zero,
        Function.comp_apply] using congrArg f hsplit
    have hc₀ : ∀ u,c (0,u)=0:=Fintype.linearIndependent_iff.mp hr _ hh
    have htail: (∑ ij:Fin (k+1)×ι,
        c (ij.1.succ,ij.2)•(a^(ij.1 :ℕ)*r ij.2))=0:= by
      simp only [hc₀,zero_smul,Finset.sum_const_zero,zero_add] at hsplit
      exact (mul_eq_zero.mp hsplit).resolve_left ha
    refine Fin.cases (hc₀ j) (fun i => ?_) i
    exact Fintype.linearIndependent_iff.mp ih _ htail (i,j)
theorem jet_powers {F B ι:Type} [Field F] [CommRing B] [IsDomain B] [Algebra F B]
    [Fintype ι] (e :ι→B →ₐ[F] PowerSeries F) (v :ι→ℕ)
    (a s :B) (t:ι→F) (u:ι→B) (ha :a≠0) (ht:Function.Injective t)
    (hs : ∀ i,constantCoeff (e i s)=t i)
    (hu : ∀ i,constantCoeff (e i (u i))=0∧coeff 1 (e i (u i))≠0)
    (hav : ∀ i j,j<v i→ coeff j (e i a)=0) :
    ∃ r : (Σ i,Fin (v i))→B,∀ k,
      LinearIndependent F (fun ij:Fin (k+1)×(Σ i,Fin (v i)) =>
        a^(ij.1 :ℕ)*r ij.2) := by
  classical
  let b (i:ι) := ∏ j∈Finset.univ.erase i,(s-algebraMap F B (t j))^(v j)
  let r (ij:Σ i,Fin (v i)) :=b ij.1*(u ij.1)^(ij.2 :ℕ)
  let f :B →ₗ[F] ((i:ι)→Fin (v i)→F) :=
    LinearMap.pi fun i=>LinearMap.pi fun j=>(coeff (j:ℕ)).comp (e i).toLinearMap
  refine ⟨r,bHQ f r a ha ?_ ?_⟩
  · intro x
    ext i j
    change coeff (j:ℕ) (e i (a*x))=0
    rw [map_mul]
    exact X_pow_dvd_iff.mp
      (dvd_mul_of_dvd_left (X_pow_dvd_iff.mpr (hav i)) _) _ j.isLt
  have hconst (i j:ι) :constantCoeff (e i (s-algebraMap F B (t j)))=t i - t j:= by
    simp [hs,Algebra.algebraMap_eq_smul_one]
  have hu' (i:ι) : (e i (u i)).order=1 := by
    apply order_eq_nat.mpr
    exact ⟨(hu i).2,fun j hj=> by
      rw [show j=0 by omega,coeff_zero_eq_constantCoeff_apply,(hu i).1]⟩
  have hb (i:ι) : (e i (b i)).order=0:= by
    apply order_eq_nat.mpr
    refine ⟨?_,fun j hj=>(Nat.not_lt_zero j hj).elim⟩
    rw [coeff_zero_eq_constantCoeff_apply]
    simp only [b,map_prod,map_pow,hconst]
    exact Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ (sub_ne_zero.mpr (ht.ne (Finset.mem_erase.mp hj).1.symm))
  have hd (i j:ι) (h:i≠j) : (PowerSeries.X:PowerSeries F)^(v i)∣e i (b j) := by
    have hmem:i∈Finset.univ.erase j:=Finset.mem_erase.mpr ⟨h,Finset.mem_univ _⟩
    have hx : (PowerSeries.X:PowerSeries F)∣e i (s-algebraMap F B (t i)) :=
      X_dvd_iff.mpr (by rw [hconst,sub_self])
    simp only [b,map_prod,map_pow]
    exact (pow_dvd_pow_of_dvd hx _).trans (Finset.dvd_prod_of_mem _ hmem)
  have hcross (i j:ι) (h:i≠j) (m:Fin (v i)) (n:Fin (v j)) :
      coeff (m:ℕ) (e i (r ⟨j,n⟩))=0:= by
    rw [show r ⟨j,n⟩=b j*u j^(n:ℕ) from rfl,map_mul]
    exact X_pow_dvd_iff.mp (dvd_mul_of_dvd_left (hd i j h) _) _ m.isLt
  have hord (i:ι) (j:Fin (v i)) : (e i (r ⟨i,j⟩)).order=(j:ℕ) := by
    change (e i (b i*u i^(j:ℕ))).order= _
    rw [map_mul,map_pow,order_mul,order_pow,hb,hu',zero_add,nsmul_one]
  refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i,j⟩ => ?_
  have hrow (m:Fin (v i)) :
      (∑ n:Fin (v i),c ⟨i,n⟩*coeff (m:ℕ) (e i (r ⟨i,n⟩)))=0:= by
    have hz :=congrFun (congrFun hc i) m
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul,
      Function.comp_apply,Fintype.sum_sigma] at hz
    change (∑ j,∑ n:Fin (v j),c ⟨j,n⟩*coeff (m:ℕ) (e i (r ⟨j,n⟩)))=0 at hz
    rw [Finset.sum_eq_single i] at hz
    · exact hz
    · intro j _ hj
      exact Finset.sum_eq_zero fun n _=> by rw [hcross i j hj.symm,mul_zero]
    · simp
  have hzero (m:ℕ) : ∀ hm:m<v i,c ⟨i,⟨m,hm⟩⟩=0:= by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      let j:Fin (v i) :=⟨m,hm⟩
      have hh:=hrow j
      rw [Finset.sum_eq_single j] at hh
      · exact (mul_eq_zero.mp hh).resolve_right (order_eq_nat.mp (hord i j)).1
      · intro n _ hn
        rcases lt_or_gt_of_ne (fun he=>hn (Fin.ext he)) with hlt | hgt
        · rw [ih n hlt n.isLt,zero_mul]
        · rw [(order_eq_nat.mp (hord i n)).2 _ hgt,mul_zero]
      · simp
  exact hzero j j.isLt
end qISdf9a
