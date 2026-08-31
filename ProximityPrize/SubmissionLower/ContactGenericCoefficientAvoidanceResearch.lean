import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactGenericCoefficientAvoidanceResearch
open Function Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {ι K M:Type*} [Field K] [AddCommGroup M] [Module K M]
private theorem finite_iUnion_ssubset
    (s:Finset ι) (p:ι → Submodule K M)
    (h₁:∀ i,p i≠⊤) (h₂:s.card < ENat.card K):
    ⋃ i∈s,(p i:Set M) ⊂ univ:=by
  letI:DecidableEq ι:=Classical.decEq ι
  letI:DecidableEq K:=Classical.decEq K
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂:s.card+1 < ENat.card K:=by simpa [Finset.card_insert_of_notMem hj] using! h₂
    specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
    contrapose hj'
    replace hj':(p j:Set M) ∪ (⋃ i∈s,p i)=univ:=by
      simpa [Finset.mem_insert] using! hj'
    suffices (p j:Set M) ⊆ ⋃ i∈s,p i by rwa [union_eq_right.mpr this] at hj'
    intro x (hx:x∈p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using! hs
    obtain ⟨y,hy⟩:∃ y,y∉p j:=by specialize h₁ j;contrapose! h₁;ext;simp [h₁]
    have hy₀:y≠0:=by aesop
    let sxy:={x+t • y | (t:K) (ht:t≠0)}
    have hsxy:sxy ⊆ ⋃ i∈s,p i:=by
      suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
      rw [Set.disjoint_iff]
      rintro-⟨⟨t,ht₀,rfl⟩,ht:x+t • y∈p j⟩
      rw [(p j).add_mem_iff_right hx,(p j).smul_mem_iff ht₀] at ht
      contradiction
    obtain ⟨k,hk,t₁,t₂,ht,ht₁,ht₂⟩:∃ᵉ (k∈s) (t₁:K) (t₂:K),
        t₁≠t₂∧x+t₁ • y∈p k∧x+t₂ • y∈p k:=by
      suffices ∃ᵉ (k∈s) (z₁∈sxy) (z₂∈sxy),z₁≠z₂∧z₁∈p k∧z₂∈p k by
        obtain ⟨k,hk, -,⟨t₁, -,rfl⟩, -,⟨t₂, -,rfl⟩,htne,ht₁,ht₂⟩:=this
        exact ⟨k,hk,t₁,t₂,by aesop,ht₁,ht₂⟩
      choose f hf using fun z:sxy↦mem_iUnion.mp (hsxy z.property)
      have hf':MapsTo f univ s:=fun z _↦by specialize hf z;aesop
      suffices ∃ z₁ z₂,z₁≠z₂∧f z₁=f z₂ by
        obtain ⟨z₁,z₂,hne,heq⟩:=this
        exact ⟨f z₁,hf' (mem_univ _),z₁,z₁.property,z₂,z₂.property,
          Subtype.coe_ne_coe.mpr hne,by specialize hf z₁;simp_all,by specialize hf z₂;aesop⟩
      have key:s.card < sxy.encard:=by
        refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
        have:Injective (fun t:K↦x+t • y):=
          fun t₁ t₂ ht↦smul_left_injective K hy₀ <| by simpa using! ht
        have aux:sxy=((fun t:K↦x+t • y) '' {t | t≠0}):=by ext;simp [sxy]
        rw [aux,this.encard_image,encard_ne_add_one]
      obtain ⟨z₁, -,z₂, -,h⟩:=exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
      exact ⟨z₁,z₂,h⟩
    replace ht:y∈p k:=by
      have:(t₁-t₂) • y∈p k:=by convert sub_mem ht₁ ht₂;module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht:x∈p k:=by convert sub_mem ht₁ ((p k).smul_mem t₁ ht);simp
    simpa using! ⟨k,hk,ht⟩
theorem exists_avoiding_finite_proper_submodules
    [Finite ι] [Infinite K]
    (p:ι → Submodule K M) (hproper:∀ i,p i≠⊤):
    ∃ x,∀ i,x∉p i:=by
  let _i:Fintype ι:=Fintype.ofFinite ι
  suffices ⋃ i,(p i:Set M) ⊂ univ by
    simpa [ssubset_univ_iff,iUnion_eq_univ_iff] using this
  simpa using finite_iUnion_ssubset Finset.univ p hproper (by simp)
variable {N:Type*} [AddCommGroup N] [Module K N]
theorem exists_simultaneous_noncancellation
    [Finite ι] [Infinite K]
    (lead:ι → M →ₗ[K] N) (hlead:∀ i,lead i≠0):
    ∃ x:M,∀ i,lead i x≠0:=by
  let bad:ι → Submodule K M:=fun i↦LinearMap.ker (lead i)
  have hproper:∀ i,bad i≠⊤:=by
    intro i htop
    apply hlead i
    rw [←LinearMap.ker_eq_top]
    exact htop
  obtain ⟨x,hx⟩:=
    exists_avoiding_finite_proper_submodules bad hproper
  refine ⟨x,fun i hi↦?_⟩
  exact hx i (by simpa [bad,LinearMap.mem_ker] using hi)
variable {σ:Type*} [DecidableEq σ]
def polynomialOfSupport (E:Finset (σ →₀ ℕ)) (c:E → K):
    MvPolynomial σ K:=
  ∑ d:E,MvPolynomial.monomial d.1 (c d)
@[simp] theorem coeff_polynomialOfSupport
    (E:Finset (σ →₀ ℕ)) (c:E → K) (d:σ →₀ ℕ):
    MvPolynomial.coeff d (polynomialOfSupport E c)=
      if hd:d∈E then c ⟨d,hd⟩ else 0:=by
  classical
  rw [show polynomialOfSupport E c=
      ∑ e∈(Finset.univ:Finset E),
        MvPolynomial.monomial e.1 (c e) by simp [polynomialOfSupport]]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd:d∈E
  · simp only [hd,dite_true]
    rw [Finset.sum_eq_single ⟨d,hd⟩]
    · simp
    · intro e _ hne
      have hval:e.1≠d:=by
        intro heq
        apply hne
        exact Subtype.ext heq
      rw [if_neg hval]
    · simp
  · simp only [hd,dite_false]
    apply Finset.sum_eq_zero
    intro e _
    have hval:e.1≠d:=by
      intro heq
      apply hd
      rw [←heq]
      exact e.2
    rw [if_neg hval]
theorem support_polynomialOfSupport_subset
    (E:Finset (σ →₀ ℕ)) (c:E → K):
    (polynomialOfSupport E c).support ⊆ E:=by
  intro d hd
  by_contra hnot
  have hcoeff:=MvPolynomial.mem_support_iff.mp hd
  rw [coeff_polynomialOfSupport,dif_neg hnot] at hcoeff
  exact hcoeff rfl
theorem exists_supportedPolynomial_simultaneous_noncancellation
    {τ:Type*} [Finite τ] [Infinite K]
    (E:Finset (σ →₀ ℕ))
    (lead:τ → (E → K) →ₗ[K] K) (hlead:∀ t,lead t≠0):
    ∃ c:E → K,
      (polynomialOfSupport E c).support ⊆ E∧
        ∀ t,lead t c≠0:=by
  obtain ⟨c,hc⟩:=exists_simultaneous_noncancellation lead hlead
  exact ⟨c,support_polynomialOfSupport_subset E c,hc⟩
end
end ProximityPrize.SubmissionLower.ContactGenericCoefficientAvoidanceResearch
