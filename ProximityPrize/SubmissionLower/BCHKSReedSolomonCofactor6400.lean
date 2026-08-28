import ProximityPrize.SubmissionLower.BCHKSReedSolomonBadWitness6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusCofactor6400

/-!
# Outside-agreement locator factorization

For a sparse error support `T` and a witness agreement set `A`, the witness
polynomial vanishes on `A \ T`.  Factoring those roots leaves a cofactor whose
degree plus the first mixed-stack width is strictly below `#(A ∩ T)`.  This is
the exact root-count budget needed for multiplier degree descent.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]

/-- Product of the agreement roots lying outside the sparse source support. -/
noncomputable def outsideAgreementLocator
    (α : ι ↪ K) (A T : Finset ι) : K[X] :=
  Lagrange.nodal (A \ T) fun i => α i

@[simp]
theorem outsideAgreementLocator_natDegree
    (α : ι ↪ K) (A T : Finset ι) :
    (outsideAgreementLocator α A T).natDegree = (A \ T).card := by
  simp only [outsideAgreementLocator, Lagrange.natDegree_nodal]

theorem outsideAgreementLocator_ne_zero
    (α : ι ↪ K) (A T : Finset ι) :
    outsideAgreementLocator α A T ≠ 0 := by
  exact Lagrange.nodal_ne_zero

theorem outsideAgreementLocator_eval_ne_zero_of_mem
    (α : ι ↪ K) (A T : Finset ι) {i : ι} (hiT : i ∈ T) :
    (outsideAgreementLocator α A T).eval (α i) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro t ht heq
  have hit : i = t := α.injective heq
  subst t
  exact (Finset.mem_sdiff.mp ht).2 hiT

theorem outsideAgreementLocator_map
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A T : Finset ι) :
    (outsideAgreementLocator α A T).map sigma.toRingHom =
      outsideAgreementLocator α A T := by
  simp only [outsideAgreementLocator, Lagrange.nodal, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show sigma.toRingHom (α i) = α i from hfixed i]

/-- Every outside-support agreement contributes a distinct linear factor of
the witness polynomial. -/
theorem outsideAgreementLocator_dvd
    (α : ι ↪ K) (A T : Finset ι) (P : K[X])
    (hzero : ∀ i ∈ A, i ∉ T → P.eval (α i) = 0) :
    outsideAgreementLocator α A T ∣ P := by
  rw [outsideAgreementLocator, Lagrange.nodal]
  apply Finset.prod_dvd_of_coprime
  · exact (Polynomial.pairwise_coprime_X_sub_C α.injective).set_pairwise _
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact hzero i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2

/-- Choose the residual witness cofactor and record its exact degree
accounting. -/
theorem exists_outsideAgreementCofactor
    (α : ι ↪ K) (A T : Finset ι) (P : K[X]) (hP : P ≠ 0)
    (hzero : ∀ i ∈ A, i ∉ T → P.eval (α i) = 0) :
    ∃ Cof : K[X],
      outsideAgreementLocator α A T * Cof = P ∧ Cof ≠ 0 ∧
      (A \ T).card + Cof.natDegree = P.natDegree := by
  obtain ⟨Cof, hfactor⟩ := outsideAgreementLocator_dvd α A T P hzero
  have hfactor' : outsideAgreementLocator α A T * Cof = P := hfactor.symm
  have hCof : Cof ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor'
    exact hP hfactor'.symm
  have hdegree := congrArg Polynomial.natDegree hfactor'
  rw [Polynomial.natDegree_mul
      (outsideAgreementLocator_ne_zero α A T) hCof,
    outsideAgreementLocator_natDegree] at hdegree
  exact ⟨Cof, hfactor', hCof, hdegree⟩

/-- Removing the outside-support roots converts the global agreement count
into the strict cofactor room on the source agreements. -/
theorem outsideAgreementCofactor_degree_room
    (α : ι ↪ K) (A T : Finset ι) (P Cof : K[X]) (c : ℕ)
    (hfactor : outsideAgreementLocator α A T * Cof = P)
    (hCof : Cof ≠ 0) (hPdegree : P.natDegree + c < A.card) :
    Cof.natDegree + c < (A ∩ T).card := by
  have hdegree := congrArg Polynomial.natDegree hfactor
  rw [Polynomial.natDegree_mul
      (outsideAgreementLocator_ne_zero α A T) hCof,
    outsideAgreementLocator_natDegree] at hdegree
  have hpartition := Finset.card_sdiff_add_card_inter A T
  omega

/-- The mixed source relation descends, on source agreements, to the pair of
the witness cofactor and its coefficient conjugate. -/
theorem mixedRelation_outsideAgreementCofactor_root
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i)
    (A T : Finset ι) (P Cof : K[X]) (source : K → K) (c h : ℕ)
    (rel : MixedBoundedKernelRelation (T.map α) source
      (fun x => sigma (source x)) c h)
    (hfactor : outsideAgreementLocator α A T * Cof = P)
    (hsource : ∀ i ∈ A ∩ T, source (α i) = P.eval (α i)) :
    ∀ x ∈ (A ∩ T).map α,
      (rel.sourceMultiplier * Cof +
        rel.targetMultiplier * Cof.map sigma.toRingHom).eval x = 0 := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
  have hiA : i ∈ A := (Finset.mem_inter.mp hi).1
  have hiT : i ∈ T := (Finset.mem_inter.mp hi).2
  subst x
  let L := outsideAgreementLocator α A T
  have hLne : L.eval (α i) ≠ 0 := by
    exact outsideAgreementLocator_eval_ne_zero_of_mem α A T hiT
  have hdirect : P.eval (α i) = L.eval (α i) * Cof.eval (α i) := by
    rw [← hfactor]
    simp only [L, Polynomial.eval_mul]
  have hconjugate : sigma (P.eval (α i)) =
      L.eval (α i) * (Cof.map sigma.toRingHom).eval (α i) := by
    rw [← polynomial_map_eval_of_fixed sigma P (α i) (hfixed i),
      ← hfactor, Polynomial.map_mul,
      outsideAgreementLocator_map α sigma hfixed A T,
      Polynomial.eval_mul]
  have hrel := rel.relation (α i) (Finset.mem_map_of_mem α hiT)
  rw [hsource i hi, hconjugate, hdirect] at hrel
  have hproduct : L.eval (α i) *
      (rel.sourceMultiplier.eval (α i) * Cof.eval (α i) +
        rel.targetMultiplier.eval (α i) *
          (Cof.map sigma.toRingHom).eval (α i)) = 0 := by
    calc
      L.eval (α i) *
          (rel.sourceMultiplier.eval (α i) * Cof.eval (α i) +
            rel.targetMultiplier.eval (α i) *
              (Cof.map sigma.toRingHom).eval (α i)) =
          rel.sourceMultiplier.eval (α i) *
              (L.eval (α i) * Cof.eval (α i)) +
            rel.targetMultiplier.eval (α i) *
              (L.eval (α i) *
                (Cof.map sigma.toRingHom).eval (α i)) := by ring
      _ = 0 := hrel
  have hroot := (mul_eq_zero.mp hproduct).resolve_left hLne
  simpa only [Polynomial.eval_add, Polynomial.eval_mul] using hroot

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Complete production bridge on the large-support, noncancelling sparse
branch: the concrete locator kernel and outside-agreement cofactor descend to
the low `2h` stack consumed by the pencil argument. -/
theorem score6400_lowStackKernel_of_sparse_mcaBad
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field) (z : IRSProfile.Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : MCABad IRSProfile.baseCode e₀ e₁ 185364 z)
    (hnoncancel : z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    LinearMap.ker
      (lowStackRelationMap
        ((pairSupport e₀ e₁).map IRSProfile.domain)
        (score6400AffineErrorSource e₀ e₁ z)
        (fun x => koalaSexticFrobenius
          (score6400AffineErrorSource e₀ e₁ z x))
        ((pairSupport e₀ e₁).card - 54292)) ≠ ⊥ := by
  classical
  obtain ⟨A, P, hA, hPnat, hPagree, hintersects,
      htranspose, hsourceNe, hcard, hhcap⟩ :=
    exists_score6400_mixed_witness_of_sparse_mcaBad
      e₀ e₁ z hsparse hbad hnoncancel hlarge
  let T := pairSupport e₀ e₁
  let S := T.map IRSProfile.domain
  let source := score6400AffineErrorSource e₀ e₁ z
  let target : IRSProfile.Field → IRSProfile.Field := fun x =>
    koalaSexticFrobenius (source x)
  let h := T.card - 54292
  have hPne : P ≠ 0 := by
    obtain ⟨i, hiA, hiT⟩ := hintersects
    have hlineNe : e₀ i + z * e₁ i ≠ 0 :=
      affine_error_ne_zero_on_support_of_not_cancellation
        e₀ e₁ T (fun _ hi => hi) z hnoncancel i hiT
    intro hPzero
    have hi := hPagree i hiA
    rw [hPzero, Polynomial.eval_zero] at hi
    exact hlineNe hi.symm
  have hzero : ∀ i ∈ A, i ∉ T → P.eval (IRSProfile.domain i) = 0 := by
    intro i hiA hiT
    obtain ⟨hi₀, hi₁⟩ := pairSupport_values_eq_zero_of_not_mem e₀ e₁ hiT
    rw [hPagree i hiA, hi₀, hi₁, mul_zero, add_zero]
  obtain ⟨Cof, hfactor, hCof, hdegree⟩ :=
    exists_outsideAgreementCofactor IRSProfile.domain A T P hPne hzero
  have hPdegreeRoom : P.natDegree + 54292 < A.card := by omega
  have hCofRoomIndex : Cof.natDegree + 54292 < (A ∩ T).card :=
    outsideAgreementCofactor_degree_room
      IRSProfile.domain A T P Cof 54292 hfactor hCof hPdegreeRoom
  have hCofRoom : Cof.natDegree + 54292 <
      ((A ∩ T).map IRSProfile.domain).card := by
    simpa only [Finset.card_map] using hCofRoomIndex
  have htargetNe : ∀ x ∈ S, target x ≠ 0 := by
    intro x hx
    intro hzero
    apply hsourceNe x hx
    apply koalaSexticFrobenius.injective
    simpa only [target, map_zero] using hzero
  have hScard : 54292 + h = S.card := by
    simpa only [T, S, h, Finset.card_map] using hcard
  have hhpos : 0 < h := by
    dsimp only [h, T]
    omega
  have hcS : 54292 ≤ S.card := by
    rw [← hScard]
    omega
  have hhS : h ≤ S.card := by
    rw [← hScard]
    omega
  have htranspose' : LinearMap.ker
      (mixedStackMatrix S source target 54292 h).transpose.mulVecLin ≠ ⊥ := by
    simpa only [S, T, source, target, h] using htranspose
  have hmixed : LinearMap.ker
      (mixedStackRelationMap S source target 54292 h) ≠ ⊥ :=
    mixedStackRelationMap_ker_ne_bot_of_transpose_ker
      S source target 54292 h hScard htranspose'
  let rel := mixedBoundedKernelRelation_of_ker_ne_bot
    S source target 54292 h (by norm_num) hhpos hcS hhS
    (by simpa only [S, T, source] using hsourceNe) htargetNe hmixed
  have hsourceAgreement : ∀ i ∈ A ∩ T,
      source (IRSProfile.domain i) = P.eval (IRSProfile.domain i) := by
    intro i hi
    rw [show source (IRSProfile.domain i) = e₀ i + z * e₁ i by
      simp only [source, score6400AffineErrorSource_domain]]
    exact (hPagree i (Finset.mem_inter.mp hi).1).symm
  have hroot : ∀ x ∈ (A ∩ T).map IRSProfile.domain,
      (rel.sourceMultiplier * Cof +
        rel.targetMultiplier * Cof.map koalaSexticFrobenius.toRingHom).eval x = 0 :=
    mixedRelation_outsideAgreementCofactor_root
      IRSProfile.domain koalaSexticFrobenius
      koalaSexticFrobenius_fixed_domain A T P Cof source 54292 h rel
      hfactor hsourceAgreement
  have hCofMap : Cof.map koalaSexticFrobenius.toRingHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff koalaSexticFrobenius.injective).2 hCof
  have hCofDegree :
      (Cof.map koalaSexticFrobenius.toRingHom).natDegree = Cof.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      koalaSexticFrobenius.injective Cof
  have hhc : h ≤ 54292 := by
    dsimp only [h, T]
    omega
  exact lowStackRelationMap_ker_ne_bot_of_mixed_relation_and_cofactor
    S ((A ∩ T).map IRSProfile.domain) source target 54292 h rel
    Cof (Cof.map koalaSexticFrobenius.toRingHom) hCof hCofMap
    hCofDegree hhc hCofRoom hroot

end ProximityPrize.SubmissionLower
