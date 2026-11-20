import ProximityPrize.SubmissionLower.Fast068
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem firstRank_le (u : Words) : firstRank u ≤ L := by
  simpa only [firstRank, GenericLayer.genericRank, Fintype.card_fin] using
    Matrix.rank_le_card_height ((ordinary u).map (algebraMap K[X] Frac))
theorem actual_stackRank (u : Words) : stackRank u = t + 1 - nullity u := by
  have h := GenericLayer.rank_add_nullity (twoBlock u)
  simp only [Fintype.card_fin] at h
  change stackRank u + nullity u = t + 1 at h
  omega
theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at h hr ⊢
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
theorem rank_fee_exact : L + p * heightCap = rankFee := by decide
theorem anchor_fee_exact : p * heightCap + 2 * heightCap + blockLength + 2 = anchorFee := by
  decide
theorem rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankFee := by
  classical
  have h := Strata.two_block_rank_exception_count p node (u 0) (u 1) L t (nullity u)
    (actual_stackRank u) hu.2.1 (abnormalSlopes u Γ) (fun γ hγ => by
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have hs : t + 1 - nullity u - L ≤ heightCap := by
    have hr := hu.1
    dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at hr ⊢
    omega
  exact h.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans_eq rank_fee_exact)
private theorem type_one_bad_count_of_syndromes {F ι : Type}
    [Field F] [Fintype ι] [DecidableEq ι] (x u v : ι → F) (hx : Function.Injective x)
    (k a p : ℕ) (hk : k ≤ Fintype.card ι) (hp : 1 < p)
    (htype : Principal.TypeOneSyndromes x u v k p)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k a γ) :
    Γ.card ≤ 1 :=
  Principal.type_one_bad_count x hx u v k a p hk hp htype Γ hΓ
theorem type_one_count (u : Words) (htype : TypeAtMostOne u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 1 := by
  have hk : k ≤ Fintype.card I := by rw [IRSProfile.card_index]; decide
  exact type_one_bad_count_of_syndromes node (u 0) (u 1) node.injective
    k agreement p hk (by decide) htype Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
theorem deficient_count (u : Words) (Γ : Finset K) (hrank : firstRank u < L)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 311288 := by
  have h := K1_3.deficient_hankel_count node (u 0) (u 1) node.injective
    k L t (firstRank u) (by rw [IRSProfile.card_index]; decide) hrank rfl Γ
    (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans (Nat.add_le_add_left (Nat.le_of_lt_succ hrank) blockLength)
theorem principal_count (u : Words) (Γ : Finset K) (hprincipal : HomogeneousPrincipal u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 733118554521609 := by
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (t - a) = t := by omega
  let φ := algebraMap K[X] Frac
  have hcertificate : Principal.PrincipalAt
      (fun b j => φ (Principal.parameterSyndromes p node (u 0) (u 1) b j)) k a (t - a) := by
    refine { generator := g, nonzero := hg, degree_bound := hga, kernel_eq := ?_ }
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ t ∧ ((twoBlock u).map φ).mulVec (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ t :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  have h := Principal.generic_principal_bad_count_coarse φ
    (IsFractionRing.injective K[X] Frac) p (by decide) node node.injective
    Native.native_domain_fixed (u 0) (u 1) k k a (t - a)
    (by rw [IRSProfile.card_index]; decide)
    (hsum.trans_lt (show t < k by decide)) hcertificate Γ (fun γ hγ => by
      rw [hsum]
      exact bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans ((Nat.mul_le_mul_left p (Nat.add_le_add_left ha blockLength)).trans (by decide))
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t + 1) → F) (hc : (coefficientBlocks p x u v L t).mulVec c = 0) :
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0 := by
  funext i
  have h0 := congrFun hc (0, i.2)
  have h1 := congrFun hc (1, i.2)
  have h2 := congrFun hc (2, i.2)
  have h3 := congrFun hc (3, i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientBlocks, Fin.reduceEq,
    ite_true, ite_false, Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi : i.1 = 0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R := F) * C (∑ j, syndrome x v (i.2.val + j.val) * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h0, h1, map_zero, mul_zero, add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R := F) ^ p * C (∑ j, syndrome x v (i.2.val + j.val) ^ p * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h2, h3, map_zero, mul_zero, add_zero]
private theorem constantRankCount {E : Type} [Field E]
    (φ : F[X] →+* E) (hφ : Function.Injective φ) (p : ℕ) [ExpChar F p] (hp : 1 ≤ p)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A) (hL : k + L = A)
    (ht : A + t = Fintype.card ι)
    (r : ℕ) (hgeneric : ((stacked p x u v L t).map φ).rank = r)
    (hconstant : (coefficientBlocks p x u v L t).rank = r)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k A γ) : Γ.card ≤ p * r := by
  let M := stacked p x u v L t
  let C₀ := coefficientBlocks p x u v L t
  let W := LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h := LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientBlocks p x u v L t).rank + Module.finrank F W = _ at h
    rw [hconstant, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j)) = 0 :=
    coefficientKernel_annihilates p x u v L t c hc
  have hminor : (NormalFiber.pivot B).det.natDegree ≤ p * r := by
    have h := NormalFiber.minor_degree_le φ M r B (fun _ => p) (by
      intro i j
      exact (stacked_entry_natDegree p x u v L t i j).trans (by split_ifs <;> omega))
    simpa [Nat.mul_comm] using h
  exact Principal.constant_kernel_count p x hx hfixed u v k A L t (p * r) hkA hL ht
    _ B.minor_ne hminor (Principal.constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW)
    Γ hΓ
theorem constant_count (u : Words) (Γ : Finset K) (hu : ConstantKernel u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 174564516642824 := by
  let φ := algebraMap K[X] Frac
  have hrank : ((twoBlock u).map φ).rank = stackRank u := rfl
  have hconstant : (coefficientBlocks p node (u 0) (u 1) L t).rank = stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective K[X] Frac)
    p (by decide) node node.injective Native.native_domain_fixed
    (u 0) (u 1) k agreement L t (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide) (stackRank u) hrank hconstant
    Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  have hr : stackRank u ≤ t + 1 := by
    rw [actual_stackRank]
    exact Nat.sub_le _ _
  exact hcount.trans ((Nat.mul_le_mul_left p hr).trans_eq (by decide))
open K1_1
private def nativeMoments (u : Words) : Fin 2 → ℕ → Frac :=
  fun b j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) b j)
private theorem independent_nativeMoments (u : Words)
    (h : ¬ TypeAtMostOne u) : IndependentMoments (nativeMoments u) k := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective K[X] Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j
private theorem locator_matrix (u : Words) :
    Principal.recurrenceMatrix (nativeMoments u) k t =
      (twoBlock u).map (algebraMap K[X] Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap K[X] Frac)
    p node (u 0) (u 1) k t
private theorem locator_nullity (u : Words) :
    sliceDim (nativeMoments u) k (t + 1) = nullity u := by
  rw [sliceDim_succ (nativeMoments u) k t, locator_matrix]
  rfl
private theorem principal_of_one_active (u : Words) (a : ℕ) (ha : a ≤ t)
    (hone : sliceDim (nativeMoments u) k (a+1) = 1)
    (hnull : nullity u = (t + 1)-a) : HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) k (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) k (t + 1) = (t-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) k a t
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP
theorem two_active (u : Words) (hu : FrontRemainder u) : Nonempty (TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) k (independent_nativeMoments u hu.2.2.1)
  have hloc := hdim (t + 1) (by decide)
  rw [locator_nullity] at hloc
  have hpos := hu.1
  have hthree : 3 * t < 2 * k + 2 := by decide
  have hinactive : t < c := by omega
  have ha : a ≤ t := by omega
  have hb : b ≤ t := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hu.2.2.2.1 (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim
end
end P0
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
def c1 : Prop :=
  ∀ u Γ, nullity u ≤ frontLimit → BadFamily u Γ → Γ.card ≤ 181262114320041249
def c2 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    MovingGCD R → NormalSaturation R → ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ 1675928535564288
def c3 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T), NormalSaturation R
def c4 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    ¬ MovingGCD R → ¬ InvalidLeft R → NormalSaturation R →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    ∃ D : Reduction u T R, columnRank D.U D.V = 4 ∨
      ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B
def c5 : Prop :=
  ∀ u (T : TwoActive u) (R : Relation T) (D : Reduction u T R) (B : RankThree u T R D),
    Parallel B → ¬ UnitNorm B → ∀ Γ, BadFamily u Γ → Γ.card ≤ t + 1
def c6 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Nonparallel B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 117191744230663308
def c7 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 160322346563912056
def c8 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ anchorFee ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ anchorFee ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (AnchoredFamily M (Γ \ book))
def c9 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ lowCutoff →
    Γ.card ≤ 211033041011743389 + 18479565405173887
def c10 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    Γ.card ≤ highPrefix M.overhead + highRetained M.overhead + 1
def c11 : Prop := WeightedList
theorem mem_normalSlopes {u : Words} {Γ : Finset K} {γ : K} :
    γ ∈ normalSlopes u Γ ↔ γ ∈ Γ ∧ Normal u γ := by
  classical exact Finset.mem_filter
theorem normal_badFamily {u : Words} {Γ : Finset K} (hΓ : BadFamily u Γ) :
    BadFamily u (normalSlopes u Γ) :=
  fun γ hγ => hΓ γ (mem_normalSlopes.mp hγ).1
theorem normal_on_normalSlopes {u : Words} {Γ : Finset K} :
    ∀ γ ∈ normalSlopes u Γ, Normal u γ :=
  fun _ hγ => (mem_normalSlopes.mp hγ).2
theorem add_rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ b + rankFee := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)]
  exact Nat.add_le_add hb (rank_exceptions u hu Γ)
theorem anchored_list_count (hlist : WeightedList) {u deleted} (M : AnchorModel u deleted)
    (Γ : Finset K) (F : AnchoredFamily M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ listCap := by
  classical
  obtain ⟨hfinite, hprice⟩ := hlist M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe (k + 1)
      · have hn : (F.scalar γ).natDegree < k + 1 := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.agreement.trans
      apply Finset.card_le_card
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card = (Γ.image F.scalar).card := (Finset.card_image_of_injOn F.distinct).symm
    _ ≤ hfinite.toFinset.card := Finset.card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ listCap := hprice
private theorem high_with_reserve (w : ℤ) :
    highPrefix w + highRetained w + 1 + anchorFee + rankFee ≤ scalarCap := by
  unfold highPrefix highRetained
  split_ifs <;> decide
private theorem coherent_count (h8 : c8) (h9 : c9) (h10 : c10) (hlist : WeightedList)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ scalarCap := by
  classical
  let N := normalSlopes u Γ
  rcases h8 u hu T R D B hsat hp hn N (normal_badFamily hΓ) normal_on_normalSlopes with
    hcheap | ⟨book, hs, hb, M, ⟨F⟩⟩
  · exact (add_rank_exceptions u hu Γ _ hcheap).trans (by decide)
  · have htotal : Γ.card ≤ (N \ book).card + book.card + rankFee :=
      add_rank_exceptions u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    have hreserve (b : ℕ) (h : (N \ book).card ≤ b) : Γ.card ≤ b + anchorFee + rankFee :=
      htotal.trans (Nat.add_le_add_right (Nat.add_le_add h hb) rankFee)
    have hwmax : M.overhead ≤ (heightCap : ℤ) := by
      have hh := M.height_bound
      unfold AnchorModel.overhead
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · exact (hreserve _ (anchored_list_count hlist M _ F hw₀)).trans (by decide)
    by_cases hwL : M.overhead ≤ lowCutoff
    · exact (hreserve _ (h9 u _ M _ F (by omega) hwL)).trans (by decide)
    · exact (hreserve _ (h10 u _ M _ F (by omega) hwmax)).trans (high_with_reserve M.overhead)
private theorem scalar_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (hlist : WeightedList)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ scalarCap := by
  classical
  by_cases hpref : nullity u ≤ frontLimit
  · exact (h1 u Γ hpref hΓ).trans (by decide)
  by_cases hdef : firstRank u < L
  · exact (deficient_count u Γ hdef hΓ).trans (by decide)
  by_cases htype : TypeAtMostOne u
  · exact (type_one_count u htype Γ hΓ).trans (by decide)
  by_cases hprincipal : HomogeneousPrincipal u
  · exact (principal_count u Γ hprincipal hΓ).trans (by decide)
  by_cases hconstant : ConstantKernel u
  · exact (constant_count u Γ hconstant hΓ).trans (by decide)
  have hu : FrontRemainder u :=
    ⟨Nat.lt_of_not_ge hpref, Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef),
      htype, hprincipal, hconstant⟩
  obtain ⟨T⟩ := two_active u hu
  let R := relation_of_two_active hu T
  have hsat := h3 u hu T R
  let N := normalSlopes u Γ
  have hN := normal_badFamily hΓ
  have hnormal := @normal_on_normalSlopes u Γ
  by_cases hmoving : MovingGCD R
  · exact (add_rank_exceptions u hu Γ _ (h2 u hu T R hmoving hsat N hN hnormal)).trans
      (by decide)
  have hnone (he : N = ∅) : Γ.card ≤ scalarCap :=
    (add_rank_exceptions u hu Γ 0 (by rw [show normalSlopes u Γ = ∅ from he]; simp)).trans
      (by decide)
  by_cases hinvalid : InvalidLeft R
  · apply hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact (hsat γ hnγ M).valid hinvalid
  by_cases hne : N.Nonempty
  · obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := h4 u hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, bad_mark u Γ hΓ γ hγΓ⟩
    · exact (add_rank_exceptions u hu Γ _ (h7 u hu T R D hsat hfour N hN hnormal)).trans
        (by decide)
    · exact (add_rank_exceptions u hu Γ _ (h6 u hu T R D B hsat hnp N hN hnormal)).trans
        (by decide)
    · by_cases hn : UnitNorm B
      · exact coherent_count h8 h9 h10 hlist u hu T R D B hsat hpar hn Γ hΓ
      · exact (h5 u T R D B hpar hn Γ hΓ).trans (by decide)
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) (h8 : c8) (h9 : c9) (h10 : c10) (h11 : c11) :
    ProtocolClaim 6920 335573291 1073741824 :=
  protocol_claim_of_scalar_cap h11 (scalar_count h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
end
end P0
end
