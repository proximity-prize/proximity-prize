import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def affineDenominator (a₀ a₁ : Polynomial K) (g : K) : Polynomial K :=
  a₀ + Polynomial.C g * a₁

private theorem affine_at_common_root {L : Type*} [Field L]
    (c : K →+* L) (a₀ a₁ : Polynomial K) (hA : IsCoprime a₀ a₁)
    (g : K) (x : L) (hz : (affineDenominator a₀ a₁ g).eval₂ c x = 0) :
    a₀.eval₂ c x = -(c g * a₁.eval₂ c x) ∧ a₁.eval₂ c x ≠ 0 := by
  have hs : a₀.eval₂ c x + c g * a₁.eval₂ c x = 0 := by
    simpa only [affineDenominator, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C] using hz
  refine ⟨eq_neg_of_add_eq_zero_left hs, ?_⟩
  intro h₁
  have h₀ : a₀.eval₂ c x = 0 := by simpa only [h₁, mul_zero, add_zero] using hs
  obtain ⟨U, V, hUV⟩ := hA
  have he := congrArg (Polynomial.eval₂ c x) hUV
  exact zero_ne_one (by simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_one, h₀, h₁, mul_zero, zero_add] using he)

private theorem seed_eq_of_common_root {L : Type*} [Field L]
    (c : K →+* L) (a₀ a₁ : Polynomial K) (hA : IsCoprime a₀ a₁)
    (g h : K) (x : L)
    (hg : (affineDenominator a₀ a₁ g).eval₂ c x = 0)
    (hh : (affineDenominator a₀ a₁ h).eval₂ c x = 0) : g = h := by
  obtain ⟨h₀, h₁⟩ := affine_at_common_root c a₀ a₁ hA g x hg
  have eq := h₀.symm.trans (affine_at_common_root c a₀ a₁ hA h x hh).1
  exact c.injective (mul_right_cancel₀ h₁ (neg_injective eq))

theorem node_pole_seeds_card_le {I : Type*} (nodes : Finset I) (x : I → K)
    (a₀ a₁ : Polynomial K) (hA : IsCoprime a₀ a₁) (seeds : Finset K)
    (hpole : ∀ g ∈ seeds, ∃ i ∈ nodes, (affineDenominator a₀ a₁ g).eval (x i) = 0) :
    seeds.card ≤ nodes.card := by
  classical
  let fiber (i : I) := seeds.filter fun g => (affineDenominator a₀ a₁ g).eval (x i) = 0
  have hsub : seeds ⊆ nodes.biUnion fiber := by
    intro g hg
    obtain ⟨i, hi, he⟩ := hpole g hg
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hg, he⟩⟩
  have hfiber (i : I) : (fiber i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro g hg h hh
    have hg' := (Finset.mem_filter.mp hg).2
    have hh' := (Finset.mem_filter.mp hh).2
    exact seed_eq_of_common_root (RingHom.id K) a₀ a₁ hA g h (x i) hg' hh'
  calc
    seeds.card ≤ (nodes.biUnion fiber).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ nodes, (fiber i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ nodes, 1 := Finset.sum_le_sum fun i _ => hfiber i
    _ = nodes.card := by simp

theorem zero_affine_denominator_seeds_card_le (a₀ a₁ : Polynomial K)
    (hA : IsCoprime a₀ a₁) (seeds : Finset K)
    (hz : ∀ g ∈ seeds, affineDenominator a₀ a₁ g = 0) : seeds.card ≤ 1 := by
  simpa using node_pole_seeds_card_le ({0} : Finset ℕ) (fun _ => (0 : K))
    a₀ a₁ hA seeds (fun g hg => ⟨0, Finset.mem_singleton_self 0, by rw [hz g hg]; simp⟩)

private theorem isUnit_of_natDegree_zero_ne_zero {P : Polynomial K}
    (hdeg : P.natDegree = 0) (hP : P ≠ 0) : IsUnit P := by
  have he := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : P.coeff 0 ≠ 0 := by
    intro hz
    exact hP (by rw [he, hz, map_zero])
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map Polynomial.C

def frobeniusEliminant (a₀ a₁ b₀ b₁ : Polynomial K) (p : ℕ) : Polynomial K :=
  b₀ * a₁ ^ p + (-a₀) ^ p * b₁

private theorem frobeniusEliminant_natDegree_le (a₀ a₁ b₀ b₁ : Polynomial K) (p : ℕ) :
    (frobeniusEliminant a₀ a₁ b₀ b₁ p).natDegree ≤
      p * max a₀.natDegree a₁.natDegree + max b₀.natDegree b₁.natDegree := by
  unfold frobeniusEliminant
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_pow]
    calc
      _ ≤ max b₀.natDegree b₁.natDegree + p * max a₀.natDegree a₁.natDegree :=
        Nat.add_le_add (le_max_left _ _) (Nat.mul_le_mul_left p (le_max_right _ _))
      _ = _ := Nat.add_comm _ _
  · apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg]
    exact Nat.add_le_add (Nat.mul_le_mul_left p (le_max_left _ _)) (le_max_right _ _)

private theorem coeff_pos_of_primitive_nondegenerate (a₀ a₁ : Polynomial K)
    (hA : IsCoprime a₀ a₁) (hpos : 0 < max a₀.natDegree a₁.natDegree) :
    a₀ ≠ 0 ∧ a₁ ≠ 0 := by
  constructor
  · intro h₀
    have hu : IsUnit a₁ := isCoprime_zero_left.mp (h₀ ▸ hA)
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    simp [h₀, hd] at hpos
  · intro h₁
    have hu : IsUnit a₀ := isCoprime_zero_left.mp (h₁ ▸ hA.symm)
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    simp [h₁, hd] at hpos

private theorem frobeniusEliminant_ne_zero (a₀ a₁ b₀ b₁ : Polynomial K) (p : ℕ)
    (hA : IsCoprime a₀ a₁) (hB : IsCoprime b₀ b₁)
    (hpos : 0 < max a₀.natDegree a₁.natDegree) (hsmall : max b₀.natDegree b₁.natDegree < p) :
    frobeniusEliminant a₀ a₁ b₀ b₁ p ≠ 0 := by
  intro hz
  obtain ⟨ha₀, ha₁⟩ := coeff_pos_of_primitive_nondegenerate a₀ a₁ hA hpos
  have hb₀ : b₀ ≠ 0 := by
    intro h₀
    have hu : IsUnit b₁ := isCoprime_zero_left.mp (h₀ ▸ hB)
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha₀)) hu.ne_zero)
      (by simpa only [frobeniusEliminant, h₀, zero_mul, zero_add] using hz)
  have hb₁ : b₁ ≠ 0 := by
    intro h₁
    have hu : IsUnit b₀ := isCoprime_zero_left.mp (h₁ ▸ hB.symm)
    exact (mul_ne_zero hu.ne_zero (pow_ne_zero _ ha₁))
      (by simpa only [frobeniusEliminant, h₁, mul_zero, add_zero] using hz)
  have hcop : IsCoprime (a₁ ^ p) ((-a₀) ^ p) := (hA.symm.neg_right).pow
  have hdiv₁ : a₁ ^ p ∣ b₁ := by
    apply hcop.dvd_of_dvd_mul_left
    refine ⟨-b₀, ?_⟩
    have h := eq_neg_of_add_eq_zero_right hz
    rw [h]
    ring
  have hdiv₀ : (-a₀) ^ p ∣ b₀ := by
    apply hcop.symm.dvd_of_dvd_mul_left
    refine ⟨-b₁, ?_⟩
    have h := eq_neg_of_add_eq_zero_left hz
    rw [mul_comm (a₁ ^ p), h]
    ring
  have hd₀ := Polynomial.natDegree_le_of_dvd hdiv₀ hb₀
  have hd₁ := Polynomial.natDegree_le_of_dvd hdiv₁ hb₁
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg] at hd₀
  rw [Polynomial.natDegree_pow] at hd₁
  have hsub₀ : a₀.natDegree = 0 := by
    by_contra h
    exact (not_lt_of_ge ((by simpa using Nat.mul_le_mul_left p (Nat.pos_of_ne_zero h) :
      p ≤ p * a₀.natDegree).trans (hd₀.trans (le_max_left _ _)))) hsmall
  have hsub₁ : a₁.natDegree = 0 := by
    by_contra h
    exact (not_lt_of_ge ((by simpa using Nat.mul_le_mul_left p (Nat.pos_of_ne_zero h) :
      p ≤ p * a₁.natDegree).trans (hd₁.trans (le_max_right _ _)))) hsmall
  simp [hsub₀, hsub₁] at hpos

private theorem common_root_of_not_relPrime (A B : Polynomial K) (hA : A ≠ 0)
    (hbad : ¬ IsRelPrime A B) :
    ∃ x : AlgebraicClosure K,
      A.eval₂ (algebraMap K (AlgebraicClosure K)) x = 0 ∧
      B.eval₂ (algebraMap K (AlgebraicClosure K)) x = 0 := by
  classical
  change ¬ ∀ D : Polynomial K, D ∣ A → D ∣ B → IsUnit D at hbad
  push Not at hbad
  obtain ⟨D, hDA, hDB, hunit⟩ := hbad
  obtain ⟨U, hU⟩ := hDA
  obtain ⟨V, hV⟩ := hDB
  have hd : D ≠ 0 := by
    intro hz
    exact hA (by rw [hU, hz, zero_mul])
  have hdegree : 0 < D.natDegree := Nat.pos_of_ne_zero fun h =>
    hunit (isUnit_of_natDegree_zero_ne_zero h hd)
  let c := algebraMap K (AlgebraicClosure K)
  have hmap : 0 < (D.map c).natDegree := by rwa [Polynomial.natDegree_map_eq_of_injective c.injective]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (D.map c)
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hmap))
  have hroot : D.eval₂ c x = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  exact ⟨x, by rw [hU, Polynomial.eval₂_mul, hroot, zero_mul],
    by rw [hV, Polynomial.eval₂_mul, hroot, zero_mul]⟩

theorem noncoprime_affine_seeds_card_le (a₀ a₁ b₀ b₁ : Polynomial K) (p : ℕ)
    (hA : IsCoprime a₀ a₁) (hB : IsCoprime b₀ b₁)
    (hsmall : max b₀.natDegree b₁.natDegree < p) (seeds : Finset K)
    (hne : ∀ g ∈ seeds, affineDenominator a₀ a₁ g ≠ 0)
    (hbad : ∀ g ∈ seeds,
      ¬ IsRelPrime (affineDenominator a₀ a₁ g) (affineDenominator b₀ b₁ (g ^ p))) :
    seeds.card ≤ p * max a₀.natDegree a₁.natDegree + max b₀.natDegree b₁.natDegree := by
  classical
  by_cases hpos : 0 < max a₀.natDegree a₁.natDegree
  · let c := algebraMap K (AlgebraicClosure K)
    let H := frobeniusEliminant a₀ a₁ b₀ b₁ p
    have hH : H ≠ 0 := frobeniusEliminant_ne_zero _ _ _ _ p hA hB hpos hsmall
    have hpoints (g : ↥seeds) : ∃ x : AlgebraicClosure K,
        (affineDenominator a₀ a₁ g.1).eval₂ c x = 0 ∧
        (affineDenominator b₀ b₁ (g.1 ^ p)).eval₂ c x = 0 :=
      common_root_of_not_relPrime _ _ (hne g.1 g.2) (hbad g.1 g.2)
    choose point hpoint using hpoints
    have hinj : Function.Injective point := by
      intro g h he
      apply Subtype.ext
      exact seed_eq_of_common_root c a₀ a₁ hA _ _ (point g) (hpoint g).1
        (he.symm ▸ (hpoint h).1)
    have hz (g : ↥seeds) : (H.map c).eval (point g) = 0 := by
      rw [Polynomial.eval_map]
      have ha := (affine_at_common_root c a₀ a₁ hA _ (point g) (hpoint g).1).1
      have hb := (affine_at_common_root c b₀ b₁ hB _ (point g) (hpoint g).2).1
      simp only [H, frobeniusEliminant, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_neg, ha, hb, map_pow, neg_neg, mul_pow]
      ring
    let roots := seeds.attach.image point
    have hcard : roots.card = seeds.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    have hHmap : H.map c ≠ 0 := fun h => hH (Polynomial.map_injective c c.injective
      (by simpa only [Polynomial.map_zero] using h))
    rw [← hcard]
    refine (Polynomial.card_le_degree_of_subset_roots (p := H.map c) ?_).trans ?_
    · intro x hx
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp (show x ∈ roots from hx)
      exact (Polynomial.mem_roots hHmap).mpr (hz g)
    · rw [Polynomial.natDegree_map_eq_of_injective c.injective]
      exact frobeniusEliminant_natDegree_le _ _ _ _ p
  · have hzero : seeds.card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hdeg : (affineDenominator a₀ a₁ g).natDegree = 0 := by
        apply Nat.eq_zero_of_le_zero
        unfold affineDenominator
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (by omega) ((Polynomial.natDegree_C_mul_le _ _).trans (by omega)))
      have hu := isUnit_of_natDegree_zero_ne_zero hdeg (hne g hg)
      exact hbad g hg (fun _ hh _ => isUnit_of_dvd_unit hh hu)
    simp [hzero]

theorem exists_retained_affine_seeds {I : Type*} (nodes : Finset I) (x : I → K)
    (a₀ a₁ b₀ b₁ : Polynomial K) (p delta : ℕ)
    (hA : IsCoprime a₀ a₁) (hB : IsCoprime b₀ b₁)
    (ha : max a₀.natDegree a₁.natDegree ≤ delta)
    (hb : max b₀.natDegree b₁.natDegree ≤ delta) (hdelta : delta < p)
    (seeds : Finset K) :
    ∃ retained ⊆ seeds,
      seeds.card ≤ retained.card + (nodes.card + 1 + (p + 1) * delta) ∧
      ∀ g ∈ retained, affineDenominator a₀ a₁ g ≠ 0 ∧
        IsRelPrime (affineDenominator a₀ a₁ g) (affineDenominator b₀ b₁ (g ^ p)) ∧
        ∀ i ∈ nodes, (affineDenominator a₀ a₁ g).eval (x i) ≠ 0 := by
  classical
  let valid (g : K) := affineDenominator a₀ a₁ g ≠ 0 ∧
    IsRelPrime (affineDenominator a₀ a₁ g) (affineDenominator b₀ b₁ (g ^ p)) ∧
    ∀ i ∈ nodes, (affineDenominator a₀ a₁ g).eval (x i) ≠ 0
  let retained := seeds.filter valid
  let bad := seeds.filter fun g => ¬ valid g
  let zeros := seeds.filter fun g => affineDenominator a₀ a₁ g = 0
  let noncoprime := seeds.filter fun g => affineDenominator a₀ a₁ g ≠ 0 ∧
    ¬ IsRelPrime (affineDenominator a₀ a₁ g) (affineDenominator b₀ b₁ (g ^ p))
  let poles := seeds.filter fun g => ∃ i ∈ nodes, (affineDenominator a₀ a₁ g).eval (x i) = 0
  have hz : zeros.card ≤ 1 := zero_affine_denominator_seeds_card_le a₀ a₁ hA _
    (fun _ hg => (Finset.mem_filter.mp hg).2)
  have hc : noncoprime.card ≤ (p + 1) * delta := by
    have hc' := noncoprime_affine_seeds_card_le a₀ a₁ b₀ b₁ p hA hB (hb.trans_lt hdelta)
      noncoprime (fun _ hg => (Finset.mem_filter.mp hg).2.1)
      (fun _ hg => (Finset.mem_filter.mp hg).2.2)
    rw [Nat.add_mul, Nat.one_mul]
    exact hc'.trans (Nat.add_le_add (Nat.mul_le_mul_left p ha) hb)
  have hpole : poles.card ≤ nodes.card := node_pole_seeds_card_le nodes x a₀ a₁ hA poles
    (fun _ hg => (Finset.mem_filter.mp hg).2)
  have hcover : bad ⊆ zeros ∪ noncoprime ∪ poles := by
    intro g hg
    obtain ⟨hseed, hnot⟩ := Finset.mem_filter.mp hg
    by_cases hzero : affineDenominator a₀ a₁ g = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hseed, hzero⟩))
    by_cases hcop : IsRelPrime (affineDenominator a₀ a₁ g) (affineDenominator b₀ b₁ (g ^ p))
    · have hp : ¬ ∀ i ∈ nodes, (affineDenominator a₀ a₁ g).eval (x i) ≠ 0 :=
        fun h => hnot ⟨hzero, hcop, h⟩
      push Not at hp
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hseed, hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hseed, hzero, hcop⟩))
  have hbound : bad.card ≤ nodes.card + 1 + (p + 1) * delta := by
    have h := (Finset.card_le_card hcover).trans (Finset.card_union_le (zeros ∪ noncoprime) poles)
    have hu := Finset.card_union_le zeros noncoprime
    omega
  have hsplit : retained.card + bad.card = seeds.card := Finset.card_filter_add_card_filter_not _
  exact ⟨retained, Finset.filter_subset _ _, by omega, fun _ hg => (Finset.mem_filter.mp hg).2⟩

end

end ProximityPrize.SubmissionLower.Koala6831Moving
