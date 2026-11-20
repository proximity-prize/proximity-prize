import ProximityPrize.SubmissionLower.Koala6844NormalizationSeparation


section NormalizationPreludePart0

namespace ProximityPrize.SubmissionLower.Koala6844Moving

noncomputable section

variable {K : Type*} [CommRing K]

abbrev P4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

structure FlowData (K : Type*) [CommRing K] where
  d0 : Polynomial K
  a0 : Polynomial K
  a1 : Polynomial K
  c0 : Polynomial K
  c1 : Polynomial K

def liftX (f : Polynomial K) : P4 K :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 4) : P4 K) f

def affine (f0 f1 : Polynomial K) : P4 K :=
  liftX f0 + MvPolynomial.X (3 : Fin 4) * liftX f1

namespace FlowData

variable (B : FlowData K)

def A : P4 K := affine B.a0 B.a1

def AX : P4 K := affine B.a0.derivative B.a1.derivative

def C : P4 K := affine B.c0 B.c1


def minor : P4 K :=
  liftX B.a1 * liftX B.c0 - liftX B.a0 * liftX B.c1

def minorX : P4 K :=
  liftX B.a1.derivative * liftX B.c0 + liftX B.a1 * liftX B.c0.derivative -
    (liftX B.a0.derivative * liftX B.c1 + liftX B.a0 * liftX B.c1.derivative)

def denominator : P4 K := liftX B.d0 * B.A

def denominatorX : P4 K :=
  liftX B.d0.derivative * B.A + liftX B.d0 * B.AX

def yCoefficient : P4 K :=
  B.A * (liftX B.d0)^2 * liftX B.a1 * MvPolynomial.X (1 : Fin 4) + B.denominator * B.minor

def rCoefficient : P4 K :=
  (liftX B.d0)^2 * (liftX B.a1.derivative * B.A - liftX B.a1 * B.AX) *
      MvPolynomial.X (1 : Fin 4) +
    B.A * (liftX B.d0)^2 * liftX B.a1 * MvPolynomial.X (2 : Fin 4) +
    B.denominator * B.minorX - B.denominatorX * B.minor

def flow : Derivation K (P4 K) (P4 K) :=
  B.denominator^2 • MvPolynomial.pderiv (3 : Fin 4) +
    B.yCoefficient • MvPolynomial.pderiv (1 : Fin 4) +
    B.rCoefficient • MvPolynomial.pderiv (2 : Fin 4)

theorem flow_apply (P : P4 K) :
    B.flow P =
      B.denominator^2 * MvPolynomial.pderiv (3 : Fin 4) P +
        B.yCoefficient * MvPolynomial.pderiv (1 : Fin 4) P +
        B.rCoefficient * MvPolynomial.pderiv (2 : Fin 4) P := by
  simp only [flow, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

theorem flow_X : B.flow (MvPolynomial.X (0 : Fin 4)) = 0 := by
  simp [flow_apply, MvPolynomial.pderiv_X]

theorem flow_Y : B.flow (MvPolynomial.X (1 : Fin 4)) = B.yCoefficient := by
  simp [flow_apply, MvPolynomial.pderiv_X]


theorem flow_Z : B.flow (MvPolynomial.X (3 : Fin 4)) = B.denominator^2 := by
  simp [flow_apply, MvPolynomial.pderiv_X]

theorem flow_liftX (f : Polynomial K) : B.flow (liftX f) = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp only [liftX, map_add] at hf hg ⊢
    rw [hf, hg, add_zero]
  | monomial n a =>
    simp only [liftX, Polynomial.aeval_monomial, Derivation.leibniz,
      Derivation.leibniz_pow, Derivation.map_algebraMap, flow_X, smul_zero, add_zero]

theorem flow_affine (f0 f1 : Polynomial K) :
    B.flow (affine f0 f1) = B.denominator^2 * liftX f1 := by
  simp only [affine, map_add, RCN347.leibniz_product, flow_liftX, flow_Z,
    mul_zero, add_zero, zero_add]

def numerator : P4 K := liftX B.d0 * MvPolynomial.X (1 : Fin 4) + B.C




end FlowData

section ExtractPartner

variable {R : Type*} [CommRing R] [Algebra K R]
variable [UniqueFactorizationMonoid R]

theorem isRelPrime_iterate_factor_product
    (D : Derivation K R R) {F S : R} {j : ℕ}
    (hF : Irreducible F) (hS : ¬F ∣ S) (htrans : ¬F ∣ D F)
    (hfactorial : IsUnit (j.factorial : R)) :
    IsRelPrime F ((D : R → R)^[j] (F^j * S)) := by
  obtain ⟨T, hT⟩ := RCN324.iterate_pow_mul_expansion D F S j j le_rfl
  simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, zero_add, pow_one] at hT
  apply hF.isRelPrime_iff_not_dvd.mpr
  intro hd
  rw [hT] at hd
  have hlead := dvd_sub hd (dvd_mul_right F T)
  rw [add_sub_cancel_right] at hlead
  rcases hF.prime.dvd_or_dvd hlead with hprod | hpower
  · rcases hF.prime.dvd_or_dvd hprod with hconst | hsource
    · exact (not_isUnit_of_not_isUnit_dvd hF.not_isUnit hconst) hfactorial
    · exact hS hsource
  · exact htrans (hF.prime.dvd_of_dvd_pow hpower)

end ExtractPartner

theorem flow_partner_of_lt_characteristic
    {L : Type*} [Field L] {p j : ℕ} [CharP L p]
    (B : FlowData L) {F S : P4 L}
    (hF : Irreducible F) (hS : ¬F ∣ S) (htrans : ¬F ∣ B.flow F)
    (hj : j < p) : IsRelPrime F ((B.flow : P4 L → P4 L)^[j] (F^j * S)) := by
  apply isRelPrime_iterate_factor_product B.flow hF hS htrans
  have hne : (j.factorial : L) ≠ 0 :=
    RCN347.factorial_cast_ne_zero_below_characteristic p j hj
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hne).map (algebraMap L (P4 L))

end

end ProximityPrize.SubmissionLower.Koala6844Moving
end NormalizationPreludePart0

section NormalizationPreludePart1


namespace ProximityPrize.SubmissionLower.Koala6844Moving

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

theorem common_root_of_not_relPrime (A B : Polynomial K) (hA : A ≠ 0)
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

end ProximityPrize.SubmissionLower.Koala6844Moving
end NormalizationPreludePart1

section NormalizationPreludePart2

namespace ProximityPrize.SubmissionLower.Koala6844Moving

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

def FlowData.seedDenominator (B : FlowData K) (g : K) : Polynomial K :=
  B.a0 + Polynomial.C g * B.a1

def FlowData.seedOffset (B : FlowData K) (g : K) : Polynomial K :=
  B.c0 + Polynomial.C g * B.c1

theorem FlowData.exists_normalized_selected_word (B : FlowData K)
    (g : K) (P otherDen otherNumerator : Polynomial K) (w δ : ℕ)
    (hdegree : P.natDegree ≤ w) (hcontent : B.d0.natDegree ≤ δ)
    (hc₀ : B.c0.natDegree ≤ w + δ) (hc₁ : B.c1.natDegree ≤ w + δ)
    (hcoprime : IsRelPrime (B.seedDenominator g) otherDen)
    (hcompat : B.seedDenominator g * otherNumerator =
      otherDen * (B.d0 * P + B.seedOffset g)) :
    ∃ Q : Polynomial K, Q.natDegree ≤ w + δ ∧
      B.d0 * P + B.seedOffset g = B.seedDenominator g * Q := by
  let numerator := B.d0 * P + B.seedOffset g
  have hdiv : B.seedDenominator g ∣ numerator :=
    hcoprime.dvd_of_dvd_mul_left ⟨otherNumerator, hcompat.symm⟩
  have hNum : numerator.natDegree ≤ w + δ := by
    unfold numerator FlowData.seedOffset
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simpa only [Nat.add_comm δ w] using Polynomial.natDegree_mul_le_of_le hcontent hdegree
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le hc₀
        ((Polynomial.natDegree_C_mul_le _ _).trans hc₁))
  by_cases hnum : numerator = 0
  · exact ⟨0, by simp, hnum.trans (mul_zero _).symm⟩
  · obtain ⟨Q, hQ⟩ := hdiv
    have hdivQ : Q ∣ numerator := ⟨B.seedDenominator g, hQ.trans (mul_comm _ _)⟩
    exact ⟨Q, (Polynomial.natDegree_le_of_dvd hdivQ hnum).trans hNum, hQ⟩

theorem FlowData.normalized_agrees_at (B : FlowData K) (P Q : Polynomial K)
    (x g u₀ u₁ normalized : K)
    (hP : P.eval x = u₀ + g * u₁)
    (h₀ : B.d0.eval x * u₀ + B.c0.eval x = B.a0.eval x * normalized)
    (h₁ : B.d0.eval x * u₁ + B.c1.eval x = B.a1.eval x * normalized)
    (hden : (B.seedDenominator g).eval x ≠ 0)
    (hQ : B.d0 * P + B.seedOffset g = B.seedDenominator g * Q) :
    Q.eval x = normalized := by
  apply mul_left_cancel₀ hden
  have heval := congrArg (Polynomial.eval x) hQ
  simp only [FlowData.seedOffset, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, hP] at heval
  rw [← heval]
  simp only [FlowData.seedDenominator, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination h₀ + g * h₁



end

end ProximityPrize.SubmissionLower.Koala6844Moving
end NormalizationPreludePart2

section NormalizationPreludePart3

namespace ProximityPrize.SubmissionLower.Koala6844Moving

open Koala6844Comparison (SymbolicRow primitiveSelected)
open Koala6844Separation (NormalForm Seeds pairDegree regroup regroup_C regroup_X)
open Koala6844BivariateSeeds (coordinates)

noncomputable section

variable {K I : Type*} [Field K]

private theorem evaluate_seed_regroup (v : Fin 2 → K) (P : Polynomial (Seeds K)) :
    MvPolynomial.eval (Polynomial.C ∘ v) (regroup P) = P.map (MvPolynomial.eval v) := by
  have hcoeff : (MvPolynomial.eval (Polynomial.C ∘ v)).comp (MvPolynomial.map Polynomial.C) =
      (Polynomial.C : K →+* Polynomial K).comp (MvPolynomial.eval v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval_X, Function.comp_apply]
  have h : (MvPolynomial.eval (Polynomial.C ∘ v)).comp regroup =
      Polynomial.mapRingHom (MvPolynomial.eval v) := by
    apply Polynomial.ringHom_ext
    · intro a
      change MvPolynomial.eval (Polynomial.C ∘ v) (regroup (Polynomial.C a)) =
        (Polynomial.C a).map (MvPolynomial.eval v)
      rw [regroup_C, Polynomial.map_C]
      exact DFunLike.congr_fun hcoeff a
    · change MvPolynomial.eval (Polynomial.C ∘ v) (regroup (Polynomial.X : Polynomial (Seeds K))) =
        (Polynomial.X : Polynomial (Seeds K)).map (MvPolynomial.eval v)
      rw [regroup_X, MvPolynomial.eval_C, Polynomial.map_X]
  exact DFunLike.congr_fun h P

def leftFlowData {q : SymbolicRow (Seeds K)} {w delta : ℕ} (N : NormalForm q w delta) :
    FlowData K := ⟨N.d₀, N.A 0, N.A 1, N.C 0, N.C 1⟩

theorem normalForm_specialized_compatibility {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (sigma : K →+* K) (p : ℕ)
    (selected : K → Polynomial K) (g : K)
    (hz : primitiveSelected sigma p q selected g = 0) :
    affineDenominator (N.A 0) (N.A 1) g *
      (N.d₁ * (selected g).map sigma - affineDenominator (N.D 0) (N.D 1) (g ^ p)) =
    affineDenominator (N.B 0) (N.B 1) (g ^ p) *
      (N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g) := by
  let v := coordinates g (g ^ p)
  let evaluate := MvPolynomial.eval (Polynomial.C ∘ v)
  have hβ := congrArg evaluate N.beta_eq
  have hfirst := congrArg evaluate N.first_eq
  have hsecond := congrArg evaluate N.second_eq
  have hzero : q.beta.map (MvPolynomial.eval v) + q.first.map (MvPolynomial.eval v) * selected g +
      q.second.map (MvPolynomial.eval v) * (selected g).map sigma = 0 := hz
  rw [← evaluate_seed_regroup v q.beta, ← evaluate_seed_regroup v q.first,
    ← evaluate_seed_regroup v q.second] at hzero
  change evaluate (regroup q.beta) + evaluate (regroup q.first) * selected g +
    evaluate (regroup q.second) * (selected g).map sigma = 0 at hzero
  rw [hβ, hfirst, hsecond] at hzero
  simp only [evaluate, Koala6844SeparationFactors.affine, map_add, map_mul, map_neg,
    MvPolynomial.eval_C, MvPolynomial.eval_X,
    Function.comp_apply, v, coordinates, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at hzero
  unfold affineDenominator
  linear_combination -hzero

theorem normalForm_exists_retained_normalized_words {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (sigma : K →+* K) (p : ℕ) (hdelta : delta < p)
    (nodes : Finset I) (x : I → K) (u₀ u₁ : I → K)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (x i)) (Koala6844SeparationFactors.affine 0 (u₀ i) (u₁ i))
        (Koala6844SeparationFactors.affine 1 (sigma (u₀ i)) (sigma (u₁ i))) = 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hselected : ∀ g ∈ seeds, primitiveSelected sigma p q selected g = 0) :
    ∃ retained ⊆ seeds,
      seeds.card ≤ retained.card + (nodes.card + 1 + (p + 1) * delta) ∧
      ∃ fixed : I → K, ∃ normalized : K → Polynomial K,
        (∀ i ∈ nodes,
          (∀ j : Fin 2, N.d₀.eval (x i) * (![u₀ i, u₁ i] : Fin 2 → K) j +
            (N.C j).eval (x i) = fixed i * (N.A j).eval (x i)) ∧
          ∀ j : Fin 2, N.d₁.eval (x i) * sigma ((![u₀ i, u₁ i] : Fin 2 → K) j) -
            (N.D j).eval (x i) = fixed i * (N.B j).eval (x i)) ∧
        ∀ g ∈ retained, affineDenominator (N.A 0) (N.A 1) g ≠ 0 ∧
          (normalized g).natDegree ≤ w + delta ∧
          N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g =
            affineDenominator (N.A 0) (N.A 1) g * normalized g ∧
          N.d₁ * (selected g).map sigma - affineDenominator (N.D 0) (N.D 1) (g ^ p) =
            affineDenominator (N.B 0) (N.B 1) (g ^ p) * normalized g ∧
          (∀ i ∈ nodes, (affineDenominator (N.A 0) (N.A 1) g).eval (x i) ≠ 0) ∧
          ∀ i ∈ nodes, (selected g).eval (x i) = u₀ i + g * u₁ i →
            (normalized g).eval (x i) = fixed i := by
  classical
  obtain ⟨retained, hsub, hcard, hden⟩ := exists_retained_affine_seeds nodes x
    (N.A 0) (N.A 1) (N.B 0) (N.B 1) p delta N.A_coprime N.B_coprime
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.second_degree))
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.first_degree)) hdelta seeds
  let B := leftFlowData N
  have hex (g : ↥retained) : ∃ poly : Polynomial K, poly.natDegree ≤ w + delta ∧
      N.d₀ * selected g.1 + affineDenominator (N.C 0) (N.C 1) g.1 =
        affineDenominator (N.A 0) (N.A 1) g.1 * poly := by
    exact B.exists_normalized_selected_word g.1 (selected g.1)
      (affineDenominator (N.B 0) (N.B 1) (g.1 ^ p))
      (N.d₁ * (selected g.1).map sigma - affineDenominator (N.D 0) (N.D 1) (g.1 ^ p)) w delta
      (hdegree g.1 (hsub g.2)) (Nat.le_of_add_right_le N.first_degree)
      (le_max_left _ _ |>.trans (Nat.le_of_add_left_le N.left_degree))
      (le_max_right _ _ |>.trans (Nat.le_of_add_left_le N.left_degree))
      (hden g.1 g.2).2.1
      (normalForm_specialized_compatibility N sigma p selected g.1 (hselected g.1 (hsub g.2)))
  choose chosen hnormDegree hnormIdentity using hex
  let normalized (g : K) : Polynomial K := if hg : g ∈ retained then chosen ⟨g, hg⟩ else 0
  have hfixed (i : ↥nodes) : ∃ u : K,
      (∀ j : Fin 2, N.d₀.eval (x i.1) * (![u₀ i.1, u₁ i.1] : Fin 2 → K) j +
        (N.C j).eval (x i.1) = u * (N.A j).eval (x i.1)) ∧
      ∀ j : Fin 2, N.d₁.eval (x i.1) * sigma ((![u₀ i.1, u₁ i.1] : Fin 2 → K) j) -
        (N.D j).eval (x i.1) = u * (N.B j).eval (x i.1) := by
    let received : Fin 2 → K := ![u₀ i.1, u₁ i.1]
    exact N.fixedWord (x i.1) received (sigma ∘ received) (hgood i.1 i.2)
  choose chosenValue hvalues using hfixed
  let fixed (i : I) : K := if hi : i ∈ nodes then chosenValue ⟨i, hi⟩ else 0
  have hf i (hi : i ∈ nodes) := hvalues ⟨i, hi⟩
  refine ⟨retained, hsub, hcard, fixed, normalized, ?_, ?_⟩
  · intro i hi
    simpa only [fixed, dif_pos hi] using hf i hi
  · intro g hg
    have hnorm : N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g =
        affineDenominator (N.A 0) (N.A 1) g * normalized g := by
      simpa only [normalized, dif_pos hg] using hnormIdentity ⟨g, hg⟩
    have hden0 := (hden g hg).1
    have hnormRight : N.d₁ * (selected g).map sigma -
        affineDenominator (N.D 0) (N.D 1) (g ^ p) =
        affineDenominator (N.B 0) (N.B 1) (g ^ p) * normalized g := by
      apply mul_left_cancel₀ hden0
      rw [normalForm_specialized_compatibility N sigma p selected g (hselected g (hsub hg)), hnorm]
      ring
    refine ⟨hden0, by simpa only [normalized, dif_pos hg] using hnormDegree ⟨g, hg⟩,
      hnorm, hnormRight, (hden g hg).2.2, ?_⟩
    intro i hi hagree
    have hvalue := hf i hi
    exact B.normalized_agrees_at (selected g) (normalized g) (x i) g (u₀ i) (u₁ i) (fixed i)
      hagree (by simpa [B, leftFlowData, fixed, hi, mul_comm] using hvalue.1 0)
      (by simpa [B, leftFlowData, fixed, hi, mul_comm] using hvalue.1 1) ((hden g hg).2.2 i hi) hnorm

end

end ProximityPrize.SubmissionLower.Koala6844Moving
end NormalizationPreludePart3

namespace ProximityPrize.SubmissionLower.Koala6844Moving

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

theorem noncoprime_fixed_content_card_le (a0 a1 d : Polynomial K)
    (hA : IsCoprime a0 a1) (hd : d ≠ 0) (seeds : Finset K)
    (hbad : ∀ g ∈ seeds, ¬ IsCoprime (affineDenominator a0 a1 g) d) :
    seeds.card ≤ d.natDegree := by
  classical
  let c := algebraMap K (AlgebraicClosure K)
  have hx (g : ↥seeds) : ∃ x : AlgebraicClosure K,
      d.eval₂ c x = 0 ∧ (affineDenominator a0 a1 g.1).eval₂ c x = 0 := by
    apply common_root_of_not_relPrime _ _ hd
    intro h
    exact hbad g.1 g.2 h.isCoprime.symm
  choose point hpoint using hx
  have hinj : Function.Injective point := by
    intro g h he
    apply Subtype.ext
    exact seed_eq_of_common_root c a0 a1 hA _ _ (point g) (hpoint g).2
      (he.symm ▸ (hpoint h).2)
  let roots := seeds.attach.image point
  have hcard : roots.card = seeds.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hdmap : d.map c ≠ 0 := (Polynomial.map_ne_zero_iff c.injective).2 hd
  rw [← hcard, ← natDegree_map_eq_of_injective c.injective d]
  apply card_le_degree_of_subset_roots
  intro x hx'
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp (show x ∈ roots from hx')
  apply (mem_roots hdmap).mpr
  change (d.map c).eval (point g) = 0
  rw [eval_map]
  exact (hpoint g).1

end

end ProximityPrize.SubmissionLower.Koala6844Moving
