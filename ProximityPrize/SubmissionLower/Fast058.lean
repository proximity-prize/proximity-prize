import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast054
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option Elab.async false
end K1_13_1_1
end
section
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_1
noncomputable section
open K1_13_6_3_6 (quotientMul quotientMul_injective quotientMul_exact)
section Quotients
variable {k R : Type} [Field k] [CommRing R] [Algebra k R]
abbrev cut (I : Ideal R) (q : R) : Ideal R := I ⊔ Ideal.span {q}
theorem cut_mono_pow (I : Ideal R) (q : R) {m n : ℕ} (hle : m ≤ n) :
    cut I (q ^ n) ≤ cut I (q ^ m) :=
  sup_le_sup_left
    ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr (pow_dvd_pow q hle))) _
private theorem cut_colon (I : Ideal R) (q : R) (hI : I.IsPrime) (hq : q ∉ I) (n : ℕ) :
    (cut I (q ^ (n + 1))).colon {q} = cut I (q ^ n) := by
  ext x
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  change x * q ∈ I ⊔ Ideal.span {q ^ (n + 1)} ↔ x ∈ I ⊔ Ideal.span {q ^ n}
  constructor
  · intro hx
    obtain ⟨r, hr, s, hs, heq⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hs
    have hprod : (x - q ^ n * y) * q ∈ I := by
      rw [sub_mul, mul_right_comm (q ^ n) y q, ← pow_succ, ← heq, add_sub_cancel_right]
      exact hr
    exact Submodule.mem_sup.mpr ⟨x - q ^ n * y, (hI.mem_or_mem hprod).resolve_right hq,
      q ^ n * y, Ideal.mem_span_singleton.mpr ⟨y, rfl⟩, sub_add_cancel _ _⟩
  · intro hx
    obtain ⟨r, hr, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hs
    refine Submodule.mem_sup.mpr ⟨r * q, I.mul_mem_right _ hr,
      q ^ (n + 1) * y, Ideal.mem_span_singleton.mpr ⟨y, rfl⟩, ?_⟩
    rw [add_mul, pow_succ]
    ring
private theorem sup_span_cut_pow (I : Ideal R) (q : R) (n : ℕ) :
    cut (cut I (q ^ (n + 1))) q = cut I q := by
  refine le_antisymm (sup_le ?_ le_sup_right) ?_
  · simpa only [pow_one] using cut_mono_pow I q (m := 1) (Nat.succ_le_succ (Nat.zero_le n))
  · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
theorem finrank_cut_pow (I : Ideal R) (q : R) (hI : I.IsPrime) (hq : q ∉ I)
    (hfinite : ∀ n : ℕ, Module.Finite k (R ⧸ cut I (q ^ n))) (n : ℕ) :
    Module.finrank k (R ⧸ cut I (q ^ n)) = n * Module.finrank k (R ⧸ cut I q) := by
  induction n with
  | zero =>
    have htop : cut I (q ^ 0) = ⊤ := by simp [Ideal.span_singleton_one]
    rw [htop, Nat.zero_mul]
    exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
    let J := cut I (q ^ (n + 1))
    let f := (quotientMul J q).restrictScalars k
    let g := (Submodule.factor (le_sup_left : J ≤ cut J q)).restrictScalars k
    have hf : Function.Injective f := quotientMul_injective J q
    have hg : Function.Surjective g :=
      Submodule.factor_surjective (le_sup_left : J ≤ cut J q)
    have hex : Function.Exact f g := quotientMul_exact J q
    have : Module.Finite k (R ⧸ J) := hfinite (n + 1)
    have h := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hg, finrank_top, LinearMap.exact_iff.mp hex,
      LinearMap.finrank_range_of_inj hf] at h
    change Module.finrank k (R ⧸ cut J q) +
      Module.finrank k (R ⧸ J.colon {q}) = Module.finrank k (R ⧸ J) at h
    dsimp only [J] at h
    rw [sup_span_cut_pow, cut_colon I q hI hq n, ih] at h
    rw [← h, Nat.succ_mul, Nat.add_comm]
theorem sum_finrank_le_of_coprime {ι : Type*} [Fintype ι] (J : Ideal R)
    (I : ι → Ideal R) (hle : ∀ i, J ≤ I i)
    (hcop : Pairwise (fun i j => IsCoprime (I i) (I j))) [Module.Finite k (R ⧸ J)] :
    (∑ i, Module.finrank k (R ⧸ I i)) ≤ Module.finrank k (R ⧸ J) := by
  let f (i : ι) : (R ⧸ J) →ₗ[k] (R ⧸ I i) :=
    (Submodule.factor (hle i)).restrictScalars k
  have hsurj : Function.Surjective (LinearMap.pi f) := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop y
    exact ⟨Ideal.Quotient.mk J r, funext hr⟩
  have (i : ι) : Module.Finite k (R ⧸ I i) :=
    Module.Finite.of_surjective (f i) (Submodule.factor_surjective (hle i))
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hsurj
end Quotients
end
end K1_13_6_1_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_7_1
open MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (J : Ideal GeoJets) (h : Shape),
    J.IsPrime → FullChamber h →
    (affineHilbertPolynomial (sliceIdeal J h)).natDegree ≤
      (affineHilbertPolynomial J).natDegree - 1 ∧
    (sliceIdeal J h = ⊤ ∨
      (sliceIdeal J h).IsPrime ∧ (sliceIdeal J h).comap (sliceMap h) = J)
def c2 : Prop :=
  ∀ (k : Type) [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (Q : MvPolynomial (Fin 4) k) (a : Shape),
    I.IsPrime → (affineHilbertPolynomial I).natDegree ≤ 1 →
    FullChamber a → Q ∉ I → FitsBox Q a →
    Module.finrank k (MvPolynomial (Fin 4) k ⧸ (I ⊔ Ideal.span {Q})) ≤
      genericCutLength I a
private theorem krullDim_of_polynomial_normalization {k R : Type*} [Field k]
    [CommRing R] [IsDomain R] {d : ℕ} [Algebra (MvPolynomial (Fin d) k) R]
    [FaithfulSMul (MvPolynomial (Fin d) k) R] [Module.Finite (MvPolynomial (Fin d) k) R] :
    ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hd⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ :=
      Algebra.IsIntegral.comap_surjective B R (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hd.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
private theorem krullDim_of_finite_hom {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* R) (hg : Function.Injective g)
    (hgfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul (MvPolynomial (Fin d) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let finite : Module.Finite (MvPolynomial (Fin d) k) R := hgfin
  exact @krullDim_of_polynomial_normalization k R _ _ _ d algebra faithful finite
private theorem dimension_eq_hilbert {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hH := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
  rw [Nat.card_fin] at hH
  rw [hH]
  exact krullDim_of_finite_hom g.toRingHom hg hgfin
private theorem slice_mono (h : Shape) {J K : Ideal GeoJets} (hle : J ≤ K) :
    sliceIdeal J h ≤ sliceIdeal K h :=
  sup_le_sup_right (Ideal.map_mono hle) _
private theorem scaled_power_fits {P : GeoJets} {a h : Shape} (hfit : GeoFits P a) :
    FitsBox ((sliceMap h P) ^ 6) (a.scale 6) := by
  have hs := support_map_of_injective P (algebraMap GeoField (SectionField h)).injective
  obtain ⟨hb, hj, ht⟩ := hfit
  change (sliceMap h P).support = P.support at hs
  have hb' : (sliceMap h P).totalDegree ≤ a.b := by
    rwa [totalDegree, hs, ← totalDegree]
  have hj' : (sliceMap h P).weightedTotalDegree Fin.val ≤ a.j := by
    rwa [weightedTotalDegree, hs, ← weightedTotalDegree]
  have ht' : (sliceMap h P).degreeOf 3 ≤ a.t := by
    rwa [degreeOf_eq_sup, hs, ← degreeOf_eq_sup]
  exact ⟨(totalDegree_pow _ _).trans (Nat.mul_le_mul_left 6 hb'),
    (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left 6 hj'),
    (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left 6 ht')⟩
private theorem sliced_components_coprime (hslice : c1) {surface : Ideal GeoJets}
    {P : GeoJets} (hs : surface.IsPrime) (hdim : (affineHilbertPolynomial surface).natDegree = 2)
    (hP : P ∉ surface) {h : Shape} (hh : FullChamber h) :
    Pairwise (fun C D : (cut surface P).minimalPrimesFinset =>
      IsCoprime (sliceIdeal C h) (sliceIdeal D h)) := by
  have := hs
  have data (C : (cut surface P).minimalPrimesFinset) :
      sliceIdeal C h = ⊤ ∨ ((sliceIdeal C h).IsMaximal ∧
        (sliceIdeal C h).comap (sliceMap h) = (C : Ideal GeoJets)) := by
    have hC := Ideal.mem_minimalPrimesFinset.mp C.2
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
    rw [hdim] at hd
    have hdimC : (affineHilbertPolynomial (C : Ideal GeoJets)).natDegree = 1 := by omega
    obtain ⟨hbound, hprime⟩ := hslice C h hC.isPrime hh
    have hf : Module.Finite (SectionField h) (SectionJets h ⧸ sliceIdeal C h) :=
      natDegree_affineHilbertPolynomial_eq_zero_iff.mp (by omega)
    refine hprime.imp_right ?_
    rintro ⟨hp, hcomap⟩
    have := hp
    have := hf
    have hfield := IsField.of_isDomain_of_finite (SectionField h)
      (SectionJets h ⧸ sliceIdeal C h)
    exact ⟨Ideal.Quotient.maximal_of_isField _ hfield, hcomap⟩
  intro C D hCD
  obtain hC | ⟨hmC, hcC⟩ := data C
  · simp [Ideal.isCoprime_iff_sup_eq, hC]
  obtain hD | ⟨hmD, hcD⟩ := data D
  · simp [Ideal.isCoprime_iff_sup_eq, hD]
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply hmC.coprime_of_ne hmD
  intro heq
  exact hCD (Subtype.ext (hcC.symm.trans (heq ▸ hcD)))
private theorem sum_slice_lengths (hslice : c1) {surface : Ideal GeoJets} {P : GeoJets}
    (hs : surface.IsPrime) (hdim : (affineHilbertPolynomial surface).natDegree = 2)
    (hP : P ∉ surface) {h : Shape} (hh : FullChamber h)
    [Module.Finite (SectionField h) (SectionJets h ⧸ cut (sliceIdeal surface h) (sliceMap h P))] :
    (∑ C ∈ (cut surface P).minimalPrimesFinset, sectionDegree C h) ≤
      Module.finrank (SectionField h) (SectionJets h ⧸ cut (sliceIdeal surface h) (sliceMap h P)) := by
  classical
  let T := (cut surface P).minimalPrimesFinset
  have heq : sliceIdeal (cut surface P) h = cut (sliceIdeal surface h) (sliceMap h P) := by
    simp only [sliceIdeal, cut, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    exact sup_right_comm _ _ _
  have hle (C : T) : cut (sliceIdeal surface h) (sliceMap h P) ≤ sliceIdeal C h :=
    heq ▸ slice_mono h (Ideal.mem_minimalPrimesFinset.mp C.2).le
  dsimp only [sectionDegree]
  rw [← Finset.sum_coe_sort]
  exact sum_finrank_le_of_coprime _ (fun C : T => sliceIdeal C h) hle
    (sliced_components_coprime hslice hs hdim hP hh)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4.c1 := by
  classical
  intro surface P a h hs hdim ha hh hP hfit
  let h' := h.scale 6
  let a' := a.scale 6
  let I := sliceIdeal surface h'
  let q := sliceMap h' P
  have full_scale6 (b : Shape) (hb : FullChamber b) : FullChamber (b.scale 6) := by
    obtain ⟨⟨hb₁, hb₂⟩, hb₃⟩ := hb
    change (6 * b.j ≤ 6 * b.b ∧ 3 * (6 * b.t) ≤ 6 * b.j) ∧ 0 < 6 * b.t
    omega
  have := hs
  have hd : (affineHilbertPolynomial surface).natDegree = 2 := by
    exact_mod_cast (dimension_eq_hilbert surface).symm.trans hdim
  obtain ⟨hdrop, hcase⟩ := h1 surface h' hs (full_scale6 h hh)
  have hIdeg : (affineHilbertPolynomial I).natDegree ≤ 1 := by
    simpa [I, hd] using hdrop
  obtain htop | ⟨hprime, hcontract⟩ := hcase
  · have hzero (C : Ideal GeoJets) (hC : C ∈ (cut surface P).minimalPrimesFinset) :
        sectionDegree C h' = 0 := by
      have hle : surface ≤ C := le_sup_left.trans (Ideal.mem_minimalPrimesFinset.mp hC).le
      have heq : sliceIdeal C h' = ⊤ :=
        top_le_iff.mp (htop.symm.trans_le (slice_mono h' hle))
      change Module.finrank (SectionField h') (SectionJets h' ⧸ sliceIdeal C h') = 0
      rw [heq]
      exact Module.finrank_zero_of_subsingleton
    change 6 * (∑ C ∈ (cut surface P).minimalPrimesFinset, sectionDegree C h') ≤ _
    rw [Finset.sum_eq_zero hzero, mul_zero]
    exact Nat.zero_le _
  have hq : q ∉ I := by
    intro hm
    apply hP
    rw [← hcontract]
    exact hm
  have hpow (n : ℕ) (hn : 0 < n) : q ^ n ∉ I :=
    fun hm => hq ((hprime.pow_mem_iff_mem n hn).mp hm)
  have finite_cut (u : SectionJets h') (hu : u ∉ I) :
      Module.Finite (SectionField h') (SectionJets h' ⧸ cut I u) := by
    apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
    have hf : (affineHilbertPolynomial (cut I u)).natDegree ≤
        (affineHilbertPolynomial I).natDegree - 1 :=
      (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
        hprime hu le_rfl).1
    exact Nat.eq_zero_of_le_zero (hf.trans (Nat.sub_eq_zero_of_le hIdeg).le)
  have hfin (n : ℕ) : Module.Finite (SectionField h') (SectionJets h' ⧸ cut I (q ^ n)) := by
    cases n with
    | zero =>
      apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
      simp [cut, Ideal.span_singleton_one, affineHilbertPolynomial_top]
    | succ n => exact finite_cut _ (hpow (n + 1) (Nat.succ_pos n))
  have := finite_cut q hq
  have hsum := sum_slice_lengths h1 hs hd hP (full_scale6 h hh)
  change 6 * (∑ C ∈ (cut surface P).minimalPrimesFinset, sectionDegree C h') ≤
    surfaceDegree surface a' h'
  calc
    _ ≤ 6 * Module.finrank (SectionField h') (SectionJets h' ⧸ cut I q) :=
      Nat.mul_le_mul_left 6 hsum
    _ = Module.finrank (SectionField h') (SectionJets h' ⧸ cut I (q ^ 6)) :=
      (finrank_cut_pow I q hprime hq hfin 6).symm
    _ ≤ genericCutLength I a' :=
      h2 (SectionField h') I (q ^ 6) a' hprime hIdeg (full_scale6 a ha)
        (hpow 6 (by decide)) (scaled_power_fits hfit)
    _ = _ := genericCutLength_sliceIdeal surface a' h'
end
end K1_13_6_1_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_1_2
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
def shift {R τ : Type} [CommRing R] (c : τ → R) :
    MvPolynomial τ R →+* MvPolynomial τ R :=
  eval₂Hom C (fun i => MvPolynomial.X i + C (c i))
@[simp] theorem shift_C {R τ : Type} [CommRing R] (c : τ → R) (a : R) :
    shift c (C a) = C a := by simp [shift]
@[simp] theorem shift_X {R τ : Type} [CommRing R] (c : τ → R) (i : τ) :
    shift c (MvPolynomial.X i) = MvPolynomial.X i + C (c i) := by simp [shift]
theorem shift_injective {R τ : Type} [CommRing R] (c : τ → R) :
    Function.Injective (shift c) := by
  have h : (shift (fun i => -c i)).comp (shift c) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [map_add, add_assoc]
  have hinv : Function.LeftInverse (shift (fun i => -c i)) (shift c) :=
    fun p => DFunLike.congr_fun h p
  exact hinv.injective
theorem shift_map {R S τ : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (c : τ → R) (p : MvPolynomial τ R) :
    shift (fun i => f (c i)) (MvPolynomial.map f p) = MvPolynomial.map f (shift c p) := by
  have h : (shift (fun i => f (c i))).comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (shift c) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp
  exact DFunLike.congr_fun h p
theorem coefficients_eq_zero {k R B ι τ : Type} [Field k] [CommRing R] [IsDomain R]
    [CommRing B] [Algebra k R] [Algebra k B] [Fintype ι]
    (q : R →ₐ[k] B) {Q : R} (hQ : Q ≠ 0) (hq : q Q = 0) {v : ι → R}
    (hv : LinearIndependent k (fun i => q (v i))) (s : Finset τ) (w : τ → R)
    (a : ι → MvPolynomial τ k) (H : MvPolynomial τ R)
    (he : ∑ i, MvPolynomial.map (algebraMap k R) (a i) * C (v i) =
      (C Q + ∑ j ∈ s, C (w j) * MvPolynomial.X j) * H) :
    ∀ i, a i = 0 := by
  classical
  have hvanish (d : τ →₀ ℕ) : H.coeff d = 0 ∧ ∀ i, (a i).coeff d = 0 := by
    induction d using (measure (fun d : τ →₀ ℕ => d.degree)).wf.induction with
    | h d ih =>
      have hlower : (∑ j ∈ s, C (w j) * MvPolynomial.X j * H).coeff d = 0 := by
        rw [coeff_sum]
        apply Finset.sum_eq_zero
        intro j _
        rw [mul_assoc, coeff_C_mul, coeff_X_mul']
        split_ifs with hj
        · have hjle : Finsupp.single j 1 ≤ d := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
          have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hjle)
          rw [map_add, Finsupp.degree_single] at hd
          rw [(ih (d - Finsupp.single j 1) (show (d - Finsupp.single j 1).degree < d.degree
            by omega)).1, mul_zero]
        · rw [mul_zero]
      have h := congrArg (fun p : MvPolynomial τ R => p.coeff d) he
      rw [add_mul, Finset.sum_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hlower, add_zero, coeff_C_mul, coeff_sum] at h
      simp only [mul_comm (MvPolynomial.map _ _) (C _), coeff_C_mul, coeff_map,
        mul_comm (v _) (algebraMap k R _)] at h
      have hh : ∑ i, (a i).coeff d • q (v i) = 0 := by
        have h' := congrArg q h
        simpa only [map_sum, map_mul, AlgHom.commutes, hq, zero_mul,
          Algebra.smul_def] using h'
      have ha := Fintype.linearIndependent_iff.mp hv _ hh
      have hz : Q * H.coeff d = 0 := by
        rw [← h]
        simp [ha]
      exact ⟨(mul_eq_zero.mp hz).resolve_left hQ, ha⟩
  exact fun i => MvPolynomial.eq_zero_iff.mpr fun d => (hvanish d).2 i
end
end K1_13_6_1_4_1_2
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3 K1_13_2_3_5
open K1_13_2_3_6 (sumFrom)
private def eDen (n : ℕ) : ℕ := (n * (n * (2*n+15)+30)+25)/72
private def eThree (n : ℕ) : ℕ := n * (n+2) * (2*n-1) / 24
private def eCore (r dr h l o : ℕ) : ℕ :=
  (h + eDen (o-3*r)) - (eDen o + (eDen l - eThree (l-dr)))
private structure EPlan where
  deg : ℕ
  hi : ℕ
  rem : ℕ
  lower : ℕ
  ord : ℕ
private def EPlan.eval (p : EPlan) (i : ℕ) : ℕ :=
  eCore p.rem (p.deg-p.rem) (eDen p.hi - eThree (p.hi-p.deg)) (p.lower-i) (p.ord-i)
private def EPlan.Valid (p : EPlan) (j : ℕ) : Prop :=
  p.rem ≤ p.deg ∧ p.ord-j ≤ p.deg+1 ∧ p.hi ≤ 3*p.deg+1 ∧ p.hi ≤ 2*p.deg+3 ∧
  p.lower-j ≤ 3*(p.deg-p.rem)+1 ∧ p.lower-j ≤ 2*(p.deg-p.rem)+3
private instance (p : EPlan) (j : ℕ) : Decidable (p.Valid j) := by unfold EPlan.Valid; infer_instance
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open K1_13_2_3_6 (sumFrom)
set_option maxHeartbeats 2000000
private def withNatF (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => f 0
  | k+1 => f (Nat.succ k)
set_option maxRecDepth 50000
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open K1_13_2_3_6 (sumFrom)
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end
end K1_13_2_3_6
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_7_2_2_3
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_2 K1_14_2_2_7_2_2 MvPolynomial
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
private abbrev SlopeField := RatFunc SeedField
private abbrev InterceptField := RatFunc SlopeField
private local instance (priority := high) jetEval (I : Ideal Ambient) : Algebra (Polynomial SlopeField) (SlopeRing I) :=
  (Polynomial.aeval (jetForm I) : _ →ₐ[SlopeField] SlopeRing I).toRingHom.toAlgebra
private local instance (priority := high) jetModule (I : Ideal Ambient) :
    Module (Polynomial SlopeField) (SlopeRing I) :=
  (jetEval I).toModule
private abbrev Fibre (I : Ideal Ambient) :=
  letI : Algebra (Polynomial SlopeField) (SlopeRing I) := jetEval I
  InterceptField ⊗[(Polynomial SlopeField)] SlopeRing I
private abbrev mixedIdeal (I : Ideal Ambient) : Ideal SectionAmbient :=
  I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}
private def mixedMk (I : Ideal Ambient) : SectionAmbient →+* OverMixed I :=
  Ideal.Quotient.mk (mixedIdeal I)
private theorem mixedMk_seed (I : Ideal Ambient) : mixedMk I sectionSeedLine = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
private theorem mixedMk_jet (I : Ideal Ambient) : mixedMk I sectionJetLine = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
private abbrev scalarToMixed (I : Ideal Ambient) : InterceptField →+* OverMixed I :=
  (algebraMap SectionField (OverMixed I)).comp coefficients.toRingHom
private theorem scalarToMixed_C_C (I : Ideal Ambient) (a : FX) :
    scalarToMixed I (RatFunc.C (RatFunc.C (algebraMap FX SeedField a))) =
      mixedMk I (C (algebraMap FX SectionField a)) := by
  change mixedMk I (C (coefficients (RatFunc.C (RatFunc.C (algebraMap FX SeedField a))))) = _
  rw [coefficients_ground]
private theorem scalarToMixed_seed (I : Ideal Ambient) (i : Fin 2) :
    scalarToMixed I (RatFunc.C (RatFunc.C (generic i))) =
      mixedMk I (C (sliceParameter (![0, 2] i))) := by
  change mixedMk I (C (coefficients (RatFunc.C (RatFunc.C (generic i))))) = _
  rw [coefficients_seed]
private theorem scalarToMixed_slope (I : Ideal Ambient) :
    scalarToMixed I (RatFunc.C RatFunc.X) = mixedMk I (C (sliceParameter 1)) := by
  change mixedMk I (C (coefficients (RatFunc.C RatFunc.X))) = _
  rw [coefficients_slope]
private theorem scalarToMixed_intercept (I : Ideal Ambient) :
    scalarToMixed I RatFunc.X = mixedMk I (C (sliceParameter 3)) := by
  change mixedMk I (C (coefficients RatFunc.X)) = _
  rw [coefficients_intercept]
private def seedEvalMixed (I : Ideal Ambient) : SeedAmbient →+* OverMixed I :=
  eval₂Hom ((scalarToMixed I).comp (RatFunc.C.comp RatFunc.C)) (fun i => mixedMk I (MvPolynomial.X i))
private theorem seedEvalMixed_base (I : Ideal Ambient) :
    (seedEvalMixed I).comp seedBase = (mixedMk I).comp sectionBase := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa only [RingHom.comp_apply, seedBase, sectionBase, map_C, seedEvalMixed, eval₂Hom_C]
      using scalarToMixed_C_C I a
  · intro i
    simp [seedEvalMixed, seedBase, sectionBase]
private def seedToMixed (I : Ideal Ambient) : JetSeedSection I →+* OverMixed I :=
  Ideal.Quotient.lift (seedIdeal I) (seedEvalMixed I) <| by
    change seedIdeal I ≤ RingHom.ker (seedEvalMixed I)
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, seedEvalMixed_base]
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_map_of_mem sectionBase hp))
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      simp only [seedLine, map_sub, map_add, map_mul, seedEvalMixed, eval₂Hom_C, eval₂Hom_X']
      change mixedMk I (MvPolynomial.X 0) +
        scalarToMixed I (RatFunc.C (RatFunc.C (generic 0))) * mixedMk I (MvPolynomial.X 1) -
        scalarToMixed I (RatFunc.C (RatFunc.C (generic 1))) = 0
      rw [scalarToMixed_seed I 0, scalarToMixed_seed I 1]
      change mixedMk I (MvPolynomial.X 0) + mixedMk I (C (sliceParameter 0)) *
        mixedMk I (MvPolynomial.X 1) - mixedMk I (C (sliceParameter 2)) = 0
      simpa only [sectionSeedLine, map_sub, map_add, map_mul] using mixedMk_seed I
private theorem seedToMixed_mk (I : Ideal Ambient) (p : SeedAmbient) :
    seedToMixed I (Ideal.Quotient.mk (seedIdeal I) p) = seedEvalMixed I p :=
  rfl
private def tensorLift {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B]
    (f : A →+* T) (g : B →+* T)
    (h : f.comp (algebraMap R A) = g.comp (algebraMap R B)) : A ⊗[R] B →+* T := by
  letI : Algebra R T := (f.comp (algebraMap R A)).toAlgebra
  let f' : A →ₐ[R] T := { f with commutes' := fun _ => rfl }
  let g' : B →ₐ[R] T := { g with commutes' := fun r => (RingHom.congr_fun h r).symm }
  exact (Algebra.TensorProduct.lift (S := R) f' g' (fun _ _ => Commute.all _ _)).toRingHom
private theorem tensorLift_tmul {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B]
    (f : A →+* T) (g : B →+* T) (h : f.comp (algebraMap R A) = g.comp (algebraMap R B))
    (a : A) (b : B) : tensorLift f g h (a ⊗ₜ[R] b) = f a * g b :=
  rfl
private def slopeToMixed (I : Ideal Ambient) : SlopeRing I →+* OverMixed I :=
  tensorLift ((scalarToMixed I).comp RatFunc.C) (seedToMixed I) <| by
    apply RingHom.ext
    intro a
    change scalarToMixed I (RatFunc.C (algebraMap SeedField SlopeField a)) =
      seedToMixed I (Ideal.Quotient.mk (seedIdeal I) (C a))
    rw [seedToMixed_mk, seedEvalMixed, eval₂Hom_C, RatFunc.algebraMap_eq_C]
    rfl
private theorem slopeToMixed_form (I : Ideal Ambient) :
    slopeToMixed I (jetForm I) = scalarToMixed I RatFunc.X := by
  apply sub_eq_zero.mp
  simp only [rationalLine, map_add, slopeToMixed, tensorLift_tmul, map_one, one_mul,
    seedCoord, seedToMixed_mk, seedEvalMixed, eval₂Hom_X']
  change mixedMk I (MvPolynomial.X 2) +
    scalarToMixed I (RatFunc.C RatFunc.X) * mixedMk I (MvPolynomial.X 3) -
    scalarToMixed I RatFunc.X = 0
  rw [scalarToMixed_slope, scalarToMixed_intercept]
  simpa only [sectionJetLine, map_sub, map_add, map_mul] using mixedMk_jet I
private def toMixed (I : Ideal Ambient) : Fibre I →+* OverMixed I :=
  tensorLift (R := (Polynomial SlopeField)) (scalarToMixed I) (slopeToMixed I) <| by
    apply Polynomial.ringHom_ext
    · intro a
      change scalarToMixed I (algebraMap (Polynomial SlopeField) InterceptField (Polynomial.C a)) =
        slopeToMixed I (Polynomial.aeval (jetForm I) (Polynomial.C a))
      rw [RatFunc.algebraMap_C, Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply]
      simp only [slopeToMixed, tensorLift_tmul, map_one, mul_one]
      rfl
    · change scalarToMixed I (algebraMap (Polynomial SlopeField) InterceptField Polynomial.X) =
        slopeToMixed I (Polynomial.aeval (jetForm I) Polynomial.X)
      rw [RatFunc.algebraMap_X, Polynomial.aeval_X, slopeToMixed_form]
private abbrev fibreScalar (I : Ideal Ambient) : InterceptField →+* Fibre I :=
  algebraMap InterceptField (Fibre I)
private abbrev fibreSlope (I : Ideal Ambient) : SlopeRing I →+* Fibre I :=
  Algebra.TensorProduct.includeRight.toRingHom
private abbrev slopeSeed (I : Ideal Ambient) : JetSeedSection I →+* SlopeRing I :=
  Algebra.TensorProduct.includeRight.toRingHom
private abbrev fibreSeed (I : Ideal Ambient) : JetSeedSection I →+* Fibre I :=
  (fibreSlope I).comp (slopeSeed I)
private theorem fibreSlope_scalar (I : Ideal Ambient) (a : SlopeField) :
    fibreSlope I (algebraMap SlopeField (SlopeRing I) a) =
      fibreScalar I (RatFunc.C a) := by
  have h : fibreScalar I (algebraMap (Polynomial SlopeField) InterceptField (Polynomial.C a)) =
      fibreSlope I (algebraMap (Polynomial SlopeField) (SlopeRing I) (Polynomial.C a)) :=
    RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := (Polynomial SlopeField)) (A := InterceptField) (B := SlopeRing I)) (Polynomial.C a)
  rw [RatFunc.algebraMap_C,
    show algebraMap (Polynomial SlopeField) (SlopeRing I) (Polynomial.C a) =
      algebraMap SlopeField (SlopeRing I) a from Polynomial.aeval_C _ _] at h
  exact h.symm
private theorem fibreSeed_scalar (I : Ideal Ambient) (a : SeedField) :
    fibreSeed I (Ideal.Quotient.mk (seedIdeal I) (C a)) =
      fibreScalar I (RatFunc.C (RatFunc.C a)) := by
  have h := RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := SeedField)
      (A := SlopeField) (B := JetSeedSection I)) a
  change fibreSlope I (Algebra.TensorProduct.includeRight (algebraMap SeedField (JetSeedSection I) a)) = _
  rw [← show Algebra.TensorProduct.includeLeftRingHom (algebraMap SeedField SlopeField a) =
      (Algebra.TensorProduct.includeRight (B := JetSeedSection I) (A := SlopeField))
        (algebraMap SeedField (JetSeedSection I) a) from h]
  exact (fibreSlope_scalar I _).trans (by rw [RatFunc.algebraMap_eq_C])
private theorem fibreSlope_form (I : Ideal Ambient) :
    fibreSlope I (jetForm I) = fibreScalar I RatFunc.X := by
  have h : fibreScalar I (algebraMap (Polynomial SlopeField) InterceptField Polynomial.X) =
      fibreSlope I (algebraMap (Polynomial SlopeField) (SlopeRing I) Polynomial.X) :=
    RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := (Polynomial SlopeField)) (A := InterceptField) (B := SlopeRing I)) Polynomial.X
  rw [RatFunc.algebraMap_X,
    show algebraMap (Polynomial SlopeField) (SlopeRing I) Polynomial.X =
      jetForm I from Polynomial.aeval_X _] at h
  exact h.symm
private abbrev scalarToFibre (I : Ideal Ambient) : SectionField →+* Fibre I :=
  (fibreScalar I).comp coefficients.symm.toRingHom
private def sectionEvalFibre (I : Ideal Ambient) : SectionAmbient →+* Fibre I :=
  eval₂Hom (scalarToFibre I) (fun i => fibreSeed I (seedCoord I i))
private theorem scalarToFibre_seed (I : Ideal Ambient) (i : Fin 2) :
    scalarToFibre I (sliceParameter (![0, 2] i)) =
      fibreScalar I (RatFunc.C (RatFunc.C (generic i))) := by
  change fibreScalar I (coefficients.symm (sliceParameter (![0, 2] i))) = _
  rw [← coefficients_seed i, RingEquiv.symm_apply_apply]
private theorem sectionEvalFibre_base (I : Ideal Ambient) :
    (sectionEvalFibre I).comp sectionBase = (fibreSeed I).comp (seedRestrict I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change sectionEvalFibre I (MvPolynomial.map (algebraMap FX SectionField) (C a)) =
      fibreSeed I (Ideal.Quotient.mk (seedIdeal I) (MvPolynomial.map (algebraMap FX SeedField) (C a)))
    rw [map_C, map_C, sectionEvalFibre, eval₂Hom_C, fibreSeed_scalar]
    change fibreScalar I (coefficients.symm (algebraMap FX SectionField a)) = _
    rw [← coefficients_ground a, RingEquiv.symm_apply_apply]
  · intro i
    change sectionEvalFibre I (MvPolynomial.map (algebraMap FX SectionField) (MvPolynomial.X i)) =
      fibreSeed I (Ideal.Quotient.mk (seedIdeal I)
        (MvPolynomial.map (algebraMap FX SeedField) (MvPolynomial.X i)))
    rw [map_X, map_X, sectionEvalFibre, eval₂Hom_X']
    rfl
private theorem sectionEvalFibre_seed (I : Ideal Ambient) :
    sectionEvalFibre I sectionSeedLine = 0 := by
  have h : Ideal.Quotient.mk (seedIdeal I) (seedLine 0 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h₀ : scalarToFibre I (sliceParameter 0) = fibreScalar I (RatFunc.C (RatFunc.C (generic 0))) :=
    scalarToFibre_seed I 0
  have h₂ : scalarToFibre I (sliceParameter 2) = fibreScalar I (RatFunc.C (RatFunc.C (generic 1))) :=
    scalarToFibre_seed I 1
  have h' := congrArg (fibreSeed I) h
  simp only [seedLine, map_add, map_mul, map_sub, map_zero, fibreSeed_scalar] at h'
  simpa only [sectionSeedLine, sectionEvalFibre, map_add, map_mul, map_sub, eval₂Hom_C,
    eval₂Hom_X', h₀, h₂, seedCoord] using h'
private theorem sectionEvalFibre_jet (I : Ideal Ambient) :
    sectionEvalFibre I sectionJetLine = 0 := by
  have h₁ : scalarToFibre I (sliceParameter 1) = fibreScalar I (RatFunc.C RatFunc.X) := by
    change fibreScalar I (coefficients.symm (sliceParameter 1)) = _
    rw [← coefficients_slope, RingEquiv.symm_apply_apply]
  have h₃ : scalarToFibre I (sliceParameter 3) = fibreScalar I RatFunc.X := by
    change fibreScalar I (coefficients.symm (sliceParameter 3)) = _
    rw [← coefficients_intercept, RingEquiv.symm_apply_apply]
  have h := sub_eq_zero.mpr (fibreSlope_form I)
  have hm : jetForm I = slopeSeed I (seedCoord I 2) +
      algebraMap SlopeField (SlopeRing I) RatFunc.X * slopeSeed I (seedCoord I 3) := by
    simp [rationalLine, Algebra.TensorProduct.algebraMap_apply]
  rw [hm, map_add, map_mul, fibreSlope_scalar] at h
  simpa only [sectionJetLine, sectionEvalFibre, map_add, map_mul, map_sub, eval₂Hom_C,
    eval₂Hom_X', h₁, h₃, fibreSeed, RingHom.comp_apply] using h
private def toFibre (I : Ideal Ambient) : OverMixed I →+* Fibre I :=
  Ideal.Quotient.lift (mixedIdeal I) (sectionEvalFibre I) <| by
    change mixedIdeal I ≤ RingHom.ker (sectionEvalFibre I)
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, sectionEvalFibre_base]
      intro p hp
      have hz : Ideal.Quotient.mk (seedIdeal I) (seedBase p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_sup_left (Ideal.mem_map_of_mem seedBase hp))
      change fibreSeed I (seedRestrict I p) = 0
      exact (congrArg (fibreSeed I) hz).trans (map_zero _)
    · rw [Ideal.span_insert, sup_le_iff]
      exact ⟨(Ideal.span_singleton_le_iff_mem _).mpr (sectionEvalFibre_seed I),
        (Ideal.span_singleton_le_iff_mem _).mpr (sectionEvalFibre_jet I)⟩
private theorem toMixed_scalar (I : Ideal Ambient) (a : InterceptField) :
    toMixed I (fibreScalar I a) = scalarToMixed I a := by
  change toMixed I (a ⊗ₜ[(Polynomial SlopeField)] 1) = _
  simp only [toMixed, tensorLift_tmul, map_one, mul_one]
private theorem toMixed_slope (I : Ideal Ambient) (b : SlopeRing I) :
    toMixed I (fibreSlope I b) = slopeToMixed I b := by
  change toMixed I (1 ⊗ₜ[(Polynomial SlopeField)] b) = _
  simp only [toMixed, tensorLift_tmul, map_one, one_mul]
private theorem slopeToMixed_seed (I : Ideal Ambient) (b : JetSeedSection I) :
    slopeToMixed I (slopeSeed I b) = seedToMixed I b := by
  change slopeToMixed I (1 ⊗ₜ[SeedField] b) = _
  simp only [slopeToMixed, tensorLift_tmul, map_one, one_mul]
private theorem slopeToMixed_scalar (I : Ideal Ambient) (a : SlopeField) :
    slopeToMixed I (algebraMap SlopeField (SlopeRing I) a) = scalarToMixed I (RatFunc.C a) := by
  change slopeToMixed I (a ⊗ₜ[SeedField] 1) = _
  simp only [slopeToMixed, tensorLift_tmul, map_one, mul_one]
  rfl
private theorem toMixed_seed (I : Ideal Ambient) (b : JetSeedSection I) :
    toMixed I (fibreSeed I b) = seedToMixed I b := by
  change toMixed I (fibreSlope I (slopeSeed I b)) = _
  rw [toMixed_slope, slopeToMixed_seed]
private theorem toMixed_coord (I : Ideal Ambient) (i : Fin 4) :
    toMixed I (fibreSeed I (seedCoord I i)) = mixedMk I (MvPolynomial.X i) := by
  rw [toMixed_seed, seedCoord, seedToMixed_mk, seedEvalMixed, eval₂Hom_X']
private theorem toFibre_mk (I : Ideal Ambient) (p : SectionAmbient) :
    toFibre I (mixedMk I p) = sectionEvalFibre I p :=
  rfl
private theorem toFibre_scalar (I : Ideal Ambient) (a : SectionField) :
    toFibre I (algebraMap SectionField (OverMixed I) a) = fibreScalar I (coefficients.symm a) :=
  eval₂Hom_C _ _ _
private theorem toFibre_scalarToMixed (I : Ideal Ambient) (a : InterceptField) :
    toFibre I (scalarToMixed I a) = fibreScalar I a := by
  change toFibre I (algebraMap SectionField (OverMixed I) (coefficients a)) = _
  rw [toFibre_scalar, RingEquiv.symm_apply_apply]
private def fibreEquiv (I : Ideal Ambient) : Fibre I ≃+* OverMixed I :=
  RingEquiv.ofRingHom (toMixed I) (toFibre I)
    (by
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        change toMixed I (toFibre I (algebraMap SectionField (OverMixed I) a)) =
          algebraMap SectionField (OverMixed I) a
        rw [toFibre_scalar, toMixed_scalar]
        simp [scalarToMixed]
      · intro i
        change toMixed I (toFibre I (mixedMk I (MvPolynomial.X i))) = mixedMk I (MvPolynomial.X i)
        rw [toFibre_mk, sectionEvalFibre, eval₂Hom_X', toMixed_coord])
    (by
      apply Algebra.TensorProduct.ringHom_ext
      · apply RingHom.ext
        intro a
        change toFibre I (toMixed I (fibreScalar I a)) = fibreScalar I a
        rw [toMixed_scalar, toFibre_scalarToMixed]
      · apply Algebra.TensorProduct.ringHom_ext
        · apply RingHom.ext
          intro a
          change toFibre I (toMixed I (fibreSlope I (algebraMap SlopeField (SlopeRing I) a))) = _
          rw [toMixed_slope, slopeToMixed_scalar, toFibre_scalarToMixed]
          exact (fibreSlope_scalar I a).symm
        · apply Ideal.Quotient.ringHom_ext
          apply MvPolynomial.ringHom_ext
          · intro a
            change toFibre I (toMixed I (fibreSeed I (Ideal.Quotient.mk (seedIdeal I) (C a)))) =
              fibreSeed I (Ideal.Quotient.mk (seedIdeal I) (C a))
            rw [toMixed_seed, seedToMixed_mk, seedEvalMixed, eval₂Hom_C, fibreSeed_scalar]
            exact toFibre_scalarToMixed I _
          · intro i
            change toFibre I (toMixed I (fibreSeed I (seedCoord I i))) = fibreSeed I (seedCoord I i)
            rw [toMixed_coord, toFibre_mk, sectionEvalFibre, eval₂Hom_X'])
theorem proof : K1_14_2_2_7_2_2.c3 := by
  intro I
  change Module.finrank InterceptField (Fibre I) = Module.finrank SectionField (OverMixed I)
  apply Algebra.finrank_eq_of_equiv_equiv coefficients (fibreEquiv I)
  apply RingHom.ext
  intro a
  change scalarToMixed I a = toMixed I (fibreScalar I a)
  exact (toMixed_scalar I a).symm
end
end K1_14_2_2_7_2_2_3
end
section
namespace K1_13_2_3_7
def natDen : ℕ → ℕ
  | 0 => 0
  | u + 1 => Nat.succ (Nat.div (Nat.mul u (Nat.add (Nat.mul u (Nat.add (Nat.mul 2 u) 21)) 66)) 72)
def countParts (d n : ℕ) : ℕ × ℕ :=
  let m := Nat.min n (3 * d + 1)
  if m ≤ d + 1 then (natDen m, 0) else
    let a := m - d
    let removed := natDen (a - 1) + natDen (a - 2) + natDen (a - 3)
    if m ≤ 2 * d + 3 then (natDen m, removed) else
      let b := m - 2 * d
      (natDen m + natDen (b - 3) + natDen (b - 4) + natDen (b - 5), removed)
def natKernel (d j h r : ℕ) : ℕ :=
  match countParts d 1651 with
  | (a, b) =>
    if r = 0 then
      match countParts d (1650 - j) with
      | (c, e) => a + e - (b + c)
    else
      match countParts d h, countParts (d - r) (h - 3 * r), countParts (d - r) (1650 - j) with
      | (c, e), (f, g), (k, l) => a + e + f + l - (b + c + g + k)
def natEntry (t j : ℕ) : ℕ :=
  if 23 ≤ t + j ∧ t + j ≤ 656 then
    let b := 1136 - t
    if 4 * j < b then
      let old := natDen 1651 - natDen (1650 - j)
      let chosen := natKernel (1650 - (b - 4 * j)) j (b - j) j
      let original := natKernel 1650 j (b - j) ((b + 3) / 4)
      Nat.min old chosen - original
    else 0
  else 0
def natGrade (t : ℕ) : ℕ := rangeSum (natEntry t) 283
def natChunk (lo len : ℕ) : ℕ := rangeSum (fun t => natGrade (lo + t)) len
private theorem rangeSum_append (f : ℕ → ℕ) (a b : ℕ) :
    rangeSum f (a + b) = rangeSum f a + rangeSum (fun k => f (a + k)) b := by
  induction b with
  | zero => simp [rangeSum]
  | succ b ih =>
    change rangeSum f (a + b) + f (a + b) =
      rangeSum f a + (rangeSum (fun k => f (a + k)) b + f (a + b))
    rw [ih, Nat.add_assoc]
theorem natChunk_append (lo a b : ℕ) :
    natChunk lo (a + b) = natChunk lo a + natChunk (lo + a) b := by
  unfold natChunk
  rw [rangeSum_append]
  simp only [Nat.add_assoc]
end K1_13_2_3_7
end
section
namespace K1_13_7_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 MeasureTheory MvPolynomial
open scoped Pointwise
abbrev RealPoint := Fin 4 → ℝ
def cap (p : Shape) : Set RealPoint :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
    x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t}
def SupportedIn (f : GeoJets) (P : Set RealPoint) : Prop :=
  ∀ e ∈ f.support, (fun i => (e i : ℝ)) ∈ P
theorem supportedIn_cap {f : GeoJets} {p : Shape} (hf : GeoFits f p) :
    SupportedIn f (cap p) := by
  intro e he
  have htotal := (le_weightedTotalDegree (1 : Fin 4 → ℕ) he).trans
    (show f.weightedTotalDegree 1 ≤ p.b by simpa only [weightedTotalDegree_one] using hf.1)
  have hindex := (le_weightedTotalDegree (Fin.val : Fin 4 → ℕ) he).trans hf.2.1
  have htop := degreeOf_le_iff.mp hf.2.2 e he
  simp only [Finsupp.weight_eq_sum, smul_eq_mul, Pi.one_apply, mul_one,
    Fin.sum_univ_four] at htotal
  simp only [Finsupp.weight_eq_sum, smul_eq_mul, Fin.sum_univ_four] at hindex
  have hj : e 1 + 2 * e 2 + 3 * e 3 ≤ p.j := by
    change e 0 * 0 + e 1 * 1 + e 2 * 2 + e 3 * 3 ≤ p.j at hindex
    omega
  refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · change (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ (p.b : ℝ)
    exact_mod_cast htotal
  · change (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ (p.j : ℝ)
    exact_mod_cast hj
  · change (e 3 : ℝ) ≤ (p.t : ℝ)
    exact_mod_cast htop
def bodyDifference (F : Set RealPoint → ℝ) (a x : Set RealPoint) : ℝ :=
  F (x + a) - F x
def mixedVolume (p q r s : Set RealPoint) : ℝ :=
  bodyDifference (bodyDifference (bodyDifference (bodyDifference
    (fun P => (volume P).toReal) p) q) r) s 0
end
end K1_13_7_1_1
end
section
namespace K1_13_7_1_1
open K1_13 K1_13_7_1
open scoped Pointwise
theorem chamber_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    Chamber (p.plus q) := by
  obtain ⟨hpb, hpj⟩ := hp
  obtain ⟨hqb, hqj⟩ := hq
  constructor <;> dsimp [Shape.plus] <;> omega
theorem cap_zero : cap ⟨0, 0, 0⟩ = 0 := by
  change cap ⟨0, 0, 0⟩ = {(0 : RealPoint)}
  ext x
  constructor
  · intro hx
    obtain ⟨h, hb, _, _⟩ := hx
    norm_num at hb
    apply Set.mem_singleton_iff.mpr
    funext i
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    change x i = 0
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
    · change x 2 = 0
      linarith
    · change x 3 = 0
      linarith
  · rintro rfl
    simp [cap]
private theorem split_pair {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : x + 2 * y ≤ A + B) :
    ∃ u v : ℝ, 0 ≤ u ∧ u ≤ x ∧ 0 ≤ v ∧ v ≤ y ∧
      u + 2 * v ≤ A ∧ (x - u) + 2 * (y - v) ≤ B := by
  let u := min x A
  let v := min y ((A - u) / 2)
  have huA : u ≤ A := min_le_right _ _
  have hvA : v ≤ (A - u) / 2 := min_le_right _ _
  refine ⟨u, v, le_min hx hA, min_le_left _ _, le_min hy (by linarith),
    min_le_left _ _, by linarith, ?_⟩
  rcases le_total y ((A - u) / 2) with h | h
  · have hve : v = y := min_eq_left h
    rcases le_total x A with h | h
    · have hue : u = x := min_eq_left h
      rw [hue, hve]
      linarith
    · have hue : u = A := min_eq_right h
      rw [hue, hve]
      linarith
  · have hve : v = (A - u) / 2 := min_eq_right h
    rw [hve]
    linarith
private theorem cap_split {p q : Shape} (hp : Chamber p) (hq : Chamber q)
    {x : RealPoint} (hx : x ∈ cap (p.plus q)) : x ∈ cap p + cap q := by
  have hpb' : (p.j : ℝ) ≤ p.b := by exact_mod_cast hp.1
  have hqb' : (q.j : ℝ) ≤ q.b := by exact_mod_cast hq.1
  obtain ⟨hx, hb, hj, ht⟩ := hx
  simp only [Shape.plus, Nat.cast_add] at hb hj ht
  let z := min (x 3) (p.t : ℝ)
  have hz0 : 0 ≤ z := le_min (hx 3) (by positivity)
  have hzx : z ≤ x 3 := min_le_left _ _
  have hzp : z ≤ (p.t : ℝ) := min_le_right _ _
  have hzq : x 3 - z ≤ (q.t : ℝ) := by
    rcases le_total (x 3) (p.t : ℝ) with hh | hh
    · dsimp only [z]
      rw [min_eq_left hh, sub_self]
      positivity
    · dsimp only [z]
      rw [min_eq_right hh]
      linarith
  have hpz : (3 : ℝ) * p.t ≤ p.j := by exact_mod_cast hp.2
  have hqz : (3 : ℝ) * q.t ≤ q.j := by exact_mod_cast hq.2
  obtain ⟨u, v, hu0, hux, hv0, hvx, huvp, huvq⟩ :=
    split_pair (x := x 1) (y := x 2) (A := (p.j : ℝ) - 3 * z)
      (B := (q.j : ℝ) - 3 * (x 3 - z)) (hx 1) (hx 2) (by linarith)
      (by linarith) (by linarith)
  let a := min (x 0) ((p.b : ℝ) - u - v - z)
  have ha0 : 0 ≤ a := le_min (hx 0) (by linarith)
  have hax : a ≤ x 0 := min_le_left _ _
  have hap : a ≤ (p.b : ℝ) - u - v - z := min_le_right _ _
  have haq : (x 0 - a) + (x 1 - u) + (x 2 - v) + (x 3 - z) ≤ (q.b : ℝ) := by
    rcases le_total (x 0) ((p.b : ℝ) - u - v - z) with hh | hh
    · dsimp only [a]
      rw [min_eq_left hh]
      linarith
    · dsimp only [a]
      rw [min_eq_right hh]
      linarith
  let y : RealPoint := ![a, u, v, z]
  have hy : y ∈ cap p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · change a + u + v + z ≤ (p.b : ℝ)
      linarith
    · change u + 2 * v + 3 * z ≤ (p.j : ℝ)
      linarith
    · exact hzp
  have hxy : x - y ∈ cap q := by
    refine ⟨?_, haq, ?_, hzq⟩
    · intro i
      fin_cases i <;> exact sub_nonneg.mpr (by assumption)
    · change (x 1 - u) + 2 * (x 2 - v) + 3 * (x 3 - z) ≤ (q.j : ℝ)
      linarith
  exact Set.mem_add.mpr ⟨y, hy, x - y, hxy, by abel⟩
theorem cap_add {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    cap (p.plus q) = cap p + cap q := by
  apply Set.Subset.antisymm (fun _ hx => cap_split hp hq hx)
  intro x hx
  obtain ⟨y, ⟨hy, hyb, hyj, hyt⟩, z, ⟨hz, hzb, hzj, hzt⟩, rfl⟩ := Set.mem_add.mp hx
  refine ⟨fun i => add_nonneg (hy i) (hz i), ?_, ?_, ?_⟩ <;>
    simp only [Pi.add_apply, Shape.plus, Nat.cast_add] <;> linarith
end K1_13_7_1_1
end
section
namespace K1_13_6_1_4_3
open K1_13 K1_13_7_1 K1_13_7_1_1 MeasureTheory Set
open scoped ENNReal Pointwise
private abbrev snocReal {n : ℕ} (y : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc y x
private theorem volume_snoc {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ x : ℝ, volume {y : Fin n → ℝ | snocReal y x ∈ S} := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e volume
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    volume_preserving_piFinSuccAbove _ _
  have hE : MeasurableSet (e '' S) := e.measurableSet_image.mpr hS
  have hpre : e ⁻¹' (e '' S) = S := Set.preimage_image_eq _ e.injective
  calc
    volume S = ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) (e '' S) :=
      (congrArg volume hpre.symm).trans (he.measure_preimage hE.nullMeasurableSet)
    _ = _ := by
      rw [Measure.prod_apply hE]
      congr 1
      funext x
      congr 1
      ext y
      change (x, y) ∈ e '' S ↔ snocReal y x ∈ S
      rw [e.image_eq_preimage_symm]
      change e.symm (x, y) ∈ S ↔ _
      change Fin.insertNth (Fin.last n) x y ∈ S ↔ _
      rw [Fin.insertNth_last']
private theorem volume_snoc_interval {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : MeasurableSet S) {u : ℝ} (hu : 0 ≤ u) {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ x ∈ Icc 0 u, 0 ≤ f x)
    (hs : ∀ x, volume {y : Fin n → ℝ | snocReal y x ∈ S} =
      (Icc 0 u).indicator (fun x => ENNReal.ofReal (f x)) x) :
    volume S = ENNReal.ofReal (∫ x in (0 : ℝ)..u, f x) := by
  rw [volume_snoc hS]
  simp_rw [hs]
  rw [lintegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hu,
    ← integral_Icc_eq_integral_Ioc]
  have hi : Integrable f (volume.restrict (Icc 0 u)) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 u)] f :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hnn)
  exact (ofReal_integral_eq_lintegral_ofReal hi hn).symm
private def cap2 (B J : ℝ) : Set (Fin 2 → ℝ) :=
  {y | 0 ≤ y 0 ∧ y 1 ∈ Icc 0 J ∧ y 0 + y 1 ≤ B}
private def cap3 (B J : ℝ) : Set (Fin 3 → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ y 0 + y 1 + y 2 ≤ B ∧ y 1 + 2 * y 2 ≤ J}
private theorem isClosed_nonneg {n : ℕ} : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
private theorem nonneg_snoc {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    (∀ i, 0 ≤ snocReal y s i) ↔ (∀ i, 0 ≤ y i) ∧ 0 ≤ s := by
  unfold snocReal
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last n)⟩
  · rintro ⟨hy, hs⟩ i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hs
    | cast i => simpa only [Fin.snoc_castSucc] using hy i
private theorem volume_cap2 {B J : ℝ} (hJ : 0 ≤ J) (hB : J ≤ B) :
    volume (cap2 B J) = ENNReal.ofReal (J * (B - J / 2)) := by
  have hm : MeasurableSet (cap2 B J) := by
    apply IsClosed.measurableSet
    exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_Icc.preimage (continuous_apply 1)).inter
        (isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const))
  have hs (x : ℝ) :
      volume {y : Fin 1 → ℝ | snocReal y x ∈ cap2 B J} =
        (Icc 0 J).indicator (fun x => ENNReal.ofReal (B - x)) x := by
    have he (y : Fin 1 → ℝ) :
        snocReal y x ∈ cap2 B J ↔ 0 ≤ y 0 ∧ x ∈ Icc 0 J ∧ y 0 + x ≤ B := by
      change 0 ≤ snocReal y x 0 ∧ snocReal y x (Fin.last 1) ∈ Icc 0 J ∧
        snocReal y x 0 + snocReal y x (Fin.last 1) ≤ B ↔ _
      simp only [snocReal, Fin.snoc_apply_zero, Fin.snoc_last]
    by_cases hx : x ∈ Icc 0 J
    · have hset : {y : Fin 1 → ℝ | snocReal y x ∈ cap2 B J} =
          Icc (fun _ => 0) (fun _ => B - x) := by
        ext y
        rw [Set.mem_ofPred_eq, he]
        have hzero (i : Fin 1) : i = 0 := Subsingleton.elim _ _
        change (0 ≤ y 0 ∧ x ∈ Icc 0 J ∧ y 0 + x ≤ B) ↔ (0 ≤ y ∧ y ≤ fun _ => B - x)
        simp only [Pi.le_def, Pi.zero_apply, hzero, forall_const, hx, true_and]
        exact and_congr_right fun _ => le_sub_iff_add_le.symm
      rw [hset, Real.volume_Icc_pi, indicator_of_mem hx]
      simp
    · have hset : {y : Fin 1 → ℝ | snocReal y x ∈ cap2 B J} = ∅ := by
        ext y
        simp [he, hx]
      rw [hset, measure_empty, indicator_of_notMem hx]
  rw [volume_snoc_interval hm hJ (by fun_prop) (fun x hx => sub_nonneg.mpr (hx.2.trans hB)) hs]
  congr 1
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => B * x - x ^ 2 / 2) (B - x) x := by
    convert ((hasDerivAt_id' x).const_mul B).sub (((hasDerivAt_id' x).pow 2).div_const 2)
      using 1
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => B - x) by fun_prop).intervalIntegrable _ _)]
  ring
private theorem volume_cap3 {B J : ℝ} (hJ : 0 ≤ J) (hB : J ≤ B) :
    volume (cap3 B J) = ENNReal.ofReal (J ^ 2 * (2 * B - J) / 8) := by
  have hm : MeasurableSet (cap3 B J) := by
    apply IsClosed.measurableSet
    exact isClosed_nonneg.inter
      ((isClosed_le (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
        continuous_const).inter
        (isClosed_le (f := fun y : Fin 3 → ℝ => y 1 + 2 * y 2)
          (by fun_prop) continuous_const))
  have hs (r : ℝ) :
      volume {y : Fin 2 → ℝ | snocReal y r ∈ cap3 B J} =
        (Icc 0 (J / 2)).indicator
          (fun r => ENNReal.ofReal ((J - 2 * r) * (B - J / 2))) r := by
    have he (y : Fin 2 → ℝ) :
        snocReal y r ∈ cap3 B J ↔
          (0 ≤ y 0 ∧ 0 ≤ y 1 ∧ 0 ≤ r) ∧ y 0 + y 1 + r ≤ B ∧ y 1 + 2 * r ≤ J := by
      have hc : (∀ i, 0 ≤ snocReal y r i) ↔ (0 ≤ y 0 ∧ 0 ≤ y 1 ∧ 0 ≤ r) := by
        rw [nonneg_snoc, Fin.forall_fin_two, and_assoc]
      change (∀ i, 0 ≤ snocReal y r i) ∧
        snocReal y r (Fin.castSucc 0) + snocReal y r (Fin.castSucc 1) +
          snocReal y r (Fin.last 2) ≤ B ∧
        snocReal y r (Fin.castSucc 1) + 2 * snocReal y r (Fin.last 2) ≤ J ↔ _
      rw [hc]
      simp only [snocReal, Fin.snoc_castSucc, Fin.snoc_last]
    by_cases hr : r ∈ Icc 0 (J / 2)
    · have hset : {y : Fin 2 → ℝ | snocReal y r ∈ cap3 B J} = cap2 (B - r) (J - 2 * r) := by
        ext y
        rw [Set.mem_ofPred_eq, he]
        change _ ↔ 0 ≤ y 0 ∧ (0 ≤ y 1 ∧ y 1 ≤ J - 2 * r) ∧ y 0 + y 1 ≤ B - r
        have hnr := hr.1
        constructor
        · rintro ⟨⟨h0, h1, _⟩, h2, h3⟩
          exact ⟨h0, ⟨h1, by linarith⟩, by linarith⟩
        · rintro ⟨h0, ⟨h1, h2⟩, h3⟩
          exact ⟨⟨h0, h1, hnr⟩, by linarith, by linarith⟩
      have hnr := hr.1
      have hru := hr.2
      rw [hset, indicator_of_mem hr, volume_cap2 (by linarith) (by linarith)]
      congr 1
      ring
    · have hset : {y : Fin 2 → ℝ | snocReal y r ∈ cap3 B J} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨⟨_, h1, h2⟩, _, h3⟩ := (he y).mp hy
        exact hr ⟨h2, by linarith⟩
      rw [hset, measure_empty, indicator_of_notMem hr]
  have hn (r : ℝ) (hr : r ∈ Icc 0 (J / 2)) : 0 ≤ (J - 2 * r) * (B - J / 2) := by
    have hru := hr.2
    exact mul_nonneg (by linarith) (by linarith)
  rw [volume_snoc_interval hm (by linarith) (by fun_prop) hn hs]
  congr 1
  have hd (r : ℝ) :
      HasDerivAt (fun r : ℝ => -(B - J / 2) * (J - 2 * r)^2 / 4)
        ((J - 2 * r) * (B - J / 2)) r := by
    have hl := ((hasDerivAt_id' r).const_mul 2).const_sub J
    convert ((hl.pow 2).const_mul (-(B - J / 2))).div_const 4
      using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    ((show Continuous (fun r : ℝ => (J - 2 * r) * (B - J / 2)) by fun_prop).intervalIntegrable _ _)]
  ring
theorem cap_volume32 (p : Shape) (hp : Chamber p) :
    32 * (volume (cap p)).toReal = (volume32 p : ℝ) := by
  let b : ℝ := p.b
  let j : ℝ := p.j
  let t : ℝ := p.t
  have hbj : j ≤ b := by
    dsimp [j, b]
    exact_mod_cast hp.1
  have hjt : 3 * t ≤ j := by
    dsimp [t, j]
    exact_mod_cast hp.2
  have ht : 0 ≤ t := by positivity
  have hm : MeasurableSet (cap p) := by
    apply IsClosed.measurableSet
    exact isClosed_nonneg.inter
      ((isClosed_le ((((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2)).add
        (continuous_apply 3)) continuous_const).inter
        ((isClosed_le (f := fun y : Fin 4 → ℝ => y 1 + 2 * y 2 + 3 * y 3)
          (by fun_prop) continuous_const).inter
          (isClosed_le (continuous_apply 3) continuous_const)))
  have hs (s : ℝ) :
      volume {y : Fin 3 → ℝ | snocReal y s ∈ cap p} =
        (Icc 0 t).indicator
          (fun s => ENNReal.ofReal ((j - 3 * s)^2 * (2 * b - j + s) / 8)) s := by
    have he (y : Fin 3 → ℝ) :
        snocReal y s ∈ cap p ↔ s ∈ Icc 0 t ∧ y ∈ cap3 (b - s) (j - 3 * s) := by
      change (∀ i, 0 ≤ snocReal y s i) ∧
        snocReal y s (Fin.castSucc 0) + snocReal y s (Fin.castSucc 1) +
          snocReal y s (Fin.castSucc 2) + snocReal y s (Fin.last 3) ≤ b ∧
        snocReal y s (Fin.castSucc 1) + 2 * snocReal y s (Fin.castSucc 2) +
          3 * snocReal y s (Fin.last 3) ≤ j ∧ snocReal y s (Fin.last 3) ≤ t ↔
        (0 ≤ s ∧ s ≤ t) ∧ (∀ i, 0 ≤ y i) ∧ y 0 + y 1 + y 2 ≤ b - s ∧ y 1 + 2 * y 2 ≤ j - 3*s
      rw [nonneg_snoc]
      simp only [snocReal, Fin.snoc_castSucc, Fin.snoc_last, le_sub_iff_add_le]
      tauto
    by_cases hsi : s ∈ Icc 0 t
    · have hss := hsi.1
      have hst := hsi.2
      have hset : {y : Fin 3 → ℝ | snocReal y s ∈ cap p} = cap3 (b - s) (j - 3 * s) := by
        ext y
        simp [he, hsi]
      rw [hset, indicator_of_mem hsi, volume_cap3 (by linarith) (by linarith)]
      congr 1
      ring
    · have hset : {y : Fin 3 → ℝ | snocReal y s ∈ cap p} = ∅ := by
        ext y
        simp [he, hsi]
      rw [hset, measure_empty, indicator_of_notMem hsi]
  have hn (s : ℝ) (hsi : s ∈ Icc 0 t) : 0 ≤ (j - 3 * s)^2 * (2 * b - j + s) / 8 := by
    have hss := hsi.1
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
  rw [volume_snoc_interval hm ht (by fun_prop) hn hs]
  let A : ℝ → ℝ := fun s =>
    -(2 * b - 2 * j / 3) * (j - 3 * s)^3 / 72 + (j - 3 * s)^4 / 288
  have hd (s : ℝ) : HasDerivAt A ((j - 3 * s)^2 * (2 * b - j + s) / 8) s := by
    have hl := ((hasDerivAt_id' s).const_mul 3).const_sub j
    dsimp [A]
    convert (((hl.pow 3).const_mul (-(2 * b - 2 * j / 3))).div_const 72).add
      ((hl.pow 4).div_const 288) using 1
    simp
    ring
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, (j - 3 * s)^2 * (2 * b - j + s) / 8 :=
    intervalIntegral.integral_nonneg ht hn
  rw [ENNReal.toReal_ofReal hnn, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((show Continuous (fun s : ℝ => (j - 3 * s)^2 * (2 * b - j + s) / 8)
      by fun_prop).intervalIntegrable _ _)]
  simp only [A, b, j, t, volume32, Int.cast_natCast, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring
end K1_13_6_1_4_3
end
section
namespace K1_13_6_1_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_7_1_1
abbrev SliceJets (a h : Shape) := MvPolynomial (Fin 4) (PairSectionField a h)
abbrev extendCoeffs (a h : Shape) : GeoJets →+* SliceJets a h :=
  MvPolynomial.map (algebraMap GeoField (PairSectionField a h))
abbrev firstSection (a h : Shape) : SliceJets a h :=
  sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h)
abbrev secondSection (a h : Shape) : SliceJets a h :=
  sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)
abbrev SliceAlgebra (J : Ideal GeoJets) (a h : Shape) :=
  SliceJets a h ⧸ (J.map (extendCoeffs a h) ⊔ Ideal.span {firstSection a h, secondSection a h})
def CapSupported {k : Type*} [CommSemiring k] (F : MvPolynomial (Fin 4) k) (p : Shape) : Prop :=
  ∀ e ∈ F.support, (fun i => (e i : ℝ)) ∈ cap p
end
end K1_13_6_1_4_3
end
