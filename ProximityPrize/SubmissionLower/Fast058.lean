import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast054
set_option autoImplicit true
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
theorem cut_colon (I : Ideal R) (q : R) (hI : I.IsPrime) (hq : q ∉ I) (n : ℕ) :
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
theorem sup_span_cut_pow (I : Ideal R) (q : R) (n : ℕ) :
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
theorem dimension_eq_hilbert {k σ : Type*} [Field k] [Finite σ]
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
theorem scaled_power_fits {P : GeoJets} {a h : Shape} (hfit : GeoFits P a) :
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
theorem sliced_components_coprime (hslice : c1) {surface : Ideal GeoJets}
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
theorem sum_slice_lengths (hslice : c1) {surface : Ideal GeoJets} {P : GeoJets}
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
open private fastDen fastDen_eq fastC fastOld fastKernel fastKernel_eq from ProximityPrize.SubmissionLower.Numeric6Defs
open private decode runLength sumFrom runValue rowValue rowStart from ProximityPrize.SubmissionLower.Numeric6AuxCert
open private kFast_correct balance denFast_correct from ProximityPrize.SubmissionLower.Numeric5Defs
def eDen (n : ℕ) : ℕ := (n * (n * (2*n+15)+30)+25)/72
theorem eDen_eq (n : ℕ) : denFast n = eDen n := by
  apply Int.ofNat_inj.mp
  rw [denFast_correct, ← fastDen_eq]
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.cast_succ, add_sub_cancel_right, fastDen,
      ite_eq_right (not_lt.mpr (Int.natCast_nonneg _)), eDen, Int.natCast_ediv,
      Nat.cast_mul]
    congr 1
    ring
def eCum (d u : ℕ) : ℕ :=
  if u ≤ d+1 then eDen u else
    let n := min u (3*d+1)
    (eDen n + eDen (n-(2*d+3)) + eDen (n-(2*d+4)) + eDen (n-(2*d+5))) -
      (eDen (n-(d+1)) + eDen (n-(d+2)) + eDen (n-(d+3)))
theorem eCum_eq (d u : ℕ) : cumFast d u = eCum d u := by
  simp only [cumFast, eCum, eDen_eq]
def eThree (n : ℕ) : ℕ := n * (n+2) * (2*n-1) / 24
theorem eThree_eq (n : ℕ) : eDen (n-1) + eDen (n-2) + eDen (n-3) = eThree n := by
  rcases n with _ | ( _ | ( _ | n ) )
  · decide
  · decide
  · decide
  have step (q r : ℕ) (hr : r < 12) :
      eDen (12*q+r+2) + eDen (12*q+r+1) + eDen (12*q+r) =
        ((12*q+r+3) * (12*q+r+5) * (24*q+2*r+5)) / 24 := by
    interval_cases r <;> unfold eDen <;> ring_nf <;> omega
  have h := step (n/12) (n%12) (Nat.mod_lt _ (by decide))
  have hdiv : 12*(n/12)+n%12 = n := by omega
  have h2 : 24*(n/12)+2*(n%12)+5 = 2*(n+3)-1 := by omega
  rw [hdiv,h2] at h
  exact h
theorem eDen_zero : eDen 0 = 0 := rfl
theorem eCum_mid (d u : ℕ) (h3 : u ≤ 3*d+1) (h2 : u ≤ 2*d+3) :
    eCum d u = eDen u - eThree (u-d) := by
  unfold eCum
  split
  · next h =>
      have hx : u-d = 0 ∨ u-d = 1 := by omega
      rcases hx with hx|hx <;> rw [hx] <;> rfl
  · rw [min_eq_left h3]
    dsimp only
    rw [show u-(2*d+3) = 0 by omega, show u-(2*d+4) = 0 by omega,
      show u-(2*d+5) = 0 by omega, eDen_zero]
    simp only [Nat.add_zero, ← eThree_eq, Nat.sub_sub]
def eCore (r dr h l o : ℕ) : ℕ :=
  (h + eDen (o-3*r)) - (eDen o + (eDen l - eThree (l-dr)))
theorem eCore_eq (d u l o r : ℕ) (hr : r ≤ d) (ho : o ≤ d+1)
    (hu3 : u ≤ 3*d+1) (hu2 : u ≤ 2*d+3)
    (hl3 : l ≤ 3*(d-r)+1) (hl2 : l ≤ 2*(d-r)+3) :
    (eCum d u + (if d < r then 0 else eCum (d-r) (o-3*r))) -
      (eCum d o + (if d < r then 0 else eCum (d-r) l)) =
        eCore r (d-r) (eDen u - eThree (u-d)) l o := by
  have hlow (x y : ℕ) (hy : y ≤ x+1) : eCum x y = eDen y := by
    rw [eCum, ite_eq_left hy]
  rw [ite_eq_right (by omega : ¬ d < r), ite_eq_right (by omega : ¬ d < r),
    hlow d o ho, hlow (d-r) (o-3*r) (by omega), eCum_mid _ _ hu3 hu2,
    eCum_mid _ _ hl3 hl2]
  rfl
private def eK (s j a b c : ℕ) : ℕ :=
  let d := 1650-(a+b+3*c)
  let u := 1651-3*(b+c)
  let l := 1650-(j+3*b+2*c)
  let o := 4650-(s+j+2*b+3*c)
  let r := min d ((4649-(s+a+4*c))/4)+1
  (eCum d u + (if d < r then 0 else eCum (d-r) (o-3*r))) -
    (eCum d o + (if d < r then 0 else eCum (d-r) l))
theorem eK_eq (s j a b c : ℕ)
    (hd : a+b+3*c ≤ 1650) (hc : b+c ≤ 550) (hl : c ≤ j+1) (hb : s+a+4*c ≤ 4649) :
    (fastKernel (1650 - ((a : ℤ)+b+3*c)) (1650-j-(3*(b : ℤ)+2*c))
      (550-((b : ℤ)+c)) (4650-s-j-(2*(b : ℤ)+3*c))).toNat = eK s j a b c := by
  let F : Flag := ⟨1650 - ((a : ℤ)+b+3*c),1650-j-(3*(b : ℤ)+2*c),
    3*(550-((b : ℤ)+c)),550-((b : ℤ)+c),4650-s-j-(2*(b : ℤ)+3*c)⟩
  let d := 1650-(a+b+3*c)
  let u := 1651-3*(b+c)
  let r := min d ((4649-(s+a+4*c))/4)+1
  rw [fastKernel_eq]
  change (kernelLower F).toNat = _
  have fd : F.degree = d := by dsimp [F,d]; omega
  have fu : F.upper = (u : ℤ)-1 := by dsimp [F,u]; omega
  have fb : balance F = 4649 - ((s : ℤ)+a+4*c) := by dsimp [F,balance]; ring
  have fr : (r : ℤ) = min F.degree (balance F/4)+1 := by
    rw [fd, fb]
    simp only [r, Nat.cast_add, Nat.cast_one, Nat.cast_min, Int.natCast_ediv, Nat.cast_ofNat,
      Int.ofNat_sub hb, Nat.cast_mul]
  have h := kFast_correct F d u r fd fu (by dsimp [F]; omega) (by dsimp [F]; omega)
    le_rfl (by dsimp [F]; omega) (by rw [fb]; omega) fr
  have fl : F.lower.toNat = 1650-(j+3*b+2*c) := by dsimp [F]; omega
  have fo : F.order.toNat = 4650-(s+j+2*b+3*c) := by dsimp [F]; omega
  rw [← h, fl, fo]
  simp only [kFast, cutFast, eCum_eq, eK, r, u, d]
theorem eBase_eq (s j : ℕ) (hs : s ≤ 4649) :
    (fastKernel 1650 (1650-j) 550 (4650-s-j)).toNat = eK s j 0 0 0 := by
  simpa using eK_eq s j 0 0 0 (by decide) (by decide) (by omega) (by simpa using hs)
theorem eOld_eq (j : ℕ) (hj : j ≤ 1649) :
    (fastOld 1650 (1650-j) 550).toNat = 125576826 - eDen (1650-j) := by
  have he := denFast_correct (1650-j)
  rw [← fastDen_eq, eDen_eq] at he
  have he' : ((1650-j : ℕ) : ℤ)-1 = 1650-(j : ℤ)-1 := by omega
  rw [he'] at he
  have hC : fastC 1650 (1650-j-1) = fastDen (1650-j-1) := by
    simp (disch := omega) [fastC]
    split_ifs <;> omega
  have hhi : fastC 1650 (3*550) = (125576826 : ℕ) := by decide
  rw [fastOld, min_eq_right (by omega), hC, hhi, ← he]
  omega
theorem eClamp (old i r : ℤ) :
    (old-max 0 i).toNat - (old-max (max 0 i) r).toNat =
      min old.toNat r.toNat - i.toNat := by
  omega
def eSaving (s j a b c : ℕ) : ℕ :=
  min (125576826 - eDen (1650-j)) (eK s j a b c) - eK s j 0 0 0
theorem eSaving_eq (s j a b c : ℕ) (hj : j ≤ 1649)
    (hd : a+b+3*c ≤ 1650) (hc : b+c ≤ 550) (hl : c ≤ j+1) (hb : s+a+4*c ≤ 4649) :
    blockSaving s j ⟨a,b,c⟩ = eSaving s j a b c := by
  unfold blockSaving
  dsimp only
  rw [eClamp, eK_eq s j a b c hd hc hl hb, eBase_eq s j (by omega), eOld_eq j hj]
  rfl
private structure EPlan where
  deg : ℕ
  hi : ℕ
  rem : ℕ
  lower : ℕ
  ord : ℕ
def ePlan (s a b c : ℕ) : EPlan :=
  let d := 1650-(a+b+3*c)
  ⟨d, 1651-3*(b+c), min d ((4649-(s+a+4*c))/4)+1,1650-(3*b+2*c),4650-(s+2*b+3*c)⟩
private def EPlan.eval (p : EPlan) (i : ℕ) : ℕ :=
  eCore p.rem (p.deg-p.rem) (eDen p.hi - eThree (p.hi-p.deg)) (p.lower-i) (p.ord-i)
private def EPlan.Valid (p : EPlan) (j : ℕ) : Prop :=
  p.rem ≤ p.deg ∧ p.ord-j ≤ p.deg+1 ∧ p.hi ≤ 3*p.deg+1 ∧ p.hi ≤ 2*p.deg+3 ∧
  p.lower-j ≤ 3*(p.deg-p.rem)+1 ∧ p.lower-j ≤ 2*(p.deg-p.rem)+3
private instance (p : EPlan) (j : ℕ) : Decidable (p.Valid j) := by unfold EPlan.Valid; infer_instance
theorem eValid_of (s j a b c : ℕ) (hs : 3214 ≤ s) (hj : 170 ≤ j)
    (hd : a+b+3*c ≤ 768) (hc : a+4*c ≤ 512) (hab : a ≤ b+384) :
    (ePlan s a b c).Valid j := by
  let d := 1650-(a+b+3*c)
  let r := min d ((4649-(s+a+4*c))/4)+1
  have hd' : d + (a+b+3*c) = 1650 := by dsimp [d]; omega
  have hr : r ≤ 360 := by
    have hm := min_le_right d ((4649-(s+a+4*c))/4)
    dsimp [r]
    omega
  have hdr : d-r+r = d := by omega
  change r ≤ d ∧ 4650-(s+2*b+3*c)-j ≤ d+1 ∧ 1651-3*(b+c) ≤ 3*d+1 ∧
    1651-3*(b+c) ≤ 2*d+3 ∧ 1650-(3*b+2*c)-j ≤ 3*(d-r)+1 ∧
    1650-(3*b+2*c)-j ≤ 2*(d-r)+3
  repeat' constructor <;> omega
theorem ePlan_eq (s j i a b c : ℕ) (h : (ePlan s a b c).Valid j) (hji : j ≤ i) :
    eK s i a b c = (ePlan s a b c).eval i := by
  let p := ePlan s a b c
  change p.Valid j at h
  obtain ⟨hr, ho, hu3, hu2, hl3, hl2⟩ := h
  have he := eCore_eq p.deg p.hi (p.lower-i) (p.ord-i) p.rem hr
    (by omega) hu3 hu2 (by omega) (by omega)
  unfold eK
  rw [show 1650-(i+3*b+2*c) = p.lower-i by dsimp [p,ePlan]; omega,
      show 4650-(s+i+2*b+3*c) = p.ord-i by dsimp [p,ePlan]; omega]
  exact he
def eNatDen (n : ℕ) : ℕ :=
  let x := (Nat.mul 2 n).add 15
  let y := (n.mul x).add 30
  ((n.mul y).add 25).div 72
def eNatThree (n : ℕ) : ℕ :=
  ((n.mul (n.add 2)).mul ((Nat.mul 2 n).sub 1)).div 24
def eNatCore (r dr h l o : ℕ) : ℕ :=
  let tail := (eNatDen l).sub (eNatThree (l.sub dr))
  (h.add (eNatDen (o.sub (Nat.mul 3 r)))).sub ((eNatDen o).add tail)
def eNatPlan (s a b c : ℕ) : EPlan :=
  let d := Nat.sub 1650 ((a.add b).add (Nat.mul 3 c))
  let r := (min d ((Nat.sub 4649 ((s.add a).add (Nat.mul 4 c))).div 4)).add 1
  ⟨d, Nat.sub 1651 (Nat.mul 3 (b.add c)), r,
    Nat.sub 1650 ((Nat.mul 3 b).add (Nat.mul 2 c)),
    Nat.sub 4650 ((s.add (Nat.mul 2 b)).add (Nat.mul 3 c))⟩
def EPlan.natEval (p : EPlan) (i : ℕ) : ℕ :=
  let h := (eNatDen p.hi).sub (eNatThree (p.hi.sub p.deg))
  eNatCore p.rem (p.deg.sub p.rem) h (p.lower.sub i) (p.ord.sub i)
theorem eSum_congr (f g : ℕ → ℕ) (j n : ℕ)
    (h : ∀ i, j ≤ i → i < j+n → f i = g i) :
    sumFrom f j n = sumFrom g j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumFrom, sumFrom, ih (by intro i hi hi'; exact h i hi (by omega)),
      h (j+n) (by omega) (by omega)]
def eRun (s j code : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0 else
    let a := code % 2048
    let b := code / 2048 % 1024
    let c := code / 2097152 % 1024
    let n := runLength code
    let p := eNatPlan s a b c
    let base := eNatPlan s 0 0 0
    if 3214 ≤ s ∧ s ≤ 3260 ∧ 170 ≤ j ∧ j+n ≤ 1650 ∧ a+b+3*c ≤ 768 ∧
        b+c ≤ 550 ∧ a+4*c ≤ 512 ∧ a ≤ b+384 then
      sumFrom (fun i => (min (Nat.sub 125576826 (eNatDen (Nat.sub 1650 i))) (p.natEval i)).sub (base.natEval i)) j n
    else runValue s j code
theorem eRun_eq (s j code : ℕ) : runValue s j code = eRun s j code := by
  unfold eRun
  split
  · rename_i h
    simp only [runValue, h, ite_true]
  · rename_i h
    dsimp only
    split
    · next hg =>
        obtain ⟨hs0, hs1, hj0, hj, hd, hc, hpow, hab⟩ := hg
        have hp := eValid_of _ _ _ _ _ hs0 hj0 hd hpow hab
        have hbase := eValid_of s j 0 0 0 hs0 hj0 (by decide) (by decide) (by decide)
        rw [runValue, ite_eq_right h]
        apply eSum_congr
        intro i hi hi'
        rw [show blockSaving s i (decode code) = _ from
          eSaving_eq _ _ _ _ _ (by omega) (by omega) hc (by omega) (by omega)]
        unfold eSaving
        rw [ePlan_eq s j i _ _ _ hp hi, ePlan_eq s j i _ _ _ hbase hi]
        rfl
    · rfl
def eRow (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => eRun s j code + eRow s (j + runLength code) tail
theorem eRow_eq (s j : ℕ) (row : List ℕ) : rowValue s j row = eRow s j row := by
  induction row generalizing j with
  | nil => rfl
  | cons code tail ih => rw [rowValue, eRow, eRun_eq, ih]
def eGood (s : ℕ) (rs : List (List ℕ)) (n v : ℕ) : Prop :=
  rs.length = n ∧ fits s rs = true ∧ value s rs = v
theorem eNil (s : ℕ) : eGood s [] 0 0 := ⟨rfl, rfl, rfl⟩
theorem eCons (s : ℕ) (row : List ℕ) (n v w : ℕ) {rs : List (List ℕ)}
    (hf : fits s [row] = true) (hv : eRow s (rowStart s) row = v)
    (ht : eGood (s+1) rs n w) : eGood s (row::rs) (n+1) (v+w) := by
  obtain ⟨hn, hfit, hval⟩ := ht
  refine ⟨congrArg Nat.succ hn, ?_, congrArg₂ Nat.add ((eRow_eq _ _ _).trans hv) hval⟩
  change fits s ([row] ++ rs) = true
  rw [fits_append, hf]
  exact hfit
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def eData00 : List ℕ := [180388626432,8724676608,6543638528,6510084096,2198339584,2181562368,25690112,17301504,8912896,524800,36507615744,2147746304,21475099008,4295098752,6442549632,4295033216,49536,2147516800,24960,12672,6528,10737418624,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits00 : fits 3214 [eData00] = true := by decide +kernel
theorem eValue00 : eRow 3214 (rowStart 3214) eData00 = 155243836 := by decide +kernel
def eData01 : List ℕ := [180388626432,8724676608,8691122176,4362600448,2198339584,2181562368,25690112,17301504,13107200,4718592,524800,34360132096,393600,2147746304,21475099008,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,8576,2432,10737418624,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits01 : fits 3215 [eData01] = true := by decide +kernel
theorem eValue01 : eRow 3215 (rowStart 3215) eData01 = 155902452 := by decide +kernel
def eData02 : List ℕ := [182536110080,8724676608,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,6815744,524800,36507615744,4295229952,21475099008,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,12884902272,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits02 : fits 3216 [eData02] = true := by decide +kernel
theorem eValue02 : eRow 3216 (rowStart 3216) eData02 = 156455536 := by decide +kernel
def eData03 : List ℕ := [182536110080,8724676608,6543638528,6510084096,2198339584,2181562368,25690112,17301504,8912896,2148008448,36507615744,4295229952,19327615360,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,12672,2432,10737418624,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits03 : fits 3217 [eData03] = true := by decide +kernel
theorem eValue03 : eRow 3217 (rowStart 3217) eData03 = 157418741 := by decide +kernel
def eData04 : List ℕ := [184683593728,8724676608,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,4718592,524800,38655099392,2147746304,21475099008,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,12884902272,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits04 : fits 3218 [eData04] = true := by decide +kernel
theorem eValue04 : eRow 3218 (rowStart 3218) eData04 = 157729597 := by decide +kernel
def eData05 : List ℕ := [184683593728,8724676608,6543638528,6510084096,2198339584,2181562368,25690112,17301504,8912896,2148008448,36507615744,4295229952,19327615360,4295098752,6442549632,2147549568,2147533184,2147516800,16768,12672,2432,12884902272,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits05 : fits 3219 [eData05] = true := by decide +kernel
theorem eValue05 : eRow 3219 (rowStart 3219) eData05 = 158862003 := by decide +kernel
def eData06 : List ℕ := [186831077376,6577192960,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,2621440,2148008448,36507615744,4295229952,19327615360,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,8576,15032385920,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits06 : fits 3220 [eData06] = true := by decide +kernel
theorem eValue06 : eRow 3220 (rowStart 3220) eData06 = 159089048 := by decide +kernel
def eData07 : List ℕ := [186831077376,8724676608,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,6815744,2148008448,36507615744,6442713600,17180131712,4295098752,6442549632,4295033216,49536,2147516800,24960,12672,4480,12884902272,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits07 : fits 3221 [eData07] = true := by decide +kernel
theorem eValue07 : eRow 3221 (rowStart 3221) eData07 = 160354339 := by decide +kernel
def eData08 : List ℕ := [188978561024,6577192960,6543638528,6510084096,2198339584,2181562368,25690112,17301504,8912896,4295492096,36507615744,4295229952,19327615360,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,8576,15032385920,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits08 : fits 3222 [eData08] = true := by decide +kernel
theorem eValue08 : eRow 3222 (rowStart 3222) eData08 = 160618361 := by decide +kernel
def eData09 : List ℕ := [188978561024,8724676608,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,4718592,2148008448,38655099392,4295229952,17180131712,4295098752,6442549632,4295033216,49536,2147516800,24960,12672,4480,15032385920,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits09 : fits 3223 [eData09] = true := by decide +kernel
theorem eValue09 : eRow 3223 (rowStart 3223) eData09 = 161561426 := by decide +kernel
def eData10 : List ℕ := [191126044672,6577192960,6543638528,6510084096,2198339584,34078720,2173173760,13107200,6815744,4295492096,36507615744,6442713600,17180131712,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,17179869568,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits10 : fits 3224 [eData10] = true := by decide +kernel
theorem eValue10 : eRow 3224 (rowStart 3224) eData10 = 162095917 := by decide +kernel
def eData11 : List ℕ := [191126044672,6577192960,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,6442975744,36507615744,6442713600,15032648064,6442582400,4295065984,4295033216,2147533184,33152,24960,12672,6528,15032385920,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits11 : fits 3225 [eData11] = true := by decide +kernel
theorem eValue11 : eRow 3225 (rowStart 3225) eData11 = 162979865 := by decide +kernel
def eData12 : List ℕ := [191126044672,8724676608,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,6815744,4295492096,36507615744,6442713600,17180131712,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,2432,15032385920,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits12 : fits 3226 [eData12] = true := by decide +kernel
theorem eValue12 : eRow 3226 (rowStart 3226) eData12 = 163971185 := by decide +kernel
def eData13 : List ℕ := [193273528320,6577192960,6543638528,6510084096,2198339584,2181562368,25690112,17301504,8912896,6442975744,36507615744,6442713600,17180131712,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,17179869568,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits13 : fits 3227 [eData13] = true := by decide +kernel
theorem eValue13 : eRow 3227 (rowStart 3227) eData13 = 164253283 := by decide +kernel
def eData14 : List ℕ := [193273528320,101449728,6577192960,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,4718592,4295492096,38655099392,6442713600,15032648064,4295098752,6442549632,2147549568,2147533184,2147516800,16768,12672,2432,17179869568,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits14 : fits 3228 [eData14] = true := by decide +kernel
theorem eValue14 : eRow 3228 (rowStart 3228) eData14 = 164948638 := by decide +kernel
def eData15 : List ℕ := [195421011968,6577192960,6543638528,6510084096,2198339584,34078720,2173173760,13107200,6815744,6442975744,36507615744,8590197248,15032648064,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,17179869568,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits15 : fits 3229 [eData15] = true := by decide +kernel
theorem eValue15 : eRow 3229 (rowStart 3229) eData15 = 165801213 := by decide +kernel
def eData16 : List ℕ := [195421011968,101449728,4429709312,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,8590459392,36507615744,6442713600,15032648064,4295098752,6442549632,2147549568,2147533184,2147516800,24960,12672,2432,17179869568,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits16 : fits 3230 [eData16] = true := by decide +kernel
theorem eValue16 : eRow 3230 (rowStart 3230) eData16 = 166377759 := by decide +kernel
def eData17 : List ℕ := [195421011968,101449728,6577192960,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,4718592,6442975744,38655099392,6442713600,15032648064,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,8576,19327353216,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits17 : fits 3231 [eData17] = true := by decide +kernel
theorem eValue17 : eRow 3231 (rowStart 3231) eData17 = 167161134 := by decide +kernel
def eData18 : List ℕ := [195421011968,2248933376,4429709312,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,8590459392,36507615744,8590197248,12885164416,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,4480,19327353216,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits18 : fits 3232 [eData18] = true := by decide +kernel
theorem eValue18 : eRow 3232 (rowStart 3232) eData18 = 167997202 := by decide +kernel
def eData19 : List ℕ := [197568495616,101449728,6577192960,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,10737943040,36507615744,8590197248,12885164416,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,19327353216,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits19 : fits 3233 [eData19] = true := by decide +kernel
theorem eValue19 : eRow 3233 (rowStart 3233) eData19 = 168577247 := by decide +kernel
def eData20 : List ℕ := [197568495616,2248933376,4429709312,6543638528,6510084096,2198339584,34078720,2173173760,13107200,6815744,8590459392,36507615744,8590197248,12885164416,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,4480,19327353216,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits20 : fits 3234 [eData20] = true := by decide +kernel
theorem eValue20 : eRow 3234 (rowStart 3234) eData20 = 169560076 := by decide +kernel
def eData21 : List ℕ := [197568495616,2248933376,6577192960,6543638528,4362600448,2198339584,2181562368,25690112,17301504,8912896,10737943040,36507615744,8590197248,12885164416,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,21474836864,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits21 : fits 3235 [eData21] = true := by decide +kernel
theorem eValue21 : eRow 3235 (rowStart 3235) eData21 = 170194524 := by decide +kernel
def eData22 : List ℕ := [199715979264,2248933376,4429709312,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,10737943040,38655099392,8590197248,10737680768,6442582400,4295065984,4295033216,2147533184,33152,24960,16768,6528,21474836864,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits22 : fits 3236 [eData22] = true := by decide +kernel
theorem eValue22 : eRow 3236 (rowStart 3236) eData22 = 170808136 := by decide +kernel
def eData23 : List ℕ := [199715979264,4396417024,2282225664,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,10737943040,36507615744,10737680896,10737680768,4295098752,6442549632,2147549568,2147533184,2147516800,16768,12672,2432,19327353216,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits23 : fits 3237 [eData23] = true := by decide +kernel
theorem eValue23 : eRow 3237 (rowStart 3237) eData23 = 171540721 := by decide +kernel
def eData24 : List ℕ := [199715979264,4396417024,4429709312,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,12885426688,36507615744,8590197248,12885164416,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,21474836864,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits24 : fits 3238 [eData24] = true := by decide +kernel
theorem eValue24 : eRow 3238 (rowStart 3238) eData24 = 172181201 := by decide +kernel
def eData25 : List ℕ := [201863462912,4396417024,2282225664,6543638528,6510084096,2198339584,34078720,2173173760,13107200,6815744,10737943040,38655099392,8590197248,10737680768,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,2432,21474836864,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits25 : fits 3239 [eData25] = true := by decide +kernel
theorem eValue25 : eRow 3239 (rowStart 3239) eData25 = 172784521 := by decide +kernel
def eData26 : List ℕ := [201863462912,4396417024,4429709312,6543638528,4362600448,2198339584,2181562368,25690112,17301504,8912896,12885426688,36507615744,10737680896,10737680768,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,8576,23622320512,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits26 : fits 3240 [eData26] = true := by decide +kernel
theorem eValue26 : eRow 3240 (rowStart 3240) eData26 = 173680751 := by decide +kernel
def eData27 : List ℕ := [201863462912,6543900672,2282225664,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,12885426688,38655099392,10737680896,8590197120,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,4480,21474836864,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits27 : fits 3241 [eData27] = true := by decide +kernel
theorem eValue27 : eRow 3241 (rowStart 3241) eData27 = 174511267 := by decide +kernel
def eData28 : List ℕ := [204010946560,4396417024,2282225664,8691122176,4362600448,2198339584,2181562368,25690112,17301504,8912896,12885426688,36507615744,10737680896,10737680768,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,23622320512,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits28 : fits 3242 [eData28] = true := by decide +kernel
theorem eValue28 : eRow 3242 (rowStart 3242) eData28 = 175252391 := by decide +kernel
def eData29 : List ℕ := [204010946560,6543900672,2282225664,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,15032910336,36507615744,10737680896,8590197120,6442582400,4295065984,4295033216,2147533184,33152,24960,12672,4480,23622320512,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits29 : fits 3243 [eData29] = true := by decide +kernel
theorem eValue29 : eRow 3243 (rowStart 3243) eData29 = 175899749 := by decide +kernel
def eData30 : List ℕ := [204010946560,8691384320,134742016,6543638528,6510084096,2198339584,34078720,2173173760,13107200,15032910336,38655099392,10737680896,8590197120,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,25769804160,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits30 : fits 3244 [eData30] = true := by decide +kernel
theorem eValue30 : eRow 3244 (rowStart 3244) eData30 = 176430272 := by decide +kernel
def eData31 : List ℕ := [206158430208,6543900672,2282225664,6543638528,4362600448,2198339584,2181562368,25690112,17301504,8912896,15032910336,36507615744,12885164544,6442713472,6442582400,4295065984,4295033216,2147533184,33152,24960,16768,6528,23622320512,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits31 : fits 3245 [eData31] = true := by decide +kernel
theorem eValue31 : eRow 3245 (rowStart 3245) eData31 = 177468520 := by decide +kernel
def eData32 : List ℕ := [206158430208,6543900672,67895296,134742016,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,15032910336,38655099392,10737680896,8590197120,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,12672,2432,23622320512,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits32 : fits 3246 [eData32] = true := by decide +kernel
theorem eValue32 : eRow 3246 (rowStart 3246) eData32 = 178039748 := by decide +kernel
def eData33 : List ℕ := [206158430208,8691384320,2282225664,6543638528,4362600448,2198339584,2181562368,25690112,17301504,8912896,15032910336,38655099392,10737680896,8590197120,4295098752,4295065984,4295033216,2147533184,33152,24960,16768,6528,25769804160,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits33 : fits 3247 [eData33] = true := by decide +kernel
theorem eValue33 : eRow 3247 (rowStart 3247) eData33 = 178657639 := by decide +kernel
def eData34 : List ℕ := [208305913856,6543900672,67895296,134742016,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,17180393984,36507615744,12885164544,6442713472,6442582400,4295065984,4295033216,49536,2147516800,16768,12672,2432,25769804160,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits34 : fits 3248 [eData34] = true := by decide +kernel
theorem eValue34 : eRow 3248 (rowStart 3248) eData34 = 179451829 := by decide +kernel
def eData35 : List ℕ := [208305913856,6543900672,67895296,134742016,6543638528,6510084096,2198339584,34078720,2173173760,13107200,17180393984,38655099392,12885164544,6442713472,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,25769804160,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits35 : fits 3249 [eData35] = true := by decide +kernel
theorem eValue35 : eRow 3249 (rowStart 3249) eData35 = 180259806 := by decide +kernel
def eData36 : List ℕ := [208305913856,8691384320,67895296,134742016,6543638528,4362600448,2198339584,2181562368,25690112,17301504,8912896,17180393984,36507615744,12885164544,6442713472,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,4480,25769804160,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits36 : fits 3250 [eData36] = true := by decide +kernel
theorem eValue36 : eRow 3250 (rowStart 3250) eData36 = 181171751 := by decide +kernel
def eData37 : List ℕ := [210453397504,6543900672,2215378944,6543638528,4362600448,4345823232,34078720,25690112,17301504,13107200,17180393984,38655099392,12885164544,6442713472,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,27917287808,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits37 : fits 3251 [eData37] = true := by decide +kernel
theorem eValue37 : eRow 3251 (rowStart 3251) eData37 = 181632443 := by decide +kernel
def eData38 : List ℕ := [210453397504,6543900672,2215378944,134742016,6543638528,4362600448,2198339584,2181562368,25690112,17301504,19327877632,38655099392,12885164544,4295229824,6442582400,4295065984,4295033216,2147533184,33152,24960,12672,4480,27917287808,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits38 : fits 3252 [eData38] = true := by decide +kernel
theorem eValue38 : eRow 3252 (rowStart 3252) eData38 = 182411987 := by decide +kernel
def eData39 : List ℕ := [210453397504,8691384320,2215378944,6543638528,4362600448,2198339584,2181562368,25690112,17301504,13107200,19327877632,36507615744,15032648192,4295229824,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,27917287808,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits39 : fits 3253 [eData39] = true := by decide +kernel
theorem eValue39 : eRow 3253 (rowStart 3253) eData39 = 183261778 := by decide +kernel
def eData40 : List ℕ := [212600881152,6543900672,2215378944,8691122176,4362600448,2198339584,34078720,2173173760,13107200,19327877632,38655099392,12885164544,4295229824,6442582400,4295065984,4295033216,2147533184,33152,24960,12672,4480,27917287808,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits40 : fits 3254 [eData40] = true := by decide +kernel
theorem eValue40 : eRow 3254 (rowStart 3254) eData40 = 184022541 := by decide +kernel
def eData41 : List ℕ := [212600881152,6543900672,4362862592,6543638528,4362600448,2198339584,2181562368,25690112,17301504,21475361280,38655099392,12885164544,4295229824,6442582400,4295065984,2147549568,2147533184,2147516800,16768,8576,2432,27917287808,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits41 : fits 3255 [eData41] = true := by decide +kernel
theorem eValue41 : eRow 3255 (rowStart 3255) eData41 = 184497850 := by decide +kernel
def eData42 : List ℕ := [212600881152,8691384320,2215378944,6443073536,6443040768,2148057088,557056,548864,540672,536576,19327877632,38655099392,15032648192,4295229824,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,6528,30064771456,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits42 : fits 3256 [eData42] = true := by decide +kernel
theorem eValue42 : eRow 3256 (rowStart 3256) eData42 = 185549501 := by decide +kernel
def eData43 : List ℕ := [214748364800,6543900672,4362862592,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,2147746176,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,2432,27917287808,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem eFits43 : fits 3257 [eData43] = true := by decide +kernel
theorem eValue43 : eRow 3257 (rowStart 3257) eData43 = 186151215 := by decide +kernel
def eData44 : List ℕ := [214748364800,6543900672,6510346240,6443073536,4295557120,2148057088,557056,2148032512,536576,21475361280,36507615744,15032648192,4295229824,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,6528,30064771456,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem eFits44 : fits 3258 [eData44] = true := by decide +kernel
theorem eValue44 : eRow 3258 (rowStart 3258) eData44 = 186968944 := by decide +kernel
def eData45 : List ℕ := [214748364800,6543900672,6510346240,6443073536,4295557120,2148057088,2148040704,548864,540672,536576,19327877632,38655099392,15032648192,2147746176,6442582400,4295065984,4295033216,49536,2147516800,24960,12672,2432,30064771456,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem eFits45 : fits 3259 [eData45] = true := by decide +kernel
theorem eValue45 : eRow 3259 (rowStart 3259) eData45 = 187924983 := by decide +kernel
def eData46 : List ℕ := [216895848448,6543900672,6510346240,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,2147746176,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,8576,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem eFits46 : fits 3260 [eData46] = true := by decide +kernel
theorem eValue46 : eRow 3260 (rowStart 3260) eData46 = 188282774 := by decide +kernel
def rowsE : List (List ℕ) := [
  eData00, eData01, eData02, eData03, eData04, eData05, eData06, eData07, eData08, eData09, eData10, eData11, eData12, eData13, eData14, eData15, eData16, eData17, eData18, eData19, eData20, eData21, eData22, eData23, eData24, eData25, eData26, eData27, eData28, eData29, eData30, eData31, eData32, eData33, eData34, eData35, eData36, eData37, eData38, eData39, eData40, eData41, eData42, eData43, eData44, eData45, eData46]
theorem checkE :
    rowsE.length = 47 ∧ fits 3214 rowsE = true ∧
      value 3214 rowsE = 8065995700 := by
  change eGood 3214 rowsE 47 8065995700
  exact
    eCons 3214 eData00 46 155243836 7910751864 eFits00 eValue00 <|
    eCons 3215 eData01 45 155902452 7754849412 eFits01 eValue01 <|
    eCons 3216 eData02 44 156455536 7598393876 eFits02 eValue02 <|
    eCons 3217 eData03 43 157418741 7440975135 eFits03 eValue03 <|
    eCons 3218 eData04 42 157729597 7283245538 eFits04 eValue04 <|
    eCons 3219 eData05 41 158862003 7124383535 eFits05 eValue05 <|
    eCons 3220 eData06 40 159089048 6965294487 eFits06 eValue06 <|
    eCons 3221 eData07 39 160354339 6804940148 eFits07 eValue07 <|
    eCons 3222 eData08 38 160618361 6644321787 eFits08 eValue08 <|
    eCons 3223 eData09 37 161561426 6482760361 eFits09 eValue09 <|
    eCons 3224 eData10 36 162095917 6320664444 eFits10 eValue10 <|
    eCons 3225 eData11 35 162979865 6157684579 eFits11 eValue11 <|
    eCons 3226 eData12 34 163971185 5993713394 eFits12 eValue12 <|
    eCons 3227 eData13 33 164253283 5829460111 eFits13 eValue13 <|
    eCons 3228 eData14 32 164948638 5664511473 eFits14 eValue14 <|
    eCons 3229 eData15 31 165801213 5498710260 eFits15 eValue15 <|
    eCons 3230 eData16 30 166377759 5332332501 eFits16 eValue16 <|
    eCons 3231 eData17 29 167161134 5165171367 eFits17 eValue17 <|
    eCons 3232 eData18 28 167997202 4997174165 eFits18 eValue18 <|
    eCons 3233 eData19 27 168577247 4828596918 eFits19 eValue19 <|
    eCons 3234 eData20 26 169560076 4659036842 eFits20 eValue20 <|
    eCons 3235 eData21 25 170194524 4488842318 eFits21 eValue21 <|
    eCons 3236 eData22 24 170808136 4318034182 eFits22 eValue22 <|
    eCons 3237 eData23 23 171540721 4146493461 eFits23 eValue23 <|
    eCons 3238 eData24 22 172181201 3974312260 eFits24 eValue24 <|
    eCons 3239 eData25 21 172784521 3801527739 eFits25 eValue25 <|
    eCons 3240 eData26 20 173680751 3627846988 eFits26 eValue26 <|
    eCons 3241 eData27 19 174511267 3453335721 eFits27 eValue27 <|
    eCons 3242 eData28 18 175252391 3278083330 eFits28 eValue28 <|
    eCons 3243 eData29 17 175899749 3102183581 eFits29 eValue29 <|
    eCons 3244 eData30 16 176430272 2925753309 eFits30 eValue30 <|
    eCons 3245 eData31 15 177468520 2748284789 eFits31 eValue31 <|
    eCons 3246 eData32 14 178039748 2570245041 eFits32 eValue32 <|
    eCons 3247 eData33 13 178657639 2391587402 eFits33 eValue33 <|
    eCons 3248 eData34 12 179451829 2212135573 eFits34 eValue34 <|
    eCons 3249 eData35 11 180259806 2031875767 eFits35 eValue35 <|
    eCons 3250 eData36 10 181171751 1850704016 eFits36 eValue36 <|
    eCons 3251 eData37 9 181632443 1669071573 eFits37 eValue37 <|
    eCons 3252 eData38 8 182411987 1486659586 eFits38 eValue38 <|
    eCons 3253 eData39 7 183261778 1303397808 eFits39 eValue39 <|
    eCons 3254 eData40 6 184022541 1119375267 eFits40 eValue40 <|
    eCons 3255 eData41 5 184497850 934877417 eFits41 eValue41 <|
    eCons 3256 eData42 4 185549501 749327916 eFits42 eValue42 <|
    eCons 3257 eData43 3 186151215 563176701 eFits43 eValue43 <|
    eCons 3258 eData44 2 186968944 376207757 eFits44 eValue44 <|
    eCons 3259 eData45 1 187924983 188282774 eFits45 eValue45 <|
    eCons 3260 eData46 0 188282774 0 eFits46 eValue46 <|
    eNil 3261
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open private fastDen fastC fastOld fastKernel from ProximityPrize.SubmissionLower.Numeric6Defs
open private rowStart rowValue runValue sumFrom runLength decode from ProximityPrize.SubmissionLower.Numeric6AuxCert
set_option maxHeartbeats 2000000
def denF (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 15) + 30) + 25) / 72
def threeF (n : ℕ) : ℕ := denF n + denF (n - 1) + denF (n - 2)
theorem denF_eq (u : ℤ) : fastDen u = (denF (u + 1).toNat : ℤ) := by
  by_cases hu : u < 0
  · rw [show (u + 1).toNat = 0 by omega]
    simp [fastDen, hu, denF]
  lift u to ℕ using (by omega)
  rw [show ((u : ℤ) + 1).toNat = u + 1 by omega]
  simp only [fastDen, not_lt.mpr (Int.natCast_nonneg _), ite_false, denF, Int.natCast_ediv,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  congr 1 <;> ring
theorem threeF_eq (x : ℤ) :
    (threeF x.toNat : ℤ) = fastDen (x-1) + fastDen (x-2) + fastDen (x-3) := by
  simp only [threeF, Nat.cast_add, denF_eq, sub_add_cancel]
  rw [show (x - 2 + 1).toNat = x.toNat - 1 by omega,
    show (x - 3 + 1).toNat = x.toNat - 2 by omega]
private theorem cumF (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ 3 * d) (h₂ : u ≤ 2 * d + 2) :
    fastC d u = (denF (u+1).toNat : ℤ) - threeF (u-d).toNat := by
  by_cases hn : u < 0
  · have hz : (u+1).toNat = 0 := by omega
    have hz' : (u-d).toNat = 0 := by omega
    simp [fastC, hn, hz, hz', threeF, denF]
  simp only [fastC, not_lt.mpr hd, hn, decide_false, Bool.false_or, Bool.false_eq_true,
    ite_false, min_eq_left hu]
  by_cases h : u ≤ d
  · rw [ite_eq_left h, show (u - d).toNat = 0 by omega, denF_eq]
    simp [threeF, denF]
  · rw [ite_eq_right h, ite_eq_left (show u-d ≤ d+2 by omega), threeF_eq, ← denF_eq]
    omega
theorem cumSmallF (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ d) :
    fastC d u = (denF (u+1).toNat : ℤ) := by
  rw [cumF _ _ hd (by omega) (by omega), show (u-d).toNat = 0 by omega]
  simp [threeF, denF]
def kernelF (d l c h r : ℕ) : ℕ :=
  (denF (3*c+1) + denF (h-3*r) + threeF (l+r-(d+1))) -
    (threeF (3*c-d) + denF h + denF l)
theorem kernelF_eq (d l c h r : ℕ)
    (hb : 0 ≤ (h : ℤ)-1-l+d)
    (hr : min (d : ℤ) (((h : ℤ)-1-l+d)/4)+1 = r)
    (hl : (l : ℤ)-1 ≤ 3*c) (hHi : 3*c ≤ 2*d+2) (hc : c ≤ d)
    (hh : h ≤ d+1) (hrle : r ≤ d)
    (hl₂ : l ≤ 2*(d-r)+3) (hl₃ : l ≤ 3*(d-r)+1) :
    (fastKernel d l c h).toNat = kernelF d l c h r := by
  have e₁ := cumF (d : ℤ) (3*c) (by omega) (by omega) (by omega)
  have e₂ := cumSmallF (d : ℤ) ((h : ℤ)-1) (by omega) (by omega)
  have e₃ := cumSmallF ((d : ℤ)-r) ((h : ℤ)-1-3*r) (by omega) (by omega)
  have e₄ := cumF ((d : ℤ)-r) ((l : ℤ)-1) (by omega) (by omega) (by omega)
  rw [show (3*(c : ℤ)+1).toNat = 3*c+1 by omega,
      show (3*(c : ℤ)-d).toNat = 3*c-d by omega] at e₁
  rw [show ((h : ℤ)-1+1).toNat = h by omega] at e₂
  rw [show ((h : ℤ)-1-3*r+1).toNat = h-3*r by omega] at e₃
  rw [show ((l : ℤ)-1+1).toNat = l by omega,
      show ((l : ℤ)-1-(d-r)).toNat = l+r-(d+1) by omega] at e₄
  simp only [fastKernel, not_lt.mpr (Int.natCast_nonneg _), decide_false, Bool.false_or,
    Bool.false_eq_true, ite_false, not_lt.mpr hb, hl, ite_true, hr, e₁, e₂, e₃, e₄]
  unfold kernelF
  omega
private theorem clippedF (a b c : ℤ) :
    (a - max 0 b).toNat - (a - max (max 0 b) c).toNat =
      min a.toNat c.toNat - b.toNat := by omega
abbrev goodF (s a b v t c : ℕ) : Prop :=
  3261 ≤ s ∧ s ≤ 3302 ∧ 148 ≤ a ∧ b ≤ 346 ∧ v+t+3*c ≤ 768 ∧ t+c ≤ 432 ∧
  3*t+2*c+b ≤ 1500 ∧ 2*t+3*c+b ≤ 1100 ∧ v+4*c ≤ 512 ∧ c ≤ a ∧
  2999+v ≤ s+a+t ∧ 2*v+4*c ≤ 1000+t
def cellF (s j v t c : ℕ) : ℕ :=
  let h := 4650-s-j
  let l := 1650-j
  let original := kernelF 1650 l 550 h ((4653-s)/4)
  let residual := kernelF (1650-(v+t+3*c)) (l-(3*t+2*c)) (550-(t+c))
    (h-(2*t+3*c)) ((4653-s-v-4*c)/4)
  min (denF 1651 - denF l) residual - original
theorem cellF_eq (s j a b v t c : ℕ) (ha : a ≤ j) (hb : j ≤ b)
    (hg : goodF s a b v t c) : blockSaving s j ⟨v,t,c⟩ = cellF s j v t c := by
  obtain ⟨hs₀,hs₁,hj₀,hj₁,hv,ht,hlo,hhi,hv₁,hc,hh,hv₂⟩ := hg
  let h := 4650-s-j
  let l := 1650-j
  let r := (4653-s)/4
  have eh : (h : ℤ) = 4650-(s : ℤ)-j := by dsimp [h]; omega
  have el : (l : ℤ) = 1650-(j : ℤ) := by dsimp [l]; omega
  have er : ((h : ℤ)-1-l+1650)/4+1 = r := by dsimp [r]; omega
  have hi := kernelF_eq 1650 l 550 h r (by omega)
    (by simp only [Nat.cast_ofNat]; omega)
    (by omega) (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
  let d := 1650-(v+t+3*c)
  let lo := l-(3*t+2*c)
  let cap := 550-(t+c)
  let ord := h-(2*t+3*c)
  let cut := (4653-s-v-4*c)/4
  have hd : (d : ℤ) = 1650-((v : ℤ)+t+3*c) := by dsimp [d]; omega
  have hl : (lo : ℤ) = (l : ℤ)-(3*t+2*(c : ℤ)) := by dsimp [lo]; omega
  have hp : (cap : ℤ) = 550-((t : ℤ)+c) := by dsimp [cap]; omega
  have ho : (ord : ℤ) = (h : ℤ)-(2*t+3*(c : ℤ)) := by dsimp [ord]; omega
  have ec : ((ord : ℤ)-1-lo+d)/4+1 = cut := by dsimp [cut]; omega
  have hc' : cut ≤ 348 := by dsimp [cut]; omega
  have hd' : 882 ≤ d := by omega
  have hres := kernelF_eq d lo cap ord cut (by omega)
    (by rw [min_eq_right (by omega : ((ord : ℤ)-1-lo+d)/4 ≤ d)]; exact ec)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.cast_ofNat] at hi
  have hold : (fastOld 1650 l 550).toNat = denF 1651 - denF l := by
    unfold fastOld
    rw [min_eq_right (by omega : (l : ℤ)-1 ≤ 3*550)]
    rw [cumSmallF _ _ (by decide) (by decide), cumSmallF _ _ (by decide) (by omega)]
    rw [show ((l : ℤ)-1+1).toNat = l by omega]
    change ((denF 1651 : ℤ) - denF l).toNat = _
    omega
  change (fastOld 1650 (1650-(j : ℤ)) 550 - max 0 (fastKernel 1650 _ 550 _)).toNat -
    (fastOld 1650 (1650-(j : ℤ)) 550 - max (max 0 (fastKernel 1650 _ 550 _))
      (fastKernel _ _ _ _)).toNat = _
  rw [clippedF, ← el, ← eh, ← hd, ← hl, ← hp, ← ho, hold, hi, hres] <;> rfl
def withNatF (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => f 0
  | k+1 => f (Nat.succ k)
theorem withNatF_eq (n : ℕ) (f : ℕ → ℕ) : withNatF n f = f n := by
  cases n <;> rfl
def tripleF (n : ℕ) : ℕ := (n * (n * (2*n+9) + 10) + 3) / 24
theorem denStepF (n : ℕ) :
    denF (n+72) = denF n + (6*n*n + 462*n + 11478) := by
  unfold denF
  rw [show (n+72)*((n+72)*(2*(n+72)+15)+30)+25 =
    n*(n*(2*n+15)+30)+25 + 72*(6*n*n + 462*n + 11478) by ring]
  omega
theorem tripleStepF (n : ℕ) :
    tripleF (n+72) = tripleF n + (18*n*n + 1350*n + 33078) := by
  unfold tripleF
  rw [show (n+72)*((n+72)*(2*(n+72)+9)+10)+3 =
    n*(n*(2*n+9)+10)+3 + 24*(18*n*n + 1350*n + 33078) by ring]
  omega
theorem tripleBaseF : ∀ i : Fin 74, tripleF i = threeF i := by decide +kernel
theorem tripleF_eq (n : ℕ) : tripleF n = threeF n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 74
    · exact tripleBaseF ⟨n,hn⟩
    obtain ⟨m,rfl⟩ : ∃ m, n = m+2+72 := ⟨n-74, by omega⟩
    rw [tripleStepF, ih (m+2) (by omega)]
    unfold threeF
    rw [show m+2+72-1 = (m+1)+72 by omega, show m+2+72-2 = m+72 by omega,
      show m+2-1 = m+1 by omega, show m+2-2 = m by omega]
    rw [denStepF, denStepF, denStepF]
    ring
def cubicF (n : ℕ) : ℕ := withNatF n fun k =>
  Nat.div (Nat.add (Nat.mul k (Nat.add (Nat.mul k (Nat.add (Nat.mul 2 k) 15)) 30)) 25) 72
def correctionF (n : ℕ) : ℕ := withNatF n fun k =>
  Nat.div (Nat.add (Nat.mul k (Nat.add (Nat.mul k (Nat.add (Nat.mul 2 k) 9)) 10)) 3) 24
theorem cubicF_eq (n : ℕ) : cubicF n = denF n := withNatF_eq _ _
theorem correctionF_eq (n : ℕ) : correctionF n = threeF n :=
  Eq.trans (withNatF_eq _ _) (tripleF_eq n)
private def batchF (s j n v t c : ℕ) : ℕ :=
  withNatF (4650-s) fun base =>
  withNatF ((4653-s)/4) fun r₀ =>
  withNatF (1650-(v+t+3*c)) fun d =>
  withNatF (3*(550-(t+c))) fun q =>
  withNatF ((4653-s-v-4*c)/4) fun r =>
  withNatF (3*t+2*c) fun dl =>
  withNatF (2*t+3*c) fun dh =>
  withNatF (cubicF (q+1)) fun cap =>
  withNatF (correctionF (q-d)) fun adj =>
  sumFrom (fun u => withNatF u fun u =>
    withNatF (base-u) fun h =>
    withNatF (1650-u) fun l =>
    withNatF (l-dl) fun ll =>
    withNatF (h-dh) fun hh =>
    withNatF (cubicF l) fun low =>
    let ori := denF 1651 + cubicF (h-3*r₀) + correctionF (l+r₀-1651) -
      (threeF 0 + cubicF h + low)
    let res := cap + cubicF (hh-3*r) + correctionF (ll+r-(d+1)) -
      (adj + cubicF hh + cubicF ll)
    min (denF 1651 - low) res - ori) j n
private theorem batchF_eq (s j n v t c : ℕ) :
    batchF s j n v t c = sumFrom (fun u => cellF s u v t c) j n := by
  simp only [batchF, withNatF_eq, cubicF_eq, correctionF_eq]
  rfl
theorem sumsF (f g : ℕ → ℕ) (j n : ℕ)
    (h : ∀ i < n, f (j+i) = g (j+i)) : sumFrom f j n = sumFrom g j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumFrom, sumFrom, h n (by omega), ih (fun i hi => h i (by omega))]
def runF (s j code : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0 else
    let p := decode code
    let n := runLength code
    if goodF s j (j+n-1) p.value p.top p.cubic then
      batchF s j n p.value p.top p.cubic
    else runValue s j code
theorem runF_eq (s j code : ℕ) : runValue s j code = runF s j code := by
  unfold runF
  by_cases hz : code % 2147483648 = 0
  · simp only [hz, ite_true, runValue]
  rw [ite_eq_right hz]
  dsimp only
  split
  · rename_i hg
    rw [runValue, ite_eq_right hz]
    rw [batchF_eq]
    apply sumsF
    intro i hi
    apply cellF_eq s (j+i) j (j+runLength code-1) _ _ _ (by omega) (by omega) hg
  · rfl
def rowF (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => runF s j code + withNatF (j + runLength code) (fun next => rowF s next tail)
theorem rowF_eq (s j : ℕ) (row : List ℕ) : rowValue s j row = rowF s j row := by
  induction row generalizing j with
  | nil => rfl
  | cons code tail ih => rw [rowValue, rowF, withNatF_eq, runF_eq, ih]
set_option maxRecDepth 50000
theorem joinGradeF (s : ℕ) (row : List ℕ) (tail : List (List ℕ)) (a b : ℕ)
    (first : rowF s (rowStart s) row = a) (rest : value (s+1) tail = b) :
    value s (row :: tail) = a+b :=
  congrArg₂ Nat.add ((rowF_eq _ _ _).trans first) rest
def gradeF3261 : List ℕ :=
  [216895848448,6543900672,6510346240,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,36507615744,17180131840,262528,6442582400,4295065984,4295033216,2147533184,33152,24960,12672,4480,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3261_sum : rowF 3261 (rowStart 3261) gradeF3261 = 189500985 := by
  decide +kernel
def gradeF3262 : List ℕ :=
  [216895848448,6543900672,6510346240,51118080,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,2147746176,6442582400,4295065984,2147549568,2147533184,33152,24960,16768,8576,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3262_sum : rowF 3262 (rowStart 3262) gradeF3262 = 190116103 := by
  decide +kernel
def gradeF3263 : List ℕ :=
  [219043332096,6543900672,6510346240,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,15032648192,262528,6442582400,4295065984,4295033216,2147533184,33152,24960,16768,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3263_sum : rowF 3263 (rowStart 3263) gradeF3263 = 190849659 := by
  decide +kernel
def gradeF3264 : List ℕ :=
  [219043332096,6543900672,6510346240,51118080,6443073536,4295557120,2148057088,2148040704,548864,540672,536576,19327877632,38655099392,17180131840,262528,6442582400,4295065984,4295033216,49536,2147516800,16768,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3264_sum : rowF 3264 (rowStart 3264) gradeF3264 = 191766959 := by
  decide +kernel
def gradeF3265 : List ℕ :=
  [219043332096,6543900672,6510346240,2198601728,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,17180131840,131584,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3265_sum : rowF 3265 (rowStart 3265) gradeF3265 = 192480602 := by
  decide +kernel
def gradeF3266 : List ℕ :=
  [221190815744,6543900672,6510346240,51118080,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,36507615744,17180131840,262528,6442582400,4295065984,4295033216,49536,2147516800,24960,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3266_sum : rowF 3266 (rowStart 3266) gradeF3266 = 193350037 := by
  decide +kernel
def gradeF3267 : List ℕ :=
  [221190815744,6543900672,6510346240,2198601728,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,17180131840,131584,4295098752,6442549632,2147549568,2147533184,33152,24960,16768,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3267_sum : rowF 3267 (rowStart 3267) gradeF3267 = 194135357 := by
  decide +kernel
def gradeF3268 : List ℕ :=
  [221190815744,8691384320,4362862592,2198601728,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,17180131840,131584,4295098752,4295065984,4295033216,2147533184,33152,24960,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3268_sum : rowF 3268 (rowStart 3268) gradeF3268 = 194832653 := by
  decide +kernel
def gradeF3269 : List ℕ :=
  [223338299392,6543900672,6510346240,2198601728,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,17180131840,2147615232,4295098752,4295065984,2147549568,2147533184,33152,24960,400,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3269_sum : rowF 3269 (rowStart 3269) gradeF3269 = 195854339 := by
  decide +kernel
def gradeF3270 : List ℕ :=
  [223338299392,6543900672,6510346240,2198601728,8590557184,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,17180131840,131584,4295098752,4295065984,4295033216,2147533184,33152,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3270_sum : rowF 3270 (rowStart 3270) gradeF3270 = 196550061 := by
  decide +kernel
def gradeF3271 : List ℕ :=
  [223338299392,8691384320,4362862592,4346085376,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,15032648192,2147615232,4295098752,4295065984,4295033216,49536,33152,24960,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3271_sum : rowF 3271 (rowStart 3271) gradeF3271 = 197183677 := by
  decide +kernel
def gradeF3272 : List ℕ :=
  [225485783040,6543900672,6510346240,2198601728,34340864,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,4295098880,2147615104,6442549632,2147549568,2147533184,33152,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3272_sum : rowF 3272 (rowStart 3272) gradeF3272 = 198141595 := by
  decide +kernel
def gradeF3273 : List ℕ :=
  [225485783040,6543900672,6510346240,4346085376,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,15032648192,4295098880,2147615104,4295065984,4295033216,49536,33152,408,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3273_sum : rowF 3273 (rowStart 3273) gradeF3273 = 198941438 := by
  decide +kernel
def gradeF3274 : List ℕ :=
  [227633266688,6543900672,4362862592,4346085376,34340864,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,4295098880,4295098752,4295065984,2147549568,2147533184,33152,408,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3274_sum : rowF 3274 (rowStart 3274) gradeF3274 = 199879452 := by
  decide +kernel
def gradeF3275 : List ℕ :=
  [227633266688,6543900672,6510346240,2198601728,34340864,8590557184,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,15032648192,4295098880,2147615104,4295065984,4295033216,49536,33152,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3275_sum : rowF 3275 (rowStart 3275) gradeF3275 = 200608042 := by
  decide +kernel
def gradeF3276 : List ℕ :=
  [227633266688,6543900672,6510346240,4346085376,34340864,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,12885164544,6442582528,2147615104,4295065984,2147549568,2147533184,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3276_sum : rowF 3276 (rowStart 3276) gradeF3276 = 201206146 := by
  decide +kernel
def gradeF3277 : List ℕ :=
  [229780750336,6543900672,4362862592,4346085376,34340864,655360,6443073536,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,12885164544,197120,6442582528,131456,4295065984,4295033216,2147533184,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3277_sum : rowF 3277 (rowStart 3277) gradeF3277 = 202451264 := by
  decide +kernel
def gradeF3278 : List ℕ :=
  [229780750336,6543900672,6510346240,2198601728,2181824512,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,12885164544,6442582528,2147615104,4295065984,4295033216,49536,416,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3278_sum : rowF 3278 (rowStart 3278) gradeF3278 = 202985770 := by
  decide +kernel
def gradeF3279 : List ℕ :=
  [229780750336,6543900672,6510346240,4346085376,34340864,25952256,6443073536,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,10737680896,197120,6442582528,131456,6442549632,2147549568,49536,2147484064,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3279_sum : rowF 3279 (rowStart 3279) gradeF3279 = 203553092 := by
  decide +kernel
def gradeF3280 : List ℕ :=
  [231928233984,6543900672,4362862592,4346085376,2181824512,8590557184,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,12885164544,8590066176,131456,4295065984,4295033216,49536,416,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3280_sum : rowF 3280 (rowStart 3280) gradeF3280 = 204651414 := by
  decide +kernel
def gradeF3281 : List ℕ :=
  [231928233984,6543900672,6510346240,2198601728,2181824512,25952256,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,10737680896,197120,8590066176,131456,4295065984,2147549568,49536,2147484064,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3281_sum : rowF 3281 (rowStart 3281) gradeF3281 = 205323275 := by
  decide +kernel
def gradeF3282 : List ℕ :=
  [231928233984,6543900672,6510346240,4346085376,34340864,25952256,8590557184,4295557120,2148057088,2148040704,548864,540672,21475361280,38655099392,12885164544,8590066176,131456,4295065984,4295033216,49536,2147484064,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3282_sum : rowF 3282 (rowStart 3282) gradeF3282 = 206524694 := by
  decide +kernel
def gradeF3283 : List ℕ :=
  [234075717632,6543900672,4362862592,4346085376,2181824512,25952256,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,10737680896,197120,8590066176,131456,4295065984,2147549568,49536,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3283_sum : rowF 3283 (rowStart 3283) gradeF3283 = 207049872 := by
  decide +kernel
def gradeF3284 : List ℕ :=
  [234075717632,6543900672,6510346240,2198601728,2181824512,25952256,17563648,6443073536,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,8590197248,197120,10737549824,4295065984,4295033216,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3284_sum : rowF 3284 (rowStart 3284) gradeF3284 = 207591589 := by
  decide +kernel
def gradeF3285 : List ℕ :=
  [236223201280,4396417024,6510346240,4346085376,2181824512,25952256,6443073536,6443040768,2148057088,2148040704,548864,540672,21475361280,38655099392,10737680896,197120,10737549824,4295065984,2147549568,432,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3285_sum : rowF 3285 (rowStart 3285) gradeF3285 = 208788887 := by
  decide +kernel
def gradeF3286 : List ℕ :=
  [236223201280,6543900672,4362862592,4346085376,2181824512,25952256,17563648,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,8590197248,197120,10737549824,6442549632,2147549568,432,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3286_sum : rowF 3286 (rowStart 3286) gradeF3286 = 209383738 := by
  decide +kernel
def gradeF3287 : List ℕ :=
  [236223201280,6543900672,6510346240,2198601728,2181824512,25952256,17563648,8590557184,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,8590197248,197120,10737549824,4295065984,2147549568,2147484080,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3287_sum : rowF 3287 (rowStart 3287) gradeF3287 = 210092969 := by
  decide +kernel
def gradeF3288 : List ℕ :=
  [238370684928,4396417024,6510346240,4346085376,2181824512,25952256,17563648,6443073536,6443040768,2148057088,557056,2148032512,536576,21475361280,38655099392,8590197248,197120,10737549824,98816,4295065984,65920,2147484080,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3288_sum : rowF 3288 (rowStart 3288) gradeF3288 = 211107879 := by
  decide +kernel
def gradeF3289 : List ℕ :=
  [238370684928,6543900672,4362862592,4346085376,2181824512,25952256,17563648,655360,6443073536,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,6442713600,2147680768,10737549824,98816,2147582336,2147549568,2147484080,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3289_sum : rowF 3289 (rowStart 3289) gradeF3289 = 211966003 := by
  decide +kernel
def gradeF3290 : List ℕ :=
  [240518168576,4396417024,6510346240,2198601728,2181824512,2173435904,13369344,6443073536,6443040768,2148057088,2148040704,548864,540672,21475361280,40802583040,6442713600,2147680768,8590066176,98816,4295065984,65920,4294967728,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3290_sum : rowF 3290 (rowStart 3290) gradeF3290 = 212502874 := by
  decide +kernel
def gradeF3291 : List ℕ :=
  [240518168576,4396417024,6510346240,4346085376,2181824512,25952256,17563648,9175040,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,6442713600,2147680768,10737549824,98816,4295065984,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3291_sum : rowF 3291 (rowStart 3291) gradeF3291 = 213482055 := by
  decide +kernel
def gradeF3292 : List ℕ :=
  [240518168576,6543900672,6510346240,2198601728,2181824512,25952256,17563648,13369344,8590557184,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,6442713600,2147680768,8590066176,2147582464,2147582336,65920,4294967728,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3292_sum : rowF 3292 (rowStart 3292) gradeF3292 = 214177691 := by
  decide +kernel
def gradeF3293 : List ℕ :=
  [242665652224,4396417024,6510346240,2198601728,2181824512,2173435904,13369344,9175040,6443073536,6443040768,2148057088,2148040704,548864,540672,21475361280,38655099392,6442713600,2147680768,10737549824,2147582464,2147582336,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3293_sum : rowF 3293 (rowStart 3293) gradeF3293 = 215275834 := by
  decide +kernel
def gradeF3294 : List ℕ :=
  [242665652224,6543900672,4362862592,4346085376,2181824512,25952256,17563648,9175040,655360,6443073536,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,4295229952,4295164416,10737549824,98816,2147582336,448,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3294_sum : rowF 3294 (rowStart 3294) gradeF3294 = 216064133 := by
  decide +kernel
def gradeF3295 : List ℕ :=
  [242665652224,6543900672,6510346240,2198601728,2181824512,25952256,17563648,13369344,7077888,6443073536,6443040768,2148057088,2148040704,548864,540672,21475361280,40802583040,4295229952,2147680768,10737549824,2147582464,2147582336,448,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3295_sum : rowF 3295 (rowStart 3295) gradeF3295 = 216739902 := by
  decide +kernel
def gradeF3296 : List ℕ :=
  [244813135872,4396417024,6510346240,2198601728,2181824512,2173435904,17563648,9175040,2883584,6443073536,4295557120,4295540736,557056,548864,540672,536576,21475361280,38655099392,4295229952,4295164416,10737549824,2147582464,98688,448,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3296_sum : rowF 3296 (rowStart 3296) gradeF3296 = 217586113 := by
  decide +kernel
def gradeF3297 : List ℕ :=
  [244813135872,6543900672,4362862592,4346085376,2181824512,25952256,17563648,13369344,4980736,8590557184,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,4295229952,2147680768,10737549824,4295066112,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3297_sum : rowF 3297 (rowStart 3297) gradeF3297 = 218371725 := by
  decide +kernel
def gradeF3298 : List ℕ :=
  [246960619520,4396417024,6510346240,2198601728,2181824512,25952256,17563648,13369344,7077888,786432,6443073536,6443040768,2148057088,2148040704,548864,540672,21475361280,40802583040,2147746304,4295164416,10737549824,2147582464,98688,2147484096,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3298_sum : rowF 3298 (rowStart 3298) gradeF3298 = 219010769 := by
  decide +kernel
def gradeF3299 : List ℕ :=
  [246960619520,4396417024,6510346240,4346085376,34340864,2173435904,17563648,9175040,2883584,8590557184,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,4295229952,2147680768,10737549824,4295066112,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem gradeF3299_sum : rowF 3299 (rowStart 3299) gradeF3299 = 220134983 := by
  decide +kernel
def gradeF3300 : List ℕ :=
  [246960619520,6543900672,4362862592,4346085376,2181824512,25952256,17563648,13369344,4980736,786432,6443073536,6443040768,2148057088,2148040704,548864,540672,23622844928,38655099392,2147746304,4295164416,10737549824,4295066112,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem gradeF3300_sum : rowF 3300 (rowStart 3300) gradeF3300 = 220688619 := by
  decide +kernel
def gradeF3301 : List ℕ :=
  [249108103168,4396417024,6510346240,2198601728,2181824512,25952256,17563648,13369344,7077888,2148270080,6443073536,4295557120,4295540736,557056,2148032512,536576,21475361280,40802583040,262656,6442648064,8590066176,6442549760,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem gradeF3301_sum : rowF 3301 (rowStart 3301) gradeF3301 = 221398891 := by
  decide +kernel
def gradeF3302 : List ℕ :=
  [249108103168,4396417024,6510346240,4346085376,34340864,2173435904,17563648,9175040,2883584,786432,8590557184,4295557120,2148057088,2148040704,548864,540672,23622844928,38655099392,2147746304,4295164416,10737549824,4295066112,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem gradeF3302_sum : rowF 3302 (rowStart 3302) gradeF3302 = 222513739 := by
  decide +kernel
def tailF3303 : List (List ℕ) := []
theorem tailF3303_sum : value 3303 tailF3303 = 0 := rfl
def tailF3302 : List (List ℕ) := gradeF3302 :: tailF3303
theorem tailF3302_sum : value 3302 tailF3302 = 222513739 :=
  joinGradeF 3302 gradeF3302 tailF3303 222513739 0 gradeF3302_sum tailF3303_sum
def tailF3301 : List (List ℕ) := gradeF3301 :: tailF3302
theorem tailF3301_sum : value 3301 tailF3301 = 443912630 :=
  joinGradeF 3301 gradeF3301 tailF3302 221398891 222513739 gradeF3301_sum tailF3302_sum
def tailF3300 : List (List ℕ) := gradeF3300 :: tailF3301
theorem tailF3300_sum : value 3300 tailF3300 = 664601249 :=
  joinGradeF 3300 gradeF3300 tailF3301 220688619 443912630 gradeF3300_sum tailF3301_sum
def tailF3299 : List (List ℕ) := gradeF3299 :: tailF3300
theorem tailF3299_sum : value 3299 tailF3299 = 884736232 :=
  joinGradeF 3299 gradeF3299 tailF3300 220134983 664601249 gradeF3299_sum tailF3300_sum
def tailF3298 : List (List ℕ) := gradeF3298 :: tailF3299
theorem tailF3298_sum : value 3298 tailF3298 = 1103747001 :=
  joinGradeF 3298 gradeF3298 tailF3299 219010769 884736232 gradeF3298_sum tailF3299_sum
def tailF3297 : List (List ℕ) := gradeF3297 :: tailF3298
theorem tailF3297_sum : value 3297 tailF3297 = 1322118726 :=
  joinGradeF 3297 gradeF3297 tailF3298 218371725 1103747001 gradeF3297_sum tailF3298_sum
def tailF3296 : List (List ℕ) := gradeF3296 :: tailF3297
theorem tailF3296_sum : value 3296 tailF3296 = 1539704839 :=
  joinGradeF 3296 gradeF3296 tailF3297 217586113 1322118726 gradeF3296_sum tailF3297_sum
def tailF3295 : List (List ℕ) := gradeF3295 :: tailF3296
theorem tailF3295_sum : value 3295 tailF3295 = 1756444741 :=
  joinGradeF 3295 gradeF3295 tailF3296 216739902 1539704839 gradeF3295_sum tailF3296_sum
def tailF3294 : List (List ℕ) := gradeF3294 :: tailF3295
theorem tailF3294_sum : value 3294 tailF3294 = 1972508874 :=
  joinGradeF 3294 gradeF3294 tailF3295 216064133 1756444741 gradeF3294_sum tailF3295_sum
def tailF3293 : List (List ℕ) := gradeF3293 :: tailF3294
theorem tailF3293_sum : value 3293 tailF3293 = 2187784708 :=
  joinGradeF 3293 gradeF3293 tailF3294 215275834 1972508874 gradeF3293_sum tailF3294_sum
def tailF3292 : List (List ℕ) := gradeF3292 :: tailF3293
theorem tailF3292_sum : value 3292 tailF3292 = 2401962399 :=
  joinGradeF 3292 gradeF3292 tailF3293 214177691 2187784708 gradeF3292_sum tailF3293_sum
def tailF3291 : List (List ℕ) := gradeF3291 :: tailF3292
theorem tailF3291_sum : value 3291 tailF3291 = 2615444454 :=
  joinGradeF 3291 gradeF3291 tailF3292 213482055 2401962399 gradeF3291_sum tailF3292_sum
def tailF3290 : List (List ℕ) := gradeF3290 :: tailF3291
theorem tailF3290_sum : value 3290 tailF3290 = 2827947328 :=
  joinGradeF 3290 gradeF3290 tailF3291 212502874 2615444454 gradeF3290_sum tailF3291_sum
def tailF3289 : List (List ℕ) := gradeF3289 :: tailF3290
theorem tailF3289_sum : value 3289 tailF3289 = 3039913331 :=
  joinGradeF 3289 gradeF3289 tailF3290 211966003 2827947328 gradeF3289_sum tailF3290_sum
def tailF3288 : List (List ℕ) := gradeF3288 :: tailF3289
theorem tailF3288_sum : value 3288 tailF3288 = 3251021210 :=
  joinGradeF 3288 gradeF3288 tailF3289 211107879 3039913331 gradeF3288_sum tailF3289_sum
def tailF3287 : List (List ℕ) := gradeF3287 :: tailF3288
theorem tailF3287_sum : value 3287 tailF3287 = 3461114179 :=
  joinGradeF 3287 gradeF3287 tailF3288 210092969 3251021210 gradeF3287_sum tailF3288_sum
def tailF3286 : List (List ℕ) := gradeF3286 :: tailF3287
theorem tailF3286_sum : value 3286 tailF3286 = 3670497917 :=
  joinGradeF 3286 gradeF3286 tailF3287 209383738 3461114179 gradeF3286_sum tailF3287_sum
def tailF3285 : List (List ℕ) := gradeF3285 :: tailF3286
theorem tailF3285_sum : value 3285 tailF3285 = 3879286804 :=
  joinGradeF 3285 gradeF3285 tailF3286 208788887 3670497917 gradeF3285_sum tailF3286_sum
def tailF3284 : List (List ℕ) := gradeF3284 :: tailF3285
theorem tailF3284_sum : value 3284 tailF3284 = 4086878393 :=
  joinGradeF 3284 gradeF3284 tailF3285 207591589 3879286804 gradeF3284_sum tailF3285_sum
def tailF3283 : List (List ℕ) := gradeF3283 :: tailF3284
theorem tailF3283_sum : value 3283 tailF3283 = 4293928265 :=
  joinGradeF 3283 gradeF3283 tailF3284 207049872 4086878393 gradeF3283_sum tailF3284_sum
def tailF3282 : List (List ℕ) := gradeF3282 :: tailF3283
theorem tailF3282_sum : value 3282 tailF3282 = 4500452959 :=
  joinGradeF 3282 gradeF3282 tailF3283 206524694 4293928265 gradeF3282_sum tailF3283_sum
def tailF3281 : List (List ℕ) := gradeF3281 :: tailF3282
theorem tailF3281_sum : value 3281 tailF3281 = 4705776234 :=
  joinGradeF 3281 gradeF3281 tailF3282 205323275 4500452959 gradeF3281_sum tailF3282_sum
def tailF3280 : List (List ℕ) := gradeF3280 :: tailF3281
theorem tailF3280_sum : value 3280 tailF3280 = 4910427648 :=
  joinGradeF 3280 gradeF3280 tailF3281 204651414 4705776234 gradeF3280_sum tailF3281_sum
def tailF3279 : List (List ℕ) := gradeF3279 :: tailF3280
theorem tailF3279_sum : value 3279 tailF3279 = 5113980740 :=
  joinGradeF 3279 gradeF3279 tailF3280 203553092 4910427648 gradeF3279_sum tailF3280_sum
def tailF3278 : List (List ℕ) := gradeF3278 :: tailF3279
theorem tailF3278_sum : value 3278 tailF3278 = 5316966510 :=
  joinGradeF 3278 gradeF3278 tailF3279 202985770 5113980740 gradeF3278_sum tailF3279_sum
def tailF3277 : List (List ℕ) := gradeF3277 :: tailF3278
theorem tailF3277_sum : value 3277 tailF3277 = 5519417774 :=
  joinGradeF 3277 gradeF3277 tailF3278 202451264 5316966510 gradeF3277_sum tailF3278_sum
def tailF3276 : List (List ℕ) := gradeF3276 :: tailF3277
theorem tailF3276_sum : value 3276 tailF3276 = 5720623920 :=
  joinGradeF 3276 gradeF3276 tailF3277 201206146 5519417774 gradeF3276_sum tailF3277_sum
def tailF3275 : List (List ℕ) := gradeF3275 :: tailF3276
theorem tailF3275_sum : value 3275 tailF3275 = 5921231962 :=
  joinGradeF 3275 gradeF3275 tailF3276 200608042 5720623920 gradeF3275_sum tailF3276_sum
def tailF3274 : List (List ℕ) := gradeF3274 :: tailF3275
theorem tailF3274_sum : value 3274 tailF3274 = 6121111414 :=
  joinGradeF 3274 gradeF3274 tailF3275 199879452 5921231962 gradeF3274_sum tailF3275_sum
def tailF3273 : List (List ℕ) := gradeF3273 :: tailF3274
theorem tailF3273_sum : value 3273 tailF3273 = 6320052852 :=
  joinGradeF 3273 gradeF3273 tailF3274 198941438 6121111414 gradeF3273_sum tailF3274_sum
def tailF3272 : List (List ℕ) := gradeF3272 :: tailF3273
theorem tailF3272_sum : value 3272 tailF3272 = 6518194447 :=
  joinGradeF 3272 gradeF3272 tailF3273 198141595 6320052852 gradeF3272_sum tailF3273_sum
def tailF3271 : List (List ℕ) := gradeF3271 :: tailF3272
theorem tailF3271_sum : value 3271 tailF3271 = 6715378124 :=
  joinGradeF 3271 gradeF3271 tailF3272 197183677 6518194447 gradeF3271_sum tailF3272_sum
def tailF3270 : List (List ℕ) := gradeF3270 :: tailF3271
theorem tailF3270_sum : value 3270 tailF3270 = 6911928185 :=
  joinGradeF 3270 gradeF3270 tailF3271 196550061 6715378124 gradeF3270_sum tailF3271_sum
def tailF3269 : List (List ℕ) := gradeF3269 :: tailF3270
theorem tailF3269_sum : value 3269 tailF3269 = 7107782524 :=
  joinGradeF 3269 gradeF3269 tailF3270 195854339 6911928185 gradeF3269_sum tailF3270_sum
def tailF3268 : List (List ℕ) := gradeF3268 :: tailF3269
theorem tailF3268_sum : value 3268 tailF3268 = 7302615177 :=
  joinGradeF 3268 gradeF3268 tailF3269 194832653 7107782524 gradeF3268_sum tailF3269_sum
def tailF3267 : List (List ℕ) := gradeF3267 :: tailF3268
theorem tailF3267_sum : value 3267 tailF3267 = 7496750534 :=
  joinGradeF 3267 gradeF3267 tailF3268 194135357 7302615177 gradeF3267_sum tailF3268_sum
def tailF3266 : List (List ℕ) := gradeF3266 :: tailF3267
theorem tailF3266_sum : value 3266 tailF3266 = 7690100571 :=
  joinGradeF 3266 gradeF3266 tailF3267 193350037 7496750534 gradeF3266_sum tailF3267_sum
def tailF3265 : List (List ℕ) := gradeF3265 :: tailF3266
theorem tailF3265_sum : value 3265 tailF3265 = 7882581173 :=
  joinGradeF 3265 gradeF3265 tailF3266 192480602 7690100571 gradeF3265_sum tailF3266_sum
def tailF3264 : List (List ℕ) := gradeF3264 :: tailF3265
theorem tailF3264_sum : value 3264 tailF3264 = 8074348132 :=
  joinGradeF 3264 gradeF3264 tailF3265 191766959 7882581173 gradeF3264_sum tailF3265_sum
def tailF3263 : List (List ℕ) := gradeF3263 :: tailF3264
theorem tailF3263_sum : value 3263 tailF3263 = 8265197791 :=
  joinGradeF 3263 gradeF3263 tailF3264 190849659 8074348132 gradeF3263_sum tailF3264_sum
def tailF3262 : List (List ℕ) := gradeF3262 :: tailF3263
theorem tailF3262_sum : value 3262 tailF3262 = 8455313894 :=
  joinGradeF 3262 gradeF3262 tailF3263 190116103 8265197791 gradeF3262_sum tailF3263_sum
def tailF3261 : List (List ℕ) := gradeF3261 :: tailF3262
theorem tailF3261_sum : value 3261 tailF3261 = 8644814879 :=
  joinGradeF 3261 gradeF3261 tailF3262 189500985 8455313894 gradeF3261_sum tailF3262_sum
def rowsF : List (List ℕ) := tailF3261
theorem checkF :
    rowsF.length = 42 ∧ fits 3261 rowsF = true ∧
      value 3261 rowsF = 8644814879 := by
  refine ⟨rfl, ?_, tailF3261_sum⟩
  decide +kernel
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open private fastDen fastC fastOld fastKernel from ProximityPrize.SubmissionLower.Numeric6Defs
open private sumFrom sumFrom_eq rowValue rowStart runValue runLength decode from ProximityPrize.SubmissionLower.Numeric6AuxCert
def iDen (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 15) + 30) + 25) / 72
theorem iDen_eq (u : ℤ) : (iDen (u + 1).toNat : ℤ) = fastDen u := by
  by_cases hu : u < 0
  · rw [show (u + 1).toNat = 0 by omega, fastDen, ite_eq_left hu]
    rfl
  lift u to ℕ using (by omega)
  rw [show ((u : ℤ) + 1).toNat = u + 1 by omega]
  simp only [iDen, fastDen, not_lt.mpr (Int.natCast_nonneg _), ite_false,
    Int.natCast_ediv, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  ring
def iParts (d n : ℕ) : ℕ × ℕ :=
  let m := Nat.min n (3 * d + 1)
  if m ≤ d + 1 then (iDen m, 0) else
    let a := m - d
    let neg := iDen (a - 1) + iDen (a - 2) + iDen (a - 3)
    if m ≤ 2 * d + 3 then (iDen m, neg) else
      let b := m - 2 * d
      (iDen m + iDen (b - 3) + iDen (b - 4) + iDen (b - 5), neg)
def iSigned (ab : ℕ × ℕ) : ℤ := (ab.1 : ℤ) - ab.2
theorem iParts_eq (d : ℕ) (u : ℤ) :
    iSigned (iParts d (u + 1).toNat) = fastC (d : ℤ) u := by
  by_cases hu : u < 0
  · simp [iParts, iSigned, iDen, fastC, hu, show (u + 1).toNat = 0 by omega]
  let v := min u (3 * (d : ℤ))
  have hvDef : min u (3 * (d : ℤ)) = v := rfl
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hm : Nat.min (u + 1).toNat (3 * d + 1) = (v + 1).toNat := by
    change min (u + 1).toNat (3 * d + 1) = (v + 1).toNat
    dsimp [v]
    omega
  have ha (k : ℕ) : (v + 1).toNat - d - k = (v - (d : ℤ) - k + 1).toNat := by omega
  have hb (k : ℕ) : (v + 1).toNat - 2 * d - k = (v - d - d - k + 1).toNat := by omega
  have h₁ : ((v + 1).toNat ≤ d + 1) ↔ v ≤ (d : ℤ) := by omega
  have h₂ : ((v + 1).toNat ≤ 2 * d + 3) ↔ v - d ≤ (d : ℤ) + 2 := by omega
  simp only [iParts, fastC, not_lt.mpr (Int.natCast_nonneg d), hu, decide_false,
    Bool.false_or, Bool.false_eq_true, ite_false, hm, hvDef, h₁, h₂]
  change iSigned (if v ≤ (d : ℤ) then _ else _) = (if v ≤ (d : ℤ) then _ else _)
  by_cases hsmall : v ≤ (d : ℤ)
  · simp only [ite_eq_left hsmall, iSigned, Nat.cast_zero, sub_zero, iDen_eq]
  · rw [ite_eq_right hsmall, ite_eq_right hsmall]
    by_cases hlarge : v - d ≤ (d : ℤ) + 2
    · simp only [ite_eq_left hlarge, iSigned, ha, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, iDen_eq]
      ring
    · simp only [ite_eq_right hlarge, iSigned, ha, hb, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, iDen_eq]
      ring
def iTriple : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 1) * (k + 3) * (2 * k + 1) / 24
theorem iDen_period (n : ℕ) :
    iDen (n + 12) = iDen n + (n * n + 17 * n + 83) := by
  unfold iDen
  have h : (n + 12) * ((n + 12) * (2 * (n + 12) + 15) + 30) + 25 =
      n * (n * (2 * n + 15) + 30) + 25 + 72 * (n * n + 17 * n + 83) := by ring
  rw [h]
  omega
theorem iTriple_period (n : ℕ) :
    iTriple (n + 12) = iTriple n + (3 * n * n + 39 * n + 161) := by
  cases n with
  | zero => decide
  | succ k =>
    change ((k + 12 + 1) * (k + 12 + 3) * (2 * (k + 12) + 1)) / 24 =
      (k + 1) * (k + 3) * (2 * k + 1) / 24 + (3 * (k + 1) * (k + 1) + 39 * (k + 1) + 161)
    have h : (k + 12 + 1) * (k + 12 + 3) * (2 * (k + 12) + 1) =
        (k + 1) * (k + 3) * (2 * k + 1) + 24 * (3 * (k + 1) * (k + 1) + 39 * (k + 1) + 161) := by ring
    rw [h]
    omega
theorem iTriple_eq (n : ℕ) :
    iTriple n = iDen (n - 1) + iDen (n - 2) + iDen (n - 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 15
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 15 := ⟨n - 15, by omega⟩
      change iTriple ((k + 3) + 12) =
        iDen ((k + 2) + 12) + iDen ((k + 1) + 12) + iDen (k + 12)
      rw [iTriple_period, iDen_period, iDen_period, iDen_period,
        ih (k + 3) (by omega)]
      change iDen (k + 2) + iDen (k + 1) + iDen k + _ = _
      ring
def iFastParts (d n : ℕ) : ℕ × ℕ :=
  let m := Nat.min n (3 * d + 1)
  if m ≤ d + 1 then (iDen m, 0) else
    let neg := iTriple (m - d)
    if m ≤ 2 * d + 3 then (iDen m, neg) else
      (iDen m + iTriple (m - 2 * d - 2), neg)
theorem iFastParts_eq (d n : ℕ) : iFastParts d n = iParts d n := by
  simp only [iFastParts, iParts, iTriple_eq, Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc]
def iKernel (d l cap o r : ℕ) : ℕ :=
  let a := iFastParts d (3 * cap + 1)
  let b := iFastParts d o
  let c := iFastParts (d - r) (o - 3 * r)
  let e := iFastParts (d - r) l
  (a.1 + b.2 + c.1 + e.2) - (a.2 + b.1 + c.2 + e.1)
theorem iMix (a b c e : ℕ × ℕ) :
    (a.1 + b.2 + c.1 + e.2) - (a.2 + b.1 + c.2 + e.1) =
      (iSigned a - iSigned b + iSigned c - iSigned e).toNat := by
  unfold iSigned
  omega
theorem iKernel_eq (d l cap o r : ℕ) (hl : l ≤ 3 * cap + 1)
    (hb : l + 1 ≤ o + d) (hr : r ≤ d)
    (hcut : r = (o + d - (l + 1)) / 4 + 1) :
    iKernel d l cap o r = (fastKernel d l cap o).toNat := by
  have hA := iParts_eq d (3 * (cap : ℤ))
  have hB := iParts_eq d ((o : ℤ) - 1)
  have hC := iParts_eq (d - r) ((o : ℤ) - 1 - 3 * r)
  have hE := iParts_eq (d - r) ((l : ℤ) - 1)
  rw [show (3 * (cap : ℤ) + 1).toNat = 3 * cap + 1 by omega] at hA
  rw [show ((o : ℤ) - 1 + 1).toNat = o by omega] at hB
  rw [show ((o : ℤ) - 1 - 3 * r + 1).toNat = o - 3 * r by omega, Nat.cast_sub hr] at hC
  rw [show ((l : ℤ) - 1 + 1).toNat = l by omega, Nat.cast_sub hr] at hE
  have hpos : ¬ (o : ℤ) - 1 - l + d < 0 := by omega
  have hrem : min (d : ℤ) (((o : ℤ) - 1 - l + d) / 4) + 1 = r := by omega
  simp only [fastKernel, not_lt.mpr (Int.natCast_nonneg _), decide_false, Bool.false_or,
    Bool.false_eq_true, ite_false, hpos, hrem, ite_eq_left (show (l : ℤ) - 1 ≤ 3 * cap by omega)]
  rw [← hA, ← hB, ← hC, ← hE]
  simpa only [iKernel, iFastParts_eq] using iMix (iParts d (3 * cap + 1)) (iParts d o)
    (iParts (d - r) (o - 3 * r)) (iParts (d - r) l)
theorem iOld_eq (j : ℕ) (hj : j ≤ 1650) :
    iDen 1651 - iDen (1650 - j) = (fastOld 1650 (1650 - (j : ℤ)) 550).toNat := by
  have h : fastC 1650 1650 = fastDen 1650 := rfl
  have H : fastC 1650 (1650 - (j : ℤ) - 1) = fastDen (1650 - (j : ℤ) - 1) := by
    unfold fastC
    by_cases hneg : 1650 - (j : ℤ) - 1 < 0
    · simp [fastDen, hneg]
    · have := min_eq_left (show 1650 - (j : ℤ) - 1 ≤ 4950 by omega)
      simp [hneg, this, show 1650 - (j : ℤ) - 1 ≤ 1650 by omega]
  have hh := iDen_eq 1650
  change (iDen 1651 : ℤ) = _ at hh
  have hL := iDen_eq (1650 - (j : ℤ) - 1)
  rw [show (1650 - (j : ℤ) - 1 + 1).toNat = 1650 - j by omega] at hL
  unfold fastOld
  rw [show (3 : ℤ) * 550 = 1650 by decide,
    min_eq_right (show 1650 - (j : ℤ) - 1 ≤ 1650 by omega), h, H]
  omega
theorem iParts_small (d n : ℕ) (h : n ≤ d + 1) :
    iFastParts d n = (iDen n, 0) := by
  have hm : Nat.min n (3 * d + 1) = n := Nat.min_eq_left (by omega)
  simp only [iFastParts, hm, ite_eq_left h]
theorem iParts_mid (d n : ℕ) (hm : n ≤ 3 * d + 1) (h : n ≤ 2 * d + 3) :
    iFastParts d n = (iDen n, iTriple (n - d)) := by
  simp only [iFastParts, Nat.min_eq_left hm, ite_eq_left h]
  split
  · rename_i hs
    rcases (show n - d = 0 ∨ n - d = 1 by omega) with he | he <;> rw [he] <;> rfl
  · rfl
def iBase (s j : ℕ) : ℕ :=
  let o := 4650 - (s + j)
  let r := (4649 - s) / 4 + 1
  iDen 1651 + iDen (o - 3 * r) + iTriple (r - j) - (iDen o + iDen (1650 - j))
theorem iBase_eq (s j : ℕ) (hs : 3000 ≤ s) :
    iBase s j = iKernel 1650 (1650 - j) 550 (4650 - (s + j)) ((4649 - s) / 4 + 1) := by
  let o := 4650 - (s + j)
  let r := (4649 - s) / 4 + 1
  have ho : o ≤ 1651 := by dsimp [o]; omega
  have hr : r ≤ 500 := by dsimp [r]; omega
  change iDen 1651 + iDen (o - 3 * r) + iTriple (r - j) - (iDen o + iDen (1650 - j)) =
    iKernel 1650 (1650 - j) 550 o r
  simp only [iKernel, iParts_small 1650 1651 (by decide), iParts_small 1650 o ho,
    iParts_small (1650 - r) (o - 3 * r) (by omega), iParts_mid (1650 - r) (1650 - j) (by omega) (by omega),
    show 1650 - j - (1650 - r) = r - j by omega, Nat.add_zero, Nat.zero_add]
def iEntry (s j v t c : ℕ) : ℕ :=
  let d := 1650 - (v + t + 3 * c)
  let cap := 550 - (t + c)
  let l := 1650 - (j + 3 * t + 2 * c)
  let o := 4650 - (s + j + 2 * t + 3 * c)
  let r := (4649 - (s + v + 4 * c)) / 4 + 1
  let base := iBase s j
  Nat.min (iDen 1651 - iDen (1650 - j)) (iKernel d l cap o r) - base
def iValid (s j n v t c : ℕ) : Bool :=
  decide (3000 ≤ s ∧ v + t + 3 * c ≤ 1650 ∧ t + c ≤ 550 ∧
    s + j + n + 2 * t + 3 * c ≤ 4651 ∧ j + n + 3 * t + 2 * c ≤ 1651 ∧
    c ≤ j + 1 ∧ s + v + 4 * c ≤ 4649 ∧
    (4649 - (s + v + 4 * c)) / 4 + 1 ≤ 1650 - (v + t + 3 * c))
theorem iClip (old base chosen : ℤ) :
    Nat.min old.toNat chosen.toNat - base.toNat =
      (old - max 0 base).toNat - (old - max (max 0 base) chosen).toNat := by
  change min _ _ - _ = _
  omega
theorem iEntry_eq (s j n k v t c : ℕ) (hk : k < n)
    (hg : iValid s j n v t c = true) :
    iEntry s (j + k) v t c = blockSaving s (j + k) ⟨v, t, c⟩ := by
  unfold iValid at hg
  replace hg := of_decide_eq_true hg
  rcases hg with ⟨hs, hd, hc, ho, hl, hcap, hb, hr⟩
  let x := j + k
  change iEntry s x v t c = blockSaving s x _
  have hx₁ : x + 3 * t + 2 * c ≤ 1650 := by dsimp [x]; omega
  have hx₂ : s + x + 2 * t + 3 * c ≤ 4650 := by dsimp [x]; omega
  have hx₃ : c ≤ x + 1 := by dsimp [x]; omega
  have h₀ := iKernel_eq 1650 (1650 - x) 550 (4650 - (s + x)) ((4649 - s) / 4 + 1)
    (by omega) (by omega) (by omega) (by omega)
  have h₁ := iKernel_eq (1650 - (v + t + 3 * c)) (1650 - (x + 3 * t + 2 * c))
    (550 - (t + c)) (4650 - (s + x + 2 * t + 3 * c)) ((4649 - (s + v + 4 * c)) / 4 + 1)
    (by omega) (by omega) hr (by omega)
  have ed : (↑(1650 - (v + t + 3 * c) : ℕ) : ℤ) = 1650 - ((v : ℤ) + t + 3 * c) := by omega
  have ec : (↑(550 - (t + c) : ℕ) : ℤ) = 550 - ((t : ℤ) + c) := by omega
  have el : (↑(1650 - (x + 3 * t + 2 * c) : ℕ) : ℤ) = 1650 - (x : ℤ) - (3 * t + 2 * c) := by omega
  have eo : (↑(4650 - (s + x + 2 * t + 3 * c) : ℕ) : ℤ) = 4650 - (s : ℤ) - x - (2 * t + 3 * c) := by omega
  rw [ed, el, ec, eo] at h₁
  rw [show (↑(1650 - x : ℕ) : ℤ) = 1650 - (x : ℤ) by omega,
    show (↑(4650 - (s + x) : ℕ) : ℤ) = 4650 - (s : ℤ) - x by omega] at h₀
  dsimp only [iEntry]
  rw [iBase_eq _ _ hs, h₀, h₁, iOld_eq x (by omega)]
  exact iClip _ _ _
def iRegular (s j v t c : ℕ) : Bool :=
  let d := 1650 - (v + t + 3 * c)
  let cap := 550 - (t + c)
  let dr := d - ((4649 - (s + v + 4 * c)) / 4 + 1)
  let l := 1650 - (j + 3 * t + 2 * c)
  let o := 4650 - (s + j + 2 * t + 3 * c)
  decide (2 ≤ dr ∧ 3 * cap + 1 ≤ 2 * d + 3 ∧ o ≤ d + 1 ∧ l ≤ 2 * dr + 3)
def iCheap (s j v t c : ℕ) : ℕ :=
  let d := 1650 - (v + t + 3 * c)
  let r := (4649 - (s + v + 4 * c)) / 4 + 1
  let dr := d - r
  let hi := 3 * (550 - (t + c)) + 1
  let l := 1650 - (j + 3 * t + 2 * c)
  let o := 4650 - (s + j + 2 * t + 3 * c)
  let chosen := iDen hi + iDen (o - 3 * r) + iTriple (l - dr) - (iTriple (hi - d) + iDen o + iDen l)
  Nat.min (iDen 1651 - iDen (1650 - j)) chosen - iBase s j
theorem iRegular_kernel (d cap o l r : ℕ) (hd : 2 ≤ d - r)
    (hh : 3 * cap + 1 ≤ 2 * d + 3) (ho : o ≤ d + 1) (hl : l ≤ 2 * (d - r) + 3) :
    iKernel d l cap o r =
      iDen (3 * cap + 1) + iDen (o - 3 * r) + iTriple (l - (d - r)) -
        (iTriple (3 * cap + 1 - d) + iDen o + iDen l) := by
  simp only [iKernel, iParts_mid d (3 * cap + 1) (by omega) hh, iParts_small d o ho,
    iParts_small (d - r) (o - 3 * r) (by omega), iParts_mid (d - r) l (by omega) hl,
    Nat.add_zero]
theorem iCheap_eq (s j k v t c : ℕ) (h : iRegular s j v t c = true) :
    iCheap s (j + k) v t c = iEntry s (j + k) v t c := by
  dsimp only [iRegular] at h
  rcases of_decide_eq_true h with ⟨hd, hh, ho, hl⟩
  dsimp only [iEntry, iCheap]
  rw [iRegular_kernel _ _ _ _ _ hd hh (by omega) (by omega)]
def iRun (s j code : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0 else
    let p := decode code
    if iValid s j (runLength code) p.value p.top p.cubic && iRegular s j p.value p.top p.cubic then
      sumFrom (fun x => iCheap s x p.value p.top p.cubic) j (runLength code)
    else runValue s j code
theorem iRun_eq (s j code : ℕ) : iRun s j code = runValue s j code := by
  unfold iRun
  by_cases hz : code % 2147483648 = 0
  · simp [runValue, hz]
  simp only [ite_eq_right hz]
  split
  · rename_i h
    rw [runValue, ite_eq_right hz, sumFrom_eq, sumFrom_eq]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := Bool.and_eq_true_iff.mp h
    rw [iCheap_eq _ _ _ _ _ _ hh.2]
    exact iEntry_eq _ _ _ _ _ _ _ (Finset.mem_range.mp hk) hh.1
  · rfl
def iRow (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => iRun s j code + iRow s (j + runLength code) tail
theorem iRow_eq (s j : ℕ) (row : List ℕ) : iRow s j row = rowValue s j row := by
  induction row generalizing j with
  | nil => rfl
  | cons x xs ih => rw [iRow, rowValue, iRun_eq, ih]
theorem iRowCons {s a b : ℕ} {row : List ℕ} {tail : List (List ℕ)}
    (h : iRow s (rowStart s) row = a) (ht : value (s + 1) tail = b) :
    value s (row :: tail) = a + b := by
  rw [value, ← iRow_eq, h, ht]
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def rowsI_part000 : List ℕ := [173946175488,4362862592,2198601728,2181824512,25952256,17563648,9175040,19328140032,19328139264,25770328832,548864,540672,25770328576,25770197504,8590131712,8590066176,6442549760,2147549696,2147533312,2147516928,16896,12800,4608,10737418752,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow000 : iRow 3379 23 rowsI_part000 = 284516493 := by decide +kernel
def rowsI_part001 : List ℕ := [173946175488,2215378944,4346085376,34340864,25952256,17563648,13369344,21475623680,19328139264,25770328832,548864,27917812224,25770197504,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,12884902400,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow001 : iRow 3380 23 rowsI_part001 = 284859648 := by decide +kernel
def rowsI_part002 : List ℕ := [171798691840,4362862592,2198601728,2181824512,25952256,13369344,7077888,21475623680,17180655616,27917812480,548864,25770328576,25770197504,8590131712,8590066176,6442549760,2147549696,2147533312,2147516928,25088,12800,4608,12884902400,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow002 : iRow 3381 23 rowsI_part002 = 286235657 := by decide +kernel
def rowsI_part003 : List ℕ := [171798691840,2215378944,2198601728,2181824512,25952256,17563648,9175040,23623107328,17180655616,27917812480,27917812224,25770197504,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,12884902400,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow003 : iRow 3382 23 rowsI_part003 = 286716111 := by decide +kernel
def rowsI_part004 : List ℕ := [169651208192,4362862592,2198601728,34340864,25952256,17563648,13369344,23623107328,19328139264,27917812480,25770328576,25770197504,8590131712,8590066176,6442549760,4295033344,49664,2147516928,25088,12800,4608,12884902400,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow004 : iRow 3383 23 rowsI_part004 = 287696107 := by decide +kernel
def rowsI_part005 : List ℕ := [169651208192,2148335616,2148319232,2148302848,811008,802816,794624,23623107328,17180655616,30065296128,25770328576,25770197504,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,15032386048,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow005 : iRow 3384 23 rowsI_part005 = 288381596 := by decide +kernel
def rowsI_part006 : List ℕ := [167503724544,4295819264,2148319232,819200,811008,802816,798720,25770590976,17180655616,27917812480,27917812224,25770197504,8590131712,6442582528,6442549760,4295033344,49664,2147516928,25088,12800,6656,15032386048,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow006 : iRow 3385 23 rowsI_part006 = 288856415 := by decide +kernel
def rowsI_part007 : List ℕ := [167503724544,2148335616,2148319232,2148302848,811008,802816,794624,25770590976,15033171968,30065296128,25770328576,25770197504,8590131712,8590066176,6442549760,2147549696,2147533312,33280,25088,16896,8704,2560,12884902400,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow007 : iRow 3386 23 rowsI_part007 = 290207678 := by decide +kernel
def rowsI_part008 : List ℕ := [165356240896,4295819264,2148319232,2148302848,811008,798720,792576,23623107328,17180655616,30065296128,25770328576,25770197504,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,15032386048,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow008 : iRow 3387 23 rowsI_part008 = 290676071 := by decide +kernel
def rowsI_part009 : List ℕ := [165356240896,2148335616,4295802880,819200,811008,802816,798720,25770590976,17180655616,30065296128,25770328576,23622713856,8590131712,8590066176,6442549760,2147549696,2147533312,33280,25088,16896,12800,2560,15032386048,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow009 : iRow 3388 23 rowsI_part009 = 291324758 := by decide +kernel
def rowsI_part010 : List ℕ := [163208757248,4295819264,2148319232,2148302848,811008,802816,794624,25770590976,15033171968,30065296128,25770328576,25770197504,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,17179869696,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow010 : iRow 3389 23 rowsI_part010 = 292375125 := by decide +kernel
def rowsI_part011 : List ℕ := [163208757248,4295819264,2148319232,819200,811008,802816,798720,27918074624,15033171968,30065296128,25770328576,23622713856,8590131712,8590066176,6442549760,2147549696,2147533312,2147516928,16896,12800,2560,15032386048,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow011 : iRow 3390 23 rowsI_part011 = 293191942 := by decide +kernel
def rowsI_part012 : List ℕ := [161061273600,4295819264,2148319232,2148302848,811008,802816,794624,25770590976,17180655616,30065296128,25770328576,23622713856,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,17179869696,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow012 : iRow 3391 23 rowsI_part012 = 293595637 := by decide +kernel
def rowsI_part013 : List ℕ := [161061273600,4295819264,2148319232,819200,2148294656,798720,792576,25770590976,15033171968,32212779776,23622844928,25770197504,8590131712,6442582528,6442549760,2147549696,2147533312,2147516928,25088,12800,4608,17179869696,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow013 : iRow 3392 23 rowsI_part013 = 294510200 := by decide +kernel
def rowsI_part014 : List ℕ := [161061273600,2148335616,2148319232,2148302848,811008,802816,798720,27918074624,15033171968,30065296128,25770328576,23622713856,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,19327353344,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow014 : iRow 3393 23 rowsI_part014 = 295273394 := by decide +kernel
def rowsI_part015 : List ℕ := [158913789952,4295819264,2148319232,2148302848,811008,802816,794624,27918074624,12885688320,32212779776,25770328576,23622713856,8590131712,8590066176,4295066112,4295033344,49664,2147516928,25088,12800,4608,17179869696,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow015 : iRow 3394 23 rowsI_part015 = 296089947 := by decide +kernel
def rowsI_part016 : List ℕ := [158913789952,4295819264,2148319232,819200,811008,802816,798720,27918074624,15033171968,32212779776,23622844928,23622713856,8590131712,8590066176,6442549760,2147549696,2147533312,33280,25088,16896,8704,19327353344,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow016 : iRow 3395 23 rowsI_part016 = 297035960 := by decide +kernel
def rowsI_part017 : List ℕ := [156766306304,4295819264,2148319232,2148302848,811008,802816,794624,27918074624,15033171968,32212779776,23622844928,23622713856,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,12800,6656,19327353344,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow017 : iRow 3396 23 rowsI_part017 = 297438467 := by decide +kernel
def rowsI_part018 : List ℕ := [156766306304,4295819264,2148319232,819200,2148294656,798720,30065558272,12885688320,32212779776,25770328576,21475230208,8590131712,8590066176,6442549760,2147549696,2147533312,33280,25088,16896,8704,2560,19327353344,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow018 : iRow 3397 23 rowsI_part018 = 298467734 := by decide +kernel
def rowsI_part019 : List ℕ := [154618822656,4295819264,2148319232,2148302848,811008,802816,798720,30065558272,12885688320,32212779776,23622844928,23622713856,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,19327353344,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow019 : iRow 3398 23 rowsI_part019 = 299277284 := by decide +kernel
def rowsI_part020 : List ℕ := [154618822656,4295819264,2148319232,2148302848,811008,802816,794624,27918074624,15033171968,32212779776,23622844928,23622713856,8590131712,6442582528,6442549760,2147549696,2147533312,2147516928,16896,12800,2560,19327353344,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow020 : iRow 3399 23 rowsI_part020 = 299609780 := by decide +kernel
def rowsI_part021 : List ℕ := [152471339008,4295819264,4295802880,819200,811008,802816,798720,30065558272,12885688320,34360263424,23622844928,21475230208,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,21474836992,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow021 : iRow 3400 23 rowsI_part021 = 300631518 := by decide +kernel
def rowsI_part022 : List ℕ := [152471339008,4295819264,2148319232,2148302848,811008,802816,794624,30065558272,12885688320,32212779776,23622844928,23622713856,8590131712,8590066176,4295066112,4295033344,49664,2147516928,25088,12800,2560,21474836992,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow022 : iRow 3401 23 rowsI_part022 = 301330653 := by decide +kernel
def rowsI_part023 : List ℕ := [150323855360,884736,4295819264,2148319232,819200,2148294656,798720,32213041920,12885688320,32212779776,23622844928,21475230208,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,8704,21474836992,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow023 : iRow 3402 23 rowsI_part023 = 302123594 := by decide +kernel
def rowsI_part024 : List ℕ := [150323855360,4295819264,2148319232,2148302848,811008,802816,798720,30065558272,12885688320,34360263424,23622844928,21475230208,8590131712,8590066176,4295066112,4295033344,49664,2147516928,25088,12800,4608,21474836992,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow024 : iRow 3403 23 rowsI_part024 = 302798684 := by decide +kernel
def rowsI_part025 : List ℕ := [148176371712,884736,4295819264,2148319232,2148302848,811008,802816,794624,30065558272,12885688320,34360263424,21475361280,21475230208,8590131712,8590066176,6442549760,2147549696,2147533312,33280,25088,16896,8704,23622320640,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow025 : iRow 3404 23 rowsI_part025 = 303772817 := by decide +kernel
def rowsI_part026 : List ℕ := [148176371712,4295819264,4295802880,819200,811008,802816,798720,32213041920,10738204672,34360263424,23622844928,21475230208,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,12800,4608,23622320640,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow026 : iRow 3405 23 rowsI_part026 = 304488891 := by decide +kernel
def rowsI_part027 : List ℕ := [146028888064,884736,4295819264,2148319232,2148302848,811008,802816,794624,32213041920,10738204672,34360263424,23622844928,19327746560,10737615360,6442582528,6442549760,2147549696,2147533312,33280,25088,16896,8704,23622320640,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow027 : iRow 3406 23 rowsI_part027 = 305287847 := by decide +kernel
def rowsI_part028 : List ℕ := [143881404416,25166848,6443302912,2148319232,2148302848,811008,798720,32213041920,12885688320,34360263424,21475361280,21475230208,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,23622320640,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow028 : iRow 3407 23 rowsI_part028 = 305924185 := by decide +kernel
def rowsI_part029 : List ℕ := [143881404416,884736,4295819264,2148319232,2148302848,811008,802816,798720,32213041920,10738204672,36507747072,21475361280,21475230208,8590131712,8590066176,4295066112,2147549696,2147533312,33280,25088,16896,12800,2560,23622320640,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow029 : iRow 3408 23 rowsI_part029 = 306613057 := by decide +kernel
def rowsI_part030 : List ℕ := [141733920768,25166848,884736,4295819264,2148319232,2148302848,811008,802816,794624,32213041920,10738204672,34360263424,23622844928,19327746560,8590131712,8590066176,4295066112,4295033344,2147533312,33280,25088,16896,6656,25769804288,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow030 : iRow 3409 23 rowsI_part030 = 307312412 := by decide +kernel
def rowsI_part031 : List ℕ := [139586437120,2172650496,4295819264,4295802880,819200,811008,802816,798720,34360525568,10738204672,34360263424,21475361280,21475230208,8590131712,8590066176,4295066112,4295033344,49664,2147516928,16896,12800,2560,23622320640,4294967744,6442451376,4294967712,2147484056,400,396,392,388,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
theorem iRow031 : iRow 3410 23 rowsI_part031 = 308034104 := by decide +kernel
def rowsI_part032 : List ℕ := [139586437120,25166848,884736,4295819264,2148319232,2148302848,811008,802816,798720,32213041920,10738204672,36507747072,21475361280,19327746560,10737615360,6442582528,6442549760,2147549696,2147533312,33280,25088,16896,8704,25769804288,4294967744,6442451376,4294967712,2147484056,400,396,392,387,32212255104,4294967616,6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3]
theorem iRow032 : iRow 3411 23 rowsI_part032 = 309035077 := by decide +kernel
def rowsI_part033 : List ℕ := [137438953472,25166848,16778240,6443302912,2148319232,2148302848,811008,802816,34360525568,10738204672,36507747072,19327877632,21475230208,8590131712,8590066176,4295066112,4295033344,49664,2147516928,25088,12800,4608,25769804288,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,386,32212255104,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
theorem iRow033 : iRow 3412 23 rowsI_part033 = 309622213 := by decide +kernel
def rowsI_part034 : List ℕ := [137438953472,25166848,884736,4295819264,2148319232,2148302848,811008,802816,798720,34360525568,10738204672,34360263424,21475361280,21475230208,8590131712,6442582528,6442549760,2147549696,2147533312,33280,25088,16896,8704,27917287936,2147484096,6442451376,4294967712,2147484056,2147484048,396,390,385,30064771456,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
theorem iRow034 : iRow 3413 23 rowsI_part034 = 310081354 := by decide +kernel
def rowsI : List (List ℕ) :=
  [rowsI_part000, rowsI_part001, rowsI_part002, rowsI_part003, rowsI_part004,
   rowsI_part005, rowsI_part006, rowsI_part007, rowsI_part008, rowsI_part009,
   rowsI_part010, rowsI_part011, rowsI_part012, rowsI_part013, rowsI_part014,
   rowsI_part015, rowsI_part016, rowsI_part017, rowsI_part018, rowsI_part019,
   rowsI_part020, rowsI_part021, rowsI_part022, rowsI_part023, rowsI_part024,
   rowsI_part025, rowsI_part026, rowsI_part027, rowsI_part028, rowsI_part029,
   rowsI_part030, rowsI_part031, rowsI_part032, rowsI_part033, rowsI_part034]
theorem checkI :
    rowsI.length = 35 ∧ fits 3379 rowsI = true ∧
      value 3379 rowsI = 10413392410 := by
  refine ⟨rfl, by decide +kernel, ?_⟩
  exact iRowCons iRow000 <| iRowCons iRow001 <| iRowCons iRow002 <| iRowCons iRow003 <|
    iRowCons iRow004 <| iRowCons iRow005 <| iRowCons iRow006 <| iRowCons iRow007 <|
    iRowCons iRow008 <| iRowCons iRow009 <| iRowCons iRow010 <| iRowCons iRow011 <|
    iRowCons iRow012 <| iRowCons iRow013 <| iRowCons iRow014 <| iRowCons iRow015 <|
    iRowCons iRow016 <| iRowCons iRow017 <| iRowCons iRow018 <| iRowCons iRow019 <|
    iRowCons iRow020 <| iRowCons iRow021 <| iRowCons iRow022 <| iRowCons iRow023 <|
    iRowCons iRow024 <| iRowCons iRow025 <| iRowCons iRow026 <| iRowCons iRow027 <|
    iRowCons iRow028 <| iRowCons iRow029 <| iRowCons iRow030 <| iRowCons iRow031 <|
    iRowCons iRow032 <| iRowCons iRow033 <| iRowCons iRow034 <|
    (show value 3414 [] = 0 from rfl)
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
private local instance (priority := high) jetEval (I : Ideal Ambient) : Algebra SlopeField[X] (SlopeRing I) :=
  (Polynomial.aeval (jetForm I) : _ →ₐ[SlopeField] SlopeRing I).toRingHom.toAlgebra
private local instance (priority := high) jetModule (I : Ideal Ambient) :
    Module SlopeField[X] (SlopeRing I) :=
  (jetEval I).toModule
private abbrev Fibre (I : Ideal Ambient) :=
  letI : Algebra SlopeField[X] (SlopeRing I) := jetEval I
  InterceptField ⊗[SlopeField[X]] SlopeRing I
private abbrev mixedIdeal (I : Ideal Ambient) : Ideal SectionAmbient :=
  I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}
def mixedMk (I : Ideal Ambient) : SectionAmbient →+* OverMixed I :=
  Ideal.Quotient.mk (mixedIdeal I)
theorem mixedMk_seed (I : Ideal Ambient) : mixedMk I sectionSeedLine = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
theorem mixedMk_jet (I : Ideal Ambient) : mixedMk I sectionJetLine = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
abbrev scalarToMixed (I : Ideal Ambient) : InterceptField →+* OverMixed I :=
  (algebraMap SectionField (OverMixed I)).comp coefficients.toRingHom
theorem scalarToMixed_C_C (I : Ideal Ambient) (a : FX) :
    scalarToMixed I (RatFunc.C (RatFunc.C (algebraMap FX SeedField a))) =
      mixedMk I (C (algebraMap FX SectionField a)) := by
  change mixedMk I (C (coefficients (RatFunc.C (RatFunc.C (algebraMap FX SeedField a))))) = _
  rw [coefficients_ground]
theorem scalarToMixed_seed (I : Ideal Ambient) (i : Fin 2) :
    scalarToMixed I (RatFunc.C (RatFunc.C (generic i))) =
      mixedMk I (C (sliceParameter (![0, 2] i))) := by
  change mixedMk I (C (coefficients (RatFunc.C (RatFunc.C (generic i))))) = _
  rw [coefficients_seed]
theorem scalarToMixed_slope (I : Ideal Ambient) :
    scalarToMixed I (RatFunc.C RatFunc.X) = mixedMk I (C (sliceParameter 1)) := by
  change mixedMk I (C (coefficients (RatFunc.C RatFunc.X))) = _
  rw [coefficients_slope]
theorem scalarToMixed_intercept (I : Ideal Ambient) :
    scalarToMixed I RatFunc.X = mixedMk I (C (sliceParameter 3)) := by
  change mixedMk I (C (coefficients RatFunc.X)) = _
  rw [coefficients_intercept]
def seedEvalMixed (I : Ideal Ambient) : SeedAmbient →+* OverMixed I :=
  eval₂Hom ((scalarToMixed I).comp (RatFunc.C.comp RatFunc.C)) (fun i => mixedMk I (MvPolynomial.X i))
theorem seedEvalMixed_base (I : Ideal Ambient) :
    (seedEvalMixed I).comp seedBase = (mixedMk I).comp sectionBase := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa only [RingHom.comp_apply, seedBase, sectionBase, map_C, seedEvalMixed, eval₂Hom_C]
      using scalarToMixed_C_C I a
  · intro i
    simp [seedEvalMixed, seedBase, sectionBase]
def seedToMixed (I : Ideal Ambient) : JetSeedSection I →+* OverMixed I :=
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
theorem seedToMixed_mk (I : Ideal Ambient) (p : SeedAmbient) :
    seedToMixed I (Ideal.Quotient.mk (seedIdeal I) p) = seedEvalMixed I p :=
  rfl
def tensorLift {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B]
    (f : A →+* T) (g : B →+* T)
    (h : f.comp (algebraMap R A) = g.comp (algebraMap R B)) : A ⊗[R] B →+* T := by
  letI : Algebra R T := (f.comp (algebraMap R A)).toAlgebra
  let f' : A →ₐ[R] T := { f with commutes' := fun _ => rfl }
  let g' : B →ₐ[R] T := { g with commutes' := fun r => (RingHom.congr_fun h r).symm }
  exact (Algebra.TensorProduct.lift (S := R) f' g' (fun _ _ => Commute.all _ _)).toRingHom
theorem tensorLift_tmul {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B]
    (f : A →+* T) (g : B →+* T) (h : f.comp (algebraMap R A) = g.comp (algebraMap R B))
    (a : A) (b : B) : tensorLift f g h (a ⊗ₜ[R] b) = f a * g b :=
  rfl
def slopeToMixed (I : Ideal Ambient) : SlopeRing I →+* OverMixed I :=
  tensorLift ((scalarToMixed I).comp RatFunc.C) (seedToMixed I) <| by
    apply RingHom.ext
    intro a
    change scalarToMixed I (RatFunc.C (algebraMap SeedField SlopeField a)) =
      seedToMixed I (Ideal.Quotient.mk (seedIdeal I) (C a))
    rw [seedToMixed_mk, seedEvalMixed, eval₂Hom_C, RatFunc.algebraMap_eq_C]
    rfl
theorem slopeToMixed_form (I : Ideal Ambient) :
    slopeToMixed I (jetForm I) = scalarToMixed I RatFunc.X := by
  apply sub_eq_zero.mp
  simp only [rationalLine, map_add, slopeToMixed, tensorLift_tmul, map_one, one_mul,
    seedCoord, seedToMixed_mk, seedEvalMixed, eval₂Hom_X']
  change mixedMk I (MvPolynomial.X 2) +
    scalarToMixed I (RatFunc.C RatFunc.X) * mixedMk I (MvPolynomial.X 3) -
    scalarToMixed I RatFunc.X = 0
  rw [scalarToMixed_slope, scalarToMixed_intercept]
  simpa only [sectionJetLine, map_sub, map_add, map_mul] using mixedMk_jet I
def toMixed (I : Ideal Ambient) : Fibre I →+* OverMixed I :=
  tensorLift (R := SlopeField[X]) (scalarToMixed I) (slopeToMixed I) <| by
    apply Polynomial.ringHom_ext
    · intro a
      change scalarToMixed I (algebraMap SlopeField[X] InterceptField (Polynomial.C a)) =
        slopeToMixed I (Polynomial.aeval (jetForm I) (Polynomial.C a))
      rw [RatFunc.algebraMap_C, Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply]
      simp only [slopeToMixed, tensorLift_tmul, map_one, mul_one]
      rfl
    · change scalarToMixed I (algebraMap SlopeField[X] InterceptField Polynomial.X) =
        slopeToMixed I (Polynomial.aeval (jetForm I) Polynomial.X)
      rw [RatFunc.algebraMap_X, Polynomial.aeval_X, slopeToMixed_form]
abbrev fibreScalar (I : Ideal Ambient) : InterceptField →+* Fibre I :=
  algebraMap InterceptField (Fibre I)
abbrev fibreSlope (I : Ideal Ambient) : SlopeRing I →+* Fibre I :=
  Algebra.TensorProduct.includeRight.toRingHom
abbrev slopeSeed (I : Ideal Ambient) : JetSeedSection I →+* SlopeRing I :=
  Algebra.TensorProduct.includeRight.toRingHom
private abbrev fibreSeed (I : Ideal Ambient) : JetSeedSection I →+* Fibre I :=
  (fibreSlope I).comp (slopeSeed I)
theorem fibreSlope_scalar (I : Ideal Ambient) (a : SlopeField) :
    fibreSlope I (algebraMap SlopeField (SlopeRing I) a) =
      fibreScalar I (RatFunc.C a) := by
  have h : fibreScalar I (algebraMap SlopeField[X] InterceptField (Polynomial.C a)) =
      fibreSlope I (algebraMap SlopeField[X] (SlopeRing I) (Polynomial.C a)) :=
    RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := SlopeField[X]) (A := InterceptField) (B := SlopeRing I)) (Polynomial.C a)
  rw [RatFunc.algebraMap_C,
    show algebraMap SlopeField[X] (SlopeRing I) (Polynomial.C a) =
      algebraMap SlopeField (SlopeRing I) a from Polynomial.aeval_C _ _] at h
  exact h.symm
theorem fibreSeed_scalar (I : Ideal Ambient) (a : SeedField) :
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
theorem fibreSlope_form (I : Ideal Ambient) :
    fibreSlope I (jetForm I) = fibreScalar I RatFunc.X := by
  have h : fibreScalar I (algebraMap SlopeField[X] InterceptField Polynomial.X) =
      fibreSlope I (algebraMap SlopeField[X] (SlopeRing I) Polynomial.X) :=
    RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := SlopeField[X]) (A := InterceptField) (B := SlopeRing I)) Polynomial.X
  rw [RatFunc.algebraMap_X,
    show algebraMap SlopeField[X] (SlopeRing I) Polynomial.X =
      jetForm I from Polynomial.aeval_X _] at h
  exact h.symm
abbrev scalarToFibre (I : Ideal Ambient) : SectionField →+* Fibre I :=
  (fibreScalar I).comp coefficients.symm.toRingHom
def sectionEvalFibre (I : Ideal Ambient) : SectionAmbient →+* Fibre I :=
  eval₂Hom (scalarToFibre I) (fun i => fibreSeed I (seedCoord I i))
theorem scalarToFibre_seed (I : Ideal Ambient) (i : Fin 2) :
    scalarToFibre I (sliceParameter (![0, 2] i)) =
      fibreScalar I (RatFunc.C (RatFunc.C (generic i))) := by
  change fibreScalar I (coefficients.symm (sliceParameter (![0, 2] i))) = _
  rw [← coefficients_seed i, RingEquiv.symm_apply_apply]
theorem sectionEvalFibre_base (I : Ideal Ambient) :
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
theorem sectionEvalFibre_seed (I : Ideal Ambient) :
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
theorem sectionEvalFibre_jet (I : Ideal Ambient) :
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
theorem toMixed_scalar (I : Ideal Ambient) (a : InterceptField) :
    toMixed I (fibreScalar I a) = scalarToMixed I a := by
  change toMixed I (a ⊗ₜ[SlopeField[X]] 1) = _
  simp only [toMixed, tensorLift_tmul, map_one, mul_one]
theorem toMixed_slope (I : Ideal Ambient) (b : SlopeRing I) :
    toMixed I (fibreSlope I b) = slopeToMixed I b := by
  change toMixed I (1 ⊗ₜ[SlopeField[X]] b) = _
  simp only [toMixed, tensorLift_tmul, map_one, one_mul]
theorem slopeToMixed_seed (I : Ideal Ambient) (b : JetSeedSection I) :
    slopeToMixed I (slopeSeed I b) = seedToMixed I b := by
  change slopeToMixed I (1 ⊗ₜ[SeedField] b) = _
  simp only [slopeToMixed, tensorLift_tmul, map_one, one_mul]
theorem slopeToMixed_scalar (I : Ideal Ambient) (a : SlopeField) :
    slopeToMixed I (algebraMap SlopeField (SlopeRing I) a) = scalarToMixed I (RatFunc.C a) := by
  change slopeToMixed I (a ⊗ₜ[SeedField] 1) = _
  simp only [slopeToMixed, tensorLift_tmul, map_one, mul_one]
  rfl
theorem toMixed_seed (I : Ideal Ambient) (b : JetSeedSection I) :
    toMixed I (fibreSeed I b) = seedToMixed I b := by
  change toMixed I (fibreSlope I (slopeSeed I b)) = _
  rw [toMixed_slope, slopeToMixed_seed]
theorem toMixed_coord (I : Ideal Ambient) (i : Fin 4) :
    toMixed I (fibreSeed I (seedCoord I i)) = mixedMk I (MvPolynomial.X i) := by
  rw [toMixed_seed, seedCoord, seedToMixed_mk, seedEvalMixed, eval₂Hom_X']
theorem toFibre_mk (I : Ideal Ambient) (p : SectionAmbient) :
    toFibre I (mixedMk I p) = sectionEvalFibre I p :=
  rfl
theorem toFibre_scalar (I : Ideal Ambient) (a : SectionField) :
    toFibre I (algebraMap SectionField (OverMixed I) a) = fibreScalar I (coefficients.symm a) :=
  eval₂Hom_C _ _ _
theorem toFibre_scalarToMixed (I : Ideal Ambient) (a : InterceptField) :
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
theorem rangeSum_append (f : ℕ → ℕ) (a b : ℕ) :
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
theorem split_pair {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
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
theorem cap_split {p q : Shape} (hp : Chamber p) (hq : Chamber q)
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
abbrev snocReal {n : ℕ} (y : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc y x
theorem volume_snoc {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
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
theorem volume_snoc_interval {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
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
theorem isClosed_nonneg {n : ℕ} : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
theorem nonneg_snoc {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
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
theorem volume_cap2 {B J : ℝ} (hJ : 0 ≤ J) (hB : J ≤ B) :
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
theorem volume_cap3 {B J : ℝ} (hJ : 0 ≤ J) (hB : J ≤ B) :
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
