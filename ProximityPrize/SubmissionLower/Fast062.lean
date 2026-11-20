import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Numeric6Defs
import ProximityPrize.SubmissionLower.Numeric6AuxCert
import ProximityPrize.SubmissionLower.Fast049
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option Elab.async false

section PackSource_K1_14_2_3Moving
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace K1_14_2_3

noncomputable section

open K1 K1_14 K1_14_2 MvPolynomial
open scoped Polynomial
open scoped BigOperators

private theorem constantCoefficients_apply (a : L) :
    constantCoefficients a = algebraMap L FX a := by
  rw [IsScalarTower.algebraMap_apply L L[X] FX]
  rfl

theorem constant_map_degree (Q : MvPolynomial (Fin 2) L) :
    (MvPolynomial.map constantCoefficients Q).totalDegree = Q.totalDegree := by
  unfold totalDegree
  rw [support_map_of_injective Q (fun a b hab => (algebraMap L FX).injective
    (by simpa only [constantCoefficients_apply] using hab))]

/-- A coefficient functional over the constants retains every constant zero. -/
private theorem constant_equation (C : Seeds) (hC : C ≠ 0) :
    ∃ Q : MvPolynomial (Fin 2) L, Q ≠ 0 ∧ Q.totalDegree ≤ C.totalDegree ∧
      ∀ x : Fin 2 → L, MvPolynomial.eval (constantCoefficients ∘ x) C = 0 →
        MvPolynomial.eval x Q = 0 := by
  classical
  let b := Module.Free.chooseBasis L FX
  obtain ⟨e, he⟩ := support_nonempty.mpr hC
  have he' : C.coeff e ≠ 0 := mem_support_iff.mp he
  have hrepr : b.repr (C.coeff e) ≠ 0 := fun hz => he' (b.repr.injective
    (hz.trans (map_zero b.repr).symm))
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hrepr
  let ℓ := b.coord j
  have hℓ : ℓ (C.coeff e) ≠ 0 := Finsupp.mem_support_iff.mp hj
  let Q : MvPolynomial (Fin 2) L := ∑ m ∈ C.support, monomial m (ℓ (C.coeff m))
  have hcoeff (m : Fin 2 →₀ ℕ) : Q.coeff m = ℓ (C.coeff m) := by
    by_cases hm : m ∈ C.support
    · rw [show Q = ∑ n ∈ C.support, monomial n (ℓ (C.coeff n)) from rfl, coeff_sum,
        Finset.sum_eq_single_of_mem m hm]
      · simp
      · intro n _ hnm
        simp [coeff_monomial, hnm]
    · rw [notMem_support_iff.mp hm, map_zero]
      change (∑ n ∈ C.support, monomial n (ℓ (C.coeff n))).coeff m = 0
      rw [coeff_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hnm : n ≠ m := fun h => hm (h ▸ hn)
      simp [coeff_monomial, hnm]
  refine ⟨Q, fun hz => hℓ (by simpa [hz] using (hcoeff e).symm), ?_, ?_⟩
  · apply Finset.sup_le
    intro m hm
    apply Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m.degree)
    apply mem_support_iff.mpr
    intro hz
    exact (mem_support_iff.mp hm) (by rw [hcoeff, hz, map_zero])
  · intro x hx
    have hx' : MvPolynomial.eval (constantCoefficients ∘ x) C =
        ∑ m ∈ C.support, C.coeff m * constantCoefficients (m.prod fun i k => x i ^ k) := by
      conv_lhs => rw [C.as_sum]
      simp only [map_sum, eval_monomial, Finsupp.prod, map_prod, map_pow, Function.comp_apply]
    have heval : MvPolynomial.eval x Q = ℓ (MvPolynomial.eval (constantCoefficients ∘ x) C) := by
      simp only [Q, hx', map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [eval_monomial, constantCoefficients_apply, mul_comm (C.coeff m), ← Algebra.smul_def,
        map_smul, smul_eq_mul, mul_comm]
    rw [heval, hx, map_zero]

private theorem plane_intersection {k : Type} [Field k]
    (A B : MvPolynomial (Fin 2) k) (hA : Irreducible A)
    (hB : B ∉ Ideal.span {A}) (S : Finset (Fin 2 → k))
    (hzero : ∀ x ∈ S, MvPolynomial.eval x A = 0 ∧ MvPolynomial.eval x B = 0) :
    S.card ≤ A.totalDegree * B.totalDegree := by
  let P : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {A}
  let J := P ⊔ Ideal.span {B}
  have : UniqueFactorizationMonoid k := PrincipalIdealRing.to_uniqueFactorizationMonoid
  have : UniqueFactorizationMonoid (MvPolynomial (Fin 2) k) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  have hprime : Prime A := UniqueFactorizationMonoid.irreducible_iff_prime.mp hA
  have hp : P.IsPrime := (Ideal.span_singleton_prime hA.ne_zero).mpr hprime
  have hdim : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hA.ne_zero hp.ne_top
    change (affineHilbertPolynomial P).natDegree + 1 = Nat.card (Fin 2) at h
    simpa [Nat.card_eq_fintype_card] using h
  have hcut := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp hB (b := B.totalDegree) le_rfl
  have hjdim : (affineHilbertPolynomial J).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (by simpa only [hdim, Nat.sub_self] using hcut.1)
  have hlead : (affineHilbertPolynomial P).leadingCoeff = (A.totalDegree : ℚ) := by
    have h := affineDegree_span_singleton hA.ne_zero
    change affineDegree P = _ at h
    simpa [affineDegree, hdim] using h
  have hcoeff : (affineHilbertPolynomial J).coeff 0 ≤ (B.totalDegree : ℚ) * (A.totalDegree : ℚ) := by
    simpa only [hdim, Nat.sub_self, Nat.cast_one, mul_one, hlead] using hcut.2
  have hsub : (S : Set (Fin 2 → k)) ⊆ zeroLocus k J := by
    intro x hx
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hzero x hx).1))
      ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hzero x hx).2))
  have hf := finite_zeroLocus_and_ncard_le_affineDegree (K := k) J hjdim
  have hs := Set.ncard_le_ncard hsub hf.1
  rw [Set.ncard_coe_finset] at hs
  have hs' : (S.card : ℚ) ≤ ((zeroLocus k J).ncard : ℚ) := by exact_mod_cast hs
  have hout := hs'.trans (hf.2.trans ((affineDegree_of_natDegree_eq_zero hjdim).le.trans hcoeff))
  rw [mul_comm] at hout
  exact_mod_cast hout

/-- Intersect the moving equation with a constant-coefficient equation extracted from it. -/
theorem moving_count (C : Seeds) (hC : Irreducible C)
    (hmoving : ¬ DefinedOverConstants (Ideal.span {C})) (marks : Finset (Fin 2 → L))
    (hmarks : ∀ x ∈ marks, MvPolynomial.eval (constantCoefficients ∘ x) C = 0) :
    marks.card ≤ C.totalDegree ^ 2 := by
  classical
  obtain ⟨Q, hQ, hdeg, hprotect⟩ := constant_equation C hC.ne_zero
  let B := MvPolynomial.map constantCoefficients Q
  have hBno : B ≠ 0 := by
    intro hz
    apply hQ
    have hinj : Function.Injective (MvPolynomial.map (σ := Fin 2) constantCoefficients) :=
      MvPolynomial.map_injective _ (fun a b h => (algebraMap L FX).injective
        (by simpa only [constantCoefficients_apply] using h))
    exact hinj (by simpa [B] using hz)
  have hBdeg : B.totalDegree ≤ C.totalDegree := (constant_map_degree Q).trans_le hdeg
  have hB : B ∉ (Ideal.span {C} : Ideal Seeds) := by
    intro hin
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hin
    have hrne : r ≠ 0 := fun hz => hBno (by simp [hr, hz])
    have hdeg' : r.totalDegree = 0 := by
      rw [hr, totalDegree_mul_of_isDomain hC.ne_zero hrne] at hBdeg
      omega
    have hunit : IsUnit r := by
      rw [totalDegree_eq_zero_iff_eq_C.mp hdeg']
      refine (isUnit_iff_ne_zero.mpr ?_).map MvPolynomial.C
      intro hz
      exact hrne (by rw [totalDegree_eq_zero_iff_eq_C.mp hdeg', hz, map_zero])
    have hAssoc : Associated C B := by
      obtain ⟨v, hv⟩ := hunit
      exact ⟨v, by simpa only [hv] using hr.symm⟩
    have hirrB : Irreducible B := hAssoc.irreducible hC
    have hirrQ : Irreducible Q := by
      refine ⟨fun h => hirrB.not_isUnit (h.map (MvPolynomial.map constantCoefficients)), ?_⟩
      intro u v huv
      have hcases := hirrB.isUnit_or_isUnit (show B = MvPolynomial.map constantCoefficients u *
          MvPolynomial.map constantCoefficients v by simp [B, huv])
      refine hcases.imp (fun hu => ?_) (fun hv => ?_)
      · rw [isUnit_iff_totalDegree_of_isReduced] at hu
        rw [constant_map_degree] at hu
        rw [totalDegree_eq_zero_iff_eq_C.mp hu.2]
        refine (isUnit_iff_ne_zero.mpr fun hz => hu.1.ne_zero ?_).map MvPolynomial.C
        simp [coeff_map, hz]
      · rw [isUnit_iff_totalDegree_of_isReduced] at hv
        rw [constant_map_degree] at hv
        rw [totalDegree_eq_zero_iff_eq_C.mp hv.2]
        refine (isUnit_iff_ne_zero.mpr fun hz => hv.1.ne_zero ?_).map MvPolynomial.C
        simp [coeff_map, hz]
    exact hmoving ⟨Q, hirrQ, Ideal.span_singleton_eq_span_singleton.mpr hAssoc⟩
  let embed (x : Fin 2 → L) : Fin 2 → FX := constantCoefficients ∘ x
  have hinj : Function.Injective embed := by
    intro a b hab
    funext i
    apply (algebraMap L FX).injective
    simpa only [embed, Function.comp_apply, constantCoefficients_apply] using congrFun hab i
  have hcount := plane_intersection C B hC hB (marks.image embed) (by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨hmarks x hx, ?_⟩
    have hzQ := hprotect x (hmarks x hx)
    change MvPolynomial.eval (constantCoefficients ∘ x) (MvPolynomial.map constantCoefficients Q) = 0
    rw [eval_map, ← eval₂_comp, hzQ, map_zero])
  rw [Finset.card_image_of_injective _ hinj] at hcount
  exact hcount.trans (by rw [pow_two]; exact Nat.mul_le_mul_left _ hBdeg)

end
end K1_14_2_3
end PackSource_K1_14_2_3Moving

section PackSource_K1_14_2_3Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace K1_14_2_3

noncomputable section

open K1 K1_14 K1_14_2
open scoped BigOperators Classical

/-- The seed projection is a plane curve and its degree is paid by the generic line. -/
def c1 : Prop :=
  ∀ I : Ideal Ambient, SeedSlice I →
    ∃ C : Seeds, Irreducible C ∧ seedImage I = Ideal.span {C} ∧
      0 < C.totalDegree ∧ C.totalDegree ≤ seedLength I

/-- The contracted Y-image has its own generic covering degree over the constant base. -/
def c2 : Prop :=
  ∀ (I : Ideal Ambient) (C : MvPolynomial (Fin 2) L), SeedSlice I →
    Module.Finite SeedField (JetYSection I) → Irreducible C →
    seedImage I = Ideal.span {MvPolynomial.map constantCoefficients C} →
    ∃ g : ℕ, 0 < g ∧ SmallRootCurve (rootImage I) g (yLength I) ∧
      C.totalDegree * g ≤ seedLength I

private def seedRate : ℚ := ((p + 1 : ℕ) : ℚ) / 9

private def yRate : ℚ :=
  15 + (11697 / 6520 : ℚ) * (((2 * endpointDegree - 1 : ℕ) : ℚ) * 15 + 1)

private theorem root_price_bound (g H : ℕ) (hg : g ≤ 8) :
    rootPrice g H ≤ yRate * (H : ℚ) + (g : ℚ) := by
  have hgq : (g : ℚ) ≤ 8 := by exact_mod_cast hg
  have ht : 2 * (g : ℚ) - 1 ≤ 15 := by linarith
  have hd : 0 ≤ ((2 * endpointDegree - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hb : 0 ≤ (11697 / 6520 : ℚ) := by norm_num
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add ht (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left ht hd) (le_refl (1 : ℚ))) hb))
    (Nat.cast_nonneg H)) (le_refl (g : ℚ))

private theorem seedRate_nonneg : 0 ≤ seedRate := by unfold seedRate; positivity
private theorem yRate_nonneg : 0 ≤ yRate := by unfold yRate; positivity
private theorem seedCap_lt_p : lossSeedCap < p := by decide +kernel
private theorem seedCap_le_rate : (lossSeedCap : ℚ) ≤ seedRate := by decide +kernel

private theorem ledger :
    seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) ≤
      (movingPrice : ℚ) := by decide +kernel

private theorem eval_root_image (a b y v : FX) (q : RootAmbient) :
    MvPolynomial.eval ![a,b,y,v] (rootIncl q) = MvPolynomial.eval ![a,b,y] q := by
  change MvPolynomial.eval ![a,b,y,v] (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4)) q) = _
  rw [MvPolynomial.eval_rename]
  have hv : ![a,b,y,v] ∘ Fin.castLE (by decide : 3 ≤ 4) = ![a,b,y] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

private theorem eval_seed_image (a b y : FX) (C : Seeds) :
    MvPolynomial.eval ![a,b,y] (rootSeeds C) = MvPolynomial.eval ![a,b] C := by
  change MvPolynomial.eval ![a,b,y] (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) C) = _
  rw [MvPolynomial.eval_rename]
  have hv : ![a,b,y] ∘ Fin.castLE (by decide : 2 ≤ 3) = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

private theorem on_root {I : Ideal Ambient} {z : K} {S : Polynomial K}
    (h : OnJet I z S) : OnRoot (rootImage I) z S := by
  intro q hq
  have heval : jetMarkHom z S (rootIncl q) = rootMarkHom z S q :=
    eval_root_image (seedEmbedding z) (seedEmbedding z ^ p) (atX S) (atX S.derivative) q
  exact RingHom.mem_ker.mpr (heval.symm.trans (RingHom.mem_ker.mp (h hq)))

private theorem on_seed {I : Ideal Ambient} {z : K} {S : Polynomial K}
    (h : OnJet I z S) {C : Seeds} (hC : C ∈ seedImage I) : graphEval z C = 0 := by
  have heval : rootMarkHom z S (rootSeeds C) = graphEval z C :=
    eval_seed_image (seedEmbedding z) (seedEmbedding z ^ p) (atX S) C
  exact heval.symm.trans (RingHom.mem_ker.mp (on_root h hC))

private theorem moving_graph_count (n : ℕ) (C : Seeds) (hC : Irreducible C)
    (hmoving : ¬ DefinedOverConstants (Ideal.span {C})) (labels : Finset K)
    (hlabels : ∀ z ∈ labels, MvPolynomial.eval ![seedEmbedding z, (seedEmbedding z)^n] C = 0) :
    labels.card ≤ C.totalDegree ^ 2 := by
  let point (z : K) : Fin 2 → L := ![algebraMap K L z, (algebraMap K L z)^n]
  have hinj : Function.Injective point := by
    intro a b hab
    exact (algebraMap K L).injective (congrFun hab 0)
  have hgraph (z : K) : constantCoefficients ∘ point z =
      ![seedEmbedding z, (seedEmbedding z)^n] := by
    funext i
    fin_cases i
    · rfl
    · change constantCoefficients ((algebraMap K L z)^n) = (seedEmbedding z)^n
      exact map_pow constantCoefficients _ n
  have hc := moving_count C hC hmoving (labels.image point) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [hgraph]
    exact hlabels z hz)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

private theorem seed_graph_count (C : Seeds) (hC : C ≠ 0) (hdeg : C.totalDegree < p)
    (labels : Finset K) (hlabels : ∀ z ∈ labels, graphEval z C = 0) :
    labels.card ≤ (p+1) * C.totalDegree := by
  classical
  have hc := frobenius_coefficient_exception_count p C.totalDegree C.totalDegree (by decide)
    C hC (C.degreeOf_le_totalDegree 0) hdeg (C.degreeOf_le_totalDegree 1)
    (labels.image seedEmbedding) (by
      intro a ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact hlabels z hz)
  simpa only [Finset.card_image_of_injective _ seedEmbedding.injective, Nat.add_mul, Nat.one_mul,
    Nat.add_comm C.totalDegree] using hc

private theorem equal_image_degree (C : Seeds) (hC : C ≠ 0) (Q : MvPolynomial (Fin 2) L)
    (h : Ideal.span {C} = Ideal.span {MvPolynomial.map constantCoefficients Q}) :
    C.totalDegree = Q.totalDegree := by
  have ha := Ideal.span_singleton_eq_span_singleton.mp h
  have hQ : MvPolynomial.map constantCoefficients Q ≠ 0 := by
    obtain ⟨v, hv⟩ := ha
    exact fun hz => mul_ne_zero hC (Units.ne_zero v) (hv.trans hz)
  rw [← constant_map_degree Q]
  exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain ha.dvd_dvd.1 hQ).antisymm
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain ha.dvd_dvd.2 hC)

private theorem union_card_le {ι : Type*} (s : Finset ι) (W : ι → Finset K) :
    ((s.biUnion W).card : ℚ) ≤ ∑ i ∈ s, ((W i).card : ℚ) := by
  exact_mod_cast (Finset.card_biUnion_le (s := s) (t := W))

private theorem group_price {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hhi : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (h1 : c1) (h2 : c2) (tariff : RootTariff)
    (P : Ideal Seeds) (s : Finset (Ideal Ambient))
    (hne : s.Nonempty) (himage : ∀ I ∈ s, seedImage I = P)
    (hslice : ∀ I ∈ s, SeedSlice I ∧ Module.Finite SeedField (JetYSection I))
    (hcap : (∑ I ∈ s, seedLength I) ≤ lossSeedCap) :
    let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
    ((s.biUnion W).card : ℚ) ≤
      seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
      yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ) := by
  classical
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let U := s.biUnion W
  let D : ℕ := ∑ I ∈ s, seedLength I
  let H : ℕ := ∑ I ∈ s, yLength I
  change (U.card : ℚ) ≤ seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
    yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ)
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  change (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ)
  have extend_seed (h : (U.card : ℚ) ≤ seedRate * (D : ℚ)) :
      (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ) := by
    exact h.trans (le_add_of_nonneg_right (mul_nonneg yRate_nonneg (Nat.cast_nonneg H)) |>.trans
      (le_add_of_nonneg_right (Nat.cast_nonneg D)))
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨C, hC, hJproj, hCpos, hCbound⟩ := h1 J (hslice J hJ).1
  have hP : P = Ideal.span {C} := (himage J hJ).symm.trans hJproj
  have hCD : C.totalDegree ≤ D :=
    hCbound.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hJ)
  have hlabels : ∀ z ∈ U.image M.label, graphEval z C = 0 := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨I, hI, hγI⟩ := Finset.mem_biUnion.mp hγ
    refine on_seed (Finset.mem_filter.mp hγI).2 ?_
    rw [himage I hI, hP]
    exact Ideal.mem_span_singleton_self C
  have hcard : (U.image M.label).card = U.card :=
    Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
  by_cases hlarge : 9 * C.totalDegree ≤ D
  · have hc := seed_graph_count C hC.ne_zero ((hCD.trans hcap).trans_lt seedCap_lt_p)
      (U.image M.label) hlabels
    rw [hcard] at hc
    have hcq : (U.card : ℚ) ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := by exact_mod_cast hc
    have hdq : (9 : ℚ) * (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hlarge
    apply extend_seed
    calc
      _ ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := hcq
      _ = seedRate * (9 * (C.totalDegree : ℚ)) := by unfold seedRate; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdq seedRate_nonneg
  by_cases hconst : DefinedOverConstants P
  · obtain ⟨Q, hQ, hQproj⟩ := hconst
    have hdeg : C.totalDegree = Q.totalDegree := equal_image_degree C hC.ne_zero Q
      (hP.symm.trans hQproj)
    have hsbound (I : Ideal Ambient) (hI : I ∈ s) :
        ((W I).card : ℚ) ≤ yRate * (yLength I : ℚ) + (seedLength I : ℚ) := by
      obtain ⟨g, hg, hroot, hgD⟩ :=
        h2 I Q (hslice I hI).1 (hslice I hI).2 hQ ((himage I hI).trans hQproj)
      have hgi : g ≤ 8 := by
        by_contra! hbad
        have hsuccess := (Nat.mul_le_mul_left Q.totalDegree hbad).trans
          (hgD.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hI))
        exact hlarge (by simpa [hdeg, Nat.mul_comm 9] using hsuccess)
      have hgcap : g ≤ seedLength I :=
        (Nat.le_mul_of_pos_left g (hdeg ▸ hCpos)).trans hgD
      have hsub : W I ⊆ Γ := (Finset.filter_subset _ _).trans hT
      have ht := tariff u del M Γ F hhi (W I) hsub (rootImage I) g (yLength I) hg hgi hroot
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
      have hgcapq : (g : ℚ) ≤ (seedLength I : ℚ) := by exact_mod_cast hgcap
      exact ht.trans ((root_price_bound g (yLength I) hgi).trans (add_le_add le_rfl hgcapq))
    calc
      (U.card : ℚ) ≤ ∑ I ∈ s, ((W I).card : ℚ) := union_card_le s W
      _ ≤ ∑ I ∈ s, (yRate * (yLength I : ℚ) + (seedLength I : ℚ)) := Finset.sum_le_sum hsbound
      _ = yRate * (H : ℚ) + (D : ℚ) := by
        simp only [H, D, Finset.sum_add_distrib, Finset.mul_sum, Nat.cast_sum]
      _ ≤ _ := by
        rw [add_assoc]
        exact le_add_of_nonneg_left (mul_nonneg seedRate_nonneg (Nat.cast_nonneg D))
  · have hc := moving_graph_count p C hC (hP ▸ hconst) (U.image M.label) hlabels
    rw [hcard] at hc
    have hq : (U.card : ℚ) ≤ (C.totalDegree : ℚ) ^ 2 := by exact_mod_cast hc
    have hCq : (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hCD
    have hCr : (C.totalDegree : ℚ) ≤ seedRate :=
      (by exact_mod_cast (hCD.trans hcap) : (C.totalDegree : ℚ) ≤ (lossSeedCap : ℚ)).trans
        seedCap_le_rate
    exact extend_seed (hq.trans (by
      rw [pow_two]
      exact mul_le_mul hCr hCq (Nat.cast_nonneg C.totalDegree) seedRate_nonneg))

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2.c3 := by
  classical
  intro tariff u del M Γ F hhi T hT hcover
  obtain ⟨cs, hs, hD, hH, hcover⟩ := hcover
  let images := cs.image seedImage
  let group (P : Ideal Seeds) := cs.filter (fun I => seedImage I = P)
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let covered (P : Ideal Seeds) := (group P).biUnion W
  have hsubset : T ⊆ images.biUnion covered := by
    intro γ hγ
    obtain ⟨I, hi, hz⟩ := hcover γ hγ
    refine Finset.mem_biUnion.mpr ⟨seedImage I, Finset.mem_image_of_mem _ hi, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_filter.mpr ⟨hi, rfl⟩,
      Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hgroup (P : Ideal Seeds) (hP : P ∈ images) :
      ((covered P).card : ℚ) ≤
        seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ) := by
    obtain ⟨I, hi, he⟩ := Finset.mem_image.mp hP
    refine group_price M F hhi T hT h1 h2 tariff P (group P)
      ⟨I, Finset.mem_filter.mpr ⟨hi, he⟩⟩
      (fun _ hJ => (Finset.mem_filter.mp hJ).2) (fun J hJ => ?_) ?_
    · obtain ⟨hp, hdim, hf, hpos, hy⟩ := hs J (Finset.mem_filter.mp hJ).1
      exact ⟨⟨hp, hdim, hf, hpos⟩, hy⟩
    · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hD
  have hsum (f : Ideal Ambient → ℚ) :
      (∑ P ∈ images, ∑ I ∈ group P, f I) = ∑ I ∈ cs, f I :=
    Finset.sum_fiberwise_of_maps_to (fun _ hI => Finset.mem_image_of_mem seedImage hI) f
  have hDq : (∑ I ∈ cs, (seedLength I : ℚ)) ≤ (lossSeedCap : ℚ) := by
    exact_mod_cast hD
  have hHq : (∑ I ∈ cs, (yLength I : ℚ)) ≤ (lossYCap : ℚ) := by
    exact_mod_cast hH
  have hbound : (T.card : ℚ) ≤ (movingPrice : ℚ) := calc
    (T.card : ℚ) ≤ ((images.biUnion covered).card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ P ∈ images, ((covered P).card : ℚ) := union_card_le images covered
    _ ≤ ∑ P ∈ images, (seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ)) :=
      Finset.sum_le_sum hgroup
    _ = seedRate * (∑ I ∈ cs, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ cs, (yLength I : ℚ)) + ∑ I ∈ cs, (seedLength I : ℚ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    _ ≤ seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDq seedRate_nonneg)
        (mul_le_mul_of_nonneg_left hHq yRate_nonneg)) hDq
    _ ≤ _ := ledger
  exact_mod_cast hbound

end
end K1_14_2_3
end PackSource_K1_14_2_3Split

section PackSource_K1_14_2_3_1Degree
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_3_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3 Polynomial
open scoped Polynomial BigOperators

def lineValues {R : Type} [CommRing R] (s t : R) : Fin 2 → R[X] :=
  ![Polynomial.C t - Polynomial.C s * (Polynomial.X : R[X]), Polynomial.X]

def eliminate : MvPolynomial (Fin 2) SeedField →ₐ[SeedField] SeedField[X] :=
  MvPolynomial.aeval (lineValues (generic 0) (generic 1))

def lineRestriction : Seeds →+* SeedField[X] :=
  eliminate.toRingHom.comp (MvPolynomial.map (algebraMap FX SeedField))

private theorem fin_two_sum (e : Fin 2 →₀ ℕ) : e.sum (fun _ m => m) = e 0 + e 1 := by
  simp [Finsupp.sum_of_support_subset e (Finset.subset_univ e.support)]

private def integralRestriction : Seeds →+* Seeds[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.C : FX →+* Seeds))
    (lineValues (MvPolynomial.X 0) (MvPolynomial.X 1))

private theorem restriction_map :
    (mapRingHom (algebraMap Seeds SeedField)).comp integralRestriction = lineRestriction := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [integralRestriction, lineRestriction, eliminate, Polynomial.algebraMap_eq, RingHom.comp_apply]
    rfl
  · intro k
    fin_cases k <;>
      simp [integralRestriction, lineRestriction, eliminate, lineValues, RingHom.comp_apply, generic]

private theorem lineValue_natDegree {R : Type} [CommRing R] (s t : R) :
    (lineValues s t 0).natDegree ≤ 1 := by
  change (Polynomial.C t - Polynomial.C s * (Polynomial.X : R[X])).natDegree ≤ 1
  have hs : (Polynomial.C s * (Polynomial.X : R[X])).natDegree ≤ 1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le s 1
  exact (natDegree_sub_le _ _).trans (max_le (by simp) hs)

private theorem coeff_integralRestriction_monomial (e : Fin 2 →₀ ℕ) (a : FX) (d : ℕ)
    (he : e 0 + e 1 ≤ d) :
    (integralRestriction (MvPolynomial.monomial e a)).coeff d =
      if e 0 + e 1 = d then MvPolynomial.C a * (-MvPolynomial.X 0) ^ e 0 else 0 := by
  let q : Seeds[X] := lineValues (MvPolynomial.X 0) (MvPolynomial.X 1) 0
  have hq : q.natDegree ≤ 1 := lineValue_natDegree _ _
  have hcoeff : q.coeff 1 = -(MvPolynomial.X 0 : Seeds) := by simp [q, lineValues, coeff_sub]
  have hpow : (q ^ e 0).natDegree ≤ e 0 := by simpa using natDegree_pow_le_of_le (e 0) hq
  have hXpow : ((Polynomial.X : Seeds[X]) ^ e 1).natDegree ≤ e 1 := by simp
  have hqpow : (q ^ e 0).coeff (e 0) = (-(MvPolynomial.X 0 : Seeds)) ^ e 0 := by
    simpa [hcoeff] using (coeff_pow_of_natDegree_le (m := e 0) hq)
  rw [MvPolynomial.monomial_fin_two, map_mul, map_mul, map_pow, map_pow]
  simp only [integralRestriction, lineValues, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((Polynomial.C (MvPolynomial.C a) * q ^ e 0) * Polynomial.X ^ e 1).coeff d = _
  rw [mul_assoc, coeff_C_mul]
  split_ifs with heq
  · rw [← heq, coeff_mul_add_eq_of_natDegree_le hpow hXpow, hqpow, coeff_X_pow_self]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
    exact (natDegree_mul_le_of_le hpow hXpow).trans_lt (lt_of_le_of_ne he heq)

/-- At top degree the distinct plane monomials give distinct powers of the
slope. This preserves the total degree in every characteristic. -/
theorem totalDegree_lineRestriction (F : Seeds) : (lineRestriction F).natDegree = F.totalDegree := by
  classical
  have hu : (lineRestriction F).natDegree ≤ F.totalDegree := by
    change (eliminate (MvPolynomial.map (algebraMap FX SeedField) F)).natDegree ≤ F.totalDegree
    have hvar (i : Fin 2) : (lineValues (generic 0) (generic 1) i).natDegree ≤ 1 := by
      fin_cases i
      · exact lineValue_natDegree _ _
      · simp [lineValues]
    have h := MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le (1 : Fin 2 → ℕ)
      _ (MvPolynomial.map (algebraMap FX SeedField) F) hvar
    simpa [eliminate, MvPolynomial.weightedTotalDegree_one,
      MvPolynomial.support_map_of_injective _ (RingHom.injective (algebraMap FX SeedField)), MvPolynomial.totalDegree]
      using h
  refine hu.antisymm ?_
  by_cases hF : F = 0
  · simp [hF]
  let d := F.totalDegree
  obtain ⟨e, he, hde⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF) (fun e => e.sum (fun _ m => m))
  change d = e.sum (fun _ m => m) at hde
  rw [fin_two_sum] at hde
  have htop : (integralRestriction F).coeff d ≠ 0 := by
    have hh (e' : Fin 2 →₀ ℕ) (he' : e' ∈ F.support) : e' 0 + e' 1 ≤ d := by
      rw [← fin_two_sum]
      exact MvPolynomial.le_totalDegree he'
    have hexp :
        (integralRestriction F).coeff d =
          ∑ e' ∈ F.support with e' 0 + e' 1 = d,
            MvPolynomial.C (F.coeff e') * (-MvPolynomial.X 0) ^ e' 0 := by
      conv_lhs => rw [F.as_sum]
      rw [map_sum, finsetSum_coeff, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun e' he' =>
        coeff_integralRestriction_monomial e' (F.coeff e') d (hh e' he'))
    have hcoef (a : FX) (k m : ℕ) :
        (MvPolynomial.C a * (-(MvPolynomial.X 0 : Seeds)) ^ k).coeff (Finsupp.single 0 m)
          = if k = m then a * (-1)^k else 0 := by
      have hneg : (MvPolynomial.C (-1 : FX) : Seeds) = -1 :=
        (map_neg (MvPolynomial.C : FX →+* Seeds) 1).trans
          (congrArg Neg.neg (map_one (MvPolynomial.C : FX →+* Seeds)))
      have hn : -(MvPolynomial.X 0 : Seeds) = MvPolynomial.C (-1 : FX) * MvPolynomial.X 0 :=
        (neg_one_mul (MvPolynomial.X 0 : Seeds)).symm.trans
          (congrArg (fun z => z * (MvPolynomial.X 0 : Seeds)) hneg.symm)
      rw [hn, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
        MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      by_cases hk : k = m
      · simp [hk]
      · have hs : Finsupp.single (0 : Fin 2) k ≠ Finsupp.single 0 m := by
          intro h
          exact hk (by simpa using DFunLike.congr_fun h 0)
        simp [hk, hs]
    intro ht
    have hz := congrArg (fun f : Seeds => f.coeff (Finsupp.single 0 (e 0))) ht
    rw [hexp] at hz
    simp only [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, hcoef] at hz
    rw [Finset.sum_eq_single e] at hz
    · have hz' : F.coeff e * (-1 : FX) ^ e 0 = 0 := by simpa using hz
      exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp he)
        (pow_ne_zero (e 0) (neg_ne_zero.mpr one_ne_zero))) hz'
    · intro e' he' hne
      have hdiff : e' 0 ≠ e 0 := by
        intro h0
        have h1 : e' 1 = e 1 := by
          have := (Finset.mem_filter.mp he').2
          omega
        exact hne (Finsupp.ext (by intro i; fin_cases i <;> assumption))
      simp [hdiff]
    · exact fun h => False.elim (h (Finset.mem_filter.mpr ⟨he, hde.symm⟩))
  apply le_natDegree_of_ne_zero
  have hr : lineRestriction F = (integralRestriction F).map (algebraMap Seeds SeedField) :=
    (RingHom.congr_fun restriction_map F).symm
  rw [hr, coeff_map]
  exact fun h => htop (IsFractionRing.injective Seeds SeedField (h.trans (map_zero _).symm))

end
end K1_14_2_3_1
end PackSource_K1_14_2_3_1Degree

section PackSource_K1_14_2_2_2_6Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_2_2_6

noncomputable section

open K1_14 K1_14_2 K1_14_2_2

/-- Embed the generic seed-line parameters into the independent mixed-section field. -/
def seedParameters : SeedField →+* SectionField :=
  let indices : Fin 2 → Fin 4 := ![0, 2]
  let rename : Seeds →+* MvPolynomial (Fin 4) FX :=
    (MvPolynomial.rename indices).toRingHom
  let g : Seeds →+* SectionField :=
    (algebraMap (MvPolynomial (Fin 4) FX) SectionField).comp rename
  have hi : Function.Injective indices := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [indices]
  IsFractionRing.lift (K := SeedField) (g := g)
    ((IsFractionRing.injective (MvPolynomial (Fin 4) FX) SectionField).comp
      (MvPolynomial.rename_injective indices hi))

/-- Substitute the same generic seed line used in `OverMixed`, leaving its second
seed coordinate free. The independent jet-line parameters extend the coefficients. -/
def mixedSeedRestriction (f : Seeds) : Polynomial SectionField :=
  (K1_14_2_3_1.lineRestriction f).map seedParameters

end
end K1_14_2_2_2_6
end PackSource_K1_14_2_2_2_6Defs

section PackSource_K1_14_2_2_2_6Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 8

namespace K1_14_2_2_2_6

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_3

/-- The generic mixed section dominates the zero-dimensional seed-line
section of a curve image, including its residue degrees and multiplicities. -/
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    Module.Finite SectionField (OverMixed I) →
    ∀ f : Seeds, f ≠ 0 → seedImage I = Ideal.span {f} →
      ∃ e : (Polynomial SectionField ⧸ Ideal.span {mixedSeedRestriction f}) →ₐ[SectionField]
          OverMixed I, Function.Injective e

/-- A point seed image that supports an actual mark meets the full generic
jet-plane section. -/
def c2 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    (seedImage I).IsMaximal → Module.Finite SeedField (OverJets I) →
    (∃ (z : K) (R : Polynomial K), OnJet I z R) → 0 < sectionDegree I 3

private abbrev seedIncl : Seeds →+* Ambient := rootIncl.comp rootSeeds

private theorem seedImage_prime (I : Ideal Ambient) [I.IsPrime] : (seedImage I).IsPrime :=
  (inferInstance : I.IsPrime).comap seedIncl

private theorem eval_seed_rename {k : Type} [CommRing k] (a b y v : k)
    (f : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval ![a, b, y, v]
      (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))
        (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) f)) =
      MvPolynomial.eval ![a, b] f := by
  let cast34 := Fin.castLE (by decide : 3 ≤ 4)
  let cast23 := Fin.castLE (by decide : 2 ≤ 3)
  rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename]
  have he : (![a, b, y, v] ∘ cast34) ∘ cast23 = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

private theorem seed_image_eval {I : Ideal Ambient} {z : K} {R : Polynomial K}
    (h : OnJet I z R) : seedImage I ≤ RingHom.ker (graphEval z) := by
  intro f hf
  have hmem : seedIncl f ∈ I := hf
  have he : jetMarkHom z R (seedIncl f) = graphEval z f :=
    eval_seed_rename (seedEmbedding z) (seedEmbedding z ^ p) (atX R) (atX R.derivative) f
  exact RingHom.mem_ker.mpr (he.symm.trans (RingHom.mem_ker.mp (h hmem)))

private abbrev SurfaceField (I : Ideal Ambient) := FractionRing (Ambient ⧸ I)

private def surfaceFractionMap (I : Ideal Ambient) : Ambient →+* SurfaceField I := by
  let q : Ambient →+* (Ambient ⧸ I) := Ideal.Quotient.mk I
  let ι : (Ambient ⧸ I) →+* SurfaceField I := algebraMap _ _
  exact ι.comp q

/-- A dominant seed projection gives a nonzero generic fibre by evaluation
in the fraction field of the surface. -/
private theorem seedImage_ne_bot (I : Ideal Ambient) [I.IsPrime]
    [Module.Finite SeedField (OverSeeds I)] (hz : sectionDegree I 0 = 0) :
    seedImage I ≠ ⊥ := by
  intro hI
  let F := SurfaceField I
  let π := surfaceFractionMap I
  have hker : RingHom.ker π = I := by
    change RingHom.ker ((algebraMap (Ambient ⧸ I) (SurfaceField I)).comp
      (Ideal.Quotient.mk I)) = I
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (Ambient ⧸ I) (SurfaceField I)),
      Ideal.mk_ker]
  have hseed : Function.Injective (π.comp seedIncl) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← RingHom.comap_ker, hker]
    exact hI
  let ρ : SeedField →+* F := IsFractionRing.lift hseed
  have hρ (f : Seeds) : ρ (algebraMap Seeds SeedField f) = π (seedIncl f) :=
    IsFractionRing.lift_algebraMap hseed f
  let e : FibreRing →+* F := MvPolynomial.eval₂Hom ρ
    ![π (MvPolynomial.X 2), π (MvPolynomial.X 3)]
  have hcomp : e.comp mapGenericSeed = π := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, mapGenericSeed, MvPolynomial.eval₂Hom_C, e]
      have hC : seedIncl (MvPolynomial.C a) = MvPolynomial.C a := by
        change MvPolynomial.rename _ (MvPolynomial.rename _ (MvPolynomial.C a)) = _
        rw [MvPolynomial.rename_C, MvPolynomial.rename_C]
      rw [IsScalarTower.algebraMap_apply FX Seeds SeedField, MvPolynomial.algebraMap_eq]
      exact (hρ _).trans (congrArg π hC)
    · intro i
      fin_cases i
      · simpa [RingHom.comp_apply, e, mapGenericSeed, generic, seedIncl, rootSeeds, rootIncl]
          using hρ (MvPolynomial.X 0)
      · simpa [RingHom.comp_apply, e, mapGenericSeed, generic, seedIncl, rootSeeds, rootIncl]
          using hρ (MvPolynomial.X 1)
      · simp [e, mapGenericSeed]; rfl
      · simp [e, mapGenericSeed]; rfl
  have hmap : I.map mapGenericSeed ≤ RingHom.ker e := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hcomp, hker]
  have htop : I.map mapGenericSeed = ⊤ :=
    Ideal.Quotient.subsingleton_iff.mp
      ((Module.finrank_eq_zero_iff_of_free SeedField (OverSeeds I)).mp hz)
  exact RingHom.ker_ne_top e (top_unique (htop ▸ hmap))

private theorem seedImage_principal (I : Ideal Ambient) [I.IsPrime]
    (hn : seedImage I ≠ ⊥) (hm : ¬ (seedImage I).IsMaximal) :
    ∃ f : Seeds, f ≠ 0 ∧ seedImage I = Ideal.span {f} := by
  let P := seedImage I
  let : P.IsPrime := seedImage_prime I
  have hlo : 1 ≤ P.height := by
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hn)
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  let : M.IsPrime := hM.isPrime
  have hlt : P < M := lt_of_le_of_ne hPM fun h => by
    have he : seedImage I = M := h
    exact hm (he.symm ▸ hM)
  have hdim : ringKrullDim Seeds = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num [Nat.card_eq_fintype_card]
  have hMheight : M.height ≤ 2 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hle : P.height ≤ 1 :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      ((Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hMheight)
  have : UniqueFactorizationMonoid FX := PrincipalIdealRing.to_uniqueFactorizationMonoid
  have : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨f, hmem, hf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (seedImage_prime I) hn
  exact ⟨f, hf.ne_zero, Ideal.eq_span_singleton_of_height_eq_one (hle.antisymm hlo) hmem hf⟩

private theorem same_seed {I : Ideal Ambient} (hI : (seedImage I).IsMaximal)
    {z w : K} {R S : Polynomial K} (hz : OnJet I z R) (hw : OnJet I w S) :
    (seedEmbedding z, seedEmbedding z ^ p) = (seedEmbedding w, seedEmbedding w ^ p) := by
  have hker := hI.eq_of_le (RingHom.ker_ne_top (graphEval z)) (seed_image_eval hz)
  have hx : (MvPolynomial.X 0 - MvPolynomial.C (seedEmbedding z) : Seeds) ∈ seedImage I := by
    rw [hker]
    apply RingHom.mem_ker.mpr
    simp [graphEval]
  have he := RingHom.mem_ker.mp (seed_image_eval hw hx)
  have he' : seedEmbedding w = seedEmbedding z := by
    simpa [graphEval, sub_eq_zero] using he
  rw [he']

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2_2.c6 := by
  classical
  intro I hI hdim hfinite hz
  let : I.IsPrime := hI
  let : Module.Finite SeedField (OverSeeds I) := hfinite.seeds
  let : Module.Finite SectionField (OverMixed I) := hfinite.mixed
  by_cases hm : (seedImage I).IsMaximal
  · by_cases hmark : ∃ (z : K) (R : Polynomial K), OnJet I z R
    · obtain ⟨z, R, hon⟩ := hmark
      refine ⟨⟨1, one_ne_zero, {(seedEmbedding z, seedEmbedding z ^ p)}⟩, by simp,
        ?_, ?_⟩
      · simp only [Finset.card_singleton]
        exact Nat.succ_le_of_lt (h2 I hI hdim hm hfinite.jets ⟨z, R, hon⟩)
      · intro w S hw
        exact Or.inr (Finset.mem_singleton.mpr (same_seed hm hw hon))
    · exact ⟨⟨1, one_ne_zero, ∅⟩, by simp, by simp, fun w S hw => (hmark ⟨w, S, hw⟩).elim⟩
  · obtain ⟨f, hf, hgen⟩ := seedImage_principal I (seedImage_ne_bot I hz) hm
    obtain ⟨e, he⟩ := h1 I hI hdim hfinite.mixed f hf hgen
    have hdegree : (mixedSeedRestriction f).natDegree = f.totalDegree := by
      rw [mixedSeedRestriction, Polynomial.natDegree_map_eq_of_injective seedParameters.injective,
        K1_14_2_3_1.totalDegree_lineRestriction]
    have hbound := LinearMap.finrank_le_finrank_of_injective (f := e.toLinearMap) he
    rw [finrank_quotient_span_eq_natDegree, hdegree] at hbound
    refine ⟨⟨f, hf, ∅⟩, hbound, by simp, ?_⟩
    intro z R hon
    have hmem : f ∈ seedImage I := by
      rw [hgen]
      exact Ideal.subset_span (Set.mem_singleton f)
    exact Or.inl (RingHom.mem_ker.mp (seed_image_eval hon hmem))

end
end K1_14_2_2_2_6
end PackSource_K1_14_2_2_2_6Split

section PackSource_K1_14_2_3_1Fiber
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_3_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3
open scoped Polynomial

abbrev Raw (n : ℕ) := MvPolynomial (Fin n) FX
abbrev Over (n : ℕ) := MvPolynomial (Fin n) SeedField

local instance (n : ℕ) (I : Ideal (Raw n)) : CommRing (CoordinateRing I)[X] :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)

abbrev sectionIdeal {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) : Ideal (Over n) :=
  I.map (MvPolynomial.map (algebraMap FX SeedField)) ⊔ Ideal.span {seedLine i j}

abbrev Slice {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) := Over n ⧸ sectionIdeal I i j

abbrev coord {n : ℕ} (I : Ideal (Raw n)) (k : Fin n) : CoordinateRing I :=
  Ideal.Quotient.mk I (MvPolynomial.X k)

/-- The two coefficient parameters are the free slope and the intercept of the
line through the indicated coordinates. -/
def parameterMap {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) :
    Seeds →+* (CoordinateRing I)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX (CoordinateRing I)))
    ![Polynomial.X, Polynomial.C (coord I i) + Polynomial.X * Polynomial.C (coord I j)]

def toSlice {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) : CoordinateRing I →+* Slice I i j :=
  Ideal.quotientMap (sectionIdeal I i j) (MvPolynomial.map (algebraMap FX SeedField))
    (Ideal.map_le_iff_le_comap.mp le_sup_left)

def slopeToSlice {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) :
    (CoordinateRing I)[X] →+* Slice I i j :=
  Polynomial.eval₂RingHom (toSlice I i j) (algebraMap SeedField (Slice I i j) (generic 0))

theorem sliceLine {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) :
    toSlice I i j (coord I i) +
      algebraMap SeedField (Slice I i j) (generic 0) * toSlice I i j (coord I j) =
      algebraMap SeedField (Slice I i j) (generic 1) := by
  have h : Ideal.Quotient.mk (sectionIdeal I i j) (seedLine i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {seedLine i j} ≤ sectionIdeal I i j from le_sup_right)
        (Ideal.mem_span_singleton_self _))
  apply sub_eq_zero.mp
  simpa only [seedLine, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap, toSlice, coord, Ideal.quotientMap_mk, MvPolynomial.map_X] using h

theorem parameter_commutes {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) :
    (slopeToSlice I i j).comp (parameterMap I i j) =
      (algebraMap SeedField (Slice I i j)).comp (algebraMap Seeds SeedField) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [parameterMap, slopeToSlice, RingHom.comp_apply, toSlice, MvPolynomial.algebraMap_eq]
    rfl
  · intro k
    fin_cases k
    · simp [parameterMap, slopeToSlice, RingHom.comp_apply, generic]
    · have h := sliceLine I i j
      rw [mul_comm (algebraMap SeedField (Slice I i j) (generic 0)) (toSlice I i j (coord I j))] at h
      simpa [parameterMap, slopeToSlice, RingHom.comp_apply, generic] using h

theorem parameter_injective {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [Nontrivial (Slice I i j)] : Function.Injective (parameterMap I i j) := by
  have h := (RingHom.injective (algebraMap SeedField (Slice I i j))).comp
    (IsFractionRing.injective Seeds SeedField)
  have hf : Function.Injective ((slopeToSlice I i j).comp (parameterMap I i j)) := by
    rw [parameter_commutes]
    exact h
  exact Function.Injective.of_comp hf

private abbrev FunctionField {n : ℕ} (I : Ideal (Raw n)) :=
  FractionRing ((CoordinateRing I)[X])

private def coefficientToFrac {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n) [I.IsPrime]
    [Nontrivial (Slice I i j)] : SeedField →+* FunctionField I :=
  IsFractionRing.lift (K := SeedField)
    (g := (algebraMap (CoordinateRing I)[X] (FunctionField I)).comp (parameterMap I i j))
    ((IsFractionRing.injective (CoordinateRing I)[X] (FunctionField I)).comp
      (parameter_injective I i j))

private theorem coefficientToFrac_base {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] (d : Seeds) :
    coefficientToFrac I i j (algebraMap Seeds SeedField d) =
      algebraMap (CoordinateRing I)[X] (FunctionField I) (parameterMap I i j d) :=
  IsFractionRing.lift_algebraMap _ d

private theorem coefficientToFrac_generic {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] (k : Fin 2) :
    coefficientToFrac I i j (generic k) =
      algebraMap (CoordinateRing I)[X] (FunctionField I) (parameterMap I i j (MvPolynomial.X k)) :=
  coefficientToFrac_base I i j _

private def polynomialToFrac {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] : Over n →+* FunctionField I :=
  MvPolynomial.eval₂Hom (coefficientToFrac I i j)
    (fun k => algebraMap (CoordinateRing I)[X] (FunctionField I) (Polynomial.C (coord I k)))

private theorem originalToFrac {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] :
    (polynomialToFrac I i j).comp (MvPolynomial.map (algebraMap FX SeedField)) =
      ((algebraMap (CoordinateRing I)[X] (FunctionField I)).comp Polynomial.C).comp
        (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.map_C, polynomialToFrac, MvPolynomial.eval₂Hom_C]
    have ha : algebraMap FX SeedField a = algebraMap Seeds SeedField (MvPolynomial.C a) := rfl
    rw [ha, coefficientToFrac_base]
    simp only [parameterMap, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    rfl
  · intro k
    simp [polynomialToFrac, RingHom.comp_apply]

private theorem map_seedLine {n : ℕ} {B : Type} [CommRing B] (f : Over n →+* B)
    (i j : Fin n) : f (seedLine i j) =
      f (MvPolynomial.X i) + f (MvPolynomial.C (generic 0)) * f (MvPolynomial.X j) -
        f (MvPolynomial.C (generic 1)) := by
  simp only [seedLine, map_sub, map_add, map_mul]

private theorem map_affine_relation {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (a b s : A) : f a + f s * f b - f (a + s * b) = 0 := by
  rw [f.map_add, f.map_mul, sub_self]

set_option maxHeartbeats 1500000 in
/-- The slice maps to the function field of the curve with a free slope. This
certifies that adjoining the coefficient fractions preserves the original coordinates. -/
private def sliceToFrac {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] : Slice I i j →+* FunctionField I :=
  Ideal.Quotient.lift (sectionIdeal I i j) (polynomialToFrac I i j) <| by
    change sectionIdeal I i j ≤ RingHom.ker (polynomialToFrac I i j)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro x hx
      change ((polynomialToFrac I i j).comp (MvPolynomial.map (algebraMap FX SeedField))) x = 0
      rw [originalToFrac]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    · intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      apply RingHom.mem_ker.mpr
      let f := polynomialToFrac I i j
      let m : (CoordinateRing I)[X] →+* FunctionField I :=
        algebraMap (CoordinateRing I)[X] (FunctionField I)
      have hX (k : Fin n) : f (MvPolynomial.X k) = m (Polynomial.C (coord I k)) :=
        MvPolynomial.eval₂Hom_X' (coefficientToFrac I i j)
          (fun k => m (Polynomial.C (coord I k))) k
      have hC (k : Fin 2) : f (MvPolynomial.C (generic k)) =
          m (parameterMap I i j (MvPolynomial.X k)) :=
        (MvPolynomial.eval₂Hom_C (coefficientToFrac I i j)
          (fun k => m (Polynomial.C (coord I k))) (generic k)).trans
            (coefficientToFrac_generic I i j k)
      have hs : parameterMap I i j (MvPolynomial.X 0) = Polynomial.X := by
        simp only [parameterMap, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero]
      have ht : parameterMap I i j (MvPolynomial.X 1) =
          Polynomial.C (coord I i) + Polynomial.X * Polynomial.C (coord I j) := by
        simp only [parameterMap, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]
      have h := map_seedLine f i j
      rw [hX i, hX j, hC 0, hC 1, hs, ht] at h
      exact h.trans (map_affine_relation m _ _ _)

private theorem sliceToFrac_slope {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] :
    (sliceToFrac I i j).comp (slopeToSlice I i j) =
      algebraMap (CoordinateRing I)[X] (FunctionField I) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simpa [sliceToFrac, slopeToSlice, toSlice, RingHom.comp_apply] using
      RingHom.congr_fun (originalToFrac I i j) a
  · simp only [RingHom.comp_apply, slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change sliceToFrac I i j (Ideal.Quotient.mk (sectionIdeal I i j) (MvPolynomial.C (generic 0))) = _
    simp only [sliceToFrac, Ideal.Quotient.lift_mk, polynomialToFrac, MvPolynomial.eval₂Hom_C,
      coefficientToFrac_generic, parameterMap, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero]

theorem slope_injective {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    [I.IsPrime] [Nontrivial (Slice I i j)] : Function.Injective (slopeToSlice I i j) := by
  have hf : Function.Injective ((sliceToFrac I i j).comp (slopeToSlice I i j)) := by
    rw [sliceToFrac_slope]
    exact IsFractionRing.injective (CoordinateRing I)[X] (FunctionField I)
  exact Function.Injective.of_comp hf

private theorem clear_denominator {n : ℕ} (I : Ideal (Raw n)) (i j : Fin n)
    (x : Slice I i j) :
    ∃ (q : (CoordinateRing I)[X]) (d : Seeds), d ≠ 0 ∧
      x * algebraMap SeedField (Slice I i j) (algebraMap Seeds SeedField d) =
        slopeToSlice I i j q := by
  let : Algebra (MvPolynomial (Fin n) Seeds) (Over n) := MvPolynomial.algebraMvPolynomial
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj
    (M := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin n))) f
  obtain ⟨d, hd, hdm⟩ := m.property
  let lift : MvPolynomial (Fin n) Seeds →+* (CoordinateRing I)[X] :=
    MvPolynomial.eval₂Hom (parameterMap I i j) (fun k => Polynomial.C (coord I k))
  have hcomp : (slopeToSlice I i j).comp lift =
      (Ideal.Quotient.mk (sectionIdeal I i j)).comp
        (MvPolynomial.map (algebraMap Seeds SeedField)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact RingHom.congr_fun (parameter_commutes I i j) a
    · intro k
      simp [lift, slopeToSlice, toSlice, RingHom.comp_apply]
  refine ⟨lift g, d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
  have hgm' : f * MvPolynomial.C (algebraMap Seeds SeedField d) =
      MvPolynomial.map (algebraMap Seeds SeedField) g := by
    simpa only [MvPolynomial.algebraMap_def, ← hdm, MvPolynomial.map_C] using hgm
  calc
    _ = Ideal.Quotient.mk (sectionIdeal I i j) (f * MvPolynomial.C (algebraMap Seeds SeedField d)) :=
      (map_mul _ _ _).symm
    _ = _ := (congrArg (Ideal.Quotient.mk (sectionIdeal I i j)) hgm').trans
      (RingHom.congr_fun hcomp g).symm

abbrev PlaneSlice (P : Ideal Seeds) := Slice P 0 1

private abbrev seedIncl := rootIncl.comp rootSeeds

private abbrev seedInclOver : Over 2 →ₐ[SeedField] Over 4 :=
  MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4))

theorem seedImage_prime (I : Ideal Ambient) [I.IsPrime] : (seedImage I).IsPrime :=
  (inferInstance : I.IsPrime).comap seedIncl

private def seedToJet (I : Ideal Ambient) : CoordinateRing (seedImage I) →+* CoordinateRing I :=
  Ideal.quotientMap I seedIncl le_rfl

private theorem seedToJet_injective (I : Ideal Ambient) : Function.Injective (seedToJet I) :=
  Ideal.quotientMap_injective

theorem plane_parameter_injective (I : Ideal Ambient) [Nontrivial (JetSeedSection I)] :
    Function.Injective (parameterMap (seedImage I) 0 1) := by
  have h : (Polynomial.mapRingHom (seedToJet I)).comp (parameterMap (seedImage I) 0 1) =
      parameterMap I 0 1 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, parameterMap, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, seedToJet]
      change Polynomial.C ((Ideal.Quotient.mk I)
        (seedIncl (MvPolynomial.C a))) = Polynomial.C (algebraMap FX (CoordinateRing I) a)
      rw [show seedIncl (MvPolynomial.C a) = MvPolynomial.C a by simp [rootIncl, rootSeeds]]
      rfl
    · intro k
      fin_cases k
      · simp [parameterMap]
      · simp [parameterMap, seedToJet, rootIncl, rootSeeds, coord, RingHom.comp_apply]
  have hinj : Function.Injective ((Polynomial.mapRingHom (seedToJet I)).comp
      (parameterMap (seedImage I) 0 1)) := by
    rw [h]
    exact parameter_injective I 0 1
  exact Function.Injective.of_comp hinj

private theorem seedIncl_square :
    (seedInclOver.toRingHom).comp (MvPolynomial.map (algebraMap FX SeedField)) =
      (MvPolynomial.map (algebraMap FX SeedField)).comp seedIncl := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootIncl, rootSeeds, RingHom.comp_apply]
  · intro k
    simp [rootIncl, rootSeeds, RingHom.comp_apply]

private theorem seedLine_map : seedInclOver (seedLine 0 1) = seedLine 0 1 := by
  simp [seedLine]

private theorem plane_le (I : Ideal Ambient) :
    sectionIdeal (seedImage I) 0 1 ≤ (sectionIdeal I 0 1).comap seedInclOver := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
  · intro p hp
    change (seedInclOver.toRingHom.comp (MvPolynomial.map (algebraMap FX SeedField))) p ∈
      sectionIdeal I 0 1
    rw [seedIncl_square]
    exact (show I.map (MvPolynomial.map (algebraMap FX SeedField)) ≤
      sectionIdeal I 0 1 from le_sup_left) (Ideal.mem_map_of_mem _ hp)
  · intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change seedInclOver (seedLine 0 1) ∈ sectionIdeal I 0 1
    rw [seedLine_map]
    exact (show Ideal.span {seedLine 0 1} ≤ sectionIdeal I 0 1 from le_sup_right)
      (Ideal.mem_span_singleton_self _)

def planeToJet (I : Ideal Ambient) : PlaneSlice (seedImage I) →ₐ[SeedField] JetSeedSection I :=
  Ideal.quotientMapₐ (sectionIdeal I 0 1) seedInclOver (plane_le I)

private theorem plane_slope_commutes (I : Ideal Ambient) :
    (planeToJet I).toRingHom.comp (slopeToSlice (seedImage I) 0 1) =
      (slopeToSlice I 0 1).comp (Polynomial.mapRingHom (seedToJet I)) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change planeToJet I (slopeToSlice (seedImage I) 0 1
        (Polynomial.C (Ideal.Quotient.mk (seedImage I) a))) =
      slopeToSlice I 0 1 (Polynomial.map (seedToJet I)
        (Polynomial.C (Ideal.Quotient.mk (seedImage I) a)))
    simp only [slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.map_C, toSlice, seedToJet, Ideal.quotientMap_mk,
      planeToJet, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    have h := RingHom.congr_fun seedIncl_square a
    change seedInclOver (MvPolynomial.map (algebraMap FX SeedField) a) =
      MvPolynomial.map (algebraMap FX SeedField) (seedIncl a) at h
    exact congrArg (Ideal.Quotient.mk (sectionIdeal I 0 1)) h
  · simp [slopeToSlice, RingHom.comp_apply]

/-- A generic affine section preserves the inclusion of the plane image in the
original prime curve. -/
theorem planeToJet_injective (I : Ideal Ambient) [I.IsPrime] [Nontrivial (JetSeedSection I)] :
    Function.Injective (planeToJet I) := by
  apply (injective_iff_map_eq_zero (planeToJet I)).mpr
  intro x hx
  obtain ⟨q, d, hd, hq⟩ := clear_denominator (seedImage I) 0 1 x
  have hq' := congrArg (planeToJet I) hq
  rw [map_mul, hx, zero_mul] at hq'
  have hzero : slopeToSlice I 0 1 (Polynomial.map (seedToJet I) q) = 0 := by
    exact (RingHom.congr_fun (plane_slope_commutes I) q).symm.trans hq'.symm
  have hq0 : q = 0 := (Polynomial.map_eq_zero_iff (seedToJet_injective I)).mp
    ((injective_iff_map_eq_zero _).mp (slope_injective I 0 1) _ hzero)
  rw [hq0, map_zero] at hq
  have hd' : algebraMap Seeds SeedField d ≠ 0 :=
    fun h => hd (IsFractionRing.injective Seeds SeedField (h.trans (map_zero _).symm))
  exact ((isUnit_iff_ne_zero.mpr hd').map (algebraMap SeedField (PlaneSlice (seedImage I)))).mul_right_cancel
    (hq.trans (zero_mul _).symm)

end
end K1_14_2_3_1
end PackSource_K1_14_2_3_1Fiber

section PackSource_K1_14_2_2_2_6_1Relative
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace K1_14_2_2_2_6_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_3 Polynomial Algebra AlgebraicIndependent
open scoped Polynomial

abbrev Surface (I : Ideal Ambient) := CoordinateRing I
abbrev Image (I : Ideal Ambient) := CoordinateRing (seedImage I)
abbrev coord (I : Ideal Ambient) (i : Fin 4) : Surface I :=
  Ideal.Quotient.mk I (MvPolynomial.X i)

abbrev seedIncl : Seeds →+* Ambient := rootIncl.comp rootSeeds

def imageToSurface (I : Ideal Ambient) : Image I →+* Surface I :=
  Ideal.quotientMap I seedIncl le_rfl

theorem imageToSurface_injective (I : Ideal Ambient) :
    Function.Injective (imageToSurface I) :=
  Ideal.quotientMap_injective

private theorem finiteType_dimension (k R : Type) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ n : ℕ, ringKrullDim R = n ∧ trdeg k R = n := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k R
  let N := MvPolynomial (Fin n) k
  letI : Algebra N R := g.toRingHom.toAlgebra
  letI : IsScalarTower k N R := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  letI : FaithfulSMul N R := (faithfulSMul_iff_algebraMap_injective N R).mpr hg
  letI : Algebra.IsIntegral N R := ⟨hint⟩
  let h := PrimeSpectrum.comap (algebraMap N R)
  have hmono : StrictMono h := by
    intro a b hab
    letI : a.asIdeal.IsPrime := a.2
    exact Ideal.IsIntegral.under_lt_under (R := N) hab
  have hsurj : Function.Surjective h := Algebra.IsIntegral.comap_surjective N R
  have hdim : ringKrullDim R = ringKrullDim N := by
    refine (Order.krullDim_le_of_strictMono h hmono).antisymm ?_
    rw [Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    apply iSup_le
    intro l
    obtain ⟨P, hP⟩ := hsurj l.head
    letI : P.asIdeal.IsPrime := P.2
    letI : P.asIdeal.LiesOver l.head.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact hL ▸ le_iSup (fun L : LTSeries (PrimeSpectrum R) => (L.length : ℕ∞)) L
  refine ⟨n, ?_, ?_⟩
  · rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  · have halg : Algebra.IsAlgebraic N R :=
      ⟨fun x => (show IsIntegral N x from hint x).isAlgebraic⟩
    have hzero : trdeg N R = 0 := @trdeg_eq_zero N R _ _ _ halg
    have hN : trdeg k N = n := by
      dsimp only [N]
      simp [MvPolynomial.trdeg_of_isDomain]
    calc
      trdeg k R = trdeg k N + trdeg N R := (trdeg_add_eq k N (A := R)).symm
      _ = n := by rw [hN, hzero, add_zero]

private theorem algebraic_polynomial_eval {k B A : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [Algebra B A] {n : ℕ} (q : MvPolynomial (Fin n) k →+* A)
    (hC : ∀ a, IsAlgebraic B (q (MvPolynomial.C a)))
    (hX : ∀ i, IsAlgebraic B (q (MvPolynomial.X i)))
    (p : MvPolynomial (Fin n) k) : IsAlgebraic B (q p) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p r hp hr =>
    rw [map_add]
    exact hp.add hr
  | mul_X p i hp =>
    rw [map_mul]
    exact hp.mul (hX i)

private theorem relative_not_algebraic (I : Ideal Ambient) [I.IsPrime]
    (hdim : ringKrullDim (Surface I) = 2) (f : Seeds) (hf : f ≠ 0)
    (hgen : seedImage I = Ideal.span {f}) :
    letI : Algebra (Image I) (Surface I) :=
      RingHom.toAlgebra (R := Image I) (S := Surface I) (imageToSurface I)
    ¬ (IsAlgebraic (Image I) (coord I 2) ∧ IsAlgebraic (Image I) (coord I 3)) := by
  let B := Image I
  let A := Surface I
  letI : (seedImage I).IsPrime :=
    (inferInstance : I.IsPrime).comap seedIncl
  letI : Algebra B A := RingHom.toAlgebra (R := B) (S := A) (imageToSurface I)
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (imageToSurface_injective I)
  letI : IsScalarTower FX B A := IsScalarTower.of_algebraMap_eq (S := B) (A := A) fun a => by
    change Ideal.Quotient.mk I (MvPolynomial.C a) =
      Ideal.Quotient.mk I (seedIncl (MvPolynomial.C a))
    simp [rootIncl, rootSeeds]
  intro ⟨hy, hv⟩
  have hseed (i : Fin 2) : IsAlgebraic B (coord I (Fin.castLE (by decide : 2 ≤ 4) i)) := by
    convert isAlgebraic_algebraMap (A := A) (Ideal.Quotient.mk (seedImage I) (MvPolynomial.X i)) using 1
    change coord I _ = imageToSurface I (Ideal.Quotient.mk (seedImage I) (MvPolynomial.X i))
    simp [coord, imageToSurface, rootIncl, rootSeeds, RingHom.comp_apply]
  have hcoord (i : Fin 4) : IsAlgebraic B (coord I i) := by
    fin_cases i
    · exact hseed 0
    · exact hseed 1
    · exact hy
    · exact hv
  have hC (a : FX) : IsAlgebraic B (Ideal.Quotient.mk I (MvPolynomial.C a)) := by
    change IsAlgebraic B (algebraMap FX A a)
    rw [IsScalarTower.algebraMap_apply FX B A]
    exact isAlgebraic_algebraMap _
  letI : Algebra.IsAlgebraic B A := ⟨fun z => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact algebraic_polynomial_eval (B := B) (A := A) (Ideal.Quotient.mk I) hC hcoord p⟩
  obtain ⟨n, hn, hnt⟩ := finiteType_dimension FX B
  obtain ⟨m, hm, hmt⟩ := finiteType_dimension FX A
  have htrdeg := trdeg_add_eq FX B (A := A)
  rw [trdeg_eq_zero (R := B) (A := A), add_zero, hnt, hmt] at htrdeg
  have hnm : n = m := by exact_mod_cast htrdeg
  have hBA : ringKrullDim B = ringKrullDim A := by rw [hn, hm, hnm]
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hf)
  change ringKrullDim (CoordinateRing (Ideal.span {f})) + 1 ≤ ringKrullDim Seeds at hle
  rw [← hgen, hBA, hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field] at hle
  norm_num [Nat.card_eq_fintype_card] at hle

/-- Adjoin an independent slope and evaluate the jet intercept at the affine
linear combination of the two jet coordinates. -/
def lineEval {B A : Type} [CommRing B] [CommRing A] (i : B →+* A) (y v : A) :
    B[X][X] →+* A[X] :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom i) (Polynomial.C y + Polynomial.X * Polynomial.C v)

private theorem lineEval_injective {B A : Type} [CommRing B] [IsDomain B] [Infinite B]
    [CommRing A] [Algebra B A] (y v : A)
    (h : ¬ (IsAlgebraic B y ∧ IsAlgebraic B v)) :
    Function.Injective (lineEval (algebraMap B A) y v) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hp0
  have hex : ∃ j, p.coeff j ≠ 0 := by
    by_contra! h
    exact hp0 (Polynomial.ext fun j => (h j).trans (Polynomial.coeff_zero _).symm)
  obtain ⟨j, hj⟩ := hex
  let bad := {c : B | (p.coeff j).IsRoot c}
  have hbad : bad.Finite := Polynomial.finite_setOfPred_isRoot hj
  obtain ⟨c, hc⟩ := hbad.exists_notMem
  obtain ⟨d, hd⟩ := (hbad.insert c).exists_notMem
  have hdc : d ≠ c := fun e => hd (e ▸ Set.mem_insert c bad)
  have hd' : d ∉ bad := fun hb => hd (Set.mem_insert_of_mem _ hb)
  have alg (b : B) (hb : b ∉ bad) : IsAlgebraic B (y + b • v) := by
    let q := p.map (Polynomial.evalRingHom b)
    refine ⟨q, ?_, ?_⟩
    · intro hz
      apply hb
      change (p.coeff j).eval b = 0
      have h := congrArg (fun z : B[X] => z.coeff j) hz
      change (p.map (Polynomial.evalRingHom b)).coeff j = (0 : B[X]).coeff j at h
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at h
      exact h
    · let E := Polynomial.evalRingHom (algebraMap B A b)
      have hcoeff : E.comp (Polynomial.mapRingHom (algebraMap B A)) =
          (algebraMap B A).comp (Polynomial.evalRingHom b) := by
        apply Polynomial.ringHom_ext
        · intro a
          simp [E, RingHom.comp_apply]
        · simp [E, RingHom.comp_apply]
      have hs : E (Polynomial.C y + Polynomial.X * Polynomial.C v) = y + b • v := by
        change (Polynomial.C y + Polynomial.X * Polynomial.C v).eval
          (algebraMap B A b) = y + b • v
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_C, Algebra.smul_def]
      have H := congrArg E hp
      change E (p.eval₂ (Polynomial.mapRingHom (algebraMap B A))
        (Polynomial.C y + Polynomial.X * Polynomial.C v)) = E 0 at H
      rw [Polynomial.hom_eval₂, hcoeff, hs, map_zero] at H
      rwa [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hvscaled := (alg d hd').sub (alg c hc)
  have he : (y + d • v) - (y + c • v) = (d - c) • v := by
    rw [sub_smul]
    abel
  rw [he] at hvscaled
  have hv := hvscaled.of_smul (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.mpr hdc))
  have hy := (alg c hc).sub (hv.smul c)
  rw [add_sub_cancel_right] at hy
  exact h ⟨hy, hv⟩

/-- The generic jet intercept is independent of its slope over the seed image. -/
theorem jetEval_injective (I : Ideal Ambient) [I.IsPrime]
    (hdim : ringKrullDim (Surface I) = 2) (f : Seeds) (hf : f ≠ 0)
    (hgen : seedImage I = Ideal.span {f}) :
    Function.Injective (lineEval (B := Image I) (A := Surface I) (imageToSurface I) (coord I 2) (coord I 3)) := by
  letI : (seedImage I).IsPrime :=
    (inferInstance : I.IsPrime).comap seedIncl
  letI : Algebra (Image I) (Surface I) :=
      RingHom.toAlgebra (R := Image I) (S := Surface I) (imageToSurface I)
  letI : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
  letI : Infinite (Image I) := Infinite.of_injective _ (algebraMap FX (Image I)).injective
  exact lineEval_injective _ _ (relative_not_algebraic I hdim f hf hgen)

end
end K1_14_2_2_2_6_1
end PackSource_K1_14_2_2_2_6_1Relative

section PackSource_K1_14_2_3_1Quotient
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_3_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3 Polynomial
open scoped Polynomial BigOperators

private theorem elimination_line : eliminate (seedLine 0 1) = 0 := by
  simp [eliminate, lineValues, seedLine, Polynomial.algebraMap_eq]

private def reconstruct (P : Ideal Seeds) : SeedField[X] →ₐ[SeedField] PlaneSlice P :=
  aeval (Ideal.Quotient.mk (sectionIdeal P 0 1) (MvPolynomial.X 1))

private theorem elimination_reconstruct (P : Ideal Seeds) :
    (reconstruct P).comp eliminate = Ideal.Quotient.mkₐ SeedField (sectionIdeal P 0 1) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · have h := sliceLine P 0 1
    simp only [toSlice, coord, Ideal.quotientMap_mk, MvPolynomial.map_X] at h
    simpa [eliminate, lineValues, reconstruct, sub_eq_iff_eq_add] using h.symm
  · simp [eliminate, lineValues, reconstruct]

/-- Eliminate the first coordinate using the generic line and retain the second
coordinate as the univariate variable. -/
def lineQuotientEquiv (P : Ideal Seeds) :
    PlaneSlice P ≃ₐ[SeedField] (SeedField[X] ⧸ P.map lineRestriction) := by
  let A := Ideal.Quotient.mkₐ SeedField (sectionIdeal P 0 1)
  let B := Ideal.Quotient.mkₐ SeedField (P.map lineRestriction)
  let f := B.comp eliminate
  let g := reconstruct P
  have hf : sectionIdeal P 0 1 ≤ RingHom.ker f.toRingHom := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem lineRestriction hp)
    · intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact show B (eliminate (seedLine 0 1)) = 0 by rw [elimination_line, map_zero]
  have hg : P.map lineRestriction ≤ RingHom.ker g.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    have h := DFunLike.congr_fun (elimination_reconstruct P)
      (MvPolynomial.map (algebraMap FX SeedField) p)
    refine (show g (lineRestriction p) = A _ from h).trans ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show P.map _ ≤ sectionIdeal P 0 1 from le_sup_left) (Ideal.mem_map_of_mem _ hp))
  let f' := Ideal.Quotient.liftₐ (sectionIdeal P 0 1) f (fun _ hx => hf hx)
  let g' := Ideal.Quotient.liftₐ (P.map lineRestriction) g (fun _ hx => hg hx)
  refine AlgEquiv.ofAlgHom f' g' ?_ ?_
  · apply AlgHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hfg : f'.comp g = B := by
      apply Polynomial.algHom_ext
      simp [f', f, g, reconstruct, eliminate, lineValues, Ideal.Quotient.liftₐ_apply]
    exact DFunLike.congr_fun hfg p
  · apply AlgHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    change g' (f' (Ideal.Quotient.mk (sectionIdeal P 0 1) p)) =
      Ideal.Quotient.mk (sectionIdeal P 0 1) p
    rw [show f' (Ideal.Quotient.mk (sectionIdeal P 0 1) p) = B (eliminate p) by rfl]
    change (reconstruct P) (eliminate p) = Ideal.Quotient.mk (sectionIdeal P 0 1) p
    exact DFunLike.congr_fun (elimination_reconstruct P) p

end
end K1_14_2_3_1
end PackSource_K1_14_2_3_1Quotient

section PackSource_K1_14_2_4_1_1Defs
set_option autoImplicit true
namespace K1_14_2_4_1_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_4_1
open scoped Polynomial

/-- Generic evaluation of the two constant seed coordinates over the independent X. -/
def genericSeedMap (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    Seeds →+* ConstantSeedX C₀ :=
  MvPolynomial.eval₂Hom (extendX C₀) (insertConstant C₀ ∘ seedCoordinate C₀)

/-- The generic evaluation on the coordinate ring of the seed curve. -/
def seedCurveMap (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (h : RingHom.ker (genericSeedMap C₀) = seedEquation C₀) :
    (Seeds ⧸ seedEquation C₀) →+* ConstantSeedX C₀ :=
  Ideal.Quotient.lift (seedEquation C₀) (genericSeedMap C₀) fun _ hf =>
    RingHom.mem_ker.mp (h.symm ▸ hf)

/-- The generic seed evaluation presents the fraction field of the seed curve. -/
structure SeedLocalization (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] : Prop where
  kernel : RingHom.ker (genericSeedMap C₀) = seedEquation C₀
  localized : letI : Algebra (Seeds ⧸ seedEquation C₀) (ConstantSeedX C₀) :=
    (seedCurveMap C₀ kernel).toAlgebra
    IsFractionRing (Seeds ⧸ seedEquation C₀) (ConstantSeedX C₀)

/-- Write the root ambient ring as the polynomial ring in its last coordinate Y. -/
def rootView : RootAmbient ≃ₐ[FX] Seeds[X] :=
  (MvPolynomial.renameEquiv FX finSuccEquivLast).trans (MvPolynomial.optionEquivLeft FX (Fin 2))

end
end K1_14_2_4_1_1
end PackSource_K1_14_2_4_1_1Defs

section PackSource_K1_14_2_4_1_1Aux1
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_2_4_1_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_4_1 K1_14_2_3_1
open scoped Polynomial

private theorem root_index_zero : finSuccEquivLast (0 : Fin 3) = some 0 := rfl
private theorem root_index_one : finSuccEquivLast (1 : Fin 3) = some 1 := rfl
private theorem root_index_two : finSuccEquivLast (2 : Fin 3) = none := finSuccEquivLast_last

theorem rootView_seed : (rootView.toRingEquiv.toRingHom).comp rootSeeds = Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootView, rootSeeds]
  · intro i
    fin_cases i <;> simp [rootView, rootSeeds, root_index_zero, root_index_one]

theorem genericRootMap_eq (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    genericRootMap C₀ =
      (Polynomial.mapRingHom (genericSeedMap C₀)).comp rootView.toRingEquiv.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [genericRootMap, genericSeedMap, rootView]
  · intro i
    fin_cases i <;> simp [genericRootMap, genericSeedMap, rootView, root_index_zero,
      root_index_one, root_index_two]

/-- Once the base is localized, prime extension and contraction are the ordinary
localization correspondence for a polynomial ring. -/
theorem exists_generic_prime (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (hC : SeedLocalization C₀) (J : Ideal RootAmbient) (hJ : J.IsPrime)
    (hseed : J.comap rootSeeds = seedEquation C₀) :
    ∃ P : Ideal (ConstantSeedX C₀)[X], P.IsPrime ∧ J = P.comap (genericRootMap C₀) := by
  let A := Seeds ⧸ seedEquation C₀
  let : CommRing A := Ideal.Quotient.commRing (seedEquation C₀)
  let : CommRing A[X] := Polynomial.commRing
  let u : Seeds →+* A := Ideal.Quotient.mk (seedEquation C₀)
  let φ : A →+* ConstantSeedX C₀ := seedCurveMap C₀ hC.kernel
  have hφ : φ.comp u = genericSeedMap C₀ := RingHom.ext fun _ => rfl
  let : (seedEquation C₀).IsPrime := hC.kernel ▸ RingHom.ker_isPrime (genericSeedMap C₀)
  let : IsDomain A := Ideal.Quotient.isDomain (seedEquation C₀)
  let : Algebra A (ConstantSeedX C₀) := φ.toAlgebra
  let : IsFractionRing A (ConstantSeedX C₀) := hC.localized
  let : Algebra A[X] (ConstantSeedX C₀)[X] := Polynomial.algebra A (ConstantSeedX C₀)
  let M : Submonoid A[X] := (nonZeroDivisors A).map Polynomial.C
  let : IsLocalization M (ConstantSeedX C₀)[X] :=
    Polynomial.isLocalization (nonZeroDivisors A) (ConstantSeedX C₀)
  let e := rootView.toRingEquiv
  let I₀ := J.comap e.symm.toRingHom
  let : I₀.IsPrime := hJ.comap e.symm.toRingHom
  have hseed' : I₀.comap Polynomial.C = seedEquation C₀ := by
    rw [← hseed]
    ext s
    have hcom : e (rootSeeds s) = Polynomial.C s := DFunLike.congr_fun rootView_seed s
    change e.symm (Polynomial.C s) ∈ J ↔ rootSeeds s ∈ J
    rw [← hcom, e.symm_apply_apply]
  let v := Polynomial.mapRingHom u
  have hv : Function.Surjective v := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hvker : RingHom.ker v ≤ I₀ := by
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (seedEquation C₀))) ≤ I₀
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
    exact Ideal.map_le_iff_le_comap.mpr hseed'.symm.le
  let I := I₀.map v
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hv hvker
  have hcomap : I.comap v = I₀ := by
    change (I₀.map v).comap v = I₀
    rw [Ideal.comap_map_of_surjective _ hv, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hvker]
  have hdisjoint : Disjoint (M : Set A[X]) (I : Set A[X]) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ hmem
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hs : s ∈ (I.comap v).comap Polynomial.C := by
      change v (Polynomial.C s) ∈ I
      simpa only [SetLike.mem_coe, v, u, Polynomial.coe_mapRingHom, Polynomial.map_C] using hmem
    rw [hcomap, hseed'] at hs
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (Ideal.Quotient.eq_zero_iff_mem.mpr hs)
  let P := I.map (algebraMap A[X] (ConstantSeedX C₀)[X])
  have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ I hI hdisjoint
  have heq : P.comap (Polynomial.mapRingHom φ) = I :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hI hdisjoint
  refine ⟨P, hP, ?_⟩
  rw [genericRootMap_eq, ← hφ, ← Polynomial.mapRingHom_comp,
    ← Ideal.comap_comap, ← Ideal.comap_comap, heq, hcomap]
  ext f
  change f ∈ J ↔ e.symm (e f) ∈ J
  rw [e.symm_apply_apply]

/-- Restricting to the independent generic line retains the entire seed curve degree. -/
theorem seed_section_rank (C₀ : ConstantSeeds) :
    Module.finrank SeedField (PlaneSlice (seedEquation C₀)) = C₀.totalDegree := by
  rw [(lineQuotientEquiv (seedEquation C₀)).toLinearEquiv.finrank_eq,
    seedEquation, Ideal.map_span, Set.image_singleton, finrank_quotient_span_eq_natDegree,
    totalDegree_lineRestriction]
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective _)]

theorem seed_degree_pos (C₀ : ConstantSeeds) (hC : Irreducible C₀) : 0 < C₀.totalDegree := by
  by_contra! hn
  have h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hn)
  have hc : C₀.coeff 0 ≠ 0 := by
    intro hz
    exact hC.ne_zero (by simpa [hz] using h)
  exact hC.not_isUnit (h ▸ hc.isUnit.map MvPolynomial.C)

end
end K1_14_2_4_1_1
end PackSource_K1_14_2_4_1_1Aux1

section PackSource_K1_14_2_4_1_1Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_2_4_1_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_4_1 K1_14_2_3_1
open scoped Polynomial

/-- Identify the function field of the constant seed curve with independent X. -/
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)], SeedLocalization C₀

/-- The ratio of the two generic line lengths is the relative degree in Y. -/
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient)
    (P : Ideal (ConstantSeedX C₀)[X]), SeedLocalization C₀ →
    P.IsPrime → J = P.comap (genericRootMap C₀) →
    Module.Finite SeedField (RootSeedSection J) →
    0 < Module.finrank SeedField (RootSeedSection J) →
    Module.finrank SeedField (RootSeedSection J) =
      Module.finrank SeedField (PlaneSlice (seedEquation C₀)) *
        Module.finrank (ConstantSeedX C₀) ((ConstantSeedX C₀)[X] ⧸ P)

/-- Clearing X-denominators and dividing by the resulting X-content changes the
generic Y-polynomial by a unit. -/
theorem primitive_equation (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (f : (ConstantSeedX C₀)[X]) (hf : f ≠ 0) :
    ∃ q : ((ConstantSeedField C₀)[X])[X],
      q.IsPrimitive ∧ q.natDegree = f.natDegree ∧ Associated (q.map (insertX C₀)) f := by
  let : EuclideanDomain (ConstantSeedField C₀)[X] := Polynomial.instEuclideanDomain
  let : IsPrincipalIdealRing (ConstantSeedField C₀)[X] := EuclideanDomain.instIsPrincipalIdealRing
  let : UniqueFactorizationMonoid (ConstantSeedField C₀)[X] :=
    PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : StrongNormalizationMonoid (ConstantSeedField C₀)[X] :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let : NormalizedGCDMonoid (ConstantSeedField C₀)[X] :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let D := IsLocalization.integerNormalization (nonZeroDivisors (ConstantSeedField C₀)[X]) f
  have hinj := IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)
  obtain ⟨b, hb, hbD⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (ConstantSeedField C₀)[X]) f
  have he : D.map (insertX C₀) = Polynomial.C (insertX C₀ b) * f := by
    exact hbD.trans (Algebra.smul_def _ _)
  have hbn : insertX C₀ b ≠ 0 := by
    exact (map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at he
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hbn) hf) he.symm
  have hcontent : insertX C₀ D.content ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr fun hc => hD (Polynomial.content_eq_zero_iff.mp hc)
  have hg : (D.map (insertX C₀)).natDegree = f.natDegree := by
    rw [he, Polynomial.natDegree_C_mul hbn]
  have hq : Associated (D.map (insertX C₀)) (D.primPart.map (insertX C₀)) := by
    conv_lhs => rw [D.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C]
    exact associated_unit_mul_left _ _
      ((isUnit_iff_ne_zero.mpr hcontent).map Polynomial.C)
  refine ⟨D.primPart, D.isPrimitive_primPart, ?_, ?_⟩
  · rw [Polynomial.natDegree_primPart, ← Polynomial.natDegree_map_eq_of_injective hinj D]
    exact hg
  · apply hq.symm.trans
    rw [he]
    exact associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.mpr hbn).map Polynomial.C)

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_4_1.c1 := by
  intro C₀ hC J g hJ hseed hfinite hrank hg
  have hCdeg := seed_degree_pos C₀ hC.out
  have hpos : 0 < Module.finrank SeedField (RootSeedSection J) := by
    rw [hrank]
    exact Nat.mul_pos hCdeg hg
  let hbase := h1 C₀
  obtain ⟨P, hP, hcontract⟩ := exists_generic_prime C₀ hbase J hJ hseed
  let : P.IsPrime := hP
  let : EuclideanDomain (ConstantSeedX C₀)[X] := Polynomial.instEuclideanDomain
  let : IsPrincipalIdealRing (ConstantSeedX C₀)[X] := EuclideanDomain.instIsPrincipalIdealRing
  let : P.IsPrincipal := IsPrincipalIdealRing.principal P
  let f := Submodule.IsPrincipal.generator P
  have hfspan : Ideal.span {f} = P := Ideal.span_singleton_generator P
  have hfdeg : f.natDegree = g := by
    have hquot :
        Module.finrank (ConstantSeedX C₀) ((ConstantSeedX C₀)[X] ⧸ P) = f.natDegree := by
      rw [← hfspan, finrank_quotient_span_eq_natDegree]
    have h := h2 C₀ J P hbase hP hcontract hfinite hpos
    rw [hrank, seed_section_rank C₀, hquot] at h
    exact Nat.mul_left_cancel hCdeg h.symm
  have hPne : P ≠ ⊥ := by
    intro hzero
    have hfzero : f = 0 := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mp hzero
    rw [hfzero, Polynomial.natDegree_zero] at hfdeg
    exact (Nat.ne_of_gt hg) hfdeg.symm
  have hfi : Irreducible f := (Submodule.IsPrincipal.prime_generator_of_isPrime P hPne).irreducible
  obtain ⟨q, hq, hqdeg, hassoc⟩ := primitive_equation C₀ f hfi.ne_zero
  exact ⟨{
    equation := q
    primitive := hq
    degree := hqdeg.trans hfdeg
    irreducible := hassoc.symm.irreducible hfi
    contraction := hcontract.trans (congrArg (fun I => I.comap (genericRootMap C₀))
      (hfspan.symm.trans (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)) }⟩

end
end K1_14_2_4_1_1
end PackSource_K1_14_2_4_1_1Split

section PackSource_K1_14_2_2_2_6_1Incidence
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K1_14_2_2_2_6_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_3 K1_14_2_2_2_6 Polynomial
open scoped Polynomial

abbrev Params := MvPolynomial (Fin 4) FX
abbrev Double (R : Type) [CommRing R] := R[X][X]
private abbrev Triple (R : Type) [CommRing R] := R[X][X][X]

private def constants {R : Type} [CommRing R] : R →+* Triple R :=
  Polynomial.C.comp (Polynomial.C.comp Polynomial.C)

def integralRestriction : Seeds →+* Params[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (K1_14_2_3_1.lineValues (MvPolynomial.X 0) (MvPolynomial.X 2))

/-- The variables of the iterated ring, from outermost to innermost, are
the seed slope, the jet intercept, and the jet slope. -/
private def parameterToTriple : Params →+* Triple Seeds :=
  let x : Fin 4 → Triple Seeds :=
    ![Polynomial.X, Polynomial.C (Polynomial.C Polynomial.X),
      constants (MvPolynomial.X (0 : Fin 2) : Seeds) +
        Polynomial.X * constants (MvPolynomial.X (1 : Fin 2) : Seeds),
      Polynomial.C Polynomial.X]
  MvPolynomial.eval₂Hom ((constants (R := Seeds)).comp (MvPolynomial.C : FX →+* Seeds)) x

private def toTriple : Params[X] →+* Triple Seeds :=
  Polynomial.eval₂RingHom parameterToTriple (constants (MvPolynomial.X 1))

private def fromTriple : Triple Seeds →+* Params[X] :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom integralRestriction (Polynomial.C (MvPolynomial.X 1)))
      (Polynomial.C (MvPolynomial.X 3)))
    (Polynomial.C (MvPolynomial.X 0))

private theorem fromTriple_constants (f : Seeds) :
    fromTriple (constants f) = integralRestriction f := by
  simp [fromTriple, constants, RingHom.comp_apply]

private theorem fromTriple_left : fromTriple.comp toTriple = RingHom.id _ := by
  have h : fromTriple.comp parameterToTriple = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, parameterToTriple, fromTriple_constants, integralRestriction]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, parameterToTriple, fromTriple, constants,
          integralRestriction, K1_14_2_3_1.lineValues]
      all_goals ring
  apply Polynomial.ringHom_ext
  · intro a
    simpa [RingHom.comp_apply, toTriple] using RingHom.congr_fun h a
  · simp [RingHom.comp_apply, toTriple, fromTriple_constants, integralRestriction,
      K1_14_2_3_1.lineValues]

private theorem toTriple_restriction (f : Seeds) :
    toTriple (integralRestriction f) = constants f := by
  suffices toTriple.comp integralRestriction = constants by
    exact RingHom.congr_fun this f
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, toTriple, parameterToTriple, integralRestriction]
  · intro i
    fin_cases i
    · have h0 : integralRestriction (MvPolynomial.X (0 : Fin 2)) =
          Polynomial.C (MvPolynomial.X 2) - Polynomial.C (MvPolynomial.X 0) * Polynomial.X := by
        simp [integralRestriction, K1_14_2_3_1.lineValues]
      change toTriple (integralRestriction (MvPolynomial.X (0 : Fin 2))) = _
      rw [h0, map_sub toTriple, map_mul toTriple]
      simp [toTriple, parameterToTriple]
      exact add_sub_cancel_right (constants (MvPolynomial.X (0 : Fin 2) : Seeds)) _
    · simp [toTriple, integralRestriction, K1_14_2_3_1.lineValues]

abbrev coords (I : Ideal Ambient) (i : Fin 4) : Double (Surface I) :=
  Polynomial.C (Polynomial.C (coord I i))

/-- Substitute the two free slopes and their corresponding intercepts. -/
def rawParameters (I : Ideal Ambient) : Params →+* Double (Surface I) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (Polynomial.C.comp (algebraMap FX (Surface I))))
    ![Polynomial.X, Polynomial.C Polynomial.X,
      coords I 0 + Polynomial.X * coords I 1,
      coords I 2 + Polynomial.C Polynomial.X * coords I 3]

def rawEval (I : Ideal Ambient) : Params[X] →+* Double (Surface I) :=
  Polynomial.eval₂RingHom (rawParameters I) (coords I 1)

private def tripleQuotient (I : Ideal Ambient) : Triple Seeds →+* Triple (Image I) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Ideal.Quotient.mk (seedImage I))))

private def tripleJet (I : Ideal Ambient) : Triple (Image I) →+* Double (Surface I) :=
  Polynomial.mapRingHom
    (lineEval (B := Image I) (A := Surface I) (imageToSurface I) (coord I 2) (coord I 3))

private theorem rawEval_factor (I : Ideal Ambient) :
    rawEval I = (tripleJet I).comp ((tripleQuotient I).comp toTriple) := by
  have h : rawParameters I = (tripleJet I).comp ((tripleQuotient I).comp parameterToTriple) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, rawParameters, parameterToTriple, constants, tripleQuotient,
        tripleJet, lineEval, imageToSurface, rootIncl, rootSeeds]
      all_goals rfl
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, rawParameters, parameterToTriple, constants, tripleQuotient,
          tripleJet, lineEval, coords, coord, imageToSurface, rootIncl, rootSeeds]
      all_goals ring
  apply Polynomial.ringHom_ext
  · intro a
    simpa [rawEval, RingHom.comp_apply, toTriple] using RingHom.congr_fun h a
  · simp [rawEval, RingHom.comp_apply, toTriple, constants, tripleQuotient,
      tripleJet, lineEval, coords, coord, imageToSurface, rootIncl, rootSeeds]

theorem rawEval_eq_zero_iff (I : Ideal Ambient) [I.IsPrime]
    (hdim : ringKrullDim (Surface I) = 2) (f : Seeds) (hf : f ≠ 0)
    (hgen : seedImage I = Ideal.span {f}) (q : Params[X]) :
    rawEval I q = 0 ↔ integralRestriction f ∣ q := by
  have hinj : Function.Injective (tripleJet I) :=
    Polynomial.map_injective _ (jetEval_injective I hdim f hf hgen)
  have hzero (x : Triple (Image I)) : tripleJet I x = 0 ↔ x = 0 :=
    ⟨(injective_iff_map_eq_zero _).mp hinj x, fun h => h.symm ▸ map_zero _⟩
  simp only [rawEval_factor, RingHom.comp_apply, hzero]
  rw [← (RingHom.mem_ker : toTriple q ∈ RingHom.ker (tripleQuotient I) ↔
    tripleQuotient I (toTriple q) = 0)]
  rw [tripleQuotient, Polynomial.ker_mapRingHom, Polynomial.ker_mapRingHom,
    Polynomial.ker_mapRingHom, Ideal.mk_ker, hgen, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  change toTriple q ∈ (Ideal.span {constants f} : Ideal (Triple Seeds)) ↔ integralRestriction f ∣ q
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    have h := congrArg fromTriple ha
    rw [map_mul, fromTriple_constants, show fromTriple (toTriple q) = q from
      RingHom.congr_fun fromTriple_left q] at h
    exact ⟨fromTriple a, h.symm.trans (mul_comm _ _)⟩
  · rintro ⟨a, ha⟩
    refine ⟨toTriple a, ?_⟩
    rw [ha, map_mul, toTriple_restriction]
    exact mul_comm (toTriple a) (constants f)

theorem seedParameters_generic (i : Fin 2) :
    seedParameters (generic i) = sliceParameter (![0, 2] i) := by
  unfold generic seedParameters
  rw [IsFractionRing.lift_algebraMap]
  simp [sliceParameter]

theorem seedParameters_base (a : FX) :
    seedParameters (algebraMap FX SeedField a) = algebraMap FX SectionField a := by
  change seedParameters (algebraMap Seeds SeedField (MvPolynomial.C a)) =
    algebraMap Params SectionField (MvPolynomial.C a)
  unfold seedParameters
  rw [IsFractionRing.lift_algebraMap]
  simp

theorem restriction_eval (f : Seeds) :
    mixedSeedRestriction f =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX SectionField))
        (K1_14_2_3_1.lineValues (sliceParameter 0) (sliceParameter 2)) f := by
  suffices (Polynomial.mapRingHom seedParameters).comp K1_14_2_3_1.lineRestriction =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX SectionField))
        (K1_14_2_3_1.lineValues (sliceParameter 0) (sliceParameter 2)) from
    RingHom.congr_fun this f
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, K1_14_2_3_1.lineRestriction, K1_14_2_3_1.eliminate,
      Polynomial.algebraMap_eq, seedParameters_base]
  · intro i
    fin_cases i <;>
      simp [RingHom.comp_apply, K1_14_2_3_1.lineRestriction, K1_14_2_3_1.eliminate,
        K1_14_2_3_1.lineValues, seedParameters_generic]

theorem restriction_map (f : Seeds) :
    (integralRestriction f).map (algebraMap Params SectionField) = mixedSeedRestriction f := by
  rw [restriction_eval]
  suffices (Polynomial.mapRingHom (algebraMap Params SectionField)).comp integralRestriction =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX SectionField))
        (K1_14_2_3_1.lineValues (sliceParameter 0) (sliceParameter 2)) from
    RingHom.congr_fun this f
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, integralRestriction]
    all_goals rfl
  · intro i
    fin_cases i <;> simp [integralRestriction, K1_14_2_3_1.lineValues,
      sliceParameter]

/-- There is no relation over the ground field among the four incidence
parameters. The only relation after adjoining the free seed coordinate has
positive degree in that coordinate. -/
theorem rawParameters_injective (I : Ideal Ambient) [I.IsPrime]
    (hdim : ringKrullDim (Surface I) = 2) (f : Seeds) (hf : f ≠ 0)
    (hgen : seedImage I = Ideal.span {f}) :
    Function.Injective (rawParameters I) := by
  have hp : 0 < (integralRestriction f).natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective Params SectionField),
      restriction_map, mixedSeedRestriction,
      Polynomial.natDegree_map_eq_of_injective seedParameters.injective,
      K1_14_2_3_1.totalDegree_lineRestriction]
    by_contra! he
    have he' := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero he)
    have hconst : f.coeff 0 ≠ 0 := fun h0 => hf (by simpa [h0] using he')
    have hprime : (seedImage I).IsPrime := (inferInstance : I.IsPrime).comap K1_14_2_2_2_6_1.seedIncl
    have hu : IsUnit f := he' ▸ hconst.isUnit.map MvPolynomial.C
    exact hprime.ne_top (hgen.trans (Ideal.span_singleton_eq_top.mpr hu))
  apply (injective_iff_map_eq_zero _).mpr
  intro d hd
  have hz : rawEval I (Polynomial.C d) = 0 := by simpa [rawEval] using hd
  have hdiv := (rawEval_eq_zero_iff I hdim f hf hgen _).mp hz
  by_contra hn
  have := Polynomial.natDegree_le_of_dvd hdiv (Polynomial.C_ne_zero.mpr hn)
  simp at this
  omega

end
end K1_14_2_2_2_6_1
end PackSource_K1_14_2_2_2_6_1Incidence

section PackSource_K1_14_2_4_1_1_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_2_4_1_1_1

noncomputable section

open K1_14 K1_14_2_4_1 K1_14_2_4_1_1
open scoped Polynomial

private abbrev PolynomialSeeds := MvPolynomial (Fin 2) L[X]

/-- Move the independent univariate indeterminate into the coefficient ring. -/
private def exchangeX : ConstantSeeds[X] ≃+* PolynomialSeeds :=
  ((MvPolynomial.optionEquivLeft L (Fin 2)).symm.trans
    (MvPolynomial.optionEquivRight L (Fin 2))).toRingEquiv

private theorem exchange_constant (a : ConstantSeeds) :
    exchangeX (Polynomial.C a) = MvPolynomial.map Polynomial.C a := by
  have h : exchangeX.toRingHom.comp Polynomial.C = MvPolynomial.map Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.optionEquivRight L (Fin 2)
        ((MvPolynomial.optionEquivLeft L (Fin 2)).symm (Polynomial.C (MvPolynomial.C r))) = _
      simp
    · intro i
      change MvPolynomial.optionEquivRight L (Fin 2)
        ((MvPolynomial.optionEquivLeft L (Fin 2)).symm (Polynomial.C (MvPolynomial.X i))) = _
      simp
  exact DFunLike.congr_fun h a

private theorem exchange_indeterminate :
    exchangeX Polynomial.X = MvPolynomial.C Polynomial.X := by
  change MvPolynomial.optionEquivRight L (Fin 2)
    ((MvPolynomial.optionEquivLeft L (Fin 2)).symm Polynomial.X) = _
  simp

private def baseChange : PolynomialSeeds →+* Seeds :=
  MvPolynomial.map (algebraMap L[X] FX)

private def quotientPolynomial (C₀ : ConstantSeeds) :
    ConstantSeeds[X] →+* (ConstantSeedRing C₀)[X] :=
  Polynomial.mapRingHom (Ideal.Quotient.mk (constantIdeal C₀))

private def intoFunctionField (C₀ : ConstantSeeds) :
    (ConstantSeedRing C₀)[X] →+* ConstantSeedX C₀ :=
  (insertX C₀).comp (Polynomial.mapRingHom
    (algebraMap (ConstantSeedRing C₀) (ConstantSeedField C₀)))

private theorem intoFunctionField_injective (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    Function.Injective (intoFunctionField C₀) :=
  (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)).comp
    (Polynomial.map_injective _ (IsFractionRing.injective
      (ConstantSeedRing C₀) (ConstantSeedField C₀)))

private theorem extend_on_polynomial (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (p : L[X]) :
    extendX C₀ (algebraMap L[X] FX p) = insertX C₀ (p.map (constToSeed C₀)) := by
  unfold extendX IsFractionRing.map
  rw [IsLocalization.map_eq]
  rfl

/-- The prescribed generic evaluation agrees with quotienting coefficients before
inverting denominators. -/
private theorem generic_comp (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    (genericSeedMap C₀).comp (baseChange.comp exchangeX.toRingHom) =
      (intoFunctionField C₀).comp (quotientPolynomial C₀) := by
  apply Polynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · intro r
      change genericSeedMap C₀ (baseChange (exchangeX (Polynomial.C (MvPolynomial.C r)))) =
        intoFunctionField C₀ (quotientPolynomial C₀ (Polynomial.C (MvPolynomial.C r)))
      simp [exchange_constant, baseChange, genericSeedMap, intoFunctionField, quotientPolynomial,
        extend_on_polynomial, constToSeed]
    · intro i
      change genericSeedMap C₀ (baseChange (exchangeX (Polynomial.C (MvPolynomial.X i)))) =
        intoFunctionField C₀ (quotientPolynomial C₀ (Polynomial.C (MvPolynomial.X i)))
      simp [exchange_constant, baseChange, genericSeedMap, intoFunctionField, quotientPolynomial,
        insertConstant, seedCoordinate]
  · change genericSeedMap C₀ (baseChange (exchangeX Polynomial.X)) =
      intoFunctionField C₀ (quotientPolynomial C₀ Polynomial.X)
    simp [exchange_indeterminate, baseChange, genericSeedMap, intoFunctionField,
      quotientPolynomial, extend_on_polynomial]

private theorem generic_kernel (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    RingHom.ker (genericSeedMap C₀) = seedEquation C₀ := by
  let : Algebra PolynomialSeeds Seeds := MvPolynomial.algebraMvPolynomial
  let M : Submonoid PolynomialSeeds := (nonZeroDivisors L[X]).map MvPolynomial.C
  let : IsLocalization M Seeds := MvPolynomial.isLocalization (nonZeroDivisors L[X]) FX
  have hk : (RingHom.ker (genericSeedMap C₀)).comap baseChange =
      (Ideal.span {Polynomial.C C₀}).map exchangeX.toRingHom := by
    have h : ((RingHom.ker (genericSeedMap C₀)).comap baseChange).comap exchangeX.toRingHom =
        Ideal.span {Polynomial.C C₀} := by
      rw [RingHom.comap_ker, RingHom.comap_ker, RingHom.comp_assoc, generic_comp,
        RingHom.ker_comp_of_injective _ (intoFunctionField_injective C₀),
        quotientPolynomial, Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span,
        Set.image_singleton]
    rw [← h, Ideal.map_comap_of_surjective exchangeX.toRingHom exchangeX.surjective]
  have hlocal := IsLocalization.map_under M Seeds (RingHom.ker (genericSeedMap C₀))
  change ((RingHom.ker (genericSeedMap C₀)).comap baseChange).map baseChange =
    RingHom.ker (genericSeedMap C₀) at hlocal
  rw [← hlocal, hk, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  change Ideal.span {baseChange (exchangeX (Polynomial.C C₀))} = seedEquation C₀
  rw [exchange_constant]
  simp only [baseChange, seedEquation, MvPolynomial.map_map]

attribute [local instance] Polynomial.algebra in
/-- A common coefficient denominator gives a fraction over the polynomial ring of the base. -/
private theorem polynomial_fractions (R F E : Type*) [CommRing R] [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra F[X] E] [IsFractionRing F[X] E]
    (z : E) :
    ∃ a b : R[X],
      z = algebraMap F[X] E (a.map (algebraMap R F)) /
        algebraMap F[X] E (b.map (algebraMap R F)) := by
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  let : IsLocalization M F[X] := Polynomial.isLocalization (nonZeroDivisors R) F
  obtain ⟨r, s, -, hz⟩ := IsFractionRing.div_surjective F[X] z
  obtain ⟨a, b, d, ha, hb⟩ := IsLocalization.surj₂ M F[X] r s
  let j := algebraMap F[X] E
  let t := algebraMap R[X] F[X] (d : R[X])
  have ht : j t ≠ 0 := ((IsLocalization.map_units F[X] d).map j).ne_zero
  have ha' : j r * j t = j (a.map (algebraMap R F)) := by
    rw [← map_mul]
    exact congrArg j ha
  have hb' : j s * j t = j (b.map (algebraMap R F)) := by
    rw [← map_mul]
    exact congrArg j hb
  refine ⟨a, b, ?_⟩
  rw [← ha', ← hb', mul_div_mul_right _ _ ht]
  exact hz.symm

/-- A field generated by fractions of the image is a fraction field of the kernel quotient. -/
private theorem quotient_isFractionRing {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) (I : Ideal R) (h : RingHom.ker f = I)
    (hfractions : ∀ z : F, ∃ a b : R, z = f a / f b) :
    letI : Algebra (R ⧸ I) F :=
      (Ideal.Quotient.lift I f fun _ hr => RingHom.mem_ker.mp (h.symm ▸ hr)).toAlgebra
    IsFractionRing (R ⧸ I) F := by
  let φ := Ideal.Quotient.lift I f fun _ hr => RingHom.mem_ker.mp (h.symm ▸ hr)
  let : Algebra (R ⧸ I) F := φ.toAlgebra
  have hinj : Function.Injective φ := RingHom.lift_injective_of_ker_le_ideal I _ h.le
  let : FaithfulSMul (R ⧸ I) F :=
    (faithfulSMul_iff_algebraMap_injective (R ⧸ I) F).mpr hinj
  change IsFractionRing (R ⧸ I) F
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hz⟩ := hfractions z
  exact ⟨Ideal.Quotient.mk I a, Ideal.Quotient.mk I b, hz⟩

/-- The constant seed curve over the independent abscissa has function field L(C₀)(X). -/
theorem proof : K1_14_2_4_1_1.c1 := by
  intro C₀ hC
  let k := generic_kernel C₀
  refine ⟨k, quotient_isFractionRing (genericSeedMap C₀) (seedEquation C₀) k ?_⟩
  intro z
  obtain ⟨a, b, hz⟩ := polynomial_fractions (ConstantSeedRing C₀) (ConstantSeedField C₀)
    (ConstantSeedX C₀) z
  have hsurj : Function.Surjective (quotientPolynomial C₀) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  refine ⟨baseChange (exchangeX a'), baseChange (exchangeX b'), ?_⟩
  change z = ((genericSeedMap C₀).comp (baseChange.comp exchangeX.toRingHom)) a' /
    ((genericSeedMap C₀).comp (baseChange.comp exchangeX.toRingHom)) b'
  rw [generic_comp]
  exact hz

end
end K1_14_2_4_1_1_1
end PackSource_K1_14_2_4_1_1_1Proof

section PackSource_K1_14_2_2_2_6_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K1_14_2_2_2_6_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_3 K1_14_2_2_2_6 Polynomial
open scoped Polynomial

private abbrev mixedIdeal (I : Ideal Ambient) :=
  I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}

private abbrev FieldOf (I : Ideal Ambient) [I.IsPrime] :=
  FractionRing (Double (Surface I))

private abbrev embed (I : Ideal Ambient) [I.IsPrime] :
    Double (Surface I) →+* FieldOf I := algebraMap _ _

private def coefficients (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) : SectionField →+* FieldOf I :=
  IsFractionRing.lift (g := (embed I).comp (rawParameters I))
    ((IsFractionRing.injective (Double (Surface I)) (FieldOf I)).comp h)

private theorem coefficients_apply (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) (d : Params) :
    coefficients I h (algebraMap Params SectionField d) = embed I (rawParameters I d) :=
  IsFractionRing.lift_algebraMap _ d

private def evalInField (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) : SectionAmbient →+* FieldOf I :=
  MvPolynomial.eval₂Hom (coefficients I h) (fun i => embed I (coords I i))

private theorem evalInField_base (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) :
    (evalInField I h).comp sectionBase =
      ((embed I).comp (Polynomial.C.comp Polynomial.C)).comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have ha : algebraMap FX SectionField a = algebraMap Params SectionField (MvPolynomial.C a) := rfl
    simp only [RingHom.comp_apply, evalInField, sectionBase, MvPolynomial.map_C,
      MvPolynomial.eval₂Hom_C, ha, coefficients_apply, rawParameters]
    rfl
  · intro i
    simp [evalInField, sectionBase, RingHom.comp_apply]

private def mixedToField (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) : OverMixed I →+* FieldOf I :=
  Ideal.Quotient.lift (mixedIdeal I) (evalInField I h) <| by
    change mixedIdeal I ≤ RingHom.ker (evalInField I h)
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro a ha
      change ((evalInField I h).comp sectionBase) a = 0
      simp [evalInField_base, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · intro a ha
      rcases (show a = sectionSeedLine ∨ a = sectionJetLine by simpa using ha) with rfl | rfl
      all_goals
        simp [RingHom.mem_ker, sectionSeedLine, sectionJetLine, evalInField,
          sliceParameter, coefficients_apply, rawParameters, coords]
      all_goals ring

private theorem mixed_scalar (I : Ideal Ambient) (a : SectionField) :
    Ideal.Quotient.mk (mixedIdeal I) (MvPolynomial.C a) = algebraMap SectionField (OverMixed I) a := by
  simpa only [MvPolynomial.algebraMap_eq] using
    (Ideal.Quotient.mk_algebraMap (R₁ := SectionField) (mixedIdeal I) a)

private def seedEval (I : Ideal Ambient) : SectionField[X] →ₐ[SectionField] OverMixed I :=
  Polynomial.aeval (Ideal.Quotient.mk (mixedIdeal I) (MvPolynomial.X 1))

private theorem seedEval_restriction (I : Ideal Ambient) (f : Seeds)
    (hf : f ∈ seedImage I) : seedEval I (mixedSeedRestriction f) = 0 := by
  let π := Ideal.Quotient.mk (mixedIdeal I)
  have hline : π sectionSeedLine = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {sectionSeedLine, sectionJetLine} ≤ mixedIdeal I from le_sup_right)
        (Ideal.subset_span (by simp)))
  have hcoord : π (MvPolynomial.X 0) =
      algebraMap SectionField (OverMixed I) (sliceParameter 2) -
        algebraMap SectionField (OverMixed I) (sliceParameter 0) * π (MvPolynomial.X 1) := by
    apply eq_sub_of_add_eq
    apply sub_eq_zero.mp
    simpa only [sectionSeedLine, map_sub, map_add, map_mul, π, mixed_scalar] using hline
  have he : (seedEval I).toRingHom.comp (MvPolynomial.eval₂Hom
      (Polynomial.C.comp (algebraMap FX SectionField))
      (K1_14_2_3_1.lineValues (sliceParameter 0) (sliceParameter 2))) =
        (π.comp sectionBase).comp K1_14_2_2_2_6_1.seedIncl := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, sectionBase, seedEval, rootIncl, rootSeeds, mixed_scalar, π]
    · intro i
      fin_cases i
      · simpa [RingHom.comp_apply, sectionBase, seedEval, rootIncl, rootSeeds,
          K1_14_2_3_1.lineValues] using hcoord.symm
      · simp [RingHom.comp_apply, sectionBase, seedEval, rootIncl, rootSeeds,
          K1_14_2_3_1.lineValues, π]
  rw [restriction_eval]
  exact (RingHom.congr_fun he f).trans (Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show I.map sectionBase ≤ mixedIdeal I from le_sup_left)
      (Ideal.mem_map_of_mem sectionBase (show K1_14_2_2_2_6_1.seedIncl f ∈ I from hf))))

private theorem seedEval_toField (I : Ideal Ambient) [I.IsPrime]
    (h : Function.Injective (rawParameters I)) :
    (mixedToField I h).comp (seedEval I).toRingHom =
      Polynomial.eval₂RingHom (coefficients I h) (embed I (coords I 1)) := by
  apply Polynomial.ringHom_ext
  · intro a
    change mixedToField I h (seedEval I (Polynomial.C a)) = _
    have ha : seedEval I (Polynomial.C a) = algebraMap SectionField (OverMixed I) a := by
      simp [seedEval]
    rw [ha, ← mixed_scalar I a]
    simp [mixedToField, evalInField]
  · simp [mixedToField, evalInField, seedEval, RingHom.comp_apply]

/-- The mixed section contains the scheme-theoretic generic seed-line section. -/
theorem proof : K1_14_2_2_2_6.c1 := by
  intro I hI hdim _ f hf hgen
  let : I.IsPrime := hI
  have hparam := rawParameters_injective I hdim f hf hgen
  have hzF : seedEval I (mixedSeedRestriction f) = 0 :=
    seedEval_restriction I f (hgen.symm ▸ Ideal.mem_span_singleton_self f)
  let P : Ideal SectionField[X] := Ideal.span {mixedSeedRestriction f}
  let e := Ideal.Quotient.liftₐ P (seedEval I) (by
    intro p hp
    exact (Ideal.span_le.mpr (by simpa [RingHom.mem_ker] using hzF) :
      P ≤ RingHom.ker (seedEval I).toRingHom) hp)
  refine ⟨e, (injective_iff_map_eq_zero e).mpr ?_⟩
  intro z hz
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hz' : seedEval I q = 0 := hz
  have hzero : q.eval₂ (coefficients I hparam) (embed I (coords I 1)) = 0 := calc
    _ = mixedToField I hparam (seedEval I q) :=
      (RingHom.congr_fun (seedEval_toField I hparam) q).symm
    _ = 0 := by rw [hz', map_zero]
  let n := IsLocalization.integerNormalization (nonZeroDivisors Params) q
  have hnorm := IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors Params)
    (coefficients I hparam) q hzero
  have hraw : rawEval I n = 0 := by
    apply (IsFractionRing.injective (Double (Surface I)) (FieldOf I))
    rw [map_zero]
    have hcomp : (embed I).comp (rawEval I) =
        Polynomial.eval₂RingHom ((coefficients I hparam).comp (algebraMap Params SectionField))
          (embed I (coords I 1)) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [RingHom.comp_apply, rawEval, coefficients_apply]
      · simp [RingHom.comp_apply, rawEval]
    exact (RingHom.congr_fun hcomp n).trans hnorm
  have hdiv := map_dvd (Polynomial.mapRingHom (algebraMap Params SectionField))
    ((rawEval_eq_zero_iff I hdim f hf hgen n).mp hraw)
  change (integralRestriction f).map (algebraMap Params SectionField) ∣
    n.map (algebraMap Params SectionField) at hdiv
  obtain ⟨d, hd, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors Params) q
  change n.map (algebraMap Params SectionField) = d • q at he
  rw [restriction_map, he, Algebra.smul_def, IsScalarTower.algebraMap_apply Params SectionField,
    Polynomial.algebraMap_eq] at hdiv
  have hdunit : IsUnit (algebraMap Params SectionField d) := isUnit_iff_ne_zero.mpr (by
    simpa using (IsFractionRing.injective Params SectionField).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp hd))
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ((hdunit.map Polynomial.C).dvd_mul_left.mp hdiv))

end
end K1_14_2_2_2_6_1
end PackSource_K1_14_2_2_2_6_1Proof

section PackSource_K1_14_2_2_3_2Aux2
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_2_3_2

noncomputable section

open Polynomial
open scoped BigOperators Polynomial

private theorem fin_two_sum (e : Fin 2 →₀ ℕ) : e.sum (fun _ m => m) = e 0 + e 1 := by
  simp [Finsupp.sum_of_support_subset e (Finset.subset_univ e.support)]

def integralRestriction {F : Type} [Field F] :
    MvPolynomial (Fin 2) F →+* (MvPolynomial (Fin 2) F)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.C : F →+* MvPolynomial (Fin 2) F))
    (K1_14_2_3_1.lineValues (R := MvPolynomial (Fin 2) F) (MvPolynomial.X 0) (MvPolynomial.X 1))

private theorem lineValue_natDegree {R : Type} [CommRing R] (s t : R) :
    (K1_14_2_3_1.lineValues s t 0).natDegree ≤ 1 := by
  change (Polynomial.C t - Polynomial.C s * (Polynomial.X : R[X])).natDegree ≤ 1
  have hs : (Polynomial.C s * (Polynomial.X : R[X])).natDegree ≤ 1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le s 1
  exact (natDegree_sub_le _ _).trans (max_le (by simp) hs)

private theorem coeff_integralRestriction_monomial {F : Type} [Field F]
    (e : Fin 2 →₀ ℕ) (a : F) (d : ℕ)
    (he : e 0 + e 1 ≤ d) :
    (integralRestriction (MvPolynomial.monomial e a)).coeff d =
      if e 0 + e 1 = d then MvPolynomial.C a * (-MvPolynomial.X 0) ^ e 0 else 0 := by
  let q : (MvPolynomial (Fin 2) F)[X] :=
    K1_14_2_3_1.lineValues (R := MvPolynomial (Fin 2) F) (MvPolynomial.X 0) (MvPolynomial.X 1) 0
  have hq : q.natDegree ≤ 1 := lineValue_natDegree _ _
  have hcoeff : q.coeff 1 = -(MvPolynomial.X 0 : MvPolynomial (Fin 2) F) := by simp [q, K1_14_2_3_1.lineValues, coeff_sub]
  have hpow : (q ^ e 0).natDegree ≤ e 0 := by simpa using natDegree_pow_le_of_le (e 0) hq
  have hXpow : ((Polynomial.X : (MvPolynomial (Fin 2) F)[X]) ^ e 1).natDegree ≤ e 1 := by simp
  have hqpow : (q ^ e 0).coeff (e 0) = (-(MvPolynomial.X 0 : MvPolynomial (Fin 2) F)) ^ e 0 := by
    simpa [hcoeff] using (coeff_pow_of_natDegree_le (m := e 0) hq)
  rw [MvPolynomial.monomial_fin_two, map_mul, map_mul, map_pow, map_pow]
  simp only [integralRestriction, K1_14_2_3_1.lineValues, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((Polynomial.C (MvPolynomial.C a) * q ^ e 0) * Polynomial.X ^ e 1).coeff d = _
  rw [mul_assoc, coeff_C_mul]
  split_ifs with heq
  · rw [← heq, coeff_mul_add_eq_of_natDegree_le hpow hXpow, hqpow, coeff_X_pow_self]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
    exact (natDegree_mul_le_of_le hpow hXpow).trans_lt (lt_of_le_of_ne he heq)

/-- At the total degree the monomials of a plane equation give distinct
powers of the independent slope. -/
theorem coeff_line_totalDegree_ne_zero {F : Type} [Field F]
    {g : MvPolynomial (Fin 2) F} (hg : g ≠ 0) :
    (integralRestriction g).coeff g.totalDegree ≠ 0 := by
  classical
  let d := g.totalDegree
  obtain ⟨e, he, hde⟩ := Finset.exists_mem_eq_sup g.support
    (MvPolynomial.support_nonempty.mpr hg) (fun e => e.sum (fun _ m => m))
  change d = e.sum (fun _ m => m) at hde
  rw [fin_two_sum] at hde
  have hh (e' : Fin 2 →₀ ℕ) (he' : e' ∈ g.support) : e' 0 + e' 1 ≤ d := by
    rw [← fin_two_sum]
    exact MvPolynomial.le_totalDegree he'
  have hexp :
      (integralRestriction g).coeff d =
        ∑ e' ∈ g.support with e' 0 + e' 1 = d,
          MvPolynomial.C (g.coeff e') * (-MvPolynomial.X 0) ^ e' 0 := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, finsetSum_coeff, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun e' he' =>
      coeff_integralRestriction_monomial e' (g.coeff e') d (hh e' he'))
  have hcoef (a : F) (k m : ℕ) :
      (MvPolynomial.C a * (-(MvPolynomial.X 0 : (MvPolynomial (Fin 2) F))) ^ k).coeff (Finsupp.single 0 m)
        = if k = m then a * (-1)^k else 0 := by
    have hneg : (MvPolynomial.C (-1 : F) : (MvPolynomial (Fin 2) F)) = -1 :=
      (map_neg (MvPolynomial.C : F →+* (MvPolynomial (Fin 2) F)) 1).trans
        (congrArg Neg.neg (map_one (MvPolynomial.C : F →+* (MvPolynomial (Fin 2) F))))
    have hn : -(MvPolynomial.X 0 : (MvPolynomial (Fin 2) F)) = MvPolynomial.C (-1 : F) * MvPolynomial.X 0 :=
      (neg_one_mul (MvPolynomial.X 0 : (MvPolynomial (Fin 2) F))).symm.trans
        (congrArg (fun z => z * (MvPolynomial.X 0 : (MvPolynomial (Fin 2) F))) hneg.symm)
    rw [hn, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    by_cases hk : k = m
    · simp [hk]
    · have hs : Finsupp.single (0 : Fin 2) k ≠ Finsupp.single 0 m := by
        intro h
        exact hk (by simpa using DFunLike.congr_fun h 0)
      simp [hk, hs]
  intro ht
  have hz := congrArg (fun f : (MvPolynomial (Fin 2) F) => f.coeff (Finsupp.single 0 (e 0))) ht
  rw [hexp] at hz
  simp only [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, hcoef] at hz
  rw [Finset.sum_eq_single e] at hz
  · have hz' : g.coeff e * (-1 : F) ^ e 0 = 0 := by simpa using hz
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp he)
      (pow_ne_zero (e 0) (neg_ne_zero.mpr one_ne_zero))) hz'
  · intro e' he' hne
    have hdiff : e' 0 ≠ e 0 := by
      intro h0
      have h1 : e' 1 = e 1 := by
        have := (Finset.mem_filter.mp he').2
        omega
      exact hne (Finsupp.ext (by intro i; fin_cases i <;> assumption))
    simp [hdiff]
  · exact fun h => False.elim (h (Finset.mem_filter.mpr ⟨he, hde.symm⟩))

end
end K1_14_2_2_3_2
end PackSource_K1_14_2_2_3_2Aux2

section PackSource_K1_14_2_4_1_1_2Plane
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_4_1_1_2

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3_1 K1_14_2_4_1 K1_14_2_4_1_1
open scoped Polynomial

local instance (I : Ideal Seeds) : CommRing (CoordinateRing I)[X] :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)

private theorem plane_denominator (I : Ideal Seeds) (x : PlaneSlice I) :
    ∃ (q : (CoordinateRing I)[X]) (d : Seeds), d ∈ nonZeroDivisors Seeds ∧
      x * algebraMap SeedField (PlaneSlice I) (algebraMap Seeds SeedField d) =
        slopeToSlice I 0 1 q := by
  let : Algebra (MvPolynomial (Fin 2) Seeds) (Over 2) := MvPolynomial.algebraMvPolynomial
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj
    (M := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin 2))) f
  obtain ⟨d, hd, hdm⟩ := m.property
  let lift : MvPolynomial (Fin 2) Seeds →+* (CoordinateRing I)[X] :=
    MvPolynomial.eval₂Hom (parameterMap I 0 1) (fun k => Polynomial.C (coord I k))
  have hcomp : (slopeToSlice I 0 1).comp lift =
      (Ideal.Quotient.mk (sectionIdeal I 0 1)).comp
        (MvPolynomial.map (algebraMap Seeds SeedField)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact RingHom.congr_fun (parameter_commutes I 0 1) a
    · intro k
      simp [lift, slopeToSlice, toSlice, RingHom.comp_apply]
  have hgm' : f * MvPolynomial.C (algebraMap Seeds SeedField d) =
      MvPolynomial.map (algebraMap Seeds SeedField) g := by
    simpa only [MvPolynomial.algebraMap_def, ← hdm, MvPolynomial.map_C] using hgm
  refine ⟨lift g, d, hd, ?_⟩
  calc
    _ = Ideal.Quotient.mk (sectionIdeal I 0 1) (f * MvPolynomial.C (algebraMap Seeds SeedField d)) :=
      (map_mul _ _ _).symm
    _ = _ := (congrArg (Ideal.Quotient.mk (sectionIdeal I 0 1)) hgm').trans
      (RingHom.congr_fun hcomp g).symm

/-- Clearing the parameter denominators reduces the domain assertion to the
coordinate ring of the seed curve with an independent slope. -/
private theorem plane_domain (I : Ideal Seeds) [I.IsPrime] [Nontrivial (PlaneSlice I)] :
    IsDomain (PlaneSlice I) := by
  let : IsDomain (CoordinateRing I) := Ideal.Quotient.isDomain I
  let scale : Seeds →+* PlaneSlice I :=
    (algebraMap SeedField (PlaneSlice I)).comp (algebraMap Seeds SeedField)
  have numerator_ne (x : PlaneSlice I) (hx : x ≠ 0) (q : (CoordinateRing I)[X]) (d : Seeds)
      (hd : d ∈ nonZeroDivisors Seeds) (he : x * scale d = slopeToSlice I 0 1 q) :
      q ≠ 0 := by
    intro hq
    rw [hq, map_zero] at he
    have hd' : algebraMap Seeds SeedField d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hd)
    have hu : IsUnit (scale d) :=
      ((isUnit_iff_ne_zero.mpr hd').map (algebraMap SeedField (PlaneSlice I)))
    exact hx (hu.mul_right_cancel (he.trans (zero_mul _).symm))
  let : NoZeroDivisors (PlaneSlice I) := ⟨by
    intro x y h
    by_contra! hne
    obtain ⟨q, d, hd, hq⟩ := plane_denominator I x
    obtain ⟨r, e, he, hr⟩ := plane_denominator I y
    have hprod : slopeToSlice I 0 1 (q * r) = 0 := by
      calc
        _ = (x * scale d) * (y * scale e) := by
          rw [map_mul, ← hq, ← hr]
          rfl
        _ = (x * y) * (scale d * scale e) := mul_mul_mul_comm x (scale d) y (scale e)
        _ = 0 := by rw [h, zero_mul]
    exact (mul_ne_zero (numerator_ne x hne.1 q d hd hq) (numerator_ne y hne.2 r e he hr))
      ((injective_iff_map_eq_zero _).mp (slope_injective I 0 1) _ hprod)⟩
  exact NoZeroDivisors.to_isDomain _

theorem plane_field (C₀ : ConstantSeeds) [h : Fact (Irreducible C₀)] (hC : SeedLocalization C₀) :
    IsField (PlaneSlice (seedEquation C₀)) := by
  have hpos : 0 < Module.finrank SeedField (PlaneSlice (seedEquation C₀)) := by
    rw [seed_section_rank]
    exact seed_degree_pos C₀ h.out
  let : (seedEquation C₀).IsPrime := hC.kernel ▸ RingHom.ker_isPrime (genericSeedMap C₀)
  let : Nontrivial (PlaneSlice (seedEquation C₀)) := Module.nontrivial_of_finrank_pos hpos
  let : IsDomain (PlaneSlice (seedEquation C₀)) := plane_domain (seedEquation C₀)
  let : Module.Finite SeedField (PlaneSlice (seedEquation C₀)) := Module.finite_of_finrank_pos hpos
  exact isField_of_isIntegral_of_isField' (S := PlaneSlice (seedEquation C₀))
    (Field.toIsField SeedField)

theorem toPlane_injective (I : Ideal Seeds) [I.IsPrime] [Nontrivial (PlaneSlice I)] :
    Function.Injective (toSlice I 0 1) := by
  intro a b hab
  apply Polynomial.C_injective
  apply slope_injective I 0 1
  simpa [slopeToSlice] using hab

end
end K1_14_2_4_1_1_2
end PackSource_K1_14_2_4_1_1_2Plane

section PackSource_K1_14_2_2_3_2Aux3
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_2_3_2

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 Polynomial
open scoped Polynomial

private abbrev JetParams (I : Ideal Ambient) :=
  Polynomial (MvPolynomial (Fin 2) (JetImageField I))

private abbrev MixedField (I : Ideal Ambient) := FractionRing (JetParams I)

private def jetVal (I : Ideal Ambient) (i : Fin 2) : JetImageField I :=
  jetImageMap I (MvPolynomial.X i)

private def paramOrder : Fin 4 ≃ Fin 4 where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def coefficientParams (I : Ideal Ambient) :
    MvPolynomial (Fin 3) FX →+* JetParams I :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (MvPolynomial.C.comp ((jetImageMap I).comp MvPolynomial.C)))
    ![Polynomial.C (MvPolynomial.C (jetVal I 0)) +
        Polynomial.X * Polynomial.C (MvPolynomial.C (jetVal I 1)),
      Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1)]

private theorem coefficientParams_injective_at_zero {I : Ideal Ambient} (hI : Active I)
    [(I.comap jetInclude).IsPrime] :
    Function.Injective (constantCoeff.comp (coefficientParams I)) := by
  let a : FX[X] →+* JetImageField I :=
    (algebraMap (JetImageRing I) (JetImageField I)).comp (ordinateInImage I).toRingHom
  have ha : Function.Injective a :=
    (IsFractionRing.injective (JetImageRing I) (JetImageField I)).comp (ordinateInImage_injective hI)
  have aC (c : FX) : a (Polynomial.C c) = jetImageMap I (MvPolynomial.C c) := by
    change (algebraMap (JetImageRing I) (JetImageField I)) (ordinateInImage I (Polynomial.C c)) = _
    rw [ordinateInImage, Polynomial.aeval_C]
    rfl
  have aX : a Polynomial.X = jetVal I 0 := by
    change (algebraMap (JetImageRing I) (JetImageField I)) (ordinateInImage I Polynomial.X) = _
    rw [ordinateInImage, Polynomial.aeval_X]
    rfl
  let b := (MvPolynomial.renameEquiv FX (finSuccEquiv 2)).trans
    (MvPolynomial.optionEquivRight FX (Fin 2))
  have he : constantCoeff.comp (coefficientParams I) =
      (MvPolynomial.map a).comp b.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change constantCoeff (coefficientParams I (MvPolynomial.C c)) =
        MvPolynomial.map a (b (MvPolynomial.C c))
      simp only [coefficientParams, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        constantCoeff_apply, coeff_C_zero, b, AlgEquiv.trans_apply,
        MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C,
        MvPolynomial.optionEquivRight_C, MvPolynomial.map_C, aC]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change constantCoeff (coefficientParams I (MvPolynomial.X 0)) =
          MvPolynomial.map a (b (MvPolynomial.X 0))
        simp only [coefficientParams, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
          constantCoeff_apply, coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, zero_mul,
          add_zero, b, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
          finSuccEquiv_zero, MvPolynomial.optionEquivRight_X_none, MvPolynomial.map_C, aX]
      · change constantCoeff (coefficientParams I (MvPolynomial.X j.succ)) =
          MvPolynomial.map a (b (MvPolynomial.X j.succ))
        simp only [coefficientParams, MvPolynomial.eval₂Hom_X', b, AlgEquiv.trans_apply,
          MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, finSuccEquiv_succ,
          MvPolynomial.optionEquivRight_X_some, MvPolynomial.map_X]
        fin_cases j <;> simp
  rw [he]
  exact (MvPolynomial.map_injective _ ha).comp b.injective

private theorem eval_X_injective_of_constantCoeff {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] (f : A →+* B[X]) (hf : Function.Injective (constantCoeff.comp f)) :
    Function.Injective (eval₂RingHom f Polynomial.X) := by
  let e := eval₂RingHom f Polynomial.X
  have he : constantCoeff.comp e = (constantCoeff.comp f).comp constantCoeff := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [e]
    · simp [e]
  apply (RingHom.injective_iff_ker_eq_bot e).2
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro q
  induction q using Polynomial.recOnHorner with
  | M0 => simp
  | MC q a hq ha _ =>
    intro hz
    have hc := RingHom.congr_fun he (q + Polynomial.C a)
    change constantCoeff (e (q + Polynomial.C a)) = (constantCoeff.comp f) ((q + Polynomial.C a).coeff 0) at hc
    rw [hz, map_zero, coeff_add, hq, coeff_C_zero, zero_add] at hc
    exact (ha (hf (hc.symm.trans (map_zero _).symm))).elim
  | MX q _ ih =>
    intro hz
    have hX : e Polynomial.X = Polynomial.X := by simp [e]
    rw [map_mul, hX] at hz
    rw [ih ((mul_eq_zero.mp hz).resolve_right X_ne_zero), zero_mul]

private def sectionParams (I : Ideal Ambient) :
    MvPolynomial (Fin 4) FX →+* JetParams I :=
  (eval₂RingHom (coefficientParams I) Polynomial.X).comp
    ((MvPolynomial.finSuccEquiv FX 3).toRingHom.comp (MvPolynomial.renameEquiv FX paramOrder).toRingHom)

private theorem sectionParams_injective {I : Ideal Ambient} (hI : Active I)
    [(I.comap jetInclude).IsPrime] : Function.Injective (sectionParams I) :=
  (eval_X_injective_of_constantCoeff _ (coefficientParams_injective_at_zero hI)).comp
    ((MvPolynomial.finSuccEquiv FX 3).injective.comp (MvPolynomial.renameEquiv FX paramOrder).injective)

private def sectionCoeff {I : Ideal Ambient} (hI : Active I)
    [(I.comap jetInclude).IsPrime] : SectionField →+* MixedField I :=
  IsFractionRing.lift (K := SectionField)
    (g := (algebraMap (JetParams I) (MixedField I)).comp (sectionParams I))
    ((IsFractionRing.injective (JetParams I) (MixedField I)).comp (sectionParams_injective hI))

private def seedCoeff (I : Ideal Ambient) :
    MvPolynomial (Fin 2) (JetImageField I) →+* MixedField I :=
  (algebraMap (JetParams I) (MixedField I)).comp Polynomial.C

private theorem sectionCoeff_C {I : Ideal Ambient} (hI : Active I)
    [(I.comap jetInclude).IsPrime] (c : FX) :
    sectionCoeff hI (algebraMap FX SectionField c) =
      seedCoeff I (MvPolynomial.C (jetImageMap I (MvPolynomial.C c))) := by
  rw [IsScalarTower.algebraMap_apply FX (MvPolynomial (Fin 4) FX) SectionField]
  simp [sectionCoeff, sectionParams, coefficientParams, seedCoeff, MvPolynomial.finSuccEquiv_apply]

private theorem sectionParams_X (I : Ideal Ambient) (i : Fin 4) :
    sectionParams I (MvPolynomial.X i) =
      ![Polynomial.C (MvPolynomial.X 0), Polynomial.X, Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.C (jetVal I 0)) +
          Polynomial.X * Polynomial.C (MvPolynomial.C (jetVal I 1))] i := by
  change eval₂RingHom (coefficientParams I) Polynomial.X
    (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.renameEquiv FX paramOrder (MvPolynomial.X i))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  fin_cases i
  · change eval₂RingHom (coefficientParams I) Polynomial.X
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.X (1 : Fin 3).succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [coefficientParams]
  · change eval₂RingHom (coefficientParams I) Polynomial.X
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.X 0)) = _
    rw [MvPolynomial.finSuccEquiv_X_zero]
    simp
  · change eval₂RingHom (coefficientParams I) Polynomial.X
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.X (2 : Fin 3).succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [coefficientParams]
  · change eval₂RingHom (coefficientParams I) Polynomial.X
      (MvPolynomial.finSuccEquiv FX 3 (MvPolynomial.X (0 : Fin 3).succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [coefficientParams]

private theorem sectionCoeff_params {I : Ideal Ambient} (hI : Active I)
    [(I.comap jetInclude).IsPrime] (i : Fin 4) :
    sectionCoeff hI (sliceParameter i) =
      ![seedCoeff I (MvPolynomial.X 0), algebraMap (JetParams I) (MixedField I) Polynomial.X,
        seedCoeff I (MvPolynomial.X 1),
        seedCoeff I (MvPolynomial.C (jetVal I 0)) + algebraMap (JetParams I) (MixedField I) Polynomial.X *
          seedCoeff I (MvPolynomial.C (jetVal I 1))] i := by
  unfold sectionCoeff sliceParameter
  rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply, sectionParams_X]
  fin_cases i <;> simp [seedCoeff, RingHom.comp_apply]
  exact mul_comm _ _

set_option maxHeartbeats 2000000 in
theorem degree_le_mixed {I : Ideal Ambient} (hI : Active I)
    (g : MvPolynomial (Fin 2) (JetImageField I)) (hg : g ≠ 0)
    (hIg : I.map (imageFibreMap I) = Ideal.span {g}) :
    g.totalDegree ≤ Module.finrank SectionField (OverMixed I) := by
  classical
  let : I.IsPrime := hI.prime
  let : (I.comap jetInclude).IsPrime := Ideal.comap_isPrime jetInclude I
  let : Module.Finite SectionField (OverMixed I) := hI.mixed_finite
  let L := MixedField I
  let b := seedCoeff I
  let s := sectionCoeff hI
  let T := (Polynomial.mapRingHom b).comp integralRestriction
  let q := T g
  let V := AdjoinRoot q
  let e : SectionAmbient →+* L[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp s)
      ![Polynomial.C (b (MvPolynomial.X 1)) - Polynomial.C (b (MvPolynomial.X 0)) * Polynomial.X,
        Polynomial.X, Polynomial.C (b (MvPolynomial.C (jetVal I 0))),
        Polynomial.C (b (MvPolynomial.C (jetVal I 1)))]
  have heC (c : SectionField) : e (MvPolynomial.C c) = Polynomial.C (s c) := by
    simp only [e, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    rfl
  have hTC (c : JetImageField I) : T (MvPolynomial.C c) = Polynomial.C (b (MvPolynomial.C c)) := by
    change (integralRestriction (MvPolynomial.C c)).map b = _
    simp [integralRestriction]
  have hTX (j : Fin 2) : T (MvPolynomial.X j) =
      (K1_14_2_3_1.lineValues (R := MvPolynomial (Fin 2) (JetImageField I))
        (MvPolynomial.X 0) (MvPolynomial.X 1) j).map b := by
    change (integralRestriction (MvPolynomial.X j)).map b = _
    rw [integralRestriction, MvPolynomial.eval₂Hom_X']
  have hcomm : e.comp sectionBase = T.comp (imageFibreMap I) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change e (MvPolynomial.map _ (MvPolynomial.C c)) =
        T (specializeJets (jetImageMap I) (MvPolynomial.C c))
      rw [MvPolynomial.map_C, specialize_C, hTC, heC]
      exact congrArg Polynomial.C (sectionCoeff_C hI c)
    · intro i
      obtain ⟨j | j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
      · rw [finSumFinEquiv_apply_left]
        change e (MvPolynomial.map _ (MvPolynomial.X (Fin.castAdd 2 j))) =
          T (specializeJets (jetImageMap I) (MvPolynomial.X (Fin.castAdd 2 j)))
        rw [MvPolynomial.map_X, specialize_seed_var, hTX]
        fin_cases j <;> simp [e, K1_14_2_3_1.lineValues]
      · rw [finSumFinEquiv_apply_right]
        change e (MvPolynomial.map _ (MvPolynomial.X (Fin.natAdd 2 j))) =
          T (specializeJets (jetImageMap I) (MvPolynomial.X (Fin.natAdd 2 j)))
        rw [MvPolynomial.map_X, specialize_jet_var, hTC]
        fin_cases j <;> simp [e, jetVal] <;> rfl
  have hs0 : s (sliceParameter 0) = b (MvPolynomial.X 0) := sectionCoeff_params hI 0
  have hs2 : s (sliceParameter 2) = b (MvPolynomial.X 1) := sectionCoeff_params hI 2
  have hs1 : s (sliceParameter 1) = algebraMap (JetParams I) L Polynomial.X :=
    sectionCoeff_params hI 1
  have hs3 : s (sliceParameter 3) = b (MvPolynomial.C (jetVal I 0)) +
      algebraMap (JetParams I) L Polynomial.X * b (MvPolynomial.C (jetVal I 1)) :=
    sectionCoeff_params hI 3
  have hseed : e sectionSeedLine = 0 := by
    simp only [sectionSeedLine, map_sub, map_add, map_mul, heC, hs0, hs2]
    simp [e]
  have hjet : e sectionJetLine = 0 := by
    have hy : e (MvPolynomial.X 2) = Polynomial.C (b (MvPolynomial.C (jetVal I 0))) := by
      simp [e]
      rfl
    have hv : e (MvPolynomial.X 3) = Polynomial.C (b (MvPolynomial.C (jetVal I 1))) := by
      simp [e]
      rfl
    rw [sectionJetLine, map_sub e, map_add e, map_mul e, heC (sliceParameter 1),
      heC (sliceParameter 3), hs1, hs3, hy, hv, Polynomial.C_add, Polynomial.C_mul, sub_self]
  let H := I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}
  let v : SectionAmbient →+* V := (AdjoinRoot.mk q).comp e
  have hker : H ≤ RingHom.ker v := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro f hf
      have hm := Ideal.mem_map_of_mem (imageFibreMap I) hf
      rw [hIg, Ideal.mem_span_singleton] at hm
      apply RingHom.mem_ker.mpr
      change AdjoinRoot.mk q ((e.comp sectionBase) f) = 0
      rw [hcomm]
      exact AdjoinRoot.mk_eq_zero.mpr (map_dvd T hm)
    · intro f hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · apply RingHom.mem_ker.mpr
        change AdjoinRoot.mk q (e sectionSeedLine) = 0
        rw [hseed, map_zero]
      · apply RingHom.mem_ker.mpr
        change AdjoinRoot.mk q (e sectionJetLine) = 0
        rw [hjet, map_zero]
  let F : OverMixed I →+* V := Ideal.Quotient.lift H v fun _ hf => RingHom.mem_ker.mp (hker hf)
  let x : OverMixed I := Ideal.Quotient.mk H (MvPolynomial.X 1)
  have hx : F x = AdjoinRoot.root q := by
    change Ideal.Quotient.lift H v _ (Ideal.Quotient.mk H (MvPolynomial.X 1)) = _
    rw [Ideal.Quotient.lift_mk]
    change AdjoinRoot.mk q (e (MvPolynomial.X 1)) = _
    rw [show e (MvPolynomial.X 1) = Polynomial.X by simp [e], AdjoinRoot.mk_X]
  have hc (c : SectionField) : F (algebraMap SectionField (OverMixed I) c) =
      algebraMap L V (s c) := by
    change Ideal.Quotient.lift H v _ (Ideal.Quotient.mk H (MvPolynomial.C c)) = _
    rw [Ideal.Quotient.lift_mk]
    change AdjoinRoot.mk q (e (MvPolynomial.C c)) = _
    rw [heC]
    exact AdjoinRoot.mk_C (s c)
  have hcoeff : q.coeff g.totalDegree ≠ 0 := by
    change ((integralRestriction g).map b).coeff _ ≠ 0
    rw [coeff_map]
    exact fun h => coeff_line_totalDegree_ne_zero hg
      ((IsFractionRing.injective (JetParams I) L).comp Polynomial.C_injective
        (h.trans (map_zero b).symm))
  have hq : q ≠ 0 := fun h => hcoeff (by simp [h])
  have hpow : LinearIndependent L (fun i : Fin q.natDegree => AdjoinRoot.root q ^ (i : ℕ)) := by
    let P := AdjoinRoot.powerBasis hq
    have hP : LinearIndependent L (fun i : Fin q.natDegree => P.basis i) :=
      P.basis.linearIndependent
    have heq : (fun i : Fin q.natDegree => P.basis i) =
        (fun i : Fin q.natDegree => AdjoinRoot.root q ^ (i : ℕ)) :=
      funext (fun i => P.basis_eq_pow i)
    exact heq ▸ hP
  have hlin : LinearIndependent SectionField (fun i : Fin q.natDegree => x ^ (i : ℕ)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hh := congrArg F ha
    simp only [map_sum, Algebra.smul_def, map_mul, map_pow, hx, hc, map_zero] at hh
    have hz := Fintype.linearIndependent_iff.mp hpow (fun j => s (a j))
      (by simpa only [Algebra.smul_def] using hh) i
    exact s.injective (hz.trans (map_zero s).symm)
  exact (le_natDegree_of_ne_zero hcoeff).trans (by simpa using hlin.fintype_card_le_finrank)

end
end K1_14_2_2_3_2
end PackSource_K1_14_2_2_3_2Aux3

section PackSource_K1_14_2_2_2_6_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace K1_14_2_2_2_6_2

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_3
open scoped nonZeroDivisors

private abbrev JetPlane (k : Type) [CommRing k] := MvPolynomial (Fin 2) k

private theorem eval_seed_inclusion {k : Type} [CommRing k] (a b y v : k)
    (f : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval ![a, b, y, v]
      (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))
        (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) f)) =
      MvPolynomial.eval ![a, b] f := by
  let cast34 := Fin.castLE (by decide : 3 ≤ 4)
  let cast23 := Fin.castLE (by decide : 2 ≤ 3)
  rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename]
  have hvec : (![a, b, y, v] ∘ cast34) ∘ cast23 = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]

/-- At an actual mark the maximal seed contraction is the ideal of its
rational seed point. -/
private theorem seedImage_eq_ker {I : Ideal Ambient} {z : K} {R : Polynomial K}
    (hm : (seedImage I).IsMaximal) (hmark : OnJet I z R) :
    seedImage I = RingHom.ker (graphEval z) := by
  apply hm.eq_of_le (RingHom.ker_ne_top (graphEval z))
  intro f hf
  have hmem : (rootIncl.comp rootSeeds) f ∈ I := hf
  have he : jetMarkHom z R ((rootIncl.comp rootSeeds) f) = graphEval z f :=
    eval_seed_inclusion (seedEmbedding z) (seedEmbedding z ^ p) (atX R) (atX R.derivative) f
  exact RingHom.mem_ker.mpr (he.symm.trans (RingHom.mem_ker.mp (hmark hmem)))

private theorem seedRelations {I : Ideal Ambient} {z : K} {R : Polynomial K}
    (hm : (seedImage I).IsMaximal) (hmark : OnJet I z R) :
    (MvPolynomial.X 0 - MvPolynomial.C (seedEmbedding z) : Ambient) ∈ I ∧
    (MvPolynomial.X 1 - MvPolynomial.C (seedEmbedding z ^ p) : Ambient) ∈ I := by
  have h₀ : (MvPolynomial.X 0 - MvPolynomial.C (seedEmbedding z) : Seeds) ∈ seedImage I := by
    rw [seedImage_eq_ker hm hmark]
    exact RingHom.mem_ker.mpr (by simp [graphEval])
  have h₁ : (MvPolynomial.X 1 - MvPolynomial.C (seedEmbedding z ^ p) : Seeds) ∈ seedImage I := by
    rw [seedImage_eq_ker hm hmark]
    exact RingHom.mem_ker.mpr (by simp [graphEval])
  have lift_mem (f : Seeds) (hf : f ∈ seedImage I) : rootIncl (rootSeeds f) ∈ I := hf
  exact ⟨by simpa [rootIncl, rootSeeds] using lift_mem _ h₀,
    by simpa [rootIncl, rootSeeds] using lift_mem _ h₁⟩

private def jetIncl {k : Type} [CommRing k] : JetPlane k →+* MvPolynomial (Fin 4) k :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 2, MvPolynomial.X 3]

private def fixSeed {k : Type} [CommRing k] (a b : k) : MvPolynomial (Fin 4) k →+* JetPlane k :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.C a, MvPolynomial.C b, MvPolynomial.X 0, MvPolynomial.X 1]

/-- A two-dimensional surface over a rational seed point fills the jet
plane. In particular the substitution fixing the seed annihilates its ideal. -/
private theorem fixSeed_kills {k : Type} [Field k] {I : Ideal (MvPolynomial (Fin 4) k)}
    (hdim : ringKrullDim (CoordinateRing I) = 2) {a b : k}
    (h₀ : MvPolynomial.X 0 - MvPolynomial.C a ∈ I)
    (h₁ : MvPolynomial.X 1 - MvPolynomial.C b ∈ I) :
    I ≤ RingHom.ker (fixSeed a b) := by
  let q : MvPolynomial (Fin 4) k →+* CoordinateRing I := Ideal.Quotient.mk I
  let j : JetPlane k →+* CoordinateRing I := q.comp jetIncl
  have q₀ : q (MvPolynomial.X 0) = q (MvPolynomial.C a) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h₀
  have q₁ : q (MvPolynomial.X 1) = q (MvPolynomial.C b) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁
  have hcomp : j.comp (fixSeed a b) = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [j, jetIncl, fixSeed]
    · intro i
      fin_cases i
      · simpa [j, jetIncl, fixSeed] using q₀.symm
      · simpa [j, jetIncl, fixSeed] using q₁.symm
      · simp [j, jetIncl, fixSeed]
      · simp [j, jetIncl, fixSeed]
  have hsurj : Function.Surjective j := by
    intro x
    obtain ⟨f, rfl⟩ := (Ideal.Quotient.mk_surjective (I := I)) x
    exact ⟨fixSeed a b f, RingHom.congr_fun hcomp f⟩
  have hplane : ringKrullDim (JetPlane k) = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num [Nat.card_eq_fintype_card]
  have hinj : Function.Injective j := by
    apply (injective_iff_map_eq_zero j).mpr
    intro f hjf
    by_contra hf
    have hreg : f ∈ (JetPlane k)⁰ := mem_nonZeroDivisors_of_ne_zero hf
    have hle := ringKrullDim_succ_le_of_surjective j hsurj hreg hjf
    rw [hdim, hplane] at hle
    norm_num at hle
  intro f hf
  apply RingHom.mem_ker.mpr
  apply hinj
  rw [map_zero]
  change (j.comp (fixSeed a b)) f = 0
  rw [hcomp]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- Specializing the free seeds in the generic jet slice gives a point over
the field of generic jet parameters. -/
private theorem jetSection_pos (I : Ideal Ambient) [Module.Finite SeedField (OverJets I)]
    (a b : FX) (hI : I ≤ RingHom.ker (fixSeed a b)) : 0 < sectionDegree I 3 := by
  let e : FibreRing →+* SeedField :=
    MvPolynomial.eval ![algebraMap FX SeedField a, algebraMap FX SeedField b]
  have hC (c : FX) :
      algebraMap (JetPlane FX) SeedField (MvPolynomial.C c) = algebraMap FX SeedField c := by
    rw [IsScalarTower.algebraMap_apply FX (JetPlane FX) SeedField, MvPolynomial.algebraMap_eq]
  have hcomp :
      e.comp mapGenericJets = (algebraMap (JetPlane FX) SeedField).comp (fixSeed a b) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, mapGenericJets, fixSeed, MvPolynomial.eval₂Hom_C, e,
        MvPolynomial.eval_C, hC]
    · intro i
      simp only [RingHom.comp_apply, mapGenericJets, fixSeed, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · change e (MvPolynomial.X 0) = algebraMap (JetPlane FX) SeedField (MvPolynomial.C a)
        rw [hC]
        exact MvPolynomial.eval_X 0
      · change e (MvPolynomial.X 1) = algebraMap (JetPlane FX) SeedField (MvPolynomial.C b)
        rw [hC]
        exact MvPolynomial.eval_X 1
      · change e (MvPolynomial.C (generic 0)) = generic 0
        exact MvPolynomial.eval_C (generic 0)
      · change e (MvPolynomial.C (generic 1)) = generic 1
        exact MvPolynomial.eval_C (generic 1)
  have hm : I.map mapGenericJets ≤ RingHom.ker e := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hcomp]
    intro f hf
    apply RingHom.mem_ker.mpr
    change algebraMap (JetPlane FX) SeedField (fixSeed a b f) = 0
    rw [RingHom.mem_ker.mp (hI hf), map_zero]
  have hn : I.map mapGenericJets ≠ ⊤ := fun ht =>
    RingHom.ker_ne_top e (top_unique (ht ▸ hm))
  let : Nontrivial (OverJets I) := Ideal.Quotient.nontrivial_iff.mpr hn
  change 0 < Module.finrank SeedField (OverJets I)
  exact (Module.finrank_pos_iff_of_free SeedField (OverJets I)).mpr inferInstance

theorem proof : K1_14_2_2_2_6.c2 := by
  intro I _ hdim hm hfinite hmark
  let : Module.Finite SeedField (OverJets I) := hfinite
  obtain ⟨z, R, hon⟩ := hmark
  obtain ⟨h₀, h₁⟩ := seedRelations hm hon
  exact jetSection_pos I _ _ (fixSeed_kills hdim h₀ h₁)

end

end K1_14_2_2_2_6_2
end PackSource_K1_14_2_2_2_6_2Proof

section PackSource_K1_14_3_2_5_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_3_2_5_1

noncomputable section

open K1_14 K1_14_3 K1_14_3_2_5 Polynomial
open scoped Polynomial

private def substitute : SectionSeeds →ₐ[SectionField] SectionField[X] :=
  MvPolynomial.aeval (K1_14_2_3_1.lineValues (sectionParameter 0) (sectionParameter 2))

private def restriction (f : Seeds) : SectionField[X] := substitute (seedBase f)

private theorem substitute_line : substitute seedLine = 0 := by
  simp [substitute, K1_14_2_3_1.lineValues, seedLine, Polynomial.algebraMap_eq]

private def restore (f : Seeds) : SectionField[X] →ₐ[SectionField] CurveSection f :=
  Polynomial.aeval (Ideal.Quotient.mk (curveSectionIdeal f) (MvPolynomial.X 1))

private theorem restore_substitute (f : Seeds) :
    (restore f).comp substitute = Ideal.Quotient.mkₐ SectionField (curveSectionIdeal f) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · let J := curveSectionIdeal f
    have hline : Ideal.Quotient.mk J seedLine = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := sub_eq_zero.mp (show Ideal.Quotient.mk J (MvPolynomial.X 0) +
        algebraMap SectionField (CurveSection f) (sectionParameter 0) *
          Ideal.Quotient.mk J (MvPolynomial.X 1) -
        algebraMap SectionField (CurveSection f) (sectionParameter 2) = 0 by
      simpa only [seedLine, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
        Ideal.Quotient.mk_algebraMap] using hline)
    simpa [substitute, K1_14_2_3_1.lineValues, restore, Ideal.Quotient.mkₐ_eq_mk, J] using
      (eq_sub_iff_add_eq.mpr h).symm
  · simp [substitute, K1_14_2_3_1.lineValues, restore, Ideal.Quotient.mkₐ_eq_mk]

/-- Eliminate the first seed coordinate and use the second as the polynomial variable. -/
private def sectionEquiv (f : Seeds) :
    CurveSection f ≃ₐ[SectionField] (SectionField[X] ⧸ Ideal.span {restriction f}) := by
  let I : Ideal SectionField[X] := Ideal.span {restriction f}
  let J := curveSectionIdeal f
  let A := Ideal.Quotient.mkₐ SectionField J
  let B := Ideal.Quotient.mkₐ SectionField I
  let forward := B.comp substitute
  have hf : J ≤ RingHom.ker forward.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (restriction f))
    · change B (substitute seedLine) = 0
      rw [substitute_line, map_zero]
  have hg : I ≤ RingHom.ker (restore f).toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change (restore f).comp substitute (seedBase f) = 0
    rw [restore_substitute]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  let fromSection := Ideal.Quotient.liftₐ J forward (fun _ hx => hf hx)
  let toSection := Ideal.Quotient.liftₐ I (restore f) (fun _ hx => hg hx)
  have hfrom : fromSection.comp A = forward := Ideal.Quotient.liftₐ_comp _ _ _
  have hto : toSection.comp B = restore f := Ideal.Quotient.liftₐ_comp _ _ _
  refine AlgEquiv.ofAlgHom fromSection toSection ?_ ?_
  · apply Ideal.Quotient.algHom_ext SectionField
    change (fromSection.comp toSection).comp B = (AlgHom.id SectionField _).comp B
    rw [AlgHom.comp_assoc, hto, AlgHom.id_comp]
    apply Polynomial.algHom_ext
    have hX : restore f Polynomial.X = A (MvPolynomial.X 1) := Polynomial.aeval_X _
    rw [AlgHom.comp_apply, hX, ← AlgHom.comp_apply, hfrom]
    simp [forward, substitute, K1_14_2_3_1.lineValues]
  · apply Ideal.Quotient.algHom_ext SectionField
    change (toSection.comp fromSection).comp A = (AlgHom.id SectionField _).comp A
    rw [AlgHom.comp_assoc, hfrom, AlgHom.id_comp]
    change toSection.comp (B.comp substitute) = A
    rw [← AlgHom.comp_assoc, hto, restore_substitute]

private def parameterIndices : Fin 2 → Fin 4 := ![0, 2]

private theorem parameterIndices_injective : Function.Injective parameterIndices := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [parameterIndices]

private def parameterMap : Seeds →+* SectionField :=
  (algebraMap (MvPolynomial (Fin 4) FX) SectionField).comp
    (MvPolynomial.rename parameterIndices).toRingHom

private def extendParameters : K1_14_2.SeedField →+* SectionField :=
  IsFractionRing.lift (g := parameterMap)
    ((IsFractionRing.injective (MvPolynomial (Fin 4) FX) SectionField).comp
      (MvPolynomial.rename_injective parameterIndices parameterIndices_injective))

private theorem extendParameters_apply (r : Seeds) :
    extendParameters (algebraMap Seeds K1_14_2.SeedField r) = parameterMap r :=
  IsFractionRing.lift_algebraMap _ r

/-- The previously proved two-parameter restriction embeds coefficientwise
into the full section field, so it keeps its univariate degree. -/
private theorem restriction_map :
    (Polynomial.mapRingHom extendParameters).comp K1_14_2_3_1.lineRestriction =
      substitute.toRingHom.comp seedBase := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [K1_14_2_3_1.lineRestriction, K1_14_2_3_1.eliminate, substitute, seedBase,
      RingHom.comp_apply, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.coe_mapRingHom, Polynomial.map_C]
    congr 1
    change extendParameters (algebraMap Seeds K1_14_2.SeedField (MvPolynomial.C a)) = _
    rw [extendParameters_apply]
    exact congrArg (algebraMap (MvPolynomial (Fin 4) FX) SectionField)
      (MvPolynomial.rename_C parameterIndices a)
  · intro i
    fin_cases i <;>
      simp [K1_14_2_3_1.lineRestriction, K1_14_2_3_1.eliminate, K1_14_2_3_1.lineValues,
        substitute, seedBase, K1_14_2.generic, extendParameters_apply, parameterMap,
        parameterIndices, sectionParameter]

theorem proof : K1_14_3_2_5.c1 := by
  intro f _
  have hmap : restriction f = (K1_14_2_3_1.lineRestriction f).map extendParameters :=
    (RingHom.congr_fun restriction_map f).symm
  rw [(sectionEquiv f).toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree, hmap,
    Polynomial.natDegree_map_eq_of_injective extendParameters.injective,
    K1_14_2_3_1.totalDegree_lineRestriction]

end
end K1_14_3_2_5_1
end PackSource_K1_14_3_2_5_1Proof

section PackSource_K1_14_2_4_1_1_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_4_1_1_2

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3_1 K1_14_2_4_1 K1_14_2_4_1_1
open scoped Polynomial

local instance (I : Ideal Seeds) : CommRing (PlaneSlice I)[X] :=
  @Polynomial.commRing (PlaneSlice I) (Ideal.Quotient.commRing (sectionIdeal I 0 1))

private def rootPolynomial (R : Type) [CommRing R] :
    MvPolynomial (Fin 3) R ≃ₐ[R] (MvPolynomial (Fin 2) R)[X] :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans (MvPolynomial.optionEquivLeft R (Fin 2))

private theorem root_index_zero : finSuccEquivLast (0 : Fin 3) = some 0 := rfl
private theorem root_index_one : finSuccEquivLast (1 : Fin 3) = some 1 := rfl
private theorem root_index_two : finSuccEquivLast (2 : Fin 3) = none := finSuccEquivLast_last

private abbrev incl (R : Type) [CommRing R] :
    MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 3) R :=
  (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3))).toRingHom

private theorem rootPolynomial_incl (R : Type) [CommRing R] :
    (rootPolynomial R).toRingEquiv.toRingHom.comp (incl R) = Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootPolynomial]
  · intro i
    fin_cases i <;> simp [rootPolynomial, root_index_zero, root_index_one]

private abbrev toOver (n : ℕ) : Raw n →+* Over n :=
  MvPolynomial.map (algebraMap FX SeedField)

private theorem incl_coeff :
    (incl SeedField).comp (toOver 2) = (toOver 3).comp rootSeeds := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootSeeds]
  · intro i
    simp [rootSeeds]

private theorem incl_line : incl SeedField (seedLine 0 1) = seedLine 0 1 := by
  simp [seedLine]

private theorem root_coeff :
    (rootPolynomial SeedField).toRingEquiv.toRingHom.comp (toOver 3) =
      (Polynomial.mapRingHom (toOver 2)).comp rootView.toRingEquiv.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootPolynomial, rootView]
  · intro i
    fin_cases i <;> simp [rootPolynomial, rootView, root_index_zero, root_index_one, root_index_two]

/-- The seed quotient followed by coefficient localization recovers every
ideal of the generic polynomial ring from its contraction. -/
private theorem generic_ideal (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (hC : SeedLocalization C₀) (P : Ideal (ConstantSeedX C₀)[X]) :
    (P.comap (genericRootMap C₀)).map (genericRootMap C₀) = P := by
  let A := Seeds ⧸ seedEquation C₀
  let T := ConstantSeedX C₀
  let : CommRing A := Ideal.Quotient.commRing (seedEquation C₀)
  let : CommRing A[X] := Polynomial.commRing
  let φ : A →+* T := seedCurveMap C₀ hC.kernel
  let : Algebra A T := φ.toAlgebra
  let : IsFractionRing A T := hC.localized
  let : Algebra A[X] T[X] := Polynomial.algebra A T
  let M : Submonoid A[X] := (nonZeroDivisors A).map Polynomial.C
  let : IsLocalization M T[X] := Polynomial.isLocalization (nonZeroDivisors A) T
  let u : RootAmbient →+* A[X] :=
    (Polynomial.mapRingHom (Ideal.Quotient.mk (seedEquation C₀))).comp
      rootView.toRingEquiv.toRingHom
  have hu : Function.Surjective u :=
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp rootView.surjective
  have hφ : φ.comp (Ideal.Quotient.mk (seedEquation C₀)) = genericSeedMap C₀ := rfl
  have h : genericRootMap C₀ = (algebraMap A[X] T[X]).comp u := by
    rw [genericRootMap_eq, ← hφ, ← Polynomial.mapRingHom_comp]
    rfl
  rw [h, ← Ideal.comap_comap, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hu]
  exact IsLocalization.map_under M T[X] P

private theorem seed_le (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (hC : SeedLocalization C₀) (J : Ideal RootAmbient) (P : Ideal (ConstantSeedX C₀)[X])
    (hJ : J = P.comap (genericRootMap C₀)) :
    (seedEquation C₀).map rootSeeds ≤ J := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro s hs
  have hzero : genericSeedMap C₀ s = 0 := RingHom.mem_ker.mp (hC.kernel.symm ▸ hs)
  have hsC : rootView.toRingEquiv.toRingHom (rootSeeds s) = Polynomial.C s :=
    DFunLike.congr_fun rootView_seed s
  have h : genericRootMap C₀ (rootSeeds s) = 0 := by
    rw [genericRootMap_eq, RingHom.comp_apply, hsC]
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hzero, map_zero]
  rw [hJ]
  change genericRootMap C₀ (rootSeeds s) ∈ P
  rw [h]
  exact P.zero_mem

private def planePolynomial (I : Ideal Seeds) : Over 3 →ₐ[SeedField] (PlaneSlice I)[X] :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ SeedField (sectionIdeal I 0 1))).comp
    (rootPolynomial SeedField).toAlgHom

private theorem planePolynomial_surjective (I : Ideal Seeds) :
    Function.Surjective (planePolynomial I) :=
  (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (rootPolynomial SeedField).surjective

private theorem planePolynomial_ker (I : Ideal Seeds) :
    RingHom.ker (planePolynomial I).toRingHom =
      (sectionIdeal I 0 1).map (incl SeedField) := by
  let e := (rootPolynomial SeedField).toRingEquiv
  change RingHom.ker ((Polynomial.mapRingHom (Ideal.Quotient.mk (sectionIdeal I 0 1))).comp
    e.toRingHom) = _
  rw [← RingHom.comap_ker, Polynomial.ker_mapRingHom, Ideal.mk_ker,
    ← rootPolynomial_incl SeedField, ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

/-- Impose the seed-plane relations first and then the extended root ideal.
The free polynomial variable on the plane slice remains the original Y. -/
private def rootSliceEquiv (I : Ideal Seeds) (J : Ideal RootAmbient)
    (hseed : I.map rootSeeds ≤ J) :
    RootSeedSection J ≃ₐ[SeedField]
      ((PlaneSlice I)[X] ⧸ (J.map (toOver 3)).map (planePolynomial I).toRingHom) := by
  let W := J.map (toOver 3)
  let f := planePolynomial I
  have hker : RingHom.ker f.toRingHom =
      (I.map rootSeeds).map (toOver 3) ⊔ Ideal.span {seedLine (0 : Fin 3) 1} := by
    rw [planePolynomial_ker]
    change ((I.map (toOver 2) ⊔ Ideal.span {seedLine (0 : Fin 2) 1}).map (incl SeedField)) = _
    rw [Ideal.map_sup, Ideal.map_map, incl_coeff, ← Ideal.map_map, Ideal.map_span,
      Set.image_singleton, incl_line]
  have hsmall : (I.map rootSeeds).map (toOver 3) ≤ W :=
    Ideal.map_mono (f := toOver 3) hseed
  have hsup : W ⊔ (I.map rootSeeds).map (toOver 3) = W := sup_eq_left.mpr hsmall
  have hW : W ⊔ RingHom.ker f.toRingHom = sectionIdeal J 0 1 := by
    rw [hker, ← sup_assoc, hsup]
  let g := (Ideal.Quotient.mkₐ SeedField (W.map f.toRingHom)).comp f
  have hf : Function.Surjective f.toRingHom := planePolynomial_surjective I
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hgker : RingHom.ker g.toRingHom = sectionIdeal J 0 1 := by
    change RingHom.ker ((Ideal.Quotient.mk (W.map f.toRingHom)).comp f.toRingHom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker,
      Ideal.comap_map_of_surjective f.toRingHom hf W,
      ← RingHom.ker_eq_comap_bot, hW]
  exact (Ideal.quotientEquivAlgOfEq SeedField hgker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)

private theorem quotient_rank {T B : Type} [Field T] [Field B]
    (η : T →+* B) (P : Ideal T[X]) :
    Module.finrank B (B[X] ⧸ P.map (Polynomial.mapRingHom η)) =
      Module.finrank T (T[X] ⧸ P) := by
  let : EuclideanDomain T[X] := Polynomial.instEuclideanDomain
  let : IsPrincipalIdealRing T[X] := EuclideanDomain.instIsPrincipalIdealRing
  let : P.IsPrincipal := IsPrincipalIdealRing.principal P
  let p := Submodule.IsPrincipal.generator P
  have hp : Ideal.span {p} = P := Ideal.span_singleton_generator P
  rw [← hp, Ideal.map_span, Set.image_singleton, finrank_quotient_span_eq_natDegree,
    finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_map_eq_of_injective η.injective p

private theorem section_rank {F T B R : Type} [Field F] [Field T] [Field B]
    [CommRing R] [Algebra F R] [Algebra F B] (η : T →+* B) (P : Ideal T[X])
    (e : R ≃ₐ[F] (B[X] ⧸ P.map (Polynomial.mapRingHom η))) :
    Module.finrank F R = Module.finrank F B * Module.finrank T (T[X] ⧸ P) := by
  calc
    Module.finrank F R = Module.finrank F (B[X] ⧸ P.map (Polynomial.mapRingHom η)) :=
      e.toLinearEquiv.finrank_eq
    _ = Module.finrank F B * Module.finrank B (B[X] ⧸ P.map (Polynomial.mapRingHom η)) :=
      (Module.finrank_mul_finrank F B _).symm
    _ = _ := congrArg (Module.finrank F B * ·) (quotient_rank η P)

theorem proof : K1_14_2_4_1_1.c2 := by
  intro C₀ hC₀ J P hC _ hJ _ _
  let I := seedEquation C₀
  let A := CoordinateRing I
  let B := PlaneSlice I
  let T := ConstantSeedX C₀
  let : I.IsPrime := show (seedEquation C₀).IsPrime from
    hC.kernel ▸ RingHom.ker_isPrime (genericSeedMap C₀)
  let : Field B := (plane_field C₀ hC).toField
  let : CommRing A := Ideal.Quotient.commRing I
  let φ : A →+* T := seedCurveMap C₀ hC.kernel
  let b : A →+* B := toSlice I 0 1
  let u : Seeds →+* A := Ideal.Quotient.mk I
  let : Algebra A T := φ.toAlgebra
  let : IsFractionRing A T := hC.localized
  have hb : Function.Injective b := toPlane_injective I
  let η : T →+* B := IsFractionRing.lift (A := A) (K := T) (L := B) (g := b) hb
  have hηbase : η.comp φ = b := by
    apply RingHom.ext
    intro x
    change η (algebraMap A T x) = b x
    exact IsFractionRing.lift_algebraMap (A := A) (K := T) (L := B) (g := b) hb x
  have hφ : φ.comp u = genericSeedMap C₀ := rfl
  have hbu : b.comp u = (Ideal.Quotient.mk (sectionIdeal I 0 1)).comp (toOver 2) := rfl
  have hη : η.comp (genericSeedMap C₀) = (Ideal.Quotient.mk (sectionIdeal I 0 1)).comp (toOver 2) := by
    rw [← hφ, ← RingHom.comp_assoc, hηbase, hbu]
  have hcomp : (planePolynomial I).toRingHom.comp (toOver 3) =
      (Polynomial.mapRingHom η).comp (genericRootMap C₀) := by
    change (Polynomial.mapRingHom (Ideal.Quotient.mk (sectionIdeal I 0 1))).comp
      ((rootPolynomial SeedField).toRingEquiv.toRingHom.comp (toOver 3)) = _
    rw [root_coeff, genericRootMap_eq, ← RingHom.comp_assoc, Polynomial.mapRingHom_comp,
      ← hη, ← Polynomial.mapRingHom_comp, RingHom.comp_assoc]
  have hmap : (J.map (toOver 3)).map (planePolynomial I).toRingHom =
      P.map (Polynomial.mapRingHom η) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJ, generic_ideal C₀ hC]
  let e := (rootSliceEquiv I J (seed_le C₀ hC J P hJ)).trans
    (Ideal.quotientEquivAlgOfEq SeedField hmap)
  exact section_rank η P e

end
end K1_14_2_4_1_1_2
end PackSource_K1_14_2_4_1_1_2Proof

section PackSource_K1_14_2_2_7_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace K1_14_2_2_7_2_1

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_2
open K1_14_2_3_1 (coord parameterMap slopeToSlice toSlice parameter_commutes)
open scoped Polynomial nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private abbrev seedIncl : Seeds →+* Ambient := rootIncl.comp rootSeeds

private theorem seed_dominant {I : Ideal Ambient} (hI : Active I) :
    Function.Injective ((Ideal.Quotient.mk I).comp seedIncl) := by
  let q := (Ideal.Quotient.mk (I.map mapGenericSeed)).comp mapGenericSeed
  let e : SeedField →+* OverSeeds I := algebraMap SeedField (OverSeeds I)
  have he : q.comp seedIncl = e.comp (algebraMap Seeds SeedField) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply FX Seeds SeedField]
      simp [q, rootIncl, rootSeeds, mapGenericSeed]
      rfl
    · intro i
      fin_cases i <;> simp [q, seedIncl, rootIncl, rootSeeds, mapGenericSeed, e, generic] <;> rfl
  let : Nontrivial (OverSeeds I) := Module.nontrivial_of_finrank_pos hI.seed_size.1
  apply (injective_iff_map_eq_zero ((Ideal.Quotient.mk I).comp seedIncl)).2
  intro f hf
  have hmem : seedIncl f ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hf
  have hz : q (seedIncl f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem mapGenericSeed hmem)
  have hzero : (e.comp (algebraMap Seeds SeedField)) f = 0 := by
    rw [← he]
    exact hz
  have hinj : Function.Injective (e.comp (algebraMap Seeds SeedField)) :=
    e.injective.comp (IsFractionRing.injective Seeds SeedField)
  exact hinj (hzero.trans (map_zero (e.comp (algebraMap Seeds SeedField))).symm)

/-- With independent seed coordinates, the slope and intercept are independent.
Specializing the second seed coordinate to zero identifies the two parameters
with the two indeterminates of an iterated polynomial ring. -/
theorem parameter_injective_of_active {I : Ideal Ambient} (hI : Active I) :
    Function.Injective (parameterMap I 0 1) := by
  let u : Seeds →+* Seeds[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0) + Polynomial.X * Polynomial.C (MvPolynomial.X 1)]
  let v : Seeds →+* FX[X] :=
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0]
  let e := MvPolynomial.finSuccEquiv FX 1
  let w := MvPolynomial.uniqueAlgEquiv FX (Fin 1)
  have hv : (Polynomial.mapRingHom v).comp u =
      (Polynomial.mapRingHom w.toRingHom).comp e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [u, v, e, w, MvPolynomial.finSuccEquiv_apply, MvPolynomial.uniqueAlgEquiv_apply,
        RingHom.comp_apply]
    · intro j
      fin_cases j
      · simp [u, e, MvPolynomial.finSuccEquiv_X_zero, RingHom.comp_apply]
      · change Polynomial.mapRingHom v (u (MvPolynomial.X 1)) =
          Polynomial.mapRingHom w.toRingHom (e (MvPolynomial.X (0 : Fin 1).succ))
        rw [show e (MvPolynomial.X (0 : Fin 1).succ) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) from
          MvPolynomial.finSuccEquiv_X_succ (R := FX) (j := (0 : Fin 1))]
        simp [u, v, w, MvPolynomial.uniqueAlgEquiv_apply]
  have hu : Function.Injective u := by
    apply Function.Injective.of_comp (f := Polynomial.mapRingHom v)
    change Function.Injective ((Polynomial.mapRingHom v).comp u)
    rw [hv]
    exact (Polynomial.map_injective w.toRingHom w.injective).comp e.injective
  let g := (Ideal.Quotient.mk I).comp seedIncl
  have hg : (Polynomial.mapRingHom g).comp u = parameterMap I 0 1 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [g, u, parameterMap, seedIncl, rootIncl, rootSeeds, RingHom.comp_apply]
      rfl
    · intro j
      fin_cases j <;>
        simp [g, u, parameterMap, seedIncl, rootIncl, rootSeeds, coord, RingHom.comp_apply]
  rw [← hg]
  exact (Polynomial.map_injective g (seed_dominant hI)).comp hu

private abbrev BeforeLocalization := MvPolynomial (Fin 4) Seeds

private abbrev denominators : Submonoid BeforeLocalization :=
  Seeds⁰.map (MvPolynomial.C (σ := Fin 4))

private def beforeBase : Ambient →+* BeforeLocalization := MvPolynomial.map MvPolynomial.C

private def beforeLine : BeforeLocalization :=
  MvPolynomial.X 0 + MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X 1 -
    MvPolynomial.C (MvPolynomial.X 1)

private def beforeEval (I : Ideal Ambient) : BeforeLocalization →+* (CoordinateRing I)[X] :=
  MvPolynomial.eval₂Hom (parameterMap I 0 1) (fun i => Polynomial.C (coord I i))

private theorem beforeEval_comp (I : Ideal Ambient) :
    (beforeEval I).comp beforeBase = Polynomial.C.comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [beforeEval, beforeBase, parameterMap]
    rfl
  · intro i
    simp [beforeEval, beforeBase, coord]

private theorem beforeEval_surjective (I : Ideal Ambient) : Function.Surjective (beforeEval I) := by
  let u := Polynomial.eval₂RingHom beforeBase
    (MvPolynomial.C (MvPolynomial.X 0) : BeforeLocalization)
  have he : (beforeEval I).comp u = Polynomial.mapRingHom (Ideal.Quotient.mk I) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, u, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact RingHom.congr_fun (beforeEval_comp I) a
    · simp [u, beforeEval, parameterMap]
  have hs : Function.Surjective ((beforeEval I).comp u) := by
    rw [he]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  exact Function.Surjective.of_comp (f := beforeEval I) (g := u) hs

private theorem localized_beforeBase :
    (algebraMap BeforeLocalization SeedAmbient).comp beforeBase = seedBase := by
  change (MvPolynomial.map (algebraMap Seeds SeedField)).comp beforeBase = seedBase
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, beforeBase, seedBase, MvPolynomial.map_C]
    rfl
  · intro i
    simp only [RingHom.comp_apply, beforeBase, seedBase, MvPolynomial.map_X]

private theorem localized_beforeLine :
    algebraMap BeforeLocalization SeedAmbient beforeLine = seedLine 0 1 := by
  change MvPolynomial.map (algebraMap Seeds SeedField) beforeLine = seedLine 0 1
  simp only [beforeLine, map_add, map_mul, map_sub, MvPolynomial.map_X, MvPolynomial.map_C,
    seedLine, generic]

private theorem evaluation_square (I : Ideal Ambient) :
    (Ideal.Quotient.mk (seedIdeal I)).comp (algebraMap BeforeLocalization SeedAmbient) =
      (slopeToSlice I 0 1).comp (beforeEval I) := by
  change (Ideal.Quotient.mk (seedIdeal I)).comp (MvPolynomial.map (algebraMap Seeds SeedField)) = _
  apply MvPolynomial.ringHom_ext
  · intro a
    change Ideal.Quotient.mk (seedIdeal I)
        (MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.C a)) =
      slopeToSlice I 0 1 (beforeEval I (MvPolynomial.C a))
    rw [MvPolynomial.map_C, beforeEval, MvPolynomial.eval₂Hom_C]
    have h := (RingHom.congr_fun (parameter_commutes I 0 1) a).symm
    change Ideal.Quotient.mk (K1_14_2_3_1.sectionIdeal I 0 1)
        (MvPolynomial.C (algebraMap Seeds SeedField a)) =
      slopeToSlice I 0 1 (parameterMap I 0 1 a) at h
    change Ideal.Quotient.mk (K1_14_2_3_1.sectionIdeal I 0 1)
        (MvPolynomial.C (algebraMap Seeds SeedField a)) =
      slopeToSlice I 0 1 (parameterMap I 0 1 a)
    exact h
  · intro i
    change Ideal.Quotient.mk (seedIdeal I)
        (MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.X i)) =
      slopeToSlice I 0 1 (beforeEval I (MvPolynomial.X i))
    rw [MvPolynomial.map_X, beforeEval, MvPolynomial.eval₂Hom_X', slopeToSlice,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, toSlice, coord, Ideal.quotientMap_mk,
      MvPolynomial.map_X]
    rfl

abbrev sectionAlgebra (I : Ideal Ambient) :
    Algebra ((CoordinateRing I)[X]) (JetSeedSection I) :=
  (slopeToSlice I 0 1).toAlgebra

abbrev seedDenominators (I : Ideal Ambient) : Submonoid ((CoordinateRing I)[X]) :=
  Seeds⁰.map (parameterMap I 0 1)

/-- Eliminate the intercept before inverting the nonzero parameter polynomials. -/
theorem localization_of_seed_section (I : Ideal Ambient) :
    letI : Algebra ((CoordinateRing I)[X]) (JetSeedSection I) := sectionAlgebra I
    IsLocalization (seedDenominators I) (JetSeedSection I) := by
  let : Algebra ((CoordinateRing I)[X]) (JetSeedSection I) := sectionAlgebra I
  have hden : denominators.map (beforeEval I) = seedDenominators I := by
    change (Seeds⁰.map (MvPolynomial.C (σ := Fin 4)).toMonoidHom).map
      (beforeEval I).toMonoidHom = Seeds⁰.map (parameterMap I 0 1).toMonoidHom
    rw [Submonoid.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    exact MvPolynomial.eval₂Hom_C _ _ _
  rw [← hden]
  apply IsLocalization.of_surjective (S' := JetSeedSection I) denominators SeedAmbient
    (beforeEval I) (beforeEval_surjective I) (Ideal.Quotient.mk (seedIdeal I))
    Ideal.Quotient.mk_surjective (evaluation_square I)
  rw [Ideal.mk_ker, seedIdeal]
  apply sup_le
  · rw [← localized_beforeBase, ← Ideal.map_map]
    apply Ideal.map_mono
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change beforeEval I (beforeBase a) = 0
    rw [show beforeEval I (beforeBase a) = Polynomial.C (Ideal.Quotient.mk I a)
        from RingHom.congr_fun (beforeEval_comp I) a,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · rw [← localized_beforeLine, Ideal.span_singleton_le_iff_mem]
    apply Ideal.mem_map_of_mem
    change beforeEval I beforeLine = 0
    simp [beforeEval, beforeLine, parameterMap]

/-- Noether normalization computes the two dimensions from the same polynomial ring. -/
private theorem affine_dimension (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) ∧ Algebra.trdeg k A = (d : Cardinal) := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let R := MvPolynomial (Fin d) k
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Module.Finite R A := hfin
  let : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  let : IsScalarTower k R A := IsScalarTower.of_algHom g
  have hdim : ringKrullDim R = (d : WithBot ℕ∞) := by
    simp [R, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  refine ⟨d, ?_, ?_⟩
  · rw [← hdim]
    apply le_antisymm
    · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
      intro a b hab
      exact Ideal.IsIntegral.under_lt_under (R := R) (show a.asIdeal < b.asIdeal from hab)
    · rw [hdim]
      obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hdim.ge
      let : l.head.asIdeal.IsPrime := l.head.isPrime
      have hbot : (⊥ : Ideal A).under R ≤ l.head.asIdeal := by
        change Ideal.comap (algebraMap R A) ⊥ ≤ l.head.asIdeal
        rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective R A)]
        exact bot_le
      obtain ⟨P, _, hP, hhead⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal A) hbot
      let : P.IsPrime := hP
      let : P.LiesOver l.head.asIdeal := ⟨hhead.symm⟩
      obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
      exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  · let : Algebra.IsAlgebraic R A := Algebra.IsAlgebraic.of_finite R A
    simpa [R, trdeg_eq_zero (R := R) (A := A), Cardinal.mk_fin] using
      (trdeg_add_eq (A := A) k R).symm

private theorem trdeg_seedField : Algebra.trdeg FX SeedField = 2 := by
  let : Algebra.IsAlgebraic Seeds SeedField := IsLocalization.isAlgebraic SeedField Seeds⁰
  simpa [Seeds, trdeg_eq_zero (R := Seeds) (A := SeedField), Cardinal.mk_fin] using
    (trdeg_add_eq (A := SeedField) FX Seeds).symm

private theorem regular_denominators {I : Ideal Ambient} [I.IsPrime] (hI : Active I) :
    seedDenominators I ≤ (CoordinateRing I)[X]⁰ :=
  map_le_nonZeroDivisors_of_injective (parameterMap I 0 1) (parameter_injective_of_active hI) le_rfl

private theorem seed_section_domain {I : Ideal Ambient} [I.IsPrime] (hI : Active I) :
    IsDomain (JetSeedSection I) := by
  let : Algebra ((CoordinateRing I)[X]) (JetSeedSection I) := sectionAlgebra I
  let : IsLocalization (seedDenominators I) (JetSeedSection I) := localization_of_seed_section I
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (JetSeedSection I) (regular_denominators hI)

private theorem section_constants (I : Ideal Ambient) (a : FX) :
    algebraMap FX (JetSeedSection I) a =
      slopeToSlice I 0 1 (algebraMap FX (CoordinateRing I)[X] a) := by
  change Ideal.Quotient.mk (seedIdeal I) (MvPolynomial.C (algebraMap FX SeedField a)) =
    slopeToSlice I 0 1 (Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.C a)))
  rw [slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, toSlice,
    Ideal.quotientMap_mk, MvPolynomial.map_C]
  rfl

private theorem trdeg_of_localization (k R S : Type) [Field k] [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra k R] [Algebra k S] [hAlg : Algebra R S]
    [FaithfulSMul k R] (M : Submonoid R) [hLoc : IsLocalization M S]
    (hM : M ≤ R⁰)
    (hcomp : ∀ x : k, algebraMap k S x = algebraMap R S (algebraMap k R x)) :
    Algebra.trdeg k S = Algebra.trdeg k R := by
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq hcomp
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (IsLocalization.injective S hM)
  let : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic S M
  simpa only [trdeg_eq_zero (R := R) (A := S), add_zero] using
    (trdeg_add_eq (A := S) k R).symm

private theorem trdeg_polynomial (k R : Type) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [FaithfulSMul k R] :
    Algebra.trdeg k R[X] = Algebra.trdeg k R + 1 := by
  let : FaithfulSMul R R[X] := (faithfulSMul_iff_algebraMap_injective R R[X]).mpr
    Polynomial.C_injective
  simpa only [Polynomial.trdeg_of_isDomain] using (trdeg_add_eq (A := R[X]) k R).symm

private theorem trdeg_section_over_constants {I : Ideal Ambient} [I.IsPrime]
    [IsDomain (JetSeedSection I)] (hI : Active I) :
    Algebra.trdeg FX (JetSeedSection I) = Algebra.trdeg FX (CoordinateRing I) + 1 := by
  let R := CoordinateRing I
  let S := JetSeedSection I
  let : FaithfulSMul FX R :=
    (faithfulSMul_iff_algebraMap_injective FX R).mpr (algebraMap FX R).injective
  let : FaithfulSMul FX R[X] :=
    (faithfulSMul_iff_algebraMap_injective FX R[X]).mpr (algebraMap FX R[X]).injective
  have hloc := trdeg_of_localization FX R[X] S (hAlg := sectionAlgebra I)
    (seedDenominators I) (hLoc := localization_of_seed_section I)
    (regular_denominators hI) (section_constants I)
  exact hloc.trans (trdeg_polynomial FX R)

theorem proof : K1_14_2_2_7_2.c1 := by
  intro I hI
  let S := JetSeedSection I
  let : I.IsPrime := hI.prime
  let : IsDomain S := seed_section_domain hI
  refine ⟨?_, ?_⟩
  · intro htop
    have hsub : Subsingleton S := Ideal.Quotient.subsingleton_iff.mpr htop
    exact zero_ne_one (hsub.elim (0 : S) 1)
  obtain ⟨d, hd, ht⟩ := affine_dimension FX (CoordinateRing I)
  have hd' : d = 2 := by
    rw [hI.dimension] at hd
    exact_mod_cast hd.symm
  have htotal : Algebra.trdeg FX S = 3 := by
    rw [trdeg_section_over_constants hI, ht, hd']
    norm_num
  let : FaithfulSMul SeedField S :=
    (faithfulSMul_iff_algebraMap_injective SeedField S).mpr (algebraMap SeedField S).injective
  have htower := trdeg_add_eq (A := S) FX SeedField
  rw [trdeg_seedField, htotal] at htower
  have hrel : Algebra.trdeg SeedField S = 1 := by
    apply Cardinal.eq_of_add_eq_add_left (a := 2)
    · exact htower.trans (by norm_num)
    · simp
  obtain ⟨e, he, hte⟩ := affine_dimension SeedField S
  have he' : e = 1 := by
    rw [hrel] at hte
    exact_mod_cast hte.symm
  simpa [he'] using he

end
end K1_14_2_2_7_2_1
end PackSource_K1_14_2_2_7_2_1Proof

section PackSource_K1_14_2_3_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace K1_14_2_3_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_3
open scoped Polynomial

private theorem seedImage_ne_bot (I : Ideal Ambient) [I.IsPrime] [Nontrivial (JetSeedSection I)]
    [Module.Finite SeedField (JetSeedSection I)] : seedImage I ≠ ⊥ := by
  have hf := Module.Finite.of_injective (planeToJet I).toLinearMap (planeToJet_injective I)
  intro h
  rw [h] at hf
  let e := lineQuotientEquiv (⊥ : Ideal Seeds)
  have he : (⊥ : Ideal Seeds).map lineRestriction = ⊥ := Ideal.map_bot
  have e' : PlaneSlice (⊥ : Ideal Seeds) ≃ₐ[SeedField]
      (SeedField[X] ⧸ (⊥ : Ideal SeedField[X])) := he ▸ e
  exact Polynomial.not_finite
    (Module.Finite.equiv (e'.trans (AlgEquiv.quotientBot SeedField SeedField[X])).toLinearEquiv)

private theorem seedImage_not_maximal (I : Ideal Ambient) [Nontrivial (JetSeedSection I)] :
    ¬ (seedImage I).IsMaximal := by
  intro hM
  let P := seedImage I
  let B := CoordinateRing P
  let : P.IsMaximal := hM
  let : Field B := Ideal.Quotient.field P
  let : Module.Finite FX B := finite_of_finite_type_of_isJacobsonRing FX B
  let f : Seeds →ₐ[FX] B[X] :=
    ⟨parameterMap P 0 1, by
      intro a
      change parameterMap P 0 1 (MvPolynomial.C a) = Polynomial.C (algebraMap FX B a)
      simp [parameterMap]
      rfl⟩
  have hdim := trdeg_le_of_injective f (plane_parameter_injective I)
  rw [MvPolynomial.trdeg_of_isDomain, ← trdeg_add_eq FX B (A := B[X]),
    trdeg_eq_zero (R := FX) (A := B), Polynomial.trdeg_of_isDomain, zero_add] at hdim
  have hbad : (2 : Cardinal.{0}) ≤ 1 := by
    simpa only [Cardinal.lift_id, Cardinal.mk_fin, Nat.cast_ofNat] using hdim
  have hn : (2 : ℕ) ≤ 1 := by exact_mod_cast hbad
  omega

private theorem seedImage_height (I : Ideal Ambient) [I.IsPrime] [Nontrivial (JetSeedSection I)]
    [Module.Finite SeedField (JetSeedSection I)] : (seedImage I).height = 1 := by
  let P := seedImage I
  let : P.IsPrime := seedImage_prime I
  have hP0 : (⊥ : Ideal Seeds) < P := bot_lt_iff_ne_bot.mpr (seedImage_ne_bot I)
  have hlo : 1 ≤ P.height := by
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime hP0
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal (Ideal.IsPrime.ne_top ‹P.IsPrime›)
  let : M.IsPrime := hM.isPrime
  have hlt : P < M := lt_of_le_of_ne hPM (by
    intro h
    have hmax : P.IsMaximal := by rw [h]; exact hM
    exact seedImage_not_maximal I hmax)
  have hdim : ringKrullDim Seeds = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num [Nat.card_eq_fintype_card]
  have hhi : M.height ≤ 2 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hP := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hhi
  have hle : P.height ≤ 1 :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hP
  exact hle.antisymm hlo

theorem proof : K1_14_2_3.c1 := by
  intro I h
  let : I.IsPrime := h.1
  let : Module.Finite SeedField (JetSeedSection I) := h.2.2.1
  let : Nontrivial (JetSeedSection I) := Module.nontrivial_of_finrank_pos h.2.2.2
  let P := seedImage I
  let : P.IsPrime := seedImage_prime I
  have : UniqueFactorizationMonoid FX := PrincipalIdealRing.to_uniqueFactorizationMonoid
  have : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨F, hmem, hprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (seedImage_prime I) (seedImage_ne_bot I)
  have hspan : P = Ideal.span {F} :=
    Ideal.eq_span_singleton_of_height_eq_one (seedImage_height I) hmem hprime
  refine ⟨F, hprime.irreducible, hspan, ?_, ?_⟩
  · by_contra! hz
    have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hz)
    have hc : F.coeff 0 ≠ 0 := by
      intro h0
      exact hprime.ne_zero (by simpa [h0] using he)
    exact hprime.not_isUnit (he ▸ hc.isUnit.map MvPolynomial.C)
  · have hbound := LinearMap.finrank_le_finrank_of_injective
      (f := (planeToJet I).toLinearMap) (planeToJet_injective I)
    have hd : Module.finrank SeedField (PlaneSlice P) = F.totalDegree := by
      rw [(lineQuotientEquiv P).toLinearEquiv.finrank_eq, hspan, Ideal.map_span, Set.image_singleton,
        finrank_quotient_span_eq_natDegree, totalDegree_lineRestriction]
    exact hd ▸ hbound

end
end K1_14_2_3_1
end PackSource_K1_14_2_3_1Proof

section PackSource_K1_14_2_2_3_2Proof
set_option autoImplicit true
namespace K1_14_2_2_3_2

open K1_14_2_2

theorem proof : K1_14_2_2_3.c2 := by
  intro I hI hd
  obtain ⟨g, hg, hIg⟩ := primeGenerator hI hd
  exact ⟨g, hg, (degree_le_mixed hI g hg.ne_zero hIg).trans_lt hI.mixed_lt, hIg⟩

end K1_14_2_2_3_2
end PackSource_K1_14_2_2_3_2Proof

section PackSource_K1_13_1_1BudgetD
set_option autoImplicit true
namespace K1_13_1_1

set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000

open private sumToCap_eq innerSlice_eq sumRange_suffix sumRange_congr sumRange_zero natLine_zero
  activeNatCount_eq sumRange_prefix sumRange_succ_left
  from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

-- With residual degree 48 the two arguments of the Pascal minimum have
-- different monotonicity.  The active count only depends on the lower index.
private def dActive (lo : ℕ) : ℕ := activeNatCount 48 lo 48

private def dTarget (lo o : ℕ) : ℕ :=
  sumRange 49 fun b =>
    min (natPairs 48 lo b) (sumRange (48 - b + 1) (natLine 48 lo o b))

-- The original evaluator skips the zero prefix of each slice.  Use it for
-- the few endpoint checks and the full target sum for the monotonicity proof.
private def dCapped (lo o cap : ℕ) : ℕ :=
  let startB := 49 - o
  sumToCap (fun b =>
    let startC := 2 * (48 - b) + 1 - o
    sumToCap (natLine 48 lo o b) (48 - b + 1 - startC) startC (natPairs 48 lo b))
    (49 - startB) startB cap

private theorem dCapped_eq (lo o cap : ℕ) :
    dCapped lo o cap = min cap (dTarget lo o) := by
  unfold dCapped dTarget
  rw [sumToCap_eq]
  congr 1
  symm
  rw [sumRange_suffix 49 (49 - o) _ (Nat.sub_le _ _)]
  · apply sumRange_congr
    intro i hi
    exact (innerSlice_eq 48 lo o (i + (49 - o)) (by omega)).symm
  · intro b hb
    have hz : sumRange (48 - b + 1) (natLine 48 lo o b) = 0 := by
      apply sumRange_zero
      intro c hc
      exact natLine_zero 48 lo o b c (by omega) (by omega)
    simp [hz]

private theorem dSumMono (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact Nat.add_le_add ih (h n)

private theorem dActive_antitone {u v : ℕ} (h : u ≤ v) : dActive v ≤ dActive u := by
  unfold dActive activeNatCount
  apply dSumMono
  intro f
  apply dSumMono
  intro c
  exact Nat.sub_le_sub_left (Nat.sub_le_sub_right h _) _

private theorem dTarget_mono {l₁ l₂ o₁ o₂ : ℕ} (hl : l₂ ≤ l₁) (ho : o₁ ≤ o₂) :
    dTarget l₁ o₁ ≤ dTarget l₂ o₂ := by
  unfold dTarget
  apply dSumMono
  intro b
  apply min_le_min
  · unfold natPairs
    apply dSumMono
    intro f
    apply Nat.sub_le_sub_left
    omega
  · apply dSumMono
    intro c
    unfold natLine
    dsimp only
    have hf : (l₂ - (b + 2 * min c 24) + 2) / 3 ≤
        (l₁ - (b + 2 * min c 24) + 2) / 3 := by omega
    apply min_le_min (Nat.sub_le_sub_left hf _)
    apply Nat.sub_le_sub_left
    exact max_le_max hf (by omega)

-- Entries occupy disjoint twelve-bit fields.  All endpoint values are
-- compared to the extracted numerals by kernel reduction below.
private def dField (data i : ℕ) : ℕ := (data >>> (12 * i)) % 4096

private def dActiveVal := dField 0xbe1762292d637e4204bd5545e66726f977a7f686c8dd9489aea0ea69abeb0eb59b9fbe0c1dc55c89cb9ce5d0dd32d53d71d8cda4db9dccddcdeadf6e00e08e0fe14e18e1be1de1ee1f

private def dTargetVal := dField 0xd61ca9bf6b49aa19ff9628cb8397ad7266a56295b35424d74714113b63613112c628023f2021ca19616613a1120ed0cc0ae09307b06605304303502901f01701000b007004002001000


private theorem dActiveTable : ∀ i : Fin 49, dActive i = dActiveVal i := by decide +kernel

-- When the order is below 49 the degree and order bounds alone determine
-- each target line. An active line already satisfies the lower-index cutoff.
private def dLine (o b c : ℕ) : ℕ :=
  min 11 (min (49 - b - c) (2 * b + c + o - 96))

private theorem dLine_eq (lo o b c : ℕ) (hl : lo ≤ 19) (ho : o ≤ 48) (hbc : b + c ≤ 48) :
    natLine 48 lo o b c = dLine o b c := by
  have hrow : 49 - b - c - (145 - (3 * b + 2 * c + o)) =
      min (49 - b - c) (2 * b + c + o - 96) := by omega
  have hx : 48 - b - c + 1 = 49 - b - c := by omega
  unfold natLine dLine
  dsimp only
  by_cases h : lo ≤ b + 2 * min c 24
  · have hf : (lo - (b + 2 * min c 24) + 2) / 3 = 0 := by omega
    simp only [hf, hx, Nat.sub_zero, Nat.zero_max]
    exact congrArg (min 11) hrow
  · have hz : 2 * b + c + o ≤ 96 := by omega
    have hle : 49 - b - c ≤ 145 - (3 * b + 2 * c + o) := by omega
    have hempty : 49 - b - c ≤ max ((lo - (b + 2 * min c 24) + 2) / 3)
        (145 - (3 * b + 2 * c + o)) := hle.trans (le_max_right _ _)
    simp only [hx, Nat.sub_eq_zero_of_le hz, Nat.sub_eq_zero_of_le hempty, Nat.min_zero]


private def dLines (o b : ℕ) := sumRange (49 - b) (dLine o b)

-- Check the most restrictive pair cap at the largest order in this range.
private theorem dPairCover : ∀ b : Fin 49, dLines 48 b ≤ natPairs 48 19 b := by decide +kernel

private theorem dSlice_eq (lo o b : ℕ) (hl : lo ≤ 19) (ho : o ≤ 48) (hb : b < 49) :
    min (natPairs 48 lo b) (sumRange (48 - b + 1) (natLine 48 lo o b)) = dLines o b := by
  have hn : 48 - b + 1 = 49 - b := by omega
  rw [hn, show sumRange (49 - b) (natLine 48 lo o b) = dLines o b from
    sumRange_congr _ fun c hc => dLine_eq lo o b c hl ho (by omega)]
  apply min_eq_right
  calc
    dLines o b ≤ dLines 48 b := by
      apply dSumMono
      intro c
      unfold dLine
      exact min_le_min_left _ (min_le_min_left _ (by omega))
    _ ≤ natPairs 48 19 b := dPairCover ⟨b, hb⟩
    _ ≤ natPairs 48 lo b := by
      unfold natPairs
      apply dSumMono
      intro f
      apply Nat.sub_le_sub_left
      omega

-- The first possible nonzero slice and line follow from the order bound.
private def dShortTarget (o : ℕ) : ℕ :=
  let start := 49 - o
  sumRange o fun i =>
    let b := i + start
    let first := 97 - (2 * b + o)
    sumRange (49 - b - first) fun j => dLine o b (j + first)

private theorem dTarget_short (lo o : ℕ) (hl : lo ≤ 19) (ho : o ≤ 48) :
    dTarget lo o = dShortTarget o := by
  have h : dTarget lo o = sumRange 49 (dLines o) :=
    sumRange_congr _ fun b hb => dSlice_eq lo o b hl ho hb
  rw [h, sumRange_suffix 49 (49 - o) _ (Nat.sub_le _ _)]
  · rw [show 49 - (49 - o) = o by omega]
    apply sumRange_congr
    intro i hi
    unfold dLines
    apply sumRange_suffix
    · omega
    · intro c hc
      unfold dLine
      omega
  · intro b hb
    unfold dLines
    apply sumRange_zero
    intro c hc
    unfold dLine
    omega

-- A row has rising heights t+j, falling heights n-j and height cap 11.
-- The uncapped area is a triangle minus the terms (n-t), (n-t-2), ...
-- The portion above height 11 is another uncapped triangle.
private def dUncappedArea (n t : ℕ) : ℕ :=
  let d := n - t
  n * (n + 1) / 2 - ((d + 1) / 2) * ((d + 2) / 2)

private def dRowArea (n t : ℕ) : ℕ :=
  dUncappedArea n t - dUncappedArea (n + t - 22) 0

private def dRowSum (n t : ℕ) : ℕ :=
  sumRange n fun j => min 11 (min (n - j) (t + j))

-- The kernel checks the first-column recurrence over the entire domain.
private theorem dAreaStep : ∀ (n : Fin 49) (t : Fin 12),
    dRowArea (n.val + 1) t.val =
      min 11 (min (n.val + 1) t.val) + dRowArea n.val (min 11 (t.val + 1)) := by
  decide +kernel

private theorem dRow_sum_step (n t : ℕ) :
    dRowSum (n + 1) t = min 11 (min (n + 1) t) + dRowSum n (t + 1) := by
  unfold dRowSum
  rw [sumRange_succ_left]
  congr 1
  apply sumRange_congr
  intro i hi
  rw [show n + 1 - (i + 1) = n - i by omega, show t + (i + 1) = t + 1 + i by omega]

private theorem dRowArea_eq (n t : ℕ) (hn : n ≤ 49) :
    dRowSum n t = dRowArea n (min 11 t) := by
  induction n generalizing t with
  | zero => simp [dRowSum, sumRange, dRowArea, dUncappedArea]
  | succ n ih =>
    rw [dRow_sum_step, ih (t + 1) (by omega)]
    have h := dAreaStep ⟨n, by omega⟩ ⟨min 11 t, by omega⟩
    change dRowArea (n + 1) (min 11 t) =
      min 11 (min (n + 1) (min 11 t)) + dRowArea n (min 11 (min 11 t + 1)) at h
    rw [show min 11 (min (n + 1) (min 11 t)) = min 11 (min (n + 1) t) by omega,
      show min 11 (min 11 t + 1) = min 11 (t + 1) by omega] at h
    exact h.symm

private def dAreaTarget (o : ℕ) : ℕ :=
  sumRange o fun i =>
    let b := i + (49 - o)
    let first := 97 - (2 * b + o)
    dRowArea (49 - b - first) (min 11 (2 * b + o + first - 96))

private theorem dAreaTarget_eq (o : ℕ) : dShortTarget o = dAreaTarget o := by
  unfold dShortTarget dAreaTarget
  apply sumRange_congr
  intro i hi
  dsimp only
  generalize i + (49 - o) = b
  let first := 97 - (2 * b + o)
  change sumRange (49 - b - first) (fun j => dLine o b (j + first)) =
    dRowArea (49 - b - first) (min 11 (2 * b + o + first - 96))
  rw [← dRowArea_eq _ _ (by omega)]
  apply sumRange_congr
  intro j hj
  unfold dLine
  rw [show 49 - b - (j + first) = 49 - b - first - j by omega,
    show 2 * b + (j + first) + o - 96 = 2 * b + o + first - 96 + j by dsimp [first]; omega]

private theorem dShortTable : ∀ i : Fin 49, dAreaTarget i = dTargetVal i := by decide +kernel

private theorem dTarget_small (lo o : ℕ) (ho : o < 49) (hl : lo ≤ o - 29) :
    dTarget lo o = dTargetVal o := by
  rw [dTarget_short _ _ (by omega) (by omega), dAreaTarget_eq]
  exact dShortTable ⟨o, ho⟩

private theorem dFullLow : dCapped 24 49 3615 = 3615 := by decide +kernel
private theorem dFullHigh : dCapped 48 49 3040 = 3040 := by decide +kernel

private theorem dTarget_large (lo o : ℕ) (hl : lo ≤ 48) (ho : 49 ≤ o) :
    dActive lo ≤ dTarget lo o := by
  by_cases h : lo ≤ 24
  · have h₁ := dFullLow
    rw [dCapped_eq] at h₁
    have h₂ : dActive lo ≤ dActive 0 := dActive_antitone (Nat.zero_le _)
    have h₃ : dActive 0 = 3615 := dActiveTable 0
    have h₄ : dTarget 24 49 ≤ dTarget lo o := dTarget_mono h ho
    omega
  · have h₁ := dFullHigh
    rw [dCapped_eq] at h₁
    have h₂ : dActive lo ≤ dActive 25 := dActive_antitone (by omega)
    have h₃ : dActive 25 = 3040 := dActiveTable 25
    have h₄ : dTarget 48 49 ≤ dTarget lo o := dTarget_mono hl ho
    omega

private def dPascal (s r : ℕ) : ℕ :=
  let lo := 48 - r
  let o := 138 - (s + r)
  if o < 49 then min (dActiveVal lo) (dTargetVal o) else dActiveVal lo

private theorem dPascal_eq (s r : ℕ) (hs : 49 ≤ s) (hs' : s ≤ 61) (hr : s + r < 138) :
    fastPascal s r = dPascal s r := by
  have hd : residualDegree s = 48 := by unfold residualDegree; omega
  have hh : min 48 (137 - r) = 48 := by omega
  unfold fastPascal
  rw [hd, hh]
  change dCapped (48 - r) (138 - (s + r)) (dActive (48 - r)) = _
  rw [dCapped_eq]
  unfold dPascal
  dsimp only
  have ha := dActiveTable ⟨48 - r, by omega⟩
  change dActive (48 - r) = dActiveVal (48 - r) at ha
  split
  · rename_i h
    rw [ha, dTarget_small _ _ h (by omega)]
  · rename_i h
    rw [min_eq_left (dTarget_large _ _ (Nat.sub_le _ _) (by omega)), ha]

-- Both integer counts use the size of an interval. Its upper endpoint plus
-- one and its lower endpoint can be clipped to naturals before subtraction.
private theorem dIntervalNat (l a b : ℤ) :
    intervalSize (max 0 l) (min a b) = min (a + 1).toNat (b + 1).toNat - l.toNat := by
  unfold intervalSize
  omega

private def dBand (d lo upper top : ℕ) : ℕ :=
  sumRange (min d top + 1) fun f =>
    sumRange (min (d - f) ((upper - 1 - 3 * f) / 2) + 1) fun c =>
      min (d - f - c + 1) (upper - (2 * c + 3 * f)) - (lo - (2 * c + 3 * f))

private theorem dBand_eq (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    bandCount d lo hi top = dBand d lo.toNat (hi + 1).toNat top := by
  unfold bandCount dBand
  apply sumRange_congr
  intro f hf
  have hdiv : ((hi - 3 * (f : ℤ)) / 2).toNat = ((hi + 1).toNat - 1 - 3 * f) / 2 := by omega
  rw [hdiv]
  apply sumRange_congr
  intro c hc
  rw [dIntervalNat]
  have h₁ : ((d : ℤ) - f - c + 1).toNat = d - f - c + 1 := by omega
  have h₂ : (hi - 2 * c - 3 * f + 1).toNat = (hi + 1).toNat - (2 * c + 3 * f : ℕ) := by omega
  have h₃ : (lo - 2 * c - 3 * f).toNat = lo.toNat - (2 * c + 3 * f : ℕ) := by omega
  rw [h₁, h₂, h₃]

private def dCount (d lo upper : ℕ) : ℕ :=
  sumRange (d + 1) fun a =>
    let x := d - a
    let u := upper - 3 * a
    sumRange (min (x + 1) ((u + 1) / 2)) fun f =>
      min (x + 1 - f) (u - 2 * f) - (lo - (x + 2 * f))

private theorem dCount_eq (d : ℕ) (lo o : ℤ) :
    targetCount d lo o = dCount d lo.toNat o.toNat := by
  unfold targetCount dCount
  apply sumRange_congr
  intro a ha
  dsimp only
  rw [sumRange_prefix (d - a + 1) (min (d - a + 1) ((o.toNat - 3 * a + 1) / 2)) _
    (Nat.min_le_left _ _)]
  · apply sumRange_congr
    intro f hf
    rw [dIntervalNat]
    have h₁ : ((d : ℤ) - a - f + 1).toNat = d - a + 1 - f := by omega
    have h₂ : (o - 1 - 3 * a - 2 * f + 1).toNat = o.toNat - 3 * a - 2 * f := by omega
    have h₃ : (lo - d + a - 2 * f).toNat = lo.toNat - (d - a + 2 * f : ℕ) := by omega
    rw [h₁, h₂, h₃]
  · intro f hlow hf
    rw [dIntervalNat]
    have h₂ : (o - 1 - 3 * a - 2 * f + 1).toNat = 0 := by omega
    simp only [h₂, Nat.min_zero, Nat.zero_sub]

private def dFlag (s r : ℕ) (v : FactorPowers) : ℕ :=
  let g := offset r
  let count := dActiveVal (48 - r)
  if v.degree ≤ 48 ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10 then
    let d' := 48 - v.degree
    let lo' := (-g - (v.minIndex : ℤ)).toNat
    let upper := ((48 : ℤ) - (v.maxIndex : ℤ) + 1).toNat
    let order := (orderCutoff s g - (v.minOrder : ℤ)).toNat
    count - (dBand d' lo' upper (10 - v.maxTop) - dCount d' lo' order)
  else count

private theorem dFlag_eq (s r : ℕ) (v : FactorPowers) (hs : 49 ≤ s) (hs' : s ≤ 61) :
    flagBound s (offset r) v = dFlag s r v := by
  have hd : residualDegree s = 48 := by unfold residualDegree; omega
  have ha : bandCount 48 (-(offset r)) 48 10 = dActiveVal (48 - r) := by
    rw [activeNatCount_eq 48 (-(offset r)) 48 (by decide)]
    have hl : (-(offset r)).toNat = 48 - r := by unfold offset; omega
    rw [hl]
    exact dActiveTable ⟨48 - r, by omega⟩
  simp only [flagBound, dFlag, hd, ha, dBand_eq, dCount_eq]

private def dBlock (s r : ℕ) : ℕ :=
  if s + r < 138 then
    match selectedFactors s (offset r) with
    | none => dPascal s r
    | some v => min (dPascal s r) (dFlag s r v)
  else 0

private theorem dBlock_eq (s r : ℕ) (hs : 49 ≤ s) (hs' : s ≤ 61) :
    fastBlock s r = dBlock s r := by
  unfold fastBlock dBlock
  by_cases hr : s + r < 138
  · cases h : selectedFactors s (offset r) <;> simp [hr, dPascal_eq s r hs hs' hr, dFlag_eq s r _ hs hs']
  · simp only [ite_eq_right hr]

private theorem dBlockSum_eq (s k n : ℕ) (hs : 49 ≤ s) (hs' : s ≤ 61) :
    sumRange n (fun i => fastBlock s (i + k)) = sumRange n (fun i => dBlock s (i + k)) :=
  sumRange_congr _ fun i _ => dBlock_eq s (i + k) hs hs'

-- Assemble independently checked runs of consecutive blocks.
private theorem budgetDAddRanges (a b : ℕ) (f : ℕ → ℕ) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (i + a)) := by
  induction b with
  | zero => exact (Nat.add_zero (sumRange a f)).symm
  | succ b ih =>
    change sumRange (a + b) f + f (a + b) =
      sumRange a f + (sumRange b (fun i => f (i + a)) + f (b + a))
    rw [ih, Nat.add_comm b a, Nat.add_assoc]

private theorem budgetDAppend (f : ℕ → ℕ) (start len lhs rhs : ℕ)
    (hp : sumRange start f = lhs)
    (hc : sumRange len (fun i => f (i + start)) = rhs) :
    sumRange (start + len) f = lhs + rhs :=
  (budgetDAddRanges start len f).trans (congrArg₂ Nat.add hp hc)

private theorem budgetDGrade49At0 :
    sumRange 4 (fun i => fastBlock 49 (i + 0)) = 1843 :=
  (dBlockSum_eq 49 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At4 :
    sumRange 4 (fun i => fastBlock 49 (i + 4)) = 4527 :=
  (dBlockSum_eq 49 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At8 :
    sumRange 4 (fun i => fastBlock 49 (i + 8)) = 6859 :=
  (dBlockSum_eq 49 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At12 :
    sumRange 4 (fun i => fastBlock 49 (i + 12)) = 8839 :=
  (dBlockSum_eq 49 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At16 :
    sumRange 4 (fun i => fastBlock 49 (i + 16)) = 10467 :=
  (dBlockSum_eq 49 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At20 :
    sumRange 4 (fun i => fastBlock 49 (i + 20)) = 11750 :=
  (dBlockSum_eq 49 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At24 :
    sumRange 4 (fun i => fastBlock 49 (i + 24)) = 12724 :=
  (dBlockSum_eq 49 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At28 :
    sumRange 4 (fun i => fastBlock 49 (i + 28)) = 13431 :=
  (dBlockSum_eq 49 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At32 :
    sumRange 4 (fun i => fastBlock 49 (i + 32)) = 13914 :=
  (dBlockSum_eq 49 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At36 :
    sumRange 4 (fun i => fastBlock 49 (i + 36)) = 14216 :=
  (dBlockSum_eq 49 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At40 :
    sumRange 4 (fun i => fastBlock 49 (i + 40)) = 13312 :=
  (dBlockSum_eq 49 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At44 :
    sumRange 4 (fun i => fastBlock 49 (i + 44)) = 10571 :=
  (dBlockSum_eq 49 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At48 :
    sumRange 4 (fun i => fastBlock 49 (i + 48)) = 8151 :=
  (dBlockSum_eq 49 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At52 :
    sumRange 4 (fun i => fastBlock 49 (i + 52)) = 6083 :=
  (dBlockSum_eq 49 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At56 :
    sumRange 4 (fun i => fastBlock 49 (i + 56)) = 4367 :=
  (dBlockSum_eq 49 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At60 :
    sumRange 4 (fun i => fastBlock 49 (i + 60)) = 3000 :=
  (dBlockSum_eq 49 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At64 :
    sumRange 4 (fun i => fastBlock 49 (i + 64)) = 1953 :=
  (dBlockSum_eq 49 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At68 :
    sumRange 4 (fun i => fastBlock 49 (i + 68)) = 1183 :=
  (dBlockSum_eq 49 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At72 :
    sumRange 4 (fun i => fastBlock 49 (i + 72)) = 648 :=
  (dBlockSum_eq 49 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At76 :
    sumRange 4 (fun i => fastBlock 49 (i + 76)) = 305 :=
  (dBlockSum_eq 49 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At80 :
    sumRange 4 (fun i => fastBlock 49 (i + 80)) = 111 :=
  (dBlockSum_eq 49 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At84 :
    sumRange 4 (fun i => fastBlock 49 (i + 84)) = 24 :=
  (dBlockSum_eq 49 84 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At88 :
    sumRange 4 (fun i => fastBlock 49 (i + 88)) = 1 :=
  (dBlockSum_eq 49 88 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade49At92 :
    sumRange 46 (fun i => fastBlock 49 (i + 92)) = 0 :=
  (dBlockSum_eq 49 92 46 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade49 : fastGrade 49 = 148279 := by
  have prefix4 : sumRange 4 (fastBlock 49) = 1843 :=
    budgetDAppend (fastBlock 49) 0 4 0 1843 rfl budgetDGrade49At0
  have prefix8 : sumRange 8 (fastBlock 49) = 6370 :=
    budgetDAppend (fastBlock 49) 4 4 1843 4527 prefix4 budgetDGrade49At4
  have prefix12 : sumRange 12 (fastBlock 49) = 13229 :=
    budgetDAppend (fastBlock 49) 8 4 6370 6859 prefix8 budgetDGrade49At8
  have prefix16 : sumRange 16 (fastBlock 49) = 22068 :=
    budgetDAppend (fastBlock 49) 12 4 13229 8839 prefix12 budgetDGrade49At12
  have prefix20 : sumRange 20 (fastBlock 49) = 32535 :=
    budgetDAppend (fastBlock 49) 16 4 22068 10467 prefix16 budgetDGrade49At16
  have prefix24 : sumRange 24 (fastBlock 49) = 44285 :=
    budgetDAppend (fastBlock 49) 20 4 32535 11750 prefix20 budgetDGrade49At20
  have prefix28 : sumRange 28 (fastBlock 49) = 57009 :=
    budgetDAppend (fastBlock 49) 24 4 44285 12724 prefix24 budgetDGrade49At24
  have prefix32 : sumRange 32 (fastBlock 49) = 70440 :=
    budgetDAppend (fastBlock 49) 28 4 57009 13431 prefix28 budgetDGrade49At28
  have prefix36 : sumRange 36 (fastBlock 49) = 84354 :=
    budgetDAppend (fastBlock 49) 32 4 70440 13914 prefix32 budgetDGrade49At32
  have prefix40 : sumRange 40 (fastBlock 49) = 98570 :=
    budgetDAppend (fastBlock 49) 36 4 84354 14216 prefix36 budgetDGrade49At36
  have prefix44 : sumRange 44 (fastBlock 49) = 111882 :=
    budgetDAppend (fastBlock 49) 40 4 98570 13312 prefix40 budgetDGrade49At40
  have prefix48 : sumRange 48 (fastBlock 49) = 122453 :=
    budgetDAppend (fastBlock 49) 44 4 111882 10571 prefix44 budgetDGrade49At44
  have prefix52 : sumRange 52 (fastBlock 49) = 130604 :=
    budgetDAppend (fastBlock 49) 48 4 122453 8151 prefix48 budgetDGrade49At48
  have prefix56 : sumRange 56 (fastBlock 49) = 136687 :=
    budgetDAppend (fastBlock 49) 52 4 130604 6083 prefix52 budgetDGrade49At52
  have prefix60 : sumRange 60 (fastBlock 49) = 141054 :=
    budgetDAppend (fastBlock 49) 56 4 136687 4367 prefix56 budgetDGrade49At56
  have prefix64 : sumRange 64 (fastBlock 49) = 144054 :=
    budgetDAppend (fastBlock 49) 60 4 141054 3000 prefix60 budgetDGrade49At60
  have prefix68 : sumRange 68 (fastBlock 49) = 146007 :=
    budgetDAppend (fastBlock 49) 64 4 144054 1953 prefix64 budgetDGrade49At64
  have prefix72 : sumRange 72 (fastBlock 49) = 147190 :=
    budgetDAppend (fastBlock 49) 68 4 146007 1183 prefix68 budgetDGrade49At68
  have prefix76 : sumRange 76 (fastBlock 49) = 147838 :=
    budgetDAppend (fastBlock 49) 72 4 147190 648 prefix72 budgetDGrade49At72
  have prefix80 : sumRange 80 (fastBlock 49) = 148143 :=
    budgetDAppend (fastBlock 49) 76 4 147838 305 prefix76 budgetDGrade49At76
  have prefix84 : sumRange 84 (fastBlock 49) = 148254 :=
    budgetDAppend (fastBlock 49) 80 4 148143 111 prefix80 budgetDGrade49At80
  have prefix88 : sumRange 88 (fastBlock 49) = 148278 :=
    budgetDAppend (fastBlock 49) 84 4 148254 24 prefix84 budgetDGrade49At84
  have prefix92 : sumRange 92 (fastBlock 49) = 148279 :=
    budgetDAppend (fastBlock 49) 88 4 148278 1 prefix88 budgetDGrade49At88
  have prefix138 : sumRange 138 (fastBlock 49) = 148279 :=
    budgetDAppend (fastBlock 49) 92 46 148279 0 prefix92 budgetDGrade49At92
  exact prefix138

private theorem budgetDGrade50At0 :
    sumRange 4 (fun i => fastBlock 50 (i + 0)) = 1843 :=
  (dBlockSum_eq 50 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At4 :
    sumRange 4 (fun i => fastBlock 50 (i + 4)) = 4527 :=
  (dBlockSum_eq 50 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At8 :
    sumRange 4 (fun i => fastBlock 50 (i + 8)) = 6859 :=
  (dBlockSum_eq 50 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At12 :
    sumRange 4 (fun i => fastBlock 50 (i + 12)) = 8839 :=
  (dBlockSum_eq 50 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At16 :
    sumRange 4 (fun i => fastBlock 50 (i + 16)) = 10467 :=
  (dBlockSum_eq 50 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At20 :
    sumRange 4 (fun i => fastBlock 50 (i + 20)) = 11750 :=
  (dBlockSum_eq 50 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At24 :
    sumRange 4 (fun i => fastBlock 50 (i + 24)) = 12724 :=
  (dBlockSum_eq 50 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At28 :
    sumRange 4 (fun i => fastBlock 50 (i + 28)) = 13431 :=
  (dBlockSum_eq 50 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At32 :
    sumRange 4 (fun i => fastBlock 50 (i + 32)) = 13914 :=
  (dBlockSum_eq 50 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At36 :
    sumRange 4 (fun i => fastBlock 50 (i + 36)) = 14216 :=
  (dBlockSum_eq 50 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At40 :
    sumRange 4 (fun i => fastBlock 50 (i + 40)) = 12617 :=
  (dBlockSum_eq 50 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At44 :
    sumRange 4 (fun i => fastBlock 50 (i + 44)) = 9933 :=
  (dBlockSum_eq 50 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At48 :
    sumRange 4 (fun i => fastBlock 50 (i + 48)) = 7601 :=
  (dBlockSum_eq 50 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At52 :
    sumRange 4 (fun i => fastBlock 50 (i + 52)) = 5621 :=
  (dBlockSum_eq 50 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At56 :
    sumRange 4 (fun i => fastBlock 50 (i + 56)) = 3993 :=
  (dBlockSum_eq 50 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At60 :
    sumRange 4 (fun i => fastBlock 50 (i + 60)) = 2710 :=
  (dBlockSum_eq 50 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At64 :
    sumRange 4 (fun i => fastBlock 50 (i + 64)) = 1736 :=
  (dBlockSum_eq 50 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At68 :
    sumRange 4 (fun i => fastBlock 50 (i + 68)) = 1029 :=
  (dBlockSum_eq 50 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At72 :
    sumRange 4 (fun i => fastBlock 50 (i + 72)) = 546 :=
  (dBlockSum_eq 50 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At76 :
    sumRange 4 (fun i => fastBlock 50 (i + 76)) = 244 :=
  (dBlockSum_eq 50 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At80 :
    sumRange 4 (fun i => fastBlock 50 (i + 80)) = 81 :=
  (dBlockSum_eq 50 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At84 :
    sumRange 4 (fun i => fastBlock 50 (i + 84)) = 14 :=
  (dBlockSum_eq 50 84 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade50At88 :
    sumRange 50 (fun i => fastBlock 50 (i + 88)) = 0 :=
  (dBlockSum_eq 50 88 50 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade50 : fastGrade 50 = 144695 := by
  have prefix4 : sumRange 4 (fastBlock 50) = 1843 :=
    budgetDAppend (fastBlock 50) 0 4 0 1843 rfl budgetDGrade50At0
  have prefix8 : sumRange 8 (fastBlock 50) = 6370 :=
    budgetDAppend (fastBlock 50) 4 4 1843 4527 prefix4 budgetDGrade50At4
  have prefix12 : sumRange 12 (fastBlock 50) = 13229 :=
    budgetDAppend (fastBlock 50) 8 4 6370 6859 prefix8 budgetDGrade50At8
  have prefix16 : sumRange 16 (fastBlock 50) = 22068 :=
    budgetDAppend (fastBlock 50) 12 4 13229 8839 prefix12 budgetDGrade50At12
  have prefix20 : sumRange 20 (fastBlock 50) = 32535 :=
    budgetDAppend (fastBlock 50) 16 4 22068 10467 prefix16 budgetDGrade50At16
  have prefix24 : sumRange 24 (fastBlock 50) = 44285 :=
    budgetDAppend (fastBlock 50) 20 4 32535 11750 prefix20 budgetDGrade50At20
  have prefix28 : sumRange 28 (fastBlock 50) = 57009 :=
    budgetDAppend (fastBlock 50) 24 4 44285 12724 prefix24 budgetDGrade50At24
  have prefix32 : sumRange 32 (fastBlock 50) = 70440 :=
    budgetDAppend (fastBlock 50) 28 4 57009 13431 prefix28 budgetDGrade50At28
  have prefix36 : sumRange 36 (fastBlock 50) = 84354 :=
    budgetDAppend (fastBlock 50) 32 4 70440 13914 prefix32 budgetDGrade50At32
  have prefix40 : sumRange 40 (fastBlock 50) = 98570 :=
    budgetDAppend (fastBlock 50) 36 4 84354 14216 prefix36 budgetDGrade50At36
  have prefix44 : sumRange 44 (fastBlock 50) = 111187 :=
    budgetDAppend (fastBlock 50) 40 4 98570 12617 prefix40 budgetDGrade50At40
  have prefix48 : sumRange 48 (fastBlock 50) = 121120 :=
    budgetDAppend (fastBlock 50) 44 4 111187 9933 prefix44 budgetDGrade50At44
  have prefix52 : sumRange 52 (fastBlock 50) = 128721 :=
    budgetDAppend (fastBlock 50) 48 4 121120 7601 prefix48 budgetDGrade50At48
  have prefix56 : sumRange 56 (fastBlock 50) = 134342 :=
    budgetDAppend (fastBlock 50) 52 4 128721 5621 prefix52 budgetDGrade50At52
  have prefix60 : sumRange 60 (fastBlock 50) = 138335 :=
    budgetDAppend (fastBlock 50) 56 4 134342 3993 prefix56 budgetDGrade50At56
  have prefix64 : sumRange 64 (fastBlock 50) = 141045 :=
    budgetDAppend (fastBlock 50) 60 4 138335 2710 prefix60 budgetDGrade50At60
  have prefix68 : sumRange 68 (fastBlock 50) = 142781 :=
    budgetDAppend (fastBlock 50) 64 4 141045 1736 prefix64 budgetDGrade50At64
  have prefix72 : sumRange 72 (fastBlock 50) = 143810 :=
    budgetDAppend (fastBlock 50) 68 4 142781 1029 prefix68 budgetDGrade50At68
  have prefix76 : sumRange 76 (fastBlock 50) = 144356 :=
    budgetDAppend (fastBlock 50) 72 4 143810 546 prefix72 budgetDGrade50At72
  have prefix80 : sumRange 80 (fastBlock 50) = 144600 :=
    budgetDAppend (fastBlock 50) 76 4 144356 244 prefix76 budgetDGrade50At76
  have prefix84 : sumRange 84 (fastBlock 50) = 144681 :=
    budgetDAppend (fastBlock 50) 80 4 144600 81 prefix80 budgetDGrade50At80
  have prefix88 : sumRange 88 (fastBlock 50) = 144695 :=
    budgetDAppend (fastBlock 50) 84 4 144681 14 prefix84 budgetDGrade50At84
  have prefix138 : sumRange 138 (fastBlock 50) = 144695 :=
    budgetDAppend (fastBlock 50) 88 50 144695 0 prefix88 budgetDGrade50At88
  exact prefix138

private theorem budgetDGrade51At0 :
    sumRange 4 (fun i => fastBlock 51 (i + 0)) = 1843 :=
  (dBlockSum_eq 51 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At4 :
    sumRange 4 (fun i => fastBlock 51 (i + 4)) = 4527 :=
  (dBlockSum_eq 51 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At8 :
    sumRange 4 (fun i => fastBlock 51 (i + 8)) = 6859 :=
  (dBlockSum_eq 51 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At12 :
    sumRange 4 (fun i => fastBlock 51 (i + 12)) = 8839 :=
  (dBlockSum_eq 51 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At16 :
    sumRange 4 (fun i => fastBlock 51 (i + 16)) = 10467 :=
  (dBlockSum_eq 51 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At20 :
    sumRange 4 (fun i => fastBlock 51 (i + 20)) = 11750 :=
  (dBlockSum_eq 51 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At24 :
    sumRange 4 (fun i => fastBlock 51 (i + 24)) = 12724 :=
  (dBlockSum_eq 51 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At28 :
    sumRange 4 (fun i => fastBlock 51 (i + 28)) = 13431 :=
  (dBlockSum_eq 51 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At32 :
    sumRange 4 (fun i => fastBlock 51 (i + 32)) = 13914 :=
  (dBlockSum_eq 51 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At36 :
    sumRange 4 (fun i => fastBlock 51 (i + 36)) = 14067 :=
  (dBlockSum_eq 51 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At40 :
    sumRange 4 (fun i => fastBlock 51 (i + 40)) = 11913 :=
  (dBlockSum_eq 51 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At44 :
    sumRange 4 (fun i => fastBlock 51 (i + 44)) = 9317 :=
  (dBlockSum_eq 51 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At48 :
    sumRange 4 (fun i => fastBlock 51 (i + 48)) = 7073 :=
  (dBlockSum_eq 51 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At52 :
    sumRange 4 (fun i => fastBlock 51 (i + 52)) = 5181 :=
  (dBlockSum_eq 51 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At56 :
    sumRange 4 (fun i => fastBlock 51 (i + 56)) = 3641 :=
  (dBlockSum_eq 51 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At60 :
    sumRange 4 (fun i => fastBlock 51 (i + 60)) = 2439 :=
  (dBlockSum_eq 51 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At64 :
    sumRange 4 (fun i => fastBlock 51 (i + 64)) = 1536 :=
  (dBlockSum_eq 51 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At68 :
    sumRange 4 (fun i => fastBlock 51 (i + 68)) = 889 :=
  (dBlockSum_eq 51 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At72 :
    sumRange 4 (fun i => fastBlock 51 (i + 72)) = 455 :=
  (dBlockSum_eq 51 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At76 :
    sumRange 4 (fun i => fastBlock 51 (i + 76)) = 192 :=
  (dBlockSum_eq 51 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At80 :
    sumRange 4 (fun i => fastBlock 51 (i + 80)) = 57 :=
  (dBlockSum_eq 51 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At84 :
    sumRange 4 (fun i => fastBlock 51 (i + 84)) = 7 :=
  (dBlockSum_eq 51 84 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade51At88 :
    sumRange 50 (fun i => fastBlock 51 (i + 88)) = 0 :=
  (dBlockSum_eq 51 88 50 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade51 : fastGrade 51 = 141121 := by
  have prefix4 : sumRange 4 (fastBlock 51) = 1843 :=
    budgetDAppend (fastBlock 51) 0 4 0 1843 rfl budgetDGrade51At0
  have prefix8 : sumRange 8 (fastBlock 51) = 6370 :=
    budgetDAppend (fastBlock 51) 4 4 1843 4527 prefix4 budgetDGrade51At4
  have prefix12 : sumRange 12 (fastBlock 51) = 13229 :=
    budgetDAppend (fastBlock 51) 8 4 6370 6859 prefix8 budgetDGrade51At8
  have prefix16 : sumRange 16 (fastBlock 51) = 22068 :=
    budgetDAppend (fastBlock 51) 12 4 13229 8839 prefix12 budgetDGrade51At12
  have prefix20 : sumRange 20 (fastBlock 51) = 32535 :=
    budgetDAppend (fastBlock 51) 16 4 22068 10467 prefix16 budgetDGrade51At16
  have prefix24 : sumRange 24 (fastBlock 51) = 44285 :=
    budgetDAppend (fastBlock 51) 20 4 32535 11750 prefix20 budgetDGrade51At20
  have prefix28 : sumRange 28 (fastBlock 51) = 57009 :=
    budgetDAppend (fastBlock 51) 24 4 44285 12724 prefix24 budgetDGrade51At24
  have prefix32 : sumRange 32 (fastBlock 51) = 70440 :=
    budgetDAppend (fastBlock 51) 28 4 57009 13431 prefix28 budgetDGrade51At28
  have prefix36 : sumRange 36 (fastBlock 51) = 84354 :=
    budgetDAppend (fastBlock 51) 32 4 70440 13914 prefix32 budgetDGrade51At32
  have prefix40 : sumRange 40 (fastBlock 51) = 98421 :=
    budgetDAppend (fastBlock 51) 36 4 84354 14067 prefix36 budgetDGrade51At36
  have prefix44 : sumRange 44 (fastBlock 51) = 110334 :=
    budgetDAppend (fastBlock 51) 40 4 98421 11913 prefix40 budgetDGrade51At40
  have prefix48 : sumRange 48 (fastBlock 51) = 119651 :=
    budgetDAppend (fastBlock 51) 44 4 110334 9317 prefix44 budgetDGrade51At44
  have prefix52 : sumRange 52 (fastBlock 51) = 126724 :=
    budgetDAppend (fastBlock 51) 48 4 119651 7073 prefix48 budgetDGrade51At48
  have prefix56 : sumRange 56 (fastBlock 51) = 131905 :=
    budgetDAppend (fastBlock 51) 52 4 126724 5181 prefix52 budgetDGrade51At52
  have prefix60 : sumRange 60 (fastBlock 51) = 135546 :=
    budgetDAppend (fastBlock 51) 56 4 131905 3641 prefix56 budgetDGrade51At56
  have prefix64 : sumRange 64 (fastBlock 51) = 137985 :=
    budgetDAppend (fastBlock 51) 60 4 135546 2439 prefix60 budgetDGrade51At60
  have prefix68 : sumRange 68 (fastBlock 51) = 139521 :=
    budgetDAppend (fastBlock 51) 64 4 137985 1536 prefix64 budgetDGrade51At64
  have prefix72 : sumRange 72 (fastBlock 51) = 140410 :=
    budgetDAppend (fastBlock 51) 68 4 139521 889 prefix68 budgetDGrade51At68
  have prefix76 : sumRange 76 (fastBlock 51) = 140865 :=
    budgetDAppend (fastBlock 51) 72 4 140410 455 prefix72 budgetDGrade51At72
  have prefix80 : sumRange 80 (fastBlock 51) = 141057 :=
    budgetDAppend (fastBlock 51) 76 4 140865 192 prefix76 budgetDGrade51At76
  have prefix84 : sumRange 84 (fastBlock 51) = 141114 :=
    budgetDAppend (fastBlock 51) 80 4 141057 57 prefix80 budgetDGrade51At80
  have prefix88 : sumRange 88 (fastBlock 51) = 141121 :=
    budgetDAppend (fastBlock 51) 84 4 141114 7 prefix84 budgetDGrade51At84
  have prefix138 : sumRange 138 (fastBlock 51) = 141121 :=
    budgetDAppend (fastBlock 51) 88 50 141121 0 prefix88 budgetDGrade51At88
  exact prefix138

private theorem budgetDGrade52At0 :
    sumRange 4 (fun i => fastBlock 52 (i + 0)) = 1843 :=
  (dBlockSum_eq 52 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At4 :
    sumRange 4 (fun i => fastBlock 52 (i + 4)) = 4527 :=
  (dBlockSum_eq 52 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At8 :
    sumRange 4 (fun i => fastBlock 52 (i + 8)) = 6859 :=
  (dBlockSum_eq 52 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At12 :
    sumRange 4 (fun i => fastBlock 52 (i + 12)) = 8839 :=
  (dBlockSum_eq 52 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At16 :
    sumRange 4 (fun i => fastBlock 52 (i + 16)) = 10467 :=
  (dBlockSum_eq 52 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At20 :
    sumRange 4 (fun i => fastBlock 52 (i + 20)) = 11750 :=
  (dBlockSum_eq 52 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At24 :
    sumRange 4 (fun i => fastBlock 52 (i + 24)) = 12724 :=
  (dBlockSum_eq 52 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At28 :
    sumRange 4 (fun i => fastBlock 52 (i + 28)) = 13431 :=
  (dBlockSum_eq 52 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At32 :
    sumRange 4 (fun i => fastBlock 52 (i + 32)) = 13914 :=
  (dBlockSum_eq 52 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At36 :
    sumRange 4 (fun i => fastBlock 52 (i + 36)) = 13746 :=
  (dBlockSum_eq 52 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At40 :
    sumRange 4 (fun i => fastBlock 52 (i + 40)) = 11231 :=
  (dBlockSum_eq 52 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At44 :
    sumRange 4 (fun i => fastBlock 52 (i + 44)) = 8723 :=
  (dBlockSum_eq 52 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At48 :
    sumRange 4 (fun i => fastBlock 52 (i + 48)) = 6567 :=
  (dBlockSum_eq 52 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At52 :
    sumRange 4 (fun i => fastBlock 52 (i + 52)) = 4763 :=
  (dBlockSum_eq 52 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At56 :
    sumRange 4 (fun i => fastBlock 52 (i + 56)) = 3310 :=
  (dBlockSum_eq 52 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At60 :
    sumRange 4 (fun i => fastBlock 52 (i + 60)) = 2187 :=
  (dBlockSum_eq 52 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At64 :
    sumRange 4 (fun i => fastBlock 52 (i + 64)) = 1352 :=
  (dBlockSum_eq 52 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At68 :
    sumRange 4 (fun i => fastBlock 52 (i + 68)) = 762 :=
  (dBlockSum_eq 52 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At72 :
    sumRange 4 (fun i => fastBlock 52 (i + 72)) = 375 :=
  (dBlockSum_eq 52 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At76 :
    sumRange 4 (fun i => fastBlock 52 (i + 76)) = 148 :=
  (dBlockSum_eq 52 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At80 :
    sumRange 4 (fun i => fastBlock 52 (i + 80)) = 38 :=
  (dBlockSum_eq 52 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At84 :
    sumRange 4 (fun i => fastBlock 52 (i + 84)) = 3 :=
  (dBlockSum_eq 52 84 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade52At88 :
    sumRange 50 (fun i => fastBlock 52 (i + 88)) = 0 :=
  (dBlockSum_eq 52 88 50 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade52 : fastGrade 52 = 137559 := by
  have prefix4 : sumRange 4 (fastBlock 52) = 1843 :=
    budgetDAppend (fastBlock 52) 0 4 0 1843 rfl budgetDGrade52At0
  have prefix8 : sumRange 8 (fastBlock 52) = 6370 :=
    budgetDAppend (fastBlock 52) 4 4 1843 4527 prefix4 budgetDGrade52At4
  have prefix12 : sumRange 12 (fastBlock 52) = 13229 :=
    budgetDAppend (fastBlock 52) 8 4 6370 6859 prefix8 budgetDGrade52At8
  have prefix16 : sumRange 16 (fastBlock 52) = 22068 :=
    budgetDAppend (fastBlock 52) 12 4 13229 8839 prefix12 budgetDGrade52At12
  have prefix20 : sumRange 20 (fastBlock 52) = 32535 :=
    budgetDAppend (fastBlock 52) 16 4 22068 10467 prefix16 budgetDGrade52At16
  have prefix24 : sumRange 24 (fastBlock 52) = 44285 :=
    budgetDAppend (fastBlock 52) 20 4 32535 11750 prefix20 budgetDGrade52At20
  have prefix28 : sumRange 28 (fastBlock 52) = 57009 :=
    budgetDAppend (fastBlock 52) 24 4 44285 12724 prefix24 budgetDGrade52At24
  have prefix32 : sumRange 32 (fastBlock 52) = 70440 :=
    budgetDAppend (fastBlock 52) 28 4 57009 13431 prefix28 budgetDGrade52At28
  have prefix36 : sumRange 36 (fastBlock 52) = 84354 :=
    budgetDAppend (fastBlock 52) 32 4 70440 13914 prefix32 budgetDGrade52At32
  have prefix40 : sumRange 40 (fastBlock 52) = 98100 :=
    budgetDAppend (fastBlock 52) 36 4 84354 13746 prefix36 budgetDGrade52At36
  have prefix44 : sumRange 44 (fastBlock 52) = 109331 :=
    budgetDAppend (fastBlock 52) 40 4 98100 11231 prefix40 budgetDGrade52At40
  have prefix48 : sumRange 48 (fastBlock 52) = 118054 :=
    budgetDAppend (fastBlock 52) 44 4 109331 8723 prefix44 budgetDGrade52At44
  have prefix52 : sumRange 52 (fastBlock 52) = 124621 :=
    budgetDAppend (fastBlock 52) 48 4 118054 6567 prefix48 budgetDGrade52At48
  have prefix56 : sumRange 56 (fastBlock 52) = 129384 :=
    budgetDAppend (fastBlock 52) 52 4 124621 4763 prefix52 budgetDGrade52At52
  have prefix60 : sumRange 60 (fastBlock 52) = 132694 :=
    budgetDAppend (fastBlock 52) 56 4 129384 3310 prefix56 budgetDGrade52At56
  have prefix64 : sumRange 64 (fastBlock 52) = 134881 :=
    budgetDAppend (fastBlock 52) 60 4 132694 2187 prefix60 budgetDGrade52At60
  have prefix68 : sumRange 68 (fastBlock 52) = 136233 :=
    budgetDAppend (fastBlock 52) 64 4 134881 1352 prefix64 budgetDGrade52At64
  have prefix72 : sumRange 72 (fastBlock 52) = 136995 :=
    budgetDAppend (fastBlock 52) 68 4 136233 762 prefix68 budgetDGrade52At68
  have prefix76 : sumRange 76 (fastBlock 52) = 137370 :=
    budgetDAppend (fastBlock 52) 72 4 136995 375 prefix72 budgetDGrade52At72
  have prefix80 : sumRange 80 (fastBlock 52) = 137518 :=
    budgetDAppend (fastBlock 52) 76 4 137370 148 prefix76 budgetDGrade52At76
  have prefix84 : sumRange 84 (fastBlock 52) = 137556 :=
    budgetDAppend (fastBlock 52) 80 4 137518 38 prefix80 budgetDGrade52At80
  have prefix88 : sumRange 88 (fastBlock 52) = 137559 :=
    budgetDAppend (fastBlock 52) 84 4 137556 3 prefix84 budgetDGrade52At84
  have prefix138 : sumRange 138 (fastBlock 52) = 137559 :=
    budgetDAppend (fastBlock 52) 88 50 137559 0 prefix88 budgetDGrade52At88
  exact prefix138

private theorem budgetDGrade53At0 :
    sumRange 4 (fun i => fastBlock 53 (i + 0)) = 1843 :=
  (dBlockSum_eq 53 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At4 :
    sumRange 4 (fun i => fastBlock 53 (i + 4)) = 4527 :=
  (dBlockSum_eq 53 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At8 :
    sumRange 4 (fun i => fastBlock 53 (i + 8)) = 6859 :=
  (dBlockSum_eq 53 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At12 :
    sumRange 4 (fun i => fastBlock 53 (i + 12)) = 8839 :=
  (dBlockSum_eq 53 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At16 :
    sumRange 4 (fun i => fastBlock 53 (i + 16)) = 10467 :=
  (dBlockSum_eq 53 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At20 :
    sumRange 4 (fun i => fastBlock 53 (i + 20)) = 11750 :=
  (dBlockSum_eq 53 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At24 :
    sumRange 4 (fun i => fastBlock 53 (i + 24)) = 12724 :=
  (dBlockSum_eq 53 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At28 :
    sumRange 4 (fun i => fastBlock 53 (i + 28)) = 13431 :=
  (dBlockSum_eq 53 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At32 :
    sumRange 4 (fun i => fastBlock 53 (i + 32)) = 13914 :=
  (dBlockSum_eq 53 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At36 :
    sumRange 4 (fun i => fastBlock 53 (i + 36)) = 13260 :=
  (dBlockSum_eq 53 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At40 :
    sumRange 4 (fun i => fastBlock 53 (i + 40)) = 10571 :=
  (dBlockSum_eq 53 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At44 :
    sumRange 4 (fun i => fastBlock 53 (i + 44)) = 8151 :=
  (dBlockSum_eq 53 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At48 :
    sumRange 4 (fun i => fastBlock 53 (i + 48)) = 6083 :=
  (dBlockSum_eq 53 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At52 :
    sumRange 4 (fun i => fastBlock 53 (i + 52)) = 4367 :=
  (dBlockSum_eq 53 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At56 :
    sumRange 4 (fun i => fastBlock 53 (i + 56)) = 3000 :=
  (dBlockSum_eq 53 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At60 :
    sumRange 4 (fun i => fastBlock 53 (i + 60)) = 1953 :=
  (dBlockSum_eq 53 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At64 :
    sumRange 4 (fun i => fastBlock 53 (i + 64)) = 1183 :=
  (dBlockSum_eq 53 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At68 :
    sumRange 4 (fun i => fastBlock 53 (i + 68)) = 648 :=
  (dBlockSum_eq 53 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At72 :
    sumRange 4 (fun i => fastBlock 53 (i + 72)) = 305 :=
  (dBlockSum_eq 53 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At76 :
    sumRange 4 (fun i => fastBlock 53 (i + 76)) = 111 :=
  (dBlockSum_eq 53 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At80 :
    sumRange 4 (fun i => fastBlock 53 (i + 80)) = 24 :=
  (dBlockSum_eq 53 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At84 :
    sumRange 4 (fun i => fastBlock 53 (i + 84)) = 1 :=
  (dBlockSum_eq 53 84 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade53At88 :
    sumRange 50 (fun i => fastBlock 53 (i + 88)) = 0 :=
  (dBlockSum_eq 53 88 50 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade53 : fastGrade 53 = 134011 := by
  have prefix4 : sumRange 4 (fastBlock 53) = 1843 :=
    budgetDAppend (fastBlock 53) 0 4 0 1843 rfl budgetDGrade53At0
  have prefix8 : sumRange 8 (fastBlock 53) = 6370 :=
    budgetDAppend (fastBlock 53) 4 4 1843 4527 prefix4 budgetDGrade53At4
  have prefix12 : sumRange 12 (fastBlock 53) = 13229 :=
    budgetDAppend (fastBlock 53) 8 4 6370 6859 prefix8 budgetDGrade53At8
  have prefix16 : sumRange 16 (fastBlock 53) = 22068 :=
    budgetDAppend (fastBlock 53) 12 4 13229 8839 prefix12 budgetDGrade53At12
  have prefix20 : sumRange 20 (fastBlock 53) = 32535 :=
    budgetDAppend (fastBlock 53) 16 4 22068 10467 prefix16 budgetDGrade53At16
  have prefix24 : sumRange 24 (fastBlock 53) = 44285 :=
    budgetDAppend (fastBlock 53) 20 4 32535 11750 prefix20 budgetDGrade53At20
  have prefix28 : sumRange 28 (fastBlock 53) = 57009 :=
    budgetDAppend (fastBlock 53) 24 4 44285 12724 prefix24 budgetDGrade53At24
  have prefix32 : sumRange 32 (fastBlock 53) = 70440 :=
    budgetDAppend (fastBlock 53) 28 4 57009 13431 prefix28 budgetDGrade53At28
  have prefix36 : sumRange 36 (fastBlock 53) = 84354 :=
    budgetDAppend (fastBlock 53) 32 4 70440 13914 prefix32 budgetDGrade53At32
  have prefix40 : sumRange 40 (fastBlock 53) = 97614 :=
    budgetDAppend (fastBlock 53) 36 4 84354 13260 prefix36 budgetDGrade53At36
  have prefix44 : sumRange 44 (fastBlock 53) = 108185 :=
    budgetDAppend (fastBlock 53) 40 4 97614 10571 prefix40 budgetDGrade53At40
  have prefix48 : sumRange 48 (fastBlock 53) = 116336 :=
    budgetDAppend (fastBlock 53) 44 4 108185 8151 prefix44 budgetDGrade53At44
  have prefix52 : sumRange 52 (fastBlock 53) = 122419 :=
    budgetDAppend (fastBlock 53) 48 4 116336 6083 prefix48 budgetDGrade53At48
  have prefix56 : sumRange 56 (fastBlock 53) = 126786 :=
    budgetDAppend (fastBlock 53) 52 4 122419 4367 prefix52 budgetDGrade53At52
  have prefix60 : sumRange 60 (fastBlock 53) = 129786 :=
    budgetDAppend (fastBlock 53) 56 4 126786 3000 prefix56 budgetDGrade53At56
  have prefix64 : sumRange 64 (fastBlock 53) = 131739 :=
    budgetDAppend (fastBlock 53) 60 4 129786 1953 prefix60 budgetDGrade53At60
  have prefix68 : sumRange 68 (fastBlock 53) = 132922 :=
    budgetDAppend (fastBlock 53) 64 4 131739 1183 prefix64 budgetDGrade53At64
  have prefix72 : sumRange 72 (fastBlock 53) = 133570 :=
    budgetDAppend (fastBlock 53) 68 4 132922 648 prefix68 budgetDGrade53At68
  have prefix76 : sumRange 76 (fastBlock 53) = 133875 :=
    budgetDAppend (fastBlock 53) 72 4 133570 305 prefix72 budgetDGrade53At72
  have prefix80 : sumRange 80 (fastBlock 53) = 133986 :=
    budgetDAppend (fastBlock 53) 76 4 133875 111 prefix76 budgetDGrade53At76
  have prefix84 : sumRange 84 (fastBlock 53) = 134010 :=
    budgetDAppend (fastBlock 53) 80 4 133986 24 prefix80 budgetDGrade53At80
  have prefix88 : sumRange 88 (fastBlock 53) = 134011 :=
    budgetDAppend (fastBlock 53) 84 4 134010 1 prefix84 budgetDGrade53At84
  have prefix138 : sumRange 138 (fastBlock 53) = 134011 :=
    budgetDAppend (fastBlock 53) 88 50 134011 0 prefix88 budgetDGrade53At88
  exact prefix138

private theorem budgetDGrade54At0 :
    sumRange 4 (fun i => fastBlock 54 (i + 0)) = 1843 :=
  (dBlockSum_eq 54 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At4 :
    sumRange 4 (fun i => fastBlock 54 (i + 4)) = 4527 :=
  (dBlockSum_eq 54 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At8 :
    sumRange 4 (fun i => fastBlock 54 (i + 8)) = 6859 :=
  (dBlockSum_eq 54 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At12 :
    sumRange 4 (fun i => fastBlock 54 (i + 12)) = 8839 :=
  (dBlockSum_eq 54 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At16 :
    sumRange 4 (fun i => fastBlock 54 (i + 16)) = 10467 :=
  (dBlockSum_eq 54 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At20 :
    sumRange 4 (fun i => fastBlock 54 (i + 20)) = 11750 :=
  (dBlockSum_eq 54 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At24 :
    sumRange 4 (fun i => fastBlock 54 (i + 24)) = 12724 :=
  (dBlockSum_eq 54 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At28 :
    sumRange 4 (fun i => fastBlock 54 (i + 28)) = 13431 :=
  (dBlockSum_eq 54 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At32 :
    sumRange 4 (fun i => fastBlock 54 (i + 32)) = 13914 :=
  (dBlockSum_eq 54 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At36 :
    sumRange 4 (fun i => fastBlock 54 (i + 36)) = 12617 :=
  (dBlockSum_eq 54 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At40 :
    sumRange 4 (fun i => fastBlock 54 (i + 40)) = 9933 :=
  (dBlockSum_eq 54 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At44 :
    sumRange 4 (fun i => fastBlock 54 (i + 44)) = 7601 :=
  (dBlockSum_eq 54 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At48 :
    sumRange 4 (fun i => fastBlock 54 (i + 48)) = 5621 :=
  (dBlockSum_eq 54 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At52 :
    sumRange 4 (fun i => fastBlock 54 (i + 52)) = 3993 :=
  (dBlockSum_eq 54 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At56 :
    sumRange 4 (fun i => fastBlock 54 (i + 56)) = 2710 :=
  (dBlockSum_eq 54 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At60 :
    sumRange 4 (fun i => fastBlock 54 (i + 60)) = 1736 :=
  (dBlockSum_eq 54 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At64 :
    sumRange 4 (fun i => fastBlock 54 (i + 64)) = 1029 :=
  (dBlockSum_eq 54 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At68 :
    sumRange 4 (fun i => fastBlock 54 (i + 68)) = 546 :=
  (dBlockSum_eq 54 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At72 :
    sumRange 4 (fun i => fastBlock 54 (i + 72)) = 244 :=
  (dBlockSum_eq 54 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At76 :
    sumRange 4 (fun i => fastBlock 54 (i + 76)) = 81 :=
  (dBlockSum_eq 54 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At80 :
    sumRange 4 (fun i => fastBlock 54 (i + 80)) = 14 :=
  (dBlockSum_eq 54 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade54At84 :
    sumRange 54 (fun i => fastBlock 54 (i + 84)) = 0 :=
  (dBlockSum_eq 54 84 54 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade54 : fastGrade 54 = 130479 := by
  have prefix4 : sumRange 4 (fastBlock 54) = 1843 :=
    budgetDAppend (fastBlock 54) 0 4 0 1843 rfl budgetDGrade54At0
  have prefix8 : sumRange 8 (fastBlock 54) = 6370 :=
    budgetDAppend (fastBlock 54) 4 4 1843 4527 prefix4 budgetDGrade54At4
  have prefix12 : sumRange 12 (fastBlock 54) = 13229 :=
    budgetDAppend (fastBlock 54) 8 4 6370 6859 prefix8 budgetDGrade54At8
  have prefix16 : sumRange 16 (fastBlock 54) = 22068 :=
    budgetDAppend (fastBlock 54) 12 4 13229 8839 prefix12 budgetDGrade54At12
  have prefix20 : sumRange 20 (fastBlock 54) = 32535 :=
    budgetDAppend (fastBlock 54) 16 4 22068 10467 prefix16 budgetDGrade54At16
  have prefix24 : sumRange 24 (fastBlock 54) = 44285 :=
    budgetDAppend (fastBlock 54) 20 4 32535 11750 prefix20 budgetDGrade54At20
  have prefix28 : sumRange 28 (fastBlock 54) = 57009 :=
    budgetDAppend (fastBlock 54) 24 4 44285 12724 prefix24 budgetDGrade54At24
  have prefix32 : sumRange 32 (fastBlock 54) = 70440 :=
    budgetDAppend (fastBlock 54) 28 4 57009 13431 prefix28 budgetDGrade54At28
  have prefix36 : sumRange 36 (fastBlock 54) = 84354 :=
    budgetDAppend (fastBlock 54) 32 4 70440 13914 prefix32 budgetDGrade54At32
  have prefix40 : sumRange 40 (fastBlock 54) = 96971 :=
    budgetDAppend (fastBlock 54) 36 4 84354 12617 prefix36 budgetDGrade54At36
  have prefix44 : sumRange 44 (fastBlock 54) = 106904 :=
    budgetDAppend (fastBlock 54) 40 4 96971 9933 prefix40 budgetDGrade54At40
  have prefix48 : sumRange 48 (fastBlock 54) = 114505 :=
    budgetDAppend (fastBlock 54) 44 4 106904 7601 prefix44 budgetDGrade54At44
  have prefix52 : sumRange 52 (fastBlock 54) = 120126 :=
    budgetDAppend (fastBlock 54) 48 4 114505 5621 prefix48 budgetDGrade54At48
  have prefix56 : sumRange 56 (fastBlock 54) = 124119 :=
    budgetDAppend (fastBlock 54) 52 4 120126 3993 prefix52 budgetDGrade54At52
  have prefix60 : sumRange 60 (fastBlock 54) = 126829 :=
    budgetDAppend (fastBlock 54) 56 4 124119 2710 prefix56 budgetDGrade54At56
  have prefix64 : sumRange 64 (fastBlock 54) = 128565 :=
    budgetDAppend (fastBlock 54) 60 4 126829 1736 prefix60 budgetDGrade54At60
  have prefix68 : sumRange 68 (fastBlock 54) = 129594 :=
    budgetDAppend (fastBlock 54) 64 4 128565 1029 prefix64 budgetDGrade54At64
  have prefix72 : sumRange 72 (fastBlock 54) = 130140 :=
    budgetDAppend (fastBlock 54) 68 4 129594 546 prefix68 budgetDGrade54At68
  have prefix76 : sumRange 76 (fastBlock 54) = 130384 :=
    budgetDAppend (fastBlock 54) 72 4 130140 244 prefix72 budgetDGrade54At72
  have prefix80 : sumRange 80 (fastBlock 54) = 130465 :=
    budgetDAppend (fastBlock 54) 76 4 130384 81 prefix76 budgetDGrade54At76
  have prefix84 : sumRange 84 (fastBlock 54) = 130479 :=
    budgetDAppend (fastBlock 54) 80 4 130465 14 prefix80 budgetDGrade54At80
  have prefix138 : sumRange 138 (fastBlock 54) = 130479 :=
    budgetDAppend (fastBlock 54) 84 54 130479 0 prefix84 budgetDGrade54At84
  exact prefix138

private theorem budgetDGrade55At0 :
    sumRange 4 (fun i => fastBlock 55 (i + 0)) = 1843 :=
  (dBlockSum_eq 55 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At4 :
    sumRange 4 (fun i => fastBlock 55 (i + 4)) = 4527 :=
  (dBlockSum_eq 55 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At8 :
    sumRange 4 (fun i => fastBlock 55 (i + 8)) = 6859 :=
  (dBlockSum_eq 55 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At12 :
    sumRange 4 (fun i => fastBlock 55 (i + 12)) = 8839 :=
  (dBlockSum_eq 55 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At16 :
    sumRange 4 (fun i => fastBlock 55 (i + 16)) = 10467 :=
  (dBlockSum_eq 55 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At20 :
    sumRange 4 (fun i => fastBlock 55 (i + 20)) = 11750 :=
  (dBlockSum_eq 55 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At24 :
    sumRange 4 (fun i => fastBlock 55 (i + 24)) = 12724 :=
  (dBlockSum_eq 55 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At28 :
    sumRange 4 (fun i => fastBlock 55 (i + 28)) = 13431 :=
  (dBlockSum_eq 55 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At32 :
    sumRange 4 (fun i => fastBlock 55 (i + 32)) = 13817 :=
  (dBlockSum_eq 55 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At36 :
    sumRange 4 (fun i => fastBlock 55 (i + 36)) = 11913 :=
  (dBlockSum_eq 55 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At40 :
    sumRange 4 (fun i => fastBlock 55 (i + 40)) = 9317 :=
  (dBlockSum_eq 55 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At44 :
    sumRange 4 (fun i => fastBlock 55 (i + 44)) = 7073 :=
  (dBlockSum_eq 55 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At48 :
    sumRange 4 (fun i => fastBlock 55 (i + 48)) = 5181 :=
  (dBlockSum_eq 55 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At52 :
    sumRange 4 (fun i => fastBlock 55 (i + 52)) = 3641 :=
  (dBlockSum_eq 55 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At56 :
    sumRange 4 (fun i => fastBlock 55 (i + 56)) = 2439 :=
  (dBlockSum_eq 55 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At60 :
    sumRange 4 (fun i => fastBlock 55 (i + 60)) = 1536 :=
  (dBlockSum_eq 55 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At64 :
    sumRange 4 (fun i => fastBlock 55 (i + 64)) = 889 :=
  (dBlockSum_eq 55 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At68 :
    sumRange 4 (fun i => fastBlock 55 (i + 68)) = 455 :=
  (dBlockSum_eq 55 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At72 :
    sumRange 4 (fun i => fastBlock 55 (i + 72)) = 192 :=
  (dBlockSum_eq 55 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At76 :
    sumRange 4 (fun i => fastBlock 55 (i + 76)) = 57 :=
  (dBlockSum_eq 55 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At80 :
    sumRange 4 (fun i => fastBlock 55 (i + 80)) = 7 :=
  (dBlockSum_eq 55 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade55At84 :
    sumRange 54 (fun i => fastBlock 55 (i + 84)) = 0 :=
  (dBlockSum_eq 55 84 54 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade55 : fastGrade 55 = 126957 := by
  have prefix4 : sumRange 4 (fastBlock 55) = 1843 :=
    budgetDAppend (fastBlock 55) 0 4 0 1843 rfl budgetDGrade55At0
  have prefix8 : sumRange 8 (fastBlock 55) = 6370 :=
    budgetDAppend (fastBlock 55) 4 4 1843 4527 prefix4 budgetDGrade55At4
  have prefix12 : sumRange 12 (fastBlock 55) = 13229 :=
    budgetDAppend (fastBlock 55) 8 4 6370 6859 prefix8 budgetDGrade55At8
  have prefix16 : sumRange 16 (fastBlock 55) = 22068 :=
    budgetDAppend (fastBlock 55) 12 4 13229 8839 prefix12 budgetDGrade55At12
  have prefix20 : sumRange 20 (fastBlock 55) = 32535 :=
    budgetDAppend (fastBlock 55) 16 4 22068 10467 prefix16 budgetDGrade55At16
  have prefix24 : sumRange 24 (fastBlock 55) = 44285 :=
    budgetDAppend (fastBlock 55) 20 4 32535 11750 prefix20 budgetDGrade55At20
  have prefix28 : sumRange 28 (fastBlock 55) = 57009 :=
    budgetDAppend (fastBlock 55) 24 4 44285 12724 prefix24 budgetDGrade55At24
  have prefix32 : sumRange 32 (fastBlock 55) = 70440 :=
    budgetDAppend (fastBlock 55) 28 4 57009 13431 prefix28 budgetDGrade55At28
  have prefix36 : sumRange 36 (fastBlock 55) = 84257 :=
    budgetDAppend (fastBlock 55) 32 4 70440 13817 prefix32 budgetDGrade55At32
  have prefix40 : sumRange 40 (fastBlock 55) = 96170 :=
    budgetDAppend (fastBlock 55) 36 4 84257 11913 prefix36 budgetDGrade55At36
  have prefix44 : sumRange 44 (fastBlock 55) = 105487 :=
    budgetDAppend (fastBlock 55) 40 4 96170 9317 prefix40 budgetDGrade55At40
  have prefix48 : sumRange 48 (fastBlock 55) = 112560 :=
    budgetDAppend (fastBlock 55) 44 4 105487 7073 prefix44 budgetDGrade55At44
  have prefix52 : sumRange 52 (fastBlock 55) = 117741 :=
    budgetDAppend (fastBlock 55) 48 4 112560 5181 prefix48 budgetDGrade55At48
  have prefix56 : sumRange 56 (fastBlock 55) = 121382 :=
    budgetDAppend (fastBlock 55) 52 4 117741 3641 prefix52 budgetDGrade55At52
  have prefix60 : sumRange 60 (fastBlock 55) = 123821 :=
    budgetDAppend (fastBlock 55) 56 4 121382 2439 prefix56 budgetDGrade55At56
  have prefix64 : sumRange 64 (fastBlock 55) = 125357 :=
    budgetDAppend (fastBlock 55) 60 4 123821 1536 prefix60 budgetDGrade55At60
  have prefix68 : sumRange 68 (fastBlock 55) = 126246 :=
    budgetDAppend (fastBlock 55) 64 4 125357 889 prefix64 budgetDGrade55At64
  have prefix72 : sumRange 72 (fastBlock 55) = 126701 :=
    budgetDAppend (fastBlock 55) 68 4 126246 455 prefix68 budgetDGrade55At68
  have prefix76 : sumRange 76 (fastBlock 55) = 126893 :=
    budgetDAppend (fastBlock 55) 72 4 126701 192 prefix72 budgetDGrade55At72
  have prefix80 : sumRange 80 (fastBlock 55) = 126950 :=
    budgetDAppend (fastBlock 55) 76 4 126893 57 prefix76 budgetDGrade55At76
  have prefix84 : sumRange 84 (fastBlock 55) = 126957 :=
    budgetDAppend (fastBlock 55) 80 4 126950 7 prefix80 budgetDGrade55At80
  have prefix138 : sumRange 138 (fastBlock 55) = 126957 :=
    budgetDAppend (fastBlock 55) 84 54 126957 0 prefix84 budgetDGrade55At84
  exact prefix138

private theorem budgetDGrade56At0 :
    sumRange 4 (fun i => fastBlock 56 (i + 0)) = 1843 :=
  (dBlockSum_eq 56 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At4 :
    sumRange 4 (fun i => fastBlock 56 (i + 4)) = 4527 :=
  (dBlockSum_eq 56 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At8 :
    sumRange 4 (fun i => fastBlock 56 (i + 8)) = 6859 :=
  (dBlockSum_eq 56 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At12 :
    sumRange 4 (fun i => fastBlock 56 (i + 12)) = 8839 :=
  (dBlockSum_eq 56 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At16 :
    sumRange 4 (fun i => fastBlock 56 (i + 16)) = 10467 :=
  (dBlockSum_eq 56 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At20 :
    sumRange 4 (fun i => fastBlock 56 (i + 20)) = 11750 :=
  (dBlockSum_eq 56 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At24 :
    sumRange 4 (fun i => fastBlock 56 (i + 24)) = 12724 :=
  (dBlockSum_eq 56 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At28 :
    sumRange 4 (fun i => fastBlock 56 (i + 28)) = 13431 :=
  (dBlockSum_eq 56 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At32 :
    sumRange 4 (fun i => fastBlock 56 (i + 32)) = 13553 :=
  (dBlockSum_eq 56 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At36 :
    sumRange 4 (fun i => fastBlock 56 (i + 36)) = 11231 :=
  (dBlockSum_eq 56 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At40 :
    sumRange 4 (fun i => fastBlock 56 (i + 40)) = 8723 :=
  (dBlockSum_eq 56 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At44 :
    sumRange 4 (fun i => fastBlock 56 (i + 44)) = 6567 :=
  (dBlockSum_eq 56 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At48 :
    sumRange 4 (fun i => fastBlock 56 (i + 48)) = 4763 :=
  (dBlockSum_eq 56 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At52 :
    sumRange 4 (fun i => fastBlock 56 (i + 52)) = 3310 :=
  (dBlockSum_eq 56 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At56 :
    sumRange 4 (fun i => fastBlock 56 (i + 56)) = 2187 :=
  (dBlockSum_eq 56 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At60 :
    sumRange 4 (fun i => fastBlock 56 (i + 60)) = 1352 :=
  (dBlockSum_eq 56 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At64 :
    sumRange 4 (fun i => fastBlock 56 (i + 64)) = 762 :=
  (dBlockSum_eq 56 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At68 :
    sumRange 4 (fun i => fastBlock 56 (i + 68)) = 375 :=
  (dBlockSum_eq 56 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At72 :
    sumRange 4 (fun i => fastBlock 56 (i + 72)) = 148 :=
  (dBlockSum_eq 56 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At76 :
    sumRange 4 (fun i => fastBlock 56 (i + 76)) = 38 :=
  (dBlockSum_eq 56 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At80 :
    sumRange 4 (fun i => fastBlock 56 (i + 80)) = 3 :=
  (dBlockSum_eq 56 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade56At84 :
    sumRange 54 (fun i => fastBlock 56 (i + 84)) = 0 :=
  (dBlockSum_eq 56 84 54 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade56 : fastGrade 56 = 123452 := by
  have prefix4 : sumRange 4 (fastBlock 56) = 1843 :=
    budgetDAppend (fastBlock 56) 0 4 0 1843 rfl budgetDGrade56At0
  have prefix8 : sumRange 8 (fastBlock 56) = 6370 :=
    budgetDAppend (fastBlock 56) 4 4 1843 4527 prefix4 budgetDGrade56At4
  have prefix12 : sumRange 12 (fastBlock 56) = 13229 :=
    budgetDAppend (fastBlock 56) 8 4 6370 6859 prefix8 budgetDGrade56At8
  have prefix16 : sumRange 16 (fastBlock 56) = 22068 :=
    budgetDAppend (fastBlock 56) 12 4 13229 8839 prefix12 budgetDGrade56At12
  have prefix20 : sumRange 20 (fastBlock 56) = 32535 :=
    budgetDAppend (fastBlock 56) 16 4 22068 10467 prefix16 budgetDGrade56At16
  have prefix24 : sumRange 24 (fastBlock 56) = 44285 :=
    budgetDAppend (fastBlock 56) 20 4 32535 11750 prefix20 budgetDGrade56At20
  have prefix28 : sumRange 28 (fastBlock 56) = 57009 :=
    budgetDAppend (fastBlock 56) 24 4 44285 12724 prefix24 budgetDGrade56At24
  have prefix32 : sumRange 32 (fastBlock 56) = 70440 :=
    budgetDAppend (fastBlock 56) 28 4 57009 13431 prefix28 budgetDGrade56At28
  have prefix36 : sumRange 36 (fastBlock 56) = 83993 :=
    budgetDAppend (fastBlock 56) 32 4 70440 13553 prefix32 budgetDGrade56At32
  have prefix40 : sumRange 40 (fastBlock 56) = 95224 :=
    budgetDAppend (fastBlock 56) 36 4 83993 11231 prefix36 budgetDGrade56At36
  have prefix44 : sumRange 44 (fastBlock 56) = 103947 :=
    budgetDAppend (fastBlock 56) 40 4 95224 8723 prefix40 budgetDGrade56At40
  have prefix48 : sumRange 48 (fastBlock 56) = 110514 :=
    budgetDAppend (fastBlock 56) 44 4 103947 6567 prefix44 budgetDGrade56At44
  have prefix52 : sumRange 52 (fastBlock 56) = 115277 :=
    budgetDAppend (fastBlock 56) 48 4 110514 4763 prefix48 budgetDGrade56At48
  have prefix56 : sumRange 56 (fastBlock 56) = 118587 :=
    budgetDAppend (fastBlock 56) 52 4 115277 3310 prefix52 budgetDGrade56At52
  have prefix60 : sumRange 60 (fastBlock 56) = 120774 :=
    budgetDAppend (fastBlock 56) 56 4 118587 2187 prefix56 budgetDGrade56At56
  have prefix64 : sumRange 64 (fastBlock 56) = 122126 :=
    budgetDAppend (fastBlock 56) 60 4 120774 1352 prefix60 budgetDGrade56At60
  have prefix68 : sumRange 68 (fastBlock 56) = 122888 :=
    budgetDAppend (fastBlock 56) 64 4 122126 762 prefix64 budgetDGrade56At64
  have prefix72 : sumRange 72 (fastBlock 56) = 123263 :=
    budgetDAppend (fastBlock 56) 68 4 122888 375 prefix68 budgetDGrade56At68
  have prefix76 : sumRange 76 (fastBlock 56) = 123411 :=
    budgetDAppend (fastBlock 56) 72 4 123263 148 prefix72 budgetDGrade56At72
  have prefix80 : sumRange 80 (fastBlock 56) = 123449 :=
    budgetDAppend (fastBlock 56) 76 4 123411 38 prefix76 budgetDGrade56At76
  have prefix84 : sumRange 84 (fastBlock 56) = 123452 :=
    budgetDAppend (fastBlock 56) 80 4 123449 3 prefix80 budgetDGrade56At80
  have prefix138 : sumRange 138 (fastBlock 56) = 123452 :=
    budgetDAppend (fastBlock 56) 84 54 123452 0 prefix84 budgetDGrade56At84
  exact prefix138

private theorem budgetDGrade57At0 :
    sumRange 4 (fun i => fastBlock 57 (i + 0)) = 1843 :=
  (dBlockSum_eq 57 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At4 :
    sumRange 4 (fun i => fastBlock 57 (i + 4)) = 4527 :=
  (dBlockSum_eq 57 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At8 :
    sumRange 4 (fun i => fastBlock 57 (i + 8)) = 6859 :=
  (dBlockSum_eq 57 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At12 :
    sumRange 4 (fun i => fastBlock 57 (i + 12)) = 8839 :=
  (dBlockSum_eq 57 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At16 :
    sumRange 4 (fun i => fastBlock 57 (i + 16)) = 10467 :=
  (dBlockSum_eq 57 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At20 :
    sumRange 4 (fun i => fastBlock 57 (i + 20)) = 11750 :=
  (dBlockSum_eq 57 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At24 :
    sumRange 4 (fun i => fastBlock 57 (i + 24)) = 12724 :=
  (dBlockSum_eq 57 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At28 :
    sumRange 4 (fun i => fastBlock 57 (i + 28)) = 13431 :=
  (dBlockSum_eq 57 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At32 :
    sumRange 4 (fun i => fastBlock 57 (i + 32)) = 13131 :=
  (dBlockSum_eq 57 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At36 :
    sumRange 4 (fun i => fastBlock 57 (i + 36)) = 10571 :=
  (dBlockSum_eq 57 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At40 :
    sumRange 4 (fun i => fastBlock 57 (i + 40)) = 8151 :=
  (dBlockSum_eq 57 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At44 :
    sumRange 4 (fun i => fastBlock 57 (i + 44)) = 6083 :=
  (dBlockSum_eq 57 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At48 :
    sumRange 4 (fun i => fastBlock 57 (i + 48)) = 4367 :=
  (dBlockSum_eq 57 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At52 :
    sumRange 4 (fun i => fastBlock 57 (i + 52)) = 3000 :=
  (dBlockSum_eq 57 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At56 :
    sumRange 4 (fun i => fastBlock 57 (i + 56)) = 1953 :=
  (dBlockSum_eq 57 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At60 :
    sumRange 4 (fun i => fastBlock 57 (i + 60)) = 1183 :=
  (dBlockSum_eq 57 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At64 :
    sumRange 4 (fun i => fastBlock 57 (i + 64)) = 648 :=
  (dBlockSum_eq 57 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At68 :
    sumRange 4 (fun i => fastBlock 57 (i + 68)) = 305 :=
  (dBlockSum_eq 57 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At72 :
    sumRange 4 (fun i => fastBlock 57 (i + 72)) = 111 :=
  (dBlockSum_eq 57 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At76 :
    sumRange 4 (fun i => fastBlock 57 (i + 76)) = 24 :=
  (dBlockSum_eq 57 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At80 :
    sumRange 4 (fun i => fastBlock 57 (i + 80)) = 1 :=
  (dBlockSum_eq 57 80 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade57At84 :
    sumRange 54 (fun i => fastBlock 57 (i + 84)) = 0 :=
  (dBlockSum_eq 57 84 54 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade57 : fastGrade 57 = 119968 := by
  have prefix4 : sumRange 4 (fastBlock 57) = 1843 :=
    budgetDAppend (fastBlock 57) 0 4 0 1843 rfl budgetDGrade57At0
  have prefix8 : sumRange 8 (fastBlock 57) = 6370 :=
    budgetDAppend (fastBlock 57) 4 4 1843 4527 prefix4 budgetDGrade57At4
  have prefix12 : sumRange 12 (fastBlock 57) = 13229 :=
    budgetDAppend (fastBlock 57) 8 4 6370 6859 prefix8 budgetDGrade57At8
  have prefix16 : sumRange 16 (fastBlock 57) = 22068 :=
    budgetDAppend (fastBlock 57) 12 4 13229 8839 prefix12 budgetDGrade57At12
  have prefix20 : sumRange 20 (fastBlock 57) = 32535 :=
    budgetDAppend (fastBlock 57) 16 4 22068 10467 prefix16 budgetDGrade57At16
  have prefix24 : sumRange 24 (fastBlock 57) = 44285 :=
    budgetDAppend (fastBlock 57) 20 4 32535 11750 prefix20 budgetDGrade57At20
  have prefix28 : sumRange 28 (fastBlock 57) = 57009 :=
    budgetDAppend (fastBlock 57) 24 4 44285 12724 prefix24 budgetDGrade57At24
  have prefix32 : sumRange 32 (fastBlock 57) = 70440 :=
    budgetDAppend (fastBlock 57) 28 4 57009 13431 prefix28 budgetDGrade57At28
  have prefix36 : sumRange 36 (fastBlock 57) = 83571 :=
    budgetDAppend (fastBlock 57) 32 4 70440 13131 prefix32 budgetDGrade57At32
  have prefix40 : sumRange 40 (fastBlock 57) = 94142 :=
    budgetDAppend (fastBlock 57) 36 4 83571 10571 prefix36 budgetDGrade57At36
  have prefix44 : sumRange 44 (fastBlock 57) = 102293 :=
    budgetDAppend (fastBlock 57) 40 4 94142 8151 prefix40 budgetDGrade57At40
  have prefix48 : sumRange 48 (fastBlock 57) = 108376 :=
    budgetDAppend (fastBlock 57) 44 4 102293 6083 prefix44 budgetDGrade57At44
  have prefix52 : sumRange 52 (fastBlock 57) = 112743 :=
    budgetDAppend (fastBlock 57) 48 4 108376 4367 prefix48 budgetDGrade57At48
  have prefix56 : sumRange 56 (fastBlock 57) = 115743 :=
    budgetDAppend (fastBlock 57) 52 4 112743 3000 prefix52 budgetDGrade57At52
  have prefix60 : sumRange 60 (fastBlock 57) = 117696 :=
    budgetDAppend (fastBlock 57) 56 4 115743 1953 prefix56 budgetDGrade57At56
  have prefix64 : sumRange 64 (fastBlock 57) = 118879 :=
    budgetDAppend (fastBlock 57) 60 4 117696 1183 prefix60 budgetDGrade57At60
  have prefix68 : sumRange 68 (fastBlock 57) = 119527 :=
    budgetDAppend (fastBlock 57) 64 4 118879 648 prefix64 budgetDGrade57At64
  have prefix72 : sumRange 72 (fastBlock 57) = 119832 :=
    budgetDAppend (fastBlock 57) 68 4 119527 305 prefix68 budgetDGrade57At68
  have prefix76 : sumRange 76 (fastBlock 57) = 119943 :=
    budgetDAppend (fastBlock 57) 72 4 119832 111 prefix72 budgetDGrade57At72
  have prefix80 : sumRange 80 (fastBlock 57) = 119967 :=
    budgetDAppend (fastBlock 57) 76 4 119943 24 prefix76 budgetDGrade57At76
  have prefix84 : sumRange 84 (fastBlock 57) = 119968 :=
    budgetDAppend (fastBlock 57) 80 4 119967 1 prefix80 budgetDGrade57At80
  have prefix138 : sumRange 138 (fastBlock 57) = 119968 :=
    budgetDAppend (fastBlock 57) 84 54 119968 0 prefix84 budgetDGrade57At84
  exact prefix138

private theorem budgetDGrade58At0 :
    sumRange 4 (fun i => fastBlock 58 (i + 0)) = 1843 :=
  (dBlockSum_eq 58 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At4 :
    sumRange 4 (fun i => fastBlock 58 (i + 4)) = 4527 :=
  (dBlockSum_eq 58 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At8 :
    sumRange 4 (fun i => fastBlock 58 (i + 8)) = 6859 :=
  (dBlockSum_eq 58 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At12 :
    sumRange 4 (fun i => fastBlock 58 (i + 12)) = 8839 :=
  (dBlockSum_eq 58 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At16 :
    sumRange 4 (fun i => fastBlock 58 (i + 16)) = 10467 :=
  (dBlockSum_eq 58 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At20 :
    sumRange 4 (fun i => fastBlock 58 (i + 20)) = 11750 :=
  (dBlockSum_eq 58 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At24 :
    sumRange 4 (fun i => fastBlock 58 (i + 24)) = 12724 :=
  (dBlockSum_eq 58 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At28 :
    sumRange 4 (fun i => fastBlock 58 (i + 28)) = 13431 :=
  (dBlockSum_eq 58 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At32 :
    sumRange 4 (fun i => fastBlock 58 (i + 32)) = 12562 :=
  (dBlockSum_eq 58 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At36 :
    sumRange 4 (fun i => fastBlock 58 (i + 36)) = 9933 :=
  (dBlockSum_eq 58 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At40 :
    sumRange 4 (fun i => fastBlock 58 (i + 40)) = 7601 :=
  (dBlockSum_eq 58 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At44 :
    sumRange 4 (fun i => fastBlock 58 (i + 44)) = 5621 :=
  (dBlockSum_eq 58 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At48 :
    sumRange 4 (fun i => fastBlock 58 (i + 48)) = 3993 :=
  (dBlockSum_eq 58 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At52 :
    sumRange 4 (fun i => fastBlock 58 (i + 52)) = 2710 :=
  (dBlockSum_eq 58 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At56 :
    sumRange 4 (fun i => fastBlock 58 (i + 56)) = 1736 :=
  (dBlockSum_eq 58 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At60 :
    sumRange 4 (fun i => fastBlock 58 (i + 60)) = 1029 :=
  (dBlockSum_eq 58 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At64 :
    sumRange 4 (fun i => fastBlock 58 (i + 64)) = 546 :=
  (dBlockSum_eq 58 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At68 :
    sumRange 4 (fun i => fastBlock 58 (i + 68)) = 244 :=
  (dBlockSum_eq 58 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At72 :
    sumRange 4 (fun i => fastBlock 58 (i + 72)) = 81 :=
  (dBlockSum_eq 58 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At76 :
    sumRange 4 (fun i => fastBlock 58 (i + 76)) = 14 :=
  (dBlockSum_eq 58 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade58At80 :
    sumRange 58 (fun i => fastBlock 58 (i + 80)) = 0 :=
  (dBlockSum_eq 58 80 58 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade58 : fastGrade 58 = 116510 := by
  have prefix4 : sumRange 4 (fastBlock 58) = 1843 :=
    budgetDAppend (fastBlock 58) 0 4 0 1843 rfl budgetDGrade58At0
  have prefix8 : sumRange 8 (fastBlock 58) = 6370 :=
    budgetDAppend (fastBlock 58) 4 4 1843 4527 prefix4 budgetDGrade58At4
  have prefix12 : sumRange 12 (fastBlock 58) = 13229 :=
    budgetDAppend (fastBlock 58) 8 4 6370 6859 prefix8 budgetDGrade58At8
  have prefix16 : sumRange 16 (fastBlock 58) = 22068 :=
    budgetDAppend (fastBlock 58) 12 4 13229 8839 prefix12 budgetDGrade58At12
  have prefix20 : sumRange 20 (fastBlock 58) = 32535 :=
    budgetDAppend (fastBlock 58) 16 4 22068 10467 prefix16 budgetDGrade58At16
  have prefix24 : sumRange 24 (fastBlock 58) = 44285 :=
    budgetDAppend (fastBlock 58) 20 4 32535 11750 prefix20 budgetDGrade58At20
  have prefix28 : sumRange 28 (fastBlock 58) = 57009 :=
    budgetDAppend (fastBlock 58) 24 4 44285 12724 prefix24 budgetDGrade58At24
  have prefix32 : sumRange 32 (fastBlock 58) = 70440 :=
    budgetDAppend (fastBlock 58) 28 4 57009 13431 prefix28 budgetDGrade58At28
  have prefix36 : sumRange 36 (fastBlock 58) = 83002 :=
    budgetDAppend (fastBlock 58) 32 4 70440 12562 prefix32 budgetDGrade58At32
  have prefix40 : sumRange 40 (fastBlock 58) = 92935 :=
    budgetDAppend (fastBlock 58) 36 4 83002 9933 prefix36 budgetDGrade58At36
  have prefix44 : sumRange 44 (fastBlock 58) = 100536 :=
    budgetDAppend (fastBlock 58) 40 4 92935 7601 prefix40 budgetDGrade58At40
  have prefix48 : sumRange 48 (fastBlock 58) = 106157 :=
    budgetDAppend (fastBlock 58) 44 4 100536 5621 prefix44 budgetDGrade58At44
  have prefix52 : sumRange 52 (fastBlock 58) = 110150 :=
    budgetDAppend (fastBlock 58) 48 4 106157 3993 prefix48 budgetDGrade58At48
  have prefix56 : sumRange 56 (fastBlock 58) = 112860 :=
    budgetDAppend (fastBlock 58) 52 4 110150 2710 prefix52 budgetDGrade58At52
  have prefix60 : sumRange 60 (fastBlock 58) = 114596 :=
    budgetDAppend (fastBlock 58) 56 4 112860 1736 prefix56 budgetDGrade58At56
  have prefix64 : sumRange 64 (fastBlock 58) = 115625 :=
    budgetDAppend (fastBlock 58) 60 4 114596 1029 prefix60 budgetDGrade58At60
  have prefix68 : sumRange 68 (fastBlock 58) = 116171 :=
    budgetDAppend (fastBlock 58) 64 4 115625 546 prefix64 budgetDGrade58At64
  have prefix72 : sumRange 72 (fastBlock 58) = 116415 :=
    budgetDAppend (fastBlock 58) 68 4 116171 244 prefix68 budgetDGrade58At68
  have prefix76 : sumRange 76 (fastBlock 58) = 116496 :=
    budgetDAppend (fastBlock 58) 72 4 116415 81 prefix72 budgetDGrade58At72
  have prefix80 : sumRange 80 (fastBlock 58) = 116510 :=
    budgetDAppend (fastBlock 58) 76 4 116496 14 prefix76 budgetDGrade58At76
  have prefix138 : sumRange 138 (fastBlock 58) = 116510 :=
    budgetDAppend (fastBlock 58) 80 58 116510 0 prefix80 budgetDGrade58At80
  exact prefix138

private theorem budgetDGrade59At0 :
    sumRange 4 (fun i => fastBlock 59 (i + 0)) = 1843 :=
  (dBlockSum_eq 59 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At4 :
    sumRange 4 (fun i => fastBlock 59 (i + 4)) = 4527 :=
  (dBlockSum_eq 59 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At8 :
    sumRange 4 (fun i => fastBlock 59 (i + 8)) = 6859 :=
  (dBlockSum_eq 59 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At12 :
    sumRange 4 (fun i => fastBlock 59 (i + 12)) = 8839 :=
  (dBlockSum_eq 59 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At16 :
    sumRange 4 (fun i => fastBlock 59 (i + 16)) = 10467 :=
  (dBlockSum_eq 59 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At20 :
    sumRange 4 (fun i => fastBlock 59 (i + 20)) = 11750 :=
  (dBlockSum_eq 59 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At24 :
    sumRange 4 (fun i => fastBlock 59 (i + 24)) = 12724 :=
  (dBlockSum_eq 59 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At28 :
    sumRange 4 (fun i => fastBlock 59 (i + 28)) = 13369 :=
  (dBlockSum_eq 59 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At32 :
    sumRange 4 (fun i => fastBlock 59 (i + 32)) = 11913 :=
  (dBlockSum_eq 59 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At36 :
    sumRange 4 (fun i => fastBlock 59 (i + 36)) = 9317 :=
  (dBlockSum_eq 59 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At40 :
    sumRange 4 (fun i => fastBlock 59 (i + 40)) = 7073 :=
  (dBlockSum_eq 59 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At44 :
    sumRange 4 (fun i => fastBlock 59 (i + 44)) = 5181 :=
  (dBlockSum_eq 59 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At48 :
    sumRange 4 (fun i => fastBlock 59 (i + 48)) = 3641 :=
  (dBlockSum_eq 59 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At52 :
    sumRange 4 (fun i => fastBlock 59 (i + 52)) = 2439 :=
  (dBlockSum_eq 59 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At56 :
    sumRange 4 (fun i => fastBlock 59 (i + 56)) = 1536 :=
  (dBlockSum_eq 59 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At60 :
    sumRange 4 (fun i => fastBlock 59 (i + 60)) = 889 :=
  (dBlockSum_eq 59 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At64 :
    sumRange 4 (fun i => fastBlock 59 (i + 64)) = 455 :=
  (dBlockSum_eq 59 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At68 :
    sumRange 4 (fun i => fastBlock 59 (i + 68)) = 192 :=
  (dBlockSum_eq 59 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At72 :
    sumRange 4 (fun i => fastBlock 59 (i + 72)) = 57 :=
  (dBlockSum_eq 59 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At76 :
    sumRange 4 (fun i => fastBlock 59 (i + 76)) = 7 :=
  (dBlockSum_eq 59 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade59At80 :
    sumRange 58 (fun i => fastBlock 59 (i + 80)) = 0 :=
  (dBlockSum_eq 59 80 58 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade59 : fastGrade 59 = 113078 := by
  have prefix4 : sumRange 4 (fastBlock 59) = 1843 :=
    budgetDAppend (fastBlock 59) 0 4 0 1843 rfl budgetDGrade59At0
  have prefix8 : sumRange 8 (fastBlock 59) = 6370 :=
    budgetDAppend (fastBlock 59) 4 4 1843 4527 prefix4 budgetDGrade59At4
  have prefix12 : sumRange 12 (fastBlock 59) = 13229 :=
    budgetDAppend (fastBlock 59) 8 4 6370 6859 prefix8 budgetDGrade59At8
  have prefix16 : sumRange 16 (fastBlock 59) = 22068 :=
    budgetDAppend (fastBlock 59) 12 4 13229 8839 prefix12 budgetDGrade59At12
  have prefix20 : sumRange 20 (fastBlock 59) = 32535 :=
    budgetDAppend (fastBlock 59) 16 4 22068 10467 prefix16 budgetDGrade59At16
  have prefix24 : sumRange 24 (fastBlock 59) = 44285 :=
    budgetDAppend (fastBlock 59) 20 4 32535 11750 prefix20 budgetDGrade59At20
  have prefix28 : sumRange 28 (fastBlock 59) = 57009 :=
    budgetDAppend (fastBlock 59) 24 4 44285 12724 prefix24 budgetDGrade59At24
  have prefix32 : sumRange 32 (fastBlock 59) = 70378 :=
    budgetDAppend (fastBlock 59) 28 4 57009 13369 prefix28 budgetDGrade59At28
  have prefix36 : sumRange 36 (fastBlock 59) = 82291 :=
    budgetDAppend (fastBlock 59) 32 4 70378 11913 prefix32 budgetDGrade59At32
  have prefix40 : sumRange 40 (fastBlock 59) = 91608 :=
    budgetDAppend (fastBlock 59) 36 4 82291 9317 prefix36 budgetDGrade59At36
  have prefix44 : sumRange 44 (fastBlock 59) = 98681 :=
    budgetDAppend (fastBlock 59) 40 4 91608 7073 prefix40 budgetDGrade59At40
  have prefix48 : sumRange 48 (fastBlock 59) = 103862 :=
    budgetDAppend (fastBlock 59) 44 4 98681 5181 prefix44 budgetDGrade59At44
  have prefix52 : sumRange 52 (fastBlock 59) = 107503 :=
    budgetDAppend (fastBlock 59) 48 4 103862 3641 prefix48 budgetDGrade59At48
  have prefix56 : sumRange 56 (fastBlock 59) = 109942 :=
    budgetDAppend (fastBlock 59) 52 4 107503 2439 prefix52 budgetDGrade59At52
  have prefix60 : sumRange 60 (fastBlock 59) = 111478 :=
    budgetDAppend (fastBlock 59) 56 4 109942 1536 prefix56 budgetDGrade59At56
  have prefix64 : sumRange 64 (fastBlock 59) = 112367 :=
    budgetDAppend (fastBlock 59) 60 4 111478 889 prefix60 budgetDGrade59At60
  have prefix68 : sumRange 68 (fastBlock 59) = 112822 :=
    budgetDAppend (fastBlock 59) 64 4 112367 455 prefix64 budgetDGrade59At64
  have prefix72 : sumRange 72 (fastBlock 59) = 113014 :=
    budgetDAppend (fastBlock 59) 68 4 112822 192 prefix68 budgetDGrade59At68
  have prefix76 : sumRange 76 (fastBlock 59) = 113071 :=
    budgetDAppend (fastBlock 59) 72 4 113014 57 prefix72 budgetDGrade59At72
  have prefix80 : sumRange 80 (fastBlock 59) = 113078 :=
    budgetDAppend (fastBlock 59) 76 4 113071 7 prefix76 budgetDGrade59At76
  have prefix138 : sumRange 138 (fastBlock 59) = 113078 :=
    budgetDAppend (fastBlock 59) 80 58 113078 0 prefix80 budgetDGrade59At80
  exact prefix138

private theorem budgetDGrade60At0 :
    sumRange 4 (fun i => fastBlock 60 (i + 0)) = 1843 :=
  (dBlockSum_eq 60 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At4 :
    sumRange 4 (fun i => fastBlock 60 (i + 4)) = 4527 :=
  (dBlockSum_eq 60 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At8 :
    sumRange 4 (fun i => fastBlock 60 (i + 8)) = 6859 :=
  (dBlockSum_eq 60 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At12 :
    sumRange 4 (fun i => fastBlock 60 (i + 12)) = 8839 :=
  (dBlockSum_eq 60 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At16 :
    sumRange 4 (fun i => fastBlock 60 (i + 16)) = 10467 :=
  (dBlockSum_eq 60 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At20 :
    sumRange 4 (fun i => fastBlock 60 (i + 20)) = 11750 :=
  (dBlockSum_eq 60 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At24 :
    sumRange 4 (fun i => fastBlock 60 (i + 24)) = 12724 :=
  (dBlockSum_eq 60 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At28 :
    sumRange 4 (fun i => fastBlock 60 (i + 28)) = 13204 :=
  (dBlockSum_eq 60 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At32 :
    sumRange 4 (fun i => fastBlock 60 (i + 32)) = 11231 :=
  (dBlockSum_eq 60 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At36 :
    sumRange 4 (fun i => fastBlock 60 (i + 36)) = 8723 :=
  (dBlockSum_eq 60 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At40 :
    sumRange 4 (fun i => fastBlock 60 (i + 40)) = 6567 :=
  (dBlockSum_eq 60 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At44 :
    sumRange 4 (fun i => fastBlock 60 (i + 44)) = 4763 :=
  (dBlockSum_eq 60 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At48 :
    sumRange 4 (fun i => fastBlock 60 (i + 48)) = 3310 :=
  (dBlockSum_eq 60 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At52 :
    sumRange 4 (fun i => fastBlock 60 (i + 52)) = 2187 :=
  (dBlockSum_eq 60 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At56 :
    sumRange 4 (fun i => fastBlock 60 (i + 56)) = 1352 :=
  (dBlockSum_eq 60 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At60 :
    sumRange 4 (fun i => fastBlock 60 (i + 60)) = 762 :=
  (dBlockSum_eq 60 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At64 :
    sumRange 4 (fun i => fastBlock 60 (i + 64)) = 375 :=
  (dBlockSum_eq 60 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At68 :
    sumRange 4 (fun i => fastBlock 60 (i + 68)) = 148 :=
  (dBlockSum_eq 60 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At72 :
    sumRange 4 (fun i => fastBlock 60 (i + 72)) = 38 :=
  (dBlockSum_eq 60 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At76 :
    sumRange 4 (fun i => fastBlock 60 (i + 76)) = 3 :=
  (dBlockSum_eq 60 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade60At80 :
    sumRange 58 (fun i => fastBlock 60 (i + 80)) = 0 :=
  (dBlockSum_eq 60 80 58 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade60 : fastGrade 60 = 109672 := by
  have prefix4 : sumRange 4 (fastBlock 60) = 1843 :=
    budgetDAppend (fastBlock 60) 0 4 0 1843 rfl budgetDGrade60At0
  have prefix8 : sumRange 8 (fastBlock 60) = 6370 :=
    budgetDAppend (fastBlock 60) 4 4 1843 4527 prefix4 budgetDGrade60At4
  have prefix12 : sumRange 12 (fastBlock 60) = 13229 :=
    budgetDAppend (fastBlock 60) 8 4 6370 6859 prefix8 budgetDGrade60At8
  have prefix16 : sumRange 16 (fastBlock 60) = 22068 :=
    budgetDAppend (fastBlock 60) 12 4 13229 8839 prefix12 budgetDGrade60At12
  have prefix20 : sumRange 20 (fastBlock 60) = 32535 :=
    budgetDAppend (fastBlock 60) 16 4 22068 10467 prefix16 budgetDGrade60At16
  have prefix24 : sumRange 24 (fastBlock 60) = 44285 :=
    budgetDAppend (fastBlock 60) 20 4 32535 11750 prefix20 budgetDGrade60At20
  have prefix28 : sumRange 28 (fastBlock 60) = 57009 :=
    budgetDAppend (fastBlock 60) 24 4 44285 12724 prefix24 budgetDGrade60At24
  have prefix32 : sumRange 32 (fastBlock 60) = 70213 :=
    budgetDAppend (fastBlock 60) 28 4 57009 13204 prefix28 budgetDGrade60At28
  have prefix36 : sumRange 36 (fastBlock 60) = 81444 :=
    budgetDAppend (fastBlock 60) 32 4 70213 11231 prefix32 budgetDGrade60At32
  have prefix40 : sumRange 40 (fastBlock 60) = 90167 :=
    budgetDAppend (fastBlock 60) 36 4 81444 8723 prefix36 budgetDGrade60At36
  have prefix44 : sumRange 44 (fastBlock 60) = 96734 :=
    budgetDAppend (fastBlock 60) 40 4 90167 6567 prefix40 budgetDGrade60At40
  have prefix48 : sumRange 48 (fastBlock 60) = 101497 :=
    budgetDAppend (fastBlock 60) 44 4 96734 4763 prefix44 budgetDGrade60At44
  have prefix52 : sumRange 52 (fastBlock 60) = 104807 :=
    budgetDAppend (fastBlock 60) 48 4 101497 3310 prefix48 budgetDGrade60At48
  have prefix56 : sumRange 56 (fastBlock 60) = 106994 :=
    budgetDAppend (fastBlock 60) 52 4 104807 2187 prefix52 budgetDGrade60At52
  have prefix60 : sumRange 60 (fastBlock 60) = 108346 :=
    budgetDAppend (fastBlock 60) 56 4 106994 1352 prefix56 budgetDGrade60At56
  have prefix64 : sumRange 64 (fastBlock 60) = 109108 :=
    budgetDAppend (fastBlock 60) 60 4 108346 762 prefix60 budgetDGrade60At60
  have prefix68 : sumRange 68 (fastBlock 60) = 109483 :=
    budgetDAppend (fastBlock 60) 64 4 109108 375 prefix64 budgetDGrade60At64
  have prefix72 : sumRange 72 (fastBlock 60) = 109631 :=
    budgetDAppend (fastBlock 60) 68 4 109483 148 prefix68 budgetDGrade60At68
  have prefix76 : sumRange 76 (fastBlock 60) = 109669 :=
    budgetDAppend (fastBlock 60) 72 4 109631 38 prefix72 budgetDGrade60At72
  have prefix80 : sumRange 80 (fastBlock 60) = 109672 :=
    budgetDAppend (fastBlock 60) 76 4 109669 3 prefix76 budgetDGrade60At76
  have prefix138 : sumRange 138 (fastBlock 60) = 109672 :=
    budgetDAppend (fastBlock 60) 80 58 109672 0 prefix80 budgetDGrade60At80
  exact prefix138

private theorem budgetDGrade61At0 :
    sumRange 4 (fun i => fastBlock 61 (i + 0)) = 1843 :=
  (dBlockSum_eq 61 0 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At4 :
    sumRange 4 (fun i => fastBlock 61 (i + 4)) = 4527 :=
  (dBlockSum_eq 61 4 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At8 :
    sumRange 4 (fun i => fastBlock 61 (i + 8)) = 6859 :=
  (dBlockSum_eq 61 8 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At12 :
    sumRange 4 (fun i => fastBlock 61 (i + 12)) = 8839 :=
  (dBlockSum_eq 61 12 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At16 :
    sumRange 4 (fun i => fastBlock 61 (i + 16)) = 10467 :=
  (dBlockSum_eq 61 16 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At20 :
    sumRange 4 (fun i => fastBlock 61 (i + 20)) = 11750 :=
  (dBlockSum_eq 61 20 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At24 :
    sumRange 4 (fun i => fastBlock 61 (i + 24)) = 12724 :=
  (dBlockSum_eq 61 24 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At28 :
    sumRange 4 (fun i => fastBlock 61 (i + 28)) = 12887 :=
  (dBlockSum_eq 61 28 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At32 :
    sumRange 4 (fun i => fastBlock 61 (i + 32)) = 10571 :=
  (dBlockSum_eq 61 32 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At36 :
    sumRange 4 (fun i => fastBlock 61 (i + 36)) = 8151 :=
  (dBlockSum_eq 61 36 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At40 :
    sumRange 4 (fun i => fastBlock 61 (i + 40)) = 6083 :=
  (dBlockSum_eq 61 40 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At44 :
    sumRange 4 (fun i => fastBlock 61 (i + 44)) = 4367 :=
  (dBlockSum_eq 61 44 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At48 :
    sumRange 4 (fun i => fastBlock 61 (i + 48)) = 3000 :=
  (dBlockSum_eq 61 48 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At52 :
    sumRange 4 (fun i => fastBlock 61 (i + 52)) = 1953 :=
  (dBlockSum_eq 61 52 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At56 :
    sumRange 4 (fun i => fastBlock 61 (i + 56)) = 1183 :=
  (dBlockSum_eq 61 56 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At60 :
    sumRange 4 (fun i => fastBlock 61 (i + 60)) = 648 :=
  (dBlockSum_eq 61 60 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At64 :
    sumRange 4 (fun i => fastBlock 61 (i + 64)) = 305 :=
  (dBlockSum_eq 61 64 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At68 :
    sumRange 4 (fun i => fastBlock 61 (i + 68)) = 111 :=
  (dBlockSum_eq 61 68 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At72 :
    sumRange 4 (fun i => fastBlock 61 (i + 72)) = 24 :=
  (dBlockSum_eq 61 72 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At76 :
    sumRange 4 (fun i => fastBlock 61 (i + 76)) = 1 :=
  (dBlockSum_eq 61 76 4 (by decide) (by decide)).trans (by decide +kernel)
private theorem budgetDGrade61At80 :
    sumRange 58 (fun i => fastBlock 61 (i + 80)) = 0 :=
  (dBlockSum_eq 61 80 58 (by decide) (by decide)).trans (by decide +kernel)

private theorem grade61 : fastGrade 61 = 106293 := by
  have prefix4 : sumRange 4 (fastBlock 61) = 1843 :=
    budgetDAppend (fastBlock 61) 0 4 0 1843 rfl budgetDGrade61At0
  have prefix8 : sumRange 8 (fastBlock 61) = 6370 :=
    budgetDAppend (fastBlock 61) 4 4 1843 4527 prefix4 budgetDGrade61At4
  have prefix12 : sumRange 12 (fastBlock 61) = 13229 :=
    budgetDAppend (fastBlock 61) 8 4 6370 6859 prefix8 budgetDGrade61At8
  have prefix16 : sumRange 16 (fastBlock 61) = 22068 :=
    budgetDAppend (fastBlock 61) 12 4 13229 8839 prefix12 budgetDGrade61At12
  have prefix20 : sumRange 20 (fastBlock 61) = 32535 :=
    budgetDAppend (fastBlock 61) 16 4 22068 10467 prefix16 budgetDGrade61At16
  have prefix24 : sumRange 24 (fastBlock 61) = 44285 :=
    budgetDAppend (fastBlock 61) 20 4 32535 11750 prefix20 budgetDGrade61At20
  have prefix28 : sumRange 28 (fastBlock 61) = 57009 :=
    budgetDAppend (fastBlock 61) 24 4 44285 12724 prefix24 budgetDGrade61At24
  have prefix32 : sumRange 32 (fastBlock 61) = 69896 :=
    budgetDAppend (fastBlock 61) 28 4 57009 12887 prefix28 budgetDGrade61At28
  have prefix36 : sumRange 36 (fastBlock 61) = 80467 :=
    budgetDAppend (fastBlock 61) 32 4 69896 10571 prefix32 budgetDGrade61At32
  have prefix40 : sumRange 40 (fastBlock 61) = 88618 :=
    budgetDAppend (fastBlock 61) 36 4 80467 8151 prefix36 budgetDGrade61At36
  have prefix44 : sumRange 44 (fastBlock 61) = 94701 :=
    budgetDAppend (fastBlock 61) 40 4 88618 6083 prefix40 budgetDGrade61At40
  have prefix48 : sumRange 48 (fastBlock 61) = 99068 :=
    budgetDAppend (fastBlock 61) 44 4 94701 4367 prefix44 budgetDGrade61At44
  have prefix52 : sumRange 52 (fastBlock 61) = 102068 :=
    budgetDAppend (fastBlock 61) 48 4 99068 3000 prefix48 budgetDGrade61At48
  have prefix56 : sumRange 56 (fastBlock 61) = 104021 :=
    budgetDAppend (fastBlock 61) 52 4 102068 1953 prefix52 budgetDGrade61At52
  have prefix60 : sumRange 60 (fastBlock 61) = 105204 :=
    budgetDAppend (fastBlock 61) 56 4 104021 1183 prefix56 budgetDGrade61At56
  have prefix64 : sumRange 64 (fastBlock 61) = 105852 :=
    budgetDAppend (fastBlock 61) 60 4 105204 648 prefix60 budgetDGrade61At60
  have prefix68 : sumRange 68 (fastBlock 61) = 106157 :=
    budgetDAppend (fastBlock 61) 64 4 105852 305 prefix64 budgetDGrade61At64
  have prefix72 : sumRange 72 (fastBlock 61) = 106268 :=
    budgetDAppend (fastBlock 61) 68 4 106157 111 prefix68 budgetDGrade61At68
  have prefix76 : sumRange 76 (fastBlock 61) = 106292 :=
    budgetDAppend (fastBlock 61) 72 4 106268 24 prefix72 budgetDGrade61At72
  have prefix80 : sumRange 80 (fastBlock 61) = 106293 :=
    budgetDAppend (fastBlock 61) 76 4 106292 1 prefix76 budgetDGrade61At76
  have prefix138 : sumRange 138 (fastBlock 61) = 106293 :=
    budgetDAppend (fastBlock 61) 80 58 106293 0 prefix80 budgetDGrade61At80
  exact prefix138

private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)

private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 49)

private theorem prefix49 : sumRange 1 gradeFrom = 148279 :=
  sumStep gradeFrom 0 0 148279 rfl grade49
private theorem prefix50 : sumRange 2 gradeFrom = 292974 :=
  sumStep gradeFrom 1 148279 144695 prefix49 grade50
private theorem prefix51 : sumRange 3 gradeFrom = 434095 :=
  sumStep gradeFrom 2 292974 141121 prefix50 grade51
private theorem prefix52 : sumRange 4 gradeFrom = 571654 :=
  sumStep gradeFrom 3 434095 137559 prefix51 grade52
private theorem prefix53 : sumRange 5 gradeFrom = 705665 :=
  sumStep gradeFrom 4 571654 134011 prefix52 grade53
private theorem prefix54 : sumRange 6 gradeFrom = 836144 :=
  sumStep gradeFrom 5 705665 130479 prefix53 grade54
private theorem prefix55 : sumRange 7 gradeFrom = 963101 :=
  sumStep gradeFrom 6 836144 126957 prefix54 grade55
private theorem prefix56 : sumRange 8 gradeFrom = 1086553 :=
  sumStep gradeFrom 7 963101 123452 prefix55 grade56
private theorem prefix57 : sumRange 9 gradeFrom = 1206521 :=
  sumStep gradeFrom 8 1086553 119968 prefix56 grade57
private theorem prefix58 : sumRange 10 gradeFrom = 1323031 :=
  sumStep gradeFrom 9 1206521 116510 prefix57 grade58
private theorem prefix59 : sumRange 11 gradeFrom = 1436109 :=
  sumStep gradeFrom 10 1323031 113078 prefix58 grade59
private theorem prefix60 : sumRange 12 gradeFrom = 1545781 :=
  sumStep gradeFrom 11 1436109 109672 prefix59 grade60
theorem budgetD : sumRange 13 (fun i => fastGrade (i + 49)) = 1652074 :=
  sumStep gradeFrom 12 1545781 106293 prefix60 grade61

end K1_13_1_1
end PackSource_K1_13_1_1BudgetD

section PackSource_K1_13_2_3_4DataA
set_option autoImplicit true
namespace K1_13_2_3_4

open K1_13_2

set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

private def daTriple (x : ℤ) : ℤ :=
  denominator (x - 1) + denominator (x - 2) + denominator (x - 3)

private theorem daDenNeg (x : ℤ) (h : x < 0) : denominator x = 0 := ite_eq_left h

private theorem daCumNeg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]

-- In this range the last four inclusion-exclusion terms have negative indices.
private theorem daCum (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ 2 * d) :
    cumulative d u = denominator u - daTriple (u - d) := by
  by_cases h : u < 0
  · rw [daCumNeg d u h, daDenNeg u h, daTriple,
      daDenNeg (u - d - 1) (by omega), daDenNeg (u - d - 2) (by omega), daDenNeg (u - d - 3) (by omega)]
    omega
  · simp only [cumulative, show ¬ d < 0 by omega, h, decide_false, Bool.false_or,
      Bool.false_eq_true, ite_false, min_eq_left (show u ≤ 3 * d by omega),
      daDenNeg (u - 2 * d - 3) (by omega), daDenNeg (u - 2 * d - 4) (by omega),
      daDenNeg (u - 2 * d - 5) (by omega), daDenNeg (u - 3 * d - 6) (by omega), daTriple]
    omega

private theorem daCumLow (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u := by
  rw [daCum d u hd (by omega), daTriple, daDenNeg (u - d - 1) (by omega), daDenNeg (u - d - 2) (by omega),
    daDenNeg (u - d - 3) (by omega)]
  omega

private theorem daCap (d u c : ℤ) (hc : 0 ≤ c) (hu : u ≤ 3 * c) :
    cappedCount d u c = cumulative d u := by
  simp [cappedCount, show ¬ c < 0 by omega, daCumNeg (d - c - 1) (u - 3 * (c + 1)) (by omega)]

private def daOld (d s q k : ℤ) : ℤ :=
  denominator (1650 - 3 * k) - daTriple (1650 - d) - denominator (s - 1351 - q - 2 * k)

private def daTarget (d q k : ℤ) : ℤ :=
  denominator (1649 - q - 3 * k) - daTriple (1649 - q - d)

private def daFlag (d s q k : ℤ) : Flag :=
  ⟨d - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩

-- On this window the cap subtraction vanishes. In the target count the
-- two lower-bound terms cancel, and the removed upper term is zero.
private theorem daCounts (d s q k : ℤ)
    (hd : 1419 ≤ d) (hD : d ≤ 1650) (hs : 1419 ≤ s) (hS : s ≤ 1757)
    (hq : 0 ≤ q) (hQ : q ≤ 70) (hk : 0 ≤ k) (hK : k ≤ 256) :
    oldCount (daFlag d s q k) = daOld d s q k ∧
    kernelLower (daFlag d s q k) = daOld d s q k - daTarget d q k := by
  let D := d - 3 * k
  let L := s - 1350 - q - 2 * k
  let U := 1650 - 3 * k
  let C := 550 - k
  let O := 1650 - q - 3 * k
  let R := (O - 1 - L + D) / 4 + 1
  have hD0 : 0 ≤ D := by dsimp [D]; omega
  have hC0 : 0 ≤ C := by dsimp [C]; omega
  have hU0 : 0 ≤ U := by dsimp [U]; omega
  have hbal : 0 ≤ O - 1 - L + D := by dsimp [D,O,L]; omega
  have hrem : (O - 1 - L + D) / 4 ≤ D := by dsimp [D,O,L]; omega
  have hr : 0 ≤ D - R := by dsimp [R,D,O,L]; omega
  have hcut : O - 1 - 3 * R < 0 := by dsimp [R,D,O,L]; omega
  have hlow : L - 1 ≤ D - R := by dsimp [R,D,O,L]; omega
  have ho : oldCount (daFlag d s q k) = daOld d s q k := by
    change cappedCount D U C - cappedCount D (min U (L - 1)) C = _
    rw [min_eq_right (show L - 1 ≤ U by dsimp [L,U]; omega),
      daCap D U C hC0 (by dsimp [U,C]; omega),
      daCap D (L - 1) C hC0 (by dsimp [L,C]; omega),
      daCum D U hD0 (by dsimp [D,U]; omega),
      daCumLow D (L - 1) hD0 (by dsimp [D,L]; omega), daOld]
    rw [show U - D = 1650 - d by dsimp [U,D]; omega,
      show L - 1 = s - 1351 - q - 2 * k by dsimp [L]; omega]
  have ht : targetCount (daFlag d s q k) = daTarget d q k := by
    change (if O - 1 - L + D < 0 then 0 else _) = _
    rw [ite_eq_right (by omega)]
    change cumulative D (O - 1) - cumulative (D - (min D ((O - 1 - L + D) / 4) + 1))
        (O - 1 - 3 * (min D ((O - 1 - L + D) / 4) + 1)) - cumulative D (L - 1) +
        cumulative (D - (min D ((O - 1 - L + D) / 4) + 1)) (L - 1) = _
    rw [min_eq_right hrem]
    change cumulative D (O - 1) - cumulative (D - R) (O - 1 - 3 * R) -
        cumulative D (L - 1) + cumulative (D - R) (L - 1) = _
    rw [daCum D (O - 1) hD0 (by dsimp [D,O]; omega), daCumNeg _ _ hcut,
      daCumLow D (L - 1) hD0 (by dsimp [L,D]; omega), daCumLow (D - R) (L - 1) hr hlow,
      daTarget, show O - 1 - D = 1649 - q - d by dsimp [O,D]; omega,
      show O - 1 = 1649 - q - 3 * k by dsimp [O]; omega]
    omega
  refine ⟨ho, ?_⟩
  change (if D < 0 || U < 0 || C < 0 then 0 else _) = _
  simp only [show ¬ D < 0 by omega, show ¬ U < 0 by omega, show ¬ C < 0 by omega,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false]
  rw [ho, ht]

private def daSavings (s q k : ℕ) : ℕ :=
  let d := min (s : ℤ) 1650
  let old := daOld d s q 0
  let low := max 0 (old - daTarget d q 0)
  let res := daOld d s q k - daTarget d q k
  (old - low).toNat - (old - max low res).toNat

private theorem daWindow (s q : ℕ) (hs : s ≤ 1757) :
    windowFlag s (3000 + q - s) = daFlag (min (s : ℤ) 1650) s q 0 := by
  simp [windowFlag, daFlag, Nat.cast_sub (show s ≤ 3000 + q by omega)]
  omega

private theorem daCubic (d s q : ℤ) (k : ℕ) :
    cubicFlag (daFlag d s q 0) k = daFlag d s q k := by
  simp [cubicFlag, daFlag]

private theorem daSavings_eq (s q k : ℕ) (hs : 1419 ≤ s) (hS : s ≤ 1757)
    (hq : q ≤ 70) (hk : k ≤ 256) (hk' : k ≠ 0) :
    cubicSavings s (3000 + q - s) k = daSavings s q k := by
  let d := min (s : ℤ) 1650
  have hd : 1419 ≤ d := by dsimp [d]; omega
  have hD : d ≤ 1650 := min_le_right _ _
  have hb := daCounts d s q 0 hd hD (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hr := daCounts d s q k hd hD (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  simp only [cubicSavings, ite_eq_right hk', daWindow s q hS, daCubic]
  change (oldCount (daFlag d s q 0) - max 0 (kernelLower (daFlag d s q 0))).toNat -
    (oldCount (daFlag d s q 0) - max (max 0 (kernelLower (daFlag d s q 0)))
      (kernelLower (daFlag d s q k))).toNat = _
  rw [hb.1, hb.2, hr.2]
  rfl

-- These rounded cubics give D(n - 1) and D(n - 1) + D(n - 2) + D(n - 3).
-- The shifted index reserves zero for negative denominator arguments.
private def daDenValue (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 15) + 30) + 25) / 72

private def daTripleValue (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 9) + 10) + 3) / 24

-- Splitting the integer argument modulo 12 resolves both divisions in the original formula.
private theorem daDenResidue (a r : ℤ) (hr : 0 ≤ r) (hR : r ≤ 11) :
    let q := 2 * a + r / 6
    let m := r % 6
    let z := 12 * a + r
    1 + m * (m + 1) / 2 + q * (22 + 7 * m + m * (m - 1) / 2) +
      (57 + 6 * m) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2) =
      ((z + 1) * ((z + 1) * (2 * (z + 1) + 15) + 30) + 25) / 72 := by
  dsimp only
  interval_cases r <;> norm_num <;> ring_nf <;> omega

private theorem daDenValue_eq (x : ℤ) :
    denominator x = (daDenValue (x + 1).toNat : ℤ) := by
  by_cases hx : x < 0
  · rw [show (x + 1).toNat = 0 by omega, denominator, ite_eq_left hx]
    decide +kernel
  · have he : x = 12 * (x / 12) + x % 12 := by omega
    have hq : x / 6 = 2 * (x / 12) + (x % 12) / 6 := by omega
    have hr : x % 6 = (x % 12) % 6 := by omega
    have hv := daDenResidue (x / 12) (x % 12) (by omega) (by omega)
    dsimp only at hv
    rw [← he, ← hq, ← hr] at hv
    rw [denominator, ite_eq_right hx]
    unfold daDenValue
    push_cast
    rw [show ((x + 1).toNat : ℤ) = x + 1 by omega]
    exact hv

private theorem daTriResidue (a r : ℤ) (hr : 0 ≤ r) (hR : r ≤ 11) :
    let f := fun t : ℤ => (t * (t * (2 * t + 15) + 30) + 25) / 72
    let z := 12 * a + r
    f z + f (z - 1) + f (z - 2) = (z * (z * (2 * z + 9) + 10) + 3) / 24 := by
  dsimp only
  interval_cases r <;> ring_nf <;> omega

private theorem daTripleValue_eq (x : ℤ) :
    daTriple x = (daTripleValue x.toNat : ℤ) := by
  by_cases hn : x < 0
  · rw [show x.toNat = 0 by omega]
    simp only [daTriple, denominator, show x - 1 < 0 by omega, show x - 2 < 0 by omega,
      show x - 3 < 0 by omega, ite_true]
    decide +kernel
  by_cases hsmall : x < 3
  · interval_cases x <;> decide +kernel
  rw [daTriple, daDenValue_eq (x - 1), daDenValue_eq (x - 2), daDenValue_eq (x - 3)]
  unfold daDenValue daTripleValue
  push_cast
  rw [show ((x - 1 + 1).toNat : ℤ) = x by omega,
    show ((x - 2 + 1).toNat : ℤ) = x - 1 by omega,
    show ((x - 3 + 1).toNat : ℤ) = x - 2 by omega,
    show (x.toNat : ℤ) = x by omega]
  have hv := daTriResidue (x / 12) (x % 12) (by omega) (by omega)
  dsimp only at hv
  rwa [show 12 * (x / 12) + x % 12 = x by omega] at hv

private def daNatSavings (s q k : ℕ) : ℕ :=
  let d := min s 1650
  let upperCorr := daTripleValue (1650 - d)
  let targetCorr := daTripleValue (1649 - q - d)
  let lowerDen := daDenValue (s - 1350 - q)
  let low := 125576826 + targetCorr - (upperCorr + lowerDen + daDenValue (1650 - q))
  let rank := 125576826 - (upperCorr + lowerDen + low)
  let gain := daDenValue (1651 - 3 * k) + targetCorr -
    (upperCorr + daDenValue (s - 1350 - q - 2 * k) + daDenValue (1650 - q - 3 * k) + low)
  min rank gain

-- Express the signed, clipped rank difference using truncated Nat subtraction.
private theorem daNatClip (p t b a v pk bk ak : ℕ) :
    let old : ℤ := (p : ℤ) - t - b
    let low := max 0 (old - ((a : ℤ) - v))
    let res := (pk : ℤ) - t - bk - ((ak : ℤ) - v)
    let natLow := p + v - (t + b + a)
    (old - low).toNat - (old - max low res).toNat =
      min (p - (t + b + natLow)) (pk + v - (t + bk + ak + natLow)) := by
  dsimp only
  omega

private theorem daNatSavings_eq (s q k : ℕ) : daSavings s q k = daNatSavings s q k := by
  let d := min s 1650
  have hd' : min (s : ℤ) 1650 = (d : ℤ) := by dsimp [d]; omega
  have ht (z : ℤ) (n : ℕ) (hn : z.toNat = n) :
      daTriple z = (daTripleValue n : ℤ) := hn ▸ daTripleValue_eq z
  have hv (z : ℤ) (n : ℕ) (hn : (z + 1).toNat = n) :
      denominator z = (daDenValue n : ℤ) := hn ▸ daDenValue_eq z
  unfold daSavings daOld daTarget
  simp only [hd', mul_zero, sub_zero]
  rw [ht (1650 - (d : ℤ)) (1650 - d) (by omega),
      ht (1649 - (q : ℤ) - (d : ℤ)) (1649 - q - d) (by omega),
      hv 1650 1651 (by decide),
      hv ((s : ℤ) - 1351 - q) (s - 1350 - q) (by omega),
      hv (1649 - (q : ℤ)) (1650 - q) (by omega),
      hv (1650 - 3 * (k : ℤ)) (1651 - 3 * k) (by omega),
      hv ((s : ℤ) - 1351 - q - 2 * (k : ℤ)) (s - 1350 - q - 2 * k) (by omega),
      hv (1649 - (q : ℤ) - 3 * (k : ℤ)) (1650 - q - 3 * k) (by omega)]
  rw [show daDenValue 1651 = 125576826 by decide +kernel]
  exact daNatClip _ _ _ _ _ _ _ _

private def daEntry (s q k : ℕ) : ℕ :=
  let j := 3000 + q - s
  if 993 ≤ j ∧ j ≤ 1581 then
    if k = 0 then 0 else if k ≤ 256 then daNatSavings s q k else cubicSavings s j k
  else 0

private theorem daEntry_eq (s q k : ℕ) (hs : 1419 ≤ s) (hS : s ≤ 1757) (hq : q ≤ 70) :
    entry s q k = daEntry s q k := by
  by_cases hz : k = 0
  · simp [entry, daEntry, hz, cubicSavings]
  · by_cases hK : k ≤ 256
    · simp only [entry, daEntry, ite_eq_right hz, ite_eq_left hK,
        daSavings_eq s q k hs hS hq hK hz, daNatSavings_eq s q k]
    · simp only [entry, daEntry, ite_eq_right hz, ite_eq_right hK]

-- Once all base-512 digits are consumed, the remaining terms vanish.
private theorem daRowZero (s q n : ℕ) : rowSum s q 0 n = 0 := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [rowSum, entry, cubicSavings, ih]

private def daRow (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if code = 0 then 0 else
      daEntry s q (code % 512) + daRow s (q + 1) (code / 512) n

private theorem daRow_eq (s q code n : ℕ) (hs : 1419 ≤ s) (hS : s ≤ 1757)
    (hn : q + n ≤ 71) : rowSum s q code n = daRow s q code n := by
  induction n generalizing code q with
  | zero => rfl
  | succ n ih =>
    by_cases hz : code = 0
    · subst code
      simp [daRowZero, daRow]
    · rw [rowSum, daRow, ite_eq_right hz, daEntry_eq s q _ hs hS (by omega),
        ih (q + 1) (code / 512) (by omega)]

private def daRows (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: more => daRow s 0 code 71 + daRows (s + 1) more

private theorem daRows_eq (s : ℕ) (xs : List ℕ) (hs : 1419 ≤ s) (he : s + xs.length ≤ 1758) :
    rowsSum s xs = daRows s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih =>
    simp only [List.length_cons] at he
    rw [rowsSum, daRows, daRow_eq s 0 c 71 hs (by omega) (by decide),
      ih (s + 1) (by omega) (by omega)]

private theorem daChecked (s : ℕ) (xs : List ℕ) (n total : ℕ)
    (h : xs.length = n ∧ 1419 ≤ s ∧ s + n ≤ 1758 ∧ daRows s xs = total) :
    xs.length = n ∧ rowsSum s xs = total :=
  ⟨h.1, (daRows_eq s xs h.2.1 (h.1.symm ▸ h.2.2.1)).trans h.2.2.2⟩

private theorem daAppend {s n m a b : ℕ} {xs ys : List ℕ}
    (hx : xs.length = n ∧ rowsSum s xs = a)
    (hy : ys.length = m ∧ rowsSum (s + n) ys = b) :
    (xs ++ ys).length = n + m ∧ rowsSum s (xs ++ ys) = a + b := by
  simp only [List.length_append, rowsSum_append, hx.1, hx.2, hy.1, hy.2, and_self]

/-- The certificate encodes a row per grade. The base-512 digit of index
`q` is the cubic exponent on the diagonal `s + j = 3000 + q`. -/
private def rowsA1_chunk000 : List ℕ := [1, 1, 2, 2]

private theorem rowsA1_chunk000_checked : rowsA1_chunk000.length = 4 ∧ rowsSum 1419 rowsA1_chunk000 = 184 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk004 : List ℕ := [3, 3, 4, 4]

private theorem rowsA1_chunk004_checked : rowsA1_chunk004.length = 4 ∧ rowsSum 1423 rowsA1_chunk004 = 1104 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk008 : List ℕ := [5, 6, 6, 6]

private theorem rowsA1_chunk008_checked : rowsA1_chunk008.length = 4 ∧ rowsSum 1427 rowsA1_chunk008 = 2856 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk012 : List ℕ := [7, 8, 8, 8]

private theorem rowsA1_chunk012_checked : rowsA1_chunk012.length = 4 ∧ rowsSum 1431 rowsA1_chunk012 = 5512 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk016 : List ℕ := [9, 9, 10, 12]

private theorem rowsA1_chunk016_checked : rowsA1_chunk016.length = 4 ∧ rowsSum 1435 rowsA1_chunk016 = 9050 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk020 : List ℕ := [12, 12, 12, 12]

private theorem rowsA1_chunk020_checked : rowsA1_chunk020.length = 4 ∧ rowsSum 1439 rowsA1_chunk020 = 13632 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk024 : List ℕ := [13, 13, 16, 16]

private theorem rowsA1_chunk024_checked : rowsA1_chunk024.length = 4 ∧ rowsSum 1443 rowsA1_chunk024 = 19103 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk028 : List ℕ := [16, 16, 16, 529]

private theorem rowsA1_chunk028_checked : rowsA1_chunk028.length = 4 ∧ rowsSum 1447 rowsA1_chunk028 = 25884 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk032 : List ℕ := [1041, 1042, 1554, 1555]

private theorem rowsA1_chunk032_checked : rowsA1_chunk032.length = 4 ∧ rowsSum 1451 rowsA1_chunk032 = 34333 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk036 : List ℕ := [2067, 2068, 2584, 3096]

private theorem rowsA1_chunk036_checked : rowsA1_chunk036.length = 4 ∧ rowsSum 1455 rowsA1_chunk036 = 44501 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk040 : List ℕ := [3096, 3096, 3608, 4120]

private theorem rowsA1_chunk040_checked : rowsA1_chunk040.length = 4 ∧ rowsSum 1459 rowsA1_chunk040 = 57794 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk044 : List ℕ := [4120, 4120, 4632, 4633]

private theorem rowsA1_chunk044_checked : rowsA1_chunk044.length = 4 ∧ rowsSum 1463 rowsA1_chunk044 = 73760 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk048 : List ℕ := [5145, 6170, 6170, 6171]

private theorem rowsA1_chunk048_checked : rowsA1_chunk048.length = 4 ∧ rowsSum 1467 rowsA1_chunk048 = 91810 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk052 : List ℕ := [6171, 6688, 268832, 269344]

private theorem rowsA1_chunk052_checked : rowsA1_chunk052.length = 4 ∧ rowsSum 1471 rowsA1_chunk052 = 111993 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk056 : List ℕ := [532512, 532512, 794656, 794656]

private theorem rowsA1_chunk056_checked : rowsA1_chunk056.length = 4 ∧ rowsSum 1475 rowsA1_chunk056 = 136932 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk060 : List ℕ := [1056800, 1319456, 1581601, 1582113]

private theorem rowsA1_chunk060_checked : rowsA1_chunk060.length = 4 ∧ rowsSum 1479 rowsA1_chunk060 = 166213 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk064 : List ℕ := [1582114, 1844770, 2106915, 2107427]

private theorem rowsA1_chunk064_checked : rowsA1_chunk064.length = 4 ∧ rowsSum 1483 rowsA1_chunk064 = 199448 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk068 : List ℕ := [2109476, 2371620, 2371620, 2633766]

private theorem rowsA1_chunk068_checked : rowsA1_chunk068.length = 4 ∧ rowsSum 1487 rowsA1_chunk068 = 236173 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk072 : List ℕ := [3158054, 3158054, 137375782, 137375784]

private theorem rowsA1_chunk072_checked : rowsA1_chunk072.length = 4 ∧ rowsSum 1491 rowsA1_chunk072 = 279400 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk076 : List ℕ := [271594032, 406073904, 406336560, 541078576]

private theorem rowsA1_chunk076_checked : rowsA1_chunk076.length = 4 ∧ rowsSum 1495 rowsA1_chunk076 = 323511 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk080 : List ℕ := [541079088, 675296816, 809515056, 809517104]

private theorem rowsA1_chunk080_checked : rowsA1_chunk080.length = 4 ∧ rowsSum 1499 rowsA1_chunk080 = 380169 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk084 : List ℕ := [809779248, 943996976, 1078476848, 1078476848]

private theorem rowsA1_chunk084_checked : rowsA1_chunk084.length = 4 ∧ rowsSum 1503 rowsA1_chunk084 = 443081 := by
  apply daChecked
  decide +kernel

private def rowsA1_chunk088 : List ℕ := [1078738992, 1212956720]

private theorem rowsA1_chunk088_checked : rowsA1_chunk088.length = 2 ∧ rowsSum 1507 rowsA1_chunk088 = 247486 := by
  apply daChecked
  decide +kernel

private def rowsA1 : List ℕ := rowsA1_chunk000 ++ rowsA1_chunk004 ++ rowsA1_chunk008 ++ rowsA1_chunk012 ++ rowsA1_chunk016 ++ rowsA1_chunk020 ++ rowsA1_chunk024 ++ rowsA1_chunk028 ++ rowsA1_chunk032 ++ rowsA1_chunk036 ++ rowsA1_chunk040 ++ rowsA1_chunk044 ++ rowsA1_chunk048 ++ rowsA1_chunk052 ++ rowsA1_chunk056 ++ rowsA1_chunk060 ++ rowsA1_chunk064 ++ rowsA1_chunk068 ++ rowsA1_chunk072 ++ rowsA1_chunk076 ++ rowsA1_chunk080 ++ rowsA1_chunk084 ++ rowsA1_chunk088

private theorem rowsA1_checked :
    rowsA1.length = 90 ∧ rowsSum 1419 rowsA1 = 2903929 :=
  daAppend rowsA1_chunk000_checked <|
  daAppend rowsA1_chunk004_checked <|
  daAppend rowsA1_chunk008_checked <|
  daAppend rowsA1_chunk012_checked <|
  daAppend rowsA1_chunk016_checked <|
  daAppend rowsA1_chunk020_checked <|
  daAppend rowsA1_chunk024_checked <|
  daAppend rowsA1_chunk028_checked <|
  daAppend rowsA1_chunk032_checked <|
  daAppend rowsA1_chunk036_checked <|
  daAppend rowsA1_chunk040_checked <|
  daAppend rowsA1_chunk044_checked <|
  daAppend rowsA1_chunk048_checked <|
  daAppend rowsA1_chunk052_checked <|
  daAppend rowsA1_chunk056_checked <|
  daAppend rowsA1_chunk060_checked <|
  daAppend rowsA1_chunk064_checked <|
  daAppend rowsA1_chunk068_checked <|
  daAppend rowsA1_chunk072_checked <|
  daAppend rowsA1_chunk076_checked <|
  daAppend rowsA1_chunk080_checked <|
  daAppend rowsA1_chunk084_checked <|
  rowsA1_chunk088_checked

private def rowsA2_chunk000 : List ℕ := [1213218864, 70336397360, 70336397872, 139055874609]

private theorem rowsA2_chunk000_checked : rowsA2_chunk000.length = 4 ∧ rowsSum 1509 rowsA2_chunk000 = 549100 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk004 : List ℕ := [139055875121, 207775352370, 207909570098, 276629047347]

private theorem rowsA2_chunk004_checked : rowsA2_chunk004.length = 4 ∧ rowsSum 1513 rowsA2_chunk004 = 631098 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk008 : List ℕ := [276763265075, 345751439412, 414470917172, 414471179316]

private theorem rowsA2_chunk008_checked : rowsA2_chunk008.length = 4 ∧ rowsSum 1517 rowsA2_chunk008 = 721185 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk012 : List ℕ := [483190656054, 551910394934, 552044613686, 552044879926]

private theorem rowsA2_chunk012_checked : rowsA2_chunk012.length = 4 ∧ rowsSum 1521 rowsA2_chunk012 = 818867 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk016 : List ℕ := [620899622968, 35805405929536, 35874125406272, 71196070666304]

private theorem rowsA2_chunk016_checked : rowsA2_chunk016.length = 4 ∧ rowsSum 1525 rowsA2_chunk016 = 919874 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk020 : List ℕ := [71196607537216, 106380979626048, 106380979626048, 141565351714880]

private theorem rowsA2_chunk020_checked : rowsA2_chunk020.length = 4 ∧ rowsSum 1529 rowsA2_chunk020 = 1043682 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk024 : List ℕ := [141634071453760, 176887163019328, 212208974323776, 212208974323776]

private theorem rowsA2_chunk024_checked : rowsA2_chunk024.length = 4 ∧ rowsSum 1533 rowsA2_chunk024 = 1181252 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk028 : List ℕ := [247393346674752, 282577852981312, 282577987461184, 282646706937920]

private theorem rowsA2_chunk028_checked : rowsA2_chunk028.length = 4 ∧ rowsSum 1537 rowsA2_chunk028 = 1328543 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk032 : List ℕ := [18332229722726976, 18332298442728000, 36381881458517057, 36452319459042369]

private theorem rowsA2_chunk032_checked : rowsA2_chunk032.length = 4 ∧ rowsSum 1541 rowsA2_chunk032 = 1486575 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk036 : List ℕ := [54466717968524866, 54467061566432834, 72481460078012483, 90531042959583299]

private theorem rowsA2_chunk036_checked : rowsA2_chunk036.length = 4 ∧ rowsSum 1545 rowsA2_chunk036 = 1653595 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk040 : List ℕ := [108545441469065284, 108580625841155140, 108650994585332804, 126665393094814790]

private theorem rowsA2_chunk040_checked : rowsA2_chunk040.length = 4 ∧ rowsSum 1549 rowsA2_chunk040 = 1814289 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk044 : List ℕ := [144679791738515526, 144679791872733254, 9368051897446989894, 9386101480462778440]

private theorem rowsA2_chunk044_checked : rowsA2_chunk044.length = 4 ∧ rowsSum 1553 rowsA2_chunk044 = 1964020 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk048 : List ℕ := [18609473586037030984, 18663551966071783496, 27886959256018124872, 37110331361592377416]

private theorem rowsA2_chunk048_checked : rowsA2_chunk048.length = 4 ∧ rowsSum 1557 rowsA2_chunk048 = 2129047 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk052 : List ℕ := [37110366821110808652, 46333879595453939788, 55575266030818459724, 55575266030818459724]

private theorem rowsA2_chunk052_checked : rowsA2_chunk052.length = 4 ∧ rowsSum 1561 rowsA2_chunk052 = 2309631 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk056 : List ℕ := [55593280429596639308, 64852681264544120908, 74076053301399158860, 4796442536171044372556]

private theorem rowsA2_chunk056_checked : rowsA2_chunk056.length = 4 ∧ rowsSum 1565 rowsA2_chunk056 = 2504617 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk060 : List ℕ := [4805665908207899410512, 9528050440729145671776, 9537273812766000447584, 14278105089360956785248]

private theorem rowsA2_chunk060_checked : rowsA2_chunk060.length = 4 ∧ rowsSum 1569 rowsA2_chunk060 = 2708537 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk064 : List ℕ := [19000471572299321476192, 19000489621882203047008, 23722856104820567737952, 28445240637273095046752]

private theorem rowsA2_chunk064_checked : rowsA2_chunk064.length = 4 ∧ rowsSum 1573 rowsA2_chunk064 = 2946193 := by
  apply daChecked
  decide +kernel

private def rowsA2_chunk068 : List ℕ := [28454536207641478203488, 28454536207778917156960]

private theorem rowsA2_chunk068_checked : rowsA2_chunk068.length = 2 ∧ rowsSum 1577 rowsA2_chunk068 = 1563390 := by
  apply daChecked
  decide +kernel

private def rowsA2 : List ℕ := rowsA2_chunk000 ++ rowsA2_chunk004 ++ rowsA2_chunk008 ++ rowsA2_chunk012 ++ rowsA2_chunk016 ++ rowsA2_chunk020 ++ rowsA2_chunk024 ++ rowsA2_chunk028 ++ rowsA2_chunk032 ++ rowsA2_chunk036 ++ rowsA2_chunk040 ++ rowsA2_chunk044 ++ rowsA2_chunk048 ++ rowsA2_chunk052 ++ rowsA2_chunk056 ++ rowsA2_chunk060 ++ rowsA2_chunk064 ++ rowsA2_chunk068

private theorem rowsA2_checked :
    rowsA2.length = 70 ∧ rowsSum 1509 rowsA2 = 28273495 :=
  daAppend rowsA2_chunk000_checked <|
  daAppend rowsA2_chunk004_checked <|
  daAppend rowsA2_chunk008_checked <|
  daAppend rowsA2_chunk012_checked <|
  daAppend rowsA2_chunk016_checked <|
  daAppend rowsA2_chunk020_checked <|
  daAppend rowsA2_chunk024_checked <|
  daAppend rowsA2_chunk028_checked <|
  daAppend rowsA2_chunk032_checked <|
  daAppend rowsA2_chunk036_checked <|
  daAppend rowsA2_chunk040_checked <|
  daAppend rowsA2_chunk044_checked <|
  daAppend rowsA2_chunk048_checked <|
  daAppend rowsA2_chunk052_checked <|
  daAppend rowsA2_chunk056_checked <|
  daAppend rowsA2_chunk060_checked <|
  daAppend rowsA2_chunk064_checked <|
  rowsA2_chunk068_checked

private def rowsA3_chunk000 : List ℕ := [33204572806759126698080, 2455778578518887121325152, 2455778578518887121325152, 4878352584231152689122400]

private theorem rowsA3_chunk000_checked : rowsA3_chunk000.length = 4 ∧ rowsSum 1579 rowsA3_chunk000 = 3338238 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk004 : List ℕ := [4878352584231702444936288, 7300935813315867428556896, 7310380564331189600555104, 9728241426932484938960992]

private theorem rowsA3_chunk004_checked : rowsA3_chunk004.length = 4 ∧ rowsSum 1583 rowsA3_chunk004 = 3625471 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk008 : List ℕ := [12146093084211326169944160, 14563953946812621508350048, 14563963188234241244696672, 14568722466219656818497632]

private theorem rowsA3_chunk008_checked : rowsA3_chunk008.length = 4 ∧ rowsSum 1587 rowsA3_chunk008 = 3946296 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk012 : List ℕ := [16991296544024563491575904, 1257358632201599836030539872, 1257358632201670204774717536, 2495298671487050479674103904]

private theorem rowsA3_chunk012_checked : rowsA3_chunk012.length = 4 ∧ rowsSum 1591 rowsA3_chunk012 = 4286127 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk016 : List ℕ := [2497716523126279738292213856, 3738074414050889272614492256, 4980854878981281302602096736, 4980854888204653339456872544]

private theorem rowsA3_chunk016_checked : rowsA3_chunk016.length = 4 ∧ rowsSum 1595 rowsA3_chunk016 = 4649499 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk020 : List ℕ := [6218799649856798027697668192, 7456744420750047607606263904, 7456744420768062074835222624, 7459167003997146239685148768]

private theorem rowsA3_chunk020_checked : rowsA3_chunk020.length = 4 ∧ rowsSum 1599 rowsA3_chunk020 = 5008695 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk024 : List ℕ := [642522426046881173208745689184, 643762783947029154778849001568, 1277592919801333816658547490913, 1278830859840619196933447139425]

private theorem rowsA3_chunk024_checked : rowsA3_chunk024.length = 4 ∧ rowsSum 1603 rowsA3_chunk024 = 5391796 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk028 : List ℕ := [1912656159954733897681798742114, 1913894099994055306891155783778, 2550197698038379997447655047267, 2550197698038379997447655047267]

private theorem rowsA3_chunk028_checked : rowsA3_chunk028.length = 4 ∧ rowsSum 1607 rowsA3_chunk028 = 5767634 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk032 : List ℕ := [3817850720840651140006811844708, 3817850720840651140006946062436, 3817853143424024339909627134052, 328971472459855790433347382067302]

private theorem rowsA3_chunk032_checked : rowsA3_chunk032.length = 4 ∧ rowsSum 1611 rowsA3_chunk032 = 6156288 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk036 : List ℕ := [329606545376147337321494902521958, 654127574914652634900385227653222, 654127574919384224755291727642726, 979279953896823755577896041758824]

private theorem rowsA3_chunk036_checked : rowsA3_chunk036.length = 4 ∧ rowsSum 1615 rowsA3_chunk036 = 6577418 := by
  apply daChecked
  decide +kernel

private def rowsA3_chunk040 : List ℕ := [979913779196937870278644394410088, 1305699983455592826498481490280552]

private theorem rowsA3_chunk040_checked : rowsA3_chunk040.length = 2 ∧ rowsSum 1619 rowsA3_chunk040 = 3462537 := by
  apply daChecked
  decide +kernel

private def rowsA3 : List ℕ := rowsA3_chunk000 ++ rowsA3_chunk004 ++ rowsA3_chunk008 ++ rowsA3_chunk012 ++ rowsA3_chunk016 ++ rowsA3_chunk020 ++ rowsA3_chunk024 ++ rowsA3_chunk028 ++ rowsA3_chunk032 ++ rowsA3_chunk036 ++ rowsA3_chunk040

private theorem rowsA3_checked :
    rowsA3.length = 42 ∧ rowsSum 1579 rowsA3 = 52209999 :=
  daAppend rowsA3_chunk000_checked <|
  daAppend rowsA3_chunk004_checked <|
  daAppend rowsA3_chunk008_checked <|
  daAppend rowsA3_chunk012_checked <|
  daAppend rowsA3_chunk016_checked <|
  daAppend rowsA3_chunk020_checked <|
  daAppend rowsA3_chunk024_checked <|
  daAppend rowsA3_chunk028_checked <|
  daAppend rowsA3_chunk032_checked <|
  daAppend rowsA3_chunk036_checked <|
  rowsA3_chunk040_checked

private def rowsA4_chunk000 : List ℕ := [1630219775054077285405986392162408, 1954739566652543297569417311862888, 1954739569070394936869044405452908, 1954740807010434222249319573012588]

private theorem rowsA4_chunk000_checked : rowsA4_chunk000.length = 4 ∧ rowsSum 1621 rowsA4_chunk000 = 7260342 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk004 : List ℕ := [168433392661501329262682438539198572, 168757912453104591428305033942319212, 334913318356302149032686757867470956, 501391336383075059872727271399800940]

private theorem rowsA4_chunk004_checked : rowsA4_chunk004.length = 4 ∧ rowsSum 1625 rowsA4_chunk004 = 7766341 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk008 : List ℕ := [501391336385497633896453866623385708, 667869354421941951293129939113525356, 668518391529263527131193588028850288, 834672524827678125376884617424978560]

private theorem rowsA4_chunk008_checked : rowsA4_chunk008.length = 4 ∧ rowsSum 1629 rowsA4_chunk008 = 8309886 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk012 : List ℕ := [1000826024300792609489860568679498368, 1000826658126102168355541523550487680, 86237572522897072671712250287278310528, 86404050540923845582552009325833930368]

private theorem rowsA4_chunk012_checked : rowsA4_chunk012.length = 4 ∧ rowsSum 1633 rowsA4_chunk012 = 8898525 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk016 : List ℕ := [171474967424775369473291520037332502144, 171475618997186304634843118601129478272, 256712364228132012803016989573667408000, 341782955959606986559785250967005481088]

private theorem rowsA4_chunk016_checked : rowsA4_chunk016.length = 4 ∧ rowsSum 1637 rowsA4_chunk016 = 9516978 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk020 : List ℕ := [341949109464034279052715006141944351872, 427352008193215123896152096989887122560, 512422924442005816040361761262199164032, 512423248960559474476311951639446604928]

private theorem rowsA4_chunk020_checked : rowsA4_chunk020.length = 4 ∧ rowsSum 1641 rowsA4_chunk020 = 10091626 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk024 : List ℕ := [44068566214840682797788261702905777672320, 44238873876953008938257405332421372596352, 87795016842833132261578578455724558438528, 131351326287365107657915482701962168815744]

private theorem rowsA4_chunk024_checked : rowsA4_chunk024.length = 4 ∧ rowsSum 1645 rowsA4_chunk024 = 10709640 := by
  apply daChecked
  decide +kernel

private def rowsA4_chunk028 : List ℕ := [131436730484169745912199023312185233297536, 174992873450683694535643534508273625520256, 175077944043049011734475892075221613598848, 218804228194924905489975988003565979359360]

private theorem rowsA4_chunk028_checked : rowsA4_chunk028.length = 4 ∧ rowsSum 1649 rowsA4_chunk028 = 11354713 := by
  apply daChecked
  decide +kernel

private def rowsA4 : List ℕ := rowsA4_chunk000 ++ rowsA4_chunk004 ++ rowsA4_chunk008 ++ rowsA4_chunk012 ++ rowsA4_chunk016 ++ rowsA4_chunk020 ++ rowsA4_chunk024 ++ rowsA4_chunk028

private theorem rowsA4_checked :
    rowsA4.length = 32 ∧ rowsSum 1621 rowsA4 = 73908051 :=
  daAppend rowsA4_chunk000_checked <|
  daAppend rowsA4_chunk004_checked <|
  daAppend rowsA4_chunk008_checked <|
  daAppend rowsA4_chunk012_checked <|
  daAppend rowsA4_chunk016_checked <|
  daAppend rowsA4_chunk020_checked <|
  daAppend rowsA4_chunk024_checked <|
  rowsA4_chunk028_checked

private def rowsA5_chunk000 : List ℕ := [262360537314305739867811336110989744593024, 262360537314305739872552149338207977527424, 22606662044964309715786179557070288086947968, 44951048457052543215265797989676111767328896]

private theorem rowsA5_chunk000_checked : rowsA5_chunk000.length = 4 ∧ rowsSum 1653 rowsA5_chunk000 = 12030169 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk004 : List ℕ := [44951048623530563717918787400195700121196672, 67251879059130935120848004740752226279809152, 67295606007894273605860984829710738635415680, 89596351206750049126359966328340272668278912]

private theorem rowsA5_chunk004_checked : rowsA5_chunk004.length = 4 ∧ rowsSum 1657 rowsA5_chunk004 = 12736568 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk008 : List ℕ := [112027764834178315113745699021143720454062208, 134328510033034100537760272436332584035221632, 134328595104923904987019289938097203859488896, 11552310136752603587278607159648759043273064576]

private theorem rowsA5_chunk008_checked : rowsA5_chunk008.length = 4 ∧ rowsSum 1661 rowsA5_chunk008 = 13509033 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk012 : List ℕ := [11574610967021725940654758743765059262721097856, 23014936810010902126213632940106344524631048320, 34432918436895326404387651045658933356170117249, 34455349935593347665786828424424981086825676929]

private theorem rowsA5_chunk012_checked : rowsA5_chunk012.length = 4 ∧ rowsSum 1665 rowsA5_chunk012 = 14361060 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk016 : List ℕ := [45873331817689547134664694127508666229679259778, 45895632562888077757808647697456572646553616514, 57358215595099296070584779809661524485991366787, 68776197136913129886177200129239092214776266884]

private theorem rowsA5_chunk016_checked : rowsA5_chunk016.length = 4 ∧ rowsSum 1669 rowsA5_chunk016 = 15213582 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk020 : List ℕ := [5914782790017332712168088371591640586814665851012, 5926200771558980715735113153477241789578581442692, 11783647646725581564101583631137487658552103338118, 17629654239605336527314999943750519643635174146182]

private theorem rowsA5_chunk020_checked : rowsA5_chunk020.length = 4 ∧ rowsSum 1673 rowsA5_chunk020 = 16020251 := by
  apply daChecked
  decide +kernel

private def rowsA5_chunk024 : List ℕ := [17629676540435605649668376095334635943854756397190, 23487145716347405028659230884446422870350489518214, 23498563872198695811996770338226847179025468686472]

private theorem rowsA5_chunk024_checked : rowsA5_chunk024.length = 3 ∧ rowsSum 1677 rowsA5_chunk024 = 12595054 := by
  apply daChecked
  decide +kernel

private def rowsA5 : List ℕ := rowsA5_chunk000 ++ rowsA5_chunk004 ++ rowsA5_chunk008 ++ rowsA5_chunk012 ++ rowsA5_chunk016 ++ rowsA5_chunk020 ++ rowsA5_chunk024

private theorem rowsA5_checked :
    rowsA5.length = 27 ∧ rowsSum 1653 rowsA5 = 96465717 :=
  daAppend rowsA5_chunk000_checked <|
  daAppend rowsA5_chunk004_checked <|
  daAppend rowsA5_chunk008_checked <|
  daAppend rowsA5_chunk012_checked <|
  daAppend rowsA5_chunk016_checked <|
  daAppend rowsA5_chunk020_checked <|
  rowsA5_chunk024_checked

private def rowsA6_chunk000 : List ℕ := [29367406384605602842908461587416285013898386538632, 35213412934014451260954146588670659100537497125000, 3028368788488533897513491167460055925280012872253576, 3034214795038197957706727556313648643549169159569544]

private theorem rowsA6_chunk000_checked : rowsA6_chunk000.length = 4 ∧ rowsSum 1680 rowsA6_chunk000 = 17567317 := by
  apply daChecked
  decide +kernel

private def rowsA6_chunk004 : List ℕ := [6033216177141955946987460403850593486796752676782216, 9026382948377186937301154880660503474702321918738572, 9026394388659473949664328437478540027048206819983500, 12025418606769871374672889911651616564186860004376716]

private theorem rowsA6_chunk004_checked : rowsA6_chunk004.length = 4 ∧ rowsSum 1684 rowsA6_chunk004 = 18497024 := by
  apply daChecked
  decide +kernel

private def rowsA6_chunk008 : List ℕ := [12031264702565731923434077340448703630098412228116620, 15036112068918068655568488603927264796406942938497164, 18029267422215313975016149089953638485114376188657804, 1550524819706085799051633964844696202559474385859707020]

private theorem rowsA6_chunk008_checked : rowsA6_chunk008.length = 4 ∧ rowsSum 1688 rowsA6_chunk008 = 19536570 := by
  apply daChecked
  decide +kernel

private def rowsA6_chunk012 : List ℕ := [3086013515925271903061735651427260728092872706363555980, 3089006682696681443528351097158860544955746139259339408, 4621508069569119711898191298893332446568723551747113616, 4621513926993650577157543162101378400562446411598202000]

private theorem rowsA6_chunk012_checked : rowsA6_chunk012.length = 4 ∧ rowsSum 1692 rowsA6_chunk012 = 20635869 := by
  apply daChecked
  decide +kernel

private def rowsA6_chunk016 : List ℕ := [6157014315248192602184840586294504074415299984680354960, 7692503068557242857958064002316072835277329170908120720, 9230984920151939839867903945682723779991179943970145936, 793868701843487035489483089825666333802838926634376038544]

private theorem rowsA6_chunk016_checked : rowsA6_chunk016.length = 4 ∧ rowsSum 1696 rowsA6_chunk016 = 21713176 := by
  apply daChecked
  decide +kernel

private def rowsA6_chunk020 : List ℕ := [793868707689515885558293294531200237355578215990684616848, 1580038920153739214197467140481127366008940568454730156176, 1581574414696054152775691918373315507834960895965543861392]

private theorem rowsA6_chunk020_checked : rowsA6_chunk020.length = 3 ∧ rowsSum 1700 rowsA6_chunk020 = 16957259 := by
  apply daChecked
  decide +kernel

private def rowsA6 : List ℕ := rowsA6_chunk000 ++ rowsA6_chunk004 ++ rowsA6_chunk008 ++ rowsA6_chunk012 ++ rowsA6_chunk016 ++ rowsA6_chunk020

private theorem rowsA6_checked :
    rowsA6.length = 23 ∧ rowsSum 1680 rowsA6 = 114907215 :=
  daAppend rowsA6_chunk000_checked <|
  daAppend rowsA6_chunk004_checked <|
  daAppend rowsA6_chunk008_checked <|
  daAppend rowsA6_chunk012_checked <|
  daAppend rowsA6_chunk016_checked <|
  rowsA6_chunk020_checked

private def rowsA7_chunk000 : List ℕ := [2366212131619389248255165920792832303977760603380639665296, 3152385343084950079842494123922771557652355891504665922712, 3152391329407074568762494765264312651303200363570301832344, 3938561571101308343274528120147479180176509093094742888600]

private theorem rowsA7_chunk000_checked : rowsA7_chunk000.length = 4 ∧ rowsSum 1703 rowsA7_chunk000 = 23599906 := by
  apply daChecked
  decide +kernel

private def rowsA7_chunk004 : List ℕ := [406460775343865362083502889905478967190309083364993706037400, 406460775343865362170615175837240451776972268282985639383192, 808979927118703037386816162914126537514723144351565297553560, 809764564835637812764582483450737448972660410064077133516952]

private theorem rowsA7_chunk004_checked : rowsA7_chunk004.length = 4 ∧ rowsSum 1707 rowsA7_chunk004 = 24803520 := by
  apply daChecked
  decide +kernel

private def rowsA7_chunk008 : List ℕ := [1211500611389127272718787298233896363520888183775137800198296, 1211500611389127295106644785292428190642050727108313530570904, 1614021295659494440879356825294957088523443496613691342788760, 2016543512431248436441056493059666223802749717108966579050648]

private theorem rowsA7_chunk008_checked : rowsA7_chunk008.length = 4 ∧ rowsSum 1711 rowsA7_chunk008 = 26030978 := by
  apply daChecked
  decide +kernel

private def rowsA7_chunk012 : List ℕ := [2419847310902464110833007867955968082184834824086641206171840, 208107916976059065386753479299297595944357683178377146364664000, 413795986641209820656124627451274041838728748723227142704928960, 414599457195840702710935280864525713788581414105007956356307136]

private theorem rowsA7_chunk012_checked : rowsA7_chunk012.length = 4 ∧ rowsSum 1715 rowsA7_chunk012 = 27292478 := by
  apply daChecked
  decide +kernel

private def rowsA7_chunk016 : List ℕ := [620288311498714238739932858487816655144931417346945351762911424, 620288313031233163632019011625162574024093143852806618286727360, 826378903377661142133843104915273630890151932221543550127513792, 1032068542318245755491386839729797654279403175700391040281813184]

private theorem rowsA7_chunk016_checked : rowsA7_chunk016.length = 4 ∧ rowsSum 1719 rowsA7_chunk016 = 28642995 := by
  apply daChecked
  decide +kernel

private def rowsA7 : List ℕ := rowsA7_chunk000 ++ rowsA7_chunk004 ++ rowsA7_chunk008 ++ rowsA7_chunk012 ++ rowsA7_chunk016

private theorem rowsA7_checked :
    rowsA7.length = 20 ∧ rowsSum 1703 rowsA7 = 130369877 :=
  daAppend rowsA7_chunk000_checked <|
  daAppend rowsA7_chunk004_checked <|
  daAppend rowsA7_chunk008_checked <|
  daAppend rowsA7_chunk012_checked <|
  rowsA7_chunk016_checked

private def rowsA8_chunk000 : List ℕ := [1238158348029949954727191987195624921824633744218736685085171904, 106551253491739248322664527712063886709323130602215337570571198656, 211863545160299428175935809084910801442406229178618105671433396416, 212069234014605289009893529401380629303024776122240989062204825792]

private theorem rowsA8_chunk000_checked : rowsA8_chunk000.length = 4 ∧ rowsSum 1723 rowsA8_chunk000 = 29931024 := by
  apply daChecked
  decide +kernel

private def rowsA8_chunk004 : List ℕ := [317587213752827626485916891486307596510998179175600447590951362752, 317587616271979407158180719025235480811657769092114839380795924672, 423105997744724781980350018103954916339029607253063770408501715136, 528419093666941820965583468381336377397400487354230715491708645568]

private theorem rowsA8_chunk004_checked : rowsA8_chunk004.length = 4 ∧ rowsSum 1727 rowsA8_chunk004 = 31362247 := by
  apply daChecked
  decide +kernel

private def rowsA8_chunk008 : List ℕ := [633937074191334376728978400874270500790820025226256055689011081408, 54554241787770495135358231595696955353923471973044403945145325662400, 108474135122073307226079134207918186721059457498802937867091018068160, 108579447815476375477524621164648523207084427748531867350340130123968]

private theorem rowsA8_chunk008_checked : rowsA8_chunk008.length = 4 ∧ rowsSum 1731 rowsA8_chunk008 = 32793617 := by
  apply daChecked
  decide +kernel

private def rowsA8_chunk012 : List ℕ := [162604653441447744749097435255229813982741869315050633729236020572352, 162604859531251920976292286697627666014235368095938750032197270450368, 216630065157229423223183917597331732163610314099788721776575946764480, 270550575957474212322686700324739351263421408356889578246953526964416]

private theorem rowsA8_chunk012_checked : rowsA8_chunk012.length = 4 ∧ rowsSum 1735 rowsA8_chunk012 = 34383972 := by
  apply daChecked
  decide +kernel

private def rowsA8_chunk016 : List ℕ := [27931561168745699198849434133033956680877202574290850142752003456053440, 27931771795338493509256646501953057573259101359986007820193111652511936]

private theorem rowsA8_chunk016_checked : rowsA8_chunk016.length = 2 ∧ rowsSum 1739 rowsA8_chunk016 = 17805320 := by
  apply daChecked
  decide +kernel

private def rowsA8 : List ℕ := rowsA8_chunk000 ++ rowsA8_chunk004 ++ rowsA8_chunk008 ++ rowsA8_chunk012 ++ rowsA8_chunk016

private theorem rowsA8_checked :
    rowsA8.length = 18 ∧ rowsSum 1723 rowsA8 = 146276180 :=
  daAppend rowsA8_chunk000_checked <|
  daAppend rowsA8_chunk004_checked <|
  daAppend rowsA8_chunk008_checked <|
  daAppend rowsA8_chunk012_checked <|
  rowsA8_chunk016_checked

private def rowsA9_chunk000 : List ℕ := [55538757182501533296759361361200422258537655024058364700822994134577344, 55646596969170135858931184774802190123866849612270681094461510603845824, 83253582562021245311537886850677664425558763928433767709830359973703872, 110860673467163238689600674193691976079724699124497022205915387522023616]

private theorem rowsA9_chunk000_checked : rowsA9_chunk000.length = 4 ∧ rowsSum 1741 rowsA9_chunk000 = 36670908 := by
  apply daChecked
  decide +kernel

private def rowsA9_chunk004 : List ℕ := [110914698672789994696589170387479527572897465646349105084407017323462848, 138521894890226795176720038282396062437946956281276246045170354840764608, 14301067158184466592364102622049244893728282195892657505731908823645520064, 14301067159213308676739403008955363987111598650029745641034156472400969920]

private theorem rowsA9_chunk004_checked : rowsA9_chunk004.length = 4 ∧ rowsSum 1745 rowsA9_chunk004 = 38204146 := by
  apply daChecked
  decide +kernel

private def rowsA9_chunk008 : List ℕ := [28463450662827545568579467281218451219350184679505683314499961509979979968, 42625834271754475864996333308560097068638240690928541028230557201692983488, 42625834271754877599507398056128982559162624055793805285886135523984113856, 56760664815187578206010554105438514035432545602686028350364866611219890368]

private theorem rowsA9_chunk008_checked : rowsA9_chunk008.length = 4 ∧ rowsSum 1749 rowsA9_chunk008 = 39928229 := by
  apply daChecked
  decide +kernel

private def rowsA9_chunk012 : List ℕ := [56788325720468477284653655215553554863217154558773105945404321563335033024, 7322091171019672569995483341672973481026032558829437468912101379019896881344, 7322146384990446895290420542489213342032737518416914882734108417791210127552, 14559151962849476255679123180858798913701143050361472396012918354141165748416]

private theorem rowsA9_chunk012_checked : rowsA9_chunk012.length = 4 ∧ rowsSum 1753 rowsA9_chunk012 = 41715946 := by
  apply daChecked
  decide +kernel

private def rowsA9_chunk016 : List ℕ := [14573286739367703331100427283634083906630848272252177398407456942191590604992]

private theorem rowsA9_chunk016_checked : rowsA9_chunk016.length = 1 ∧ rowsSum 1757 rowsA9_chunk016 = 10717684 := by
  apply daChecked
  decide +kernel

private def rowsA9 : List ℕ := rowsA9_chunk000 ++ rowsA9_chunk004 ++ rowsA9_chunk008 ++ rowsA9_chunk012 ++ rowsA9_chunk016

private theorem rowsA9_checked :
    rowsA9.length = 17 ∧ rowsSum 1741 rowsA9 = 167236913 :=
  daAppend rowsA9_chunk000_checked <|
  daAppend rowsA9_chunk004_checked <|
  daAppend rowsA9_chunk008_checked <|
  daAppend rowsA9_chunk012_checked <|
  rowsA9_chunk016_checked

def rowsA : List ℕ := rowsA1 ++ rowsA2 ++ rowsA3 ++ rowsA4 ++ rowsA5 ++ rowsA6 ++ rowsA7 ++ rowsA8 ++ rowsA9

theorem rowsA_length : rowsA.length = 339 := by
  simp only [rowsA, List.length_append, Nat.reduceAdd,
    rowsA1_checked.1, rowsA2_checked.1, rowsA3_checked.1, rowsA4_checked.1,
    rowsA5_checked.1, rowsA6_checked.1, rowsA7_checked.1, rowsA8_checked.1,
    rowsA9_checked.1]

theorem rowsA_sum : rowsSum 1419 rowsA = 812551376 := by
  simp only [rowsA, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsA1_checked.1, rowsA2_checked.1, rowsA3_checked.1, rowsA4_checked.1,
    rowsA5_checked.1, rowsA6_checked.1, rowsA7_checked.1, rowsA8_checked.1,
    rowsA1_checked.2, rowsA2_checked.2, rowsA3_checked.2, rowsA4_checked.2,
    rowsA5_checked.2, rowsA6_checked.2, rowsA7_checked.2, rowsA8_checked.2,
    rowsA9_checked.2]

end K1_13_2_3_4
end PackSource_K1_13_2_3_4DataA

section PackSource_K1_13_2_3_6AuxC
set_option autoImplicit true
namespace K1_13_2_3_6
open K1_13_2_3
open private fastDen fastC fastOld fastKernel from ProximityPrize.SubmissionLower.Numeric6Defs
open private decode runLength rowLength rowValue rowStart runValue sumFrom from ProximityPrize.SubmissionLower.Numeric6AuxCert

set_option maxRecDepth 50000
set_option maxHeartbeats 0

-- Shift the cubic by one to handle negative inputs at zero.
private def auxCDen (k : ℕ) : ℕ :=
  let lin := Nat.add (Nat.mul 2 k) 15
  let quad := Nat.add (Nat.mul k lin) 30
  Nat.div (Nat.add (Nat.mul k quad) 25) 72

-- The sum of three consecutive denominators is itself a rounded cubic.
private def auxCExc (k : ℕ) : ℕ :=
  let lin := Nat.add (Nat.mul 2 k) 9
  let quad := Nat.add (Nat.mul k lin) 10
  Nat.div (Nat.add (Nat.mul k quad) 3) 24

private theorem auxCDen_formula (k : ℕ) :
    auxCDen k = (k * (k * (2*k+15)+30)+25) / 72 := rfl

private theorem auxCExc_formula (k : ℕ) :
    auxCExc k = (k * (k * (2*k+9)+10)+3) / 24 := rfl

private theorem auxCDen_step (k : ℕ) :
    auxCDen (k+12) = auxCDen k + (k*(k+17)+83) := by
  simp only [auxCDen_formula]
  rw [show (k+12)*((k+12)*(2*(k+12)+15)+30)+25 =
      (k*(k*(2*k+15)+30)+25) + 72*(k*(k+17)+83) by ring, Nat.add_mul_div_left _ _ (by decide)]

private theorem auxCExc_step (k : ℕ) :
    auxCExc (k+12) = auxCExc k + (k*(3*k+45)+203) := by
  simp only [auxCExc_formula]
  rw [show (k+12)*((k+12)*(2*(k+12)+9)+10)+3 =
      (k*(k*(2*k+9)+10)+3) + 24*(k*(3*k+45)+203) by ring, Nat.add_mul_div_left _ _ (by decide)]

private theorem auxCExc_small : ∀ i : Fin 14, auxCExc i.val =
    auxCDen i.val + auxCDen (i.val-1) + auxCDen (i.val-2) := by decide +kernel

private theorem auxCExc_correct (k : ℕ) :
    auxCExc k = auxCDen k + auxCDen (k-1) + auxCDen (k-2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k < 14
    · exact auxCExc_small ⟨k,h⟩
    · obtain ⟨n,rfl⟩ : ∃ n, k = n+14 := ⟨k-14, by omega⟩
      have hi := ih (n+2) (by omega)
      rw [show n+2-1 = n+1 by omega, show n+2-2 = n by omega] at hi
      rw [show n+14-1 = (n+1)+12 by omega, show n+14-2 = n+12 by omega,
        show n+14 = (n+2)+12 by omega, auxCExc_step, auxCDen_step (n+2),
        auxCDen_step (n+1), auxCDen_step n, hi]
      ring

private theorem auxCDen_eq (u : ℤ) : fastDen u = (auxCDen (u+1).toNat : ℤ) := by
  by_cases hu : u < 0
  · rw [fastDen, ite_eq_left hu, show (u+1).toNat = 0 by omega]
    rfl
  · lift u to ℕ using (by omega)
    rw [show ((u : ℤ)+1).toNat = u+1 by omega, auxCDen_formula]
    simp only [fastDen, not_lt.mpr (Int.natCast_nonneg _), ite_false, Int.natCast_ediv,
      Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    ring

private theorem auxCExc_eq (x : ℤ) :
    (auxCExc x.toNat : ℤ) = fastDen (x-1) + fastDen (x-2) + fastDen (x-3) := by
  simp only [auxCExc_correct, Nat.cast_add, auxCDen_eq]
  rw [show (x-1+1).toNat = x.toNat by omega,
    show (x-2+1).toNat = x.toNat-1 by omega, show (x-3+1).toNat = x.toNat-2 by omega]

-- On this interval the second inclusion-exclusion correction is zero.
private theorem auxCCum (d u : ℤ) (hd : 0 ≤ d) (h₁ : u ≤ 3*d) (h₂ : u ≤ 2*d+2) :
    fastC d u = (auxCDen (u+1).toNat : ℤ) - auxCExc (u-d).toNat := by
  rw [← auxCDen_eq, auxCExc_eq]
  have hz (a : ℤ) (ha : a < 0) : fastDen a = 0 := by simp [fastDen, ha]
  unfold fastC
  simp only [not_lt.mpr hd, decide_false, Bool.false_or, decide_eq_true_eq,
    min_eq_left h₁]
  split <;> rename_i hu
  · simp [hz _ hu, hz _ (show u-d-1 < 0 by omega),
      hz _ (show u-d-2 < 0 by omega), hz _ (show u-d-3 < 0 by omega)]
  · split <;> rename_i h
    · simp [hz _ (show u-d-1 < 0 by omega), hz _ (show u-d-2 < 0 by omega),
        hz _ (show u-d-3 < 0 by omega)]
    · rw [ite_eq_left (show u-d ≤ d+2 by omega)]
      omega

private def auxCRem (d l o : ℕ) := (o + d - (1+l)) / 4 + 1

-- The nonnegative part of the signed kernel on the checked range.
private def auxCK (d l cap o : ℕ) :=
  let m := auxCRem d l o
  auxCDen (3*cap+1) + auxCDen (o - 3*m) + auxCExc (l - (1+(d-m))) -
    (auxCExc (3*cap-d) + auxCDen o + auxCDen l)

private def auxCGood (d l cap o : ℕ) : Bool :=
  let m := auxCRem d l o
  1+l ≤ o+d && m ≤ d && l ≤ 3*cap+1 && 3*cap ≤ 2*d+2 && cap ≤ d &&
    o ≤ d+1 && l ≤ 3*(d-m)+1 && l ≤ 2*(d-m)+3

private theorem auxCK_eq (d l cap o : ℕ) (hg : auxCGood d l cap o = true) :
    (fastKernel d l cap o).toNat = auxCK d l cap o := by
  let m := auxCRem d l o
  simp only [auxCGood, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hbal, hmd⟩, hlc⟩, hcd⟩, hcap⟩, hod⟩, hlm₁⟩, hlm₂⟩ := hg
  change m ≤ d at hmd
  change l ≤ 3*(d-m)+1 at hlm₁
  change l ≤ 2*(d-m)+3 at hlm₂
  have hm : ((m : ℕ) : ℤ) = ((o : ℤ)-1-l+d)/4+1 := by dsimp [m, auxCRem]; omega
  have hmin : min (d : ℤ) (((o : ℤ)-1-l+d)/4) = ((o : ℤ)-1-l+d)/4 :=
    min_eq_right (by omega)
  simp only [fastKernel, show ¬ (d : ℤ) < 0 by omega, show ¬ (cap : ℤ) < 0 by omega,
    decide_false, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_eq_right (show ¬ ((o : ℤ)-1-l+d < 0) by omega),
    ite_eq_left (show (l : ℤ)-1 ≤ 3*cap by omega), hmin, ← hm]
  rw [auxCCum (d : ℤ) (3*cap) (by omega) (by omega) (by omega),
    auxCCum (d : ℤ) (o-1) (by omega) (by omega) (by omega),
    auxCCum ((d : ℤ)-m) (o-1-3*m) (by omega) (by omega) (by omega),
    auxCCum ((d : ℤ)-m) (l-1) (by omega) (by omega) (by omega)]
  have e₁ : (3*(cap : ℤ)+1).toNat = 3*cap+1 := by omega
  have e₂ : (3*(cap : ℤ)-d).toNat = 3*cap-d := by omega
  have e₃ : ((o : ℤ)-1+1).toNat = o := by omega
  have e₄ : ((o : ℤ)-1-d).toNat = 0 := by omega
  have e₅ : ((o : ℤ)-1-3*m+1).toNat = o-3*m := by omega
  have e₆ : ((o : ℤ)-1-3*m-(d-m)).toNat = 0 := by omega
  have e₇ : ((l : ℤ)-1+1).toNat = l := by omega
  have e₈ : ((l : ℤ)-1-(d-m)).toNat = l-(1+(d-m)) := by omega
  rw [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈]
  simp only [show auxCExc 0 = 0 from rfl, Nat.cast_zero, sub_zero]
  change _ = auxCDen (3*cap+1) + auxCDen (o-3*m) + auxCExc (l-(1+(d-m))) -
    (auxCExc (3*cap-d) + auxCDen o + auxCDen l)
  omega

private theorem auxCOld (j : ℕ) :
    (fastOld 1650 (1650-j) 550).toNat = auxCDen 1651 - auxCDen (1650-j) := by
  unfold fastOld
  rw [min_eq_right (show (1650:ℤ)-j-1 ≤ 3*550 by omega)]
  rw [auxCCum 1650 (3*550) (by decide) (by decide) (by decide),
    auxCCum 1650 (1650-j-1) (by decide) (by omega) (by omega)]
  rw [show ((1650 : ℤ)-j-1+1).toNat = 1650-j by omega,
    show ((1650 : ℤ)-j-1-1650).toNat = 0 by omega]
  change ((auxCDen 1651 : ℤ) - 0 - (auxCDen (1650-j) - 0)).toNat = _
  omega

private theorem auxCClip (old initial residual : ℤ) :
    min old.toNat residual.toNat - initial.toNat =
      (old - max 0 initial).toNat - (old - max (max 0 initial) residual).toNat := by
  omega

-- The bounds apply to all offsets of a nonzero run.
private def auxCBox (s j n a b c : ℕ) : Bool :=
  3100 ≤ s && s ≤ 3200 && 200 ≤ j && j+n ≤ 410 && 3360 ≤ s+j &&
    a+4*c ≤ 384 && b ≤ 256 && a ≤ b+360

private def auxCQuick (s j a b c : ℕ) : ℕ :=
  let l := 1650-j
  let o := 4650-(s+j)
  Nat.min (auxCDen 1651 - auxCDen l)
    (auxCK (1650-(a+b+3*c)) (l-(3*b+2*c)) (550-(b+c)) (o-(2*b+3*c))) -
    auxCK 1650 l 550 o

private theorem auxCQuick_eq (s j a b c : ℕ)
    (hs : 3100 ≤ s) (hs' : s ≤ 3200) (hj : 200 ≤ j) (hj' : j ≤ 409)
    (hsj : 3360 ≤ s+j) (ha : a+4*c ≤ 384) (hb : b ≤ 256) (hab : a ≤ b+360) :
    auxCQuick s j a b c = blockSaving s j ⟨a,b,c⟩ := by
  let l := 1650-j
  let o := 4650-(s+j)
  let d := 1650-(a+b+3*c)
  let cap := 550-(b+c)
  let l' := l-(3*b+2*c)
  let o' := o-(2*b+3*c)
  have hl : l+j = 1650 := by dsimp only [l]; omega
  have ho : o+(s+j) = 4650 := by dsimp only [o]; omega
  have hd : d+(a+b+3*c) = 1650 := by dsimp only [d]; omega
  have hcap : cap+(b+c) = 550 := by dsimp only [cap]; omega
  have hl' : l'+(3*b+2*c) = l := by dsimp only [l']; omega
  have ho' : o'+(2*b+3*c) = o := by dsimp only [o']; omega
  have g : auxCGood 1650 l 550 o = true := by
    simp only [auxCGood, Bool.and_eq_true, decide_eq_true_eq]
    have hm : auxCRem 1650 l o ≤ 388 := by dsimp only [auxCRem]; omega
    repeat' apply And.intro <;> omega
  have g' : auxCGood d l' cap o' = true := by
    simp only [auxCGood, Bool.and_eq_true, decide_eq_true_eq]
    have hm : auxCRem d l' o' ≤ 388 := by dsimp only [auxCRem]; omega
    repeat' apply And.intro <;> omega
  change Nat.min (auxCDen 1651 - auxCDen l) (auxCK d l' cap o') - auxCK 1650 l 550 o = _
  rw [← auxCK_eq _ _ _ _ g', ← auxCK_eq _ _ _ _ g]
  have old : auxCDen 1651 - auxCDen l = (fastOld 1650 (1650-j) 550).toNat := (auxCOld j).symm
  rw [old, show (d : ℤ) = 1650-(a+b+3*c) by omega,
    show (cap : ℤ) = 550-(b+c) by omega, show (l' : ℤ) = 1650-j-(3*b+2*c) by omega,
    show (o' : ℤ) = 4650-s-j-(2*b+3*c) by omega, show (l : ℤ) = 1650-j by omega,
    show (o : ℤ) = 4650-s-j by omega]
  exact auxCClip _ _ _

-- Force a natural argument to a literal before reusing it at every offset of a run.
private def auxCForce {α : Type} (x : ℕ) (f : ℕ → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f n.succ

private theorem auxCForce_eq {α : Type} (x : ℕ) (f : ℕ → α) :
    auxCForce x f = f x := by cases x <;> rfl

private def auxCAt (h e x y o l i : ℕ) :=
  let positive := Nat.add (Nat.add h (auxCDen (Nat.sub x i))) (auxCExc (Nat.sub y i))
  let negative := Nat.add (Nat.add e (auxCDen (Nat.sub o i))) (auxCDen (Nat.sub l i))
  Nat.sub positive negative

-- Advancing the offset decreases l and o together, so the cut m stays fixed.
private def auxCWithK {α : Type} (d l cap o : ℕ) (f : (ℕ → ℕ) → α) : α :=
  let m := auxCRem d l o
  auxCForce (auxCDen (3*cap+1)) fun h =>
  auxCForce (auxCExc (3*cap-d)) fun e =>
  auxCForce (o-3*m) fun x =>
  auxCForce (l-(1+(d-m))) fun y =>
  auxCForce o fun o' =>
  auxCForce l fun l' =>
  f (auxCAt h e x y o' l')

private theorem auxCAt_eq (d l cap o i : ℕ) (hl : i ≤ l) (ho : i ≤ o) :
    auxCAt (auxCDen (3*cap+1)) (auxCExc (3*cap-d)) (o-3*auxCRem d l o)
      (l-(1+(d-auxCRem d l o))) o l i = auxCK d (l-i) cap (o-i) := by
  simp only [auxCK, auxCAt]
  have hm : auxCRem d (l-i) (o-i) = auxCRem d l o := by
    unfold auxCRem
    rw [show o-i+d-(1+(l-i)) = o+d-(1+l) by omega]
  rw [hm, show o-i-3*auxCRem d l o = o-3*auxCRem d l o-i by omega,
    show l-i-(1+(d-auxCRem d l o)) = l-(1+(d-auxCRem d l o))-i by omega]
  rfl

private def auxCOffsetSum (s j a b c n : ℕ) :=
  let l := 1650-j
  let o := 4650-(s+j)
  let d := 1650-(a+b+3*c)
  let cap := 550-(b+c)
  auxCWithK 1650 l 550 o fun init =>
  auxCWithK d (l-(3*b+2*c)) cap (o-(2*b+3*c)) fun res =>
  sumFrom (fun i => auxCForce (res i) fun residual =>
    Nat.sub (Nat.min (Nat.sub 125576826 (auxCDen (Nat.sub l i))) residual) (init i)) 0 n

private theorem auxCOffsetSum_eq (s j a b c n : ℕ)
    (hbox : auxCBox s j n a b c = true) : auxCOffsetSum s j a b c n =
    sumFrom (fun u => blockSaving s u ⟨a,b,c⟩) j n := by
  simp only [auxCBox, Bool.and_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨⟨⟨⟨⟨⟨⟨hs,hs'⟩,hj⟩,hj'⟩,hsj⟩,ha⟩,hb⟩,hab⟩ := hbox
  simp only [auxCOffsetSum, auxCWithK, auxCForce_eq]
  suffices ∀ (f g : ℕ → ℕ) (n : ℕ), (∀ i < n, f i = g (j+i)) →
      sumFrom f 0 n = sumFrom g j n by
    apply this
    intro i hi
    have h₀ := auxCAt_eq 1650 (1650-j) 550 (4650-(s+j)) i (by omega) (by omega)
    have h₁ := auxCAt_eq (1650-(a+b+3*c)) (1650-j-(3*b+2*c)) (550-(b+c))
      (4650-(s+j)-(2*b+3*c)) i (by omega) (by omega)
    rw [h₀, h₁, ← auxCQuick_eq s (j+i) a b c (by omega) (by omega)
      (by omega) (by omega) (by omega) ha hb hab]
    unfold auxCQuick
    rw [show Nat.sub (1650-j) i = 1650-(j+i) by change 1650-j-i = _; omega]
    rw [show auxCDen 1651 = 125576826 from rfl,
      show 1650-j-i = 1650-(j+i) by omega,
      show 4650-(s+j)-i = 4650-(s+(j+i)) by omega,
      show 1650-j-(3*b+2*c)-i = 1650-(j+i)-(3*b+2*c) by omega,
      show 4650-(s+j)-(2*b+3*c)-i = 4650-(s+(j+i))-(2*b+3*c) by omega]
    rfl
  intro f g k h
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sumFrom, sumFrom, ih (fun i hi => h i (by omega)), Nat.zero_add, h k (by omega)]

private def auxCRun (s j code : ℕ) : ℕ :=
  let n := runLength code
  let a := code % 2048
  let b := code / 2048 % 1024
  let c := code / 2097152 % 1024
  if code % 2147483648 = 0 then 0 else
    if auxCBox s j n a b c then auxCOffsetSum s j a b c n
    else runValue s j code

private theorem auxCRun_eq (s j code : ℕ) : auxCRun s j code = runValue s j code := by
  unfold auxCRun
  dsimp only
  split <;> rename_i hz
  · simp only [runValue, hz, ite_true]
  · split <;> rename_i h
    · rw [runValue, ite_eq_right hz]
      exact auxCOffsetSum_eq _ _ _ _ _ _ h
    · rfl

private def auxCRow (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => auxCRun s j code + auxCForce (j + runLength code) (fun j' => auxCRow s j' tail)

private theorem auxCRow_eq (s j : ℕ) (row : List ℕ) :
    auxCRow s j row = rowValue s j row := by
  induction row generalizing j with
  | nil => rfl
  | cons code tail ih => rw [auxCRow, auxCForce_eq, auxCRun_eq, ih, rowValue]

-- Check each row against its own literal total.
private def auxCChecks (s : ℕ) : List (List ℕ) → List ℕ → Bool
  | [], [] => true
  | row :: rest, v :: vs =>
      (auxCRow s (rowStart s) row == v) && auxCChecks (s+1) rest vs
  | _, _ => false

private theorem auxCChecks_sound (s : ℕ) (rows : List (List ℕ)) (vs : List ℕ)
    (h : auxCChecks s rows vs = true) :
    rows.length = vs.length ∧ value s rows = vs.sum := by
  induction rows generalizing s vs with
  | nil => cases vs <;> simp_all [auxCChecks, value]
  | cons row rest ih =>
    cases vs with
    | nil => contradiction
    | cons v vs =>
      have p := Bool.and_eq_true_iff.mp h
      obtain ⟨hn, hv⟩ := ih (s+1) vs p.2
      refine ⟨congrArg Nat.succ hn, ?_⟩
      exact congrArg₂ Nat.add ((auxCRow_eq s (rowStart s) row).symm.trans (eq_of_beq p.1)) hv

private def auxCBatch (s : ℕ) (rows : List (List ℕ)) (n w : ℕ) : Prop :=
  rows.length = n ∧ fits s rows = true ∧ value s rows = w

private theorem auxCChecked (s : ℕ) (rows : List (List ℕ)) (vs : List ℕ)
    (h : fits s rows = true ∧ auxCChecks s rows vs = true) : auxCBatch s rows vs.length vs.sum := by
  have p := auxCChecks_sound s rows vs h.2
  exact ⟨p.1, h.1, p.2⟩

private theorem auxCMerge (s : ℕ) (a b : List (List ℕ)) (n m x y : ℕ)
    (ha : auxCBatch s a n x) (hb : auxCBatch (s+n) b m y) :
    auxCBatch s (a++b) (n+m) (x+y) := by
  obtain ⟨hn, hf, hv⟩ := ha
  obtain ⟨hm, hg, hw⟩ := hb
  exact ⟨by rw [List.length_append, hn, hm], by rw [fits_append, hn, hf, hg]; rfl,
    by rw [value_append, hn, hv, hw]⟩

private def auxCData3103 : List (List ℕ) := [
    [77309411328, 4496818176, 2282225664, 2349203456, 13019512832, 6543507456, 4362469376,
    2248409088, 4362338304, 2198077440, 33816576, 6442713472, 6442647936, 8590131456, 4295098624,
    98560, 2147549440, 2147533056, 33024, 24832, 16640, 264, 259, 15032385792, 2147483872,
    2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131,
    8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680,
    2147483672, 16, 12, 8, 3],
    [77309411328, 6644301824, 134742016, 2349203456, 13019512832, 8690991104, 2214985728,
    2248409088, 4362338304, 4345561088, 8590197120, 6442647936, 8590131456, 2147614976, 98560,
    4295033088, 49408, 2147516672, 24832, 12544, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2],
    [79456894976, 4496818176, 2282225664, 2349203456, 10872029184, 8690991104, 4362469376,
    100925440, 6509821952, 2198077440, 8590197120, 8590131584, 6442647808, 4295098624, 98560,
    2147549440, 2147533056, 33024, 24832, 16640, 268, 262, 257, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072,
    112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25,
    24, 17, 16, 12, 6, 1],
    [79456894976, 4496818176, 2282225664, 2349203456, 13019512832, 6543507456, 4362469376,
    2248409088, 4362338304, 2198077440, 10737680768, 8590131584, 6442647808, 2147614976, 98560,
    4295033088, 2147533056, 33024, 24832, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204,
    200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100,
    8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [81604378624, 4496818176, 2282225664, 201719808, 13019512832, 8690991104, 4362469376,
    100925440, 6509821952, 2198077440, 10737680768, 6442647936, 6442647808, 4295098624, 98560,
    2147549440, 2147533056, 33024, 24832, 16640, 268, 264, 259, 15032385792, 2147483872,
    2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131,
    8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680,
    2147483672, 16, 12, 8, 3],
    [81604378624, 4496818176, 4429709312, 201719808, 10872029184, 8690991104, 4362469376,
    2248409088, 4362338304, 2198077440, 10737680768, 8590131584, 6442647808, 2147614976, 98560,
    4295033088, 2147533056, 33024, 24832, 272, 268, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2]
  ]

private theorem auxCValues3103 : auxCBatch 3103 auxCData3103 6 533140834 :=
  auxCChecked 3103 auxCData3103
    [87538471, 88431136, 88445518, 89347227, 89301948, 90076534] (by decide +kernel)

private def auxCData3109 : List (List ℕ) := [
    [81604378624, 4496818176, 4429709312, 201719808, 13019512832, 6543507456, 6509953024,
    100925440, 4362338304, 2198077440, 12885164416, 8590131584, 6442647808, 2147614976, 98560,
    2147549440, 2147533056, 33024, 24832, 16640, 272, 268, 262, 257, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072,
    112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25,
    24, 17, 16, 12, 6, 1],
    [83751862272, 4496818176, 4429709312, 201719808, 10872029184, 8690991104, 4362469376, 50724864,
    6509821952, 50593792, 12885164416, 10737615232, 4295164160, 2147614976, 2147582208, 2147549440,
    2147533056, 33024, 24832, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204, 200, 196,
    17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100, 8589934688, 76,
    72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [83751862272, 4496818176, 4429709312, 201719808, 13019512832, 6543507456, 6509953024,
    100925440, 4362338304, 2198077440, 12885164416, 8590131584, 6442647808, 2147614976, 98560,
    4295033088, 49408, 2147516672, 16640, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864,
    208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3],
    [85899345920, 4496818176, 4429709312, 13019512832, 8690991104, 4362469376, 50724864,
    6509821952, 50593792, 15032648064, 8590131584, 4295164160, 2147614976, 2147582208, 2147549440,
    2147533056, 33024, 24832, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864, 2147483856,
    204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108,
    102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18,
    16, 12, 6, 2],
    [85899345920, 4496818176, 4429709312, 201719808, 10872029184, 8690991104, 4362469376, 50724864,
    100925440, 4362338304, 50593792, 15032648064, 10737615232, 4295164160, 2147614976, 98560,
    4295033088, 49408, 2147516672, 280, 2147483920, 268, 262, 257, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072,
    112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25,
    24, 17, 16, 12, 6, 1],
    [85899345920, 4496818176, 6577192960, 13019512832, 6543507456, 6509953024, 50724864,
    4362338304, 50593792, 17180131712, 10737615232, 4295164160, 131328, 2147582208, 2147549440,
    2147533056, 33024, 24832, 280, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204, 200,
    196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100, 8589934688,
    76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4]
  ]

private theorem auxCValues3109 : auxCBatch 3109 auxCData3109 6 551130453 :=
  auxCChecked 3109 auxCData3109
    [90766116, 90885142, 91739364, 91775485, 92704907, 93259439] (by decide +kernel)

private def auxCData3115 : List (List ℕ) := [
    [88046829568, 4496818176, 6577192960, 10872029184, 8690991104, 4362469376, 2198208512,
    4362338304, 50593792, 15032648064, 10737615232, 4295164160, 2147614976, 98560, 4295033088,
    2147533056, 33024, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864, 208,
    204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108, 104,
    99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16, 12, 8,
    3],
    [88046829568, 4496818176, 6577192960, 13019512832, 6543507456, 6509953024, 50724864,
    4362338304, 50593792, 17180131712, 10737615232, 4295164160, 2147614976, 98560, 2147549440,
    2147533056, 33024, 24832, 280, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2],
    [90194313216, 2349334528, 8724676608, 10872029184, 8690991104, 4362469376, 2198208512,
    4362338304, 19327615360, 10737615232, 4295164160, 131328, 2147582208, 2147549440, 2147533056,
    33024, 2147483928, 2147483920, 268, 262, 257, 15032385792, 224, 2147483864, 2147483856, 204,
    198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108, 102,
    97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12,
    6, 1],
    [90194313216, 4496818176, 6577192960, 10872029184, 8690991104, 4362469376, 2198208512,
    4362338304, 19327615360, 12885098880, 2147680512, 2147614976, 98560, 4295033088, 49408,
    2147516672, 2147483928, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204, 200, 196,
    17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100, 8589934688, 76,
    72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [90194313216, 4496818176, 8724676608, 10872029184, 6543507456, 6509953024, 2198208512,
    2214854656, 50593792, 19327615360, 10737615232, 4295164160, 131328, 2147582208, 2147549440,
    2147533056, 33024, 288, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864,
    208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3],
    [92341796864, 2349334528, 8724676608, 10872029184, 8690991104, 4362469376, 2198208512,
    33947648, 2214854656, 19327615360, 12885098880, 2147680512, 2147614976, 98560, 4295033088,
    49408, 33024, 288, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2]
  ]

private theorem auxCValues3115 : auxCBatch 3115 auxCData3115 6 569091567 :=
  auxCChecked 3115 auxCData3115
    [93388796, 94248210, 94182920, 95243120, 95854815, 96173706] (by decide +kernel)

private def auxCData3121 : List (List ℕ) := [
    [92341796864, 4496818176, 8724676608, 10872029184, 6543507456, 6509953024, 2198208512,
    2214854656, 21475099008, 12885098880, 2147680512, 131328, 2147582208, 2147549440, 2147533056,
    33024, 288, 2147483928, 2147483920, 268, 262, 257, 15032385792, 224, 2147483864, 2147483856,
    204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108,
    102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17,
    16, 12, 6, 1],
    [94489280512, 2349334528, 10872160256, 8724545536, 6543507456, 6509953024, 2198208512,
    33947648, 67371008, 23622582656, 12885098880, 2147680512, 131328, 98560, 4295033088,
    2147533056, 2147483936, 2147483928, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204,
    200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100,
    8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [94489280512, 4496818176, 8724676608, 8724545536, 8690991104, 4362469376, 4345692160,
    2214854656, 21475099008, 12885098880, 2147680512, 131328, 2147582208, 2147549440, 2147533056,
    33024, 2147483936, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864, 208,
    204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108, 104,
    99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16, 12, 8,
    3],
    [94489280512, 4496818176, 10872160256, 8724545536, 6543507456, 6509953024, 2198208512,
    33947648, 67371008, 23622582656, 12885098880, 2147680512, 131328, 2147582208, 2147549440,
    2147533056, 2147483936, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2],
    [96636764160, 2349334528, 10872160256, 8724545536, 8690991104, 4362469376, 2198208512,
    33947648, 67371008, 23622582656, 15032582528, 196864, 131328, 2147582208, 4295033088, 49408,
    33024, 2147483936, 2147483928, 2147483920, 268, 262, 257, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072,
    112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25,
    24, 17, 16, 12, 6, 1],
    [96636764160, 4496818176, 10872160256, 8724545536, 6543507456, 4362469376, 4345692160,
    33947648, 67371008, 23622582656, 15032582528, 196864, 131328, 2147582208, 2147549440,
    2147533056, 4294967584, 2147483928, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204,
    200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100,
    8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4]
  ]

private theorem auxCValues3121 : auxCBatch 3121 auxCData3121 6 588624088 :=
  auxCChecked 3121 auxCData3121
    [96895255, 96783674, 97940204, 98480426, 98977850, 99546679] (by decide +kernel)

private def auxCData3127 : List (List ℕ) := [
    [98784247808, 2349334528, 10872160256, 8724545536, 6543507456, 6509953024, 2198208512,
    2181431296, 25770066304, 12885098880, 2147680512, 2147582208, 4295033088, 49408, 304,
    4294967584, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864, 208, 204, 200,
    195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108, 104, 99,
    8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16, 12, 8, 3],
    [98784247808, 2349334528, 13019643904, 6577061888, 8690991104, 4362469376, 4345692160,
    33947648, 25770066304, 15032582528, 196864, 131328, 2147582208, 2147549440, 2147533056,
    4294967584, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864, 2147483856,
    204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108,
    102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18,
    16, 12, 6, 2],
    [98784247808, 4496818176, 13019643904, 6577061888, 6543507456, 6509953024, 2198208512,
    2181431296, 25770066304, 15032582528, 196864, 2147582208, 4295033088, 49408, 304, 4294967584,
    2147483928, 2147483920, 268, 262, 257, 15032385792, 224, 2147483864, 2147483856, 204, 198, 193,
    15032385728, 160, 2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97,
    6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6,
    1],
    [100931731456, 2349334528, 13019643904, 6577061888, 8690991104, 4362469376, 2198208512,
    2181431296, 25770066304, 17180066176, 131328, 2147582208, 2147549440, 2147533056, 304,
    4294967584, 2147483928, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204, 200, 196,
    17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100, 8589934688, 76,
    72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [100931731456, 4496818176, 13019643904, 6577061888, 6543507456, 4362469376, 4345692160,
    33947648, 25559040, 25770066304, 15032582528, 196864, 98688, 2147582208, 2147549440, 49408,
    2147483952, 4294967584, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864,
    208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3],
    [103079215104, 2349334528, 13019643904, 6577061888, 6543507456, 6509953024, 2198208512,
    2181431296, 25559040, 25770066304, 15032582528, 196864, 98688, 98560, 4295033088, 49408, 304,
    4294967584, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864, 2147483856,
    204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108,
    102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18,
    16, 12, 6, 2]
  ]

private theorem auxCValues3127 : auxCBatch 3127 auxCData3127 6 608227577 :=
  auxCChecked 3127 auxCData3127
    [99738493, 100649740, 101225458, 101742608, 102334122, 102537156] (by decide +kernel)

private def auxCData3133 : List (List ℕ) := [
    [103079215104, 2349334528, 13019643904, 101187584, 4429578240, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 25770066304, 17180066176, 98688, 2147582208, 2147549440,
    49408, 2147483952, 4294967584, 2147483928, 2147483920, 268, 262, 257, 15032385792, 224,
    2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129,
    6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38,
    33, 32, 25, 24, 17, 16, 12, 6, 1],
    [103079215104, 4496818176, 13019643904, 6577061888, 6543507456, 6509953024, 2198208512,
    2181431296, 25559040, 25770066304, 17180066176, 98688, 98560, 4295033088, 49408, 2147483952,
    4294967584, 2147483928, 272, 268, 264, 260, 17179869440, 224, 2147483864, 208, 204, 200, 196,
    17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720, 108, 104, 100, 8589934688, 76,
    72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672, 16, 12, 8, 4],
    [105226698752, 2349334528, 13019643904, 101187584, 4429578240, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 25770066304, 17180066176, 2147582336, 98560, 2147549440,
    49408, 4294967600, 4294967584, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872,
    2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131,
    8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680,
    2147483672, 16, 12, 8, 3],
    [105226698752, 4496818176, 13019643904, 101187584, 4429578240, 6543507456, 4362469376,
    4345692160, 33947648, 2173042688, 25770066304, 17180066176, 2147582336, 4295033088, 4294967600,
    4294967584, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864, 2147483856,
    204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108,
    102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18,
    16, 12, 6, 2],
    [107374182400, 2349334528, 13019643904, 101187584, 4429578240, 6543507456, 6509953024,
    2198208512, 2181431296, 25559040, 17170432, 25770066304, 15032582528, 2147582336, 98560,
    2147549440, 49408, 4294967600, 4294967584, 2147483928, 2147483920, 268, 262, 257, 15032385792,
    224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134,
    129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696,
    38, 33, 32, 25, 24, 17, 16, 12, 6, 1],
    [107374182400, 2349334528, 13019643904, 2248671232, 2282094592, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 25770066304, 17180066176, 2147582336, 98560,
    2147549440, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260, 17179869440, 224,
    2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720,
    108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672,
    16, 12, 8, 4]
  ]

private theorem auxCValues3133 : auxCBatch 3133 auxCData3133 6 629231195 :=
  auxCChecked 3133 auxCData3133
    [103444958, 104227698, 104582763, 105169767, 105502099, 106303910] (by decide +kernel)

private def auxCData3139 : List (List ℕ) := [
    [109521666048, 2349334528, 13019643904, 101187584, 4429578240, 6543507456, 6509953024,
    2198208512, 2181431296, 25559040, 17170432, 25770066304, 15032582528, 4295065984, 4295033088,
    6442451248, 4294967584, 2147483928, 272, 268, 264, 259, 15032385792, 2147483872, 2147483864,
    208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108,
    104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16,
    12, 8, 3],
    [109521666048, 2349334528, 13019643904, 2248671232, 2282094592, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 25770066304, 17180066176, 4295065984, 2147549440,
    6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 258, 15032385792, 224, 2147483864,
    2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072,
    112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26,
    24, 18, 16, 12, 6, 2],
    [109521666048, 2349334528, 13019643904, 2248671232, 4429578240, 6543507456, 4362469376,
    4345692160, 33947648, 25559040, 17170432, 12976128, 25770066304, 15032582528, 4295065984,
    4295033088, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 257, 15032385792, 224,
    2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800, 2147483792, 140, 134, 129,
    6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65, 2147483712, 54, 49, 2147483696, 38,
    33, 32, 25, 24, 17, 16, 12, 6, 1],
    [111669149696, 2349334528, 13019643904, 2248671232, 2282094592, 6543507456, 6509953024,
    2198208512, 2181431296, 25559040, 17170432, 8781824, 25770066304, 15032582528, 4295065984,
    2147549440, 320, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260, 17179869440, 224,
    2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132, 8589934720,
    108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680, 2147483672,
    16, 12, 8, 4],
    [111669149696, 2349334528, 13019643904, 4396154880, 134610944, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 12976128, 25770066304, 15032582528, 4295065984,
    65920, 65792, 2147483968, 6442451248, 4294967584, 2147483928, 272, 268, 264, 259, 15032385792,
    2147483872, 2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800, 144, 140, 136,
    131, 8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51, 4294967344, 35,
    2147483680, 2147483672, 16, 12, 8, 3],
    [113816633344, 2349334528, 13019643904, 2248671232, 2282094592, 6543507456, 6509953024,
    2198208512, 33947648, 2173042688, 12976128, 6684672, 25770066304, 15032582528, 4295065984,
    65920, 65792, 320, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 258, 15032385792,
    224, 2147483864, 2147483856, 204, 198, 194, 15032385728, 160, 2147483800, 2147483792, 140, 134,
    130, 6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696,
    38, 34, 32, 26, 24, 18, 16, 12, 6, 2]
  ]

private theorem auxCValues3139 : auxCBatch 3139 auxCData3139 6 649902183 :=
  auxCChecked 3139 auxCData3139
    [106663438, 107462595, 108401759, 108389864, 109408998, 109575529] (by decide +kernel)

private def auxCData3145 : List (List ℕ) := [
    [113816633344, 2349334528, 13019643904, 4396154880, 134610944, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 8781824, 25770066304, 15032582528, 4295065984,
    65920, 65792, 2147483968, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 257,
    15032385792, 224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65,
    2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1],
    [113816633344, 2349334528, 13019643904, 4396154880, 2282094592, 6543507456, 4362469376,
    4345692160, 33947648, 25559040, 17170432, 12976128, 6684672, 25770066304, 12885098880,
    6442549632, 65920, 65792, 2147483968, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260,
    17179869440, 224, 2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136,
    132, 8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36,
    2147483680, 2147483672, 16, 12, 8, 4],
    [115964116992, 2349334528, 13019643904, 4396154880, 134610944, 6543507456, 6509953024,
    2198208512, 2181431296, 25559040, 17170432, 8781824, 393600, 25770066304, 12885098880,
    4295065984, 2147549568, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 259,
    15032385792, 2147483872, 2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800,
    144, 140, 136, 131, 8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51,
    4294967344, 35, 2147483680, 2147483672, 16, 12, 8, 3],
    [115964116992, 2349334528, 13019643904, 4396154880, 134610944, 8690991104, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 12976128, 4587520, 25770066304, 12885098880,
    6442549632, 2147549568, 2147483968, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262,
    258, 15032385792, 224, 2147483864, 2147483856, 204, 198, 194, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 130, 6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70, 66,
    2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16, 12, 6, 2],
    [118111600640, 2349334528, 10872160256, 6543638528, 134610944, 6543507456, 4362469376,
    4345692160, 33947648, 2173042688, 12976128, 6684672, 393600, 25770066304, 12885098880,
    4295065984, 2147549568, 4294967616, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262,
    257, 15032385792, 224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65,
    2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1],
    [118111600640, 2349334528, 13019643904, 6543638528, 8690991104, 4362469376, 2198208512,
    2181431296, 25559040, 17170432, 8781824, 393600, 27917549952, 10737615232, 6442549632,
    2147549568, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260, 17179869440,
    224, 2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132,
    8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680,
    2147483672, 16, 12, 8, 4]
  ]

private theorem auxCValues3145 : auxCBatch 3145 auxCData3145 6 672517077 :=
  auxCChecked 3145 auxCData3145
    [110571115, 111455567, 111522245, 112665163, 112711833, 113591154] (by decide +kernel)

private def auxCData3151 : List (List ℕ) := [
    [120259084288, 201850880, 13019643904, 6543638528, 134610944, 6543507456, 4362469376,
    4345692160, 33947648, 25559040, 17170432, 12976128, 4587520, 393600, 25770066304, 12885098880,
    4295065984, 4295033216, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 259,
    15032385792, 2147483872, 2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800,
    144, 140, 136, 131, 8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51,
    4294967344, 35, 2147483680, 2147483672, 16, 12, 8, 3],
    [120259084288, 2349334528, 13019643904, 6543638528, 6543507456, 6509953024, 2198208512,
    2181431296, 25559040, 17170432, 8781824, 2147877248, 25770066304, 10737615232, 6442549632,
    4295033216, 2147483968, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 258,
    15032385792, 224, 2147483864, 2147483856, 204, 198, 194, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 130, 6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70, 66,
    2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16, 12, 6, 2],
    [120259084288, 2349334528, 13019643904, 6543638528, 8690991104, 4362469376, 2198208512,
    2181431296, 25559040, 17170432, 12976128, 2147877248, 25770066304, 12885098880, 6442549632,
    2147549568, 4294967616, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262, 257,
    15032385792, 224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65,
    2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1],
    [122406567936, 201850880, 13019643904, 8691122176, 6543507456, 4362469376, 4345692160,
    33947648, 2173042688, 12976128, 6684672, 2147877248, 25770066304, 10737615232, 6442549632,
    4295033216, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260, 17179869440,
    224, 2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136, 132,
    8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36, 2147483680,
    2147483672, 16, 12, 8, 4],
    [122406567936, 2349334528, 13019643904, 6543638528, 8690991104, 4362469376, 2198208512,
    2181431296, 25559040, 17170432, 8781824, 2147877248, 27917549952, 10737615232, 6442549632,
    2147549568, 49536, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 259,
    15032385792, 2147483872, 2147483864, 208, 204, 200, 195, 15032385728, 2147483808, 2147483800,
    144, 140, 136, 131, 8589934720, 108, 104, 99, 8589934688, 76, 72, 67, 4294967360, 51,
    4294967344, 35, 2147483680, 2147483672, 16, 12, 8, 3],
    [124554051584, 201850880, 13019643904, 8691122176, 6543507456, 4362469376, 2198208512,
    2181431296, 25559040, 17170432, 12976128, 4587520, 2147877248, 25770066304, 10737615232,
    6442549632, 4295033216, 49536, 2147483968, 6442451248, 4294967584, 2147483928, 2147483920, 268,
    262, 258, 15032385792, 224, 2147483864, 2147483856, 204, 198, 194, 15032385728, 160,
    2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108, 102, 98, 6442451040, 80, 76, 70,
    66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16, 12, 6, 2]
  ]

private theorem auxCValues3151 : auxCBatch 3151 auxCData3151 6 694058266 :=
  auxCChecked 3151 auxCData3151
    [113925853, 114679591, 115690581, 115887800, 116779841, 117094600] (by decide +kernel)

private def auxCData3157 : List (List ℕ) := [
    [124554051584, 2349334528, 10872160256, 8691122176, 67633152, 4396023808, 6509953024,
    2198208512, 2181431296, 25559040, 17170432, 8781824, 4295360896, 25770066304, 10737615232,
    6442549632, 4295033216, 4294967616, 6442451248, 4294967584, 2147483928, 2147483920, 268, 262,
    257, 15032385792, 224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160, 2147483800,
    2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70, 65,
    2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1],
    [126701535232, 201850880, 13019643904, 8691122176, 6543507456, 4362469376, 2198208512,
    2181431296, 25559040, 17170432, 12976128, 4295360896, 25770066304, 10737615232, 6442549632,
    4295033216, 49536, 4294967616, 6442451248, 4294967584, 2147483928, 272, 268, 264, 260,
    17179869440, 224, 2147483864, 208, 204, 200, 196, 17179869376, 160, 2147483800, 144, 140, 136,
    132, 8589934720, 108, 104, 100, 8589934688, 76, 72, 68, 4294967360, 52, 4294967344, 36,
    2147483680, 2147483672, 16, 12, 8, 4],
    [126701535232, 201850880, 13019643904, 8691122176, 67633152, 4396023808, 4362469376,
    4345692160, 33947648, 25559040, 17170432, 12976128, 6684672, 4295360896, 25770066304,
    10737615232, 6442549632, 4295033216, 49536, 4294967616, 6442451248, 4294967584, 2147483928,
    272, 268, 264, 259, 15032385792, 2147483872, 2147483864, 208, 204, 200, 195, 15032385728,
    2147483808, 2147483800, 144, 140, 136, 131, 8589934720, 108, 104, 99, 8589934688, 76, 72, 67,
    4294967360, 51, 4294967344, 35, 2147483680, 2147483672, 16, 12, 8, 3],
    [126701535232, 2349334528, 13019643904, 6543638528, 67633152, 6543507456, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 8781824, 4295360896, 27917549952, 8590131584,
    131456, 4295065984, 4295033216, 2147533184, 2147483968, 6442451248, 4294967584, 2147483928,
    2147483920, 268, 262, 258, 15032385792, 224, 2147483864, 2147483856, 204, 198, 194,
    15032385728, 160, 2147483800, 2147483792, 140, 134, 130, 6442451072, 112, 108, 102, 98,
    6442451040, 80, 76, 70, 66, 2147483712, 54, 50, 2147483696, 38, 34, 32, 26, 24, 18, 16, 12, 6,
    2],
    [128849018880, 201850880, 13019643904, 8691122176, 67633152, 4396023808, 4362469376,
    2198208512, 2181431296, 25559040, 17170432, 12976128, 6442844544, 25770066304, 10737615232,
    6442549632, 4295033216, 49536, 4294967616, 6442451248, 4294967584, 2147483928, 2147483920, 268,
    262, 257, 15032385792, 224, 2147483864, 2147483856, 204, 198, 193, 15032385728, 160,
    2147483800, 2147483792, 140, 134, 129, 6442451072, 112, 108, 102, 97, 6442451040, 80, 76, 70,
    65, 2147483712, 54, 49, 2147483696, 38, 33, 32, 25, 24, 17, 16, 12, 6, 1]
  ]

private theorem auxCValues3157 : auxCBatch 3157 auxCData3157 5 595226413 :=
  auxCChecked 3157 auxCData3157
    [117742062, 118322356, 118983761, 119938168, 120240066] (by decide +kernel)

private def auxCRows3157 := auxCData3157

private theorem auxCBatch3157 : auxCBatch 3157 auxCRows3157 5 595226413 :=
  auxCValues3157

private def auxCRows3151 := auxCData3151 ++ auxCRows3157

private theorem auxCBatch3151 : auxCBatch 3151 auxCRows3151 11 1289284679 :=
  auxCMerge 3151 auxCData3151 auxCRows3157 6 5 694058266 595226413 auxCValues3151 auxCBatch3157

private def auxCRows3145 := auxCData3145 ++ auxCRows3151

private theorem auxCBatch3145 : auxCBatch 3145 auxCRows3145 17 1961801756 :=
  auxCMerge 3145 auxCData3145 auxCRows3151 6 11 672517077 1289284679 auxCValues3145 auxCBatch3151

private def auxCRows3139 := auxCData3139 ++ auxCRows3145

private theorem auxCBatch3139 : auxCBatch 3139 auxCRows3139 23 2611703939 :=
  auxCMerge 3139 auxCData3139 auxCRows3145 6 17 649902183 1961801756 auxCValues3139 auxCBatch3145

private def auxCRows3133 := auxCData3133 ++ auxCRows3139

private theorem auxCBatch3133 : auxCBatch 3133 auxCRows3133 29 3240935134 :=
  auxCMerge 3133 auxCData3133 auxCRows3139 6 23 629231195 2611703939 auxCValues3133 auxCBatch3139

private def auxCRows3127 := auxCData3127 ++ auxCRows3133

private theorem auxCBatch3127 : auxCBatch 3127 auxCRows3127 35 3849162711 :=
  auxCMerge 3127 auxCData3127 auxCRows3133 6 29 608227577 3240935134 auxCValues3127 auxCBatch3133

private def auxCRows3121 := auxCData3121 ++ auxCRows3127

private theorem auxCBatch3121 : auxCBatch 3121 auxCRows3121 41 4437786799 :=
  auxCMerge 3121 auxCData3121 auxCRows3127 6 35 588624088 3849162711 auxCValues3121 auxCBatch3127

private def auxCRows3115 := auxCData3115 ++ auxCRows3121

private theorem auxCBatch3115 : auxCBatch 3115 auxCRows3115 47 5006878366 :=
  auxCMerge 3115 auxCData3115 auxCRows3121 6 41 569091567 4437786799 auxCValues3115 auxCBatch3121

private def auxCRows3109 := auxCData3109 ++ auxCRows3115

private theorem auxCBatch3109 : auxCBatch 3109 auxCRows3109 53 5558008819 :=
  auxCMerge 3109 auxCData3109 auxCRows3115 6 47 551130453 5006878366 auxCValues3109 auxCBatch3115

private def auxCRows3103 := auxCData3103 ++ auxCRows3109

private theorem auxCBatch3103 : auxCBatch 3103 auxCRows3103 59 6091149653 :=
  auxCMerge 3103 auxCData3103 auxCRows3109 6 53 533140834 5558008819 auxCValues3103 auxCBatch3109

/-- Certified factor products for grades 3103 through 3161. -/
def rowsC : List (List ℕ) := auxCRows3103

theorem checkC :
    rowsC.length = 59 ∧ fits 3103 rowsC = true ∧
      value 3103 rowsC = 6091149653 := auxCBatch3103

end K1_13_2_3_6
end PackSource_K1_13_2_3_6AuxC

section PackSource_K1_13_7Split
set_option autoImplicit true
namespace K1_13_7
noncomputable section
open Polynomial K1 K1_13

/-- Singular solutions on the leading-unit open. -/
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ ¬ RegularAt f (extend (s γ))) →
    Γ.card ≤ singularPrice (shape f)

/-- Regular solutions over a fixed lower-jet hypersurface. -/
def c2 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ D : Row 3, D ≠ 0 → LowerCaps D 35007 12106 →
      (∀ γ ∈ Γ, atJet D (extend (s γ)) = 0) → Γ.card ≤ hypersurfacePrice (shape f)

/-- Buy the common and high-power factors and produce a geometrically proper
residual pair with the two pointwise orders. -/
def c3 : Prop :=
  ∀ E : FatEquations, ∃ D P Q : Row 3,
    D ≠ 0 ∧ LowerCaps D 35007 12106 ∧
    LowerCaps P 952630000 322000000 ∧ LowerCaps Q 952630000 322000000 ∧
    ProperLowerPair P Q ∧
    ∀ S : Geom[X], E.holds S →
      atJet D S = 0 ∨ (OrderAt P S 41481 ∧ OrderAt Q S 8298)

/-- A third cut isolates the residual marks away from the purchased curves. -/
def c4 : Prop :=
  ∀ P Q : Row 3, ProperLowerPair P Q →
    LowerCaps P 952630000 322000000 → LowerCaps Q 952630000 322000000 →
    ∃ R : Row 3, LowerCaps R 952630000 322000000 ∧
      ∀ S : Geom[X], OrderAt P S 41481 → OrderAt Q S 8298 →
        HighCurve P Q (lowerPoint S) ∨ IsolatedFat P Q R (lowerPoint S)

/-- The regular lifts of the high curves, weighted by their local lengths. -/
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ P Q : Row 3, ProperLowerPair P Q →
      LowerCaps P 952630000 322000000 → LowerCaps Q 952630000 322000000 →
      (∀ γ ∈ Γ, HighCurve P Q (lowerPoint (extend (s γ)))) →
      Γ.card ≤ highCurvePrice (shape f)

/-- The sparse isolated-intersection bound in three lower coordinates. -/
def c6 : Prop :=
  ∀ P Q R : Row 3, LowerCaps P 952630000 322000000 →
    LowerCaps Q 952630000 322000000 → LowerCaps R 952630000 322000000 →
    ∀ points : Finset LowerPoint,
      (∀ y ∈ points, IsolatedFat P Q R y) → points.card ≤ isolatedPrice

theorem lowerPoint_injective : Function.Injective lowerPoint := by
  intro S T h
  have h₀ := congrFun h (0 : Fin 3)
  have hcoeff : Function.Injective genericCoeff :=
    (algebraMap GenericX GeometricX).injective.comp
      (IsFractionRing.injective Geom[X] GenericX)
  exact hcoeff (by simpa [lowerPoint, jet, Polynomial.hasseDeriv_zero'] using h₀)

theorem fat_price_sum (x : Shape) :
    fatPrice x = hypersurfacePrice x + singularPrice x + highCurvePrice x + isolatedPrice :=
  rfl

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_13.c7 := by
  classical
  intro w Γ s hmsg f hf hon helig E hE
  obtain ⟨D, P, Q, hD, hDb, hPb, hQb, hpq, hres⟩ := h3 E
  obtain ⟨R, hRb, hstrata⟩ := h4 P Q hpq hPb hQb
  let S : K → Geom[X] := fun γ => extend (s γ)
  let singular := Γ.filter (fun γ => ¬ RegularAt f (S γ))
  let divisors := Γ.filter (fun γ => RegularAt f (S γ) ∧ atJet D (S γ) = 0)
  let curves := Γ.filter (fun γ => RegularAt f (S γ) ∧ HighCurve P Q (lowerPoint (S γ)))
  let isolated := Γ.filter (fun γ => IsolatedFat P Q R (lowerPoint (S γ)))
  have hsingular : singular.card ≤ singularPrice (shape f) :=
    h1 w singular s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2⟩)
  have hdivisors : divisors.card ≤ hypersurfacePrice (shape f) :=
    h2 w divisors s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      D hD hDb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hcurves : curves.card ≤ highCurvePrice (shape f) :=
    h5 w curves s (hmsg.mono (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      P Q hpq hPb hQb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hisolated : isolated.card ≤ isolatedPrice := by
    let points := isolated.image (fun γ => lowerPoint (S γ))
    have hinj : Set.InjOn (fun γ => lowerPoint (S γ)) (isolated : Set K) := by
      intro a ha b hb hab
      exact hmsg.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (lowerPoint_injective hab))
    have hcard : points.card = isolated.card := Finset.card_image_of_injOn hinj
    rw [← hcard]
    apply h6 P Q R hPb hQb hRb points
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hγ).2
  have hcover : Γ ⊆ singular ∪ divisors ∪ curves ∪ isolated := by
    intro γ hγ
    by_cases hr : RegularAt f (S γ)
    · rcases hres (S γ) (hE γ hγ) with hd | ⟨hp, hq⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hr, hd⟩)))
      · rcases hstrata (S γ) hp hq with hc | hi
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hγ, hr, hc⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)))
  have hunion := Finset.card_le_card hcover
  have hunion₁ := Finset.card_union_le singular divisors
  have hunion₂ := Finset.card_union_le (singular ∪ divisors) curves
  have hunion₃ := Finset.card_union_le (singular ∪ divisors ∪ curves) isolated
  rw [fat_price_sum]
  omega

end
end K1_13_7
end PackSource_K1_13_7Split

section PackSource_K1_13_7_5Defs
set_option autoImplicit true
namespace K1_13_7_5

noncomputable section

open Polynomial K1 K1_13 K1_13_7

abbrev Jets := MvPolynomial (Fin 4) GeometricX
abbrev JetPoint := Fin 4 → GeometricX

def jetPoint (S : Geom[X]) : JetPoint := fun i => genericCoeff (jet S i)

def jetPointIdeal (y : JetPoint) : Ideal Jets := RingHom.ker (MvPolynomial.eval y)

def geometricFactor (f : Row 4) : Jets := MvPolynomial.map genericCoeff f

def liftRow (P : Row 3) : Jets := MvPolynomial.rename Fin.castSucc (genericRow P)

def liftIdeal (f : Row 4) (P Q : Row 3) : Ideal Jets :=
  Ideal.span {geometricFactor f, liftRow P, liftRow Q}

def liftLength (r : PrimeSpectrum Jets) (J : Ideal Jets) : ℕ∞ :=
  let A := Localization.AtPrime r.asIdeal
  Module.length A (A ⧸ J.map (algebraMap Jets A))

abbrev threshold : ℕ := 293711590
abbrev lowerBox : Shape := ⟨952630000, 322000000, 0⟩

/-- The weight is the generic complete-intersection length in the ambient four jets. -/
structure LiftedCurve (f : Row 4) (P Q : Row 3) (r : PrimeSpectrum Jets) : Prop where
  component : r.asIdeal ∈ (liftIdeal f P Q).minimalPrimes
  height : r.asIdeal.height = 3
  heavy : (↑threshold : ℕ∞) ≤ liftLength r (liftIdeal f P Q)
  finite : liftLength r (liftIdeal f P Q) < ⊤

/-- The downward-closed support envelope, including the cap on the highest jet. -/
def Supported (H : Shape) (F : Jets) : Prop :=
  ∀ m ∈ F.support, m.sum (fun _ a => a) ≤ H.b ∧
    m.sum (fun i a => i.val * a) ≤ H.j ∧ m 3 ≤ H.t

abbrev constantCoeff : K →+* GeometricX := genericCoeff.comp (Polynomial.C.comp embed)

/-- A common clearing denominator for the inverse Taylor evaluation functions. -/
structure ValueChart (H : Shape) where
  denominator : Jets
  numerator : I → Jets
  denominator_supported : Supported H denominator
  numerator_supported : ∀ i, Supported H (numerator i)

def ValueChart.recovers {H : Shape} (C : ValueChart H) (S : K[X]) : Prop :=
  let ev := MvPolynomial.eval (jetPoint (extend S))
  ev C.denominator ≠ 0 ∧
    ∀ i, ev (C.numerator i) = constantCoeff (S.eval (node i)) * ev C.denominator

end
end K1_13_7_5
end PackSource_K1_13_7_5Defs

section PackSource_K1_13_7_6Chart
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6
noncomputable section

open K1_13 K1_13_7 MvPolynomial
open scoped Pointwise

private theorem zero_mem_cap (b j : ℕ) : 0 ∈ cap b j := by
  simp [cap]

theorem chartMap_surjective : Function.Surjective chartMap := by
  apply monomialMap_surjective
  intro i
  change (Finsupp.single i 1).degree ≤ totalCap ∧
    Finsupp.single i 1 1 + 2 * Finsupp.single i 1 2 ≤ 2 * halfIndexCap
  fin_cases i <;> norm_num [Finsupp.degree_single, Finsupp.single_apply, totalCap, halfIndexCap]

private theorem cap_add_subset (b j b' j' : ℕ) :
    cap b j + cap b' j' ⊆ cap (b + b') (j + j') := by
  rintro _ ⟨e, he, e', he', rfl⟩
  change e.degree ≤ b ∧ e 1 + 2 * e 2 ≤ j at he
  change e'.degree ≤ b' ∧ e' 1 + 2 * e' 2 ≤ j' at he'
  change (e + e').degree ≤ b + b' ∧
    (e + e') 1 + 2 * (e + e') 2 ≤ j + j'
  simp only [map_add, Finsupp.add_apply]
  omega

private theorem nsmul_cap_subset (b j n : ℕ) : n • cap b j ⊆ cap (b * n) (j * n) := by
  induction n with
  | zero =>
      rw [zero_smul, Set.zero_subset]
      exact zero_mem_cap _ _
  | succ n ih =>
      rw [succ_nsmul, Nat.mul_succ, Nat.mul_succ]
      exact (Set.add_subset_add ih subset_rfl).trans (cap_add_subset _ _ _ _)

private theorem indexWeight_eq (e : Fin 3 →₀ ℕ) :
    (e.sum fun i a => i.val * a) = e 1 + 2 * e 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_three]
  simp

private theorem genericRow_mem_chart (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    genericRow P ∈ restrictSupport GeometricX chartExponents := by
  intro e he
  have he' : e ∈ P.support := support_map_subset _ _ he
  refine ⟨(le_totalDegree he').trans hP.1, ?_⟩
  rw [← indexWeight_eq]
  exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum fun i a => i.val * a) he').trans hP.2

theorem chart_lift (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    ∃ L : MvPolynomial chartExponents GeometricX,
      chartMap L = genericRow P ∧ L.totalDegree ≤ 1 := by
  let h := genericRow_mem_chart P hP
  exact ⟨monomialLift (genericRow P) h, monomialMap_monomialLift (genericRow P) h,
    totalDegree_monomialLift_le_one (genericRow P) h⟩

theorem chartDegree_eq_one {σ : Type} [Finite σ]
    (φ : MvPolynomial σ GeometricX →ₐ[GeometricX] Lower) (hφ : Function.Surjective φ)
    (y : LowerPoint) (q : PrimeSpectrum Lower) (hq : q.asIdeal = pointIdeal y) :
    chartDegree φ q = 1 := by
  let ψ : MvPolynomial σ GeometricX →ₐ[GeometricX] GeometricX := (aeval y).comp φ
  have hψ : Function.Surjective ψ := by
    intro t
    obtain ⟨v, hv⟩ := hφ (C t)
    exact ⟨v, by simp [ψ, hv]⟩
  have hker : q.asIdeal.comap φ = RingHom.ker ψ := by
    rw [hq]
    rfl
  rw [chartDegree, hker]
  let e := Ideal.quotientKerAlgEquivOfSurjective hψ
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  rw [affineDegree_eq_finrank, e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]

private theorem chartHilbert_le (n : ℕ) :
    affineHilbertFunction (RingHom.ker chartMap) n ≤
      (cap (totalCap * n) ((2 * halfIndexCap) * n)).ncard := by
  let S := cap (totalCap * n) ((2 * halfIndexCap) * n)
  let M := restrictSupport GeometricX S
  let : Module.Finite GeometricX M := restrictSupport_finite (Set.toFinite S)
  have hmap (L : MvPolynomial chartExponents GeometricX) (hL : L.totalDegree ≤ n) :
      chartMap L ∈ M :=
    restrictSupport_mono GeometricX (nsmul_cap_subset _ _ n)
      (monomialMap_mem_restrictSupport_nsmul (zero_mem_cap _ _) hL)
  calc
    affineHilbertFunction (RingHom.ker chartMap) n ≤
        Module.finrank GeometricX (M.map (Ideal.Quotient.mkₐ GeometricX ⊥).toLinearMap) := by
      rw [RingHom.ker_eq_comap_bot]
      exact affineHilbertFunction_comap_le_finrank_map chartMap ⊥ M hmap
    _ ≤ Module.finrank GeometricX M := Submodule.finrank_map_le _ _
    _ = S.ncard := by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeometricX S), Nat.card_coe_set_eq]

/-- The leading term of the cap's lattice polynomial gives its normalized volume. -/
theorem chartDegree_bound :
    chartDegree chartMap zeroPrime ≤ 6 * (halfIndexCap : ℚ) ^ 2 * (totalCap - halfIndexCap : ℚ) := by
  let a : ℚ := halfIndexCap
  let b : ℚ := totalCap - halfIndexCap
  let H : Polynomial ℚ := Polynomial.C (a ^ 2 * b) * Polynomial.X ^ 3 +
    Polynomial.C (a ^ 2 + 2 * a * b) * Polynomial.X ^ 2 +
    Polynomial.C (2 * a + b) * Polynomial.X ^ 1 + Polynomial.C 1
  have hdim : (affineHilbertPolynomial (RingHom.ker chartMap)).natDegree = 3 := by
    rw [natDegree_affineHilbertPolynomial_ker_of_surjective chartMap chartMap_surjective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hH : H.natDegree ≤ 3 := by
    dsimp only [H]
    apply Polynomial.natDegree_add_le_of_degree_le _ (by simp)
    apply Polynomial.natDegree_add_le_of_degree_le _
      ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide))
    apply Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_C_mul_X_pow_le _ _)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide)
  have hB : ∀ n : ℕ, 2 * (halfIndexCap * n) ≤ totalCap * n := fun n => by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right n (by decide)
  have hfit : ∀ n : ℕ, (affineHilbertFunction (RingHom.ker chartMap) n : ℚ) ≤ H.eval (n : ℚ) := by
    intro n
    have h := chartHilbert_le n
    rw [Nat.mul_assoc, cap_ncard _ _ (hB n)] at h
    refine (Nat.cast_le.mpr h).trans_eq ?_
    have hsub : halfIndexCap * n ≤ totalCap * n + 1 := by have := hB n; omega
    push_cast [Nat.cast_sub hsub]
    simp only [H, a, b, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  change affineDegree ((⊥ : Ideal Lower).comap chartMap) ≤ _
  rw [← RingHom.ker_eq_comap_bot]
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim hH
    (Filter.Eventually.of_forall hfit)).trans_eq ?_
  norm_num [H, a, b, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one]

end
end K1_13_7_6
end PackSource_K1_13_7_6Chart
