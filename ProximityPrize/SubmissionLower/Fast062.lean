import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
set_option autoImplicit true
section
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
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace K1_14_2_3
noncomputable section
open K1 K1_14 K1_14_2
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ I : Ideal Ambient, SeedSlice I →
    ∃ C : Seeds, Irreducible C ∧ seedImage I = Ideal.span {C} ∧
      0 < C.totalDegree ∧ C.totalDegree ≤ seedLength I
def c2 : Prop :=
  ∀ (I : Ideal Ambient) (C : MvPolynomial (Fin 2) L), SeedSlice I →
    Module.Finite SeedField (JetYSection I) → Irreducible C →
    seedImage I = Ideal.span {MvPolynomial.map constantCoefficients C} →
    ∃ g : ℕ, 0 < g ∧ SmallRootCurve (rootImage I) g (yLength I) ∧
      C.totalDegree * g ≤ seedLength I
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
end
end K1_14_2_3
end
section
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
end
section
set_option autoImplicit false
namespace K1_14_2_2_2_6
noncomputable section
open K1_14 K1_14_2 K1_14_2_2
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
def mixedSeedRestriction (f : Seeds) : Polynomial SectionField :=
  (K1_14_2_3_1.lineRestriction f).map seedParameters
end
end K1_14_2_2_2_6
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_6
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_3
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    Module.Finite SectionField (OverMixed I) →
    ∀ f : Seeds, f ≠ 0 → seedImage I = Ideal.span {f} →
      ∃ e : (Polynomial SectionField ⧸ Ideal.span {mixedSeedRestriction f}) →ₐ[SectionField]
          OverMixed I, Function.Injective e
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
end
section
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
end
section
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
end
section
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
end
section
namespace K1_14_2_4_1_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4_1
open scoped Polynomial
def genericSeedMap (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] :
    Seeds →+* ConstantSeedX C₀ :=
  MvPolynomial.eval₂Hom (extendX C₀) (insertConstant C₀ ∘ seedCoordinate C₀)
def seedCurveMap (C₀ : ConstantSeeds) [Fact (Irreducible C₀)]
    (h : RingHom.ker (genericSeedMap C₀) = seedEquation C₀) :
    (Seeds ⧸ seedEquation C₀) →+* ConstantSeedX C₀ :=
  Ideal.Quotient.lift (seedEquation C₀) (genericSeedMap C₀) fun _ hf =>
    RingHom.mem_ker.mp (h.symm ▸ hf)
structure SeedLocalization (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] : Prop where
  kernel : RingHom.ker (genericSeedMap C₀) = seedEquation C₀
  localized : letI : Algebra (Seeds ⧸ seedEquation C₀) (ConstantSeedX C₀) :=
    (seedCurveMap C₀ kernel).toAlgebra
    IsFractionRing (Seeds ⧸ seedEquation C₀) (ConstantSeedX C₀)
def rootView : RootAmbient ≃ₐ[FX] Seeds[X] :=
  (MvPolynomial.renameEquiv FX finSuccEquivLast).trans (MvPolynomial.optionEquivLeft FX (Fin 2))
end
end K1_14_2_4_1_1
end
section
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
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_4_1_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4_1 K1_14_2_3_1
open scoped Polynomial
def c1 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)], SeedLocalization C₀
def c2 : Prop :=
  ∀ (C₀ : ConstantSeeds) [Fact (Irreducible C₀)] (J : Ideal RootAmbient)
    (P : Ideal (ConstantSeedX C₀)[X]), SeedLocalization C₀ →
    P.IsPrime → J = P.comap (genericRootMap C₀) →
    Module.Finite SeedField (RootSeedSection J) →
    0 < Module.finrank SeedField (RootSeedSection J) →
    Module.finrank SeedField (RootSeedSection J) =
      Module.finrank SeedField (PlaneSlice (seedEquation C₀)) *
        Module.finrank (ConstantSeedX C₀) ((ConstantSeedX C₀)[X] ⧸ P)
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
end
section
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
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_4_1_1_1
noncomputable section
open K1_14 K1_14_2_4_1 K1_14_2_4_1_1
open scoped Polynomial
private abbrev PolynomialSeeds := MvPolynomial (Fin 2) L[X]
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
namespace K1_14_2_2_3_2
open K1_14_2_2
theorem proof : K1_14_2_2_3.c2 := by
  intro I hI hd
  obtain ⟨g, hg, hIg⟩ := primeGenerator hI hd
  exact ⟨g, hg, (degree_le_mixed hI g hg.ne_zero hIg).trans_lt hI.mixed_lt, hIg⟩
end K1_14_2_2_3_2
end
section
namespace K1_13_2_3_4
open K1_13_2
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private def daTriple (x : ℤ) : ℤ :=
  denominator (x - 1) + denominator (x - 2) + denominator (x - 3)
private theorem daDenNeg (x : ℤ) (h : x < 0) : denominator x = 0 := ite_eq_left h
private theorem daCumNeg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
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
private def daDenValue (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 15) + 30) + 25) / 72
private def daTripleValue (n : ℕ) : ℕ :=
  (n * (n * (2 * n + 9) + 10) + 3) / 24
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
private def rowsA1_chunk000 : List ℕ := [1,1,2,2]
private theorem rowsA1_chunk000_checked : rowsA1_chunk000.length = 4 ∧ rowsSum 1419 rowsA1_chunk000 = 184 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk004 : List ℕ := [3,3,4,4]
private theorem rowsA1_chunk004_checked : rowsA1_chunk004.length = 4 ∧ rowsSum 1423 rowsA1_chunk004 = 1104 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk008 : List ℕ := [5,6,6,6]
private theorem rowsA1_chunk008_checked : rowsA1_chunk008.length = 4 ∧ rowsSum 1427 rowsA1_chunk008 = 2856 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk012 : List ℕ := [7,8,8,8]
private theorem rowsA1_chunk012_checked : rowsA1_chunk012.length = 4 ∧ rowsSum 1431 rowsA1_chunk012 = 5512 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk016 : List ℕ := [9,9,10,12]
private theorem rowsA1_chunk016_checked : rowsA1_chunk016.length = 4 ∧ rowsSum 1435 rowsA1_chunk016 = 9050 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk020 : List ℕ := [12,12,12,12]
private theorem rowsA1_chunk020_checked : rowsA1_chunk020.length = 4 ∧ rowsSum 1439 rowsA1_chunk020 = 13632 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk024 : List ℕ := [13,13,16,16]
private theorem rowsA1_chunk024_checked : rowsA1_chunk024.length = 4 ∧ rowsSum 1443 rowsA1_chunk024 = 19103 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk028 : List ℕ := [16,16,16,529]
private theorem rowsA1_chunk028_checked : rowsA1_chunk028.length = 4 ∧ rowsSum 1447 rowsA1_chunk028 = 25884 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk032 : List ℕ := [1041,1042,1554,1555]
private theorem rowsA1_chunk032_checked : rowsA1_chunk032.length = 4 ∧ rowsSum 1451 rowsA1_chunk032 = 34333 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk036 : List ℕ := [2067,2068,2584,3096]
private theorem rowsA1_chunk036_checked : rowsA1_chunk036.length = 4 ∧ rowsSum 1455 rowsA1_chunk036 = 44501 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk040 : List ℕ := [3096,3096,3608,4120]
private theorem rowsA1_chunk040_checked : rowsA1_chunk040.length = 4 ∧ rowsSum 1459 rowsA1_chunk040 = 57794 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk044 : List ℕ := [4120,4120,4632,4633]
private theorem rowsA1_chunk044_checked : rowsA1_chunk044.length = 4 ∧ rowsSum 1463 rowsA1_chunk044 = 73760 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk048 : List ℕ := [5145,6170,6170,6171]
private theorem rowsA1_chunk048_checked : rowsA1_chunk048.length = 4 ∧ rowsSum 1467 rowsA1_chunk048 = 91810 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk052 : List ℕ := [6171,6688,268832,269344]
private theorem rowsA1_chunk052_checked : rowsA1_chunk052.length = 4 ∧ rowsSum 1471 rowsA1_chunk052 = 111993 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk056 : List ℕ := [532512,532512,794656,794656]
private theorem rowsA1_chunk056_checked : rowsA1_chunk056.length = 4 ∧ rowsSum 1475 rowsA1_chunk056 = 136932 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk060 : List ℕ := [1056800,1319456,1581601,1582113]
private theorem rowsA1_chunk060_checked : rowsA1_chunk060.length = 4 ∧ rowsSum 1479 rowsA1_chunk060 = 166213 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk064 : List ℕ := [1582114,1844770,2106915,2107427]
private theorem rowsA1_chunk064_checked : rowsA1_chunk064.length = 4 ∧ rowsSum 1483 rowsA1_chunk064 = 199448 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk068 : List ℕ := [2109476,2371620,2371620,2633766]
private theorem rowsA1_chunk068_checked : rowsA1_chunk068.length = 4 ∧ rowsSum 1487 rowsA1_chunk068 = 236173 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk072 : List ℕ := [3158054,3158054,137375782,137375784]
private theorem rowsA1_chunk072_checked : rowsA1_chunk072.length = 4 ∧ rowsSum 1491 rowsA1_chunk072 = 279400 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk076 : List ℕ := [271594032,406073904,406336560,541078576]
private theorem rowsA1_chunk076_checked : rowsA1_chunk076.length = 4 ∧ rowsSum 1495 rowsA1_chunk076 = 323511 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk080 : List ℕ := [541079088,675296816,809515056,809517104]
private theorem rowsA1_chunk080_checked : rowsA1_chunk080.length = 4 ∧ rowsSum 1499 rowsA1_chunk080 = 380169 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk084 : List ℕ := [809779248,943996976,1078476848,1078476848]
private theorem rowsA1_chunk084_checked : rowsA1_chunk084.length = 4 ∧ rowsSum 1503 rowsA1_chunk084 = 443081 := by
  apply daChecked
  decide +kernel
private def rowsA1_chunk088 : List ℕ := [1078738992,1212956720]
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
private def rowsA2_chunk000 : List ℕ := [1213218864,70336397360,70336397872,139055874609]
private theorem rowsA2_chunk000_checked : rowsA2_chunk000.length = 4 ∧ rowsSum 1509 rowsA2_chunk000 = 549100 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk004 : List ℕ := [139055875121,207775352370,207909570098,276629047347]
private theorem rowsA2_chunk004_checked : rowsA2_chunk004.length = 4 ∧ rowsSum 1513 rowsA2_chunk004 = 631098 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk008 : List ℕ := [276763265075,345751439412,414470917172,414471179316]
private theorem rowsA2_chunk008_checked : rowsA2_chunk008.length = 4 ∧ rowsSum 1517 rowsA2_chunk008 = 721185 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk012 : List ℕ := [483190656054,551910394934,552044613686,552044879926]
private theorem rowsA2_chunk012_checked : rowsA2_chunk012.length = 4 ∧ rowsSum 1521 rowsA2_chunk012 = 818867 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk016 : List ℕ := [620899622968,35805405929536,35874125406272,71196070666304]
private theorem rowsA2_chunk016_checked : rowsA2_chunk016.length = 4 ∧ rowsSum 1525 rowsA2_chunk016 = 919874 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk020 : List ℕ := [71196607537216,0x60c0c0806040,0x60c0c0806040,0x80c0c0806040]
private theorem rowsA2_chunk020_checked : rowsA2_chunk020.length = 4 ∧ rowsSum 1529 rowsA2_chunk020 = 1043682 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk024 : List ℕ := [0x80d0c0846040,0xa0e0c0846040,0xc100c0886040,0xc100c0886040]
private theorem rowsA2_chunk024_checked : rowsA2_chunk024.length = 4 ∧ rowsSum 1533 rowsA2_chunk024 = 1181252 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk028 : List ℕ := [0xe100c08c6040,282577852981312,282577987461184,282646706937920]
private theorem rowsA2_chunk028_checked : rowsA2_chunk028.length = 4 ∧ rowsSum 1537 rowsA2_chunk028 = 1328543 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk032 : List ℕ := [0x412110d8906240,0x412120d8986240,0x814120e0986441,0x81813100986441]
private theorem rowsA2_chunk032_checked : rowsA2_chunk032.length = 4 ∧ rowsSum 1541 rowsA2_chunk032 = 1486575 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk036 : List ℕ := [0xc1813100986642,0xc1818100a06642,72481460078012483,90531042959583299]
private theorem rowsA2_chunk036_checked : rowsA2_chunk036.length = 4 ∧ rowsSum 1545 rowsA2_chunk036 = 1653595 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk040 : List ℕ := [0x181a18100c06844,0x181c18100c06c44,0x182018100c06c44,0x1c2018100c06c46]
private theorem rowsA2_chunk040_checked : rowsA2_chunk040.length = 4 ∧ rowsSum 1549 rowsA2_chunk040 = 1814289 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk044 : List ℕ := [0x202018108c07046,0x202018110c07046,0x8202019110c08046,0x8242219118c08048]
private theorem rowsA2_chunk044_checked : rowsA2_chunk044.length = 4 ∧ rowsSum 1553 rowsA2_chunk044 = 1964020 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk048 : List ℕ := [0x1024221a118c08048,0x1030241a120c08048,0x1830261b120c08048,0x2030261c120c08048]
private theorem rowsA2_chunk048_checked : rowsA2_chunk048.length = 4 ∧ rowsSum 1557 rowsA2_chunk048 = 2129047 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk052 : List ℕ := [0x20302820130c0804c,0x28303020130c0804c,0x30343020130c4804c,0x30343020130c4804c]
private theorem rowsA2_chunk052_checked : rowsA2_chunk052.length = 4 ∧ rowsSum 1561 rowsA2_chunk052 = 2309631 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk056 : List ℕ := [0x30383020140c8804c,0x38403020180c8804c,0x40403020180cc804c,0x1040403020180cc804c]
private theorem rowsA2_chunk056_checked : rowsA2_chunk056.length = 4 ∧ rowsSum 1565 rowsA2_chunk056 = 2504617 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk060 : List ℕ := [0x1048403020180d08050,0x2048443221180d08060,0x2050443221180d08060,0x3060483422180d88260]
private theorem rowsA2_chunk060_checked : rowsA2_chunk060.length = 4 ∧ rowsSum 1569 rowsA2_chunk060 = 2708537 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk064 : List ℕ := [0x4060483423180d88460,0x40604c3623180d88460,0x50604c3624180d88660,0x6060503824180e08660]
private theorem rowsA2_chunk064_checked : rowsA2_chunk064.length = 4 ∧ rowsSum 1573 rowsA2_chunk064 = 2946193 := by
  apply daChecked
  decide +kernel
private def rowsA2_chunk068 : List ℕ := [0x6068604024181008860,0x6068604026181008860]
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
private def rowsA3_chunk000 : List ℕ := [0x7080604026181008860,0x208080604026181008c60,0x208080604026181008c60,0x409080604028189008c60]
private theorem rowsA3_chunk000_checked : rowsA3_chunk000.length = 4 ∧ rowsSum 1579 rowsA3_chunk000 = 3338238 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk004 : List ℕ := [0x409080604030189008c60,0x60a088604030191009060,0x60c088644230191009060,0x80c090644230199009060]
private theorem rowsA3_chunk004_checked : rowsA3_chunk004.length = 4 ∧ rowsSum 1583 rowsA3_chunk004 = 3625471 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk008 : List ℕ := [0xa0c090684430199009060,0xc0c0986844301a1009060,0xc0c0a06c46301a1009060,0xc0d0c07046301a1009860]
private theorem rowsA3_chunk008_checked : rowsA3_chunk008.length = 4 ∧ rowsSum 1587 rowsA3_chunk008 = 3946296 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk012 : List ℕ := [0xe0e0c08048301b1009860,0x410100c08048301b1009860,0x410100c0804c301b1009860,0x810100c0804c301b1049860]
private theorem rowsA3_chunk012_checked : rowsA3_chunk012.length = 4 ∧ rowsSum 1591 rowsA3_chunk012 = 4286127 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk016 : List ℕ := [0x812100c0804c301c1089860,0xc14100c0804c30201089860,0x1018110c08050302010ca060,0x1018110c88050302010ca060]
private theorem rowsA3_chunk016_checked : rowsA3_chunk016.length = 4 ∧ rowsSum 1595 rowsA3_chunk016 = 4649499 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk020 : List ℕ := [0x1418120c880603120110c060,0x1818130d084603120110c060,0x1818130d088603220110c060,0x181a140d888603220118c060]
private theorem rowsA3_chunk020_checked : rowsA3_chunk020.length = 4 ∧ rowsSum 1599 rowsA3_chunk020 = 5008695 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk024 : List ℕ := [0x81c1a180d88c603320118c060,0x8201c180e08c603320118c060,0x1020201810090603420118c061,0x1024201810090603420120c061]
private theorem rowsA3_chunk024_checked : rowsA3_chunk024.length = 4 ∧ rowsSum 1603 rowsA3_chunk024 = 5391796 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk028 : List ℕ := [0x1824201810090603420120c062,0x1828201810098603620120c062,0x2030221810098603620120c063,0x2030221810098603620120c063]
private theorem rowsA3_chunk028_checked : rowsA3_chunk028.length = 4 ∧ rowsSum 1607 rowsA3_chunk028 = 5767634 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk032 : List ℕ := [0x30302419100a0603820130c064,0x30302419100a0603820930c064,0x3030261a108c0604020930c064,0x103834281a108c0604021130c066]
private theorem rowsA3_chunk032_checked : rowsA3_chunk032.length = 4 ∧ rowsSum 1611 rowsA3_chunk032 = 6156288 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk036 : List ℕ := [0x104038301b110c0624021130c066,0x204040301b110c0644021930c066,0x204040301c118c0644021930c066,0x3048403020120c0664022130c068]
private theorem rowsA3_chunk036_checked : rowsA3_chunk036.length = 4 ∧ rowsSum 1615 rowsA3_chunk036 = 6577418 := by
  apply daChecked
  decide +kernel
private def rowsA3_chunk040 : List ℕ := [0x3050403020120c0664022140c068,0x4060403020120c0684022140c068]
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
private def rowsA4_chunk000 : List ℕ := [0x5060443020130c0684023180c068,0x6060483020130c0684023180c068,0x6060483220130c06c4023180c06c,0x60604c3220130c06c4024180c06c]
private theorem rowsA4_chunk000_checked : rowsA4_chunk000.length = 4 ∧ rowsSum 1621 rowsA4_chunk000 = 7260342 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk004 : List ℕ := [0x2070684c3420140c06c4024180c06c,0x208068503421180c06c4024180c06c,0x408080603622180c0704024180c06c,0x609080603622180c0804024180c06c]
private theorem rowsA4_chunk004_checked : rowsA4_chunk004.length = 4 ∧ rowsSum 1625 rowsA4_chunk004 = 7766341 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk008 : List ℕ := [0x609080603823180c4804124180c06c,0x80a080604023180c4804126180c06c,0x80c080604024180c8804226180c070,0xa0c088604024180cc804226180c280]
private theorem rowsA4_chunk008_checked : rowsA4_chunk008.length = 4 ∧ rowsSum 1629 rowsA4_chunk008 = 8309886 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk012 : List ℕ := [0xc0c088604024180cc804326180c280,0xc0c090604026180d0804426180c480,0x40e0c098644026180d0804426180c480,0x4100d098644026180d0804426180c680]
private theorem rowsA4_chunk012_checked : rowsA4_chunk012.length = 4 ∧ rowsSum 1633 rowsA4_chunk012 = 8898525 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk016 : List ℕ := [0x8100e0a0684028180d8804628180c680,0x810100c0684228180d8804628180c880,0xc12100c06c4230180d8804628180c880,0x1012100c0704430180d8804630180c880]
private theorem rowsA4_chunk016_checked : rowsA4_chunk016.length = 4 ∧ rowsSum 1637 rowsA4_chunk016 = 9516978 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk020 : List ℕ := [0x1014100c0804630180e0804830180cc80,0x1418100c080463018900804830180cc80,0x1818110c080483018900804830180cc80,0x1818120c080483019100824830180cc80]
private theorem rowsA4_chunk020_checked : rowsA4_chunk020.length = 4 ∧ rowsSum 1641 rowsA4_chunk020 = 10091626 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk024 : List ℕ := [0x81818120c080483019100824830180d080,0x8201a130c8804c3019900844c30180d080,0x10201a130c8804c301a100844c30180d080,0x18201c140d0804c301a100864c30180d080]
private theorem rowsA4_chunk024_checked : rowsA4_chunk024.length = 4 ∧ rowsSum 1645 rowsA4_chunk024 = 10709640 := by
  apply daChecked
  decide +kernel
private def rowsA4_chunk028 : List ℕ := [0x182420180d08450301a100884c30180d080,0x202420180d88450301b100884c30180d880,0x202820180e08860301b100884c30180d880,0x283020181008860301b1008c4c30180d880]
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
private def rowsA5_chunk000 : List ℕ := [0x303022181008c60301b1008c4c30180d880,0x303022181008c60311c1008c5030184d880,0x1038302418100906031201008c5030184d880,0x204034241810090603220100906030188d880]
private theorem rowsA5_chunk000_checked : rowsA5_chunk000.length = 4 ∧ rowsSum 1653 rowsA5_chunk000 = 12030169 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk004 : List ℕ := [0x204034261910098603220100906030188d880,0x304038281a1009860332010490603018ce080,0x304840301a10098603320104906030190e080,0x404840301b108986034201089060301910080]
private theorem rowsA5_chunk004_checked : rowsA5_chunk004.length = 4 ∧ rowsSum 1657 rowsA5_chunk004 = 12736568 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk008 : List ℕ := [0x506040301b108a06034201089860301910080,0x606040301c110c060342010c9860301990080,0x6060443020110c06036201109860301990080,0x206060443020118c06036201109860301990080]
private theorem rowsA5_chunk008_checked : rowsA5_chunk008.length = 4 ∧ rowsSum 1661 rowsA5_chunk008 = 13509033 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk012 : List ℕ := [0x207060483020118c06036201109860301990080,0x408068483020120c06238201189860301a10080,0x6080684c3220120c06238201189860301a10081,0x609080503220130c06440201189860301a10081]
private theorem rowsA5_chunk012_checked : rowsA5_chunk012.length = 4 ∧ rowsSum 1665 rowsA5_chunk012 = 14361060 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk016 : List ℕ := [0x809080603420130c0644020118a060301a10082,0x80a080603420130c0664020120a060301a10082,0xa0c080603621130c0664020920c060301a10083,0xc0c080603821140c0684020920c060309b10084]
private theorem rowsA5_chunk016_checked : rowsA5_chunk016.length = 4 ∧ rowsSum 1669 rowsA5_chunk016 = 15213582 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk020 : List ℕ := [0x40c0c088604022180c0684021120c060309b10084,0x40e0c088604023180c06c4021120c060311b10084,0x8100d090604023180c06c4021930c060311b10086,0xc100d098604024180c06c4022130c060319b10086]
private theorem rowsA5_chunk020_checked : rowsA5_chunk020.length = 4 ∧ rowsSum 1673 rowsA5_chunk020 = 16020251 := by
  apply daChecked
  decide +kernel
private def rowsA5_chunk024 : List ℕ := [0xc100e098644024180c06c4022130c060321b10086,0x1012100a0644024180c4704022130c060321b10086,0x1014100c0684026180c8704023130c060321c10088]
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
private def rowsA6_chunk000 : List ℕ := [0x1418100c0684026180c8804023130c060331c10088,0x1818100c06c4226180cc804023130c060332010088,0x81818110c0704228180cc804023140c060332010088,0x81c18110c0804428180d0804124140c060332010088]
private theorem rowsA6_chunk000_checked : rowsA6_chunk000.length = 4 ∧ rowsSum 1680 rowsA6_chunk000 = 17567317 := by
  apply daChecked
  decide +kernel
private def rowsA6_chunk004 : List ℕ := [0x102018120c0804430180d0804124140c060342010088,0x18201a120c0804630180d0804224180c06034201008c,0x18201c130c0804830180d8804224180c06034201008c,0x202420140c8804830180d8804324180c06034201008c]
private theorem rowsA6_chunk004_checked : rowsA6_chunk004.length = 4 ∧ rowsSum 1684 rowsA6_chunk004 = 18497024 := by
  apply daChecked
  decide +kernel
private def rowsA6_chunk008 : List ℕ := [0x202820180d0804830180d8804326180c06134201008c,0x283020180d0804c30188e0804426180c06136201008c,0x303020180d8804c30190e0804426180c06236201008c,0x10303022180d8844c3019100804626180c06236201008c]
private theorem rowsA6_chunk008_checked : rowsA6_chunk008.length = 4 ∧ rowsSum 1688 rowsA6_chunk008 = 19536570 := by
  apply daChecked
  decide +kernel
private def rowsA6_chunk012 : List ℕ := [0x20383022180e084503019900804626180c06336201008c,0x204030241810088503019900804626180c064362010290,0x30403424181008c60301a100804626180c064362010290,0x30403826181008c60301a100824828180c064362010490]
private theorem rowsA6_chunk012_checked : rowsA6_chunk012.length = 4 ∧ rowsSum 1692 rowsA6_chunk012 = 20635869 := by
  apply daChecked
  decide +kernel
private def rowsA6_chunk016 : List ℕ := [0x40484026191009060301b100824828180c066362010490,0x50504030191009060301b100844828180c066382010690,0x606040301a1009060301b100844830180c066382010690,0x20606040301a1009860311b100864830180c066402010890]
private theorem rowsA6_chunk016_checked : rowsA6_chunk016.length = 4 ∧ rowsSum 1696 rowsA6_chunk016 = 21713176 := by
  apply daChecked
  decide +kernel
private def rowsA6_chunk020 : List ℕ := [0x20606044301b1009860311c100884c30180c068402010890,0x40706044301c1089860321c100884c30180c068402010890,0x408068483020110a0603220100884c30180c068402010c90]
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
private def rowsA7_chunk000 : List ℕ := [0x608068483020110a06033201008c4c30180c268402010c90,0x8090704c3020118c06034201008c4c30180c468402010c98,0x8090804c3220118c06034201008c4c30180c46c402010c98,0xa0a080603220120c06034201048c4c30180c66c402011098]
private theorem rowsA7_chunk000_checked : rowsA7_chunk000.length = 4 ∧ rowsSum 1703 rowsA7_chunk000 = 23599906 := by
  apply daChecked
  decide +kernel
private def rowsA7_chunk004 : List ℕ := [0x40c0c080603420120c0603620104905030180c66c402011098,0x40c0c080603420130c0603620108905030180c86c402011098,0x80e0c088603620130c0623620108905030180c86c402011098,0x8100c088603821130c062382010c906030180c86c402011098]
private theorem rowsA7_chunk004_checked : rowsA7_chunk004.length = 4 ∧ rowsSum 1707 rowsA7_chunk004 = 24803520 := by
  apply daChecked
  decide +kernel
private def rowsA7_chunk008 : List ℕ := [0xc100d090604021130c0643820110906030180cc6c402011898,0xc100d090604022140c0644020110986030180cc6c402011898,0x10120e098604023180c0664020110986030180cc70402011898,0x1414100a0644023180c0684020118986030180d070402051898]
private theorem rowsA7_chunk008_checked : rowsA7_chunk008.length = 4 ∧ rowsSum 1711 rowsA7_chunk008 = 26030978 := by
  apply daChecked
  decide +kernel
private def rowsA7_chunk012 : List ℕ := [0x1818100c0644024180c0684020118986030180d0804020518c0,0x81818100c0684024180c0684020118986030184d0804020918c0,0x101818100c0684024180c06c4020918986030184d0804020918c0,0x102018110c06c4026180c06c4020920986030188d0804020d18c0]
private theorem rowsA7_chunk012_checked : rowsA7_chunk012.length = 4 ∧ rowsSum 1715 rowsA7_chunk012 = 27292478 := by
  apply daChecked
  decide +kernel
private def rowsA7_chunk016 : List ℕ := [0x18201a110c0704226180c46c4021120a06030188d0804021120c0,0x18201a120c0804226180c4704021920a0603018cd8804021120c0,0x20241c130c0804428180c8704021920a06030190d8804021120c0,0x282420130c0804628180cc804022120c06030190d8804021920c0]
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
private def rowsA8_chunk000 : List ℕ := [0x302820140c8804630180cc804022130c06030190d8804021920c0,0x10303020180c8804830180d0804022130c06030198d8804021920c0,0x20303020180d0804830180d0804023130c06030198d8804021920c0,0x20383022180d8804830180d0804023130c06030198d8804022120c0]
private theorem rowsA8_chunk000_checked : rowsA8_chunk000.length = 4 ∧ rowsSum 1723 rowsA8_chunk000 = 29931024 := by
  apply daChecked
  decide +kernel
private def rowsA8_chunk004 : List ℕ := [0x30403022180d8804c30180d8804123130c06030198e0804022120c0,0x30403424180e0844c30188d8804124130c060301a0e0804022120c0,0x4048382418100844c30188d8804224130c060309a0e0804022120c0,0x5048402618100885030190e0804224140c060311a100804022130c0]
private theorem rowsA8_chunk004_checked : rowsA8_chunk004.length = 4 ∧ rowsSum 1727 rowsA8_chunk004 = 31362247 := by
  apply daChecked
  decide +kernel
private def rowsA8_chunk008 : List ℕ := [0x60504028191008c5030190e0804324140c060311a1008040a2130c0,0x2060604030191008c603019900804424140c060319a1008040a3130c0,0x40606040301a10090603019900804424180c060319b100804123130c0,0x40706044301a1009060301a100804426180c060321b100804123130c0]
private theorem rowsA8_chunk008_checked : rowsA8_chunk008.length = 4 ∧ rowsSum 1731 rowsA8_chunk008 = 32793617 := by
  apply daChecked
  decide +kernel
private def rowsA8_chunk012 : List ℕ := [0x60806044301b1009060301a100804626180c060321b1008041a3130c0,0x60806848301b1009860301b100804626180c060321b1008041a3130c0,0x8090684830201089860301b100824626180c060331b100804223130c0,0xa090804c30201109860311b100824826180c060331b100804223130c0]
private theorem rowsA8_chunk012_checked : rowsA8_chunk012.length = 4 ∧ rowsSum 1735 rowsA8_chunk012 = 34383972 := by
  apply daChecked
  decide +kernel
private def rowsA8_chunk016 : List ℕ := [0x40c0a0804c3020110a060321b100844826180c060331b100804224130c0,0x40c0c080603220118a060321c100844826180c060341c100804324130c0]
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
private def rowsA9_chunk000 : List ℕ := [0x80c0c080603420118c0603320100864828180c061341c100804324130c0,0x8100c080603420120c0603320100884828180c062341c100804324130c0,0xc100c088603620120c0603420100884830180c0623420100804424130c0,0x10100d090603620130c0603420100884c30180c0633420100804424180c0]
private theorem rowsA9_chunk000_checked : rowsA9_chunk000.length = 4 ∧ rowsSum 1741 rowsA9_chunk000 = 36670908 := by
  apply daChecked
  decide +kernel
private def rowsA9_chunk004 : List ℕ := [0x10120e090603821130c06036201008c4c30180c0633420100804424180c0,0x141210098604021130c06036201008c4c30180c0643620100804424180c0,0x8181810098604022130c06236201048c4c30180c0643620100814424180c0,0x81818100c0644023140c0643620108904c30180c0643620100814424180c0]
private theorem rowsA9_chunk004_checked : rowsA9_chunk004.length = 4 ∧ rowsSum 1745 rowsA9_chunk004 = 38204146 := by
  apply daChecked
  decide +kernel
private def rowsA9_chunk008 : List ℕ := [0x101c18100c0644023180c0643820108904c30180c0663620100824624180c0,0x182018110c0684024180c066402010c904c30180c0663620100834626180c0,0x182018110c06c4024180c066402010c905030180c0663620100834626180c0,0x20201a120c06c4024180c0684020110905030180c2683620100844626180c0]
private theorem rowsA9_chunk008_checked : rowsA9_chunk008.length = 4 ∧ rowsSum 1749 rowsA9_chunk008 = 39928229 := by
  apply daChecked
  decide +kernel
private def rowsA9_chunk012 : List ℕ := [0x20241c120c0704226180c0684020110905030180c2683820100844626180c0,0x10302820130c0804226180c06c4020118986030180c4683820100844626180c0,0x10303020130c0804426180c46c4020118986030180c6683820100864626180c0,0x20303020180c8804428180c46c4020918986030180c6684020100864826180c0]
private theorem rowsA9_chunk012_checked : rowsA9_chunk012.length = 4 ∧ rowsSum 1753 rowsA9_chunk012 = 41715946 := by
  apply daChecked
  decide +kernel
private def rowsA9_chunk016 : List ℕ := [0x20383020180c8804628180c86c4020918986030180c8684020100864826180c0]
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
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open private fastDen fastC fastOld fastKernel from ProximityPrize.SubmissionLower.Numeric6Defs
open private decode runLength rowLength rowValue rowStart runValue sumFrom from ProximityPrize.SubmissionLower.Numeric6AuxCert
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private def auxCDen (k : ℕ) : ℕ :=
  let lin := Nat.add (Nat.mul 2 k) 15
  let quad := Nat.add (Nat.mul k lin) 30
  Nat.div (Nat.add (Nat.mul k quad) 25) 72
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
    [77309411328,4496818176,2282225664,2349203456,13019512832,6543507456,4362469376,
    2248409088,4362338304,2198077440,33816576,6442713472,6442647936,8590131456,4295098624,
    98560,2147549440,2147533056,33024,24832,16640,264,259,15032385792,2147483872,
    2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,
    8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,
    2147483672,16,12,8,3],
    [77309411328,6644301824,134742016,2349203456,13019512832,8690991104,2214985728,
    2248409088,4362338304,4345561088,8590197120,6442647936,8590131456,2147614976,98560,
    4295033088,49408,2147516672,24832,12544,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2],
    [79456894976,4496818176,2282225664,2349203456,10872029184,8690991104,4362469376,
    100925440,6509821952,2198077440,8590197120,8590131584,6442647808,4295098624,98560,
    2147549440,2147533056,33024,24832,16640,268,262,257,15032385792,224,2147483864,
    2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,
    112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,
    24,17,16,12,6,1],
    [79456894976,4496818176,2282225664,2349203456,13019512832,6543507456,4362469376,
    2248409088,4362338304,2198077440,10737680768,8590131584,6442647808,2147614976,98560,
    4295033088,2147533056,33024,24832,268,264,260,17179869440,224,2147483864,208,204,
    200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,
    8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [81604378624,4496818176,2282225664,201719808,13019512832,8690991104,4362469376,
    100925440,6509821952,2198077440,10737680768,6442647936,6442647808,4295098624,98560,
    2147549440,2147533056,33024,24832,16640,268,264,259,15032385792,2147483872,
    2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,
    8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,
    2147483672,16,12,8,3],
    [81604378624,4496818176,4429709312,201719808,10872029184,8690991104,4362469376,
    2248409088,4362338304,2198077440,10737680768,8590131584,6442647808,2147614976,98560,
    4295033088,2147533056,33024,24832,272,268,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2]
  ]
private theorem auxCValues3103 : auxCBatch 3103 auxCData3103 6 533140834 :=
  auxCChecked 3103 auxCData3103
    [87538471,88431136,88445518,89347227,89301948,90076534] (by decide +kernel)
private def auxCData3109 : List (List ℕ) := [
    [81604378624,4496818176,4429709312,201719808,13019512832,6543507456,6509953024,
    100925440,4362338304,2198077440,12885164416,8590131584,6442647808,2147614976,98560,
    2147549440,2147533056,33024,24832,16640,272,268,262,257,15032385792,224,2147483864,
    2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,
    112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,
    24,17,16,12,6,1],
    [83751862272,4496818176,4429709312,201719808,10872029184,8690991104,4362469376,50724864,
    6509821952,50593792,12885164416,10737615232,4295164160,2147614976,2147582208,2147549440,
    2147533056,33024,24832,272,268,264,260,17179869440,224,2147483864,208,204,200,196,
    17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,
    72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [83751862272,4496818176,4429709312,201719808,13019512832,6543507456,6509953024,
    100925440,4362338304,2198077440,12885164416,8590131584,6442647808,2147614976,98560,
    4295033088,49408,2147516672,16640,272,268,264,259,15032385792,2147483872,2147483864,
    208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3],
    [85899345920,4496818176,4429709312,13019512832,8690991104,4362469376,50724864,
    6509821952,50593792,15032648064,8590131584,4295164160,2147614976,2147582208,2147549440,
    2147533056,33024,24832,2147483920,268,262,258,15032385792,224,2147483864,2147483856,
    204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,
    102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,
    16,12,6,2],
    [85899345920,4496818176,4429709312,201719808,10872029184,8690991104,4362469376,50724864,
    100925440,4362338304,50593792,15032648064,10737615232,4295164160,2147614976,98560,
    4295033088,49408,2147516672,280,2147483920,268,262,257,15032385792,224,2147483864,
    2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,
    112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,
    24,17,16,12,6,1],
    [85899345920,4496818176,6577192960,13019512832,6543507456,6509953024,50724864,
    4362338304,50593792,17180131712,10737615232,4295164160,131328,2147582208,2147549440,
    2147533056,33024,24832,280,272,268,264,260,17179869440,224,2147483864,208,204,200,
    196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,
    76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
  ]
private theorem auxCValues3109 : auxCBatch 3109 auxCData3109 6 551130453 :=
  auxCChecked 3109 auxCData3109
    [90766116,90885142,91739364,91775485,92704907,93259439] (by decide +kernel)
private def auxCData3115 : List (List ℕ) := [
    [88046829568,4496818176,6577192960,10872029184,8690991104,4362469376,2198208512,
    4362338304,50593792,15032648064,10737615232,4295164160,2147614976,98560,4295033088,
    2147533056,33024,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,
    204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,
    99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,
    3],
    [88046829568,4496818176,6577192960,13019512832,6543507456,6509953024,50724864,
    4362338304,50593792,17180131712,10737615232,4295164160,2147614976,98560,2147549440,
    2147533056,33024,24832,280,2147483920,268,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2],
    [90194313216,2349334528,8724676608,10872029184,8690991104,4362469376,2198208512,
    4362338304,19327615360,10737615232,4295164160,131328,2147582208,2147549440,2147533056,
    33024,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,
    198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,
    97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,
    6,1],
    [90194313216,4496818176,6577192960,10872029184,8690991104,4362469376,2198208512,
    4362338304,19327615360,12885098880,2147680512,2147614976,98560,4295033088,49408,
    2147516672,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,
    17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,
    72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [90194313216,4496818176,8724676608,10872029184,6543507456,6509953024,2198208512,
    2214854656,50593792,19327615360,10737615232,4295164160,131328,2147582208,2147549440,
    2147533056,33024,288,2147483928,272,268,264,259,15032385792,2147483872,2147483864,
    208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3],
    [92341796864,2349334528,8724676608,10872029184,8690991104,4362469376,2198208512,
    33947648,2214854656,19327615360,12885098880,2147680512,2147614976,98560,4295033088,
    49408,33024,288,2147483928,2147483920,268,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2]
  ]
private theorem auxCValues3115 : auxCBatch 3115 auxCData3115 6 569091567 :=
  auxCChecked 3115 auxCData3115
    [93388796,94248210,94182920,95243120,95854815,96173706] (by decide +kernel)
private def auxCData3121 : List (List ℕ) := [
    [92341796864,4496818176,8724676608,10872029184,6543507456,6509953024,2198208512,
    2214854656,21475099008,12885098880,2147680512,131328,2147582208,2147549440,2147533056,
    33024,288,2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,
    204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,
    102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,
    16,12,6,1],
    [94489280512,2349334528,10872160256,8724545536,6543507456,6509953024,2198208512,
    33947648,67371008,23622582656,12885098880,2147680512,131328,98560,4295033088,
    2147533056,2147483936,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,
    200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,
    8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [94489280512,4496818176,8724676608,8724545536,8690991104,4362469376,4345692160,
    2214854656,21475099008,12885098880,2147680512,131328,2147582208,2147549440,2147533056,
    33024,2147483936,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,
    204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,
    99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,
    3],
    [94489280512,4496818176,10872160256,8724545536,6543507456,6509953024,2198208512,
    33947648,67371008,23622582656,12885098880,2147680512,131328,2147582208,2147549440,
    2147533056,2147483936,2147483928,2147483920,268,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2],
    [96636764160,2349334528,10872160256,8724545536,8690991104,4362469376,2198208512,
    33947648,67371008,23622582656,15032582528,196864,131328,2147582208,4295033088,49408,
    33024,2147483936,2147483928,2147483920,268,262,257,15032385792,224,2147483864,
    2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,6442451072,
    112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,
    24,17,16,12,6,1],
    [96636764160,4496818176,10872160256,8724545536,6543507456,4362469376,4345692160,
    33947648,67371008,23622582656,15032582528,196864,131328,2147582208,2147549440,
    2147533056,4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,
    200,196,17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,
    8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4]
  ]
private theorem auxCValues3121 : auxCBatch 3121 auxCData3121 6 588624088 :=
  auxCChecked 3121 auxCData3121
    [96895255,96783674,97940204,98480426,98977850,99546679] (by decide +kernel)
private def auxCData3127 : List (List ℕ) := [
    [98784247808,2349334528,10872160256,8724545536,6543507456,6509953024,2198208512,
    2181431296,25770066304,12885098880,2147680512,2147582208,4295033088,49408,304,
    4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,208,204,200,
    195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,104,99,
    8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3],
    [98784247808,2349334528,13019643904,6577061888,8690991104,4362469376,4345692160,
    33947648,25770066304,15032582528,196864,131328,2147582208,2147549440,2147533056,
    4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,
    204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,
    102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,
    16,12,6,2],
    [98784247808,4496818176,13019643904,6577061888,6543507456,6509953024,2198208512,
    2181431296,25770066304,15032582528,196864,2147582208,4295033088,49408,304,4294967584,
    2147483928,2147483920,268,262,257,15032385792,224,2147483864,2147483856,204,198,193,
    15032385728,160,2147483800,2147483792,140,134,129,6442451072,112,108,102,97,
    6442451040,80,76,70,65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,
    1],
    [100931731456,2349334528,13019643904,6577061888,8690991104,4362469376,2198208512,
    2181431296,25770066304,17180066176,131328,2147582208,2147549440,2147533056,304,
    4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,
    17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,
    72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [100931731456,4496818176,13019643904,6577061888,6543507456,4362469376,4345692160,
    33947648,25559040,25770066304,15032582528,196864,98688,2147582208,2147549440,49408,
    2147483952,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,
    208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3],
    [103079215104,2349334528,13019643904,6577061888,6543507456,6509953024,2198208512,
    2181431296,25559040,25770066304,15032582528,196864,98688,98560,4295033088,49408,304,
    4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,
    204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,
    102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,
    16,12,6,2]
  ]
private theorem auxCValues3127 : auxCBatch 3127 auxCData3127 6 608227577 :=
  auxCChecked 3127 auxCData3127
    [99738493,100649740,101225458,101742608,102334122,102537156] (by decide +kernel)
private def auxCData3133 : List (List ℕ) := [
    [103079215104,2349334528,13019643904,101187584,4429578240,8690991104,4362469376,
    2198208512,2181431296,25559040,25770066304,17180066176,98688,2147582208,2147549440,
    49408,2147483952,4294967584,2147483928,2147483920,268,262,257,15032385792,224,
    2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,
    6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,
    33,32,25,24,17,16,12,6,1],
    [103079215104,4496818176,13019643904,6577061888,6543507456,6509953024,2198208512,
    2181431296,25559040,25770066304,17180066176,98688,98560,4295033088,49408,2147483952,
    4294967584,2147483928,272,268,264,260,17179869440,224,2147483864,208,204,200,196,
    17179869376,160,2147483800,144,140,136,132,8589934720,108,104,100,8589934688,76,
    72,68,4294967360,52,4294967344,36,2147483680,2147483672,16,12,8,4],
    [105226698752,2349334528,13019643904,101187584,4429578240,8690991104,4362469376,
    2198208512,2181431296,25559040,25770066304,17180066176,2147582336,98560,2147549440,
    49408,4294967600,4294967584,2147483928,272,268,264,259,15032385792,2147483872,
    2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,
    8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,
    2147483672,16,12,8,3],
    [105226698752,4496818176,13019643904,101187584,4429578240,6543507456,4362469376,
    4345692160,33947648,2173042688,25770066304,17180066176,2147582336,4295033088,4294967600,
    4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,2147483856,
    204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,
    102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,
    16,12,6,2],
    [107374182400,2349334528,13019643904,101187584,4429578240,6543507456,6509953024,
    2198208512,2181431296,25559040,17170432,25770066304,15032582528,2147582336,98560,
    2147549440,49408,4294967600,4294967584,2147483928,2147483920,268,262,257,15032385792,
    224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,
    129,6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,
    38,33,32,25,24,17,16,12,6,1],
    [107374182400,2349334528,13019643904,2248671232,2282094592,8690991104,4362469376,
    2198208512,2181431296,25559040,17170432,25770066304,17180066176,2147582336,98560,
    2147549440,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,
    2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,
    108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,
    16,12,8,4]
  ]
private theorem auxCValues3133 : auxCBatch 3133 auxCData3133 6 629231195 :=
  auxCChecked 3133 auxCData3133
    [103444958,104227698,104582763,105169767,105502099,106303910] (by decide +kernel)
private def auxCData3139 : List (List ℕ) := [
    [109521666048,2349334528,13019643904,101187584,4429578240,6543507456,6509953024,
    2198208512,2181431296,25559040,17170432,25770066304,15032582528,4295065984,4295033088,
    6442451248,4294967584,2147483928,272,268,264,259,15032385792,2147483872,2147483864,
    208,204,200,195,15032385728,2147483808,2147483800,144,140,136,131,8589934720,108,
    104,99,8589934688,76,72,67,4294967360,51,4294967344,35,2147483680,2147483672,16,
    12,8,3],
    [109521666048,2349334528,13019643904,2248671232,2282094592,8690991104,4362469376,
    2198208512,2181431296,25559040,17170432,25770066304,17180066176,4295065984,2147549440,
    6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,224,2147483864,
    2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,130,6442451072,
    112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,
    24,18,16,12,6,2],
    [109521666048,2349334528,13019643904,2248671232,4429578240,6543507456,4362469376,
    4345692160,33947648,25559040,17170432,12976128,25770066304,15032582528,4295065984,
    4295033088,6442451248,4294967584,2147483928,2147483920,268,262,257,15032385792,224,
    2147483864,2147483856,204,198,193,15032385728,160,2147483800,2147483792,140,134,129,
    6442451072,112,108,102,97,6442451040,80,76,70,65,2147483712,54,49,2147483696,38,
    33,32,25,24,17,16,12,6,1],
    [111669149696,2349334528,13019643904,2248671232,2282094592,6543507456,6509953024,
    2198208512,2181431296,25559040,17170432,8781824,25770066304,15032582528,4295065984,
    2147549440,320,6442451248,4294967584,2147483928,272,268,264,260,17179869440,224,
    2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,8589934720,
    108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,2147483672,
    16,12,8,4],
    [111669149696,2349334528,13019643904,4396154880,134610944,8690991104,4362469376,
    2198208512,2181431296,25559040,17170432,12976128,25770066304,15032582528,4295065984,
    65920,65792,2147483968,6442451248,4294967584,2147483928,272,268,264,259,15032385792,
    2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,144,140,136,
    131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,4294967344,35,
    2147483680,2147483672,16,12,8,3],
    [113816633344,2349334528,13019643904,2248671232,2282094592,6543507456,6509953024,
    2198208512,33947648,2173042688,12976128,6684672,25770066304,15032582528,4295065984,
    65920,65792,320,6442451248,4294967584,2147483928,2147483920,268,262,258,15032385792,
    224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,2147483792,140,134,
    130,6442451072,112,108,102,98,6442451040,80,76,70,66,2147483712,54,50,2147483696,
    38,34,32,26,24,18,16,12,6,2]
  ]
private theorem auxCValues3139 : auxCBatch 3139 auxCData3139 6 649902183 :=
  auxCChecked 3139 auxCData3139
    [106663438,107462595,108401759,108389864,109408998,109575529] (by decide +kernel)
private def auxCData3145 : List (List ℕ) := [
    [113816633344,2349334528,13019643904,4396154880,134610944,8690991104,4362469376,
    2198208512,2181431296,25559040,17170432,8781824,25770066304,15032582528,4295065984,
    65920,65792,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,257,
    15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,
    2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,
    2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1],
    [113816633344,2349334528,13019643904,4396154880,2282094592,6543507456,4362469376,
    4345692160,33947648,25559040,17170432,12976128,6684672,25770066304,12885098880,
    6442549632,65920,65792,2147483968,6442451248,4294967584,2147483928,272,268,264,260,
    17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,
    132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,
    2147483680,2147483672,16,12,8,4],
    [115964116992,2349334528,13019643904,4396154880,134610944,6543507456,6509953024,
    2198208512,2181431296,25559040,17170432,8781824,393600,25770066304,12885098880,
    4295065984,2147549568,4294967616,6442451248,4294967584,2147483928,272,268,264,259,
    15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,
    144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,
    4294967344,35,2147483680,2147483672,16,12,8,3],
    [115964116992,2349334528,13019643904,4396154880,134610944,8690991104,4362469376,
    2198208512,2181431296,25559040,17170432,12976128,4587520,25770066304,12885098880,
    6442549632,2147549568,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,
    258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,
    2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,
    2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2],
    [118111600640,2349334528,10872160256,6543638528,134610944,6543507456,4362469376,
    4345692160,33947648,2173042688,12976128,6684672,393600,25770066304,12885098880,
    4295065984,2147549568,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,
    257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,
    2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,
    2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1],
    [118111600640,2349334528,13019643904,6543638528,8690991104,4362469376,2198208512,
    2181431296,25559040,17170432,8781824,393600,27917549952,10737615232,6442549632,
    2147549568,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,
    224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,
    8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,
    2147483672,16,12,8,4]
  ]
private theorem auxCValues3145 : auxCBatch 3145 auxCData3145 6 672517077 :=
  auxCChecked 3145 auxCData3145
    [110571115,111455567,111522245,112665163,112711833,113591154] (by decide +kernel)
private def auxCData3151 : List (List ℕ) := [
    [120259084288,201850880,13019643904,6543638528,134610944,6543507456,4362469376,
    4345692160,33947648,25559040,17170432,12976128,4587520,393600,25770066304,12885098880,
    4295065984,4295033216,4294967616,6442451248,4294967584,2147483928,272,268,264,259,
    15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,
    144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,
    4294967344,35,2147483680,2147483672,16,12,8,3],
    [120259084288,2349334528,13019643904,6543638528,6543507456,6509953024,2198208512,
    2181431296,25559040,17170432,8781824,2147877248,25770066304,10737615232,6442549632,
    4295033216,2147483968,6442451248,4294967584,2147483928,2147483920,268,262,258,
    15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,2147483800,
    2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,66,
    2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2],
    [120259084288,2349334528,13019643904,6543638528,8690991104,4362469376,2198208512,
    2181431296,25559040,17170432,12976128,2147877248,25770066304,12885098880,6442549632,
    2147549568,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,257,
    15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,
    2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,
    2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1],
    [122406567936,201850880,13019643904,8691122176,6543507456,4362469376,4345692160,
    33947648,2173042688,12976128,6684672,2147877248,25770066304,10737615232,6442549632,
    4295033216,4294967616,6442451248,4294967584,2147483928,272,268,264,260,17179869440,
    224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,132,
    8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,2147483680,
    2147483672,16,12,8,4],
    [122406567936,2349334528,13019643904,6543638528,8690991104,4362469376,2198208512,
    2181431296,25559040,17170432,8781824,2147877248,27917549952,10737615232,6442549632,
    2147549568,49536,4294967616,6442451248,4294967584,2147483928,272,268,264,259,
    15032385792,2147483872,2147483864,208,204,200,195,15032385728,2147483808,2147483800,
    144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,4294967360,51,
    4294967344,35,2147483680,2147483672,16,12,8,3],
    [124554051584,201850880,13019643904,8691122176,6543507456,4362469376,2198208512,
    2181431296,25559040,17170432,12976128,4587520,2147877248,25770066304,10737615232,
    6442549632,4295033216,49536,2147483968,6442451248,4294967584,2147483928,2147483920,268,
    262,258,15032385792,224,2147483864,2147483856,204,198,194,15032385728,160,
    2147483800,2147483792,140,134,130,6442451072,112,108,102,98,6442451040,80,76,70,
    66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,2]
  ]
private theorem auxCValues3151 : auxCBatch 3151 auxCData3151 6 694058266 :=
  auxCChecked 3151 auxCData3151
    [113925853,114679591,115690581,115887800,116779841,117094600] (by decide +kernel)
private def auxCData3157 : List (List ℕ) := [
    [124554051584,2349334528,10872160256,8691122176,67633152,4396023808,6509953024,
    2198208512,2181431296,25559040,17170432,8781824,4295360896,25770066304,10737615232,
    6442549632,4295033216,4294967616,6442451248,4294967584,2147483928,2147483920,268,262,
    257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,2147483800,
    2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,65,
    2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1],
    [126701535232,201850880,13019643904,8691122176,6543507456,4362469376,2198208512,
    2181431296,25559040,17170432,12976128,4295360896,25770066304,10737615232,6442549632,
    4295033216,49536,4294967616,6442451248,4294967584,2147483928,272,268,264,260,
    17179869440,224,2147483864,208,204,200,196,17179869376,160,2147483800,144,140,136,
    132,8589934720,108,104,100,8589934688,76,72,68,4294967360,52,4294967344,36,
    2147483680,2147483672,16,12,8,4],
    [126701535232,201850880,13019643904,8691122176,67633152,4396023808,4362469376,
    4345692160,33947648,25559040,17170432,12976128,6684672,4295360896,25770066304,
    10737615232,6442549632,4295033216,49536,4294967616,6442451248,4294967584,2147483928,
    272,268,264,259,15032385792,2147483872,2147483864,208,204,200,195,15032385728,
    2147483808,2147483800,144,140,136,131,8589934720,108,104,99,8589934688,76,72,67,
    4294967360,51,4294967344,35,2147483680,2147483672,16,12,8,3],
    [126701535232,2349334528,13019643904,6543638528,67633152,6543507456,4362469376,
    2198208512,2181431296,25559040,17170432,8781824,4295360896,27917549952,8590131584,
    131456,4295065984,4295033216,2147533184,2147483968,6442451248,4294967584,2147483928,
    2147483920,268,262,258,15032385792,224,2147483864,2147483856,204,198,194,
    15032385728,160,2147483800,2147483792,140,134,130,6442451072,112,108,102,98,
    6442451040,80,76,70,66,2147483712,54,50,2147483696,38,34,32,26,24,18,16,12,6,
    2],
    [128849018880,201850880,13019643904,8691122176,67633152,4396023808,4362469376,
    2198208512,2181431296,25559040,17170432,12976128,6442844544,25770066304,10737615232,
    6442549632,4295033216,49536,4294967616,6442451248,4294967584,2147483928,2147483920,268,
    262,257,15032385792,224,2147483864,2147483856,204,198,193,15032385728,160,
    2147483800,2147483792,140,134,129,6442451072,112,108,102,97,6442451040,80,76,70,
    65,2147483712,54,49,2147483696,38,33,32,25,24,17,16,12,6,1]
  ]
private theorem auxCValues3157 : auxCBatch 3157 auxCData3157 5 595226413 :=
  auxCChecked 3157 auxCData3157
    [117742062,118322356,118983761,119938168,120240066] (by decide +kernel)
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
def rowsC : List (List ℕ) := auxCRows3103
theorem checkC :
    rowsC.length = 59 ∧ fits 3103 rowsC = true ∧
      value 3103 rowsC = 6091149653 := auxCBatch3103
end K1_13_2_3_6
end
section
namespace K1_13_7
noncomputable section
open Polynomial K1 K1_13
theorem lowerPoint_injective : Function.Injective lowerPoint := by
  intro S T h
  have h₀ := congrFun h (0 : Fin 3)
  have hcoeff : Function.Injective genericCoeff :=
    (algebraMap GenericX GeometricX).injective.comp
      (IsFractionRing.injective Geom[X] GenericX)
  exact hcoeff (by simpa [lowerPoint, jet, Polynomial.hasseDeriv_zero'] using h₀)
end
end K1_13_7
end
section
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
structure LiftedCurve (f : Row 4) (P Q : Row 3) (r : PrimeSpectrum Jets) : Prop where
  component : r.asIdeal ∈ (liftIdeal f P Q).minimalPrimes
  height : r.asIdeal.height = 3
  heavy : (↑threshold : ℕ∞) ≤ liftLength r (liftIdeal f P Q)
  finite : liftLength r (liftIdeal f P Q) < ⊤
def Supported (H : Shape) (F : Jets) : Prop :=
  ∀ m ∈ F.support, m.sum (fun _ a => a) ≤ H.b ∧
    m.sum (fun i a => i.val * a) ≤ H.j ∧ m 3 ≤ H.t
abbrev constantCoeff : K →+* GeometricX := genericCoeff.comp (Polynomial.C.comp embed)
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
end
section
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
end
