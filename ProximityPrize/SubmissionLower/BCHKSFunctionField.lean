import ProximityPrize.Benchmark.TargetLower
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
open Polynomial
open Polynomial.Bivariate
namespace Univariate
section
noncomputable def discriminant {F : Type} [Field F] [Inhabited F] (f : F[X]) : F :=
  1/f.leadingCoeff * Polynomial.resultant f (Polynomial.derivative f)
theorem resultant_is_divisible_by_leadingCoeff {F : Type} [CommRing F] [Inhabited F]
    (f : F[X]) (hf : 0 < f.degree) :
    ∃ r',
      Polynomial.resultant f (Polynomial.derivative f) f.natDegree (f.natDegree - 1) =
        f.leadingCoeff * r' := by
  classical
  refine ⟨(-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr, ?_⟩
  rw [Polynomial.resultant_deriv (f := f) hf]
  simp [mul_left_comm, mul_comm]
lemma separable_iff_discr_eq_zero {F : Type} [Field F] [Inhabited F] (f : F[X]) :
    f.Separable ↔ discriminant f ≠ 0 := by
  unfold discriminant
  constructor
  · intro h
    have hne : f ≠ 0 := fun hf => by subst hf; exact not_isCoprime_zero_zero h
    exact mul_ne_zero (div_ne_zero one_ne_zero (leadingCoeff_ne_zero.mpr hne))
      (resultant_ne_zero f (derivative f) h)
  · intro h
    have hres : resultant f (derivative f) ≠ 0 := right_ne_zero_of_mul h
    exact of_not_not (fun hns => hres
      (resultant_eq_zero_iff.mpr ⟨Or.inl (fun hf => by simp [hf] at h), hns⟩))
end
end Univariate
namespace Ideal
section
def principalIdeal {F : Type} [Semiring F] (f : F) : Ideal F := Ideal.span {f}
lemma principal_is_maximal_iff_irred {F : Type} [Field F] (f : F[X]) :
    (principalIdeal f).IsMaximal ↔ Irreducible f := by
    constructor <;> intro h;
    ·
      have h_nonzero : f ≠ 0 := by
        intro hf;
        subst hf
        rw [principalIdeal] at h
        rw [Ideal.isMaximal_iff] at h
        have hmax := h.2 (Ideal.span ({Polynomial.X} : Set F[X])) Polynomial.X
        have hXmem : (Polynomial.X : F[X]) ∈ Ideal.span ({Polynomial.X} : Set F[X]) :=
          Ideal.mem_span_singleton_self _
        have hXnotmem : (Polynomial.X : F[X]) ∉ Ideal.span ({0} : Set F[X]) := by
          simp
        have htop : (1 : F[X]) ∈ Ideal.span ({Polynomial.X} : Set F[X]) := by
          apply hmax
          · simp
          · exact hXnotmem
          · exact hXmem
        exact absurd (Polynomial.X_dvd_iff.mp (by simpa [Ideal.mem_span_singleton] using htop))
          (by norm_num);
      have h_prime : Prime f := by
        rw [ ← Ideal.span_singleton_prime h_nonzero ];
        exact h.isPrime;
      exact h_prime.irreducible;
    · rw [ Ideal.isMaximal_iff ];
      constructor;
      · exact fun h' => h.not_isUnit <| isUnit_of_dvd_one <| Ideal.mem_span_singleton.mp h';
      · intro J x hJ hx hxJ
        have h_coprime : IsCoprime f x := by
          exact h.coprime_iff_not_dvd.mpr fun h' => hx <| Ideal.mem_span_singleton.mpr h';
        rcases h_coprime with ⟨ a, b, h ⟩;
        exact h.symm ▸
          J.add_mem
            (J.mul_mem_left a (hJ (Ideal.subset_span (Set.mem_singleton f))))
            (J.mul_mem_left b hxJ)
end
end Ideal
namespace ToRatFunc
noncomputable section
def univPolyHom {F : Type} [CommRing F] [IsDomain F] : F[X] →+* RatFunc F :=
  algebraMap (F[X]) (RatFunc F)
def bivPolyHom {F : Type} [CommRing F] [IsDomain F] :
    Polynomial (F[X]) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom (univPolyHom)
end
end ToRatFunc
open Polynomial Polynomial.Bivariate ToRatFunc Ideal
namespace RationalFunctions
section Monicization
variable {F : Type} [CommRing F] [IsDomain F]
noncomputable def monicizeRatFunc (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'
section FieldIrreducibility
variable {F : Type} [Field F]
lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  letI : Invertible a := invertibleOfNonzero ha
  let e : K[X] ≃ₐ[K] K[X] := Polynomial.algEquivCMulXAddC a 0
  have hp : e p = p.comp (Polynomial.C a * Polynomial.X) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← hp]
  exact MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p)
private lemma irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0)
    (hH : Irreducible H) :
    Irreducible (H.map (univPolyHom (F := F))) := by
  have hprim : H.IsPrimitive := Irreducible.isPrimitive hH hdeg
  simpa [ToRatFunc.univPolyHom] using
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F) hprim).mp hH
lemma irreducible_monicizeRatFunc_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (monicizeRatFunc H) := by
  classical
  let d : ℕ := H.natDegree
  let a : RatFunc F := univPolyHom (F := F) H.leadingCoeff
  let W : Polynomial (RatFunc F) := Polynomial.C a
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  have hlead_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hlead_ne (univPolyHom_injective (by simpa [a] using ha))
  have hmap_irreducible : Irreducible (H.map (univPolyHom (F := F))) :=
    irreducible_map_univPolyHom_of_irreducible (Nat.ne_of_gt hdeg) hH
  have hsub :
      Polynomial.X / W = Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)) := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := rfl
      _ = Polynomial.X * Polynomial.C a⁻¹ := Polynomial.div_C
      _ = Polynomial.C a⁻¹ * Polynomial.X := by rw [mul_comm]
  have hcomp_irreducible :
      Irreducible
        ((H.map (univPolyHom (F := F))).comp
          (Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)))) := by
    exact (irreducible_comp_C_mul_X_iff (a := a⁻¹) (inv_ne_zero ha_ne)
      (H.map (univPolyHom (F := F)))).mpr hmap_irreducible
  have heval :
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := univPolyHom (F := F))
        (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
        (x := Polynomial.X / W)).symm
  have heval_irreducible :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
          H) := by
    rw [heval, hsub]
    exact hcomp_irreducible
  have hunitW : IsUnit (W ^ (d - 1)) := by
    exact (isUnit_C.mpr (Ne.isUnit ha_ne)).pow (d - 1)
  rcases hunitW with ⟨u, hu⟩
  have htilde :
      monicizeRatFunc H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible
end FieldIrreducibility
lemma irreducible_monicizeRatFunc {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (monicizeRatFunc H) :=
  irreducible_monicizeRatFunc_of_natDegree_pos hHdeg
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {monicizeRatFunc H})
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducible_monicizeRatFunc_of_natDegree_pos hHdeg hH
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducible_monicizeRatFunc hHdeg h
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)
noncomputable def monicize (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i
omit [IsDomain F] in
lemma monicize_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (monicize H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [monicize, if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))
private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]
private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp
lemma map_monicize_eq_monicizeRatFunc (H : F[X][Y]) : (monicize H).map univPolyHom = monicizeRatFunc
    H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [monicize, hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, monicizeRatFunc]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [monicize, hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [monicizeRatFunc, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]
section IntegralIrreducibility
variable {F : Type} [Field F]
lemma irreducible_monicize {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (monicize H) := by
  have hmap : Irreducible ((monicize H).map (univPolyHom (F := F))) := by
    simpa [map_monicize_eq_monicizeRatFunc] using
      irreducible_monicizeRatFunc_of_natDegree_pos hHdeg hH
  exact (monicize_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap
end IntegralIrreducibility
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {monicize H})
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {monicize H})
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
    (I := Ideal.span {monicize H}) (Ideal.span {monicizeRatFunc H})
    bivPolyHom (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change bivPolyHom (monicize H) ∈ span {monicizeRatFunc H}
      rw [show bivPolyHom (monicize H) = (monicize H).map univPolyHom from rfl,
        map_monicize_eq_monicizeRatFunc]
      exact Ideal.subset_span rfl)
section FieldEmbedding
variable {F : Type} [Field F]
lemma monicize_dvd_of_map_dvd_monicizeRatFunc {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : monicizeRatFunc H ∣ p.map (univPolyHom (F := F))) :
    monicize H ∣ p := by
  let q : F[X][Y] := monicize H
  have hqmonic : q.Monic := monicize_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, map_monicize_eq_monicizeRatFunc] using hp
  have hqmap_dvd_rem :
      q.map (univPolyHom (F := F)) ∣
        (p %ₘ q).map (univPolyHom (F := F)) := by
    have hrem :
        (p %ₘ q).map (univPolyHom (F := F)) =
          p.map (univPolyHom (F := F)) -
            q.map (univPolyHom (F := F)) * (p /ₘ q).map (univPolyHom (F := F)) := by
      have h := congrArg (fun r : F[X][Y] => r.map (univPolyHom (F := F)))
        (Polynomial.modByMonic_add_div p q)
      simp only [Polynomial.map_add, Polynomial.map_mul] at h
      rw [← h]
      ring
    rw [hrem]
    exact dvd_sub hqmap_dvd_p (dvd_mul_right _ _)
  have hdegree :
      ((p %ₘ q).map (univPolyHom (F := F))).degree <
        (q.map (univPolyHom (F := F))).degree := by
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    exact Polynomial.degree_modByMonic_lt p hqmonic
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hqmap_dvd_rem hdegree
private lemma mem_span_monicize_of_bivPolyHom_mem_span_monicizeRatFunc {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {monicizeRatFunc H}) :
    p ∈ Ideal.span {monicize H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact monicize_dvd_of_map_dvd_monicizeRatFunc hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_monicize_of_bivPolyHom_mem_span_monicizeRatFunc hHdeg hp
end FieldEmbedding
def regularElementsSet (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}
@[simp]
lemma regularElementsSet_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨0, by simp⟩
@[simp]
lemma regularElementsSet_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨1, by simp⟩
lemma regularElementsSet_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a + b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩
lemma regularElementsSet_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) : -a ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩
lemma regularElementsSet_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a - b ∈ regularElementsSet H := by
  simpa [sub_eq_add_neg] using regularElementsSet_add ha (regularElementsSet_neg hb)
lemma regularElementsSet_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a * b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩
lemma regularElementsSet_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (n : ℕ) : a ^ n ∈ regularElementsSet H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElementsSet_mul ih ha
lemma regularElementsSet_sum {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∑ i ∈ s, f i) ∈ regularElementsSet H := by
  letI : DecidableEq ι := Classical.decEq ι
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact regularElementsSet_add
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))
lemma regularElementsSet_prod {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∏ i ∈ s, f i) ∈ regularElementsSet H := by
  letI : DecidableEq ι := Classical.decEq ι
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.prod_insert ha]
    exact regularElementsSet_mul
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}
noncomputable def piZLift {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) :
    F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1
noncomputable def piZ {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) :
    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {monicize H}) (piZLift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [piZLift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (monicize H) = 0 from root.2]
    ring)
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := monicize_monic H hH
  Polynomial.modByMonic β.out (monicize H)
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (monicize H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (monicize_monic H hH)
omit [IsDomain F] in
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {monicize H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {monicize H}
  let q : F[X][Y] := monicize H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {monicize H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]
omit [IsDomain F] in
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) =
      p %ₘ monicize H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (monicize_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {monicize H})
        ((Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {monicize H}) p := rfl
omit [IsDomain F] in
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (monicize H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (monicize_monic H hH)).2 hp
end Monicization
end RationalFunctions
open Polynomial Polynomial.Bivariate ToRatFunc Ideal
namespace RationalFunctions
section AlgebraicWeights
variable {F : Type} [CommRing F] [IsDomain F]
noncomputable def weight (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )
omit [IsDomain F] in
@[simp]
lemma weight_zero (H : F[X][Y]) (D : ℕ) :
    weight (0 : F[X][Y]) H D = ⊥ := by
  simp [weight]
noncomputable def regularWeight {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight (canonicalRepOf𝒪 hH f) H D
omit [IsDomain F] in
@[simp]
lemma regularWeight_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    regularWeight hH (0 : 𝒪 H) D = ⊥ := by
  simp [regularWeight]
omit [IsDomain F] in
lemma regularWeight_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D =
      weight (p %ₘ monicize H) H D := by
  simp [regularWeight, canonicalRepOf𝒪_mk]
lemma regularWeight_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (monicize H).degree) (D : ℕ) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D =
      weight p H D := by
  simp [regularWeight, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]
omit [IsDomain F] in
lemma le_weight_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn
omit [IsDomain F] in
lemma weight_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)
omit [IsDomain F] in
lemma weight_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]
omit [IsDomain F] in
lemma weight_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]
omit [IsDomain F] in
lemma weight_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  intro n hn
  have : (Polynomial.C c * Polynomial.X ^ k : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
omit [IsDomain F] in
@[simp]
lemma weight_neg (f H : F[X][Y]) (D : ℕ) : weight (-f) H D = weight f H D := by
  classical
  unfold weight
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]
omit [IsDomain F] in
lemma weight_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight (f + g) H D ≤ max (weight f H D) (weight g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  have hcoeff : (f + g).coeff n = f.coeff n + g.coeff n := Polynomial.coeff_add _ _ _
  have hsum_ne : f.coeff n + g.coeff n ≠ 0 := by
    rw [← hcoeff]
    exact Polynomial.mem_support_iff.mp hn
  by_cases hf : f.coeff n = 0
  ·
    have hg : g.coeff n ≠ 0 := by simpa [hf] using hsum_ne
    have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
    have heq : (f + g).coeff n = g.coeff n := by simp [hcoeff, hf]
    change (WithBot.some _ : WithBot ℕ) ≤ _
    rw [heq]
    exact (le_weight_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_of_mem_support hnf).trans (le_max_left _ _)
    · have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
      have hdeg : ((f + g).coeff n).natDegree ≤
          max (f.coeff n).natDegree (g.coeff n).natDegree := by
        rw [hcoeff]
        exact Polynomial.natDegree_add_le _ _
      rcases le_total (f.coeff n).natDegree (g.coeff n).natDegree with h | h
      ·
        have hbound : ((f + g).coeff n).natDegree ≤ (g.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_right h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight g H D := le_weight_of_mem_support hng
          _ ≤ max (weight f H D) (weight g H D) := le_max_right _ _
      · have hbound : ((f + g).coeff n).natDegree ≤ (f.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_left h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight f H D := le_weight_of_mem_support hnf
          _ ≤ max (weight f H D) (weight g H D) := le_max_left _ _
omit [IsDomain F] in
lemma weight_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight (f - g) H D ≤ max (weight f H D) (weight g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_add_le f (-g) H D).trans_eq (by rw [weight_neg])
omit [IsDomain F] in
lemma weight_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight (f i) H D) := by
  letI : DecidableEq ι := Classical.decEq ι
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_add_le _ _ _ _).trans (max_le_max le_rfl ih)
omit [IsDomain F] in
lemma weight_mul_le' {f g H : F[X][Y]} {D bf bg : ℕ}
    (hf : weight f H D ≤ (WithBot.some bf : WithBot ℕ))
    (hg : weight g H D ≤ (WithBot.some bg : WithBot ℕ)) :
    weight (f * g) H D ≤ (WithBot.some (bf + bg) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  rw [weight_le_iff] at hf hg
  intro n hn
  set m := D + 1 - Bivariate.natDegreeY H with hm
  have hcoeff_ne : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hexists : ∃ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hcoeff_ne (by rw [Polynomial.coeff_mul]; exact Finset.sum_eq_zero h)
  obtain ⟨x0, hx0mem, hx0ne⟩ := hexists
  have hx0sum : x0.1 + x0.2 = n := Finset.mem_antidiagonal.mp hx0mem
  have hfb0 := hf x0.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hx0ne))
  have hgb0 := hg x0.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx0ne))
  have hnm_le : n * m ≤ bf + bg := by
    have : n * m = x0.1 * m + x0.2 * m := by rw [← hx0sum, Nat.add_mul]
    omega
  have hdeg : ((f * g).coeff n).natDegree ≤ bf + bg - n * m := by
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro x hx
    have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    by_cases hxz : f.coeff x.1 * g.coeff x.2 = 0
    · simp [hxz]
    · have hfb := hf x.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hxz))
      have hgb := hg x.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hxz))
      have hprod : (f.coeff x.1 * g.coeff x.2).natDegree ≤
          (f.coeff x.1).natDegree + (g.coeff x.2).natDegree := Polynomial.natDegree_mul_le
      have hnm : n * m = x.1 * m + x.2 * m := by rw [← hxsum, Nat.add_mul]
      omega
  omega
omit [IsDomain F] in
private lemma exists_top_weight_index {f : F[X][Y]} (H : F[X][Y]) (D : ℕ) (hf : f ≠ 0) :
    ∃ N b : ℕ, weight f H D = (WithBot.some b : WithBot ℕ) ∧ f.coeff N ≠ 0 ∧
      N * (D + 1 - Bivariate.natDegreeY H) + (f.coeff N).natDegree = b ∧
      ∀ m, f.coeff m ≠ 0 → N < m →
        m * (D + 1 - Bivariate.natDegreeY H) + (f.coeff m).natDegree < b := by
  classical
  set u := D + 1 - Bivariate.natDegreeY H with hu
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨n₀, hn₀mem, hn₀⟩ := Finset.exists_mem_eq_sup f.support hne
    (fun d => (WithBot.some (d * u + (f.coeff d).natDegree) : WithBot ℕ))
  set b := n₀ * u + (f.coeff n₀).natDegree with hb
  have hw : weight f H D = (WithBot.some b : WithBot ℕ) := hn₀
  have hall : ∀ m ∈ f.support, m * u + (f.coeff m).natDegree ≤ b :=
    weight_le_iff.mp (le_of_eq hw)
  set S := f.support.filter (fun m => m * u + (f.coeff m).natDegree = b) with hS
  have hSne : S.Nonempty := ⟨n₀, Finset.mem_filter.mpr ⟨hn₀mem, rfl⟩⟩
  refine ⟨S.max' hSne, b, hw, ?_, ?_, ?_⟩
  · exact Polynomial.mem_support_iff.mp (Finset.mem_filter.mp (S.max'_mem hSne)).1
  · exact (Finset.mem_filter.mp (S.max'_mem hSne)).2
  · intro m hm hlt
    have hmem : m ∈ f.support := Polynomial.mem_support_iff.mpr hm
    have hle := hall m hmem
    rcases Nat.lt_or_ge (m * u + (f.coeff m).natDegree) b with h | h
    · exact h
    · exact absurd (S.le_max' m (Finset.mem_filter.mpr ⟨hmem, by omega⟩)) (by omega)
theorem weight_mul (f g H : F[X][Y]) (D : ℕ) :
    weight (f * g) H D = weight f H D + weight g H D := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨Nf, bf, hwf, hfNe, hfEq, hfMax⟩ := exists_top_weight_index H D hf
  obtain ⟨Ng, bg, hwg, hgNe, hgEq, hgMax⟩ := exists_top_weight_index H D hg
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = D + 1 - Bivariate.natDegreeY H := ⟨_, rfl⟩
  simp only [← hu] at hfEq hfMax hgEq hgMax
  rw [hwf, hwg, ← WithBot.coe_add]
  refine le_antisymm (weight_mul_le' (le_of_eq hwf) (le_of_eq hwg)) ?_
  have hallf : ∀ m ∈ f.support, m * u + (f.coeff m).natDegree ≤ bf := by
    simpa only [← hu] using weight_le_iff.mp (le_of_eq hwf)
  have hallg : ∀ m ∈ g.support, m * u + (g.coeff m).natDegree ≤ bg := by
    simpa only [← hu] using weight_le_iff.mp (le_of_eq hwg)
  set df := (f.coeff Nf).natDegree with hdf
  set dg := (g.coeff Ng).natDegree with hdg
  have hAne : f.coeff Nf * g.coeff Ng ≠ 0 := mul_ne_zero hfNe hgNe
  have hAdeg : (f.coeff Nf * g.coeff Ng).degree = ((df + dg : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hAne, Polynomial.natDegree_mul hfNe hgNe]
  have hrest : ∀ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      (f.coeff x.1 * g.coeff x.2).degree < ((df + dg : ℕ) : WithBot ℕ) := by
    intro x hx
    obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.mp hx
    have hxsum : x.1 + x.2 = Nf + Ng := Finset.mem_antidiagonal.mp hxmem
    by_cases hz : f.coeff x.1 * g.coeff x.2 = 0
    · rw [hz, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hfx : f.coeff x.1 ≠ 0 := left_ne_zero_of_mul hz
      have hgx : g.coeff x.2 ≠ 0 := right_ne_zero_of_mul hz
      have hmul : x.1 * u + x.2 * u = Nf * u + Ng * u := by
        rw [← Nat.add_mul, ← Nat.add_mul, hxsum]
      have hstrict : (f.coeff x.1).natDegree + (g.coeff x.2).natDegree < df + dg := by
        rcases Nat.lt_trichotomy x.1 Nf with h1 | h1 | h1
        · have h2 : Ng < x.2 := by omega
          have hgs := hgMax x.2 hgx h2
          have hfl := hallf x.1 (Polynomial.mem_support_iff.mpr hfx)
          omega
        · exact absurd (Prod.ext h1 (by omega)) hxne
        · have hfs := hfMax x.1 hfx h1
          have hgl := hallg x.2 (Polynomial.mem_support_iff.mpr hgx)
          omega
      rw [Polynomial.degree_eq_natDegree hz, Polynomial.natDegree_mul hfx hgx]
      exact_mod_cast hstrict
  have hsplit : (f * g).coeff (Nf + Ng) =
      f.coeff Nf * g.coeff Ng +
        ∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng), f.coeff x.1 * g.coeff x.2 := by
    have hpair : (Nf, Ng) ∈ Finset.antidiagonal (Nf + Ng) :=
      Finset.mem_antidiagonal.mpr rfl
    rw [Polynomial.coeff_mul, ← Finset.add_sum_erase _ _ hpair]
  have hBdeg : (∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      f.coeff x.1 * g.coeff x.2).degree < ((df + dg : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hrest)
  have hlt : (∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      f.coeff x.1 * g.coeff x.2).degree < (f.coeff Nf * g.coeff Ng).degree := by
    rw [hAdeg]; exact hBdeg
  have hcoeff_deg : ((f * g).coeff (Nf + Ng)).degree = ((df + dg : ℕ) : WithBot ℕ) := by
    rw [hsplit, Polynomial.degree_add_eq_left_of_degree_lt hlt, hAdeg]
  have hcoeff_ne : (f * g).coeff (Nf + Ng) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.degree_zero] at hcoeff_deg
    exact WithBot.bot_ne_coe hcoeff_deg
  have hnd : ((f * g).coeff (Nf + Ng)).natDegree = df + dg :=
    Polynomial.natDegree_eq_of_degree_eq_some hcoeff_deg
  have hbound := le_weight_of_mem_support (f := f * g) (H := H) (D := D)
    (Polynomial.mem_support_iff.mpr hcoeff_ne)
  simp only [hnd, ← hu] at hbound
  have harith : (Nf + Ng) * u + (df + dg) = bf + bg := by
    have hd : (Nf + Ng) * u = Nf * u + Ng * u := Nat.add_mul _ _ _
    omega
  rwa [harith] at hbound
omit [IsDomain F] in
lemma natDegree_coeff_le_of_totalDegree_le (f : F[X][Y]) {D : ℕ}
    (hD : Bivariate.totalDegree f ≤ D) (i : ℕ) :
    (f.coeff i).natDegree ≤ D - i := by
  classical
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hi_in : i ∈ f.support := Polynomial.mem_support_iff.mpr hi
    have h1 : (f.coeff i).natDegree + i ≤ Bivariate.totalDegree f :=
      Bivariate.coeff_totalDegree_le f hi_in
    omega
omit [IsDomain F] in
lemma weight_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  rw [weight_le_iff] at hf
  intro n hn
  have hcoeff_ne : (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeff_eq :
      (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n =
        (if k ≤ n then c * f.coeff (n - k) else 0) := by
    rw [show (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]) =
           Polynomial.C c * (f * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  by_cases hkn : k ≤ n
  · rw [hcoeff_eq, if_pos hkn] at hcoeff_ne
    have hf_ne : f.coeff (n - k) ≠ 0 := by
      intro h0
      apply hcoeff_ne
      rw [h0, mul_zero]
    have hn_k_in : n - k ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
    have hf_bound := hf (n - k) hn_k_in
    rw [hcoeff_eq, if_pos hkn]
    have hdeg : (c * f.coeff (n - k)).natDegree ≤ c.natDegree + (f.coeff (n - k)).natDegree :=
      Polynomial.natDegree_mul_le
    have hsplit : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hgoal :
        n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
          k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b := by
      have h1 :
          n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) :=
        Nat.add_le_add_left hdeg _
      have h2 :
          n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) =
            k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree +
              ((n - k) * (D + 1 - Bivariate.natDegreeY H) +
                (f.coeff (n - k)).natDegree) := by
        have hnk : k + (n - k) = n := Nat.add_sub_cancel' hkn
        conv_lhs => rw [hsplit, Nat.add_mul]
        rw [show k + (n - k) - k = n - k from by omega]
        ring
      rw [h2] at h1
      exact h1.trans (Nat.add_le_add_left hf_bound _)
    exact hgoal
  · rw [hcoeff_eq, if_neg hkn] at hcoeff_ne
    exact (hcoeff_ne rfl).elim
lemma natDegree_monicize {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (monicize H).natDegree = H.natDegree := by
  classical
  rw [monicize, if_neg (Nat.ne_of_gt hH)]
  have hsum_deg :
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]).degree < (H.natDegree : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr <| by
        intro i hi
        exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  rw [show (Polynomial.X ^ H.natDegree +
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]) =
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i) + Polynomial.X ^ H.natDegree by ring]
  have hX_deg : (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_right_of_degree_lt (hsum_deg.trans_eq hX_deg.symm), hX_deg]
lemma canonicalRepOf𝒪_natDegree_lt_H {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree < H.natDegree := by
  classical
  by_cases hβ : canonicalRepOf𝒪 hH β = 0
  · simp [hβ, hH]
  · have hdeg := canonicalRepOf𝒪_degree_lt hH β
    have hq_ne : monicize H ≠ 0 := (monicize_monic H hH).ne_zero
    rw [Polynomial.degree_eq_natDegree hβ, Polynomial.degree_eq_natDegree hq_ne] at hdeg
    exact_mod_cast (by simpa [natDegree_monicize hH] using hdeg)
omit [IsDomain F] in
lemma weight_monicize_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight (monicize H) H D ≤
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hd_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  rw [monicize, if_neg (Nat.ne_of_gt hH)]
  refine (weight_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  ·
    refine (weight_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  ·
    refine (weight_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_C_mul_X_pow_le H D _ _).trans ?_
    rw [WithBot.coe_le_coe]
    rw [hbY]
    have hcoeff_natDeg :
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) := by
      have h1 :
          (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 :
          (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree :=
        Polynomial.natDegree_pow_le
      have hi_deg : (H.coeff i).natDegree ≤ D - i :=
        natDegree_coeff_le_of_totalDegree_le H hD i
      have hd_deg : (H.coeff H.natDegree).natDegree ≤ D - H.natDegree :=
        natDegree_coeff_le_of_totalDegree_le H hD H.natDegree
      calc (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree
          ≤ (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree := h1
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree := by
            exact Nat.add_le_add hi_deg h2
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hd_deg) _
    have hadd : i * (D + 1 - H.natDegree) +
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          i * (D + 1 - H.natDegree) +
            ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) :=
      Nat.add_le_add_left hcoeff_natDeg _
    refine hadd.trans ?_
    have hkey : i * (D + 1 - H.natDegree) +
        ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) =
        H.natDegree * (D + 1 - H.natDegree) := by
      have hi_le : i ≤ H.natDegree - 1 := by omega
      have hi_le_D : i ≤ D := by omega
      have hd_le_D1 : H.natDegree ≤ 1 + D := by omega
      have hd_le_D' : H.natDegree ≤ D + 1 := by omega
      zify [hd_le_D, hd_le_D', hi_le, hi_le_D, hH]
      ring
    omega
omit [IsDomain F] in
lemma weight_sub_leadingCoeff_mul_monicize_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * monicize H) H D ≤
      weight p H D := by
  classical
  refine (weight_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_C_mul_X_pow_mul_le (weight_monicize_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_of_mem_support hp_in)
    rw [WithBot.coe_le_coe]
    change (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
        (p.coeff p.natDegree).natDegree + H.natDegree * (D + 1 - Bivariate.natDegreeY H) ≤
        p.natDegree * (D + 1 - Bivariate.natDegreeY H) + (p.coeff p.natDegree).natDegree
    have hsum : (p.natDegree - H.natDegree) + H.natDegree = p.natDegree := by omega
    have hadd_mul :
        (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
            H.natDegree * (D + 1 - Bivariate.natDegreeY H) =
          p.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
      rw [← Nat.add_mul, hsum]
    linarith [hadd_mul]
lemma weight_modByMonic_monicize_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight (p %ₘ monicize H) H D ≤ weight p H D
  | p => by
      classical
      have hq : (monicize H).Monic := monicize_monic H hH
      unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      rw [dif_pos hq]
      by_cases h : (monicize H).degree ≤ p.degree ∧ p ≠ 0
      · have _wf := Polynomial.div_wf_lemma h hq
        simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        let z := Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - (monicize H).natDegree)
        have ih := weight_modByMonic_monicize_le hD hH (p - monicize H * z)
        have ih' :
            weight ((Polynomial.divModByMonicAux (p - monicize H * z) hq).2) H D ≤
              weight (p - monicize H * z) H D := by
          simpa [Polynomial.modByMonic, hq, z] using ih
        have hqnat : (monicize H).natDegree = H.natDegree := natDegree_monicize hH
        have hp_deg : H.natDegree ≤ p.natDegree := by
          have hdeg := h.1
          rw [Polynomial.degree_eq_natDegree h.2, Polynomial.degree_eq_natDegree hq.ne_zero]
            at hdeg
          exact_mod_cast (by simpa [hqnat] using hdeg)
        have hstep0 :=
          weight_sub_leadingCoeff_mul_monicize_le (p := p) (H := H) hD hH hp_deg
        have hstep : weight (p - monicize H * z) H D ≤ weight p H D := by
          have hz :
              z = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - H.natDegree) := by
            simp [z, hqnat]
          rw [hz]
          convert hstep0 using 1
          ring_nf
        exact ih'.trans hstep
      · simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        exact le_rfl
termination_by p => p
lemma regularWeight_mk_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (p : F[X][Y]) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D ≤
      weight p H D := by
  rw [regularWeight_mk]
  exact weight_modByMonic_monicize_le hD hH p
lemma weight_monicize {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight (monicize H) H D =
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  refine le_antisymm (weight_monicize_le hD hH) ?_
  have hmonic : (monicize H).Monic := monicize_monic H hH
  have hdeg : (monicize H).natDegree = H.natDegree := natDegree_monicize hH
  have hlead : (monicize H).coeff H.natDegree = 1 := by
    rw [← hdeg]; exact hmonic.coeff_natDegree
  have hmem : H.natDegree ∈ (monicize H).support :=
    Polynomial.mem_support_iff.mpr (by rw [hlead]; exact one_ne_zero)
  have h := le_weight_of_mem_support (f := monicize H) (H := H) (D := D) hmem
  rwa [hlead, Polynomial.natDegree_one, Nat.add_zero] at h
lemma regularWeight_le_of_mk_eq {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {α : 𝒪 H} {p : F[X][Y]}
    (hp : (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = α) :
    regularWeight hH α D ≤ weight p H D := by
  subst hp
  exact regularWeight_mk_le hD hH p
noncomputable def rationalVanishingSet {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (monicize H) z, (piZ z root) β = 0}
omit [IsDomain F] in
lemma piZ_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (monicize H) z) (β : 𝒪 H) :
    (piZ z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl
end AlgebraicWeights
end RationalFunctions
