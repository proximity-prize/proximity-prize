import ProximityPrize.SubmissionLower.BCHKSFrobeniusPencilMinors6400

/-!
# From a defect-aware scroll to a Frobenius amplitude atom

The scroll numerator pair is pulled back through a coefficient automorphism,
then divided by its polynomial gcd.  The roots of that gcd are removed from
the valid source set; the degree drop exactly pays for this additional loss.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A polynomial pair divided by its gcd, with the exact compensated degree
bounds retained. -/
structure NormalizedPolynomialPair
    (A B : F[X]) (h loss : ℕ) where
  common : F[X]
  first : F[X]
  second : F[X]
  common_ne_zero : common ≠ 0
  first_factor : common * first = A
  second_factor : common * second = B
  coprime : IsCoprime first second
  first_degree : first.natDegree + common.natDegree + loss < h
  second_degree : second.natDegree + common.natDegree + loss < h

/-- Divide a nonzero polynomial pair by its gcd without losing its strict
degree-plus-loss budget. -/
noncomputable def normalizePolynomialPair
    [DecidableEq F]
    (A B : F[X]) (h loss : ℕ)
    (hnontrivial : ¬(A = 0 ∧ B = 0))
    (hAdegree : A.natDegree + loss < h)
    (hBdegree : B.natDegree + loss < h) :
    NormalizedPolynomialPair A B h loss := by
  let G : F[X] := gcd A B
  let C₀ : F[X] := A / G
  let C₁ : F[X] := B / G
  have hGne : G ≠ 0 := by
    intro hGzero
    exact hnontrivial ((gcd_eq_zero_iff A B).mp hGzero)
  have hGdvdA : G ∣ A := GCDMonoid.gcd_dvd_left A B
  have hGdvdB : G ∣ B := GCDMonoid.gcd_dvd_right A B
  have hAfactor : G * C₀ = A :=
    EuclideanDomain.mul_div_cancel' hGne hGdvdA
  have hBfactor : G * C₁ = B :=
    EuclideanDomain.mul_div_cancel' hGne hGdvdB
  have hcoprime : IsCoprime C₀ C₁ :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hGne
  have hC₀degree : C₀.natDegree + G.natDegree + loss < h := by
    by_cases hAne : A ≠ 0
    · have hC₀ne : C₀ ≠ 0 := left_div_gcd_ne_zero hAne
      have hdegree : G.natDegree + C₀.natDegree = A.natDegree := by
        calc
          G.natDegree + C₀.natDegree = (G * C₀).natDegree :=
            (Polynomial.natDegree_mul hGne hC₀ne).symm
          _ = A.natDegree := congrArg Polynomial.natDegree hAfactor
      omega
    · have hAzero : A = 0 := not_ne_iff.mp hAne
      have hBne : B ≠ 0 := by
        intro hBzero
        exact hnontrivial ⟨hAzero, hBzero⟩
      have hGdegree : G.natDegree ≤ B.natDegree :=
        Polynomial.natDegree_le_of_dvd hGdvdB hBne
      dsimp only [C₀]
      simp only [hAzero, EuclideanDomain.zero_div,
        Polynomial.natDegree_zero, zero_add]
      omega
  have hC₁degree : C₁.natDegree + G.natDegree + loss < h := by
    by_cases hBne : B ≠ 0
    · have hC₁ne : C₁ ≠ 0 := right_div_gcd_ne_zero hBne
      have hdegree : G.natDegree + C₁.natDegree = B.natDegree := by
        calc
          G.natDegree + C₁.natDegree = (G * C₁).natDegree :=
            (Polynomial.natDegree_mul hGne hC₁ne).symm
          _ = B.natDegree := congrArg Polynomial.natDegree hBfactor
      omega
    · have hBzero : B = 0 := not_ne_iff.mp hBne
      have hAne : A ≠ 0 := by
        intro hAzero
        exact hnontrivial ⟨hAzero, hBzero⟩
      have hGdegree : G.natDegree ≤ A.natDegree :=
        Polynomial.natDegree_le_of_dvd hGdvdA hAne
      dsimp only [C₁]
      simp only [hBzero, EuclideanDomain.zero_div,
        Polynomial.natDegree_zero, zero_add]
      omega
  exact
    { common := G
      first := C₀
      second := C₁
      common_ne_zero := hGne
      first_factor := hAfactor
      second_factor := hBfactor
      coprime := hcoprime
      first_degree := hC₀degree
      second_degree := hC₁degree }

/-- Filtering out the roots of a nonzero polynomial loses at most its degree. -/
theorem card_le_filter_eval_ne_zero_add_natDegree
    [DecidableEq F] (T : Finset F) (P : F[X]) (hP : P ≠ 0) :
    T.card ≤ (T.filter (fun x ↦ P.eval x ≠ 0)).card + P.natDegree := by
  have hbad :
      (T.filter (fun x ↦ P.eval x = 0)).card ≤ P.natDegree := by
    have hsubset : T.filter (fun x ↦ P.eval x = 0) ⊆ P.roots.toFinset := by
      intro x hx
      have hxzero := (Finset.mem_filter.mp hx).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hxzero
    calc
      (T.filter (fun x ↦ P.eval x = 0)).card ≤ P.roots.toFinset.card :=
        Finset.card_le_card hsubset
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun x ↦ P.eval x ≠ 0) (s := T)
  have hbad' :
      (T.filter (fun x ↦ ¬P.eval x ≠ 0)).card ≤ P.natDegree := by
    simpa only [not_ne_iff] using hbad
  omega

/-- Mapping coefficients through an automorphism and then its inverse returns
the original polynomial. -/
theorem polynomial_map_symm_map (sigma : F ≃+* F) (P : F[X]) :
    (P.map sigma.symm.toRingHom).map sigma.toRingHom = P := by
  ext n
  simp

/-- At a fixed evaluation point, mapping coefficients through an automorphism
commutes with evaluation in the expected way. -/
theorem polynomial_map_eval_of_fixed
    (sigma : F ≃+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    (P.map sigma.toRingHom).eval x = sigma (P.eval x) := by
  have h := Polynomial.eval_map_apply (p := P) sigma.toRingHom x
  have hx' : sigma.toRingHom x = x := hx
  calc
    (P.map sigma.toRingHom).eval x = sigma.toRingHom (P.eval x) := by
      simpa only [hx'] using h
    _ = sigma (P.eval x) := rfl

/-- Pulling coefficients back through `sigma` makes evaluation a preimage of
the original evaluation at every fixed point. -/
theorem polynomial_symm_map_eval_of_fixed
    (sigma : F ≃+* F) (P : F[X]) (x : F) (hx : sigma x = x) :
    sigma ((P.map sigma.symm.toRingHom).eval x) = P.eval x := by
  calc
    sigma ((P.map sigma.symm.toRingHom).eval x) =
        ((P.map sigma.symm.toRingHom).map sigma.toRingHom).eval (sigma x) :=
      (Polynomial.eval_map_apply
        (p := P.map sigma.symm.toRingHom) sigma.toRingHom x).symm
    _ = P.eval x := by rw [polynomial_map_symm_map, hx]

/-- A direct error pair and a common pointwise amplitude, together with the
adjusted Frobenius relation used by the cofactor finish. -/
structure FrobeniusAmplitudeAtom
    (S : Finset F) (error₀ error₁ : F → F)
    (sigma : F ≃+* F) (z : F) (h : ℕ) where
  direct₀ : F[X]
  direct₁ : F[X]
  common : F[X]
  denominator : F[X]
  amplitudeMultiplier : F[X]
  amplitude : F → F
  baseLoss : ℕ
  gcdLoss : ℕ
  valid : Finset F
  common_ne_zero : common ≠ 0
  denominator_ne_zero : denominator ≠ 0
  amplitudeMultiplier_ne_zero : amplitudeMultiplier ≠ 0
  direct_coprime : IsCoprime direct₀ direct₁
  direct₀_degree : direct₀.natDegree + gcdLoss + baseLoss < h
  direct₁_degree : direct₁.natDegree + gcdLoss + baseLoss < h
  denominator_degree : denominator.natDegree + baseLoss < h
  amplitudeMultiplier_degree : amplitudeMultiplier.natDegree + baseLoss < h
  valid_subset : valid ⊆ S
  coverage : S.card ≤ valid.card + (baseLoss + gcdLoss)
  decomposition₀ : ∀ x ∈ valid,
    error₀ x = direct₀.eval x * amplitude x
  decomposition₁ : ∀ x ∈ valid,
    error₁ x = direct₁.eval x * amplitude x
  amplitude_relation : ∀ x ∈ valid,
    denominator.eval x * sigma (amplitude x) =
      amplitudeMultiplier.eval x * amplitude x

variable {S : Finset F} {error₀ error₁ : F → F}
  {sigma : F ≃+* F} {z : F} {h : ℕ}

/-- The direct numerator and the amplitude multiplier stay below the `2*h`
root-count budget, including every point removed by both normalization
steps. -/
theorem FrobeniusAmplitudeAtom.direct₀_amplitude_degree
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.direct₀.natDegree + atom.amplitudeMultiplier.natDegree +
      (atom.baseLoss + atom.gcdLoss) < 2 * h := by
  have hdirect := atom.direct₀_degree
  have hamplitude := atom.amplitudeMultiplier_degree
  omega

theorem FrobeniusAmplitudeAtom.direct₁_amplitude_degree
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.direct₁.natDegree + atom.amplitudeMultiplier.natDegree +
      (atom.baseLoss + atom.gcdLoss) < 2 * h := by
  have hdirect := atom.direct₁_degree
  have hamplitude := atom.amplitudeMultiplier_degree
  omega

/-- The same compensated `2*h` budget holds when the direct numerator is
paired with the scroll denominator. -/
theorem FrobeniusAmplitudeAtom.direct₀_denominator_degree
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.direct₀.natDegree + atom.denominator.natDegree +
      (atom.baseLoss + atom.gcdLoss) < 2 * h := by
  have hdirect := atom.direct₀_degree
  have hdenominator := atom.denominator_degree
  omega

theorem FrobeniusAmplitudeAtom.direct₁_denominator_degree
    (atom : FrobeniusAmplitudeAtom S error₀ error₁ sigma z h) :
    atom.direct₁.natDegree + atom.denominator.natDegree +
      (atom.baseLoss + atom.gcdLoss) < 2 * h := by
  have hdirect := atom.direct₁_degree
  have hdenominator := atom.denominator_degree
  omega

/-- Convert a defect-aware rational scroll into a normalized Frobenius
amplitude atom.

The source is assumed nonzero and equal to `error₀ + z*error₁`; the two
scroll targets are the `sigma` images of those errors.  Source coordinates
are fixed by `sigma`, as they are for the base-field domain in the production
sextic extension.  No fixed-point assumption on `z` is needed. -/
noncomputable def frobeniusAmplitudeAtom_of_scroll
    [DecidableEq F]
    (S : Finset F) (source target₀ target₁ error₀ error₁ : F → F)
    (sigma : F ≃+* F) (z : F) (h : ℕ)
    (atom : DefectAwareScrollAtom S source target₀ target₁ h)
    (hcard : h ≤ S.card)
    (hsource : ∀ x ∈ S, source x ≠ 0)
    (hsource_eq : ∀ x ∈ S,
      source x = error₀ x + z * error₁ x)
    (htarget₀ : ∀ x ∈ S, target₀ x = sigma (error₀ x))
    (htarget₁ : ∀ x ∈ S, target₁ x = sigma (error₁ x))
    (hfixed : ∀ x ∈ S, sigma x = x) :
    FrobeniusAmplitudeAtom S error₀ error₁ sigma z h := by
  let B₀ : F[X] := atom.numerator₀.map sigma.symm.toRingHom
  let B₁ : F[X] := atom.numerator₁.map sigma.symm.toRingHom
  have hnumNontrivial : ¬(atom.numerator₀ = 0 ∧ atom.numerator₁ = 0) := by
    intro hzero
    have hroot : ∀ x ∈ atom.valid, atom.denominator.eval x = 0 := by
      intro x hx
      have hxS := atom.valid_subset hx
      have hs := hsource x hxS
      have herr : error₀ x ≠ 0 ∨ error₁ x ≠ 0 := by
        by_contra herrzero
        push Not at herrzero
        rw [hsource_eq x hxS, herrzero.1, herrzero.2,
          zero_add, mul_zero] at hs
        exact hs rfl
      rcases herr with he₀ | he₁
      · have ht₀ : target₀ x ≠ 0 := by
          rw [htarget₀ x hxS]
          intro hz
          apply he₀
          apply sigma.injective
          simpa using hz
        have hrel := atom.interpolation₀ x hx
        rw [hzero.1, Polynomial.eval_zero, zero_mul] at hrel
        exact (mul_eq_zero.mp hrel.symm).resolve_right ht₀
      · have ht₁ : target₁ x ≠ 0 := by
          rw [htarget₁ x hxS]
          intro hz
          apply he₁
          apply sigma.injective
          simpa using hz
        have hrel := atom.interpolation₁ x hx
        rw [hzero.2, Polynomial.eval_zero, zero_mul] at hrel
        exact (mul_eq_zero.mp hrel.symm).resolve_right ht₁
    have hdegree : atom.denominator.natDegree < atom.valid.card := by
      have hcoverage := atom.coverage
      have hden := atom.denominator_degree
      omega
    have hdenzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      atom.denominator atom.valid hroot hdegree
    exact atom.denominator_ne_zero hdenzero
  have hBnontrivial : ¬(B₀ = 0 ∧ B₁ = 0) := by
    intro hzero
    apply hnumNontrivial
    constructor
    · have hBzero : atom.numerator₀.map sigma.symm.toRingHom = 0 := by
        simpa only [B₀] using hzero.1
      calc
        atom.numerator₀ =
            (atom.numerator₀.map sigma.symm.toRingHom).map
              sigma.toRingHom :=
          (polynomial_map_symm_map sigma atom.numerator₀).symm
        _ = 0 := by rw [hBzero, Polynomial.map_zero]
    · have hBzero : atom.numerator₁.map sigma.symm.toRingHom = 0 := by
        simpa only [B₁] using hzero.2
      calc
        atom.numerator₁ =
            (atom.numerator₁.map sigma.symm.toRingHom).map
              sigma.toRingHom :=
          (polynomial_map_symm_map sigma atom.numerator₁).symm
        _ = 0 := by rw [hBzero, Polynomial.map_zero]
  have hB₀degree : B₀.natDegree + atom.loss < h := by
    dsimp only [B₀]
    rw [Polynomial.natDegree_map_eq_of_injective sigma.symm.injective]
    exact atom.numerator₀_degree
  have hB₁degree : B₁.natDegree + atom.loss < h := by
    dsimp only [B₁]
    rw [Polynomial.natDegree_map_eq_of_injective sigma.symm.injective]
    exact atom.numerator₁_degree
  let pair := normalizePolynomialPair B₀ B₁ h atom.loss
    hBnontrivial hB₀degree hB₁degree
  let T : Finset F := atom.valid.filter (fun x ↦ pair.common.eval x ≠ 0)
  let U : F[X] := Classical.choose pair.coprime
  let V : F[X] := Classical.choose (Classical.choose_spec pair.coprime)
  have hbezout : U * pair.first + V * pair.second = 1 :=
    Classical.choose_spec (Classical.choose_spec pair.coprime)
  let H : F → F := fun x ↦
    U.eval x * error₀ x + V.eval x * error₁ x
  let C : F[X] := pair.first + Polynomial.C z * pair.second
  let Aamp : F[X] := pair.common.map sigma.toRingHom * C
  have hTsubset : T ⊆ S := by
    intro x hx
    exact atom.valid_subset (Finset.mem_filter.mp hx).1
  have hcoverage :
      S.card ≤ T.card + (atom.loss + pair.common.natDegree) := by
    have hfilter := card_le_filter_eval_ne_zero_add_natDegree
      atom.valid pair.common pair.common_ne_zero
    have hfilter' :
        atom.valid.card ≤ T.card + pair.common.natDegree := by
      simpa only [T] using hfilter
    have hatom := atom.coverage
    omega
  have hCdegree :
      C.natDegree ≤ max pair.first.natDegree pair.second.natDegree := by
    dsimp only [C]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le_max le_rfl
        (Polynomial.natDegree_C_mul_le z pair.second))
  have hAampdegree : Aamp.natDegree + atom.loss < h := by
    have hmapDegree :
        (pair.common.map sigma.toRingHom).natDegree = pair.common.natDegree :=
      Polynomial.natDegree_map_eq_of_injective sigma.injective pair.common
    have hmul := Polynomial.natDegree_mul_le
      (p := pair.common.map sigma.toRingHom) (q := C)
    dsimp only [Aamp]
    rw [hmapDegree] at hmul
    have hfirst := pair.first_degree
    have hsecond := pair.second_degree
    omega
  have hcross (x : F) (hx : x ∈ T) :
      pair.first.eval x * error₁ x =
        pair.second.eval x * error₀ x := by
    have hxAtom := (Finset.mem_filter.mp hx).1
    have hxG := (Finset.mem_filter.mp hx).2
    have hxS := atom.valid_subset hxAtom
    have hN₀eval : atom.numerator₀.eval x = sigma (B₀.eval x) := by
      exact (polynomial_symm_map_eval_of_fixed sigma atom.numerator₀ x
        (hfixed x hxS)).symm
    have hN₁eval : atom.numerator₁.eval x = sigma (B₁.eval x) := by
      exact (polynomial_symm_map_eval_of_fixed sigma atom.numerator₁ x
        (hfixed x hxS)).symm
    have hrel₀ := atom.interpolation₀ x hxAtom
    have hrel₁ := atom.interpolation₁ x hxAtom
    rw [hN₀eval, htarget₀ x hxS] at hrel₀
    rw [hN₁eval, htarget₁ x hxS] at hrel₁
    have hsigmaCross :
        sigma (B₀.eval x) * sigma (error₁ x) =
          sigma (B₁.eval x) * sigma (error₀ x) := by
      apply mul_right_cancel₀ (hsource x hxS)
      calc
        (sigma (B₀.eval x) * sigma (error₁ x)) * source x =
            (sigma (B₀.eval x) * source x) * sigma (error₁ x) := by ring
        _ = (atom.denominator.eval x * sigma (error₀ x)) *
            sigma (error₁ x) := by rw [hrel₀]
        _ = (atom.denominator.eval x * sigma (error₁ x)) *
            sigma (error₀ x) := by ring
        _ = (sigma (B₁.eval x) * source x) * sigma (error₀ x) := by
          rw [hrel₁]
        _ = (sigma (B₁.eval x) * sigma (error₀ x)) * source x := by ring
    have hBcross : B₀.eval x * error₁ x =
        B₁.eval x * error₀ x := by
      apply sigma.injective
      simpa only [map_mul] using hsigmaCross
    have hfactor₀ : B₀.eval x =
        pair.common.eval x * pair.first.eval x := by
      have hf := congrArg (fun P : F[X] ↦ P.eval x) pair.first_factor
      simpa only [Polynomial.eval_mul] using hf.symm
    have hfactor₁ : B₁.eval x =
        pair.common.eval x * pair.second.eval x := by
      have hf := congrArg (fun P : F[X] ↦ P.eval x) pair.second_factor
      simpa only [Polynomial.eval_mul] using hf.symm
    have hfactored : pair.common.eval x *
        (pair.first.eval x * error₁ x -
          pair.second.eval x * error₀ x) = 0 := by
      calc
        pair.common.eval x *
            (pair.first.eval x * error₁ x -
              pair.second.eval x * error₀ x) =
          (pair.common.eval x * pair.first.eval x) * error₁ x -
            (pair.common.eval x * pair.second.eval x) * error₀ x := by ring
        _ = B₀.eval x * error₁ x - B₁.eval x * error₀ x := by
          rw [← hfactor₀, ← hfactor₁]
        _ = 0 := sub_eq_zero.mpr hBcross
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactored).resolve_left hxG)
  have hbezoutEval (x : F) :
      U.eval x * pair.first.eval x + V.eval x * pair.second.eval x = 1 := by
    have h := congrArg (fun P : F[X] ↦ P.eval x) hbezout
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one] using h
  have hdecomp₀ (x : F) (hx : x ∈ T) :
      error₀ x = pair.first.eval x * H x := by
    have hcr := hcross x hx
    have hb := hbezoutEval x
    dsimp only [H]
    calc
      error₀ x = 1 * error₀ x := by ring
      _ = (U.eval x * pair.first.eval x +
          V.eval x * pair.second.eval x) * error₀ x := by rw [hb]
      _ = U.eval x * pair.first.eval x * error₀ x +
          V.eval x * pair.second.eval x * error₀ x := by ring
      _ = U.eval x * pair.first.eval x * error₀ x +
          V.eval x * pair.first.eval x * error₁ x := by
        linear_combination -V.eval x * hcr
      _ = pair.first.eval x *
          (U.eval x * error₀ x + V.eval x * error₁ x) := by ring
  have hdecomp₁ (x : F) (hx : x ∈ T) :
      error₁ x = pair.second.eval x * H x := by
    have hcr := hcross x hx
    have hb := hbezoutEval x
    dsimp only [H]
    calc
      error₁ x = 1 * error₁ x := by ring
      _ = (U.eval x * pair.first.eval x +
          V.eval x * pair.second.eval x) * error₁ x := by rw [hb]
      _ = U.eval x * pair.first.eval x * error₁ x +
          V.eval x * pair.second.eval x * error₁ x := by ring
      _ = U.eval x * pair.second.eval x * error₀ x +
          V.eval x * pair.second.eval x * error₁ x := by
        linear_combination U.eval x * hcr
      _ = pair.second.eval x *
          (U.eval x * error₀ x + V.eval x * error₁ x) := by ring
  have hsourceC (x : F) (hx : x ∈ T) :
      source x = C.eval x * H x := by
    have hxAtom := (Finset.mem_filter.mp hx).1
    have hxS := atom.valid_subset hxAtom
    have hCeval : C.eval x = pair.first.eval x + z * pair.second.eval x := by
      simp only [C, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C]
    rw [hsource_eq x hxS, hdecomp₀ x hx, hdecomp₁ x hx, hCeval]
    ring
  have hTnonempty : T.Nonempty := by
    rw [← Finset.card_pos]
    have hpair := pair.first_degree
    have hS := hcard
    omega
  have hCne : C ≠ 0 := by
    intro hCzero
    obtain ⟨x, hx⟩ := hTnonempty
    have hs := hsource x (hTsubset hx)
    have hsc := hsourceC x hx
    rw [hCzero, Polynomial.eval_zero, zero_mul] at hsc
    exact hs hsc
  have hAampne : Aamp ≠ 0 := by
    have hGmap : pair.common.map sigma.toRingHom ≠ 0 :=
      Polynomial.map_ne_zero pair.common_ne_zero
    exact mul_ne_zero hGmap hCne
  have hamplitude (x : F) (hx : x ∈ T) :
      atom.denominator.eval x * sigma (H x) = Aamp.eval x * H x := by
    have hxAtom := (Finset.mem_filter.mp hx).1
    have hxS := atom.valid_subset hxAtom
    have hCeval : C.eval x = pair.first.eval x + z * pair.second.eval x := by
      simp only [C, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C]
    have hGeval : (pair.common.map sigma.toRingHom).eval x =
        sigma (pair.common.eval x) :=
      polynomial_map_eval_of_fixed sigma pair.common x (hfixed x hxS)
    have hAeval : Aamp.eval x = sigma (pair.common.eval x) * C.eval x := by
      simp only [Aamp, Polynomial.eval_mul, hGeval]
    have hN₀eval : atom.numerator₀.eval x =
        sigma (pair.common.eval x) * sigma (pair.first.eval x) := by
      rw [← polynomial_symm_map_eval_of_fixed sigma atom.numerator₀ x
          (hfixed x hxS)]
      change sigma (B₀.eval x) = _
      have hf := congrArg (fun P : F[X] ↦ P.eval x) pair.first_factor
      have hf' : B₀.eval x =
          pair.common.eval x * pair.first.eval x := by
        simpa only [Polynomial.eval_mul] using hf.symm
      rw [hf', map_mul]
    have hN₁eval : atom.numerator₁.eval x =
        sigma (pair.common.eval x) * sigma (pair.second.eval x) := by
      rw [← polynomial_symm_map_eval_of_fixed sigma atom.numerator₁ x
          (hfixed x hxS)]
      change sigma (B₁.eval x) = _
      have hf := congrArg (fun P : F[X] ↦ P.eval x) pair.second_factor
      have hf' : B₁.eval x =
          pair.common.eval x * pair.second.eval x := by
        simpa only [Polynomial.eval_mul] using hf.symm
      rw [hf', map_mul]
    by_cases hC₀ : pair.first.eval x ≠ 0
    · have hrel := atom.interpolation₀ x hxAtom
      rw [hN₀eval, hsourceC x hx, htarget₀ x hxS,
        hdecomp₀ x hx, map_mul] at hrel
      apply mul_left_cancel₀ ((_root_.map_ne_zero sigma.toRingHom).2 hC₀)
      calc
        sigma (pair.first.eval x) *
            (atom.denominator.eval x * sigma (H x)) =
          atom.denominator.eval x *
            (sigma (pair.first.eval x) * sigma (H x)) := by ring
        _ = (sigma (pair.common.eval x) * sigma (pair.first.eval x)) *
            (C.eval x * H x) := hrel.symm
        _ = sigma (pair.first.eval x) *
            ((sigma (pair.common.eval x) * C.eval x) * H x) := by ring
        _ = sigma (pair.first.eval x) * (Aamp.eval x * H x) := by rw [hAeval]
    · have hC₁ : pair.second.eval x ≠ 0 := by
        intro hzero
        have hb := hbezoutEval x
        rw [not_ne_iff.mp hC₀, hzero, mul_zero, mul_zero, zero_add] at hb
        exact zero_ne_one hb
      have hrel := atom.interpolation₁ x hxAtom
      rw [hN₁eval, hsourceC x hx, htarget₁ x hxS,
        hdecomp₁ x hx, map_mul] at hrel
      apply mul_left_cancel₀ ((_root_.map_ne_zero sigma.toRingHom).2 hC₁)
      calc
        sigma (pair.second.eval x) *
            (atom.denominator.eval x * sigma (H x)) =
          atom.denominator.eval x *
            (sigma (pair.second.eval x) * sigma (H x)) := by ring
        _ = (sigma (pair.common.eval x) * sigma (pair.second.eval x)) *
            (C.eval x * H x) := hrel.symm
        _ = sigma (pair.second.eval x) *
            ((sigma (pair.common.eval x) * C.eval x) * H x) := by ring
        _ = sigma (pair.second.eval x) * (Aamp.eval x * H x) := by rw [hAeval]
  exact
    { direct₀ := pair.first
      direct₁ := pair.second
      common := pair.common
      denominator := atom.denominator
      amplitudeMultiplier := Aamp
      amplitude := H
      baseLoss := atom.loss
      gcdLoss := pair.common.natDegree
      valid := T
      common_ne_zero := pair.common_ne_zero
      denominator_ne_zero := atom.denominator_ne_zero
      amplitudeMultiplier_ne_zero := hAampne
      direct_coprime := pair.coprime
      direct₀_degree := pair.first_degree
      direct₁_degree := pair.second_degree
      denominator_degree := atom.denominator_degree
      amplitudeMultiplier_degree := hAampdegree
      valid_subset := hTsubset
      coverage := hcoverage
      decomposition₀ := hdecomp₀
      decomposition₁ := hdecomp₁
      amplitude_relation := hamplitude }

end ProximityPrize.SubmissionLower
