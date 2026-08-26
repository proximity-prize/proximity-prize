import ProximityPrize.SubmissionLower.BCHKSFrobeniusLinearPairNoGo6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusLinearReceivedLift6401
open Polynomial
open BCHKSFrobeniusLinearPairNoGo6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def receivedLinearA
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha u₀ : I → K) (i : I) : K :=
  alpha i * (sigma (u₀ i) - u₀ i)
def receivedLinearB
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha u₀ u₁ : I → K) (i : I) : K :=
  -sigma (u₀ i) - alpha i * u₁ i
def receivedLinearC
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha u₀ u₁ : I → K) (i : I) : K :=
  alpha i * sigma (u₁ i) + u₀ i
def receivedLinearD
    {K I : Type*} [Field K] (sigma : K →+* K)
    (u₁ : I → K) (i : I) : K :=
  u₁ i - sigma (u₁ i)
theorem movingLinear_received_expansion
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha u₀ u₁ : I → K) (z : K) (i : I) :
    (alpha i - z) * sigma (u₀ i + z * u₁ i) -
        (alpha i - sigma z) * (u₀ i + z * u₁ i) =
      receivedLinearA sigma alpha u₀ i +
        z * receivedLinearB sigma alpha u₀ u₁ i +
        sigma z * receivedLinearC sigma alpha u₀ u₁ i +
        (z * sigma z) * receivedLinearD sigma u₁ i := by
  simp only [map_add, map_mul, receivedLinearA, receivedLinearB,
    receivedLinearC, receivedLinearD]
  ring
theorem receivedLinear_coefficients_compatibility
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha u₀ u₁ : I → K) (i : I) :
    receivedLinearA sigma alpha u₀ i +
        alpha i *
          (receivedLinearB sigma alpha u₀ u₁ i +
            receivedLinearC sigma alpha u₀ u₁ i) +
        alpha i ^ 2 * receivedLinearD sigma u₁ i = 0 := by
  simp only [receivedLinearA, receivedLinearB, receivedLinearC,
    receivedLinearD]
  ring
theorem polynomial_eq_zero_of_eval_injective
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (alpha : I ↪ K) (P : K[X])
    (hdegree : P.natDegree < Fintype.card I)
    (hzero : ∀ i, P.eval (alpha i) = 0) : P = 0 := by
  classical
  let roots : Finset K := Finset.univ.image alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P roots
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact hzero i
  · rw [show roots.card = Fintype.card I by
      simp [roots, Finset.card_image_of_injective _ alpha.injective]]
    exact hdegree
theorem receivedLinear_polynomial_compatibility
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha : I ↪ K) (u₀ u₁ : I → K)
    (a b c d : K[X]) (k : Nat)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k)
    (hc : c.natDegree ≤ k) (hd : d.natDegree ≤ k)
    (hcard : k + 2 < Fintype.card I)
    (haeval : ∀ i, a.eval (alpha i) =
      receivedLinearA sigma alpha u₀ i)
    (hbeval : ∀ i, b.eval (alpha i) =
      receivedLinearB sigma alpha u₀ u₁ i)
    (hceval : ∀ i, c.eval (alpha i) =
      receivedLinearC sigma alpha u₀ u₁ i)
    (hdeval : ∀ i, d.eval (alpha i) =
      receivedLinearD sigma u₁ i) :
    a + Polynomial.X * (b + c) + Polynomial.X ^ 2 * d = 0 := by
  apply polynomial_eq_zero_of_eval_injective alpha
  · apply lt_of_le_of_lt _ hcard
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact ha.trans (Nat.le_add_right k 2)
      · calc
          (Polynomial.X * (b + c)).natDegree ≤
              Polynomial.X.natDegree + (b + c).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 + k := by
            apply Nat.add_le_add (by simp)
            exact (Polynomial.natDegree_add_le _ _).trans (max_le hb hc)
          _ ≤ k + 2 := by omega
    · calc
        (Polynomial.X ^ 2 * d).natDegree ≤
            (Polynomial.X ^ 2 : K[X]).natDegree + d.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 2 + k := by
          apply Nat.add_le_add (by simp) hd
        _ = k + 2 := by omega
  · intro i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, haeval i, hbeval i, hceval i, hdeval i]
    exact receivedLinear_coefficients_compatibility sigma alpha u₀ u₁ i
theorem wordInterpolant_natDegree_lt
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (alpha : I ↪ K) (u : I → K) (hI : 0 < Fintype.card I) :
    (Lagrange.interpolate Finset.univ alpha u).natDegree < Fintype.card I := by
  let P := Lagrange.interpolate Finset.univ alpha u
  change P.natDegree < Fintype.card I
  by_cases hP : P = 0
  · simpa [P, hP] using hI
  · have hdeg : P.degree <
        ((Finset.univ : Finset I).card : WithBot Nat) := by
      change (Lagrange.interpolate Finset.univ alpha u).degree <
        ((Finset.univ : Finset I).card : WithBot Nat)
      exact Lagrange.degree_interpolate_lt u alpha.injective.injOn
    have hn : P.natDegree < (Finset.univ : Finset I).card :=
      (Polynomial.natDegree_lt_iff_degree_lt hP).2 hdeg
    simpa using hn
theorem fourMonomial_words_have_lowDegreeRepresentatives
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I] [DecidableEq K]
    (alpha : I ↪ K) (A B C D : I → K) (S : Finset K)
    (q k : Nat) (hq : 1 < q)
    (hcardI : k < Fintype.card I)
    (howners : q + 1 < S.card)
    (hcode : ∀ z ∈ S, ∃ P : K[X],
      P.natDegree ≤ k ∧
      ∀ i, P.eval (alpha i) =
        A i + z * B i + z ^ q * C i + z ^ (q + 1) * D i) :
    ∃ a b c d : K[X],
      a.natDegree ≤ k ∧ b.natDegree ≤ k ∧
      c.natDegree ≤ k ∧ d.natDegree ≤ k ∧
      (∀ i, a.eval (alpha i) = A i) ∧
      (∀ i, b.eval (alpha i) = B i) ∧
      (∀ i, c.eval (alpha i) = C i) ∧
      (∀ i, d.eval (alpha i) = D i) := by
  classical
  let a := Lagrange.interpolate Finset.univ alpha A
  let b := Lagrange.interpolate Finset.univ alpha B
  let c := Lagrange.interpolate Finset.univ alpha C
  let d := Lagrange.interpolate Finset.univ alpha D
  have hIpos : 0 < Fintype.card I := lt_of_le_of_lt (Nat.zero_le k) hcardI
  have hadegAmbient : a.natDegree < Fintype.card I :=
    wordInterpolant_natDegree_lt alpha A hIpos
  have hbdegAmbient : b.natDegree < Fintype.card I :=
    wordInterpolant_natDegree_lt alpha B hIpos
  have hcdegAmbient : c.natDegree < Fintype.card I :=
    wordInterpolant_natDegree_lt alpha C hIpos
  have hddegAmbient : d.natDegree < Fintype.card I :=
    wordInterpolant_natDegree_lt alpha D hIpos
  have haeval : ∀ i, a.eval (alpha i) = A i := by
    intro i
    exact Lagrange.eval_interpolate_at_node A alpha.injective.injOn
      (Finset.mem_univ i)
  have hbeval : ∀ i, b.eval (alpha i) = B i := by
    intro i
    exact Lagrange.eval_interpolate_at_node B alpha.injective.injOn
      (Finset.mem_univ i)
  have hceval : ∀ i, c.eval (alpha i) = C i := by
    intro i
    exact Lagrange.eval_interpolate_at_node C alpha.injective.injOn
      (Finset.mem_univ i)
  have hdeval : ∀ i, d.eval (alpha i) = D i := by
    intro i
    exact Lagrange.eval_interpolate_at_node D alpha.injective.injOn
      (Finset.mem_univ i)
  have hcoeff (N : Nat) (hN : k < N) :
      a.coeff N = 0 ∧ b.coeff N = 0 ∧ c.coeff N = 0 ∧ d.coeff N = 0 := by
    let H : K[X] :=
      Polynomial.C (a.coeff N) +
        Polynomial.C (b.coeff N) * Polynomial.X +
        Polynomial.C (c.coeff N) * Polynomial.X ^ q +
        Polynomial.C (d.coeff N) * Polynomial.X ^ (q + 1)
    have hHdegree : H.natDegree ≤ q + 1 := by
      dsimp [H]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · apply (Polynomial.natDegree_add_le _ _).trans
          apply max_le
          · calc
              (Polynomial.C (a.coeff N)).natDegree ≤ 0 := by
                simpa using (Polynomial.natDegree_C_mul_le
                  (a.coeff N) (1 : K[X]))
              _ ≤ q + 1 := by omega
          · calc
              (Polynomial.C (b.coeff N) * Polynomial.X).natDegree ≤
                  Polynomial.X.natDegree :=
                Polynomial.natDegree_C_mul_le _ _
              _ = 1 := by simp
              _ ≤ q + 1 := by omega
        · calc
            (Polynomial.C (c.coeff N) * Polynomial.X ^ q).natDegree ≤
                (Polynomial.X ^ q : K[X]).natDegree :=
              Polynomial.natDegree_C_mul_le _ _
            _ = q := by simp
            _ ≤ q + 1 := by omega
      · calc
          (Polynomial.C (d.coeff N) * Polynomial.X ^ (q + 1)).natDegree ≤
              (Polynomial.X ^ (q + 1) : K[X]).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
          _ = q + 1 := by simp
    have hHzero : ∀ z ∈ S, H.eval z = 0 := by
      intro z hz
      obtain ⟨P, hPdegree, hPeval⟩ := hcode z hz
      let R := a + Polynomial.C z * b + Polynomial.C (z ^ q) * c +
        Polynomial.C (z ^ (q + 1)) * d
      have hRdegree : R.natDegree < Fintype.card I := by
        dsimp [R]
        apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) _
        apply max_lt
        · apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) _
          apply max_lt
          · apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) _
            exact max_lt hadegAmbient
              ((Polynomial.natDegree_C_mul_le _ _).trans_lt hbdegAmbient)
          · exact (Polynomial.natDegree_C_mul_le _ _).trans_lt hcdegAmbient
        · exact (Polynomial.natDegree_C_mul_le _ _).trans_lt hddegAmbient
      have hPR : P = R := by
        apply sub_eq_zero.mp
        apply polynomial_eq_zero_of_eval_injective alpha
        · exact (Polynomial.natDegree_sub_le _ _).trans_lt
            (max_lt (hPdegree.trans_lt hcardI) hRdegree)
        · intro i
          rw [Polynomial.eval_sub, hPeval i]
          simp only [R, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_C, haeval i, hbeval i, hceval i, hdeval i,
            sub_self]
      have hPN : P.coeff N = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hPdegree.trans_lt hN)
      have hRN : R.coeff N = 0 := by rw [← hPR, hPN]
      have hscalar : a.coeff N + z * b.coeff N + z ^ q * c.coeff N +
          z ^ (q + 1) * d.coeff N = 0 := by
        simpa only [R, Polynomial.coeff_add, Polynomial.coeff_C_mul] using hRN
      simp only [H, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      linear_combination hscalar
    have hHeq : H = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' H S
      · exact hHzero
      · exact hHdegree.trans_lt howners
    have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) hHeq
    have h1 := congrArg (fun P : K[X] ↦ P.coeff 1) hHeq
    have hqcoeff := congrArg (fun P : K[X] ↦ P.coeff q) hHeq
    have hq1 := congrArg (fun P : K[X] ↦ P.coeff (q + 1)) hHeq
    have hq0 : q ≠ 0 := by omega
    have h0q : 0 ≠ q := Ne.symm hq0
    have hq1ne : q ≠ 1 := by omega
    have h1q : 1 ≠ q := Ne.symm hq1ne
    have hqsucc0 : q + 1 ≠ 0 := by omega
    have h0qsucc : 0 ≠ q + 1 := Ne.symm hqsucc0
    have hqsucc1 : q + 1 ≠ 1 := by omega
    have h1qsucc : 1 ≠ q + 1 := Ne.symm hqsucc1
    have hq_ne_qsucc : q ≠ q + 1 := by omega
    have hqsucc_ne_q : q + 1 ≠ q := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [H, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow,
        hq0, h0q, hqsucc0, h0qsucc] using h0
    · simpa [H, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow,
        hq0, h0q, hq1ne, h1q, hqsucc1, h1qsucc] using h1
    · simpa [H, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow,
        hq0, h0q, hq1ne, h1q, hq_ne_qsucc, hqsucc_ne_q] using hqcoeff
    · simpa [H, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow,
        hq0, h0q, hqsucc0, h0qsucc, hqsucc1, h1qsucc,
        hq_ne_qsucc, hqsucc_ne_q] using hq1
  have hadeg : a.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact (hcoeff N hN).1
  have hbdeg : b.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact (hcoeff N hN).2.1
  have hcdeg : c.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact (hcoeff N hN).2.2.1
  have hddeg : d.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact (hcoeff N hN).2.2.2
  exact ⟨a, b, c, d, hadeg, hbdeg, hcdeg, hddeg,
    haeval, hbeval, hceval, hdeval⟩
noncomputable def movingReceivedPolynomial
    {K : Type*} [Field K] (sigma : K →+* K) (z : K) (P : K[X]) : K[X] :=
  linearFactor z * P.map sigma - linearFactor (sigma z) * P
theorem movingReceivedPolynomial_natDegree_le
    {K : Type*} [Field K] (sigma : K →+* K) (z : K)
    (P : K[X]) (k : Nat) (hk : 0 < k)
    (hP : P.natDegree ≤ k - 1) :
    (movingReceivedPolynomial sigma z P).natDegree ≤ k := by
  unfold movingReceivedPolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · calc
      (linearFactor z * P.map sigma).natDegree ≤
          (linearFactor z).natDegree + (P.map sigma).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (k - 1) := Nat.add_le_add (by simp [linearFactor])
        (Polynomial.natDegree_map_le.trans hP)
      _ = k := Nat.add_sub_of_le hk
  · calc
      (linearFactor (sigma z) * P).natDegree ≤
          (linearFactor (sigma z)).natDegree + P.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (k - 1) := Nat.add_le_add (by simp [linearFactor]) hP
      _ = k := Nat.add_sub_of_le hk
theorem movingReceivedPolynomial_eval_of_discrepancy_relation
    {K I : Type*} [Field K] (sigma : K →+* K)
    (alpha : I → K) (u₀ u₁ : I → K) (z : K) (P : K[X])
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hrel : ∀ i,
      (alpha i - z) *
          sigma (u₀ i + z * u₁ i - P.eval (alpha i)) =
        (alpha i - sigma z) *
          (u₀ i + z * u₁ i - P.eval (alpha i))) :
    ∀ i, (movingReceivedPolynomial sigma z P).eval (alpha i) =
      (alpha i - z) * sigma (u₀ i + z * u₁ i) -
        (alpha i - sigma z) * (u₀ i + z * u₁ i) := by
  intro i
  have hmap : (P.map sigma).eval (alpha i) = sigma (P.eval (alpha i)) := by
    calc
      (P.map sigma).eval (alpha i) =
          (P.map sigma).eval (sigma (alpha i)) := by rw [hfixed i]
      _ = sigma (P.eval (alpha i)) :=
        Polynomial.eval_map_apply (p := P) sigma (alpha i)
  rw [movingReceivedPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_mul, linearFactor_eval, linearFactor_eval,
    hmap]
  have hi := hrel i
  simp only [map_sub] at hi
  linear_combination -hi
def cyclicTraceSix {K : Type*} [Field K] (sigma : K →+* K) (x : K) : K :=
  x + sigma x + sigma (sigma x) + sigma (sigma (sigma x)) +
    sigma (sigma (sigma (sigma x))) +
    sigma (sigma (sigma (sigma (sigma x))))
def additivePreimageSix {K : Type*} [Field K]
    (sigma : K →+* K) (x : K) : K :=
  (6 : K)⁻¹ *
    (sigma x + 2 * sigma (sigma x) +
      3 * sigma (sigma (sigma x)) +
      4 * sigma (sigma (sigma (sigma x))) +
      5 * sigma (sigma (sigma (sigma (sigma x)))))
theorem cyclicTraceSix_map_sub_self
    {K : Type*} [Field K] (sigma : K →+* K)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (x : K) : cyclicTraceSix sigma (sigma x - x) = 0 := by
  simp only [cyclicTraceSix, map_sub]
  rw [horder x]
  ring
theorem sigma_additivePreimageSix_sub
    {K : Type*} [Field K] (sigma : K →+* K)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsix : (6 : K) ≠ 0) (x : K)
    (htrace : cyclicTraceSix sigma x = 0) :
    sigma (additivePreimageSix sigma x) - additivePreimageSix sigma x = x := by
  simp only [additivePreimageSix, map_mul, map_add, map_natCast]
  have h2 : sigma (2 : K) = 2 := by simpa using map_natCast sigma 2
  have h3 : sigma (3 : K) = 3 := by simpa using map_natCast sigma 3
  have h4 : sigma (4 : K) = 4 := by simpa using map_natCast sigma 4
  have h5 : sigma (5 : K) = 5 := by simpa using map_natCast sigma 5
  have h6 : sigma (6 : K) = 6 := by simpa using map_natCast sigma 6
  have hinv : sigma (6 : K)⁻¹ = (6 : K)⁻¹ := by
    rw [map_inv₀, h6]
  rw [hinv, horder x]
  rw [h2, h3, h4, h5]
  dsimp [cyclicTraceSix] at htrace
  field_simp [hsix]
  linear_combination -htrace
noncomputable def polynomialCyclicTraceSix
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) : K[X] :=
  P + P.map sigma + (P.map sigma).map sigma +
    ((P.map sigma).map sigma).map sigma +
    (((P.map sigma).map sigma).map sigma).map sigma +
    ((((P.map sigma).map sigma).map sigma).map sigma).map sigma
noncomputable def polynomialAdditivePreimageSix
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) : K[X] :=
  Polynomial.C (6 : K)⁻¹ *
    (P.map sigma + Polynomial.C 2 * (P.map sigma).map sigma +
      Polynomial.C 3 * ((P.map sigma).map sigma).map sigma +
      Polynomial.C 4 * (((P.map sigma).map sigma).map sigma).map sigma +
      Polynomial.C 5 * ((((P.map sigma).map sigma).map sigma).map sigma).map sigma)
theorem polynomialCyclicTraceSix_coeff
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) (n : Nat) :
    (polynomialCyclicTraceSix sigma P).coeff n =
      cyclicTraceSix sigma (P.coeff n) := by
  simp [polynomialCyclicTraceSix, cyclicTraceSix]
theorem polynomialCyclicTraceSix_natDegree_le
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) :
    (polynomialCyclicTraceSix sigma P).natDegree ≤ P.natDegree := by
  let P₁ := P.map sigma
  let P₂ := P₁.map sigma
  let P₃ := P₂.map sigma
  let P₄ := P₃.map sigma
  let P₅ := P₄.map sigma
  have hP₁ : P₁.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
  have hP₂ : P₂.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₁
  have hP₃ : P₃.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₂
  have hP₄ : P₄.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₃
  have hP₅ : P₅.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₄
  have h01 : (P + P₁).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le le_rfl hP₁)
  have h012 : (P + P₁ + P₂).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le h01 hP₂)
  have h0123 : (P + P₁ + P₂ + P₃).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le h012 hP₃)
  have h01234 : (P + P₁ + P₂ + P₃ + P₄).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le h0123 hP₄)
  change (P + P₁ + P₂ + P₃ + P₄ + P₅).natDegree ≤ P.natDegree
  exact (Polynomial.natDegree_add_le _ _).trans (max_le h01234 hP₅)
theorem eval_map_eq_sigma_eval_of_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (P : K[X]) (x : K) (hx : sigma x = x) :
    (P.map sigma).eval x = sigma (P.eval x) := by
  calc
    (P.map sigma).eval x = (P.map sigma).eval (sigma x) := by rw [hx]
    _ = sigma (P.eval x) :=
      Polynomial.eval_map_apply (p := P) sigma x
theorem eval_polynomialCyclicTraceSix_of_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (P : K[X]) (x : K) (hx : sigma x = x) :
    (polynomialCyclicTraceSix sigma P).eval x =
      cyclicTraceSix sigma (P.eval x) := by
  simp only [polynomialCyclicTraceSix, Polynomial.eval_add]
  repeat' rw [eval_map_eq_sigma_eval_of_fixed sigma _ x hx]
  rfl
theorem polynomialAdditivePreimageSix_coeff
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) (n : Nat) :
    (polynomialAdditivePreimageSix sigma P).coeff n =
      additivePreimageSix sigma (P.coeff n) := by
  simp [polynomialAdditivePreimageSix, additivePreimageSix]
theorem polynomialAdditivePreimageSix_sigma_sub
    {K : Type*} [Field K] (sigma : K →+* K)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsix : (6 : K) ≠ 0) (P : K[X])
    (htrace : polynomialCyclicTraceSix sigma P = 0) :
    (polynomialAdditivePreimageSix sigma P).map sigma -
        polynomialAdditivePreimageSix sigma P = P := by
  ext n
  rw [Polynomial.coeff_sub, Polynomial.coeff_map,
    polynomialAdditivePreimageSix_coeff]
  have hntrace : cyclicTraceSix sigma (P.coeff n) = 0 := by
    have := congrArg (fun Q : K[X] ↦ Q.coeff n) htrace
    simpa [polynomialCyclicTraceSix_coeff] using this
  exact sigma_additivePreimageSix_sub sigma horder hsix _ hntrace
theorem polynomialAdditivePreimageSix_natDegree_le
    {K : Type*} [Field K] (sigma : K →+* K) (P : K[X]) :
    (polynomialAdditivePreimageSix sigma P).natDegree ≤ P.natDegree := by
  let P₁ := P.map sigma
  let P₂ := P₁.map sigma
  let P₃ := P₂.map sigma
  let P₄ := P₃.map sigma
  let P₅ := P₄.map sigma
  have hP₁ : P₁.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
  have hP₂ : P₂.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₁
  have hP₃ : P₃.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₂
  have hP₄ : P₄.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₃
  have hP₅ : P₅.natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le.trans hP₄
  have h2P₂ : (Polynomial.C 2 * P₂).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_C_mul_le 2 P₂).trans hP₂
  have h3P₃ : (Polynomial.C 3 * P₃).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_C_mul_le 3 P₃).trans hP₃
  have h4P₄ : (Polynomial.C 4 * P₄).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_C_mul_le 4 P₄).trans hP₄
  have h5P₅ : (Polynomial.C 5 * P₅).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_C_mul_le 5 P₅).trans hP₅
  have h12 : (P₁ + Polynomial.C 2 * P₂).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hP₁ h2P₂)
  have h123 :
      (P₁ + Polynomial.C 2 * P₂ + Polynomial.C 3 * P₃).natDegree ≤
        P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le h12 h3P₃)
  have h1234 :
      (P₁ + Polynomial.C 2 * P₂ + Polynomial.C 3 * P₃ +
        Polynomial.C 4 * P₄).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le h123 h4P₄)
  have hsum :
      (P₁ + Polynomial.C 2 * P₂ + Polynomial.C 3 * P₃ +
        Polynomial.C 4 * P₄ + Polynomial.C 5 * P₅).natDegree ≤
        P.natDegree := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le h1234 h5P₅)
  change (Polynomial.C (6 : K)⁻¹ *
      (P₁ + Polynomial.C 2 * P₂ + Polynomial.C 3 * P₃ +
        Polynomial.C 4 * P₄ + Polynomial.C 5 * P₅)).natDegree ≤
      P.natDegree
  exact (Polynomial.natDegree_C_mul_le _ _).trans hsum
theorem compatibility_degree_drops
    {K : Type*} [Field K] (a b c d : K[X]) (k : Nat)
    (hk : 0 < k)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k)
    (hc : c.natDegree ≤ k) (hd : d.natDegree ≤ k)
    (hcompat : a + Polynomial.X * (b + c) + Polynomial.X ^ 2 * d = 0) :
    a.coeff 0 = 0 ∧ d.natDegree ≤ k - 1 := by
  constructor
  · have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) hcompat
    simpa using h0
  · have haTop : a.coeff (k + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (ha.trans_lt (by omega))
    have hbcDegree : (Polynomial.X * (b + c)).natDegree ≤ k + 1 := by
      calc
        (Polynomial.X * (b + c)).natDegree ≤
            Polynomial.X.natDegree + (b + c).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 + k := by
          apply Nat.add_le_add (by simp)
          exact (Polynomial.natDegree_add_le _ _).trans (max_le hb hc)
        _ = k + 1 := by omega
    have hbcTop : (Polynomial.X * (b + c)).coeff (k + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hbcDegree.trans_lt (by omega))
    have htop := congrArg (fun P : K[X] ↦ P.coeff (k + 2)) hcompat
    have hdTop : d.coeff k = 0 := by
      rw [Polynomial.coeff_add, Polynomial.coeff_add, haTop, hbcTop,
        Polynomial.coeff_zero, zero_add, zero_add] at htop
      have hshift : (Polynomial.X ^ 2 * d).coeff (k + 2) = d.coeff k := by
        simpa [Nat.add_comm] using Polynomial.coeff_X_pow_mul d 2 k
      simpa [hshift] using htop
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hkN : k ≤ N := by omega
    rcases hkN.eq_or_lt with rfl | hkNlt
    · exact hdTop
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hkNlt)
theorem polynomial_trace_eq_zero_of_eval_map_sub_self
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha : I ↪ K) (u : I → K) (P : K[X])
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hdegree : P.natDegree < Fintype.card I)
    (heval : ∀ i, P.eval (alpha i) = sigma (u i) - u i) :
    polynomialCyclicTraceSix sigma P = 0 := by
  apply polynomial_eq_zero_of_eval_injective alpha
  · exact (polynomialCyclicTraceSix_natDegree_le sigma P).trans_lt hdegree
  · intro i
    rw [eval_polynomialCyclicTraceSix_of_fixed sigma P (alpha i) (hfixed i),
      heval i]
    exact cyclicTraceSix_map_sub_self sigma horder (u i)
theorem polynomial_trace_eq_zero_of_eval_self_sub_map
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha : I ↪ K) (u : I → K) (P : K[X])
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hdegree : P.natDegree < Fintype.card I)
    (heval : ∀ i, P.eval (alpha i) = u i - sigma (u i)) :
    polynomialCyclicTraceSix sigma P = 0 := by
  apply polynomial_eq_zero_of_eval_injective alpha
  · exact (polynomialCyclicTraceSix_natDegree_le sigma P).trans_lt hdegree
  · intro i
    rw [eval_polynomialCyclicTraceSix_of_fixed sigma P (alpha i) (hfixed i),
      heval i]
    simp only [sub_eq_neg_add, map_neg, map_add, cyclicTraceSix]
    rw [horder (u i)]
    ring
theorem exists_affineParticular_of_fourRepresentatives
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (sigma : K →+* K) (alpha : I ↪ K) (u₀ u₁ : I → K)
    (a b c d : K[X]) (k : Nat)
    (hk : 0 < k)
    (hsix : (6 : K) ≠ 0)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (halpha : ∀ i, alpha i ≠ 0)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k)
    (hc : c.natDegree ≤ k) (hd : d.natDegree ≤ k)
    (hcard : k + 2 < Fintype.card I)
    (haeval : ∀ i, a.eval (alpha i) =
      receivedLinearA sigma alpha u₀ i)
    (hbeval : ∀ i, b.eval (alpha i) =
      receivedLinearB sigma alpha u₀ u₁ i)
    (hceval : ∀ i, c.eval (alpha i) =
      receivedLinearC sigma alpha u₀ u₁ i)
    (hdeval : ∀ i, d.eval (alpha i) =
      receivedLinearD sigma u₁ i) :
    ∃ P₀ P₁ : K[X], ∃ f : I → K,
      P₀.natDegree ≤ k - 1 ∧ P₁.natDegree ≤ k - 1 ∧
      (∀ i, sigma (f i) = f i) ∧
      (∀ i, u₀ i - P₀.eval (alpha i) = alpha i * f i) ∧
      (∀ i, u₁ i - P₁.eval (alpha i) = -f i) ∧
      a = Polynomial.X * (P₀.map sigma - P₀) ∧
      b = -(P₀.map sigma) - Polynomial.X * P₁ ∧
      c = Polynomial.X * (P₁.map sigma) + P₀ ∧
      d = P₁ - P₁.map sigma := by
  let e := a.divX
  have hcompat := receivedLinear_polynomial_compatibility sigma alpha u₀ u₁
    a b c d k ha hb hc hd hcard haeval hbeval hceval hdeval
  have hdrops := compatibility_degree_drops a b c d k hk ha hb hc hd hcompat
  have hXe : Polynomial.X * e = a := by
    have hdiv := Polynomial.X_mul_divX_add a
    rw [hdrops.1, Polynomial.C_0, add_zero] at hdiv
    exact hdiv
  have hedegree : e.natDegree ≤ k - 1 := by
    dsimp [e]
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_le_sub_right ha 1
  have heeval : ∀ i, e.eval (alpha i) = sigma (u₀ i) - u₀ i := by
    intro i
    have hi := congrArg (Polynomial.eval (alpha i)) hXe
    rw [Polynomial.eval_mul, Polynomial.eval_X, haeval i,
      receivedLinearA] at hi
    exact mul_left_cancel₀ (halpha i) hi
  have hetrace : polynomialCyclicTraceSix sigma e = 0 :=
    polynomial_trace_eq_zero_of_eval_map_sub_self sigma alpha u₀ e hfixed
      horder (hedegree.trans_lt (by omega)) heeval
  have hdtrace : polynomialCyclicTraceSix sigma d = 0 :=
    polynomial_trace_eq_zero_of_eval_self_sub_map sigma alpha u₁ d hfixed
      horder (hdrops.2.trans_lt (by omega)) hdeval
  let Q₀ := polynomialAdditivePreimageSix sigma e
  let Q₁ := polynomialAdditivePreimageSix sigma d
  have hQ₀rel : Q₀.map sigma - Q₀ = e :=
    polynomialAdditivePreimageSix_sigma_sub sigma horder hsix e hetrace
  have hQ₁rel : Q₁.map sigma - Q₁ = d :=
    polynomialAdditivePreimageSix_sigma_sub sigma horder hsix d hdtrace
  have hQ₀degree : Q₀.natDegree ≤ k - 1 :=
    (polynomialAdditivePreimageSix_natDegree_le sigma e).trans hedegree
  have hQ₁degree : Q₁.natDegree ≤ k - 1 :=
    (polynomialAdditivePreimageSix_natDegree_le sigma d).trans hdrops.2
  let P₀pre := Q₀
  let P₁pre := -Q₁
  have hP₀preRel : P₀pre.map sigma - P₀pre = e := hQ₀rel
  have hP₁preRel : P₁pre - P₁pre.map sigma = d := by
    dsimp [P₁pre]
    rw [Polynomial.map_neg]
    linear_combination hQ₁rel
  have hP₀preDegree : P₀pre.natDegree ≤ k - 1 := hQ₀degree
  have hP₁preDegree : P₁pre.natDegree ≤ k - 1 := by
    simpa [P₁pre] using hQ₁degree
  let v₀ : I → K := fun i ↦ u₀ i - P₀pre.eval (alpha i)
  let v₁ : I → K := fun i ↦ u₁ i - P₁pre.eval (alpha i)
  have hv₀fixed : ∀ i, sigma (v₀ i) = v₀ i := by
    intro i
    have hrelEval := congrArg (Polynomial.eval (alpha i)) hP₀preRel
    rw [Polynomial.eval_sub,
      eval_map_eq_sigma_eval_of_fixed sigma P₀pre (alpha i) (hfixed i),
      heeval i] at hrelEval
    dsimp [v₀]
    simp only [map_sub]
    linear_combination -hrelEval
  have hv₁fixed : ∀ i, sigma (v₁ i) = v₁ i := by
    intro i
    have hrelEval := congrArg (Polynomial.eval (alpha i)) hP₁preRel
    rw [Polynomial.eval_sub,
      eval_map_eq_sigma_eval_of_fixed sigma P₁pre (alpha i) (hfixed i),
      hdeval i, receivedLinearD] at hrelEval
    dsimp [v₁]
    simp only [map_sub]
    linear_combination hrelEval
  let qpoly := b - (-(P₀pre.map sigma) - Polynomial.X * P₁pre)
  have hqdegree : qpoly.natDegree ≤ k := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le hb
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have hmap : (P₀pre.map sigma).natDegree ≤ k :=
        Polynomial.natDegree_map_le.trans
          (hP₀preDegree.trans (Nat.sub_le k 1))
      simpa using hmap
    · calc
        (Polynomial.X * P₁pre).natDegree ≤
            Polynomial.X.natDegree + P₁pre.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 + (k - 1) := Nat.add_le_add (by simp) hP₁preDegree
        _ = k := Nat.add_sub_of_le hk
  have hqeval : ∀ i, qpoly.eval (alpha i) = -(v₀ i + alpha i * v₁ i) := by
    intro i
    rw [show qpoly = b - (-(P₀pre.map sigma) - Polynomial.X * P₁pre) by rfl,
      Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_neg,
      Polynomial.eval_mul, Polynomial.eval_X,
      eval_map_eq_sigma_eval_of_fixed sigma P₀pre (alpha i) (hfixed i),
      hbeval i]
    have hv := hv₀fixed i
    dsimp [v₀] at hv
    simp only [map_sub] at hv
    simp only [receivedLinearB, v₀, v₁]
    linear_combination -hv
  have hqfixed : qpoly.map sigma = qpoly := by
    apply sub_eq_zero.mp
    apply polynomial_eq_zero_of_eval_injective alpha
    · apply lt_of_le_of_lt _ (by omega : k < Fintype.card I)
      exact (Polynomial.natDegree_sub_le _ _).trans
        (max_le (Polynomial.natDegree_map_le.trans hqdegree) hqdegree)
    · intro i
      rw [Polynomial.eval_sub,
        eval_map_eq_sigma_eval_of_fixed sigma qpoly (alpha i) (hfixed i),
        hqeval i]
      simp only [map_neg, map_add, map_mul, hv₀fixed i, hv₁fixed i,
        hfixed i, sub_self]
  let H₀ := Polynomial.C (qpoly.coeff 0)
  let H₁ := qpoly.divX
  have hqsplit : H₀ + Polynomial.X * H₁ = qpoly := by
    simpa [H₀, H₁, add_comm] using Polynomial.X_mul_divX_add qpoly
  have hcoefffixed : ∀ n, sigma (qpoly.coeff n) = qpoly.coeff n := by
    intro n
    have hn := congrArg (fun P : K[X] ↦ P.coeff n) hqfixed
    simpa using hn
  have hH₀fixed : H₀.map sigma = H₀ := by
    simp [H₀, hcoefffixed 0]
  have hH₁fixed : H₁.map sigma = H₁ := by
    ext n
    simp [H₁, hcoefffixed (n + 1)]
  have hH₀degree : H₀.natDegree ≤ k - 1 := by
    have hzero : H₀.natDegree ≤ 0 := by
      simpa [H₀] using
        (Polynomial.natDegree_C_mul_le (qpoly.coeff 0) (1 : K[X]))
    calc
      H₀.natDegree ≤ 0 := hzero
      _ ≤ k - 1 := by omega
  have hH₁degree : H₁.natDegree ≤ k - 1 := by
    dsimp [H₁]
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_le_sub_right hqdegree 1
  let P₀ := P₀pre - H₀
  let P₁ := P₁pre - H₁
  have hP₀degree : P₀.natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le hP₀preDegree hH₀degree)
  have hP₁degree : P₁.natDegree ≤ k - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le hP₁preDegree hH₁degree)
  have hP₀rel : P₀.map sigma - P₀ = e := by
    dsimp [P₀]
    rw [Polynomial.map_sub, hH₀fixed]
    linear_combination hP₀preRel
  have hP₁rel : P₁ - P₁.map sigma = d := by
    dsimp [P₁]
    rw [Polynomial.map_sub, hH₁fixed]
    linear_combination hP₁preRel
  have hbpoly : b = -(P₀.map sigma) - Polynomial.X * P₁ := by
    calc
      b = (-(P₀pre.map sigma) - Polynomial.X * P₁pre) + qpoly := by
        dsimp [qpoly]
        ring
      _ = (-(P₀pre.map sigma) - Polynomial.X * P₁pre) +
          (H₀ + Polynomial.X * H₁) := by rw [hqsplit]
      _ = -(P₀.map sigma) - Polynomial.X * P₁ := by
        dsimp [P₀, P₁]
        rw [Polynomial.map_sub, hH₀fixed]
        ring
  have hapoly : a = Polynomial.X * (P₀.map sigma - P₀) := by
    rw [hP₀rel, hXe]
  let cExpected := Polynomial.X * (P₁.map sigma) + P₀
  have hExpectedCompat :
      a + Polynomial.X * (b + cExpected) + Polynomial.X ^ 2 * d = 0 := by
    rw [hapoly, hbpoly, ← hP₁rel]
    dsimp [cExpected]
    ring
  have hXdiff : Polynomial.X * (c - cExpected) = 0 := by
    linear_combination hcompat - hExpectedCompat
  have hcpoly : c = Polynomial.X * (P₁.map sigma) + P₀ := by
    have hdiff : c - cExpected = 0 :=
      (mul_eq_zero.mp hXdiff).resolve_left Polynomial.X_ne_zero
    exact sub_eq_zero.mp hdiff
  let f : I → K := fun i ↦ -(u₁ i - P₁.eval (alpha i))
  have hv₀FinalFixed : ∀ i,
      sigma (u₀ i - P₀.eval (alpha i)) =
        u₀ i - P₀.eval (alpha i) := by
    intro i
    have hrelEval := congrArg (Polynomial.eval (alpha i)) hP₀rel
    rw [Polynomial.eval_sub,
      eval_map_eq_sigma_eval_of_fixed sigma P₀ (alpha i) (hfixed i),
      heeval i] at hrelEval
    simp only [map_sub]
    linear_combination -hrelEval
  have hv₁FinalFixed : ∀ i,
      sigma (u₁ i - P₁.eval (alpha i)) =
        u₁ i - P₁.eval (alpha i) := by
    intro i
    have hrelEval := congrArg (Polynomial.eval (alpha i)) hP₁rel
    rw [Polynomial.eval_sub,
      eval_map_eq_sigma_eval_of_fixed sigma P₁ (alpha i) (hfixed i),
      hdeval i, receivedLinearD] at hrelEval
    simp only [map_sub]
    linear_combination hrelEval
  have hfFixed : ∀ i, sigma (f i) = f i := by
    intro i
    have hv := hv₁FinalFixed i
    dsimp [f]
    simp only [map_neg, map_sub]
    simp only [map_sub] at hv
    linear_combination -hv
  have hsecond : ∀ i, u₁ i - P₁.eval (alpha i) = -f i := by
    intro i
    simp [f]
  have hfirst : ∀ i, u₀ i - P₀.eval (alpha i) = alpha i * f i := by
    intro i
    have hbe := congrArg (Polynomial.eval (alpha i)) hbpoly
    rw [hbeval i, Polynomial.eval_sub, Polynomial.eval_neg,
      Polynomial.eval_mul, Polynomial.eval_X,
      eval_map_eq_sigma_eval_of_fixed sigma P₀ (alpha i) (hfixed i)] at hbe
    have hsum : sigma (u₀ i - P₀.eval (alpha i)) +
        alpha i * (u₁ i - P₁.eval (alpha i)) = 0 := by
      simp only [map_sub]
      simp only [receivedLinearB] at hbe
      linear_combination -hbe
    rw [hv₀FinalFixed i] at hsum
    dsimp [f]
    linear_combination hsum
  exact ⟨P₀, P₁, f, hP₀degree, hP₁degree, hfFixed, hfirst, hsecond,
    hapoly, hbpoly, hcpoly, hP₁rel.symm⟩
theorem exists_affineParticular_of_many_canonicalMovingOwners
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I] [DecidableEq K]
    (sigma : K →+* K) (alpha : I ↪ K) (u₀ u₁ : I → K)
    (S : Finset K) (P : K → K[X]) (q k : Nat)
    (hq : 1 < q) (hk : 0 < k)
    (hsix : (6 : K) ≠ 0)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (halpha : ∀ i, alpha i ≠ 0)
    (hcard : k + 2 < Fintype.card I)
    (howners : q + 1 < S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k - 1)
    (hrel : ∀ z ∈ S, ∀ i,
      (alpha i - z) *
          sigma (u₀ i + z * u₁ i - (P z).eval (alpha i)) =
        (alpha i - sigma z) *
          (u₀ i + z * u₁ i - (P z).eval (alpha i))) :
    ∃ P₀ P₁ : K[X], ∃ f : I → K,
      P₀.natDegree ≤ k - 1 ∧ P₁.natDegree ≤ k - 1 ∧
      (∀ i, sigma (f i) = f i) ∧
      (∀ i, u₀ i - P₀.eval (alpha i) = alpha i * f i) ∧
      (∀ i, u₁ i - P₁.eval (alpha i) = -f i) := by
  have hcode : ∀ z ∈ S, ∃ Q : K[X], Q.natDegree ≤ k ∧
      ∀ i, Q.eval (alpha i) =
        receivedLinearA sigma alpha u₀ i +
          z * receivedLinearB sigma alpha u₀ u₁ i +
          z ^ q * receivedLinearC sigma alpha u₀ u₁ i +
          z ^ (q + 1) * receivedLinearD sigma u₁ i := by
    intro z hz
    refine ⟨movingReceivedPolynomial sigma z (P z),
      movingReceivedPolynomial_natDegree_le sigma z (P z) k hk
        (hPdegree z hz), ?_⟩
    intro i
    rw [movingReceivedPolynomial_eval_of_discrepancy_relation sigma alpha
      u₀ u₁ z (P z) hfixed (hrel z hz) i,
      movingLinear_received_expansion]
    rw [hsigma z hz]
    congr 1
    rw [pow_succ]
    ring
  obtain ⟨a, b, c, d, ha, hb, hc, hd, haeval, hbeval, hceval, hdeval⟩ :=
    fourMonomial_words_have_lowDegreeRepresentatives alpha
      (receivedLinearA sigma alpha u₀)
      (receivedLinearB sigma alpha u₀ u₁)
      (receivedLinearC sigma alpha u₀ u₁)
      (receivedLinearD sigma u₁) S q k hq (by omega) howners hcode
  obtain ⟨P₀, P₁, f, hP₀, hP₁, hf, h0, h1, _ha, _hb, _hc, _hd⟩ :=
    exists_affineParticular_of_fourRepresentatives sigma alpha u₀ u₁
      a b c d k hk hsix horder hfixed halpha ha hb hc hd hcard
      haeval hbeval hceval hdeval
  exact ⟨P₀, P₁, f, hP₀, hP₁, hf, h0, h1⟩
def affinePencilRoot
    {K : Type*} [Field K] (a₀ a₁ b₀ b₁ t : K) : K :=
  -(a₀ + t * a₁) / (b₀ + t * b₁)
def affinePencilDet
    {K : Type*} [Field K] (a₀ a₁ b₀ b₁ : K) : K :=
  a₀ * b₁ - a₁ * b₀
theorem affinePencilRoot_injective
    {K : Type*} [Field K] (a₀ a₁ b₀ b₁ t v : K)
    (hdet : affinePencilDet a₀ a₁ b₀ b₁ ≠ 0)
    (ht : b₀ + t * b₁ ≠ 0) (hv : b₀ + v * b₁ ≠ 0)
    (hroot : affinePencilRoot a₀ a₁ b₀ b₁ t =
      affinePencilRoot a₀ a₁ b₀ b₁ v) :
    t = v := by
  have hcross :
      (a₀ + t * a₁) * (b₀ + v * b₁) =
        (a₀ + v * a₁) * (b₀ + t * b₁) := by
    dsimp [affinePencilRoot] at hroot
    apply (div_eq_div_iff ht hv).mp
    apply neg_inj.mp
    simpa only [neg_div] using hroot
  have hprod :
      (t - v) * affinePencilDet a₀ a₁ b₀ b₁ = 0 := by
    dsimp [affinePencilDet]
    linear_combination -hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hdet)
theorem normalize_affinePencil_relation
    {K : Type*} [Field K] (sigma : K →+* K)
    (alpha E a b : K) (hb : b ≠ 0) (hfixed : sigma alpha = alpha)
    (hrel : (a + b * alpha) * sigma E =
      sigma (a + b * alpha) * E) :
    (alpha - affinePencilRoot a 0 b 0 0) * sigma (E / b) =
      (alpha - sigma (affinePencilRoot a 0 b 0 0)) * (E / b) := by
  have hsigmab : sigma b ≠ 0 := (map_ne_zero sigma).2 hb
  simp only [affinePencilRoot, zero_mul, add_zero, map_neg]
  rw [map_div₀ sigma E b, map_div₀ sigma (-a) b, map_neg sigma a]
  rw [map_add, map_mul, hfixed] at hrel
  field_simp [hb, hsigmab]
  linear_combination hrel
theorem normalize_affinePencil_relation_at
    {K : Type*} [Field K] (sigma : K →+* K)
    (alpha E a₀ a₁ b₀ b₁ t : K)
    (hb : b₀ + t * b₁ ≠ 0) (hfixed : sigma alpha = alpha)
    (hrel :
      ((a₀ + t * a₁) + (b₀ + t * b₁) * alpha) * sigma E =
        sigma ((a₀ + t * a₁) +
          (b₀ + t * b₁) * alpha) * E) :
    (alpha - affinePencilRoot a₀ a₁ b₀ b₁ t) *
        sigma (E / (b₀ + t * b₁)) =
      (alpha - sigma (affinePencilRoot a₀ a₁ b₀ b₁ t)) *
        (E / (b₀ + t * b₁)) := by
  simpa [affinePencilRoot] using
    normalize_affinePencil_relation sigma alpha E
      (a₀ + t * a₁) (b₀ + t * b₁) hb hfixed hrel
def normalizedReceivedZero
    {K I : Type*} [Field K]
    (a₀ a₁ b₀ b₁ : K) (u₀ u₁ : I → K) (i : I) : K :=
  (affinePencilDet a₀ a₁ b₀ b₁)⁻¹ *
    (-a₁ * u₀ i + a₀ * u₁ i)
def normalizedReceivedOne
    {K I : Type*} [Field K]
    (a₀ a₁ b₀ b₁ : K) (u₀ u₁ : I → K) (i : I) : K :=
  (affinePencilDet a₀ a₁ b₀ b₁)⁻¹ *
    (-b₁ * u₀ i + b₀ * u₁ i)
theorem affineReceived_eq_leading_mul_normalized
    {K I : Type*} [Field K]
    (a₀ a₁ b₀ b₁ t : K) (u₀ u₁ : I → K) (i : I)
    (hdet : affinePencilDet a₀ a₁ b₀ b₁ ≠ 0)
    (hb : b₀ + t * b₁ ≠ 0) :
    u₀ i + t * u₁ i =
      (b₀ + t * b₁) *
        (normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁ i +
          affinePencilRoot a₀ a₁ b₀ b₁ t *
            normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁ i) := by
  dsimp [normalizedReceivedZero, normalizedReceivedOne,
    affinePencilRoot, affinePencilDet]
  have hd : a₀ * b₁ - a₁ * b₀ ≠ 0 := by
    simpa [affinePencilDet] using hdet
  field_simp [hd, hb]
  have hd' : b₁ * a₀ - b₀ * a₁ ≠ 0 := by
    intro h
    apply hd
    linear_combination h
  try field_simp [hd']
  ring
theorem exists_affineParticular_of_many_embeddedCanonicalMovingOwners
    {K I T : Type*} [Field K] [Fintype I] [DecidableEq I]
    [DecidableEq K] [DecidableEq T] [Nonempty T]
    (sigma : K →+* K) (alpha : I ↪ K) (u₀ u₁ : I → K)
    (beta : T ↪ K) (S : Finset T) (P : T → K[X]) (q k : Nat)
    (hq : 1 < q) (hk : 0 < k)
    (hsix : (6 : K) ≠ 0)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ t ∈ S, sigma (beta t) = beta t ^ q)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (halpha : ∀ i, alpha i ≠ 0)
    (hcard : k + 2 < Fintype.card I)
    (howners : q + 1 < S.card)
    (hPdegree : ∀ t ∈ S, (P t).natDegree ≤ k - 1)
    (hrel : ∀ t ∈ S, ∀ i,
      (alpha i - beta t) *
          sigma (u₀ i + beta t * u₁ i - (P t).eval (alpha i)) =
        (alpha i - sigma (beta t)) *
          (u₀ i + beta t * u₁ i - (P t).eval (alpha i))) :
    ∃ P₀ P₁ : K[X], ∃ f : I → K,
      P₀.natDegree ≤ k - 1 ∧ P₁.natDegree ≤ k - 1 ∧
      (∀ i, sigma (f i) = f i) ∧
      (∀ i, u₀ i - P₀.eval (alpha i) = alpha i * f i) ∧
      (∀ i, u₁ i - P₁.eval (alpha i) = -f i) := by
  classical
  let R : Finset K := S.map beta
  let PR : K → K[X] := fun z ↦ P (Function.invFun beta z)
  have hleft : Function.LeftInverse (Function.invFun beta) beta :=
    Function.leftInverse_invFun beta.injective
  have hRcard : R.card = S.card := by simp [R]
  have hsigmaR : ∀ z ∈ R, sigma z = z ^ q := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hz
    exact hsigma t ht
  have hPRdegree : ∀ z ∈ R, (PR z).natDegree ≤ k - 1 := by
    intro z hz
    obtain ⟨t, ht, htz⟩ := Finset.mem_map.mp hz
    subst z
    simpa [PR, hleft t] using hPdegree t ht
  have hPRrel : ∀ z ∈ R, ∀ i,
      (alpha i - z) *
          sigma (u₀ i + z * u₁ i - (PR z).eval (alpha i)) =
        (alpha i - sigma z) *
          (u₀ i + z * u₁ i - (PR z).eval (alpha i)) := by
    intro z hz i
    obtain ⟨t, ht, htz⟩ := Finset.mem_map.mp hz
    subst z
    simpa [PR, hleft t] using hrel t ht i
  apply exists_affineParticular_of_many_canonicalMovingOwners sigma alpha
    u₀ u₁ R PR q k hq hk hsix horder hsigmaR hfixed halpha hcard
  · simpa [hRcard] using howners
  · exact hPRdegree
  · exact hPRrel
theorem receivedZero_eq_normalizedCombination
    {K I : Type*} [Field K]
    (a₀ a₁ b₀ b₁ : K) (u₀ u₁ : I → K) (i : I)
    (hdet : affinePencilDet a₀ a₁ b₀ b₁ ≠ 0) :
    u₀ i = b₀ * normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁ i -
      a₀ * normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁ i := by
  symm
  calc
    b₀ * normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁ i -
        a₀ * normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁ i =
      (affinePencilDet a₀ a₁ b₀ b₁)⁻¹ *
        (affinePencilDet a₀ a₁ b₀ b₁ * u₀ i) := by
          dsimp [normalizedReceivedZero, normalizedReceivedOne,
            affinePencilDet]
          ring
    _ = u₀ i := by
      rw [← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
theorem receivedOne_eq_normalizedCombination
    {K I : Type*} [Field K]
    (a₀ a₁ b₀ b₁ : K) (u₀ u₁ : I → K) (i : I)
    (hdet : affinePencilDet a₀ a₁ b₀ b₁ ≠ 0) :
    u₁ i = b₁ * normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁ i -
      a₁ * normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁ i := by
  symm
  calc
    b₁ * normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁ i -
        a₁ * normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁ i =
      (affinePencilDet a₀ a₁ b₀ b₁)⁻¹ *
        (affinePencilDet a₀ a₁ b₀ b₁ * u₁ i) := by
          dsimp [normalizedReceivedZero, normalizedReceivedOne,
            affinePencilDet]
          ring
    _ = u₁ i := by
      rw [← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
theorem exists_affineParticular_of_many_affinePencilOwners
    {K I T : Type*} [Field K] [Fintype I] [DecidableEq I]
    [DecidableEq K] [DecidableEq T] [Nonempty T]
    (sigma : K →+* K) (alpha : I ↪ K) (u₀ u₁ : I → K)
    (tau : T ↪ K) (S : Finset T) (P : T → K[X])
    (a₀ a₁ b₀ b₁ : K) (q k : Nat)
    (hq : 1 < q) (hk : 0 < k)
    (hsix : (6 : K) ≠ 0)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hdet : affinePencilDet a₀ a₁ b₀ b₁ ≠ 0)
    (hden : ∀ t, b₀ + tau t * b₁ ≠ 0)
    (hsigma : ∀ t ∈ S,
      sigma (affinePencilRoot a₀ a₁ b₀ b₁ (tau t)) =
        affinePencilRoot a₀ a₁ b₀ b₁ (tau t) ^ q)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (halpha : ∀ i, alpha i ≠ 0)
    (hcard : k + 2 < Fintype.card I)
    (howners : q + 1 < S.card)
    (hPdegree : ∀ t ∈ S, (P t).natDegree ≤ k - 1)
    (hrel : ∀ t ∈ S, ∀ i,
      ((a₀ + tau t * a₁) + (b₀ + tau t * b₁) * alpha i) *
          sigma (u₀ i + tau t * u₁ i - (P t).eval (alpha i)) =
        sigma ((a₀ + tau t * a₁) +
          (b₀ + tau t * b₁) * alpha i) *
          (u₀ i + tau t * u₁ i - (P t).eval (alpha i))) :
    ∃ P₀ P₁ : K[X], ∃ f : I → K,
      P₀.natDegree ≤ k - 1 ∧ P₁.natDegree ≤ k - 1 ∧
      (∀ i, sigma (f i) = f i) ∧
      (∀ i, u₀ i - P₀.eval (alpha i) =
        (a₀ + b₀ * alpha i) * f i) ∧
      (∀ i, u₁ i - P₁.eval (alpha i) =
        (a₁ + b₁ * alpha i) * f i) := by
  classical
  let beta : T ↪ K :=
    ⟨fun t ↦ affinePencilRoot a₀ a₁ b₀ b₁ (tau t), by
      intro t v htv
      apply tau.injective
      exact affinePencilRoot_injective a₀ a₁ b₀ b₁ (tau t) (tau v)
        hdet (hden t) (hden v) htv⟩
  let v₀ : I → K :=
    normalizedReceivedZero a₀ a₁ b₀ b₁ u₀ u₁
  let v₁ : I → K :=
    normalizedReceivedOne a₀ a₁ b₀ b₁ u₀ u₁
  let PN : T → K[X] := fun t ↦
    Polynomial.C (b₀ + tau t * b₁)⁻¹ * P t
  have hPNdegree : ∀ t ∈ S, (PN t).natDegree ≤ k - 1 := by
    intro t ht
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hPdegree t ht)
  have hnormalized : ∀ t ∈ S, ∀ i,
      (alpha i - beta t) *
          sigma (v₀ i + beta t * v₁ i - (PN t).eval (alpha i)) =
        (alpha i - sigma (beta t)) *
          (v₀ i + beta t * v₁ i - (PN t).eval (alpha i)) := by
    intro t ht i
    let E := u₀ i + tau t * u₁ i - (P t).eval (alpha i)
    have hnorm := normalize_affinePencil_relation_at sigma (alpha i) E
      a₀ a₁ b₀ b₁ (tau t) (hden t) (hfixed i) (hrel t ht i)
    have hword := affineReceived_eq_leading_mul_normalized
      a₀ a₁ b₀ b₁ (tau t) u₀ u₁ i hdet (hden t)
    have hdisc :
        E / (b₀ + tau t * b₁) =
          v₀ i + beta t * v₁ i - (PN t).eval (alpha i) := by
      dsimp [E, v₀, v₁, beta, PN]
      rw [hword]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      field_simp [hden t]
    simpa [beta, hdisc] using hnorm
  obtain ⟨Q₀, Q₁, f, hQ₀, hQ₁, hf, hv₀, hv₁⟩ :=
    exists_affineParticular_of_many_embeddedCanonicalMovingOwners sigma alpha
      v₀ v₁ beta S PN q k hq hk hsix horder hsigma hfixed halpha
      hcard howners hPNdegree hnormalized
  let P₀ := Polynomial.C b₀ * Q₀ - Polynomial.C a₀ * Q₁
  let P₁ := Polynomial.C b₁ * Q₀ - Polynomial.C a₁ * Q₁
  have hP₀ : P₀.natDegree ≤ k - 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans hQ₀)
      ((Polynomial.natDegree_C_mul_le _ _).trans hQ₁)
  have hP₁ : P₁.natDegree ≤ k - 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans hQ₀)
      ((Polynomial.natDegree_C_mul_le _ _).trans hQ₁)
  refine ⟨P₀, P₁, f, hP₀, hP₁, hf, ?_, ?_⟩
  · intro i
    have hu := receivedZero_eq_normalizedCombination
      a₀ a₁ b₀ b₁ u₀ u₁ i hdet
    dsimp [P₀]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, hu]
    dsimp [v₀, v₁] at hv₀ hv₁ ⊢
    linear_combination b₀ * hv₀ i - a₀ * hv₁ i
  · intro i
    have hu := receivedOne_eq_normalizedCombination
      a₀ a₁ b₀ b₁ u₀ u₁ i hdet
    dsimp [P₁]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, hu]
    dsimp [v₀, v₁] at hv₀ hv₁ ⊢
    linear_combination b₁ * hv₀ i - a₁ * hv₁ i
end BCHKSFrobeniusLinearReceivedLift6401
end ProximityPrize.SubmissionLower
