import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusTripleLight6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankTwoClosure6401
open Polynomial
open scoped BigOperators
open ProximityPrize.Benchmark
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoLedger6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
open BCHKSTwoFrobeniusTripleLight6401
open BCHKSTwoFrobeniusSymbolicKernel6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
theorem receivedFrobeniusZ_natDegree_le {F : Type*} [Field F]
    (sigma : F →+* F) (u₀ u₁ : F) :
    (receivedFrobeniusZ sigma u₀ u₁).natDegree ≤ q6401 := by
  unfold receivedFrobeniusZ
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_monomial_le _
theorem symbolicCoordinateRelation_coefficientRowMap_natDegree_lt
    {F : Type*} [Field F] (sigma : F →+* F) (x u₀ u₁ : F)
    (c : SymbolicCoefficients F) :
    (symbolicCoordinateRelation sigma x u₀ u₁
      (coefficientRowMap c)).natDegree < symbolicDepth6401 := by
  have h0 : (evalOuterAt x ((coefficientRowMap c) 0)).natDegree ≤
      symbolicDepth6401 - 1 := by
    simpa [coefficientRowMap] using
      evalOuterAt_boxPolynomialMap_natDegree_le x a0XSlots6401
        symbolicDepth6401 c.1
  have h1 : (evalOuterAt x ((coefficientRowMap c) 1)).natDegree ≤
      symbolicDepthOne6401 - 1 := by
    simpa [coefficientRowMap] using
      evalOuterAt_boxPolynomialMap_natDegree_le x a1XSlots6401
        symbolicDepthOne6401 c.2.1
  have h2 : (evalOuterAt x ((coefficientRowMap c) 2)).natDegree ≤
      symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      evalOuterAt_boxPolynomialMap_natDegree_le x a2XSlots6401
        symbolicDepthFrobenius6401 c.2.2
  have hZ : (receivedZ u₀ u₁).natDegree ≤ 1 := by
    simpa [receivedZ, affineValuePolynomial] using
      affineValuePolynomial_natDegree_le_one u₀ u₁
  have hF := receivedFrobeniusZ_natDegree_le sigma u₀ u₁
  unfold symbolicCoordinateRelation
  have hterm1 :
      (evalOuterAt x (coefficientRowMap c 1) * receivedZ u₀ u₁).natDegree ≤
        symbolicDepth6401 - 1 := by
    exact Polynomial.natDegree_mul_le.trans <|
      (Nat.add_le_add h1 hZ).trans <| by
        norm_num [symbolicDepth6401, symbolicDepthOne6401]
  have hterm2 :
      (evalOuterAt x (coefficientRowMap c 2) *
        receivedFrobeniusZ sigma u₀ u₁).natDegree ≤
          symbolicDepth6401 - 1 := by
    exact Polynomial.natDegree_mul_le.trans <|
      (Nat.add_le_add h2 hF).trans <| by
        norm_num [symbolicDepth6401, symbolicDepthFrobenius6401, q6401]
  have hall :
      ((evalOuterAt x (coefficientRowMap c 0) +
          evalOuterAt x (coefficientRowMap c 1) * receivedZ u₀ u₁) +
        evalOuterAt x (coefficientRowMap c 2) *
          receivedFrobeniusZ sigma u₀ u₁).natDegree ≤
          symbolicDepth6401 - 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le h0 hterm1)
    · exact hterm2
  exact hall.trans_lt (by norm_num [symbolicDepth6401])
theorem kernel_coordinate_relation_eq_zero
    {F : Type*} [Field F] (sigma : F →+* F)
    (alpha : Fin n6401 → F) (u₀ u₁ : Fin n6401 → F)
    (c : SymbolicKernel sigma alpha u₀ u₁) (i : Fin n6401) :
    symbolicCoordinateRelation sigma (alpha i) (u₀ i) (u₁ i)
      (coefficientRowMap c.1) = 0 := by
  let R := symbolicCoordinateRelation sigma (alpha i) (u₀ i) (u₁ i)
    (coefficientRowMap c.1)
  have hdegree : R.natDegree < symbolicDepth6401 :=
    symbolicCoordinateRelation_coefficientRowMap_natDegree_lt
      sigma (alpha i) (u₀ i) (u₁ i) c.1
  apply Polynomial.ext
  intro n
  by_cases hn : n < symbolicDepth6401
  · let nf : Fin symbolicDepth6401 := ⟨n, hn⟩
    have hc := LinearMap.mem_ker.mp c.property
    have hfun := congrFun hc (i, nf)
    simpa [R, nf, symbolicConstraintMap] using hfun
  · rw [Polynomial.coeff_zero]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    change R.natDegree < n
    exact hdegree.trans_le (Nat.le_of_not_gt hn)
theorem eval_receivedFrobeniusZ
    {F : Type*} [Field F] (sigma : F →+* F) (z u₀ u₁ : F)
    (hsigma : sigma z = z ^ q6401) :
    Polynomial.eval z (receivedFrobeniusZ sigma u₀ u₁) =
      sigma (u₀ + z * u₁) := by
  simp only [receivedFrobeniusZ, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_monomial, map_add, map_mul]
  rw [hsigma]
  ring
theorem kernel_specialized_value_relation
    {F : Type*} [Field F] (sigma : F →+* F)
    (alpha : Fin n6401 → F) (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (c : SymbolicKernel sigma alpha u₀ u₁)
    (z : F) (i : Fin n6401) :
    Polynomial.eval (alpha i) (specializeRow z (coefficientRowMap c.1) 0) +
      Polynomial.eval (alpha i) (specializeRow z (coefficientRowMap c.1) 1) *
        (u₀ i + z * u₁ i) +
      Polynomial.eval (alpha i) (specializeRow z (coefficientRowMap c.1) 2) *
        sigma (u₀ i + z * u₁ i) = 0 := by
  have hzero := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ c i
  have heval := congrArg (Polynomial.eval z) hzero
  simp only [Polynomial.eval_zero] at heval
  unfold symbolicCoordinateRelation at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at heval
  rw [← eval_specializeCoeffZ_comm z (alpha i) ((coefficientRowMap c.1) 0),
    ← eval_specializeCoeffZ_comm z (alpha i) ((coefficientRowMap c.1) 1),
    ← eval_specializeCoeffZ_comm z (alpha i) ((coefficientRowMap c.1) 2)] at heval
  have hZ : Polynomial.eval z (receivedZ (u₀ i) (u₁ i)) =
      u₀ i + z * u₁ i := by
    simp [receivedZ]
    ring
  rw [hZ, eval_receivedFrobeniusZ sigma z (u₀ i) (u₁ i) (hsigma z)] at heval
  exact heval
theorem specialized_symbolicRelation_coefficientRowMap_natDegree_le
    {F : Type*} [Field F] (sigma : F →+* F)
    (c : SymbolicCoefficients F) (z : F) (P : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401) :
    (symbolicRelation sigma (specializeRow z (coefficientRowMap c)) P).natDegree ≤
      174762 := by
  have h0 : (specializeRow z (coefficientRowMap c) 0).natDegree ≤ 174762 := by
    exact Polynomial.natDegree_map_le.trans <| by
      simpa [coefficientRowMap, specializeRow, a0XSlots6401] using
        boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401 c.1
  have h1c : (specializeRow z (coefficientRowMap c) 1).natDegree ≤ 43691 := by
    exact Polynomial.natDegree_map_le.trans <| by
      simpa [coefficientRowMap, specializeRow, a1XSlots6401] using
        boxPolynomialMap_natDegree_le a1XSlots6401 symbolicDepthOne6401 c.2.1
  have h2c : (specializeRow z (coefficientRowMap c) 2).natDegree ≤ 43691 := by
    exact Polynomial.natDegree_map_le.trans <| by
      simpa [coefficientRowMap, specializeRow, a2XSlots6401] using
        boxPolynomialMap_natDegree_le a2XSlots6401
          symbolicDepthFrobenius6401 c.2.2
  have h1 : (specializeRow z (coefficientRowMap c) 1 * P).natDegree ≤
      174762 := Polynomial.natDegree_mul_le.trans (by
        norm_num [ownerDegreeCap6401] at hP ⊢
        omega)
  have hPmap : (P.map sigma).natDegree ≤ ownerDegreeCap6401 :=
    Polynomial.natDegree_map_le.trans hP
  have h2 : (specializeRow z (coefficientRowMap c) 2 * P.map sigma).natDegree ≤
      174762 := Polynomial.natDegree_mul_le.trans (by
        norm_num [ownerDegreeCap6401] at hPmap ⊢
        omega)
  unfold symbolicRelation
  exact (Polynomial.natDegree_add_le _ _).trans <| max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le h0 h1)) h2
theorem kernel_symbolicRelation_eq_zero_of_owner
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (c : SymbolicKernel sigma alpha u₀ u₁)
    (z : F) (A : Finset (Fin n6401)) (P : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ i ∈ A,
      Polynomial.eval (alpha i) P = u₀ i + z * u₁ i)
    (hcard : a6401 ≤ A.card) :
    symbolicRelation sigma (specializeRow z (coefficientRowMap c.1)) P = 0 := by
  classical
  let roots : Finset F := A.map alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (symbolicRelation sigma (specializeRow z (coefficientRowMap c.1)) P) roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hvalue := kernel_specialized_value_relation
      sigma alpha u₀ u₁ hsigma c z i
    have hown := howner i hi
    have htwist := eval_twist_of_fixed sigma (alpha i) (hfixed i) P
    unfold symbolicRelation
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hown, show Polynomial.eval (alpha i) (P.map sigma) =
        sigma (Polynomial.eval (alpha i) P) by
          simpa [twist] using htwist,
      hown]
    exact hvalue
  · rw [Finset.card_map]
    have hdeg := specialized_symbolicRelation_coefficientRowMap_natDegree_le
      sigma c.1 z P hP
    norm_num [a6401] at hcard
    exact hdeg.trans_lt (by omega)
theorem natDegree_det_le_sum_colCaps
    {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (M : Matrix J J (Polynomial R)) (cap : J → ℕ)
    (hentry : ∀ i j, (M i j).natDegree ≤ cap j) :
    M.det.natDegree ≤ ∑ j, cap j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _hσ
  apply (Polynomial.natDegree_smul_le _ _).trans
  calc
    (∏ j, M (σ j) j).natDegree ≤ ∑ j, (M (σ j) j).natDegree := by
      simpa using Polynomial.natDegree_prod_le (Finset.univ : Finset J)
        (fun j => M (σ j) j)
    _ ≤ ∑ j, cap j := Finset.sum_le_sum fun j _ => hentry (σ j) j
theorem swap_symbolicDeterminant_coefficientRows_natDegree_le
    {F : Type*} [Field F] (c : Fin 3 → SymbolicCoefficients F) :
    (Polynomial.Bivariate.swap
      (symbolicDeterminant fun i => coefficientRowMap (c i))).natDegree ≤
        rankThreeDetZCap6401 := by
  let M : Matrix (Fin 3) (Fin 3) (XOverZ F) := fun i j =>
    Polynomial.Bivariate.swap (coefficientRowMap (c i) j)
  have hdet : Polynomial.Bivariate.swap
      (symbolicDeterminant fun i => coefficientRowMap (c i)) = M.det := by
    rw [symbolicDeterminant, Polynomial.Bivariate.swap.map_det]
    rfl
  rw [hdet]
  let cap : Fin 3 → ℕ := ![
    symbolicDepth6401 - 1,
    symbolicDepthOne6401 - 1,
    symbolicDepthFrobenius6401 - 1]
  refine (natDegree_det_le_sum_colCaps M cap ?_).trans ?_
  · intro i j
    fin_cases j
    · simpa [M, cap, coefficientRowMap] using
        swap_boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401
          (c i).1
    · simpa [M, cap, coefficientRowMap] using
        swap_boxPolynomialMap_natDegree_le a1XSlots6401 symbolicDepthOne6401
          (c i).2.1
    · simpa [M, cap, coefficientRowMap] using
        swap_boxPolynomialMap_natDegree_le a2XSlots6401
          symbolicDepthFrobenius6401 (c i).2.2
  · simp [cap, Fin.sum_univ_three]
    norm_num [symbolicDepth6401, symbolicDepthOne6401,
      symbolicDepthFrobenius6401, rankThreeDetZCap6401,
      balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
      a1XSlots6401, q6401]
theorem coeff_natDegree_le_swap_natDegree
    {F : Type*} [Field F] (P : XOverZ F) (n : ℕ) :
    (P.coeff n).natDegree ≤ (Polynomial.Bivariate.swap P).natDegree := by
  by_cases hc : P.coeff n = 0
  · simp [hc]
  · have hn : n ∈ P.support := Polynomial.mem_support_iff.mpr hc
    have hle : (P.coeff n).natDegree ≤ Polynomial.Bivariate.degreeX P :=
      Finset.le_sup (f := fun k => (P.coeff k).natDegree) hn
    have heq : Polynomial.Bivariate.degreeX P =
        (Polynomial.Bivariate.swap P).natDegree := by
      have h := Polynomial.Bivariate.degreeX_swap
        (Polynomial.Bivariate.swap P)
      rw [Polynomial.Bivariate.swap_swap_apply] at h
      simpa [Polynomial.Bivariate.natDegreeY] using h
    exact hle.trans_eq heq
theorem kernelTriple_owner_card_le_rankThreeDetZCap6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (c : Fin 3 → SymbolicKernel sigma alpha u₀ u₁)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hdet : symbolicDeterminant
      (fun i => coefficientRowMap (c i).1) ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i) :
    S.card ≤ rankThreeDetZCap6401 := by
  classical
  let T : XOverZ F := symbolicDeterminant
    (fun i => coefficientRowMap (c i).1)
  have hzero : ∀ z ∈ S, specializeCoeffZ z T = 0 := by
    intro z hz
    apply specialize_symbolicDeterminant_eq_zero_of_owner sigma z
      (fun i => coefficientRowMap (c i).1) (P z)
    intro i
    exact kernel_symbolicRelation_eq_zero_of_owner
      sigma alpha u₀ u₁ hsigma hfixed (c i) z (A z) (P z)
        (hPdegree z hz) (howner z hz) (hrow z hz)
  obtain ⟨a, _ha, hcard⟩ :=
    card_zero_specializations_le_coefficient_degree S T (by
      simpa [T] using hdet)
  have hfilter : (S.filter fun z => specializeCoeffZ z T = 0) = S :=
    Finset.filter_eq_self.mpr hzero
  rw [hfilter] at hcard
  exact hcard.trans <| (coeff_natDegree_le_swap_natDegree T a).trans <| by
    simpa [T] using
      swap_symbolicDeterminant_coefficientRows_natDegree_le
        (fun i => (c i).1)
theorem rationalCoordinateMismatch_eval_eq_zero_of_owner
    {F : Type*} [Field F]
    (D N : XOverZ F) (z x u₀ u₁ : F) (P : Polynomial F)
    (hbranch : specializeCoeffZ z D * P = -specializeCoeffZ z N)
    (howner : Polynomial.eval x P = u₀ + z * u₁) :
    Polynomial.eval z (rationalCoordinateMismatch D N x u₀ u₁) = 0 := by
  have heval := congrArg (Polynomial.eval x) hbranch
  simp only [Polynomial.eval_mul, Polynomial.eval_neg] at heval
  rw [eval_specializeCoeffZ_comm z x D,
    eval_specializeCoeffZ_comm z x N] at heval
  unfold rationalCoordinateMismatch affineValuePolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [← howner]
  linear_combination heval
theorem rational_owner_card_mul_agreement_sub_identity_le
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D N : XOverZ F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (a mismatchCap : ℕ)
    (hrow : ∀ z ∈ S, a ≤ (A z).card)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z D * P z = -specializeCoeffZ z N)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hdegree : ∀ i : ι,
      (rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        mismatchCap) :
    S.card *
        (a - (rationalIdentityCoordinates D N alpha u₀ u₁ Finset.univ).card) ≤
      Fintype.card ι * mismatchCap := by
  classical
  let H : Finset ι :=
    rationalIdentityCoordinates D N alpha u₀ u₁ Finset.univ
  let E : F → Finset ι := fun z => A z \ H
  let fib : ι → ℕ := fun i => (S.filter fun z => i ∈ E z).card
  have hrow' : ∀ z ∈ S, a - H.card ≤ (E z).card := by
    intro z hz
    have hdiff := Finset.le_card_sdiff H (A z)
    exact (Nat.sub_le_sub_right (hrow z hz) H.card).trans hdiff
  have hlower : S.card * (a - H.card) ≤
      ∑ z ∈ S, (E z).card := by
    calc
      S.card * (a - H.card) = ∑ _z ∈ S, (a - H.card) := by simp
      _ ≤ ∑ z ∈ S, (E z).card := Finset.sum_le_sum hrow'
  have hswap : (∑ z ∈ S, (E z).card) = ∑ i : ι, fib i :=
    sum_card_eq_sum_fiber_card S E
  have hfib : ∀ i : ι, fib i ≤ mismatchCap := by
    intro i
    by_cases hi : i ∈ H
    · have hempty : S.filter (fun z => i ∈ E z) = ∅ := by
        ext z
        simp [E, hi]
      simp [fib, hempty]
    · have hnonzero :
          rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i) ≠ 0 := by
        simpa [H, rationalIdentityCoordinates] using hi
      have hsub : S.filter (fun z => i ∈ E z) ⊆
          S.filter fun z => Polynomial.eval z
            (rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i)) = 0 := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        refine ⟨hz.1, ?_⟩
        exact rationalCoordinateMismatch_eval_eq_zero_of_owner
          D N z (alpha i) (u₀ i) (u₁ i) (P z)
            (hbranch z hz.1) (howner z hz.1 i (Finset.mem_sdiff.mp hz.2).1)
      calc
        fib i ≤ (S.filter fun z => Polynomial.eval z
              (rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i)) = 0).card :=
          Finset.card_le_card hsub
        _ ≤ (rationalCoordinateMismatch D N
              (alpha i) (u₀ i) (u₁ i)).natDegree :=
          card_filter_eval_eq_zero_le_natDegree S _ hnonzero
        _ ≤ mismatchCap := hdegree i
  calc
    S.card *
        (a - (rationalIdentityCoordinates D N alpha u₀ u₁ Finset.univ).card) =
        S.card * (a - H.card) := by rfl
    _ ≤ ∑ z ∈ S, (E z).card := hlower
    _ = ∑ i : ι, fib i := hswap
    _ ≤ ∑ _i : ι, mismatchCap := Finset.sum_le_sum fun i _ => hfib i
    _ = Fintype.card ι * mismatchCap := by simp
theorem rational_owner_card_le_rankTwoIncidenceOwnerCap6401
    {F ι : Type} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (D N : XOverZ F) (alpha u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hidentity :
      (rationalIdentityCoordinates D N alpha u₀ u₁ Finset.univ).card ≤
        rankTwoIdentityIncidenceCutoff6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hbranch : ∀ z ∈ S,
      specializeCoeffZ z D * P z = -specializeCoeffZ z N)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hdegree : ∀ i : ι,
      (rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i)).natDegree ≤
        rankTwoMismatchZCap6401) :
    S.card ≤ rankTwoIncidenceOwnerCap6401 := by
  have hinc := rational_owner_card_mul_agreement_sub_identity_le
    D N alpha u₀ u₁ S A P a6401 rankTwoMismatchZCap6401
      hrow hbranch howner hdegree
  have hgap : 60 ≤
      a6401 -
        (rationalIdentityCoordinates D N alpha u₀ u₁ Finset.univ).card := by
    norm_num [a6401, rankTwoIdentityIncidenceCutoff6401] at hidentity ⊢
    omega
  rw [hcardι] at hinc
  rw [rankTwoIncidenceOwnerCap6401,
    Nat.le_div_iff_mul_le (by norm_num : 0 < 60)]
  exact (Nat.mul_le_mul_left S.card hgap).trans hinc
theorem lightChallenges_card_le_lineCap_of_no_direction6401
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F]
    (C : LinearCode ι F)
    (D N : XOverZ F) (alpha : ι ↪ F) (u₀ u₁ : ι → F)
    (I : Finset ι) (S : Finset F) (A : F → Finset ι)
    (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z))
    (p₀ p₁ : Polynomial F)
    (hp₀ : p₀.natDegree ≤ ownerDegreeCap6401)
    (hp₁ : p₁.natDegree ≤ ownerDegreeCap6401)
    (halign : ∀ z ∈ lightChallenges D alpha
      (rationalIdentityCoordinates D N alpha u₀ u₁ I) S
        tripleLightThreshold6401,
      P z = p₀ + Polynomial.C z * p₁) :
    (lightChallenges D alpha
      (rationalIdentityCoordinates D N alpha u₀ u₁ I) S
        tripleLightThreshold6401).card ≤ tripleLightLineCap6401 := by
  classical
  let L := lightChallenges D alpha
    (rationalIdentityCoordinates D N alpha u₀ u₁ I) S
      tripleLightThreshold6401
  by_contra hnot
  have hLlarge : bchksErrors6401 + 1 < L.card := by
    norm_num [tripleLightLineCap6401, bchksErrors6401] at hnot ⊢
    omega
  let U : Fin 2 → ι → F := ![u₀, u₁]
  let p : Fin 2 → ι → F := ![
    fun i => Polynomial.eval (alpha i) p₀,
    fun i => Polynomial.eval (alpha i) p₁]
  obtain ⟨z, hzL, hzdir⟩ :=
    exists_direction_projection_of_affine_owner_alignment
      C U p L A bchksErrors6401 hLlarge
      (by
        intro z hz
        have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
        rw [hcardι]
        have := hrow z hzS
        norm_num [n6401, a6401, bchksErrors6401] at this ⊢
        exact this)
      (by
        intro j
        fin_cases j
        · exact hcode p₀ hp₀
        · exact hcode p₁ hp₁)
      (by
        intro z hz i hi
        have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
        have hline : P z = p₀ + Polynomial.C z * p₁ := by
          exact halign z (by simpa [L] using hz)
        have heval := congrArg (Polynomial.eval (alpha i)) hline
        have hagree := howner z hzS i hi
        dsimp [U, p]
        rw [← hagree]
        simpa using heval)
  have hzS : z ∈ S := (Finset.mem_filter.mp hzL).1
  exact hnoDirection z hzS (by simpa [U] using hzdir)
theorem coefficientRows_owner_card_le_mca_of_no_direction6401
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F]
    (C : LinearCode ι F) (sigma : F →+* F)
    (c d : SymbolicCoefficients F) (alpha : ι ↪ F)
    (u₀ u₁ : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c) (coefficientRowMap d) ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hc : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap c)) (P z) = 0)
    (hd : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap d)) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z)) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 := by
  classical
  let D := symbolicRankTwoDenominator
    (coefficientRowMap c) (coefficientRowMap d)
  let N := symbolicRankTwoNumerator
    (coefficientRowMap c) (coefficientRowMap d)
  let R := primitiveRationalFrame D N alpha Finset.univ (by simpa [D] using hden)
  have hDswap : (Polynomial.Bivariate.swap D).natDegree ≤
      rankTwoDenomZCap6401 := by
    simpa [D] using swap_coefficientRowMap_denominator_natDegree_le c d
  have hNswap : (Polynomial.Bivariate.swap N).natDegree ≤
      rankTwoMismatchZCap6401 := by
    simpa [N] using swap_coefficientRowMap_numerator_natDegree_le c d
  have hbranch : ∀ z ∈ S,
      specializeCoeffZ z R.denominator * P z =
        -specializeCoeffZ z R.numerator := by
    intro z hz
    apply R.cancel_specialized_owner z (P z)
    exact specialized_rankTwo_owner_identity sigma z
      (coefficientRowMap c) (coefficientRowMap d) (P z)
        (hc z hz) (hd z hz)
  have hmismatchDegree : ∀ i : ι,
      (rationalCoordinateMismatch R.denominator R.numerator
        (alpha i) (u₀ i) (u₁ i)).natDegree ≤
          rankTwoMismatchZCap6401 := by
    intro i
    have h := R.rationalCoordinateMismatch_natDegree_le
      (alpha i) (u₀ i) (u₁ i)
        rankTwoDenomZCap6401 rankTwoMismatchZCap6401 hDswap hNswap
    simpa [rankTwoDenomZCap6401, rankTwoMismatchZCap6401,
      balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
      a1XSlots6401, q6401] using h
  by_cases hsmall :
      (rationalIdentityCoordinates R.denominator R.numerator
        alpha u₀ u₁ Finset.univ).card ≤
          rankTwoIdentityIncidenceCutoff6401
  · exact (rational_owner_card_le_rankTwoIncidenceOwnerCap6401
      R.denominator R.numerator alpha u₀ u₁ S A P hcardι hsmall
        hrow hbranch howner hmismatchDegree).trans
      (Nat.le_of_lt rankTwo_identity_incidence_ledger_exact6401.2.2.2.1)
  · have hlarge : 185295 ≤
        (rationalIdentityCoordinates R.denominator R.numerator
          alpha u₀ u₁ Finset.univ).card := by
      norm_num [rankTwoIdentityIncidenceCutoff6401] at hsmall ⊢
      omega
    have hactive : ∀ i ∈
        rationalIdentityCoordinates R.denominator R.numerator
          alpha u₀ u₁ Finset.univ,
        evalOuterAt (alpha i) R.denominator ≠ 0 := by
      intro i hi hDzero
      have hmismatch : rationalCoordinateMismatch R.denominator R.numerator
          (alpha i) (u₀ i) (u₁ i) = 0 := by
        simpa [rationalIdentityCoordinates] using hi
      unfold rationalCoordinateMismatch at hmismatch
      rw [hDzero, zero_mul, zero_add] at hmismatch
      exact R.primitive_at_coordinates i (Finset.mem_univ i)
        ⟨hDzero, hmismatch⟩
    have hlargeCap := ownerFamily_card_le_tripleLightTotalCap6401
      R.denominator R.numerator alpha u₀ u₁ Finset.univ S P
      (by rw [hcardι]) hlarge hactive
      (by
        intro i hi
        exact R.evalOuterAt_denominator_natDegree_le
          (alpha i) rankTwoDenomZCap6401 hDswap)
      hPdegree hbranch
      (by
        intro p₀ p₁ hp₀ hp₁ halign
        exact lightChallenges_card_le_lineCap_of_no_direction6401
          C R.denominator R.numerator alpha u₀ u₁ Finset.univ
            S A P hcardι hrow howner hcode hnoDirection
              p₀ p₁ hp₀ hp₁ halign)
    exact hlargeCap.trans
      (Nat.le_of_lt tripleLight_ledger_exact6401.2.2.2.1)
theorem IRS_baseCode_eval_mem_of_natDegree_le6401
    (Q : Polynomial IRSProfile.Field)
    (hQ : Q.natDegree ≤ ownerDegreeCap6401) :
    (fun i => Polynomial.eval (IRSProfile.domain i) Q) ∈
      IRSProfile.baseCode := by
  change ReedSolomon.evalOnPoints IRSProfile.domain Q ∈
    ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
  apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
  by_cases hzero : Q = 0
  · rw [hzero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · apply (Polynomial.natDegree_lt_iff_degree_lt hzero).1
    norm_num [ownerDegreeCap6401, IRSProfile.baseDimension] at hQ ⊢
    omega
theorem coefficientRows_IRS_owner_card_le_mca_of_no_direction6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (c d : SymbolicCoefficients IRSProfile.Field)
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c) (coefficientRowMap d) ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hc : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap c)) (P z) = 0)
    (hd : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap d)) (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u₀ i + z * u₁ i)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (A z)) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 := by
  apply coefficientRows_owner_card_le_mca_of_no_direction6401
    IRSProfile.baseCode sigma c d IRSProfile.domain u₀ u₁ S A P
  · norm_num [IRSProfile.Index, n6401]
  · exact hden
  · exact hPdegree
  · exact hrow
  · exact hc
  · exact hd
  · exact howner
  · exact IRS_baseCode_eval_mem_of_natDegree_le6401
  · exact hnoDirection
def SymbolicA1A2RankOneResidual6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F) : Prop :=
  ∀ c d : SymbolicKernel sigma alpha u₀ u₁,
    symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) = 0
theorem kernelPair_owner_card_le_mca_of_no_direction6401
    {F : Type} [Field F] [DecidableEq F]
    (C : LinearCode (Fin n6401) F)
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (c d : SymbolicKernel sigma alpha u₀ u₁)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) ≠ 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z)) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 := by
  apply coefficientRows_owner_card_le_mca_of_no_direction6401
    C sigma c.1 d.1 alpha u₀ u₁ S A P
  · exact Fintype.card_fin _
  · exact hden
  · exact hPdegree
  · exact hrow
  · intro z hz
    exact kernel_symbolicRelation_eq_zero_of_owner
      sigma alpha u₀ u₁ hsigma hfixed c z (A z) (P z)
        (hPdegree z hz) (howner z hz) (hrow z hz)
  · intro z hz
    exact kernel_symbolicRelation_eq_zero_of_owner
      sigma alpha u₀ u₁ hsigma hfixed d z (A z) (P z)
        (hPdegree z hz) (howner z hz) (hrow z hz)
  · exact howner
  · exact hcode
  · exact hnoDirection
theorem symbolicKernel_det_rankTwo_or_A1A2RankOne6401
    {F : Type} [Field F] [DecidableEq F]
    (C : LinearCode (Fin n6401) F)
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z)) :
    (∃ q : Fin 3 → SymbolicKernel sigma alpha u₀ u₁,
      LinearIndependent F q ∧
      symbolicDeterminant (fun i => coefficientRowMap (q i).1) ≠ 0 ∧
      S.card ≤ rankThreeDetZCap6401) ∨
    (∃ c d : SymbolicKernel sigma alpha u₀ u₁,
      symbolicRankTwoDenominator
        (coefficientRowMap c.1) (coefficientRowMap d.1) ≠ 0 ∧
      S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401) ∨
    SymbolicA1A2RankOneResidual6401 sigma alpha u₀ u₁ := by
  classical
  obtain ⟨q, hqIndependent⟩ :=
    exists_three_independent_symbolicKernel_coefficients sigma alpha u₀ u₁
  by_cases hdet : symbolicDeterminant
      (fun i => coefficientRowMap (q i).1) ≠ 0
  · left
    refine ⟨q, hqIndependent, hdet, ?_⟩
    exact kernelTriple_owner_card_le_rankThreeDetZCap6401
      sigma alpha u₀ u₁ hsigma hfixed q S A P hdet
        hPdegree hrow howner
  · right
    by_cases hpair : ∃ c d : SymbolicKernel sigma alpha u₀ u₁,
        symbolicRankTwoDenominator
          (coefficientRowMap c.1) (coefficientRowMap d.1) ≠ 0
    · left
      obtain ⟨c, d, hden⟩ := hpair
      refine ⟨c, d, hden, ?_⟩
      exact kernelPair_owner_card_le_mca_of_no_direction6401
        C sigma alpha u₀ u₁ hsigma hfixed c d S A P hden
          hPdegree hrow howner hcode hnoDirection
    · right
      intro c d
      exact not_ne_iff.mp (fun hne => hpair ⟨c, d, hne⟩)
theorem symbolicKernel_owner_card_le_mca_or_A1A2RankOneResidual6401
    {F : Type} [Field F] [DecidableEq F]
    (C : LinearCode (Fin n6401) F)
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u₀ u₁ : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u₀ i + z * u₁ i)
    (hcode : ∀ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 →
      (fun i => Polynomial.eval (alpha i) Q) ∈ C)
    (hnoDirection : ∀ z ∈ S,
      LinearCode.projectedWord u₁ (A z) ∉
        LinearCode.projectedCodeSubmod C (A z)) :
    S.card ≤ BCHKSFinalConditional6401.mcaNumerator6401 ∨
      SymbolicA1A2RankOneResidual6401 sigma alpha u₀ u₁ := by
  rcases symbolicKernel_det_rankTwo_or_A1A2RankOne6401
      C sigma alpha u₀ u₁ hsigma hfixed S A P
        hPdegree hrow howner hcode hnoDirection with hdet | hrankTwo | hrankOne
  · left
    rcases hdet with ⟨_q, _hlinear, _hdet, hcard⟩
    have hrank : rankThreeDetZCap6401 = 93092694807894 :=
      rankThree_determinant_caps_exact6401.2.1
    have hmca : BCHKSFinalConditional6401.mcaNumerator6401 =
        274980728094349243 :=
      BCHKSFinalConditional6401.field_and_list_ledger_exact6401.1
    omega
  · left
    rcases hrankTwo with ⟨_c, _d, _hden, hcard⟩
    exact hcard
  · exact Or.inr hrankOne
end BCHKSTwoFrobeniusRankTwoClosure6401
end ProximityPrize.SubmissionLower
