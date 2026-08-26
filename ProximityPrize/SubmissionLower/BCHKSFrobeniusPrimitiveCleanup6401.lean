import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveDegreeDrop6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusPrimitiveCleanup6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveDegreeDrop6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
noncomputable def highCoefficientWindow
    {F : Type*} [Field F] (delta cap : Nat)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap))) :
    U →ₗ[F] (Fin (delta - 1) → F) where
  toFun H j := H.1.1.coeff (cap + 1 + j.1)
  map_add' H K := by
    funext j
    simp
  map_smul' a H := by
    funext j
    simp
theorem exists_nonzero_multiplier_natDegree_le
    {F : Type*} [Field F] (delta cap : Nat)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap)))
    (hdelta : 0 < delta) (hU : Module.finrank F U = delta) :
    ∃ H : U, H ≠ 0 ∧ H.1.1.natDegree ≤ cap := by
  classical
  let T := highCoefficientWindow delta cap U
  have htarget : Module.finrank F (Fin (delta - 1) → F) = delta - 1 := by
    simp
  have hnotinj : ¬Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hU, htarget] at hle
    omega
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := by
      intro x y hxy
      have hsub : x - y ∈ LinearMap.ker T := by
        rw [LinearMap.mem_ker]
        calc
          T (x - y) = T x - T y := map_sub T x y
          _ = 0 := sub_eq_zero.mpr hxy
      have hsubBot : x - y ∈ (⊥ : Submodule F U) := by
        rw [← hbot]
        exact hsub
      have hzero : x - y = 0 := by simpa using hsubBot
      exact sub_eq_zero.mp hzero
    exact hnotinj hinj
  obtain ⟨H, hHker, hH⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hwindow : ∀ j : Fin (delta - 1),
      H.1.1.coeff (cap + 1 + j.1) = 0 := by
    intro j
    have hzero := LinearMap.mem_ker.mp hHker
    exact congrFun hzero j
  have hdegreeLT : H.1.1.natDegree < delta + cap :=
    (Polynomial.natDegree_lt_iff_degree_lt (by
      intro hz
      apply hH
      apply Subtype.ext
      apply Subtype.ext
      exact hz)).2 (Polynomial.mem_degreeLT.mp H.1.2)
  refine ⟨H, hH, ?_⟩
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hntop : n < delta + cap
  · let j : Fin (delta - 1) := ⟨n - (cap + 1), by omega⟩
    have hj : cap + 1 + j.1 = n := by
      dsimp [j]
      omega
    simpa [hj] using hwindow j
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdegreeLT.trans_le (Nat.le_of_not_gt hntop))
def commonMultiplierZeroSet
    {F : Type*} [Field F] {s delta cap : Nat}
    (alpha : Fin s ↪ F)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap))) :
    Set (Fin s) :=
  {i | ∀ H : U, Polynomial.eval (alpha i) H.1.1 = 0}
noncomputable def multiplierZeroSet
    {F : Type*} [Field F] [DecidableEq F] {s delta cap : Nat}
    (alpha : Fin s ↪ F)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap)))
    (H : U) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun i => Polynomial.eval (alpha i) H.1.1 = 0
private theorem multiplierZeroSet_card_le_natDegree
    {F : Type*} [Field F] [DecidableEq F] {s delta cap : Nat}
    (alpha : Fin s ↪ F)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap)))
    (H : U) (hH : H ≠ 0) :
    (multiplierZeroSet alpha U H).card ≤ H.1.1.natDegree := by
  classical
  let roots : Finset F := (multiplierZeroSet alpha U H).map alpha
  have hpoly : H.1.1 ≠ 0 := by
    intro hz
    apply hH
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  have hsub : roots ⊆ H.1.1.roots.toFinset := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hpoly).2
    exact (Finset.mem_filter.mp hi).2
  calc
    (multiplierZeroSet alpha U H).card = roots.card :=
      (Finset.card_map alpha).symm
    _ ≤ H.1.1.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ H.1.1.roots.card := Multiset.toFinset_card_le _
    _ ≤ H.1.1.natDegree := Polynomial.card_roots' H.1.1
theorem exists_primitive_cleanup
    {F : Type*} [Field F] [DecidableEq F] {s delta cap : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F) (E : Fin s → F)
    (A B : Polynomial F)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap)))
    (hdelta : 0 < delta) (hU : Module.finrank F U = delta)
    (hrelation : ∀ H : U,
      TwoLaneFailureRelation sigma alpha E (H.1.1 * A) (H.1.1 * B)) :
    ∃ H : U, ∃ bad : Finset (Fin s),
      H ≠ 0 ∧ H.1.1.natDegree ≤ cap ∧
      commonMultiplierZeroSet alpha U ⊆ (bad : Set (Fin s)) ∧
        bad.card ≤ cap ∧
      ∀ i, i ∉ bad →
        Polynomial.eval (alpha i) A * sigma (E i) =
          Polynomial.eval (alpha i) B * E i := by
  classical
  obtain ⟨H, hH, hHdegree⟩ :=
    exists_nonzero_multiplier_natDegree_le delta cap U hdelta hU
  refine ⟨H, multiplierZeroSet alpha U H, hH, hHdegree, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi H⟩
  · exact (multiplierZeroSet_card_le_natDegree alpha U H hH).trans hHdegree
  · intro i hi
    have hHi : Polynomial.eval (alpha i) H.1.1 ≠ 0 := by
      intro hz
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz⟩
    have hrel := hrelation H i
    simp only [Polynomial.eval_mul] at hrel
    apply mul_left_cancel₀ hHi
    simpa [mul_assoc] using hrel
def scalarFrobeniusNormSix
    {F : Type*} [Field F] (sigma : F →+* F) (x : F) : F :=
  x * sigma x * sigma (sigma x) * sigma (sigma (sigma x)) *
    sigma (sigma (sigma (sigma x))) *
      sigma (sigma (sigma (sigma (sigma x))))
noncomputable def polynomialFrobeniusNormSix
    {F : Type*} [Field F] (sigma : F →+* F) (P : Polynomial F) :
    Polynomial F :=
  let P1 := P.map sigma
  let P2 := P1.map sigma
  let P3 := P2.map sigma
  let P4 := P3.map sigma
  let P5 := P4.map sigma
  P * P1 * P2 * P3 * P4 * P5
theorem scalarFrobeniusNormSix_eq_of_relation
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (a b e : F) (he : e ≠ 0)
    (hrel : a * sigma e = b * e) :
    scalarFrobeniusNormSix sigma a = scalarFrobeniusNormSix sigma b := by
  have he1 : sigma e ≠ 0 := by
    intro hz
    exact he (sigma.injective (by simpa using hz))
  have he2 : sigma (sigma e) ≠ 0 :=
    fun hz => he1 (sigma.injective (by simpa using hz))
  have he3 : sigma (sigma (sigma e)) ≠ 0 :=
    fun hz => he2 (sigma.injective (by simpa using hz))
  have he4 : sigma (sigma (sigma (sigma e))) ≠ 0 :=
    fun hz => he3 (sigma.injective (by simpa using hz))
  have he5 : sigma (sigma (sigma (sigma (sigma e)))) ≠ 0 :=
    fun hz => he4 (sigma.injective (by simpa using hz))
  have h1 := congrArg sigma hrel
  have h2 := congrArg sigma h1
  have h3 := congrArg sigma h2
  have h4 := congrArg sigma h3
  have h5 := congrArg sigma h4
  simp only [map_mul] at h1 h2 h3 h4 h5
  have hcycle := horder e
  have h5cycle :
      sigma (sigma (sigma (sigma (sigma a)))) * e =
        sigma (sigma (sigma (sigma (sigma b)))) *
          sigma (sigma (sigma (sigma (sigma e)))) := by
    simpa only [hcycle] using h5
  have hpaired :
      (a * sigma e) * (sigma a * sigma (sigma e)) *
          (sigma (sigma a) * sigma (sigma (sigma e))) *
          (sigma (sigma (sigma a)) * sigma (sigma (sigma (sigma e)))) *
          (sigma (sigma (sigma (sigma a))) *
            sigma (sigma (sigma (sigma (sigma e))))) *
          (sigma (sigma (sigma (sigma (sigma a)))) * e) =
        (b * e) * (sigma b * sigma e) *
          (sigma (sigma b) * sigma (sigma e)) *
          (sigma (sigma (sigma b)) * sigma (sigma (sigma e))) *
          (sigma (sigma (sigma (sigma b))) *
            sigma (sigma (sigma (sigma e)))) *
          (sigma (sigma (sigma (sigma (sigma b)))) *
            sigma (sigma (sigma (sigma (sigma e))))) := by
    rw [hrel, h1, h2, h3, h4, h5cycle]
  have hprod :
      scalarFrobeniusNormSix sigma a *
          (e * sigma e * sigma (sigma e) * sigma (sigma (sigma e)) *
            sigma (sigma (sigma (sigma e))) *
              sigma (sigma (sigma (sigma (sigma e))))) =
        scalarFrobeniusNormSix sigma b *
          (e * sigma e * sigma (sigma e) * sigma (sigma (sigma e)) *
            sigma (sigma (sigma (sigma e))) *
              sigma (sigma (sigma (sigma (sigma e))))) := by
    calc
      _ = (a * sigma e) * (sigma a * sigma (sigma e)) *
          (sigma (sigma a) * sigma (sigma (sigma e))) *
          (sigma (sigma (sigma a)) * sigma (sigma (sigma (sigma e)))) *
          (sigma (sigma (sigma (sigma a))) *
            sigma (sigma (sigma (sigma (sigma e))))) *
          (sigma (sigma (sigma (sigma (sigma a)))) * e) := by
            dsimp [scalarFrobeniusNormSix]
            ring
      _ = _ := hpaired
      _ = _ := by
        dsimp [scalarFrobeniusNormSix]
        ring
  apply mul_right_cancel₀ _ hprod
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero he he1) he2) he3) he4) he5
theorem polynomialFrobeniusNormSix_eval_of_fixed
    {F : Type*} [Field F] (sigma : F →+* F)
    (P : Polynomial F) (x : F) (hx : sigma x = x) :
    Polynomial.eval x (polynomialFrobeniusNormSix sigma P) =
      scalarFrobeniusNormSix sigma (Polynomial.eval x P) := by
  simp only [polynomialFrobeniusNormSix, Polynomial.eval_mul]
  have hmap : ∀ Q : Polynomial F,
      Polynomial.eval x (Q.map sigma) = sigma (Polynomial.eval x Q) := by
    intro Q
    calc
      Polynomial.eval x (Q.map sigma) =
          Polynomial.eval (sigma x) (Q.map sigma) := by rw [hx]
      _ = sigma (Polynomial.eval x Q) :=
        Polynomial.eval_map_apply (p := Q) sigma x
  repeat' rw [hmap]
  rfl
theorem polynomialFrobeniusNormSix_natDegree_le
    {F : Type*} [Field F] (sigma : F →+* F)
    (P : Polynomial F) (p : Nat) (hP : P.natDegree ≤ p) :
    (polynomialFrobeniusNormSix sigma P).natDegree ≤ 6 * p := by
  let P1 := P.map sigma
  let P2 := P1.map sigma
  let P3 := P2.map sigma
  let P4 := P3.map sigma
  let P5 := P4.map sigma
  have h1 : P1.natDegree ≤ p := Polynomial.natDegree_map_le.trans hP
  have h2 : P2.natDegree ≤ p := Polynomial.natDegree_map_le.trans h1
  have h3 : P3.natDegree ≤ p := Polynomial.natDegree_map_le.trans h2
  have h4 : P4.natDegree ≤ p := Polynomial.natDegree_map_le.trans h3
  have h5 : P5.natDegree ≤ p := Polynomial.natDegree_map_le.trans h4
  dsimp [P1, P2, P3, P4, P5] at h1 h2 h3 h4 h5
  dsimp [polynomialFrobeniusNormSix, P1, P2, P3, P4, P5]
  have h01 := Polynomial.natDegree_mul_le (p := P) (q := P.map sigma)
  have h012 := Polynomial.natDegree_mul_le
    (p := P * P.map sigma) (q := (P.map sigma).map sigma)
  have h0123 := Polynomial.natDegree_mul_le
    (p := P * P.map sigma * (P.map sigma).map sigma)
    (q := ((P.map sigma).map sigma).map sigma)
  have h01234 := Polynomial.natDegree_mul_le
    (p := P * P.map sigma * (P.map sigma).map sigma *
      ((P.map sigma).map sigma).map sigma)
    (q := (((P.map sigma).map sigma).map sigma).map sigma)
  have h012345 := Polynomial.natDegree_mul_le
    (p := P * P.map sigma * (P.map sigma).map sigma *
      ((P.map sigma).map sigma).map sigma *
        (((P.map sigma).map sigma).map sigma).map sigma)
    (q := ((((P.map sigma).map sigma).map sigma).map sigma).map sigma)
  omega
theorem normDifference_natDegree_le
    {F : Type*} [Field F] (sigma : F →+* F)
    (A B : Polynomial F) (p : Nat)
    (hA : A.natDegree ≤ p) (hB : B.natDegree ≤ p) :
    (polynomialFrobeniusNormSix sigma A -
      polynomialFrobeniusNormSix sigma B).natDegree ≤ 6 * p := by
  exact (Polynomial.natDegree_sub_le _ _).trans <|
    max_le (polynomialFrobeniusNormSix_natDegree_le sigma A p hA)
      (polynomialFrobeniusNormSix_natDegree_le sigma B p hB)
theorem primitive_norm_split
    {F : Type*} [Field F] [DecidableEq F] {s delta cap p : Nat}
    (sigma : F →+* F)
    (horder : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (alpha : Fin s ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : Fin s → F) (hE : ∀ i, E i ≠ 0)
    (A B : Polynomial F)
    (hA : A.natDegree ≤ p) (hB : B.natDegree ≤ p)
    (U : Submodule F (Polynomial.degreeLT F (delta + cap)))
    (hdelta : 0 < delta) (hU : Module.finrank F U = delta)
    (hrelation : ∀ H : U,
      TwoLaneFailureRelation sigma alpha E (H.1.1 * A) (H.1.1 * B)) :
    polynomialFrobeniusNormSix sigma A =
        polynomialFrobeniusNormSix sigma B ∨
      s - cap ≤ 6 * p := by
  classical
  obtain ⟨H, bad, hH, hHdegree, hcommon, hbad, hprimitive⟩ :=
    exists_primitive_cleanup sigma alpha E A B U hdelta hU hrelation
  let D := polynomialFrobeniusNormSix sigma A -
    polynomialFrobeniusNormSix sigma B
  by_cases hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B
  · exact Or.inl hnorm
  right
  have hD : D ≠ 0 := sub_ne_zero.mpr hnorm
  let good := Finset.univ \ bad
  have hgoodRoot : ∀ i ∈ good, Polynomial.eval (alpha i) D = 0 := by
    intro i hi
    have hibad : i ∉ bad := (Finset.mem_sdiff.mp hi).2
    have hrel := hprimitive i hibad
    have hnormValue := scalarFrobeniusNormSix_eq_of_relation sigma horder
      (Polynomial.eval (alpha i) A) (Polynomial.eval (alpha i) B)
      (E i) (hE i) hrel
    dsimp [D]
    rw [Polynomial.eval_sub,
      polynomialFrobeniusNormSix_eval_of_fixed sigma A (alpha i) (hfixed i),
      polynomialFrobeniusNormSix_eval_of_fixed sigma B (alpha i) (hfixed i),
      hnormValue, sub_self]
  have hgoodCard : good.card ≤ D.natDegree := by
    let roots : Finset F := good.map alpha
    have hsub : roots ⊆ D.roots.toFinset := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hD).2
        (hgoodRoot i hi))
    calc
      good.card = roots.card := (Finset.card_map alpha).symm
      _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ D.roots.card := Multiset.toFinset_card_le _
      _ ≤ D.natDegree := Polynomial.card_roots' D
  have hgoodLower : s - cap ≤ good.card := by
    have huniv : (Finset.univ : Finset (Fin s)).card = s := by simp
    have hpartition : good.card + bad.card = s := by
      simpa [good, huniv] using
        (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad))
    omega
  exact hgoodLower.trans (hgoodCard.trans
    (normDifference_natDegree_le sigma A B p hA hB))
theorem primitive_nonzeroNorm_forces_rows_add_delta_le_five_mul
    (rows h delta p s cap : Nat)
    (hs : s = rows + h + delta) (hcap : cap = h - p)
    (hp : p ≤ h) :
    s - cap ≤ 6 * p → rows + delta ≤ 5 * p := by
  omega
theorem primitive_nonzeroNorm_forces_p_ge_10857_6401
    (delta p : Nat) (hdelta : 0 < delta)
    (hcharge : keyFirstLaneRows6401 + delta ≤ 5 * p) :
    10857 ≤ p := by
  norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.n6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.ownerDegreeCap6401,
    ProximityPrize.SubmissionLower.bchksErrors6401] at hcharge
  omega
end BCHKSFrobeniusPrimitiveCleanup6401
end ProximityPrize.SubmissionLower
