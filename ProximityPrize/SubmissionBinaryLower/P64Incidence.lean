import ProximityPrize.SubmissionBinaryLower.P64Resultant

/-!
# Incidences: Lemma O, Lemma U, Lemma AF(2) and inseparable factors (PROOF.md 2.5, 4.10)

Generic over a field `F`, points `ω : ι ↪ F` and lines `y i ∈ F[Z]` of degree at most one.
For a factor `R`, `g_i(Z) = R(x_i, y_i(Z), Z)` is `lineEval R (ω i) (y i)`; it vanishes exactly on
the lines on `R` (`0 < lineOrd`). Degrees in `Z` are bounded by `d = yzSupportDegree R 1`
(formal-plan.md section 5 item 4).

- Lemma O: `Σ_z |A_z \ Λ| ≤ (n - λ)·d`.
- Lemma AF(2): if `λ ≤ 208983`, at most `2d` bad slopes lie on `R`.
- Lemma U: a full line misses at most `d` agreement sets (with `A_z` the full agreement set).
- Section 4.10.2: if `∂_Y R = 0 ≠ ∂_X R`, at most `2h·d` bad slopes lie on `R`. The `X`-derivative
  helpers are copied from `BCHKSInseparable.lean` (63.99 submission).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Incidence

open Polynomial BCHKSSubstitutionVanish P64LineOrder P64Resultant

section Line

variable {F : Type} [Field F]

/-- `R(x, y(Z), Z)`. -/
noncomputable def lineEval (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    F[X] :=
  (triSpecializeX G x).eval y

lemma eval_lineEval (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) (z : F) :
    (lineEval G x y).eval z = biEval (triSpecializeX G x) (y.eval z) z := by
  unfold lineEval biEval
  rw [eval_map, ← coe_evalRingHom, ← Polynomial.eval₂_hom]

/-- A bad curve through the point `(x, y(z))` makes `g(z) = 0`. -/
lemma lineEval_eval_eq_zero (G : Polynomial (Polynomial (Polynomial F))) (x z : F) (y P : F[X])
    (h0 : triEval G z P = 0) (hmatch : P.eval x = y.eval z) : (lineEval G x y).eval z = 0 := by
  rw [eval_lineEval, ← hmatch, ← eval_triEval_eq_biEval_triSpecializeX, h0, eval_zero]

lemma lineEval_eq_coeff (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    lineEval G x y = ((lineShift G x y).coeff 0).coeff 0 := by
  rw [lineShift_coeff_zero, coeff_zero_eq_eval_zero, eval_comp]
  simp [lineEval, evalXAt, triSpecializeX]

/-- `g_i = 0` exactly on the lines on `G`. -/
lemma lineEval_eq_zero_iff {G : Polynomial (Polynomial (Polynomial F))} (hG : G ≠ 0) (x : F)
    (y : F[X]) : lineEval G x y = 0 ↔ 0 < lineOrd G x y := by
  rw [lineEval_eq_coeff, ← Nat.one_le_iff_ne_zero.trans (Nat.pos_iff_ne_zero.symm),
    ← ordGE_iff hG]
  constructor
  · intro h a b hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    exact h
  · intro h
    exact h 0 0 (by omega)

/-- `deg_Z g_i ≤ d` for lines of degree at most one. -/
lemma natDegree_lineEval_le (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X])
    (hy : y.natDegree ≤ 1) :
    (lineEval G x y).natDegree ≤ P64Caps.YZ.yzSupportDegree G 1 := by
  unfold lineEval triSpecializeX
  rw [eval_eq_sum, sum_def]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : G.coeff j ≠ 0 := by
    intro h
    apply mem_support_iff.mp hj
    simp [h]
  have hcap := P64Caps.YZ.coeffWeight_le_of_ne G 1 j hj'
  have h1 : ((map (evalRingHom (C x)) G).coeff j).natDegree ≤
      Polynomial.Bivariate.degreeX (G.coeff j) := by
    rw [coeff_map]
    apply natDegree_eval_C_le_of_coeff
    intro a
    exact Polynomial.Bivariate.coeff_natDegree_le_degreeX _ a
  calc ((map (evalRingHom (C x)) G).coeff j * y ^ j).natDegree
      ≤ ((map (evalRingHom (C x)) G).coeff j).natDegree + (y ^ j).natDegree :=
        natDegree_mul_le
    _ ≤ Polynomial.Bivariate.degreeX (G.coeff j) + j * 1 :=
        Nat.add_le_add h1 (natDegree_pow_le_of_le j hy)
    _ ≤ P64Caps.YZ.yzSupportDegree G 1 := by omega

end Line

section Counts

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- The lines on `R`. -/
noncomputable def lam (ω : ι ↪ F) (y : ι → F[X]) (R : Polynomial (Polynomial (Polynomial F))) :
    Finset ι :=
  Finset.univ.filter fun i => 0 < lineOrd R (ω i) (y i)

/-- Incidence count from a bound on the parameter degree of each line evaluation. -/
theorem sum_card_sdiff_le_of_degree (ω : ι ↪ F) (y : ι → F[X])
    (R : Polynomial (Polynomial (Polynomial F))) (hR : R ≠ 0) (d : ℕ)
    (hdeg : ∀ i, (lineEval R (ω i) (y i)).natDegree ≤ d) (Vs : Finset F) (P : F → F[X])
    (Az : F → Finset ι) (h0 : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = (y i).eval z) :
    ∑ z ∈ Vs, (Az z \ lam ω y R).card ≤
      (Finset.univ \ lam ω y R).card * d := by
  classical
  have hdc : ∑ z ∈ Vs, (Az z \ lam ω y R).card =
      ∑ i ∈ Finset.univ \ lam ω y R, (Vs.filter fun z => i ∈ Az z).card := by
    have h1 : ∀ z, (Az z \ lam ω y R).card =
        ∑ i ∈ Finset.univ \ lam ω y R, if i ∈ Az z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter]
      congr 1
      ext i
      simp [and_comm]
    have h2 : ∀ i, (Vs.filter fun z => i ∈ Az z).card =
        ∑ z ∈ Vs, if i ∈ Az z then 1 else 0 := fun i => Finset.card_filter _ _
    simp only [h1, h2]
    exact Finset.sum_comm
  rw [hdc, ← smul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro i hi
  have hg : lineEval R (ω i) (y i) ≠ 0 := by
    rw [Ne, lineEval_eq_zero_iff hR]
    simpa [lam] using hi
  calc (Vs.filter fun z => i ∈ Az z).card ≤ (lineEval R (ω i) (y i)).roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Finset.mem_filter] at hz
        rw [Multiset.mem_toFinset, mem_roots hg, IsRoot.def]
        exact lineEval_eval_eq_zero R (ω i) z (y i) (P z) (h0 z hz.1) (hmatch z hz.1 i hz.2)
    _ ≤ (lineEval R (ω i) (y i)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (lineEval R (ω i) (y i)).natDegree := card_roots' _
    _ ≤ _ := hdeg i

/-- **Lemma O.** -/
theorem sum_card_sdiff_le (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ 1)
    (R : Polynomial (Polynomial (Polynomial F))) (hR : R ≠ 0) (Vs : Finset F) (P : F → F[X])
    (Az : F → Finset ι) (h0 : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = (y i).eval z) :
    ∑ z ∈ Vs, (Az z \ lam ω y R).card ≤
      (Finset.univ \ lam ω y R).card * P64Caps.YZ.yzSupportDegree R 1 :=
  sum_card_sdiff_le_of_degree ω y R hR _ (fun i => natDegree_lineEval_le R (ω i) (y i) (hy i))
    Vs P Az h0 hmatch

/-- **Lemma AF(2)**, with `|A_z| ≥ A = 1482911`, `n = 2^21` and `λ ≤ 208983`. -/
theorem card_le_of_few_lines (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ 1)
    (hn : Fintype.card ι = 2097152)
    (R : Polynomial (Polynomial (Polynomial F))) (hR : R ≠ 0) (Vs : Finset F) (P : F → F[X])
    (Az : F → Finset ι) (h0 : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hmatch : ∀ z ∈ Vs, ∀ i ∈ Az z, (P z).eval (ω i) = (y i).eval z)
    (hAz : ∀ z ∈ Vs, 1482911 ≤ (Az z).card) (hlam : (lam ω y R).card ≤ 208983) :
    Vs.card ≤ 2 * P64Caps.YZ.yzSupportDegree R 1 := by
  classical
  have hO := sum_card_sdiff_le ω y hy R hR Vs P Az h0 hmatch
  have hcompl : (Finset.univ \ lam ω y R).card ≤ 2097152 := by
    rw [← hn]; exact Finset.card_le_univ _
  have hlow : ∀ z ∈ Vs, 1273928 ≤ (Az z \ lam ω y R).card := by
    intro z hz
    have h1 := Finset.le_card_sdiff (lam ω y R) (Az z)
    have := hAz z hz
    omega
  have hsum : Vs.card * 1273928 ≤ ∑ z ∈ Vs, (Az z \ lam ω y R).card := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hlow
  have := Nat.mul_le_mul_right (P64Caps.YZ.yzSupportDegree R 1) hcompl
  nlinarith

end Counts

section FullLine

variable {F : Type} [Field F] [DecidableEq F]

/-- A full line: `R(x, Y, Z) = r(Z)·(Y - y(Z))^h` with `r ≠ 0` of `Z`-degree at most `d`. -/
theorem evalXAt_eq_of_full {R : Polynomial (Polynomial (Polynomial F))} (hirr : Irreducible R)
    (hpos : 1 ≤ R.natDegree) (x : F) (y : F[X]) (hfull : lineOrd R x y = R.natDegree) :
    ∃ c : F[X], c ≠ 0 ∧ c.natDegree ≤ P64Caps.YZ.yzSupportDegree R 1 ∧
      evalXAt R x = C c * ((Polynomial.X : Polynomial (Polynomial F)) - C y) ^ R.natDegree := by
  have hR0 : R ≠ 0 := hirr.ne_zero
  have hE : evalXAt R x ≠ 0 := evalXAt_ne_zero_of_irreducible hirr hpos x
  set h := R.natDegree
  set E' := (evalXAt R x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y)
  have hord := (ordGE_iff hR0 x y h).mpr hfull.ge
  have hE'deg : E'.natDegree ≤ h := by
    simp only [E', natDegree_comp, natDegree_X_add_C, mul_one]
    exact natDegree_map_le
  have hE' : E' = C (E'.coeff h) * (Polynomial.X : Polynomial (Polynomial F)) ^ h := by
    ext b : 1
    rw [coeff_C_mul_X_pow]
    split_ifs with hb
    · rw [hb]
    · rcases Nat.lt_or_gt_of_ne hb with hlt | hgt
      · have := hord 0 b (by omega)
        rwa [lineShift_coeff_zero] at this
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hEeq : evalXAt R x = C (E'.coeff h) * ((Polynomial.X : Polynomial (Polynomial F)) - C y) ^ h := by
    have hinv : evalXAt R x = E'.comp ((Polynomial.X : Polynomial (Polynomial F)) - C y) := by
      simp only [E', comp_assoc]
      simp
    rw [hinv, hE']
    simp [mul_comp]
  refine ⟨E'.coeff h, ?_, ?_, hEeq⟩
  · intro h0
    apply hE
    rw [hEeq, h0]
    simp
  · have hc : E'.coeff h = (evalXAt R x).coeff h := by
      rw [hEeq, coeff_C_mul]
      have : (((Polynomial.X : Polynomial (Polynomial F)) - C y) ^ h).coeff h = 1 := by
        have hm : (((Polynomial.X : Polynomial (Polynomial F)) - C y) ^ h).Monic := (monic_X_sub_C y).pow h
        have hd : (((Polynomial.X : Polynomial (Polynomial F)) - C y) ^ h).natDegree = h := by
          rw [natDegree_pow, natDegree_X_sub_C, mul_one]
        have := hm.coeff_natDegree
        rwa [hd] at this
      rw [this, mul_one]
    rw [hc]
    simp only [evalXAt, coeff_map, coe_evalRingHom]
    calc ((R.coeff h).eval (C x)).natDegree ≤ Polynomial.Bivariate.degreeX (R.coeff h) :=
          natDegree_eval_C_le_of_coeff _ x _
            (fun a => Polynomial.Bivariate.coeff_natDegree_le_degreeX _ a)
      _ ≤ P64Caps.YZ.yzSupportDegree R 1 := by
          by_cases hj : R.coeff h = 0
          · simp [hj, Polynomial.Bivariate.degreeX]
          · have := P64Caps.YZ.coeffWeight_le_of_ne R 1 h hj
            omega

/-- **Lemma U.** A full line lies in every agreement set of a bad curve on `R`, except where
`r(z) = 0`: so it is missing from at most `d` full agreement sets. -/
theorem card_filter_not_mem_le_of_full {ι : Type} [DecidableEq ι] (ω : ι ↪ F) (y : ι → F[X])
    {R : Polynomial (Polynomial (Polynomial F))} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    (i : ι) (hfull : lineOrd R (ω i) (y i) = R.natDegree) (Vs : Finset F) (P : F → F[X])
    (Az : F → Finset ι) (h0 : ∀ z ∈ Vs, triEval R z (P z) = 0)
    (hAz : ∀ z ∈ Vs, (P z).eval (ω i) = (y i).eval z → i ∈ Az z) :
    (Vs.filter fun z => i ∉ Az z).card ≤ P64Caps.YZ.yzSupportDegree R 1 := by
  classical
  obtain ⟨c, hc0, hcdeg, hEeq⟩ := evalXAt_eq_of_full hirr hpos (ω i) (y i) hfull
  calc (Vs.filter fun z => i ∉ Az z).card ≤ c.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Finset.mem_filter] at hz
        rw [Multiset.mem_toFinset, mem_roots hc0, IsRoot.def]
        by_contra hcz
        apply hz.2
        apply hAz z hz.1
        have h1 := eval_triEval_eq_biEval_triSpecializeX R (P z) (ω i) z
        rw [h0 z hz.1, eval_zero] at h1
        have h2 : triSpecializeX R (ω i) = evalXAt R (ω i) := rfl
        rw [h2, hEeq] at h1
        simp only [biEval, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X,
          map_C, coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_sub, eval_X] at h1
        have := (mul_eq_zero.mp h1.symm).resolve_left hcz
        exact sub_eq_zero.mp ((pow_eq_zero_iff (by omega)).mp this)
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := card_roots' _
    _ ≤ _ := hcdeg

end FullLine

section DerivX

variable {A : Type*} [CommRing A]

/-- Differentiate every `Y`-coefficient in its own variable (the middle `X`). -/
noncomputable def dXPoly (f : Polynomial (Polynomial A)) : Polynomial (Polynomial A) :=
  ∑ j ∈ f.support, Polynomial.monomial j (Polynomial.derivative (f.coeff j))

@[simp] theorem coeff_dXPoly (f : Polynomial (Polynomial A)) (j : ℕ) :
    (dXPoly f).coeff j = Polynomial.derivative (f.coeff j) := by
  classical
  simp only [dXPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.derivative_zero]
    · intro b hb
      have : b ≠ j := fun h => hj (h ▸ hb)
      simp [this]

theorem natDegree_dXPoly_le (f : Polynomial (Polynomial A)) :
    (dXPoly f).natDegree ≤ f.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dXPoly, Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hj),
    Polynomial.derivative_zero]

theorem dXPoly_map {B : Type*} [CommRing B] (φ : A →+* B) (f : Polynomial (Polynomial A)) :
    (dXPoly f).map (Polynomial.mapRingHom φ) =
      dXPoly (f.map (Polynomial.mapRingHom φ)) := by
  ext1 j
  simp [Polynomial.coeff_map, Polynomial.derivative_map]

/-- Chain rule along an inseparable polynomial: if `∂f/∂Y = 0` then
`d/dX f(X, P(X)) = (∂f/∂X)(X, P(X))`. -/
theorem derivative_eval_of_derivative_eq_zero
    (f : Polynomial (Polynomial A)) (P : Polynomial A) (hf : f.derivative = 0) :
    Polynomial.derivative (f.eval P) = (dXPoly f).eval P := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self f.natDegree),
    Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_dXPoly_le f)
      (Nat.lt_succ_self f.natDegree)),
    Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.derivative_mul, coeff_dXPoly]
  have hzero : f.coeff j * Polynomial.derivative (P ^ j) = 0 := by
    cases j with
    | zero => simp
    | succ i =>
      have h := congrArg (fun g => g.coeff i) hf
      simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h
      rw [Polynomial.derivative_pow]
      calc f.coeff (i + 1) *
            (Polynomial.C ((↑(i + 1) : A)) * P ^ (i + 1 - 1) * Polynomial.derivative P) =
          (f.coeff (i + 1) * (↑i + 1)) * (P ^ (i + 1 - 1) * Polynomial.derivative P) := by
            rw [Polynomial.C_eq_natCast]
            push_cast
            ring
        _ = 0 := by rw [h, zero_mul]
  rw [hzero, add_zero]

end DerivX

section Dead

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem degreeX_dXPoly_lt (R : Polynomial (Polynomial (Polynomial F)))
    (hX : dXPoly R ≠ 0) :
    Polynomial.Bivariate.degreeX (dXPoly R) < Polynomial.Bivariate.degreeX R := by
  classical
  obtain ⟨j₀, hj₀⟩ := Polynomial.support_nonempty.mpr hX
  have hlt : ∀ j ∈ (dXPoly R).support,
      ((dXPoly R).coeff j).natDegree < Polynomial.Bivariate.degreeX R := by
    intro j hj
    have hne : (dXPoly R).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    rw [coeff_dXPoly] at hne ⊢
    have hc : R.coeff j ≠ 0 := by
      intro hz
      rw [hz, Polynomial.derivative_zero] at hne
      exact hne rfl
    have hdeg : (R.coeff j).natDegree ≠ 0 := by
      intro hz
      apply hne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.derivative_C]
    have h1 := Polynomial.natDegree_derivative_lt hdeg
    have h2 : (R.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX R := by
      unfold Polynomial.Bivariate.degreeX
      exact Finset.le_sup (f := fun n => (R.coeff n).natDegree)
        (Polynomial.mem_support_iff.mpr hc)
    omega
  have hpos : 0 < Polynomial.Bivariate.degreeX R := by
    have := hlt j₀ hj₀
    omega
  unfold Polynomial.Bivariate.degreeX
  exact (Finset.sup_lt_iff (by exact hpos)).mpr hlt

/-- An irreducible `R` does not divide its nonzero `X`-derivative. -/
theorem not_dvd_dXPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hX : dXPoly R ≠ 0) : ¬ R ∣ dXPoly R := by
  rintro ⟨M, hM⟩
  have hR : R ≠ 0 := by
    rintro rfl
    simp at hM
    exact hX hM
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
    exact hX hM
  have hdeg := Polynomial.Bivariate.degreeX_mul R M hR hM0
  rw [← hM] at hdeg
  have := degreeX_dXPoly_lt R hX
  omega


/-- **Section 4.10.2.** A factor with `∂_Y R = 0 ≠ ∂_X R` carries at most `2h·d` bad slopes. -/
theorem card_le_of_inseparable (R : Polynomial (Polynomial (Polynomial F)))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hY : R.derivative = 0)
    (hX : dXPoly R ≠ 0) (DX : ℕ) (hXcap : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hF : 2 * R.natDegree * DX < Fintype.card F) (S : Finset F) (P : F → Polynomial F)
    (hvan : ∀ z ∈ S, triEval R z (P z) = 0) :
    S.card ≤ 2 * R.natDegree * P64Caps.YZ.yzSupportDegree R 1 := by
  classical
  have hvanD : ∀ z ∈ S, triEval (dXPoly R) z (P z) = 0 := by
    intro z hz
    have h0 := hvan z hz
    have hRz : (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).derivative = 0 := by
      rw [Polynomial.derivative_map, hY, Polynomial.map_zero]
    have hchain := derivative_eval_of_derivative_eq_zero
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) (P z) hRz
    rw [← dXPoly_map] at hchain
    unfold triEval specializeZ at h0 ⊢
    rw [← hchain, h0, Polynomial.derivative_zero]
  have hZR : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ P64Caps.YZ.yzSupportDegree R 1 :=
    coeff_natDegree_le_yz R
  have hZD : ∀ j a, (((dXPoly R).coeff j).coeff a).natDegree ≤
      P64Caps.YZ.yzSupportDegree R 1 := by
    intro j a
    rw [coeff_dXPoly, Polynomial.coeff_derivative]
    calc ((R.coeff j).coeff (a + 1) * (↑a + 1)).natDegree ≤
          ((R.coeff j).coeff (a + 1)).natDegree + ((↑a + 1 : Polynomial F)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ P64Caps.YZ.yzSupportDegree R 1 + 0 := by
        apply Nat.add_le_add (hZR j (a + 1))
        rw [show ((↑a + 1 : Polynomial F)) = Polynomial.C ((↑a + 1 : F)) by simp]
        simp
      _ = _ := by simp
  have hXD : ∀ j, ((dXPoly R).coeff j).natDegree ≤ DX := by
    intro j
    rw [coeff_dXPoly]
    exact (Polynomial.natDegree_derivative_le _).trans (by have := hXcap j; omega)
  have hnm := natDegree_dXPoly_le R
  have hcard := card_common_le R (dXPoly R) hirr hpos (not_dvd_dXPoly R hX) _ _ DX hZR hZD
    hXcap hXD (by nlinarith) S P (fun z hz => ⟨hvan z hz, hvanD z hz⟩)
  have := Nat.mul_le_mul_right (P64Caps.YZ.yzSupportDegree R 1) hnm
  nlinarith

end Dead

end P64Incidence
end ProximityPrize.SubmissionBinaryLower
