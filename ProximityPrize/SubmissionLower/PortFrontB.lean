import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.PortLow4
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_6
noncomputable section
open P0 Polynomial
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0 Polynomial ProximityPrize.Benchmark FrobeniusLocator
private theorem amp_le (v : Fin 2 → K[X]) (j : Fin 2) :
    (v j).natDegree ≤ amplitudeDegree (v 0) (v 1) := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _
private theorem amp_witness (v : Fin 2 → K[X]) (hc : IsCoprime (v 0) (v 1)) :
    ∃ j, v j ≠ 0 ∧ (v j).natDegree = amplitudeDegree (v 0) (v 1) := by
  by_cases hv : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h
      obtain ⟨a, b, hab⟩ := hc
      simp [hv, h] at hab
    exact ⟨1, h1, by simp [amplitudeDegree, hv]⟩
  by_cases hd : (v 1).natDegree ≤ (v 0).natDegree
  · exact ⟨0, hv, (max_eq_left hd).symm⟩
  · refine ⟨1, ?_, (max_eq_right (by omega)).symm⟩
    intro hz
    simp [hz] at hd
private theorem primitive_lift (del : Finset I) (v L : Fin 2 → K[X]) (w : I → K)
    (t : ℕ) (hc : IsCoprime (v 0) (v 1)) (hL : ∀ j, (L j).natDegree < t)
    (he : ∀ i ∉ del, ∀ j, (L j).eval (node i) = (v j).eval (node i) * w i)
    (hpos : amplitudeDegree (v 0) (v 1) < t)
    (hroom : t + amplitudeDegree (v 0) (v 1) + del.card ≤ 262144) :
    ∃ P : K[X], P.natDegree + amplitudeDegree (v 0) (v 1) < t ∧
      ∀ i ∉ del, P.eval (node i) = w i := by
  classical
  have hcross : v 0 * L 1 - v 1 * L 0 = 0 := by
    by_contra hn
    have hb := Strata.root_nodes_card_le node IRSProfile.domain.injective _ hn (Finset.univ \ del)
      (by
        intro i hi
        simp only [eval_sub, eval_mul, he i (Finset.mem_sdiff.mp hi).2]
        ring)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hb
    have hprod (i j : Fin 2) : (v i * L j).natDegree < amplitudeDegree (v 0) (v 1) + t :=
      natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt (amp_le v i) (hL j))
    have hlt := (natDegree_sub_le (v 0 * L 1) (v 1 * L 0)).trans_lt
      (max_lt (hprod 0 1) (hprod 1 0))
    omega
  obtain ⟨a,b,hab⟩ := hc
  let P := a * L 0 + b * L 1
  have hdiv (j : Fin 2) : v j * P = L j := by
    dsimp [P]
    fin_cases j
    · change v 0 * (a * L 0 + b * L 1) = L 0
      linear_combination L 0 * hab + b * hcross
    · change v 1 * (a * L 0 + b * L 1) = L 1
      linear_combination L 1 * hab - a * hcross
  refine ⟨P, ?_, ?_⟩
  · by_cases hz : P = 0
    · simpa [hz] using hpos
    obtain ⟨j,hv,hd⟩ := amp_witness v ⟨a,b,hab⟩
    have hh := hL j
    rw [← hdiv j, natDegree_mul hv hz, hd, add_comm] at hh
    exact hh
  · intro i hi
    have hh := congrArg (Polynomial.eval (node i)) hab
    simp only [eval_add, eval_mul, eval_one] at hh
    simp only [P, eval_add, eval_mul, he i hi]
    linear_combination w i * hh
private theorem contraction_degree {U V P Q : K[X]} {s t : ℕ}
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s)
    (hP : P.natDegree < t) (hQ : Q.natDegree < t) :
    (U * P - V * Q).natDegree < t + s := by
  apply (natDegree_sub_le _ _).trans_lt
  rw [add_comm t s]
  exact max_lt (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hU hP))
    (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hV hQ))
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0
open scoped BigOperators
private theorem sum_rows {n : ℕ} (f : ℕ → ℕ) (rows : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.val = rows i) :
    (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, rows i := by
  rw [← Fin.sum_univ_eq_sum_range f n]
  exact Finset.sum_congr rfl (fun i _ => h i)
private theorem ceil_sq_div_eq (a b c v : ℕ) (hb : 0 < b) (hv : v ≠ 0)
    (hl : (v - 1) * b ^ 2 < c * a ^ 2) (hu : c * a ^ 2 ≤ v * b ^ 2) :
    ⌈(c : ℚ) * ((a : ℚ) / (b : ℚ)) ^ 2⌉₊ = v := by
  rw [Nat.ceil_eq_iff hv, div_pow, ← mul_div_assoc]
  have hpos : 0 < (b : ℚ) ^ 2 := pow_pos (Nat.cast_pos.mpr hb) 2
  constructor
  · apply (lt_div_iff₀ hpos).mpr
    exact_mod_cast hl
  · apply (div_le_iff₀ hpos).mpr
    exact_mod_cast hu
end
end P0_6
end
section
namespace P0_6
noncomputable section
open P0 FrobeniusLocator ProximityPrize.Benchmark Polynomial
private theorem natDegree_lt_of_degree_lt_pos {P : K[X]} {m : ℕ} (hm : 0 < m)
    (h : P.degree < m) : P.natDegree < m := by
  by_cases hP : P = 0
  · simpa [hP] using hm
  · exact (natDegree_lt_iff_degree_lt hP).mpr h
end
end P0_6
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0_6
noncomputable section
open P0 Polynomial FrobeniusLocator
attribute [local instance 2500] CJ0.stackRank._proof_1 P0.ordinary._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      CJ0.stackRank._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
      KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params)))
private def column (n : ℕ) (f : Fin 2 → K[X]) : Bivar :=
  liftX (f 0) + liftX (f 1) * C (Polynomial.X ^ n)
private theorem column_ne {n : ℕ} (hn : n ≠ 0) {f : Fin 2 → K[X]}
    (hf : ∃ j, f j ≠ 0) : column n f ≠ 0 := by
  intro hz
  have h := congrArg Polynomial.Bivariate.swap hz
  simp only [column, liftX, map_add, map_mul, Bivariate.swap_map_C, Bivariate.swap_C,
    Polynomial.map_pow, Polynomial.map_X, map_zero] at h
  have hcoeff (i : ℕ) := congrArg (fun q : Bivar => q.coeff i) h
  have h0 : f 0 = 0 := by simpa [coeff_C_mul_X_pow, Ne.symm hn] using hcoeff 0
  have h1 : f 1 = 0 := by simpa [coeff_C_mul_X_pow, coeff_C, hn] using hcoeff n
  obtain ⟨j,hj⟩ := hf
  fin_cases j
  · exact hj h0
  · exact hj h1
private theorem column_bound (n : ℕ) (f : Fin 2 → K[X]) :
    (column n f).natDegree ≤ amplitudeDegree (f 0) (f 1) :=
  (natDegree_add_le _ _).trans (max_le_max natDegree_map_le
    ((natDegree_mul_C_le _ _).trans natDegree_map_le))
private theorem column_dvd (n : ℕ) (f : Fin 2 → K[X]) (q : K[X])
    (hd : ∀ j, q ∣ f j) : liftX q ∣ column n f :=
  dvd_add ((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 0))
    ((((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 1))).mul_right _)
private theorem column_mul (a : K[X]) (n : ℕ) (f : Fin 2 → K[X]) :
    liftX a * (liftX (f 0) + seed ^ n * liftX (f 1)) =
      column n (fun j => a * f j) := by
  simp only [column, liftX, seed, Polynomial.map_mul, ← C_pow]
  ring
private def firstColumn (d : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX (@Polynomial.map K K KS KS twist (β 0)) +
    seed ^ d * liftX (@Polynomial.map K K KS KS twist (β 1)))
private theorem threeU_fun : threeU = firstColumn p := rfl
private theorem firstColumn_normal (d : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    firstColumn d a β = column d (fun j => a * (β j).map twist) :=
  column_mul a d (fun j => (β j).map twist)
private theorem tight_pair {F : Type*} [Field F] (U V U' V' : F[X])
    (hneU : U ≠ 0) (hneV : V ≠ 0) (hne' : U' ≠ 0) (hc : IsCoprime U V)
    (he : U * V' = V * U') (hmax : max U'.natDegree V'.natDegree ≤ max U.natDegree V.natDegree) :
    max U'.natDegree V'.natDegree = max U.natDegree V.natDegree ∧ IsCoprime U' V' := by
  obtain ⟨a,b,hab⟩ := hc
  let m := a * U' + b * V'
  have hu : U' = m * U := by dsimp [m]; linear_combination -U' * hab - b * he
  have hv : V' = m * V := by dsimp [m]; linear_combination -V' * hab + a * he
  have hm : m ≠ 0 := by intro h; exact hne' (hu.trans (by simp [h]))
  have huD := congrArg Polynomial.natDegree hu
  have hvD := congrArg Polynomial.natDegree hv
  rw [natDegree_mul hm hneU] at huD
  rw [natDegree_mul hm hneV] at hvD
  have hdeg : m.natDegree = 0 := by omega
  have hunit : IsUnit m := isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hm, hdeg]; rfl)
  obtain ⟨k,hk⟩ := isUnit_iff_dvd_one.mp hunit
  refine ⟨by omega, a*k, b*k, ?_⟩
  calc
    a*k*U' + b*k*V' = (m*k) * (a*U + b*V) := by rw [hu,hv]; ring
    _ = 1 := by rw [← hk,hab,one_mul]
private def slice (P : Bivar) (n : ℕ) : K[X] :=
  ∑ j ∈ Finset.range (P.natDegree + 1), monomial j ((P.coeff j).coeff n)
private theorem slice_eval (P : Bivar) (n : ℕ) (x : K) :
    (slice P n).eval x = (P.eval (C x)).coeff n := by
  rw [eval_eq_sum_range (C x)]
  simp only [slice, eval_finsetSum, eval_monomial, finsetSum_coeff, ← C_pow, coeff_mul_C]
private theorem slice_bound (P : Bivar) (n : ℕ) : (slice P n).natDegree ≤ P.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
private theorem select_four (d : ℕ) (hd : 1 < d) (r : Fin 2 → Fin 2 → K) (j l : Fin 2) :
    ((C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1)) : K[X]).coeff (j.val + d*l.val) = r j l := by
  fin_cases j <;> fin_cases l <;>
    simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add, Nat.add_zero] <;>
    split_ifs <;> first | omega | simp_all
private theorem four_coeff (d : ℕ) (hd : 1 < d) (u v w z : Fin 2 → K) (j l : Fin 2) :
    (((C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) : K[X]).coeff
      (j.val + d*l.val)) = u l*w j + v j*z l := by
  let r := fun j l => u l*w j + v j*z l
  have hex : (C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) =
      C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1) := by
    simp only [r, map_add, map_mul, pow_succ]
    ring
  rw [hex]
  exact select_four d hd r j l
private theorem column_eval (d : ℕ) (f : Fin 2 → K[X]) (x : K) :
    (column d f).eval (C x) = C ((f 0).eval x) + C ((f 1).eval x) * Polynomial.X^d := by
  simp only [column, liftX, eval_add, eval_mul, eval_C, eval_map_apply]
private theorem word_coeff (d : ℕ) (hd : 1 < d) (U V : Fin 2 → K[X]) (u : Words)
    (i : I) (j l : Fin 2) :
    (U l).eval (node i) * u j i + (V j).eval (node i) * (u l i)^d =
    (((C ((U 0).eval (node i)) + C ((U 1).eval (node i)) * Polynomial.X^d) *
          (C (u 0 i) + Polynomial.X * C (u 1 i)) +
        (C ((V 0).eval (node i)) + C ((V 1).eval (node i)) * Polynomial.X) *
          (C ((u 0 i)^d) + Polynomial.X^d * C ((u 1 i)^d))) : K[X]).coeff
        (j.val + d*l.val) :=
  (four_coeff d hd (fun l => (U l).eval (node i)) (fun j => (V j).eval (node i))
    (fun j => u j i) (fun l => (u l i)^d) j l).symm
private def relationAt (d : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ d) + Polynomial.X (R := K) ^ d * C (u 1 i ^ d)) =
      output.eval (C (node i))
private theorem relationOn_fun : relationOn = relationAt p := rfl
private def outputs (d : ℕ) (P : Bivar) (j l : Fin 2) := slice P (j.val + d*l.val)
private theorem nodes_of_columns (d : ℕ) (hd : 1 < d) (u : Words) (deleted : Finset I)
    (U V : Fin 2 → K[X]) (P : Bivar)
    (h : relationAt d u deleted (column d U) (column 1 V) P) :
    K1_10.planeNodes d u deleted U V (outputs d P) := by
  intro i hi j l
  rw [outputs, slice_eval, ← h i hi, column_eval, column_eval, pow_one]
  exact word_coeff d hd U V u i j l
end
end P0_6
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace P0_6_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts  relationBounds)
private theorem exists_kernel_outside {F E G : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (f : E →ₗ[F] G) (R : Submodule F E)
    (hdim : Module.finrank F G + Module.finrank F R < Module.finrank F E) :
    ∃ q : E, f q = 0 ∧ q ∉ R := by
  by_contra hn
  have hle : LinearMap.ker f ≤ R := by
    intro q hq
    by_contra hnot
    exact hn ⟨q, LinearMap.mem_ker.mp hq, hnot⟩
  have hk := Submodule.finrank_mono hle
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hr := (LinearMap.range f).finrank_le
  omega
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
end
end P0_6_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_6_1
noncomputable section
open K1 K1_10 K1_11 MvPolynomial
open K1_10_1 (Contacts denominator liftOrdinary numerator pencil planeRelation
  planeRelation_view relationBounds toScalarSource )
private theorem eval_liftOrdinary (Q P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (liftOrdinary Q) = Q := by
  let φ : MvPolynomial (Fin 4) K →+* Polynomial K := (aeval (scalarImages P s t)).toRingHom
  have hh : φ.comp liftOrdinary = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ, liftOrdinary]
    · simp [φ, liftOrdinary, scalarImages]
  exact RingHom.congr_fun hh Q
private theorem eval_denominator (V : Fin 2 → Polynomial K) (P : Polynomial K) (s t : K) :
    aeval (scalarImages P s t) (denominator V) = V 0 + Polynomial.C s * V 1 := by
  simp only [denominator, pencil, map_add, map_mul, aeval_X, eval_liftOrdinary]
  rfl
private theorem denominator_ne {V : Fin 2 → Polynomial K} (hV : ∃ j, V j ≠ 0) :
    denominator V ≠ 0 := by
  intro hz
  have h (s : K) := eval_denominator V 0 s 0
  simp only [hz, map_zero] at h
  have h0 : V 0 = 0 := by simpa using (h 0).symm
  have h1 : V 1 = 0 := by simpa [h0] using (h 1).symm
  obtain ⟨j,hj⟩ := hV
  fin_cases j
  · exact hj h0
  · exact hj h1
private theorem relation_eval (U V : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K)
    (Q Q' : Polynomial K) (s t : K) :
    aeval (decoderImages Q Q' s t) (planeRelation U V O) =
      (V 0 + Polynomial.C s * V 1) * Q' -
      ((O 0 0 + Polynomial.C s * O 1 0) + Polynomial.C t * (O 0 1 + Polynomial.C s * O 1 1) -
        (U 0 + Polynomial.C t * U 1) * Q) := by
  rw [decoderImages, ← polynomialView_eval, planeRelation_view]
  simp [eval_denominator, numerator, pencil, eval_liftOrdinary]
  rfl
private theorem coeff_bounds (L : MvPolynomial (Fin 5) K) (a b : MvPolynomial (Fin 4) K)
    (d : ℕ) (hL : L ∈ filtered (sourceWeights 131071) (sourceBounds d 1 1 1))
    (hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hb : b ≠ 0) :
    a.weightedTotalDegree scalarWeightY ≤ 1 ∧ b.weightedTotalDegree scalarWeightY ≤ 0 ∧
    a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ b.weightedTotalDegree scalarWeightYS ≤ 1 ∧
    a.weightedTotalDegree scalarWeightT ≤ 1 ∧ b.weightedTotalDegree scalarWeightT ≤ 0 := by
  have hz : (polynomialView L).coeff 0 = -a := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X]
  have hone : (polynomialView L).coeff 1 = b := by
    rw [hview]
    simp [Polynomial.coeff_sub, Polynomial.coeff_C]
  obtain ⟨hy, hs, ht⟩ := polynomialView_source_coefficients d 131071 1 1 1 L hL
  have hs1 := hs 1 (by decide) (hone ▸ hb)
  have hy1 := hy 1 (by decide) (hone ▸ hb)
  have ht1 := ht 1 (by decide) (hone ▸ hb)
  rw [hone] at hs1 hy1 ht1
  have ha (v : Fin 4 → ℕ) : (-a).weightedTotalDegree v = a.weightedTotalDegree v := by
    simp [weightedTotalDegree]
  have ha0 : a.weightedTotalDegree scalarWeightY ≤ 1 ∧
      a.weightedTotalDegree scalarWeightYS ≤ 1 ∧ a.weightedTotalDegree scalarWeightT ≤ 1 := by
    by_cases ha' : a = 0
    · simp [ha', weightedTotalDegree]
    · have h0 : (polynomialView L).coeff 0 ≠ 0 := hz ▸ neg_ne_zero.mpr ha'
      have hy0 := hy 0 (by decide) h0
      have hs0 := hs 0 (by decide) h0
      have ht0 := ht 0 (by decide) h0
      simp only [hz, ha, Nat.add_zero] at hy0 hs0 ht0
      exact ⟨hy0, hs0, ht0⟩
  exact ⟨ha0.1, by omega, ha0.2.1, hs1, ha0.2.2, by omega⟩
end
end P0_6_1
end
