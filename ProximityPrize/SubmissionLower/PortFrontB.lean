import ProximityPrize.SubmissionLower.PortFrontA
set_option Elab.async false

section PackSource_P0_6Defs
set_option autoImplicit true
namespace P0_6
noncomputable section

open P0 Polynomial

/-- Coefficients of the first column as a pencil in the independent second seed. -/
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist

/-- Coefficients of the second column as a pencil in the independent first seed. -/
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)

abbrev Plane := K1_10.Plane
abbrev Adjugate := K1_10.Adjugate
abbrev ScalarSource := K1_10.ScalarSource

abbrev sourceCutoff : ℕ := 4 * agreement - 1

/-- The global quotient dimension beats the local conditions after deleting the fixed nodes. -/
def quotientSurplus (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 16 16 - K1_10.jetDim 3 15 15) <
    K1_10.sourceDim sourceCutoff 5 16 16 -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 15 15

abbrev cutDegree : ℕ := (2 * (k - 1) - 1) * (37 - 1) + 1

def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) /
    ((agreement - (k - 1) : ℕ) : ℚ)

def regularPrice : ℕ := ⌈((185 : ℕ) : ℚ) * incidenceRatio ^ 2⌉₊

end
end P0_6
end PackSource_P0_6Defs

section PackSource_P0_6Adjugate
set_option autoImplicit true
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

/-- Divide two compatible lifts by their primitive pair. The degree bound
uses a nonzero coefficient of maximum degree, including constant pairs. -/
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

theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : D.height + (fixedNodes R).card ≤ 32784) :
    Nonempty (Adjugate u (fixedNodes R) D.height) := by
  let A := B.α
  let V := fun j => (B.β j).map twist
  let s := amplitudeDegree (A 0) (A 1)
  let t := amplitudeDegree (V 0) (V 1)
  have htw (P : K[X]) : (P.map twist).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht : t = amplitudeDegree (B.β 0) (B.β 1) := by simp only [t, V, amplitudeDegree, htw]
  have ha : B.a.natDegree + t ≤ D.height := ht ▸ B.first_degree
  have hb : B.b.natDegree + s ≤ D.height := B.second_degree
  have hv : IsCoprime (V 0) (V 1) := B.β_primitive.map (mapRingHom twist)
  have hout (j l : Fin 2) : (W.output j l).natDegree < 131072 + D.height := by
    by_cases hz : W.output j l = 0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L := fun l => A 0 * W.output 1 l - A 1 * W.output 0 l
  let N := fun j => V 1 * W.output j 0 - V 0 * W.output j 1
  let w := fun i => B.a.eval (node i) * ((A 0).eval (node i) * u 1 i - (A 1).eval (node i) * u 0 i)
  let z := fun i => B.b.eval (node i) * ((V 0).eval (node i) * (u 1 i)^p - (V 1).eval (node i) * (u 0 i)^p)
  have hn (i : I) (hi : i ∉ fixedNodes R) (j l : Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i) * (V l).eval (node i) * u j i -
        B.b.eval (node i) * (A j).eval (node i) * (u l i)^p := by
    rw [← W.nodes i hi]
    simp only [leftCoeff, rightCoeff, eval_mul, eval_neg, A, V]
    ring
  obtain ⟨P, hP, heP⟩ := primitive_lift (fixedNodes R) V L w (131072 + D.height + s) hv
    (fun l => contraction_degree (amp_le A 0) (amp_le A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L, w, eval_sub, eval_mul, hn i hi]; ring)
    (by change t < _; omega) (by change _ + t + _ ≤ _; omega)
  obtain ⟨Q, hQ, heQ⟩ := primitive_lift (fixedNodes R) A N z (131072 + D.height + t) B.α_primitive
    (fun j => contraction_degree (amp_le V 1) (amp_le V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N, z, eval_sub, eval_mul, hn i hi]; ring)
    (by change s < _; omega) (by change _ + s + _ ≤ _; omega)
  change P.natDegree + t < 131072 + D.height + s at hP
  change Q.natDegree + s < 131072 + D.height + t at hQ
  let σ := RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩
  let τ := σ.symm.toRingHom
  have hundo (x : K) : τ (twist x) = x := σ.symm_apply_apply x
  have hfixed (i : I) : τ (node i) = node i := by
    have hh : twist (node i) = node i := Native.native_domain_fixed i
    simpa only [hh] using hundo (node i)
  have hmap (F : K[X]) (i : I) : (F.map τ).eval (node i) = τ (F.eval (node i)) :=
    Strata.eval_coefficient_map τ _ _ (hfixed i)
  have hβ (l : Fin 2) (i : I) : (V l).eval (node i) = twist ((B.β l).eval (node i)) :=
    Strata.eval_coefficient_map twist _ _ (Native.native_domain_fixed i)
  let b := B.b.map τ
  let Q' := Q.map τ
  have heQ' (i : I) (hi : i ∉ fixedNodes R) : Q'.eval (node i) = b.eval (node i) *
      ((B.β 0).eval (node i) * u 1 i - (B.β 1).eval (node i) * u 0 i) := by
    rw [show Q'.eval (node i) = τ (Q.eval (node i)) from hmap Q i, heQ i hi]
    change τ (B.b.eval (node i) * ((V 0).eval (node i) * twist (u 1 i) -
      (V 1).eval (node i) * twist (u 0 i))) = _
    simp only [b, hmap, hβ, map_mul, map_sub, hundo]
  let det := A 0 * B.β 1 - A 1 * B.β 0
  let denom := B.a * b * det
  let num := fun j => b * B.β j * P - B.a * A j * Q'
  have hb' : b.natDegree = B.b.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j : Fin 2) : (B.β j).natDegree ≤ t := ht ▸ amp_le B.β j
  have hadeg (j : Fin 2) : (A j).natDegree ≤ s := amp_le A j
  have ddet : det.natDegree ≤ s + t := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom, mul_ne_zero (mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff τ.injective).mpr B.b_ne)) hnp,
    ?_, num, ?_, ?_⟩⟩
  · calc
      denom.natDegree ≤ B.a.natDegree + b.natDegree + det.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _ ≤ 2 * D.height := by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree < 131072 + 2 * D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have := hvdeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega)
      · have := hadeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i) * u 0 i = (num 0).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
    · change denom.eval (node i) * u 1 i = (num 1).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
end
end P0_6
end PackSource_P0_6Adjugate

section PackSource_P0_6Arithmetic
set_option autoImplicit true
namespace P0_6
noncomputable section

open P0
open scoped BigOperators

private theorem sum_rows {n : ℕ} (f : ℕ → ℕ) (rows : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.val = rows i) :
    (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, rows i := by
  rw [← Fin.sum_univ_eq_sum_range f n]
  exact Finset.sum_congr rfl (fun i _ => h i)

private theorem source_count : K1_10.sourceDim sourceCutoff 5 16 16 = 1494315144 := by
  let rows : Fin 6 → ℕ := ![620469128, 414114160, 253567980, 135750244, 57056324, 13357308]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1494315144 := by decide

private theorem multiple_count : K1_10.sourceDim 565192 4 15 15 = 740478301 := by
  let rows : Fin 5 → ℕ := ![360388480, 216468810, 112017388, 43749095, 7854528]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 740478301 := by decide

private theorem jet_count : K1_10.jetDim 4 16 16 = 5276 := by
  let rows : Fin 4 → ℕ := ![2720, 1568, 750, 238]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 4, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 5276 := by decide

private theorem local_multiple_count : K1_10.jetDim 3 15 15 = 2401 := by
  let rows : Fin 3 → ℕ := ![1472, 705, 224]
  unfold K1_10.jetDim
  calc
    _ = ∑ i : Fin 3, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 2401 := by decide

theorem minimum_surplus :
    K1_10.sourceDim sourceCutoff 5 16 16 -
      K1_10.sourceDim (sourceCutoff - (k - 1) - 24568) 4 15 15 =
      blockLength * (K1_10.jetDim 4 16 16 - K1_10.jetDim 3 15 15) + 172843 := by
  have h : sourceCutoff - (k - 1) - 24568 = 565192 := by decide
  rw [h, source_count, multiple_count, jet_count, local_multiple_count]
  decide

theorem bank_surplus (n h : ℕ) (hn : n ≤ blockLength) (hh : 24568 ≤ h) :
    quotientSurplus n h := by
  have hm : K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 15 15 ≤
      K1_10.sourceDim (sourceCutoff - (k - 1) - 24568) 4 15 15 := by
    unfold K1_10.sourceDim
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.sub_le_sub_left hh _) _) _))
  unfold quotientSurplus
  rw [jet_count, local_multiple_count]
  have hd := minimum_surplus
  rw [jet_count, local_multiple_count] at hd
  have hs : n * (5276 - 2401) ≤ blockLength * (5276 - 2401) :=
    Nat.mul_le_mul_right _ hn
  omega

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

theorem regularPrice_exact : regularPrice = 117234633400712490 := by
  unfold regularPrice incidenceRatio
  exact ceil_sq_div_eq 1236945993621 49137 185 117234633400712490
    (by decide) (by decide) (by decide) (by decide)

end
end P0_6
end PackSource_P0_6Arithmetic

section PackSource_P0_6Height
set_option autoImplicit true
namespace P0_6
noncomputable section

open P0 FrobeniusLocator ProximityPrize.Benchmark Polynomial

theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ : K} (hn : Normal u γ) (M : BadMark u γ) :
    Disjoint M.support (fixedNodes R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)

private theorem natDegree_lt_of_degree_lt_pos {P : K[X]} {m : ℕ} (hm : 0 < m)
    (h : P.degree < m) : P.natDegree < m := by
  by_cases hP : P = 0
  · simpa [hP] using hm
  · exact (natDegree_lt_iff_degree_lt hP).mpr h

/-- If the adjugate has overhead below A-k, agreement makes its cleared
decoder identity global. All errors lie on the fixed puncture or the zeros
of the multiplier, too few columns for a normal stacked matrix. -/
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D : Reduction u T R) (J : Adjugate u (fixedNodes R) D.height)
    (hsmall : 2 * D.height < P0.L) {γ : K} (hn : Normal u γ) (M : BadMark u γ) : False := by
  classical
  let F := J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder
  have hfit : P0.k + 2 * D.height < P0.agreement := by
    have hsum : P0.k + P0.L = P0.agreement := by decide
    omega
  have hdeg : F.natDegree < P0.agreement := by
    have hj (j : Fin 2) : (J.numer j).natDegree < P0.k + 2 * D.height :=
      natDegree_lt_of_degree_lt_pos (by
        have hk : 0 < P0.k := by decide
        omega) (J.numer_degree j)
    have hP : M.decoder.natDegree < P0.k := natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod := natDegree_mul_le (p := J.denom) (q := M.decoder)
    have hsub := natDegree_sub_le (J.numer 0 + C γ * J.numer 1) (J.denom * M.decoder)
    change (J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder).natDegree < P0.agreement
    have := J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have := hj 0; omega) (by have := hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF : F = 0 := by
    by_contra hf
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd : i ∉ fixedNodes R := fun h => (Finset.disjoint_left.mp (mark_disjoint D hn M)) hi h
        simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd, M.hits i hi]
        ring)
    have := M.agreement
    omega
  let zeros := Finset.univ.filter (fun i : I => J.denom.eval (node i) = 0)
  let E := fixedNodes R ∪ zeros
  have hZ : zeros.card ≤ J.denom.natDegree := Strata.root_nodes_card_le node
    IRSProfile.domain.injective _ J.nonzero zeros (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hE : E.card ≤ (fixedNodes R).card + 2 * D.height := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    have hd : i ∉ fixedNodes R := fun h => hi (Finset.mem_union_left _ h)
    have hz : J.denom.eval (node i) ≠ 0 :=
      fun h => hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hf : F.eval (node i) = 0 := by rw [hF, eval_zero]
    simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal := relation_height_balance T
  have hheight := D.height_eq
  have hs := actual_stackRank u
  have hcard : P0.k + P0.L + P0.t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) P0.L P0.t).map (evalRingHom γ)).rank = stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      P0.k P0.L P0.t M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b : Fin 2 => iterateFrobenius K p b.val) (fun i : E => node i.val)
    (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) P0.L)
  rw [Fintype.card_coe, hn] at hr
  have hsize : 2 * D.height + (fixedNodes R).card < stackRank u := by
    omega
  omega

end
end P0_6
end PackSource_P0_6Height

section PackSource_P0_6Plane
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace P0_6
noncomputable section
open P0 Polynomial FrobeniusLocator

-- Use the same finite-field instances in the two native power expressions.
-- This keeps kernel conversion from expanding a polynomial power of 2130706433.
attribute [local instance 2500] P0.WeightedList._proof_1 P0.ordinary._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      P0.WeightedList._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
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

private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))

private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring

/-- A polynomial pair in the direction of a coprime pair and of no greater
maximum degree can differ only by a unit of the coefficient field. -/
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

theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → K[X]) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap K[X] Frac
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < P0.k + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h

end
end P0_6
end PackSource_P0_6Plane

section PackSource_P0_6Split
set_option autoImplicit true
namespace P0_6
noncomputable section

open P0 Polynomial

/-- The (1,1) filtered quotient supplies an eliminant for every marked decoder on the puncture. -/
def c1 : Prop :=
  ∀ u deleted h U V, Plane u deleted h U V → 24568 ≤ h → h + deleted.card ≤ 32784 →
    quotientSurplus (blockLength - deleted.card) h →
    ∃ A : ScalarSource, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0

/-- Taylor incidence for labels at which the scalar equation remains nonzero. -/
def c2 : Prop :=
  ∀ u (A : ScalarSource) (Γ : Finset K),
    (∀ γ ∈ Γ, A.atLabel γ ≠ 0 ∧ ∃ M : BadMark u γ, A.atDecoder γ M.decoder = 0) →
    Γ.card ≤ regularPrice

private theorem zero_specializations (A : ScalarSource) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, A.atLabel γ = 0) : Γ.card ≤ 44744835119 := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr A.nonzero
  apply K1_10.frobenius_coefficient_exception_count p 26 21 (by decide) (A.poly.coeff e)
    (MvPolynomial.mem_support_iff.mp he) (A.s_degree e he) (by decide) (A.t_degree e he) Γ
  intro γ hγ
  have hh := congrArg (fun P : MvPolynomial (Fin 2) K => P.coeff e) (hΓ γ hγ)
  simpa only [K1_10.ScalarSource.atLabel, MvPolynomial.coeff_map,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh

theorem of_children (h1 : c1) (h2 : c2) : P0.c6 := by
  classical
  intro u hu T R D B _hsat hnp Γ hΓ hn
  obtain ⟨W⟩ := plane_of_rankThree B
  have hh : D.height + (fixedNodes R).card ≤ 32784 :=
    D.height_eq ▸ relation_height_le hu T
  by_cases hsmall : 2 * D.height < L
  · obtain ⟨J⟩ := adjugate_of_plane B hnp W hh
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin : 24568 ≤ D.height := by
    change ¬ 2 * D.height < 49136 at hsmall
    omega
  obtain ⟨A, hA⟩ := h1 u _ D.height _ _ W hmin hh
    (bank_surplus _ _ (Nat.sub_le _ _) hmin)
  let good := Γ.filter (fun γ => A.atLabel γ ≠ 0)
  let exc := Γ.filter (fun γ => ¬ A.atLabel γ ≠ 0)
  have hexc : exc.card ≤ 44744835119 := zero_specializations A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood : good.card ≤ regularPrice := h2 u A good (by
    intro γ hγ
    obtain ⟨hγΓ, hnonzero⟩ := Finset.mem_filter.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact ⟨hnonzero, M, hA γ M (mark_disjoint D (hn γ hγΓ) M)⟩)
  rw [regularPrice_exact] at hgood
  have hsum : good.card + exc.card = Γ.card :=
    Finset.card_filter_add_card_filter_not (s := Γ) (p := fun γ => A.atLabel γ ≠ 0)
  omega

end
end P0_6
end PackSource_P0_6Split

section PackSource_P0_6_1Quotient
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace P0_6_1
noncomputable section

open MvPolynomial K1_11
open K1_10_1 (Contacts Multipliers relationBounds)
open P0_6 (sourceCutoff)

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

abbrev Source (F : Type*) [Field F] :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds sourceCutoff 5 16 16)

variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}

variable (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)

private def localMultiply (i : Fin N) : Multipliers F →ₗ[F] JetSpace F 3 16 16 where
  toFun Q := ⟨weightedTruncation contactWeight 4 (C.shifted i L * Q.val), by
    apply truncated_mul_mem_jet 2 15 15 1 1
    · exact (contactShift_parameter_weights _ _ _ _ _ L).1.trans (le_of_eq (hdeg 2))
    · exact (contactShift_parameter_weights _ _ _ _ _ L).2.trans (le_of_eq (hdeg 3))⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp

private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 16 16) ⧸ LinearMap.range (localMultiply C hdeg i)

private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace C hdeg i) = J 4 16 16 - J 3 15 15 := by
  have hinj : Function.Injective (localMultiply C hdeg i) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro Q hQ
    by_contra hn
    have hprod : weightedTruncation contactWeight 4 (C.shifted i L * Q.val) = 0 :=
      congrArg (fun x : JetSpace F 3 16 16 => x.val) hQ
    have horder := C.order_one i
    change (contactLift contactWeight (C.shifted i L)).natTrailingDegree = 1 at horder
    have hL : C.shifted i L ≠ 0 := by
      intro hz
      simp [hz] at horder
    exact contact_product_not_high_order contactWeight 4 (C.shifted i L) Q.val
      horder hL (fun hz => hn (Subtype.ext hz)) (jetSpace_support_bound _ _ _ Q)
      ((weightedTruncation_eq_zero_iff _ _ _).mp hprod)
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply C hdeg i))
  rw [LinearMap.finrank_range_of_inj hinj, jetSpace_finrank, jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace C hdeg i) + J 3 15 15 = J 4 16 16 at hq
  omega

private def nodeMap (i : Fin N) : Source F →ₗ[F] LocalSpace C hdeg i :=
  (LinearMap.range (localMultiply C hdeg i)).mkQ.comp
    (sourceToJet sourceCutoff 131071 5 16 16 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))

include hdeg in
/-- Produce a source outside the plane relation with order-four contacts modulo it. -/
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 32784) (hs : P0_6.quotientSurplus N h) :
    ∃ G : Source F, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 16 16 j := by
    have hcapacity : 131071 + 32784 ≤ sourceCutoff := by decide
    intro j
    fin_cases j <;> simp [relationBounds, sourceBounds] <;> omega
  have hshift : (fun j => sourceBounds sourceCutoff 5 16 16 j - relationBounds h j) =
      sourceBounds (sourceCutoff - 131071 - h) 4 15 15 := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds] <;> omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds sourceCutoff 5 16 16)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (sourceCutoff - 131071 - h) 131071 4 15 15 := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  letI (i : Fin N) : Module.Free F (LocalSpace C hdeg i) := Module.Free.of_divisionRing F _
  letI : Module F (∀ i : Fin N, LocalSpace C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace C hdeg i) =
      N * (J 4 16 16 - J 3 15 15) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 16 16 - J 3 15 15) <
      V sourceCutoff 131071 5 16 16 - V (sourceCutoff - 131071 - h) 131071 4 15 15 at hs
    omega
  obtain ⟨G, hG, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace C hdeg i)
    (LinearMap.pi (nodeMap C hdeg)) (LinearMap.range mult) hdim
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm

end
end P0_6_1
end PackSource_P0_6_1Quotient

section PackSource_P0_6_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace P0_6_1
noncomputable section

open K1 K1_10 K1_11 MvPolynomial

open K1_10_1 (Contacts denominator liftOrdinary numerator pencil planeRelation
  planeRelation_view relationBounds toScalarSource toScalarSource_atDecoder)
open P0_6 (sourceCutoff)

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

private theorem relation_at_decoder {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (P : Puncture deleted)
    (hdeg : (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 0) ≤ 131071 + h)
    (hh : h ≤ 32784) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
    (hq' : Q'.natDegree ≤ 131071) (s t : K) (S : Finset (Fin P.N)) (hS : P0.agreement ≤ S.card)
    (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) (planeRelation U V W.output) = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro j hj
    rw [pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, relation_eval]
    have hi : P.index j ∉ deleted := (P.retained _).mp ⟨j, rfl⟩
    have hcj := hc j hj
    change Q.eval (node (P.index j)) = u 0 (P.index j) + s * u 1 (P.index j) ∧
      Q'.eval (node (P.index j)) = u 0 (P.index j) ^ p + t * u 1 (P.index j) ^ p at hcj
    simp only [Puncture.nodes, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hcj.1, hcj.2]
    linear_combination W.nodes _ hi 0 0 + s * W.nodes _ hi 1 0 +
      t * W.nodes _ hi 0 1 + (s*t) * W.nodes _ hi 1 1
  · have hd := decoder_eval_degree 131071 (131071+h) _ hdeg Q Q' hq hq' s t
    have hcapacity : 131071 + 32784 < P0.agreement := by decide
    omega

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

private theorem total_bound (Q : MvPolynomial (Fin 4) K)
    (hs : Q.weightedTotalDegree scalarWeightYS ≤ 21)
    (ht : Q.weightedTotalDegree scalarWeightT ≤ 16) :
    Q.weightedTotalDegree scalarWeightTotal ≤ 37 := by
  apply Finset.sup_le
  intro e he
  have hS := (le_weightedTotalDegree scalarWeightYS he).trans hs
  have hT := (le_weightedTotalDegree scalarWeightT he).trans ht
  simp [scalarWeightYS, scalarWeightT, scalarWeightTotal, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul] at hS hT ⊢
  omega

private theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : P0.BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, K1.twist, frobenius_def]

theorem proof : P0_6.c1 := by
  intro u deleted h U V W _ hh hs
  let P := nativePuncture deleted
  let L := planeRelation U V W.output
  let a := numerator U W.output
  let b := denominator V
  have hb : b ≠ 0 := denominator_ne W.V_ne
  have hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a :=
    planeRelation_view U V W.output
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j :=
    K1_10_1_1.proof u deleted h U V W
  have hl : L ≠ 0 := by
    intro hz
    have hpos := hdeg 1
    simp [hz, relationBounds, weightedTotalDegree] at hpos
  let C : Contacts P.N L :=
    ⟨P.nodes, fun i => u 0 (P.index i), fun i => u 1 (P.index i),
      fun i => u 0 (P.index i) ^ p, fun i => u 1 (P.index i) ^ p,
      fun i => K1_10_1_2.proof u deleted h U V W (P.index i) ((P.retained _).mp ⟨i, rfl⟩)⟩
  have hN : P.N = P0.blockLength - deleted.card := by
    have hsize : P.N + deleted.card = P0.blockLength := P.size
    omega
  obtain ⟨G, hnot, hcontacts⟩ := quotientSource C hdeg hl (by omega) (hN ▸ hs)
  let Q := scalarEliminant 5 G.val a b
  have hne : Q ≠ 0 := scalarEliminant_ne_zero sourceCutoff 131071 5 16 16
    G.val L G.property hnot a b hb hview (K1_10_1_3.proof u deleted h U V W)
  have hLsource : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071+h) 1 1 1) := by
    apply (mem_filtered _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY, hbY, haS, hbS, haT, hbT⟩ := coeff_bounds L a b _ hLsource hview hb
  obtain ⟨hY,hS,hT⟩ := polynomialView_source_coefficients sourceCutoff 131071 5 16 16 G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 :=
    clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree scalarWeightYS ≤ 21 :=
    clearedEval_weight_bound scalarWeightYS 5 16 0 1 1 (polynomialView G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree scalarWeightT ≤ 16 :=
    clearedEval_weight_bound scalarWeightT 5 16 1 1 0 (polynomialView G.val) a b
      (by simpa using hT) haT hbT (by decide)
  refine ⟨toScalarSource Q hne hy (hs'.trans (by decide)) (ht'.trans (by decide))
    (total_bound Q hs' ht'), ?_⟩
  intro γ M hdis
  rw [toScalarSource_atDecoder]
  let S := indexedSupport P M.support
  have hS' : P0.agreement ≤ S.card := by
    rw [indexedSupport_card P M.support
      (fun i hi hid => Finset.disjoint_left.mp hdis hi hid)]
    exact M.agreement
  have hd : M.decoder.natDegree ≤ 131071 :=
    Polynomial.natDegree_le_of_degree_le (Order.le_of_lt_succ M.degree)
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 := Polynomial.natDegree_map_le.trans hd
  have hcorrect := P0_6_1.correctOn_mark P M
  have hrel := relation_at_decoder W P (le_of_eq (hdeg 0)) (by omega)
    _ _ hd hd' γ (γ ^ p) S hS' hcorrect
  apply scalarEliminant_annihilates sourceCutoff 131071 5 16 16
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ ^ p) hrel
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hcontacts i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ γ (γ ^ p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG := decoder_eval_degree 131071 sourceCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) _ _ hd hd' γ (γ ^ p)
    have hcut : sourceCutoff < 4 * P0.agreement := by decide
    omega

end
end P0_6_1
end PackSource_P0_6_1Proof

section PackSource_P0_6_2Counting
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace P0_6_2
noncomputable section

open P0 Polynomial MvPolynomial ProximityPrize.Benchmark
open P0_6 (cutDegree incidenceRatio)
open K1_10_2 (GenericRow point surface_count_with_terminal)

abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ

/-- The archived cut degree is unchanged. The marks use the retuned agreement. -/
structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i

private theorem pencil_count {u : Words} (Γ : Finset K) (F : Marks u Γ)
    (P Q : K[X]) (hP : P.degree < 131072) (hQ : Q.degree < 131072)
    (hpencil : ∀ γ (hγ : γ ∈ Γ), (F γ hγ).decoder = P + Polynomial.C γ * Q) :
    Γ.card ≤ 81937 := by
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · simp
  let S := (F r hr).support
  let mismatch (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {γ : K} (hγ : γ ∈ Γ) {i : I} (hi : i ∈ (F γ hγ).support) :
      P.eval (node i) + γ * Q.eval (node i) = u 0 i + γ * u 1 i := by
    simpa only [hpencil γ hγ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      using (F γ hγ).hits i hi
  have unique {γ δ : K} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) {i : I}
      (hi : i ∈ (F γ hγ).support) (hj : i ∈ (F δ hδ).support) (hm : mismatch i) :
      γ = δ := by
    by_contra hne
    have hγi := hits hγ hi
    have hδi := hits hδ hj
    have h := show (γ - δ) * (Q.eval (node i) - u 1 i) = 0 by
      linear_combination hγi - hδi
    have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at hγi
    exact hm.elim (fun hbad => hbad hγi) (fun hbad => hbad he)
  have witness (γ : ↥(Γ.erase r)) :
      ∃ i ∈ (F γ.val (Finset.mem_erase.mp γ.property).2).support, mismatch i := by
    let M := F γ.val (Finset.mem_erase.mp γ.property).2
    by_contra hw
    apply M.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose index hindex hmismatch using witness
  let f : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun γ =>
    ⟨index γ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp γ.property).1
        (unique (Finset.mem_erase.mp γ.property).2 hr (hindex γ) hi (hmismatch γ))⟩⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have he : index γ = index δ := congrArg Subtype.val h
    have hδ := hindex δ
    rw [← he] at hδ
    exact Subtype.ext (unique (Finset.mem_erase.mp γ.property).2
      (Finset.mem_erase.mp δ.property).2 (hindex γ) hδ (hmismatch γ))
  have hcard := Finset.card_le_card_of_injective hf
  have he := Finset.card_erase_add_one hr
  have hS : 180208 ≤ S.card := (F r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcard
  omega

private theorem persistent_count {u : Words} {Γ : Finset K} {F : Marks u Γ}
    (C : TaylorCuts F) (J : Ideal GenericRow) (W : Finset K) (hW : W ⊆ Γ)
    (hzero : ∀ γ (hγ : γ ∈ W), point γ (F γ (hW hγ)).decoder ∈ zeroLocus Frac J)
    (hpersistent : 131072 ≤ {i | C.equation i ∈ J}.ncard) :
    W.card ≤ 81937 := by
  classical
  let keep := Finset.univ.filter fun i => C.equation i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersistent.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P := Lagrange.interpolate S node (u 0)
  let Q := Lagrange.interpolate S node (u 1)
  have hinj : Set.InjOn node (S : Set I) := node.injective.injOn
  have hP : P.degree < (131072 : ℕ) := by
    simpa only [P, hcard] using Lagrange.degree_interpolate_lt (u 0) hinj
  have hQ : Q.degree < (131072 : ℕ) := by
    simpa only [Q, hcard] using Lagrange.degree_interpolate_lt (u 1) hinj
  apply pencil_count W (fun γ hγ => F γ (hW hγ)) P Q hP hQ
  intro γ hγ
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact (F γ (hW hγ)).degree
  · rw [hcard]
    have hm : (Polynomial.C γ * Q).degree ≤ Q.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) Q.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hP (hm.trans_lt hQ))
  · intro i hi
    have hcut := (Finset.mem_filter.mp (hS hi)).2
    have hz := hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (C.agrees γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])

private theorem terminal_price_le : (81937 : ℚ) ≤ incidenceRatio := by
  change ((81937 : ℕ) : ℚ) ≤ ((1236945993621 : ℕ) : ℚ) / ((49137 : ℕ) : ℚ)
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast (show (81937 : ℕ) * 49137 ≤ 1236945993621 by decide)

/-- Every proper cut is charged against the agreement left after its persistent nodes. -/
private theorem node_incidence (m : ℕ) (hm : m < 131072) :
    (((Fintype.card I - m) * cutDegree : ℕ) : ℚ) ≤
      incidenceRatio * ((180208 - m : ℕ) : ℚ) := by
  rw [IRSProfile.card_index, Nat.cast_mul]
  have hn : (262144 - m) * 49137 ≤ 131073 * (180208 - m) := by omega
  have hq : ((262144 - m : ℕ) : ℚ) * 49137 ≤ 131073 * ((180208 - m : ℕ) : ℚ) := by
    exact_mod_cast hn
  change ((262144 - m : ℕ) : ℚ) * (cutDegree : ℚ) ≤
    (((131073 : ℕ) * cutDegree : ℕ) : ℚ) / 49137 * ((180208 - m : ℕ) : ℚ)
  rw [Nat.cast_mul, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (((262144 - m : ℕ) : ℚ) * 49137) * (cutDegree : ℚ) := by ring
    _ ≤ (131073 * ((180208 - m : ℕ) : ℚ)) * (cutDegree : ℚ) :=
      mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

theorem count_chart {u : Words} {Γ : Finset K} (F : Marks u Γ) (C : TaylorCuts F)
    (g s : GenericRow) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 37)
    (hroot : ∀ γ (hγ : γ ∈ Γ), MvPolynomial.eval (point γ (F γ hγ).decoder) g = 0 ∧
      MvPolynomial.eval (point γ (F γ hγ).decoder) s ≠ 0) :
    (Γ.card : ℚ) ≤ 37 * incidenceRatio ^ 2 := by
  classical
  let x : Γ → (Fin 3 → Frac) := fun γ => point γ (F γ γ.property).decoder
  have hinj : Function.Injective x := by
    intro γ δ h
    apply Subtype.ext
    apply Polynomial.C_injective
    apply IsFractionRing.injective K[X] Frac
    exact congrFun h 1
  let S := Γ.attach.image x
  have hcard : S.card = Γ.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [← hcard]
  refine surface_count_with_terminal g s hg C.equation (L := 131072) (A := 180208)
    (by decide) hdeg C.degree ((by norm_num : (1 : ℚ) ≤ 81937).trans terminal_price_le)
    node_incidence S
    (fun y hy => ?_) (fun y hy => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot γ γ.property
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    let M := F γ γ.property
    have hsub : (M.support : Set I) ⊆ {i | aeval (x γ) (C.equation i) = 0} :=
      fun i hi => (C.agrees γ γ.property i).mpr (M.hits i hi)
    exact M.agreement.trans (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub)
  · let W := Γ.attach.filter fun γ => x γ ∈ zeroLocus Frac J
    let V := W.image (fun γ : Γ => (γ : K))
    have hV : V ⊆ Γ := fun γ hγ => by
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact δ.property
    have hV0 : ∀ γ (hγ : γ ∈ V), point γ (F γ (hV hγ)).decoder ∈ zeroLocus Frac J := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hδ).2
    have hcount := persistent_count C J V hV hV0 hJ
    have hW : W.card = V.card := (Finset.card_image_of_injective W Subtype.val_injective).symm
    have he : (S : Set (Fin 3 → Frac)) ∩ zeroLocus Frac J = (W.image x : Finset _) := by
      ext y
      simp only [S, W, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨γ, hγ, rfl⟩, h⟩
        exact ⟨γ, ⟨hγ, h⟩, rfl⟩
      · rintro ⟨γ, ⟨hγ, h⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, h⟩
    rw [he, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, hW]
    exact (by exact_mod_cast hcount : (V.card : ℚ) ≤ 81937).trans terminal_price_le

end
end P0_6_2
end PackSource_P0_6_2Counting

section PackSource_P0_6_2Proof
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace P0_6_2
noncomputable section

open P0 MvPolynomial
open P0_6 (ScalarSource incidenceRatio)
open K1_10_2 (Row RegularRoot derivativeOrder toGeneric atTrajectory point)
open scoped Polynomial

-- These archived lemmas are independent of the agreement threshold.
open private regroup regroup_degree specialize specialize_regroup decoderView
  decoderView_injective decoderView_degree eval_decoderView exists_simple_derivative
  eval_specialize specialize_iterate specialize_pderiv from ProximityPrize.SubmissionLower.Fast069
open private nodeCut nodeCut_degree eval_nodeCut from ProximityPrize.SubmissionLower.Fast069
open private derivativeOrder_degree K1_10_2.eval_toGeneric from ProximityPrize.SubmissionLower.Fast069

/-- Assign a simple derivative chart at each selected root of the scalar source. -/
private theorem assign_charts (A : ScalarSource) (Γ : Finset K)
    (P : ∀ γ ∈ Γ, K[X])
    (hF : ∀ γ (hγ : γ ∈ Γ), A.atLabel γ ≠ 0 ∧ A.atDecoder γ (P γ hγ) = 0) :
    ∃ g : Row, g.totalDegree ≤ 37 ∧
      ∀ γ (hγ : γ ∈ Γ), ∃ j : Fin 5, RegularRoot (derivativeOrder g j) γ (P γ hγ) := by
  let g := regroup A.poly
  refine ⟨g, regroup_degree A, ?_⟩
  intro γ hγ
  let Q := P γ hγ
  let specializeLabel := specialize (Polynomial.C γ) (Polynomial.C (γ ^ p))
  have hview : specializeLabel g = decoderView (A.atLabel γ) :=
    specialize_regroup A.poly γ (γ ^ p)
  have hne : specializeLabel g ≠ 0 := by
    rw [hview]
    intro hz
    exact (hF γ hγ).1 (decoderView_injective (hz.trans (map_zero _).symm))
  have hdegree : (specializeLabel g).natDegree ≤ 5 := by
    rw [hview]
    apply (decoderView_degree _).trans
    rw [degreeOf_eq_sup, Finset.sup_le_iff]
    intro e he
    exact (le_degreeOf_of_mem_support 1 (support_map_subset _ _ he)).trans A.y_degree
  have hroot : (specializeLabel g).IsRoot Q := by
    change (specializeLabel g).eval Q = 0
    rw [hview, eval_decoderView]
    exact (hF γ hγ).2
  obtain ⟨j, hj, hz, hsep⟩ :=
    exists_simple_derivative p 5 _ hne hdegree (by decide) Q hroot
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (derivativeOrder g ⟨j, hj⟩) = 0
    rw [← eval_specialize, derivativeOrder, specialize_iterate]
    exact hz
  · change MvPolynomial.eval ![Q, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (pderiv 0 (derivativeOrder g ⟨j, hj⟩)) ≠ 0
    rw [← eval_specialize, specialize_pderiv, derivativeOrder, specialize_iterate]
    exact hsep


theorem proof : P0_6.c2 := by
  classical
  intro u A Γ hΓ
  let F : Marks u Γ := fun γ hγ => Classical.choose (hΓ γ hγ).2
  have hF (γ : K) (hγ : γ ∈ Γ) :
      A.atLabel γ ≠ 0 ∧ A.atDecoder γ (F γ hγ).decoder = 0 :=
    ⟨(hΓ γ hγ).1, Classical.choose_spec (hΓ γ hγ).2⟩
  obtain ⟨g, hg, hassign⟩ := assign_charts A Γ (fun γ hγ => (F γ hγ).decoder) hF
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, RegularRoot (derivativeOrder g j) γ (F γ hγ).decoder
  have hsub (j : Fin 5) : charts j ⊆ Γ := Finset.filter_subset _ _
  have hcover : Γ ⊆ Finset.univ.biUnion charts := by
    intro γ hγ
    obtain ⟨j, hj⟩ := hassign γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  have hchart (j : Fin 5) : ((charts j).card : ℚ) ≤ 37 * incidenceRatio ^ 2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀, hγ₀⟩
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    let G := derivativeOrder g j
    let M : Marks u (charts j) := fun γ hγ => F γ (hsub j hγ)
    have hregular (γ : K) (hγ : γ ∈ charts j) : RegularRoot G γ (M γ hγ).decoder := by
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hγ).2
      exact hr
    have hG : G.totalDegree ≤ 37 := (derivativeOrder_degree g j).trans hg
    let C : TaylorCuts M :=
      ⟨nodeCut u G, nodeCut_degree u G hG, fun γ hγ i =>
        eval_nodeCut u G γ (M γ hγ).decoder (hregular γ hγ) (M γ hγ).degree i⟩
    have hinj := IsFractionRing.injective K[X] Frac
    have hGne : G ≠ 0 := by
      intro h
      exact (hregular γ₀ hγ₀).2 (by simp [h, atTrajectory])
    have hgne : toGeneric G ≠ 0 := by
      intro h
      exact hGne (MvPolynomial.map_injective (algebraMap K[X] Frac) hinj
        (by simpa [toGeneric] using h))
    have hgd : (toGeneric G).totalDegree ≤ 37 := by
      simpa only [toGeneric, totalDegree, support_map_of_injective G hinj] using hG
    apply count_chart M C (toGeneric G) (toGeneric (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr, hs⟩ := hregular γ hγ
    rw [K1_10_2.eval_toGeneric, K1_10_2.eval_toGeneric, hr, map_zero]
    exact ⟨rfl, by simpa only [map_zero] using hinj.ne hs⟩
  have hnat : Γ.card ≤ ∑ j : Fin 5, (charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card : ℚ) ≤ 5 * 37 * incidenceRatio ^ 2 := by
    calc
      (Γ.card : ℚ) ≤ ∑ j : Fin 5, ((charts j).card : ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j : Fin 5, (37 * incidenceRatio ^ 2 : ℚ) :=
        Finset.sum_le_sum fun j _ => hchart j
      _ = _ := by simp; ring
  have hrounded : (Γ.card : ℚ) ≤ (P0_6.regularPrice : ℚ) := by
    unfold P0_6.regularPrice
    apply hrat.trans
    rw [show (5 : ℚ) * 37 = ((185 : ℕ) : ℚ) by norm_num]
    exact Nat.le_ceil _
  exact_mod_cast hrounded

end
end P0_6_2
end PackSource_P0_6_2Proof

section PackSource_P0_8Defs
set_option autoImplicit true
namespace P0_8
noncomputable section

open Polynomial P0

/-- The homogeneous direction and four output coefficients on the puncture.
The numerator contents are U,V; den is a Hilbert-90 denominator with no domain zeros. -/
structure Direction (u : Words) (deleted : Finset I) where
  den : K[X]
  U : K[X]
  V : K[X]
  A : Fin 2 → K[X]
  out : Fin 2 → Fin 2 → K[X]
  den_nodes : ∀ i, den.eval (node i) ≠ 0
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ den
  coprime : IsCoprime U V
  phase : U * den.map twist = V * den
  degrees_eq : V.natDegree = U.natDegree
  primitive : IsCoprime (A 0) (A 1)
  height : U.natDegree + amplitudeDegree (A 0) (A 1) + deleted.card ≤ heightCap
  out_degree : ∀ i j, (out i j).degree <
    (k + U.natDegree + amplitudeDegree (A 0) (A 1) : ℕ)
  nodes : ∀ x ∉ deleted, ∀ i j, (out i j).eval (node x) =
    U.eval (node x) * ((A i).map twist).eval (node x) * u j x -
    V.eval (node x) * (A j).eval (node x) * twist (u i x)

variable {u : Words} {deleted : Finset I}

def Direction.s (F : Direction u deleted) := amplitudeDegree (F.A 0) (F.A 1)

def Direction.amp (F : Direction u deleted) (γ : K) := F.A 0 + C γ * F.A 1

/-- Guards on the original finite label for the one-anchor determinant proof. -/
structure Regular (F : Direction u deleted) (γ : K) : Prop where
  amp_ne : F.amp γ ≠ 0
  degree_eq : (F.amp γ).natDegree = F.s
  adjacent : IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit : IsCoprime (F.amp γ) F.U
  node_unit : ∀ i ∉ deleted, (F.amp γ).eval (node i) ≠ 0

def excluded (F : Direction u deleted) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Regular F γ)

/-- L/G interpolates A₀u₁−A₁u₀ on the puncture; the two pole conditions
retain full divisibility and the strict bound is an order-at-infinity bound. -/
structure CrossLift (F : Direction u deleted) where
  G : K[X]
  L : K[X]
  monic : G.Monic
  left : G ∣ F.U
  right : G.map twist ∣ F.V
  degree_lt : L.degree < (k + F.s + G.natDegree : ℕ)
  nodes : ∀ i ∉ deleted, L.eval (node i) = G.eval (node i) *
    ((F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i)

/-- After the affine translation by η and subtraction of its actual decoder,
the sole remaining rational offset is proper and reduced. -/
structure Offset (F : Direction u deleted) {η : K} (anchor : BadMark u η) where
  pencil : K[X]
  pencil_degree : pencil.degree < k
  E : K[X]
  Q : K[X]
  E_monic : E.Monic
  left : E ∣ F.U
  right : E.map twist ∣ F.V
  proper : Q.degree < E.degree
  reduced : IsCoprime Q E
  raw : I → K
  raw_fixed : ∀ i ∉ deleted, twist (raw i) = raw i
  first : ∀ i ∉ deleted, u 0 i + η * u 1 i - anchor.decoder.eval (node i) =
    (F.amp η).eval (node i) * raw i / F.den.eval (node i)
  second : ∀ i ∉ deleted, u 1 i - pencil.eval (node i) =
    Q.eval (node i) / E.eval (node i) + (F.A 1).eval (node i) * raw i / F.den.eval (node i)

end
end P0_8
end PackSource_P0_8Defs

section PackSource_P0_8Exceptions
set_option autoImplicit true
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace P0_8
noncomputable section

open Polynomial P0
open ProximityPrize.Benchmark
open scoped BigOperators

variable {u : Words} {deleted : Finset I}

private theorem coprime_amplitudes (F : Direction u deleted) {γ δ : K} (hne : γ ≠ δ) :
    IsCoprime (F.amp γ) (F.amp δ) := by
  have hd : F.amp δ - F.amp γ * 1 = C (δ - γ) * F.A 1 := by
    simp only [Direction.amp, mul_one, map_sub]
    ring
  have hunit : IsUnit (C (δ - γ)) :=
    isUnit_C.mpr (sub_ne_zero.mpr hne.symm).isUnit
  apply (IsCoprime.sub_mul_left_right_iff (x := F.amp γ) (y := F.amp δ) (z := 1)).mp
  rw [hd, isCoprime_mul_unit_left_right hunit]
  exact F.primitive.add_mul_right_left _

/-- Each failed coprimality test contributes a positive-degree factor of the
same nonzero polynomial. The factors are coprime across distinct labels. -/
private theorem card_of_failed_coprime (F : Direction u deleted) (S : Finset K)
    (Q : K → K[X]) {P : K[X]} (hP : P ≠ 0)
    (hbad : ∀ γ ∈ S, ¬ IsCoprime (F.amp γ) (Q γ))
    (hdiv : ∀ γ ∈ S, GCDMonoid.gcd (F.amp γ) (Q γ) ∣ P) :
    S.card ≤ P.natDegree := by
  classical
  let g (γ : K) := GCDMonoid.gcd (F.amp γ) (Q γ)
  have hne (γ : K) (hγ : γ ∈ S) : g γ ≠ 0 := by
    intro hz
    obtain ⟨H, hH⟩ := hdiv γ hγ
    change P = g γ * H at hH
    exact hP (by simpa only [hz, zero_mul] using hH)
  have hpos (γ : K) (hγ : γ ∈ S) : 1 ≤ (g γ).natDegree := by
    by_contra! h
    have hd : (g γ).natDegree = 0 := by omega
    have hu : IsUnit (g γ) := isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (hne γ hγ), hd]
      rfl)
    exact hbad γ hγ ((gcd_isUnit_iff _ _).mp hu)
  have hpairs : (S : Set K).Pairwise (fun γ δ => IsCoprime (g γ) (g δ)) := by
    intro γ _ δ _ hne
    exact (coprime_amplitudes F hne).mono (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have hprod : (∏ γ ∈ S, g γ) ∣ P := Finset.prod_dvd_of_coprime hpairs hdiv
  calc
    S.card = ∑ γ ∈ S, (1 : ℕ) := by simp
    _ ≤ ∑ γ ∈ S, (g γ).natDegree := Finset.sum_le_sum hpos
    _ = (∏ γ ∈ S, g γ).natDegree := (natDegree_prod S g hne).symm
    _ ≤ P.natDegree := natDegree_le_of_dvd hprod hP

/-- Eliminate the label from an amplitude and its coefficient Frobenius
conjugate by taking the p-th power of the first amplitude. -/
private def eliminant (F : Direction u deleted) (q : ℕ) (σ : K →+* K) : K[X] :=
  ((F.A 0).map σ) * F.A 1 ^ q - (F.A 0 ^ q) * ((F.A 1).map σ)

private theorem gcd_dvd_eliminant (F : Direction u deleted) (q : ℕ) [ExpChar K q]
    (σ : K →+* K) (hσ : ∀ γ, σ γ = γ ^ q) (hq : q ≠ 0) (γ : K) :
    GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ eliminant F q σ := by
  have hpow : (F.amp γ)^q = F.A 0 ^ q + C (σ γ) * F.A 1 ^ q := by
    rw [Direction.amp, add_pow_expChar _ _ q, mul_pow, ← C_pow, ← hσ γ]
  have heq : eliminant F q σ =
      ((F.amp γ).map σ) * F.A 1 ^ q - (F.amp γ)^q * ((F.A 1).map σ) := by
    rw [hpow]
    simp only [eliminant, Direction.amp, Polynomial.map_add, Polynomial.map_mul, map_C]
    ring
  have hd : GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ F.amp γ :=
    gcd_dvd_left _ _
  rw [heq]
  exact dvd_sub ((gcd_dvd_right _ _).mul_right _)
    ((hd.trans (dvd_pow_self _ hq)).mul_right _)

private theorem degree_zero_of_power_dvd_map {q : ℕ} (hq : 2 ≤ q) {σ : K →+* K}
    {P : K[X]} (hdiv : P ^ q ∣ P.map σ) : P.natDegree = 0 := by
  by_cases hP : P = 0
  · simp [hP]
  have h := natDegree_le_of_dvd hdiv (Polynomial.map_ne_zero hP)
  rw [natDegree_pow, natDegree_map_eq_of_injective σ.injective] at h
  have htwo := (Nat.mul_le_mul_right P.natDegree hq).trans h
  omega

private theorem eliminant_ne (F : Direction u deleted) {q : ℕ} (hq : 2 ≤ q)
    (σ : K →+* K) (hs : F.s ≠ 0) : eliminant F q σ ≠ 0 := by
  intro hz
  have hcross : ((F.A 0).map σ) * F.A 1 ^ q = F.A 0 ^ q * ((F.A 1).map σ) :=
    sub_eq_zero.mp hz
  have hp : IsCoprime (F.A 0 ^ q) (F.A 1 ^ q) := F.primitive.pow
  have h0 : F.A 0 ^ q ∣ (F.A 0).map σ := hp.dvd_of_dvd_mul_right
    (by rw [hcross]; exact dvd_mul_right _ _)
  have h1 : F.A 1 ^ q ∣ (F.A 1).map σ := hp.symm.dvd_of_dvd_mul_left
    (by rw [← hcross]; exact dvd_mul_left _ _)
  exact hs (by simp [Direction.s, amplitudeDegree, degree_zero_of_power_dvd_map hq h0,
    degree_zero_of_power_dvd_map hq h1])

private theorem eliminant_degree (F : Direction u deleted) (q : ℕ) (σ : K →+* K) :
    (eliminant F q σ).natDegree ≤ (q + 1) * F.s := by
  have h0 : (F.A 0).natDegree ≤ F.s := le_max_left _ _
  have h1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  rw [eliminant, Nat.add_mul, one_mul]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [add_comm]
    exact natDegree_mul_le_of_le (natDegree_map_le.trans h0) (natDegree_pow_le_of_le q h1)
  · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le q h0) (natDegree_map_le.trans h1)

private theorem same_label {a b γ δ : K} (hpair : a ≠ 0 ∨ b ≠ 0)
    (hγ : a + γ * b = 0) (hδ : a + δ * b = 0) : γ = δ := by
  have hb : b ≠ 0 := by
    intro hz
    exact hpair.elim (fun ha => ha (by simpa [hz] using hγ)) (fun hb => hb hz)
  apply sub_eq_zero.mp
  refine (mul_eq_zero.mp (show (γ - δ) * b = 0 from ?_)).resolve_right hb
  linear_combination hγ - hδ

private theorem top_pair (F : Direction u deleted) :
    (F.A 0).coeff F.s ≠ 0 ∨ (F.A 1).coeff F.s ≠ 0 := by
  have at_top (P : K[X]) (hp : P ≠ 0) (hd : P.natDegree = F.s) :
      P.coeff F.s ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  by_cases h0 : F.A 0 = 0
  · exact Or.inr (at_top _ (F.primitive.ne_zero_or_ne_zero.resolve_left (by simp [h0]))
      (by simp [Direction.s, amplitudeDegree, h0]))
  by_cases h1 : F.A 1 = 0
  · exact Or.inl (at_top _ h0 (by simp [Direction.s, amplitudeDegree, h1]))
  rcases le_total (F.A 0).natDegree (F.A 1).natDegree with h | h
  · exact Or.inr (at_top _ h1 (max_eq_right h).symm)
  · exact Or.inl (at_top _ h0 (max_eq_left h).symm)

private theorem amp_degree_le (F : Direction u deleted) (γ : K) :
    (F.amp γ).natDegree ≤ F.s :=
  natDegree_add_le_of_degree_le (le_max_left _ _)
    ((natDegree_C_mul_le _ _).trans (le_max_right _ _))

private theorem card_node_failures (F : Direction u deleted) (S : Finset K)
    (hS : ∀ γ ∈ S, ∃ i : I, (F.amp γ).eval (node i) = 0) : S.card ≤ blockLength := by
  classical
  choose f hf using fun γ : S => hS γ γ.property
  rw [blockLength, ← IRSProfile.card_index, ← Fintype.card_coe]
  apply Fintype.card_le_of_injective f
  intro γ δ he
  apply Subtype.ext
  have hγ := hf γ
  have hδ := hf δ
  rw [← he] at hδ
  exact same_label
    ((F.primitive.map (evalRingHom (node (f γ)))).ne_zero_or_ne_zero)
    (by simpa [Direction.amp] using hγ)
    (by simpa [Direction.amp] using hδ)

/-- Count the rejected original labels by adjacent, content, node, and leading-coefficient failures. -/
theorem excluded_card_le (F : Direction u deleted) (Γ : Finset K) :
    (excluded F Γ).card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 := by
  classical
  let A := Γ.filter (fun γ => F.amp γ ≠ 0 ∧ ¬ IsCoprime (F.amp γ) ((F.amp γ).map twist))
  let U := Γ.filter (fun γ => ¬ IsCoprime (F.amp γ) F.U)
  let N := Γ.filter (fun γ => ∃ i : I, (F.amp γ).eval (node i) = 0)
  let L := Γ.filter (fun γ => (F.amp γ).coeff F.s = 0)
  have ha : A.card ≤ (p + 1) * F.s := by
    by_cases hs : F.s = 0
    · have hempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro γ hγ
        obtain ⟨hamp, hbad⟩ := (Finset.mem_filter.mp hγ).2
        have hd := amp_degree_le F γ
        rw [hs, Nat.le_zero] at hd
        have hunit : IsUnit (F.amp γ) := isUnit_iff_degree_eq_zero.mpr (by
          rw [degree_eq_natDegree hamp, hd]
          rfl)
        exact hbad (by simpa only [mul_one] using
          (isCoprime_mul_unit_left_left hunit 1 _).mpr isCoprime_one_left)
      simp [hempty]
    · exact (card_of_failed_coprime F A (fun γ => (F.amp γ).map twist)
        (eliminant_ne F (by decide : 2 ≤ p) twist hs)
        (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
        (fun γ _ => gcd_dvd_eliminant F p twist (fun _ => rfl) (by decide) γ)).trans
          (eliminant_degree F p twist)
  have hu : U.card ≤ F.U.natDegree :=
    card_of_failed_coprime F U (fun _ => F.U) F.U_ne
      (fun _ hγ => (Finset.mem_filter.mp hγ).2) (fun _ _ => gcd_dvd_right _ _)
  have hn : N.card ≤ blockLength :=
    card_node_failures F N (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hl : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro γ hγ δ hδ
    exact same_label (top_pair F)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hγ).2)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hδ).2)
  have hsub : excluded F Γ ⊆ ((A ∪ U) ∪ N) ∪ L := by
    intro γ hγ
    obtain ⟨hΓ, hbad⟩ := Finset.mem_filter.mp hγ
    by_contra h
    simp only [Finset.mem_union, A, U, N, L, Finset.mem_filter, hΓ, true_and,
      not_or] at h
    obtain ⟨⟨⟨hA, hU⟩, hN⟩, hL⟩ := h
    have hne : F.amp γ ≠ 0 := by
      intro hz
      exact hL (by simp [hz])
    exact hbad ⟨hne, natDegree_eq_of_le_of_coeff_ne_zero (amp_degree_le F γ) hL,
      not_not.mp (fun hbadA => hA ⟨hne, hbadA⟩), not_not.mp hU,
      fun i _ hi => hN ⟨i, hi⟩⟩
  have hcount := Finset.card_le_card hsub
  have hAU := Finset.card_union_le A U
  have hAUN := Finset.card_union_le (A ∪ U) N
  have hAUNL := Finset.card_union_le ((A ∪ U) ∪ N) L
  omega

end
end P0_8
end PackSource_P0_8Exceptions

section PackSource_P0_8Lift
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace P0_8
noncomputable section

open Polynomial P0
open K1_12 (eq_on_puncture natDegree_lt_of_degree_lt_pos eval_unit_of_dvd)
-- This donor lemma uses only the puncture and the two amplitude and lift pairs.
open private cancel_pair from ProximityPrize.SubmissionLower.Fast068

theorem eval_twist (P : K[X]) (i : I) :
    (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  K1_12.eval_twist P i

theorem cross_lift {u deleted} (F : Direction u deleted) : Nonempty (CrossLift F) := by
  classical
  let d := k + F.U.natDegree + F.s
  let w (i : I) := (F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i
  let A' (j : Fin 2) := (F.A j).map twist
  let P (j : Fin 2) := F.A 0 * F.out j 1 - F.A 1 * F.out j 0
  let P' (j : Fin 2) := A' 1 * F.out 0 j - A' 0 * F.out 1 j
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
  have hmargin : k + 3 * heightCap ≤ blockLength := by decide
  have hroom : d + 2 * F.s + deleted.card ≤ blockLength := by
    dsimp only [d]
    omega
  have hk : 0 < k := by decide
  have hpos : 0 < d := by dsimp only [d]; omega
  have ha (j : Fin 2) : (F.A j).natDegree ≤ F.s := by
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have ha' (j : Fin 2) : (A' j).natDegree ≤ F.s := natDegree_map_le.trans (ha j)
  have hout (i j : Fin 2) : (F.out i j).natDegree < d :=
    natDegree_lt_of_degree_lt_pos hpos (F.out_degree i j)
  have hprod {a : K[X]} (ha : a.natDegree ≤ F.s) (i j : Fin 2) :
      (a * F.out i j).natDegree < d + F.s :=
    natDegree_mul_le.trans_lt (by have := hout i j; omega)
  obtain ⟨leftLift,hY,hYn⟩ := cancel_pair deleted (fun i => F.U.eval (node i)*w i) A' P d F.s
    (by simp only [A', natDegree_map_eq_of_injective twist.injective]; rfl)
    (F.primitive.map (Polynomial.mapRingHom twist)) hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha 0) j 1) (hprod (ha 1) j 0)))
    (by intro i hi j; simp only [P, A', w, eval_sub, eval_mul, F.nodes i hi]; ring)
  obtain ⟨rightLift,hZ,hZn⟩ := cancel_pair deleted (fun i => F.V.eval (node i)*twist (w i)) F.A P' d F.s
    rfl F.primitive hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha' 1) 0 j) (hprod (ha' 0) 1 j)))
    (by intro i hi j
        simp only [P', A', w, eval_sub, eval_mul, F.nodes i hi, eval_twist, map_sub, map_mul]
        ring)
  let f : RatFunc K := algebraMap K[X] (RatFunc K) leftLift / algebraMap K[X] (RatFunc K) F.U
  have heq : f.num * F.U = leftLift * f.denom := (RatFunc.num_mul_eq_mul_denom_iff F.U_ne).mpr rfl
  have hn (i : I) (hi : i ∉ deleted) : f.num.eval (node i) = f.denom.eval (node i) * w i := by
    have h := congrArg (eval (node i)) heq
    simp only [eval_mul, hYn i hi] at h
    apply mul_left_cancel₀ (eval_unit_of_dvd F.U_dvd (F.den_nodes i))
    linear_combination h
  have hleft : f.denom ∣ F.U := RatFunc.denom_div_dvd _ _
  have hdegG := natDegree_le_of_dvd hleft F.U_ne
  have hnf : f.num.natDegree < k + F.s + f.denom.natDegree := by
    by_cases hzero : f.num = 0
    · simp [hzero]
    have hy : leftLift ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at heq
      exact mul_ne_zero hzero F.U_ne heq
    have h := congrArg natDegree heq
    rw [natDegree_mul hzero F.U_ne, natDegree_mul hy f.denom_ne_zero] at h
    dsimp [d] at hY
    omega
  have heq' : f.denom.map twist * rightLift = f.num.map twist * F.V := by
    apply eq_on_puncture (deleted := deleted) (d := d + F.U.natDegree)
    · change d + F.U.natDegree + deleted.card ≤ blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have hg : (f.denom.map twist).natDegree ≤ f.denom.natDegree := natDegree_map_le
      omega
    · apply natDegree_mul_le.trans_lt
      have hg : (f.num.map twist).natDegree ≤ f.num.natDegree := natDegree_map_le
      have hh := F.degrees_eq
      dsimp [d]
      omega
    · intro i hi
      simp only [eval_mul, eval_twist, hn i hi, hZn i hi, map_mul]
      ring
  have hcop : IsCoprime (f.denom.map twist) (f.num.map twist) :=
    f.isCoprime_num_denom.symm.map (Polynomial.mapRingHom twist)
  exact ⟨⟨f.denom, f.num, f.monic_denom, hleft,
    hcop.dvd_of_dvd_mul_left (by rw [← heq']; exact dvd_mul_right _ _),
    degree_le_natDegree.trans_lt (by exact_mod_cast hnf), hn⟩⟩

end
end P0_8
end PackSource_P0_8Lift

section PackSource_P0_8Split
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace P0_8
noncomputable section

open Polynomial P0 FrobeniusLocator

/-- Extract the normalized homogeneous rational direction on the actual puncture. -/
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    Nonempty (Direction u (fixedNodes R))

/-- Use a regular original decoder to translate the pencil and construct the reduced offset. -/
def c2 : Prop :=
  ∀ {u deleted} (F : Direction u deleted) (_H : CrossLift F)
    {η : K} (m : BadMark u η), Disjoint m.support deleted → Regular F η →
    Nonempty (Offset F m)

/-- Clear the offset and normalize the scalar marks on the selected witnesses. -/
def c3 : Prop :=
  ∀ {u deleted} (F : Direction u deleted) (Γ : Finset K),
    (∀ γ ∈ Γ, Regular F γ) → ∀ (m : ∀ g : Γ, BadMark u g.val),
    (∀ g, Disjoint (m g).support deleted) →
    ∀ (η ζ : Γ), ζ.val ≠ η.val → ∀ O : Offset F (m η),
    ∃ M : AnchorModel u deleted,
      M.shift = η.val ∧ M.pencil₀ = (m η).decoder ∧ M.pencil₁ = O.pencil ∧
      M.E = O.E ∧ M.Q = O.Q ∧
      ∃ S : Γ → K[X], ∃ marks : ∀ g : Γ, AnchorMark M g.val (S g),
        ∀ g, (marks g).bad = m g

/-- A second decoder with the same scalar explains its own affine
combination on the FIRST decoder's support as well. -/
private theorem other_hits {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) (i : I) (hi : i ∈ m.bad.support) :
    n.bad.decoder.eval (node i) = u 0 i + δ * u 1 i := by
  have hd := Finset.disjoint_left.mp m.avoids_deleted hi
  have h0 := M.first_word i hd
  have h1 := M.second_word i hd
  have h := congrArg (eval (node i)) n.identity
  simp only [AnchorModel.decoder, AnchorModel.amplitude, AnchorModel.label, eval_sub,
    eval_mul, eval_C, eval_add, m.scalar_hits i hi] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show M.E.eval (node i) * _ = 0 from ?_)).resolve_left (M.E_nodes i)
  linear_combination h - h0 - (δ - M.shift) * h1

private theorem same_scalar_label {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) : γ = δ := by
  by_contra hne
  let V := (δ-γ)⁻¹ • (n.bad.decoder - m.bad.decoder)
  have hd : δ-γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hV : V.degree < k := Principal.degree_smul_lt _
    (Principal.degree_sub_lt n.bad.degree m.bad.degree)
  have hv (i : I) (hi : i ∈ m.bad.support) : V.eval (node i) = u 1 i := by
    simp only [V, eval_smul, eval_sub, smul_eq_mul, other_hits m n i hi, m.bad.hits i hi]
    field_simp [hd]
    ring
  apply m.bad.nonjoint
  refine ⟨⟨m.bad.decoder - γ • V, Principal.degree_sub_lt m.bad.degree
    (Principal.degree_smul_lt _ hV), ?_⟩, ⟨V, hV, hv⟩⟩
  intro i hi
  simp only [eval_sub, eval_smul, smul_eq_mul, m.bad.hits i hi, hv i hi]
  ring

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : P0.c8 := by
  classical
  intro u hu T R D B sat par unit Γ bad normal
  by_cases hsmall : Γ.card ≤ anchorFee
  · exact Or.inl hsmall
  right
  obtain ⟨γ, hγ⟩ := Finset.card_pos.mp (show 0 < Γ.card by omega)
  obtain ⟨F⟩ := h1 u hu T R D B sat par unit ⟨γ, normal γ hγ, bad_mark u Γ bad γ hγ⟩
  let book := excluded F Γ
  have hbook : book ⊆ Γ := Finset.filter_subset _ _
  have hcard : book.card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 :=
    excluded_card_le F Γ
  have hbudget : book.card + 1 ≤ anchorFee := by
    have height := F.height
    change F.U.natDegree + F.s + (fixedNodes R).card ≤ heightCap at height
    have hprod := Nat.mul_le_mul_left p (show F.s ≤ heightCap by omega)
    rw [Nat.add_mul, one_mul] at hcard
    rw [← anchor_fee_exact]
    omega
  let Δ := Γ \ book
  have hbig : 1 < Δ.card := by
    have hpart := Finset.card_sdiff_add_card_eq_card hbook
    change Δ.card + book.card = Γ.card at hpart
    omega
  have regular (δ : K) (hd : δ ∈ Δ) : Regular F δ := by
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hd
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hin, h⟩)
  let m (g : Δ) := Classical.choice (bad_mark u Γ bad g.val (Finset.mem_sdiff.mp g.property).1)
  have avoid (g : Δ) : Disjoint (m g).support (fixedNodes R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (Finset.mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).hits i hi)
  obtain ⟨η, hη, ζ, hζ, hne⟩ := Finset.one_lt_card.mp hbig
  let a : Δ := ⟨η, hη⟩
  let b : Δ := ⟨ζ, hζ⟩
  obtain ⟨lift⟩ := cross_lift F
  obtain ⟨O⟩ := h2 F lift (m a) (avoid a) (regular η hη)
  obtain ⟨M, _, _, _, _, _, S, marks, _⟩ := h3 F Δ regular m avoid a b hne.symm O
  let scalar (γ : K) : K[X] := if h : γ ∈ Δ then S ⟨γ, h⟩ else 0
  have hmarked (γ : K) (hγ : γ ∈ Δ) : AnchorMark M γ (scalar γ) := by
    simpa only [scalar, dite_eq_left hγ] using marks ⟨γ, hγ⟩
  refine ⟨book, hbook, by omega, M, ⟨⟨scalar, hmarked, ?_⟩⟩⟩
  intro γ hγ δ hδ he
  exact same_scalar_label (hmarked γ hγ) (he ▸ hmarked δ hδ)

end
end P0_8
end PackSource_P0_8Split

section PackSource_P0_8_1Proof
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace P0_8_1
noncomputable section

open Polynomial P0 FrobeniusLocator

/-- The two pencils in the shared plane are jointly primitive, so the
constant contents in the parallel presentation are coprime. -/
private theorem coprime_contents {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (P0_6.leftCoeff B) (P0_6.rightCoeff B)) :
    IsCoprime B.a B.b := by
  apply (gcd_isUnit_iff _ _).mp
  apply P.primitive
  · intro i
    exact (gcd_dvd_left B.a B.b).trans (dvd_mul_right _ _)
  · intro j
    rw [P0_6.rightCoeff, dvd_neg]
    exact (gcd_dvd_right B.a B.b).trans (dvd_mul_right _ _)

private theorem plane_height {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (P0_6.leftCoeff B) (P0_6.rightCoeff B))
    (par : Parallel B) (hdeg : B.b.natDegree = B.a.natDegree) :
    D.height = B.a.natDegree + amplitudeDegree (B.α 0) (B.α 1) := by
  let s := amplitudeDegree (B.α 0) (B.α 1)
  have hA (i : Fin 2) : (B.α i).natDegree ≤ s := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hL (i : Fin 2) : (P0_6.leftCoeff B i).natDegree ≤ B.a.natDegree + s := by
    change B.α = B.β at par
    unfold P0_6.leftCoeff
    rw [← par]
    exact natDegree_mul_le_of_le le_rfl (natDegree_map_le.trans (hA i))
  have hR (j : Fin 2) : (P0_6.rightCoeff B j).natDegree ≤ B.a.natDegree + s := by
    rw [P0_6.rightCoeff, natDegree_neg, ← hdeg]
    exact natDegree_mul_le_of_le le_rfl (hA j)
  have hmax := max_le (max_le (hL 0) (hL 1)) (max_le (hR 0) (hR 1))
  exact le_antisymm (P.height_eq ▸ hmax) (hdeg ▸ B.second_degree)

private theorem plane_nodes {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (P0_6.leftCoeff B) (P0_6.rightCoeff B))
    (par : Parallel B) (x : I) (hx : x ∉ fixedNodes R) (i j : Fin 2) :
    (P.output j i).eval (node x) =
      B.a.eval (node x) * ((B.α i).map twist).eval (node x) * u j x -
      B.b.eval (node x) * (B.α j).eval (node x) * twist (u i x) := by
  change B.α = B.β at par
  simpa only [P0_6.leftCoeff, P0_6.rightCoeff, eval_mul, eval_neg, neg_mul,
    ← sub_eq_add_neg, ← par, twist, frobenius_def] using (P.nodes x hx j i).symm

/-- Construct the homogeneous direction with the four output lifts on the
actual puncture. -/
theorem proof : P0_8.c1 := by
  intro u hu T R D B _ par hnorm _
  obtain ⟨P⟩ := P0_6.plane_of_rankThree B
  change K1.sixNorm B.a = K1.sixNorm B.b at hnorm
  obtain ⟨den, hden, hphase, hnodes⟩ := K1_12_1.denominator B.b_ne hnorm
  have hden' : den.map twist ≠ 0 := (Polynomial.map_ne_zero_iff twist.injective).mpr hden
  have hdeg := congrArg (fun Q : K[X] => Q.natDegree) hphase
  change (B.a * den.map twist).natDegree = (B.b * den).natDegree at hdeg
  rw [natDegree_mul B.a_ne hden', natDegree_mul B.b_ne hden,
    natDegree_map_eq_of_injective twist.injective] at hdeg
  have hdeg' : B.b.natDegree = B.a.natDegree := by omega
  have hcop := coprime_contents B P
  have hheight := plane_height B P par hdeg'
  have hdvd : B.a ∣ den := hcop.dvd_of_dvd_mul_left
    (hphase ▸ dvd_mul_right B.a (den.map twist))
  have hbudget := relation_height_le hu T
  exact ⟨{
    den := den
    U := B.a
    V := B.b
    A := B.α
    out := fun i j => P.output j i
    den_nodes := hnodes
    U_ne := B.a_ne
    V_ne := B.b_ne
    U_dvd := hdvd
    coprime := hcop
    phase := hphase
    degrees_eq := hdeg'
    primitive := B.α_primitive
    height := by rwa [← hheight, D.height_eq]
    out_degree := by
      intro i j
      simpa only [hheight, ← Nat.add_assoc] using P.output_degree j i
    nodes := plane_nodes B P par
  }⟩

end
end P0_8_1
end PackSource_P0_8_1Proof

section PackSource_P0_8_2Proof
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P0_8_2
noncomputable section
open Polynomial P0 P0_8 FrobeniusLocator ProximityPrize.Benchmark
open K1_12 (eq_on_puncture natDegree_lt_of_degree_lt_pos eval_unit_of_dvd)

/-- Port of `K1_12.offset_of_anchor` for the 69.20 height and agreement bounds. -/
private theorem offset_of_anchor {u deleted} (F : Direction u deleted) (H : CrossLift F)
    {η : K} (m : BadMark u η) (avoid : Disjoint m.support deleted) (reg : Regular F η) :
    Nonempty (Offset F m) := by
  classical
  let a := F.amp η
  let w (i : I) := u 0 i + η * u 1 i
  let r (j : Fin 2) := F.out 0 j + C (twist η) * F.out 1 j
  let out := r 0 + C η * r 1
  let d := k + F.U.natDegree + F.s
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
  have hk : 0 < k := by decide
  have hagMargin : k + heightCap ≤ agreement := by decide
  have hdetMargin : k + 2 * heightCap ≤ blockLength := by decide
  have hpos : 0 < d := by dsimp only [d]; omega
  have hA1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  have ha : a.natDegree = F.s := reg.degree_eq
  have ha' : (a.map twist).natDegree ≤ F.s := natDegree_map_le.trans ha.le
  have hr (j : Fin 2) : (r j).natDegree < d := by
    apply (natDegree_add_le _ _).trans_lt
    exact max_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 0 j))
      ((natDegree_C_mul_le _ _).trans_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 1 j)))
  have hout : out.natDegree < d := (natDegree_add_le _ _).trans_lt
    (max_lt (hr 0) ((natDegree_C_mul_le _ _).trans_lt (hr 1)))
  have hrn (j : Fin 2) (i : I) (hi : i ∉ deleted) : (r j).eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * u j i -
      F.V.eval (node i) * (F.A j).eval (node i) * twist (w i) := by
    simp only [r, w, a, Direction.amp, eval_twist, eval_add, eval_mul, eval_C,
      F.nodes i hi, map_add, map_mul]
    ring
  have hspec (i : I) (hi : i ∉ deleted) : out.eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * w i -
      F.V.eval (node i) * a.eval (node i) * twist (w i) := by
    simp only [out, eval_add, eval_mul, eval_C, hrn _ i hi, a, Direction.amp, w, eval_add,
      eval_mul, eval_C]
    ring
  have hp := natDegree_lt_of_degree_lt_pos hk m.degree
  have ident : F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist = out := by
    let left := F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist
    have hdeg : left.natDegree < d := by
      apply (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · apply natDegree_mul_le.trans_lt
        have h : (F.U * a.map twist).natDegree ≤ F.U.natDegree + (a.map twist).natDegree :=
          natDegree_mul_le
        dsimp only [d]; omega
      · apply natDegree_mul_le.trans_lt
        have h : (F.V * a).natDegree ≤ F.V.natDegree+a.natDegree := natDegree_mul_le
        have h' : (m.decoder.map twist).natDegree ≤ m.decoder.natDegree := natDegree_map_le
        have := F.degrees_eq
        dsimp only [d]; omega
    apply sub_eq_zero.mp
    by_contra hne
    have hc := Strata.root_nodes_card_le node IRSProfile.domain.injective (left-out) hne m.support
      (by intro i hi
          rw [eval_sub, hspec i (Finset.disjoint_left.mp avoid hi)]
          simp only [left, eval_sub, eval_mul, eval_twist, m.hits i hi, w, sub_self])
    have hd := natDegree_sub_le left out
    have hag : agreement ≤ m.support.card := m.agreement
    dsimp only [d] at hdeg hout
    omega
  have hG := natDegree_le_of_dvd H.left F.U_ne
  have hLd := natDegree_lt_of_degree_lt_pos (by omega : 0 < k + F.s + H.G.natDegree) H.degree_lt
  have determinant : H.G * (a * r 1 - F.A 1 * out) = F.U * a.map twist * H.L := by
    apply eq_on_puncture (deleted := deleted) (d := d + F.s + H.G.natDegree)
    · change d + F.s + H.G.natDegree + deleted.card ≤ blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have h1 := @natDegree_mul_le _ _ a (r 1)
      have h2 := @natDegree_mul_le _ _ (F.A 1) out
      have h3 := natDegree_sub_le (a * r 1) (F.A 1 * out)
      have := hr 1
      omega
    · apply natDegree_mul_le.trans_lt
      have h := @natDegree_mul_le _ _ F.U (a.map twist)
      dsimp only [d]; omega
    · intro i hi
      simp only [eval_mul, eval_sub, hrn 1 i hi, hspec i hi, H.nodes i hi, a, Direction.amp,
        eval_add, eval_mul, eval_C, w]
      ring
  have div : a ∣ H.L + H.G * F.A 1 * m.decoder := by
    have cop : IsCoprime a (F.U * a.map twist) :=
      reg.content_unit.mul_right reg.adjacent
    apply cop.dvd_of_dvd_mul_left
    refine ⟨H.G * (r 1 + F.A 1 * F.V * m.decoder.map twist), ?_⟩
    linear_combination H.G * F.A 1 * ident - determinant
  obtain ⟨J, hJ⟩ := div
  have hjd : J.natDegree < k + H.G.natDegree := by
    by_cases hj : J = 0
    · simp [hj]
    have h := natDegree_add_le H.L (H.G * F.A 1 * m.decoder)
    rw [hJ, natDegree_mul reg.amp_ne hj, ha] at h
    have h1 := @natDegree_mul_le _ _ H.G (F.A 1)
    have h2 := @natDegree_mul_le _ _ (H.G * F.A 1) m.decoder
    omega
  let f : RatFunc K := algebraMap K[X] (RatFunc K) J / algebraMap K[X] (RatFunc K) H.G
  have hfrac : f.num * H.G = J * f.denom := (RatFunc.num_mul_eq_mul_denom_iff H.monic.ne_zero).mpr rfl
  have hE : f.denom ∣ H.G := RatFunc.denom_div_dvd _ _
  let Q := f.num %ₘ f.denom
  let pencil := f.num /ₘ f.denom
  have division : Q + f.denom * pencil = f.num := modByMonic_add_div _ _
  have hn : f.num.natDegree < k + f.denom.natDegree := by
    by_cases hn : f.num = 0
    · simp [hn]
    have hj : J ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hfrac
      exact mul_ne_zero hn H.monic.ne_zero hfrac
    have h := congrArg natDegree hfrac
    rw [natDegree_mul hn H.monic.ne_zero, natDegree_mul hj f.denom_ne_zero] at h
    omega
  have hpencil : pencil.degree < k := by
    have hd : pencil.natDegree < k := by
      rw [show pencil.natDegree = f.num.natDegree - f.denom.natDegree from
        natDegree_divByMonic _ f.monic_denom]
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  let raw (i : I) := F.den.eval (node i) * (w i - m.decoder.eval (node i)) / a.eval (node i)
  have hUn (i : I) := eval_unit_of_dvd F.U_dvd (F.den_nodes i)
  have hfixed (i : I) (hi : i ∉ deleted) : twist (raw i) = raw i := by
    have h1 := congrArg (eval (node i)) ident
    simp only [eval_sub, eval_mul, eval_twist, hspec i hi] at h1
    have h2 := congrArg (eval (node i)) F.phase
    simp only [eval_mul, eval_twist] at h2
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    have haσ : twist (a.eval (node i)) ≠ 0 := (map_ne_zero twist).mpr ha0
    simp only [raw, map_div₀, map_mul, map_sub]
    apply (div_eq_div_iff haσ ha0).mpr
    apply mul_left_cancel₀ (hUn i)
    linear_combination F.den.eval (node i) * h1 +
      a.eval (node i) * (twist (w i) - twist (m.decoder.eval (node i))) * h2
  refine ⟨{
    pencil := pencil
    pencil_degree := hpencil
    E := f.denom
    Q := Q
    E_monic := f.monic_denom
    left := hE.trans H.left
    right := (map_dvd (Polynomial.mapRingHom twist) hE).trans H.right
    proper := degree_modByMonic_lt _ f.monic_denom
    reduced := ?_
    raw := raw
    raw_fixed := hfixed
    first := ?_
    second := ?_ }⟩
  · obtain ⟨x, y, h⟩ := f.isCoprime_num_denom
    rw [← division] at h
    exact ⟨x, x * pencil + y, by linear_combination h⟩
  · intro i hi
    change w i - m.decoder.eval (node i) = a.eval (node i) * raw i / F.den.eval (node i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    simp only [raw]
    field_simp [ha0, F.den_nodes i]
  · intro i hi
    have h1 := congrArg (eval (node i)) hJ
    simp only [eval_add, eval_mul, H.nodes i hi] at h1
    have h2 := congrArg (eval (node i)) hfrac
    simp only [eval_mul, ← division, eval_add, eval_mul] at h2
    have hEn := eval_unit_of_dvd ((hE.trans H.left).trans F.U_dvd) (F.den_nodes i)
    have hGn := eval_unit_of_dvd (H.left.trans F.U_dvd) (F.den_nodes i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    change u 1 i - pencil.eval (node i) = Q.eval (node i) / f.denom.eval (node i) +
      (F.A 1).eval (node i) * raw i / F.den.eval (node i)
    simp only [raw]
    field_simp [F.den_nodes i, hEn, ha0]
    apply mul_left_cancel₀ hGn
    have h3 : a.eval (node i) = (F.A 0).eval (node i) + η * (F.A 1).eval (node i) := by
      simp only [a, Direction.amp, eval_add, eval_mul, eval_C]
    dsimp [w]
    linear_combination f.denom.eval (node i) * h1 - a.eval (node i) * h2 +
      f.denom.eval (node i) * H.G.eval (node i) * u 1 i * h3

theorem proof : P0_8.c2 := by
  intro u deleted F H η m avoid reg
  exact offset_of_anchor F H m avoid reg

end
end P0_8_2
end PackSource_P0_8_2Proof

section PackSource_P0_8_3Proof
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P0_8_3
noncomputable section

open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open P0_8 (Direction Regular Offset eval_twist)
open K1_12 (eval_unit_of_dvd invariant_multiple)
open private coprime_factor_of_label from ProximityPrize.SubmissionLower.Fast068

variable {u : Words} {deleted : Finset I} {F : Direction u deleted} {η γ : K}
  {anchor : BadMark u η}

private def translated (O : Offset F anchor) (m : BadMark u γ) :=
  m.decoder - anchor.decoder - C (γ-η) * O.pencil

private def numerator (O : Offset F anchor) (m : BadMark u γ) :=
  O.E * translated O m - C (γ-η) * O.Q

private theorem E_nodes (O : Offset F anchor) (i : I) : O.E.eval (node i) ≠ 0 :=
  eval_unit_of_dvd (O.left.trans F.U_dvd) (F.den_nodes i)

private theorem translated_degree (O : Offset F anchor) (m : BadMark u γ) :
    (translated O m).degree < k := by
  unfold translated
  rw [C_mul']
  exact Principal.degree_sub_lt (Principal.degree_sub_lt m.degree anchor.degree)
    (Principal.degree_smul_lt _ O.pencil_degree)

private theorem numerator_degree (O : Offset F anchor) (m : BadMark u γ) :
    (numerator O m).natDegree < k + O.E.natDegree := by
  have hQ := O.proper.trans_le (degree_le_natDegree (p := O.E))
  by_cases hz : numerator O m = 0
  · simpa only [hz, natDegree_zero] using
      (Nat.lt_of_lt_of_le (show 0 < k by decide) (Nat.le_add_right k O.E.natDegree))
  apply (natDegree_lt_iff_degree_lt hz).mpr
  apply Principal.degree_sub_lt (Strata.degree_mul_lt_add O.E (translated O m)
    O.E.natDegree k le_rfl (translated_degree O m))
  rw [C_mul']
  exact Principal.degree_smul_lt _ (hQ.trans_le (by exact_mod_cast Nat.le_add_left _ _))

private theorem hits (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (i : I) (hi : i ∈ m.support) :
    W.eval (node i) * (numerator O m).eval (node i) = (F.amp γ).eval (node i) * O.raw i := by
  have hd := Finset.disjoint_left.mp avoid hi
  have he := E_nodes O i
  have hf := O.first i hd
  have hs := O.second i hd
  have hn := F.den_nodes i
  have hw : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by rw [hW, eval_mul]
  simp only [Direction.amp, eval_add, eval_C, eval_mul] at hf ⊢
  rw [eq_div_iff hn] at hf
  have hs' : O.E.eval (node i) * F.den.eval (node i) * (u 1 i - O.pencil.eval (node i)) =
      F.den.eval (node i) * O.Q.eval (node i) + O.E.eval (node i) * ((F.A 1).eval (node i) * O.raw i) := by
    rw [hs]
    field_simp [he, hn]
  simp only [numerator, translated, eval_sub, eval_mul, eval_C, m.hits i hi]
  apply mul_left_cancel₀ he
  rw [← mul_assoc, ← hw]
  linear_combination O.E.eval (node i) * hf + (γ - η) * hs'

/-- Clearing the small contents U/E and V/E^σ permits root counting at
the original agreement. The much larger den/E never enters the degree test. -/
private theorem fixed_numerator (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (reg : Regular F γ) :
    ∃ N : K[X], numerator O m = F.amp γ * N ∧ (W*N).map twist = W*N := by
  classical
  obtain ⟨l, hl⟩ := O.left
  obtain ⟨r, hr⟩ := O.right
  have hl0 : l ≠ 0 := fun hz => F.U_ne (by simp [hl, hz])
  have hr0 : r ≠ 0 := fun hz => F.V_ne (by simp [hr, hz])
  have hWnodes (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  have hEσ : O.E.map twist ≠ 0 := (O.E_monic.map twist).ne_zero
  have hphase : l * W.map twist = r * W := by
    apply mul_left_cancel₀ (mul_ne_zero O.E_monic.ne_zero hEσ)
    have h := F.phase
    rw [hl, hr, hW, Polynomial.map_mul] at h
    linear_combination h
  let a := F.amp γ
  let P := numerator O m
  let diff := l * a.map twist * P - r * a * P.map twist
  have zero_at (i : I) (hi : i ∈ m.support) : diff.eval (node i) = 0 := by
    have hrw := O.raw_fixed i (Finset.disjoint_left.mp avoid hi)
    have h1 := hits O W hW m avoid i hi
    have h2 := congrArg twist h1
    simp only [map_mul, hrw] at h2
    have h3 := congrArg (eval (node i)) hphase
    simp only [eval_mul, eval_twist] at h3
    simp only [diff, eval_sub, eval_mul, eval_twist]
    change W.eval (node i) * P.eval (node i) = a.eval (node i) * O.raw i at h1
    change twist (W.eval (node i)) * twist (P.eval (node i)) =
      twist (a.eval (node i)) * O.raw i at h2
    apply (mul_eq_zero.mp (show W.eval (node i) * _ = 0 from ?_)).resolve_left (hWnodes i)
    linear_combination l.eval (node i) * twist (a.eval (node i)) * h1 -
      l.eval (node i) * a.eval (node i) * h2 +
      a.eval (node i) * twist (P.eval (node i)) * h3
  have ident : diff = 0 := by
    by_contra hne
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective diff hne m.support zero_at
    have hld : O.E.natDegree + l.natDegree = F.U.natDegree := by
      rw [hl, natDegree_mul O.E_monic.ne_zero hl0]
    have hrd : O.E.natDegree + r.natDegree = F.U.natDegree := by
      rw [← F.degrees_eq, hr, natDegree_mul hEσ hr0, natDegree_map_eq_of_injective twist.injective]
    have hP := numerator_degree O m
    have hA := reg.degree_eq
    have hheight := F.height
    change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
    have hmargin : k + heightCap ≤ agreement := by decide
    have hdeg : diff.natDegree ≤ max (l.natDegree + a.natDegree + P.natDegree)
        (r.natDegree + a.natDegree + P.natDegree) := by
      apply (natDegree_sub_le _ _).trans
      exact max_le_max
        (natDegree_mul_le.trans (Nat.add_le_add_right
          (natDegree_mul_le.trans (Nat.add_le_add_left natDegree_map_le _)) _))
        (natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_map_le))
    change P.natDegree < _ at hP
    change a.natDegree = _ at hA
    have hcount := m.agreement
    omega
  have eqn : l * a.map twist * P = r * a * P.map twist := sub_eq_zero.mp ident
  have hlU : l ∣ F.U := hl ▸ dvd_mul_left l O.E
  have cop : IsCoprime a (l * a.map twist) :=
    (reg.content_unit.of_isCoprime_of_dvd_right hlU).mul_right reg.adjacent
  have hdvd : a ∣ P := by
    apply cop.dvd_of_dvd_mul_left
    rw [eqn]
    exact (dvd_mul_left a r).mul_right _
  obtain ⟨N, hN⟩ := hdvd
  refine ⟨N, hN, ?_⟩
  have hred : l*N = r*N.map twist := by
    apply mul_left_cancel₀ (mul_ne_zero reg.amp_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr reg.amp_ne))
    rw [hN, Polynomial.map_mul] at eqn
    linear_combination eqn
  rw [Polynomial.map_mul]
  apply mul_left_cancel₀ hl0
  linear_combination N.map twist * hphase - W * hred

/-- Normalize all selected decoders against the same chart and word. -/
theorem proof : P0_8.c3 := by
  intro u deleted F Γ reg m avoid η ζ hne O
  classical
  obtain ⟨W,hW⟩ := O.left.trans F.U_dvd
  have hWn (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  obtain ⟨L,c,hL,hLf,hLn,hsplit⟩ := invariant_multiple W hWn
  change L.map twist = L at hLf
  have hcn (i : I) : c.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hL ▸ dvd_mul_left c W) (hLn i)
  have hscalar (g : Γ) : ∃ S : K[X], S.map twist = S ∧
      numerator O (m g) = c * F.amp g.val * S := by
    obtain ⟨N, hN, hfix⟩ := fixed_numerator O W hW (m g) (avoid g) (reg g.val g.property)
    obtain ⟨S,hS,hNS⟩ := hsplit N hfix
    exact ⟨S,hS,by rw [hN,hNS]; ring⟩
  choose S hS ident using hscalar
  let word (i : I) := if i ∈ deleted then 0 else O.raw i / L.eval (node i)
  have hword (i : I) (hi : i ∉ deleted) : word i = O.raw i / L.eval (node i) := by simp [word, hi]
  have hden (i : I) : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by
    rw [hW, eval_mul]
  have hLval (i : I) : L.eval (node i) = W.eval (node i) * c.eval (node i) := by rw [hL, eval_mul]
  have hs : amplitudeDegree (F.amp η.val) (F.A 1) = F.s := by
    unfold amplitudeDegree
    rw [(reg η.val η.property).degree_eq]
    exact max_eq_left (le_max_right _ _)
  have hcop : IsCoprime O.E c := coprime_factor_of_label (sub_ne_zero.mpr hne) O.reduced (ident ζ)
  let M : AnchorModel u deleted := {
    shift := η.val
    pencil₀ := (m η).decoder
    pencil₁ := O.pencil
    pencil₀_degree := (m η).degree
    pencil₁_degree := O.pencil_degree
    E := O.E
    factor := c
    Q := O.Q
    A₀ := F.amp η.val
    A₁ := F.A 1
    word := word
    word_fixed := by
      intro i
      by_cases hi : i ∈ deleted
      · simp [word,hi]
      · rw [hword i hi, map_div₀, O.raw_fixed i hi, ← eval_twist L i, hLf]
    word_deleted := fun i hi => by simp [word, hi]
    E_monic := O.E_monic
    E_nodes := E_nodes O
    factor_nodes := fun i _ => hcn i
    coprime_factor := hcop
    offset_proper := O.proper
    offset_reduced := O.reduced
    adjacent_coprime := F.coprime.mono O.left O.right
    amplitudes_primitive := by
      obtain ⟨x,y,hxy⟩ := F.primitive
      exact ⟨x,y - x*C η.val,by unfold Direction.amp; linear_combination hxy⟩
    first_amplitude_unit := (reg η.val η.property).content_unit.of_isCoprime_of_dvd_right O.left
    height_bound := by
      rw [hs]
      have h := F.height
      change F.U.natDegree + F.s + deleted.card ≤ heightCap at h
      have hd := natDegree_le_of_dvd O.left F.U_ne
      omega
    first_word := by
      intro i hi
      rw [O.first i hi, hword i hi]
      field_simp [F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring
    second_word := by
      intro i hi
      rw [O.second i hi, hword i hi]
      field_simp [E_nodes O i, F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring }
  have amp_eq (g : Γ) : M.amplitude g.val = F.amp g.val := by
    change F.amp η.val + C (g.val-η.val) * F.A 1 = F.amp g.val
    simp only [Direction.amp, map_sub]
    ring
  let marks (g : Γ) : AnchorMark M g.val (S g) := by
    have hreg := reg g.val g.property
    refine {
      bad := m g
      avoids_deleted := avoid g
      scalar_fixed := hS g
      scalar_degree := ?_
      scalar_hits := ?_
      pole_unit := ?_
      identity := ?_ }
    · by_cases hz : S g = 0
      · exact Or.inl hz
      right
      have hc : c ≠ 0 := fun h => hcn 0 (by rw [h, eval_zero])
      have hd := numerator_degree O (m g)
      rw [ident g, natDegree_mul (mul_ne_zero hc hreg.amp_ne) hz,
        natDegree_mul hc hreg.amp_ne, hreg.degree_eq] at hd
      change (S g).natDegree ≤ (k : ℤ) - 1 + (O.E.natDegree - c.natDegree -
        (amplitudeDegree (F.amp η.val) (F.A 1) : ℤ))
      rw [hs]
      omega
    · intro i hi
      have hits := hits O W hW (m g) (avoid g) i hi
      rw [ident g, eval_mul, eval_mul] at hits
      change (S g).eval (node i) = word i
      have hd := Finset.disjoint_left.mp (avoid g) hi
      rw [hword i hd, eq_div_iff (hLn i), hLval]
      apply mul_left_cancel₀ (hreg.node_unit i hd)
      linear_combination hits
    · rw [amp_eq]
      exact hreg.content_unit.of_isCoprime_of_dvd_right O.left
    · rw [amp_eq]
      exact ident g
  exact ⟨M, rfl, rfl, rfl, rfl, rfl, S, marks, fun g => rfl⟩

end
end P0_8_3
end PackSource_P0_8_3Proof
