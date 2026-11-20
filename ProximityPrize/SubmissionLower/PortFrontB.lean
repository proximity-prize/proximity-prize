import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.PortLow4
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_6
noncomputable section
open P0 Polynomial
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)
abbrev Plane := K1_10.Plane
abbrev Adjugate := K1_10.Adjugate
abbrev ScalarSource := K1_10.ScalarSource
abbrev sourceCutoff : ℕ := 4 * agreement - 1
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
theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : D.height + (fixedNodes R).card ≤ 32766) :
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
private theorem source_count : K1_10.sourceDim sourceCutoff 5 16 16 = 1494492048 := by
  let rows : Fin 6 → ℕ := ![620522372, 414157360, 253601460, 135774436, 57071768, 13364652]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1494492048 := by decide
private theorem multiple_count : K1_10.sourceDim 565223 4 15 15 = 740577966 := by
  let rows : Fin 5 → ℕ := ![360423200, 216495780, 112036918, 43761588, 7860480]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 740577966 := by decide
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
      K1_10.sourceDim (sourceCutoff - (k - 1) - 24573) 4 15 15 =
      blockLength * (K1_10.jetDim 4 16 16 - K1_10.jetDim 3 15 15) + 250082 := by
  have h : sourceCutoff - (k - 1) - 24573 = 565223 := by decide
  rw [h, source_count, multiple_count, jet_count, local_multiple_count]
  decide
theorem bank_surplus (n h : ℕ) (hn : n ≤ blockLength) (hh : 24573 ≤ h) :
    quotientSurplus n h := by
  have hm : K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 15 15 ≤
      K1_10.sourceDim (sourceCutoff - (k - 1) - 24573) 4 15 15 := by
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
theorem regularPrice_exact : regularPrice = 117191699485828189 := by
  unfold regularPrice incidenceRatio
  exact ceil_sq_div_eq 1236945993621 49146 185 117191699485828189
    (by decide) (by decide) (by decide) (by decide)
end
end P0_6
end
section
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
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
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
end
section
namespace P0_6
noncomputable section
open P0 Polynomial
def c1 : Prop :=
  ∀ u deleted h U V, Plane u deleted h U V → 24573 ≤ h → h + deleted.card ≤ 32766 →
    quotientSurplus (blockLength - deleted.card) h →
    ∃ A : ScalarSource, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0
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
  have hh : D.height + (fixedNodes R).card ≤ 32766 :=
    D.height_eq ▸ relation_height_le hu T
  by_cases hsmall : 2 * D.height < L
  · obtain ⟨J⟩ := adjugate_of_plane B hnp W hh
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin : 24573 ≤ D.height := by
    change ¬ 2 * D.height < 49145 at hsmall
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
end
section
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
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 32766) (hs : P0_6.quotientSurplus N h) :
    ∃ G : Source F, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 16 16 j := by
    have hcapacity : 131071 + 32766 ≤ sourceCutoff := by decide
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
    (hh : h ≤ 32766) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
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
    have hcapacity : 131071 + 32766 < P0.agreement := by decide
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
end
