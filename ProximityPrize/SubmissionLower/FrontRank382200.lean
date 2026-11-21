import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.FrontCases82200
set_option Elab.async false
set_option autoImplicit true
section
namespace Front82200_3
noncomputable section
open Front82200 Polynomial
open P1_3 (Bank cutDegree)
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)
abbrev sourceCutoff : ℕ := 4 * agreement - 1
def quotientSurplus (bank : Bank) (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1)) <
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4
        (bank.first - 1) (bank.second - 1)
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
def regularPrice : ℕ := ⌈((210 : ℕ) : ℚ) * incidenceRatio ^ 2⌉₊
end
end Front82200_3
end
section
namespace Front82200_3
noncomputable section
open Front82200 Polynomial ProximityPrize.Benchmark FrobeniusLocator
open P1_3 (Adjugate Plane)
open private amp_le primitive_lift contraction_degree from ProximityPrize.SubmissionLower.PortFrontB
theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength) :
    Nonempty (Adjugate u (fixedNodes R) D.height) := by
  change 131072 + 3 * D.height + (fixedNodes R).card ≤ 262144 at hroom
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
end Front82200_3
end
section
namespace Front82200_3
noncomputable section
open Front82200
open P1_3 (Bank)
open scoped BigOperators
open private jet_quotient from ProximityPrize.SubmissionLower.FrontBranch3
open private sum_rows ceil_sq_div_eq from ProximityPrize.SubmissionLower.PortFrontB
private theorem source_st : K1_10.sourceDim sourceCutoff 5 20 17 = 1983603874 := by
  let rows : Fin 6 → ℕ := ![813936963, 548715000, 339780230, 184180212, 78438221, 18553248]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1983603874 := by decide
private theorem source_ts : K1_10.sourceDim sourceCutoff 5 17 20 = 1983603874 := by
  let rows : Fin 6 → ℕ := ![824700168, 549681315, 336248000, 179874930, 75512528, 17586933]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1983603874 := by decide
private theorem multiple_st : K1_10.sourceDim 564268 4 19 16 = 994259196 := by
  let rows : Fin 5 → ℕ := ![479404700, 291156532, 152510940, 60311104, 10875920]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 994259196 := by decide
private theorem multiple_ts : K1_10.sourceDim 564268 4 16 19 = 994259196 := by
  let rows : Fin 5 → ℕ := ![484536380, 290610016, 150185010, 58531690, 10396100]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 994259196 := by decide
private theorem source_corner (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second = 1983603874 := by
  cases bank
  · exact source_st
  · exact source_ts
private theorem multiple_corner (bank : Bank) :
    K1_10.sourceDim 564268 4 (bank.first - 1) (bank.second - 1) = 994259196 := by
  cases bank
  · exact multiple_st
  · exact multiple_ts
theorem minimum_surplus (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim 564268 4 (bank.first - 1) (bank.second - 1) =
      blockLength * 3765 + 2372518 := by
  rw [source_corner, multiple_corner]
  decide
theorem bank_surplus (bank : Bank) (n h : ℕ) (hn : n ≤ blockLength) (hh : 24436 ≤ h) :
    quotientSurplus bank n h := by
  let s := bank.first - 1
  let t := bank.second - 1
  have hm : K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 s t ≤
      K1_10.sourceDim 564268 4 s t := by
    have hcut : sourceCutoff - (k - 1) - 24436 = 564268 := by decide
    rw [← hcut]
    unfold K1_10.sourceDim
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.sub_le_sub_left hh _) _) _))
  unfold quotientSurplus
  rw [jet_quotient]
  have hd := minimum_surplus bank
  have hs : n * 3765 ≤ blockLength * 3765 := Nat.mul_le_mul_right _ hn
  calc
    n * 3765 ≤ blockLength * 3765 := hs
    _ < blockLength * 3765 + 2372518 := Nat.lt_add_of_pos_right (by decide)
    _ = _ := hd.symm
    _ ≤ _ := Nat.sub_le_sub_left hm _
theorem regularPrice_exact : regularPrice = 174479928733806260 := by
  unfold regularPrice incidenceRatio
  exact ceil_sq_div_eq 0x147ffafff86 48873 210 174479928733806260
    (by decide) (by decide) (by decide) (by decide)
theorem bank_price_le (bank : Bank) : regularPrice + bank.graphFee ≤ 250000000000000000 := by
  rw [regularPrice_exact]
  cases bank <;> decide
end
end Front82200_3
end
section
namespace Front82200_3
noncomputable section
open Front82200 FrobeniusLocator ProximityPrize.Benchmark Polynomial
open P1_3 (Adjugate)
open private natDegree_lt_of_degree_lt_pos from ProximityPrize.SubmissionLower.PortFrontB
theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ : K} (hn : Normal u γ) (M : BadMark u γ) :
    Disjoint M.support (fixedNodes R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D : Reduction u T R) (J : Adjugate u (fixedNodes R) D.height)
    (hsmall : 2 * D.height < Front82200.L) {γ : K} (hn : Normal u γ) (M : BadMark u γ) : False := by
  classical
  let F := J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder
  have hfit : Front82200.k + 2 * D.height < Front82200.agreement := by
    have hsum : Front82200.k + Front82200.L = Front82200.agreement := by decide
    omega
  have hdeg : F.natDegree < Front82200.agreement := by
    have hj (j : Fin 2) : (J.numer j).natDegree < Front82200.k + 2 * D.height :=
      natDegree_lt_of_degree_lt_pos (by
        have hk : 0 < Front82200.k := by decide
        omega) (J.numer_degree j)
    have hP : M.decoder.natDegree < Front82200.k := natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod := natDegree_mul_le (p := J.denom) (q := M.decoder)
    have hsub := natDegree_sub_le (J.numer 0 + C γ * J.numer 1) (J.denom * M.decoder)
    change (J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder).natDegree < Front82200.agreement
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
  have hcard : Front82200.k + Front82200.L + Front82200.t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) Front82200.L Front82200.t).map (evalRingHom γ)).rank = stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      Front82200.k Front82200.L Front82200.t M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b : Fin 2 => iterateFrobenius K p b.val) (fun i : E => node i.val)
    (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) Front82200.L)
  rw [Fintype.card_coe, hn] at hr
  have hsize : 2 * D.height + (fixedNodes R).card < stackRank u := by
    omega
  omega
end
end Front82200_3
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front82200_3
noncomputable section
open Front82200 Polynomial FrobeniusLocator
open P1_3 (Plane)
open private column column_ne column_bound column_dvd firstColumn_normal threeU_fun
  tight_pair outputs slice_bound nodes_of_columns relationOn_fun from ProximityPrize.SubmissionLower.PortFrontB
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
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
end Front82200_3
end
section
namespace Front82200_3
noncomputable section
open Front82200 Polynomial
open P1_3 (Bank Plane ScalarSource)
def c1 : Prop :=
  ∀ bank u deleted h U V, Plane u deleted h U V → 24436 ≤ h →
    h + deleted.card ≤ heightCap → quotientSurplus bank (blockLength - deleted.card) h →
    ∃ A : ScalarSource bank, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0
def c2 : Prop :=
  ∀ bank u (A : ScalarSource bank) (Γ : Finset K),
    (∀ γ ∈ Γ, A.atLabel γ ≠ 0 ∧ ∃ M : BadMark u γ, A.atDecoder γ M.decoder = 0) →
    Γ.card ≤ regularPrice
private theorem zero_specializations {bank : Bank} (A : ScalarSource bank) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, A.atLabel γ = 0) : Γ.card ≤ bank.graphFee := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr A.nonzero
  have hlt : bank.first + 5 < p := by cases bank <;> decide
  apply K1_10.frobenius_coefficient_exception_count p (bank.first + 5) bank.second
    (by decide) (A.poly.coeff e) (MvPolynomial.mem_support_iff.mp he)
    (A.s_degree e he) hlt (A.t_degree e he) Γ
  intro γ hγ
  have hh := congrArg (fun P : MvPolynomial (Fin 2) K => P.coeff e) (hΓ γ hγ)
  simpa only [ScalarSource.atLabel, MvPolynomial.coeff_map,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh
private theorem count_with_bank (h1 : c1) (h2 : c2) (bank : Bank) : Front82200.c3 := by
  classical
  intro u hu T R D B _hsat hnp Γ hΓ hn
  obtain ⟨W⟩ := plane_of_rankThree B
  have hh : D.height + (fixedNodes R).card ≤ heightCap :=
    D.height_eq ▸ relation_height_le hu T
  by_cases hsmall : 2 * D.height < L
  · have hshort := (shortened_guards D hu).1
    have hcap : heightCap ≤ blockLength := by decide
    have hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength := by omega
    obtain ⟨J⟩ := adjugate_of_plane B hnp W hroom
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin : 24436 ≤ D.height := by
    change ¬ 2 * D.height < 48872 at hsmall
    omega
  obtain ⟨A, hA⟩ := h1 bank u _ D.height _ _ W hmin hh
    (bank_surplus bank _ _ (Nat.sub_le _ _) hmin)
  let good := Γ.filter (fun γ => A.atLabel γ ≠ 0)
  let exc := Γ.filter (fun γ => ¬ A.atLabel γ ≠ 0)
  have hexc : exc.card ≤ bank.graphFee := zero_specializations A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood : good.card ≤ regularPrice := h2 bank u A good (by
    intro γ hγ
    obtain ⟨hγΓ, hnonzero⟩ := Finset.mem_filter.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact ⟨hnonzero, M, hA γ M (mark_disjoint D (hn γ hγΓ) M)⟩)
  have hsum : good.card + exc.card = Γ.card :=
    Finset.card_filter_add_card_filter_not (s := Γ) (p := fun γ => A.atLabel γ ≠ 0)
  exact hsum ▸ (Nat.add_le_add hgood hexc).trans (bank_price_le bank)
theorem of_children (h1 : c1) (h2 : c2) : Front82200.c3 :=
  count_with_bank h1 h2 .ts
end
end Front82200_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Front82200_3_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts relationBounds)
open Front82200_3 (sourceCutoff)
open P1_3_1 (Multipliers)
open private localMultiply LocalSpace local_finrank from ProximityPrize.SubmissionLower.FrontBranch3
open private exists_kernel_outside from ProximityPrize.SubmissionLower.PortFrontB
abbrev Source (F : Type*) [Field F] (bank : P1_3.Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (bank : P1_3.Bank) (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
private def nodeMap (i : Fin N) : Source F bank →ₗ[F] LocalSpace bank C hdeg i :=
  (LinearMap.range (localMultiply bank C hdeg i)).mkQ.comp
    (sourceToJet sourceCutoff 131071 5 bank.first bank.second 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))
include hdeg in
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 33327) (hs : Front82200_3.quotientSurplus bank N h) :
    ∃ G : Source F bank, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F bank,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 bank.first bank.second j := by
    have hcapacity : 131071 + 33327 ≤ sourceCutoff := by decide
    intro j
    cases bank <;> fin_cases j <;> simp [relationBounds, sourceBounds, P1_3.Bank.first, P1_3.Bank.second] <;> omega
  have hshift : (fun j => sourceBounds sourceCutoff 5 bank.first bank.second j - relationBounds h j) =
      sourceBounds (sourceCutoff - 131071 - h) 4 (bank.first - 1) (bank.second - 1) := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds, Nat.sub_sub]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  let (i : Fin N) : Module.Free F (LocalSpace bank C hdeg i) := Module.Free.of_divisionRing F _
  let : Module F (∀ i : Fin N, LocalSpace bank C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) =
      N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank bank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F bank) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) <
      V sourceCutoff 131071 5 bank.first bank.second -
        V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) at hs
    omega
  obtain ⟨G, hG, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace bank C hdeg i)
    (LinearMap.pi (nodeMap bank C hdeg)) (LinearMap.range mult) hdim
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap bank C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
end
end Front82200_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front82200_3_1
noncomputable section
open MvPolynomial K1_11
open Front82200 (K I Words node p blockLength agreement twist heightCap BadMark)
open P1_3 (Plane)
open Front82200_3 (sourceCutoff)
open P1_3_1 (toScalarSource toScalarSource_atDecoder)
open K1_10_1 (Contacts denominator numerator planeRelation planeRelation_view relationBounds)
open private coeff_bounds denominator_ne relation_eval from ProximityPrize.SubmissionLower.PortFrontB
open private scalar_total_weight_le from ProximityPrize.SubmissionLower.Fast071
private theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)
private theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]
private theorem relation_at_decoder {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (P : Puncture deleted)
    (hdeg : (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 0) ≤ 131071 + h)
    (hh : h ≤ 33327) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
    (hq' : Q'.natDegree ≤ 131071) (s t : K) (S : Finset (Fin P.N)) (hS : agreement ≤ S.card)
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
      t * W.nodes _ hi 0 1 + (s * t) * W.nodes _ hi 1 1
  · have hd := decoder_eval_degree 131071 (131071 + h) _ hdeg Q Q' hq hq' s t
    have hcapacity : 131071 + 33327 < agreement := by decide
    omega
theorem proof : Front82200_3.c1 := by
  intro bank u deleted h U V W _ hh hs
  have hheight : h ≤ 33327 := by
    have hh' : h + deleted.card ≤ heightCap := hh
    change h + deleted.card ≤ 33327 at hh'
    omega
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
  have hN : P.N = blockLength - deleted.card := by
    have hsize : P.N + deleted.card = blockLength := P.size
    omega
  obtain ⟨G, hnot, hcontacts⟩ := quotientSource bank C hdeg hl hheight (hN ▸ hs)
  let Q := scalarEliminant 5 G.val a b
  have hne : Q ≠ 0 := scalarEliminant_ne_zero sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property hnot a b hb hview (K1_10_1_3.proof u deleted h U V W)
  have hLsource : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071 + h) 1 1 1) := by
    apply (mem_filtered _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY, hbY, haS, hbS, haT, hbT⟩ := coeff_bounds L a b _ hLsource hview hb
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients
    sourceCutoff 131071 5 bank.first bank.second G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 :=
    clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5 :=
    clearedEval_weight_bound scalarWeightYS 5 bank.first 0 1 1 (polynomialView G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree scalarWeightT ≤ bank.second :=
    clearedEval_weight_bound scalarWeightT 5 bank.second 1 1 0 (polynomialView G.val) a b
      (by simpa using hT) haT hbT (by decide)
  have htotal : Q.weightedTotalDegree scalarWeightTotal ≤ 42 :=
    (scalar_total_weight_le Q _ _ hs' ht').trans (by cases bank <;> decide)
  refine ⟨toScalarSource Q hne hy hs' ht' htotal, ?_⟩
  intro γ M hdis
  rw [toScalarSource_atDecoder]
  let S := indexedSupport P M.support
  have hS' : agreement ≤ S.card := by
    rw [indexedSupport_card P M.support
      (fun i hi hid => Finset.disjoint_left.mp hdis hi hid)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 := Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_at_decoder W P (le_of_eq (hdeg 0)) hheight
    _ _ hd hd' γ (γ ^ p) S hS' hcorrect
  apply scalarEliminant_annihilates sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ ^ p) hrel
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hcontacts i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ γ (γ ^ p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG := decoder_eval_degree 131071 sourceCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) _ _ hd hd' γ (γ ^ p)
    have hcut : sourceCutoff < 4 * agreement := by decide
    omega
end
end Front82200_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Front82200_3_2
noncomputable section
open Front82200 Polynomial MvPolynomial ProximityPrize.Benchmark
open P1_3 (cutDegree)
open P1_3_2 (nodeCut_degree)
open Front82200_3 (incidenceRatio)
open K1_10_2 (GenericRow point surface_count_with_terminal RegularRoot
  derivativeOrder toGeneric atTrajectory)
open scoped Polynomial
open private assign_charts from ProximityPrize.SubmissionLower.FrontBranch3
open private nodeCut eval_nodeCut from ProximityPrize.SubmissionLower.Fast069
open private derivativeOrder_degree K1_10_2.eval_toGeneric from ProximityPrize.SubmissionLower.Fast069
private abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ
private structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i
private theorem pencil_count {u : Words} (Γ : Finset K) (F : Marks u Γ)
    (P Q : K[X]) (hP : P.degree < 131072) (hQ : Q.degree < 131072)
    (hpencil : ∀ γ (hγ : γ ∈ Γ), (F γ hγ).decoder = P + Polynomial.C γ * Q) :
    Γ.card ≤ 82201 := by
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
  have hS : 179944 ≤ S.card := (F r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcard
  omega
private theorem persistent_count {u : Words} {Γ : Finset K} {F : Marks u Γ}
    (C : TaylorCuts F) (J : Ideal GenericRow) (W : Finset K) (hW : W ⊆ Γ)
    (hzero : ∀ γ (hγ : γ ∈ W), point γ (F γ (hW hγ)).decoder ∈ zeroLocus Frac J)
    (hpersistent : 131072 ≤ {i | C.equation i ∈ J}.ncard) :
    W.card ≤ 82201 := by
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
private theorem terminal_price_le : (82201 : ℚ) ≤ incidenceRatio := by
  change ((82201 : ℕ) : ℚ) ≤ ((0x147ffafff86 : ℕ) : ℚ) / ((48873 : ℕ) : ℚ)
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast (show (82201 : ℕ) * 48873 ≤ 0x147ffafff86 by decide)
private theorem node_incidence (m : ℕ) (hm : m < 131072) :
    (((Fintype.card I - m) * cutDegree : ℕ) : ℚ) ≤
      incidenceRatio * ((179944 - m : ℕ) : ℚ) := by
  rw [IRSProfile.card_index, Nat.cast_mul]
  have hn : (262144 - m) * 48873 ≤ 131073 * (179944 - m) := by omega
  have hq : ((262144 - m : ℕ) : ℚ) * 48873 ≤ 131073 * ((179944 - m : ℕ) : ℚ) := by
    exact_mod_cast hn
  change ((262144 - m : ℕ) : ℚ) * (cutDegree : ℚ) ≤
    (((131073 : ℕ) * cutDegree : ℕ) : ℚ) / 48873 * ((179944 - m : ℕ) : ℚ)
  rw [Nat.cast_mul, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (((262144 - m : ℕ) : ℚ) * 48873) * (cutDegree : ℚ) := by ring
    _ ≤ (131073 * ((179944 - m : ℕ) : ℚ)) * (cutDegree : ℚ) :=
      mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring
private theorem count_chart {u : Words} {Γ : Finset K} (F : Marks u Γ) (C : TaylorCuts F)
    (g s : GenericRow) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 42)
    (hroot : ∀ γ (hγ : γ ∈ Γ), MvPolynomial.eval (point γ (F γ hγ).decoder) g = 0 ∧
      MvPolynomial.eval (point γ (F γ hγ).decoder) s ≠ 0) :
    (Γ.card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
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
  refine surface_count_with_terminal g s hg C.equation (L := 131072) (A := 179944)
    (by decide) hdeg C.degree ((by norm_num : (1 : ℚ) ≤ 82201).trans terminal_price_le)
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
    exact (by exact_mod_cast hcount : (V.card : ℚ) ≤ 82201).trans terminal_price_le
theorem proof : Front82200_3.c2 := by
  classical
  intro bank u A Γ hΓ
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
  have hchart (j : Fin 5) : ((charts j).card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀, hγ₀⟩
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    let G := derivativeOrder g j
    let M : Marks u (charts j) := fun γ hγ => F γ (hsub j hγ)
    have hregular (γ : K) (hγ : γ ∈ charts j) : RegularRoot G γ (M γ hγ).decoder := by
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hγ).2
      exact hr
    have hG : G.totalDegree ≤ 42 := (derivativeOrder_degree g j).trans hg
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
    have hgd : (toGeneric G).totalDegree ≤ 42 := by
      simpa only [toGeneric, totalDegree, support_map_of_injective G hinj] using hG
    apply count_chart M C (toGeneric G) (toGeneric (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr, hs⟩ := hregular γ hγ
    rw [K1_10_2.eval_toGeneric, K1_10_2.eval_toGeneric, hr, map_zero]
    exact ⟨rfl, by simpa only [map_zero] using hinj.ne hs⟩
  have hnat : Γ.card ≤ ∑ j : Fin 5, (charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card : ℚ) ≤ 5 * 42 * incidenceRatio ^ 2 := by
    calc
      (Γ.card : ℚ) ≤ ∑ j : Fin 5, ((charts j).card : ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j : Fin 5, (42 * incidenceRatio ^ 2 : ℚ) :=
        Finset.sum_le_sum fun j _ => hchart j
      _ = _ := by simp; ring
  have hrounded : (Γ.card : ℚ) ≤ (Front82200_3.regularPrice : ℚ) := by
    unfold Front82200_3.regularPrice
    apply hrat.trans
    rw [show (5 : ℚ) * 42 = ((210 : ℕ) : ℚ) by norm_num]
    exact Nat.le_ceil _
  exact_mod_cast hrounded
end
end Front82200_3_2
end
