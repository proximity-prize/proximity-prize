import ProximityPrize.SubmissionLower.ColumnRank6921
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_9Defs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace K21_9
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

abbrev K := K21.K
abbrev I := K21.I
abbrev node := K21.node
abbrev twist := K21.twist

def pencil (P Q : K[X]) (z : K) : K[X] := P + C z * Q

def fold (u : K21.Words) (z : K) (i : I) : K := u 0 i + z * u 1 i

theorem map_eval_node (P : K[X]) (i : I) :
    (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  Strata.eval_coefficient_map twist P (node i) (Native.native_domain_fixed i)

theorem pencil_natDegree (P Q : K[X]) (z : K) :
    (pencil P Q z).natDegree ≤ max P.natDegree Q.natDegree :=
  (natDegree_add_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le z Q))

theorem degree_sub_lt {P Q : K[X]} {n : ℕ} (hP : P.degree < n) (hQ : Q.degree < n) :
    (P-Q).degree < n :=
  (Polynomial.degree_sub_le _ _).trans_lt (max_lt hP hQ)

theorem pencil_degree {P Q : K[X]} {n : ℕ} (hP : P.degree < n) (hQ : Q.degree < n) (z : K) :
    (pencil P Q z).degree < n := by
  apply (Polynomial.degree_add_le _ _).trans_lt (max_lt hP ?_)
  by_cases hz : z = 0
  · simp [hz]
  · simpa only [degree_C_mul hz] using hQ

theorem eq_on_nodes (S : Finset I) (P Q : K[X])
    (hP : P.degree < S.card) (hQ : Q.degree < S.card)
    (h : ∀ i ∈ S, P.eval (node i) = Q.eval (node i)) : P = Q :=
  Polynomial.eq_of_degrees_lt_of_eval_index_eq S
    (fun _ _ _ _ hxy => node.injective hxy) hP hQ h

/-- The coefficient of the inner seed power, as an evaluation-coordinate polynomial. -/
def seedCoeff (P : K21.Bivar) (j : ℕ) : K[X] := (Bivariate.swap P).coeff j

def crossValue (u : K21.Words) (a b : K[X]) (A : Fin 2 → K[X])
    (i : I) (l j : Fin 2) : K :=
  a.eval (node i) * twist ((A l).eval (node i)) * u j i -
    b.eval (node i) * (A j).eval (node i) * twist (u l i)

def FirstEvaluation (a : K[X]) (A : Fin 2 → K[X]) (i : I) : Prop :=
  (K21.threeU a A).eval (C (node i)) =
    C (a.eval (node i)) * (C (twist ((A 0).eval (node i))) +
      Polynomial.X ^ K21.p * C (twist ((A 1).eval (node i))))

def _root_.K21_9_1.firstEvaluationAt (n : ℕ) (a : K[X]) (A : Fin 2 → K[X]) (i : I) : Prop :=
  (K21_8.threeUAt n a A).eval (C (node i)) =
    C (a.eval (node i)) * (C (twist ((A 0).eval (node i))) +
      Polynomial.X ^ n * C (twist ((A 1).eval (node i))))

def CoefficientIdentities (u : K21.Words) (a b : K[X]) (A : Fin 2 → K[X])
    (P : K21.Bivar) (i : I) : Prop :=
  (seedCoeff P 0).eval (node i) = crossValue u a b A i 0 0 ∧
  (seedCoeff P 1).eval (node i) = crossValue u a b A i 0 1 ∧
  (seedCoeff P K21.p).eval (node i) = crossValue u a b A i 1 0 ∧
  (seedCoeff P (K21.p + 1)).eval (node i) = crossValue u a b A i 1 1

/-- The four seed coefficients evaluated bilinearly, after restoring the fixed locator. -/
structure PolarData (u : K21.Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K21.sixNorm a ≠ K21.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ 32877
  b_bound : b.natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ 32877
  Q_degree : ∀ r s, (Q r s).degree < 163949
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)

abbrev PolarData.amp {u : K21.Words} (D : PolarData u) := pencil (D.A 0) (D.A 1)

theorem PolarData.left_bound {u : K21.Words} (D : PolarData u) (z : K) :
    (D.a * (D.amp z).map twist).natDegree ≤ 32877 :=
  natDegree_mul_le.trans <|
    (Nat.add_le_add_left (natDegree_map_le.trans (pencil_natDegree ..)) _).trans D.a_bound

theorem PolarData.right_bound {u : K21.Words} (D : PolarData u) (z : K) :
    (D.b * D.amp z).natDegree ≤ 32877 :=
  natDegree_mul_le.trans <|
    (Nat.add_le_add_left (pencil_natDegree ..) _).trans D.b_bound

private theorem iterate_six : iterateFrobenius K K21.p 6 = RingHom.id K := by
  apply RingHom.ext
  intro x
  change x ^ K21.p ^ 6 = x
  have hc : Fintype.card K = K21.p ^ 6 := KoalaBear.card_ext6
  rw [← hc]
  exact FiniteField.pow_card x

theorem sixNorm_twist (P : K[X]) : K21.sixNorm (P.map twist) = K21.sixNorm P := by
  unfold K21.sixNorm
  have h (j : Fin 6) :
      (P.map twist).map (iterateFrobenius K K21.p j.val) =
        P.map (iterateFrobenius K K21.p (j.val + 1)) := by
    rw [Polynomial.map_map, iterateFrobenius_add, iterateFrobenius_one]
    rfl
  simp_rw [h]
  rw [Fin.prod_univ_castSucc (n := 5),
    Fin.prod_univ_succ (f := fun j : Fin 6 => P.map (iterateFrobenius K K21.p j.val))]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, Nat.reduceAdd,
    iterate_six, iterateFrobenius_zero, Polynomial.map_id]
  exact mul_comm _ _

theorem sixNorm_mul (P Q : K[X]) : K21.sixNorm (P*Q) = K21.sixNorm P * K21.sixNorm Q := by
  simp only [K21.sixNorm, Polynomial.map_mul, Finset.prod_mul_distrib]

theorem sixNorm_ne_zero {P : K[X]} (h : P ≠ 0) : K21.sixNorm P ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ =>
    (Polynomial.map_ne_zero_iff (iterateFrobenius K K21.p j.val).injective).mpr h

end
end K21_9
end Port_K1_9Defs

section Port_K1_9Pencil
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace K21_9
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark

private theorem all_card : (Finset.univ : Finset I).card = 262144 := by
  rw [Finset.card_univ, IRSProfile.card_index]

private theorem affine_zero (f χ : K → K) (h : Function.Injective χ)
    {r s : K} (hrs : r ≠ s) (hf : ∀ z, f z = f 0 + χ z * (f 1 - f 0))
    (hr : f r = 0) (hs : f s = 0) (z : K) : f z = 0 := by
  have h₁ := hf r
  have h₂ := hf s
  have hb : (χ r - χ s) * (f 1 - f 0) = 0 := by linear_combination h₂ - h₁ + hr - hs
  have hd := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr (h.ne hrs))
  have hz : f z = f 0 := by simpa [hd] using hf z
  have hrr : f r = f 0 := by simpa [hd] using h₁
  exact hz.trans (hrr.symm.trans hr)

private theorem PolarData.amp_bound {u} (D : PolarData u) (z : K) :
    (D.amp z).natDegree ≤ 32877 :=
  (pencil_natDegree ..).trans (Nat.le_trans (Nat.le_add_left _ _) D.a_bound)

private theorem PolarData.amp_nonzero_at {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (i : I) : (D.amp r).eval (node i) ≠ 0 ∨ (D.amp s).eval (node i) ≠ 0 := by
  by_contra! hz
  obtain ⟨hr, hs⟩ := hz
  simp only [PolarData.amp, pencil, eval_add, eval_mul, eval_C] at hr hs
  have hb : (r-s) * (D.A 1).eval (node i) = 0 := by linear_combination hr - hs
  have h1 := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hrs)
  have h0 : (D.A 0).eval (node i) = 0 := by simpa [h1] using hr
  obtain ⟨P, Q, hPQ⟩ := D.primitive
  have h := congrArg (Polynomial.eval (node i)) hPQ
  simp only [eval_add, eval_mul, h0, h1, mul_zero, add_zero, eval_one, zero_ne_one] at h

private def PolarData.cross {u} (D : PolarData u) (r s : K) (P Q : K[X]) : K[X] :=
  D.a * (D.amp r).map twist * Q - D.b * D.amp s * P.map twist

private theorem PolarData.cross_degree {u} (D : PolarData u) (r s : K)
    {P Q : K[X]} (hP : P.degree < 131072) (hQ : Q.degree < 131072) :
    (D.cross r s P Q).degree < 163949 :=
  degree_sub_lt
    (Strata.degree_mul_lt_add _ _ 32877 131072 (D.left_bound r) hQ)
    (Strata.degree_mul_lt_add _ _ 32877 131072 (D.right_bound s) (degree_map_le.trans_lt hP))

private theorem PolarData.decoder_identity {u} (D : PolarData u) (z : K)
    (S : Finset I) (P : K[X]) (hS : 180169 ≤ S.card) (hP : P.degree < 131072)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : D.cross z z P P = D.Q z z := by
  have hcard : 163949 ≤ S.card := by omega
  have hb : (163949 : WithBot ℕ) ≤ S.card := by exact_mod_cast hcard
  apply eq_on_nodes S _ _ ((D.cross_degree z z hP hP).trans_le hb) ((D.Q_degree z z).trans_le hb)
  intro i hi
  simp only [PolarData.cross, eval_sub, eval_mul, map_eval_node, hits i hi, D.nodes]

private def residual (u : K21.Words) (P Q : K[X]) : K21.Words :=
  fun j i => u j i - (if j = 0 then P else Q).eval (node i)

private theorem fold_residual (u : K21.Words) (P Q : K[X]) (z : K) (i : I) :
    fold (residual u P Q) z i = fold u z i - (pencil P Q z).eval (node i) := by
  simp [fold, pencil, residual]
  ring

private def PolarData.subtract {u} (D : PolarData u) (P Q : K[X])
    (hP : P.degree < 131072) (hQ : Q.degree < 131072) : PolarData (residual u P Q) where
  a := D.a
  b := D.b
  A := D.A
  Q r s := D.Q r s - D.cross r s (pencil P Q r) (pencil P Q s)
  a_ne := D.a_ne
  norms_ne := D.norms_ne
  primitive := D.primitive
  a_bound := D.a_bound
  b_bound := D.b_bound
  Q_degree r s := degree_sub_lt (D.Q_degree r s)
    (D.cross_degree r s (pencil_degree hP hQ r) (pencil_degree hP hQ s))
  nodes r s i := by
    simp only [eval_sub, D.nodes, PolarData.cross, eval_mul, map_eval_node, fold_residual, map_sub]
    ring

/-- Two zero diagonal entries force an off-diagonal entry to vanish by the cyclic norm. -/
private theorem PolarData.offdiag_zero {u} (D : PolarData u) {r s : K}
    (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0) (hrr : D.Q r r = 0) (hss : D.Q s s = 0) :
    D.Q r s = 0 := by
  let E := D.amp s * (D.amp r).map twist
  have ha : D.a.natDegree ≤ 32877 := (Nat.le_add_right _ _).trans D.a_bound
  have hb : D.b.natDegree ≤ 32877 := (Nat.le_add_right _ _).trans D.b_bound
  let d := K21.amplitudeDegree (D.A 0) (D.A 1)
  have hE : E.natDegree ≤ d+d := natDegree_mul_le.trans
    (Nat.add_le_add (pencil_natDegree ..) (natDegree_map_le.trans (pencil_natDegree ..)))
  have hbE : D.b.natDegree + E.natDegree ≤ 65754 := by
    have := D.b_bound
    dsimp [d] at hE
    omega
  have haE : D.a.natDegree + E.natDegree ≤ 65754 := by
    have := D.a_bound
    dsimp [d] at hE
    omega
  have hl : (D.b * E * (D.Q r s).map twist).degree < 229703 :=
    Strata.degree_mul_lt_add _ _ 65754 163949 (natDegree_mul_le.trans hbE)
      (degree_map_le.trans_lt (D.Q_degree r s))
  have ht : (D.a.map twist * E.map twist * D.Q r s).degree < 229703 :=
    Strata.degree_mul_lt_add _ _ 65754 163949
      (natDegree_mul_le.trans ((Nat.add_le_add natDegree_map_le natDegree_map_le).trans haE))
      (D.Q_degree r s)
  have heq : D.b * E * (D.Q r s).map twist = D.a.map twist * E.map twist * D.Q r s := by
    apply eq_on_nodes Finset.univ _ _
      (by rw [all_card]; exact hl.trans (by norm_num)) (by rw [all_card]; exact ht.trans (by norm_num))
    intro i _
    have h₁ := (D.nodes r r i).symm
    have h₂ := (D.nodes s s i).symm
    rw [hrr, eval_zero] at h₁
    rw [hss, eval_zero] at h₂
    have hσ := congrArg (fun x => twist x) h₁
    simp only [map_sub, map_mul, map_zero] at hσ
    simp only [E, eval_mul, map_eval_node, D.nodes, map_sub, map_mul]
    linear_combination
      -(twist (D.a.eval (node i))) * twist (twist ((D.amp r).eval (node i))) *
        twist ((D.amp r).eval (node i)) * h₂ +
      D.b.eval (node i) * (D.amp s).eval (node i) * twist ((D.amp s).eval (node i)) * hσ
  by_contra hne
  have hn : E ≠ 0 := mul_ne_zero hs ((Polynomial.map_ne_zero_iff twist.injective).mpr hr)
  have hN := congrArg K21.sixNorm heq
  simp only [sixNorm_mul, sixNorm_twist] at hN
  exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hn)
    (mul_right_cancel₀ (sixNorm_ne_zero hne) hN.symm))

private theorem PolarData.zero_of_diagonal_zeros {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0)
    (hrr : D.Q r r = 0) (hss : D.Q s s = 0) (y z : K) : D.Q y z = 0 := by
  have hrs' := D.offdiag_zero hr hs hrr hss
  have hsr' := D.offdiag_zero hs hr hss hrr
  apply eq_on_nodes Finset.univ _ _ (by rw [all_card]; exact (D.Q_degree y z).trans (by norm_num))
    (by rw [all_card, degree_zero]; exact WithBot.bot_lt_coe 262144)
  intro i _
  let f (r s : K) := (D.Q r s).eval (node i)
  have right (x γ : K) : f x γ = f x 0 + id γ * (f x 1 - f x 0) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, id_eq]
    ring
  have left (x γ : K) : f γ x = f 0 x + twist γ * (f 1 x - f 0 x) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, map_add, map_mul,
      map_zero, map_one]
    ring
  have h₁ : f r z = 0 := affine_zero (f r) id Function.injective_id hrs (right r)
    (by simp [f, hrr]) (by simp [f, hrs']) z
  have h₂ : f s z = 0 := affine_zero (f s) id Function.injective_id hrs (right s)
    (by simp [f, hsr']) (by simp [f, hss]) z
  simpa only [eval_zero] using affine_zero (fun γ => f γ z) twist twist.injective hrs (left z) h₁ h₂ y

/-- A vanishing polarized relation forces every close decoder to be zero, including
the zero-amplitude case, where enough agreeing nodes survive the zeros of the left scalar. -/
private theorem PolarData.decoder_zero {u} (D : PolarData u) (hQ : ∀ r s, D.Q r s = 0) (z : K)
    (S : Finset I) (P : K[X]) (hS : 180169 ≤ S.card) (hP : P.degree < 131072)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : P = 0 := by
  classical
  by_cases hz : D.amp z = 0
  · let S' := S.filter (fun i => D.a.eval (node i) ≠ 0)
    let roots := S.filter (fun i => D.a.eval (node i) = 0)
    have hroots : roots.card ≤ D.a.natDegree := by
      rw [← Finset.card_image_of_injective roots node.injective]
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots D.a_ne).mpr (Finset.mem_filter.mp hi).2
    have hsum : roots.card + S'.card = S.card := Finset.card_filter_add_card_filter_not ..
    have ha : D.a.natDegree ≤ 32877 := (Nat.le_add_right _ _).trans D.a_bound
    have hcard : 131072 ≤ S'.card := by omega
    apply eq_on_nodes S' _ _ (hP.trans_le (by exact_mod_cast hcard))
      (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
    intro i hi
    have hi' : i ∈ S ∧ D.a.eval (node i) ≠ 0 := Finset.mem_filter.mp hi
    obtain ⟨hiS, hia⟩ := hi'
    rw [hits i hiS, eval_zero]
    obtain ⟨r, hr⟩ : ∃ r, (D.amp r).eval (node i) ≠ 0 := by
      rcases D.amp_nonzero_at zero_ne_one i with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have he := (D.nodes r z i).symm
    simp only [hQ, hz, eval_zero, mul_zero, zero_mul, sub_zero] at he
    have ht : twist ((D.amp r).eval (node i)) ≠ 0 := by
      intro h
      exact hr (twist.injective (h.trans (map_zero twist).symm))
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hia ht)
  · have he := D.decoder_identity z S P hS hP hits
    rw [hQ, PolarData.cross] at he
    by_contra hne
    have hN := congrArg K21.sixNorm (sub_eq_zero.mp he)
    simp only [sixNorm_mul, sixNorm_twist] at hN
    exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hz)
      (mul_right_cancel₀ (sixNorm_ne_zero hne) hN))

/-- Two nonzero-amplitude decoders determine a polynomial pencil for all marked labels. -/
theorem pencil_of_marks {u : K21.Words} (D : PolarData u) (Γ : Finset K)
    (M : ∀ z ∈ Γ, K21.BadMark u z) :
    Γ.card ≤ 2 ∨ ∃ P Q : K[X], P.degree < 131072 ∧ Q.degree < 131072 ∧
      ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z := by
  classical
  let G := Γ.filter (fun z => D.amp z ≠ 0)
  by_cases hsmall : G.card ≤ 1
  · let zeros := Γ.filter (fun z => D.amp z = 0)
    have hZ : zeros.card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro r s hr hs
      by_contra hrs
      have hr' := (Finset.mem_filter.mp hr).2
      have hs' := (Finset.mem_filter.mp hs).2
      simpa [hr', hs'] using D.amp_nonzero_at hrs (0 : I)
    have hsum : zeros.card + G.card = Γ.card := Finset.card_filter_add_card_filter_not ..
    exact Or.inl (by omega)
  right
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
  obtain ⟨hrΓ, hrA⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsΓ, hsA⟩ := Finset.mem_filter.mp hs
  let Wr := (M r hrΓ).decoder
  let Ws := (M s hsΓ).decoder
  let Q := C ((s-r)⁻¹) * (Ws-Wr)
  let P := Wr - C r * Q
  have hWr : Wr.degree < 131072 := (M r hrΓ).degree
  have hWs : Ws.degree < 131072 := (M s hsΓ).degree
  have scale (c : K) (V : K[X]) (hV : V.degree < 131072) : (C c * V).degree < 131072 := by
    by_cases hc : c = 0
    · rw [hc, map_zero, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe 131072
    · simpa only [degree_C_mul hc] using hV
  have hQ : Q.degree < 131072 := scale _ _ (degree_sub_lt hWs hWr)
  have hP : P.degree < 131072 := degree_sub_lt hWr (scale _ _ hQ)
  have hpr : pencil P Q r = Wr := by simp [pencil, P]
  have hps : pencil P Q s = Ws := by
    have hc : (C s - C r : K[X]) * C ((s-r)⁻¹) = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one]
    calc
      pencil P Q s = Wr + ((C s - C r) * C ((s-r)⁻¹)) * (Ws-Wr) := by
        simp only [pencil, P, Q]
        ring
      _ = Ws := by rw [hc, one_mul, add_comm, sub_add_cancel]
  let D' := D.subtract P Q hP hQ
  have hd (z : K) (hz : z ∈ Γ) (h : pencil P Q z = (M z hz).decoder) : D'.Q z z = 0 := by
    change D.Q z z - D.cross z z (pencil P Q z) (pencil P Q z) = 0
    rw [h, D.decoder_identity z _ _ (M z hz).agreement (M z hz).degree (M z hz).hits, sub_self]
  have hzero := D'.zero_of_diagonal_zeros hrs hrA hsA (hd r hrΓ hpr) (hd s hsΓ hps)
  refine ⟨P, Q, hP, hQ, fun z hz => sub_eq_zero.mp ?_⟩
  let W := M z hz
  change W.decoder - pencil P Q z = 0
  apply D'.decoder_zero hzero z W.support _ W.agreement (degree_sub_lt W.degree (pencil_degree hP hQ z))
  intro i hi
  rw [fold_residual, eval_sub, W.hits i hi]
  rfl

end
end K21_9
end Port_K1_9Pencil

section Port_K1_9Polar
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace K21_9
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark

private theorem coeff_seedCoeff (P : K21.Bivar) (j m : ℕ) :
    (seedCoeff P j).coeff m = (P.coeff m).coeff j := by
  induction P using Polynomial.induction_on' with
  | add A B hA hB => simp only [seedCoeff, map_add, coeff_add] at hA hB ⊢; rw [hA, hB]
  | monomial n f =>
    simp only [seedCoeff, Bivariate.swap_monomial, coeff_mul_C, coeff_map,
      C_mul_X_pow_eq_monomial, coeff_monomial]
    split_ifs <;> simp

private theorem eval_seedCoeff (P : K21.Bivar) (j : ℕ) (x : K) :
    (seedCoeff P j).eval x = (P.eval (C x)).coeff j := by
  induction P using Polynomial.induction_on' with
  | add A B hA hB =>
    simp only [seedCoeff, map_add, coeff_add, eval_add] at hA hB ⊢
    rw [hA, hB]
  | monomial n f =>
    simp only [seedCoeff, Bivariate.swap_monomial, eval_monomial, ← C_pow, coeff_mul_C,
      coeff_map, eval_mul, eval_C, eval_pow, eval_X]

private theorem seedCoeff_degree (P : K21.Bivar) (j h : ℕ) (hp : P.degree < h) :
    (seedCoeff P j).degree < h := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  rw [coeff_seedCoeff, coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm)), coeff_zero]

private theorem eval_liftX (P : K[X]) (x : K) :
    (K21.liftX P).eval (C x) = C (P.eval x) :=
  Polynomial.eval_map_apply Polynomial.C x

theorem eval_first (a : K21.K[X]) (A : Fin 2 → K21.K[X]) (i : K21.I) (n : ℕ) :
    (K21.liftX a * (K21.liftX ((A 0).map K21.twist) +
      K21.seed ^ n * K21.liftX ((A 1).map K21.twist))).eval (C (K21.node i)) =
      C (a.eval (K21.node i)) * (C (K21.twist ((A 0).eval (K21.node i))) +
        Polynomial.X ^ n * C (K21.twist ((A 1).eval (K21.node i)))) := by
  rw [eval_mul, eval_liftX a, eval_add, eval_liftX ((A 0).map K21.twist), eval_mul,
    eval_liftX ((A 1).map K21.twist), eval_pow, K21.seed, eval_C, map_eval_node, map_eval_node]

private theorem eval_threeV (b : K[X]) (A : Fin 2 → K[X]) (i : I) :
    (K21.threeV b A).eval (C (node i)) =
      -(C (b.eval (node i)) * (C ((A 0).eval (node i)) + (Polynomial.X (R := K)) * C ((A 1).eval (node i)))) := by
  unfold K21.threeV
  rw [eval_neg, eval_mul, eval_liftX b, eval_add, eval_liftX (A 0), eval_mul,
    eval_liftX (A 1), K21.seed, eval_C]

theorem coefficients_at_node
    (u : K21.Words) (a b : K21.K[X]) (A : Fin 2 → K21.K[X])
    (i : K21.I) (n : ℕ) (hn : 1 < n) (hσ : ∀ z : K21.K, z ^ n = K21.twist z) (P U : K21.Bivar)
    (hU : U.eval (C (K21.node i)) =
      C (a.eval (K21.node i)) * (C (K21.twist ((A 0).eval (K21.node i))) +
        Polynomial.X ^ n * C (K21.twist ((A 1).eval (K21.node i)))))
    (h : P.eval (C (K21.node i)) =
      U.eval (C (K21.node i)) *
          (C (u 0 i) + Polynomial.X (R := K21.K) * C (u 1 i)) +
      (K21.threeV b A).eval (C (K21.node i)) *
        (C (u 0 i ^ n) + Polynomial.X (R := K21.K) ^ n * C (u 1 i ^ n))) :
    (seedCoeff P 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff P 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff P n).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff P (n + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  let q := crossValue u a b A i
  have hexpand : P.eval (C (node i)) =
      C (q 0 0) + C (q 0 1) * Polynomial.X + C (q 1 0) * Polynomial.X ^ n +
        C (q 1 1) * Polynomial.X ^ (n + 1) := by
    rw [h, hU, hσ (u 0 i), hσ (u 1 i), eval_threeV, pow_succ (Polynomial.X (R := K)) n]
    simp only [q, crossValue, map_sub, map_mul]
    generalize (Polynomial.X (R := K)) ^ n = xp
    ring
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have hs0 : n + 1 ≠ 0 := by omega
  have hs1 : n + 1 ≠ 1 := by omega
  have hs : n + 1 ≠ n := by omega
  simp only [eval_seedCoeff, hexpand, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
    h0, h0.symm, h1, h1.symm, hs0, hs0.symm, hs1, hs1.symm, hs, hs.symm, ite_true, ite_false, and_self,
    Nat.zero_ne_one, Nat.one_ne_zero, zero_add, add_zero, q]

-- The node set stays abstract while checking the locator and degree calculations.
private theorem polarData_of_set {u : K21.Words} (S : Finset I) (height : ℕ)
    (a b : K[X]) (A : Fin 2 → K[X]) (output : K21.Bivar)
    (hh : height + S.card ≤ 32877)
    (hout : output.degree < (131072 + height : ℕ))
    (hfirst : a.natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K21.sixNorm a ≠ K21.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let t (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (t j).degree < 163949 := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (131072 + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show 131072 + height + g.natDegree ≤ 163949 by omega))
  have ha : (g * a).natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ 32877 := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ 32877 := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (t 0) (t 1) s) (pencil (t K21.p) (t (K21.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K21.p) (hd (K21.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, t, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, t, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring

/-- Polarize the four distinct seed powers and restore the fixed locator. -/
theorem polarData_of_coefficients {u : K21.Words} {T : K21.TwoActive u} {R : K21.Relation T}
    {D : K21.Reduction u T R} (B : K21.RankThree u T R D)
    (hp : K21.Parallel B) (hn : ¬ K21.UnitNorm B)
    (hc : ∀ i ∉ K21.fixedNodes R, CoefficientIdentities u B.a B.b B.α B.output i) :
    Nonempty (PolarData u) := by
  have hh : D.height + (K21.fixedNodes R).card ≤ 32877 := by
    rw [D.height_eq, K21.TwoActive.height]
    have h₁ := T.ab
    have h₂ := T.active
    have h₃ := T.degreeSum
    omega
  have hfirst := (congrArg (fun A : Fin 2 → K[X] =>
    B.a.natDegree + K21.amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (K21.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive hc

end
end K21_9
end Port_K1_9Polar

section Port_K1_9Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace K21_9
noncomputable section

open Polynomial FrobeniusLocator ProximityPrize.Benchmark

def c1 : Prop :=
  ∀ (a : K[X]) (A : Fin 2 → K[X]) (i : I), FirstEvaluation a A i

def c2 : Prop :=
  ∀ u (T : K21.TwoActive u) (R : K21.Relation T) (D : K21.Reduction u T R)
    (B : K21.RankThree u T R D), K21.Parallel B →
    ∀ i ∉ K21.fixedNodes R, FirstEvaluation B.a B.α i →
      CoefficientIdentities u B.a B.b B.α B.output i

/-- Fixing one support leaves at most one other label per node outside that support. -/
private theorem pencil_count {u : K21.Words} (Γ : Finset K)
    (M : ∀ z ∈ Γ, K21.BadMark u z) {P Q : K[X]} (hP : P.degree < 131072)
    (hQ : Q.degree < 131072) (h : ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z) :
    Γ.card ≤ 81976 := by
  classical
  by_cases hΓ : Γ.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
  obtain ⟨r, hr⟩ := hΓ
  let S := (M r hr).support
  let nonjoint (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {z : K} (hz : z ∈ Γ) {i : I} (hi : i ∈ (M z hz).support) :
      P.eval (node i) + z * Q.eval (node i) = u 0 i + z * u 1 i := by
    simpa only [h z hz, pencil, eval_add, eval_mul, eval_C] using (M z hz).hits i hi
  have unique {z t : K} (hz : z ∈ Γ) (ht : t ∈ Γ) {i : I}
      (hi : i ∈ (M z hz).support) (hj : i ∈ (M t ht).support) (hn : nonjoint i) : z = t := by
    by_contra hne
    have h₁ := hits hz hi
    have h₂ := hits ht hj
    have hw : (z-t) * (Q.eval (node i) - u 1 i) = 0 := by linear_combination h₁ - h₂
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at h₁
    exact hn.elim (fun hbad => hbad h₁) (fun hbad => hbad he)
  have witness (z : ↥(Γ.erase r)) :
      ∃ i ∈ (M z.val (Finset.mem_erase.mp z.property).2).support, nonjoint i := by
    let W := M z.val (Finset.mem_erase.mp z.property).2
    by_contra hw
    apply W.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose f hf hn using witness
  let g : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun z =>
    ⟨f z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp z.property).1 (unique (Finset.mem_erase.mp z.property).2 hr (hf z) hi (hn z))⟩⟩
  have hg : Function.Injective g := by
    intro z t hzt
    have he : f z = f t := congrArg Subtype.val hzt
    apply Subtype.ext
    have ht := hf t
    rw [← he] at ht
    exact unique (Finset.mem_erase.mp z.property).2 (Finset.mem_erase.mp t.property).2 (hf z) ht (hn z)
  have hcard := Finset.card_le_card_of_injective hg
  have he := Finset.card_erase_add_one hr
  have hS : 180169 ≤ S.card := (M r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hcard
  omega

theorem of_children (h1 : c1) (h2 : c2) : K21.c9 := by
  intro u T R D B hp hn Γ hΓ
  classical
  obtain ⟨data⟩ := polarData_of_coefficients B hp hn
    (fun i hi => h2 u T R D B hp i hi (h1 B.a B.α i))
  let M (z : K) (hz : z ∈ Γ) := Classical.choice (K21.bad_mark u Γ hΓ z hz)
  rcases pencil_of_marks data Γ M with hsmall | ⟨P, Q, hP, hQ, h⟩
  · omega
  · exact pencil_count Γ M hP hQ h

end
end K21_9
end Port_K1_9Split

section Port_K1_9_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace K21_9_1

private theorem firstEvaluationAt_ok (n : ℕ) (a : Polynomial K21.K)
    (A : Fin 2 → Polynomial K21.K) (i : K21.I) : firstEvaluationAt n a A i := by
  unfold firstEvaluationAt K21_8.threeUAt
  exact K21_9.eval_first a A i n

private theorem threeUAt_native : K21_8.threeUAt K21.p = K21.threeU := by
  unfold K21_8.threeUAt K21.threeU
  rfl

/-- Evaluating the outer coordinate at a native node leaves the seed variable intact. -/
theorem proof : K21_9.c1 := by
  intro a A i
  unfold K21_9.FirstEvaluation
  rw [← threeUAt_native]
  exact firstEvaluationAt_ok K21.p a A i

end K21_9_1
end Port_K1_9_1Proof

section Port_K1_9_2Proof
set_option autoImplicit true
namespace K21_9_2

noncomputable section

open Polynomial

private theorem pow_eq_twist (z : K21.K) : z ^ K21.p = K21.twist z :=
  (frobenius_def K21.p z).symm

theorem proof : K21_9.c2 := by
  intro u T R D B hparallel i hi hfirst
  change B.α = B.β at hparallel
  have hnodes := (B.nodes i hi).symm
  rw [← hparallel] at hnodes
  have hp : 1 < K21.p := by norm_num [K21.p, FrobeniusLocator.Native.p]
  have hσ := pow_eq_twist
  unfold K21_9.FirstEvaluation at hfirst
  unfold K21_9.CoefficientIdentities
  -- Check the instance conversions at a variable exponent before specializing to p.
  generalize K21.p = n at hp hσ hfirst hnodes ⊢
  as_aux_lemma =>
    exact K21_9.coefficients_at_node u B.a B.b B.α i n hp hσ
      B.output (K21.threeU B.a B.α) hfirst hnodes

end

end K21_9_2
end Port_K1_9_2Proof
