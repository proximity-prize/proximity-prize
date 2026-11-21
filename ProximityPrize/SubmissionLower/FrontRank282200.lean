import ProximityPrize.SubmissionLower.FrontRank182200

set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace Front82200_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open private seedCoeff_degree from ProximityPrize.SubmissionLower.Fast068
open private coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native from ProximityPrize.SubmissionLower.PortFrontA
abbrev heightBound : ℕ := Front82200.heightCap
structure PolarData (u : Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
abbrev PolarData.amp {u : Words} (D : PolarData u) := pencil (D.A 0) (D.A 1)
private theorem polarData_of_set {u : Words} (S : Finset I) (height : ℕ)
    (a b : K[X]) (A : Fin 2 → K[X]) (output : P0.Bivar)
    (hh : height + S.card ≤ heightBound)
    (hout : output.degree < (k + height : ℕ))
    (hfirst : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K1.sixNorm a ≠ K1.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let v (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (v j).degree < (k + heightBound : ℕ) := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (k + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show k + height + g.natDegree ≤ k + heightBound by omega))
  have ha : (g * a).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (v 0) (v 1) s) (pencil (v K1.p) (v (K1.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K1.p) (hd (K1.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, v, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, v, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring
end
end Front82200_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Front82200_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open Front82200 (Words k agreement amplitudeDegree)
open K1_9 (K I node twist pencil fold map_eval_node pencil_natDegree pencil_degree
  degree_sub_lt eq_on_nodes sixNorm_mul sixNorm_twist sixNorm_ne_zero)
open private all_card affine_zero residual fold_residual from ProximityPrize.SubmissionLower.Fast068
private theorem amp_natDegree_le {u : Words} (D : PolarData u) (z : K) :
    (D.amp z).natDegree ≤ amplitudeDegree (D.A 0) (D.A 1) :=
  pencil_natDegree ..
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
    {P Q : K[X]} (hP : P.degree < k) (hQ : Q.degree < k) :
    (D.cross r s P Q).degree < (k + heightBound : ℕ) := by
  have hl : (D.a * (D.amp r).map twist).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (natDegree_map_le.trans (amp_natDegree_le D r)) _).trans D.a_bound
  have hr : (D.b * D.amp s).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (amp_natDegree_le D s) _).trans D.b_bound
  exact degree_sub_lt
    (Strata.degree_mul_lt_add _ _ heightBound k hl hQ)
    (Strata.degree_mul_lt_add _ _ heightBound k hr (degree_map_le.trans_lt hP))
private theorem PolarData.decoder_identity {u} (D : PolarData u) (z : K)
    (S : Finset I) (P : K[X]) (hS : agreement ≤ S.card) (hP : P.degree < k)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : D.cross z z P P = D.Q z z := by
  have hcard := (show k + heightBound ≤ agreement by decide).trans hS
  have hb : ((k + heightBound : ℕ) : WithBot ℕ) ≤ S.card := by exact_mod_cast hcard
  apply eq_on_nodes S _ _ ((D.cross_degree z z hP hP).trans_le hb) ((D.Q_degree z z).trans_le hb)
  intro i hi
  simp only [PolarData.cross, eval_sub, eval_mul, map_eval_node, hits i hi, D.nodes]
private def PolarData.subtract {u} (D : PolarData u) (P Q : K[X])
    (hP : P.degree < k) (hQ : Q.degree < k) : PolarData (residual u P Q) where
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
private theorem PolarData.offdiag_zero {u} (D : PolarData u) {r s : K}
    (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0) (hrr : D.Q r r = 0) (hss : D.Q s s = 0) :
    D.Q r s = 0 := by
  let E := D.amp s * (D.amp r).map twist
  let d := amplitudeDegree (D.A 0) (D.A 1)
  have hd : d ≤ heightBound := (Nat.le_add_left _ _).trans D.a_bound
  have hE : E.natDegree ≤ d + d := natDegree_mul_le.trans
    (Nat.add_le_add (amp_natDegree_le D s) (natDegree_map_le.trans (amp_natDegree_le D r)))
  have hl : (D.b * E).natDegree ≤ heightBound + heightBound := by
    have hb : D.b.natDegree + d ≤ heightBound := D.b_bound
    exact natDegree_mul_le.trans (by omega)
  have ht : (D.a.map twist * E.map twist).natDegree ≤ heightBound + heightBound := by
    have ha : D.a.natDegree + d ≤ heightBound := D.a_bound
    exact natDegree_mul_le.trans
      ((Nat.add_le_add natDegree_map_le natDegree_map_le).trans (by omega))
  have hcut : ((k + heightBound + (heightBound + heightBound) : ℕ) : WithBot ℕ) ≤
      (Finset.univ : Finset I).card := by
    rw [all_card]
    exact_mod_cast (show k + heightBound + (heightBound + heightBound) ≤ 262144 by decide)
  have heq : D.b * E * (D.Q r s).map twist = D.a.map twist * E.map twist * D.Q r s := by
    apply eq_on_nodes Finset.univ _ _
      ((Strata.degree_mul_lt_add _ _ _ _ hl (degree_map_le.trans_lt (D.Q_degree r s))).trans_le hcut)
      ((Strata.degree_mul_lt_add _ _ _ _ ht (D.Q_degree r s)).trans_le hcut)
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
  have hN := congrArg K1.sixNorm heq
  simp only [sixNorm_mul, sixNorm_twist] at hN
  exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hn)
    (mul_right_cancel₀ (sixNorm_ne_zero hne) hN.symm))
private theorem PolarData.zero_of_diagonal_zeros {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0)
    (hrr : D.Q r r = 0) (hss : D.Q s s = 0) (y z : K) : D.Q y z = 0 := by
  have hrs' := D.offdiag_zero hr hs hrr hss
  have hsr' := D.offdiag_zero hs hr hss hrr
  apply eq_on_nodes Finset.univ _ _ (by rw [all_card]; exact (D.Q_degree y z).trans_le (by exact_mod_cast (show k + heightBound ≤ 262144 by decide)))
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
private theorem PolarData.decoder_zero {u} (D : PolarData u) (hQ : ∀ r s, D.Q r s = 0) (z : K)
    (S : Finset I) (P : K[X]) (hS : agreement ≤ S.card) (hP : P.degree < k)
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
    have ha : D.a.natDegree ≤ heightBound := (Nat.le_add_right _ _).trans D.a_bound
    have hmargin : k + heightBound ≤ agreement := by decide
    have hcard : k ≤ S'.card := by omega
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
    have hN := congrArg K1.sixNorm (sub_eq_zero.mp he)
    simp only [sixNorm_mul, sixNorm_twist] at hN
    exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hz)
      (mul_right_cancel₀ (sixNorm_ne_zero hne) hN))
theorem pencil_of_marks {u : Words} (D : PolarData u) (Γ : Finset K)
    (M : ∀ z ∈ Γ, Front82200.BadMark u z) :
    Γ.card ≤ 2 ∨ ∃ P Q : K[X], P.degree < k ∧ Q.degree < k ∧
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
  have hWr : Wr.degree < k := (M r hrΓ).degree
  have hWs : Ws.degree < k := (M s hsΓ).degree
  have scale (c : K) (V : K[X]) (hV : V.degree < k) : (C c * V).degree < k := by
    by_cases hc : c = 0
    · rw [hc, map_zero, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe k
    · simpa only [degree_C_mul hc] using hV
  have hQ : Q.degree < k := scale _ _ (degree_sub_lt hWs hWr)
  have hP : P.degree < k := degree_sub_lt hWr (scale _ _ hQ)
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
end Front82200_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Front82200_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open Front82200 (Words k agreement t amplitudeDegree)
open K1_9 (K I node pencil CoefficientIdentities)
open private coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native from ProximityPrize.SubmissionLower.PortFrontA
private theorem coefficients {u : Words} {T : Front82200.TwoActive u} {R : Front82200.Relation T}
    {D : Front82200.Reduction u T R} (B : Front82200.RankThree u T R D) (hp : Front82200.Parallel B)
    (i : I) (hi : i ∉ Front82200.fixedNodes R) :
    CoefficientIdentities u B.a B.b B.α B.output i := by
  have hnodes : P0_5.relationOnAt P0.p u (Front82200.fixedNodes R) (P0_5.threeUAt P0.p B.a B.β)
      (P0.threeV B.b B.α) B.output := by
    rw [threeUAt_native, relationOnAt_native]
    exact B.nodes
  exact coefficientsAt P0.p (by decide) pow_eq_twist u (Front82200.fixedNodes R)
    B.a B.b B.α B.β B.output hp hnodes i hi
private theorem polarData_of_parallel {u : Words} {T : Front82200.TwoActive u} {R : Front82200.Relation T}
    {D : Front82200.Reduction u T R} (B : Front82200.RankThree u T R D)
    (hu : Front82200.FrontRemainder u) (hp : Front82200.Parallel B) (hn : ¬ Front82200.UnitNorm B) :
    Nonempty (PolarData u) := by
  have hh : D.height + (Front82200.fixedNodes R).card ≤ heightBound := by
    rw [D.height_eq]
    exact (Front82200.relation_height_le hu T).trans (by decide)
  have hfirst := (congrArg (fun A : Fin 2 → K[X] =>
    B.a.natDegree + amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (Front82200.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive (coefficients B hp)
private theorem pencil_count {u : Words} (Γ : Finset K)
    (M : ∀ z ∈ Γ, Front82200.BadMark u z) {P Q : K[X]} (hP : P.degree < k)
    (hQ : Q.degree < k) (h : ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z) :
    Γ.card ≤ t + 1 := by
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
  have hS : agreement ≤ S.card := (M r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hcard
  change 179935 ≤ S.card at hS
  change Γ.card ≤ 82210
  omega
theorem proof : Front82200.c2 := by
  intro u hu T R D B _ hp hn Γ hΓ _
  classical
  obtain ⟨data⟩ := polarData_of_parallel B hu hp hn
  let M (z : K) (hz : z ∈ Γ) := Classical.choice (Front82200.bad_mark u Γ hΓ z hz)
  rcases pencil_of_marks data Γ M with
    hsmall | ⟨P, Q, hP, hQ, h⟩
  · exact hsmall.trans (by decide)
  · exact pencil_count Γ M hP hQ h
end
end Front82200_2
end
