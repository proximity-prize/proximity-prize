import ProximityPrize.SubmissionLower.H2429ConstantSlopes

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace H2429AffineResidue

open Polynomial FrobeniusLocator P1
open scoped Polynomial

private noncomputable def words {cap : ℕ} {u : Words} {del : Finset I}
    (M : ModelAt cap u del) : Words := fun j i =>
  (if j = 0 then M.word i else M.Q.eval (node i)) / M.E.eval (node i)

private theorem first {cap : ℕ} {u : Words} {del : Finset I} (M : ModelAt cap u del) (i : I) :
    M.E.eval (node i) * words M 0 i = M.word i := by
  change M.E.eval (node i) * (M.word i / M.E.eval (node i)) = M.word i
  rw [mul_comm, div_mul_cancel₀ _ (M.E_nodes i)]

private theorem second {cap : ℕ} {u : Words} {del : Finset I} (M : ModelAt cap u del) (i : I) :
    M.E.eval (node i) * words M 1 i = M.Q.eval (node i) := by
  change M.E.eval (node i) * (M.Q.eval (node i) / M.E.eval (node i)) = M.Q.eval (node i)
  rw [mul_comm, div_mul_cancel₀ _ (M.E_nodes i)]

private noncomputable def linearModel {cap : ℕ} {u : Words} {del : Finset I}
    (M : ModelAt cap u del) : ModelAt cap (words M) del :=
  {
    shift := 0
    pencil₀ := 0
    pencil₁ := 0
    pencil₀_degree := by rw [degree_zero]; exact WithBot.bot_lt_coe k
    pencil₁_degree := by rw [degree_zero]; exact WithBot.bot_lt_coe k
    E := M.E
    factor := 1
    Q := M.Q
    A₀ := 1
    A₁ := 0
    word := M.word
    word_fixed := M.word_fixed
    word_deleted := M.word_deleted
    E_monic := M.E_monic
    E_nodes := M.E_nodes
    factor_nodes := by simp
    coprime_factor := ⟨0,1,by simp⟩
    offset_proper := M.offset_proper
    offset_reduced := M.offset_reduced
    adjacent_coprime := M.adjacent_coprime
    amplitudes_primitive := ⟨1,0,by simp⟩
    first_amplitude_unit := ⟨1,0,by simp⟩
    height_bound := by simpa [amplitudeDegree] using (le_trans (Nat.le_add_right _ _) M.height_bound)
    first_word := fun i _ => by simpa using first M i
    second_word := fun i _ => by simpa using second M i
  }

private theorem linearHeight {cap : ℕ} {u : Words} {del : Finset I} (M : ModelAt cap u del)
    (degree : M.E.natDegree = 2429) : (linearModel M).overhead = 2429 := by
  simp [ModelAt.overhead, linearModel, amplitudeDegree, degree]

private theorem linearMark {cap : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (M : ModelAt cap u del) (F : FamilyAt 179876 M Γ) {γ : K} (hγ : γ ∈ Γ) (z : K)
    (height : M.overhead = 2429) (degree : M.E.natDegree = 2429)
    (residue : M.E ∣ F.scalar γ + C z * M.Q) :
    Nonempty (MarkAt (A := 179876) (linearModel M) z (F.scalar γ)) := by
  let S := F.scalar γ
  let B := F.mark γ hγ
  obtain ⟨W, hW⟩ := residue
  have Edeg : M.E.natDegree = 2429 := degree
  have Qdeg : M.Q.natDegree < 2429 := by
    by_cases qzero : M.Q = 0
    · simp [qzero]
    · exact (natDegree_lt_iff_degree_lt qzero).mpr (by
        simpa only [degree_eq_natDegree M.E_monic.ne_zero, Edeg] using M.offset_proper)
  have Sdeg : S.natDegree < k + 2429 := by
    rcases B.scalar_degree with zero | bound
    · simp [S, zero]
    · change (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead at bound
      omega
  have Wdeg : W.degree < k := by
    by_cases wz : W = 0
    · rw [wz, degree_zero]
      exact WithBot.bot_lt_coe k
    have total : (S + C (z) * M.Q).natDegree < k + 2429 :=
      (natDegree_add_le _ _).trans_lt
        (max_lt Sdeg ((natDegree_C_mul_le _ _).trans_lt (by omega)))
    rw [hW, natDegree_mul M.E_monic.ne_zero wz, Edeg] at total
    exact (natDegree_lt_iff_degree_lt wz).mp (by omega)
  have nonjoint : ¬ (ExtendsOn node ((words M) 0) k B.bad.support ∧
      ExtendsOn node ((words M) 1) k B.bad.support) := by
    rintro ⟨_, ⟨W₁, deg₁, eval₁⟩⟩
    have injective : Set.InjOn node (B.bad.support : Set I) :=
      ProximityPrize.Benchmark.IRSProfile.domain.injective.injOn
    have cards : 179876 ≤ B.bad.support.card := B.bad.agreement
    have room : 2429 + k ≤ 179876 := by decide
    have eq : M.E * W₁ = M.Q := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq B.bad.support injective
      · have h := Strata.degree_mul_lt_add M.E W₁ 2429 k degree.le deg₁
        exact h.trans_le (by exact_mod_cast (show 2429 + k ≤ B.bad.support.card by omega))
      · exact (M.offset_proper.trans_le degree_le_natDegree).trans_le (by
          rw [degree]
          exact_mod_cast (show 2429 ≤ B.bad.support.card by omega))
      · intro i hi
        rw [eval_mul, eval₁ i hi, second M i]
    have dv : M.E ∣ M.Q := ⟨W₁,eq.symm⟩
    exact (Nat.ne_of_gt (show 0 < M.E.natDegree by omega)) (natDegree_eq_zero_of_isUnit
      (M.offset_reduced.isUnit_of_dvd' dv (dvd_refl _)))
  let bad : BadMarkAt 179876 (words M) (z) := {
    support := B.bad.support
    decoder := W
    agreement := B.bad.agreement
    degree := Wdeg
    hits := by
      intro i hi
      apply mul_left_cancel₀ (M.E_nodes i)
      have evalW := congrArg (eval (node i)) hW
      simp only [eval_add, eval_mul, eval_C, B.scalar_hits i hi] at evalW
      linear_combination -evalW - first M i - z * second M i
    nonjoint := nonjoint
  }
  refine ⟨⟨bad,B.avoids_deleted,B.scalar_fixed,?_,B.scalar_hits,?_,?_⟩⟩
  · rw [linearHeight M degree, ← height]
    exact B.scalar_degree
  · have firstUnit : IsCoprime (1 : K[X]) M.E := ⟨1,0,by simp⟩
    simpa [linearModel, ModelAt.amplitude] using firstUnit
  · change M.E * (W - 0 - C (z - 0) * 0) -
      C (z - 0) * M.Q = 1 * (1 + C (z - 0) * 0) * S
    simp only [sub_zero, mul_zero, add_zero, one_mul]
    rw [← hW, add_sub_cancel_right]

private theorem relabelFamily {cap hits : ℕ} {u v : Words} {del : Finset I} {Γ : Finset K}
    {M : ModelAt cap u del} (F : FamilyAt hits M Γ) (N : ModelAt cap v del)
    (label : K → K) (injective : Set.InjOn label (Γ : Set K))
    (marks : ∀ γ ∈ Γ, Nonempty (MarkAt (A := hits) N (label γ) (F.scalar γ))) :
    ∃ G : FamilyAt hits N (Γ.image label), ∀ γ ∈ Γ, G.scalar (label γ) = F.scalar γ := by
  classical
  let Λ := Γ.image label
  let origin (z : K) := if hz : z ∈ Λ then (Finset.mem_image.mp hz).choose else 0
  have origin_spec (z : K) (hz : z ∈ Λ) : origin z ∈ Γ ∧ label (origin z) = z := by
    simpa only [origin, dite_eq_left hz] using (Finset.mem_image.mp hz).choose_spec
  let G : FamilyAt hits N Λ := {
    scalar := fun z => F.scalar (origin z)
    mark := fun z hz => by
      have hm := (marks (origin z) (origin_spec z hz).1).some
      rw [(origin_spec z hz).2] at hm
      exact hm
    distinct := by
      intro a ha b hb h
      have origins := F.distinct (origin_spec a ha).1 (origin_spec b hb).1 h
      exact (origin_spec a ha).2.symm.trans ((congrArg label origins).trans (origin_spec b hb).2)
  }
  refine ⟨G, ?_⟩
  intro γ hγ
  have hz : label γ ∈ Λ := Finset.mem_image.mpr ⟨γ,hγ,rfl⟩
  have eq := injective (origin_spec _ hz).1 hγ (origin_spec _ hz).2
  exact congrArg F.scalar eq

/-- At the minimum pole degree, a change of label makes the residues linear. -/
theorem normalize {cap : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (M : ModelAt cap u del) (F : FamilyAt 179876 M Γ)
    (height : M.overhead = 2429) (degree : M.E.natDegree = 2429) :
    ∃ (label : K → K) (u' : Words) (N : ModelAt cap u' del)
      (G : FamilyAt 179876 N (Γ.image label)),
      Set.InjOn label (Γ : Set K) ∧ N.shift = 0 ∧ N.E = M.E ∧ N.Q = M.Q ∧
      N.factor = 1 ∧ N.A₀ = 1 ∧ N.A₁ = 0 ∧ N.word = M.word ∧ N.overhead = 2429 ∧
      ∀ γ ∈ Γ, G.scalar (label γ) = F.scalar γ := by
  classical
  have arithmetic := height
  change (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁ = 2429 at arithmetic
  have factorDegree : M.factor.natDegree = 0 := by omega
  have amplitude : amplitudeDegree M.A₀ M.A₁ = 0 := by omega
  have positive : 0 < M.E.natDegree := by omega
  obtain ⟨D⟩ := H2429ConstantSlopes.exists_coordinate M F amplitude positive
  let c := M.factor.coeff 0
  have hc₀ : M.factor = C c := eq_C_of_natDegree_le_zero factorDegree.le
  have hc : c ≠ 0 := by
    intro h
    have hunit : IsUnit M.E := isCoprime_zero_right.mp (by simpa [hc₀,h] using M.coprime_factor)
    exact (Nat.ne_of_gt positive) (natDegree_eq_zero_of_isUnit hunit)
  let label (γ : K) := -D.slope γ / c
  have label_inj : Set.InjOn label (Γ : Set K) := by
    intro a ha b hb h
    apply D.slope_injective ha hb
    have h₁ := congrArg (fun z : K => z * c) h
    simpa only [label, div_mul_cancel₀ _ hc, neg_inj] using h₁
  have residue (γ : K) (hγ : γ ∈ Γ) :
      M.E ∣ F.scalar γ + C (label γ) * M.Q := by
    let B := F.mark γ hγ
    let a := c * D.denominator γ
    have ha : a ≠ 0 := mul_ne_zero hc (D.denominator_nonzero γ hγ)
    have he : a * label γ = M.label γ := by
      change (c * D.denominator γ) * (-D.slope γ / c) = M.label γ
      rw [mul_comm c, mul_assoc, mul_comm c, div_mul_cancel₀ _ hc, mul_neg,
        D.denominator_mul_slope hγ, neg_neg]
    have basis : M.E * M.decoder B.bad = C a * F.scalar γ + C (M.label γ) * M.Q := by
      have h := B.identity
      rw [hc₀, D.amplitude_eq, ← C_mul] at h
      linear_combination h
    refine ⟨C a⁻¹ * M.decoder B.bad, ?_⟩
    have hprod : C a * (F.scalar γ + C (label γ) * M.Q) = M.E * M.decoder B.bad := by
      rw [mul_add, ← mul_assoc, ← C_mul, he, basis]
    calc
      _ = C a⁻¹ * (C a * (F.scalar γ + C (label γ) * M.Q)) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
      _ = _ := by rw [hprod]; ring
  obtain ⟨G, hG⟩ := relabelFamily F (linearModel M) label label_inj
    (fun γ hγ => linearMark M F hγ (label γ) height degree (residue γ hγ))
  exact ⟨label,words M,linearModel M,G,label_inj,rfl,rfl,rfl,rfl,rfl,rfl,rfl,linearHeight M degree,hG⟩

end H2429AffineResidue
