import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence
import ProximityPrize.SubmissionLower.MergedInfra6815_6



namespace ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

open MvPolynomial KaehlerDifferential
open RCN002 RCN005 RCN095 RCN237 RCN264 RCN265 RCN277 RCN314 RCN341 RCN344
open RCN037 RCN038 RCN041 RCN042 RCN046
open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

theorem koala_ordinary_sharp_projection_gate (y t yCut tCut u : ℕ)
    (hy : y ≤ 19) (ht : t ≤ 185) (hyt : y ≤ t)
    (hyCut : yCut ≤ 19) (htCut : tCut ≤ 185) (hu : u ≤ 131071) :
    flagMixed (ordinaryFlag y t) (cutFlag 1 u yCut tCut) unitZFlag < 2130706433 := by
  have hY : 1 + u * (2 * (yCut - 1)) ≤ 4718557 := by
    have h := Nat.mul_le_mul hu (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hyCut 1))
    omega
  have hT : 1 + u * (2 * (tCut - 1)) ≤ 48234129 := by
    have h := Nat.mul_le_mul hu (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right htCut 1))
    omega
  let dY := 1 + u * (2 * (yCut - 1))
  let dT := 1 + u * (2 * (tCut - 1))
  have hd : flagMixed (ordinaryFlag y t) (cutFlag 1 u yCut tCut) unitZFlag =
      (t - y) * dY + y * dY + (dT - dY) * y := by
    simp only [flagMixed, ordinaryFlag, cutFlag, unitZFlag, zero_mul, mul_zero, zero_add,
      add_zero, dY, dT]
    ring
  rw [hd, ← Nat.add_mul, Nat.sub_add_cancel hyt]
  have h₀ : t * dY ≤ 185 * 4718557 := Nat.mul_le_mul ht hY
  have h₁ : (dT - dY) * y ≤ 48234129 * 19 :=
    Nat.mul_le_mul ((Nat.sub_le dT dY).trans hT) hy
  exact (Nat.add_le_add h₀ h₁).trans_lt (by decide)

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem exists_regular_curve_budgets (p : ℕ) [CharP Ω p]
    (F G T : MvPolynomial (Fin 3) Ω) (left first : FlagDegree)
    (hdiv : G ∣ F) (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hR : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hGflag : PolynomialInFlag left G) (hTflag : PolynomialInFlag first T)
    (hchar : left.zOnly + left.yz + left.all < p)
    (hsharp : flagMixed left first unitZFlag < p) :
    ∃ B : PrimeFlagBudgetFamily
        (G := G) (T := T) (H := MvPolynomial.pderiv (1 : Fin 3) F) left first,
      ∀ C, 1 ≤ B.yzCost C := by
  classical
  let H := MvPolynomial.pderiv (1 : Fin 3) F
  have hYdegree : 0 < G.degreeOf 1 := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply hR
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro mem
    exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp mem) zero
  obtain ⟨g₀, g₁, g₂⟩ := RCN314.degree_bounds_of_polynomialInFlag hGflag
  have degrees : ∀ i : Fin 3, G.degreeOf i < p := by
    intro i
    fin_cases i
    · exact g₀.trans_lt (by omega)
    · exact g₁.trans_lt (by omega)
    · exact g₂.trans_lt hchar
  have seed_transcendental (C : RegularComponent Ω G T H) :
      Transcendental Ω (coordinate Ω C.1 0) ∨ Transcendental Ω (coordinate Ω C.1 2) := by
    have FC : F ∈ C.1 := by
      obtain ⟨Q, hQ⟩ := hdiv
      rw [hQ]
      exact C.1.mul_mem_right Q (regularComponent_G_mem Ω G T H C)
    exact y_or_z_transcendental_of_regular_polynomial C.1 F FC
      (regularComponent_H_not_mem Ω G T H C) (regularComponent_ne_point Ω G T H C)
  let hZ : ∀ C : RegularComponent Ω G T H, LiteralProjectionGate C 2 := by
    intro C ht
    exact BoundaryTailSharpGate.finite_separable_z_of_flag_gate C.1 ht p G T hG
      (regularComponent_G_mem Ω G T H C) (regularComponent_T_mem Ω G T H C)
      hproper hR left first hGflag hTflag hsharp
  let choice : ∀ C : RegularComponent Ω G T H, ∃ B : SeparableLiteralCoordinate C.1,
      B.index = 0 ∨ B.index = 2 := by
    intro C
    by_cases hz : Transcendental Ω (coordinate Ω C.1 2)
    · exact ⟨⟨2, hz, (hZ C hz).1, (hZ C hz).2⟩, Or.inr rfl⟩
    · have hy := (seed_transcendental C).resolve_right hz
      have hsep := finite_separable_at_y_of_z_algebraic C.1 p G hG
        (regularComponent_G_mem Ω G T H C) hYdegree degrees hy (not_not.mp hz)
      exact ⟨⟨0, hy, hsep.1, hsep.2⟩, Or.inl rfl⟩
  let base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1 :=
    fun C => (choice C).choose
  have active (C : RegularComponent Ω G T H) :
      D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0) ≠ 0 ∨
      D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2) ≠ 0 := by
    have h := base_differential_ne_zero (base C)
    rcases (choice C).choose_spec with index | index
    · exact Or.inl (by simpa only [base, index] using h)
    · exact Or.inr (by simpa only [base, index] using h)
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionDataActive base active hR
  let P := adaptiveUnitProjectionFamilyYZ_of_active_nested left first base active hZ hR D
    hG hproper ((support_subset_flagSupport_iff left G).mpr hGflag)
      ((support_subset_flagSupport_iff first T).mpr hTflag)
  refine ⟨P.family.toPrimeFlagBudgetFamily, ?_⟩
  intro C
  change 1 ≤ coordinateDegree Ω (CoordinateField Ω C.1) (P.family.yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  rw [P.yzValue C]
  exact D.uTranscendental C

omit [IsAlgClosed Ω] in
theorem curve_cut_seed_bound {Seed : Type*} {G T H : MvPolynomial (Fin 3) Ω}
    {left first : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) left first)
    (C : RegularComponent Ω G T H) (seeds : Finset Seed) (v : Seed → Fin 3 → Ω)
    (A : MvPolynomial (Fin 3) Ω) (flag : FlagDegree)
    (hflag : PolynomialInFlag flag A) (hproper : A ∉ C.1)
    (hinj : Set.InjOn v seeds)
    (hon : ∀ g ∈ seeds, C.1 ≤ RingHom.ker (MvPolynomial.aeval (v g)).toRingHom)
    (hzero : ∀ g ∈ seeds, MvPolynomial.aeval (v g) A = 0) :
    seeds.card ≤ B.weightedCost flag C := by
  classical
  let points := seeds.image v
  have card_eq : points.card = seeds.card := Finset.card_image_of_injOn hinj
  rw [← card_eq]
  apply (B.primeBudget C).zero_le flag A hflag hproper points
  · intro point hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact hon g hg
  · intro point hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact hzero g hg

end

end ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence
