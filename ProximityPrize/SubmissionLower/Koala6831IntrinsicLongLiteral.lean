import ProximityPrize.SubmissionLower.Koala6831IntrinsicSeedProjections
import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Classical
open MvPolynomial RCN002 RCN005 RCN011 RCN022 RCN093 RCN112 RCN113 RCN117 RCN120
  RCN125 RCN135 RCN136 RCN264 RCN267 RCN341

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {Ω : Type} [Field Ω]

@[simp] theorem flagAlgHom_zero_apply (A : MvPolynomial (Fin 3) Ω) :
    flagAlgHom (0 : Ω) 0 0 A = A := by
  have heq : flagAlgHom (0 : Ω) 0 0 = AlgHom.id Ω (MvPolynomial (Fin 3) Ω) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [flagImage, Pi.single_apply]
  exact AlgHom.congr_fun heq A

@[simp] theorem flagEvaluation_zero_X (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (i : Fin 3) :
    flagEvaluation Ω P 0 0 0 (MvPolynomial.X i) = coordinate Ω P i := by
  fin_cases i <;> simp [affineU, affineV]

@[simp] theorem flagPlaneMap_zero_apply (order : Fin 3 ≃ Fin 3) (A : MvPolynomial (Fin 3) Ω) :
    flagPlaneMap Ω 0 0 0 order A = planeMap Ω order A := by
  simp [flagPlaneMap]

theorem flagPlaneResultant_zero_eq (order : Fin 3 ≃ Fin 3) (G T : MvPolynomial (Fin 3) Ω) :
    flagPlaneResultant (0 : Ω) 0 0 order G T =
      Polynomial.resultant (planeMap Ω order G) (planeMap Ω order T)
        (planeMap Ω order G).natDegree (planeMap Ω order T).natDegree := by
  unfold flagPlaneResultant
  rw [flagAlgHom_zero_apply G, flagAlgHom_zero_apply T]

theorem flagBaseAlgebra_zero_eq (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω (flagEvaluation Ω P 0 0 0 (MvPolynomial.X (order 0))))
    (hs : Transcendental Ω (coordinate Ω P (order 0))) :
    flagBaseAlgebra Ω P 0 0 0 order ht = rationalBaseAlgebra Ω P (order 0) hs := by
  have hcongr (x y : CoordinateField Ω P) (hx : Transcendental Ω x)
      (hy : Transcendental Ω y) (hxy : x = y) :
      elementEmbedding Ω (CoordinateField Ω P) x hx =
        elementEmbedding Ω (CoordinateField Ω P) y hy := by
    subst y
    rfl
  unfold flagBaseAlgebra
  rw [hcongr _ _ ht hs (flagEvaluation_zero_X P (order 0))]
  rfl

theorem zero_flag_generators (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω (flagEvaluation Ω P 0 0 0 (MvPolynomial.X (order 0)))) :
    letI : Algebra (RatFunc Ω) (CoordinateField Ω P) := flagBaseAlgebra Ω P 0 0 0 order ht
    IntermediateField.adjoin (RatFunc Ω)
      ({flagEvaluation Ω P 0 0 0 (MvPolynomial.X (order 2)),
        flagEvaluation Ω P 0 0 0 (MvPolynomial.X (order 1))} : Set (CoordinateField Ω P)) = ⊤ := by
  have hs : Transcendental Ω (coordinate Ω P (order 0)) := by simpa using ht
  have hcover (i : Fin 3) : i = order 0 ∨ i = order 2 ∨ i = order 1 := by
    obtain ⟨j, rfl⟩ := order.surjective i
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  rw [flagBaseAlgebra_zero_eq P order ht hs, flagEvaluation_zero_X, flagEvaluation_zero_X]
  exact adjoin_two_coordinates_over_ratFunc_eq_top Ω P (order 0) (order 2) (order 1) hs hcover

private def seedSlice (a b : Ω) : MvPolynomial (Fin 3) Ω →ₐ[Ω] Polynomial Ω :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C a, Polynomial.C b]

private theorem derivative_seedSlice (a b : Ω) (F : MvPolynomial (Fin 3) Ω) :
    (seedSlice a b F).derivative = seedSlice a b (MvPolynomial.pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [seedSlice]
  | add F G hF hG => simp [Polynomial.derivative_add, hF, hG]
  | mul_X F i hF =>
    rw [map_mul, Polynomial.derivative_mul, hF, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    fin_cases i <;> simp [seedSlice, MvPolynomial.pderiv_X]

theorem seed_transcendental_of_separant [IsAlgClosed Ω]
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime] (G : MvPolynomial (Fin 3) Ω)
    (hG : G ∈ P) (hreg : MvPolynomial.pderiv 0 G ∉ P)
    (hnonpoint : ∀ v : Fin 3 → Ω, P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
    Transcendental Ω (coordinate Ω P 1) ∨ Transcendental Ω (coordinate Ω P 2) := by
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  have ha' : IsAlgebraic Ω (coordinate Ω P 1) := not_not.mp ha
  have hb' : IsAlgebraic Ω (coordinate Ω P 2) := not_not.mp hb
  obtain ⟨a, heqa⟩ := coordinate_eq_scalar_of_isAlgebraic Ω P 1 ha'
  obtain ⟨b, heqb⟩ := coordinate_eq_scalar_of_isAlgebraic Ω P 2 hb'
  have heval : (Polynomial.aeval (coordinate Ω P 0)).comp (seedSlice a b) =
      MvPolynomial.aeval (coordinate Ω P) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [seedSlice, heqa, heqb]
  have hzero : MvPolynomial.aeval (coordinate Ω P) G = 0 := by
    change G ∈ RingHom.ker (MvPolynomial.aeval (coordinate Ω P)).toRingHom
    simpa only [aeval_coordinate_ker] using hG
  have hnonzero : MvPolynomial.aeval (coordinate Ω P) (MvPolynomial.pderiv 0 G) ≠ 0 := by
    intro hz
    apply hreg
    rw [← aeval_coordinate_ker Ω P]
    exact hz
  have hQ : seedSlice a b G ≠ 0 := by
    intro hz
    have hd := derivative_seedSlice a b G
    rw [hz, Polynomial.derivative_zero] at hd
    apply hnonzero
    rw [← heval, AlgHom.comp_apply, ← hd, map_zero]
  have hY : IsAlgebraic Ω (coordinate Ω P 0) := by
    refine ⟨_, hQ, ?_⟩
    exact (congrArg (fun f : MvPolynomial (Fin 3) Ω →ₐ[Ω] CoordinateField Ω P => f G)
      heval).trans hzero
  have hall : ∀ i : Fin 3, IsAlgebraic Ω (coordinate Ω P i) := by
    intro i
    fin_cases i
    · exact hY
    · exact ha'
    · exact hb'
  obtain ⟨v, hv⟩ := eq_point_kernel_of_coordinates_algebraic Ω P hall
  exact hnonpoint v hv

abbrev longSeedOrder (useZ₁ : Bool) : Fin 3 ≃ Fin 3 :=
  if useZ₁ then seedOneOrder else seedZeroOrder

theorem longSeedOrder_outer (useZ₁ : Bool) : longSeedOrder useZ₁ 1 = 0 := by
  cases useZ₁ <;> decide

structure LongLiteralSeedCaps (G T : MvPolynomial (Fin 3) Ω) : Prop where
  Gy : G.degreeOf 0 ≤ 22
  Ty : T.degreeOf 0 ≤ 5505004
  Gz : G.degreeOf 2 ≤ 162
  Tz : T.degreeOf 2 ≤ 42467166
  Gt : ∀ d ∈ G.support, d 0 + d 1 ≤ 200
  Tt : ∀ d ∈ T.support, d 0 + d 1 ≤ 52166458

variable {K : Type} [Field K]

local notation "L" => GenericField K
local notation "φ" => polynomialEmbedding K

abbrev LongTailRegularComponent (F : Carrier K) (w : ℕ) (G : MvPolynomial (Fin 3) L) :=
  RegularComponent L G (surfaceMap φ (tailNumerator F w)) (surfaceMap φ (implicitRegularity F))

variable (F : Carrier K) (w : ℕ) {G : MvPolynomial (Fin 3) (GenericField K)}

local notation "T" => surfaceMap φ (tailNumerator F w)
local notation "H" => surfaceMap φ (implicitRegularity F)

theorem long_regular_pderiv_Y_not_mem (hdiv : G ∣ surfaceMap φ F)
    (C : LongTailRegularComponent F w G) : MvPolynomial.pderiv 0 G ∉ C.1 := by
  intro hd
  apply regularComponent_H_not_mem L G T H C
  obtain ⟨Q, hQ⟩ := hdiv
  have hG := regularComponent_G_mem L G T H C
  have hH : H = MvPolynomial.pderiv 0 (surfaceMap φ F) :=
    (surfaceMap_pderiv φ F 0).symm
  let P : Ideal (MvPolynomial (Fin 3) L) := C.1
  change H ∈ P
  rw [hH, hQ, MvPolynomial.pderiv_mul]
  exact P.add_mem (P.mul_mem_right _ hd) (P.mul_mem_right _ hG)

theorem long_regular_seed_transcendental (hdiv : G ∣ surfaceMap φ F)
    (C : LongTailRegularComponent F w G) :
    Transcendental L (coordinate L C.1 1) ∨ Transcendental L (coordinate L C.1 2) :=
  seed_transcendental_of_separant C.1 G (regularComponent_G_mem L G T H C)
    (long_regular_pderiv_Y_not_mem F w hdiv C) (regularComponent_ne_point L G T H C)

theorem long_regular_seed_outer_positive (hdiv : G ∣ surfaceMap φ F)
    (C : LongTailRegularComponent F w G) (useZ₁ : Bool) :
    0 < (planeMap L (longSeedOrder useZ₁) G).natDegree := by
  apply planeMap_natDegree_pos_of_pderiv_ne_zero
  rw [longSeedOrder_outer]
  intro hz
  apply long_regular_pderiv_Y_not_mem F w hdiv C
  simpa only [hz] using C.1.zero_mem

variable [CharP (GenericField K) 2130706433]

theorem long_literal_projection_gate (hdiv : G ∣ surfaceMap φ F) (hG : Irreducible G)
    (hproper : ¬ G ∣ T) (caps : LongLiteralSeedCaps G T)
    (C : LongTailRegularComponent F w G) (useZ₁ : Bool)
    (ht : Transcendental L (coordinate L C.1 (longSeedOrder useZ₁ 0))) :
    letI : Algebra (RatFunc L) (CoordinateField L C.1) :=
      rationalBaseAlgebra L C.1 (longSeedOrder useZ₁ 0) ht
    FiniteDimensional (RatFunc L) (CoordinateField L C.1) ∧
      Algebra.IsSeparable (RatFunc L) (CoordinateField L C.1) :=
  long_tail_seed_projection_finite_separable useZ₁ C.1 G T hG
    (regularComponent_G_mem L G T H C) (regularComponent_T_mem L G T H C) hproper
    caps.Gy caps.Ty caps.Gz caps.Tz caps.Gt caps.Tt ht
    (long_regular_seed_outer_positive F w hdiv C useZ₁)

theorem long_zero_flag_projection_gate (hdiv : G ∣ surfaceMap φ F) (hG : Irreducible G)
    (hproper : ¬ G ∣ T) (caps : LongLiteralSeedCaps G T)
    (C : LongTailRegularComponent F w G) (useZ₁ : Bool)
    (ht : Transcendental L (flagEvaluation L C.1 0 0 0 (MvPolynomial.X (longSeedOrder useZ₁ 0)))) :
    letI : Algebra (RatFunc L) (CoordinateField L C.1) :=
      flagBaseAlgebra L C.1 0 0 0 (longSeedOrder useZ₁) ht
    FiniteDimensional (RatFunc L) (CoordinateField L C.1) ∧
      Algebra.IsSeparable (RatFunc L) (CoordinateField L C.1) := by
  have hs : Transcendental L (coordinate L C.1 (longSeedOrder useZ₁ 0)) := by simpa using ht
  rw [flagBaseAlgebra_zero_eq C.1 (longSeedOrder useZ₁) ht hs]
  exact long_literal_projection_gate F w hdiv hG hproper caps C useZ₁ hs

theorem exists_long_literal_seed_projection (hdiv : G ∣ surfaceMap φ F) (hG : Irreducible G)
    (hproper : ¬ G ∣ T) (caps : LongLiteralSeedCaps G T)
    (C : LongTailRegularComponent F w G) :
    ∃ B : SeparableLiteralCoordinate C.1, B.index = 1 ∨ B.index = 2 := by
  have hselect (useZ₁ : Bool) (ht : Transcendental L (coordinate L C.1 (longSeedOrder useZ₁ 0))) :
      ∃ B : SeparableLiteralCoordinate C.1, B.index = longSeedOrder useZ₁ 0 := by
    obtain ⟨hfin, hsep⟩ := long_literal_projection_gate F w hdiv hG hproper caps C useZ₁ ht
    exact ⟨⟨longSeedOrder useZ₁ 0, ht, hfin, hsep⟩, rfl⟩
  rcases long_regular_seed_transcendental F w hdiv C with hZ₀ | hZ₁
  · obtain ⟨B, hB⟩ := hselect false (by simpa only [show longSeedOrder false 0 = 1 by decide] using hZ₀)
    exact ⟨B, Or.inl (hB.trans seedZeroOrder_base)⟩
  · obtain ⟨B, hB⟩ := hselect true (by simpa only [show longSeedOrder true 0 = 2 by decide] using hZ₁)
    exact ⟨B, Or.inr (hB.trans seedOneOrder_base)⟩

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
