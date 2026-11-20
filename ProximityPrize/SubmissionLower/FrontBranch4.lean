import ProximityPrize.SubmissionLower.UpperBranch2
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace P1_4
noncomputable section
open P1 MvPolynomial
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V
abbrev Puncture := K1_11.Puncture
open K1_11 (sourceWeights scalarWeightY scalarWeightYS scalarWeightT
  contactLift contactWeight contactShift polynomialView scalarImages)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | w22 | w12 | w21 | w13 | w23 | w31 | w32 | w33
def Bank.dS : Bank → ℕ
  | .w22 | .w21 | .w23 => 2
  | .w12 | .w13 => 1
  | .w31 | .w32 | .w33 => 3
def Bank.dT : Bank → ℕ
  | .w22 | .w12 | .w32 => 2
  | .w21 | .w31 => 1
  | .w13 | .w23 | .w33 => 3
def Bank.s : Bank → ℕ
  | .w12 => 16
  | .w13 => 8
  | .w21 => 10
  | .w22 => 11
  | .w23 => 8
  | .w31 => 7
  | .w32 => 6
  | .w33 => 6
def Bank.t : Bank → ℕ
  | .w12 => 10
  | .w13 => 7
  | .w21 => 16
  | .w22 => 10
  | .w23 => 6
  | .w31 => 8
  | .w32 => 8
  | .w33 => 8
def Bank.heightFloor : Bank → ℕ
  | .w22 | .w12 | .w21 => 24436
  | _ => 32582
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
def Bank.chartRate (b : Bank) : ℚ := (43691 / 16291 : ℚ) * b.M
def Bank.chartFee (b : Bank) : ℚ := b.E * b.chartRate ^ 2
abbrev weightedCutoff : ℕ := 4 * agreement - 1
abbrev nodeCut := K1_11.nodeCut
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
abbrev scalarWeightTotal := K1_11.scalarWeightTotal
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end P1_4
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P1_4
open P1 Finset
open K1_11 (V J)
open private countRow gradeRow count grade contactRow V_affine rational_fee from ProximityPrize.SubmissionLower.PortFrontA
private theorem surplus_of_stats (h H e N lo s t ds dt c g c' g' j : ℕ)
    (hlo : lo ≤ h) (hmax : h ≤ 33327) (hH : H + e = h) (hN : N + e = 262144)
    (hc : count 5 s t = c) (hg : grade 5 s t = g)
    (hc' : count 4 (s-ds) (t-dt) = c') (hg' : grade 4 (s-ds) (t-dt) = g')
    (hj : J 4 s t - J 3 (s-ds) (t-dt) = j) (hgain : c' ≤ j)
    (hmargin : 262144 * j + (588705 - lo) * c' + 131071 * g <
      719776 * c + 131071 * g') :
    N * (J 4 s t - J 3 (s-ds) (t-dt)) + V (719775 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 719775 131071 5 s t := by
  have hv := V_affine 719775 131071 5 s t (by decide)
  have hv' := V_affine (719775 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc, hg] at hv
  rw [hc', hg'] at hv'
  have hw : 719775 - 131071 - H + 1 ≤ (588705 - lo) + e := by omega
  have hm : N * j + (719775 - 131071 - H + 1) * c' ≤
      262144 * j + (588705 - lo) * c' := by
    calc
      _ ≤ N * j + ((588705 - lo) + e) * c' :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) _
      _ = N * j + e * c' + (588705 - lo) * c' := by ring
      _ ≤ N * j + e * j + (588705 - lo) * c' :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hgain) _) _
      _ = _ := by rw [← Nat.add_mul, hN]
  rw [hj]
  omega
private theorem dims_5_16_10 : count 5 16 10 = 2982 ∧ grade 5 16 10 = 9324 := by
  constructor
  · have r0 : countRow 5 16 10 0 = 867 := by decide
    have r1 : countRow 5 16 10 1 = 720 := by decide
    have r2 : countRow 5 16 10 2 = 570 := by decide
    have r3 : countRow 5 16 10 3 = 420 := by decide
    have r4 : countRow 5 16 10 4 = 273 := by decide
    have r5 : countRow 5 16 10 5 = 132 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 16 10 i) = 9324
    have r0 : gradeRow 5 16 10 0 = 1870 := by decide
    have r1 : gradeRow 5 16 10 1 = 2000 := by decide
    have r2 : gradeRow 5 16 10 2 = 1920 := by decide
    have r3 : gradeRow 5 16 10 3 = 1652 := by decide
    have r4 : gradeRow 5 16 10 4 = 1222 := by decide
    have r5 : gradeRow 5 16 10 5 = 660 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_15_8 : count 4 15 8 = 1675 ∧ grade 4 15 8 = 4189 := by
  constructor
  · have r0 : countRow 4 15 8 0 = 560 := by decide
    have r1 : countRow 4 15 8 1 = 450 := by decide
    have r2 : countRow 4 15 8 2 = 336 := by decide
    have r3 : countRow 4 15 8 3 = 221 := by decide
    have r4 : countRow 4 15 8 4 = 108 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 15 8 i) = 4189
    have r0 : gradeRow 4 15 8 0 = 960 := by decide
    have r1 : gradeRow 4 15 8 1 = 1050 := by decide
    have r2 : gradeRow 4 15 8 2 = 980 := by decide
    have r3 : gradeRow 4 15 8 3 = 767 := by decide
    have r4 : gradeRow 4 15 8 4 = 432 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_16_10 : J 4 16 10 = 3326 := by
  change (∑ i ∈ range 4, contactRow 4 16 10 i) = 3326
  have r0 : contactRow 4 16 10 0 = 1700 := by decide
  have r1 : contactRow 4 16 10 1 = 992 := by decide
  have r2 : contactRow 4 16 10 2 = 480 := by decide
  have r3 : contactRow 4 16 10 3 = 154 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_15_8 : J 3 15 8 = 1316 := by
  change (∑ i ∈ range 3, contactRow 3 15 8 i) = 1316
  have r0 : contactRow 3 15 8 0 = 800 := by decide
  have r1 : contactRow 3 15 8 1 = 390 := by decide
  have r2 : contactRow 3 15 8 2 = 126 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_8_7 : count 5 8 7 = 952 ∧ grade 5 8 7 = 2814 := by
  constructor
  · have r0 : countRow 5 8 7 0 = 297 := by decide
    have r1 : countRow 5 8 7 1 = 240 := by decide
    have r2 : countRow 5 8 7 2 = 182 := by decide
    have r3 : countRow 5 8 7 3 = 126 := by decide
    have r4 : countRow 5 8 7 4 = 75 := by decide
    have r5 : countRow 5 8 7 5 = 32 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 8 7 i) = 2814
    have r0 : gradeRow 5 8 7 0 = 585 := by decide
    have r1 : gradeRow 5 8 7 1 = 640 := by decide
    have r2 : gradeRow 5 8 7 2 = 602 := by decide
    have r3 : gradeRow 5 8 7 3 = 492 := by decide
    have r4 : gradeRow 5 8 7 4 = 335 := by decide
    have r5 : gradeRow 5 8 7 5 = 160 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_7_4 : count 4 7 4 = 355 ∧ grade 4 7 4 = 809 := by
  constructor
  · have r0 : countRow 4 7 4 0 = 120 := by decide
    have r1 : countRow 4 7 4 1 = 98 := by decide
    have r2 : countRow 4 7 4 2 = 72 := by decide
    have r3 : countRow 4 7 4 3 = 45 := by decide
    have r4 : countRow 4 7 4 4 = 20 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 7 4 i) = 809
    have r0 : gradeRow 4 7 4 0 = 160 := by decide
    have r1 : gradeRow 4 7 4 1 = 210 := by decide
    have r2 : gradeRow 4 7 4 2 = 204 := by decide
    have r3 : gradeRow 4 7 4 3 = 155 := by decide
    have r4 : gradeRow 4 7 4 4 = 80 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_8_7 : J 4 8 7 = 1191 := by
  change (∑ i ∈ range 4, contactRow 4 8 7 i) = 1191
  have r0 : contactRow 4 8 7 0 = 630 := by decide
  have r1 : contactRow 4 8 7 1 = 352 := by decide
  have r2 : contactRow 4 8 7 2 = 161 := by decide
  have r3 : contactRow 4 8 7 3 = 48 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_7_4 : J 3 7 4 = 336 := by
  change (∑ i ∈ range 3, contactRow 3 7 4 i) = 336
  have r0 : contactRow 3 7 4 0 = 208 := by decide
  have r1 : contactRow 3 7 4 1 = 98 := by decide
  have r2 : contactRow 3 7 4 2 = 30 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_10_16 : count 5 10 16 = 2982 ∧ grade 5 10 16 = 9324 := by
  constructor
  · have r0 : countRow 5 10 16 0 = 957 := by decide
    have r1 : countRow 5 10 16 1 = 750 := by decide
    have r2 : countRow 5 10 16 2 = 558 := by decide
    have r3 : countRow 5 10 16 3 = 384 := by decide
    have r4 : countRow 5 10 16 4 = 231 := by decide
    have r5 : countRow 5 10 16 5 = 102 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 10 16 i) = 9324
    have r0 : gradeRow 5 10 16 0 = 2200 := by decide
    have r1 : gradeRow 5 10 16 1 = 2150 := by decide
    have r2 : gradeRow 5 10 16 2 = 1908 := by decide
    have r3 : gradeRow 5 10 16 3 = 1520 := by decide
    have r4 : gradeRow 5 10 16 4 = 1036 := by decide
    have r5 : gradeRow 5 10 16 5 = 510 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_8_15 : count 4 8 15 = 1675 ∧ grade 4 8 15 = 4189 := by
  constructor
  · have r0 : countRow 4 8 15 0 = 630 := by decide
    have r1 : countRow 4 8 15 1 = 464 := by decide
    have r2 : countRow 4 8 15 2 = 315 := by decide
    have r3 : countRow 4 8 15 3 = 186 := by decide
    have r4 : countRow 4 8 15 4 = 80 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 8 15 i) = 4189
    have r0 : gradeRow 4 8 15 0 = 1170 := by decide
    have r1 : gradeRow 4 8 15 1 = 1120 := by decide
    have r2 : gradeRow 4 8 15 2 = 931 := by decide
    have r3 : gradeRow 4 8 15 3 = 648 := by decide
    have r4 : gradeRow 4 8 15 4 = 320 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_10_16 : J 4 10 16 = 3326 := by
  change (∑ i ∈ range 4, contactRow 4 10 16 i) = 3326
  have r0 : contactRow 4 10 16 0 = 1760 := by decide
  have r1 : contactRow 4 10 16 1 = 980 := by decide
  have r2 : contactRow 4 10 16 2 = 450 := by decide
  have r3 : contactRow 4 10 16 3 = 136 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_8_15 : J 3 8 15 = 1316 := by
  change (∑ i ∈ range 3, contactRow 3 8 15 i) = 1316
  have r0 : contactRow 3 8 15 0 = 828 := by decide
  have r1 : contactRow 3 8 15 1 = 376 := by decide
  have r2 : contactRow 3 8 15 2 = 112 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_11_10 : count 5 11 10 = 2002 ∧ grade 5 11 10 = 6174 := by
  constructor
  · have r0 : countRow 5 11 10 0 = 612 := by decide
    have r1 : countRow 5 11 10 1 = 495 := by decide
    have r2 : countRow 5 11 10 2 = 380 := by decide
    have r3 : countRow 5 11 10 3 = 270 := by decide
    have r4 : countRow 5 11 10 4 = 168 := by decide
    have r5 : countRow 5 11 10 5 = 77 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 11 10 i) = 6174
    have r0 : gradeRow 5 11 10 0 = 1320 := by decide
    have r1 : gradeRow 5 11 10 1 = 1375 := by decide
    have r2 : gradeRow 5 11 10 2 = 1280 := by decide
    have r3 : gradeRow 5 11 10 3 = 1062 := by decide
    have r4 : gradeRow 5 11 10 4 = 752 := by decide
    have r5 : gradeRow 5 11 10 5 = 385 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_9_8 : count 4 9 8 = 985 ∧ grade 4 9 8 = 2419 := by
  constructor
  · have r0 : countRow 4 9 8 0 = 350 := by decide
    have r1 : countRow 4 9 8 1 = 270 := by decide
    have r2 : countRow 4 9 8 2 = 192 := by decide
    have r3 : countRow 4 9 8 3 = 119 := by decide
    have r4 : countRow 4 9 8 4 = 54 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 9 8 i) = 2419
    have r0 : gradeRow 4 9 8 0 = 600 := by decide
    have r1 : gradeRow 4 9 8 1 = 630 := by decide
    have r2 : gradeRow 4 9 8 2 = 560 := by decide
    have r3 : gradeRow 4 9 8 3 = 413 := by decide
    have r4 : gradeRow 4 9 8 4 = 216 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_11_10 : J 4 11 10 = 2301 := by
  change (∑ i ∈ range 4, contactRow 4 11 10 i) = 2301
  have r0 : contactRow 4 11 10 0 = 1200 := by decide
  have r1 : contactRow 4 11 10 1 = 682 := by decide
  have r2 : contactRow 4 11 10 2 = 320 := by decide
  have r3 : contactRow 4 11 10 3 = 99 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_9_8 : J 3 9 8 = 806 := by
  change (∑ i ∈ range 3, contactRow 3 9 8 i) = 806
  have r0 : contactRow 3 9 8 0 = 500 := by decide
  have r1 : contactRow 3 9 8 1 = 234 := by decide
  have r2 : contactRow 3 9 8 2 = 72 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_8_6 : count 5 8 6 = 798 ∧ grade 5 8 6 = 2324 := by
  constructor
  · have r0 : countRow 5 8 6 0 = 243 := by decide
    have r1 : countRow 5 8 6 1 = 200 := by decide
    have r2 : countRow 5 8 6 2 = 154 := by decide
    have r3 : countRow 5 8 6 3 = 108 := by decide
    have r4 : countRow 5 8 6 4 = 65 := by decide
    have r5 : countRow 5 8 6 5 = 28 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 8 6 i) = 2324
    have r0 : gradeRow 5 8 6 0 = 450 := by decide
    have r1 : gradeRow 5 8 6 1 = 520 := by decide
    have r2 : gradeRow 5 8 6 2 = 504 := by decide
    have r3 : gradeRow 5 8 6 3 = 420 := by decide
    have r4 : gradeRow 5 8 6 4 = 290 := by decide
    have r5 : gradeRow 5 8 6 5 = 140 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_6_3 : count 4 6 3 = 215 ∧ grade 4 6 3 = 459 := by
  constructor
  · have r0 : countRow 4 6 3 0 = 70 := by decide
    have r1 : countRow 4 6 3 1 = 60 := by decide
    have r2 : countRow 4 6 3 2 = 45 := by decide
    have r3 : countRow 4 6 3 3 = 28 := by decide
    have r4 : countRow 4 6 3 4 = 12 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 6 3 i) = 459
    have r0 : gradeRow 4 6 3 0 = 70 := by decide
    have r1 : gradeRow 4 6 3 1 = 120 := by decide
    have r2 : gradeRow 4 6 3 2 = 125 := by decide
    have r3 : gradeRow 4 6 3 3 = 96 := by decide
    have r4 : gradeRow 4 6 3 4 = 48 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_8_6 : J 4 8 6 = 1026 := by
  change (∑ i ∈ range 4, contactRow 4 8 6 i) = 1026
  have r0 : contactRow 4 8 6 0 = 540 := by decide
  have r1 : contactRow 4 8 6 1 = 304 := by decide
  have r2 : contactRow 4 8 6 2 = 140 := by decide
  have r3 : contactRow 4 8 6 3 = 42 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_6_3 : J 3 6 3 = 226 := by
  change (∑ i ∈ range 3, contactRow 3 6 3 i) = 226
  have r0 : contactRow 3 6 3 0 = 140 := by decide
  have r1 : contactRow 3 6 3 1 = 66 := by decide
  have r2 : contactRow 3 6 3 2 = 20 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_7_8 : count 5 7 8 = 952 ∧ grade 5 7 8 = 2814 := by
  constructor
  · have r0 : countRow 5 7 8 0 = 312 := by decide
    have r1 : countRow 5 7 8 1 = 245 := by decide
    have r2 : countRow 5 7 8 2 = 180 := by decide
    have r3 : countRow 5 7 8 3 = 120 := by decide
    have r4 : countRow 5 7 8 4 = 68 := by decide
    have r5 : countRow 5 7 8 5 = 27 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 7 8 i) = 2814
    have r0 : gradeRow 5 7 8 0 = 640 := by decide
    have r1 : gradeRow 5 7 8 1 = 665 := by decide
    have r2 : gradeRow 5 7 8 2 = 600 := by decide
    have r3 : gradeRow 5 7 8 3 = 470 := by decide
    have r4 : gradeRow 5 7 8 4 = 304 := by decide
    have r5 : gradeRow 5 7 8 5 = 135 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_4_7 : count 4 4 7 = 355 ∧ grade 4 4 7 = 809 := by
  constructor
  · have r0 : countRow 4 4 7 0 = 150 := by decide
    have r1 : countRow 4 4 7 1 = 104 := by decide
    have r2 : countRow 4 4 7 2 = 63 := by decide
    have r3 : countRow 4 4 7 3 = 30 := by decide
    have r4 : countRow 4 4 7 4 = 8 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 4 7 i) = 809
    have r0 : gradeRow 4 4 7 0 = 250 := by decide
    have r1 : gradeRow 4 4 7 1 = 240 := by decide
    have r2 : gradeRow 4 4 7 2 = 183 := by decide
    have r3 : gradeRow 4 4 7 3 = 104 := by decide
    have r4 : gradeRow 4 4 7 4 = 32 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_7_8 : J 4 7 8 = 1191 := by
  change (∑ i ∈ range 4, contactRow 4 7 8 i) = 1191
  have r0 : contactRow 4 7 8 0 = 640 := by decide
  have r1 : contactRow 4 7 8 1 = 350 := by decide
  have r2 : contactRow 4 7 8 2 = 156 := by decide
  have r3 : contactRow 4 7 8 3 = 45 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_4_7 : J 3 4 7 = 336 := by
  change (∑ i ∈ range 3, contactRow 3 4 7 i) = 336
  have r0 : contactRow 3 4 7 0 = 220 := by decide
  have r1 : contactRow 3 4 7 1 = 92 := by decide
  have r2 : contactRow 3 4 7 2 = 24 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_5_6_8 : count 5 6 8 = 798 ∧ grade 5 6 8 = 2324 := by
  constructor
  · have r0 : countRow 5 6 8 0 = 273 := by decide
    have r1 : countRow 5 6 8 1 = 210 := by decide
    have r2 : countRow 5 6 8 2 = 150 := by decide
    have r3 : countRow 5 6 8 3 = 96 := by decide
    have r4 : countRow 5 6 8 4 = 51 := by decide
    have r5 : countRow 5 6 8 5 = 18 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 6 8 i) = 2324
    have r0 : gradeRow 5 6 8 0 = 560 := by decide
    have r1 : gradeRow 5 6 8 1 = 570 := by decide
    have r2 : gradeRow 5 6 8 2 = 500 := by decide
    have r3 : gradeRow 5 6 8 3 = 376 := by decide
    have r4 : gradeRow 5 6 8 4 = 228 := by decide
    have r5 : gradeRow 5 6 8 5 = 90 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_3_6 : count 4 3 6 = 215 ∧ grade 4 3 6 = 459 := by
  constructor
  · have r0 : countRow 4 3 6 0 = 100 := by decide
    have r1 : countRow 4 3 6 1 = 66 := by decide
    have r2 : countRow 4 3 6 2 = 36 := by decide
    have r3 : countRow 4 3 6 3 = 13 := by decide
    have r4 : countRow 4 3 6 4 = 0 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 3 6 i) = 459
    have r0 : gradeRow 4 3 6 0 = 160 := by decide
    have r1 : gradeRow 4 3 6 1 = 150 := by decide
    have r2 : gradeRow 4 3 6 2 = 104 := by decide
    have r3 : gradeRow 4 3 6 3 = 45 := by decide
    have r4 : gradeRow 4 3 6 4 = 0 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_6_8 : J 4 6 8 = 1026 := by
  change (∑ i ∈ range 4, contactRow 4 6 8 i) = 1026
  have r0 : contactRow 4 6 8 0 = 560 := by decide
  have r1 : contactRow 4 6 8 1 = 300 := by decide
  have r2 : contactRow 4 6 8 2 = 130 := by decide
  have r3 : contactRow 4 6 8 3 = 36 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_3_6 : J 3 3 6 = 226 := by
  change (∑ i ∈ range 3, contactRow 3 3 6 i) = 226
  have r0 : contactRow 3 3 6 0 = 152 := by decide
  have r1 : contactRow 3 3 6 1 = 60 := by decide
  have r2 : contactRow 3 3 6 2 = 14 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem dims_4_3_5 : count 4 3 5 = 175 ∧ grade 4 3 5 = 364 := by
  constructor
  · have r0 : countRow 4 3 5 0 = 80 := by decide
    have r1 : countRow 4 3 5 1 = 54 := by decide
    have r2 : countRow 4 3 5 2 = 30 := by decide
    have r3 : countRow 4 3 5 3 = 11 := by decide
    have r4 : countRow 4 3 5 4 = 0 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 3 5 i) = 364
    have r0 : gradeRow 4 3 5 0 = 120 := by decide
    have r1 : gradeRow 4 3 5 1 = 120 := by decide
    have r2 : gradeRow 4 3 5 2 = 86 := by decide
    have r3 : gradeRow 4 3 5 3 = 38 := by decide
    have r4 : gradeRow 4 3 5 4 = 0 := by decide
    simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_3_3_5 : J 3 3 5 = 191 := by
  change (∑ i ∈ range 3, contactRow 3 3 5 i) = 191
  have r0 : contactRow 3 3 5 0 = 128 := by decide
  have r1 : contactRow 3 3 5 1 = 51 := by decide
  have r2 : contactRow 3 3 5 2 = 12 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
theorem bank_surplus (b : Bank) (h H e N : ℕ) (hlo : b.heightFloor ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  cases b with
  | w12 =>
    exact surplus_of_stats h H e N 24436 16 10 1 2 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_16_10.1 dims_5_16_10.2 dims_4_15_8.1 dims_4_15_8.2
      (by rw [jets_4_16_10, jets_3_15_8]) (by decide) (by decide)
  | w13 =>
    exact surplus_of_stats h H e N 32582 8 7 1 3 952 2814 355 809 855
      hlo hmax hH hN dims_5_8_7.1 dims_5_8_7.2 dims_4_7_4.1 dims_4_7_4.2
      (by rw [jets_4_8_7, jets_3_7_4]) (by decide) (by decide)
  | w21 =>
    exact surplus_of_stats h H e N 24436 10 16 2 1 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_10_16.1 dims_5_10_16.2 dims_4_8_15.1 dims_4_8_15.2
      (by rw [jets_4_10_16, jets_3_8_15]) (by decide) (by decide)
  | w22 =>
    exact surplus_of_stats h H e N 24436 11 10 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN dims_5_11_10.1 dims_5_11_10.2 dims_4_9_8.1 dims_4_9_8.2
      (by rw [jets_4_11_10, jets_3_9_8]) (by decide) (by decide)
  | w23 =>
    exact surplus_of_stats h H e N 32582 8 6 2 3 798 2324 215 459 800
      hlo hmax hH hN dims_5_8_6.1 dims_5_8_6.2 dims_4_6_3.1 dims_4_6_3.2
      (by rw [jets_4_8_6, jets_3_6_3]) (by decide) (by decide)
  | w31 =>
    exact surplus_of_stats h H e N 32582 7 8 3 1 952 2814 355 809 855
      hlo hmax hH hN dims_5_7_8.1 dims_5_7_8.2 dims_4_4_7.1 dims_4_4_7.2
      (by rw [jets_4_7_8, jets_3_4_7]) (by decide) (by decide)
  | w32 =>
    exact surplus_of_stats h H e N 32582 6 8 3 2 798 2324 215 459 800
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_6.1 dims_4_3_6.2
      (by rw [jets_4_6_8, jets_3_3_6]) (by decide) (by decide)
  | w33 =>
    exact surplus_of_stats h H e N 32582 6 8 3 3 798 2324 175 364 835
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_5.1 dims_4_3_5.2
      (by rw [jets_4_6_8, jets_3_3_5]) (by decide) (by decide)
def Bank.regularCap : Bank → ℕ
  | .w12 => 108985118822435430
  | .w13 => 62351371041429575
  | .w21 => 108985120953141862
  | .w22 => 108985118822435430
  | .w23 => 91503024555190792
  | .w31 => 62351351865071687
  | .w32 => 91503018163071496
  | .w33 => 139174733275325973
theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * b.chartFee ≤ b.regularCap := by
  cases b with
  | w12 => exact rational_fee 36 9174936 31960596516 108985118822435430 43691 16291 (by decide) (by decide)
  | w13 => exact rational_fee 30 7602090 36222009374 62351371041429575 43691 16291 (by decide) (by decide)
  | w21 => exact rational_fee 36 9174936 34091302948 108985120953141862 43691 16291 (by decide) (by decide)
  | w22 => exact rational_fee 36 9174936 31960596516 108985118822435430 43691 16291 (by decide) (by decide)
  | w23 => exact rational_fee 34 8650654 34091302946 91503024555190792 43691 16291 (by decide) (by decide)
  | w31 => exact rational_fee 30 7602090 17045651486 62351351865071687 43691 16291 (by decide) (by decide)
  | w32 => exact rational_fee 34 8650654 27699183650 91503018163071496 43691 16291 (by decide) (by decide)
  | w33 => exact rational_fee 39 9961359 38352715815 139174733275325973 43691 16291 (by decide) (by decide)
theorem bank_cap (b : Bank) : b.regularCap ≤ 139174733275325973 := by
  cases b <;> decide
theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ b.chartRate := by
  have hm : (262144 : ℕ) ≤ b.M := by cases b <;> decide
  have hr : (1 : ℚ) ≤ 43691 / 16291 := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 16291)).mpr
    rw [one_mul]
    exact_mod_cast (show (16291 : ℕ) ≤ 43691 by decide)
  exact (by exact_mod_cast hm : (262144 : ℚ) ≤ b.M).trans
    (by simpa only [one_mul, Bank.chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℚ) ≤ b.M))
end P1_4
end
