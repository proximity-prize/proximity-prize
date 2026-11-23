import ProximityPrize.SubmissionLower.R6960Low6960Prices
import ProximityPrize.SubmissionLower.PortLow5

set_option Elab.async false
set_option autoImplicit true
section
namespace Low6960Leading
noncomputable section
variable {top : Fin 15}
open P3 (K I)
open Low6960Prices (TrueWeightLE anchorCutoff taylorLength lowerWidth lowerIndex lowerTop)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily)
open K1_13 (Shape)
open scoped BigOperators Polynomial
abbrev lowBox : Shape := ⟨132, 55, 27⟩
abbrev graphBox (top : Fin 15) : Shape :=
  ⟨lowerWidth top, lowerIndex top + 1, (lowerIndex top + 1) / 2⟩
def liftedBox (top : Fin 15) (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowerIndex top + 2)
  ⟨1 + (L - 4) * lowerWidth top, j, min (1 + (L - 4) * (lowerTop top + 2)) (j / 2)⟩
def firstWidth (top : Fin 15) : ℕ :=
  max (lowerWidth top) ((2 * lowerTop top - 1) * lowerWidth top - lowerTop top ^ 2)
def firstIndex (top : Fin 15) : ℕ :=
  max (lowerIndex top) ((2 * lowerTop top - 1) * lowerIndex top - 2 * lowerTop top ^ 2)

structure FirstRow (top : Fin 15) (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ firstWidth top
  index : indexDegree q ≤ firstIndex top

structure FirstFactors (top : Fin 15) {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ firstWidth top
  index : (∑ i, indexDegree (f i)) ≤ firstIndex top

structure SecondFactors (top : Fin 15) {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ lowerWidth top
  index : (∑ i, indexDegree (f i)) ≤ lowerIndex top
  coordinate : (∑ i, (f i).degreeOf 2) ≤ lowerTop top
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)

-- Mixed volume coefficients in the support bounds of the contracted row.
def mixedCoefficients (top : Fin 15) : ℕ × ℕ × ℕ :=
  ![(85722834650025, 270797069607808, 27682368),
    (76886255935869, 258191826356328, 3701948197168),
    (68530216172895, 248888054360254, 27949186),
    (60654715361103, 235464115162342, 3737543852910),
    (53259753500493, 225377242608760, 28216004),
    (46345330591065, 211134607464416, 3773139508652),
    (39911446632819, 200264634353326, 28482822),
    (33958101625755, 185203303262550, 3808735164394),
    (28485295569873, 173550229593952, 28749640),
    (23493028465173, 157670202556744, 3844330820136),
    (18981300311655, 145234028330638, 29016458),
    (14950111109319, 128535305346998, 3879926475878),
    (11399460858165, 115316030563384, 29283276),
    (8329349558193, 97798611633312, 3915522131620),
    (5739777209403, 83796236292190, 29550094)] top

def mixedBudget (top : Fin 15) : ℕ :=
  let (b, j, r) := mixedCoefficients top
  b * lowerWidth top + j * lowerIndex top + r * lowerTop top
def invariantBudget (top : Fin 15) : ℕ :=
  lowerWidth top * (1 + (2 * (taylorLength + 1) - 7) * (lowerWidth top - 1))
abbrev firstExponent : ℕ := 2 * taylorLength - 5
abbrev firstChartTotal (top : Fin 15) : ℕ := 1 + firstExponent * (firstWidth top - 1)
abbrev firstChartTop (top : Fin 15) : ℕ :=
  min (firstChartTotal top) (firstExponent * (firstIndex top - 1) + taylorLength - 1)
def firstMixedBudget (top : Fin 15) : ℕ :=
  firstWidth top * firstChartTop top + firstIndex top * (firstChartTotal top - firstChartTop top)
structure ProperCover (top : Fin 15) (w : I → K) (Γ : Finset K) (s : K → K[X]) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget top
  fresh : invariant.totalCap ≤ (invariantBudget top)
  components : multiple.n + invariant.n ≤ 2 * (invariantBudget top)
end
end Low6960Leading
end
section
namespace Low6960Leading_1
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator separant)
open Low6960Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open Low6960Prices (taylorLength physicalDegree)
open Low6960Leading (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : Geom[X]) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : GeometricX[X] :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open private compatibility_degree from ProximityPrize.SubmissionLower.Fast048
theorem ordinary_bound (f : Row 3) :
    (oldCut f).totalDegree ≤ 1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1) :=
  compatibility_degree f (taylorLength - 3)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} : (i, P) ∈ properComponents f ↔
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hw : Whole (f k)
    · simp [hw] at hk
    · simp only [hw, ite_false] at hk
      obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
      cases he
      exact ⟨hw, hP'⟩
  · rintro ⟨hw, hP⟩
    exact ⟨i, by simpa only [hw, ite_false] using Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def SimpleInvariant (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  componentLength f P = 1 ∧ genericRow (oldNext f) ∈ P
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (top : Fin 15) (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) (graphBox top) 1
  cut_box : InLiftedBox cut (liftedBox top (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox top (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox top taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections (top : Fin 15) {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart top (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget top
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end Low6960Leading_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Low6960Leading
noncomputable section
variable {top : Fin 15}
open P3 (I K node)
open Low6960Prices (Messages)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 133409 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 133409 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (h.degree γ hγ) (h.degree η hη))
  have hroots : (sites.image node).card ≤ diff.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    change a ∈ sites.image node at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Polynomial.mem_roots hdiff).mpr (by simp [diff, hγval i hi, hηval i hi])
  rw [Finset.card_image_of_injective _ IRSProfile.domain.injective] at hroots
  exact hroots.trans hdeg
private theorem count_by_nodes {α ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset α)
    (S : α → Finset ι) {a d : ℕ}
    (hsize : ∀ γ ∈ T, a ≤ (S γ).card)
    (hcap : ∀ i : ι, (T.filter fun γ => i ∈ S γ).card ≤ d) :
    T.card * a ≤ Fintype.card ι * d := by
  classical
  calc
    T.card * a = ∑ _ ∈ T, a := by simp
    _ ≤ ∑ γ ∈ T, (S γ).card := Finset.sum_le_sum hsize
    _ = ∑ γ ∈ T, ∑ i : ι, if i ∈ S γ then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.sum_boole]
      congr 1
      ext i
      simp
    _ = ∑ i : ι, ∑ γ ∈ T, if i ∈ S γ then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ i : ι, (T.filter fun γ => i ∈ S γ).card := by simp
    _ ≤ ∑ _ : ι, d := Finset.sum_le_sum fun i _ => hcap i
    _ = Fintype.card ι * d := by simp
theorem nodeCapacity_count {w Γ s d} (h : Messages w Γ s)
    (hc : NodeCapacity w Γ s d) : 46418 * Γ.card ≤ 82317 * d + 46418 := by
  classical
  by_cases hsmall : Γ.card ≤ 1
  · omega
  obtain ⟨persistent, hp, hd⟩ := hc
  obtain ⟨γ, hγ, η, hη, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < Γ.card)
  have hpN := agree_pair_le h hγ hη hne persistent
    (fun i hi => hp i hi γ hγ) (fun i hi => hp i hi η hη)
  let U : Finset I := Finset.univ \ persistent
  let hits (γ : K) : Finset I := Finset.univ.filter fun i => (s γ).eval (node i) = w i
  let supports (γ : K) : Finset U := (hits γ \ persistent).subtype (· ∈ U)
  let a : ℕ := 179827 - persistent.card
  let b : ℕ := 133409 - persistent.card
  have hU : Fintype.card U = 262144 - persistent.card := by
    rw [Fintype.card_coe]
    change (Finset.univ \ persistent).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ persistent), Finset.card_univ]
    change Fintype.card (Fin (2 ^ 18)) - persistent.card = _
    rw [Fintype.card_fin]
    rfl
  have hsubcard (T : Finset I) : ((T \ persistent).subtype (· ∈ U)).card =
      (T \ persistent).card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hpSub : ∀ γ ∈ Γ, persistent ⊆ hits γ := by
    intro γ hγ i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi γ hγ⟩
  have hsize : ∀ γ ∈ Γ, a ≤ (supports γ).card := by
    intro γ hγ
    obtain ⟨T, hT, hval⟩ := h.hits γ hγ
    have hTsub : T ⊆ hits γ := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval i hi⟩
    calc
      a ≤ (hits γ).card - persistent.card := Nat.sub_le_sub_right
        (hT.trans (Finset.card_le_card hTsub)) _
      _ = (supports γ).card := by
        dsimp only [supports]
        rw [hsubcard, Finset.card_sdiff_of_subset (hpSub γ hγ)]
  have hpair : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
      (supports γ ∩ supports η).card ≤ b := by
    intro γ hγ η hη hne
    have heq : supports γ ∩ supports η =
        ((hits γ ∩ hits η) \ persistent).subtype (· ∈ U) := by
      ext i
      simp only [supports, Finset.mem_inter, Finset.mem_subtype, Finset.mem_sdiff]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩,
        fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
    have hsub : persistent ⊆ hits γ ∩ hits η :=
      fun _ hi => Finset.mem_inter.mpr ⟨hpSub γ hγ hi, hpSub η hη hi⟩
    rw [heq, hsubcard, Finset.card_sdiff_of_subset hsub]
    apply Nat.sub_le_sub_right
    exact agree_pair_le h hγ hη hne _
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2)
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2)
  have hcap : ∀ i : U, (Γ.filter fun γ => i ∈ supports γ).card ≤ d := by
    intro i
    have hi := (Finset.mem_sdiff.mp i.property).2
    apply (Finset.card_le_card ?_).trans (hd i.val hi)
    intro γ hγ
    obtain ⟨hγΓ, hγi⟩ := Finset.mem_filter.mp hγ
    exact Finset.mem_filter.mpr
      ⟨hγΓ, (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hγi)).1).2⟩
  have hincNat := count_by_nodes Γ supports hsize hcap
  let l : ℤ := Γ.card
  let x : ℤ := a
  have hb : (b : ℤ) = x - 46418 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 133409 ≤ 179827))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 82317 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 133409 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 133409 ≤ 179827))]
    ring
  have hinc' : l * x ≤ (x + 82317) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 82317 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 82317 * (d : ℤ) < (l - 1) * 46418 := by
    have hc : 82317 * (d : ℤ) + 46418 < 46418 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 35899 * (d : ℤ) < (l - (d : ℤ)) * 46418 := by linarith only [hbad]
  have hden : 0 < 82317 * 46418 - 35899 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 35899)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 82317)
    have hpos : 0 < (l - (d : ℤ)) * (82317 * 46418 - 35899 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 133409 ≤ 179827) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hba hdenNat hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 82317 * 46418 ≤ (35899 * l + 46418) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 35899 * l + 46418 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 82317 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]
theorem nodeFamily_count {w Γ s} (C : NodeFamily w Γ s) (h : Messages w Γ s) :
    46418 * C.labels.card ≤ 82317 * C.totalCap + 46418 * C.n := by
  classical
  calc
    46418 * C.labels.card ≤ 46418 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46418 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (82317 * C.cap i + 46418) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 82317 * C.totalCap + 46418 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
end
end Low6960Leading
end
section
namespace Low6960Leading_1
noncomputable section
variable {top : Fin 15}
open P3 (I K node)
open Low6960Prices (Messages taylorLength physicalDegree)
open Low6960Leading (nodeCapacity_count)
open K1_13 (Geom embed extend)
open K1_13_5 (NodeCapacity)
open K1_13_5_4 (GeometricX GeoRow)
open Polynomial
open scoped BigOperators
private theorem recover_coefficients (S : Geom[X]) (hS : S.natDegree ≤ physicalDegree) :
    coefficientPolynomial (coefficientPoint S) = S.map (algebraMap Geom GeometricX) := by
  unfold coefficientPolynomial coefficientPoint
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    Polynomial.monomial j (algebraMap Geom GeometricX (S.coeff j)))]
  conv_rhs => rw [Polynomial.as_sum_range' S taylorLength (Nat.lt_succ_of_le hS)]
  simp only [Polynomial.map_sum, Polynomial.map_monomial]
private theorem coefficientPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coefficientPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ δ hδ heq
  apply h.distinct hγ hδ
  apply Polynomial.map_injective embed embed.injective
  apply Polynomial.map_injective (algebraMap Geom GeometricX) (algebraMap Geom GeometricX).injective
  have hdeg : ∀ η ∈ Γ, (extend (s η)).natDegree ≤ physicalDegree := by
    intro η hη
    simpa only [Polynomial.natDegree_map] using h.degree η hη
  rw [← recover_coefficients _ (hdeg _ hγ), ← recover_coefficients _ (hdeg _ hδ)]
  exact congrArg coefficientPolynomial heq
private def valueCut (x y : GeometricX) : GeoRow taylorLength :=
  (∑ j : Fin taylorLength, MvPolynomial.C (x ^ j.val) * MvPolynomial.X j) - MvPolynomial.C y
private theorem totalDegree_valueCut (x y : GeometricX) : (valueCut x y).totalDegree ≤ 1 := by
  unfold valueCut
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
    MvPolynomial.totalDegree_mul (MvPolynomial.C (x ^ j.val)) (MvPolynomial.X j)
private theorem eval_valueCut (a : Coefficients) (x y : GeometricX) :
    MvPolynomial.eval a (valueCut x y) = (coefficientPolynomial a).eval x - y := by
  simp only [valueCut, coefficientPolynomial, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact congrArg (fun z : GeometricX => z - y) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
private def constantEmbed : K →+* GeometricX := (algebraMap Geom GeometricX).comp embed
private def nodeCut (w : I → K) (i : I) : GeoRow taylorLength :=
  valueCut (constantEmbed (node i)) (constantEmbed (w i))
private theorem eval_nodeCut_iff {w Γ s} (h : Messages w Γ s) {γ : K} (hγ : γ ∈ Γ) (i : I) :
    MvPolynomial.eval (coefficientPoint (extend (s γ))) (nodeCut w i) = 0 ↔
      (s γ).eval (node i) = w i := by
  have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using h.degree γ hγ
  rw [nodeCut, eval_valueCut, recover_coefficients _ hdeg, sub_eq_zero]
  unfold constantEmbed
  simp only [RingHom.comp_apply, Polynomial.eval_map_apply]
  exact (algebraMap Geom GeometricX).injective.eq_iff.trans embed.injective.eq_iff
theorem nodeCapacity_of_coefficient_curve {w Γ s} {d : ℕ} (h : Messages w Γ s)
    (Q : CoefficientIdeal) (hp : Q.IsPrime)
    (hdim : (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1)
    (hdegree : MvPolynomial.affineDegree Q ≤ (d : ℚ))
    (hcurve : ∀ γ ∈ Γ, coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    NodeCapacity w Γ s d := by
  classical
  let A := fun γ => coefficientPoint (extend (s γ))
  have hinj : Set.InjOn A (Γ : Set K) := coefficientPoint_injOn h
  by_cases hzero : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 0
  · have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) Q hzero
    have hsub : (↑(Γ.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX Q := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      exact hcurve γ hγ
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hcard
    have hcard' : (Γ.card : ℚ) ≤ d := (Nat.cast_le.mpr hcard).trans (bound.2.trans hdegree)
    refine ⟨∅, by simp, fun i _ => (Finset.card_filter_le _ _).trans ?_⟩
    exact_mod_cast hcard'
  have hone : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1 := by omega
  let persistent := Finset.univ.filter fun i => nodeCut w i ∈ Q
  refine ⟨persistent, ?_, ?_⟩
  · intro i hi γ hγ
    have he := hcurve γ hγ (nodeCut w i) (Finset.mem_filter.mp hi).2
    exact (eval_nodeCut_iff h hγ i).mp he
  · intro i hi
    let cut := nodeCut w i
    have hcut : cut ∉ Q := fun hc => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    let J := Q ⊔ Ideal.span {cut}
    have hJ := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hcut (totalDegree_valueCut (constantEmbed (node i)) (constantEmbed (w i)))
    have hjdim : (MvPolynomial.affineHilbertPolynomial J).natDegree = 0 := by
      rw [hone] at hJ
      exact Nat.eq_zero_of_le_zero hJ.1
    have hjdeg : MvPolynomial.affineDegree J ≤ MvPolynomial.affineDegree Q := by
      rw [MvPolynomial.affineDegree_of_natDegree_eq_zero hjdim, MvPolynomial.affineDegree, hone]
      simpa [hone] using hJ.2
    have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hjdim
    let selected := Γ.filter (fun γ => (s γ).eval (node i) = w i)
    have hsub : (↑(selected.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX J := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hγ, he⟩ := Finset.mem_filter.mp hγ
      exact MvPolynomial.mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hcurve γ hγ, (eval_nodeCut_iff h hγ i).mpr he⟩
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))] at hcard
    have hcard' : (selected.card : ℚ) ≤ d :=
      (Nat.cast_le.mpr hcard).trans (bound.2.trans (hjdeg.trans hdegree))
    exact_mod_cast hcard'
theorem curveCount_le_twice_degree {w Γ s} {d : ℕ} (h : Messages w Γ s) (hd : 0 < d)
    (hc : NodeCapacity w Γ s d) : Γ.card ≤ 2*d := by
  have hcount := nodeCapacity_count h hc
  omega
end
end Low6960Leading_1
end
section
namespace Low6960Leading_1
noncomputable section
variable {top : Fin 15}
open Low6960Prices (physicalDegree taylorLength)
open Low6960Leading (SecondFactors)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant)
open Low6960Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open private mul_bound K1_13_5_4_1_1.partialFlow_bound liftSep_eq liftedStep_bound generic_bound
  totalWeight indexWeight topWeight heightWeight lift_weight fits
  from ProximityPrize.SubmissionLower.Fast070
open private represents from ProximityPrize.SubmissionLower.Fast076
open private atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero
  actual_zero_of_represents from ProximityPrize.SubmissionLower.Fast048
local notation "W" => weightedTotalDegree
private def coefficientNumerator (m : ℕ) (f : Row 3) (i : Fin m) : GeoRow 4 :=
  ∑ j : Fin m, MvPolynomial.C (((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val) *
    genericRow (padJet f (m - 4) j.val)
private def cut (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 3))
private def next (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 2))
private theorem padded_bound (w : Fin 4 → ℕ) {initial step m : ℕ} {f : Row 3}
    (hinit : ∀ i, w i ≤ initial) (hs : W w (liftSep f) ≤ step)
    (hthird : ∀ k, W w (thirdNumerator f k) ≤ w 3 + k * step) (j : Fin m) :
    W w (padJet f (m - 4) j.val) ≤ initial + (m - 4) * step := by
  unfold padJet jetNumerator
  have hpow := (weightedTotalDegree_pow_le w (liftSep f) (m - 4 - (j.val - 3))).trans
    (Nat.mul_le_mul_left _ hs)
  split_ifs with hj
  · have hz : j.val - 3 = 0 := by omega
    rw [hz, Nat.sub_zero] at hpow ⊢
    exact (mul_bound hpow ((weight_X_le w _).trans (hinit _))).trans_eq (Nat.add_comm _ _)
  · have hsum : (m - 4 - (j.val - 3)) + (j.val - 3) = m - 4 := by
      have hj' := j.isLt
      omega
    calc
      _ ≤ (m - 4 - (j.val - 3)) * step + (w 3 + (j.val - 3) * step) :=
        mul_bound hpow ((weight_const_mul_le w _ _).trans (hthird _))
      _ = w 3 + ((m - 4 - (j.val - 3)) + (j.val - 3)) * step := by ring
      _ ≤ _ := by rw [hsum]; exact Nat.add_le_add_right (hinit 3) _
private theorem weight_bounds (w : Fin 4 → ℕ) (base delta step initial m : ℕ) {f : Row 3}
    (hf : W w (liftRaw f) ≤ base)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    (hsep : base - w 2 + delta ≤ step) (hvelocity : base + 2 * delta ≤ w 3 + step)
    (hinit : ∀ i, w i ≤ initial) :
    W w (graph f) ≤ base + delta ∧
    (∀ k, W w (genericRow (thirdNumerator f k)) ≤ w 3 + k * step) ∧
    (∀ i, W w (coefficientNumerator m f i) ≤ initial + (m - 4) * step) := by
  have hg : W w (graphRaw f) ≤ base + delta := by
    rw [← partialFlow_lift]
    exact K1_13_5_4_1_1.partialFlow_bound w hshift hf
  have hs : W w (liftSep f) ≤ base - w 2 := by
    rw [liftSep_eq]
    exact (weightedTotalDegree_pderiv_le_sub w 2 _).trans (Nat.sub_le_sub_right hf _)
  have hu : W w (thirdVelocityNumerator f) ≤ w 3 + step := by
    unfold thirdVelocityNumerator
    exact ((weight_const_mul_le w _ _).trans (K1_13_5_4_1_1.partialFlow_bound w hshift hg)).trans (by omega)
  have hthird (k : ℕ) : W w (thirdNumerator f k) ≤ w 3 + k * step := by
    induction k with
    | zero =>
      simpa only [thirdNumerator, Nat.zero_mul, Nat.add_zero] using weight_X_le (R := Geom[X]) w 3
    | succ k ih =>
      rw [thirdNumerator, Nat.succ_mul, ← Nat.add_assoc]
      exact liftedStep_bound w hshift ih hs hsep hu k
  refine ⟨?_, fun k => (generic_bound w _).trans (hthird k), ?_⟩
  · rw [← generic_graph]
    exact (generic_bound w _).trans hg
  · intro i
    unfold coefficientNumerator
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sum_mem
    intro j _
    exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_const_mul_le w _ _).trans ((generic_bound w _).trans
        (padded_bound w hinit (hs.trans ((Nat.le_add_right _ _).trans hsep)) hthird j)))
private theorem fits_lifted {p : GeoRow 4} (L : ℕ)
    (hb : W totalWeight p ≤ 1 + (L - 4) * (Low6960Prices.lowerWidth top))
    (hj : W indexWeight p ≤ 2 + (L - 4) * (Low6960Prices.lowerIndex top + 2))
    (ht : W topWeight p ≤ 1 + (L - 4) * (Low6960Prices.lowerTop top + 2))
    (hh : W heightWeight p ≤ L - 2) :
    InLiftedBox p (liftedBox top L) (L - 2) :=
  fits hb hj ht hh
private theorem support (f : Row 3)
    (hb : f.totalDegree ≤ (Low6960Prices.lowerWidth top)) (hj : indexDegree f ≤ (Low6960Prices.lowerIndex top)) (ht : f.degreeOf 2 ≤ (Low6960Prices.lowerTop top)) :
    InLiftedBox (graph f) (graphBox top) 1 ∧
    InLiftedBox (cut taylorLength f) (liftedBox top (taylorLength + 1)) (taylorLength - 1) ∧
    InLiftedBox (next taylorLength f) (liftedBox top (taylorLength + 2)) taylorLength ∧
    ∀ i, InLiftedBox (coefficientNumerator taylorLength f i) (liftedBox top taylorLength) (taylorLength - 2) := by
  have htotal : W totalWeight (liftRaw f) ≤ (Low6960Prices.lowerWidth top) := by
    rw [lift_weight, show totalWeight ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_one]
    exact hb
  have hindex : W indexWeight (liftRaw f) ≤ (Low6960Prices.lowerIndex top) := by
    rw [lift_weight, show indexWeight ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have htop : W topWeight (liftRaw f) ≤ (Low6960Prices.lowerTop top) := by
    rw [lift_weight, show topWeight ∘ Fin.castSucc = Pi.single (2 : Fin 3) 1 from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_piSingle]
    exact ht
  have hheight : W heightWeight (liftRaw f) ≤ 0 := by
    rw [lift_weight, show heightWeight ∘ Fin.castSucc = (0 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree, Finset.sup_le_iff]
    intro a _
    simp [Finsupp.weight_eq_sum]
  obtain ⟨bg, bn, bc⟩ := weight_bounds totalWeight (Low6960Prices.lowerWidth top) 0 (Low6960Prices.lowerWidth top) 1 taylorLength htotal
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨jg, jn, jc⟩ := weight_bounds indexWeight (Low6960Prices.lowerIndex top) 1 (Low6960Prices.lowerIndex top + 2) 2 taylorLength hindex
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨tg, tn, tc⟩ := weight_bounds topWeight (Low6960Prices.lowerTop top) 1 (Low6960Prices.lowerTop top + 2) 1 taylorLength htop
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨hg, hn, hc⟩ := weight_bounds heightWeight 0 1 1 1 taylorLength hheight
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  have hrepl : min (Low6960Prices.lowerTop top + 1) ((Low6960Prices.lowerIndex top + 1) / 2) =
      (Low6960Prices.lowerIndex top + 1) / 2 := by fin_cases top <;> decide
  have hGraphB : W totalWeight (graph f) ≤ Low6960Prices.lowerWidth top := bg
  have hGraphH : W heightWeight (graph f) ≤ 1 := hg
  refine ⟨by simpa only [graphBox, hrepl] using fits hGraphB jg tg hGraphH, ?_, ?_, ?_⟩
  · rw [show taylorLength - 1 = taylorLength + 1 - 2 by decide]
    exact fits_lifted _ ((bn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 3)).trans (by decide))
  · have hh : taylorLength + 2 - 2 = taylorLength := by decide
    simpa only [hh, next] using fits_lifted (taylorLength + 2) ((bn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 2)).trans (by decide))
  · intro i
    exact fits_lifted _ (bc i) (jc i) (tc i) ((hc i).trans (by decide))
private theorem atJet_padded (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0)
    {m : ℕ} (hm : m < K1.p) (j : Fin m) :
    atJet (padJet f (m - 4) j.val) S =
      atJet (separant f) S ^ (m - 4) * hasseDeriv j.val S := by
  have hj := j.isLt
  exact atJet_padJet f S hf (m - 4) j.val (by omega) (hj.trans hm)
private theorem reconstruct_actual {f : Row 3} {S : Geom[X]} (hdeg : S.natDegree < taylorLength)
    (hS : RegularAt 2 f S) :
    reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  funext i
  rw [reconstruct, graphPoint_of_actual hS, eval_genericRow]
  let s := genericCoeff (atJet (separant f) S)
  have hs : s ≠ 0 := genericCoeff_ne_zero hS.2
  have hp : taylorLength < K1.p := by decide
  unfold coefficientNumerator
  rw [map_sum]
  change (∑ j : Fin taylorLength, MvPolynomial.eval (jetPoint S) _) /
    s ^ (taylorLength - 4) = _
  simp only [map_mul, MvPolynomial.eval_C, eval_genericRow, atJet_padded f S hS.1 hp, map_pow]
  change _ = algebraMap Geom GeometricX (S.coeff i)
  rw [div_eq_iff (pow_ne_zero _ hs), ← taylor_coefficients_aux S taylorLength hdeg i.val,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (s ^ (taylorLength - 4) * _) = _ * s ^ (taylorLength - 4)
  rw [mul_comm (s ^ (taylorLength - 4)), ← mul_assoc]
private theorem actual {f : Row 3}
    (hcut : RepresentsOnGraph f (oldCut f) (cut taylorLength f))
    (hnext : RepresentsOnGraph f (oldNext f) (next taylorLength f))
    (S : Geom[X]) (hdeg : S.natDegree ≤ physicalDegree) (hS : RegularAt 2 f S) :
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  have hlength (d m : ℕ) (hd : d < m) (hm : 4 ≤ m) : d - 3 < m - 3 := by omega
  have hdeg' : S.natDegree < taylorLength := Nat.lt_succ_of_le hdeg
  have hfirst := hlength S.natDegree taylorLength hdeg' (by decide)
  have hsecond : S.natDegree - 3 < taylorLength - 2 :=
    hfirst.trans_le (Nat.sub_le_sub_left (by decide : 2 ≤ 3) _)
  refine ⟨actual_zero_of_represents hS hcut ?_, actual_zero_of_represents hS hnext ?_,
    reconstruct_actual hdeg' hS⟩
  · rw [cut, eval_genericRow, third_atJet_zero hS.1 _ hfirst, map_zero]
  · rw [next, eval_genericRow, third_atJet_zero hS.1 _ hsecond, map_zero]
theorem lifted_chart (n : ℕ) (f : Fin n → Row 3) (hf : SecondFactors top f) (i : Fin n) :
    Nonempty (LiftedChart top (f i)) := by
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.coordinate
  obtain ⟨hg, he, hn, hc⟩ := support (f i) hb hj ht
  have hrep : RepresentsOnGraph (f i) (oldCut (f i)) (cut taylorLength (f i)) :=
    represents (f i) (taylorLength - 3)
  have hrep' : RepresentsOnGraph (f i) (oldNext (f i)) (next taylorLength (f i)) :=
    represents (f i) (taylorLength - 2)
  exact ⟨{
    cut := cut taylorLength (f i)
    next := next taylorLength (f i)
    numerator := coefficientNumerator taylorLength (f i)
    graph_box := hg
    cut_box := he
    next_box := hn
    coefficient_box := hc
    cut_represents := hrep
    next_represents := hrep'
    actual := actual hrep hrep'
  }⟩
end
end Low6960Leading_1
end
section
namespace Low6960Leading
noncomputable section
variable {top : Fin 15}
open K1_13 (Geom Row atJet jet indexDegree)
open K1_13_5 (RegularAt)
open Low6960Leading (FirstRow)
open K1_13_5_1
open Low6960Prices (LowerRow TrueWeightLE physicalDegree anchorCutoff lowerWidth lowerIndex lowerTop)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open private coeff_flatten from ProximityPrize.SubmissionLower.Fast040
private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr
private theorem aggregate_contracted {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a r : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ r) (hB : a * r ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ max B ((2 * r - 1) * B - a * r^2) := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    exact h.trans (le_max_left _ _)
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (r + C) ≤ 2 * B := by
    calc
      _ ≤ a * (r + r) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc r)
      _ = 2 * (a * r) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : r = C + (r - C) := by omega
  have hsq : a * C ^ 2 + a * ((r - C) * (r + C)) = a * r ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((r - C) * ((C + (r - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((r - C) * (n + C))) he
      _ = a * (C + (r - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)).trans (le_max_right _ _)
theorem factor_cover (g : Row 3) (hg : LowerRow top g) :
    ∃ (n : ℕ) (f : Fin n → Row 3) (q : Row 2), SecondFactors top f ∧ FirstRow top q ∧
      ∀ S : Geom[X], atJet g S = 0 →
        atJet q S = 0 ∨ ∃ i, RegularAt 2 (f i) S := by
  classical
  obtain ⟨hg₀, hgt₀, hgi₀, hgw⟩ := hg
  let _ : StrongNormalizationMonoid (Row 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors g
  let T := A.toFinset
  let c (f : Row 3) := (view f).natDegree
  let P := T.filter fun f => 0 < c f
  let n := Fintype.card ↥P
  let e : Fin n ≃ ↥P := (Fintype.equivFin ↥P).symm
  let f : Fin n → Row 3 := fun i => (e i).val
  let q : Row 2 := ∏ a ∈ T, elimination a
  have hmem (a : Row 3) (ha : a ∈ T) : a ∈ A := Multiset.mem_toFinset.mp ha
  have hirr (a : Row 3) (ha : a ∈ T) : Irreducible a :=
    irreducible_of_normalized_factor a (hmem a ha)
  have hf (i : Fin n) : f i ∈ T ∧ 0 < c (f i) := Finset.mem_filter.mp (e i).property
  have hdvd : (∏ a ∈ T, a) ∣ g :=
    (Multiset.toFinset_prod_dvd_prod A).trans (prod_normalizedFactors hg₀).dvd
  have hsum (w : Fin 3 → ℕ) :
      (∑ a ∈ T, a.weightedTotalDegree w) ≤ g.weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w T id hg₀ hdvd
  have htop (a : Row 3) : c a = a.degreeOf 2 := view_degree a
  have hc : ∑ a ∈ T, c a ≤ lowerTop top := by
    have hbound : g.weightedTotalDegree (fun i => i.val) ≤ lowerIndex top :=
      (K1_13_1.indexDegree_eq g) ▸ hgi₀
    have h : 2 * (∑ a ∈ T, c a) ≤ lowerIndex top := calc
      _ = ∑ a ∈ T, (2 * c a) := Finset.mul_sum T c 2
      _ ≤ ∑ a ∈ T, a.weightedTotalDegree (fun i => i.val) := by
        apply Finset.sum_le_sum
        intro a _
        exact (Nat.le_add_left _ _).trans (view_coeff_weight (fun i => i.val) a (c a) le_rfl)
      _ ≤ _ := (hsum _).trans hbound
    unfold lowerTop
    omega
  have hr : lowerTop top < K1.p := by fin_cases top <;> decide
  have he₀ (a : Row 3) (ha : a ∈ T) : elimination a ≠ 0 := by
    have hca := (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) ha).trans hc
    exact elimination_ne_zero (hirr a ha) (hca.trans_lt hr)
  have hq (w : Fin 3 → ℕ) (B : ℕ) (hb : g.weightedTotalDegree w ≤ B)
      (hB : w 2 * lowerTop top ≤ B) :
      q.weightedTotalDegree (fun i => w i.castSucc) ≤
        max B ((2 * lowerTop top - 1) * B - w 2 * lowerTop top ^ 2) := by
    let v : Fin 2 → ℕ := fun i => w i.castSucc
    rw [show q = ∏ a ∈ T, elimination a from rfl, weightedTotalDegree_prod v T _ he₀]
    apply aggregate_contracted T (fun a => a.weightedTotalDegree w) c
      (fun a => (elimination a).weightedTotalDegree v) B (w 2) (lowerTop top)
      ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (view_coeff_weight w a (c a) le_rfl)
    · intro a _ ha
      exact elimination_weight_zero w a ha
    · intro a _ ha
      exact elimination_weight_positive w a ha
  have hqtotal : q.totalDegree ≤ firstWidth top := by
    have hb : g.totalDegree ≤ lowerWidth top := hgt₀
    have h := hq (1 : Fin 3 → ℕ) (lowerWidth top)
      (by simpa only [weightedTotalDegree_one] using hb)
      (by fin_cases top <;> decide)
    have hv : (fun i : Fin 2 => (1 : Fin 3 → ℕ) i.castSucc) = (1 : Fin 2 → ℕ) := by
      funext i
      simp
    rw [hv, weightedTotalDegree_one, Pi.one_apply, one_mul] at h
    exact h
  have hqindex : indexDegree q ≤ firstIndex top := by
    rw [K1_13_1.indexDegree_eq] at hgi₀ ⊢
    have hbudget : (2 : ℕ) * lowerTop top ≤ lowerIndex top := by
      unfold lowerTop
      omega
    exact hq (fun i => i.val) (lowerIndex top) hgi₀ hbudget
  have hsub (d : Row 3 → ℕ) : (∑ i, d (f i)) ≤ ∑ a ∈ T, d a := by
    calc
      _ = ∑ a : ↥P, d a.val := e.sum_comp _
      _ = ∑ a ∈ P, d a := Finset.sum_coe_sort P d
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨n, f, q, ⟨fun i => hirr _ (hf i).1, fun i => htop _ ▸ (hf i).2, ?_, ?_, ?_, ?_⟩,
    ⟨Finset.prod_ne_zero_iff.mpr he₀, hqtotal, hqindex⟩, ?_⟩
  · intro i
    let E := MvPolynomial.optionEquivRight Geom (Fin 3)
    have hdi := map_dvd E.symm (dvd_of_mem_normalizedFactors (hmem _ (hf i).1))
    have hgn : E.symm g ≠ 0 := fun hz => hg₀ (E.symm.injective (hz.trans (map_zero _).symm))
    exact (trueWeight_iff _).mpr
      ((weightedTotalDegree_le_of_dvd _ hdi hgn).trans ((trueWeight_iff _).mp hgw))
  · exact (hsub _).trans ((by simpa only [weightedTotalDegree_one] using hsum (1 : Fin 3 → ℕ) :
      (∑ a ∈ T, a.totalDegree) ≤ g.totalDegree).trans hgt₀)
  · exact (hsub _).trans ((by simpa only [← K1_13_1.indexDegree_eq] using hsum (fun i => i.val) :
      (∑ a ∈ T, indexDegree a) ≤ indexDegree g).trans hgi₀)
  · simpa only [htop] using (hsub c).trans hc
  · intro S hS
    have hz := map_dvd (eval (jet S)) (prod_normalizedFactors hg₀).symm.dvd
    change atJet g S ∣ eval (jet S) A.prod at hz
    rw [hS, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨a, ha, hzero⟩ := hz
    have haT : a ∈ T := Multiset.mem_toFinset.mpr ha
    rcases elimination_eval a S hzero with h | ⟨hp, hr⟩
    · left
      change eval (jet S) (∏ a ∈ T, elimination a) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero haT h
    · right
      let j : ↥P := ⟨a, Finset.mem_filter.mpr ⟨haT, hp⟩⟩
      refine ⟨e.symm j, ?_⟩
      change RegularAt 2 ((e (e.symm j)).val) S
      rw [Equiv.apply_symm_apply]
      exact hr
end
end Low6960Leading
end
namespace Low6960LeadingFirst
noncomputable section
variable {top : Fin 15}
open K1_13 MvPolynomial UniqueFactorizationMonoid
open K1_13_5 (RegularAt)
open Low6960Leading (FirstRow FirstFactors firstWidth firstIndex)
open scoped BigOperators Polynomial
private def firstView : Row 2 ≃ₐ[Geom[X]] (Row 1)[X] :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin 1))
private abbrev valueView : Row 1 ≃ₐ[Geom[X]] Geom[X][X] :=
  uniqueAlgEquiv Geom[X] (Fin 1)
private theorem firstView_degree (f : Row 2) : (firstView f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)
private theorem firstView_pderiv (f : Row 2) :
    firstView (pderiv 1 f) = (firstView f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv 1 f)) =
    (optionEquivLeft _ _ (rename finSuccEquivLast f)).derivative
  rw [← pderiv_rename finSuccEquivLast.injective,
    show finSuccEquivLast (1 : Fin 2) = none from finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
private theorem valueView_eval (g : Row 1) (S : Geom[X]) :
    (valueView g).eval S = MvPolynomial.eval (jet S) g := by
  have h := eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id Geom[X]) (a := jet S)
  have hzero : jet S (default : Fin 1) = S := by
    change Polynomial.hasseDeriv 0 S = S
    simp
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hzero] using h
private theorem firstView_eval (f : Row 2) (S : Geom[X]) :
    ((firstView f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
      atJet f S := by
  rw [firstView, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename, atJet]
  apply congrArg (fun x : Fin 2 → Geom[X] => MvPolynomial.eval x f)
  funext i
  fin_cases i <;> rfl
private theorem valueView_degree_le (g : Row 1) : (valueView g).natDegree ≤ g.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [valueView, coeff_uniqueAlgEquiv]
  by_contra hn
  have h := le_totalDegree (mem_support_iff.mpr hn)
  change (Finsupp.single (default : Fin 1) k).degree ≤ g.totalDegree at h
  rw [Finsupp.degree_single] at h
  exact (not_le_of_gt hk) h
private theorem firstView_coeff_bound (f : Row 2) (k : ℕ) (hk : k ≤ f.totalDegree) :
    k + (valueView ((firstView f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le Geom[X] (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)
private def eliminant (f : Row 2) : Geom[X][X] :=
  let A := firstView f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)
set_option maxHeartbeats 600000 in
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) (hb : f.totalDegree ≤ (firstWidth top)) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * ((firstWidth top) - 1) ∧
      ∀ S : Geom[X], atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ firstView.injective).mpr hf.ne_zero
  by_cases hc : 0 < c
  · let R := A.resultant A.derivative c (c - 1)
    have hform : eliminant f = valueView R := ite_eq_left hc
    have hcast : (c : Row 1) ≠ 0 := by
      have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
      have : CharP Geom[X] K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R := Geom)) K1.p
      have : CharP (Row 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ := Fin 1) (R := Geom[X])) K1.p
      intro h
      have hp : K1.p ∣ c := (CharP.cast_eq_zero_iff (Row 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt (by fin_cases top <;> decide : (firstWidth top) < K1.p))))
        (Nat.le_of_dvd hc hp)
    have hder : A.derivative ≠ 0 := by
      intro h
      have hz := congrArg (fun P : (Row 1)[X] => P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc, Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 : ℕ) : Row 1) + 1) = (c : Row 1) := calc
        _ = ((c - 1 + 1 : ℕ) : Row 1) := by rw [Nat.cast_add, Nat.cast_one]
        _ = _ := congrArg (fun k : ℕ => (k : Row 1)) (Nat.sub_add_cancel hc)
      rw [hnat] at hz
      change A.leadingCoeff * (c : Row 1) = 0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR : R ≠ 0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map firstView) hder
    have hdeg : (valueView R).natDegree + c ^ 2 ≤ (2 * c - 1) * b := by
      let B := A.map valueView.toRingHom
      have h := Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Polynomial.coeff_map]
        exact firstView_coeff_bound f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map] at h
      exact h
    have hbudget : (valueView R).natDegree ≤ b * (b - 1) := by
      have hbpos : 1 ≤ b := hc.trans_le hcb
      have hcpos : 1 ≤ 2 * c := by omega
      zify [hbpos, hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b : ℤ) - (c : ℤ))]
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hR, ?_, ?_⟩
    · rw [hform]
      exact hbudget.trans (Nat.mul_le_mul_left b (Nat.sub_le_sub_right hb 1))
    · intro S hS
      by_cases hS' : atJet (pderiv 1 f) S = 0
      · left
        rw [hform, valueView_eval]
        exact Polynomial.map_resultant_eq_zero_of_common_root (MvPolynomial.eval (jet S))
          A A.derivative le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 : Fin 2)) ((firstView_eval f S).trans hS) (by
            rw [show A.derivative = firstView (pderiv 1 f) from (firstView_pderiv f).symm]
            exact (firstView_eval _ S).trans hS')
      · exact Or.inr ⟨(firstView_degree f) ▸ hc, hS, hS'⟩
  · have hform : eliminant f = valueView (A.coeff 0) := ite_eq_right hc
    have hAc : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0 : A.coeff 0 ≠ 0 := fun h => hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hA0, ?_, ?_⟩
    · rw [hform]
      have h := firstView_coeff_bound f 0 (Nat.zero_le _)
      exact (by simpa using h : (valueView (A.coeff 0)).natDegree ≤ b).trans
        (by simpa using Nat.mul_le_mul_left b (by fin_cases top <;> decide : 1 ≤ (firstWidth top) - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h
theorem proof (q : Row 2) (hq : FirstRow top q) :
    ∃ (n : ℕ) (f : Fin n → Row 2) (u : Geom[X][X]), FirstFactors top f ∧ u ≠ 0 ∧
      u.natDegree ≤ (firstWidth top) * ((firstWidth top) - 1) ∧
      ∀ S : Geom[X], atJet q S = 0 →
        u.eval S = 0 ∨ ∃ i, RegularAt 1 (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 2 := fun i => (e i).val
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq.ne_zero).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ (firstWidth top) := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq.ne_zero hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hq.total
  have hfactor : ∀ i, f i ∈ A ∧ 0 < (f i).degreeOf 1 := fun i =>
    Finset.mem_filter.mp (e i).property
  have hfdiv : (∏ i, f i) ∣ q := by
    rw [show (∏ i, f i) = ∏ g : ↥T, id g.val from e.prod_comp Subtype.val,
      Finset.prod_coe_sort T id]
    exact (Finset.prod_dvd_prod_of_subset T A id (Finset.filter_subset _ _)).trans hdiv
  have hf : FirstFactors top f := by
    refine ⟨fun i => hA _ (hfactor i).1, fun i => (hfactor i).2, ?_, ?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) Finset.univ f hq.ne_zero hfdiv
      simp only [weightedTotalDegree_one] at h
      exact h.trans hq.total
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i : Fin 2 => i.val)
        Finset.univ f hq.ne_zero hfdiv
      simp only [← K1_13_1.indexDegree_eq] at h
      exact h.trans hq.index
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨n, f, u, hf, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * ((firstWidth top) - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ (firstWidth top) * ((firstWidth top) - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq.ne_zero).symm.dvd
      change atJet q S ∣ _ at hd
      rwa [hS, zero_dvd_iff] at hd
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hroot
    obtain ⟨g, hgM, hgS⟩ := hroot
    have hgA : g ∈ A := Multiset.mem_toFinset.mpr hgM
    rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos, hreg⟩
    · left
      change Polynomial.evalRingHom S u = 0
      rw [show u = ∏ g ∈ A, eliminant g from rfl, map_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨g, hgA, hzero⟩
    · right
      let j := e.symm ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩⟩
      have hj : f j = g := congrArg Subtype.val (e.apply_symm_apply _)
      exact ⟨j, hj ▸ hreg⟩
end
end Low6960LeadingFirst

section
namespace Low6960Leading
noncomputable section
variable {top : Fin 15}
open P3 (I K node p)
open Low6960Prices (Messages taylorLength)
open K1_13 (Row Geom embed extend indexDegree atJet)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open Low6960Leading (FirstFactors)
open K1_13_5_3 (CenterField toCenter constants center chart plane marked toCenter_inj
  marked_injective aeval_plane plane_ne_zero plane_prime chart_degree chart_top
  degreeOf_le_index mem_capped capped_cut_card)
open Polynomial PolynomialDifferential
open scoped BigOperators
open private eval_at_center specialization_flatten from ProximityPrize.SubmissionLower.Fast048
open K1_13_5_3 (flatten)
private theorem exponent_sufficient : TaylorExponentSufficient 1 taylorLength firstExponent := by
  exact taylorExponentSufficient_firstOrder_tight 133409
private theorem chart_cut_agreement {f : Row 2} {S : Geom[X]} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 133409) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (chart f) taylorLength firstExponent (constants x) (constants y))
      = 0 ↔ S.eval x = y := by
  have hsol : differentialSpecialization (chart f) (S.map constants) = 0 := by
    rw [chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) S ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) S ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) S).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked S) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked S) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  have hdeg : (S.map constants).degree < (taylorLength : WithBot ℕ) := by
    have hb : (S.map constants).natDegree ≤ 133409 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom P3.p := charP_of_injective_ringHom embed.injective P3.p
  have : CharP CenterField P3.p := charP_of_injective_ringHom constants.injective P3.p
  have hpiv : ∀ i : ℕ, 1 < i → i < taylorLength → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField P3.p i).mp hz)
    change 0x7f000001 ≤ i at hp
    change i < 133410 at ht
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (chart f) exponent_sufficient (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]
private theorem plane_capped (f : Row 2) :
    plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (indexDegree f) := by
  intro m hm
  have hf := MvPolynomial.support_map_subset toCenter f hm
  exact ⟨MvPolynomial.le_totalDegree hf,
    (MvPolynomial.monomial_le_degreeOf 1 hf).trans (degreeOf_le_index f)⟩
private def nodeCut (w : I → K) (f : Row 2) (i : I) : MvPolynomial (Fin 2) CenterField :=
  taylorAgreementEquation center (chart f) taylorLength firstExponent
    (constants (embed (node i))) (constants (embed (w i)))
private theorem nodeCut_capped (w : I → K) (f : Row 2)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top)) (i : I) :
    nodeCut w f i ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      (firstChartTotal top) (firstChartTop top) := by
  have ht : (nodeCut w f i).totalDegree ≤ (firstChartTotal top) := by
    refine (totalDegree_taylorAgreementEquation_le center (chart f)
      exponent_sufficient _ _).trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_left firstExponent
      (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1
  refine mem_capped _ ht (le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans ht) ?_)
  exact degreeOf_taylorAgreementEquation_firstOrder_le center (chart f) (firstIndex top)
    taylorLength firstExponent exponent_sufficient (by fin_cases top <;> decide)
    ((chart_top f).trans ((degreeOf_le_index f).trans hJ)) _ _
private theorem nodeCut_vanishes {w : I → K} {f : Row 2} {S : K[X]}
    (hreg : RegularAt 1 f (extend S)) (hD : S.natDegree ≤ 133409) (i : I) :
    MvPolynomial.aeval (marked (extend S)) (nodeCut w f i) = 0 ↔
      S.eval (node i) = w i := by
  rw [nodeCut, chart_cut_agreement hreg (Polynomial.natDegree_map_le.trans hD),
    Polynomial.eval_map_apply, embed.injective.eq_iff]
private theorem factor_capacity {w Γ s} (h : Messages w Γ s) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top))
    (hreg : ∀ γ ∈ Γ, RegularAt 1 f (extend (s γ))) :
    NodeCapacity w Γ s
      (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (indexDegree f) (firstChartTotal top) (firstChartTop top)) := by
  classical
  let P := Ideal.span {plane f}
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (Γ : Set K) := by
    intro γ hγ η hη heq
    exact h.distinct hγ hη (Polynomial.map_injective embed embed.injective (marked_injective heq))
  have hxg : ∀ γ ∈ Γ, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hxe (γ : K) (hγ : γ ∈ Γ) (i : I) :
      MvPolynomial.aeval (x γ) (nodeCut w f i) = 0 ↔ (s γ).eval (node i) = w i :=
    nodeCut_vanishes (hreg γ hγ) (h.degree γ hγ) i
  refine ⟨Finset.univ.filter (fun i => nodeCut w f i ∈ P), ?_, ?_⟩
  · intro i hi γ hγ
    apply (hxe γ hγ i).mp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Finset.mem_filter.mp hi).2
    rw [hq, map_mul, hxg γ hγ, zero_mul]
  · intro i hi
    have hi' : nodeCut w f i ∉ P := by
      intro hh
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    let hits := Γ.filter fun γ => (s γ).eval (node i) = w i
    have hh : (hits.image x).card ≤ _ := capped_cut_card (by fin_cases top <;> decide : 0 < (firstChartTotal top))
      (by fin_cases top <;> decide : 0 < (firstChartTop top)) (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
      (plane_capped f) (nodeCut_capped w f hB hJ i) hi' (hits.image x) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
        exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
    rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hh
theorem first_order_cover {w Γ s} (h : Messages w Γ s)
    {n : ℕ} (f : Fin n → Row 2) (hf : FirstFactors top f)
    (hregular : ∀ γ ∈ Γ, ∃ i, RegularAt 1 (f i) (extend (s γ))) :
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ (firstWidth top) ∧
      C.totalCap ≤ (firstMixedBudget top) := by
  classical
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 1 (f i) (extend (s γ))
  let cap (i : Fin n) :=
    MvPolynomial.cappedDegreeMixedVolume (f i).totalDegree (indexDegree (f i)) (firstChartTotal top) (firstChartTop top)
  have hsub : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  have hlocal : ∀ i, NodeCapacity w (part i) s (cap i) := by
    intro i
    apply factor_capacity (h.mono (hsub i)) (f i) (hf.irreducible i) (hf.positive i)
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (f j).totalDegree)
        (Finset.mem_univ i)).trans hf.total
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
        (Finset.mem_univ i)).trans hf.index
    · exact fun γ hγ => (Finset.mem_filter.mp hγ).2
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi⟩ := hregular γ hγ
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hi⟩⟩
  · change n ≤ (firstWidth top)
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := Finset.sum_le_sum fun i _ =>
        (Nat.succ_le_of_lt (hf.positive i)).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      _ ≤ (firstWidth top) := hf.total
  · change (∑ i, cap i) ≤ (firstMixedBudget top)
    simp only [cap, MvPolynomial.cappedDegreeMixedVolume, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right (firstChartTop top) hf.total)
      (Nat.mul_le_mul_right ((firstChartTotal top) - (firstChartTop top)) hf.index)
end
end Low6960Leading
end
section
namespace Low6960Leading
noncomputable section
variable {top : Fin 15}
open P3 (K)
open Low6960Prices (Messages taylorLength lowerCap)
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (RegularAt NodeFamily mixed3)
open Low6960Leading (lowBox graphBox liftedBox FirstRow)
open Polynomial
open scoped BigOperators
def c1 (top : Fin 15) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) →
    Nonempty (ProperCover top w Γ s)
def c2 (top : Fin 15) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ Low6960Prices.lowerWidth top ∧ C.totalCap ≤ 133409 * Low6960Prices.lowerWidth top
private theorem roots_card_le {w Γ s} (h : Messages w Γ s) (u : Geom[X][X]) (hu : u ≠ 0)
    (hr : ∀ γ ∈ Γ, u.eval (extend (s γ)) = 0) :
    Γ.card ≤ u.natDegree := by
  classical
  let a : K → Geom[X] := fun γ => extend (s γ)
  have hinj : Set.InjOn a (Γ : Set K) :=
    fun _ hx _ hy heq => h.distinct hx hy (Polynomial.map_injective embed embed.injective heq)
  have hb : (Γ.image a).card ≤ u.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro b hb
    change b ∈ Γ.image a at hb
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hb
    exact (Polynomial.mem_roots hu).mpr (hr γ hγ)
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb
private theorem first_count {w Γ s} (h : Messages w Γ s)
    (q : Row 2) (hq : FirstRow top q) (hr : ∀ γ ∈ Γ, atJet q (extend (s γ)) = 0) :
    46418 * Γ.card ≤ 82317 * (firstMixedBudget top) + 46418 * ((firstWidth top) * (firstWidth top)) := by
  classical
  obtain ⟨n, f, u, hf, hu, hd, hc⟩ := Low6960LeadingFirst.proof q hq
  let ordinary := Γ.filter fun γ => u.eval (extend (s γ)) = 0
  let regular := Γ.filter fun γ => ∃ i, RegularAt 1 (f i) (extend (s γ))
  have hr₀ : ordinary.card ≤ (firstWidth top) * ((firstWidth top) - 1) :=
    (roots_card_le (h.mono (Finset.filter_subset _ _)) u hu
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C, hC, hn, hcap⟩ := first_order_cover (h.mono (Δ := regular) (Finset.filter_subset _ _)) f hf
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₁ := nodeFamily_count C (h.mono (Finset.filter_subset _ _))
  have hr₁' : 46418 * regular.card ≤ 82317 * C.totalCap + 46418 * C.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hC)).trans hr₁
  have covers : Γ ⊆ ordinary ∪ regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hreg⟩)
  have htotal := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  have hw : 1 ≤ firstWidth top := by fin_cases top <;> decide
  have hs : firstWidth top * (firstWidth top - 1) + firstWidth top =
      firstWidth top * firstWidth top := by
    calc
      _ = firstWidth top * (firstWidth top - 1) + firstWidth top * 1 := by rw [Nat.mul_one]
      _ = _ := by rw [← Nat.mul_add, Nat.sub_add_cancel hw]
  omega
private theorem proper_count {w Γ s} (C : ProperCover top w Γ s) (h : Messages w Γ s) :
    46418 * Γ.card ≤ 46418 * mixedBudget top + (82317 + 2 * 46418) * (invariantBudget top) := by
  classical
  have hm := nodeFamily_count C.multiple h
  have hi := nodeFamily_count C.invariant h
  have hc := (Finset.card_le_card C.cover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hmix := C.mixed
  have hf := C.fresh
  have hn := C.components
  omega
theorem of_children (h1 : c1 top) (h2 : c2 top) : Low6960Prices.c5 top := by
  classical
  intro w Γ s h g hg hr
  obtain ⟨n, f, q, hf, hq, hc⟩ := factor_cover g hg
  let first := Γ.filter fun γ => atJet q (extend (s γ)) = 0
  let proper := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)
  let whole := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  have hfirst := first_count (h.mono (Δ := first) (Finset.filter_subset _ _)) q hq
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hpmsg := h.mono (Δ := proper) (Finset.filter_subset _ _)
  obtain ⟨P⟩ := h1 w proper s hpmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hproper := proper_count P hpmsg
  have hwmsg := h.mono (Δ := whole) (Finset.filter_subset _ _)
  obtain ⟨W, hW, hn, hcap⟩ := h2 w whole s hwmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwhole : 46418 * whole.card ≤ 82317 * W.totalCap + 46418 * W.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hW)).trans (nodeFamily_count W hwmsg)
  have covers : Γ ⊆ first ∪ proper ∪ whole := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with hlow | ⟨i, hreg⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hlow⟩))
    by_cases hw : Whole (f i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩))
  have htotal := (Finset.card_le_card covers).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnumeric : 82317 * (firstMixedBudget top) + 46418 * ((firstWidth top) * (firstWidth top)) +
      (46418 * mixedBudget top + (82317 + 2 * 46418) * (invariantBudget top)) +
      (82317 * (133409 * Low6960Prices.lowerWidth top) + 46418 * Low6960Prices.lowerWidth top) ≤ 46418 * lowerCap top := by
    fin_cases top <;> decide
  omega
end
end Low6960Leading
end
