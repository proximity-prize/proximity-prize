import ProximityPrize.SubmissionLower.Scalar70LeadingPrice
import ProximityPrize.SubmissionLower.Fast076

set_option Elab.async false
set_option maxRecDepth 16000
set_option linter.unnecessarySeqFocus false
set_option autoImplicit true
section
namespace Scalar70LeadingLower
noncomputable section
variable {top : Fin 1}
open K1 (K I)
open Scalar70LeadingPrice (TrueWeightLE anchorCutoff taylorLength lowerWidth lowerIndex lowerTop)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily)
open K1_13 (Shape)
open scoped BigOperators Polynomial
abbrev lowBox : Shape := ⟨113, 35, 16⟩
abbrev graphBox (top : Fin 1) : Shape :=
  ⟨lowerWidth top, lowerIndex top + 1, min (lowerTop top + 1) ((lowerIndex top + 1) / 2)⟩
def liftedBox (top : Fin 1) (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowerIndex top + 2)
  ⟨1 + (L - 4) * lowerWidth top, j, min (1 + (L - 4) * (lowerTop top + 2)) (j / 2)⟩
def firstWidth (top : Fin 1) : ℕ :=
  max (lowerWidth top) ((2 * lowerTop top - 1) * lowerWidth top - lowerTop top ^ 2)
def firstIndex (top : Fin 1) : ℕ :=
  max (lowerIndex top) ((2 * lowerTop top - 1) * lowerIndex top - 2 * lowerTop top ^ 2)

structure FirstRow (top : Fin 1) (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ firstWidth top
  index : indexDegree q ≤ firstIndex top

structure FirstFactors (top : Fin 1) {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ firstWidth top
  index : (∑ i, indexDegree (f i)) ≤ firstIndex top

structure SecondFactors (top : Fin 1) {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ lowerWidth top
  index : (∑ i, indexDegree (f i)) ≤ lowerIndex top
  coordinate : (∑ i, (f i).degreeOf 2) ≤ lowerTop top
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)

-- Mixed volume coefficients in the support bounds of the contracted row.
def mixedCoefficients (_ : Fin 1) : ℕ × ℕ × ℕ :=
  (34599304434783, 155095547010366, 13004813764262)

def mixedBudget (top : Fin 1) : ℕ :=
  let (b, j, r) := mixedCoefficients top
  b * lowerWidth top + j * lowerIndex top + r * lowerTop top
def invariantBudget (top : Fin 1) : ℕ :=
  lowerWidth top * (1 + (2 * (taylorLength + 1) - 7) * (lowerWidth top - 1))
structure ProperCover (top : Fin 1) (w : I → K) (Γ : Finset K) (s : K → K[X]) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget top
  fresh : invariant.totalCap ≤ (invariantBudget top)
  components : multiple.n + invariant.n ≤ 2 * (invariantBudget top)
end
end Scalar70LeadingLower
end
section
namespace Scalar70LeadingLower_1
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator separant)
open Scalar70LeadingLower (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open Scalar70LeadingPrice (taylorLength physicalDegree)
open Scalar70LeadingLower (Whole mixedBudget)
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
structure LiftedChart (top : Fin 1) (f : Row 3) where
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
structure MixedSections (top : Fin 1) {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart top (f i)) where
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
end Scalar70LeadingLower_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Scalar70LeadingLower
noncomputable section
variable {top : Fin 1}
open K1 (I K node)
open Scalar70LeadingPrice (Messages)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 131071 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 131071 :=
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
    (hc : NodeCapacity w Γ s d) : 48367 * Γ.card ≤ 82706 * d + 48367 := by
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
  let a : ℕ := 179438 - persistent.card
  let b : ℕ := 131071 - persistent.card
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
  have hb : (b : ℤ) = x - 48367 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 131071 ≤ 179438))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 82706 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 131071 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 131071 ≤ 179438))]
    ring
  have hinc' : l * x ≤ (x + 82706) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 82706 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 82706 * (d : ℤ) < (l - 1) * 48367 := by
    have hc : 82706 * (d : ℤ) + 48367 < 48367 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 34339 * (d : ℤ) < (l - (d : ℤ)) * 48367 := by linarith only [hbad]
  have hden : 0 < 82706 * 48367 - 34339 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 34339)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 82706)
    have hpos : 0 < (l - (d : ℤ)) * (82706 * 48367 - 34339 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 131071 ≤ 179438) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hba hdenNat hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 82706 * 48367 ≤ (34339 * l + 48367) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 34339 * l + 48367 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 82706 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]
end
end Scalar70LeadingLower
end
section
namespace Scalar70LeadingLower_1
noncomputable section
variable {top : Fin 1}
open K1 (I K node)
open Scalar70LeadingPrice (Messages taylorLength physicalDegree)
open Scalar70LeadingLower (nodeCapacity_count)
open K1_13 (Geom embed extend)
open K1_13_5 (NodeCapacity)
open K1_13_5_4 (GeometricX GeoRow)
open Polynomial
open scoped BigOperators
end
end Scalar70LeadingLower_1
end
section
namespace Scalar70LeadingLower_1
noncomputable section
variable {top : Fin 1}
open Scalar70LeadingPrice (physicalDegree taylorLength)
open Scalar70LeadingLower (SecondFactors)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant)
open Scalar70LeadingLower (graphBox liftedBox)
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
end
end Scalar70LeadingLower_1
end
section
namespace Scalar70LeadingLower
noncomputable section
variable {top : Fin 1}
open K1_13 (Geom Row atJet jet indexDegree)
open K1_13_5 (RegularAt)
open Scalar70LeadingLower (FirstRow)
open K1_13_5_1
open Scalar70LeadingPrice (LowerRow TrueWeightLE physicalDegree anchorCutoff lowerWidth lowerIndex lowerTop)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open private coeff_flatten from ProximityPrize.SubmissionLower.Fast040
end
end Scalar70LeadingLower
end
namespace Scalar70LeadingFirst
noncomputable section
variable {top : Fin 1}
open K1_13 MvPolynomial UniqueFactorizationMonoid
open K1_13_5 (RegularAt)
open Scalar70LeadingLower (FirstRow FirstFactors firstWidth firstIndex)
open scoped BigOperators Polynomial
end
end Scalar70LeadingFirst

section
namespace Scalar70LeadingLower
noncomputable section
variable {top : Fin 1}
open K1 (I K node p)
open Scalar70LeadingPrice (Messages taylorLength)
open K1_13 (Row Geom embed extend indexDegree atJet)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open Scalar70LeadingLower (FirstFactors)
open K1_13_5_3 (CenterField toCenter constants center chart plane marked toCenter_inj
  marked_injective aeval_plane plane_ne_zero plane_prime chart_degree chart_top
  degreeOf_le_index mem_capped capped_cut_card)
open Polynomial PolynomialDifferential
open scoped BigOperators
open private eval_at_center specialization_flatten from ProximityPrize.SubmissionLower.Fast048
open K1_13_5_3 (flatten)
end
end Scalar70LeadingLower
end
section
namespace Scalar70LeadingLower
noncomputable section
variable {top : Fin 1}
open K1 (K)
open Scalar70LeadingPrice (Messages taylorLength lowerCap)
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (RegularAt NodeFamily mixed3)
open Scalar70LeadingLower (lowBox graphBox liftedBox FirstRow)
open Polynomial
open scoped BigOperators
end
end Scalar70LeadingLower
end
