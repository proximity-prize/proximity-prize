import ProximityPrize.SubmissionLower.PortLow4
set_option Elab.async false

section PackSource_P0_9_5Defs
set_option autoImplicit true
namespace P0_9_5
noncomputable section

open P0 (K I)
open P0_9 (TrueWeightLE anchorCutoff taylorLength)
open K1_13 (Row Shape indexDegree)
open K1_13_5 (NodeFamily lowBox liftedBox graphBox mixed3)
open scoped BigOperators Polynomial

/-- Additive caps on the distinct positive-top factors of the lower row. -/
structure SecondFactors {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ 120
  index : (∑ i, indexDegree (f i)) ≤ 48
  top : (∑ i, (f i).degreeOf 2) ≤ 24

/-- The first missing Hasse jet vanishes identically on the regular chart. -/
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)

def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a

def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))

abbrev firstExponent : ℕ := 2 * taylorLength - 5
abbrev firstChartTotal : ℕ := 1 + firstExponent * (5064 - 1)
abbrev firstChartTop : ℕ := min firstChartTotal (firstExponent * (1104 - 1) + taylorLength - 1)

def firstMixedBudget : ℕ :=
  5064 * firstChartTop + 1104 * (firstChartTotal - firstChartTop)

/-- Mixed intersections pay for isolated marks and twice the capacity of
multiple components. Fresh invariant curves have a separate degree budget. -/
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → K[X]) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget
  fresh : invariant.totalCap ≤ invariantBudget
  components : multiple.n + invariant.n ≤ 2 * invariantBudget

end
end P0_9_5
end PackSource_P0_9_5Defs

section PackSource_P0_9_5_1Defs
set_option autoImplicit true
namespace P0_9_5_1
noncomputable section
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator graphBox liftedBox separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open P0_9 (taylorLength physicalDegree)
open P0_9_5 (Whole mixedBudget)
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

/-- Only compatibility divisors on the separant open of proper factors. -/
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

/-- Use the geometric generic point length, not the set-theoretic degree. -/
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

/-- The support conditions use a common envelope. Only the first slot in
the mixed product retains the actual Newton polytope of each factor. -/
structure LiftedChart (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) graphBox 1
  cut_box : InLiftedBox cut (liftedBox (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S

/-- The last box bounds both proper point cuts and the degree of the
coefficient curve. The first cut keeps its full local length. -/
structure MixedSections {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q

/-- A coefficient curve consists of genuine polynomial solutions. The
polynomial identities are in an indeterminate independent of the coefficient field. -/
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0

end
end P0_9_5_1
end PackSource_P0_9_5_1Defs

section PackSource_P0_9_5Incidence
set_option autoImplicit true
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace P0_9_5
noncomputable section
open P0 (I K node)
open P0_9 (Messages)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators

theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 133551 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 133551 :=
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

/-- The fixed-word capacity lemma, with the agreement gap as a common denominator.
Under a hypothetical violation, the ordinary Johnson denominator on the
nonpersistent nodes is positive, so the pairwise-intersection theorem applies. -/
theorem nodeCapacity_count {w Γ s d} (h : Messages w Γ s)
    (hc : NodeCapacity w Γ s d) : 46657 * Γ.card ≤ 81936 * d + 46657 := by
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
  let a : ℕ := 180208 - persistent.card
  let b : ℕ := 133551 - persistent.card
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
  have hb : (b : ℤ) = x - 46657 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 133551 ≤ 180208))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 81936 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 133551 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 133551 ≤ 180208))]
    ring
  have hinc' : l * x ≤ (x + 81936) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 81936 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 81936 * (d : ℤ) < (l - 1) * 46657 := by
    have hc : 81936 * (d : ℤ) + 46657 < 46657 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 35261 * (d : ℤ) < (l - (d : ℤ)) * 46657 := by linarith only [hbad]
  have hden : 0 < 81936 * 46657 - 35261 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 35261)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 81936)
    have hpos : 0 < (l - (d : ℤ)) * (81936 * 46657 - 35261 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 133551 ≤ 180208) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hba hdenNat hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 81936 * 46657 ≤ (35261 * l + 46657) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 35261 * l + 46657 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 81936 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]

theorem nodeFamily_count {w Γ s} (C : NodeFamily w Γ s) (h : Messages w Γ s) :
    46657 * C.labels.card ≤ 81936 * C.totalCap + 46657 * C.n := by
  classical
  calc
    46657 * C.labels.card ≤ 46657 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46657 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (81936 * C.cap i + 46657) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 81936 * C.totalCap + 46657 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

end
end P0_9_5
end PackSource_P0_9_5Incidence

section PackSource_P0_9_5_1Capacity
set_option autoImplicit true
namespace P0_9_5_1
noncomputable section
open P0 (I K node)
open P0_9 (Messages taylorLength physicalDegree)
open P0_9_5 (nodeCapacity_count)
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
    MvPolynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]

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

/-- Linear sections of a prime coefficient curve give the local capacity.
A zero-dimensional image is also allowed. -/
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

/-- The fixed-word count for a positive-degree multiple component can be
paid inside the mixed bound, including its additive constant. -/
theorem curveCount_le_twice_degree {w Γ s} {d : ℕ} (h : Messages w Γ s) (hd : 0 < d)
    (hc : NodeCapacity w Γ s d) : Γ.card ≤ 2*d := by
  have hcount := nodeCapacity_count h hc
  omega

end
end P0_9_5_1
end PackSource_P0_9_5_1Capacity

section PackSource_P0_9_5Factor
set_option autoImplicit true
namespace P0_9_5

noncomputable section

open K1_13 (Geom Row atJet jet indexDegree)
open K1_13_5 (FirstRow RegularAt)
open K1_13_5_1
open P0_9 (LowerRow TrueWeightLE physicalDegree anchorCutoff)
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

/-- Factorwise second-order regular locus and a first-order resultant cover. -/
theorem factor_cover (g : Row 3) (hg : LowerRow g) :
    ∃ (n : ℕ) (f : Fin n → Row 3) (q : Row 2), SecondFactors f ∧ FirstRow q ∧
      ∀ S : Geom[X], atJet g S = 0 →
        atJet q S = 0 ∨ ∃ i, RegularAt 2 (f i) S := by
  classical
  obtain ⟨hg₀, hgt, hgi, hgw⟩ := hg
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
  have hc : ∑ a ∈ T, c a ≤ 24 := by
    have hbound : g.weightedTotalDegree (fun i => i.val) ≤ 48 :=
      (K1_13_1.indexDegree_eq g) ▸ hgi
    have h : 2 * (∑ a ∈ T, c a) ≤ 48 := calc
      _ = ∑ a ∈ T, (2 * c a) := Finset.mul_sum T c 2
      _ ≤ ∑ a ∈ T, a.weightedTotalDegree (fun i => i.val) := by
        apply Finset.sum_le_sum
        intro a _
        exact (Nat.le_add_left _ _).trans (view_coeff_weight (fun i => i.val) a (c a) le_rfl)
      _ ≤ _ := (hsum _).trans hbound
    omega
  have he₀ (a : Row 3) (ha : a ∈ T) : elimination a ≠ 0 := by
    have hca : c a ≤ 24 := (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) ha).trans hc
    exact elimination_ne_zero (hirr a ha) (hca.trans_lt (by decide))
  have hq (w : Fin 3 → ℕ) (B : ℕ) (hb : g.weightedTotalDegree w ≤ B)
      (hB : w 2 * 24 ≤ B) :
      q.weightedTotalDegree (fun i => w i.castSucc) ≤ 47 * B - w 2 * 24 ^ 2 := by
    let v : Fin 2 → ℕ := fun i => w i.castSucc
    rw [show q = ∏ a ∈ T, elimination a from rfl, weightedTotalDegree_prod v T _ he₀]
    apply aggregate T (fun a => a.weightedTotalDegree w) c
      (fun a => (elimination a).weightedTotalDegree v) B (w 2) ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (view_coeff_weight w a (c a) le_rfl)
    · intro a _ ha
      exact elimination_weight_zero w a ha
    · intro a _ ha
      exact elimination_weight_positive w a ha
  have hqtotal : q.totalDegree ≤ 5064 := by
    have h := hq (1 : Fin 3 → ℕ) 120 (by simpa only [weightedTotalDegree_one] using hgt) (by decide)
    change q.weightedTotalDegree (1 : Fin 2 → ℕ) ≤ 5064 at h
    simpa only [weightedTotalDegree_one] using h
  have hqindex : indexDegree q ≤ 1104 := by
    rw [K1_13_1.indexDegree_eq] at hgi ⊢
    exact hq (fun i => i.val) 48 hgi (by decide)
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
      (∑ a ∈ T, a.totalDegree) ≤ g.totalDegree).trans hgt)
  · exact (hsub _).trans ((by simpa only [← K1_13_1.indexDegree_eq] using hsum (fun i => i.val) :
      (∑ a ∈ T, indexDegree a) ≤ indexDegree g).trans hgi)
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

end P0_9_5
end PackSource_P0_9_5Factor

section PackSource_P0_9_5First
set_option autoImplicit true
namespace P0_9_5
noncomputable section

open P0 (I K node)
open P0_9 (Messages taylorLength)
open K1_13 (Row Geom embed extend indexDegree atJet)
open K1_13_5 (RegularAt NodeCapacity NodeFamily FirstFactors)
open K1_13_5_3 (CenterField toCenter constants center chart plane marked toCenter_inj
  marked_injective aeval_plane plane_ne_zero plane_prime chart_degree chart_top
  degreeOf_le_index mem_capped capped_cut_card)
open Polynomial PolynomialDifferential
open scoped BigOperators

open private eval_at_center specialization_flatten from ProximityPrize.SubmissionLower.Fast048
open K1_13_5_3 (flatten)

private theorem exponent_sufficient : TaylorExponentSufficient 1 taylorLength firstExponent := by
  exact taylorExponentSufficient_firstOrder_tight 133551

private theorem chart_cut_agreement {f : Row 2} {S : Geom[X]} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 133551) (x y : Geom) :
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
    have hb : (S.map constants).natDegree ≤ 133551 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom P0.p := charP_of_injective_ringHom embed.injective P0.p
  have : CharP CenterField P0.p := charP_of_injective_ringHom constants.injective P0.p
  have hpiv : ∀ i : ℕ, 1 < i → i < taylorLength → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField P0.p i).mp hz)
    change 2130706433 ≤ i at hp
    change i < 133552 at ht
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
    (hB : f.totalDegree ≤ 5064) (hJ : indexDegree f ≤ 1104) (i : I) :
    nodeCut w f i ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      firstChartTotal firstChartTop := by
  have ht : (nodeCut w f i).totalDegree ≤ firstChartTotal := by
    refine (totalDegree_taylorAgreementEquation_le center (chart f)
      exponent_sufficient _ _).trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_left firstExponent
      (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1
  refine mem_capped _ ht (le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans ht) ?_)
  exact degreeOf_taylorAgreementEquation_firstOrder_le center (chart f) 1104
    taylorLength firstExponent exponent_sufficient (by decide)
    ((chart_top f).trans ((degreeOf_le_index f).trans hJ)) _ _

private theorem nodeCut_vanishes {w : I → K} {f : Row 2} {S : K[X]}
    (hreg : RegularAt 1 f (extend S)) (hD : S.natDegree ≤ 133551) (i : I) :
    MvPolynomial.aeval (marked (extend S)) (nodeCut w f i) = 0 ↔
      S.eval (node i) = w i := by
  rw [nodeCut, chart_cut_agreement hreg (Polynomial.natDegree_map_le.trans hD),
    Polynomial.eval_map_apply, embed.injective.eq_iff]

/-- The generic first-order curve of a single factor supplies a node capacity. -/
private theorem factor_capacity {w Γ s} (h : Messages w Γ s) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1)
    (hB : f.totalDegree ≤ 5064) (hJ : indexDegree f ≤ 1104)
    (hreg : ∀ γ ∈ Γ, RegularAt 1 f (extend (s γ))) :
    NodeCapacity w Γ s
      (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (indexDegree f) firstChartTotal firstChartTop) := by
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
    have hh : (hits.image x).card ≤ _ := capped_cut_card (by decide : 0 < firstChartTotal)
      (by decide : 0 < firstChartTop) (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
      (plane_capped f) (nodeCut_capped w f hB hJ i) hi' (hits.image x) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
        exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
    rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hh

/-- The first-order regular factors give a cover with the mixed-area capacity budget. -/
theorem first_order_cover {w Γ s} (h : Messages w Γ s)
    {n : ℕ} (f : Fin n → Row 2) (hf : FirstFactors f)
    (hregular : ∀ γ ∈ Γ, ∃ i, RegularAt 1 (f i) (extend (s γ))) :
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ 5064 ∧
      C.totalCap ≤ firstMixedBudget := by
  classical
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 1 (f i) (extend (s γ))
  let cap (i : Fin n) :=
    MvPolynomial.cappedDegreeMixedVolume (f i).totalDegree (indexDegree (f i)) firstChartTotal firstChartTop
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
  · change n ≤ 5064
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := Finset.sum_le_sum fun i _ =>
        (Nat.succ_le_of_lt (hf.positive i)).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      _ ≤ 5064 := hf.total
  · change (∑ i, cap i) ≤ firstMixedBudget
    simp only [cap, MvPolynomial.cappedDegreeMixedVolume, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right firstChartTop hf.total)
      (Nat.mul_le_mul_right (firstChartTotal - firstChartTop) hf.index)


end
end P0_9_5
end PackSource_P0_9_5First

section PackSource_P0_9_5Split
set_option autoImplicit true
namespace P0_9_5
noncomputable section

open P0 (K)
open P0_9 (Messages taylorLength)
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (FirstRow RegularAt NodeFamily mixed3 lowBox graphBox liftedBox)
open Polynomial
open scoped BigOperators

/-- Proper compatibility cuts, with their mixed and fresh-curve budgets. -/
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) →
    Nonempty (ProperCover w Γ s)

/-- Whole compatibility charts give coefficient surfaces with node capacity. -/
def c2 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ 120 ∧ C.totalCap ≤ 133551 * 120

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
    (q : Row 2) (hq : FirstRow q) (hr : ∀ γ ∈ Γ, atJet q (extend (s γ)) = 0) :
    46657 * Γ.card ≤ 81936 * firstMixedBudget + 46657 * (5064 * 5064) := by
  classical
  obtain ⟨n, f, u, hf, hu, hd, hc⟩ := K1_13_5_2.proof q hq
  let ordinary := Γ.filter fun γ => u.eval (extend (s γ)) = 0
  let regular := Γ.filter fun γ => ∃ i, RegularAt 1 (f i) (extend (s γ))
  have hr₀ : ordinary.card ≤ 5064 * (5064 - 1) :=
    (roots_card_le (h.mono (Finset.filter_subset _ _)) u hu
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C, hC, hn, hcap⟩ := first_order_cover (h.mono (Δ := regular) (Finset.filter_subset _ _)) f hf
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₁ := nodeFamily_count C (h.mono (Finset.filter_subset _ _))
  have hr₁' : 46657 * regular.card ≤ 81936 * C.totalCap + 46657 * C.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hC)).trans hr₁
  have covers : Γ ⊆ ordinary ∪ regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hreg⟩)
  have htotal := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  omega

private theorem proper_count {w Γ s} (C : ProperCover w Γ s) (h : Messages w Γ s) :
    46657 * Γ.card ≤ 46657 * mixedBudget + (81936 + 2 * 46657) * invariantBudget := by
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

private theorem firstMixedBudget_eq : firstMixedBudget = 2660148992832 := rfl

private theorem invariantBudget_eq : invariantBudget = 3814173840 := rfl

private theorem mixedBudget_eq : mixedBudget = 18474880859443656 := by
  have hxy : mixed3 lowBox (liftedBox (taylorLength + 1)) (liftedBox (taylorLength + 2)) =
      6206745694646832 := rfl
  have hgy : mixed3 lowBox graphBox (liftedBox (taylorLength + 2)) = 45930525288 := rfl
  have hgx : mixed3 lowBox graphBox (liftedBox (taylorLength + 1)) = 45930181368 := rfl
  change mixed3 lowBox (liftedBox (taylorLength + 1)) (liftedBox (taylorLength + 2)) +
    (taylorLength - 1) * mixed3 lowBox graphBox (liftedBox (taylorLength + 2)) +
    taylorLength * mixed3 lowBox graphBox (liftedBox (taylorLength + 1)) = _
  rw [hxy, hgy, hgx]
  rfl

theorem of_children (h1 : c1) (h2 : c2) : P0_9.c5 := by
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
  have hwhole : 46657 * whole.card ≤ 81936 * W.totalCap + 46657 * W.n :=
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
  have hnumeric : 81936 * firstMixedBudget + 46657 * (5064 * 5064) +
      (46657 * mixedBudget + (81936 + 2 * 46657) * invariantBudget) +
      (81936 * (133551 * 120) + 46657 * 120) ≤ 46657 * 18479565405033887 := by
    rw [firstMixedBudget_eq, mixedBudget_eq, invariantBudget_eq]
    change 862367399191311339816 ≤ 862367399191311370742
    decide
  omega

end
end P0_9_5
end PackSource_P0_9_5Split

section PackSource_P0_9_5_1Split
set_option autoImplicit true
namespace P0_9_5_1
noncomputable section
open P0 (I K)
open P0_9 (Messages taylorLength physicalDegree)
open P0_9_5 (ProperCover SecondFactors Whole mixedBudget invariantBudget)
open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily separant)
open K1_13_5_4 (GeometricX GeoRow genericRow genericCoeff genericCoeff_injective
  jetPoint regularLocus eval_genericRow_at_point jetPoint_injOn)
open Polynomial
open scoped BigOperators

/-- Lifted Taylor support, comparison with the ordinary compatibility
numerators, and recognition of actual polynomial messages. -/
def c1 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ i, Nonempty (LiftedChart (f i))

/-- The simultaneous last-section degree budget with the compatibility
multiplicity retained on each divisor. -/
def c2 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ T : ∀ i, LiftedChart (f i),
    Nonempty (MixedSections f T)

/-- At a simple tangent-invariant divisor, integration gives a genuine
coefficient curve through all its marked polynomial trajectories. -/
def c3 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ a ∈ properComponents f,
    SimpleInvariant (f a.1) a.2 →
    ∃ Q : CoefficientIdeal, ActualSolutionCurve (f a.1) Q ∧
      ∀ S : Geom[X], S.natDegree ≤ physicalDegree → jetPoint S ∈ regularLocus (f a.1) a.2 →
        coefficientPoint S ∈ MvPolynomial.zeroLocus GeometricX Q

/-- The proper divisor at an independent abscissa bounds the sum of the
degrees of distinct genuine solution curves. -/
def c4 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ i, (oldCut (f i)).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * ((f i).totalDegree - 1)) →
    ∀ C : Finset CoefficientIdeal,
      (∀ Q ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q) →
      ∃ d : CoefficientIdeal → ℕ,
        (∀ Q ∈ C, 0 < d Q ∧ MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) ∧
          (∑ Q ∈ C, d Q) ≤ invariantBudget

private theorem exists_properComponent {n : ℕ} {f : Fin n → Row 3}
    (T : ∀ i, LiftedChart (f i)) {i : Fin n} {S : Geom[X]}
    (hS : S.natDegree ≤ physicalDegree) (hr : RegularAt 2 (f i) S) (hw : ¬ Whole (f i)) :
    ∃ P, (i, P) ∈ properComponents f ∧ jetPoint S ∈ regularLocus (f i) P := by
  have hzero : jetPoint S ∈ MvPolynomial.zeroLocus GeometricX (oldCutIdeal (f i)) := by
    apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
    apply Ideal.span_le.mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    change g ∈ RingHom.ker (MvPolynomial.aeval (jetPoint S))
    rw [RingHom.mem_ker]
    change MvPolynomial.eval (jetPoint S) g = 0
    rcases hg with rfl | rfl
    · rw [eval_genericRow_at_point, hr.1, map_zero]
    · rw [eval_genericRow_at_point, (T i).actual S hS hr |>.1, map_zero]
  have hsep : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := by
    rw [eval_genericRow_at_point]
    exact fun h => hr.2 ((map_eq_zero_iff genericCoeff genericCoeff_injective).mp h)
  obtain ⟨P, hP, hy⟩ := MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus
    (oldCutIdeal (f i)) (genericRow (separant (f i))) (jetPoint S) hzero hsep
  exact ⟨P, mem_properComponents.mpr ⟨hw, hP⟩, ⟨hy, hsep⟩⟩

private def componentMarks {n : ℕ} (f : Fin n → Row 3)
    (Γ : Finset K) (s : K → K[X]) (a : CurveIndex n) : Finset K := by
  classical
  exact Γ.filter fun γ => jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2

private theorem mem_componentMarks {n : ℕ} {f : Fin n → Row 3} {Γ : Finset K}
    {s : K → K[X]} {a : CurveIndex n} {γ : K} : γ ∈ componentMarks f Γ s a ↔
    γ ∈ Γ ∧ jetPoint (extend (s γ)) ∈ regularLocus (f a.1) a.2 := by
  classical
  exact Finset.mem_filter

private theorem regular_of_componentMark {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n}
    {S : Geom[X]} (ha : a ∈ properComponents f) (hS : jetPoint S ∈ regularLocus (f a.1) a.2) :
    RegularAt 2 (f a.1) S := by
  have hp := (Ideal.mem_retainedMinimalPrimes.mp (mem_properComponents.mp ha).2).1.le
  have hz : genericRow (f a.1) ∈ oldCutIdeal (f a.1) := Ideal.subset_span (by simp)
  have he : MvPolynomial.eval (jetPoint S) (genericRow (f a.1)) = 0 :=
    hS.1 _ (hp hz)
  have hsep := hS.2
  rw [eval_genericRow_at_point] at he hsep
  refine ⟨?_, fun h => hsep (by rw [show atJet (separant (f a.1)) S = 0 from h, map_zero])⟩
  exact (map_eq_zero_iff genericCoeff genericCoeff_injective).mp he

private theorem mixedComponent_card {w Γ s n f} (hm : Messages w Γ s)
    {T : ∀ i, LiftedChart (f i)} (M : MixedSections (n := n) f T)
    {a : CurveIndex n} (ha : a ∈ properComponents f) (hi : ¬ SimpleInvariant (f a.1) a.2) :
    (componentMarks f Γ s a).card ≤ M.length a * M.degree a := by
  classical
  have hsub : componentMarks f Γ s a ⊆ Γ := fun _ hg => (mem_componentMarks.mp hg).1
  have hdeg (γ : K) (hγ : γ ∈ Γ) : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
  by_cases hlen : M.length a = 1
  · have hsimp : componentLength (f a.1) a.2 = 1 := by rw [← M.length_eq a ha, hlen, Nat.cast_one]
    have hn : genericRow (oldNext (f a.1)) ∉ a.2 := fun hn => hi ⟨hsimp, hn⟩
    obtain ⟨hfinite, hcard⟩ := M.points a ha hn
    let pt := fun γ => jetPoint (n := 3) (extend (s γ))
    have hpts : ↑((componentMarks f Γ s a).image pt) ⊆ nextCutLocus (f a.1) a.2 := by
      intro y hy
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      exact ⟨hy, by rw [eval_genericRow_at_point, ((T a.1).actual _ (hdeg γ hmem) hreg).2.1, map_zero]⟩
    have hle := (Set.ncard_le_ncard hpts hfinite).trans hcard
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn ((jetPoint_injOn s Γ hm.distinct).mono hsub)] at hle
    simpa [hlen] using hle
  · have htwo : 2 ≤ M.length a := by have := M.length_pos a ha; omega
    obtain ⟨Q, hprime, hdim, hd, hdegree, hrec⟩ := M.curves a ha htwo
    have hm' := hm.mono hsub
    have hcap := nodeCapacity_of_coefficient_curve hm' Q hprime hdim hdegree (by
      intro γ hγ
      obtain ⟨hmem, hy⟩ := mem_componentMarks.mp hγ
      have hreg := regular_of_componentMark ha hy
      rw [← ((T a.1).actual _ (hdeg γ hmem) hreg).2.2]
      exact hrec _ hy)
    exact (curveCount_le_twice_degree hm' hd hcap).trans (Nat.mul_le_mul_right _ htwo)

private def coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ)
    (hcut : ∀ Q ∈ C, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) : NodeFamily w Γ s := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  let part : Fin C.card → Finset K := fun i => Γ.filter fun γ =>
    coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  have hs : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  refine ⟨C.card, part, fun i => d (e i).val, hs, ?_⟩
  intro i
  obtain ⟨hp, hdim, hd⟩ := hcut (e i).val (e i).property
  exact nodeCapacity_of_coefficient_curve (hm.mono (hs i)) (e i).val hp hdim hd
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)

private theorem coefficientFamily_total {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) :
    (coefficientFamily hm C d hcut).totalCap = ∑ Q ∈ C, d Q := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  change (∑ i : Fin C.card, d (e i).val) = ∑ Q ∈ C, d Q
  rw [Equiv.sum_comp e (fun P : C => d P.val), Finset.sum_coe_sort]

private theorem mem_coefficientFamily {w Γ s} (hm : Messages w Γ s)
    (C : Finset CoefficientIdeal) (d : CoefficientIdeal → ℕ) (hcut) {γ : K} (hγ : γ ∈ Γ)
    {Q : CoefficientIdeal} (hQ : Q ∈ C)
    (hy : coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    γ ∈ (coefficientFamily hm C d hcut).labels := by
  classical
  let e : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  rw [NodeFamily.labels]
  let i := e.symm ⟨Q, hQ⟩
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, ?_⟩⟩
  change coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX (e i).val
  simpa [i] using hy

private def emptyFamily (w : I → K) (Γ : Finset K) (s : K → K[X]) : NodeFamily w Γ s where
  n := 0
  part := Fin.elim0
  cap := Fin.elim0
  sub i := Fin.elim0 i
  localCapacity i := Fin.elim0 i

/-- The simple invariant branches use fresh degree. Every other component
spends its actual label count from the mixed budget. -/
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : P0_9_5.c1 := by
  classical
  intro w Γ s hm n f hf marks
  let T (i : Fin n) := Classical.choice (h1 n f hf i)
  obtain ⟨M⟩ := h2 n f hf T
  let direct := (properComponents f).filter fun a => ¬ SimpleInvariant (f a.1) a.2
  let isolated := direct.biUnion (componentMarks f Γ s)
  have hmixed : isolated.card ≤ mixedBudget := by
    calc
      _ ≤ ∑ a ∈ direct, (componentMarks f Γ s a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ direct, M.length a * M.degree a := Finset.sum_le_sum fun a ha =>
        mixedComponent_card hm M (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a ∈ properComponents f, M.length a * M.degree a :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ _ := M.total
  let stable := (properComponents f).filter fun a => SimpleInvariant (f a.1) a.2
  have heach (a : stable) := h3 n f hf a.val (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp a.property).2
  choose Q hQ hrec using heach
  let C := stable.attach.image Q
  have hfresh : ∀ P ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) P := by
    intro P hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    have ha := (Finset.mem_filter.mp a.property).1
    exact ⟨a.val.1, (mem_properComponents.mp ha).1, hQ a⟩
  obtain ⟨d, hd, hsum⟩ := h4 n f hf (fun i => ordinary_bound (f i)) C hfresh
  have hcut (P : CoefficientIdeal) (hp : P ∈ C) : P.IsPrime ∧
      (MvPolynomial.affineHilbertPolynomial P).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree P ≤ (d P : ℚ) := by
    obtain ⟨i, _, h⟩ := hfresh P hp
    exact ⟨h.prime, h.dimension.le, (hd P hp).2⟩
  let F := coefficientFamily hm C d hcut
  have hFnum : F.n ≤ invariantBudget := by
    calc
      F.n = ∑ P ∈ C, 1 := Finset.card_eq_sum_ones C
      _ ≤ ∑ P ∈ C, d P := Finset.sum_le_sum fun P hp => (hd P hp).1
      _ ≤ _ := hsum
  refine ⟨⟨isolated, emptyFamily w Γ s, F, ?_, ?_, ?_, ?_⟩⟩
  · intro γ hγ
    obtain ⟨i, hi, hw⟩ := marks γ hγ
    have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
      simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
    obtain ⟨P, hp, hy⟩ := exists_properComponent T hdeg hi hw
    by_cases hs : SimpleInvariant (f i) P
    · let a : stable := ⟨(i, P), Finset.mem_filter.mpr ⟨hp, hs⟩⟩
      have hQC : Q a ∈ C := Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_union_right _ (mem_coefficientFamily hm C d hcut hγ hQC
        (hrec a _ hdeg hy))
    · have hγiso : γ ∈ isolated := Finset.mem_biUnion.mpr
        ⟨(i,P), Finset.mem_filter.mpr ⟨hp, hs⟩, mem_componentMarks.mpr ⟨hγ, hy⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hγiso)
  · have hz : (emptyFamily w Γ s).totalCap = 0 := by
      change (∑ i : Fin 0, (Fin.elim0 i : ℕ)) = 0
      exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
    simpa [hz] using hmixed
  · exact (coefficientFamily_total hm C d hcut).trans_le hsum
  · change 0 + F.n ≤ 2 * invariantBudget
    omega

end
end P0_9_5_1
end PackSource_P0_9_5_1Split

section PackSource_P0_9_5_1_1Proof
set_option autoImplicit true
namespace P0_9_5_1_1
noncomputable section

open P0_9 (physicalDegree taylorLength)
open P0_9_5 (SecondFactors)
open P0_9_5_1 (LiftedChart coefficientPoint reconstruct oldCut oldNext)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial

open private mul_bound K1_13_5_4_1_1.partialFlow_bound liftSep_eq liftedStep_bound generic_bound
  totalWeight indexWeight topWeight heightWeight lift_weight fits fits_lifted
  from ProximityPrize.SubmissionLower.Fast070
open private represents from ProximityPrize.SubmissionLower.Fast076
open private atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero
  actual_zero_of_represents from ProximityPrize.SubmissionLower.Fast048

local notation "W" => weightedTotalDegree

/-- At length m every Hasse jet uses the common separant power m - 4. -/
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

/-- The four weights give the lifted boxes for every sufficiently long Taylor space. -/
private theorem support (m : ℕ) (hm : 4 ≤ m) (f : Row 3)
    (hb : f.totalDegree ≤ 120) (hj : indexDegree f ≤ 48) (ht : f.degreeOf 2 ≤ 24) :
    InLiftedBox (graph f) graphBox 1 ∧
    InLiftedBox (cut m f) (liftedBox (m + 1)) (m - 1) ∧
    InLiftedBox (next m f) (liftedBox (m + 2)) m ∧
    ∀ i, InLiftedBox (coefficientNumerator m f i) (liftedBox m) (m - 2) := by
  have htotal : W totalWeight (liftRaw f) ≤ 120 := by
    rw [lift_weight, show totalWeight ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_one]
    exact hb
  have hindex : W indexWeight (liftRaw f) ≤ 48 := by
    rw [lift_weight, show indexWeight ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have htop : W topWeight (liftRaw f) ≤ 24 := by
    rw [lift_weight, show topWeight ∘ Fin.castSucc = Pi.single (2 : Fin 3) 1 from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_piSingle]
    exact ht
  have hheight : W heightWeight (liftRaw f) ≤ 0 := by
    rw [lift_weight, show heightWeight ∘ Fin.castSucc = (0 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree, Finset.sup_le_iff]
    intro a _
    simp [Finsupp.weight_eq_sum]
  obtain ⟨bg, bn, bc⟩ := weight_bounds totalWeight 120 0 120 1 m htotal
    (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨jg, jn, jc⟩ := weight_bounds indexWeight 48 1 50 2 m hindex
    (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨tg, tn, tc⟩ := weight_bounds topWeight 24 1 26 1 m htop
    (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨hg, hn, hc⟩ := weight_bounds heightWeight 0 1 1 1 m hheight
    (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> decide)
  refine ⟨fits bg jg tg hg, ?_, ?_, ?_⟩
  · rw [show m - 1 = m + 1 - 2 by omega]
    exact fits_lifted _ ((bn (m - 3)).trans (by change 0 + _ ≤ _; omega))
      ((jn (m - 3)).trans (by change 0 + _ ≤ _; omega))
      ((tn (m - 3)).trans (by change 0 + _ ≤ _; omega))
      ((hn (m - 3)).trans (by change 1 + _ ≤ _; omega))
  · have hh : m + 2 - 2 = m := by omega
    simpa only [hh, next] using fits_lifted (m + 2) ((bn (m - 2)).trans (by change 0 + _ ≤ _; omega))
      ((jn (m - 2)).trans (by change 0 + _ ≤ _; omega))
      ((tn (m - 2)).trans (by change 0 + _ ≤ _; omega))
      ((hn (m - 2)).trans (by change 1 + _ ≤ _; omega))
  · intro i
    exact fits_lifted _ (bc i) (jc i) (tc i) ((hc i).trans (by omega))

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

theorem proof : P0_9_5_1.c1 := by
  intro n f hf i
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.top
  obtain ⟨hg, he, hn, hc⟩ := support taylorLength (by decide) (f i) hb hj ht
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
end P0_9_5_1_1
end PackSource_P0_9_5_1_1Proof

section PackSource_P0_9_5_1_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5 (graphBox liftedBox separant)
open K1_13_5_4 (InLiftedBox GeoRow GeometricX genericRow)
open K1_13_5_4_2 (JetPoint ExponentSpace boxExponents graphLocus graphCurve capBody mixedVolume4)
open P0_9 (taylorLength)
open P0_9_5 (Whole)
open P0_9_5_1 (oldCutIdeal)
open MvPolynomial

def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))

abbrev lastBox := liftedBox (taylorLength + 2)
abbrev lastExponents := boxExponents lastBox taylorLength
abbrev lastMap := monomialMap GeometricX lastExponents

def sectionIdeal (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial lastExponents GeometricX) :=
  (graphCurve f P).comap lastMap

def IsSectionCurve (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  (sectionIdeal f P).IsPrime ∧ (affineHilbertPolynomial (sectionIdeal f P)).natDegree = 1

/-- Ordinary affine degree in the coordinates of the full last-box monomial system. -/
def sectionDegree (f : Row 3) (P : Ideal (GeoRow 3)) : ℚ :=
  affineDegree (sectionIdeal f P)

structure GenericSection (f : Row 3) where
  polynomial : GeoRow 4
  support : InLiftedBox polynomial lastBox taylorLength
  points : Ideal (GeoRow 3) → Finset JetPoint
  card_eq : ∀ P ∈ factorCurves f, ((points P).card : ℚ) = sectionDegree f P
  proper : ∀ P ∈ factorCurves f, polynomial ∉ graphCurve f P
  roots : ∀ P ∈ factorCurves f, ∀ y ∈ points P,
    y ∈ graphLocus f P ∧ eval y polynomial = 0
  off_other_curves : ∀ P ∈ factorCurves f, ∀ P' ∈ factorCurves f, P ≠ P' →
    ∀ y ∈ points P, y ∉ graphLocus f P'

def lastMixedVolume (first : Set ExponentSpace) : ℝ :=
  mixedVolume4 ![first, capBody graphBox 1,
    capBody (liftedBox (taylorLength + 1)) (taylorLength - 1),
    capBody lastBox taylorLength]

end
end P0_9_5_1_2
end PackSource_P0_9_5_1_2Defs

section PackSource_P0_9_5_1_2Geometry
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2
noncomputable section
open K1_13 (Row Geom Shape)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericCoeff_injective genericRow
  liftRow regularLocus graphPoint)
open K1_13_5_4_2 (boxExponents graphCurve eval_represents_iff)
open P0_9 (taylorLength)
open P0_9_5 (Whole)
open P0_9_5_1 (oldCut oldCutIdeal properComponents CurveIndex componentLength nextCutLocus
  oldNext LiftedChart)
open MvPolynomial RingTheory.Sequence
open scoped BigOperators Polynomial

open private quotient_regular_iff graph_dimension from ProximityPrize.SubmissionLower.Fast048
open private graphPoint_injective from ProximityPrize.SubmissionLower.Fast048
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mem_factorCurves {f : Row 3} {P : Ideal (GeoRow 3)} :
    P ∈ factorCurves f ↔ ¬ Whole f ∧
      P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) := by
  classical
  by_cases hf : Whole f <;> simp [factorCurves, hf]

theorem properComponents_eq {n : ℕ} (f : Fin n → Row 3) :
    properComponents f = Finset.univ.biUnion fun i =>
      (factorCurves (f i)).image (fun P => (i, P)) := by
  classical
  unfold properComponents
  congr 1
  funext i
  by_cases hf : Whole (f i) <;> simp [factorCurves, hf]

theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {a : CurveIndex n} :
    a ∈ properComponents f ↔ a.2 ∈ factorCurves (f a.1) := by
  classical
  rcases a with ⟨i, P⟩
  rw [properComponents_eq]
  simp

theorem sum_properComponents {n : ℕ} (f : Fin n → Row 3) (v : CurveIndex n → ℕ) :
    (∑ a ∈ properComponents f, v a) =
      ∑ i, ∑ P ∈ factorCurves (f i), v (i, P) := by
  classical
  rw [properComponents_eq, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨Q, _, he⟩ := Finset.mem_image.mp hb
    exact hij (Prod.mk.inj he).1.symm

theorem componentLength_of_retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    0 < componentLength f P ∧ componentLength f P < ⊤ := by
  classical
  have hm := (Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1
  have hp : P.IsPrime := hm.isPrime
  rw [componentLength, dite_eq_left hp]
  let A := Localization.AtPrime P
  let L := (oldCutIdeal f).map (algebraMap (GeoRow 3) A)
  have hle : L ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.map_le_iff_le_comap.mpr
    change oldCutIdeal f ≤ (IsLocalRing.maximalIdeal A).under (GeoRow 3)
    rw [IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hm.le
  have hL : L ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  let : Nontrivial (A ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  exact ⟨Module.length_pos, K1_13_5_4_2.localLength_lt_top hm⟩

theorem componentLength_toNat {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    ((componentLength f P).toNat : ℕ∞) = componentLength f P :=
  ENat.natCast_toNat (componentLength_of_retained hP).2.ne

theorem componentLength_toNat_pos {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) : 0 < (componentLength f P).toNat := by
  have h := (componentLength_of_retained hP).1
  rw [← componentLength_toNat hP] at h
  exact_mod_cast h

private theorem single_mem_box (s : Shape) (h : ℕ)
    (hb : 1 ≤ s.b) (hj : 2 ≤ s.j) (ht : 1 ≤ s.t) (hh : 1 ≤ h)
    (i : Fin 4) : Finsupp.single i 1 ∈ boxExponents s h := by
  change (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 + (Finsupp.single i 1) 2 ≤
    s.b ∧ (Finsupp.single i 1) 1 + 2 * (Finsupp.single i 1) 2 ≤ s.j ∧
    (Finsupp.single i 1) 2 ≤ s.t ∧ (Finsupp.single i 1) 3 ≤ h
  fin_cases i <;> norm_num [Finsupp.single_apply] <;> omega

theorem lastExponents_single (i : Fin 4) : Finsupp.single i 1 ∈ lastExponents :=
  single_mem_box lastBox taylorLength
    (show 1 ≤ 16026001 by decide) (show 2 ≤ 6677502 by decide)
    (show 1 ≤ 3338751 by decide) (show 1 ≤ 133552 by decide) i

/-- The proper cutter remains regular modulo the hypersurface after scalar extension. -/
private theorem cut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span {genericRow f}) (genericRow (oldCut f))) := by
  let : Algebra Geom[X] GeometricX := genericCoeff.toAlgebra
  have : Module.IsTorsionFree (Geom[X]) GeometricX :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr genericCoeff_injective
  have : Module.Flat (Geom[X]) GeometricX := inferInstance
  have hbase : IsBaseChange (Row 3)
      (IsScalarTower.toAlgHom (Geom[X]) GeometricX (GeoRow 3)).toLinearMap :=
    Algebra.IsPushout.out
  have : Module.Flat (Row 3) (GeoRow 3) :=
    Module.Flat.isBaseChange (R := Geom[X]) (S := Row 3) (M := GeometricX)
      (N := GeoRow 3) hbase
  have : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  have hseq : IsWeaklyRegular (Row 3) [f, oldCut f] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff]
    exact ⟨fun _ _ h => mul_left_cancel₀ hf.ne_zero h,
      fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h⟩
  have h := hseq.of_flat (S := GeoRow 3)
  change IsWeaklyRegular (GeoRow 3) [genericRow f, genericRow (oldCut f)] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff] at h
  exact h.2

/-- First cut the affine three-space by the factor and then cut a prime
hypersurface component by the regular compatibility polynomial. -/
private theorem retained_dimension {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (affineHilbertPolynomial P).natDegree = 1 := by
  obtain ⟨hw, hret⟩ := mem_factorCurves.mp hP
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hret).1
  let := hmin.isPrime
  let H : Ideal (GeoRow 3) := Ideal.span {genericRow f}
  let g := genericRow (oldCut f)
  have heq : oldCutIdeal f = H ⊔ Ideal.span {g} := by
    rw [← Ideal.span_union]
    rfl
  have hHP : H ≤ P := le_sup_left.trans (heq ▸ hmin.le)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hHP
  let := hQ.isPrime
  have hgQ : g ∉ Q := by
    intro hg
    obtain ⟨a, ha, hga⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hQ hg
    have hga' : Ideal.Quotient.mk H g * Ideal.Quotient.mk H a = Ideal.Quotient.mk H g * 0 := by
      rw [← map_mul, mul_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hga
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp (cut_regular hf hw hga'))
  have hP' : P ∈ (Q ⊔ Ideal.span {g}).minimalPrimes := by
    have hle : H ⊔ Ideal.span {g} ≤ Q ⊔ Ideal.span {g} := sup_le_sup_right hQ.le _
    refine ⟨⟨hmin.isPrime, sup_le hQP (le_sup_right.trans (heq ▸ hmin.le))⟩, ?_⟩
    intro J hJ hJP
    exact hmin.2 ⟨hJ.1, heq.trans_le (hle.trans hJ.2)⟩ hJP
  have hF : genericRow f ≠ 0 :=
    fun h => hf.ne_zero (map_injective _ genericCoeff_injective (h.trans (map_zero _).symm))
  have hdQ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hQ
  have hdP := principalCut_natDegree_affineHilbertPolynomial_add_one hgQ hP'
  rw [Nat.card_fin] at hdQ
  omega

theorem section_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) : IsSectionCurve f P := by
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  obtain ⟨hprime, hdim⟩ := graph_dimension f P hm.2
  refine ⟨hprime.comap lastMap, ?_⟩
  unfold sectionIdeal
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective lastMap
      (monomialMap_surjective lastExponents_single), hdim, retained_dimension hf hP]

private theorem eval_factor_of_regular {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {x : Fin 3 → GeometricX} (hx : x ∈ regularLocus f P) :
    eval x (genericRow f) = 0 :=
  hx.1 _ ((Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2).1.le
    (Ideal.subset_span (by simp)))

private theorem next_notMem_graphCurve {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (T : LiftedChart f) (hnext : genericRow (oldNext f) ∉ P) :
    T.next ∉ graphCurve f P := by
  intro hn
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  have hvanish : genericRow (separant f) * genericRow (oldNext f) ∈
      vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
    intro x hx
    change eval x (_ * _) = 0
    rw [map_mul]
    by_cases hs : eval x (genericRow (separant f)) = 0
    · rw [hs, zero_mul]
    · have hr : x ∈ regularLocus f P := ⟨hx, hs⟩
      have he : eval (graphPoint f x) T.next = 0 := hn _ ⟨x, hr, rfl⟩
      rw [(eval_represents_iff T.next_represents (eval_factor_of_regular hP hr) hs).mp he,
        mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hvanish
  exact (hm.1.isPrime.mem_or_mem hvanish).elim hm.2 hnext

theorem points_le_sectionDegree {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hcurve : IsSectionCurve f P) (T : LiftedChart f)
    (hnext : genericRow (oldNext f) ∉ P) :
    (nextCutLocus f P).Finite ∧ ((nextCutLocus f P).ncard : ℚ) ≤ sectionDegree f P := by
  let h : T.next ∈ restrictSupport GeometricX lastExponents := T.next_box
  let l := monomialLift T.next h
  have hmap : lastMap l = T.next := monomialMap_monomialLift _ _
  have hl : l ∉ sectionIdeal f P := by
    intro hm
    change lastMap l ∈ graphCurve f P at hm
    rw [hmap] at hm
    exact next_notMem_graphCurve hP T hnext hm
  let J := sectionIdeal f P ⊔ Ideal.span {l}
  obtain ⟨hdim, hbound⟩ := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hcurve.1 hl (totalDegree_monomialLift_le_one _ _)
  change (affineHilbertPolynomial J).natDegree ≤ _ at hdim
  rw [hcurve.2] at hdim hbound
  have hzero : (affineHilbertPolynomial J).natDegree = 0 := Nat.eq_zero_of_le_zero hdim
  have hdeg : affineDegree J ≤ sectionDegree f P := by
    rw [sectionDegree, affineDegree_of_natDegree_eq_zero hzero, affineDegree, hcurve.2]
    simpa [J] using hbound
  obtain ⟨hfinite, hcard⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hzero
  let m := fun x => monomialPoint lastExponents (graphPoint f x)
  have hinj : Function.Injective m :=
    (monomialPoint_injective lastExponents_single).comp (graphPoint_injective f)
  have hsubset : m '' nextCutLocus f P ⊆ zeroLocus GeometricX J := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply sup_le
    · apply mem_zeroLocus_iff_le_ker_aeval.mp
      apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mpr
      exact zeroLocus_vanishingIdeal_le _ ⟨x, hx.1, rfl⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, aeval_monomialPoint, hmap]
      exact (eval_represents_iff T.next_represents
        (eval_factor_of_regular hP hx.1) hx.1.2).mpr hx.2
  refine ⟨(hfinite.subset hsubset).of_finite_image hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset hfinite)).trans (hcard.trans hdeg)

end
end P0_9_5_1_2
end PackSource_P0_9_5_1_2Geometry

section PackSource_P0_9_5_1_2Sparse
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2
noncomputable section
open K1_13_5 (graphBox liftedBox)
open K1_13_5_4 (InLiftedBox GeoRow)
open K1_13_5_4_2 (JetPoint fourCutIdeal pointIdeal pointLength downBody capBody)
open K1_13_5_4_2_4 (Exponent Downward cutIdeal downSupport capSupport mem_downSupport mem_capSupport
  latticeBody latticeBody_downSupport latticeBody_capSupport)
open P0_9 (taylorLength)
open MvPolynomial
open scoped BigOperators Pointwise

open private mixed_eq_generic downSupport_downward capSupport_downward zero_mem_capSupport
  from ProximityPrize.SubmissionLower.Fast048

private theorem deformation_bound : K1_13_5_4_2_4.c1 :=
  K1_13_5_4_2_4_1.of_children K1_13_5_4_2_4_1_1.proof K1_13_5_4_2_4_1_2.proof

private theorem generic_degree : K1_13_5_4_2_4.c2 :=
  K1_13_5_4_2_4_2.of_children K1_13_5_4_2_4_2_1.proof K1_13_5_4_2_4_2_2.proof
    (K1_13_5_4_2_4_2_3.of_children K1_13_5_4_2_4_2_3_1.proof K1_13_5_4_2_4_2_3_2.proof)

/-- The arbitrary-support sparse bound specialized to the retuned boxes. -/
theorem sparse_bound
    (F G E L : GeoRow 4) (hF : F ≠ 0) (hG : InLiftedBox G graphBox 1)
    (hE : InLiftedBox E (liftedBox (taylorLength + 1)) (taylorLength - 1))
    (hL : InLiftedBox L lastBox taylorLength) (points : Finset JetPoint)
    (hpoints : ∀ y ∈ points, pointIdeal y ∈ (fourCutIdeal F G E L).minimalPrimes) :
    (↑(∑ y ∈ points, (pointLength (fourCutIdeal F G E L) y).toNat) : ℝ) ≤
      lastMixedVolume (downBody F) := by
  classical
  let A : Fin 4 → Finset Exponent :=
    ![downSupport F, capSupport graphBox 1,
      capSupport (liftedBox (taylorLength + 1)) (taylorLength - 1),
      capSupport lastBox taylorLength]
  let f : Fin 4 → GeoRow 4 := ![F, G, E, L]
  have hz : ∀ i, 0 ∈ A i := by
    intro i
    fin_cases i
    · obtain ⟨e, he⟩ := support_nonempty.mpr hF
      exact mem_downSupport.mpr ⟨e, he, fun _ => Nat.zero_le _⟩
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
    · exact zero_mem_capSupport _ _
  have hd : ∀ i, Downward (A i) := by
    intro i
    fin_cases i
    · exact downSupport_downward F
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
    · exact capSupport_downward _ _
  have hv (j : Fin 4) : ∃ i, Finsupp.single j 1 ∈ A i := by
    exact ⟨3, mem_capSupport.mpr (lastExponents_single j)⟩
  have hsup : ∀ i, (f i).support ⊆ A i := by
    intro i
    fin_cases i
    · exact fun a ha => mem_downSupport.mpr ⟨a, ha, le_rfl⟩
    · exact fun a ha => mem_capSupport.mpr (hG a ha)
    · exact fun a ha => mem_capSupport.mpr (hE a ha)
    · exact fun a ha => mem_capSupport.mpr (hL a ha)
  have hJ : cutIdeal f = fourCutIdeal F G E L := by
    unfold cutIdeal fourCutIdeal
    apply congrArg Ideal.span
    ext p
    simp [f, or_left_comm, or_comm]
  obtain ⟨hfinite, hmv⟩ := mixed_eq_generic generic_degree K1_13_5_4_2_4_3.proof A hz hd hv
  have hbound := deformation_bound A hz hfinite f hsup points (by simpa only [hJ] using hpoints)
  have hbodies : (fun i => latticeBody (A i)) =
      ![downBody F, capBody graphBox 1,
        capBody (liftedBox (taylorLength + 1)) (taylorLength - 1), capBody lastBox taylorLength] := by
    funext i
    fin_cases i
    · exact latticeBody_downSupport F
    · exact latticeBody_capSupport _ _ (show 49 ≤ 120 by decide) (show 48 ≤ 49 by decide)
    · exact latticeBody_capSupport _ _ (show 6677452 ≤ 16025881 by decide)
        (show 6677452 ≤ 6677452 by decide)
    · exact latticeBody_capSupport _ _ (show 6677502 ≤ 16026001 by decide)
        (show 6677502 ≤ 6677502 by decide)
  simpa only [hJ, hmv, hbodies, lastMixedVolume] using (Nat.cast_le (α := ℝ)).mpr hbound

end
end P0_9_5_1_2
end PackSource_P0_9_5_1_2Sparse

section PackSource_P0_9_5_1_2Image
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2
noncomputable section
open K1_13 (Row Shape indexDegree)
open K1_13_5 (lowBox separant)
open K1_13_5_4 (InLiftedBox GeometricX GeoRow genericRow liftRow graphPoint regularLocus)
open K1_13_5_4_2 (graphLocus JetPoint eval_liftRow_graphPoint)
open P0_9 (taylorLength)
open P0_9_5 (SecondFactors)
open P0_9_5_1 (LiftedChart reconstruct CoefficientIdeal)
open MvPolynomial
open scoped BigOperators Pointwise

open private ratio_image_degree box_mono from ProximityPrize.SubmissionLower.Fast048

private theorem separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors f)
    (i : Fin n) : InLiftedBox (liftRow (genericRow (separant (f i)))) lowBox 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hs : b ∈ (separant (f i)).support := support_map_subset _ _ hb
  let m : Fin 3 →₀ ℕ := b + Finsupp.single 2 1
  have hm : m ∈ (f i).support := by
    rw [MvPolynomial.mem_support_iff, separant, coeff_pderiv] at hs
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs)
  have hb₀ : m.degree ≤ lowBox.b :=
    (le_totalDegree hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le ((f j).totalDegree))
      (Finset.mem_univ i)).trans hf.total)
  have hj₀ : (m.sum fun j a => j.val * a) ≤ lowBox.j :=
    (Finset.le_sup hm).trans ((Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
      (Finset.mem_univ i)).trans hf.index)
  have ht₀ : m 2 ≤ lowBox.t :=
    (monomial_le_degreeOf 2 hm).trans ((Finset.single_le_sum
      (fun j _ => Nat.zero_le ((f j).degreeOf 2)) (Finset.mem_univ i)).trans hf.top)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hb₀
  rw [Finsupp.sum_fintype _ _ (fun j => mul_zero j.val), Fin.sum_univ_three] at hj₀
  have h0 : Finsupp.mapDomain Fin.castSucc b 0 = b 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 0
  have h1 : Finsupp.mapDomain Fin.castSucc b 1 = b 1 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 1
  have h2 : Finsupp.mapDomain Fin.castSucc b 2 = b 2 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 2
  have h3 : Finsupp.mapDomain Fin.castSucc b 3 = 0 :=
    Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)
  simp only [h0, h1, h2, h3, le_refl, and_true]
  simp [m, Finsupp.add_apply] at hb₀ hj₀ ht₀
  omega

private theorem pow_separator_box {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors f)
    (i : Fin n) (r : ℕ) :
    InLiftedBox (liftRow (genericRow (separant (f i))) ^ r)
      ⟨120 * r, 48 * r, 24 * r⟩ 0 := by
  classical
  induction r with
  | zero =>
      simp only [pow_zero, InLiftedBox, support_one, Finset.mem_singleton]
      rintro a rfl
      simp
  | succ r ih =>
      intro a ha
      rw [pow_succ] at ha
      obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ ha)
      have ⟨hb₀, hb₁, hb₂, hb₃⟩ := ih b hb
      have ⟨hc₀, hc₁, hc₂, hc₃⟩ := separator_box hf i c hc
      simp only [Finsupp.add_apply, Nat.mul_succ] at *
      exact ⟨by omega, by omega, by omega, by omega⟩

theorem coefficient_image_degree {n : ℕ} {f : Fin n → Row 3} (hf : SecondFactors f)
    (i : Fin n) (P : Ideal (GeoRow 3)) (T : LiftedChart (f i))
    (hcurve : IsSectionCurve (f i) P) (hone : 1 ≤ sectionDegree (f i) P) :
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      affineDegree Q ≤ sectionDegree (f i) P ∧
      ∀ y ∈ regularLocus (f i) P, reconstruct (f i) T.numerator y ∈ zeroLocus GeometricX Q := by
  let A := monomialPoint lastExponents '' graphLocus (f i) P
  have hA : sectionIdeal (f i) P = vanishingIdeal GeometricX A := by
    ext p
    constructor
    · intro hp
      rintro _ ⟨z, hz, rfl⟩
      rw [aeval_monomialPoint]
      exact hp z hz
    · intro hp z hz
      have he := hp _ ⟨z, hz, rfl⟩
      rwa [aeval_monomialPoint] at he
  obtain ⟨D, hD_eq⟩ : ∃ D : GeoRow 4,
      D = liftRow (genericRow (separant (f i))) ^ (taylorLength - 4) := ⟨_, rfl⟩
  have hD : D ∈ restrictSupport GeometricX lastExponents := by
    have hbox : InLiftedBox D
        ⟨120 * (taylorLength - 4), 48 * (taylorLength - 4), 24 * (taylorLength - 4)⟩ 0 := by
      rw [hD_eq]
      exact pow_separator_box hf i (taylorLength - 4)
    change InLiftedBox D lastBox taylorLength
    exact box_mono (show 16025760 ≤ 16026001 by decide)
      (show 6410304 ≤ 6677502 by decide) (show 3205152 ≤ 3338751 by decide)
      (Nat.zero_le _) hbox
  have hN (j : Fin taylorLength) : T.numerator j ∈ restrictSupport GeometricX lastExponents := by
    change InLiftedBox (T.numerator j) lastBox taylorLength
    exact box_mono (show 16025761 ≤ 16026001 by decide)
      (show 6677402 ≤ 6677502 by decide) (show 3338701 ≤ 3338751 by decide)
      (Nat.sub_le _ _) (T.coefficient_box j)
  let d := monomialLift D hD
  let ν (j : Fin taylorLength) := monomialLift (T.numerator j) (hN j)
  have hdeval (z : JetPoint) : eval (monomialPoint lastExponents z) d = eval z D := by
    have hmap : lastMap d = D := monomialMap_monomialLift D hD
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z d
  have hνeval (z : JetPoint) (j : Fin taylorLength) :
      eval (monomialPoint lastExponents z) (ν j) = eval z (T.numerator j) := by
    have hmap : lastMap (ν j) = T.numerator j := monomialMap_monomialLift _ _
    simpa only [aeval_eq_eval, hmap] using aeval_monomialPoint z (ν j)
  have hden (z) (hz : z ∈ A) : eval z d ≠ 0 := by
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    rw [hdeval, hD_eq, map_pow, eval_liftRow_graphPoint]
    exact pow_ne_zero _ hx.2
  obtain ⟨Q, hp, hd, hb, hz⟩ := ratio_image_degree A _ hA hcurve.1 hcurve.2 hone d ν
    (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  refine ⟨Q, hp, hd, hb, fun x hx => ?_⟩
  have hz' := hz (monomialPoint lastExponents (graphPoint (f i) x)) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  unfold reconstruct
  simpa only [hνeval, hdeval, hD_eq, map_pow, eval_liftRow_graphPoint] using hz'

end
end P0_9_5_1_2
end PackSource_P0_9_5_1_2Image

section PackSource_P0_9_5_1_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2
noncomputable section
open K1_13 (Row)
open K1_13_5_4 (GeoRow genericRow liftRow graph)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal pointLength downBody
  localLength_lt_top)
open P0_9_5 (SecondFactors mixedBudget)
open P0_9_5_1 (LiftedChart CurveIndex properComponents componentLength)
open MvPolynomial
open scoped BigOperators

open private lift_generic_ne_zero from ProximityPrize.SubmissionLower.Fast048

/-- One generic section realizes the last-box degree of each reduced curve of
the same factor on its regular open and away from the other curves. -/
def c1 : Prop :=
  ∀ (f : Row 3), (∀ P ∈ factorCurves f, IsSectionCurve f P) →
    Nonempty (GenericSection f)

/-- The compatibility length survives the graph change and is a lower bound
for the local length at each isolated last-section point. -/
def c2 : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 → ∀ (T : LiftedChart f) (L : GeoRow 4),
    (∀ P ∈ factorCurves f, L ∉ graphCurve f P) →
    ∀ P ∈ factorCurves f, ∀ y ∈ graphLocus f P, eval y L = 0 →
      let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y

/-- Aggregate the actual first slots by Minkowski addition and polarize the
three possible contributions of the last-coordinate interval. -/
def c3 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∑ i, lastMixedVolume (downBody (liftRow (genericRow (f i))))) ≤ (mixedBudget : ℝ)

private theorem section_cost (hlocal : c2) {f : Row 3}
    (hf : Irreducible f) (hpos : 0 < f.degreeOf 2) (T : LiftedChart f) (S : GenericSection f) :
    (↑(∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) : ℝ) ≤
      lastMixedVolume (downBody (liftRow (genericRow f))) := by
  classical
  let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut S.polynomial
  let points := (factorCurves f).biUnion S.points
  have hlocal' (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ S.points P) :
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y :=
    hlocal f hf hpos T S.polynomial S.proper P hP y (S.roots P hP y hy).1
      (S.roots P hP y hy).2
  have hmin : ∀ y ∈ points, pointIdeal y ∈ J.minimalPrimes := by
    intro y hy
    obtain ⟨P, hP, hyP⟩ := Finset.mem_biUnion.mp hy
    exact (hlocal' P hP y hyP).1
  have hd : Set.PairwiseDisjoint (↑(factorCurves f)) S.points := by
    intro P hP P' hP' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    exact S.off_other_curves P hP P' hP' hne y hy (S.roots P' hP' y hy').1
  have hcost : (∑ P ∈ factorCurves f, (componentLength f P).toNat * (S.points P).card) ≤
      ∑ y ∈ points, (pointLength J y).toNat := by
    change _ ≤ ∑ y ∈ (factorCurves f).biUnion S.points, (pointLength J y).toNat
    rw [Finset.sum_biUnion hd]
    apply Finset.sum_le_sum
    intro P hP
    calc
      _ = ∑ _ ∈ S.points P, (componentLength f P).toNat := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        exact ENat.toNat_le_toNat (hlocal' P hP y hy).2 (localLength_lt_top (hmin y
          (Finset.mem_biUnion.mpr ⟨P, hP, hy⟩))).ne
  exact (Nat.cast_le.mpr hcost).trans
    (sparse_bound _ _ _ _ (lift_generic_ne_zero hf.ne_zero) T.graph_box T.cut_box S.support points hmin)

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : P0_9_5_1.c2 := by
  classical
  intro n f hf T
  have hcurve (i : Fin n) (P) (hP : P ∈ factorCurves (f i)) : IsSectionCurve (f i) P :=
    section_curve (hf.irreducible i) hP
  let S (i : Fin n) := Classical.choice (h1 (f i) (hcurve i))
  let e : CurveIndex n → ℕ := fun a => (componentLength (f a.1) a.2).toNat
  let d : CurveIndex n → ℕ := fun a => ((S a.1).points a.2).card
  have hdeg (a : CurveIndex n) (ha : a ∈ properComponents f) :
      (d a : ℚ) = sectionDegree (f a.1) a.2 :=
    (S a.1).card_eq a.2 (mem_properComponents.mp ha)
  refine ⟨⟨e, d, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun _ ha => componentLength_toNat (mem_properComponents.mp ha)
  · exact fun _ ha => componentLength_toNat_pos (mem_properComponents.mp ha)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sum_properComponents, Nat.cast_sum]
    exact (Finset.sum_le_sum fun i _ =>
      section_cost h2 (hf.irreducible i) (hf.positive i) (T i) (S i)).trans (h3 n f hf)
  · intro a ha hn
    have hp := mem_properComponents.mp ha
    obtain ⟨hfin, hcard⟩ := points_le_sectionDegree hp (hcurve _ _ hp) (T a.1) hn
    exact ⟨hfin, Nat.cast_le.mp (hcard.trans_eq (hdeg a ha).symm)⟩
  · intro a ha _
    have hp := mem_properComponents.mp ha
    have hC := hcurve _ _ hp
    have hpos : 0 < d a := by
      have h : (0 : ℚ) < (d a : ℚ) := by
        rw [hdeg a ha]
        exact affineDegree_pos hC.1.ne_top
      exact_mod_cast h
    have hone : 1 ≤ sectionDegree (f a.1) a.2 := by
      rw [← hdeg a ha]
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    obtain ⟨Q, hprime, hdim, hb, hrec⟩ := coefficient_image_degree hf a.1 a.2 (T a.1) hC hone
    exact ⟨Q, hprime, hdim, hpos, hb.trans_eq (hdeg a ha).symm, hrec⟩

end
end P0_9_5_1_2
end PackSource_P0_9_5_1_2Split

section PackSource_P0_9_5_1_2_1Geometry
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_1
noncomputable section

open K1_13 (Row)
open K1_13_5 (separant lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow regularLocus graph graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve eval_liftRow_graphPoint eval_graph_graphPoint)
open P0_9_5_1 (oldCutIdeal)
open P0_9_5_1_2 (factorCurves mem_factorCurves lastExponents lastExponents_single lastMap
  sectionIdeal IsSectionCurve)
open MvPolynomial

open private K1_13_5_4_2.three_ne_zero from ProximityPrize.SubmissionLower.Fast048

abbrev EmbeddedPoint := lastExponents → GeometricX

/-- The original coordinates occur among the monomial coordinates. -/
def jetOfEmbedded (z : EmbeddedPoint) : JetPoint :=
  fun i => z ⟨Finsupp.single i 1, lastExponents_single i⟩

private theorem jetOf_monomialPoint (y : JetPoint) :
    jetOfEmbedded (monomialPoint lastExponents y) = y :=
  funext fun i => monomialPoint_single y (lastExponents_single i)

theorem monomialPoint_jetOf {f : Row 3} {P : Ideal (GeoRow 3)} {z : EmbeddedPoint}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal f P)) :
    monomialPoint lastExponents (jetOfEmbedded z) = z := by
  obtain ⟨y, hy⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker lastExponents_single
    (zeroLocus_anti_mono (show RingHom.ker lastMap ≤ sectionIdeal f P from
      fun q hq => show lastMap q ∈ graphCurve f P from
        (RingHom.mem_ker.mp hq).symm ▸ (graphCurve f P).zero_mem) hz)
  rw [← hy, jetOf_monomialPoint]

private theorem jetOf_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)} {z : EmbeddedPoint}
    (hz : z ∈ zeroLocus GeometricX (sectionIdeal f P)) :
    jetOfEmbedded z ∈ zeroLocus GeometricX (graphCurve f P) := by
  apply (monomialPoint_mem_zeroLocus_comap_iff lastExponents_single _ _).mp
  rw [monomialPoint_jetOf hz]
  exact hz

private theorem retained {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    P ∈ (oldCutIdeal f).minimalPrimes ∧ genericRow (separant f) ∉ P :=
  Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2

private theorem lift_mem_graphCurve_iff {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (g : GeoRow 3) :
    liftRow g ∈ graphCurve f P ↔ g ∈ P := by
  constructor
  · intro hg
    let : P.IsPrime := (retained hP).1.isPrime
    have hv : genericRow (separant f) * g ∈
        vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
      intro x hx
      change eval x (genericRow (separant f) * g) = 0
      rw [map_mul]
      by_cases hs : eval x (genericRow (separant f)) = 0
      · rw [hs, zero_mul]
      · have he : eval (graphPoint f x) (liftRow g) = 0 :=
          hg _ ⟨x, ⟨hx, hs⟩, rfl⟩
        rw [eval_liftRow_graphPoint] at he
        rw [he, mul_zero]
    rw [IsPrime.vanishingIdeal_zeroLocus P] at hv
    exact (Ideal.IsPrime.mem_or_mem inferInstance hv).resolve_left (retained hP).2
  · intro hg y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change eval (graphPoint f x) (liftRow g) = 0
    rw [eval_liftRow_graphPoint]
    exact hx.1 g hg

private theorem mem_graphLocus_of_mem_closure {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ zeroLocus GeometricX (graphCurve f P))
    (hs : eval y (liftRow (genericRow (separant f))) ≠ 0) :
    y ∈ graphLocus f P := by
  let x : Fin 3 → GeometricX := y ∘ Fin.castSucc
  have hs' : eval x (genericRow (separant f)) ≠ 0 := by
    simpa only [liftRow, eval_rename, x] using hs
  have hx : x ∈ regularLocus f P := by
    refine ⟨fun g hg => ?_, hs'⟩
    have h := hy (liftRow g) ((lift_mem_graphCurve_iff hP g).mpr hg)
    simpa only [aeval_eq_eval, liftRow, eval_rename, x] using h
  have hvan : graph f ∈ graphCurve f P := by
    rintro _ ⟨w, hw, rfl⟩
    exact eval_graph_graphPoint hw.2
  have h := hy (graph f) hvan
  simp only [aeval_eq_eval, graph, map_add, map_mul, map_ofNat, eval_X, liftRow,
    eval_rename] at h
  change eval x (genericRow (lowerTangent f)) +
    3 * y 3 * eval x (genericRow (separant f)) = 0 at h
  refine ⟨x, hx, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.snoc_castSucc _ _ j) i
  rw [graphPoint, Fin.snoc_last, div_eq_iff (mul_ne_zero K1_13_5_4_2.three_ne_zero hs')]
  change -eval x (genericRow (lowerTangent f)) =
    y 3 * (3 * eval x (genericRow (separant f)))
  linear_combination -h

private theorem finite_cut {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : IsSectionCurve f P) {g : GeoRow 4} (hg : g ∉ graphCurve f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal f P) ∧
      eval (jetOfEmbedded z) g = 0}.Finite := by
  obtain ⟨G, hG⟩ := monomialMap_surjective lastExponents_single g
  have hnot : G ∉ sectionIdeal f P := by
    change lastMap G ∉ graphCurve f P
    rwa [hG]
  obtain ⟨hdim, _⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP.1 hnot (b := G.totalDegree) le_rfl
  rw [hP.2] at hdim
  have hn := Nat.eq_zero_of_le_zero hdim
  refine ((finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ hn).1).subset ?_
  intro z hz
  apply mem_zeroLocus_sup_span_singleton_iff.mpr
  refine ⟨hz.1, ?_⟩
  rw [← monomialPoint_jetOf hz.1, aeval_monomialPoint, hG, aeval_eq_eval]
  exact hz.2

private theorem finite_boundary {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal f P) ∧
      jetOfEmbedded z ∉ graphLocus f P}.Finite := by
  have hsep : liftRow (genericRow (separant f)) ∉ graphCurve f P :=
    fun h => (retained hP).2 ((lift_mem_graphCurve_iff hP _).mp h)
  refine (finite_cut hC hsep).subset ?_
  intro z hz
  exact ⟨hz.1, not_ne_iff.mp fun hs =>
    hz.2 (mem_graphLocus_of_mem_closure hP (jetOf_mem_closure hz.1) hs)⟩

private theorem finite_overlap {f : Row 3} {P Q : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hQ : Q ∈ factorCurves f) (hne : P ≠ Q)
    (hC : IsSectionCurve f P) :
    {z | z ∈ zeroLocus GeometricX (sectionIdeal f P) ∧
      jetOfEmbedded z ∈ graphLocus f Q}.Finite := by
  have h : ¬ Q ≤ P := Ideal.not_le_of_mem_minimalPrimes (retained hQ).1 (retained hP).1 hne.symm
  obtain ⟨g, hgQ, hgP⟩ : ∃ g, g ∈ Q ∧ g ∉ P := by
    by_contra! hbad
    exact h hbad
  refine (finite_cut hC (fun hg => hgP ((lift_mem_graphCurve_iff hP _).mp hg))).subset ?_
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨x, hx, he⟩ := hz.2
  rw [← he, eval_liftRow_graphPoint]
  exact hx.1 g hgQ

/-- Only finitely many embedded points of this curve are unavailable on the
separant graph or also occur on another retained graph. -/
theorem exists_excluded_points {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) (hC : IsSectionCurve f P) :
    ∃ B : Finset EmbeddedPoint,
      ∀ z ∈ zeroLocus GeometricX (sectionIdeal f P), z ∉ B →
        jetOfEmbedded z ∈ graphLocus f P ∧
        ∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded z ∉ graphLocus f Q := by
  classical
  let boundary := (finite_boundary hP hC).toFinset
  let overlap (Q : (factorCurves f).erase P) :=
    (finite_overlap hP (Finset.mem_of_mem_erase Q.property)
      (Finset.ne_of_mem_erase Q.property).symm hC).toFinset
  refine ⟨boundary ∪ Finset.univ.biUnion overlap, ?_⟩
  intro z hz hB
  constructor
  · by_contra hn
    apply hB
    exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr ⟨hz, hn⟩)
  · intro Q hQ hne hmeet
    let q : (factorCurves f).erase P := ⟨Q, Finset.mem_erase.mpr ⟨hne.symm, hQ⟩⟩
    apply hB
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ _, (Set.Finite.mem_toFinset _).mpr ⟨hz, hmeet⟩⟩)

end
end P0_9_5_1_2_1
end PackSource_P0_9_5_1_2_1Geometry

section PackSource_P0_9_5_1_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_1
noncomputable section

open K1_13_5_4 (GeoRow GeometricX InLiftedBox)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve)
open K1_13_5_4_2_2 (linearForm fiberIdeal totalDegree_hyperplane_le_one zeroLocus_fiber_iff
  ncard_eq_affineDegree_of_radical)
open P0_9 (taylorLength)
open P0_9_5_1_2 (factorCurves lastBox lastExponents lastMap sectionIdeal sectionDegree)
open MvPolynomial
open scoped Pointwise

private theorem hyperplane_support (a : EmbeddedPoint) (t : GeometricX) :
    InLiftedBox (lastMap (linearForm a - MvPolynomial.C t)) lastBox taylorLength := by
  have hz : (0 : Fin 4 →₀ ℕ) ∈ lastExponents := by
    change 0 + 0 + 0 ≤ lastBox.b ∧ 0 + 2 * 0 ≤ lastBox.j ∧ 0 ≤ lastBox.t ∧ 0 ≤ taylorLength
    simp
  have h := monomialMap_mem_restrictSupport_nsmul hz (totalDegree_hyperplane_le_one a t)
  rw [one_nsmul] at h
  exact h

theorem proof : P0_9_5_1_2.c1 := by
  classical
  intro f hC
  have h1 := K1_13_5_4_2_2_1.proof
  have h2 := K1_13_5_4_2_2_2.proof
  have h3 := K1_13_5_4_2_2_3.proof
  let I (P : factorCurves f) := sectionIdeal f P.val
  obtain ⟨degreeBad, hdegreeBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h1 GeometricX lastExponents (I P) (hC P.val P.property).1 (hC P.val P.property).2
  obtain ⟨separationBad, hseparationBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h2 GeometricX lastExponents (I P) (hC P.val P.property).1 (hC P.val P.property).2
  let bad := Finset.univ.biUnion fun P => insert (separationBad P) (degreeBad P)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun V : bad => V.val) (by
      intro V
      obtain ⟨P, _, hV⟩ := Finset.mem_biUnion.mp V.property
      rcases Finset.mem_insert.mp hV with h | h
      · rw [h]
        exact (hseparationBad P).1
      · exact (hdegreeBad P).1 _ h)
  have havoid (P : factorCurves f) (V : Submodule GeometricX EmbeddedPoint)
      (hV : V ∈ insert (separationBad P) (degreeBad P)) : a ∉ V :=
    ha ⟨V, Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, hV⟩⟩
  have hdegree (P : factorCurves f) :=
    (hdegreeBad P).2 a (fun V hV => havoid P V (Finset.mem_insert_of_mem hV))
  obtain ⟨valueBad, hvalueBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    h3 GeometricX lastExponents (I P) (hC P.val P.property).1 a (hdegree P).1
      ((hseparationBad P).2 a (havoid P _ (Finset.mem_insert_self _ _)))
  obtain ⟨pointsBad, hpointsBad⟩ := Classical.skolem.mp fun P : factorCurves f =>
    exists_excluded_points P.property (hC P.val P.property)
  let value (z : EmbeddedPoint) := aeval z (linearForm a)
  let excludedValues := Finset.univ.biUnion fun P => valueBad P ∪ (pointsBad P).image value
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset excludedValues
  have hmiss (P : factorCurves f) : t ∉ valueBad P ∪ (pointsBad P).image value :=
    fun h => ht (Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, h⟩)
  let L := linearForm a - MvPolynomial.C t
  let J (P : Ideal (GeoRow 3)) := fiberIdeal (sectionIdeal f P) a t
  have hcut (P) (hP : P ∈ factorCurves f) :
      (affineHilbertPolynomial (J P)).natDegree = 0 ∧
        affineDegree (J P) = sectionDegree f P :=
    (hdegree ⟨P, hP⟩).2 t
  have hproper (P) (hP : P ∈ factorCurves f) : lastMap L ∉ graphCurve f P := by
    intro hmem
    have hL : L ∈ sectionIdeal f P := hmem
    have heq : J P = sectionIdeal f P :=
      sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hL)
    have hz := (hcut P hP).1
    rw [heq, (hC P hP).2] at hz
    omega
  have hfinite (P) (hP : P ∈ factorCurves f) : (zeroLocus GeometricX (J P)).Finite :=
    (finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) _ (hcut P hP).1).1
  let points (P : Ideal (GeoRow 3)) : Finset JetPoint :=
    if hP : P ∈ factorCurves f then (hfinite P hP).toFinset.image jetOfEmbedded else ∅
  have hg (P) (hP : P ∈ factorCurves f) {z : EmbeddedPoint}
      (hz : z ∈ zeroLocus GeometricX (J P)) :
      jetOfEmbedded z ∈ graphLocus f P ∧
      (∀ Q ∈ factorCurves f, P ≠ Q → jetOfEmbedded z ∉ graphLocus f Q) := by
    obtain ⟨hzC, hzt⟩ := zeroLocus_fiber_iff.mp hz
    apply hpointsBad ⟨P, hP⟩ z hzC
    intro hbad
    exact hmiss ⟨P, hP⟩ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨z, hbad, hzt⟩))
  have hpoint (P) (hP : P ∈ factorCurves f) (y) (hy : y ∈ points P) :
      ∃ z ∈ zeroLocus GeometricX (J P), jetOfEmbedded z = y := by
    simp only [points, dite_eq_left hP] at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨z, (Set.Finite.mem_toFinset _).mp hz, rfl⟩
  refine ⟨⟨lastMap L, hyperplane_support a t, points, ?_, hproper, ?_, ?_⟩⟩
  · intro P hP
    have hrad := hvalueBad ⟨P, hP⟩ t (fun ht' => hmiss ⟨P, hP⟩ (Finset.mem_union_left _ ht'))
    have hinj : Set.InjOn jetOfEmbedded (zeroLocus GeometricX (J P)) := by
      intro x hx y hy hxy
      rw [← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hx).1,
        ← monomialPoint_jetOf (zeroLocus_fiber_iff.mp hy).1, hxy]
    simp only [points, dite_eq_left hP]
    rw [Finset.card_image_of_injOn (by simpa using hinj),
      ← Set.ncard_eq_toFinset_card _ (hfinite P hP)]
    exact (ncard_eq_affineDegree_of_radical (J P) (hcut P hP).1 hrad).trans (hcut P hP).2
  · intro P hP y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    have hzC := (zeroLocus_fiber_iff.mp hz).1
    refine ⟨(hg P hP hz).1, ?_⟩
    have hev := (mem_zeroLocus_sup_span_singleton_iff.mp hz).2
    rw [← monomialPoint_jetOf hzC, aeval_monomialPoint, aeval_eq_eval] at hev
    exact hev
  · intro P hP Q hQ hne y hy
    obtain ⟨z, hz, rfl⟩ := hpoint P hP y hy
    exact (hg P hP hz).2 Q hQ hne

end
end P0_9_5_1_2_1
end PackSource_P0_9_5_1_2_1Proof

section PackSource_P0_9_5_1_2_2Aux1
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_2

noncomputable section
open K1_13 (Row)
open K1_13_5 (lowerTangent)
open K1_13_5_4 (GeoRow GeometricX genericRow liftRow graph graphIdeal)
open P0_9_5_1 (LiftedChart oldCutIdeal)
open K1_13_5_4_2_3 (OpenRing onOpen onOpen_kills onOpen_isUnit onOpen_hom_ext
  openLift openLift_onOpen sep liftedSep)
open MvPolynomial

open private three_isUnit graph_coord_unique represents_vanish from ProximityPrize.SubmissionLower.Fast048

def threeCut (f : Row 3) (T : LiftedChart f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}

abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart f) := onOpen (threeCut f T) (liftedSep f)

private def newJet (f : Row 3) : OldOpen f :=
  -oldMap f (genericRow (lowerTangent f)) *
    ↑(((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit⁻¹)

private theorem newJet_eq (f : Row 3) :
    oldMap f (genericRow (lowerTangent f)) + 3 * newJet f * oldMap f (sep f) = 0 := by
  let a := oldMap f (genericRow (lowerTangent f))
  let s := oldMap f (sep f)
  let u := ((three_isUnit ((oldMap f).comp C)).mul (onOpen_isUnit (oldCutIdeal f) (sep f))).unit
  have hu : (u : OldOpen f) = 3 * s := IsUnit.unit_spec _
  change a + 3 * (-a * (↑u⁻¹ : OldOpen f)) * s = 0
  calc
    _ = a + -a * ((↑u⁻¹ : OldOpen f) * (u : OldOpen f)) := by rw [hu]; ring
    _ = 0 := by simp

private def substitute (f : Row 3) : GeoRow 4 →+* OldOpen f :=
  eval₂Hom ((oldMap f).comp C) (Fin.snoc (fun i => oldMap f (MvPolynomial.X i)) (newJet f))

@[simp] private theorem substitute_lift (f : Row 3) (p : GeoRow 3) :
    substitute f (liftRow p) = oldMap f p := by
  rw [substitute, liftRow, eval₂Hom_rename, Fin.snoc_comp_castSucc]
  have h : eval₂Hom ((oldMap f).comp C) (fun i : Fin 3 => oldMap f (MvPolynomial.X i)) = oldMap f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  rw [h]

private theorem substitute_last (f : Row 3) :
    substitute f (MvPolynomial.X (Fin.last 3)) = newJet f := by
  rw [substitute, eval₂Hom_X']
  exact Fin.snoc_last _ _

private theorem substitute_graph (f : Row 3) : substitute f (graph f) = 0 := by
  rw [graph, map_add, map_mul, map_mul, map_ofNat, substitute_lift, substitute_lift,
    show (3 : Fin 4) = Fin.last 3 from rfl, substitute_last]
  exact newJet_eq f

private theorem substitute_kills (f : Row 3) (T : LiftedChart f) :
    threeCut f T ≤ RingHom.ker (substitute f) := by
  have hG : graphIdeal f ≤ RingHom.ker (substitute f) := by
    rw [graphIdeal, Ideal.span_insert, sup_le_iff, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.mem_ker]
    refine ⟨?_, substitute_graph f⟩
    rw [substitute_lift]
    exact onOpen_kills (Ideal.subset_span (by simp))
  have hs : IsUnit (substitute f (liftedSep f)) := by
    rw [substitute_lift]
    exact onOpen_isUnit _ _
  refine sup_le hG ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr ?_))
  apply (represents_vanish T.cut_represents _ hG hs).mpr
  rw [substitute_lift]
  exact onOpen_kills (Ideal.subset_span (by simp))

private def graphToOld (f : Row 3) (T : LiftedChart f) : GraphOpen f T →+* OldOpen f :=
  openLift _ _ (substitute f) (substitute_kills f T)
    (by rw [substitute_lift]; exact onOpen_isUnit _ _)

private theorem graphToOld_on (f : Row 3) (T : LiftedChart f) (b : GeoRow 4) :
    graphToOld f T (graphMap f T b) = substitute f b := by
  rw [graphToOld, openLift_onOpen]

private theorem oldToGraph_kills (f : Row 3) (T : LiftedChart f) :
    oldCutIdeal f ≤ RingHom.ker ((graphMap f T).comp (rename Fin.castSucc).toRingHom) := by
  let b := (graphMap f T).comp (rename Fin.castSucc).toRingHom
  have hG : graphIdeal f ≤ RingHom.ker (graphMap f T) := fun u hu =>
    RingHom.mem_ker.mpr (onOpen_kills (show u ∈ threeCut f T from Ideal.mem_sup_left hu))
  change oldCutIdeal f ≤ RingHom.ker b
  rw [oldCutIdeal, Ideal.span_insert, sup_le_iff]
  rw [Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_le_iff_mem]
  refine ⟨hG (show liftRow (genericRow f) ∈ graphIdeal f from
    Ideal.subset_span (by simp)), RingHom.mem_ker.mpr ?_⟩
  exact (represents_vanish T.cut_represents _ hG (onOpen_isUnit _ _)).mp
    (onOpen_kills (show T.cut ∈ threeCut f T from
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

private def oldToGraph (f : Row 3) (T : LiftedChart f) : OldOpen f →+* GraphOpen f T :=
  openLift _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f))

@[simp] private theorem oldToGraph_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    oldToGraph f T (oldMap f a) = graphMap f T (liftRow a) :=
  openLift_onOpen _ _ ((graphMap f T).comp (rename Fin.castSucc).toRingHom)
    (oldToGraph_kills f T) (onOpen_isUnit (threeCut f T) (liftedSep f)) a

/-- Solve the linear equation for the fourth jet in the full localized
coordinate ring. The congruence for the cut is used before taking radicals. -/
def graphEquiv (f : Row 3) (T : LiftedChart f) : OldOpen f ≃+* GraphOpen f T := by
  refine RingEquiv.ofRingHom (oldToGraph f T) (graphToOld f T) ?_ ?_
  · apply onOpen_hom_ext
    have hcomp : (graphToOld f T).comp (graphMap f T) = substitute f :=
      RingHom.ext (graphToOld_on f T)
    rw [RingHom.comp_assoc, RingHom.id_comp, hcomp]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substitute, liftRow]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hG : graphMap f T (graph f) = 0 :=
          onOpen_kills (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
        have he := DFunLike.congr_arg (oldToGraph f T) (newJet_eq f)
        rw [map_add, map_mul, map_mul, map_ofNat, map_zero, oldToGraph_on, oldToGraph_on] at he
        have h := graph_coord_unique f (graphMap f T) (onOpen_isUnit _ _) hG he
        rw [RingHom.comp_apply, substitute_last]
        exact h.symm
      · simp [substitute, liftRow]
  · apply onOpen_hom_ext
    apply RingHom.ext
    intro a
    simp [graphToOld_on]

@[simp] theorem graphEquiv_on (f : Row 3) (T : LiftedChart f) (a : GeoRow 3) :
    graphEquiv f T (oldMap f a) = graphMap f T (liftRow a) :=
  oldToGraph_on f T a

end

end P0_9_5_1_2_2
end PackSource_P0_9_5_1_2_2Aux1

section PackSource_P0_9_5_1_2_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_2

noncomputable section
open K1_13 (Row)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus liftRow graph graphIdeal graphPoint)
open K1_13_5_4_2 (JetPoint graphLocus graphCurve fourCutIdeal pointIdeal
  eval_liftRow_graphPoint eval_graph_graphPoint eval_represents_iff)
open K1_13_5_4_2_3 (sep liftedSep openLift openLift_onOpen onOpen_kills
  length_atPrime_le_length_principalCut)
open P0_9_5_1 (LiftedChart componentLength oldCutIdeal)
open P0_9_5_1_2 (factorCurves mem_factorCurves)
open MvPolynomial

open private graph_dimension from ProximityPrize.SubmissionLower.Fast048
open P0_9_5_1_2 (retained_dimension)
open private mem_iff_vanishes_regular from ProximityPrize.SubmissionLower.Fast073
open private exists_open_prime openAtPrimeEquivQuotient colength_eq_of_quotient_equiv
  from ProximityPrize.SubmissionLower.Fast076

private theorem threeCut_le_graphCurve {f : Row 3} (T : LiftedChart f)
    {P : Ideal (GeoRow 3)} (hP : oldCutIdeal f ≤ P) :
    threeCut f T ≤ graphCurve f P := by
  have hf (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval x (genericRow f) = 0 :=
    hx.1 _ (hP (Ideal.subset_span (by simp)))
  apply sup_le
  · apply Ideal.span_le.mpr
    intro u hu y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using hf x hx
    · exact eval_graph_graphPoint hx.2
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (eval_represents_iff T.cut_represents (hf x hx) hx.2).mpr
      (hx.1 _ (hP (Ideal.subset_span (by simp))))

private theorem graphCurve_comap {f : Row 3} {P : Ideal (GeoRow 3)} [P.IsPrime]
    (hsep : sep f ∉ P) : (graphCurve f P).comap (rename Fin.castSucc).toRingHom = P := by
  apply SetLike.ext
  intro a
  change liftRow a ∈ graphCurve f P ↔ a ∈ P
  rw [mem_iff_vanishes_regular hsep a]
  constructor
  · intro ha x hx
    simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using ha _ ⟨x, hx, rfl⟩
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using ha x hx

/-- Away from the separant, a prime over the lifted compatibility equations
is the reduced graph of its contraction. -/
private theorem prime_of_chart {f : Row 3} (T : LiftedChart f)
    (Q : Ideal (GeoRow 4)) [Q.IsPrime] (hcut : threeCut f T ≤ Q) (hsep : liftedSep f ∉ Q) :
    let P := Q.comap (rename Fin.castSucc).toRingHom
    oldCutIdeal f ≤ P ∧ graphCurve f P = Q := by
  let P := Q.comap (rename Fin.castSucc).toRingHom
  let : P.IsPrime := Ideal.comap_isPrime _ Q
  let F := FractionRing (GeoRow 4 ⧸ Q)
  let q : GeoRow 4 →+* F := (algebraMap (GeoRow 4 ⧸ Q) F).comp (Ideal.Quotient.mk Q)
  have hq (b : GeoRow 4) : q b = 0 ↔ b ∈ Q := by
    change algebraMap (GeoRow 4 ⧸ Q) F (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hsq : q (liftedSep f) ≠ 0 := fun h => hsep ((hq _).mp h)
  let qOpen := openLift (threeCut f T) (liftedSep f) q
    (fun b hb => RingHom.mem_ker.mpr ((hq b).mpr (hcut hb))) (isUnit_iff_ne_zero.mpr hsq)
  have hqOpen (b : GeoRow 4) : qOpen (graphMap f T b) = q b := openLift_onOpen _ _ _ _ _ b
  have hP : oldCutIdeal f ≤ P := by
    intro a ha
    change liftRow a ∈ Q
    apply (hq _).mp
    rw [← hqOpen, ← graphEquiv_on, onOpen_kills ha, map_zero, map_zero]
  refine ⟨hP, ?_⟩
  apply SetLike.ext
  intro b
  let e := graphEquiv f T
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (oldCutIdeal f) (sep f)) (e.symm (graphMap f T b))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e.symm (graphMap f T b) * oldMap f (sep f) ^ n = oldMap f a at hc
  have hab : graphMap f T b * graphMap f T (liftedSep f) ^ n = graphMap f T (liftRow a) := by
    simpa only [e, map_mul, map_pow, RingEquiv.apply_symm_apply, graphEquiv_on] using congrArg e hc
  have hfrac := congrArg qOpen hab
  simp only [map_mul, map_pow, hqOpen] at hfrac
  have hQmem : b ∈ Q ↔ a ∈ P := by
    change b ∈ Q ↔ liftRow a ∈ Q
    rw [← hq b, ← hq (liftRow a), ← hfrac, mul_eq_zero]
    simp only [pow_ne_zero n hsq, or_false]
  have hpoint (x : Fin 3 → GeometricX) (hx : x ∈ regularLocus f P) :
      eval (graphPoint f x) b * eval x (sep f) ^ n = eval x a := by
    have hs : eval (graphPoint f x) (liftedSep f) ≠ 0 := by
      rw [eval_liftRow_graphPoint]
      exact hx.2
    have hkill : threeCut f T ≤ RingHom.ker (eval (graphPoint f x)) := by
      intro g hg
      exact RingHom.mem_ker.mpr (threeCut_le_graphCurve T hP hg _ ⟨x, hx, rfl⟩)
    let w := openLift (threeCut f T) (liftedSep f) (eval (graphPoint f x)) hkill
      (isUnit_iff_ne_zero.mpr hs)
    have hw (g : GeoRow 4) : w (graphMap f T g) = eval (graphPoint f x) g :=
      openLift_onOpen _ _ _ _ _ g
    simpa only [map_mul, map_pow, hw, eval_liftRow_graphPoint] using congrArg w hab
  rw [hQmem, mem_iff_vanishes_regular (show sep f ∉ P from hsep)]
  constructor
  · intro hb x hx
    have hz : eval (graphPoint f x) b = 0 := hb _ ⟨x, hx, rfl⟩
    rw [← hpoint x hx, hz, zero_mul]
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (mul_eq_zero.mp ((hpoint x hx).trans (ha x hx))).resolve_right (pow_ne_zero n hx.2)

/-- The full localized compatibility schemes yield the same local colength
at matching primes. -/
private theorem chart_colength {f : Row 3} (T : LiftedChart f)
    (P : Ideal (GeoRow 3)) (Q : Ideal (GeoRow 4)) [P.IsPrime] [Q.IsPrime]
    (hQ : threeCut f T ≤ Q) (hsQ : liftedSep f ∉ Q)
    (hQP : Q.comap (rename Fin.castSucc).toRingHom = P) :
    let A := Localization.AtPrime P
    let B := Localization.AtPrime Q
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A)) =
      Module.length B (B ⧸ (threeCut f T).map (algebraMap (GeoRow 4) B)) := by
  obtain ⟨q, hprime, hq⟩ := exists_open_prime hQ hsQ
  let : q.IsPrime := hprime
  let e := graphEquiv f T
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime _ q
  have hp : p.comap (oldMap f) = P := by
    ext b
    change graphEquiv f T (oldMap f b) ∈ q ↔ b ∈ P
    rw [graphEquiv_on]
    change liftRow b ∈ q.comap (graphMap f T) ↔ b ∈ P
    rw [hq]
    change b ∈ Q.comap (rename Fin.castSucc).toRingHom ↔ b ∈ P
    rw [hQP]
  exact colength_eq_of_quotient_equiv
    ((openAtPrimeEquivQuotient p hp).symm.trans
      ((Localization.localRingEquiv p q e rfl).trans (openAtPrimeEquivQuotient q hq)))

private theorem graphCurve_le_point {f : Row 3} {P : Ideal (GeoRow 3)} {y : JetPoint}
    (hy : y ∈ graphLocus f P) : graphCurve f P ≤ pointIdeal y :=
  vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hy)

private theorem sep_notMem_point {f : Row 3} {P : Ideal (GeoRow 3)} {y : JetPoint}
    (hy : y ∈ graphLocus f P) : liftedSep f ∉ pointIdeal y := by
  obtain ⟨x, hx, rfl⟩ := hy
  intro hs
  apply hx.2
  rw [← eval_liftRow_graphPoint f x (sep f)]
  exact (mem_vanishingIdeal_singleton_iff _ _).mp hs

private theorem graph_is_curve {f : Row 3} (hf : Irreducible f)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (graphCurve f P).IsPrime ∧ (affineHilbertPolynomial (graphCurve f P)).natDegree = 1 := by
  obtain ⟨hm, hs⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hm.isPrime
  obtain ⟨hp, hdim⟩ := graph_dimension f P hs
  exact ⟨hp, hdim.trans (retained_dimension hf hP)⟩

private theorem point_isolated {f : Row 3} (hf : Irreducible f)
    (T : LiftedChart f) {L : GeoRow 4} (hL : ∀ P ∈ factorCurves f, L ∉ graphCurve f P)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) {y : JetPoint}
    (hy : y ∈ graphLocus f P) (hLy : eval y L = 0) :
    pointIdeal y ∈ (threeCut f T ⊔ Ideal.span {L}).minimalPrimes := by
  let m := pointIdeal y
  have hmsep : liftedSep f ∉ m := sep_notMem_point hy
  obtain ⟨hProper, hRet⟩ := mem_factorCurves.mp hP
  have hBm : threeCut f T ≤ m :=
    (threeCut_le_graphCurve T (Ideal.mem_retainedMinimalPrimes.mp hRet).1.le).trans
      (graphCurve_le_point hy)
  have hmL : L ∈ m := (mem_vanishingIdeal_singleton_iff _ _).mpr hLy
  refine ⟨⟨inferInstance, sup_le hBm ((Ideal.span_singleton_le_iff_mem _).mpr hmL)⟩, ?_⟩
  intro Q hQ hQm
  let q := Q.comap (rename Fin.castSucc).toRingHom
  have hQsep : liftedSep f ∉ Q := fun h => hmsep (hQm h)
  let : Q.IsPrime := hQ.1
  let : q.IsPrime := hQ.1.comap _
  obtain ⟨hIq, hGQ⟩ := prime_of_chart T Q (le_sup_left.trans hQ.2) hQsep
  have hsq : sep f ∉ q := hQsep
  obtain ⟨P', hP', hP'q⟩ := Ideal.exists_mem_retainedMinimalPrimes_le (Q := q) hIq hsq
  have hP'f : P' ∈ factorCurves f := mem_factorCurves.mpr ⟨hProper, hP'⟩
  have hle : graphCurve f P' ≤ Q := by
    rw [← hGQ]
    exact vanishingIdeal_anti_mono
      (Set.image_mono fun _ hx => ⟨zeroLocus_anti_mono hP'q hx.1, hx.2⟩)
  obtain ⟨hp', hd⟩ := graph_is_curve hf hP'f
  have hLQ : Ideal.span {L} ≤ Q := le_sup_right.trans hQ.2
  have hcut := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp' (hL P' hP'f) le_rfl).1
  rw [hd, Nat.sub_self] at hcut
  have hdeg := (natDegree_affineHilbertPolynomial_le_of_le (sup_le hle hLQ)).trans hcut
  let : Module.Finite GeometricX (GeoRow 4 ⧸ Q) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  have hfield : IsField (GeoRow 4 ⧸ Q) :=
    isField_of_isIntegral_of_isField' (R := GeometricX) (Field.toIsField _)
  exact (Ideal.Quotient.maximal_of_isField Q hfield).eq_of_le
    (inferInstance : m.IsPrime).ne_top hQm |>.ge

theorem proof : P0_9_5_1_2.c2 := by
  intro f hf _ T L hL P hP y hy hLy
  have hJ : fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L =
      threeCut f T ⊔ Ideal.span {L} := by
    simp [fourCutIdeal, threeCut, graphIdeal, Ideal.span_insert, sup_assoc]
  dsimp only
  rw [hJ]
  refine ⟨point_isolated hf T hL hP hy hLy, ?_⟩
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hmin.isPrime
  let Q := graphCurve f P
  let : Q.IsPrime := (graph_is_curve hf hP).1
  have hQy : Q ≤ pointIdeal y := graphCurve_le_point hy
  have hLiftSep : liftedSep f ∉ Q := fun h => sep_notMem_point hy (hQy h)
  rw [componentLength, dite_eq_left hmin.isPrime]
  rw [chart_colength T P Q (threeCut_le_graphCurve T hmin.le) hLiftSep (graphCurve_comap hsep)]
  exact length_atPrime_le_length_principalCut hQy
    ((mem_vanishingIdeal_singleton_iff _ _).mpr hLy) (hL P hP)

end

end P0_9_5_1_2_2
end PackSource_P0_9_5_1_2_2Proof

section PackSource_P0_9_5_1_2_3Variation
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_3
noncomputable section

open K1_13 (Shape)
open K1_13_5 (lowBox graphBox liftedBox)
open K1_13_5_4_2 (ExponentSpace capBody mixedVolume4)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation
  volumeQuotient rest univ_eq_insert zero_notMem_rest)
open K1_13_5_4_2_5_2_1 (cap_polytope closedOrthant)
open P0_9 (taylorLength)
open P0_9_5_1_2 (lastBox lastMixedVolume)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology

open private K1_13_5_4_2_5.sumShape sumChamber sum_capBody capBody_zero from ProximityPrize.SubmissionLower.Fast048
open private labelHull_eq positivePolynomial from ProximityPrize.SubmissionLower.Fast071
open private weights polar_linear from ProximityPrize.SubmissionLower.Fast048
open private volume_zero_height from ProximityPrize.SubmissionLower.Fast048

def boxShape : Fin 4 → Shape := ![lowBox, graphBox, liftedBox (taylorLength + 1), lastBox]

def boxHeight : Fin 4 → ℕ := ![0, 1, taylorLength - 1, taylorLength]

abbrev baseShape (S : Finset (Fin 4)) : Shape := K1_13_5_4_2_5.sumShape S boxShape

def baseHeight (S : Finset (Fin 4)) : ℕ := ∑ i ∈ S, boxHeight i

private def base (S : Finset (Fin 4)) : Set ExponentSpace :=
  capBody (baseShape S) (baseHeight S)

private def slots (P : Set ExponentSpace) : Fin 4 → Set ExponentSpace :=
  Function.update (fun i => capBody (boxShape i) (boxHeight i)) 0 P

private theorem mixed_eq (P : Set ExponentSpace) : lastMixedVolume P = mixedVolume4 (slots P) := by
  unfold lastMixedVolume
  congr 1
  funext i
  fin_cases i <;> rfl

theorem box_chamber (i : Fin 4) : Chamber (boxShape i) := by
  fin_cases i <;> exact ⟨by decide, by decide⟩

theorem base_chamber (S : Finset (Fin 4)) : Chamber (baseShape S) :=
  sumChamber S boxShape box_chamber

private theorem slots_nonempty (P : Set ExponentSpace) (hP : FirstBody P)
    (i : Fin 4) : 0 ∈ slots P i := by
  by_cases hi : i = 0
  · simpa [slots, hi] using hP.zero_mem
  · simp [slots, Function.update_of_ne hi, capBody]

private theorem volume_polynomial (P : Set ExponentSpace) (hP : FirstBody P) :
    ∃ p : MvPolynomial (Fin 4) ℝ, p.IsHomogeneous 4 ∧
      ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) →
        p.eval w = (volume (∑ i, w i • slots P i)).toReal := by
  classical
  have hslot (i : Fin 4) :
      ∃ v : Finset ExponentSpace, slots P i = convexHull ℝ (v : Set ExponentSpace) := by
    by_cases hi : i = 0
    · subst i
      obtain ⟨s, hs, hr⟩ := hP.polytope
      exact ⟨hs.toFinset, by simpa [slots] using hr⟩
    · rw [slots, Function.update_of_ne hi]
      exact cap_polytope _ _ (box_chamber i)
  choose v hv using hslot
  obtain ⟨p, hp, he⟩ := positivePolynomial K1_13_5_4_2_5_2_1_1.proof
    K1_13_5_4_2_5_2_1_2.proof (slots P) v hv
  refine ⟨p, hp, closedOrthant (slots P) ?_ (slots_nonempty P hP) ?_ p he⟩
  · intro i
    rw [hv i]
    exact convex_convexHull _ _
  · intro w
    rw [← labelHull_eq (slots P) v hv w]
    exact (Set.finite_range _).isCompact_convexHull ℝ

private theorem polar_slots (P : Set ExponentSpace) (hP : FirstBody P)
    (t : ℝ) (S : Finset (Fin 4)) :
    (∑ i, weights t S i • slots P i) = ∑ i ∈ S, slots (t • P) i := by
  calc
    _ = ∑ i ∈ S, (![t, 1, 1, 1] : Fin 4 → ℝ) i • slots P i := by
      rw [← Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
        (f := fun i => weights t S i • slots P i)]
      · exact Finset.sum_congr rfl (fun i hi => by simp [weights, hi])
      · intro i _ hi
        simp [weights, hi, Set.zero_smul_set (Set.nonempty_of_mem (slots_nonempty P hP i))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> simp [slots]

private theorem mixed_scale (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) (ht : 0 ≤ t) :
    lastMixedVolume (t • P) = t * lastMixedVolume P := by
  obtain ⟨p, hp, heval⟩ := volume_polynomial P hP
  have hw (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) (i : Fin 4) :
      0 ≤ weights s S i := by
    unfold weights
    apply ite_nonneg _ (le_refl (0 : ℝ))
    fin_cases i
    · exact hs
    all_goals exact zero_le_one
  have hpol (s : ℝ) (hs : 0 ≤ s) (S : Finset (Fin 4)) :
      p.eval (weights s S) = (volume (∑ i ∈ S, slots (s • P) i)).toReal := by
    rw [heval _ (hw s hs S), polar_slots P hP]
  simpa only [mixed_eq, mixedVolume4, hpol _ ht, hpol 1 zero_le_one, one_smul]
    using polar_linear p hp t

private theorem sum_slots (P : Set ExponentSpace) {S : Finset (Fin 4)} (h0 : 0 ∉ S) :
    (∑ i ∈ S, slots P i) = base S := by
  change _ = capBody (K1_13_5_4_2_5.sumShape S boxShape) (∑ i ∈ S, boxHeight i)
  rw [← sum_capBody _ _ _ box_chamber]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
  simp [slots, Function.update_of_ne hne]

private theorem mixed_increment (P : Set ExponentSpace) (t : ℝ) :
    lastMixedVolume (t • P) =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        ((volume (t • P + base S)).toReal - (volume (base S)).toReal) := by
  rw [mixed_eq, mixedVolume4, univ_eq_insert,
    Finset.sum_powerset_insert zero_notMem_rest, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have h0 : (0 : Fin 4) ∉ S := fun h => zero_notMem_rest (hsub h)
  have hs : S.card ≤ 3 :=
    (Finset.card_le_card hsub).trans (show rest.card ≤ 3 by decide)
  rw [Finset.sum_insert h0, Finset.card_insert_of_notMem h0,
    sum_slots _ h0, show slots (t • P) 0 = t • P by simp [slots]]
  have e₁ : 4 - S.card = (3 - S.card) + 1 := by omega
  have e₂ : 4 - (S.card + 1) = 3 - S.card := by omega
  rw [e₁, e₂, pow_succ]
  ring

private theorem empty_quotient (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) :
    volumeQuotient P (base ∅) t = 0 := by
  have hbase : base ∅ = 0 := by simp [base, K1_13_5_4_2_5.sumShape, baseHeight, capBody_zero]
  have hPz : volume (t • P) = 0 := by
    apply volume_zero_height
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp [Pi.smul_apply, hP.zero_height y hy]
  rw [volumeQuotient, hbase, add_zero, hPz,
    show (0 : Set ExponentSpace) = {0} by rfl]
  simp

private theorem tendsto_quotient (P : Set ExponentSpace)
    (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) {S : Finset (Fin 4)} (hS : S ⊆ rest) :
    Tendsto (volumeQuotient P (base S)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation (baseShape S) (baseHeight S)
        (totalSupport P) (indexSupport P) (topSupport P))) := by
  by_cases he : S = ∅
  · subst S
    rw [show volumeQuotient P (base ∅) = (fun _ : ℝ => 0) from funext (empty_quotient P hP)]
    simp [capFirstVariation, K1_13_5_4_2_5.sumShape, baseHeight]
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    apply K1_13_5_4_2_5_2_2.proof P hP hsub _ _ (base_chamber S)
    · exact Finset.sum_lt_sum_of_nonempty hn (fun i _ => by fin_cases i <;> decide)
    · exact Finset.sum_pos (fun i _ => by fin_cases i <;> decide) hn
    · apply Finset.sum_pos _ hn
      intro i hi
      have hne : i ≠ 0 := fun h0 => zero_notMem_rest (h0 ▸ hS hi)
      fin_cases i
      · exact (hne rfl).elim
      all_goals decide

/-- Polarize the first variation at the retuned sums of the three fixed boxes. -/
theorem variation_eq (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume P =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        capFirstVariation (baseShape S) (baseHeight S)
          (totalSupport P) (indexSupport P) (topSupport P) := by
  have hlim := tendsto_finsetSum rest.powerset (fun S hS =>
    (tendsto_quotient P hP hsub (Finset.mem_powerset.mp hS)).const_mul
      ((-1 : ℝ) ^ (3 - S.card)))
  have heq : (fun _ : ℝ => lastMixedVolume P) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun t : ℝ => ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        volumeQuotient P (base S) t) := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht
    have ht' : 0 < t := ht
    have hquot : lastMixedVolume (t • P) / t = lastMixedVolume P := by
      rw [mixed_scale P hP t ht'.le]
      exact mul_div_cancel_left₀ _ ht'.ne'
    calc
      lastMixedVolume P = lastMixedVolume (t • P) / t := hquot.symm
      _ = _ := by simp only [mixed_increment, Finset.sum_div, volumeQuotient, mul_div_assoc]
  exact tendsto_const_nhds_iff.mp (hlim.congr' heq.symm)

end
end P0_9_5_1_2_3
end PackSource_P0_9_5_1_2_3Variation

section PackSource_P0_9_5_1_2_3Budget
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_3
noncomputable section

open K1_13 (Shape)
open K1_13_5 (lowBox)
open K1_13_5_4_2 (ExponentSpace capBody)
open K1_13_5_4_2_5 (FirstBody Chamber)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport capFirstVariation rest)
open P0_9_5 (mixedBudget)
open P0_9_5_1_2 (lastMixedVolume)
open scoped BigOperators

open P0_9_5 (mixedBudget_eq)

/-- Twice the first variation has natural coefficients on the chamber. -/
private def coefficients (s : Shape) (h : ℕ) : ℕ × ℕ × ℕ :=
  (2 * h * s.t * (s.j - s.t),
    h * s.t * (2 * (s.b - s.j) + s.t),
    h * (s.j - 2 * s.t) * (2 * s.b - s.j))

private theorem twice_variation (s : Shape) (h : ℕ) (hs : Chamber s) (B J T : ℝ) :
    2 * capFirstVariation s h B J T =
      (coefficients s h).1 * B + (coefficients s h).2.1 * J + (coefficients s h).2.2 * T := by
  have hB : s.j ≤ s.b := hs.1
  have hJ : 2 * s.t ≤ s.j := hs.2
  have ht : s.t ≤ s.j := by omega
  have hb : s.j ≤ 2 * s.b := by omega
  simp only [capFirstVariation, coefficients, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_sub hB, Nat.cast_sub hJ, Nat.cast_sub ht, Nat.cast_sub hb]
  ring

private def row (S : Finset (Fin 4)) : ℕ × ℕ × ℕ :=
  coefficients (baseShape S) (baseHeight S)

private theorem row_empty : row ∅ = (0, 0, 0) := rfl
private theorem row_graph : row (insert 1 ∅) = (1200, 3984, 191) := rfl
private theorem row_cut : row (insert 2 ∅) = (2977410381234205752, 9825450869307389184, 0) := rfl
private theorem row_last : row (insert 3 ∅) = (2977477264937227104, 9825671585476610448, 0) := rfl
private theorem row_graph_cut : row (insert 1 (insert 2 ∅)) =
    (2977476373143480000, 9825669088455000000, 3388815357552) := rfl
private theorem row_graph_last : row (insert 1 (insert 3 ∅)) =
    (2977543257834776400, 9825889807892206125, 3388866107123) := rfl
private theorem row_cut_last : row (insert 2 (insert 3 ∅)) =
    (23819550583684104974, 78604489815830631623, 0) := rfl
private theorem row_all : row (insert 1 (insert 2 (insert 3 ∅))) =
    (23819814552322828416, 78605362695726708896, 13555261163104) := rfl

private theorem alternating_three (F : Finset (Fin 4) → ℝ) :
    (∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) * F S) =
      F (insert 1 (insert 2 (insert 3 ∅))) -
        F (insert 1 (insert 2 ∅)) - F (insert 1 (insert 3 ∅)) - F (insert 2 (insert 3 ∅)) +
        F (insert 1 ∅) + F (insert 2 ∅) + F (insert 3 ∅) - F ∅ := by
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
  ring

private theorem twice_row (S : Finset (Fin 4)) (B J T : ℝ) :
    2 * capFirstVariation (baseShape S) (baseHeight S) B J T =
      (row S).1 * B + (row S).2.1 * J + (row S).2.2 * T :=
  twice_variation _ _ (base_chamber S) _ _ _

/-- The alternating first variation is linear in the three cap supports. -/
theorem mixed_formula (P : Set ExponentSpace) (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume P = 65991915950549 * totalSupport P +
      218219166437382 * indexSupport P + 3388789849310 * topSupport P := by
  rw [variation_eq P hP hsub]
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  generalize totalSupport P = B
  generalize indexSupport P = J
  generalize topSupport P = T
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (2 : ℝ), twice_row]
  rw [alternating_three, row_empty, row_graph, row_cut, row_last, row_graph_cut, row_graph_last,
    row_cut_last, row_all]
  simp only [Nat.cast_ofNat, Nat.cast_zero]
  ring

theorem price_eq : 65991915950549 * (lowBox.b : ℝ) + 218219166437382 * (lowBox.j : ℝ) +
    3388789849310 * (lowBox.t : ℝ) = (mixedBudget : ℝ) := by
  rw [mixedBudget_eq]
  exact_mod_cast (show (65991915950549 * 120 + 218219166437382 * 48 +
    3388789849310 * 24 : ℕ) = 18474880859443656 by decide)

end
end P0_9_5_1_2_3
end PackSource_P0_9_5_1_2_3Budget

section PackSource_P0_9_5_1_2_3Proof
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_2_3
noncomputable section

open K1_13 (Row indexDegree)
open K1_13_5 (lowBox)
open K1_13_5_4 (genericRow liftRow)
open K1_13_5_4_2 (ExponentSpace downBody capBody)
open K1_13_5_4_2_5 (FirstBody firstBody_zero firstBody_row)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open P0_9_5 (SecondFactors mixedBudget)
open P0_9_5_1_2 (lastMixedVolume)
open MvPolynomial
open scoped BigOperators Pointwise

open private rowShape row_support downBody_subset from ProximityPrize.SubmissionLower.Fast048

private theorem sum_downBody_subset {n : ℕ} (f : Fin n → Row 3) (hf : SecondFactors f)
    (S : Finset (Fin n)) :
    (∑ i ∈ S, downBody (liftRow (genericRow (f i)))) ⊆ capBody lowBox 0 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Set.mem_finsetSum S _ x).mp hx
  have hb (i : Fin n) (hi : i ∈ S) : y i ∈ capBody (rowShape (f i)) 0 :=
    downBody_subset (row_support (f i)) (hy hi)
  have cap (degree : Fin n → ℕ) (b : ℕ) (h : (∑ i, degree i) ≤ b) :
      (∑ i ∈ S, (degree i : ℝ)) ≤ b := by
    rw [← Nat.cast_sum, Nat.cast_le]
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ S)).trans h
  simp only [capBody, Set.mem_ofPred_eq, Finset.sum_apply]
  refine ⟨fun j => Finset.sum_nonneg (fun i hi => (hb i hi).1 j), ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.1)).trans (cap _ _ hf.total)
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.1)).trans (cap _ _ hf.index)
  · exact (Finset.sum_le_sum (fun i hi => (hb i hi).2.2.2.1)).trans (cap _ _ hf.top)
  · rw [Nat.cast_zero]
    exact Finset.sum_nonpos (fun i hi => by simpa using (hb i hi).2.2.2.2)

private theorem support_add {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q)
    (L : ExponentSpace → ℝ) (hL : Continuous L) (ha : ∀ x y, L (x + y) = L x + L y) :
    sSup (L '' (P + Q)) = sSup (L '' P) + sSup (L '' Q) := by
  let ℓ := AddMonoidHom.mk' L ha
  change sSup (ℓ '' (P + Q)) = _
  have bounded {U : Set ExponentSpace} (hU : FirstBody U) : BddAbove (L '' U) := by
    obtain ⟨v, hv, rfl⟩ := hU.polytope
    exact (hv.isCompact_convexHull ℝ).bddAbove_image hL.continuousOn
  rw [Set.image_add ℓ]
  exact csSup_add ((Set.nonempty_of_mem hP.zero_mem).image L) (bounded hP)
    ((Set.nonempty_of_mem hQ.zero_mem).image L) (bounded hQ)

private theorem sum_mixed {ι : Type} (P : ι → Set ExponentSpace) (hP : ∀ i, FirstBody (P i))
    (hsub : ∀ S : Finset ι, (∑ i ∈ S, P i) ⊆ capBody lowBox 0) (S : Finset ι) :
    FirstBody (∑ i ∈ S, P i) ∧
      (∑ i ∈ S, lastMixedVolume (P i)) = lastMixedVolume (∑ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨firstBody_zero, ?_⟩
    have hz : (0 : Set ExponentSpace) ⊆ capBody lowBox 0 := by simpa using hsub ∅
    rw [mixed_formula _ firstBody_zero hz]
    simp [totalSupport, indexSupport, topSupport, show (0 : Set ExponentSpace) = {0} from rfl]
  | @insert i S hi ih =>
    let Q := ∑ j ∈ S, P j
    have hPi : P i ⊆ capBody lowBox 0 := by simpa using hsub {i}
    have hPQ : P i + Q ⊆ capBody lowBox 0 := by simpa only [Q, Finset.sum_insert hi] using hsub (insert i S)
    have hbody := (hP i).add ih.1
    simp only [Finset.sum_insert hi, ih.2]
    refine ⟨hbody, ?_⟩
    rw [mixed_formula (P i) (hP i) hPi, mixed_formula Q ih.1 (hsub S), mixed_formula _ hbody hPQ]
    have hB : totalSupport (P i + Q) = totalSupport (P i) + totalSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hJ : indexSupport (P i + Q) = indexSupport (P i) + indexSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun x y => by simp only [Pi.add_apply]; ring)
    have hT : topSupport (P i + Q) = topSupport (P i) + topSupport Q :=
      support_add (hP i) ih.1 _ (by fun_prop) (fun _ _ => rfl)
    rw [hB, hJ, hT]
    ring

theorem proof : P0_9_5_1_2.c3 := by
  intro n f hf
  let P (i : Fin n) := downBody (liftRow (genericRow (f i)))
  have hP (i : Fin n) : FirstBody (P i) := firstBody_row (hf.irreducible i).ne_zero
  have hs (S : Finset (Fin n)) : (∑ i ∈ S, P i) ⊆ capBody lowBox 0 := sum_downBody_subset f hf S
  obtain ⟨hbody, hsum⟩ := sum_mixed P hP hs Finset.univ
  change (∑ i, lastMixedVolume (P i)) ≤ (mixedBudget : ℝ)
  rw [hsum, mixed_formula _ hbody (hs _), ← price_eq]
  have bound (L : ExponentSpace → ℝ) (a : ℝ)
      (h : ∀ x ∈ (∑ i, P i), L x ≤ a) : sSup (L '' (∑ i, P i)) ≤ a := by
    apply csSup_le ((Set.nonempty_of_mem hbody.zero_mem).image L)
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hB : totalSupport (∑ i, P i) ≤ (lowBox.b : ℝ) :=
    bound _ _ (fun _ hx => (hs _ hx).2.1)
  have hJ : indexSupport (∑ i, P i) ≤ (lowBox.j : ℝ) :=
    bound _ _ (fun _ hx => (hs _ hx).2.2.1)
  have hT : topSupport (∑ i, P i) ≤ (lowBox.t : ℝ) :=
    bound _ _ (fun _ hx => (hs _ hx).2.2.2.1)
  gcongr

end
end P0_9_5_1_2_3
end PackSource_P0_9_5_1_2_3Proof

section PackSource_P0_9_5_1_3Aux1
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace P0_9_5_1_3

noncomputable section

open K1_13 (Row)
open K1_13_5 (compatibilityNumerator separant tangentNumerator)
open K1_13_5_4 (GeoRow genericRow genericCoeff genericCoeff_injective)
open K1_13_5_4_3 (TangentStable)
open K1_13_5_4_3_1 (tangentNumerator_add tangentNumerator_mul)
open P0_9 (taylorLength)
open P0_9_5 (Whole)
open P0_9_5_1 (oldCut oldNext oldCutIdeal componentLength SimpleInvariant)
open Polynomial

open private flat_rowToGeo rowToGeo_eq tangent_self from ProximityPrize.SubmissionLower.Fast048
open private generic_cut_regular from ProximityPrize.SubmissionLower.Fast074

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem map_eq_maximal_of_length_one (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) :
    (oldCutIdeal f).map (algebraMap (GeoRow 3) (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  classical
  unfold componentLength at h
  rw [dite_eq_left ‹P.IsPrime›, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  exact h

private theorem simple_saturation (f : Row 3) (P : Ideal (GeoRow 3))
    [P.IsPrime] (h : componentLength f P = 1) (x : Row 3) (hx : genericRow x ∈ P) :
    ∃ s : Row 3, genericRow s ∉ P ∧ s * x ∈ Ideal.span {f, oldCut f} := by
  let q := P.comap (algebraMap (Row 3) (GeoRow 3))
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : P.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime P
  let _ : Algebra A B := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Flat (Row 3) (GeoRow 3) := flat_rowToGeo
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P (algebraMap (Row 3) (GeoRow 3)) rfl)
    infer_instance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal (Row 3) := Ideal.span {f, oldCut f}
  have hJ : J.map (algebraMap (Row 3) (GeoRow 3)) = oldCutIdeal f := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, rowToGeo_eq,
      oldCutIdeal]
  have hJB : (J.map (algebraMap (Row 3) A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq (Row 3) A B,
      IsScalarTower.algebraMap_eq (Row 3) (GeoRow 3) B, ← Ideal.map_map, hJ]
    exact map_eq_maximal_of_length_one f P h
  have hxB : algebraMap A B (algebraMap (Row 3) A x) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsScalarTower.algebraMap_apply (Row 3) A B,
      IsScalarTower.algebraMap_apply (Row 3) (GeoRow 3) B, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by rwa [rowToGeo_eq])
  rw [← hJB] at hxB
  have hxA : algebraMap (Row 3) A x ∈ J.map (algebraMap (Row 3) A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap (Row 3) A))]
    exact hxB
  obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
  refine ⟨s, ?_, hsx⟩
  change algebraMap (Row 3) (GeoRow 3) s ∉ P at hs
  rwa [rowToGeo_eq] at hs

private theorem numerator_succ (f : Row 3) (P : Ideal (GeoRow 3)) (j : ℕ)
    (hj : genericRow (compatibilityNumerator f j) ∈ P) :
    genericRow (compatibilityNumerator f (j + 1)) ∈ P ↔
      genericRow (separant f) * genericRow (tangentNumerator f (compatibilityNumerator f j)) ∈ P := by
  have hterm :
      genericRow (((2 * j + 1 : ℕ) : Row 3) * compatibilityNumerator f j *
        tangentNumerator f (separant f)) ∈ P := by
    simp only [genericRow, map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hj)
  change (MvPolynomial.map genericCoeff) (_ - _) ∈ P ↔ _
  unfold genericRow at hterm ⊢
  rw [map_sub, P.sub_mem_iff_left hterm, map_mul]

theorem tangent_stable {f : Row 3} {P : Ideal (GeoRow 3)} (hp : P.IsPrime)
    (hle : oldCutIdeal f ≤ P) (hsep : genericRow (separant f) ∉ P)
    (hInv : SimpleInvariant f P) : TangentStable f P := by
  let := hp
  have hf : genericRow f ∈ P := hle (Ideal.subset_span (by simp))
  have hc : genericRow (oldCut f) ∈ P := hle (Ideal.subset_span (by simp))
  have hprod := (numerator_succ f P (taylorLength - 3) hc).mp hInv.2
  have hcut := (hp.mem_or_mem hprod).resolve_left hsep
  have hgen : ∀ z ∈ (Ideal.span {f, oldCut f} : Ideal (Row 3)),
      genericRow (tangentNumerator f z) ∈ P := by
    intro z hz
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
    rw [tangentNumerator_add, tangentNumerator_mul, tangentNumerator_mul, tangent_self,
      mul_zero, add_zero]
    simp only [genericRow, map_add, map_mul]
    exact P.add_mem (P.mul_mem_left _ hf)
      (P.add_mem (P.mul_mem_left _ hc) (P.mul_mem_left _ hcut))
  intro x hx
  obtain ⟨s, hs, hsx⟩ := simple_saturation f P hInv.1 x hx
  have hd := hgen (s * x) hsx
  rw [tangentNumerator_mul] at hd
  simp only [genericRow, map_add, map_mul] at hd
  change genericRow (tangentNumerator f s) * genericRow x +
    genericRow s * genericRow (tangentNumerator f x) ∈ P at hd
  have hz := P.sub_mem hd (P.mul_mem_left (genericRow (tangentNumerator f s)) hx)
  rw [add_sub_cancel_left] at hz
  exact (hp.mem_or_mem hz).resolve_left hs

theorem numerator_mem {f : Row 3} {P : Ideal (GeoRow 3)} (h : TangentStable f P)
    (hc : genericRow (oldCut f) ∈ P) {j : ℕ} (hj : taylorLength - 3 ≤ j) :
    genericRow (compatibilityNumerator f j) ∈ P := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction i with
  | zero => exact hc
  | succ i hi =>
    exact (numerator_succ f P _ hi).mpr (P.mul_mem_left _ (h _ hi))

/-- Every retained component of the retuned proper compatibility cut is a curve. -/
theorem component_dimension {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : Irreducible f) (hwhole : ¬ Whole f)
    (hP : P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))) :
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1 := by
  let F := genericRow f
  let G := genericRow (oldCut f)
  have hF : F ≠ 0 := by
    simpa only [F, genericRow, map_zero] using
      (MvPolynomial.map_injective _ genericCoeff_injective).ne hf.ne_zero
  have hregular := generic_cut_regular hf (show ¬ f ∣ oldCut f from hwhole)
  have hmin := (Ideal.mem_retainedMinimalPrimes.mp hP).1
  change P ∈ (Ideal.span {F, G}).minimalPrimes at hmin
  rw [Ideal.span_insert] at hmin
  have hp := hmin.isPrime
  obtain ⟨D, hD, hDP⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hmin.le)
  have hd := hD.isPrime
  have hFD : F ∈ D := hD.le (Ideal.mem_span_singleton_self F)
  have hDne : D ≠ ⊥ := fun h => hF (Ideal.mem_bot.mp (h ▸ hFD))
  have hDheight : D.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hD)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hDne))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hDheight).principal
  change D = Ideal.span {a} at ha
  have hGD : G ∉ D := by
    intro hG
    obtain ⟨b, hFb⟩ := Ideal.mem_span_singleton.mp (ha ▸ hFD)
    obtain ⟨c, hGc⟩ := Ideal.mem_span_singleton.mp (ha ▸ hG)
    have hb0 : b ≠ 0 := by
      intro hb
      exact hF (by simp [hFb, hb])
    have hdiv : F ∣ G * b := ⟨c, by rw [hGc, hFb, mul_right_comm]⟩
    obtain ⟨q, hq⟩ := hregular b hdiv
    have hb : b * (a * q) = b * 1 := by
      calc
        b * (a * q) = (a * b) * q := by rw [← mul_assoc, mul_comm b a]
        _ = b := by rw [← hFb, ← hq]
        _ = b * 1 := (mul_one _).symm
    have haUnit := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hb0 hb)
    exact hd.ne_top (ha.trans (Ideal.span_singleton_eq_top.mpr haUnit))
  have hcut : P ∈ (D ⊔ Ideal.span {G}).minimalPrimes :=
    ⟨⟨hp, sup_le hDP (le_sup_right.trans hmin.le)⟩, fun J hJ hJP =>
      hmin.2 ⟨hJ.1, sup_le (hD.le.trans (le_sup_left.trans hJ.2))
        (le_sup_right.trans hJ.2)⟩ hJP⟩
  have hsurface :=
    MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  rw [Nat.card_fin] at hsurface
  have hcurve := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  omega

end
end P0_9_5_1_3
end PackSource_P0_9_5_1_3Aux1

section PackSource_P0_9_5_1_3Aux2
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace P0_9_5_1_3

noncomputable section

open K1_13 (Row Geom)
open K1_13_5 (separant)
open K1_13_5_4 (GeoRow GeometricX genericRow regularLocus extendedAtJet)
open K1_13_5_4_3 (TangentStable trajectory pointEval taylorAt)
open K1_13_5_4_3_2
open P0_9 (physicalDegree taylorLength TrueWeightLE anchorCutoff)
open P0_9_5_1 (oldCut oldCutIdeal)
open Polynomial

open private fresh_identity initial_residual from ProximityPrize.SubmissionLower.Fast073
open private specialize specialize_trajectory specialize_taylor from ProximityPrize.SubmissionLower.Fast073

private theorem trajectory_degree {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3)
    (U : A[X]) (hU : U.natDegree ≤ physicalDegree) {D : ℕ} (hf : TrueWeightLE f D) :
    (trajectory k f U).natDegree ≤ D := by
  classical
  rw [trajectory, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => (natDegree_mul_le).trans ?_
  apply le_trans _ (hf m hm)
  apply Nat.add_le_add natDegree_map_le
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans
    (Nat.sub_le_sub_right hU _)) |>.trans_eq (Nat.mul_comm _ _)

/-- Stability and the first missing jet force every subsequent compatibility
numerator to vanish, including the donor chart's first missing jet. -/
theorem stable_taylor {f : Row 3} {P : Ideal (GeoRow 3)}
    (hf : TrueWeightLE f anchorCutoff) (hc : oldCutIdeal f ≤ P)
    (h : TangentStable f P) {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) :
    (taylorAt f (pointEval y)).natDegree ≤ physicalDegree ∧
      extendedAtJet f (taylorAt f (pointEval y)) = 0 := by
  have hrow : genericRow f ∈ P := hc (Ideal.subset_span (by simp))
  have hcut : genericRow (oldCut f) ∈ P := hc (Ideal.subset_span (by simp))
  have hold : K1_13_5_4.oldCutIdeal f ≤ P := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases (show b = genericRow f ∨ b = genericRow (K1_13_5_4.oldCut f) by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb) with rfl | rfl
    · exact hrow
    · exact numerator_mem h hcut (by change 133549 ≤ 133669; decide)
  have hU : (localTaylor f P).natDegree ≤ physicalDegree := by
    rw [localTaylor, natDegree_taylor, natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hsmall : 3 ≤ j := by
      change 133551 < j at hj
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsmall
    rw [Nat.add_comm 3 n, centred, coeff_jetPolynomial]
    have hn : taylorLength - 3 ≤ n := by
      change 133551 < 3 + n at hj
      change 133549 ≤ n
      omega
    have hz : localJet f P (n + 3) = 0 := by
      rw [localJet, chart_zero f P (numerator_mem h hcut hn), mul_zero, zero_mul, zero_mul]
    split_ifs with hj'
    · exact hz
    · rfl
  refine ⟨by rw [← specialize_taylor hy]; exact natDegree_map_le.trans hU, ?_⟩
  have hOne : delta h (1 : Chart f P) = 0 := by
    simpa only [map_one] using delta_constants h (1 : Geom)
  have hShift : taylor (chartEval f P (MvPolynomial.C Polynomial.X)) (localTaylor f P) =
      centred f P := by
    rw [localTaylor, taylor_taylor, add_neg_cancel, taylor_zero]
  have hidentity := fresh_identity (delta h) hOne (delta_mul h) (constants (chartEval f P))
    (delta_constants h) _ (delta_centre h) f (localTaylor f P) (centred f P) hShift
    (centred_step h hold) (initial_residual hold)
    ((trajectory_degree _ _ _ hU hf).trans_lt (by change 16218719 < 2130706433; decide))
    (fun n hn hp => by
      rw [← map_natCast (constants (chartEval f P))]
      exact (natCast_geom_ne_zero hn hp).isUnit.map _)
  rw [← specialize_trajectory hy, hidentity, Polynomial.map_zero]

end
end P0_9_5_1_3
end PackSource_P0_9_5_1_3Aux2

section PackSource_P0_9_5_1_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace P0_9_5_1_3

noncomputable section

open K1_13 (Geom)
open K1_13_5 (RegularAt separant)
open K1_13_5_4 (GeoRow GeometricX extendedAtJet genericCoeff genericCoeff_injective
  genericRow jetPoint regularLocus eval_genericRow_at_point)
open K1_13_5_4_3 (coefficientImage coefficientPolynomial_reconstructAt curveIdeal
  eval_trajectory_at_centre pointEval reconstructAt reconstructAt_mark regularLocus_nonempty
  solves_on_closure taylorAt)
open K1_13_5_4_3_2 (jetPolynomial coeff_jetPolynomial)
open P0_9 (physicalDegree taylorLength)
open P0_9_5_1 (Coefficients coefficientPoint coefficientPolynomial oldCutIdeal mem_properComponents)
open Polynomial MvPolynomial

private theorem length_le : taylorLength ≤ K1_13.taylorLength := by
  change 133552 ≤ 133672
  decide

private def pad {m n : ℕ} (a : Fin m → GeometricX) (i : Fin n) : GeometricX :=
  if h : i.val < m then a ⟨i.val, h⟩ else 0

private def truncate {m n : ℕ} : GeoRow n →ₐ[GeometricX] GeoRow m :=
  aeval fun i => if h : i.val < m then MvPolynomial.X ⟨i.val, h⟩ else 0

private theorem truncate_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (truncate : GeoRow n →ₐ[GeometricX] GeoRow m) := by
  let r := rename (R := GeometricX) (Fin.castLE h)
  have he : truncate.comp r = AlgHom.id GeometricX (GeoRow m) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rename_X, truncate, MvPolynomial.aeval_X, AlgHom.id_apply]
    exact dite_eq_left i.isLt
  exact fun p => ⟨r p, DFunLike.congr_fun he p⟩

private theorem eval_truncate {m n : ℕ} (a : Fin m → GeometricX) (p : GeoRow n) :
    MvPolynomial.eval a (truncate p) = MvPolynomial.eval (pad a) p := by
  change aeval a (truncate p) = aeval (pad a) p
  rw [truncate, comp_aeval_apply]
  apply congrArg (fun z : Fin n → GeometricX => aeval z p)
  funext i
  unfold pad
  split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]

private theorem pad_restrict {m n : ℕ} (h : m ≤ n) (a : Fin n → GeometricX)
    (hz : ∀ i : Fin n, m ≤ i.val → a i = 0) : pad (a ∘ Fin.castLE h) = a := by
  funext i
  unfold pad
  split_ifs with hi
  · exact congrArg a (Fin.ext rfl)
  · exact (hz i (Nat.le_of_not_lt hi)).symm

private theorem vanishingIdeal_restrict {m n : ℕ} (h : m ≤ n)
    (C : Set (Fin n → GeometricX)) (hz : ∀ a ∈ C, ∀ i : Fin n, m ≤ i.val → a i = 0) :
    vanishingIdeal GeometricX C =
      (vanishingIdeal GeometricX ((fun a => a ∘ Fin.castLE h) '' C)).comap
        (truncate : GeoRow n →ₐ[GeometricX] GeoRow m).toRingHom := by
  ext p
  constructor
  · intro hp a ha
    obtain ⟨b, hb, rfl⟩ := ha
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0
    rw [eval_truncate, pad_restrict h b (hz b hb)]
    exact hp b hb
  · intro hp b hb
    have ha := hp (b ∘ Fin.castLE h) ⟨b, hb, rfl⟩
    change MvPolynomial.eval (b ∘ Fin.castLE h) (truncate p) = 0 at ha
    rwa [eval_truncate, pad_restrict h b (hz b hb)] at ha

private theorem polynomial_pad {m n : ℕ} (h : m ≤ n) (a : Fin m → GeometricX) :
    (∑ i : Fin n, Polynomial.monomial i.val (pad a i)) =
      ∑ i : Fin m, Polynomial.monomial i.val (a i) := by
  let c : ℕ → GeometricX := fun j => if hj : j < m then a ⟨j, hj⟩ else 0
  change jetPolynomial n c = _
  have he : (∑ i : Fin m, Polynomial.monomial i.val (a i)) = jetPolynomial m c := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, dite_eq_left i.isLt, Fin.eta]
  rw [he]
  ext j
  simp only [coeff_jetPolynomial]
  by_cases hj : j < m
  · rw [ite_eq_left hj, ite_eq_left (hj.trans_le h)]
  · simp [c, hj]

/-- On a simple invariant component the longer donor reconstruction has a
zero tail, so its coefficient curve lies in the retuned coefficient space. -/
theorem proof : P0_9_5_1.c3 := by
  intro n f hf a ha hs
  rcases a with ⟨i, P⟩
  obtain ⟨hw, hm⟩ := mem_properComponents.mp ha
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp hm
  have hp := hmin.isPrime
  have hle := hmin.le
  have hstable := tangent_stable hp hle hsep hs
  have hdim := component_dimension (hf.irreducible i) hw hm
  obtain ⟨hprime, hcurve⟩ :=
    K1_13_5_4_3_4.proof (f i) P hp hsep hdim
  have hTaylor := fun y hy => stable_taylor (hf.weight i) hle hstable (y := y) hy
  let C := coefficientImage (f i) P
  let Q := vanishingIdeal GeometricX ((fun b => b ∘ Fin.castLE length_le) '' C)
  have hz : ∀ b ∈ C, ∀ j : Fin K1_13.taylorLength, taylorLength ≤ j.val → b j = 0 := by
    rintro b ⟨y, hy, rfl⟩ j hj
    exact coeff_eq_zero_of_natDegree_lt ((hTaylor y hy).1.trans_lt (Nat.lt_of_succ_le hj))
  let T : GeoRow K1_13.taylorLength →ₐ[GeometricX] GeoRow taylorLength := truncate
  have hT : Function.Surjective T := truncate_surjective length_le
  have hQ : curveIdeal (f i) P = Q.comap T.toRingHom :=
    vanishingIdeal_restrict length_le C hz
  have hQprime : Q.IsPrime := by
    have hker : RingHom.ker T.toRingHom ≤ curveIdeal (f i) P := by
      rw [hQ]
      intro p hp'
      change T p = 0 at hp'
      change T p ∈ Q
      rw [hp']
      exact Q.zero_mem
    let := hprime
    have hmap := Ideal.map_isPrime_of_surjective (f := T.toRingHom) hT hker
    rwa [hQ, Ideal.map_comap_of_surjective T.toRingHom hT] at hmap
  have hQdim : (affineHilbertPolynomial Q).natDegree = 1 := by
    rw [hQ] at hcurve
    change (affineHilbertPolynomial (Q.comap T)).natDegree = 1 at hcurve
    rwa [natDegree_affineHilbertPolynomial_comap_of_surjective T hT Q] at hcurve
  have hmem (b : K1_13_5_4.Coefficients) (hb : b ∈ C) :
      b ∘ Fin.castLE length_le ∈ zeroLocus GeometricX Q :=
    zeroLocus_vanishingIdeal_le _ ⟨b, hb, rfl⟩
  have hpoly (b : Coefficients) :
      K1_13_5_4.coefficientPolynomial (pad b) = coefficientPolynomial b :=
    polynomial_pad length_le b
  refine ⟨Q, ⟨hQprime, hQdim, ?_, ?_⟩, ?_⟩
  · intro b hb
    have hpad : pad b ∈ zeroLocus GeometricX (curveIdeal (f i) P) := by
      intro p hp'
      change MvPolynomial.eval (pad b) p = 0
      rw [← eval_truncate]
      exact hb (T p) (by rw [hQ] at hp'; exact hp')
    rw [← hpoly b]
    exact solves_on_closure _ _ (fun y hy => (hTaylor y hy).2) _ hpad
  · obtain ⟨y, hy⟩ := regularLocus_nonempty (f i) P hp hsep
    let b := reconstructAt (f i) y
    have hb : b ∈ C := ⟨y, hy, rfl⟩
    refine ⟨b ∘ Fin.castLE length_le, hmem b hb, ?_⟩
    rw [← hpoly, pad_restrict length_le b (hz b hb), coefficientPolynomial_reconstructAt]
    intro hzero
    apply hy.2
    rw [← eval_trajectory_at_centre (f i), hzero, Polynomial.eval_zero]
  · intro S hS hy
    have hfP : genericRow (f i) ∈ P := hle (Ideal.subset_span (by simp))
    have he : MvPolynomial.eval (jetPoint S) (genericRow (f i)) = 0 := hy.1 _ hfP
    have hn : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := hy.2
    rw [eval_genericRow_at_point] at he hn
    have hr : RegularAt 2 (f i) S :=
      ⟨genericCoeff_injective (he.trans genericCoeff.map_zero.symm),
        fun h => hn (by rw [show K1_13.atJet (separant (f i)) S = 0 from h, map_zero])⟩
    have hS' : S.natDegree ≤ 133671 := hS.trans (by change 133551 ≤ 133671; decide)
    have hres := hmem (reconstructAt (f i) (jetPoint S)) ⟨jetPoint S, hy, rfl⟩
    rw [reconstructAt_mark (f i) S hS' hr] at hres
    exact hres

end
end P0_9_5_1_3
end PackSource_P0_9_5_1_3Proof

section PackSource_P0_9_5_1_4Padding
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_4

noncomputable section

open K1_13_5_4 (GeometricX)
open MvPolynomial
open scoped BigOperators

private def restrictVariables {k : Type*} [Field k] {m n : ℕ} :
    Fin n → MvPolynomial (Fin m) k :=
  fun i => if hi : i.val < m then MvPolynomial.X ⟨i.val, hi⟩ else 0

private theorem restrict_rename {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (p : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval restrictVariables (rename (Fin.castLE h) p) = p := by
  have he : (MvPolynomial.aeval restrictVariables).comp (rename (R := k) (Fin.castLE h)) =
      AlgHom.id k (MvPolynomial (Fin m) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [restrictVariables, i.isLt]
  exact DFunLike.congr_fun he p

private theorem padded_hilbert {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (Q : Ideal (MvPolynomial (Fin m) k)) :
    affineHilbertPolynomial (Q.comap (MvPolynomial.aeval (R := k)
      (restrictVariables : Fin n → MvPolynomial (Fin m) k))) = affineHilbertPolynomial Q := by
  let r := MvPolynomial.aeval (R := k) (restrictVariables (k := k) (m := m) (n := n))
  let P := Q.comap r
  let s := rename (R := k) (Fin.castLE h)
  have hSQ : Q ≤ P.comap s := by
    intro p hp
    change r (s p) ∈ Q
    rwa [restrict_rename h]
  let g := Ideal.quotientMapₐ Q r (show P ≤ Q.comap r from le_rfl)
  let j := Ideal.quotientMapₐ P s hSQ
  have hg : Function.Injective g := Ideal.quotientMap_injective
  have hj : Function.Injective j := Ideal.quotientMap_injective' (H := hSQ) (by
    intro p hp
    change r (s p) ∈ Q at hp
    rwa [restrict_rename h] at hp)
  have hgX (i : Fin n) : g (Ideal.Quotient.mk P (MvPolynomial.X i)) ∈ quotientDegreeLE Q 1 := by
    change Ideal.Quotient.mk Q (r (MvPolynomial.X i)) ∈ _
    rw [show r (MvPolynomial.X i) = restrictVariables i from MvPolynomial.aeval_X _ _]
    by_cases hi : i.val < m
    · rw [restrictVariables, dite_eq_left hi]
      exact mk_mem_quotientDegreeLE (totalDegree_X _).le
    · rw [restrictVariables, dite_eq_right hi, map_zero]
      exact zero_mem _
  have hjX (i : Fin m) : j (Ideal.Quotient.mk Q (MvPolynomial.X i)) ∈ quotientDegreeLE P 1 := by
    change Ideal.Quotient.mk P (s (MvPolynomial.X i)) ∈ _
    rw [show s (MvPolynomial.X i) = MvPolynomial.X (Fin.castLE h i) from rename_X _ _]
    exact mk_mem_quotientDegreeLE (totalDegree_X _).le
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial Q
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
  intro d hd
  rw [hN d hd]
  have heq : affineHilbertFunction Q d = affineHilbertFunction P d :=
    le_antisymm
      (by simpa only [one_mul] using affineHilbertFunction_le_of_injective j hj hjX d)
      (by simpa only [one_mul] using affineHilbertFunction_le_of_injective g hg hgX d)
  change (affineHilbertFunction Q d : ℚ) = (affineHilbertFunction P d : ℚ)
  exact_mod_cast heq

private theorem sum_monomial_eq_of_tail_zero {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n)
    (b : Fin n → k) (hb : ∀ i, m ≤ i.val → b i = 0) :
    (∑ i : Fin n, Polynomial.monomial i.val (b i)) =
      ∑ i : Fin m, Polynomial.monomial i.val (b (Fin.castLE h i)) := by
  classical
  let e : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  calc
    _ = ∑ i ∈ Finset.univ.map e, Polynomial.monomial i.val (b i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hi' : m ≤ i.val := le_of_not_gt fun hl =>
        hi (Finset.mem_map.mpr ⟨⟨i.val, hl⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [hb i hi', Polynomial.monomial_zero_right]
    _ = _ := Finset.sum_map _ _ _

theorem length_le : P0_9.taylorLength ≤ K1_13.taylorLength := by decide

private def dropCoefficients : K1_13_5_4.GeoRow K1_13.taylorLength →ₐ[GeometricX]
    K1_13_5_4.GeoRow P0_9.taylorLength :=
  MvPolynomial.aeval restrictVariables

/-- Place the shorter coefficient curve in the existing ambient space with
all coefficients from the shorter Taylor length onward equal to zero. -/
def pad (Q : P0_9_5_1.CoefficientIdeal) : K1_13_5_4.CoefficientIdeal :=
  Q.comap dropCoefficients

theorem pad_injective : Function.Injective pad :=
  Ideal.comap_injective_of_surjective dropCoefficients
    (fun p => ⟨rename (Fin.castLE length_le) p, restrict_rename length_le p⟩)

theorem pad_hilbert (Q : P0_9_5_1.CoefficientIdeal) :
    affineHilbertPolynomial (pad Q) = affineHilbertPolynomial Q :=
  padded_hilbert length_le Q

theorem pad_degree (Q : P0_9_5_1.CoefficientIdeal) :
    affineDegree (pad Q) = affineDegree Q := by
  unfold affineDegree
  rw [pad_hilbert]

theorem pad_points {Q : P0_9_5_1.CoefficientIdeal} {b : K1_13_5_4.Coefficients}
    (hb : b ∈ zeroLocus GeometricX (pad Q)) :
    let a := b ∘ Fin.castLE length_le
    a ∈ zeroLocus GeometricX Q ∧
      K1_13_5_4.coefficientPolynomial b = P0_9_5_1.coefficientPolynomial a := by
  dsimp only
  constructor
  · intro p hp
    have hv := hb (rename (Fin.castLE length_le) p)
      (show dropCoefficients (rename (Fin.castLE length_le) p) ∈ Q from
        (restrict_rename length_le p).symm ▸ hp)
    change eval b (rename (Fin.castLE length_le) p) = 0 at hv
    rwa [eval_rename] at hv
  · apply sum_monomial_eq_of_tail_zero length_le
    intro i hi
    have hx : MvPolynomial.X i ∈ pad Q := by
      change dropCoefficients (MvPolynomial.X i) ∈ Q
      simp [dropCoefficients, restrictVariables, Nat.not_lt.mpr hi]
    exact (eval_X (f := b) i).symm.trans (hb _ hx)

private def paddedPoint (a : P0_9_5_1.Coefficients) : K1_13_5_4.Coefficients :=
  fun i => if hi : i.val < P0_9.taylorLength then a ⟨i.val, hi⟩ else 0

private theorem eval_paddedPoint (a : P0_9_5_1.Coefficients) :
    MvPolynomial.aeval (paddedPoint a) =
      (MvPolynomial.aeval a).comp dropCoefficients := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i.val < P0_9.taylorLength <;>
    simp [dropCoefficients, restrictVariables, paddedPoint, hi]

theorem pad_actual {f : K1_13.Row 3} {Q : P0_9_5_1.CoefficientIdeal}
    (h : P0_9_5_1.ActualSolutionCurve f Q) : K1_13_5_4.ActualSolutionCurve f (pad Q) := by
  refine ⟨h.prime.comap dropCoefficients, ?_, ?_, ?_⟩
  · rw [pad_hilbert]
    exact h.dimension
  · intro b hb
    obtain ⟨ha, he⟩ := pad_points hb
    rw [he]
    exact h.solves _ ha
  · obtain ⟨a, ha, hs⟩ := h.regular
    have hb : paddedPoint a ∈ zeroLocus GeometricX (pad Q) := by
      intro p hp
      exact (DFunLike.congr_fun (eval_paddedPoint a) p).trans (ha _ hp)
    obtain ⟨_, he⟩ := pad_points hb
    exact ⟨paddedPoint a, hb, by
      have hrestrict : paddedPoint a ∘ Fin.castLE length_le = a := by
        funext i
        simp [paddedPoint, i.isLt]
      rw [he, hrestrict]
      exact hs⟩

end

end P0_9_5_1_4
end PackSource_P0_9_5_1_4Padding

section PackSource_P0_9_5_1_4Proof
set_option autoImplicit true
set_option autoImplicit false

namespace P0_9_5_1_4

noncomputable section

open K1_13 (Geom Row embed)
open K1_13_5 (separant)
open K1_13_5_4 (GeometricX extendedAtJet)
open K1_13_5_4_4
open P0_9 (taylorLength)
open P0_9_5 (Whole invariantBudget)
open P0_9_5_1 (CoefficientIdeal ActualSolutionCurve coefficientPolynomial oldCut)
open MvPolynomial Finset
open scoped BigOperators Polynomial

open private flat_of_injective regular_cut_of_flat_map from ProximityPrize.SubmissionLower.Fast067
open private curve_minimal from ProximityPrize.SubmissionLower.Fast067

private theorem donorCharts : K1_13_5_4_4.c1 :=
  K1_13_5_4_4_1.of_children K1_13_5_4_4_1_1.proof K1_13_5_4_4_1_2.proof

private def projectedIdeal (Q : CoefficientIdeal) : FreshJetIdeal := freshImage (pad Q)

private def retunedDivisor (f : Row 3) : FreshJetIdeal :=
  freshHypersurface f ⊔ Ideal.span {freshRow (oldCut f)}

private theorem compatibility_zero (f : Row 3) (S : GeometricX[X]) (k : ℕ)
    (hk : k + 3 ≤ K1_13.taylorLength) (hS : S.natDegree < k + 3)
    (hf : extendedAtJet f S = 0) : extendedAtJet (K1_13_5.compatibilityNumerator f k) S = 0 := by
  have h := K1_13_5_4_4_1_2.proof f S (hS.trans_le hk) hf k hk
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k + 3) hS, mul_zero, mul_zero] at h
  have htwo : (2 : GeometricX[X]) ≠ 0 := by
    let g : K1.K →+* GeometricX[X] :=
      Polynomial.C.comp ((algebraMap Geom GeometricX).comp embed)
    have hne : (2 : K1.K) ≠ 0 := by decide
    exact fun hz => hne (g.injective (by simpa only [map_ofNat, map_zero] using hz))
  exact (mul_eq_zero.mp h).resolve_left htwo

private theorem cut_zero (f : Row 3) (S : GeometricX[X])
    (hS : S.natDegree < taylorLength) (hf : extendedAtJet f S = 0) :
    extendedAtJet (oldCut f) S = 0 := by
  have hk : taylorLength - 3 + 3 = taylorLength := rfl
  change extendedAtJet (K1_13_5.compatibilityNumerator f (taylorLength - 3)) S = 0
  exact compatibility_zero f S _ (hk.le.trans length_le) (hk.symm ▸ hS) hf

private theorem projected_on_divisor {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) : retunedDivisor f ≤ projectedIdeal Q := by
  have hold := pad_actual h
  have hrow : freshHypersurface f ≤ projectedIdeal Q :=
    le_sup_left.trans (((donorCharts f).1 (pad Q) hold).on_divisor)
  refine sup_le hrow ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  change freshProjection (freshRow (oldCut f)) ∈ extendIdeal (pad Q)
  rw [(K1_13_5_4_4_1_1.proof (pad Q) hold.prime).2]
  intro b hb
  obtain ⟨ha, he⟩ := pad_points hb
  have hdeg (a : P0_9_5_1.Coefficients) : (coefficientPolynomial a).natDegree < taylorLength := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)
  rw [K1_13_5_4_4_1.point_projected, K1_13_5_4_4_1.eval_row, he,
    cut_zero f _ (hdeg _) (h.solves _ ha), map_zero]

private theorem projected_comparison {f : Row 3} {Q : CoefficientIdeal}
    (h : ActualSolutionCurve f Q) :
    (projectedIdeal Q).IsPrime ∧ (affineHilbertPolynomial (projectedIdeal Q)).natDegree = 1 ∧
      affineDegree Q ≤ affineDegree (projectedIdeal Q) := by
  have hold := pad_actual h
  have hc := (donorCharts f).1 (pad Q) hold
  obtain ⟨hdim, hdeg⟩ := K1_13_5_4_4_2.proof (pad Q) hold.prime hold.dimension
    hc.extended_prime hc.birational
  exact ⟨hc.extended_prime.comap freshProjection, hdim, (pad_degree Q).symm.trans_le hdeg⟩

/-- The properness argument is unchanged, with the compatibility numerator
at the shorter Taylor length used as the nonzero divisor. -/
private theorem retunedCut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular (Ideal.Quotient.mk (freshHypersurface f) (freshRow (oldCut f))) := by
  have hp : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  apply regular_cut_of_flat_map freshCoeff (flat_of_injective freshCoeff freshCoeff_injective)
  · exact fun _ _ h => mul_left_cancel₀ hf.ne_zero h
  · exact fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h

private theorem factor_degree_sum (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (T : Finset FreshJetIdeal)
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ retunedDivisor f ≤ Q ∧
      (affineHilbertPolynomial Q).natDegree = 1) :
    (∑ Q ∈ T, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  by_cases hEmpty : T = ∅
  · rw [hEmpty, sum_empty]
    positivity
  have hPproper : freshHypersurface f ≠ ⊤ := by
    obtain ⟨Q, hQ⟩ := nonempty_iff_ne_empty.mpr hEmpty
    exact ne_top_of_le_ne_top (hT Q hQ).1.ne_top
      (le_sup_left.trans (hT Q hQ).2.1)
  have hPdim : (affineHilbertPolynomial (freshHypersurface f)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      (freshRow_ne_zero hf.ne_zero) hPproper
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial (freshHypersurface f)).natDegree + 1 = 3 at h
    omega
  have hcut := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (retunedCut_regular hf hw) (freshRow_degree_le (oldCut f))
  rw [hPdim] at hcut
  have hJdim : (affineHilbertPolynomial (retunedDivisor f)).natDegree ≤ 1 := hcut.1
  have hsub : T ⊆ (retunedDivisor f).minimalPrimesFinset := by
    intro Q hQ
    obtain ⟨hp, hle, hdim⟩ := hT Q hQ
    exact Ideal.mem_minimalPrimesFinset.mpr (curve_minimal hp hle hJdim hdim)
  have hdeg : affineDegree (freshHypersurface f) ≤ (f.totalDegree : ℚ) := by
    rw [freshHypersurface, affineDegree_span_singleton (freshRow_ne_zero hf.ne_zero)]
    exact_mod_cast freshRow_degree_le f
  calc
    (∑ Q ∈ T, affineDegree Q) = ∑ Q ∈ T, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_congr rfl
      intro Q hQ
      rw [affineDegree, (hT Q hQ).2.2, Polynomial.leadingCoeff, (hT Q hQ).2.2]
      simp
    _ ≤ ∑ Q ∈ (retunedDivisor f).minimalPrimesFinset, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro Q hQ _
      have hle := (Ideal.mem_minimalPrimesFinset.mp hQ).le
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((natDegree_affineHilbertPolynomial_le_of_le hle).trans hJdim)
        (eventually_eval_affineHilbertPolynomial_nonneg Q)
    _ ≤ (affineHilbertPolynomial (retunedDivisor f)).coeff 1 :=
      sum_coeff_affineHilbertPolynomial_minimalPrimes_le _ hJdim
    _ ≤ ((oldCut f).totalDegree : ℚ) * affineDegree (freshHypersurface f) := by
      simpa [retunedDivisor, affineDegree, hPdim, mul_assoc] using hcut.2
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      rw [Nat.cast_mul, mul_comm (f.totalDegree : ℚ)]
      exact mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)

private theorem curve_family_bound (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (C : Finset CoefficientIdeal) (hC : ∀ Q ∈ C, ActualSolutionCurve f Q) :
    (∑ Q ∈ C, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  have hinj : Set.InjOn projectedIdeal (C : Set CoefficientIdeal) := by
    intro Q hQ R hR he
    exact pad_injective ((donorCharts f).2 (pad_actual (hC Q hQ)) (pad_actual (hC R hR)) he)
  calc
    (∑ Q ∈ C, affineDegree Q) ≤ ∑ Q ∈ C, affineDegree (projectedIdeal Q) :=
      sum_le_sum fun Q hQ => (projected_comparison (hC Q hQ)).2.2
    _ = ∑ P ∈ C.image projectedIdeal, affineDegree P := (sum_image hinj).symm
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      apply factor_degree_sum f hf hw
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
      have hc := projected_comparison (hC Q hQ)
      exact ⟨hc.1, projected_on_divisor (hC Q hQ), hc.2.1⟩

private def cutterBound (b : ℕ) : ℕ :=
  1 + (2 * (taylorLength + 1) - 7) * (b - 1)

private theorem cutterBound_mono : Monotone cutterBound := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hab _)) _

theorem proof : P0_9_5_1.c4 := by
  classical
  intro n f hf hcut C hsource
  by_cases hEmpty : C = ∅
  · subst C
    exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨Q₀, hQ₀⟩ := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨i₀, _⟩ := hsource Q₀ hQ₀
  let pick (Q : CoefficientIdeal) : Fin n :=
    if hQ : Q ∈ C then Classical.choose (hsource Q hQ) else i₀
  have hpick (Q : CoefficientIdeal) (hQ : Q ∈ C) :
      ¬ Whole (f (pick Q)) ∧ ActualSolutionCurve (f (pick Q)) Q := by
    simpa only [pick, dite_eq_left hQ] using Classical.choose_spec (hsource Q hQ)
  let part (i : Fin n) := C.filter fun Q => pick Q = i
  have hlocal (i : Fin n) : (∑ Q ∈ part i, affineDegree Q) ≤
      ((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) := by
    have hpart (Q : CoefficientIdeal) (hQ : Q ∈ part i) :
        ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q := by
      obtain ⟨hm, hi⟩ := mem_filter.mp hQ
      simpa only [hi] using hpick Q hm
    by_cases hw : Whole (f i)
    · have he : part i = ∅ := eq_empty_iff_forall_notMem.mpr fun Q hQ => (hpart Q hQ).1 hw
      rw [he, sum_empty]
      positivity
    exact curve_family_bound _ (hf.irreducible i) hw _ fun Q hQ => (hpart Q hQ).2
  have hnat : (∑ i : Fin n, (f i).totalDegree * (oldCut (f i)).totalDegree) ≤ invariantBudget := by
    calc
      _ ≤ ∑ i : Fin n, (f i).totalDegree * cutterBound 120 := by
        apply sum_le_sum
        intro i _
        have hi := (single_le_sum (f := fun j => (f j).totalDegree)
          (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hf.total
        exact Nat.mul_le_mul_left _ ((hcut i).trans (cutterBound_mono hi))
      _ = (∑ i : Fin n, (f i).totalDegree) * cutterBound 120 := by rw [sum_mul]
      _ ≤ invariantBudget := Nat.mul_le_mul_right _ hf.total
  have hsum : (∑ Q ∈ C, affineDegree Q) ≤ (invariantBudget : ℚ) := by
    calc
      _ = ∑ i : Fin n, ∑ Q ∈ part i, affineDegree Q :=
        (sum_fiberwise_of_maps_to (t := (univ : Finset (Fin n)))
          (g := pick) (fun _ _ => mem_univ _) affineDegree).symm
      _ ≤ ∑ i : Fin n, (((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) : ℚ) :=
        sum_le_sum fun i _ => hlocal i
      _ ≤ (invariantBudget : ℚ) := by exact_mod_cast hnat
  have hex (Q : CoefficientIdeal) : ∃ d : ℕ, Q ∈ C → 0 < d ∧ affineDegree Q = (d : ℚ) := by
    by_cases hQ : Q ∈ C
    · have h := (hpick Q hQ).2
      have hp := pad_actual h
      obtain ⟨d, hd, he⟩ := curve_degree_nat (pad Q) hp.prime hp.dimension
      exact ⟨d, fun _ => ⟨hd, (pad_degree Q).symm.trans he⟩⟩
    · exact ⟨0, fun h => False.elim (hQ h)⟩
  let d (Q : CoefficientIdeal) := Classical.choose (hex Q)
  have hd (Q : CoefficientIdeal) (hQ : Q ∈ C) : 0 < d Q ∧ affineDegree Q = (d Q : ℚ) :=
    Classical.choose_spec (hex Q) hQ
  refine ⟨d, fun Q hQ => ⟨(hd Q hQ).1, (hd Q hQ).2.le⟩, ?_⟩
  have hcast : (∑ Q ∈ C, (d Q : ℚ)) ≤ (invariantBudget : ℚ) :=
    (sum_congr rfl fun Q hQ => (hd Q hQ).2.symm).trans_le hsum
  exact_mod_cast hcast

end

end P0_9_5_1_4
end PackSource_P0_9_5_1_4Proof

section PackSource_P0_9_5_2Capacity
set_option autoImplicit true
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace P0_9_5_2

noncomputable section

open P0 (K I node)
open P0_9 (Messages)
open K1_13 (Geom embed extend taylorLength)
open K1_13_5 (NodeCapacity)
open K1_13_5_5 (CoeffRing CoeffIndex coeffPoint)
open Finset MvPolynomial
open scoped BigOperators Polynomial
open private valueCut valueCut_degree valueCut_eval nodeCapacity_of_sections
  curve_degree_nat from ProximityPrize.SubmissionLower.Fast064

private theorem coeffPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coeffPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ η hη heq
  apply h.distinct hγ hη
  apply Polynomial.ext
  intro j
  by_cases hj : j < taylorLength
  · exact embed.injective (by simpa [coeffPoint] using congrFun heq ⟨j, hj⟩)
  · change ¬ j < 133672 at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := s γ) (by
          have hdeg : (s γ).natDegree ≤ 133551 := h.degree γ hγ
          omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (p := s η) (by
          have hdeg : (s η).natDegree ≤ 133551 := h.degree η hη
          omega)]

private theorem zeroDim_count {w Γ s} (h : Messages w Γ s) (P : Ideal CoeffRing)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let A := Γ.image (fun γ => coeffPoint (extend (s γ)))
  have hA : A.card = Γ.card := card_image_of_injOn (coeffPoint_injOn h)
  have hsub : (A : Set _) ⊆ zeroLocus Geom P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hA] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree

/-- The minimal primes of a proper node section cover its marked points.
The cut drops dimension by one and does not increase total degree. -/
private theorem section_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset K), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => (s γ).eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let prime := hP
  let cut := valueCut x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => (s γ).eval x = a
  let part (Q : Ideal CoeffRing) := U.filter fun γ => coeffPoint (extend (s γ)) ∈ zeroLocus Geom Q
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree ≤ 133671 :=
    (h.degree γ hγ).trans (by decide : 133551 ≤ 133671)
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (hdegree γ hγ) x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint (extend (s γ)) ∈ zeroLocus Geom (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (hdegree γ hγΓ) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc

private theorem curve_count {w Γ s} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P) :
    (Γ.card : ℚ) ≤ 2 * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hP hdim
  have hcap : NodeCapacity w Γ s δ := by
    apply nodeCapacity_of_sections
    intro i hi
    have hcount := section_count h hP hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun V hV Q _ hQ hp => by
        rw [one_mul]
        exact zeroDim_count (h.mono hV) Q (by omega) hp)
    rw [one_mul, hdeg] at hcount
    exact_mod_cast hcount
  have hcount := P0_9_5.nodeCapacity_count h hcap
  have hi : Γ.card ≤ 2 * δ := by omega
  rw [hdeg]
  exact_mod_cast hi

/-- The fixed-word price for a proper node section of a coefficient surface. -/
theorem surface_nodeCapacity {w Γ s} {d : ℕ} (h : Messages w Γ s) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ Γ, coeffPoint (extend (s γ)) ∈ zeroLocus Geom P)
    (hd : 2 * affineDegree P ≤ (d : ℚ)) :
    NodeCapacity w Γ s d := by
  classical
  apply nodeCapacity_of_sections
  intro i hi
  have hcount := section_count h hP hpoints (node i) (w i) hi (c := 2) (by norm_num)
    (fun _ hV _ hQ hdimQ hp => curve_count (h.mono hV) hQ (by omega) hp)
  exact_mod_cast hcount.trans hd

end

end P0_9_5_2
end PackSource_P0_9_5_2Capacity

section PackSource_P0_9_5_2Chart
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace P0_9_5_2

noncomputable section

open K1_13 (Geom embed Row atJet)
open K1_13_5 (RegularAt separant compatibilityNumerator)
open K1_13_5_5 K1_13_5_5_1
open P0_9 (taylorLength physicalDegree TrueWeightLE anchorCutoff)
open P0_9_5 (Whole)
open scoped Polynomial
open private evalRow coeffValue jetValue existsDerivation deriv_poly deriv_jet
  evalNumerator iterate_value from ProximityPrize.SubmissionLower.Fast071
open private reconstruct mapCoeffs_trajectory eq_zero_of_constant_coeffs
  from ProximityPrize.SubmissionLower.Fast071

/-- The donor coefficient ring is used with all coordinates beyond the retuned length zero. -/
def LowSupport (P : Ideal CoeffRing) : Prop :=
  ∀ i : CoeffIndex, taylorLength ≤ i.val → MvPolynomial.X i ∈ P

private theorem degree_trajectory {F : Type} [Field F] (k : Geom →+* F) {U : F[X]}
    (hU : U.natDegree < taylorLength) (f : Row 3) (hf : TrueWeightLE f anchorCutoff) :
    (trajectory k U f).natDegree ≤ anchorCutoff := by
  classical
  unfold trajectory
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, Polynomial.hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (physicalDegree - i.val) * e) := by
    unfold Finsupp.sum
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((Polynomial.hasseDeriv i.val U) ^ m i).natDegree ≤ (physicalDegree - i.val) * m i
    rw [Nat.mul_comm]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)

private theorem reconstruct_solution {F : Type} [Field F] [CharP F K1.p]
    (D : Derivation ℕ F F) (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (f : Row 3) (k : Geom →+* F) (x : F) (y : Fin 3 → F)
    (hx : D x = 1) (hk : ∀ a, D (k a) = 0)
    (hy₀ : D (y 0) = y 1) (hy₁ : D (y 1) = 2 * y 2)
    (hcut : ((D : F → F)^[L]) (y 0) = 0) (hzero : rowAt k x y f = 0)
    (hweight : ∀ U : F[X], U.natDegree < L → (trajectory k U f).natDegree < K1.p) :
    ∃ U : F[X], U.natDegree < L ∧ trajectory k U f = 0 ∧ jetAt x U = y := by
  let _ : Differential F :=
    ⟨Derivation.mk' D.toLinearMap.toAddMonoidHom.toIntLinearMap (fun a b => D.leibniz a b)⟩
  obtain ⟨U, hU, hc, hinit⟩ := reconstruct hL hchar x y hx hy₀ hy₁ hcut
  have hroot : (trajectory k U f).eval x = 0 := by
    rwa [eval_trajectory, hinit]
  exact ⟨U, hU, eq_zero_of_constant_coeffs _ hx _ (hweight U hU)
    (mapCoeffs_trajectory _ hk hc f) hroot, hinit⟩

private theorem chart_trajectory (f : Row 3) [(chartIdeal f).IsPrime]
    (L : ℕ) (hL : 3 ≤ L) (hchar : L < K1.p)
    (hs : freshRow (separant f) ∉ chartIdeal f)
    (hweight : ∀ U : (ChartField f)[X], U.natDegree < L →
      (trajectory (chartConstants f) U f).natDegree < K1.p)
    (hwhole : f ∣ compatibilityNumerator f (L - 3)) :
    ∃ U : (ChartField f)[X], U.natDegree < L ∧
      trajectory (chartConstants f) U f = 0 ∧ jetAt (chartCenter f) U = chartJets f := by
  let e := onChart f
  let π : FreshJetRing →+* ChartRing f := Ideal.Quotient.mk (chartIdeal f)
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = chartIdeal f := Ideal.mk_ker
  have hregular : evalRow e (separant f) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  let qr : CommRing (ChartRing f) := Ideal.Quotient.commRing (chartIdeal f)
  let qd : IsDomain (ChartRing f) := Ideal.Quotient.isDomain (chartIdeal f)
  let kf : Field (ChartField f) := FractionRing.field (ChartRing f)
  let ka : Algebra (ChartRing f) (ChartField f) := inferInstance
  let kl : IsFractionRing (ChartRing f) (ChartField f) := inferInstance
  obtain ⟨D, hD⟩ := @existsDerivation (ChartRing f) (ChartField f) qr kf ka qd kl π f
    hsurj hker hregular
  have hnum : evalRow e (compatibilityNumerator f (L - 3)) = 0 := by
    obtain ⟨q, hq⟩ := hwhole
    have hzero : evalRow e f = 0 :=
      (onChart_eq_zero f _).mpr (Ideal.mem_span_singleton_self _)
    rw [hq, map_mul, hzero, zero_mul]
  rw [evalNumerator e f D hD hregular] at hnum
  have hjet := (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hregular)
  have hcut : ((D : ChartField f → ChartField f)^[L]) (chartJets f 0) = 0 := by
    change ((D : ChartField f → ChartField f)^[L]) (jetValue e 0) = 0
    rw [show L = (L - 3 + 1) + 2 by omega,
      iterate_value e f D hD, hjet, mul_zero]
  let _ : CharP (ChartField f) K1.p :=
    charP_of_injective_ringHom ((chartConstants f).comp embed).injective K1.p
  have hx : D (chartCenter f) = 1 := by
    change D (coeffValue e Polynomial.X) = 1
    rw [deriv_poly e f D hD, Polynomial.derivative_X, map_one]
  have hk (a : Geom) : D (chartConstants f a) = 0 := by
    change D (coeffValue e (Polynomial.C a)) = 0
    rw [deriv_poly e f D hD, Polynomial.derivative_C, map_zero]
  have hzero : rowAt (chartConstants f) (chartCenter f) (chartJets f) f = 0 := by
    rw [rowAt_chart]
    exact (onChart_eq_zero f _).mpr (Ideal.mem_span_singleton_self _)
  exact reconstruct_solution D L hL hchar f (chartConstants f) (chartCenter f) (chartJets f)
    hx hk (deriv_jet e f D hD 0) (deriv_jet e f D hD 1) hcut hzero hweight

/-- Integrate on the generic chart, then specialize its coefficient identities at regular marks. -/
theorem chart_of_whole (f : Row 3) (hf : Irreducible f)
    (hd : 0 < f.degreeOf 2) (hmax : f.degreeOf 2 ≤ 24)
    (hw : TrueWeightLE f anchorCutoff) (hwhole : Whole f) :
    ∃ P : Ideal CoeffRing, FreshChart P (freshRow f) (freshRow (separant f)) ∧
      LowSupport P ∧ ∀ S : Geom[X], S.natDegree ≤ physicalDegree → RegularAt 2 f S →
        coeffPoint S ∈ MvPolynomial.zeroLocus Geom P := by
  let hp : (chartIdeal f).IsPrime := chart_prime f hf hd
  have hs := separant_regular f hf hd hmax
  have hweight (U : (ChartField f)[X]) (hU : U.natDegree < taylorLength) :
      (trajectory (chartConstants f) U f).natDegree < K1.p :=
    (degree_trajectory _ hU f hw).trans_lt (by decide : anchorCutoff < K1.p)
  obtain ⟨U, hsmall, hsol, hinit⟩ :=
    chart_trajectory f taylorLength (by decide) (by decide) hs hweight hwhole
  have length_le : taylorLength ≤ K1_13.taylorLength := by decide
  have hU := hsmall.trans_le length_le
  obtain ⟨m, v, hv⟩ := K1_13_5_5_1_1.proof f
  let k := chartConstants f
  let point : CoeffIndex → ChartField f := fun a => U.coeff a.val
  let P := RingHom.ker (coeffEval k point)
  have hbase := freshIdeal_eq_ker k point
  have himage := freshJetEval_ker f hf hd U hU hsol hinit
  have hD : onChart f (freshRow (separant f)) ≠ 0 :=
    fun h => hs ((onChart_eq_zero f _).mp h)
  have hUreg : trajectory k U (separant f) ≠ 0 := by
    intro hz
    have h := eval_trajectory k U (chartCenter f) (separant f)
    rw [hz, Polynomial.eval_zero, hinit, rowAt_chart] at h
    exact hD h.symm
  refine ⟨P, ⟨RingHom.ker_isPrime _, ?_, ?_, hs, ?_⟩, ?_, ?_⟩
  · exact fun h => hf.ne_zero (rowMap_injective (h.trans (map_zero _).symm))
  · change (freshIdeal P).comap freshProjection.toRingHom = chartIdeal f
    rw [hbase, RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨freshRow (v a), m, ?_⟩
    have hU' : (U.map (newConstants : ChartField f →+* NewField (ChartField f))).natDegree <
        K1_13.taylorLength := Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : trajectory (newConstants.comp k) (U.map newConstants) f = 0 := by
      rw [← map_trajectory, hsol, Polynomial.map_zero]
    have hs' : rowAt (newConstants.comp k) newCenter
        (jetAt newCenter (U.map newConstants)) (separant f) ≠ 0 := by
      rw [newTrajectory_eval]
      exact fun h => hUreg ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have h := hv (NewField (ChartField f)) (newConstants.comp k) (U.map newConstants) newCenter
      hU' hsol' hs' a
    rw [newTrajectory_eval, newTrajectory_eval, Polynomial.coeff_map,
      ← freshJetEval_row k U hU, ← freshJetEval_row k U hU] at h
    exact fresh_recovered_mem k U a m _ _ h
  · intro a ha
    change coeffEval k point (MvPolynomial.X a) = 0
    rw [coeffEval, MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e : FreshJetRing →+* ChartField f := onChart f
    let g : FreshJetRing →+* FreshField :=
      MvPolynomial.eval (jetAt freshCenter (S.map freshConstants))
    let b : Geom →+* FreshJetRing := MvPolynomial.C.comp freshConstants
    have hg (q : Row 3) : g (freshRow q) = algebraMap Geom[X] FreshField (atJet q S) := by
      rw [← actual_eval, actual_eval_fresh]
      rfl
    have hreg' : g (freshRow (separant f)) ≠ 0 := by
      rw [hg]
      exact fun h => hreg.2 ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
    have hker : RingHom.ker e ≤ RingHom.ker g := by
      rw [show RingHom.ker e = chartIdeal f by
        ext q
        exact onChart_eq_zero f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker, hg, hreg.1, map_zero]
    have hS' : (S.map freshConstants).natDegree < K1_13.taylorLength :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS : trajectory freshConstants (S.map freshConstants) f = 0 := by
      simpa only [trajectory_actual, hreg.1, Polynomial.map_zero, RingHom.comp_id] using
        (map_trajectory (RingHom.id Geom) freshConstants S f).symm
    have hrecU (a : CoeffIndex) :
        e (freshRow (separant f)) ^ m * point a = e (freshRow (v a)) := by
      have hc := hv (ChartField f) k U (chartCenter f) hU hsol
        (by rwa [hinit, rowAt_chart]) a
      rwa [hinit, rowAt_chart] at hc
    have hrecS (a : CoeffIndex) :
        g (freshRow (separant f)) ^ m * freshConstants (S.coeff a.val) = g (freshRow (v a)) := by
      have hc := hv FreshField freshConstants (S.map freshConstants) freshCenter hS' hsolS
        (by rwa [actual_eval_fresh]) a
      rwa [actual_eval_fresh, Polynomial.coeff_map] at hc
    have hle := eval_kernel_le_of_cleared b e g hker (freshRow (separant f)) m
      (fun a => freshRow (v a)) hD hreg' point (freshConstants ∘ coeffPoint S) hrecU hrecS
    intro q hq
    have hz := hle hq
    change MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) q = 0 at hz
    have hqmap : MvPolynomial.eval₂Hom (g.comp b) (freshConstants ∘ coeffPoint S) =
        freshConstants.comp (MvPolynomial.aeval (coeffPoint S)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b, g]
      · intro a
        simp
    rw [hqmap] at hz
    exact freshConstants.injective (hz.trans (map_zero _).symm)

end

end P0_9_5_2
end PackSource_P0_9_5_2Chart

section PackSource_P0_9_5_2Degree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace P0_9_5_2

noncomputable section

open K1_13 (Geom)
open K1_13_5_5 K1_13_5_5_2 K1_13_5_5_2_1
open P0_9 (physicalDegree)
open MvPolynomial
open scoped BigOperators Polynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open private monic_chart_aux from ProximityPrize.SubmissionLower.Fast064
open private commonFactor_monic trimmedValue_monic trimmedValue_dvd from ProximityPrize.SubmissionLower.Fast064

/-- A nonconstant factor's multiplicity is bounded by the actual direction degree. -/
private theorem square_dvd_trimmed_pow {A : Type} [CommRing A] [IsDomain A]
    {f : A[X]} (s : Factorization f) {d : ℕ} (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    f ^ 2 ∣ (trimmedValue s) ^ d := by
  classical
  have hdegree : (∑ i, s.multiplicity i * (s.factor i).natDegree) = f.natDegree := by
    conv_rhs => rw [s.product_eq]
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun i _ => (s.monic i).pow _)]
    simp only [Polynomial.natDegree_pow]
  refine (dvd_of_eq (congrArg (fun g : A[X] => g ^ 2) s.product_eq)).trans ?_
  rw [trimmedValue, ← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  by_cases hconstant : (s.factor i).natDegree = 0
  · simp [Polynomial.eq_one_of_monic_natDegree_zero (s.monic i) hconstant]
  have hmi : s.multiplicity i ≤ d := calc
    _ = s.multiplicity i * 1 := (mul_one _).symm
    _ ≤ s.multiplicity i * (s.factor i).natDegree :=
      Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hconstant)
    _ ≤ ∑ j, s.multiplicity j * (s.factor j).natDegree :=
      Finset.single_le_sum (f := fun j => s.multiplicity j * (s.factor j).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = f.natDegree := hdegree
    _ ≤ d := hf
  rw [← pow_mul, ← pow_mul]
  apply pow_dvd_pow
  by_cases h : s.multiplicity i ≤ 2
  · rw [min_eq_left h]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (s.multiplicity i) hd
  · rw [min_eq_right (by omega)]
    exact (Nat.mul_le_mul_right 2 hmi).trans_eq (Nat.mul_comm d 2)

private theorem eval_divisions {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    (e : A[X] →+* B) {f : A[X]} (s : Factorization f) {d : ℕ}
    (hf : f.natDegree ≤ d) (hd : 2 ≤ d) :
    e (trimmedValue s) ∣ e f ∧ e f ^ 2 ∣ e (trimmedValue s) ^ d :=
  ⟨map_dvd e (trimmedValue_dvd s),
    by simpa only [map_pow] using map_dvd e (square_dvd_trimmed_pow s hf hd)⟩

/-- The infinity component uses the retuned height when its high coordinates vanish. -/
private theorem supported_height (Q : Ideal CoeffRing) (L : Fin 2 → FreshJetRing)
    (hQ : Q.IsPrime) (hhom : Q.IsHomogeneous (homogeneousSubmodule CoeffIndex Geom))
    (hdim : (affineHilbertPolynomial Q).natDegree = 2)
    (hL : FiniteJetPair L (jetImage (freshIdeal Q))) (hlow : LowSupport Q) :
    2 * affineDegree Q ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal Q) : ℚ) := by
  have h1 := K1_13_5_5_2_1_1.of_children K1_13_5_5_2_1_1_1.proof
    K1_13_5_5_2_1_1_2.proof K1_13_5_5_2_1_1_3.proof
  have h2 := K1_13_5_5_2_1_2.proof
  have h3 := K1_13_5_5_2_1_3.proof
  have h4 := K1_13_5_5_2_1_4.of_children K1_13_5_5_2_1_4_1.proof K1_13_5_5_2_1_4_2.proof
  have h5 := K1_13_5_5_2_1_5.proof
  have h6 := K1_13_5_5_2_1_6.proof
  obtain ⟨i, hi, hchart, hmonic, hdegree⟩ := monic_chart_aux Q hQ hhom (by omega)
  have hid : i.val ≤ physicalDegree :=
    Nat.le_of_lt_succ (lt_of_not_ge (fun h => hi (hlow i h)))
  let : IsDomain (ChartRing Q i) := hchart
  obtain ⟨a, ha, ⟨s⟩⟩ := h2 (ChartRing Q i) (direction Q i) hmonic ((hdegree.trans hid).trans (by decide))
  obtain ⟨hdom, heval, hfinite, hcoeff⟩ := h1 Q i a hQ hhom hdim hi hchart ha
  let : IsDomain (FreshOpen Q i a) := hdom
  let : IsDomain (OpenRing Q i a) := IsLocalization.Away.isDomain _ ha
  change Factorization (openDirection Q i a) at s
  obtain ⟨q, hq0, hq, hqspan⟩ := h3 (OpenRing Q i a) (openDirection Q i a) s
  let e : (OpenRing Q i a)[X] →+* FreshOpen Q i a := freshEval (OpenRing Q i a)
  let x := e (openDirection Q i a)
  let b := e (commonFactor s)
  let d : Fin 3 → FreshOpen Q i a := fun j => e (q j)
  have hx : x ≠ 0 := by
    simpa only [e, x, openDirection, map_zero] using
      heval.ne (hmonic.map (algebraMap _ (OpenRing Q i a))).ne_zero
  have hb : b ≠ 0 := by
    simpa only [e, b, map_zero] using heval.ne (commonFactor_monic s).ne_zero
  have hd : d 0 ≠ 0 := by
    simpa only [d, hq0, e, map_zero] using heval.ne (trimmedValue_monic s).ne_zero
  have htrim : ∀ j, b * d j = e (Polynomial.hasseDeriv j.val (openDirection Q i a)) := by
    intro j
    exact (e.map_mul _ _).symm.trans (congrArg e (hq j))
  have hspan : Ideal.span (Set.range d) = ⊤ := by
    have hm := congrArg (Ideal.map e) hqspan
    rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at hm
  let : Module.Finite FreshField (PrincipalQuot x) := hfinite
  have hdegree' : (openDirection Q i a).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hdegree.trans hid)
  have hdiv := eval_divisions e s hdegree' (by decide)
  have hdeq : d 0 = e (trimmedValue s) := congrArg e hq0
  rw [← hdeq] at hdiv
  obtain ⟨hdfin, hlen⟩ := length_bound x (d 0) physicalDegree hx hd hdiv.1 hdiv.2
  rw [← hcoeff]
  have hlenQ : 2 * (Module.finrank FreshField (PrincipalQuot x) : ℚ) ≤
      (physicalDegree : ℚ) * (Module.finrank FreshField (PrincipalQuot (d 0)) : ℚ) := by
    exact_mod_cast hlen
  by_cases hu : IsUnit (d 0)
  · have hzero : Module.finrank FreshField (PrincipalQuot (d 0)) = 0 := by
      have : Subsingleton (PrincipalQuot (d 0)) :=
        Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
      exact Module.finrank_zero_of_subsingleton
    exact hlenQ.trans (by rw [hzero, Nat.cast_zero, mul_zero]; positivity)
  · obtain ⟨hk, hcomparison⟩ := h4 Q i a hQ hhom hdim hi hchart ha hdom b d hb htrim
    obtain ⟨hpairfin, hrank⟩ := hcomparison L hL
    have hL' : FiniteJetPair L (coneJetIdeal d) := hk ▸ hL
    obtain ⟨M, w, hM, hMw, hinj, hw⟩ := h5 _ d L hd hu hspan hL'
    obtain ⟨hwfin, hwRank⟩ := h6 _ d L M hL' hpairfin hM hinj
    rw [hMw] at hwfin hwRank hinj
    let : Module.Finite PairField (pairFiber (valuePairMap (d 0) w)) := hwfin
    let : Module.Finite FreshField (PrincipalQuot (d 0)) := hdfin
    have hbound := pin_bound (d 0) w hw hinj
    rw [hwRank, hrank] at hbound
    exact hlenQ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbound)
      (Nat.cast_nonneg physicalDegree))

/-- A chart supported in the retuned space has the same infinity-cycle comparison
with the sharper degree bound on every homogeneous component. -/
theorem chart_degree (P : Ideal CoeffRing) (g d : FreshJetRing)
    (hchart : FreshChart P g d) (hlow : LowSupport P) :
    (affineHilbertPolynomial P).natDegree = 2 ∧
      2 * affineDegree P ≤ (physicalDegree : ℚ) * (g.totalDegree : ℚ) := by
  have hdim := K1_13_5_5_2.chart_dimension P g d hchart
  refine ⟨hdim, ?_⟩
  have h2 := K1_13_5_5_2_2.of_children K1_13_5_5_2_2_1.proof K1_13_5_5_2_2_2.proof
  have h3 := K1_13_5_5_2_3.of_children K1_13_5_5_2_3_1.proof
    K1_13_5_5_2_3_2.proof K1_13_5_5_2_3_3.proof
  obtain ⟨n, Q, hQ, hdeg, hfiber⟩ := h2 P hchart.prime hdim
  obtain ⟨L, hL, hfinite, hbudget⟩ := h3 P g d hchart
  have htail : LowSupport (infinityIdeal P) := by
    intro i hi
    change MvPolynomial.X i ∈ Ideal.span _
    apply Ideal.subset_span
    refine ⟨MvPolynomial.X i, hlow i hi, ?_⟩
    change homogeneousComponent (MvPolynomial.X (R := Geom) i).totalDegree
      (MvPolynomial.X i) = MvPolynomial.X i
    rw [totalDegree_X]
    exact homogeneousComponent_eq_self (isHomogeneous_X Geom i)
  have hcurve (i : Fin n) : 2 * affineDegree (Q i) ≤
      (physicalDegree : ℚ) * (genericFiberDimension L (freshIdeal (Q i)) : ℚ) := by
    obtain ⟨hi, hhom, hd⟩ := hQ i
    have hle : jetImage (freshIdeal (infinityIdeal P)) ≤ jetImage (freshIdeal (Q i)) :=
      Ideal.comap_mono (Ideal.map_mono hi.le)
    exact supported_height (Q i) L hi.isPrime hhom hd (hL.of_le hle)
      (fun j hj => hi.le (htail j hj))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcurve i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hdeg]
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg physicalDegree))
  exact_mod_cast (hfiber L hfinite).trans hbudget

end

end P0_9_5_2
end PackSource_P0_9_5_2Degree

section PackSource_P0_9_5_2Proof
set_option autoImplicit true
set_option maxHeartbeats 1000000

namespace P0_9_5_2

noncomputable section

open P0 (K)
open P0_9_5 (Whole)
open K1_13 (Row Geom extend)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open K1_13_5_5 (freshRow FreshField)
open Finset MvPolynomial
open scoped BigOperators Polynomial

private theorem freshRow_degree_le (f : Row 3) : (freshRow f).totalDegree ≤ f.totalDegree := by
  unfold freshRow MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset (algebraMap Geom[X] FreshField) f)

theorem proof : P0_9_5.c2 := by
  classical
  intro w Γ s hm n f hf hcover
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  let cap (i : Fin n) := 133551 * (f i).totalDegree
  have hsub (i : Fin n) : part i ⊆ Γ := filter_subset _ _
  have hlocal (i : Fin n) : NodeCapacity w (part i) s (cap i) := by
    by_cases hi : Whole (f i)
    · have htop : (f i).degreeOf 2 ≤ 24 :=
        (single_le_sum (f := fun j => (f j).degreeOf 2) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
          hf.top
      obtain ⟨P, hp, hsupport, hall⟩ := chart_of_whole _ (hf.irreducible i) (hf.positive i) htop (hf.weight i) hi
      obtain ⟨hdim, hdeg⟩ := chart_degree _ _ _ hp hsupport
      change 2 * affineDegree P ≤ (133551 : ℚ) * ((freshRow (f i)).totalDegree : ℚ) at hdeg
      apply surface_nodeCapacity (hm.mono (hsub i)) hp.prime hdim
      · intro γ hγ
        have hγΓ := hsub i hγ
        exact hall _ (Polynomial.natDegree_map_le.trans (hm.degree γ hγΓ))
          (mem_filter.mp hγ).2.1
      · have hle : ((freshRow (f i)).totalDegree : ℚ) ≤ ((f i).totalDegree : ℚ) :=
          Nat.cast_le.mpr (freshRow_degree_le (f i))
        simpa only [cap, Nat.cast_mul, Nat.cast_ofNat] using
          hdeg.trans (mul_le_mul_of_nonneg_left hle (by norm_num))
    · have hempty : part i = ∅ := by simp [part, hi]
      rw [hempty]
      exact ⟨∅, by simp, by simp⟩
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi, hwhole⟩ := hcover γ hγ
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hγ, hi, hwhole⟩⟩
  · change n ≤ 120
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := sum_le_sum fun i _ =>
        (hf.positive i).trans_le (degreeOf_le_totalDegree _ _)
      _ ≤ 120 := hf.total
  · change (∑ i, 133551 * (f i).totalDegree) ≤ 133551 * 120
    rw [← mul_sum]
    exact Nat.mul_le_mul_left _ hf.total

end

end P0_9_5_2
end PackSource_P0_9_5_2Proof
