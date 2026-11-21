import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_5
noncomputable section
open K1 K1_13 Polynomial
open scoped BigOperators
def RegularAt {r : ℕ} (top : Fin r) (f : Row r) (S : Geom[X]) : Prop :=
  atJet f S = 0 ∧ atJet (MvPolynomial.pderiv top f) S ≠ 0
structure FirstRow (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ 5064
  index : indexDegree q ≤ 1104
structure FirstFactors {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ 5064
  index : (∑ i, indexDegree (f i)) ≤ 1104
structure SecondFactors {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) (90 * 180265 - 1)
  total : (∑ i, (f i).totalDegree) ≤ 120
  index : (∑ i, indexDegree (f i)) ≤ 48
  top : (∑ i, (f i).degreeOf 2) ≤ 24
def coeffDerivative {r : ℕ} (f : Row r) : Row r :=
  ∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m).derivative
def separant (f : Row 3) : Row 3 := MvPolynomial.pderiv 2 f
def lowerTangent (b : Row 3) : Row 3 :=
  coeffDerivative b + MvPolynomial.X 1 * MvPolynomial.pderiv 0 b +
    2 * MvPolynomial.X 2 * MvPolynomial.pderiv 1 b
def tangentNumerator (f b : Row 3) : Row 3 :=
  separant f * lowerTangent b - lowerTangent f * MvPolynomial.pderiv 2 b
def compatibilityNumerator (f : Row 3) : ℕ → Row 3
  | 0 => -lowerTangent f
  | j + 1 =>
    let b := compatibilityNumerator f j
    separant f * tangentNumerator f b - (2 * j + 1 : ℕ) * b * tangentNumerator f (separant f)
def Whole (f : Row 3) : Prop :=
  f ∣ compatibilityNumerator f (taylorLength - 3)
def NodeCapacity (w : I → K) (Γ : Finset K) (s : K → K[X]) (d : ℕ) : Prop := by
  classical
  exact ∃ persistent : Finset I,
    (∀ i ∈ persistent, ∀ γ ∈ Γ, (s γ).eval (node i) = w i) ∧
    ∀ i, i ∉ persistent → (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d
structure NodeFamily (w : I → K) (Γ : Finset K) (s : K → K[X]) where
  n : ℕ
  part : Fin n → Finset K
  cap : Fin n → ℕ
  sub : ∀ i, part i ⊆ Γ
  localCapacity : ∀ i, NodeCapacity w (part i) s (cap i)
def NodeFamily.labels {w Γ s} (F : NodeFamily w Γ s) : Finset K := by
  classical
  exact Finset.univ.biUnion F.part
def NodeFamily.totalCap {w Γ s} (F : NodeFamily w Γ s) : ℕ := ∑ i, F.cap i
abbrev lowBox : Shape := ⟨120,48,24⟩
def liftedBox (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowBox.j + 2)
  ⟨1 + (L - 4) * lowBox.b, j, min (1 + (L - 4) * (lowBox.t + 2)) (j / 2)⟩
abbrev graphBox : Shape := ⟨120,49,24⟩
def volumeTerm (p q r : Shape) : ℕ := p.t * (q.j - q.t) * (2 * r.b - r.j)
def mixed3 (p q r : Shape) : ℕ :=
  (volumeTerm p q r + volumeTerm p r q + volumeTerm q p r +
    volumeTerm q r p + volumeTerm r p q + volumeTerm r q p) / 2
def mixedBudget : ℕ :=
  let a := liftedBox (taylorLength + 1)
  let b := liftedBox (taylorLength + 2)
  mixed3 lowBox a b + (taylorLength - 1) * mixed3 lowBox graphBox b +
    taylorLength * mixed3 lowBox graphBox a
def invariantBudget : ℕ :=
  lowBox.b * (1 + (2 * (taylorLength + 1) - 7) * (lowBox.b - 1))
def firstMixedBudget : ℕ :=
  let h := 5064
  let i := 1104
  let a := 1 + (2 * taylorLength - 5) * (h - 1)
  let d := min a ((2 * taylorLength - 5) * (i - 1) + taylorLength - 1)
  h * d + i * a - i * d
structure ProperCover (w : I → K) (Γ : Finset K) (s : K → K[X]) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget
  fresh : invariant.totalCap ≤ invariantBudget
  components : multiple.n + invariant.n ≤ 2 * invariantBudget
end
end K1_13_5
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace K1_13_5
noncomputable section
open K1 K1_13 Polynomial ProximityPrize.Benchmark
open scoped BigOperators
theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 133671 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 133671 :=
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
    (hc : NodeCapacity w Γ s d) : 46594 * Γ.card ≤ 81879 * d + 46594 := by
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
  let a : ℕ := 180265 - persistent.card
  let b : ℕ := 133671 - persistent.card
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
  have hb : (b : ℤ) = x - 46594 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 133671 ≤ 180265))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 81879 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 133671 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 133671 ≤ 180265))]
    ring
  have hinc' : l * x ≤ (x + 81879) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 81879 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 81879 * (d : ℤ) < (l - 1) * 46594 := by
    have hc : 81879 * (d : ℤ) + 46594 < 46594 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 35285 * (d : ℤ) < (l - (d : ℤ)) * 46594 := by linarith only [hbad]
  have hden : 0 < 81879 * 46594 - 35285 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 35285)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 81879)
    have hpos : 0 < (l - (d : ℤ)) * (81879 * 46594 - 35285 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 133671 ≤ 180265) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hba hdenNat hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 81879 * 46594 ≤ (35285 * l + 46594) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 35285 * l + 46594 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 81879 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]
theorem NodeFamily.count {w Γ s} (C : NodeFamily w Γ s) (h : Messages w Γ s) :
    46594 * C.labels.card ≤ 81879 * C.totalCap + 46594 * C.n := by
  classical
  calc
    46594 * C.labels.card ≤ 46594 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46594 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (81879 * C.cap i + 46594) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 81879 * C.totalCap + 46594 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
end
end K1_13_5
end
section
namespace K1_13_5
noncomputable section
open K1 K1_13 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ g : Row 3, LowerRow g →
    ∃ (n : ℕ) (f : Fin n → Row 3) (q : Row 2), SecondFactors f ∧ FirstRow q ∧
      ∀ S : Geom[X], atJet g S = 0 →
        atJet q S = 0 ∨ ∃ i, RegularAt 2 (f i) S
def c2 : Prop :=
  ∀ q : Row 2, FirstRow q →
    ∃ (n : ℕ) (f : Fin n → Row 2) (u : Geom[X][X]), FirstFactors f ∧ u ≠ 0 ∧
      u.natDegree ≤ 5064 * (5064 - 1) ∧
      ∀ S : Geom[X], atJet q S = 0 →
        u.eval S = 0 ∨ ∃ i, RegularAt 1 (f i) S
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 2), FirstFactors f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 1 (f i) (extend (s γ))) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ 5064 ∧
      C.totalCap ≤ firstMixedBudget
def c4 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) →
    Nonempty (ProperCover w Γ s)
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ 120 ∧ C.totalCap ≤ 133671 * 120
theorem roots_card_le {w Γ s} (h : Messages w Γ s) (u : Geom[X][X]) (hu : u ≠ 0)
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
theorem first_count (h2 : c2) (h3 : c3) {w Γ s} (h : Messages w Γ s)
    (q : Row 2) (hq : FirstRow q) (hr : ∀ γ ∈ Γ, atJet q (extend (s γ)) = 0) :
    46594 * Γ.card ≤ 81879 * firstMixedBudget + 46594 * (5064 * 5064) := by
  classical
  obtain ⟨n, f, u, hf, hu, hd, hc⟩ := h2 q hq
  let ordinary := Γ.filter fun γ => u.eval (extend (s γ)) = 0
  let regular := Γ.filter fun γ => ∃ i, RegularAt 1 (f i) (extend (s γ))
  have hr₀ : ordinary.card ≤ 5064 * (5064 - 1) :=
    (roots_card_le (h.mono (Finset.filter_subset _ _)) u hu
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C, hC, hn, hcap⟩ := h3 w regular s (h.mono (Finset.filter_subset _ _)) n f hf
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₁ := C.count (h.mono (Finset.filter_subset _ _))
  have hr₁' : 46594 * regular.card ≤ 81879 * C.totalCap + 46594 * C.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hC)).trans hr₁
  have covers : Γ ⊆ ordinary ∪ regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hreg⟩)
  have htotal := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  omega
theorem ProperCover.count {w Γ s} (C : ProperCover w Γ s) (h : Messages w Γ s) :
    46594 * Γ.card ≤ 46594 * mixedBudget + (81879 + 2 * 46594) * invariantBudget := by
  classical
  have hm := C.multiple.count h
  have hi := C.invariant.count h
  have hc := (Finset.card_le_card C.cover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hmix := C.mixed
  have hf := C.fresh
  have hn := C.components
  omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) : K1_13.c5 := by
  classical
  intro w Γ s h g hg hr
  obtain ⟨n, f, q, hf, hq, hc⟩ := h1 g hg
  let first := Γ.filter fun γ => atJet q (extend (s γ)) = 0
  let proper := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)
  let whole := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  have hfirst := first_count h2 h3 (h.mono (Δ := first) (Finset.filter_subset _ _)) q hq
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hpmsg := h.mono (Δ := proper) (Finset.filter_subset _ _)
  obtain ⟨P⟩ := h4 w proper s hpmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hproper := P.count hpmsg
  have hwmsg := h.mono (Δ := whole) (Finset.filter_subset _ _)
  obtain ⟨W, hW, hn, hcap⟩ := h5 w whole s hwmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwhole : 46594 * whole.card ≤ 81879 * W.totalCap + 46594 * W.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hW)).trans (W.count hwmsg)
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
  have hnumeric : 81879 * firstMixedBudget + 46594 * (5064 * 5064) +
      (46594 * mixedBudget + (81879 + 2 * 46594) * invariantBudget) +
      (81879 * (133671 * 120) + 46594 * 120) ≤ 46594 * 18512789806000648 := by decide
  omega
end
end K1_13_5
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
abbrev RationalX := FractionRing Geom[X]
abbrev GeometricX := AlgebraicClosure RationalX
abbrev GeoRow (n : ℕ) := MvPolynomial (Fin n) GeometricX
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def genericCoeff : Geom[X] →+* GeometricX :=
  (algebraMap RationalX GeometricX).comp (algebraMap Geom[X] RationalX)
def genericRow {n : ℕ} (P : Row n) : GeoRow n := MvPolynomial.map genericCoeff P
def jetPoint {n : ℕ} (S : Geom[X]) : Fin n → GeometricX :=
  fun j => genericCoeff (jet S j)
def coefficientPoint (S : Geom[X]) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : GeometricX[X] :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
def regularLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ MvPolynomial.zeroLocus GeometricX P ∧
    MvPolynomial.eval y (genericRow (separant f)) ≠ 0}
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
def liftRow (P : GeoRow 3) : GeoRow 4 := MvPolynomial.rename Fin.castSucc P
def graph (f : Row 3) : GeoRow 4 :=
  liftRow (genericRow (lowerTangent f)) + 3 * MvPolynomial.X 3 * liftRow (genericRow (separant f))
def graphIdeal (f : Row 3) : Ideal (GeoRow 4) :=
  Ideal.span {liftRow (genericRow f), graph f}
def graphPoint (f : Row 3) (y : Fin 3 → GeometricX) : Fin 4 → GeometricX :=
  Fin.snoc y (-MvPolynomial.eval y (genericRow (lowerTangent f)) /
    (3 * MvPolynomial.eval y (genericRow (separant f))))
def InLiftedBox (P : GeoRow 4) (box : Shape) (height : ℕ) : Prop :=
  ∀ a ∈ P.support, a 0 + a 1 + a 2 ≤ box.b ∧
    a 1 + 2 * a 2 ≤ box.j ∧ a 2 ≤ box.t ∧ a 3 ≤ height
def RepresentsOnGraph (f old : Row 3) (P : GeoRow 4) : Prop :=
  ∃ (a b : ℕ) (c : GeometricX), c ≠ 0 ∧
    let sep := liftRow (genericRow (separant f))
    sep ^ a * (sep ^ b * P - MvPolynomial.C c * liftRow (genericRow old)) ∈ graphIdeal f
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
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
  ordinary_bound : (oldCut f).totalDegree ≤
    1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1)
  actual : ∀ S : Geom[X], S.natDegree ≤ 133671 → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
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
def extendedAtJet (P : Row 3) (S : GeometricX[X]) : GeometricX[X] :=
  MvPolynomial.eval (fun j => hasseDeriv j.val S)
    (MvPolynomial.map (Polynomial.mapRingHom (algebraMap Geom GeometricX)) P)
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end K1_13_5_4
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap RationalX GeometricX).injective.comp (IsFractionRing.injective Geom[X] RationalX)
theorem eval_genericRow_at_point {n : ℕ} (P : Row n) (S : Geom[X]) :
    MvPolynomial.eval (jetPoint S) (genericRow P) = genericCoeff (atJet P S) := by
  unfold genericRow atJet jetPoint
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp _ _ _).symm
theorem jetPoint_injOn (s : K → K[X]) (Γ : Finset K)
    (hs : Set.InjOn s (Γ : Set K)) :
    Set.InjOn (fun γ => jetPoint (n := 3) (extend (s γ))) (Γ : Set K) := by
  intro γ hγ δ hδ heq
  apply hs hγ hδ
  apply Polynomial.map_injective embed embed.injective
  have h := genericCoeff_injective (congrFun heq (0 : Fin 3))
  simpa [jet, jetPoint] using h
private theorem recover_coefficients (S : Geom[X]) (hS : S.natDegree ≤ 133671) :
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
  have hdeg : ∀ η ∈ Γ, (extend (s η)).natDegree ≤ 133671 := by
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
  have hdeg : (extend (s γ)).natDegree ≤ 133671 := by
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
end K1_13_5_4
end
section
namespace K1_13_5_4
noncomputable section
open K1 K1_13 K1_13_5 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ i, Nonempty (LiftedChart (f i))
def c2 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ T : ∀ i, LiftedChart (f i),
    Nonempty (MixedSections f T)
def c3 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f → ∀ a ∈ properComponents f,
    SimpleInvariant (f a.1) a.2 →
    ∃ Q : CoefficientIdeal, ActualSolutionCurve (f a.1) Q ∧
      ∀ S : Geom[X], S.natDegree ≤ 133671 → jetPoint S ∈ regularLocus (f a.1) a.2 →
        coefficientPoint S ∈ MvPolynomial.zeroLocus GeometricX Q
def c4 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∀ i, (oldCut (f i)).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * ((f i).totalDegree - 1)) →
    ∀ C : Finset CoefficientIdeal,
      (∀ Q ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q) →
      ∃ d : CoefficientIdeal → ℕ,
        (∀ Q ∈ C, 0 < d Q ∧ MvPolynomial.affineDegree Q ≤ (d Q : ℚ)) ∧
          (∑ Q ∈ C, d Q) ≤ invariantBudget
private theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
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
private theorem exists_properComponent {n : ℕ} {f : Fin n → Row 3}
    (T : ∀ i, LiftedChart (f i)) {i : Fin n} {S : Geom[X]}
    (hS : S.natDegree ≤ 133671) (hr : RegularAt 2 (f i) S) (hw : ¬ Whole (f i)) :
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
  have hdeg (γ : K) (hγ : γ ∈ Γ) : (extend (s γ)).natDegree ≤ 133671 := by
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
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_13_5.c4 := by
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
  obtain ⟨d, hd, hsum⟩ := h4 n f hf (fun i => (T i).ordinary_bound) C hfresh
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
    have hdeg : (extend (s γ)).natDegree ≤ 133671 := by
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
end K1_13_5_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators Pointwise
abbrev JetPoint := Fin 4 → GeometricX
def factorCurves (f : Row 3) : Finset (Ideal (GeoRow 3)) := by
  classical
  exact if Whole f then ∅ else
    (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f))
def graphLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set JetPoint :=
  graphPoint f '' regularLocus f P
def graphCurve (f : Row 3) (P : Ideal (GeoRow 3)) : Ideal (GeoRow 4) :=
  vanishingIdeal GeometricX (graphLocus f P)
def boxExponents (s : Shape) (h : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {a | a 0 + a 1 + a 2 ≤ s.b ∧ a 1 + 2 * a 2 ≤ s.j ∧ a 2 ≤ s.t ∧ a 3 ≤ h}
instance boxExponentsFinite (s : Shape) (h : ℕ) : Finite (boxExponents s h) :=
  ((Finsupp.finite_of_degree_le (s.b + h)).subset (by
    intro a ha
    change a.degree ≤ s.b + h
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
    exact (Nat.add_le_add ha.1 ha.2.2.2))).to_subtype
abbrev lastBox := liftedBox (taylorLength + 2)
abbrev lastExponents := boxExponents lastBox taylorLength
abbrev lastMap := monomialMap GeometricX lastExponents
def sectionIdeal (f : Row 3) (P : Ideal (GeoRow 3)) :
    Ideal (MvPolynomial lastExponents GeometricX) :=
  (graphCurve f P).comap lastMap
def IsSectionCurve (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  (sectionIdeal f P).IsPrime ∧ (affineHilbertPolynomial (sectionIdeal f P)).natDegree = 1
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
def fourCutIdeal (F G E L : GeoRow 4) : Ideal (GeoRow 4) :=
  Ideal.span {F, G, E, L}
abbrev pointIdeal (y : JetPoint) : Ideal (GeoRow 4) :=
  vanishingIdeal GeometricX {y}
def pointLength (J : Ideal (GeoRow 4)) (y : JetPoint) : ℕ∞ :=
  let A := Localization.AtPrime (pointIdeal y)
  Module.length A (A ⧸ J.map (algebraMap (GeoRow 4) A))
abbrev ExponentSpace := Fin 4 → ℝ
def capBody (s : Shape) (h : ℕ) : Set ExponentSpace :=
  {x | (∀ j, 0 ≤ x j) ∧ x 0 + x 1 + x 2 ≤ s.b ∧
    x 1 + 2 * x 2 ≤ s.j ∧ x 2 ≤ s.t ∧ x 3 ≤ h}
def downBody (F : GeoRow 4) : Set ExponentSpace :=
  convexHull ℝ {x | ∃ a ∈ F.support, ∀ j, 0 ≤ x j ∧ x j ≤ a j}
def mixedVolume4 (B : Fin 4 → Set ExponentSpace) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
    (-1 : ℝ) ^ (4 - S.card) * (MeasureTheory.volume (∑ i ∈ S, B i)).toReal
def lastMixedVolume (first : Set ExponentSpace) : ℝ :=
  mixedVolume4 ![first, capBody graphBox 1,
    capBody (liftedBox (taylorLength + 1)) (taylorLength - 1),
    capBody lastBox taylorLength]
end
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators
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
theorem localLength_lt_top {R : Type} [CommRing R] [IsNoetherianRing R]
    {P J : Ideal R} [P.IsPrime] (hP : P ∈ J.minimalPrimes) :
    let A := Localization.AtPrime P
    Module.length A (A ⧸ J.map (algebraMap R A)) < ⊤ := by
  let A := Localization.AtPrime P
  let L := J.map (algebraMap R A)
  change Module.length A (A ⧸ L) < ⊤
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    rw [show L = J.map (algebraMap R A) from rfl,
      IsLocalization.minimalPrimes_map P.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hP
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := L))⟩))
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
  exact ⟨Module.length_pos, localLength_lt_top hm⟩
theorem componentLength_toNat {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) :
    ((componentLength f P).toNat : ℕ∞) = componentLength f P :=
  ENat.natCast_toNat (componentLength_of_retained hP).2.ne
theorem componentLength_toNat_pos {f : Row 3} {P : Ideal (GeoRow 3)}
    (hP : P ∈ factorCurves f) : 0 < (componentLength f P).toNat := by
  have h := (componentLength_of_retained hP).1
  rw [← componentLength_toNat hP] at h
  exact_mod_cast h
theorem lastExponents_single (i : Fin 4) : Finsupp.single i 1 ∈ lastExponents := by
  change (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 + (Finsupp.single i 1) 2 ≤
    lastBox.b ∧ (Finsupp.single i 1) 1 + 2 * (Finsupp.single i 1) 2 ≤ lastBox.j ∧
    (Finsupp.single i 1) 2 ≤ lastBox.t ∧ (Finsupp.single i 1) 3 ≤ taylorLength
  fin_cases i <;> norm_num [Finsupp.single_apply, liftedBox, taylorLength]
private theorem graphPoint_injective (f : Row 3) : Function.Injective (graphPoint f) := by
  intro y z h
  funext i
  simpa only [graphPoint, Fin.snoc_castSucc] using congrFun h i.castSucc
@[simp] theorem eval_liftRow_graphPoint (f : Row 3) (x : Fin 3 → GeometricX) (P : GeoRow 3) :
    eval (graphPoint f x) (liftRow P) = eval x P := by
  rw [liftRow, eval_rename]
  have h : graphPoint f x ∘ Fin.castSucc = x := Fin.snoc_comp_castSucc
  rw [h]
private theorem three_ne_zero : (3 : GeometricX) ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  let : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  let : CharP GeometricX K1.p :=
    charP_of_injective_ringHom genericCoeff_injective K1.p
  exact fun h => (by decide : ¬ K1.p ∣ 3)
    ((CharP.cast_eq_zero_iff GeometricX K1.p 3).mp h)
theorem eval_graph_graphPoint {f : Row 3} {x : Fin 3 → GeometricX}
    (hx : eval x (genericRow (separant f)) ≠ 0) :
    eval (graphPoint f x) (graph f) = 0 := by
  have hs : (3 : GeometricX) * eval x (genericRow (separant f)) ≠ 0 :=
    mul_ne_zero three_ne_zero hx
  have hz : graphPoint f x 3 = -eval x (genericRow (lowerTangent f)) /
      (3 * eval x (genericRow (separant f))) := by
    exact Fin.snoc_last _ _
  rw [graph, map_add, map_mul, map_mul, map_ofNat, eval_X,
    eval_liftRow_graphPoint, eval_liftRow_graphPoint, hz]
  let u := eval x (genericRow (lowerTangent f))
  let s := eval x (genericRow (separant f))
  change u + 3 * (-u / (3 * s)) * s = 0
  calc
    _ = u + (-u / (3 * s)) * (3 * s) := by ring
    _ = 0 := by rw [div_mul_cancel₀ _ hs, add_neg_cancel]
theorem eval_represents_iff {f old : Row 3} {B : GeoRow 4}
    (hB : RepresentsOnGraph f old B) {x : Fin 3 → GeometricX}
    (hf : eval x (genericRow f) = 0) (hx : eval x (genericRow (separant f)) ≠ 0) :
    eval (graphPoint f x) B = 0 ↔ eval x (genericRow old) = 0 := by
  have ht : graphIdeal f ≤ RingHom.ker (eval (graphPoint f x)) := by
    apply Ideal.span_le.mpr
    intro q hq
    change q ∈ RingHom.ker (eval (graphPoint f x))
    rw [RingHom.mem_ker]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · simpa only [eval_liftRow_graphPoint] using hf
    · exact eval_graph_graphPoint hx
  obtain ⟨a, b, c, hc, hm⟩ := hB
  have he := RingHom.mem_ker.mp (ht hm)
  simp only [map_mul, map_pow, map_sub, eval_C, eval_liftRow_graphPoint] at he
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero a hx))
  constructor
  · intro h
    rw [h, mul_zero] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left hc
  · intro h
    rw [h, mul_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero b hx)
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
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped Pointwise
abbrev Exponent := Fin 4 →₀ ℕ
def Downward (A : Finset Exponent) : Prop :=
  ∀ ⦃a b : Exponent⦄, a ∈ A → b ≤ a → b ∈ A
def exponentVector : Exponent →+ ExponentSpace where
  toFun a i := (a i : ℝ)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp [Finsupp.add_apply]
def latticeBody (A : Set Exponent) : Set ExponentSpace :=
  convexHull ℝ (exponentVector '' A)
def downSupport (F : GeoRow 4) : Finset Exponent :=
  F.support.biUnion fun a => Finset.Icc 0 a
def capSupport (s : Shape) (h : ℕ) : Finset Exponent :=
  (Set.toFinite (boxExponents s h)).toFinset
def cutSupports (F : GeoRow 4) : Fin 4 → Finset Exponent :=
  ![downSupport F, capSupport graphBox 1,
    capSupport (liftedBox (taylorLength + 1)) (taylorLength - 1),
    capSupport lastBox taylorLength]
def cutIdeal (f : Fin 4 → GeoRow 4) : Ideal (GeoRow 4) :=
  Ideal.span (Set.range f)
abbrev CoefficientRing (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Σ i : Fin 4, ↥(A i)) GeometricX
abbrev CoefficientField (A : Fin 4 → Finset Exponent) :=
  FractionRing (CoefficientRing A)
def genericEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    MvPolynomial (Fin 4) (CoefficientField A) :=
  ∑ a : ↥(A i), monomial a.1
    (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))
abbrev GenericQuotient (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Fin 4) (CoefficientField A) ⧸ Ideal.span (Set.range (genericEquation A))
def exponentCount (A : Fin 4 → Finset Exponent) (d : Fin 4 → ℕ) : ℕ :=
  (∑ i : Fin 4, d i • (↑(A i) : Set Exponent)).ncard
def corner (q n : ℕ) (S : Finset (Fin 4)) : Fin 4 → ℕ :=
  fun i => q + if i ∈ S then n else 0
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5_4 K1_13_5_4_2 MvPolynomial
theorem mem_downSupport {F : GeoRow 4} {a : Exponent} :
    a ∈ downSupport F ↔ ∃ b ∈ F.support, a ≤ b := by
  classical
  simp [downSupport, Finset.mem_Icc, show (0 : Exponent) ≤ a from fun _ => Nat.zero_le _]
theorem mem_capSupport {s : Shape} {h : ℕ} {a : Exponent} :
    a ∈ capSupport s h ↔ a ∈ boxExponents s h :=
  Set.Finite.mem_toFinset _
theorem latticeBody_downSupport (F : GeoRow 4) :
    latticeBody (downSupport F) = downBody F := by
  unfold latticeBody downBody
  apply Set.Subset.antisymm
  · apply convexHull_mono
    rintro x ⟨e, he, rfl⟩
    obtain ⟨a, ha, hea⟩ := mem_downSupport.mp he
    exact ⟨a, ha, fun i => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hea i)⟩⟩
  · refine convexHull_min ?_ (convex_convexHull _ _)
    rintro x ⟨a, ha, hx⟩
    let corners : Set ExponentSpace :=
      Set.univ.pi fun i => ({0, (a i : ℝ)} : Set ℝ)
    have hxc : x ∈ convexHull ℝ corners := by
      apply mem_convexHull_pi
      intro i _
      rw [convexHull_pair, segment_eq_Icc (Nat.cast_nonneg (a i))]
      exact hx i
    apply convexHull_mono (t := exponentVector '' (↑(downSupport F) : Set Exponent)) ?_ hxc
    intro y hy
    change ∀ i ∈ (Set.univ : Set (Fin 4)), y i ∈ ({0, (a i : ℝ)} : Set ℝ) at hy
    have hv (i : Fin 4) : ∃ b : ℕ, (b : ℝ) = y i ∧ b ≤ a i := by
      have hi := hy i (Set.mem_univ i)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with hi | hi
      · exact ⟨0, by simpa using hi.symm, Nat.zero_le _⟩
      · exact ⟨a i, hi.symm, le_rfl⟩
    choose v hv using hv
    let e : Exponent := Finsupp.equivFunOnFinite.symm v
    have hev : ∀ i, e i = v i := fun i =>
      congrFun (Finsupp.equivFunOnFinite.apply_symm_apply v) i
    refine ⟨e, mem_downSupport.mpr ⟨a, ha, fun i => (hev i).trans_le (hv i).2⟩, ?_⟩
    funext i
    change (e i : ℝ) = y i
    rw [hev i, (hv i).1]
private def capParameter (s : Shape) (h : ℕ) (u : Fin 4 → ℝ) : ExponentSpace :=
  let z := u 2 * s.t
  let y := u 1 * ((s.j : ℝ) - 2 * z)
  ![u 0 * ((s.b : ℝ) - y - z), y, z, u 3 * h]
private theorem capParameter_update (s : Shape) (h : ℕ) (u : Fin 4 → ℝ) (i : Fin 4) :
    capParameter s h u = (1 - u i) • capParameter s h (Function.update u i 0) +
      u i • capParameter s h (Function.update u i 1) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [capParameter, Pi.add_apply, smul_eq_mul, Function.update] <;> ring
private theorem cap_corner_mem (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) (u : Fin 4 → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) :
    capParameter s h u ∈ latticeBody (capSupport s h) := by
  have hbinary (i : Fin 4) : ∃ v : ℕ, (v : ℝ) = u i ∧ v ≤ 1 := by
    rcases hu i with hi | hi
    · exact ⟨0, by simpa using hi.symm, Nat.zero_le 1⟩
    · exact ⟨1, by simpa using hi.symm, le_rfl⟩
  choose v hv using hbinary
  let z := v 2 * s.t
  let y := v 1 * (s.j - 2 * z)
  have hz : z ≤ s.t := by
    simpa [z] using Nat.mul_le_mul_right s.t (hv 2).2
  have hzs : 2 * z ≤ s.j := (Nat.mul_le_mul_left 2 hz).trans ht
  have hy : y ≤ s.j - 2 * z := by
    simpa [y] using Nat.mul_le_mul_right (s.j - 2 * z) (hv 1).2
  have hyz : y + 2 * z ≤ s.j := by omega
  have hys : y ≤ s.b := by omega
  have hzys : z ≤ s.b - y := by omega
  let exponents : Fin 4 → ℕ := ![v 0 * (s.b - y - z), y, z, v 3 * h]
  let e : Exponent := Finsupp.equivFunOnFinite.symm exponents
  have he (i : Fin 4) : e i = exponents i :=
    congrFun (Finsupp.equivFunOnFinite.apply_symm_apply exponents) i
  have hsupp : e ∈ capSupport s h := by
    apply mem_capSupport.mpr
    have hc₀ : v 0 * (s.b - y - z) ≤ s.b - y - z := by
      simpa using Nat.mul_le_mul_right (s.b - y - z) (hv 0).2
    have hc₃ : v 3 * h ≤ h := by simpa using Nat.mul_le_mul_right h (hv 3).2
    change e 0 + e 1 + e 2 ≤ s.b ∧ e 1 + 2 * e 2 ≤ s.j ∧ e 2 ≤ s.t ∧ e 3 ≤ h
    rw [he 0, he 1, he 2, he 3]
    change v 0 * (s.b - y - z) + y + z ≤ s.b ∧ y + 2 * z ≤ s.j ∧ z ≤ s.t ∧ v 3 * h ≤ h
    exact ⟨by omega, hyz, hz, hc₃⟩
  apply subset_convexHull ℝ _
  refine ⟨e, hsupp, ?_⟩
  have hz' : (z : ℝ) = u 2 * s.t := by
    simp only [z, Nat.cast_mul, (hv 2).1]
  have hy' : (y : ℝ) = u 1 * ((s.j : ℝ) - 2 * (u 2 * s.t)) := by
    simp only [y, Nat.cast_mul, Nat.cast_sub hzs, Nat.cast_ofNat, (hv 1).1]
    rw [hz']
  funext i
  change (e i : ℝ) = capParameter s h u i
  rw [he]
  fin_cases i
  · change (↑(v 0 * (s.b - y - z)) : ℝ) =
      u 0 * ((s.b : ℝ) - u 1 * ((s.j : ℝ) - 2 * (u 2 * s.t)) - u 2 * s.t)
    rw [Nat.cast_mul, Nat.cast_sub hzys, Nat.cast_sub hys, (hv 0).1, hy', hz']
  · exact hy'
  · exact hz'
  · change (↑(v 3 * h) : ℝ) = u 3 * h
    rw [Nat.cast_mul, (hv 3).1]
private theorem cap_cube_mem (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) (S : Finset (Fin 4)) (u : Fin 4 → ℝ)
    (hside : ∀ i ∈ S, 0 ≤ u i ∧ u i ≤ 1)
    (hcorner : ∀ i ∉ S, u i = 0 ∨ u i = 1) :
    capParameter s h u ∈ latticeBody (capSupport s h) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty =>
      exact cap_corner_mem s h hs ht u (fun i => hcorner i (by simp))
  | insert i S hi ih =>
      have updated (b : ℝ) (hb : b = 0 ∨ b = 1) :
          capParameter s h (Function.update u i b) ∈ latticeBody (capSupport s h) := by
        apply ih
        · intro j hj
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          simpa [Function.update_of_ne hji] using hside j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa using hb
          · rw [Function.update_of_ne hji]
            exact hcorner j (by simp [hji, hj])
      have hui := hside i (Finset.mem_insert_self i S)
      rw [capParameter_update s h u i]
      exact convex_convexHull ℝ _ (updated 0 (Or.inl rfl)) (updated 1 (Or.inr rfl))
        (sub_nonneg.mpr hui.2) hui.1 (sub_add_cancel 1 (u i))
private theorem exists_scale {x d : ℝ} (hx : 0 ≤ x) (hxd : x ≤ d) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ u * d = x := by
  by_cases hd : d = 0
  · exact ⟨0, le_rfl, zero_le_one, by linarith⟩
  · have hd' : 0 < d := lt_of_le_of_ne (hx.trans hxd) (Ne.symm hd)
    exact ⟨x / d, div_nonneg hx hd'.le, (div_le_one hd').mpr hxd, div_mul_cancel₀ x hd⟩
private theorem convex_capBody (s : Shape) (h : ℕ) : Convex ℝ (capBody s h) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx, hx₁, hx₂, hx₃, hx₄⟩ := hx
  obtain ⟨hy, hy₁, hy₂, hy₃, hy₄⟩ := hy
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)), ?_, ?_, ?_, ?_⟩
  · change a * x 0 + b * y 0 + (a * x 1 + b * y 1) + (a * x 2 + b * y 2) ≤ s.b
    nlinarith [mul_le_mul_of_nonneg_left hx₁ ha, mul_le_mul_of_nonneg_left hy₁ hb,
      congrArg (fun t : ℝ => t * s.b) hab]
  · change a * x 1 + b * y 1 + 2 * (a * x 2 + b * y 2) ≤ s.j
    nlinarith [mul_le_mul_of_nonneg_left hx₂ ha, mul_le_mul_of_nonneg_left hy₂ hb,
      congrArg (fun t : ℝ => t * s.j) hab]
  · change a * x 2 + b * y 2 ≤ s.t
    nlinarith [mul_le_mul_of_nonneg_left hx₃ ha, mul_le_mul_of_nonneg_left hy₃ hb,
      congrArg (fun t : ℝ => t * s.t) hab]
  · change a * x 3 + b * y 3 ≤ h
    nlinarith [mul_le_mul_of_nonneg_left hx₄ ha, mul_le_mul_of_nonneg_left hy₄ hb,
      congrArg (fun t : ℝ => t * h) hab]
theorem latticeBody_capSupport (s : Shape) (h : ℕ) (hs : s.j ≤ s.b)
    (ht : 2 * s.t ≤ s.j) : latticeBody (capSupport s h) = capBody s h := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_capBody s h)
    rintro x ⟨e, he, rfl⟩
    obtain ⟨he₁, he₂, he₃, he₄⟩ := mem_capSupport.mp he
    refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_, Nat.cast_le.mpr he₃, Nat.cast_le.mpr he₄⟩
    · change (e 0 : ℝ) + e 1 + e 2 ≤ s.b
      exact_mod_cast he₁
    · change (e 1 : ℝ) + 2 * e 2 ≤ s.j
      exact_mod_cast he₂
  · intro x hx
    obtain ⟨hx, hx₁, hx₂, hx₃, hx₄⟩ := hx
    obtain ⟨u₀, hu₀, hv₀, h₀⟩ := exists_scale (hx 0) (show x 0 ≤ s.b - x 1 - x 2 by linarith)
    obtain ⟨u₁, hu₁, hv₁, h₁⟩ := exists_scale (hx 1) (show x 1 ≤ s.j - 2 * x 2 by linarith)
    obtain ⟨u₂, hu₂, hv₂, h₂⟩ := exists_scale (hx 2) hx₃
    obtain ⟨u₃, hu₃, hv₃, h₃⟩ := exists_scale (hx 3) hx₄
    let u : Fin 4 → ℝ := ![u₀, u₁, u₂, u₃]
    have hu : capParameter s h u = x := by
      funext i
      fin_cases i
      · change u₀ * ((s.b : ℝ) - u₁ * ((s.j : ℝ) - 2 * (u₂ * s.t)) - u₂ * s.t) = x 0
        rw [h₂, h₁, h₀]
      · change u₁ * ((s.j : ℝ) - 2 * (u₂ * s.t)) = x 1
        rw [h₂, h₁]
      · exact h₂
      · exact h₃
    rw [← hu]
    apply cap_cube_mem s h hs ht Finset.univ
    · intro i _
      fin_cases i
      · exact ⟨hu₀, hv₀⟩
      · exact ⟨hu₁, hv₁⟩
      · exact ⟨hu₂, hv₂⟩
      · exact ⟨hu₃, hv₃⟩
    · simp
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators Pointwise
private theorem affineDegree_point {k σ : Type} [Field k] [Finite σ] (x : σ → k) :
    affineDegree (vanishingIdeal k {x}) = 1 := by
  have hker : vanishingIdeal k {x} = RingHom.ker (aeval x : MvPolynomial σ k →ₐ[k] k) := by
    ext p
    rw [RingHom.mem_ker, mem_vanishingIdeal_singleton_iff]
  rw [hker]
  have hs : Function.Surjective (aeval x : MvPolynomial σ k →ₐ[k] k) :=
    fun b => ⟨C b, by simp⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hs
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  rw [affineDegree_eq_finrank, e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
private theorem ratio_image_degree {k σ τ : Type} [Field k] [Finite σ] [Finite τ]
    (A : Set (σ → k)) (I : Ideal (MvPolynomial σ k)) (hI : I = vanishingIdeal k A)
    (hprime : I.IsPrime) (hdim : (affineHilbertPolynomial I).natDegree = 1)
    (hone : 1 ≤ affineDegree I) (D : MvPolynomial σ k) (N : τ → MvPolynomial σ k)
    (hD : D.totalDegree ≤ 1) (hN : ∀ i, (N i).totalDegree ≤ 1)
    (hnonzero : ∀ x ∈ A, eval x D ≠ 0) :
    ∃ Q : Ideal (MvPolynomial τ k), Q.IsPrime ∧ (affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      affineDegree Q ≤ affineDegree I ∧
      ∀ x ∈ A, (fun i => eval x (N i) / eval x D) ∈ zeroLocus k Q := by
  have hA : A.Nonempty := by
    by_contra! h
    exact hprime.ne_top (by rw [hI, h, vanishingIdeal_empty])
  obtain ⟨x₀, hx₀⟩ := hA
  let e : MvPolynomial σ k →ₐ[k] (A → k) := AlgHom.pi fun x => aeval x.val
  have he : I = RingHom.ker e := by
    ext p
    rw [hI, mem_vanishingIdeal_iff, RingHom.mem_ker, _root_.funext_iff]
    exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  clear hI
  subst I
  let I := RingHom.ker e
  let : I.IsPrime := hprime
  change (affineHilbertPolynomial I).natDegree = 1 at hdim
  change 1 ≤ affineDegree I at hone
  let R := MvPolynomial σ k ⧸ I
  let j : R →ₐ[k] (A → k) := Ideal.kerLiftAlg e
  have hj : Function.Injective j := Ideal.kerLiftAlg_injective e
  let dr : R := Ideal.Quotient.mk I D
  let d : A → k := e D
  have hjd : j dr = d := rfl
  have hd : IsUnit d := Pi.isUnit_iff.mpr fun x => isUnit_iff_ne_zero.mpr (hnonzero _ x.property)
  let y (i : τ) (x : A) : k := eval x.val (N i) / eval x.val D
  let φ : MvPolynomial τ k →ₐ[k] (A → k) := aeval y
  let Q := RingHom.ker φ
  have hφ (p : MvPolynomial τ k) (x : A) :
      φ p x = aeval (fun i => y i x) p := by
    let π := Pi.evalAlgHom k (fun _ : A => k) x
    have h : π.comp φ = aeval (fun i => y i x) := by
      apply algHom_ext
      intro i
      simp [φ, π]
    exact DFunLike.congr_fun h p
  have hy (i : τ) : d * y i = e (N i) := by
    ext x
    change eval x.val D * (eval x.val (N i) / eval x.val D) = eval x.val (N i)
    rw [mul_comm, div_mul_cancel₀ _ (hnonzero _ x.property)]
  let V (m : ℕ) : Submodule k (A → k) := (quotientDegreeLE I m).map j.toLinearMap
  let W (m : ℕ) : Submodule k (A → k) := (V m).comap (LinearMap.mulLeft k (d ^ m))
  have hW (m : ℕ) (z : A → k) :
      z ∈ W m ↔ ∃ r ∈ quotientDegreeLE I m, j r = d ^ m * z := by
    simp only [W, V, Submodule.mem_comap, Submodule.mem_map, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply]
    rfl
  have hdr_pow (n : ℕ) : dr ^ n ∈ quotientDegreeLE I n := by
    dsimp only [dr]
    rw [← map_pow]
    exact mk_mem_quotientDegreeLE ((totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left n hD))
  have hmono : Monotone W := by
    intro m n hmn z hz
    obtain ⟨r, hr, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨dr ^ (n - m) * r, ?_, ?_⟩
    · simpa only [Nat.sub_add_cancel hmn] using
        mul_mem_quotientDegreeLE (hdr_pow (n - m)) hr
    · rw [map_mul, map_pow, hjd, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  have hmul (i : τ) (m : ℕ) (z : A → k) (hz : z ∈ W m) :
      y i * z ∈ W (m + 1) := by
    obtain ⟨r, hr, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨r * Ideal.Quotient.mk I (N i),
      mul_mem_quotientDegreeLE hr (mk_mem_quotientDegreeLE (hN i)), ?_⟩
    rw [map_mul, heq, Ideal.kerLiftAlg_mk, pow_succ, ← hy]
    ring
  have hclear (p : MvPolynomial τ k) (m : ℕ) (hp : p.totalDegree ≤ m) :
      ∃ r ∈ quotientDegreeLE I m, j r = d ^ m * φ p := by
    have hz : (1 : A → k) ∈ W 0 :=
      (hW _ _).mpr ⟨1, one_mem_quotientDegreeLE I _, by simp⟩
    have h := aeval_mem_of_forall_mul_mem y hmono hz hmul hp
    rw [one_mul] at h
    exact (hW _ _).mp h
  have hQ : Q.IsPrime := by
    apply Ideal.isPrime_iff.mpr
    constructor
    · intro htop
      have hz : φ 1 = 0 := RingHom.mem_ker.mp (show 1 ∈ Q from htop ▸ Submodule.mem_top)
      rw [map_one] at hz
      exact one_ne_zero (congrFun hz ⟨x₀, hx₀⟩)
    · intro p q hpq
      have hz := RingHom.mem_ker.mp hpq
      change φ (p * q) = 0 at hz
      rw [map_mul] at hz
      obtain ⟨r, _, hr⟩ := hclear p _ le_rfl
      obtain ⟨s, _, hs⟩ := hclear q _ le_rfl
      have hrs : r * s = 0 := hj (by
        rw [map_mul, hr, hs, map_zero]
        calc
          _ = (d ^ p.totalDegree * d ^ q.totalDegree) * (φ p * φ q) := by ring
          _ = 0 := by rw [hz, mul_zero])
      rcases mul_eq_zero.mp hrs with hr₀ | hs₀
      · left
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hr, hr₀, map_zero, mul_zero])
      · right
        apply RingHom.mem_ker.mpr
        exact (hd.pow _).mul_left_cancel (by rw [← hs, hs₀, map_zero, mul_zero])
  have hgrowth (m : ℕ) : affineHilbertFunction Q m ≤ affineHilbertFunction I m := by
    let ι := Ideal.kerLiftAlg φ
    have hm (a : quotientDegreeLE Q m) : d ^ m * ι a.1 ∈ V m := by
      obtain ⟨p, hp, hp'⟩ := mem_quotientDegreeLE.mp a.2
      obtain ⟨r, hr, heq⟩ := hclear p m hp
      refine Submodule.mem_map.mpr ⟨r, hr, ?_⟩
      rw [AlgHom.toLinearMap_apply, ← hp', Ideal.kerLiftAlg_mk, heq]
    let l : quotientDegreeLE Q m →ₗ[k] V m :=
      (((LinearMap.mulLeft k (d ^ m)).comp ι.toLinearMap).domRestrict
        (quotientDegreeLE Q m)).codRestrict (V m) hm
    have hl : Function.Injective l := by
      intro a b hab
      have h : d ^ m * ι a.1 = d ^ m * ι b.1 := congrArg Subtype.val hab
      exact Subtype.ext (Ideal.kerLiftAlg_injective φ ((hd.pow _).mul_left_cancel h))
    exact (LinearMap.finrank_le_finrank_of_injective hl).trans (Submodule.finrank_map_le _ _)
  have hle : ∀ᶠ m : ℕ in Filter.atTop,
      (affineHilbertPolynomial Q).eval (m : ℚ) ≤ (affineHilbertPolynomial I).eval (m : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial Q,
      eventually_eval_affineHilbertPolynomial I] with m hq hi
    rw [hq, hi]
    exact_mod_cast hgrowth m
  obtain ⟨hdegree, hcoeff⟩ := Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg Q) hle
  have hcover (x : A) : (fun i => y i x) ∈ zeroLocus k Q := by
    intro p hp
    rw [← hφ p x, RingHom.mem_ker.mp hp]
    rfl
  refine ⟨Q, hQ, hdegree.trans_eq hdim, ?_, fun x hx => hcover ⟨x, hx⟩⟩
  by_cases heq : (affineHilbertPolynomial Q).natDegree = (affineHilbertPolynomial I).natDegree
  · rw [affineDegree, affineDegree, heq]
    exact mul_le_mul_of_nonneg_left (hcoeff heq) (Nat.cast_nonneg _)
  · have hzero : (affineHilbertPolynomial Q).natDegree = 0 := by omega
    let := hQ
    let := natDegree_affineHilbertPolynomial_eq_zero_iff.mp hzero
    have hmax := Ideal.Quotient.maximal_of_isField Q (IsField.of_isDomain_of_finite k _)
    have hpoint : Q ≤ vanishingIdeal k {(fun i => y i ⟨x₀, hx₀⟩)} := by
      intro p hp
      exact (mem_vanishingIdeal_singleton_iff _ _).mpr (hcover ⟨x₀, hx₀⟩ p hp)
    have hprime' : (vanishingIdeal k {(fun i => y i ⟨x₀, hx₀⟩)}).IsPrime := inferInstance
    rw [hmax.eq_of_le hprime'.ne_top hpoint, affineDegree_point]
    exact hone
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
private theorem box_mono {B : GeoRow 4} {s t : Shape} {h k : ℕ}
    (hb : s.b ≤ t.b) (hj : s.j ≤ t.j) (ht : s.t ≤ t.t) (hh : h ≤ k)
    (hB : InLiftedBox B s h) : InLiftedBox B t k := by
  intro a ha
  obtain ⟨hb', hj', ht', hh'⟩ := hB a ha
  exact ⟨hb'.trans hb, hj'.trans hj, ht'.trans ht, hh'.trans hh⟩
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
    exact box_mono (by norm_num [liftedBox, taylorLength]) (by norm_num [liftedBox, taylorLength])
      (by norm_num [liftedBox, taylorLength]) (Nat.zero_le _) hbox
  have hN (j : Fin taylorLength) : T.numerator j ∈ restrictSupport GeometricX lastExponents := by
    change InLiftedBox (T.numerator j) lastBox taylorLength
    exact box_mono (by norm_num [liftedBox, taylorLength]) (by norm_num [liftedBox, taylorLength])
      (by norm_num [liftedBox, taylorLength]) (Nat.sub_le _ _) (T.coefficient_box j)
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
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 →
    ∀ P ∈ factorCurves f, IsSectionCurve f P
def c2 : Prop :=
  ∀ (f : Row 3), (∀ P ∈ factorCurves f, IsSectionCurve f P) →
    Nonempty (GenericSection f)
def c3 : Prop :=
  ∀ (f : Row 3), Irreducible f → 0 < f.degreeOf 2 → ∀ (T : LiftedChart f) (L : GeoRow 4),
    (∀ P ∈ factorCurves f, L ∉ graphCurve f P) →
    ∀ P ∈ factorCurves f, ∀ y ∈ graphLocus f P, eval y L = 0 →
      let J := fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L
      pointIdeal y ∈ J.minimalPrimes ∧ componentLength f P ≤ pointLength J y
def c4 : Prop :=
  ∀ (F G E L : GeoRow 4), F ≠ 0 →
    InLiftedBox G graphBox 1 →
    InLiftedBox E (liftedBox (taylorLength + 1)) (taylorLength - 1) →
    InLiftedBox L lastBox taylorLength →
    ∀ points : Finset JetPoint,
      (∀ y ∈ points, pointIdeal y ∈ (fourCutIdeal F G E L).minimalPrimes) →
      (↑(∑ y ∈ points, (pointLength (fourCutIdeal F G E L) y).toNat) : ℝ) ≤
        lastMixedVolume (downBody F)
def c5 : Prop :=
  ∀ n (f : Fin n → Row 3), SecondFactors f →
    (∑ i, lastMixedVolume (downBody (liftRow (genericRow (f i))))) ≤ (mixedBudget : ℝ)
private theorem lift_generic_ne_zero {f : Row 3} (hf : f ≠ 0) :
    liftRow (genericRow f) ≠ 0 := by
  have hg : genericRow f ≠ 0 := by
    simpa only [genericRow, map_zero] using (map_injective _ genericCoeff_injective).ne hf
  simpa only [liftRow, map_zero] using
    (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hg
private theorem section_cost (hlocal : c3) (hsparse : c4) {f : Row 3}
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
    (hsparse _ _ _ _ (lift_generic_ne_zero hf.ne_zero) T.graph_box T.cut_box S.support points hmin)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_13_5_4.c2 := by
  classical
  intro n f hf T
  have hcurve (i : Fin n) (P) (hP : P ∈ factorCurves (f i)) : IsSectionCurve (f i) P :=
    h1 (f i) (hf.irreducible i) (hf.positive i) P hP
  let S (i : Fin n) := Classical.choice (h2 (f i) (hcurve i))
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
      section_cost h3 h4 (hf.irreducible i) (hf.positive i) (T i) (S i)).trans (h5 n f hf)
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
end K1_13_5_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial Filter MeasureTheory
open scoped BigOperators Pointwise Topology
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent),
    (∀ i, 0 ∈ A i) → Module.Finite (CoefficientField A) (GenericQuotient A) →
    ∀ (f : Fin 4 → GeoRow 4), (∀ i, (f i).support ⊆ A i) →
    ∀ points : Finset JetPoint,
      (∀ y ∈ points, pointIdeal y ∈ (cutIdeal f).minimalPrimes) →
      (∑ y ∈ points, (pointLength (cutIdeal f) y).toNat) ≤
        Module.finrank (CoefficientField A) (GenericQuotient A)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    Module.Finite (CoefficientField A) (GenericQuotient A) ∧
      ∃ q : ℕ, ∀ n : ℕ,
        (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) * (n : ℝ)^4 =
          ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
            (-1 : ℝ) ^ (4 - S.card) * (exponentCount A (corner q n S) : ℝ)
def c3 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) → (∀ i, Downward (A i)) →
    ∀ (q : ℕ) (S : Finset (Fin 4)),
      Tendsto (fun n : ℕ => (exponentCount A (corner q n S) : ℝ) / (n : ℝ)^4)
        atTop (𝓝 (volume (∑ i ∈ S, latticeBody (A i))).toReal)
private theorem mixed_eq_generic (h2 : c2) (h3 : c3)
    (A : Fin 4 → Finset Exponent) (hzero : ∀ i, 0 ∈ A i)
    (hdown : ∀ i, Downward (A i))
    (hcoords : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) :
    Module.Finite (CoefficientField A) (GenericQuotient A) ∧
      (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) =
        mixedVolume4 (fun i => latticeBody (A i)) := by
  obtain ⟨hfinite, q, hq⟩ := h2 A hzero hcoords
  refine ⟨hfinite, ?_⟩
  unfold mixedVolume4
  apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    (f := fun n : ℕ => ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * ((exponentCount A (corner q n S) : ℝ) / (n : ℝ)^4))
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ)^4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
    symm
    calc
      _ = (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
          (-1 : ℝ) ^ (4 - S.card) * (exponentCount A (corner q n S) : ℝ)) / (n : ℝ)^4 := by
        simp only [Finset.sum_div, mul_div_assoc]
      _ = _ := by rw [← hq n, mul_div_cancel_right₀ _ hn']
  · exact tendsto_finsetSum _ fun S _ => (h3 A hzero hdown q S).const_mul _
private theorem downSupport_downward (F : GeoRow 4) : Downward (downSupport F) := by
  intro a b ha hab
  obtain ⟨e, he, hae⟩ := mem_downSupport.mp ha
  exact mem_downSupport.mpr ⟨e, he, hab.trans hae⟩
private theorem capSupport_downward (s : Shape) (h : ℕ) : Downward (capSupport s h) := by
  intro a b ha hb
  have ha' := mem_capSupport.mp ha
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := ha'
  apply mem_capSupport.mpr
  exact ⟨(Nat.add_le_add (Nat.add_le_add (hb 0) (hb 1)) (hb 2)).trans hb₁,
    (Nat.add_le_add (hb 1) (Nat.mul_le_mul_left 2 (hb 2))).trans hb₂,
    (hb 2).trans hb₃, (hb 3).trans hb₄⟩
private theorem zero_mem_capSupport (s : Shape) (h : ℕ) : (0 : Exponent) ∈ capSupport s h :=
  mem_capSupport.mpr (by simp [boxExponents])
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) :
    K1_13_5_4_2.c4 := by
  classical
  intro F G E L hF hG hE hL points hpoints
  let A := cutSupports F
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
  obtain ⟨hfinite, hmv⟩ := mixed_eq_generic h2 h3 A hz hd hv
  have hbound := h1 A hz hfinite f hsup points (by simpa only [hJ] using hpoints)
  have hbodies : (fun i => latticeBody (A i)) =
      ![downBody F, capBody graphBox 1,
        capBody (liftedBox (taylorLength + 1)) (taylorLength - 1), capBody lastBox taylorLength] := by
    funext i
    fin_cases i
    · exact latticeBody_downSupport F
    · exact latticeBody_capSupport _ _ (by decide) (by decide)
    · exact latticeBody_capSupport _ _ (by decide) (by decide)
    · exact latticeBody_capSupport _ _ (by decide) (by decide)
  simpa only [hJ, hmv, hbodies, lastMixedVolume] using (Nat.cast_le (α := ℝ)).mpr hbound
end
end K1_13_5_4_2_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
open scoped Pointwise
abbrev Degree := Fin 4 → ℕ
abbrev Row (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientField A)
def exponentSet (A : Fin 4 → Finset Exponent) (d : Degree) : Set Exponent :=
  ∑ i : Fin 4, d i • (↑(A i) : Set Exponent)
def piece (A : Fin 4 → Finset Exponent) (d : Degree) : Submodule (CoefficientField A) (Row A) :=
  Submodule.span (CoefficientField A)
    (Set.range fun a : ↥(exponentSet A d) => monomial a.1 (1 : CoefficientField A))
def shift (d : Degree) (i : Fin 4) (n : ℕ) : Degree := d + Pi.single i n
def prefixIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (Row A) :=
  Ideal.span (genericEquation A '' {i : Fin 4 | (i : ℕ) < k})
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
open scoped Pointwise
variable {A : Fin 4 → Finset Exponent}
private theorem finite_nsmul (s : Set Exponent) (hs : s.Finite) (n : ℕ) : (n • s).Finite := by
  induction n with
  | zero => simpa only [zero_nsmul] using (Set.finite_zero : (0 : Set Exponent).Finite)
  | succ n ih => rw [succ_nsmul]; exact ih.add hs
private theorem exponentSet_finite (A : Fin 4 → Finset Exponent) (d : Degree) :
    (exponentSet A d).Finite := by
  classical
  unfold exponentSet
  have h (s : Finset (Fin 4)) : (∑ i ∈ s, d i • (↑(A i) : Set Exponent)).Finite := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s nhi ih =>
      rw [Finset.sum_insert nhi]
      exact (finite_nsmul _ (A i).finite_toSet _).add ih
  exact h _
instance (d : Degree) : Module.Finite (CoefficientField A) (piece A d) := by
  classical
  let _ := (exponentSet_finite A d).fintype
  exact Module.Finite.span_of_finite _ (Set.finite_range _)
private theorem monomial_mem_piece {d : Degree} {a : Exponent} (ha : a ∈ exponentSet A d)
    (c : CoefficientField A) : monomial a c ∈ piece A d := by
  have h : monomial a (1 : CoefficientField A) ∈ piece A d :=
    Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (piece A d).smul_mem c h
private theorem exponentSet_add (A : Fin 4 → Finset Exponent) (d e : Degree) :
    exponentSet A (d + e) = exponentSet A d + exponentSet A e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
private theorem exponentSet_single (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    exponentSet A (Pi.single i 1) = A i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp
theorem equation_mul_mem_piece (i : Fin 4) {d : Degree} {p : Row A}
    (hp : p ∈ piece A d) : genericEquation A i * p ∈ piece A (shift d i 1) := by
  change p ∈ Submodule.span _ _ at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    rw [genericEquation, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [monomial_mul_monomial]
    apply monomial_mem_piece
    rw [shift, exponentSet_add, exponentSet_single]
    exact Set.mem_add.mpr ⟨a, a.2, b, b.2, add_comm _ _⟩
  | zero => simp
  | add p r _ _ hp hr => simpa only [mul_add] using (piece A _).add_mem hp hr
  | smul c p _ hp => simpa only [mul_smul_comm] using (piece A _).smul_mem c hp
private theorem zero_mem_exponentSet (hz : ∀ i, 0 ∈ A i) (d : Degree) :
    (0 : Exponent) ∈ exponentSet A d := by
  classical
  have hn (i : Fin 4) (n : ℕ) : (0 : Exponent) ∈ n • (↑(A i) : Set Exponent) := by
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul]; exact Set.mem_add.mpr ⟨0, ih, 0, hz i, zero_add _⟩
  have h (s : Finset (Fin 4)) : (0 : Exponent) ∈ ∑ i ∈ s, d i • (↑(A i) : Set Exponent) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s nhi ih =>
      rw [Finset.sum_insert nhi]
      exact Set.mem_add.mpr ⟨0, hn i _, 0, ih, zero_add _⟩
  exact h _
private theorem exponentSet_mono (hz : ∀ i, 0 ∈ A i) {d e : Degree} (h : d ≤ e) :
    exponentSet A d ⊆ exponentSet A e := by
  have he : e = d + (e - d) := by
    funext i
    exact (Nat.add_sub_of_le (h i)).symm
  intro a ha
  rw [he, exponentSet_add]
  exact Set.mem_add.mpr ⟨a, ha, 0, zero_mem_exponentSet hz _, add_zero _⟩
theorem piece_mono (hz : ∀ i, 0 ∈ A i) {d e : Degree} (h : d ≤ e) : piece A d ≤ piece A e := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact monomial_mem_piece (exponentSet_mono hz h a.2) _
private theorem monomial_eventually_mem
    (hz : ∀ i, 0 ∈ A i) (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i)
    (a : Exponent) : ∃ n : ℕ, a ∈ exponentSet A (fun _ => n) := by
  classical
  have hadd {a b : Exponent} {m n : ℕ} (ha : a ∈ exponentSet A (fun _ => m))
      (hb : b ∈ exponentSet A (fun _ => n)) : a + b ∈ exponentSet A (fun _ => m + n) := by
    change _ ∈ exponentSet A ((fun _ => m) + (fun _ => n))
    rw [exponentSet_add]
    exact Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
  have hvar (j : Fin 4) : Finsupp.single j 1 ∈ exponentSet A (fun _ => 1) := by
    obtain ⟨i, hi⟩ := hv j
    exact exponentSet_mono hz (show Pi.single i 1 ≤ fun _ => 1 by
      intro l; by_cases h : l = i <;> simp [h, Pi.single_eq_of_ne])
      (by rw [exponentSet_single]; exact Finset.mem_coe.mpr hi)
  have hsingle (j : Fin 4) (m : ℕ) : Finsupp.single j m ∈ exponentSet A (fun _ => m) := by
    induction m with
    | zero => simpa using zero_mem_exponentSet hz (fun _ => 0)
    | succ m ih =>
      rw [Finsupp.single_add]
      exact hadd ih (hvar j)
  have hsum (s : Finset (Fin 4)) :
      (∑ j ∈ s, Finsupp.single j (a j)) ∈ exponentSet A (fun _ => ∑ j ∈ s, a j) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using zero_mem_exponentSet hz (fun _ => 0)
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd (hsingle j _) ih
  refine ⟨∑ j : Fin 4, a j, ?_⟩
  have ha : (∑ j : Fin 4, Finsupp.single j (a j)) = a := by
    ext j
    simp
  simpa only [ha] using hsum Finset.univ
theorem piece_exhaustive (hz : ∀ i, 0 ∈ A i)
    (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) (p : Row A) :
    ∃ n : ℕ, p ∈ piece A (fun _ => n) := by
  classical
  choose n hn using monomial_eventually_mem hz hv
  refine ⟨p.support.sup n, ?_⟩
  have hsum : (∑ a ∈ p.support, monomial a (p.coeff a)) ∈ piece A (fun _ => p.support.sup n) := by
    refine Submodule.sum_mem _ fun a ha => monomial_mem_piece ?_ _
    exact exponentSet_mono hz (show (fun _ => n a) ≤ (fun _ => p.support.sup n : Degree) from
      fun _ => Finset.le_sup ha) (hn a)
  rwa [← p.as_sum] at hsum
theorem finrank_piece (A : Fin 4 → Finset Exponent) (d : Degree) :
    Module.finrank (CoefficientField A) (piece A d) = exponentCount A d := by
  classical
  let _ := (exponentSet_finite A d).fintype
  let m : ↥(exponentSet A d) → Row A := fun a => monomial a.1 1
  have h : LinearIndependent (CoefficientField A) m :=
    (basisMonomials (Fin 4) (CoefficientField A)).linearIndependent.comp
      (fun a : ↥(exponentSet A d) => a.1) Subtype.val_injective
  change Module.finrank (CoefficientField A) (Submodule.span _ (Set.range m)) = (exponentSet A d).ncard
  exact (finrank_span_eq_card h).trans (Set.fintypeCard_eq_ncard _)
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
private def shiftSet (d : Degree) (n : ℕ) (S : Finset (Fin 4)) : Degree :=
  fun i => d i + if i ∈ S then n else 0
private def boxDiff (F : Degree → ℝ) (J : Finset (Fin 4)) (d : Degree) (n : ℕ) : ℝ :=
  ∑ S ∈ J.powerset, (-1 : ℝ) ^ (J.card - S.card) * F (shiftSet d n S)
private theorem shift_le (d : Degree) (i : Fin 4) (t : ℕ) : d ≤ shift d i t :=
  fun _ => Nat.le_add_right _ _
private theorem shiftSet_le (d : Degree) (n : ℕ) (S : Finset (Fin 4)) : d ≤ shiftSet d n S :=
  fun _ => Nat.le_add_right _ _
private theorem shift_succ (d : Degree) (i : Fin 4) (t : ℕ) :
    shift d i (t + 1) = shift (shift d i t) i 1 := by
  funext j
  by_cases h : j = i <;> simp [shift, h, Pi.single_eq_of_ne, add_assoc]
private theorem shiftSet_insert {i : Fin 4} {S : Finset (Fin 4)} (hi : i ∉ S)
    (d : Degree) (n : ℕ) : shiftSet d n (insert i S) = shift (shiftSet d n S) i n := by
  funext j
  by_cases h : j = i <;> simp [shift, shiftSet, hi, h, Pi.single_eq_of_ne]
private theorem shift_comm_shiftSet (d : Degree) (i : Fin 4) (t n : ℕ) (S : Finset (Fin 4)) :
    shift (shiftSet d n S) i t = shiftSet (shift d i t) n S := by
  funext j
  simp only [shift, shiftSet, Pi.add_apply]
  ac_rfl
private theorem line_sum {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G d)
    (d : Degree) (hd : ∀ j, q ≤ d j) (n : ℕ) :
    F (shift d i n) - F d = ∑ t ∈ Finset.range n, G (shift d i t) := by
  induction n with
  | zero => simp [shift]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, shift_succ,
      ← h (shift d i n) (fun j => (hd j).trans (shift_le d i n j))]
    ring
private theorem boxDiff_step {F G : Degree → ℝ} {q : ℕ} {i : Fin 4} {J : Finset (Fin 4)}
    (hi : i ∉ J) (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G d)
    (d : Degree) (hd : ∀ j, q ≤ d j) (n : ℕ) :
    boxDiff F (insert i J) d n = ∑ t ∈ Finset.range n, boxDiff G J (shift d i t) n := by
  unfold boxDiff
  rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have hiS : i ∉ S := fun hh => hi (hsub hh)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiS,
    Nat.add_sub_add_right, show J.card + 1 - S.card = (J.card - S.card) + 1 by omega,
    pow_succ, shiftSet_insert hiS]
  have hs : (-1 : ℝ) ^ (J.card - S.card) * (-1) * F (shiftSet d n S) +
      (-1 : ℝ) ^ (J.card - S.card) * F (shift (shiftSet d n S) i n) =
      (-1 : ℝ) ^ (J.card - S.card) *
        (F (shift (shiftSet d n S) i n) - F (shiftSet d n S)) := by ring
  rw [hs, line_sum h _ (fun j => (hd j).trans (shiftSet_le d n S j)), Finset.mul_sum]
  simp only [shift_comm_shiftSet]
theorem fourfold_telescoping (H : ℕ → Degree → ℝ) (C : ℝ) (q : ℕ)
    (hstep : ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1))
    (htop : ∀ d : Degree, (∀ j, q ≤ d j) → H 4 d = C) (n : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * H 0 (K1_13_5_4_2_4.corner q n S)) = C * (n : ℝ)^4 := by
  let tail (k : ℕ) : Finset (Fin 4) := Finset.univ.filter fun i => k ≤ i.val
  have htail (i : Fin 4) : tail i.val = insert i (tail (i.val + 1)) := by
    ext j
    simp only [tail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : j = i
      · exact Or.inl he
      · exact Or.inr (by have hne := Fin.val_ne_of_ne he; omega)
    · rintro (rfl | h)
      · exact le_rfl
      · omega
  have hnot (i : Fin 4) : i ∉ tail (i.val + 1) := by simp [tail]
  have ht4 : tail 4 = ∅ := by ext i; simp [tail, not_le.mpr i.isLt]
  have ht0 : tail 0 = Finset.univ := by simp [tail]
  have hbox (k : ℕ) (hk : k ≤ 4) : ∀ d : Degree, (∀ j, q ≤ d j) →
      boxDiff (H k) (tail k) d n = C * (n : ℝ)^(4 - k) := by
    refine Nat.decreasingInduction' (m := k) (n := 4)
      (P := fun l => ∀ d : Degree, (∀ j, q ≤ d j) →
        boxDiff (H l) (tail l) d n = C * (n : ℝ)^(4 - l)) ?_ hk ?_
    · intro l hl _ ih d hd
      let i : Fin 4 := ⟨l, hl⟩
      have hi : tail l = insert i (tail (l + 1)) := htail i
      rw [hi, boxDiff_step (hnot i) (hstep i) d hd]
      have he (t : ℕ) : boxDiff (fun e => H (l + 1) (shift e i 1))
          (tail (l + 1)) (shift d i t) n = C * (n : ℝ)^(4 - (l + 1)) := by
        unfold boxDiff
        simpa only [boxDiff, shift_comm_shiftSet] using
          ih (shift (shift d i t) i 1) (fun j =>
            ((hd j).trans (shift_le d i t j)).trans (shift_le (shift d i t) i 1 j))
      calc
        _ = ∑ _t ∈ Finset.range n, C * (n : ℝ)^(4 - (l + 1)) :=
          Finset.sum_congr rfl fun t _ => he t
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [show 4 - l = (4 - (l + 1)) + 1 by omega, pow_succ]
          ring
    · intro d hd
      have he : shiftSet d n ∅ = d := by funext j; simp [shiftSet]
      simpa [boxDiff, ht4, he] using htop d hd
  have h := hbox 0 (by decide) (fun _ => q) (fun _ => le_rfl)
  have hc (S : Finset (Fin 4)) : shiftSet (fun _ => q) n S = K1_13_5_4_2_4.corner q n S := rfl
  simpa [boxDiff, ht0, hc] using h
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def TangentStable (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  ∀ b : Row 3, genericRow b ∈ P → genericRow (tangentNumerator f b) ∈ P
def pointEval (y : Fin 3 → GeometricX) : Row 3 →+* GeometricX :=
  (MvPolynomial.eval y).comp (MvPolynomial.map genericCoeff)
def centre {F : Type*} [Field F] (e : Row 3 →+* F) : F :=
  e (MvPolynomial.C Polynomial.X)
def centredJet {F : Type*} [Field F] (f : Row 3) (e : Row 3 →+* F) : ℕ → F
  | 0 => e (MvPolynomial.X 0)
  | 1 => e (MvPolynomial.X 1)
  | 2 => e (MvPolynomial.X 2)
  | k + 3 => 2 * e (compatibilityNumerator f k) /
      (((k + 3).factorial : F) * e (separant f) ^ (2 * k + 1))
def taylorAt {F : Type*} [Field F] (f : Row 3) (e : Row 3 →+* F) : F[X] :=
  Polynomial.taylor (-centre e)
    (∑ j : Fin taylorLength, Polynomial.monomial j.val (centredJet f e j.val))
def reconstructAt (f : Row 3) (y : Fin 3 → GeometricX) : Coefficients :=
  fun j => (taylorAt f (pointEval y)).coeff j.val
def coefficientImage (f : Row 3) (P : Ideal (GeoRow 3)) : Set Coefficients :=
  reconstructAt f '' regularLocus f P
def curveIdeal (f : Row 3) (P : Ideal (GeoRow 3)) : CoefficientIdeal :=
  MvPolynomial.vanishingIdeal GeometricX (coefficientImage f P)
def trajectory {A : Type*} [CommRing A] (k : Geom →+* A) (f : Row 3) (U : A[X]) :
    A[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom k) (fun i => hasseDeriv i.val U) f
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
theorem coefficientPolynomial_reconstructAt (f : Row 3) (y : Fin 3 → GeometricX) :
    coefficientPolynomial (reconstructAt f y) = taylorAt f (pointEval y) := by
  let U := taylorAt f (pointEval y)
  have hdeg : U.natDegree ≤ taylorLength - 1 := by
    dsimp [U, taylorAt]
    rw [Polynomial.natDegree_taylor]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt i.isLt)
  change (∑ j : Fin taylorLength, Polynomial.monomial j.val (U.coeff j.val)) = U
  rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (U.coeff j))]
  exact (Polynomial.as_sum_range' U taylorLength (Nat.lt_succ_of_le hdeg)).symm
private theorem taylor_inverse_coefficient {A : Type*} [CommRing A] {L : ℕ}
    (x : A) (a : ℕ → A) (j : Fin L) :
    (hasseDeriv j.val (Polynomial.taylor (-x)
      (∑ l : Fin L, Polynomial.monomial l.val (a l.val)))).eval x = a j.val := by
  rw [← Polynomial.taylor_coeff, Polynomial.taylor_taylor, add_neg_cancel,
    Polynomial.taylor_zero, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
private theorem centredJet_initial (f : Row 3) (e : Row 3 →+* GeometricX) (i : Fin 3) :
    centredJet f e i.val = e (MvPolynomial.X i) := by
  fin_cases i <;> rfl
private theorem three_lt_length : 3 < taylorLength := by
  change 3 < 133672
  omega
theorem recover_initial (f : Row 3) (y : Fin 3 → GeometricX) (i : Fin 3) :
    (hasseDeriv i.val (taylorAt f (pointEval y))).eval (genericCoeff Polynomial.X) =
      y i := by
  have hx : centre (pointEval y) = genericCoeff Polynomial.X := by
    simp [centre, pointEval]
  let j : Fin taylorLength := ⟨i.val, i.isLt.trans three_lt_length⟩
  calc
    _ = (hasseDeriv j.val (taylorAt f (pointEval y))).eval (centre (pointEval y)) :=
      congrArg (fun x => (hasseDeriv i.val (taylorAt f (pointEval y))).eval x) hx.symm
    _ = centredJet f (pointEval y) j.val :=
      taylor_inverse_coefficient (centre (pointEval y)) (centredJet f (pointEval y)) j
    _ = pointEval y (MvPolynomial.X i) := centredJet_initial f (pointEval y) i
    _ = y i := by simp [pointEval]
theorem eval_abscissa :
    (Polynomial.evalRingHom (genericCoeff Polynomial.X)).comp
      (Polynomial.mapRingHom (algebraMap Geom GeometricX)) = genericCoeff := by
  apply Polynomial.ringHom_ext
  · intro a
    change ((Polynomial.C a).map (algebraMap Geom GeometricX)).eval
      (genericCoeff Polynomial.X) = genericCoeff (Polynomial.C a)
    rw [Polynomial.map_C, Polynomial.eval_C, ← Polynomial.algebraMap_eq]
    rfl
  · simp
theorem eval_trajectory_at_centre (f b : Row 3) (y : Fin 3 → GeometricX) :
    (extendedAtJet b (taylorAt f (pointEval y))).eval (genericCoeff Polynomial.X) =
      MvPolynomial.eval y (genericRow b) := by
  unfold extendedAtJet genericRow
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  change (Polynomial.evalRingHom (genericCoeff Polynomial.X)) (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.hom_eval₂, eval_abscissa]
  simp only [Polynomial.coe_evalRingHom, recover_initial]
theorem pointImage_in_zeroLocus (f : Row 3) (P : Ideal (GeoRow 3)) {y : Fin 3 → GeometricX}
    (hy : y ∈ regularLocus f P) :
    reconstructAt f y ∈ MvPolynomial.zeroLocus GeometricX (curveIdeal f P) :=
  MvPolynomial.zeroLocus_vanishingIdeal_le (coefficientImage f P) ⟨y, hy, rfl⟩
theorem regularLocus_nonempty (f : Row 3) (P : Ideal (GeoRow 3)) (hp : P.IsPrime)
    (hsep : genericRow (separant f) ∉ P) : (regularLocus f P).Nonempty := by
  classical
  let _ := hp
  by_contra hn
  apply hsep
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeometricX) P]
  intro y hy
  change MvPolynomial.eval y (genericRow (separant f)) = 0
  by_contra he
  exact hn ⟨y, hy, he⟩
private def universalTrajectory (f : Row 3) : (GeoRow taylorLength)[X] :=
  trajectory ((MvPolynomial.C : GeometricX →+* GeoRow taylorLength).comp
    (algebraMap Geom GeometricX)) f
    (∑ j : Fin taylorLength, Polynomial.monomial j.val (MvPolynomial.X j))
private theorem map_trajectory {A B : Type*} [CommRing A] [CommRing B]
    (h : A →+* B) (k : Geom →+* A) (f : Row 3) (U : A[X]) :
    (trajectory k f U).map h = trajectory (h.comp k) f (U.map h) := by
  unfold trajectory
  change (Polynomial.mapRingHom h) (MvPolynomial.eval₂ _ _ _) = _
  rw [MvPolynomial.hom_eval₂]
  simp only [Polynomial.coe_mapRingHom, Polynomial.hasseDeriv_map, Polynomial.mapRingHom_comp]
private theorem eval_universalTrajectory (f : Row 3) (a : Coefficients) :
    (universalTrajectory f).map (MvPolynomial.eval a) =
      extendedAtJet f (coefficientPolynomial a) := by
  unfold universalTrajectory
  rw [map_trajectory]
  have hk : (MvPolynomial.eval a).comp ((MvPolynomial.C :
      GeometricX →+* GeoRow taylorLength).comp (algebraMap Geom GeometricX)) =
      algebraMap Geom GeometricX := RingHom.ext fun z => by simp
  rw [hk]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X]
  unfold trajectory extendedAtJet coefficientPolynomial
  rw [MvPolynomial.eval_map]
theorem solves_on_closure (f : Row 3) (P : Ideal (GeoRow 3))
    (h : ∀ y ∈ regularLocus f P, extendedAtJet f (taylorAt f (pointEval y)) = 0)
    (a : Coefficients) (ha : a ∈ MvPolynomial.zeroLocus GeometricX (curveIdeal f P)) :
    extendedAtJet f (coefficientPolynomial a) = 0 := by
  rw [← eval_universalTrajectory]
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply ha
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  change MvPolynomial.eval (reconstructAt f y) ((universalTrajectory f).coeff m) = 0
  rw [← Polynomial.coeff_map, eval_universalTrajectory, coefficientPolynomial_reconstructAt,
    h y hy, Polynomial.coeff_zero]
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2
noncomputable section
open K1_13_5_4_2_4
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    Module.Finite (CoefficientField A) (GenericQuotient A)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    ∀ (i : Fin 4) (p : Row A),
      genericEquation A i * p ∈ prefixIdeal A i.val → p ∈ prefixIdeal A i.val
def c3 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent), (∀ i, 0 ∈ A i) →
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    ∃ q : ℕ, ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
        ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val
private def affineMk (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Row A →ₐ[CoefficientField A] Row A ⧸ prefixIdeal A k :=
  Ideal.Quotient.mkₐ (CoefficientField A) (prefixIdeal A k)
private def quotPiece (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) :
    Submodule (CoefficientField A) (Row A ⧸ prefixIdeal A k) :=
  (piece A d).map (affineMk A k).toLinearMap
private instance (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) :
    Module.Finite (CoefficientField A) (quotPiece A k d) := by
  unfold quotPiece
  infer_instance
private def hilbert (A : Fin 4 → Finset Exponent) (k : ℕ) (d : Degree) : ℕ :=
  Module.finrank (CoefficientField A) (quotPiece A k d)
variable {A : Fin 4 → Finset Exponent}
private theorem affineMk_zero (k : ℕ) (p : Row A) :
    affineMk A k p = 0 ↔ p ∈ prefixIdeal A k := Ideal.Quotient.eq_zero_iff_mem
private theorem affineMk_eq (k : ℕ) (p r : Row A) :
    affineMk A k p = affineMk A k r ↔ p - r ∈ prefixIdeal A k := by
  rw [← affineMk_zero, map_sub, sub_eq_zero]
private theorem prefix_mono {k l : ℕ} (h : k ≤ l) : prefixIdeal A k ≤ prefixIdeal A l :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
private theorem equation_mem_next (i : Fin 4) : genericEquation A i ∈ prefixIdeal A (i.val + 1) :=
  Ideal.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
private theorem hilbert_zero (A : Fin 4 → Finset Exponent) (d : Degree) :
    hilbert A 0 d = exponentCount A d := by
  have hbot : prefixIdeal A 0 = ⊥ := by simp [prefixIdeal]
  let f := ((affineMk A 0).toLinearMap.comp (piece A d).subtype)
  have hrange : LinearMap.range f = quotPiece A 0 d := by
    simp [f, quotPiece, LinearMap.range_comp]
  have hinj : Function.Injective f := by
    intro p r hpr
    apply Subtype.ext
    change affineMk A 0 (p : Row A) = affineMk A 0 (r : Row A) at hpr
    have hm := (affineMk_eq 0 (p : Row A) (r : Row A)).mp hpr
    rw [hbot, Ideal.mem_bot] at hm
    exact sub_eq_zero.mp hm
  unfold hilbert
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_piece]
private theorem prefix_four (A : Fin 4 → Finset Exponent) :
    prefixIdeal A 4 = Ideal.span (Set.range (genericEquation A)) := by
  have h : {i : Fin 4 | (i : ℕ) < 4} = Set.univ := Set.eq_univ_of_forall fun i => i.isLt
  rw [prefixIdeal, h, Set.image_univ]
private theorem hilbert_stable (hz : ∀ i, 0 ∈ A i)
    (hv : ∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i)
    (hf : Module.Finite (CoefficientField A) (GenericQuotient A)) :
    ∃ q : ℕ, ∀ d : Degree, (∀ j, q ≤ d j) →
      hilbert A 4 d = Module.finrank (CoefficientField A) (GenericQuotient A) := by
  let hfin : Module.Finite (CoefficientField A) (Row A ⧸ prefixIdeal A 4) := by
    rw [prefix_four]; exact hf
  let N : ℕ →o Submodule (CoefficientField A) (Row A ⧸ prefixIdeal A 4) :=
    ⟨fun n => quotPiece A 4 (fun _ => n),
      fun _ _ h => Submodule.map_mono (piece_mono hz fun _ => h)⟩
  have hsup : (⨆ n, N n) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective (CoefficientField A) (prefixIdeal A 4) x
    obtain ⟨n, hn⟩ := piece_exhaustive hz hv p
    exact le_iSup N n (Submodule.mem_map_of_mem hn)
  obtain ⟨q, hq⟩ := hfin.fg_top.stabilizes_of_iSup_eq N hsup
  refine ⟨q, fun d hd => ?_⟩
  have hqd : quotPiece A 4 d = ⊤ := top_unique (by
    rw [hq]
    exact Submodule.map_mono (piece_mono hz hd))
  unfold hilbert
  rw [hqd, finrank_top, prefix_four]
private theorem rank_step (i : Fin 4) (d : Degree)
    (hinj : ∀ p : Row A, genericEquation A i * p ∈ prefixIdeal A i.val → p ∈ prefixIdeal A i.val)
    (hlift : ∀ p ∈ piece A (shift d i 1), p ∈ prefixIdeal A (i.val + 1) →
      ∃ r ∈ piece A d, p - genericEquation A i * r ∈ prefixIdeal A i.val) :
    hilbert A (i.val + 1) (shift d i 1) + hilbert A i.val d = hilbert A i.val (shift d i 1) := by
  let f := Ideal.Quotient.factorₐ (CoefficientField A)
    (prefix_mono (A := A) (Nat.le_succ i.val))
  have hf (p : Row A) : f (affineMk A i.val p) = affineMk A (i.val + 1) p := rfl
  let cut : quotPiece A i.val (shift d i 1) →ₗ[CoefficientField A]
      quotPiece A (i.val + 1) (shift d i 1) :=
    f.toLinearMap.restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hf p).symm⟩)
  let mul : quotPiece A i.val d →ₗ[CoefficientField A] quotPiece A i.val (shift d i 1) :=
    (LinearMap.mulLeft (CoefficientField A) (affineMk A i.val (genericEquation A i))).restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, equation_mul_mem_piece i hp, map_mul (affineMk A i.val) _ _⟩)
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, he⟩ := y.property
    exact ⟨⟨affineMk A i.val p, ⟨p, hp, rfl⟩⟩, Subtype.ext ((hf p).trans he)⟩
  have hmul : Function.Injective mul := by
    apply (LinearMap.ker_eq_bot (f := mul)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨p, _, hp⟩ := x.property
    change affineMk A i.val p = (x : Row A ⧸ prefixIdeal A i.val) at hp
    have hz : affineMk A i.val (genericEquation A i * p) = 0 := by
      rw [map_mul]
      have h := congrArg Subtype.val hx
      change affineMk A i.val (genericEquation A i) * (x : Row A ⧸ prefixIdeal A i.val) = 0 at h
      rwa [hp]
    have hpI := hinj p ((affineMk_zero _ _).mp hz)
    exact Subtype.ext (hp.symm.trans ((affineMk_zero _ _).mpr hpI))
  have hk : LinearMap.range mul = LinearMap.ker cut := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change f (affineMk A i.val (genericEquation A i) * (x : Row A ⧸ prefixIdeal A i.val)) = 0
      rw [map_mul, hf, (affineMk_zero _ _).mpr (equation_mem_next i), zero_mul]
    · intro hy
      obtain ⟨p, hp, he⟩ := y.property
      change affineMk A i.val p = (y : Row A ⧸ prefixIdeal A i.val) at he
      have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      change f (y : Row A ⧸ prefixIdeal A i.val) = 0 at hz
      rw [← he, hf] at hz
      obtain ⟨r, hr, hrel⟩ := hlift p hp ((affineMk_zero _ _).mp hz)
      refine ⟨⟨affineMk A i.val r, ⟨r, hr, rfl⟩⟩, Subtype.ext ?_⟩
      change affineMk A i.val (genericEquation A i) * affineMk A i.val r = (y : Row A ⧸ prefixIdeal A i.val)
      rw [← he, ← map_mul]
      exact ((affineMk_eq _ _ _).mpr hrel).symm
  have hdim := LinearMap.finrank_range_add_finrank_ker cut
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hk,
    LinearMap.finrank_range_of_inj hmul] at hdim
  exact hdim
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_4_2_4.c2 := by
  intro A hz hv
  have hfinite := h1 A hz
  obtain ⟨q1, hq1⟩ := h3 A hz hv
  obtain ⟨q2, hq2⟩ := hilbert_stable hz hv hfinite
  refine ⟨hfinite, max q1 q2, fun n => ?_⟩
  let H (k : ℕ) (d : Degree) : ℝ := hilbert A k d
  have hstep (i : Fin 4) (d : Degree) (hd : ∀ j, max q1 q2 ≤ d j) :
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1) := by
    have hnat := rank_step i d (h2 A hz i) (hq1 i d fun j => (le_max_left _ _).trans (hd j))
    dsimp only [H]
    rw [sub_eq_iff_eq_add]
    exact_mod_cast hnat.symm
  have htop (d : Degree) (hd : ∀ j, max q1 q2 ≤ d j) :
      H 4 d = (Module.finrank (CoefficientField A) (GenericQuotient A) : ℝ) := by
    dsimp only [H]
    rw [hq2 d fun j => (le_max_right _ _).trans (hd j)]
  simpa only [H, hilbert_zero] using (fourfold_telescoping H _ _ hstep htop n).symm
end
end K1_13_5_4_2_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4
abbrev OpenRing {R : Type*} [CommRing R] (I : Ideal R) (s : R) :=
  Localization.Away (Ideal.Quotient.mk I s)
def onOpen {R : Type*} [CommRing R] (I : Ideal R) (s : R) : R →+* OpenRing I s :=
  (algebraMap (R ⧸ I) (OpenRing I s)).comp (Ideal.Quotient.mk I)
abbrev sep (f : Row 3) : GeoRow 3 := genericRow (separant f)
abbrev liftedSep (f : Row 3) : GeoRow 4 := liftRow (sep f)
def threeCut (f : Row 3) (T : LiftedChart f) : Ideal (GeoRow 4) :=
  graphIdeal f ⊔ Ideal.span {T.cut}
abbrev OldOpen (f : Row 3) := OpenRing (oldCutIdeal f) (sep f)
abbrev GraphOpen (f : Row 3) (T : LiftedChart f) := OpenRing (threeCut f T) (liftedSep f)
abbrev oldMap (f : Row 3) := onOpen (oldCutIdeal f) (sep f)
abbrev graphMap (f : Row 3) (T : LiftedChart f) := onOpen (threeCut f T) (liftedSep f)
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
@[simp] private theorem coeff_coeffDerivative (P : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_C (p : Geom[X]) :
    coeffDerivative (MvPolynomial.C p : Row 3) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coeffDerivative_add (P Q : Row 3) :
    coeffDerivative (P + Q) = coeffDerivative P + coeffDerivative Q := by
  ext m
  simp
private theorem coeffDerivative_mul_X (P : Row 3) (j : Fin 3) :
    coeffDerivative (P * MvPolynomial.X j) = coeffDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coeffDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem eval_chain (P : Row 3) (a : Fin 3 → Geom[X]) :
    derivative (MvPolynomial.eval a P) = MvPolynomial.eval a (coeffDerivative P) +
      ∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [coeffDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coeffDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, MvPolynomial.eval_X, derivative_mul, ih, coeffDerivative_mul_X,
      map_mul, MvPolynomial.eval_X]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X,
      mul_add, Finset.sum_add_distrib]
    have left : (∑ i, derivative (a i) *
          (MvPolynomial.eval a (MvPolynomial.pderiv i P) * a j)) =
        (∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P)) * a j := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, derivative (a i) *
          (MvPolynomial.eval a P * MvPolynomial.eval a (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        derivative (a j) * MvPolynomial.eval a P := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
private theorem derivative_hasse_one (S : Geom[X]) :
    derivative (hasseDeriv 1 S) = 2 * hasseDeriv 2 S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 1) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul] using h
private theorem eval_lowerTangent (P : Row 3) (S : Geom[X]) :
    derivative (atJet P S) = atJet (lowerTangent P) S +
      derivative (jet S (2 : Fin 3)) * atJet (separant P) S := by
  unfold atJet lowerTangent separant
  rw [eval_chain, Fin.sum_univ_three]
  simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
  have h0 : derivative (jet S (0 : Fin 3)) = jet S (1 : Fin 3) := by
    simp [jet]
  have h1 : derivative (jet S (1 : Fin 3)) = 2 * jet S (2 : Fin 3) :=
    derivative_hasse_one S
  rw [h0, h1]
  ring
private theorem eval_tangentNumerator (f P : Row 3) (S : Geom[X]) (hf : atJet f S = 0) :
    atJet (tangentNumerator f P) S = atJet (separant f) S * derivative (atJet P S) := by
  have hz : atJet (lowerTangent f) S +
      derivative (jet S (2 : Fin 3)) * atJet (separant f) S = 0 := by
    rw [← eval_lowerTangent, hf, map_zero]
  unfold tangentNumerator
  rw [eval_lowerTangent]
  change (MvPolynomial.eval (jet S)) (_ - _) = _
  rw [map_sub, map_mul, map_mul]
  change atJet (separant f) S * atJet (lowerTangent P) S -
      atJet (lowerTangent f) S * atJet (separant P) S = _
  linear_combination -atJet (separant P) S * hz
private theorem cleared_product_rule (a : ℕ) (U V : Geom[X]) :
    U * (U * derivative (U^a * V)) - (a : Geom[X]) * (U * derivative U) * (U^a * V) =
      U^(a+2) * derivative V := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one,
      pow_add U (a+1) 2, pow_succ' U a]
    simp only [C_eq_natCast]
    push_cast
    ring
theorem eval_compatibility (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0) (k : ℕ) :
    atJet (compatibilityNumerator f k) S =
      atJet (separant f) S ^ (2 * k + 1) *
        ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)) := by
  induction k with
  | zero =>
    have hz : atJet (lowerTangent f) S +
        derivative (jet S (2 : Fin 3)) * atJet (separant f) S = 0 := by
      rw [← eval_lowerTangent, hf, map_zero]
    change MvPolynomial.eval (jet S) (-lowerTangent f) =
      atJet (separant f) S ^ (2 * 0 + 1) *
        ((derivative (R := Geom))^[0 + 1]) (jet S (2 : Fin 3))
    rw [map_neg]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, Function.iterate_one]
    change -atJet (lowerTangent f) S = _
    linear_combination -hz
  | succ k ih =>
    let e := MvPolynomial.eval (jet S : Fin 3 → Geom[X])
    change e (_ - _) = _
    rw [map_sub, map_mul, map_mul, map_mul, map_natCast]
    change atJet (separant f) S * atJet (tangentNumerator f (compatibilityNumerator f k)) S -
      (↑(2 * k + 1) : Geom[X]) * atJet (compatibilityNumerator f k) S *
        atJet (tangentNumerator f (separant f)) S = _
    rw [eval_tangentNumerator _ _ _ hf, eval_tangentNumerator _ _ _ hf, ih]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      Function.iterate_succ_apply' (derivative (R := Geom)) (k + 1) (jet S (2 : Fin 3))]
    calc
      _ = atJet (separant f) S * (atJet (separant f) S *
          derivative (atJet (separant f) S ^ (2 * k + 1) *
            ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))) -
          (↑(2 * k + 1) : Geom[X]) * (atJet (separant f) S * derivative (atJet (separant f) S)) *
            (atJet (separant f) S ^ (2 * k + 1) *
              ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3))) := by ring
      _ = _ := cleared_product_rule (2 * k + 1) (atJet (separant f) S)
        (((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))
private theorem twice_iterate_derivative_top (k : ℕ) (S : Geom[X]) :
    2 * ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)) =
      ((derivative (R := Geom))^[k + 3]) S := by
  have hsecond : ((derivative (R := Geom))^[2]) S = 2 * jet S (2 : Fin 3) := by
    rw [Function.iterate_succ_apply' (derivative (R := Geom)) 1 S, Function.iterate_one]
    change derivative (derivative S) = 2 * hasseDeriv 2 S
    simpa only [hasseDeriv_one'] using derivative_hasse_one S
  rw [show k + 3 = (k + 1) + 2 by omega,
    Function.iterate_add_apply (derivative (R := Geom)) (k + 1) 2 S, hsecond]
  simpa only [Nat.cast_ofNat] using
    (Polynomial.iterate_derivative_natCast_mul (n := 2) (k := k + 1)
      (f := jet S (2 : Fin 3))).symm
private theorem factorial_ne_zero (j : ℕ) (hj : j < K1.p) :
    (j.factorial : GeometricX) ≠ 0 := by
  let g : K1.K →+* GeometricX := genericCoeff.comp (Polynomial.C.comp embed)
  intro hz
  have hK : (j.factorial : K1.K) = 0 :=
    g.injective (by simpa only [map_natCast, map_zero] using hz)
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  exact (not_le_of_gt hj) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K1.K K1.p _).mp hK))
private theorem centredJet_mark (f : Row 3) (S : Geom[X]) (hr : RegularAt 2 f S)
    (j : ℕ) (hj : j < taylorLength) :
    centredJet f (pointEval (jetPoint S)) j = genericCoeff (hasseDeriv j S) := by
  rcases j with _ | _ | _ | k
  · simp [centredJet, pointEval, jetPoint, jet]
  · simp [centredJet, pointEval, jetPoint, jet]
  · simp [centredJet, pointEval, jetPoint, jet]
  have he (b : Row 3) : pointEval (jetPoint S) b = genericCoeff (atJet b S) :=
    eval_genericRow_at_point b S
  have hsep : genericCoeff (atJet (separant f) S) ≠ 0 :=
    fun h => hr.2 (genericCoeff_injective (h.trans genericCoeff.map_zero.symm))
  have hchar : taylorLength < K1.p := by
    change 133672 < 2130706433
    omega
  have hfact : ((k + 3).factorial : GeometricX) ≠ 0 :=
    factorial_ne_zero _ (hj.trans hchar)
  change centredJet f (pointEval (jetPoint S)) (k + 3) = genericCoeff (hasseDeriv (k + 3) S)
  rw [centredJet, he, he, eval_compatibility _ _ hr.1, map_mul, map_pow]
  apply (div_eq_iff (mul_ne_zero hfact (pow_ne_zero _ hsep))).mpr
  rw [show 2 * (genericCoeff (atJet (separant f) S) ^ (2 * k + 1) *
      genericCoeff (((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3)))) =
      genericCoeff (atJet (separant f) S) ^ (2 * k + 1) *
      genericCoeff (2 * ((derivative (R := Geom))^[k + 1]) (jet S (2 : Fin 3))) by
    rw [map_mul, map_ofNat]
    ring]
  have hscale : ((derivative (R := Geom))^[k + 3]) S =
      ((k + 3).factorial : Geom[X]) * hasseDeriv (k + 3) S := by
    rw [← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]
  rw [twice_iterate_derivative_top, hscale, map_mul, map_natCast]
  ring
theorem reconstructAt_mark (f : Row 3) (S : Geom[X]) (hS : S.natDegree ≤ 133671)
    (hr : RegularAt 2 f S) :
    reconstructAt f (jetPoint S) = coefficientPoint S := by
  let U := S.map (algebraMap Geom GeometricX)
  let x := genericCoeff Polynomial.X
  have hx : centre (pointEval (jetPoint S)) = x := by
    simp [centre, pointEval, x]
  have hdegree : (Polynomial.taylor x U).natDegree < taylorLength := by
    rw [Polynomial.natDegree_taylor, show U.natDegree = S.natDegree from
      Polynomial.natDegree_map_eq_of_injective (algebraMap Geom GeometricX).injective S]
    exact Nat.lt_succ_of_le hS
  have htaylor : (∑ j : Fin taylorLength,
      Polynomial.monomial j.val (centredJet f (pointEval (jetPoint S)) j.val)) =
      Polynomial.taylor x U := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      Polynomial.monomial j (centredJet f (pointEval (jetPoint S)) j))]
    conv_rhs => rw [Polynomial.as_sum_range' _ taylorLength hdegree]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [centredJet_mark f S hr j (Finset.mem_range.mp hj), Polynomial.taylor_coeff]
    congr 1
    dsimp [U, x]
    rw [Polynomial.hasseDeriv_map]
    exact (RingHom.congr_fun eval_abscissa (hasseDeriv j S)).symm
  have hU : taylorAt f (pointEval (jetPoint S)) = U := by
    rw [taylorAt, hx, htaylor, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  funext j
  change (taylorAt f (pointEval (jetPoint S))).coeff j.val =
    algebraMap Geom GeometricX (S.coeff j.val)
  rw [hU, Polynomial.coeff_map]
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
theorem onOpen_kills {R : Type*} [CommRing R] {I : Ideal R} {s a : R} (ha : a ∈ I) :
    onOpen I s a = 0 := by
  rw [onOpen, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
theorem onOpen_isUnit {R : Type*} [CommRing R] (I : Ideal R) (s : R) :
    IsUnit (onOpen I s s) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I s)
theorem onOpen_hom_ext {R A : Type*} [CommRing R] [CommRing A] {I : Ideal R} {s : R}
    {g h : OpenRing I s →+* A} (he : g.comp (onOpen I s) = h.comp (onOpen I s)) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I s))
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun he b
def openLift {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (s : R)
    (b : R →+* A) (hI : I ≤ RingHom.ker b) (hs : IsUnit (b s)) : OpenRing I s →+* A :=
  let g := Ideal.Quotient.lift I b fun _ hx => RingHom.mem_ker.mp (hI hx)
  IsLocalization.Away.lift (g := g) (Ideal.Quotient.mk I s) hs
@[simp] theorem openLift_onOpen {R A : Type*} [CommRing R] [CommRing A] (I : Ideal R) (s : R)
    (b : R →+* A) (hI : I ≤ RingHom.ker b) (hs : IsUnit (b s)) (a : R) :
    openLift I s b hI hs (onOpen I s a) = b a :=
  IsLocalization.Away.lift_eq (g := Ideal.Quotient.lift I b
    fun _ hx => RingHom.mem_ker.mp (hI hx)) (Ideal.Quotient.mk I s) hs (Ideal.Quotient.mk I a)
private theorem three_ne_zero : (3 : GeometricX) ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  let : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  let : CharP GeometricX K1.p :=
    charP_of_injective_ringHom genericCoeff_injective K1.p
  exact fun h => (by decide : ¬ K1.p ∣ 3)
    ((CharP.cast_eq_zero_iff GeometricX K1.p 3).mp h)
private theorem three_isUnit {A : Type*} [CommRing A] (c : GeometricX →+* A) :
    IsUnit (3 : A) := by
  simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr three_ne_zero).map c
private theorem graph_coord_unique {A : Type*} [CommRing A] (f : Row 3)
    (w : GeoRow 4 →+* A) (hu : IsUnit (w (liftedSep f))) (hG : w (graph f) = 0)
    {z : A} (hz : w (liftRow (genericRow (lowerTangent f))) + 3 * z * w (liftedSep f) = 0) :
    w (MvPolynomial.X 3) = z := by
  have hh := hG
  rw [graph, map_add, map_mul, map_mul, map_ofNat] at hh
  have he := add_left_cancel (hh.trans hz.symm)
  have hc (x : A) : 3 * x * w (liftedSep f) = (3 * w (liftedSep f)) * x := by ring
  rw [hc, hc] at he
  exact ((three_isUnit (w.comp C)).mul hu).mul_left_cancel he
private theorem represents_vanish {A : Type*} [CommRing A] {f old : Row 3} {F : GeoRow 4}
    (hF : RepresentsOnGraph f old F) (w : GeoRow 4 →+* A)
    (hG : graphIdeal f ≤ RingHom.ker w) (hs : IsUnit (w (liftedSep f))) :
    w F = 0 ↔ w (liftRow (genericRow old)) = 0 := by
  obtain ⟨a, b, c, hc, hm⟩ := hF
  have he := RingHom.mem_ker.mp (hG hm)
  simp only [map_mul, map_sub, map_pow] at he
  have hz : w (liftedSep f) ^ b * w F = w (C c) * w (liftRow (genericRow old)) := by
    apply sub_eq_zero.mp
    apply (hs.pow a).mul_left_cancel
    simpa only [mul_zero] using he
  constructor
  · intro h
    have hu : IsUnit (w (C c)) := (isUnit_iff_ne_zero.mpr hc).map (w.comp C)
    apply hu.mul_left_cancel
    rw [mul_zero, ← hz, h, mul_zero]
  · intro h
    apply (hs.pow b).mul_left_cancel
    rw [mul_zero, hz, h, mul_zero]
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
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 MvPolynomial
abbrev Slot (A : Fin 4 → Finset Exponent) := (i : Fin 4) × ↥(A i)
abbrev SlotRing (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Slot A) (CoefficientField A)
def slotWeight (A : Fin 4 → Finset Exponent) (v : Slot A) : Degree :=
  Pi.single v.1 1
abbrev slotPiece (A : Fin 4 → Finset Exponent) (d : Degree) :=
  weightedHomogeneousSubmodule (CoefficientField A) (slotWeight A) d
def dehom (A : Fin 4 → Finset Exponent) : SlotRing A →ₐ[CoefficientField A] Row A :=
  aeval fun v => monomial v.2.val 1
def relationGenerators (A : Fin 4 → Finset Exponent) (k : ℕ) : Set (SlotRing A) :=
  {f | (∃ d, f ∈ slotPiece A d) ∧ dehom A f ∈ prefixIdeal A k}
def relationIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (SlotRing A) :=
  Ideal.span (relationGenerators A k)
def homogeneousEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) : SlotRing A :=
  ∑ a : ↥(A i), C (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩)) *
    MvPolynomial.X ⟨i, a⟩
def cutIdeal (A : Fin 4 → Finset Exponent) (k : ℕ) : Ideal (SlotRing A) :=
  relationIdeal A 0 ⊔ Ideal.span (homogeneousEquation A '' {i : Fin 4 | (i : ℕ) < k})
def chartProduct (A : Fin 4 → Finset Exponent) (b : (i : Fin 4) → ↥(A i)) :
    SlotRing A :=
  ∏ i : Fin 4, MvPolynomial.X (⟨i, b i⟩ : Slot A)
def constantChart (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i) : SlotRing A :=
  chartProduct A fun i => ⟨0, hz i⟩
open scoped Pointwise
private def affineWeight (A : Fin 4 → Finset Exponent) (v : Slot A) : Exponent :=
  v.2.val
private def exponentImage (A : Fin 4 → Finset Exponent) (d : Degree) : Set Exponent :=
  {a | ∃ e : Slot A →₀ ℕ,
    Finsupp.weight (slotWeight A) e = d ∧ Finsupp.weight (affineWeight A) e = a}
private theorem exponentSet_add (A : Fin 4 → Finset Exponent) (d e : Degree) :
    exponentSet A (d + e) = exponentSet A d + exponentSet A e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
private theorem exponentSet_single (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    exponentSet A (Pi.single i 1) = A i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp
private theorem sumset_eq_exponentImage (A : Fin 4 → Finset Exponent) (d : Degree) :
    exponentSet A d = exponentImage A d := by
  classical
  have hadd (d e : Degree) :
      exponentImage A d + exponentImage A e ⊆ exponentImage A (d + e) := by
    intro m hm
    obtain ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_add.mp hm
    exact ⟨u + v, by rw [map_add, hu, hv], map_add _ _ _⟩
  have hzero : (0 : Exponent) ∈ exponentImage A 0 :=
    ⟨0, map_zero _, map_zero _⟩
  have hsingle (i : Fin 4) : (↑(A i) : Set Exponent) ⊆ exponentImage A (Pi.single i 1) := by
    intro a ha
    let v : Slot A := ⟨i, ⟨a, ha⟩⟩
    exact ⟨Finsupp.single v 1, by rw [Finsupp.weight_single, one_smul]; rfl,
      by rw [Finsupp.weight_single, one_smul]; rfl⟩
  have hscale (i : Fin 4) (n : ℕ) :
      n • (↑(A i) : Set Exponent) ⊆ exponentImage A (n • Pi.single i 1) := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact (Set.add_subset_add ih (hsingle i)).trans (hadd _ _)
  have hsum (s : Finset (Fin 4)) :
      (∑ i ∈ s, d i • (↑(A i) : Set Exponent)) ⊆
        exponentImage A (∑ i ∈ s, d i • Pi.single i 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Set.add_subset_add (hscale i _) ih).trans (hadd _ _)
  apply Set.Subset.antisymm
  · have hdeg : (∑ i : Fin 4, d i • Pi.single i (1 : ℕ)) = d := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    simpa only [exponentSet, hdeg] using hsum Finset.univ
  · clear hsum
    rintro _ ⟨e, rfl, rfl⟩
    induction e using Finsupp.induction_linear with
    | zero => simp [exponentSet]
    | add e f he hf =>
      rw [map_add, map_add, exponentSet_add]
      exact Set.mem_add.mpr ⟨_, he, _, hf, rfl⟩
    | single v n =>
      rw [Finsupp.weight_single, Finsupp.weight_single]
      have hv : affineWeight A v ∈ exponentSet A (slotWeight A v) := by
        rw [slotWeight, exponentSet_single]
        exact v.2.property
      induction n with
      | zero => simp [exponentSet]
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul, exponentSet_add]
        exact Set.mem_add.mpr ⟨_, ih, _, hv, rfl⟩
private theorem dehom_monomial_one (A : Fin 4 → Finset Exponent) (e : Slot A →₀ ℕ) :
    dehom A (monomial e 1) = monomial (Finsupp.weight (affineWeight A) e) 1 := by
  induction e using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add e f he hf =>
    rw [← one_mul (1 : CoefficientField A), ← monomial_mul_monomial, map_mul, he, hf,
      monomial_mul_monomial, one_mul, map_add]
  | single v n =>
    rw [← X_pow_eq_monomial, map_pow, dehom, aeval_X]
    change (monomial (affineWeight A v) (1 : CoefficientField A)) ^ n = _
    rw [monomial_pow, one_pow, Finsupp.weight_single]
theorem map_slotPiece (A : Fin 4 → Finset Exponent) (d : Degree) :
    (slotPiece A d).map (dehom A).toLinearMap = piece A d := by
  have hS : slotPiece A d = restrictSupport (CoefficientField A)
      {e | Finsupp.weight (slotWeight A) e = d} :=
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
  rw [hS, restrictSupport_eq_span, Submodule.map_span, piece]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    rw [AlgHom.toLinearMap_apply, dehom_monomial_one]
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [sumset_eq_exponentImage]
    exact ⟨e, he, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha : a.val ∈ exponentImage A d := by
      rw [← sumset_eq_exponentImage]
      exact a.property
    obtain ⟨e, he, hea⟩ := ha
    exact ⟨_, ⟨e, he, rfl⟩, by rw [AlgHom.toLinearMap_apply, dehom_monomial_one, hea]⟩
variable {A : Fin 4 → Finset Exponent}
theorem homogeneousEquation_mem (i : Fin 4) :
    homogeneousEquation A i ∈ slotPiece A (Pi.single i 1) := by
  classical
  apply Submodule.sum_mem
  intro a _
  have hC := isWeightedHomogeneous_C (slotWeight A)
    (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X ⟨i, a⟩))
  have hX := isWeightedHomogeneous_X (CoefficientField A) (slotWeight A) (⟨i, a⟩ : Slot A)
  simpa only [mem_weightedHomogeneousSubmodule, zero_add, slotWeight] using hC.mul hX
theorem dehom_equation (i : Fin 4) :
    dehom A (homogeneousEquation A i) = genericEquation A i := by
  classical
  simp only [homogeneousEquation, genericEquation, map_sum, map_mul, dehom, aeval_C,
    algebraMap_eq, aeval_X, C_mul_monomial, mul_one]
end
end K1_13_5_4_2_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem quotient_regular_iff {R : Type*} [CommRing R] (a b : R) :
    IsSMulRegular (QuotSMulTop a R) b ↔
      IsLeftRegular (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  let e : QuotSMulTop a R ≃ₗ[R] R ⧸ (Ideal.span {a} : Ideal R) :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
      change ((Ideal.span {a}).map (RingHom.id R) : Ideal R) = Ideal.span {a}
      rw [Ideal.map_id])
  exact e.isSMulRegular_congr b
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
private theorem graph_dimension (f : Row 3) (P : Ideal (GeoRow 3)) [P.IsPrime]
    (hs : genericRow (separant f) ∉ P) :
    (graphCurve f P).IsPrime ∧
      (affineHilbertPolynomial (graphCurve f P)).natDegree =
        (affineHilbertPolynomial P).natDegree := by
  let s := genericRow (separant f)
  let v : GeoRow 3 := -genericRow (lowerTangent f) * C ((3 : GeometricX)⁻¹)
  let L := Localization.Away (Ideal.Quotient.mk P s)
  let J := awayPresentationIdeal P s
  have hsA : Ideal.Quotient.mk P s ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hsreg : IsLeftRegular (Ideal.Quotient.mk P s) := fun _ _ h => mul_left_cancel₀ hsA h
  have : IsDomain L := IsLocalization.Away.isDomain L hsA
  have hJ : J.IsPrime := RingHom.ker_isPrime (awayPresentation P s)
  let coords : Fin 4 → MvPolynomial (Option (Fin 3)) GeometricX :=
    Fin.snoc (fun i => MvPolynomial.X (some i)) (rename some v * MvPolynomial.X none)
  let φ : GeoRow 4 →ₐ[GeometricX] MvPolynomial (Option (Fin 3)) GeometricX := aeval coords
  have hpoint (w : Option (Fin 3) → GeometricX) (hw : w ∈ zeroLocus GeometricX J) :
      (fun i => aeval w (coords i)) = graphPoint f (w ∘ some) := by
    have hrel := hw _ (X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal P s)
    rw [map_sub, map_mul, aeval_X, aeval_rename, map_one, sub_eq_zero] at hrel
    have hinv : w none = (aeval (w ∘ some) s)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [coords, graphPoint, Fin.snoc_last, map_mul, aeval_rename, aeval_X, hinv, v,
        map_neg, aeval_C, Algebra.algebraMap_self_apply, aeval_eq_eval, div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    · simp [coords, graphPoint, Function.comp_def]
  have himage : (fun w : Option (Fin 3) → GeometricX => graphPoint f (w ∘ some)) ''
        zeroLocus GeometricX J = graphLocus f P := by
    change (graphPoint f ∘ (fun w : Option (Fin 3) → GeometricX => w ∘ some)) ''
      zeroLocus GeometricX J = graphPoint f '' regularLocus f P
    rw [Set.image_comp]
    have hopen := image_comp_some_zeroLocus_awayPresentationIdeal (K := GeometricX) P s
    simpa only [regularLocus, aeval_eq_eval] using congrArg (Set.image (graphPoint f)) hopen
  have hcomap : graphCurve f P = J.comap φ := by
    ext p
    change p ∈ vanishingIdeal GeometricX (graphLocus f P) ↔ φ p ∈ J
    have hjp : φ p ∈ J ↔ φ p ∈ vanishingIdeal GeometricX (zeroLocus GeometricX J) := by
      rw [IsPrime.vanishingIdeal_zeroLocus J]
    rw [← himage, hjp]
    simp only [mem_vanishingIdeal_iff, Set.forall_mem_image]
    refine forall₂_congr fun w hw => ?_
    change aeval (graphPoint f (w ∘ some)) p = 0 ↔ aeval w (aeval coords p) = 0
    rw [comp_aeval_apply, hpoint w hw]
  have hrename : φ.comp (rename Fin.castSucc) = rename some := by
    apply algHom_ext
    intro i
    simp [φ, coords]
  have hback : (graphCurve f P).comap (rename Fin.castSucc) = P := by
    rw [hcomap]
    change J.comap (φ.comp (rename Fin.castSucc)) = P
    rw [hrename]
    ext p
    change rename some p ∈ awayPresentationIdeal P s ↔ p ∈ P
    rw [mem_awayPresentationIdeal, awayPresentation_rename_some,
      map_eq_zero_iff _ (IsLocalization.Away.algebraMap_injective_of_isLeftRegular hsreg),
      Ideal.Quotient.eq_zero_iff_mem]
  have hupper : (affineHilbertPolynomial (J.comap φ)).natDegree ≤
      (affineHilbertPolynomial J).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_injective (Ideal.quotientMapₐ J φ le_rfl)
      Ideal.quotientMap_injective
  have hlower : (affineHilbertPolynomial ((graphCurve f P).comap (rename Fin.castSucc))).natDegree ≤
      (affineHilbertPolynomial (graphCurve f P)).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_injective
      (Ideal.quotientMapₐ (graphCurve f P) (rename Fin.castSucc) le_rfl)
      Ideal.quotientMap_injective
  rw [hback] at hlower
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal hsreg, ← hcomap] at hupper
  refine ⟨?_, le_antisymm hupper hlower⟩
  rw [hcomap]
  exact hJ.comap φ
theorem proof : K1_13_5_4_2.c1 := by
  intro f hf _ P hP
  have hm := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let := hm.1.isPrime
  obtain ⟨hprime, hdim⟩ := graph_dimension f P hm.2
  refine ⟨hprime.comap lastMap, ?_⟩
  unfold sectionIdeal
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective lastMap
      (monomialMap_surjective lastExponents_single), hdim, retained_dimension hf hP]
end
end K1_13_5_4_2_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
open K1_13 K1_13_5_4_2
structure FirstBody (P : Set ExponentSpace) : Prop where
  polytope : ∃ v : Set ExponentSpace, v.Finite ∧ P = convexHull ℝ v
  zero_mem : 0 ∈ P
  zero_height : ∀ x ∈ P, x 3 = 0
def Chamber (s : Shape) : Prop := s.j ≤ s.b ∧ 2 * s.t ≤ s.j
noncomputable def boxVolume (s : Shape) (h : ℕ) : ℝ :=
  (h : ℝ) * (s.t : ℝ) * ((s.j : ℝ) - s.t) * ((s.b : ℝ) - (s.j : ℝ) / 2)
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5_4_2 MeasureTheory Set
private theorem volume_slices {α β : Type} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)]
    (e : β ≃ᵐ ℝ × α) (he : MeasurePreserving e) {C : Set β} (hC : MeasurableSet C)
    {d : ℝ} (hd : ∀ v ∈ C, (e v).1 ∈ Icc 0 d) :
    volume C = ∫⁻ t in Icc 0 d, volume ((fun v => e.symm (t, v)) ⁻¹' C) := by
  have hpre : MeasurableSet (e.symm ⁻¹' C) := hC.preimage e.symm.measurable
  rw [← (MeasurePreserving.symm e he).measure_preimage_equiv C, Measure.volume_eq_prod,
    Measure.prod_apply hpre, ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Icc 0 d
  · rw [indicator_of_mem ht]
    rfl
  · rw [indicator_of_notMem ht]
    have h : Prod.mk t ⁻¹' (e.symm ⁻¹' C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hv' := hd _ hv
      rw [e.apply_symm_apply] at hv'
      exact ht hv'
    rw [h, measure_empty]
private theorem lintegral_affine {a b d : ℝ} (hd : 0 ≤ d)
    (hn : ∀ x ∈ Icc 0 d, 0 ≤ a + b * x) :
    (∫⁻ x in Icc 0 d, ENNReal.ofReal (a + b * x)) = ENNReal.ofReal (d * a + b * d^2 / 2) := by
  have hi : IntegrableOn (fun x : ℝ => a + b * x) (Icc 0 d) :=
    (show Continuous (fun x : ℝ => a + b * x) by fun_prop).integrableOn_Icc
  have hnn : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 d), 0 ≤ a + b * x :=
    (ae_restrict_mem measurableSet_Icc).mono hn
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd,
    intervalIntegral.integral_add
      (show IntervalIntegrable (fun _ : ℝ => a) volume 0 d from intervalIntegrable_const)
      ((show Continuous (fun x : ℝ => b * x) by fun_prop).intervalIntegrable 0 d),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, smul_eq_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  ring
private abbrev splitLast {n : ℕ} : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)
private theorem splitLast_symm {n : ℕ} (t : ℝ) (v : Fin n → ℝ) :
    splitLast.symm (t, v) = Fin.snoc v t := by
  change @Fin.insertNth n (fun _ => ℝ) (Fin.last n) t v = @Fin.snoc n (fun _ => ℝ) v t
  exact Fin.insertNth_last' t v
private def triangle (d e : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x 1 ∈ Icc 0 e ∧ x 0 ∈ Icc 0 (d - x 1)}
private theorem volume_triangle {d e : ℝ} (he : 0 ≤ e) (hed : e ≤ d) :
    volume (triangle d e) = ENNReal.ofReal (e * d - e^2 / 2) := by
  let equiv : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.finTwoArrow (α := ℝ)).trans MeasurableEquiv.prodComm
  have hpres : MeasurePreserving equiv :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp
      (volume_preserving_finTwoArrow ℝ)
  have hm : MeasurableSet (triangle d e) := by
    have h0 : Measurable (fun x : Fin 2 → ℝ => x 0) := measurable_pi_apply 0
    have h1 : Measurable (fun x : Fin 2 → ℝ => x 1) := measurable_pi_apply 1
    exact (measurableSet_Icc.preimage h1).inter
      ((measurableSet_le measurable_const h0).inter (measurableSet_le h0 (by fun_prop)))
  rw [volume_slices equiv hpres hm (fun v hv => hv.1)]
  calc
    _ = ∫⁻ x in Icc 0 e, ENNReal.ofReal (d + (-1) * x) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hsec : (fun v : ℝ => equiv.symm (x, v)) ⁻¹' triangle d e = Icc 0 (d - x) := by
        ext y
        change (x ∈ Icc 0 e ∧ y ∈ Icc 0 (d - x)) ↔ _
        simp [hx]
      dsimp only
      rw [hsec, Real.volume_Icc]
      congr 1
      ring
    _ = _ := by
      rw [lintegral_affine he (fun x hx => by linarith [hx.2])]
      congr 1
      ring
private def oldCap (b j c : ℝ) : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 ≤ b ∧ x 1 + 2 * x 2 ≤ j ∧ x 2 ≤ c}
private theorem measurableSet_oldCap (b j c : ℝ) : MeasurableSet (oldCap b j c) := by
  have horth : MeasurableSet {x : Fin 3 → ℝ | ∀ i, 0 ≤ x i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hb : MeasurableSet {x : Fin 3 → ℝ | x 0 + x 1 + x 2 ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  have hj : MeasurableSet {x : Fin 3 → ℝ | x 1 + 2 * x 2 ≤ j} :=
    measurableSet_le (by fun_prop) measurable_const
  have ht : MeasurableSet {x : Fin 3 → ℝ | x 2 ≤ c} :=
    measurableSet_le (measurable_pi_apply 2) measurable_const
  exact horth.inter (hb.inter (hj.inter ht))
private theorem volume_oldCap {b j c : ℝ} (hc : 0 ≤ c) (hbj : j ≤ b) (hjc : 2 * c ≤ j) :
    volume (oldCap b j c) = ENNReal.ofReal (c * (j - c) * (b - j / 2)) := by
  have hbound (v : Fin 3 → ℝ) (hv : v ∈ oldCap b j c) : (splitLast v).1 ∈ Icc 0 c :=
    ⟨hv.1 2, hv.2.2.2⟩
  rw [volume_slices splitLast (volume_preserving_piFinSuccAbove _ _) (measurableSet_oldCap b j c) hbound]
  calc
    _ = ∫⁻ z in Icc 0 c, ENNReal.ofReal (j * (b - j / 2) + (-2 * (b - j / 2)) * z) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro z hz
      have hsec : (fun v : Fin 2 → ℝ => splitLast.symm (z, v)) ⁻¹' oldCap b j c =
          triangle (b - z) (j - 2 * z) := by
        ext v
        have h0 : (@Fin.snoc 2 (fun _ => ℝ) v z) 0 = v 0 :=
          @Fin.snoc_castSucc 2 (fun _ => ℝ) z v 0
        have h1 : (@Fin.snoc 2 (fun _ => ℝ) v z) 1 = v 1 :=
          @Fin.snoc_castSucc 2 (fun _ => ℝ) z v 1
        have h2 : (@Fin.snoc 2 (fun _ => ℝ) v z) 2 = z :=
          @Fin.snoc_last 2 (fun _ => ℝ) z v
        simp only [mem_preimage, splitLast_symm, oldCap, triangle, mem_ofPred_eq, mem_Icc,
          Fin.forall_iff_castSucc (n := 2), Fin.snoc_last, Fin.snoc_castSucc, Fin.forall_fin_two,
          h0, h1, h2]
        change ((0 ≤ z ∧ 0 ≤ v 0 ∧ 0 ≤ v 1) ∧ v 0 + v 1 + z ≤ b ∧
          v 1 + 2 * z ≤ j ∧ z ≤ c) ↔ ((0 ≤ v 1 ∧ v 1 ≤ j - 2 * z) ∧
          0 ≤ v 0 ∧ v 0 ≤ b - z - v 1)
        constructor
        · rintro ⟨⟨_, hv0, hv1⟩, hb', hj', _⟩
          exact ⟨⟨hv1, by linarith⟩, hv0, by linarith⟩
        · rintro ⟨⟨hv1, hj'⟩, hv0, hb'⟩
          exact ⟨⟨hz.1, hv0, hv1⟩, by linarith, by linarith, hz.2⟩
      dsimp only
      rw [hsec, volume_triangle (by linarith [hz.2]) (by linarith [hz.1])]
      congr 1
      ring
    _ = _ := by
      rw [lintegral_affine hc (fun z hz => by
        have h1 : 0 ≤ j - 2 * z := by linarith [hz.2]
        have h2 : 0 ≤ b - j / 2 := by linarith
        nlinarith [mul_nonneg h1 h2])]
      congr 1
      ring
theorem capBody_volume (s : Shape) (h : ℕ) (hs : Chamber s) :
    (volume (capBody s h)).toReal = boxVolume s h := by
  have hcap : capBody s h = {x | (fun i : Fin 3 => x i.castSucc) ∈ oldCap s.b s.j s.t ∧
      x 3 ∈ Icc 0 (h : ℝ)} := by
    ext x
    simp only [capBody, oldCap, mem_ofPred_eq, mem_Icc, Fin.forall_iff_castSucc (n := 3)]
    change ((0 ≤ x 3 ∧ ∀ i : Fin 3, 0 ≤ x i.castSucc) ∧
      x 0 + x 1 + x 2 ≤ (s.b : ℝ) ∧ x 1 + 2 * x 2 ≤ (s.j : ℝ) ∧
      x 2 ≤ (s.t : ℝ) ∧ x 3 ≤ (h : ℝ)) ↔
      ((∀ i : Fin 3, 0 ≤ x i.castSucc) ∧ x 0 + x 1 + x 2 ≤ (s.b : ℝ) ∧
      x 1 + 2 * x 2 ≤ (s.j : ℝ) ∧ x 2 ≤ (s.t : ℝ)) ∧ 0 ≤ x 3 ∧ x 3 ≤ (h : ℝ)
    tauto
  have hm : MeasurableSet (capBody s h) := by
    rw [hcap]
    exact ((measurableSet_oldCap _ _ _).preimage
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc))).inter
        (measurableSet_Icc.preimage (measurable_pi_apply 3))
  have hbound (v : ExponentSpace) (hv : v ∈ capBody s h) : (splitLast v).1 ∈ Icc 0 (h : ℝ) :=
    ⟨hv.1 3, hv.2.2.2.2⟩
  have hvol : volume (capBody s h) =
      volume (oldCap s.b s.j s.t) * ENNReal.ofReal (h : ℝ) := by
    rw [volume_slices splitLast (volume_preserving_piFinSuccAbove _ _) hm hbound]
    calc
      _ = ∫⁻ _ in Icc 0 (h : ℝ), volume (oldCap s.b s.j s.t) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro z hz
        dsimp only
        congr 1
        ext v
        have h3 : (@Fin.snoc 3 (fun _ => ℝ) v z) 3 = z :=
          @Fin.snoc_last 3 (fun _ => ℝ) z v
        simp [hcap, splitLast_symm, h3, hz.1, hz.2]
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  have hbj : (s.j : ℝ) ≤ s.b := by exact_mod_cast hs.1
  have hjc : 2 * (s.t : ℝ) ≤ s.j := by exact_mod_cast hs.2
  have hn : 0 ≤ (s.t : ℝ) * ((s.j : ℝ) - s.t) * ((s.b : ℝ) - (s.j : ℝ) / 2) := by
    have ht : 0 ≤ (s.t : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg ht (by linarith)) (by linarith)
  rw [hvol, volume_oldCap (by positivity) hbj hjc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal (by positivity)]
  unfold boxVolume
  ring
end
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i),
    (∀ j : Fin 4, ∃ i, Finsupp.single j 1 ∈ A i) →
    ∀ (i : Fin 4) (f : SlotRing A), f ∈ relationGenerators A (i.val + 1) →
      ∃ n : ℕ, constantChart A hz ^ n * f ∈ cutIdeal A (i.val + 1)
def c2 : Prop :=
  ∀ (A : Fin 4 → Finset Exponent) (hz : ∀ i, 0 ∈ A i) (i : Fin 4)
    (b : (j : Fin 4) → ↥(A j)) (f : SlotRing A) (n : ℕ),
    constantChart A hz ^ n * f ∈ cutIdeal A (i.val + 1) →
      ∃ m : ℕ, chartProduct A b ^ m * f ∈ cutIdeal A (i.val + 1)
private theorem weight_apply (A : Fin 4 → Finset Exponent) (e : Slot A →₀ ℕ) (i : Fin 4) :
    Finsupp.weight (slotWeight A) e i = ∑ a : ↥(A i), e ⟨i, a⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [slotWeight, Pi.smul_apply]
  · intro j _ hj
    simp [slotWeight, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj)]
  · simp
private theorem monomial_mul_mem (A : Fin 4 → Finset Exponent)
    (J : Ideal (SlotRing A)) (g : SlotRing A) (N : ℕ)
    (hkill : ∀ b : (i : Fin 4) → ↥(A i), chartProduct A b ^ N * g ∈ J)
    (e : Slot A →₀ ℕ) (c : CoefficientField A)
    (he : ∀ i, Fintype.card ↥(A i) * N < Finsupp.weight (slotWeight A) e i) :
    monomial e c * g ∈ J := by
  classical
  have hpick (i : Fin 4) : ∃ a : ↥(A i), N ≤ e ⟨i, a⟩ := by
    by_contra! h
    have hsum : (∑ a : ↥(A i), e ⟨i, a⟩) ≤ Fintype.card ↥(A i) * N := by
      calc
        _ ≤ ∑ _a : ↥(A i), N := Finset.sum_le_sum fun a _ => (h a).le
        _ = _ := by simp
    exact (not_le_of_gt (he i)) ((weight_apply A e i).trans_le hsum)
  choose b hb using hpick
  let v : Slot A →₀ ℕ := ∑ i : Fin 4, Finsupp.single ⟨i, b i⟩ N
  have hv : v ≤ e := by
    rintro ⟨i, a⟩
    rw [show v ⟨i, a⟩ = Finsupp.single (⟨i, b i⟩ : Slot A) N ⟨i, a⟩ by
      simp only [v, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_single i
      · intro j _ hj
        apply Finsupp.single_eq_of_ne
        intro h
        exact hj (congrArg Sigma.fst h).symm
      · simp]
    by_cases ha : b i = a
    · subst a
      simpa using hb i
    · simp [Ne.symm ha]
  have hchart : chartProduct A b ^ N = monomial v (1 : CoefficientField A) := by
    unfold chartProduct
    rw [← Finset.prod_pow]
    simp only [MvPolynomial.X_pow_eq_monomial, v, monomial_sum_one]
  have hfac : monomial e c * g = monomial (e - v) c * (chartProduct A b ^ N * g) := by
    rw [hchart, ← mul_assoc, monomial_mul_monomial, mul_one, add_comm (e - v),
      add_tsub_cancel_of_le hv]
  rw [hfac]
  exact J.mul_mem_left _ (hkill b)
private theorem homogeneous_mul_mem (A : Fin 4 → Finset Exponent)
    (J : Ideal (SlotRing A)) (g : SlotRing A) (N : ℕ)
    (hkill : ∀ b : (i : Fin 4) → ↥(A i), chartProduct A b ^ N * g ∈ J)
    {f : SlotRing A} {d : Degree} (hf : f ∈ slotPiece A d)
    (hd : ∀ i, Fintype.card ↥(A i) * N < d i) :
    f * g ∈ J := by
  classical
  rw [f.as_sum, Finset.sum_mul]
  exact J.sum_mem fun e he => monomial_mul_mem A J g N hkill e _ (by
    have hdeg := hf (mem_support_iff.mp he)
    intro i
    simpa only [hdeg] using hd i)
private theorem component_mul (A : Fin 4 → Finset Exponent) {g : SlotRing A} {e : Degree}
    (hg : g ∈ slotPiece A e) (f : SlotRing A) (d : Degree) :
    weightedHomogeneousComponent (slotWeight A) (d + e) (f * g) =
      weightedHomogeneousComponent (slotWeight A) d f * g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have ha := isWeightedHomogeneous_monomial (slotWeight A) a c rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight A) e := hg
    simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
      weightedHomogeneousComponent_of_mem ha, add_right_cancel_iff]
    split <;> simp_all
  | add p r hp hr => simp [add_mul, hp, hr]
private theorem high_degree_mem (A : Fin 4 → Finset Exponent) (k : ℕ) (J : Ideal (SlotRing A))
    (hlocal : ∀ g ∈ relationGenerators A k, ∀ b : (i : Fin 4) → ↥(A i),
      ∃ n : ℕ, chartProduct A b ^ n * g ∈ J) :
    ∃ q : ℕ, ∀ (d : Degree), (∀ i, q ≤ d i) →
      ∀ f ∈ slotPiece A d, f ∈ relationIdeal A k → f ∈ J := by
  classical
  obtain ⟨G, hG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := SlotRing A) (relationGenerators A k)).mp (IsNoetherian.noetherian _)
  have hspan' : relationIdeal A k = Ideal.span (↑G : Set (SlotRing A)) := hspan
  choose D hD using fun g : G => (hG g.property).1
  choose n hn using fun g : G => hlocal g (hG g.property)
  let N (g : G) := Finset.univ.sup (n g)
  have hN (g : G) (b : (i : Fin 4) → ↥(A i)) : chartProduct A b ^ N g * (g : SlotRing A) ∈ J := by
    have hle : n g b ≤ N g := Finset.le_sup (f := n g) (Finset.mem_univ b)
    have hpow : chartProduct A b ^ N g * (g : SlotRing A) =
        chartProduct A b ^ (N g - n g b) * (chartProduct A b ^ n g b * (g : SlotRing A)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    exact J.mul_mem_left _ (hn g b)
  let bound (g : G) (i : Fin 4) := D g i + Fintype.card ↥(A i) * N g + 1
  let q := Finset.univ.sup fun g : G => Finset.univ.sup (bound g)
  refine ⟨q, ?_⟩
  intro d hd f hf hrel
  rw [hspan'] at hrel
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hrel
  have hsum := congrArg (weightedHomogeneousComponent (slotWeight A) d) hc
  rw [map_sum, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ d from hf)]
    at hsum
  rw [← hsum]
  refine J.sum_mem fun g _ => ?_
  have hgd (i : Fin 4) : bound g i ≤ d i := by
    exact (Finset.le_sup (f := bound g) (Finset.mem_univ i)).trans
      ((Finset.le_sup (f := fun x : G => Finset.univ.sup (bound x)) (Finset.mem_univ g)).trans (hd i))
  have hdiff : ∀ i, Fintype.card ↥(A i) * N g < (d - D g) i := by
    intro i
    have hh := hgd i
    change D g i + Fintype.card ↥(A i) * N g + 1 ≤ d i at hh
    change _ < d i - D g i
    omega
  have heq : d - D g + D g = d := by
    funext i
    exact Nat.sub_add_cancel (by have hh := hgd i; dsimp [bound] at hh; omega)
  change weightedHomogeneousComponent (slotWeight A) d (c g * (g : SlotRing A)) ∈ J
  rw [← heq, component_mul A (hD g)]
  exact homogeneous_mul_mem A J g (N g) (hN g)
    (weightedHomogeneousComponent_mem _ _ _) hdiff
variable {A : Fin 4 → Finset Exponent}
private theorem relationIdeal_le (k : ℕ) :
    relationIdeal A k ≤ (prefixIdeal A k).comap (dehom A).toRingHom :=
  Ideal.span_le.mpr fun _ h => h.2
private theorem relationIdeal_homogeneous (k : ℕ) :
    (relationIdeal A k).IsHomogeneous (slotPiece A) :=
  Ideal.homogeneous_span _ _ fun _ h => h.1
private theorem prefix_mono {k l : ℕ} (h : k ≤ l) : prefixIdeal A k ≤ prefixIdeal A l :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
private theorem relation_mono {k l : ℕ} (h : k ≤ l) : relationIdeal A k ≤ relationIdeal A l :=
  Ideal.span_mono fun _ hf => ⟨hf.1, prefix_mono h hf.2⟩
private def nextIdeal (A : Fin 4 → Finset Exponent) (i : Fin 4) : Ideal (SlotRing A) :=
  relationIdeal A i.val ⊔ Ideal.span {homogeneousEquation A i}
private theorem cutIdeal_le_next (i : Fin 4) : cutIdeal A (i.val + 1) ≤ nextIdeal A i := by
  apply sup_le ((relation_mono (Nat.zero_le i.val)).trans le_sup_left)
  apply Ideal.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change j.val < i.val + 1 at hj
  by_cases hji : j = i
  · subst j
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  · have hlt : j.val < i.val := by
      have hn : j.val ≠ i.val := fun he => hji (Fin.ext he)
      omega
    apply Submodule.mem_sup_left
    apply Ideal.subset_span
    exact ⟨⟨_, homogeneousEquation_mem j⟩, by
      rw [dehom_equation]
      exact Ideal.subset_span ⟨j, hlt, rfl⟩⟩
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_4_2.c3 := by
  classical
  intro A hz hv
  have hlocal (i : Fin 4) (f : SlotRing A) (hf : f ∈ relationGenerators A (i.val + 1))
      (b : (j : Fin 4) → ↥(A j)) : ∃ n : ℕ, chartProduct A b ^ n * f ∈ nextIdeal A i := by
    obtain ⟨n, hn⟩ := h1 A hz hv i f hf
    obtain ⟨m, hm⟩ := h2 A hz i b f n hn
    exact ⟨m, cutIdeal_le_next i hm⟩
  choose q hq using fun i : Fin 4 => high_degree_mem A (i.val + 1) (nextIdeal A i) (hlocal i)
  refine ⟨Finset.univ.sup q, ?_⟩
  intro i d hd p hp hpI
  have hp' : p ∈ (slotPiece A (shift d i 1)).map (dehom A).toLinearMap := by
    rwa [map_slotPiece]
  obtain ⟨f, hf, hfp⟩ := hp'
  change dehom A f = p at hfp
  have hfI : f ∈ relationIdeal A (i.val + 1) :=
    Ideal.subset_span ⟨⟨_, hf⟩, hfp ▸ hpI⟩
  have hqd (j : Fin 4) : q i ≤ shift d i 1 j :=
    (Finset.le_sup (f := q) (Finset.mem_univ i)).trans
      ((hd j).trans (Nat.le_add_right _ _))
  have hJ := hq i _ hqd f hf hfI
  change f ∈ relationIdeal A i.val ⊔ Ideal.span {homogeneousEquation A i} at hJ
  rw [sup_comm] at hJ
  obtain ⟨m, g, hg, hsum⟩ := Ideal.mem_span_singleton_sup.mp hJ
  let r := weightedHomogeneousComponent (slotWeight A) d m
  let s := weightedHomogeneousComponent (slotWeight A) (shift d i 1) g
  have hs : s ∈ relationIdeal A i.val :=
    weightedHomogeneousComponent_mem_of_mem _ _ (relationIdeal_homogeneous i.val) hg _
  have hfg : r * homogeneousEquation A i + s = f := by
    have he := congrArg (weightedHomogeneousComponent (slotWeight A) (shift d i 1)) hsum
    rw [map_add, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ _ from hf)]
      at he
    change weightedHomogeneousComponent (slotWeight A) (d + Pi.single i 1)
      (m * homogeneousEquation A i) + s = f at he
    rwa [component_mul A (homogeneousEquation_mem i)] at he
  have hsI : dehom A s ∈ prefixIdeal A i.val := relationIdeal_le i.val hs
  refine ⟨dehom A r, ?_, ?_⟩
  · rw [← map_slotPiece]
    exact ⟨r, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  · have he := congrArg (dehom A) hfg
    rw [map_add, map_mul, dehom_equation, hfp] at he
    rw [← he, mul_comm (genericEquation A i), add_sub_cancel_left]
    exact hsI
end
end K1_13_5_4_2_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4 MvPolynomial
abbrev Affine (L : Type) [CommRing L] := MvPolynomial (Fin 4) L
def equationsIdeal {L : Type} [CommRing L] (f : Fin 4 → Affine L) :
    Ideal (Affine L) :=
  Ideal.span (Set.range f)
abbrev Total (L : Type) [Field L] := Affine (Polynomial L)
abbrev ParameterField (L : Type) [Field L] := FractionRing (Polynomial L)
def reduce {L : Type} [Field L] : Total L →+* Affine L :=
  MvPolynomial.map (Polynomial.evalRingHom 0)
def toGeneric {L : Type} [Field L] : Total L →+* Affine (ParameterField L) :=
  MvPolynomial.map (algebraMap (Polynomial L) (ParameterField L))
abbrev GenericFiber {L : Type} [Field L] (g : Fin 4 → Total L) :=
  Affine (ParameterField L) ⧸ (equationsIdeal g).map toGeneric
def genericClass {L : Type} [Field L] (g : Fin 4 → Total L) :
    Total L →+* GenericFiber g :=
  (Ideal.Quotient.mk _).comp toGeneric
abbrev rationalIdeal {L : Type} [Field L] (y : Fin 4 → L) : Ideal (Affine L) :=
  vanishingIdeal L {y}
abbrev PointLocal {L : Type} [Field L] (y : Fin 4 → L) :=
  Localization.AtPrime (rationalIdeal y)
abbrev PointAlgebra {L : Type} [Field L] (I : Ideal (Affine L)) (y : Fin 4 → L) :=
  PointLocal y ⧸ I.map (algebraMap (Affine L) (PointLocal y))
def pointClass {L : Type} [Field L] (I : Ideal (Affine L)) (y : Fin 4 → L) :
    Affine L →ₐ[L] PointAlgebra I y :=
  (Ideal.Quotient.mkₐ L _).comp (IsScalarTower.toAlgHom L (Affine L) (PointLocal y))
abbrev totalPrime {L : Type} [Field L] (y : Fin 4 → L) : Ideal (Total L) :=
  (rationalIdeal y).comap reduce
instance totalPrime_isPrime {L : Type} [Field L] (y : Fin 4 → L) :
    (totalPrime y).IsPrime :=
  Ideal.IsPrime.comap reduce
abbrev TotalLocal {L : Type} [Field L] (y : Fin 4 → L) :=
  Localization.AtPrime (totalPrime y)
abbrev BranchAlgebra {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :=
  TotalLocal y ⧸ (equationsIdeal g).map (algebraMap (Total L) (TotalLocal y))
def branchClass {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :
    Total L →+* BranchAlgebra g y :=
  (Ideal.Quotient.mk _).comp (algebraMap (Total L) (TotalLocal y))
def branchParameter {L : Type} [Field L] (g : Fin 4 → Total L) (y : Fin 4 → L) :
    BranchAlgebra g y :=
  branchClass g y (MvPolynomial.C Polynomial.X)
def extendPoint (L : Type) [Field L] [Algebra GeometricX L] (y : JetPoint) : Fin 4 → L :=
  fun i => algebraMap GeometricX L (y i)
def extendIdeal (L : Type) [Field L] [Algebra GeometricX L]
    (I : Ideal (GeoRow 4)) : Ideal (Affine L) :=
  I.map (MvPolynomial.map (algebraMap GeometricX L))
end
end K1_13_5_4_2_4_1
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def liftRaw : Row 3 →ₐ[Geom[X]] Row 4 := MvPolynomial.rename Fin.castSucc
abbrev liftSep (f : Row 3) : Row 4 := liftRaw (K1_13_5.separant f)
def graphRaw (f : Row 3) : Row 4 :=
  liftRaw (lowerTangent f) + 3 * MvPolynomial.X 3 * liftSep f
def thirdVelocityNumerator (f : Row 3) : Row 4 :=
  MvPolynomial.C (Polynomial.C (-(3 : Geom)⁻¹)) * K1_13_6.partialFlow (graphRaw f)
def liftedStep (f : Row 3) (a : ℕ) (b : Row 4) : Row 4 :=
  liftSep f * K1_13_6.partialFlow b + thirdVelocityNumerator f * MvPolynomial.pderiv 3 b -
    (a : Row 4) * K1_13_6.partialFlow (liftSep f) * b
def thirdNumerator (f : Row 3) : ℕ → Row 4
  | 0 => MvPolynomial.X 3
  | k + 1 => liftedStep f k (thirdNumerator f k)
def thirdScale : ℕ → Geom
  | 0 => 1
  | k + 1 => thirdScale k * ((k + 4 : ℕ) : Geom)⁻¹
def jetNumerator (f : Row 3) (j : ℕ) : Row 4 :=
  if h : j < 3 then
    MvPolynomial.X ⟨j, h.trans (by decide : 3 < 4)⟩
  else
    MvPolynomial.C (Polynomial.C (thirdScale (j - 3))) *
      thirdNumerator f (j - 3)
def padJet (f : Row 3) (d j : ℕ) : Row 4 :=
  liftSep f ^ (d - (j - 3)) * jetNumerator f j
def paddedJet (f : Row 3) (j : Fin taylorLength) : Row 4 :=
  padJet f (taylorLength - 4) j.val
def centre : GeometricX := genericCoeff Polynomial.X
def coefficientNumerator (f : Row 3) (i : Fin taylorLength) : GeoRow 4 :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C (((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val) *
      genericRow (paddedJet f j)
def cut (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (taylorLength - 3))
def next (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (taylorLength - 2))
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_5_4_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) →
    SimpleInvariant f P → TangentStable f P
def c2 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    TrueWeightLE f (90 * 180265 - 1) → P.IsPrime →
    oldCutIdeal f ≤ P → genericRow (separant f) ∉ P → TangentStable f P →
    ∀ y ∈ regularLocus f P, extendedAtJet f (taylorAt f (pointEval y)) = 0
def c3 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    Irreducible f → 0 < f.degreeOf 2 → ¬ Whole f →
    P ∈ (oldCutIdeal f).retainedMinimalPrimes (genericRow (separant f)) →
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1
def c4 : Prop :=
  ∀ (f : Row 3) (P : Ideal (GeoRow 3)),
    P.IsPrime → genericRow (separant f) ∉ P →
    (MvPolynomial.affineHilbertPolynomial P).natDegree = 1 →
    (curveIdeal f P).IsPrime ∧ (MvPolynomial.affineHilbertPolynomial (curveIdeal f P)).natDegree = 1
private theorem component_data {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} (ha : (i, P) ∈ properComponents f) :
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes
      (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
  obtain ⟨k, hk⟩ := ha
  by_cases hw : Whole (f k)
  · simp [hw] at hk
  · simp only [hw, ite_false] at hk
    obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
    cases he
    exact ⟨hw, hP'⟩
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_13_5_4.c3 := by
  intro n f hf a ha hs
  rcases a with ⟨i, P⟩
  obtain ⟨hw, hc⟩ := component_data ha
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp hc
  have hp : P.IsPrime := hmin.1.1
  have hle : oldCutIdeal (f i) ≤ P := hmin.1.2
  have hstable := h1 (f i) P hc hs
  have hsol := h2 (f i) P (hf.weight i) hp hle hsep hstable
  have hdim := h3 (f i) P (hf.irreducible i) (hf.positive i) hw hc
  obtain ⟨hprime, hcurve⟩ := h4 (f i) P hp hsep hdim
  obtain ⟨y, hy⟩ := regularLocus_nonempty (f i) P hp hsep
  refine ⟨curveIdeal (f i) P, ⟨hprime, hcurve, solves_on_closure _ _ hsol, ?_⟩, ?_⟩
  · refine ⟨reconstructAt (f i) y, pointImage_in_zeroLocus _ _ hy, ?_⟩
    intro hzero
    apply hy.2
    rw [← eval_trajectory_at_centre (f i), ← coefficientPolynomial_reconstructAt,
      hzero, Polynomial.eval_zero]
  · intro S hS hyS
    have hfP : genericRow (f i) ∈ P := hle (Ideal.subset_span (by simp))
    have he : MvPolynomial.eval (jetPoint S) (genericRow (f i)) = 0 := hyS.1 _ hfP
    have hn : MvPolynomial.eval (jetPoint S) (genericRow (separant (f i))) ≠ 0 := hyS.2
    rw [eval_genericRow_at_point] at he hn
    have hr : RegularAt 2 (f i) S := by
      refine ⟨genericCoeff_injective (he.trans genericCoeff.map_zero.symm), ?_⟩
      intro h
      exact hn (by rw [show atJet (separant (f i)) S = 0 from h, map_zero])
    rw [← reconstructAt_mark (f i) S hS hr]
    exact pointImage_in_zeroLocus _ _ hyS
end
end K1_13_5_4_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped BigOperators Pointwise
theorem firstBody_zero : FirstBody (0 : Set ExponentSpace) := by
  refine ⟨⟨0, Set.finite_zero, convexHull_zero.symm⟩, by simp, ?_⟩
  intro x hx
  rw [Set.mem_zero] at hx
  simp [hx]
theorem FirstBody.add {P Q : Set ExponentSpace} (hP : FirstBody P) (hQ : FirstBody Q) :
    FirstBody (P + Q) := by
  obtain ⟨v, hv, hvP⟩ := hP.polytope
  obtain ⟨w, hw, hwQ⟩ := hQ.polytope
  refine ⟨⟨v + w, hv.add hw, by rw [hvP, hwQ, convexHull_add]⟩, ?_, ?_⟩
  · exact Set.mem_add.mpr ⟨0, hP.zero_mem, 0, hQ.zero_mem, zero_add 0⟩
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    simp [Pi.add_apply, hP.zero_height y hy, hQ.zero_height z hz]
theorem capBody_convex (s : Shape) (h : ℕ) : Convex ℝ (capBody s h) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx, hxb, hxj, hxt, hxh⟩ := hx
  obtain ⟨hy, hyb, hyj, hyt, hyh⟩ := hy
  simp only [capBody, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)), ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hxb ha, mul_le_mul_of_nonneg_left hyb hb,
      congrArg (fun r : ℝ => r * (s.b : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxj ha, mul_le_mul_of_nonneg_left hyj hb,
      congrArg (fun r : ℝ => r * (s.j : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxt ha, mul_le_mul_of_nonneg_left hyt hb,
      congrArg (fun r : ℝ => r * (s.t : ℝ)) hab]
  · nlinarith [mul_le_mul_of_nonneg_left hxh ha, mul_le_mul_of_nonneg_left hyh hb,
      congrArg (fun r : ℝ => r * (h : ℝ)) hab]
private theorem downBody_polytope (F : GeoRow 4) :
    ∃ v : Set ExponentSpace, v.Finite ∧ downBody F = convexHull ℝ v := by
  let corners (a : ↥F.support) : Set ExponentSpace :=
    Set.univ.pi (fun j => ({0, (a.val j : ℝ)} : Set ℝ))
  let v := ⋃ a, corners a
  refine ⟨v, Set.finite_iUnion (fun a => Set.Finite.pi (fun j => by simp)), ?_⟩
  have hc (a : ↥F.support) : convexHull ℝ (corners a) =
      {x : ExponentSpace | ∀ j, 0 ≤ x j ∧ x j ≤ (a.val j : ℝ)} := by
    dsimp only [corners]
    rw [convexHull_pi]
    have hseg (j : Fin 4) : convexHull ℝ ({0, (a.val j : ℝ)} : Set ℝ) =
        Set.Icc 0 (a.val j : ℝ) := by
      rw [convexHull_pair, segment_eq_Icc (by positivity)]
    simp only [hseg, Set.pi_univ_Icc]
    ext x
    exact forall_and.symm
  unfold downBody
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull _ _)
    rintro x ⟨a, ha, hx⟩
    have hx' : x ∈ convexHull ℝ (corners ⟨a, ha⟩) := by rwa [hc]
    exact convexHull_mono (Set.subset_iUnion corners ⟨a, ha⟩) hx'
  · apply convexHull_mono
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    have hx' : x ∈ convexHull ℝ (corners a) := subset_convexHull ℝ _ ha
    rw [hc] at hx'
    exact ⟨a.val, a.property, hx'⟩
private def rowShape (f : Row 3) : Shape := ⟨f.totalDegree, indexDegree f, f.degreeOf 2⟩
private theorem row_support (f : Row 3) :
    InLiftedBox (liftRow (genericRow f)) (rowShape f) 0 := by
  classical
  intro a ha
  rw [liftRow, support_rename_of_injective (Fin.castSucc_injective 3)] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hb' : b ∈ f.support := support_map_subset _ _ hb
  have htotal : b.degree ≤ f.totalDegree := le_totalDegree hb'
  have hindex : b.sum (fun j a => j.val * a) ≤ indexDegree f :=
    Finset.le_sup (f := fun m => m.sum (fun j a => j.val * a)) hb'
  have htop := monomial_le_degreeOf 2 hb'
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at htotal
  rw [Finsupp.sum_fintype _ _ (fun j => mul_zero j.val), Fin.sum_univ_three] at hindex
  have h0 : Finsupp.mapDomain Fin.castSucc b 0 = b 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 0
  have h1 : Finsupp.mapDomain Fin.castSucc b 1 = b 1 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 1
  have h2 : Finsupp.mapDomain Fin.castSucc b 2 = b 2 :=
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 3) b 2
  have h3 : Finsupp.mapDomain Fin.castSucc b 3 = 0 :=
    Finsupp.mapDomain_of_notMem_range b _ (fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj)
  simp only [h0, h1, h2, h3, rowShape, le_refl, and_true]
  exact ⟨htotal, by simpa using hindex, htop⟩
private theorem downBody_subset {F : GeoRow 4} {s : Shape} {h : ℕ}
    (hs : InLiftedBox F s h) : downBody F ⊆ capBody s h := by
  apply convexHull_min _ (capBody_convex s h)
  rintro x ⟨a, ha, hx⟩
  obtain ⟨hb, hj, ht, hh⟩ := hs a ha
  have hb' : (a 0 : ℝ) + a 1 + a 2 ≤ s.b := by exact_mod_cast hb
  have hj' : (a 1 : ℝ) + 2 * a 2 ≤ s.j := by exact_mod_cast hj
  exact ⟨fun j => (hx j).1, by linarith [(hx 0).2, (hx 1).2, (hx 2).2],
    by linarith [(hx 1).2, (hx 2).2], (hx 2).2.trans (by exact_mod_cast ht),
    (hx 3).2.trans (by exact_mod_cast hh)⟩
theorem firstBody_row {f : Row 3} (hf : f ≠ 0) : FirstBody (downBody (liftRow (genericRow f))) := by
  have hg : genericRow f ≠ 0 := by
    simpa only [genericRow, map_zero] using (map_injective _ genericCoeff_injective).ne hf
  have hF : liftRow (genericRow f) ≠ 0 := by
    simpa only [liftRow, map_zero] using
      (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hg
  obtain ⟨a, ha⟩ := support_nonempty.mpr hF
  refine ⟨downBody_polytope _, subset_convexHull ℝ _ ⟨a, ha, fun _ => ⟨le_rfl, by positivity⟩⟩, ?_⟩
  intro x hx
  have hc := downBody_subset (row_support f) hx
  exact le_antisymm (by simpa using hc.2.2.2.2) (hc.1 3)
theorem sum_downBody_subset {n : ℕ} (f : Fin n → Row 3) (hf : SecondFactors f) :
    (∑ i, downBody (liftRow (genericRow (f i)))) ⊆ capBody lowBox 0 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Set.mem_fintype_sum _ _ |>.mp hx
  have hb (i : Fin n) : y i ∈ capBody (rowShape (f i)) 0 :=
    downBody_subset (row_support (f i)) (hy i)
  simp only [capBody, Set.mem_ofPred_eq, Finset.sum_apply]
  refine ⟨fun j => Finset.sum_nonneg (fun i _ => (hb i).1 j), ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply le_trans (Finset.sum_le_sum (fun i _ => (hb i).2.1))
    simpa only [rowShape, ← Nat.cast_sum] using (show
      (↑(∑ i, (f i).totalDegree) : ℝ) ≤ (lowBox.b : ℝ) by exact_mod_cast hf.total)
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply le_trans (Finset.sum_le_sum (fun i _ => (hb i).2.2.1))
    simpa only [rowShape, ← Nat.cast_sum] using (show
      (↑(∑ i, indexDegree (f i)) : ℝ) ≤ (lowBox.j : ℝ) by exact_mod_cast hf.index)
  · apply le_trans (Finset.sum_le_sum (fun i _ => (hb i).2.2.2.1))
    simpa only [rowShape, ← Nat.cast_sum] using (show
      (↑(∑ i, (f i).degreeOf 2) : ℝ) ≤ (lowBox.t : ℝ) by exact_mod_cast hf.top)
  · rw [Nat.cast_zero]
    exact Finset.sum_nonpos (fun i _ => by simpa using (hb i).2.2.2.2)
end
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 MeasureTheory
open scoped BigOperators Pointwise
private theorem split_cap {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ≤ A + B) : ∃ y, 0 ≤ y ∧ y ≤ A ∧ 0 ≤ x - y ∧ x - y ≤ B := by
  refine ⟨min x A, le_min hx hA, min_le_right _ _, sub_nonneg.mpr (min_le_left _ _), ?_⟩
  rcases le_total x A with hle | hle
  · simpa only [min_eq_left hle, sub_self] using hB
  · rw [min_eq_right hle]
    linarith
private theorem capBody_zero : capBody ⟨0, 0, 0⟩ 0 = 0 := by
  ext x
  rw [Set.mem_zero]
  constructor
  · intro hx
    obtain ⟨hx, hb, _, _, hh⟩ := hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    norm_num at hb hh
    funext i
    change x i = 0
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
    · change x 2 = 0
      linarith
    · change x 3 = 0
      linarith
  · rintro rfl
    simp [capBody]
private theorem capBody_split {p q : Shape} (hp : Chamber p) (hq : Chamber q)
    {h k : ℕ} {x : ExponentSpace} (hx : x ∈ capBody (p.plus q) (h + k)) :
    x ∈ capBody p h + capBody q k := by
  obtain ⟨hx, hb, hj, ht, hh⟩ := hx
  simp only [Shape.plus, Nat.cast_add] at hb hj ht hh
  have hpj : (p.j : ℝ) ≤ p.b := by exact_mod_cast hp.1
  have hqj : (q.j : ℝ) ≤ q.b := by exact_mod_cast hq.1
  have hpt : 2 * (p.t : ℝ) ≤ p.j := by exact_mod_cast hp.2
  have hqt : 2 * (q.t : ℝ) ≤ q.j := by exact_mod_cast hq.2
  obtain ⟨z, hz, hzp, hz', hzq⟩ := split_cap (hx 2) (by positivity) (by positivity) ht
  obtain ⟨v, hv, hvp, hv', hvq⟩ := split_cap (hx 1)
    (show 0 ≤ (p.j : ℝ) - 2 * z by linarith)
    (show 0 ≤ (q.j : ℝ) - 2 * (x 2 - z) by linarith) (by linarith)
  obtain ⟨u, hu, hup, hu', huq⟩ := split_cap (hx 0)
    (show 0 ≤ (p.b : ℝ) - v - z by linarith)
    (show 0 ≤ (q.b : ℝ) - (x 1 - v) - (x 2 - z) by linarith) (by linarith)
  obtain ⟨w, hw, hwp, hw', hwq⟩ := split_cap (hx 3) (by positivity) (by positivity) hh
  let y : ExponentSpace := ![u, v, z, w]
  have hy : y ∈ capBody p h := by
    refine ⟨?_, ?_, ?_, hzp, hwp⟩
    · intro i
      fin_cases i <;> assumption
    · change u + v + z ≤ (p.b : ℝ)
      linarith
    · change v + 2 * z ≤ (p.j : ℝ)
      linarith
  have hy' : x - y ∈ capBody q k := by
    refine ⟨?_, ?_, ?_, hzq, hwq⟩
    · intro i
      fin_cases i <;> assumption
    · change (x 0 - u) + (x 1 - v) + (x 2 - z) ≤ (q.b : ℝ)
      linarith
    · change (x 1 - v) + 2 * (x 2 - z) ≤ (q.j : ℝ)
      linarith
  exact Set.mem_add.mpr ⟨y, hy, x - y, hy', by abel⟩
theorem capBody_add {p q : Shape} (hp : Chamber p) (hq : Chamber q) (h k : ℕ) :
    capBody (p.plus q) (h + k) = capBody p h + capBody q k := by
  apply Set.Subset.antisymm (fun _ hx => capBody_split hp hq hx)
  intro x hx
  obtain ⟨y, ⟨hy, hyb, hyj, hyt, hyh⟩, z, ⟨hz, hzb, hzj, hzt, hzh⟩, rfl⟩ := Set.mem_add.mp hx
  refine ⟨fun i => add_nonneg (hy i) (hz i), ?_, ?_, ?_, ?_⟩ <;>
    simp only [Pi.add_apply, Shape.plus, Nat.cast_add] <;> linarith
private def sumShape {ι : Type} (S : Finset ι) (p : ι → Shape) : Shape :=
  ⟨∑ i ∈ S, (p i).b, ∑ i ∈ S, (p i).j, ∑ i ∈ S, (p i).t⟩
private theorem sumChamber {ι : Type} (S : Finset ι) (p : ι → Shape)
    (hp : ∀ i, Chamber (p i)) : Chamber (sumShape S p) := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => (hp i).1)
  · change 2 * (∑ i ∈ S, (p i).t) ≤ ∑ i ∈ S, (p i).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hp i).2)
private theorem sum_capBody {ι : Type} (S : Finset ι) (p : ι → Shape)
    (h : ι → ℕ) (hp : ∀ i, Chamber (p i)) :
    (∑ i ∈ S, capBody (p i) (h i)) = capBody (sumShape S p) (∑ i ∈ S, h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sumShape, Finset.sum_empty, capBody_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, ih, ← capBody_add (hp i) (sumChamber S p hp)]
    simp only [sumShape, Shape.plus, Finset.sum_insert hi]
private def slotShapes : Fin 4 → Shape :=
  ![lowBox, graphBox, liftedBox (taylorLength + 1), lastBox]
private def slotHeights : Fin 4 → ℕ := ![0, 1, taylorLength - 1, taylorLength]
private theorem slotChamber (i : Fin 4) : Chamber (slotShapes i) := by
  fin_cases i <;> exact (show _ ∧ _ from ⟨by decide, by decide⟩)
private theorem native_polarization :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ (4 - S.card) *
      boxVolume (sumShape S slotShapes) (∑ i ∈ S, slotHeights i)) = (mixedBudget : ℝ) := by
  have hu : (Finset.univ : Finset (Fin 4)) = insert 0 (insert 1 (insert 2 (insert 3 ∅))) := by decide
  rw [hu]
  simp only [
    Finset.sum_powerset_insert (a := (0 : Fin 4)) (s := insert 1 (insert 2 (insert 3 ∅))) (by decide),
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [boxVolume, sumShape, slotShapes, slotHeights, mixedBudget, mixed3, volumeTerm,
    liftedBox, taylorLength, Finset.sum_insert, Finset.card_insert_of_notMem]
theorem native_box_price
    (hvol : ∀ (s : Shape) (h : ℕ), Chamber s → (volume (capBody s h)).toReal = boxVolume s h) :
    lastMixedVolume (capBody lowBox 0) = (mixedBudget : ℝ) := by
  change (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ (4 - S.card) *
    (volume (∑ i ∈ S, capBody (slotShapes i) (slotHeights i))).toReal) = _
  simp_rw [sum_capBody _ _ _ slotChamber, hvol _ _ (sumChamber _ _ slotChamber)]
  exact native_polarization
end
end K1_13_5_4_2_5
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 Polynomial MvPolynomial
open K1_13_6 (coefficientDerivative partialFlow flowNumerator eval_flowNumerator)
private theorem coeff_coeffDerivative {r : ℕ} (P : Row r) (m : Fin r →₀ ℕ) :
    (coeffDerivative P).coeff m = (P.coeff m).derivative := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
private theorem coefficientDerivative_lift (P : Row 3) :
    coefficientDerivative (liftRaw P) = liftRaw (coeffDerivative P) := by
  apply MvPolynomial.ext
  intro m
  change (coeffDerivative (liftRaw P)).coeff m = _
  rw [coeff_coeffDerivative]
  change ((rename Fin.castSucc P).coeff m).derivative =
    (rename Fin.castSucc (coeffDerivative P)).coeff m
  by_cases h : ∃ u : Fin 3 →₀ ℕ, u.mapDomain Fin.castSucc = m
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain _ (Fin.castSucc_injective 3), coeff_rename_mapDomain _ (Fin.castSucc_injective 3),
      coeff_coeffDerivative]
  · rw [coeff_rename_eq_zero _ _ _ (fun u hu => (h ⟨u, hu⟩).elim),
      coeff_rename_eq_zero _ _ _ (fun u hu => (h ⟨u, hu⟩).elim), map_zero]
theorem pderiv_last_lift (P : Row 3) : pderiv 3 (liftRaw P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [liftRaw]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i h =>
    have hi : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
    rw [map_mul, show liftRaw (MvPolynomial.X i) = MvPolynomial.X i.castSucc from rename_X _ _,
      pderiv_mul, h, pderiv_X_of_ne hi, zero_mul, mul_zero, zero_add]
theorem partialFlow_lift (P : Row 3) : partialFlow (liftRaw P) = graphRaw P := by
  unfold partialFlow graphRaw lowerTangent
  rw [coefficientDerivative_lift, Fin.sum_univ_three]
  have hs (i : Fin 3) : pderiv i.castSucc (liftRaw P) = liftRaw (pderiv i P) :=
    pderiv_rename (Fin.castSucc_injective 3) i P
  have hx (i : Fin 3) : liftRaw (MvPolynomial.X i) = MvPolynomial.X i.castSucc := rename_X _ _
  have hc (a : ℕ) : MvPolynomial.C (Polynomial.C (a : Geom)) = (a : Row 4) := by
    rw [C_eq_natCast, map_natCast]
  simp only [hs, hx, hc, map_add, map_mul, map_ofNat]
  change _ = liftRaw (coeffDerivative P) + MvPolynomial.X 1 * liftRaw (pderiv 0 P) +
      2 * MvPolynomial.X 2 * liftRaw (pderiv 1 P) + 3 * MvPolynomial.X 3 * liftRaw (pderiv 2 P)
  norm_num [Fin.val_succ, Fin.val_zero]
  ring
theorem graph_separant (f : Row 3) : K1_13_6.separant (graphRaw f) = 3 * liftSep f := by
  have h3 : pderiv 3 (3 : Row 4) = 0 := (pderiv (R := Geom[X]) (3 : Fin 4)).map_natCast 3
  simp [K1_13_6.separant, graphRaw, pderiv_last_lift, h3, mul_comm]
theorem geomCast_ne_zero {a : ℕ} (ha : 0 < a) (hp : a < K1.p) : (a : Geom) ≠ 0 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro hz
  exact (not_le_of_gt hp) (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff Geom K1.p a).mp hz))
private theorem three_ne_zero : (3 : Geom[X]) ≠ 0 := by
  have h := geomCast_ne_zero (a := 3) (by decide) (by decide)
  exact Polynomial.C_ne_zero.mpr h
@[simp] theorem atJet_lift (P : Row 3) (S : Geom[X]) : atJet (liftRaw P) S = atJet P S :=
  eval_rename _ _ _
theorem derivative_atJet (P : Row 3) (S : Geom[X]) :
    derivative (atJet P S) = atJet (graphRaw P) S := by
  let g : Row 4 := MvPolynomial.X 3 - MvPolynomial.C (jet S (3 : Fin 4))
  have hg : atJet g S = 0 := by simp [atJet, g]
  have hsep : K1_13_6.separant g = 1 := by
    simp [K1_13_6.separant, g]
  have h := eval_flowNumerator g (liftRaw P) S hg
  unfold flowNumerator at h
  rw [hsep, show K1_13_6.separant (liftRaw P) = 0 from pderiv_last_lift P,
    mul_zero, sub_zero, one_mul, partialFlow_lift, atJet_lift,
    show atJet (1 : Row 4) S = 1 by exact map_one _, one_mul] at h
  exact h.symm
theorem graph_atJet_zero {f : Row 3} {S : Geom[X]} (h : atJet f S = 0) :
    atJet (graphRaw f) S = 0 := by
  rw [← derivative_atJet, h, map_zero]
private theorem three_mul_velocity (f : Row 3) :
    3 * thirdVelocityNumerator f = -partialFlow (graphRaw f) := by
  let c : Geom →+* Row 4 := (MvPolynomial.C : Geom[X] →+* Row 4).comp Polynomial.C
  have h : (3 : Geom) * -(3 : Geom)⁻¹ = -1 := by
    have hn : (3 : Geom) ≠ 0 := geomCast_ne_zero (a := 3) (by decide) (by decide)
    rw [mul_neg, mul_inv_cancel₀ hn]
  change c 3 * (c (-(3 : Geom)⁻¹) * _) = _
  rw [← mul_assoc, ← map_mul, h, map_neg, map_one]
  ring
private theorem atJet_liftedFlow (f : Row 3) (b : Row 4) (S : Geom[X])
    (hf : atJet f S = 0) :
    atJet (liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b) S =
      atJet (liftSep f) S * derivative (atJet b S) := by
  have hpoly : flowNumerator (graphRaw f) b =
      3 * (liftSep f * partialFlow b + thirdVelocityNumerator f * pderiv 3 b) := by
    rw [flowNumerator, graph_separant, K1_13_6.separant, mul_add, ← mul_assoc, ← mul_assoc,
      three_mul_velocity]
    ring
  have h := eval_flowNumerator (graphRaw f) b S (graph_atJet_zero hf)
  rw [hpoly, graph_separant] at h
  let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
  change e (3 * _) = e (3 * _) * _ at h
  rw [map_mul, map_mul, map_ofNat, mul_assoc] at h
  exact mul_left_cancel₀ three_ne_zero h
private theorem atJet_partialFlow_sep (f : Row 3) (S : Geom[X]) :
    atJet (partialFlow (liftSep f)) S = derivative (atJet (liftSep f) S) := by
  rw [partialFlow_lift, ← derivative_atJet, atJet_lift]
private theorem clear_one_derivative (a : ℕ) (u v : Geom[X]) :
    u * derivative (u ^ a * v) - (a : Geom[X]) * derivative u * (u ^ a * v) =
      u ^ (a + 1) * derivative v := by
  cases a with
  | zero => simp
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one, pow_succ u (a+1)]
    simp only [C_eq_natCast]
    push_cast
    rw [pow_succ u a]
    ring
theorem atJet_thirdNumerator (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0) (k : ℕ) :
    atJet (thirdNumerator f k) S = atJet (liftSep f) S ^ k *
      ((derivative (R := Geom))^[k]) (jet S (3 : Fin 4)) := by
  induction k with
  | zero => simp [thirdNumerator, atJet]
  | succ k ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
    change e (liftedStep f k (thirdNumerator f k)) = _
    unfold liftedStep
    rw [map_sub, map_mul, map_mul, map_natCast]
    change atJet (liftSep f * partialFlow (thirdNumerator f k) +
        thirdVelocityNumerator f * pderiv 3 (thirdNumerator f k)) S -
        (k : Geom[X]) * atJet (partialFlow (liftSep f)) S * atJet (thirdNumerator f k) S = _
    rw [atJet_liftedFlow _ _ _ hf, atJet_partialFlow_sep, ih, clear_one_derivative,
      Function.iterate_succ_apply']
theorem derivative_hasse (S : Geom[X]) (k : ℕ) :
    derivative (hasseDeriv k S) = Polynomial.C ((k+1 : ℕ) : Geom) * hasseDeriv (k+1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast, Nat.add_comm, add_mul] using h
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
section Branch
variable {L : Type} [Field L]
private def localReduce (y : Fin 4 → L) : TotalLocal y →+* PointLocal y :=
  Localization.localRingHom (totalPrime y) (rationalIdeal y) reduce rfl
private def branchReduce (g : Fin 4 → Total L) (y : Fin 4 → L) :
    BranchAlgebra g y →+* PointAlgebra (equationsIdeal fun i => reduce (g i)) y := by
  refine Ideal.quotientMap _ (localReduce y) ?_
  rw [Ideal.map_le_iff_le_comap, equationsIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change localReduce y (algebraMap (Total L) (TotalLocal y) (g i)) ∈
    (equationsIdeal fun i => reduce (g i)).map (algebraMap (Affine L) (PointLocal y))
  rw [localReduce, Localization.localRingHom_to_map]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))
private theorem branchReduce_class (g : Fin 4 → Total L) (y : Fin 4 → L) (p : Total L) :
    branchReduce g y (branchClass g y p) =
      pointClass (equationsIdeal fun i => reduce (g i)) y (reduce p) := by
  simp [branchReduce, branchClass, pointClass, localReduce]
private theorem clear_generic_ideal (g : Fin 4 → Total L) (p : Total L)
    (h : genericClass g p = 0) :
    ∃ d : Polynomial L, d ≠ 0 ∧ C d * p ∈ equationsIdeal g := by
  let : Algebra (Total L) (Affine (ParameterField L)) := MvPolynomial.algebraMvPolynomial
  let S := (Polynomial L)⁰.map (C (σ := Fin 4))
  have : IsLocalization S (Affine (ParameterField L)) :=
    MvPolynomial.isLocalization (Polynomial L)⁰ (ParameterField L)
  have hmem : algebraMap (Total L) (Affine (ParameterField L)) p ∈
      (equationsIdeal g).map (algebraMap (Total L) (Affine (ParameterField L))) :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨_, ⟨d, hd, rfl⟩, hp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff S _ (equationsIdeal g) p).mp hmem
  exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, hp⟩
theorem relation_vanishes (g : Fin 4 → Total L) (y : Fin 4 → L)
    (hreg : IsSMulRegular (BranchAlgebra g y) (branchParameter g y))
    (p : Total L) (hp : genericClass g p = 0) :
    pointClass (equationsIdeal fun i => reduce (g i)) y (reduce p) = 0 := by
  obtain ⟨d, hd0, hd⟩ := clear_generic_ideal g p hp
  obtain ⟨q, hfactor, hq⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd0 (0 : L)
  rw [Polynomial.C_0, sub_zero] at hfactor hq
  have hu : C q ∉ totalPrime y := by
    change reduce (C q) ∉ rationalIdeal y
    rw [mem_vanishingIdeal_singleton_iff]
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero] at hq
    simpa [reduce] using hq
  have hunit : IsUnit (branchClass g y (C q)) :=
    (IsLocalization.map_units (TotalLocal y) (⟨C q, hu⟩ : (totalPrime y).primeCompl)).map
      (Ideal.Quotient.mk _)
  have hz : branchClass g y (C d * p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hd)
  have hz' : branchParameter g y ^ d.rootMultiplicity 0 *
      (branchClass g y (C q) * branchClass g y p) = 0 := by
    rw [hfactor] at hz
    simpa only [map_mul, map_pow, mul_assoc, branchParameter] using hz
  have hz'' : branchClass g y (C q) * branchClass g y p = 0 :=
    (hreg.pow (d.rootMultiplicity 0)) (by simpa only [smul_eq_mul, mul_zero] using hz')
  have hp' : branchClass g y p = 0 :=
    hunit.mul_left_cancel (by simpa only [mul_zero] using hz'')
  rw [← branchReduce_class, hp', map_zero]
end Branch
section Rank
variable {L : Type} [Field L]
private theorem reduce_surjective : Function.Surjective (reduce (L := L)) := by
  apply MvPolynomial.map_surjective
  intro a
  exact ⟨Polynomial.C a, Polynomial.eval_C⟩
private theorem class_C (g : Fin 4 → Total L) (a : Polynomial L) :
    genericClass g (C a) =
      algebraMap (ParameterField L) (GenericFiber g)
        (algebraMap (Polynomial L) (ParameterField L) a) := by
  change Ideal.Quotient.mk _
    (MvPolynomial.map (algebraMap (Polynomial L) (ParameterField L)) (C a)) = _
  rw [map_C]
  rfl
theorem specialization_rank (g : Fin 4 → Total L)
    {D : Type} [AddCommGroup D] [Module L D]
    (s : Affine L →ₗ[L] D) (hs : Function.Surjective s)
    (hrel : ∀ p, genericClass g p = 0 → s (reduce p) = 0)
    [Module.Finite (ParameterField L) (GenericFiber g)] :
    Module.finrank L D ≤ Module.finrank (ParameterField L) (GenericFiber g) := by
  classical
  let n := Module.finrank L D
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := L) (M := D)
    (show n ≤ Module.finrank L D from le_rfl)
  choose p hp using fun i => (hs.comp reduce_surjective) (b i)
  let v (i : Fin n) := genericClass g (p i)
  let inc := algebraMap (Polynomial L) (ParameterField L)
  have hsum (a : Fin n → Polynomial L) :
      genericClass g (∑ i, C (a i) * p i) = ∑ i, inc (a i) • v i := by
    simp only [map_sum, map_mul, class_C]
    apply Finset.sum_congr rfl
    intro i _
    exact (Algebra.smul_def (inc (a i)) (v i)).symm
  have hconstant (a : Fin n → Polynomial L) (ha : (∑ i, inc (a i) • v i) = 0) (i : Fin n) :
      (a i).eval 0 = 0 := by
    have hz := hrel _ ((hsum a).trans ha)
    have hrow (j : Fin n) :
        s (reduce (C (a j) * p j)) = (a j).eval 0 • b j := by
      rw [map_mul]
      change s (MvPolynomial.map (Polynomial.evalRingHom 0) (C (a j)) * reduce (p j)) = _
      rw [map_C, MvPolynomial.C_mul', map_smul]
      rw [show s (reduce (p j)) = b j from hp j]
      rfl
    simp only [map_sum, hrow] at hz
    exact Fintype.linearIndependent_iff.mp hb _ hz i
  suffices hv : LinearIndependent (ParameterField L) v by
    simpa [n] using hv.fintype_card_le_finrank
  refine Fintype.linearIndependent_iff.mpr fun a ha j => ?_
  by_contra hj
  obtain ⟨den, hden⟩ := IsLocalization.exist_integer_multiples_of_finite (Polynomial L)⁰ a
  choose c hc using hden
  have hden0 : inc den ≠ 0 := by
    simpa only [inc, map_zero] using
      (IsFractionRing.injective (Polynomial L) (ParameterField L)).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp den.prop)
  have hc' (i : Fin n) : inc (c i) = inc den * a i :=
    (hc i).trans (Algebra.smul_def (den : Polynomial L) (a i))
  have hcj : c j ≠ 0 := by
    intro hz
    exact (mul_ne_zero hden0 hj) (by rw [← hc', hz, map_zero])
  have hc0 : (∑ i, inc (c i) • v i) = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, ha, smul_zero]
  let P (d : ℕ) := ∃ a : Fin n → Polynomial L,
    a j ≠ 0 ∧ (a j).natDegree = d ∧ (∑ i, inc (a i) • v i) = 0
  have hP : ∃ d, P d := ⟨(c j).natDegree, c, hcj, rfl, hc0⟩
  obtain ⟨a, haj, hdeg, ha0⟩ := Nat.find_spec hP
  have hdiv (i : Fin n) : Polynomial.X ∣ a i := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hconstant a ha0 i
  choose a' ha' using hdiv
  have ha'j : a' j ≠ 0 := by
    intro hz
    exact haj (by rw [ha' j, hz, mul_zero])
  have hX : inc Polynomial.X ≠ 0 := by
    simpa only [inc, map_zero] using
      (IsFractionRing.injective (Polynomial L) (ParameterField L)).ne Polynomial.X_ne_zero
  have ha'0 : (∑ i, inc (a' i) • v i) = 0 := by
    have h : inc Polynomial.X • (∑ i, inc (a' i) • v i) = 0 := by
      simp only [Finset.smul_sum, ← mul_smul, ← inc.map_mul, ← ha', ha0]
    exact (smul_eq_zero.mp h).resolve_left hX
  have hmin := Nat.find_min' hP (show P (a' j).natDegree from ⟨a', ha'j, rfl, ha'0⟩)
  rw [ha' j, Polynomial.natDegree_X_mul ha'j] at hdeg
  omega
end Rank
section IsolatedPoints
open scoped Function
variable {L : Type} [Field L]
private theorem pointIdeal_injective : Function.Injective (rationalIdeal (L := L)) := by
  intro x y h
  funext j
  have hx : MvPolynomial.X j - C (x j) ∈ rationalIdeal x := by
    rw [mem_vanishingIdeal_singleton_iff]
    simp
  rw [h, mem_vanishingIdeal_singleton_iff] at hx
  simpa [sub_eq_zero, eq_comm] using hx
theorem pointClass_ker_contains_power (I : Ideal (Affine L)) (y : Fin 4 → L)
    (hy : rationalIdeal y ∈ I.minimalPrimes) :
    ∃ n : ℕ, rationalIdeal y ^ n ≤ RingHom.ker (pointClass I y).toRingHom := by
  let T := PointLocal y
  let J := I.map (algebraMap (Affine L) T)
  have hm : IsLocalRing.maximalIdeal T ∈ J.minimalPrimes := by
    rw [show J = I.map (algebraMap (Affine L) T) from rfl,
      IsLocalization.minimalPrimes_map (rationalIdeal y).primeCompl T, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal T (rationalIdeal y)]
    exact hy
  have : IsArtinianRing (T ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hm
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  refine ⟨n, fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hn ?_)⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (rationalIdeal y) T, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hp
theorem pointClass_surjective (I : Ideal (Affine L)) (y : Fin 4 → L)
    (n : ℕ) (hn : rationalIdeal y ^ n ≤ RingHom.ker (pointClass I y).toRingHom) :
    Function.Surjective (pointClass I y) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (rationalIdeal y).primeCompl z
  have hcop : IsCoprime (rationalIdeal y) (Ideal.span {(s : Affine L)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have he := (inferInstance : (rationalIdeal y).IsMaximal).eq_of_le h le_sup_left
    have hle : Ideal.span {(s : Affine L)} ≤
        rationalIdeal y ⊔ Ideal.span {(s : Affine L)} := le_sup_right
    have hm := hle (Ideal.mem_span_singleton_self (s : Affine L))
    rw [← he] at hm
    exact s.prop hm
  obtain ⟨a, ha, b, hb, hab⟩ := (hcop.pow_left (m := n)).exists
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hb
  have hs : pointClass I y (s : Affine L) * pointClass I y w = 1 := by
    have hz : pointClass I y a = 0 := hn ha
    simpa only [map_add, map_mul, hz, zero_add, map_one] using congrArg (pointClass I y) hab
  have hr : pointClass I y r =
      Ideal.Quotient.mk _ (IsLocalization.mk' (PointLocal y) r s) *
        pointClass I y (s : Affine L) := by
    let mk := Ideal.Quotient.mk (I.map (algebraMap (Affine L) (PointLocal y)))
    change mk (algebraMap (Affine L) (PointLocal y) r) =
      mk (IsLocalization.mk' (PointLocal y) r s) *
        mk (algebraMap (Affine L) (PointLocal y) s)
    rw [← map_mul, IsLocalization.mk'_spec]
  refine ⟨r * w, ?_⟩
  rw [map_mul, hr, mul_assoc, hs, mul_one]
theorem points_surjective (I : Ideal (Affine L)) {ι : Type} [Fintype ι]
    (y : ι → Fin 4 → L) (hy : Function.Injective y)
    (hmin : ∀ i, rationalIdeal (y i) ∈ I.minimalPrimes) :
    Function.Surjective (AlgHom.pi fun i => pointClass I (y i)) := by
  classical
  choose n hn using fun i => pointClass_ker_contains_power I (y i) (hmin i)
  intro z
  choose r hr using fun i => pointClass_surjective I (y i) (n i) (hn i) (z i)
  have hcop : Pairwise (IsCoprime on fun i => rationalIdeal (y i) ^ n i) := by
    intro i j hij
    have hne : rationalIdeal (y i) ≠ rationalIdeal (y j) :=
      fun he => hij (hy (pointIdeal_injective he))
    exact (Ideal.isCoprime_of_isMaximal hne).pow_left.pow_right
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hcop r
  refine ⟨p, funext fun i => ?_⟩
  change pointClass I (y i) p = z i
  rw [← hr i, ← sub_eq_zero, ← map_sub]
  exact hn i (hp i)
end IsolatedPoints
end
end K1_13_5_4_2_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace K1_13_5_4_3_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem flat_rowToGeo : Module.Flat (Row 3) (GeoRow 3) := by
  have : Module.Flat Geom[X] RationalX :=
    IsLocalization.flat RationalX (nonZeroDivisors Geom[X])
  have : Module.Flat Geom[X] GeometricX :=
    Module.Flat.trans Geom[X] RationalX GeometricX
  have h : Algebra.IsPushout Geom[X] (Row 3) GeometricX (GeoRow 3) := inferInstance
  exact Module.Flat.isBaseChange Geom[X] (Row 3) GeometricX (GeoRow 3) h.out
private theorem rowToGeo_eq (b : Row 3) :
    algebraMap (Row 3) (GeoRow 3) b = genericRow b := by
  exact congrArg (fun g => MvPolynomial.map g b)
    (IsScalarTower.algebraMap_eq Geom[X] RationalX GeometricX)
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
@[simp] private theorem coeff_coeffDerivative (b : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative b).coeff m = derivative (b.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_add (a b : Row 3) :
    coeffDerivative (a + b) = coeffDerivative a + coeffDerivative b := by
  ext m
  simp
private theorem coeffDerivative_mul (a b : Row 3) :
    coeffDerivative (a * b) = coeffDerivative a * b + a * coeffDerivative b := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  change derivative ((a * b).coeff m) =
    (coeffDerivative a * b).coeff m + (a * coeffDerivative b).coeff m
  simp only [coeff_coeffDerivative, MvPolynomial.coeff_mul, map_sum, derivative_mul,
    Finset.sum_add_distrib]
theorem tangentNumerator_add (f a b : Row 3) :
    tangentNumerator f (a + b) = tangentNumerator f a + tangentNumerator f b := by
  simp only [tangentNumerator, lowerTangent, coeffDerivative_add, map_add]
  ring
theorem tangentNumerator_mul (f a b : Row 3) :
    tangentNumerator f (a * b) = tangentNumerator f a * b + a * tangentNumerator f b := by
  simp only [tangentNumerator, lowerTangent, coeffDerivative_mul, MvPolynomial.pderiv_mul]
  ring
private theorem tangent_self (f : Row 3) : tangentNumerator f f = 0 := by
  unfold tangentNumerator separant
  exact sub_eq_zero.mpr (mul_comm _ _)
private theorem tangent_cut_mem (f : Row 3) (P : Ideal (GeoRow 3)) [hp : P.IsPrime]
    (hs : genericRow (separant f) ∉ P) (hc : genericRow (oldCut f) ∈ P)
    (hn : genericRow (oldNext f) ∈ P) :
    genericRow (tangentNumerator f (oldCut f)) ∈ P := by
  let k := taylorLength - 3
  have hrec : oldNext f = separant f * tangentNumerator f (oldCut f) -
      ((2 * k + 1 : ℕ) : Row 3) * oldCut f * tangentNumerator f (separant f) := by
    change compatibilityNumerator f (k + 1) = _
    rfl
  have hadd : genericRow (separant f * tangentNumerator f (oldCut f)) =
      genericRow (oldNext f) +
        genericRow (((2 * k + 1 : ℕ) : Row 3) * oldCut f * tangentNumerator f (separant f)) := by
    rw [hrec]
    simp only [genericRow, map_sub, sub_add_cancel]
  have hterm :
      genericRow (((2 * k + 1 : ℕ) : Row 3) * oldCut f * tangentNumerator f (separant f)) ∈ P := by
    simp only [genericRow, map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hc)
  have hprod : genericRow (separant f) * genericRow (tangentNumerator f (oldCut f)) ∈ P := by
    rw [show genericRow (separant f) * genericRow (tangentNumerator f (oldCut f)) =
      genericRow (separant f * tangentNumerator f (oldCut f)) from
        ((MvPolynomial.map genericCoeff).map_mul _ _).symm, hadd]
    exact P.add_mem hn hterm
  exact (hp.mem_or_mem hprod).resolve_left hs
theorem proof : K1_13_5_4_3.c1 := by
  intro f P hP hInv
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp hP
  have hp : P.IsPrime := hmin.isPrime
  have hf : genericRow f ∈ P := hmin.le (Ideal.subset_span (by simp))
  have hc : genericRow (oldCut f) ∈ P := hmin.le (Ideal.subset_span (by simp))
  have hcut := tangent_cut_mem f P hsep hc hInv.2
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
  have ha := P.mul_mem_left (genericRow (tangentNumerator f s)) hx
  have hz := P.sub_mem hd ha
  rw [add_sub_cancel_left] at hz
  exact (hp.mem_or_mem hz).resolve_left hs
end
end K1_13_5_4_3_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3_2
noncomputable section
open K1_13_5_4_2_4_2 K1_13_5_4_2_4_2_3 MvPolynomial
abbrev Geo := K1_13_5_4.GeometricX
abbrev Supports := Fin 4 → Finset K1_13_5_4_2_4.Exponent
private abbrev degreeExponent : Degree ≃+ (Fin 4 →₀ ℕ) :=
  Finsupp.addEquivFunOnFinite.symm
private def affineExponent (A : Supports) : (Slot A →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight fun v => v.2.val
private def taggedExponent (A : Supports) : (Slot A →₀ ℕ) →+ ((Fin 4 ⊕ Fin 4) →₀ ℕ) :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
    ((degreeExponent.toAddMonoidHom.comp (Finsupp.weight (slotWeight A))).prod (affineExponent A))
private theorem taggedExponent_eq {A : Supports} {e f : Slot A →₀ ℕ} :
    taggedExponent A e = taggedExponent A f ↔
      Finsupp.weight (slotWeight A) e = Finsupp.weight (slotWeight A) f ∧
        affineExponent A e = affineExponent A f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) ↔ _
  rw [EquivLike.apply_eq_iff_eq, Prod.ext_iff]
  change (degreeExponent (Finsupp.weight (slotWeight A) e) =
    degreeExponent (Finsupp.weight (slotWeight A) f) ∧ _) ↔ _
  rw [EquivLike.apply_eq_iff_eq]
private def monomialHom {R σ τ : Type*} [CommRing R] (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
    MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R w
private theorem monomialHom_apply {R σ τ : Type*} [CommRing R]
    (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : R) :
    monomialHom w (monomial e c) = monomial (w e) c := by
  change AddMonoidAlgebra.mapDomain w (AddMonoidAlgebra.single e c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl
def binomialIdeal (A : Supports) (R : Type*) [CommRing R] : Ideal (MvPolynomial (Slot A) R) :=
  Ideal.span {p | ∃ e f : Slot A →₀ ℕ, taggedExponent A e = taggedExponent A f ∧
    p = monomial e 1 - monomial f 1}
theorem map_binomialIdeal {R S : Type*} [CommRing R] [CommRing S]
    (A : Supports) (g : R →+* S) :
    (binomialIdeal A R).map (MvPolynomial.map g) = binomialIdeal A S := by
  rw [binomialIdeal, Ideal.map_span, binomialIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, f, h, rfl⟩, rfl⟩
    exact ⟨e, f, h, by simp⟩
  · rintro ⟨e, f, h, rfl⟩
    exact ⟨_, ⟨e, f, h, rfl⟩, by simp⟩
private theorem lift_monomials {A : Supports} {R τ : Type*} [CommRing R]
    (s : Set (Slot A →₀ ℕ)) (w : (Slot A →₀ ℕ) → (τ →₀ ℕ))
    (h : ∀ e ∈ s, ∀ f ∈ s, w e = w f → taggedExponent A e = taggedExponent A f) :
    ∃ l : MvPolynomial τ R →ₗ[R] (MvPolynomial (Slot A) R ⧸ binomialIdeal A R),
      ∀ e ∈ s, l (monomial (w e) 1) = Ideal.Quotient.mk _ (monomial e 1) := by
  classical
  let J := binomialIdeal A R
  let g (a : τ →₀ ℕ) : MvPolynomial (Slot A) R ⧸ J :=
    if ha : ∃ e ∈ s, w e = a then Ideal.Quotient.mk J (monomial ha.choose 1) else 0
  refine ⟨(basisMonomials τ R).constr R g, fun e he => ?_⟩
  change (basisMonomials τ R).constr R g ((basisMonomials τ R) (w e)) = _
  rw [Module.Basis.constr_basis]
  let he' : ∃ f ∈ s, w f = w e := ⟨e, he, rfl⟩
  dsimp only [g]
  rw [dite_eq_left he', Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span ⟨_, _, h _ he'.choose_spec.1 e he he'.choose_spec.2, rfl⟩
private theorem tagged_ker (A : Supports) (R : Type*) [CommRing R] :
    RingHom.ker (monomialHom (R := R) (taggedExponent A)).toRingHom = binomialIdeal A R := by
  let J := binomialIdeal A R
  let φ := monomialHom (R := R) (taggedExponent A)
  obtain ⟨l, hl⟩ := lift_monomials (R := R) Set.univ (taggedExponent A)
    (fun _ _ _ _ h => h)
  have hfac : l.comp φ.toLinearMap = (Ideal.Quotient.mkₐ R J).toLinearMap := by
    apply (basisMonomials (Slot A) R).ext
    intro e
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [show φ (monomial e 1) = monomial (taggedExponent A e) 1 from monomialHom_apply _ _ _]
    exact hl e (Set.mem_univ _)
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := DFunLike.congr_fun hfac p
    change l (φ p) = Ideal.Quotient.mk J p at h
    change φ p = 0 at hp
    simpa [hp] using h.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    change monomialHom (R := R) (taggedExponent A) (monomial e 1 - monomial f 1) = 0
    rw [map_sub, monomialHom_apply, monomialHom_apply, h, sub_self]
private theorem dehom_eq_monomialHom (A : Supports) :
    dehom A = monomialHom (affineExponent A) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [dehom, aeval_X, MvPolynomial.X, monomialHom_apply, affineExponent, Finsupp.weight_single, one_smul]
theorem relationIdeal_zero (A : Supports) :
    relationIdeal A 0 = binomialIdeal A (K1_13_5_4_2_4.CoefficientField A) := by
  classical
  have hprefix : prefixIdeal A 0 = ⊥ := by simp [prefixIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨d, hd⟩, hp⟩
    have hz : dehom A p = 0 := by simpa [hprefix] using hp
    let J := binomialIdeal A (K1_13_5_4_2_4.CoefficientField A)
    obtain ⟨l, hl⟩ := lift_monomials (R := K1_13_5_4_2_4.CoefficientField A)
      {e | Finsupp.weight (slotWeight A) e = d} (affineExponent A)
      (fun e he f hf h => taggedExponent_eq.mpr ⟨he.trans hf.symm, h⟩)
    let q := Ideal.Quotient.mkₐ (K1_13_5_4_2_4.CoefficientField A) J
    have hfac : l (dehom A p) = q p := by
      calc
        l (dehom A p) = l (dehom A (∑ e ∈ p.support, monomial e (p.coeff e))) :=
          congrArg (fun r => l (dehom A r)) p.as_sum
        _ = q (∑ e ∈ p.support, monomial e (p.coeff e)) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [show monomial e (p.coeff e) = p.coeff e • monomial e 1 by
            simp [smul_monomial]]
          simp only [map_smul, dehom_eq_monomialHom, monomialHom_apply,
            hl e (hd (mem_support_iff.mp he))]
          rfl
        _ = q p := (congrArg q p.as_sum).symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [← hfac, hz, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    obtain ⟨hd, ha⟩ := taggedExponent_eq.mp h
    apply Ideal.subset_span
    refine ⟨⟨_, Submodule.sub_mem (slotPiece A (Finsupp.weight (slotWeight A) e)) ?_ ?_⟩, ?_⟩
    · exact isWeightedHomogeneous_monomial _ _ _ rfl
    · exact isWeightedHomogeneous_monomial _ _ _ hd.symm
    · rw [hprefix, Ideal.mem_bot, map_sub, dehom_eq_monomialHom,
        monomialHom_apply, monomialHom_apply, ha, sub_self]
abbrev MonomialRing (A : Supports) := MvPolynomial (Slot A) Geo ⧸ binomialIdeal A Geo
instance (A : Supports) : IsDomain (MonomialRing A) := by
  have : (binomialIdeal A Geo).IsPrime := by
    rw [← tagged_ker]
    exact RingHom.ker_isPrime _
  infer_instance
theorem monomialCoordinate_ne_zero {A : Supports} (v : Slot A) :
    Ideal.Quotient.mk (binomialIdeal A Geo) (MvPolynomial.X v) ≠ 0 := by
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [← tagged_ker] at hm
  change monomialHom (R := Geo) (taggedExponent A) (MvPolynomial.X v) = 0 at hm
  rw [MvPolynomial.X, monomialHom_apply, monomial_eq_zero] at hm
  exact one_ne_zero hm
end
end K1_13_5_4_2_4_2_3_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {k σ : Type} [Field k] [Finite σ]
def linearForm (a : σ → k) : MvPolynomial σ k := by
  classical
  letI := Fintype.ofFinite σ
  exact ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i
def fiberIdeal (I : Ideal (MvPolynomial σ k)) (a : σ → k) (t : k) :
    Ideal (MvPolynomial σ k) :=
  I ⊔ Ideal.span {linearForm a - MvPolynomial.C t}
def projection (I : Ideal (MvPolynomial σ k)) (a : σ → k) :
    Polynomial k →ₐ[k] (MvPolynomial σ k ⧸ I) :=
  Polynomial.aeval (Ideal.Quotient.mk I (linearForm a))
def IsSeparating (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) (a : σ → k) : Prop :=
  letI : I.IsPrime := hI
  let u : FractionRing (MvPolynomial σ k ⧸ I) :=
    algebraMap (MvPolynomial σ k ⧸ I) _ (Ideal.Quotient.mk I (linearForm a))
  Transcendental k u ∧
    Algebra.IsSeparable (IntermediateField.adjoin k ({u} : Set _))
      (FractionRing (MvPolynomial σ k ⧸ I))
end
end K1_13_5_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
abbrev EmbeddedPoint := lastExponents → GeometricX
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
private theorem three_ne_zero : (3 : GeometricX) ≠ 0 := by
  let : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  let : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  let : CharP GeometricX K1.p :=
    charP_of_injective_ringHom genericCoeff_injective K1.p
  exact fun h => (by decide : ¬ K1.p ∣ 3)
    ((CharP.cast_eq_zero_iff GeometricX K1.p 3).mp h)
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
  rw [graphPoint, Fin.snoc_last, div_eq_iff (mul_ne_zero three_ne_zero hs')]
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
end K1_13_5_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2_4 MvPolynomial
open scoped TensorProduct
private abbrev CoeffIndex (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
private def center {A : Fin 4 → Finset Exponent} (f : Fin 4 → GeoRow 4)
    (a : CoeffIndex A) : GeometricX :=
  (f a.1).coeff a.2.1
private def coeffLine (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (a : CoeffIndex A) : Polynomial (CoefficientField A) :=
  Polynomial.C (algebraMap GeometricX (CoefficientField A) (center f a)) +
    Polynomial.X * Polynomial.C (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X a))
def deformation (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (i : Fin 4) : Total (CoefficientField A) :=
  ∑ a : ↥(A i), monomial a.1 (coeffLine A f ⟨i, a⟩)
private def coeffLineHom (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4) :
    CoefficientRing A →+* Polynomial (CoefficientField A) :=
  eval₂Hom (Polynomial.C.comp (algebraMap GeometricX (CoefficientField A))) (coeffLine A f)
private theorem coeffLineHom_injective (A : Fin 4 → Finset Exponent)
    (f : Fin 4 → GeoRow 4) : Function.Injective (coeffLineHom A f) := by
  let shift : CoefficientRing A →ₐ[GeometricX] CoefficientRing A :=
    aeval fun a => C (center f a) + MvPolynomial.X a
  let unshift : CoefficientRing A →ₐ[GeometricX] CoefficientRing A :=
    aeval fun a => MvPolynomial.X a - C (center f a)
  have hshift : unshift.comp shift = AlgHom.id GeometricX _ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [shift, unshift, algebraMap_eq]
  have hleft : Function.LeftInverse unshift shift := fun p => AlgHom.congr_fun hshift p
  have heval : (Polynomial.evalRingHom 1).comp (coeffLineHom A f) =
      (algebraMap (CoefficientRing A) (CoefficientField A)).comp shift.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Polynomial.eval 1 (coeffLineHom A f (C c)) =
        algebraMap (CoefficientRing A) (CoefficientField A) (shift (C c))
      rw [coeffLineHom, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C, algHom_C]
      exact IsScalarTower.algebraMap_apply GeometricX (CoefficientRing A) (CoefficientField A) c
    · intro a
      change Polynomial.eval 1 (coeffLineHom A f (MvPolynomial.X a)) =
        algebraMap (CoefficientRing A) (CoefficientField A)
          (aeval (fun b => C (center f b) + MvPolynomial.X b) (MvPolynomial.X a))
      rw [coeffLineHom, MvPolynomial.eval₂Hom_X', aeval_X]
      simp only [coeffLine, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, one_mul, map_add]
      rw [IsScalarTower.algebraMap_apply GeometricX (CoefficientRing A) (CoefficientField A)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply IsFractionRing.injective (CoefficientRing A) (CoefficientField A)
  exact (RingHom.congr_fun heval p).symm.trans
    ((congrArg (Polynomial.evalRingHom 1) hpq).trans (RingHom.congr_fun heval q))
private def genericCoeffMap (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4) :
    CoefficientField A →+* ParameterField (CoefficientField A) :=
  IsFractionRing.lift (g := (algebraMap (Polynomial (CoefficientField A))
      (ParameterField (CoefficientField A))).comp (coeffLineHom A f))
    ((IsFractionRing.injective (Polynomial (CoefficientField A)) (ParameterField (CoefficientField A))).comp
      (coeffLineHom_injective A f))
private theorem genericCoeffMap_coeff (A : Fin 4 → Finset Exponent)
    (f : Fin 4 → GeoRow 4) (a : CoeffIndex A) :
    genericCoeffMap A f (algebraMap (CoefficientRing A) (CoefficientField A) (MvPolynomial.X a)) =
      algebraMap (Polynomial (CoefficientField A)) (ParameterField (CoefficientField A))
        (coeffLine A f a) := by
  rw [genericCoeffMap, IsFractionRing.lift_algebraMap]
  simp [coeffLineHom]
theorem deformation_reduce (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (hs : ∀ i, (f i).support ⊆ A i) :
    equationsIdeal (fun i => reduce (deformation A f i)) = extendIdeal (CoefficientField A)
      (cutIdeal f) := by
  classical
  have hrow (i : Fin 4) : reduce (deformation A f i) =
      MvPolynomial.map (algebraMap GeometricX (CoefficientField A)) (f i) := by
    have hsum : (∑ a ∈ A i, monomial a ((f i).coeff a)) = f i := by
      rw [← Finset.sum_subset (hs i), ← MvPolynomial.as_sum]
      intro a _ ha
      rw [notMem_support_iff.mp ha, monomial_zero]
    conv_rhs => rw [← hsum]
    simp [reduce, deformation, coeffLine, center]
    exact Finset.sum_attach (A i)
      (fun a => monomial a (algebraMap GeometricX (CoefficientField A) ((f i).coeff a)))
  simp only [equationsIdeal, extendIdeal, cutIdeal, Ideal.map_span, ← Set.range_comp', hrow]
def baseQuotient {k L : Type} [Field k] [Field L] [Algebra k L]
    (I : Ideal (Affine k)) :
    L ⊗[k] (Affine k ⧸ I) ≃ₐ[L]
      Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (Affine k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap k L) p = e (1 ⊗ₜ[k] p)
  simp [e]
private theorem finite_rank_map_ideal {k L : Type} [Field k] [Field L] [Algebra k L]
    (I : Ideal (Affine k)) [Module.Finite k (Affine k ⧸ I)] :
    Module.Finite L (Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L))) ∧
    Module.finrank L (Affine L ⧸ I.map (MvPolynomial.map (algebraMap k L))) =
      Module.finrank k (Affine k ⧸ I) := by
  let e := (baseQuotient (L := L) I).toLinearEquiv
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem deformation_generic (A : Fin 4 → Finset Exponent) (f : Fin 4 → GeoRow 4)
    (hf : Module.Finite (CoefficientField A) (GenericQuotient A)) :
    Module.Finite (ParameterField (CoefficientField A)) (GenericFiber (deformation A f)) ∧
    Module.finrank (ParameterField (CoefficientField A)) (GenericFiber (deformation A f)) =
      Module.finrank (CoefficientField A) (GenericQuotient A) := by
  let : Algebra (CoefficientField A) (ParameterField (CoefficientField A)) :=
    (genericCoeffMap A f).toAlgebra
  have hrow (i : Fin 4) :
      MvPolynomial.map (algebraMap (CoefficientField A) (ParameterField (CoefficientField A)))
          (genericEquation A i) = toGeneric (deformation A f i) := by
    change MvPolynomial.map (genericCoeffMap A f) (genericEquation A i) = _
    simp [genericEquation, toGeneric, deformation, genericCoeffMap_coeff]
  have hid :
      (Ideal.span (Set.range (genericEquation A))).map
          (MvPolynomial.map (algebraMap (CoefficientField A) (ParameterField (CoefficientField A)))) =
        (equationsIdeal (deformation A f)).map toGeneric := by
    simp only [equationsIdeal, Ideal.map_span, ← Set.range_comp', hrow]
  have := hf
  have hbase := finite_rank_map_ideal (L := ParameterField (CoefficientField A))
    (Ideal.span (Set.range (genericEquation A)))
  rw [hid] at hbase
  exact hbase
end
end K1_13_5_4_2_4_1
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open scoped BigOperators
theorem genericCoeff_injective : Function.Injective genericCoeff :=
  (algebraMap RationalX GeometricX).injective.comp (IsFractionRing.injective _ _)
@[simp] theorem eval_genericRow {r : ℕ} (S : Geom[X]) (P : Row r) :
    MvPolynomial.eval (jetPoint S) (genericRow P) = genericCoeff (atJet P S) :=
  (MvPolynomial.map_eval genericCoeff (jet S) P).symm
theorem generic_lift (P : Row 3) : genericRow (liftRaw P) = liftRow (genericRow P) :=
  MvPolynomial.map_rename genericCoeff Fin.castSucc P
theorem generic_graph (f : Row 3) : genericRow (graphRaw f) = graph f := by
  unfold graphRaw graph
  change MvPolynomial.map genericCoeff (_ + _) = _
  rw [map_add, map_mul, map_mul, MvPolynomial.map_X, map_ofNat]
  exact congrArg₂ (· + 3 * MvPolynomial.X 3 * ·) (generic_lift _) (generic_lift _)
private theorem genericCoeff_ne_zero {a : Geom[X]} (h : a ≠ 0) : genericCoeff a ≠ 0 := by
  intro ha
  exact h (genericCoeff_injective (ha.trans genericCoeff.map_zero.symm))
private theorem geometric_three_ne_zero : (3 : GeometricX) ≠ 0 := by
  have h := geomCast_ne_zero (a := 3) (by decide) (by decide)
  intro hz
  apply h
  apply (algebraMap Geom GeometricX).injective
  rw [map_natCast, map_zero]
  exact hz
theorem graphPoint_of_actual {f : Row 3} {S : Geom[X]} (hS : RegularAt 2 f S) :
    graphPoint f (jetPoint S) = jetPoint (n := 4) S := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs : genericCoeff (atJet (separant f) S) ≠ 0 := genericCoeff_ne_zero hS.2
    have h := congrArg genericCoeff (graph_atJet_zero hS.1)
    change genericCoeff (MvPolynomial.eval (jet S : Fin 4 → Geom[X]) (_ + _)) = _ at h
    simp only [map_add, map_mul, map_ofNat, map_zero, MvPolynomial.eval_X,
      show ∀ p : Row 3, MvPolynomial.eval (jet S) (liftRaw p) = atJet p S from
        fun p => atJet_lift p S] at h
    unfold graphPoint
    rw [Fin.snoc_last, eval_genericRow, eval_genericRow,
      div_eq_iff (mul_ne_zero geometric_three_ne_zero hs)]
    change -genericCoeff (atJet (lowerTangent f) S) =
      genericCoeff (jet S (3 : Fin 4)) * (3 * genericCoeff (atJet (separant f) S))
    linear_combination -h
  · exact Fin.snoc_castSucc _ _ _
private theorem graphIdeal_eval_zero {f : Row 3} {S : Geom[X]} (hS : RegularAt 2 f S)
    {P : GeoRow 4} (hP : P ∈ graphIdeal f) :
    MvPolynomial.eval (jetPoint S) P = 0 := by
  let e := MvPolynomial.eval (jetPoint (n := 4) S)
  have hJ : graphIdeal f ≤ RingHom.ker e := by
    rw [graphIdeal, Ideal.span_le]
    intro p hp
    change e p = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · simp [e, ← generic_lift, atJet_lift, hS.1]
    · simp [e, ← generic_graph, graph_atJet_zero hS.1]
  exact hJ hP
private theorem scaled_third (S : Geom[X]) (k : ℕ) (hk : k + 3 < K1.p) :
    Polynomial.C (thirdScale k) * ((derivative (R := Geom))^[k]) (jet S (3 : Fin 4)) =
      hasseDeriv (k+3) S := by
  induction k with
  | zero => simp [thirdScale, jet]
  | succ k ih =>
    have he := congrArg derivative (ih (by omega))
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_hasse] at he
    rw [thirdScale, map_mul, mul_comm (Polynomial.C (thirdScale k)), mul_assoc,
      Function.iterate_succ_apply', he, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (geomCast_ne_zero (a := k+4) (by omega) (by omega)), map_one, one_mul]
private theorem atJet_jetNumerator (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0)
    (j : ℕ) (hj : j < K1.p) :
    atJet (jetNumerator f j) S = atJet (liftSep f) S ^ (j-3) * hasseDeriv j S := by
  have hVar (i : Fin 4) : atJet (MvPolynomial.X i) S = hasseDeriv i.val S :=
    MvPolynomial.eval_X i
  unfold jetNumerator
  split_ifs with h
  · rw [hVar, show j - 3 = 0 by omega, pow_zero, one_mul]
  · let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
    change e (MvPolynomial.C _ * _) = _
    rw [map_mul, MvPolynomial.eval_C]
    change Polynomial.C _ * atJet (thirdNumerator f (j-3)) S = _
    rw [atJet_thirdNumerator _ _ hf, mul_left_comm, scaled_third S (j-3) (by omega),
      Nat.sub_add_cancel (by omega : 3 ≤ j)]
private theorem atJet_padJet (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0)
    (d j : ℕ) (hd : j - 3 ≤ d) (hj : j < K1.p) :
    atJet (padJet f d j) S = atJet (separant f) S ^ d * hasseDeriv j S := by
  let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
  change e (_ ^ _ * jetNumerator f j) = _
  rw [map_mul, map_pow]
  change atJet (liftSep f) S ^ _ * atJet (jetNumerator f j) S = _
  rw [atJet_jetNumerator f S hf j hj, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd, atJet_lift]
private theorem atJet_paddedJet (f : Row 3) (S : Geom[X]) (hf : atJet f S = 0)
    (j : Fin taylorLength) :
    atJet (paddedJet f j) S =
      atJet (separant f) S ^ (taylorLength - 4) * hasseDeriv j.val S := by
  have hjlt : j.val < 133672 := j.isLt
  have hp : 133672 < K1.p := by decide
  have hd : j.val - 3 ≤ 133668 := by omega
  exact atJet_padJet f S hf (taylorLength - 4) j.val hd (hjlt.trans hp)
private theorem taylor_coeff_generic (S : Geom[X]) (j : ℕ) :
    (taylor centre (S.map (algebraMap Geom GeometricX))).coeff j =
      genericCoeff (hasseDeriv j S) := by
  rw [taylor_coeff, hasseDeriv_map, Polynomial.eval_map]
  have he : Polynomial.eval₂RingHom (algebraMap Geom GeometricX) centre = genericCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      change (Polynomial.C a).eval₂ (algebraMap Geom GeometricX) centre = genericCoeff (Polynomial.C a)
      rw [eval₂_C]
      exact IsScalarTower.algebraMap_apply Geom Geom[X] GeometricX a
    · exact eval₂_X _ _
  exact RingHom.congr_fun he _
private theorem taylor_coefficients_aux (S : Geom[X]) (m : ℕ) (hS : S.natDegree < m)
    (i : ℕ) :
    (∑ j : Fin m, ((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i *
      genericCoeff (hasseDeriv j.val S)) = algebraMap Geom GeometricX (S.coeff i) := by
  let P := S.map (algebraMap Geom GeometricX)
  have hn : (taylor centre P).natDegree < m := by
    rw [natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have Hd : (taylor centre P).degree < (m : WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  have hsum : (∑ j : Fin m, Polynomial.C ((taylor centre P).coeff j.val) *
      (Polynomial.X - Polynomial.C centre) ^ j.val) = P := by
    exact (Polynomial.sum_fin
      (fun j (a : GeometricX) => Polynomial.C a * (Polynomial.X - Polynomial.C centre) ^ j)
      (fun _ => by rw [Polynomial.C_0, zero_mul]) Hd).trans (Polynomial.sum_taylor_eq P centre)
  calc
    _ = ∑ j : Fin m, (Polynomial.C ((taylor centre P).coeff j.val) *
        (Polynomial.X - Polynomial.C centre) ^ j.val).coeff i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [coeff_C_mul, taylor_coeff_generic, mul_comm]
    _ = P.coeff i := by rw [← finsetSum_coeff, hsum]
    _ = _ := Polynomial.coeff_map (algebraMap Geom GeometricX) i
private theorem taylor_coefficients (S : Geom[X]) (hS : S.natDegree ≤ 133671)
    (i : Fin taylorLength) :
    (∑ j : Fin taylorLength, ((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val *
      genericCoeff (hasseDeriv j.val S)) = coefficientPoint S i :=
  taylor_coefficients_aux S taylorLength (show S.natDegree < 133672 by omega) i.val
theorem reconstruct_actual {f : Row 3} {S : Geom[X]} (hdeg : S.natDegree ≤ 133671)
    (hS : RegularAt 2 f S) :
    reconstruct f (coefficientNumerator f) (jetPoint S) = coefficientPoint S := by
  funext i
  rw [reconstruct, graphPoint_of_actual hS, eval_genericRow]
  let s := genericCoeff (atJet (separant f) S)
  have hs : s ≠ 0 := genericCoeff_ne_zero hS.2
  unfold coefficientNumerator
  rw [map_sum]
  change (∑ j : Fin taylorLength, MvPolynomial.eval (jetPoint S) _) /
    s ^ (taylorLength - 4) = _
  simp only [map_mul, MvPolynomial.eval_C, eval_genericRow, atJet_paddedJet f S hS.1, map_pow]
  rw [div_eq_iff (pow_ne_zero _ hs), ← taylor_coefficients S hdeg i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (s ^ (taylorLength - 4) * _) = _ * s ^ (taylorLength - 4)
  rw [mul_comm (s ^ (taylorLength - 4)), ← mul_assoc]
private theorem third_atJet_zero {f : Row 3} {S : Geom[X]} (hf : atJet f S = 0)
    (k : ℕ) (hk : S.natDegree - 3 < k) :
    atJet (thirdNumerator f k) S = 0 := by
  rw [atJet_thirdNumerator f S hf, iterate_derivative_eq_zero, mul_zero]
  exact (natDegree_hasseDeriv_le S 3).trans_lt hk
private theorem actual_zero_of_represents {f old : Row 3} {P : GeoRow 4} {S : Geom[X]}
    (hS : RegularAt 2 f S) (hP : RepresentsOnGraph f old P)
    (hzero : MvPolynomial.eval (jetPoint S) P = 0) : atJet old S = 0 := by
  obtain ⟨a, b, c, hc, h⟩ := hP
  have he := graphIdeal_eval_zero hS h
  simp only [map_mul, map_pow, map_sub, hzero, mul_zero, MvPolynomial.eval_C,
    ← generic_lift, eval_genericRow, atJet_lift, zero_sub] at he
  have hs : genericCoeff (atJet (separant f) S) ≠ 0 :=
    genericCoeff_ne_zero hS.2
  have hq : genericCoeff (atJet old S) = 0 := by
    simpa [mul_eq_zero, pow_ne_zero _ hs, hc] using he
  exact genericCoeff_injective (by simpa only [map_zero] using hq)
theorem actual {f : Row 3} (hcut : RepresentsOnGraph f (oldCut f) (cut f))
    (hnext : RepresentsOnGraph f (oldNext f) (next f))
    (S : Geom[X]) (hdeg : S.natDegree ≤ 133671) (hS : RegularAt 2 f S) :
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f (coefficientNumerator f) (jetPoint S) = coefficientPoint S := by
  refine ⟨actual_zero_of_represents hS hcut ?_, actual_zero_of_represents hS hnext ?_,
    reconstruct_actual hdeg hS⟩
  · rw [cut, eval_genericRow, third_atJet_zero hS.1 _ (by change _ < 133669; omega), map_zero]
  · rw [next, eval_genericRow, third_atJet_zero hS.1 _ (by change _ < 133670; omega), map_zero]
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ P Q : Set ExponentSpace, FirstBody P → FirstBody Q →
    lastMixedVolume (P + Q) = lastMixedVolume P + lastMixedVolume Q
def c2 : Prop :=
  ∀ P : Set ExponentSpace, FirstBody P → P ⊆ capBody lowBox 0 →
    lastMixedVolume P ≤ lastMixedVolume (capBody lowBox 0)
private theorem sum_mixed {ι : Type} (h : c1) (P : ι → Set ExponentSpace)
    (hP : ∀ i, FirstBody (P i)) (S : Finset ι) :
    FirstBody (∑ i ∈ S, P i) ∧
      (∑ i ∈ S, lastMixedVolume (P i)) = lastMixedVolume (∑ i ∈ S, P i) := by
  classical
  have hz := h 0 0 firstBody_zero firstBody_zero
  rw [zero_add] at hz
  have hv : lastMixedVolume (0 : Set ExponentSpace) = 0 := by linarith
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, hv] using
      (show FirstBody (0 : Set ExponentSpace) ∧ (0 : ℝ) = 0 from ⟨firstBody_zero, rfl⟩)
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, ih.2]
    exact ⟨(hP i).add ih.1, (h _ _ (hP i) ih.1).symm⟩
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2.c5 := by
  intro n f hf
  let P (i : Fin n) := downBody (liftRow (genericRow (f i)))
  have hP (i : Fin n) : FirstBody (P i) := firstBody_row (hf.irreducible i).ne_zero
  obtain ⟨hbody, hsum⟩ := sum_mixed h1 P hP Finset.univ
  change (∑ i, lastMixedVolume (P i)) ≤ (mixedBudget : ℝ)
  rw [hsum, ← native_box_price capBody_volume]
  exact h2 _ hbody (sum_downBody_subset f hf)
end
end K1_13_5_4_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators Function
variable {k σ : Type} [Field k] [Finite σ]
theorem totalDegree_hyperplane_le_one (a : σ → k) (t : k) :
    (linearForm a - MvPolynomial.C t).totalDegree ≤ 1 := by
  classical
  apply (totalDegree_sub_C_le _ _).trans
  unfold linearForm
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
theorem zeroLocus_fiber_iff {I : Ideal (MvPolynomial σ k)} {a z : σ → k} {t : k} :
    z ∈ zeroLocus k (fiberIdeal I a t) ↔ z ∈ zeroLocus k I ∧ aeval z (linearForm a) = t := by
  rw [fiberIdeal, mem_zeroLocus_sup_span_singleton_iff, map_sub, aeval_C]
  exact and_congr_right fun _ => sub_eq_zero
theorem ncard_eq_affineDegree_of_radical [IsAlgClosed k] (J : Ideal (MvPolynomial σ k))
    (hJ : (affineHilbertPolynomial J).natDegree = 0) (hrad : J.IsRadical) :
    ((zeroLocus k J).ncard : ℚ) = affineDegree J := by
  classical
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  let zeros := zeroLocus k J
  have hZ : zeros.Finite := finite_zeroLocus_of_finite_quotient J
  let : Fintype zeros := hZ.fintype
  let e (x : zeros) : MvPolynomial σ k →ₐ[k] k := aeval x.val
  let M (x : zeros) := RingHom.ker (e x)
  have hpair : Pairwise (IsCoprime on M) := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, y.val i ≠ x.val i := by
      by_contra! he
      exact hxy (Subtype.ext (funext he).symm)
    let u : MvPolynomial σ k :=
      MvPolynomial.C ((y.val i - x.val i)⁻¹) * (MvPolynomial.X i - MvPolynomial.C (x.val i))
    have hx : e x u = 0 := by simp [e, u]
    have hy : e y u = 1 := by
      simp [e, u, inv_mul_cancel₀ (sub_ne_zero.mpr hi)]
    refine Ideal.isCoprime_iff_exists.mpr ⟨u, RingHom.mem_ker.mpr hx, 1 - u, ?_, by ring⟩
    exact RingHom.mem_ker.mpr (by rw [map_sub, map_one, hy, sub_self])
  let φ := AlgHom.pi e
  have hker : RingHom.ker φ = J := by
    calc
      _ = vanishingIdeal k zeros := by
        ext p
        rw [RingHom.mem_ker, mem_vanishingIdeal_iff]
        exact ⟨fun h x hx => congrFun h (⟨x, hx⟩ : zeros), fun h => funext fun x => h x.val x.property⟩
      _ = J := (vanishingIdeal_zeroLocus_eq_radical J).trans (Ideal.radical_eq_iff.mpr hrad)
  have hsurj : Function.Surjective φ := by
    intro d
    obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hpair
      (fun x => Ideal.Quotient.mk (M x) (MvPolynomial.C (d x)))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨p, funext fun x => ?_⟩
    have hx := congrArg (Ideal.kerLiftAlg (e x)) (congrFun hq x)
    rw [Ideal.quotientInfToPiQuotient_mk', Ideal.kerLiftAlg_mk, Ideal.kerLiftAlg_mk] at hx
    simpa [φ, e] using hx
  let E := (Ideal.quotientEquivAlgOfEq k hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  rw [affineDegree_eq_finrank, E.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact_mod_cast (Nat.card_eq_fintype_card (α := zeros))
end
end K1_13_5_4_2_2
end
section
namespace K1_13_5_3
noncomputable section
open K1 K1_13 K1_13_5 Polynomial PolynomialDifferential
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev CenterField := FractionRing Geom[X]
abbrev toCenter : Geom[X] →+* CenterField := algebraMap Geom[X] CenterField
abbrev constants : Geom →+* CenterField := toCenter.comp Polynomial.C
abbrev center : CenterField := toCenter Polynomial.X
def flatten (f : Row 2) : DifferentialPolynomial Geom 1 :=
  (MvPolynomial.optionEquivRight Geom (Fin 2)).symm f
def chart (f : Row 2) : DifferentialPolynomial CenterField 1 :=
  MvPolynomial.map constants (flatten f)
def plane (f : Row 2) : MvPolynomial (Fin 2) CenterField := MvPolynomial.map toCenter f
def marked (S : Geom[X]) : Fin 2 → CenterField :=
  polynomialJet center (S.map constants)
theorem toCenter_inj : Function.Injective toCenter := IsFractionRing.injective _ _
private theorem eval_at_center (S : Geom[X]) : (S.map constants).eval center = toCenter S := by
  rw [Polynomial.eval_map]
  change eval₂RingHom constants center S = toCenter S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
theorem marked_apply (S : Geom[X]) (i : Fin 2) :
    marked S i = toCenter (jet S i) := by
  change (hasseDeriv i.val (S.map constants)).eval center = _
  rw [Polynomial.hasseDeriv_map, eval_at_center]
  rfl
theorem marked_injective : Function.Injective marked := by
  intro S T heq
  have h := congrFun heq (0 : Fin 2)
  simpa only [marked_apply, jet, Fin.val_zero, Polynomial.hasseDeriv_zero',
    toCenter_inj.eq_iff] using h
theorem aeval_plane (f : Row 2) (S : Geom[X]) :
    MvPolynomial.aeval (marked S) (plane f) = toCenter (atJet f S) := by
  have hm : marked S = toCenter ∘ jet S := funext (marked_apply S)
  rw [plane, MvPolynomial.aeval_eq_eval, hm, atJet, ← MvPolynomial.map_eval]
theorem plane_ne_zero {f : Row 2} (hf : f ≠ 0) : plane f ≠ 0 :=
  fun h => hf ((MvPolynomial.map_injective _ toCenter_inj) (h.trans (map_zero _).symm))
theorem plane_prime {f : Row 2} (hf : Irreducible f) (hp : 0 < f.degreeOf 1) :
    (Ideal.span {plane f}).IsPrime := by
  let M := (Geom[X]⁰).map (MvPolynomial.C (σ := Fin 2))
  have hI : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hdis : Disjoint (M : Set (Row 2)) (Ideal.span {f} : Ideal (Row 2)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hd
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hd
    have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hq' : q ≠ 0 := by
      intro h
      exact ha' (by simpa [h] using hq)
    have hh := congrArg (MvPolynomial.degreeOf (1 : Fin 2)) hq
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_mul_eq hf.ne_zero hq'] at hh
    omega
  have h := IsLocalization.isPrime_of_isPrime_disjoint M
    (MvPolynomial (Fin 2) CenterField) (Ideal.span {f}) hI hdis
  simpa only [plane, MvPolynomial.algebraMap_def, Ideal.map_span, Set.image_singleton] using h
private theorem specialization_flatten (f : Row 2) (S : Geom[X]) :
    differentialSpecialization (flatten f) S = atJet f S := by
  let x : Option (Fin 2) → Geom[X] := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_optionEquivRight_symm (R := Geom) x f
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id (Geom[X]) from rfl,
    MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  unfold flatten at *
  unfold atJet differentialSpecialization
  refine (AlgHom.congr_fun ?_ _).trans h
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
theorem chart_degree (f : Row 2) : jetTotalDegree (chart f) ≤ f.totalDegree := by
  apply (jetTotalDegree_map_le constants _).trans
  have hw : (jetDegreeWeight : Option (Fin 2) → ℕ) =
      fun v => v.elim 0 (fun _ => 1) := by
    funext v
    cases v <;> rfl
  rw [jetTotalDegree, hw, ← MvPolynomial.totalDegree_optionEquivRight]
  simp only [flatten, AlgEquiv.apply_symm_apply, le_refl]
theorem chart_top (f : Row 2) : (chart f).degreeOf (some 1) ≤ f.degreeOf 1 := by
  have h : (flatten f).degreeOf (some 1) = f.degreeOf 1 := by
    rw [← MvPolynomial.degreeOf_optionEquivRight]
    simp only [flatten, AlgEquiv.apply_symm_apply]
  rw [← h, MvPolynomial.degreeOf_def, MvPolynomial.degreeOf_def]
  exact Multiset.count_le_of_le _ MvPolynomial.degrees_map_le
theorem degreeOf_le_index (f : Row 2) : f.degreeOf 1 ≤ indexDegree f := by
  rw [MvPolynomial.degreeOf_eq_sup, indexDegree]
  exact Finset.sup_le fun m hm => by
    apply (Finset.le_sup (f := fun m : Fin 2 →₀ ℕ =>
      m.sum fun i a => i.val * a) hm).trans'
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    simp
abbrev exponent := 2 * taylorLength - 5
abbrev chartTotal := 1 + exponent * (5064 - 1)
abbrev chartTop := min chartTotal (exponent * (1104 - 1) + taylorLength - 1)
theorem exponent_sufficient : TaylorExponentSufficient 1 taylorLength exponent := by
  exact taylorExponentSufficient_firstOrder_tight 133671
theorem chart_cut_agreement {f : Row 2} {S : Geom[X]} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 133671) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (chart f) taylorLength exponent (constants x) (constants y))
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
    have hb : (S.map constants).natDegree ≤ 133671 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP CenterField K1.p := charP_of_injective_ringHom constants.injective K1.p
  have hpiv : ∀ i : ℕ, 1 < i → i < taylorLength → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField K1.p i).mp hz)
    change 2130706433 ≤ i at hp
    change i < 133672 at ht
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (chart f) exponent_sufficient (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]
end
end K1_13_5_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
def c1 : Prop :=
  ∀ (f : Row 3) (T : LiftedChart f) (e : OldOpen f ≃+* GraphOpen f T),
    (∀ b, e (oldMap f b) = graphMap f T (liftRow b)) →
    ∀ Q : Ideal (GeoRow 4), Q.IsPrime → threeCut f T ≤ Q → liftedSep f ∉ Q →
      let P := Q.comap (rename Fin.castSucc).toRingHom
      oldCutIdeal f ≤ P ∧ graphCurve f P = Q
def c2 : Prop :=
  ∀ (f : Row 3) (T : LiftedChart f) (e : OldOpen f ≃+* GraphOpen f T),
    (∀ b, e (oldMap f b) = graphMap f T (liftRow b)) →
    ∀ (P : Ideal (GeoRow 3)) (Q : Ideal (GeoRow 4)) [P.IsPrime] [Q.IsPrime],
      oldCutIdeal f ≤ P → threeCut f T ≤ Q → sep f ∉ P → liftedSep f ∉ Q →
      Q.comap (rename Fin.castSucc).toRingHom = P →
      let A := Localization.AtPrime P
      let B := Localization.AtPrime Q
      Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A)) =
        Module.length B (B ⧸ (threeCut f T).map (algebraMap (GeoRow 4) B))
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
  constructor
  · intro ha
    have hh : sep f * a ∈ vanishingIdeal GeometricX (zeroLocus GeometricX P) := by
      intro x hx
      change eval x (sep f * a) = 0
      rw [map_mul]
      by_cases hs : eval x (sep f) = 0
      · rw [hs, zero_mul]
      · have he : eval (graphPoint f x) (liftRow a) = 0 := ha _ ⟨x, ⟨hx, hs⟩, rfl⟩
        rw [eval_liftRow_graphPoint] at he
        rw [he, mul_zero]
    rw [IsPrime.vanishingIdeal_zeroLocus] at hh
    exact (‹P.IsPrime›.mem_or_mem hh).resolve_left hsep
  · intro ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [aeval_eq_eval, eval_liftRow_graphPoint] using hx.1 a ha
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
private theorem graph_is_curve {f : Row 3} (hf : Irreducible f) (hpos : 0 < f.degreeOf 2)
    {P : Ideal (GeoRow 3)} (hP : P ∈ factorCurves f) :
    (graphCurve f P).IsPrime ∧ (affineHilbertPolynomial (graphCurve f P)).natDegree = 1 := by
  obtain ⟨hprime, hdim⟩ := K1_13_5_4_2_1.proof f hf hpos P hP
  have hs : Function.Surjective lastMap := monomialMap_surjective lastExponents_single
  let : (sectionIdeal f P).IsPrime := hprime
  have hmap : (sectionIdeal f P).map lastMap = graphCurve f P :=
    Ideal.map_comap_of_surjective _ hs _
  have hker : RingHom.ker lastMap.toRingHom ≤ sectionIdeal f P := by
    intro p hp
    change lastMap.toRingHom p ∈ graphCurve f P
    rw [RingHom.mem_ker.mp hp]
    exact Ideal.zero_mem _
  refine ⟨hmap ▸ Ideal.map_isPrime_of_surjective (f := lastMap.toRingHom) hs hker, ?_⟩
  change (affineHilbertPolynomial ((graphCurve f P).comap lastMap)).natDegree = 1 at hdim
  rwa [natDegree_affineHilbertPolynomial_comap_of_surjective lastMap hs] at hdim
private theorem point_isolated (h1 : c1) {f : Row 3} (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 2) (T : LiftedChart f) {L : GeoRow 4}
    (hL : ∀ P ∈ factorCurves f, L ∉ graphCurve f P)
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
  have hChart := h1 f T (graphEquiv f T) (graphEquiv_on f T)
  refine ⟨⟨inferInstance, sup_le hBm ((Ideal.span_singleton_le_iff_mem _).mpr hmL)⟩, ?_⟩
  intro Q hQ hQm
  let q := Q.comap (rename Fin.castSucc).toRingHom
  have hQsep : liftedSep f ∉ Q := fun h => hmsep (hQm h)
  obtain ⟨hIq, hGQ⟩ := hChart Q hQ.1 (le_sup_left.trans hQ.2) hQsep
  let : Q.IsPrime := hQ.1
  let : q.IsPrime := hQ.1.comap _
  have hsq : sep f ∉ q := hQsep
  obtain ⟨P', hP', hP'q⟩ := Ideal.exists_mem_retainedMinimalPrimes_le (Q := q) hIq hsq
  have hP'f : P' ∈ factorCurves f := mem_factorCurves.mpr ⟨hProper, hP'⟩
  have hle : graphCurve f P' ≤ Q := by
    rw [← hGQ]
    exact vanishingIdeal_anti_mono
      (Set.image_mono fun _ hx => ⟨zeroLocus_anti_mono hP'q hx.1, hx.2⟩)
  obtain ⟨hp', hd⟩ := graph_is_curve hf hpos hP'f
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
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2.c3 := by
  intro f hf hpos T L hL P hP y hy hLy
  have hJ : fourCutIdeal (liftRow (genericRow f)) (graph f) T.cut L =
      threeCut f T ⊔ Ideal.span {L} := by
    simp [fourCutIdeal, threeCut, graphIdeal, Ideal.span_insert, sup_assoc]
  dsimp only
  rw [hJ]
  refine ⟨point_isolated h1 hf hpos T hL hP hy hLy, ?_⟩
  obtain ⟨hmin, hsep⟩ := Ideal.mem_retainedMinimalPrimes.mp (mem_factorCurves.mp hP).2
  let : P.IsPrime := hmin.isPrime
  let Q := graphCurve f P
  let : Q.IsPrime := (graph_is_curve hf hpos hP).1
  have hQy : Q ≤ pointIdeal y := graphCurve_le_point hy
  have hLiftSep : liftedSep f ∉ Q := fun h => sep_notMem_point hy (hQy h)
  rw [componentLength, dite_eq_left hmin.isPrime]
  rw [h2 f T (graphEquiv f T) (graphEquiv_on f T) P Q hmin.le
    (threeCut_le_graphCurve T hmin.le) hsep hLiftSep (graphCurve_comap hsep)]
  exact length_atPrime_le_length_principalCut hQy
    ((mem_vanishingIdeal_singleton_iff _ _).mpr hLy) (hL P hP)
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 MeasureTheory
open scoped BigOperators Pointwise
def slotShape : Fin 4 → Shape :=
  ![lowBox, graphBox, liftedBox (taylorLength + 1), lastBox]
def slotHeight : Fin 4 → ℕ :=
  ![0, 1, taylorLength - 1, taylorLength]
def slots (P : Set ExponentSpace) : Fin 4 → Set ExponentSpace :=
  Function.update (fun i => capBody (slotShape i) (slotHeight i)) 0 P
def totalSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 0 + x 1 + x 2) '' P)
def indexSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 1 + 2 * x 2) '' P)
def topSupport (P : Set ExponentSpace) : ℝ :=
  sSup ((fun x : ExponentSpace => x 2) '' P)
def volumeQuotient (P C : Set ExponentSpace) (t : ℝ) : ℝ :=
  ((volume (t • P + C)).toReal - (volume C).toReal) / t
def capFirstVariation (s : Shape) (h : ℕ) (B J T : ℝ) : ℝ :=
  (h : ℝ) * ((s.t : ℝ) * ((s.j : ℝ) - s.t) * B +
    (s.t : ℝ) * ((s.b : ℝ) - s.j + (s.t : ℝ) / 2) * J +
    ((s.j : ℝ) - 2 * s.t) * ((s.b : ℝ) - (s.j : ℝ) / 2) * T)
end
end K1_13_5_4_2_5_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_2 MvPolynomial
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)), I.IsPrime →
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ bad : Finset (Submodule k (σ → k)),
      (∀ B ∈ bad, B ≠ ⊤) ∧
      ∀ (a : σ → k), (∀ B ∈ bad, a ∉ B) →
        (projection I a).Finite ∧
        ∀ t : k, (affineHilbertPolynomial (fiberIdeal I a t)).natDegree = 0 ∧
          affineDegree (fiberIdeal I a t) = affineDegree I
def c2 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime),
    (affineHilbertPolynomial I).natDegree = 1 →
    ∃ B : Submodule k (σ → k), B ≠ ⊤ ∧
      ∀ (a : σ → k), a ∉ B → IsSeparating I hI a
def c3 : Prop :=
  ∀ (k σ : Type) [Field k] [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    (a : σ → k), (projection I a).Finite → IsSeparating I hI a →
    ∃ bad : Finset k, ∀ t ∉ bad, (fiberIdeal I a t).IsRadical
private theorem hyperplane_support (a : EmbeddedPoint) (t : GeometricX) :
    InLiftedBox (lastMap (linearForm a - MvPolynomial.C t)) lastBox taylorLength := by
  have hz : (0 : Fin 4 →₀ ℕ) ∈ lastExponents := by
    change 0 + 0 + 0 ≤ lastBox.b ∧ 0 + 2 * 0 ≤ lastBox.j ∧ 0 ≤ lastBox.t ∧ 0 ≤ taylorLength
    simp
  have h := monomialMap_mem_restrictSupport_nsmul hz (totalDegree_hyperplane_le_one a t)
  rw [one_nsmul] at h
  exact h
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_5_4_2.c2 := by
  classical
  intro f hC
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
end K1_13_5_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13_5_4_2 MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
theorem mixed_eq (P : Set ExponentSpace) : lastMixedVolume P = mixedVolume4 (slots P) := by
  unfold lastMixedVolume
  congr 1
  funext i
  fin_cases i <;> rfl
def rest : Finset (Fin 4) := insert 1 (insert 2 (insert 3 ∅))
theorem univ_eq_insert : (Finset.univ : Finset (Fin 4)) = insert 0 rest := by decide
theorem zero_notMem_rest : (0 : Fin 4) ∉ rest := by decide
private theorem alternating_product (u v : Fin 4 → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * ∏ i, (if i ∈ S then u i else v i)) =
      ∏ i, (u i - v i) := by
  rw [univ_eq_insert]
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (0 : Fin 4)) (s := insert 1 (insert 2 (insert 3 ∅))) (by decide),
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert]
  ring
private def weights (t : ℝ) (S : Finset (Fin 4)) (i : Fin 4) : ℝ :=
  if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i else 0
private theorem eval_as_sum (p : MvPolynomial (Fin 4) ℝ) (w : Fin 4 → ℝ) :
    p.eval w = ∑ d ∈ p.support, p.coeff d * ∏ i, (w i) ^ d i := by
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [eval_monomial, Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (by simp)]
private theorem polar_eval (p : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * p.eval (weights t S)) =
      ∑ d ∈ p.support, p.coeff d * ∏ i, ((![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i) := by
  simp_rw [eval_as_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
        p.coeff d * ((-1 : ℝ) ^ (4 - S.card) *
          ∏ i, (if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i else 0 ^ d i)) := by
      apply Finset.sum_congr rfl
      intro S _
      have heq : (∏ i, weights t S i ^ d i) =
          ∏ i, (if i ∈ S then (![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i else 0 ^ d i) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [weights, hi]
      rw [heq]
      ring
    _ = _ := by
      rw [← Finset.mul_sum, alternating_product]
private theorem product_linear (d : Fin 4 →₀ ℕ) (hd : d.degree = 4) (t : ℝ) :
    (∏ i, ((![t, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i)) =
      t * ∏ i, ((![1, 1, 1, 1] : Fin 4 → ℝ) i ^ d i - 0 ^ d i) := by
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]),
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  · have hn (i : Fin 4) : 0 < d i := Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
    have hones (i : Fin 4) : d i = 1 := by
      have h0 := hn 0
      have h1 := hn 1
      have h2 := hn 2
      have h3 := hn 3
      fin_cases i
      · change d 0 = 1
        omega
      · change d 1 = 1
        omega
      · change d 2 = 1
        omega
      · change d 3 = 1
        omega
    simp [hones, Fin.prod_univ_four]
private theorem polar_linear (p : MvPolynomial (Fin 4) ℝ)
    (hp : p.IsHomogeneous 4) (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      (-1 : ℝ) ^ (4 - S.card) * p.eval (weights t S)) =
      t * ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (-1 : ℝ) ^ (4 - S.card) * p.eval (weights 1 S) := by
  rw [polar_eval, polar_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d.degree = 4 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  rw [product_linear d hd' t]
  ring
private theorem polar_slots (P : Set ExponentSpace) (hP : ∀ i, (slots P i).Nonempty)
    (t : ℝ) (S : Finset (Fin 4)) :
    (∑ i, weights t S i • slots P i) = ∑ i ∈ S, slots (t • P) i := by
  calc
    _ = ∑ i ∈ S, (![t, 1, 1, 1] : Fin 4 → ℝ) i • slots P i := by
      rw [← Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
        (f := fun i => weights t S i • slots P i)]
      · exact Finset.sum_congr rfl (fun i hi => by simp [weights, hi])
      · intro i _ hi
        simp [weights, hi, Set.zero_smul_set (hP i)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> simp [slots]
theorem mixed_scale (P : Set ExponentSpace) (hP : ∀ i, (slots P i).Nonempty)
    (p : MvPolynomial (Fin 4) ℝ) (hp : p.IsHomogeneous 4)
    (heval : ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) →
      p.eval w = (volume (∑ i, w i • slots P i)).toReal)
    (t : ℝ) (ht : 0 ≤ t) :
    lastMixedVolume (t • P) = t * lastMixedVolume P := by
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
  simp only [mixed_eq, mixedVolume4]
  simpa only [hpol _ ht, hpol 1 zero_le_one, one_smul] using polar_linear p hp t
end
end K1_13_5_4_2_5_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_3_2
noncomputable section
open K1_13_5_4_2_4_2_3 MvPolynomial
abbrev UniversalRing (A : Supports) := MvPolynomial (Slot A) (MonomialRing A)
def coordinate {A : Supports} (v : Slot A) : MonomialRing A :=
  Ideal.Quotient.mk (binomialIdeal A Geo) (MvPolynomial.X v)
def modelChart (A : Supports) (b : (j : Fin 4) → ↥(A j)) : MonomialRing A :=
  ∏ j : Fin 4, coordinate ⟨j, b j⟩
theorem modelChart_ne_zero (A : Supports) (b : (j : Fin 4) → ↥(A j)) :
    modelChart A b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => monomialCoordinate_ne_zero ⟨j, b j⟩
def modelEquation (A : Supports) (i : Fin 4) : UniversalRing A :=
  ∑ a : ↥(A i), C (coordinate ⟨i, a⟩) * MvPolynomial.X ⟨i, a⟩
def modelIdeal (A : Supports) (k : ℕ) : Ideal (UniversalRing A) :=
  Ideal.span (modelEquation A '' {i : Fin 4 | i.val < k})
private theorem substitution {L : Type*} [CommRing L] (A : Supports) (k : ℕ)
    (b : (j : Fin 4) → ↥(A j)) (z : Slot A → L) (w : Fin 4 → L)
    (hw : ∀ j, w j * z ⟨j, b j⟩ = 1) :
    ∃ E : MvPolynomial (Slot A) L →ₐ[L] MvPolynomial (Slot A) L,
      RingHom.ker E.toRingHom =
        Ideal.span ((fun j : Fin 4 => ∑ a : ↥(A j), C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩) ''
          {j : Fin 4 | j.val < k}) := by
  classical
  let terms (j : Fin 4) (a : ↥(A j)) : MvPolynomial (Slot A) L :=
    C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩
  let equation (j : Fin 4) := ∑ a, terms j a
  let rest (j : Fin 4) := ∑ a ∈ Finset.univ.erase (b j), terms j a
  let value (v : Slot A) : MvPolynomial (Slot A) L :=
    if v.1.val < k ∧ v.2 = b v.1 then - (C (w v.1) * rest v.1) else MvPolynomial.X v
  let E : MvPolynomial (Slot A) L →ₐ[L] MvPolynomial (Slot A) L := aeval value
  let J := Ideal.span (equation '' {j : Fin 4 | j.val < k})
  have hsum (j : Fin 4) : equation j = rest j + terms j (b j) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ (b j))).symm
  have hrest (j : Fin 4) : E (rest j) = rest j := by
    simp only [rest, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    simp [terms, E, value, hne]
  have hpivot (j : Fin 4) (hj : j.val < k) :
      E (MvPolynomial.X ⟨j, b j⟩) = - (C (w j) * rest j) := by
    simp [E, value, hj]
  have hunit (j : Fin 4) : C (w j) * C (z ⟨j, b j⟩) = (1 : MvPolynomial (Slot A) L) := by
    rw [← map_mul, hw, map_one]
  refine ⟨E, show RingHom.ker E.toRingHom = J from le_antisymm ?_ ?_⟩
  · let q := Ideal.Quotient.mkₐ L J
    have hq : q.comp E = q := by
      apply MvPolynomial.algHom_ext
      rintro ⟨j, a⟩
      change q (E (MvPolynomial.X ⟨j, a⟩)) = q (MvPolynomial.X ⟨j, a⟩)
      by_cases h : j.val < k ∧ a = b j
      · obtain ⟨hj, rfl⟩ := h
        rw [hpivot j hj, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        rw [show - (C (w j) * rest j) - MvPolynomial.X ⟨j, b j⟩ =
          -(C (w j) * rest j + MvPolynomial.X ⟨j, b j⟩) by abel]
        apply J.neg_mem
        have he : equation j ∈ J := Ideal.subset_span ⟨j, hj, rfl⟩
        have hm := J.mul_mem_left (C (w j)) he
        simpa only [hsum j, terms, mul_add, ← mul_assoc, hunit j, one_mul] using hm
      · simp [E, value, h]
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    have hh := DFunLike.congr_fun hq p
    change q (E p) = q p at hh
    change E p = 0 at hp
    simpa only [hp, map_zero] using hh.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change E (equation j) = 0
    rw [hsum, map_add, hrest]
    simp only [terms, map_mul, hpivot j hj, mul_neg]
    rw [show E (C (z ⟨j, b j⟩)) = C (z ⟨j, b j⟩) by simp [E]]
    rw [← mul_assoc, mul_comm (C (z ⟨j, b j⟩)), hunit, one_mul, add_neg_cancel]
theorem model_saturate (A : Supports) (k : ℕ) (b : (j : Fin 4) → ↥(A j))
    {a : MonomialRing A} (ha : a ≠ 0) (u : UniversalRing A) (n : ℕ)
    (hu : C a ^ n * u ∈ modelIdeal A k) :
    ∃ m : ℕ, C (modelChart A b) ^ m * u ∈ modelIdeal A k := by
  classical
  let x := modelChart A b
  let L := Localization.Away x
  have hx : x ≠ 0 := modelChart_ne_zero A b
  let : IsDomain L := Localization.Away.isDomain hx
  let g := algebraMap (MonomialRing A) L
  let z (v : Slot A) := g (coordinate v)
  have hux : IsUnit (∏ j : Fin 4, z ⟨j, b j⟩) := by
    simp only [z, ← map_prod]
    change IsUnit (algebraMap (MonomialRing A) L x)
    exact IsLocalization.Away.algebraMap_isUnit (S := L) x
  have hz (j : Fin 4) : IsUnit (z ⟨j, b j⟩) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => z ⟨i, b i⟩) (Finset.mem_univ j)) hux
  choose w hw using fun j => isUnit_iff_exists_inv.mp (hz j)
  obtain ⟨E, hE⟩ := substitution A k b z w (fun j => (mul_comm _ _).trans (hw j))
  let : Algebra (UniversalRing A) (MvPolynomial (Slot A) L) := MvPolynomial.algebraMvPolynomial
  let incl := algebraMap (UniversalRing A) (MvPolynomial (Slot A) L)
  let M := (Submonoid.powers x).map (C (σ := Slot A))
  have : IsLocalization M (MvPolynomial (Slot A) L) :=
    MvPolynomial.isLocalization (Submonoid.powers x) L
  have hincl : incl = MvPolynomial.map g := rfl
  have hJ : (modelIdeal A k).map incl = RingHom.ker E.toRingHom := by
    rw [hE, modelIdeal, Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    simp [hincl, modelEquation, z]
  have hmem := Ideal.mem_map_of_mem incl hu
  rw [hJ] at hmem
  change E (incl (C a ^ n * u)) = 0 at hmem
  have hga : g a ≠ 0 := by
    have hinj : Function.Injective g := IsLocalization.injective (S := L)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    exact fun h => ha (hinj (h.trans (map_zero g).symm))
  have hEa : E (incl (C a)) = C (g a) := by simp [hincl]
  have heu : E (incl u) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow, hEa] at hmem
    exact (mul_eq_zero.mp hmem).resolve_left (pow_ne_zero _ (C_ne_zero.mpr hga))
  have hu' : incl u ∈ (modelIdeal A k).map incl := by rw [hJ]; exact heu
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, hm⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M _ (modelIdeal A k) u).mp hu'
  exact ⟨m, by simpa only [map_pow] using hm⟩
end
end K1_13_5_4_2_4_2_3_2
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 MvPolynomial
open scoped Polynomial
private theorem partial_degree (P : Row 3) (i : Fin 3) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 3 → ℕ) i P
private theorem coeffDerivative_degree (P : Row 3) :
    (coeffDerivative P).totalDegree ≤ P.totalDegree := by
  unfold coeffDerivative
  exact totalDegree_finsetSum_le fun m hm =>
    (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem nat_mul_degree (a : ℕ) (P : Row 3) :
    ((a : Row 3) * P).totalDegree ≤ P.totalDegree := by
  rw [← map_natCast (C : Geom[X] →+* Row 3) a]
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
private theorem shift_degree (P : Row 3) (i j : Fin 3) :
    (MvPolynomial.X j * pderiv i P).totalDegree ≤ P.totalDegree := by
  by_cases h : P.totalDegree = 0
  · rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C, mul_zero, totalDegree_zero]
    exact Nat.zero_le _
  · have hp := partial_degree P i
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    omega
private theorem lowerTangent_degree (P : Row 3) :
    (lowerTangent P).totalDegree ≤ P.totalDegree := by
  unfold lowerTangent
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (coeffDerivative_degree P) (shift_degree P 0 1)))
    (by rw [mul_assoc]; exact (nat_mul_degree 2 _).trans (shift_degree P 1 2)))
private theorem tangent_degree (f P : Row 3) :
    (tangentNumerator f P).totalDegree ≤ P.totalDegree + (f.totalDegree - 1) := by
  unfold tangentNumerator
  apply (totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · have hs := partial_degree f 2
    have hl := lowerTangent_degree P
    apply (totalDegree_mul _ _).trans
    unfold separant
    omega
  · by_cases h : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C, mul_zero, totalDegree_zero]
      exact Nat.zero_le _
    · have hl := lowerTangent_degree f
      have hp := partial_degree P 2
      apply (totalDegree_mul _ _).trans
      omega
private theorem compatibility_degree (f : Row 3) (j : ℕ) :
    (compatibilityNumerator f j).totalDegree ≤ 1 + (2 * j + 1) * (f.totalDegree - 1) := by
  have hs : (separant f).totalDegree ≤ f.totalDegree - 1 := partial_degree f 2
  induction j with
  | zero =>
    rw [compatibilityNumerator, totalDegree_neg]
    have h := lowerTangent_degree f
    simp only [Nat.mul_zero, zero_add, one_mul]
    omega
  | succ j ih =>
    rw [compatibilityNumerator]
    let b := compatibilityNumerator f j
    change (separant f * tangentNumerator f b -
      ((2 * j + 1 : ℕ) : Row 3) * b * tangentNumerator f (separant f)).totalDegree ≤ _
    have h₁ := (totalDegree_mul (separant f) (tangentNumerator f b)).trans
      (Nat.add_le_add hs (tangent_degree f b))
    have h₂ := (totalDegree_mul (((2 * j + 1 : ℕ) : Row 3) * b)
      (tangentNumerator f (separant f))).trans
      (Nat.add_le_add (nat_mul_degree (2 * j + 1) b)
        ((tangent_degree f (separant f)).trans (Nat.add_le_add_right hs _)))
    have hstep := (totalDegree_sub _ _).trans (max_le h₁ (h₂.trans_eq (by omega)))
    change b.totalDegree ≤ _ at ih
    calc
      _ ≤ b.totalDegree + 2 * (f.totalDegree - 1) := by
        apply hstep.trans
        omega
      _ ≤ _ := by
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, Nat.add_mul]
        omega
theorem ordinary_bound (f : Row 3) :
    (K1_13_5_4.oldCut f).totalDegree ≤
      1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1) := by
  unfold K1_13_5_4.oldCut
  exact compatibility_degree f (taylorLength - 3)
end
end K1_13_5_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_7_5_3_3_3
noncomputable section
open K1_13_5_4_2_4 MvPolynomial
abbrev Ground := K1_13_5_4.GeometricX
abbrev Coeff (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
abbrev Universal (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientRing A)
def universalEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) : Universal A :=
  ∑ a : ↥(A i), monomial a.1 (MvPolynomial.X ⟨i, a⟩)
def cutPrefix {R : Type*} [CommRing R] (f : Fin 4 → R) (k : ℕ) : Ideal R :=
  Ideal.span (f '' {i : Fin 4 | (i : ℕ) < k})
private def IsPivot {A : Fin 4 → Finset Exponent} (k : ℕ) (v : Coeff A) : Prop :=
  v.1.val < k ∧ v.2.val = 0
private abbrev Pivot (A : Fin 4 → Finset Exponent) (k : ℕ) := {v : Coeff A // IsPivot k v}
private abbrev Other (A : Fin 4 → Finset Exponent) (k : ℕ) := {v : Coeff A // ¬IsPivot k v}
private abbrev Rest (A : Fin 4 → Finset Exponent) (k : ℕ) :=
  MvPolynomial (Fin 4 ⊕ Other A k) Ground
private def regroupIndex (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Fin 4 ⊕ Coeff A ≃ Pivot A k ⊕ (Fin 4 ⊕ Other A k) := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCompl (IsPivot k)).symm).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)))
private theorem regroupIndex_space (A : Fin 4 → Finset Exponent) (k : ℕ) (j : Fin 4) :
    regroupIndex A k (.inl j) = .inr (.inl j) := by
  simp [regroupIndex]
private theorem regroupIndex_pivot {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : IsPivot k v) : regroupIndex A k (.inr v) = .inl ⟨v, hv⟩ := by
  classical
  simp [regroupIndex, Equiv.sumCompl_symm_apply_of_pos hv]
private theorem regroupIndex_other {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : ¬IsPivot k v) : regroupIndex A k (.inr v) = .inr (.inr ⟨v, hv⟩) := by
  classical
  simp [regroupIndex, Equiv.sumCompl_symm_apply_of_neg hv]
private def regroup (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Universal A ≃ₐ[Ground] MvPolynomial (Pivot A k) (Rest A k) :=
  (sumAlgEquiv Ground (Fin 4) (Coeff A)).symm.trans
    ((renameEquiv Ground (regroupIndex A k)).trans (sumAlgEquiv Ground _ _))
private theorem regroup_space (A : Fin 4 → Finset Exponent) (k : ℕ) (j : Fin 4) :
    regroup A k (MvPolynomial.X j) = C (MvPolynomial.X (.inl j)) := by
  simp [regroup, renameEquiv_apply, regroupIndex_space]
private theorem regroup_pivot {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : IsPivot k v) : regroup A k (C (MvPolynomial.X v)) = MvPolynomial.X ⟨v, hv⟩ := by
  simp [regroup, renameEquiv_apply, regroupIndex_pivot hv]
private theorem regroup_other {A : Fin 4 → Finset Exponent} {k : ℕ} {v : Coeff A}
    (hv : ¬IsPivot k v) : regroup A k (C (MvPolynomial.X v)) = C (MvPolynomial.X (.inr ⟨v, hv⟩)) := by
  simp [regroup, renameEquiv_apply, regroupIndex_other hv]
private def pivotIndex {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) (hi : i.val < k) : Pivot A k :=
  ⟨⟨i, ⟨0, hz i⟩⟩, hi, rfl⟩
private theorem pivotIndex_surjective {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) :
    Function.Surjective (fun i : {i : Fin 4 // i.val < k} => pivotIndex hz i.val i.property) := by
  rintro ⟨⟨i, ⟨a, ha⟩⟩, hi, hzero⟩
  change a = 0 at hzero
  subst a
  exact ⟨⟨i, hi⟩, rfl⟩
private def remainingVariable {A : Fin 4 → Finset Exponent} (k : ℕ) (v : Coeff A) : Rest A k := by
  classical
  exact if h : IsPivot k v then 0 else MvPolynomial.X (.inr ⟨v, h⟩)
private def tail {A : Fin 4 → Finset Exponent} (k : ℕ)
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) : Rest A k :=
  ∑ a ∈ Finset.univ.erase (⟨0, hz i⟩ : ↥(A i)),
    remainingVariable k ⟨i, a⟩ * a.val.prod (fun j e => (MvPolynomial.X (.inl j) : Rest A k) ^ e)
private theorem regroup_equation {A : Fin 4 → Finset Exponent} {k : ℕ}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) (hi : i.val < k) :
    regroup A k (universalEquation A i) = MvPolynomial.X (pivotIndex hz i hi) + C (tail k hz i) := by
  classical
  unfold universalEquation tail
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, hz i⟩ : ↥(A i))), map_add,
    monomial_zero', regroup_pivot (show IsPivot k (⟨i, ⟨0, hz i⟩⟩ : Coeff A) from ⟨hi, rfl⟩),
    add_comm, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hn : ¬IsPivot k (⟨i, a⟩ : Coeff A) := by
    intro h
    exact (Finset.ne_of_mem_erase ha) (Subtype.ext h.2)
  simp only [monomial_eq, map_mul, regroup_other hn, remainingVariable, dite_eq_right hn]
  congr 1
  rw [Finsupp.prod, map_prod, Finsupp.prod, map_prod]
  simp [regroup_space]
private theorem evalSub_ker {B ι : Type*} [CommRing B] (s : ι → B) :
    RingHom.ker (aeval s : MvPolynomial ι B →ₐ[B] B).toRingHom =
      Ideal.span (Set.range fun i => MvPolynomial.X i - C (s i)) := by
  let I : Ideal (MvPolynomial ι B) := Ideal.span (Set.range fun i => MvPolynomial.X i - C (s i))
  change RingHom.ker (aeval s : MvPolynomial ι B →ₐ[B] B).toRingHom = I
  apply le_antisymm
  · intro f hf
    have h (p : MvPolynomial ι B) : p - C (aeval s p) ∈ I := by
      induction p using MvPolynomial.induction_on with
      | C b => simp
      | add p q hp hq =>
        simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
      | mul_X p i hp =>
        simp only [map_mul, aeval_X]
        have hi : MvPolynomial.X i - C (s i) ∈ I := Ideal.subset_span ⟨i, rfl⟩
        have he : p * MvPolynomial.X i - C (aeval s p * s i) =
            (p - C (aeval s p)) * MvPolynomial.X i + C (aeval s p) * (MvPolynomial.X i - C (s i)) := by
          rw [map_mul]
          ring
        rw [← map_mul, he]
        exact I.add_mem (I.mul_mem_right (MvPolynomial.X i) hp) (I.mul_mem_left _ hi)
    have hf' : aeval s f = 0 := hf
    simpa only [hf', map_zero, sub_zero] using h f
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
private def incidenceEquiv {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) (k : ℕ) :
    (Universal A ⧸ cutPrefix (universalEquation A) k) ≃ₐ[Ground] Rest A k := by
  let e := regroup A k
  let s : Pivot A k → Rest A k := fun v => -tail k hz v.val.1
  have hker := evalSub_ker s
  have hmap : Ideal.map e.toRingHom (cutPrefix (universalEquation A) k) =
      RingHom.ker (aeval s : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Rest A k] Rest A k).toRingHom := by
    rw [hker, cutPrefix, Ideal.map_span, Set.image_image]
    apply congrArg Ideal.span
    ext f
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨pivotIndex hz i hi, ?_⟩
      change MvPolynomial.X (pivotIndex hz i hi) - C (s (pivotIndex hz i hi)) =
        regroup A k (universalEquation A i)
      simpa only [s, pivotIndex, map_neg, sub_neg_eq_add] using (regroup_equation hz i hi).symm
    · rintro ⟨v, rfl⟩
      obtain ⟨⟨i, hi⟩, rfl⟩ := pivotIndex_surjective hz v
      refine ⟨i, hi, ?_⟩
      change regroup A k (universalEquation A i) =
        MvPolynomial.X (pivotIndex hz i hi) - C (s (pivotIndex hz i hi))
      simpa only [s, pivotIndex, map_neg, sub_neg_eq_add] using regroup_equation hz i hi
  let f : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Ground] Rest A k :=
    (aeval s : MvPolynomial (Pivot A k) (Rest A k) →ₐ[Rest A k] Rest A k).restrictScalars Ground
  have hsurj : Function.Surjective f := fun b => ⟨C b, aeval_C s b⟩
  let q := Ideal.quotientEquivAlg (cutPrefix (universalEquation A) k) (RingHom.ker f.toRingHom) e hmap.symm
  exact q.trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
private theorem universalPrefix_prime {A : Fin 4 → Finset Exponent}
    (hz : ∀ i, 0 ∈ A i) (k : ℕ) : (cutPrefix (universalEquation A) k).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  let e := (incidenceEquiv hz k).toRingEquiv
  exact e.toMulEquiv.isDomain
private theorem universalEquation_not_mem {A : Fin 4 → Finset Exponent}
    (hz : ∀ i, 0 ∈ A i) (i : Fin 4) :
    universalEquation A i ∉ cutPrefix (universalEquation A) i.val := by
  classical
  let v : Coeff A → Ground := fun j => if j.1 = i then 1 else 0
  let ev := (eval v).comp (constantCoeff : Universal A →+* CoefficientRing A)
  have h (j : Fin 4) : ev (universalEquation A j) = v ⟨j, ⟨0, hz j⟩⟩ := by
    unfold universalEquation
    rw [map_sum, Finset.sum_eq_single (⟨0, hz j⟩ : ↥(A j))]
    · simp [ev, monomial_zero']
    · intro a _ ha
      have ha' : a.val ≠ 0 := fun ha' => ha (Subtype.ext ha')
      simp [ev, constantCoeff_monomial, ha']
    · simp
  have hle : cutPrefix (universalEquation A) i.val ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change j.val < i.val at hj
    have hji : j ≠ i := fun he => (ne_of_lt hj) (congrArg Fin.val he)
    change ev (universalEquation A j) = 0
    rw [h]
    simp [v, hji]
  intro hi
  have h0 : ev (universalEquation A i) = 0 := hle hi
  simp [h, v] at h0
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Affine (A : Fin 4 → Finset Exponent) := MvPolynomial (Fin 4) (CoefficientField A)
private abbrev Denoms (A : Fin 4 → Finset Exponent) :=
  (nonZeroDivisors (CoefficientRing A)).map (C (σ := Fin 4))
private theorem map_universalEquation (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    algebraMap (Universal A) (Affine A) (universalEquation A i) = genericEquation A i := by
  rw [MvPolynomial.algebraMap_def, universalEquation, genericEquation, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact MvPolynomial.map_monomial _ _ _
private theorem map_cutPrefix (A : Fin 4 → Finset Exponent) (k : ℕ) :
    Ideal.map (algebraMap (Universal A) (Affine A)) (cutPrefix (universalEquation A) k) =
      cutPrefix (genericEquation A) k := by
  simp only [cutPrefix, Ideal.map_span, Set.image_image, map_universalEquation]
theorem generic_prefix_regular {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i)
    (i : Fin 4) (p : Affine A) :
    genericEquation A i * p ∈ cutPrefix (genericEquation A) i.val →
      p ∈ cutPrefix (genericEquation A) i.val := by
  intro hp
  let J := cutPrefix (universalEquation A) i.val
  obtain ⟨q, s, rfl⟩ := IsLocalization.exists_mk'_eq (Denoms A) p
  rw [← map_cutPrefix] at hp ⊢
  change _ ∈ Ideal.map _ J at hp ⊢
  have hq : algebraMap (Universal A) (Affine A) (universalEquation A i * q) ∈
      Ideal.map (algebraMap (Universal A) (Affine A)) J := by
    rw [map_mul, map_universalEquation, ← IsLocalization.mk'_spec (Affine A) q s, ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hp
  obtain ⟨d, hd, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Denoms A) _ J _).mp hq
  rw [mul_left_comm] at hmem
  have hprime := universalPrefix_prime hz i.val
  exact (IsLocalization.mk'_mem_map_algebraMap_iff (Denoms A) _ J q s).mpr
    ⟨d, hd, (hprime.mem_or_mem hmem).resolve_left (universalEquation_not_mem hz i)⟩
private theorem cutPrefix_four {R : Type*} [CommRing R] (f : Fin 4 → R) :
    cutPrefix f 4 = Ideal.span (Set.range f) := by
  rw [cutPrefix, show {i : Fin 4 | i.val < 4} = Set.univ from Set.eq_univ_of_forall Fin.isLt,
    Set.image_univ]
private def pivotEquiv {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Fin 4 ≃ Pivot A 4 :=
  Equiv.ofBijective (fun i => pivotIndex hz i i.isLt) ⟨fun _ _ h => congrArg (fun x => x.val.1) h,
    fun v => by
      obtain ⟨⟨i, _⟩, rfl⟩ := pivotIndex_surjective hz v
      exact ⟨i, rfl⟩⟩
private theorem incidence_trdeg {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Algebra.trdeg Ground (Universal A ⧸ cutPrefix (universalEquation A) 4) = Cardinal.mk (Coeff A) := by
  classical
  rw [(incidenceEquiv hz 4).trdeg_eq, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
  exact Cardinal.mk_congr ((Equiv.sumCongr (pivotEquiv hz) (Equiv.refl _)).trans
    (Equiv.sumCompl (IsPivot 4)))
private theorem fraction_trdeg (A : Fin 4 → Finset Exponent) :
    Algebra.trdeg Ground (CoefficientField A) = Cardinal.mk (Coeff A) := by
  let : Algebra.IsAlgebraic (CoefficientRing A) (CoefficientField A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoefficientRing A))
  rw [← trdeg_add_eq Ground (CoefficientRing A), trdeg_eq_zero (R := CoefficientRing A), add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]
private theorem trdeg_localized_quotient {F U S : Type} [Field F] [CommRing U] [CommRing S]
    [Algebra F U] [Algebra U S] [Algebra F S] [IsScalarTower F U S]
    (M : Submonoid U) [IsLocalization M S] (J : Ideal U) (hprime : J.IsPrime)
    (hdis : Disjoint (M : Set U) (J : Set U)) :
    Algebra.trdeg F (S ⧸ Ideal.map (algebraMap U S) J) = Algebra.trdeg F (U ⧸ J) := by
  let B := U ⧸ J
  let I := Ideal.map (algebraMap U S) J
  let G := S ⧸ I
  let : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S J hprime hdis
  let : J.IsPrime := hprime
  let f : B →+* G := Ideal.quotientMap I (algebraMap U S) Ideal.le_comap_map
  have hf (u : U) : f (Ideal.Quotient.mk J u) = Ideal.Quotient.mk I (algebraMap U S u) := rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hf, hf, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, ← Ideal.mem_comap] at hab
    change a - b ∈ I.under U at hab
    rw [show I.under U = J from IsLocalization.under_map_of_isPrime_disjoint M S hprime hdis] at hab
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hab
  let : Algebra B G := RingHom.toAlgebra (R := B) (S := G) f
  let : IsScalarTower F B G := IsScalarTower.of_algebraMap_eq fun a => by
    change Ideal.Quotient.mk I (algebraMap F S a) = f (Ideal.Quotient.mk J (algebraMap F U a))
    rw [hf, IsScalarTower.algebraMap_apply F U S]
  let : FaithfulSMul B G := (faithfulSMul_iff_algebraMap_injective B G).mpr hfinj
  let : Algebra.IsAlgebraic B G := ⟨fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨q, s⟩, hs⟩ := IsLocalization.surj M p
    let a := Ideal.Quotient.mk J q
    let b := Ideal.Quotient.mk J s.val
    have hb : b ≠ 0 := fun hb => Set.disjoint_left.mp hdis s.property
      (Ideal.Quotient.eq_zero_iff_mem.mp hb)
    have hq : Ideal.Quotient.mk I p * f b = f a := by
      simp only [a, b, hf, ← map_mul, hs]
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, ?_, ?_⟩
    · intro h0
      have h := congrArg (fun P : Polynomial B => P.coeff 1) h0
      have hb1 : (Polynomial.C b * (Polynomial.X : Polynomial B)).coeff 1 = b := by
        rw [Polynomial.coeff_C_mul_X, ite_eq_left rfl]
      have ha1 : (Polynomial.C a).coeff 1 = 0 := by
        rw [Polynomial.coeff_C, ite_eq_right Nat.one_ne_zero]
      change (Polynomial.C b * Polynomial.X - Polynomial.C a).coeff 1 = (0 : Polynomial B).coeff 1 at h
      rw [Polynomial.coeff_sub, hb1, ha1, sub_zero, Polynomial.coeff_zero] at h
      exact hb h
    · let ev : Polynomial B →ₐ[B] G := Polynomial.aeval (Ideal.Quotient.mk I p)
      change ev (Polynomial.C b * Polynomial.X - Polynomial.C a) = 0
      have hC (c : B) : ev (Polynomial.C c) = f c := ev.commutes c
      have hX : ev Polynomial.X = Ideal.Quotient.mk I p := Polynomial.aeval_X _
      rw [map_sub, map_mul, hC, hC, hX, mul_comm, hq, sub_self]⟩
  change Algebra.trdeg F G = Algebra.trdeg F B
  rw [← trdeg_add_eq F B, trdeg_eq_zero (R := B), add_zero]
theorem generic_finite {A : Fin 4 → Finset Exponent} (hz : ∀ i, 0 ∈ A i) :
    Module.Finite (CoefficientField A) (GenericQuotient A) := by
  classical
  let J := cutPrefix (universalEquation A) 4
  let S := Affine A
  let U := Universal A
  let M := Denoms A
  let I := Ideal.span (Set.range (genericEquation A))
  let G := S ⧸ I
  have hI : Ideal.map (algebraMap U S) J = I := (map_cutPrefix A 4).trans (cutPrefix_four _)
  by_cases htop : I = ⊤
  · let : Subsingleton G := Ideal.Quotient.subsingleton_iff.mpr htop
    exact Module.Finite.of_finite (R := CoefficientField A) (M := G)
  have hprime : J.IsPrime := universalPrefix_prime hz 4
  have hdis : Disjoint (M : Set U) (J : Set U) := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint M S J).mp
    rwa [hI]
  let : I.IsPrime := hI ▸ IsLocalization.isPrime_of_isPrime_disjoint M S J hprime hdis
  let : IsScalarTower Ground U S := IsScalarTower.of_algebraMap_eq fun a => by
    change C (algebraMap Ground (CoefficientField A) a) = algebraMap U S (C (C a))
    rw [MvPolynomial.algebraMap_def, map_C]
    rfl
  have htrG : Algebra.trdeg Ground G = Cardinal.mk (Coeff A) := by
    have h := trdeg_localized_quotient (F := Ground) (S := S) M J hprime hdis
    rw [hI] at h
    exact h.trans (incidence_trdeg hz)
  have htr := trdeg_add_eq Ground (CoefficientField A) (A := G)
  rw [fraction_trdeg, htrG, Cardinal.add_eq_left_iff] at htr
  have hztr : Algebra.trdeg (CoefficientField A) G = 0 := by
    refine htr.resolve_left ?_
    intro h
    exact (Cardinal.mk_lt_aleph0 (α := Coeff A)).not_ge ((le_max_left _ _).trans h)
  let : Algebra.IsIntegral (CoefficientField A) G := ⟨fun x => isAlgebraic_iff_isIntegral.mp
    ((trdeg_eq_zero_iff.mp hztr).isAlgebraic x)⟩
  exact Algebra.IsIntegral.finite (R := CoefficientField A) (A := G)
end
end K1_13_7_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_2_2
noncomputable section
open Algebra KaehlerDifferential MvPolynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin
private theorem trdeg_fractionRing_of_finite {k P A : Type} [Field k]
    [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Algebra k P] [Algebra k A] {ι : Type} {v : ι → P}
    (hv : IsTranscendenceBasis k v) (g : P →ₐ[k] A)
    (hg : Function.Injective g) (hgfin : g.Finite) :
    trdeg k (FractionRing A) = Cardinal.mk ι := by
  let K := FractionRing A
  let _ : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower k P A := .of_algebraMap_eq fun a => (g.commutes a).symm
  have : IsScalarTower k P K := IsScalarTower.to₁₂₄ k P A K
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : Module.Finite P A := hgfin
  have : Algebra.IsAlgebraic P K := (IsFractionRing.isAlgebraic_iff' P A K).mp inferInstance
  exact (hv.algebraMap_comp (A := K)).cardinalMk_eq_trdeg.symm
private theorem curve_trdeg {k σ : Type} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (hd : (affineHilbertPolynomial I).natDegree = 1) :
    trdeg k (FractionRing (MvPolynomial σ k ⧸ I)) = 1 := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hd' : d = 1 := by
    simpa using (natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
      g hgfin hg).symm.trans hd
  simpa [hd'] using trdeg_fractionRing_of_finite
    (IsTranscendenceBasis.mvPolynomial (Fin d) k) g hg hgfin
private theorem differential_finrank {k K : Type} [Field k] [Field K] [Algebra k K]
    [PerfectField k] [EssFiniteType k K] (ht : trdeg k K = 1) :
    Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : Fintype.card s = 1 := by
    have h := hs.cardinalMk_eq_trdeg.trans ht
    rw [Cardinal.mk_fintype] at h
    exact_mod_cast h
  let v : s → K := (↑)
  have hv : Set.range v = (s : Set K) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← hv] at hsep
  let P := MvPolynomial s k
  let A := Algebra.adjoin k (Set.range v)
  let E := IntermediateField.adjoin k (Set.range v)
  let e : P ≃ₐ[k] A := hs.1.aevalEquiv
  let _ : Algebra P E := ((algebraMap A E).comp e.toRingHom).toAlgebra
  let _ : Algebra P K := ((algebraMap E K).comp (algebraMap P E)).toAlgebra
  have : IsScalarTower P E K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k P K := .of_algebraMap_eq fun a => by
    change algebraMap k K a = algebraMap E K (algebraMap A E (e (algebraMap k P a)))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply k A E,
      ← IsScalarTower.algebraMap_apply k E K]
  have : IsFractionRing P E := IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _ => rfl
  have : Algebra.FormallyEtale P E := Algebra.FormallyEtale.of_isLocalization
    (nonZeroDivisors P)
  have : Algebra.IsSeparable E K := hsep
  have : Algebra.FormallyEtale E K := Algebra.FormallyEtale.of_isSeparable E K
  have : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P E K
  let b := ((mvPolynomialBasis k s).baseChange K).map
    (tensorKaehlerEquivOfFormallyEtale k P K)
  exact (Module.finrank_eq_card_basis b).trans hcard
private theorem separates_over_intermediate {k E K : Type} [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K] [EssFiniteType E K]
    (z : E) (hd : Module.finrank K Ω[K⁄k] = 1)
    (hu : D k K (algebraMap E K z) ≠ 0) : Algebra.IsSeparable E K := by
  apply (Algebra.FormallyUnramified.iff_isSeparable (K := E) K).mp
  constructor
  let m := KaehlerDifferential.map k E K K
  have hm : m (D k K (algebraMap E K z)) = 0 := by
    simpa only [m, map_D, Algebra.algebraMap_self_apply] using (D E K).map_algebraMap z
  apply (subsingleton_iff_forall_eq 0).mpr
  intro y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective k E K y
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one hd hu x
  change m (t • D k K (algebraMap E K z)) = 0
  rw [map_smul, hm, smul_zero]
private theorem separates_of_nonzero_differential {k K : Type} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] [EssFiniteType k K] (u : K)
    (hd : Module.finrank K Ω[K⁄k] = 1) (hu : D k K u ≠ 0) :
    Transcendental k u ∧ Algebra.IsSeparable (IntermediateField.adjoin k {u}) K := by
  let E := IntermediateField.adjoin k ({u} : Set K)
  have humem : u ∈ E := IntermediateField.mem_adjoin_simple_self k u
  have htrans : Transcendental k u := by
    intro ha
    have : Algebra.IsAlgebraic k E :=
      IntermediateField.isAlgebraic_adjoin_simple (isAlgebraic_iff_isIntegral.mp ha)
    have hbot : E = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic E
    rw [hbot] at humem
    obtain ⟨t, ht⟩ := (IntermediateField.mem_bot.mp humem)
    exact hu (ht ▸ (D k K).map_algebraMap t)
  refine ⟨htrans, ?_⟩
  have : EssFiniteType E K := EssFiniteType.of_comp k E K
  exact separates_over_intermediate (⟨u, humem⟩ : E) hd hu
set_option maxHeartbeats 600000 in
theorem proof : K1_13_5_4_2_2.c2 := by
  classical
  intro k σ _ _ _ I hI hd
  have : I.IsPrime := hI
  let A := MvPolynomial σ k ⧸ I
  let K := FractionRing A
  let f : MvPolynomial σ k →ₐ[k] K :=
    (IsScalarTower.toAlgHom k A K).comp (Ideal.Quotient.mkₐ k I)
  have : EssFiniteType A K := EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  have : EssFiniteType k K := EssFiniteType.comp k A K
  have hr : Module.finrank K Ω[K⁄k] = 1 := differential_finrank (curve_trdeg I hd)
  let _ : Fintype σ := Fintype.ofFinite σ
  let L : (σ → k) →ₗ[k] Ω[K⁄k] := {
    toFun := fun a => ∑ i, a i • D k K (f (MvPolynomial.X i))
    map_add' := by
      intro a b
      simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro t a
      simp [smul_smul, Finset.smul_sum] }
  refine ⟨L.ker, ?_, ?_⟩
  · intro htop
    have hX (i : σ) : D k K (f (MvPolynomial.X i)) = 0 := by
      have h : L (Pi.single i 1) = 0 := LinearMap.mem_ker.mp (htop.symm ▸ Submodule.mem_top)
      simpa [L, Pi.single_apply] using h
    have hp (p : MvPolynomial σ k) : D k K (f p) = 0 := by
      induction p using MvPolynomial.induction_on with
      | C t =>
        rw [← MvPolynomial.algebraMap_eq, f.commutes]
        exact (D k K).map_algebraMap t
      | add p q hp hq => simp only [map_add, hp, hq, add_zero]
      | mul_X p i hp => simp only [map_mul, Derivation.leibniz, hp, hX, smul_zero, add_zero]
    have hA (x : A) : D k K (algebraMap A K x) = 0 := by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hp p
    have hK (x : K) : D k K x = 0 := by
      obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective A x
      simp [Derivation.leibniz_div, hA]
    have hle : (⊤ : Submodule K Ω[K⁄k]) ≤ ⊥ := by
      rw [← span_range_derivation k K, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simpa using hK x
    have : Subsingleton Ω[K⁄k] := (subsingleton_iff_forall_eq 0).mpr fun x =>
      (Submodule.mem_bot K).mp (hle (Submodule.mem_top : x ∈ ⊤))
    exact Nat.zero_ne_one ((Module.finrank_zero_of_subsingleton (R := K) (M := Ω[K⁄k])).symm.trans hr)
  · intro a ha
    have hL : L a = D k K (f (K1_13_5_4_2_2.linearForm a)) := by
      change (∑ i, a i • D k K (f (MvPolynomial.X i))) =
        D k K (f (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i))
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← MvPolynomial.algebraMap_eq, ← Algebra.smul_def, map_smul, (D k K).map_smul]
    have hn : D k K (f (K1_13_5_4_2_2.linearForm a)) ≠ 0 := by
      rw [← hL]
      exact fun hz => ha (LinearMap.mem_ker.mpr hz)
    exact separates_of_nonzero_differential _ hr hn
end
end K1_13_5_4_2_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4_2 K1_13_5_4_2_5 MeasureTheory Filter
open scoped BigOperators Pointwise Topology
def c1 : Prop :=
  ∀ P : Set ExponentSpace, FirstBody P → P ⊆ capBody lowBox 0 →
    ∃ p : MvPolynomial (Fin 4) ℝ, p.IsHomogeneous 4 ∧
      ∀ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) →
        p.eval w = (volume (∑ i, w i • slots P i)).toReal
def c2 : Prop :=
  ∀ P : Set ExponentSpace, FirstBody P → P ⊆ capBody lowBox 0 →
    ∀ (s : Shape) (h : ℕ), Chamber s → s.j < s.b → 0 < s.t → 0 < h →
      Tendsto (volumeQuotient P (capBody s h)) (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 (capFirstVariation s h (totalSupport P) (indexSupport P) (topSupport P)))
private def sumShape (S : Finset (Fin 4)) : Shape :=
  ⟨∑ i ∈ S, (slotShape i).b, ∑ i ∈ S, (slotShape i).j, ∑ i ∈ S, (slotShape i).t⟩
private def sumHeight (S : Finset (Fin 4)) : ℕ := ∑ i ∈ S, slotHeight i
private def base (S : Finset (Fin 4)) : Set ExponentSpace := capBody (sumShape S) (sumHeight S)
private theorem slot_chamber (i : Fin 4) : Chamber (slotShape i) := by
  fin_cases i <;> exact ⟨by decide, by decide⟩
private theorem sum_chamber (S : Finset (Fin 4)) : Chamber (sumShape S) := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => (slot_chamber i).1)
  · change 2 * (∑ i ∈ S, (slotShape i).t) ≤ ∑ i ∈ S, (slotShape i).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (slot_chamber i).2)
private theorem cap_zero : capBody ⟨0, 0, 0⟩ 0 = 0 := by
  ext x
  rw [Set.mem_zero]
  constructor
  · intro hx
    obtain ⟨hx, hb, _, _, hh⟩ := hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    norm_num at hb hh
    funext i
    change x i = 0
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
    · change x 2 = 0
      linarith
    · change x 3 = 0
      linarith
  · rintro rfl
    simp [capBody]
private theorem sum_caps (S : Finset (Fin 4)) :
    (∑ i ∈ S, capBody (slotShape i) (slotHeight i)) = base S := by
  induction S using Finset.induction_on with
  | empty => simp [base, sumShape, sumHeight, cap_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, ih, base, ← capBody_add (slot_chamber i) (sum_chamber S)]
    simp only [base, sumShape, sumHeight, Shape.plus, Finset.sum_insert hi]
private theorem sum_slots (P : Set ExponentSpace) {S : Finset (Fin 4)} (h0 : 0 ∉ S) :
    (∑ i ∈ S, slots P i) = base S := by
  rw [← sum_caps]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
  simp [slots, Function.update_of_ne hne]
private theorem slots_nonempty (P : Set ExponentSpace) (hP : FirstBody P)
    (i : Fin 4) : (slots P i).Nonempty := by
  refine ⟨0, ?_⟩
  by_cases hi : i = 0
  · simpa [slots, hi] using hP.zero_mem
  · simp [slots, Function.update_of_ne hi, capBody]
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
private theorem volume_zero_height {A : Set ExponentSpace} (hA : ∀ x ∈ A, x 3 = 0) :
    volume A = 0 := by
  let fibers (i : Fin 4) : Set ℝ := if i = 3 then {0} else Set.univ
  have hsub : A ⊆ Set.pi Set.univ fibers := by
    intro x hx
    refine Set.mem_pi.mpr (fun i _ => ?_)
    by_cases hi : i = 3
    · simpa [fibers, hi] using hA x hx
    · simp [fibers, hi]
  have hz : volume (Set.pi Set.univ fibers) = 0 := by
    rw [volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ (3 : Fin 4)) (by simp [fibers])
  exact le_antisymm ((measure_mono hsub).trans_eq hz) bot_le
private theorem empty_quotient (P : Set ExponentSpace) (hP : FirstBody P) (t : ℝ) :
    volumeQuotient P (base ∅) t = 0 := by
  have hbase : base ∅ = 0 := by simp [base, sumShape, sumHeight, cap_zero]
  have hPz : volume (t • P) = 0 := by
    apply volume_zero_height
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    simp [Pi.smul_apply, hP.zero_height y hy]
  rw [volumeQuotient, hbase, add_zero, hPz,
    show (0 : Set ExponentSpace) = {0} by rfl]
  simp
private theorem tendsto_quotient (h : c2) (P : Set ExponentSpace)
    (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) {S : Finset (Fin 4)} (hS : S ⊆ rest) :
    Tendsto (volumeQuotient P (base S)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (capFirstVariation (sumShape S) (sumHeight S)
        (totalSupport P) (indexSupport P) (topSupport P))) := by
  by_cases he : S = ∅
  · subst S
    rw [show volumeQuotient P (base ∅) = (fun _ : ℝ => 0) from funext (empty_quotient P hP)]
    simp [capFirstVariation, sumShape, sumHeight]
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    apply h P hP hsub _ _ (sum_chamber S)
    · exact Finset.sum_lt_sum_of_nonempty hn (fun i _ => by fin_cases i <;> decide)
    · exact Finset.sum_pos (fun i _ => by fin_cases i <;> decide) hn
    · apply Finset.sum_pos _ hn
      intro i hi
      have hne : i ≠ 0 := fun h0 => zero_notMem_rest (h0 ▸ hS hi)
      fin_cases i
      · exact (hne rfl).elim
      all_goals decide
private theorem variation_eq (h1 : c1) (h2 : c2) (P : Set ExponentSpace)
    (hP : FirstBody P) (hsub : P ⊆ capBody lowBox 0) :
    lastMixedVolume P =
      ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        capFirstVariation (sumShape S) (sumHeight S)
          (totalSupport P) (indexSupport P) (topSupport P) := by
  obtain ⟨p, hp, heval⟩ := h1 P hP hsub
  have hlim := tendsto_finsetSum rest.powerset (fun S hS =>
    (tendsto_quotient h2 P hP hsub (Finset.mem_powerset.mp hS)).const_mul
      ((-1 : ℝ) ^ (3 - S.card)))
  have heq : (fun _ : ℝ => lastMixedVolume P) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun t : ℝ => ∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
        volumeQuotient P (base S) t) := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht
    have ht' : 0 < t := ht
    have hscale := mixed_scale P (slots_nonempty P hP) p hp heval t ht'.le
    have hquot : lastMixedVolume (t • P) / t = lastMixedVolume P := by
      rw [hscale]
      exact mul_div_cancel_left₀ _ ht'.ne'
    calc
      lastMixedVolume P = lastMixedVolume (t • P) / t := hquot.symm
      _ = _ := by simp only [mixed_increment, Finset.sum_div, volumeQuotient, mul_div_assoc]
  exact tendsto_const_nhds_iff.mp (hlim.congr' heq.symm)
private theorem native_coefficients (B J T : ℝ) :
    (∑ S ∈ rest.powerset, (-1 : ℝ) ^ (3 - S.card) *
      capFirstVariation (sumShape S) (sumHeight S) B J T) =
        66110561798309 * B + 218611499353422 * J + 3394882488110 * T := by
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a := (1 : Fin 4)) (s := insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a := (2 : Fin 4)) (s := insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a := (3 : Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  norm_num [capFirstVariation, sumShape, sumHeight, slotShape, slotHeight,
    liftedBox, taylorLength, Finset.sum_insert, Finset.card_insert_of_notMem]
  ring
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_5.c2 := by
  intro P hP hsub
  rw [variation_eq h1 h2 P hP hsub, native_coefficients, native_box_price capBody_volume]
  have hB : totalSupport P ≤ (lowBox.b : ℝ) := by
    apply csSup_le ((Set.nonempty_of_mem hP.zero_mem).image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2.1
  have hJ : indexSupport P ≤ (lowBox.j : ℝ) := by
    apply csSup_le ((Set.nonempty_of_mem hP.zero_mem).image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2.2.1
  have hT : topSupport P ≤ (lowBox.t : ℝ) := by
    apply csSup_le ((Set.nonempty_of_mem hP.zero_mem).image _)
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2.2.2.1
  have hbudget : (mixedBudget : ℝ) = 18508096564475976 := by
    norm_num [mixedBudget, mixed3, volumeTerm, liftedBox, taylorLength]
  rw [hbudget]
  change totalSupport P ≤ 120 at hB
  change indexSupport P ≤ 48 at hJ
  change topSupport P ≤ 24 at hT
  linarith
end
end K1_13_5_4_2_5_2
end
section
namespace K1_14_2_5
noncomputable section
open K1_13 K1_13_5 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
def firstView (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] (MvPolynomial (Fin 1) R)[X] :=
  (renameEquiv R finSuccEquivLast).trans (optionEquivLeft R (Fin 1))
private abbrev valueView : Row 1 ≃ₐ[Geom[X]] Geom[X][X] :=
  uniqueAlgEquiv Geom[X] (Fin 1)
private theorem firstView_degree (f : Row 2) : (firstView Geom[X] f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)
private theorem firstView_pderiv (f : Row 2) :
    firstView Geom[X] (pderiv 1 f) = (firstView Geom[X] f).derivative := by
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
    ((firstView Geom[X] f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
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
    k + (valueView ((firstView Geom[X] f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le Geom[X] (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)
private def eliminant (f : Row 2) : Geom[X][X] :=
  let A := firstView Geom[X] f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)
set_option maxHeartbeats 600000 in
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) {B : ℕ} (hB : 2 ≤ B)
    (hchar : B < K1.p) (hb : f.totalDegree ≤ B) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * (B - 1) ∧
      ∀ S : Geom[X], atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView Geom[X] f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView Geom[X] f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ (firstView Geom[X]).injective).mpr hf.ne_zero
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
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt hchar)))
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
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map (firstView Geom[X])) hder
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
            rw [show A.derivative = firstView Geom[X] (pderiv 1 f) from (firstView_pderiv f).symm]
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
        (by simpa using Nat.mul_le_mul_left b (by omega : 1 ≤ B - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h
theorem factor_cover (q : Row 2) {B J : ℕ} (hq : q ≠ 0) (hB : 2 ≤ B)
    (hchar : B < K1.p) (hb : q.totalDegree ≤ B) (hj : q.degreeOf 1 ≤ J) :
    ∃ (A : Finset (Row 2)) (u : Geom[X][X]),
      (∀ g ∈ A, Irreducible g ∧ 0 < g.degreeOf 1) ∧
      (∑ g ∈ A, g.totalDegree) ≤ B ∧ (∑ g ∈ A, g.degreeOf 1) ≤ J ∧
      u ≠ 0 ∧ u.natDegree ≤ B * (B - 1) ∧
      ∀ S : Geom[X], atJet q S = 0 → u.eval S = 0 ∨ ∃ g ∈ A, RegularAt 1 g S := by
  classical
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ B := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hb
  have hT : ∀ g ∈ T, Irreducible g ∧ 0 < g.degreeOf 1 := fun g hg =>
    ⟨hA g (Finset.mem_filter.mp hg).1, (Finset.mem_filter.mp hg).2⟩
  have hJ : (∑ g ∈ T, g.degreeOf 1) ≤ J := by
    obtain ⟨r, hr⟩ := (Finset.prod_dvd_prod_of_subset T A id
      (Finset.filter_subset _ _)).trans hdiv
    have hprod := Finset.prod_ne_zero_iff.mpr fun g hg => (hT g hg).1.ne_zero
    have hr0 : r ≠ 0 := fun hh => hq (by simp [hr, hh])
    simp only [id_eq] at hr
    have hb' := hj
    rw [hr, degreeOf_mul_eq hprod hr0, degreeOf_prod_eq T (fun g => g)
      (fun g hg => (hT g hg).1.ne_zero)] at hb'
    exact (Nat.le_add_right _ _).trans hb'
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) hB hchar
      ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨T, u, hT, ?_, hJ, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun g _ _ => Nat.zero_le g.totalDegree)).trans hcap
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * (B - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ B * (B - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq).symm.dvd
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
    · exact Or.inr ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩, hreg⟩
end
end K1_14_2_5
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4 MvPolynomial
def c1 : Prop :=
  ∀ (L : Type) [Field L] [Algebra GeometricX L]
    (I : Ideal (GeoRow 4)) (y : JetPoint), pointIdeal y ∈ I.minimalPrimes →
    rationalIdeal (extendPoint L y) ∈ (extendIdeal L I).minimalPrimes ∧
      Module.Finite L (PointAlgebra (extendIdeal L I) (extendPoint L y)) ∧
      Module.finrank L (PointAlgebra (extendIdeal L I) (extendPoint L y)) =
        (pointLength I y).toNat
def c2 : Prop :=
  ∀ (L : Type) [Field L] [Infinite L] (g : Fin 4 → Total L) (y : Fin 4 → L),
    rationalIdeal y ∈ (equationsIdeal fun i => reduce (g i)).minimalPrimes →
    IsSMulRegular (BranchAlgebra g y) (branchParameter g y)
private theorem branch_sum_bound {L : Type} [Field L] [Infinite L] (h : c2)
    (g : Fin 4 → Total L) {ι : Type} [Fintype ι] (y : ι → Fin 4 → L)
    (hy : Function.Injective y)
    (hmin : ∀ i, rationalIdeal (y i) ∈ (equationsIdeal fun j => reduce (g j)).minimalPrimes)
    (hlocal : ∀ i, Module.Finite L (PointAlgebra (equationsIdeal fun j => reduce (g j)) (y i)))
    [Module.Finite (ParameterField L) (GenericFiber g)] :
    (∑ i, Module.finrank L (PointAlgebra (equationsIdeal fun j => reduce (g j)) (y i))) ≤
      Module.finrank (ParameterField L) (GenericFiber g) := by
  let I := equationsIdeal (fun j => reduce (g j))
  let s := AlgHom.pi fun i => pointClass I (y i)
  have hs : Function.Surjective s := points_surjective I y hy hmin
  have hrel (p : Total L) (hp : genericClass g p = 0) : s (reduce p) = 0 := by
    funext i
    exact relation_vanishes g (y i) (h L g (y i) (hmin i)) p hp
  let pointModules : ∀ i : ι, Module L (PointAlgebra I (y i)) :=
    fun i => inferInstance
  let : Module L ((i : ι) → PointAlgebra I (y i)) := Pi.module ι _ L
  let : ∀ i : ι, Module.Free L (PointAlgebra I (y i)) := fun i => inferInstance
  let : ∀ i : ι, Module.Finite L (PointAlgebra I (y i)) := hlocal
  let s' : Affine L →ₗ[L] ((i : ι) → PointAlgebra I (y i)) := s.toLinearMap
  have hr : Module.finrank L ((i : ι) → PointAlgebra I (y i)) ≤
      Module.finrank (ParameterField L) (GenericFiber g) := by
    refine specialization_rank (L := L) (D := (i : ι) → PointAlgebra I (y i)) g s' ?_ ?_
    · exact hs
    · exact hrel
  rw [Module.finrank_pi_fintype] at hr
  exact hr
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4_2_4.c1 := by
  classical
  intro A _ hfinite f hsupport points hpoints
  let L := CoefficientField A
  have : Infinite L := Infinite.of_injective (algebraMap GeometricX L) (RingHom.injective _)
  let g := deformation A f
  let I := equationsIdeal (fun i => reduce (g i))
  let y : ↥points → Fin 4 → L := fun i => extendPoint L i.1
  have hI : I = extendIdeal L (cutIdeal f) := deformation_reduce A f hsupport
  have hlocal (i : ↥points) :
      rationalIdeal (y i) ∈ I.minimalPrimes ∧
        Module.Finite L (PointAlgebra I (y i)) ∧
        Module.finrank L (PointAlgebra I (y i)) =
          (pointLength (cutIdeal f) i.1).toNat := by
    rw [hI]
    exact h1 L (cutIdeal f) i.1 (hpoints i.1 i.2)
  have hy : Function.Injective y := by
    intro i j hij
    apply Subtype.ext
    funext a
    exact (RingHom.injective (algebraMap GeometricX L)) (congrFun hij a)
  obtain ⟨hfin, hrank⟩ := deformation_generic A f hfinite
  have := hfin
  have h := branch_sum_bound h2 g y hy (fun i => (hlocal i).1) (fun i => (hlocal i).2.1)
  rw [hrank] at h
  calc
    (∑ z ∈ points, (pointLength (cutIdeal f) z).toNat) =
        ∑ i : ↥points, Module.finrank L (PointAlgebra I (y i)) := by
      rw [← Finset.sum_attach points (fun z => (pointLength (cutIdeal f) z).toNat)]
      exact Finset.sum_congr rfl fun i _ => (hlocal i).2.2.symm
    _ ≤ _ := h
end
end K1_13_5_4_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_3_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
def contracted (P : Ideal (GeoRow 3)) : Ideal (Row 3) :=
  P.comap (MvPolynomial.map genericCoeff)
abbrev LocalRows (f : Row 3) := Localization.Away (separant f)
def localRowsMap (f : Row 3) : Row 3 →+* LocalRows f := algebraMap _ _
def localContraction (f : Row 3) (P : Ideal (GeoRow 3)) : Ideal (LocalRows f) :=
  (contracted P).map (localRowsMap f)
def Chart (f : Row 3) (P : Ideal (GeoRow 3)) := LocalRows f ⧸ localContraction f P
instance chartCommRing (f : Row 3) (P : Ideal (GeoRow 3)) : CommRing (Chart f P) :=
  inferInstanceAs (CommRing (LocalRows f ⧸ localContraction f P))
def chartEval (f : Row 3) (P : Ideal (GeoRow 3)) : Row 3 →+* Chart f P :=
  show Row 3 →+* (LocalRows f ⧸ localContraction f P) from
    (Ideal.Quotient.mk (localContraction f P)).comp (localRowsMap f)
def invSep (f : Row 3) (P : Ideal (GeoRow 3)) : Chart f P :=
  Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f))
theorem sep_mul_inv (f : Row 3) (P : Ideal (GeoRow 3)) :
    chartEval f P (separant f) * invSep f P = 1 := by
  change Ideal.Quotient.mk (localContraction f P) (localRowsMap f (separant f)) *
    Ideal.Quotient.mk (localContraction f P) (IsLocalization.Away.invSelf (separant f)) = 1
  rw [← map_mul, show localRowsMap f (separant f) * IsLocalization.Away.invSelf (separant f) = 1
    from IsLocalization.Away.mul_invSelf (separant f), map_one]
theorem chart_zero (f : Row 3) (P : Ideal (GeoRow 3)) {b : Row 3}
    (hb : genericRow b ∈ P) : chartEval f P b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb)
private def liftRows {R : Type*} [CommRing R] {f : Row 3} (g : Row 3 →+* R)
    (hs : IsUnit (g (separant f))) : LocalRows f →+* R :=
  IsLocalization.Away.lift (separant f) hs
def chartLift {R : Type*} [CommRing R] {f : Row 3} {P : Ideal (GeoRow 3)}
    (g : Row 3 →+* R) (hg : ∀ b ∈ contracted P, g b = 0)
    (hs : IsUnit (g (separant f))) : Chart f P →+* R :=
  show (LocalRows f ⧸ localContraction f P) →+* R from
    Ideal.Quotient.lift (localContraction f P) (liftRows g hs) (by
      change (contracted P).map (localRowsMap f) ≤ RingHom.ker (liftRows g hs)
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      change liftRows g hs (localRowsMap f b) = 0
      exact (IsLocalization.Away.lift_eq (separant f) hs b).trans (hg b hb))
theorem chartLift_eval {R : Type*} [CommRing R] {f : Row 3} {P : Ideal (GeoRow 3)}
    (g : Row 3 →+* R) (hg : ∀ b ∈ contracted P, g b = 0)
    (hs : IsUnit (g (separant f))) (b : Row 3) :
    chartLift g hg hs (chartEval f P b) = g b :=
  IsLocalization.Away.lift_eq (separant f) hs b
def constants {A : Type*} [CommRing A] (e : Row 3 →+* A) : Geom →+* A :=
  e.comp (MvPolynomial.C.comp Polynomial.C)
def localJet (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ → Chart f P
  | 0 => chartEval f P (MvPolynomial.X 0)
  | 1 => chartEval f P (MvPolynomial.X 1)
  | 2 => chartEval f P (MvPolynomial.X 2)
  | k + 3 => 2 * chartEval f P (compatibilityNumerator f k) *
      constants (chartEval f P) (((k + 3).factorial : Geom)⁻¹) *
      invSep f P ^ (2 * k + 1)
def jetPolynomial {A : Type*} [Semiring A] (len : ℕ) (a : ℕ → A) : A[X] :=
  ∑ j : Fin len, Polynomial.monomial j.val (a j.val)
def centred (f : Row 3) (P : Ideal (GeoRow 3)) : (Chart f P)[X] :=
  jetPolynomial taylorLength (localJet f P)
def localTaylor (f : Row 3) (P : Ideal (GeoRow 3)) : (Chart f P)[X] :=
  Polynomial.taylor (-chartEval f P (MvPolynomial.C Polynomial.X)) (centred f P)
end
end K1_13_5_4_3_2
end
section
namespace K1_14_3_6
noncomputable section
open K1 K1_13 K1_14 K1_14_3 Polynomial
open K1_13_5_3
abbrev total := Bivariate.totalDegree (F := FX)
def atScalar (S : K[X]) : JetPlane →+* FX :=
  eval₂RingHom (evalRingHom (atX S)) (atX S.derivative)
def power (d : ℕ) : ℕ := 2 * d - 3
def totalCap (d b : ℕ) : ℕ := 1 + power d * (b - 1)
def topCap (d b j : ℕ) : ℕ := min (totalCap d b) (power d * (j - 1) + d)
structure AgreementChart (f : Row 2) (d b j : ℕ) where
  cut : K → K → MvPolynomial (Fin 2) CenterField
  total_bound : ∀ x y, (cut x y).totalDegree ≤ totalCap d b
  top_bound : ∀ x y, (cut x y).degreeOf 1 ≤ topCap d b j
  agrees : ∀ S : K[X], S.natDegree ≤ d → K1_13_5.RegularAt 1 f (extend S) → ∀ x y,
    MvPolynomial.aeval (marked (extend S)) (cut x y) = 0 ↔ S.eval x = y
end
end K1_14_3_6
end
section
namespace K1_13_5_4_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_4
def c1 : Prop :=
  ∀ f : Row 3, f.totalDegree ≤ 120 → indexDegree f ≤ 48 → f.degreeOf 2 ≤ 24 →
    InLiftedBox (graph f) graphBox 1 ∧
      InLiftedBox (cut f) (liftedBox (taylorLength + 1)) (taylorLength - 1) ∧
      InLiftedBox (next f) (liftedBox (taylorLength + 2)) taylorLength ∧
      ∀ i, InLiftedBox (coefficientNumerator f i) (liftedBox taylorLength) (taylorLength - 2)
def c2 : Prop :=
  ∀ f : Row 3, Irreducible f → 0 < f.degreeOf 2 →
    RepresentsOnGraph f (oldCut f) (cut f) ∧ RepresentsOnGraph f (oldNext f) (next f)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4.c1 := by
  classical
  intro n f hf i
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.top
  obtain ⟨hg, he, hn, hc⟩ := h1 (f i) hb hj ht
  obtain ⟨hrep, hrep'⟩ := h2 (f i) (hf.irreducible i) (hf.positive i)
  exact ⟨{
    cut := cut (f i)
    next := next (f i)
    numerator := coefficientNumerator (f i)
    graph_box := hg
    cut_box := he
    next_box := hn
    coefficient_box := hc
    cut_represents := hrep
    next_represents := hrep'
    ordinary_bound := ordinary_bound (f i)
    actual := actual hrep hrep'
  }⟩
end
end K1_13_5_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace K1_14_3_6
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
theorem atScalar_eq (S : K[X]) (g : JetPlane) : atScalar S g = fixedAt g S := rfl
theorem atX_injective : Function.Injective atX :=
  (IsFractionRing.injective L[X] FX).comp
    (Polynomial.map_injective _ (algebraMap K L).injective)
theorem outer_le_total (g : JetPlane) : g.natDegree ≤ total g := by
  by_cases hg : g = 0
  · simp [hg, Bivariate.totalDegree]
  · exact (Nat.le_add_left _ _).trans
      (Bivariate.coeff_totalDegree_le g
        (mem_support_iff.mpr (leadingCoeff_ne_zero.mpr hg)))
theorem caps_degree {g : JetPlane} {b j : ℕ} (hg : JetCaps g b j) :
    total g ≤ b ∧ g.natDegree ≤ j := by
  constructor
  · apply Finset.sup_le
    intro v hv
    have hn : g.coeff v ≠ 0 := mem_support_iff.mp hv
    exact (hg v (g.coeff v).natDegree (leadingCoeff_ne_zero.mpr hn)).1
  · by_cases h : g = 0
    · simp [h]
    · have hn := leadingCoeff_ne_zero.mpr h
      exact (hg g.natDegree (g.coeff g.natDegree).natDegree
        (leadingCoeff_ne_zero.mpr hn)).2
theorem factor_cover (g : JetPlane) (hg : g ≠ 0) :
    ∃ fs : Finset JetPlane, (∀ f ∈ fs, Irreducible f) ∧
      (∑ f ∈ fs, total f) ≤ total g ∧ (∑ f ∈ fs, f.natDegree) ≤ g.natDegree ∧
      ∀ S : K[X], atScalar S g = 0 → ∃ f ∈ fs, atScalar S f = 0 := by
  classical
  let _ : StrongNormalizationMonoid JetPlane := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := UniqueFactorizationMonoid.normalizedFactors g
  let fs := A.toFinset
  have hprod := UniqueFactorizationMonoid.prod_normalizedFactors (a := g) hg
  have hdvd : (∏ f ∈ fs, f) ∣ g :=
    (Multiset.toFinset_prod_dvd_prod A).trans hprod.dvd
  have hirr (f : JetPlane) (hf : f ∈ fs) : Irreducible f :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (Multiset.mem_toFinset.mp hf)
  have total_prod (s : Finset JetPlane) (hs : (∏ f ∈ s, f) ≠ 0) :
      total (∏ f ∈ s, f) = ∑ f ∈ s, total f := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro i hi
      by_cases h : i = 0
      · simp [h, Polynomial.coeff_one]
      · exact False.elim ((mem_support_iff.mp hi) (by simp [Polynomial.coeff_one, h]))
    | @insert f s hf ih =>
      rw [Finset.prod_insert hf] at hs ⊢
      rw [Finset.sum_insert hf]
      calc
        _ = total f + total (∏ x ∈ s, x) :=
          Bivariate.totalDegree_mul (F := FX) (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs)
        _ = _ := congrArg (total f + ·) (ih (right_ne_zero_of_mul hs))
  have hp₀ : (∏ f ∈ fs, f) ≠ 0 := ne_zero_of_dvd_ne_zero hg hdvd
  refine ⟨fs, hirr, ?_, ?_, ?_⟩
  · rw [← total_prod fs hp₀]
    obtain ⟨q, hq⟩ := hdvd
    have hq₀ : q ≠ 0 := fun he => hg (by simp [hq, he])
    calc
      total (∏ f ∈ fs, f) ≤ total (∏ f ∈ fs, f) + total q := Nat.le_add_right _ _
      _ = total ((∏ f ∈ fs, f) * q) := (Bivariate.totalDegree_mul (F := FX) hp₀ hq₀).symm
      _ = total g := congrArg total hq.symm
  · calc
      _ = (∏ f ∈ fs, f).natDegree :=
        (Polynomial.natDegree_prod fs (fun f : JetPlane => f) (fun f hf => (hirr f hf).ne_zero)).symm
      _ ≤ _ := Polynomial.natDegree_le_of_dvd hdvd hg
  · intro S hS
    have hz := map_dvd (atScalar S) hprod.symm.dvd
    change atScalar S g ∣ atScalar S A.prod at hz
    rw [hS, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨f, hf, hzero⟩ := hz
    exact ⟨f, Multiset.mem_toFinset.mpr hf, hzero⟩
def exception (g : JetPlane) : Polynomial FX :=
  if g.natDegree = 0 then g.coeff 0
  else g.resultant g.derivative g.natDegree (g.natDegree - 1)
theorem exception_ne_zero {g : JetPlane} (hg : Irreducible g) (hp : g.natDegree < p) :
    exception g ≠ 0 := by
  unfold exception
  split_ifs with h
  · have hn := leadingCoeff_ne_zero.mpr hg.ne_zero
    change g.coeff g.natDegree ≠ 0 at hn
    rwa [h] at hn
  · have hp0 : 0 < g.natDegree := Nat.pos_of_ne_zero h
    have hchar : CharP FX p := charP_of_injective_ringHom (RingHom.injective seedEmbedding) p
    have hc : (g.natDegree : FX) ≠ 0 := by
      intro hz
      exact not_le_of_gt hp (Nat.le_of_dvd hp0 ((CharP.cast_eq_zero_iff FX p _).mp hz))
    have hc' : (g.natDegree : FX[X]) ≠ 0 := by
      simpa only [map_natCast, map_zero] using (Polynomial.C_injective.ne hc :
        Polynomial.C (g.natDegree : FX) ≠ Polynomial.C 0)
    have hder : g.derivative ≠ 0 := by
      intro hz
      have ha := congrArg (fun f : JetPlane => f.coeff (g.natDegree - 1)) hz
      rw [coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp0, coeff_zero] at ha
      exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hg.ne_zero) hc') ha
    exact resultant_derivative_ne_zero_of_irreducible g hg hder
theorem exception_degree {g : JetPlane} {b : ℕ} (hb : 2 ≤ b) (ht : total g ≤ b) :
    (exception g).natDegree ≤ total g * (b - 1) := by
  unfold exception
  split_ifs with h
  · have hc : (g.coeff 0).natDegree ≤ total g := by
      by_cases hn : g.coeff 0 = 0
      · simp [hn]
      · simpa only [Nat.add_zero] using
          Bivariate.coeff_totalDegree_le g (mem_support_iff.mpr hn)
    exact hc.trans (by simpa using Nat.mul_le_mul_left (total g) (show 1 ≤ b - 1 by omega))
  · let r := g.natDegree
    let t := total g
    have hrt : r ≤ t := outer_le_total g
    have hr : 1 ≤ r := Nat.pos_of_ne_zero h
    have hbound : ∀ i ≤ r, i + (g.coeff i).natDegree ≤ t := by
      intro i hi
      rcases Bivariate.coeff_totalDegree_le' g i with h | h
      · simpa only [Nat.add_comm] using h
      · simpa only [h, natDegree_zero, Nat.add_zero] using hi.trans hrt
    have hres := natDegree_resultant_derivative_padded_add_sq_le g r t hbound
    have he : (2 * r - 1) * t + (t - r)^2 = t * (t - 1) + r^2 := by
      zify [show 1 ≤ 2 * r by omega, show 1 ≤ t by omega, hrt]
      ring
    calc
      (g.resultant g.derivative r (r - 1)).natDegree ≤ t * (t - 1) := by
        have ha := Nat.add_le_add_right hres ((t - r)^2)
        rw [he] at ha
        omega
      _ ≤ t * (b - 1) := Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ht 1)
theorem exception_root {g : JetPlane} {S : K[X]} (hg : atScalar S g = 0)
    (hs : g.natDegree = 0 ∨ atScalar S g.derivative = 0) :
    (exception g).eval (atX S) = 0 := by
  unfold exception
  split_ifs with h
  · calc
      _ = atScalar S (C (g.coeff 0)) := (eval₂_C _ _).symm
      _ = 0 := (congrArg (atScalar S) (eq_C_of_natDegree_eq_zero h)).symm.trans hg
  · exact map_resultant_eq_zero_of_common_root (evalRingHom (atX S)) g g.derivative
      le_rfl (natDegree_derivative_le _) (Or.inl h) (atX S.derivative)
      (by rwa [eval_map]) (by rw [eval_map]; exact hs.resolve_left h)
theorem root_count {T : Finset K} {s : K → K[X]} (hs : Set.InjOn s (T : Set K))
    {f : FX[X]} (hf : f ≠ 0) (hroot : ∀ γ ∈ T, f.eval (atX (s γ)) = 0) :
    T.card ≤ f.natDegree := by
  classical
  have hc : (T.image fun γ => atX (s γ)).card ≤ f.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_roots hf).mpr (hroot γ hγ)
  rwa [Finset.card_image_of_injOn (fun _ ha _ hb h => hs ha hb (atX_injective h))] at hc
end
end K1_14_3_6
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_1_1
noncomputable section
open K1_13_5_4 K1_13_5_4_2 K1_13_5_4_2_4_1 MvPolynomial IsLocalRing
open scoped TensorProduct
private theorem rationalIdeal_span {k : Type} [Field k] (y : Fin 4 → k) :
    rationalIdeal y = Ideal.span (Set.range fun i => MvPolynomial.X i - C (y i)) := by
  let J : Ideal (Affine k) := Ideal.span (Set.range fun i => MvPolynomial.X i - C (y i))
  let q := Ideal.Quotient.mk J
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · have hcomp : q = q.comp (C.comp (eval y)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        have h : q (MvPolynomial.X i - C (y i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
        simpa [q, map_sub, sub_eq_zero] using h
    intro p hp
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [hcomp, RingHom.comp_apply, RingHom.comp_apply, hp, map_zero, map_zero]
  · rintro _ ⟨i, rfl⟩
    change MvPolynomial.X i - C (y i) ∈ vanishingIdeal k {y}
    rw [mem_vanishingIdeal_singleton_iff]
    simp
private theorem map_rationalIdeal {k L : Type} [Field k] [Field L] [Algebra k L]
    (y : Fin 4 → k) :
    (rationalIdeal y).map (MvPolynomial.map (algebraMap k L)) =
      rationalIdeal (algebraMap k L ∘ y) := by
  simp only [rationalIdeal_span, Ideal.map_span, ← Set.range_comp', Function.comp_apply,
    map_sub, map_X, map_C]
private theorem comap_rationalIdeal {k L : Type} [Field k] [Field L] [Algebra k L]
    (y : Fin 4 → k) :
    (rationalIdeal (algebraMap k L ∘ y)).comap (MvPolynomial.map (algebraMap k L)) =
      rationalIdeal y := by
  ext p
  rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, mem_vanishingIdeal_singleton_iff,
    aeval_eq_eval, aeval_eq_eval, ← MvPolynomial.map_eval, map_eq_zero_iff _ (RingHom.injective _)]
private theorem map_minimal {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) {I p : Ideal R} {q : Ideal S}
    (hp : I.IsMinimalPrime p) (hq : q.IsPrime) (hm : p.map f = q) (hc : q.comap f = p) :
    (I.map f).IsMinimalPrime q := by
  refine ⟨⟨hq, hm ▸ Ideal.map_mono hp.le⟩, ?_⟩
  intro T hT hTq
  have := hT.1
  have hTp : T.comap f ≤ p := hc ▸ Ideal.comap_mono hTq
  have hpT : p ≤ T.comap f :=
    hp.2 ⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp hT.2⟩ hTp
  exact hm ▸ Ideal.map_le_iff_le_comap.mpr hpT
private theorem affine_flat {k L : Type} [Field k] [Field L] [Algebra k L] :
    let : Algebra (Affine k) (Affine L) := (MvPolynomial.map (algebraMap k L)).toAlgebra
    Module.Flat (Affine k) (Affine L) := by
  let : Algebra (Affine k) (Affine L) := (MvPolynomial.map (algebraMap k L)).toAlgebra
  let e := (Algebra.TensorProduct.comm k (Affine k) L).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) k L).toRingEquiv
  let e' : Affine k ⊗[k] L ≃ₐ[Affine k] Affine L :=
    { e with
      commutes' := fun p => by
        change MvPolynomial.algebraTensorAlgEquiv k L (1 ⊗ₜ[k] p) =
          MvPolynomial.map (algebraMap k L) p
        simp }
  exact Module.Flat.of_linearEquiv e'.symm.toLinearEquiv
private theorem residue_constants_surjective {L : Type} [Field L] (y : Fin 4 → L) :
    Function.Surjective (algebraMap L (ResidueField (PointLocal y))) := by
  let B := PointLocal y
  let p := rationalIdeal y
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p B
  intro x
  change ∃ a : L, Ideal.Quotient.mk (maximalIdeal B) (algebraMap L B a) = x
  obtain ⟨z, rfl⟩ := e.surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  have he : Ideal.Quotient.mk p (C (eval y P)) = Ideal.Quotient.mk p P := by
    rw [Ideal.Quotient.eq, mem_vanishingIdeal_singleton_iff, aeval_eq_eval,
      map_sub, eval_C, sub_self]
  refine ⟨eval y P, ?_⟩
  rw [IsScalarTower.algebraMap_apply L (Affine L) B, MvPolynomial.algebraMap_eq]
  simpa only [e, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] using congrArg e he
private theorem length_over_constants {L : Type} [Field L]
    (I : Ideal (Affine L)) (y : Fin 4 → L) :
    Module.length L (PointAlgebra I y) = Module.length (PointLocal y) (PointAlgebra I y) := by
  let B := PointLocal y
  have : IsLocalHom (algebraMap L B) := ⟨fun a ha =>
    isUnit_iff_ne_zero.mpr (by intro h; subst a; simp at ha)⟩
  have hres : Function.Surjective (algebraMap (ResidueField L) (ResidueField B)) := by
    intro x
    obtain ⟨a, ha⟩ := residue_constants_surjective y x
    exact ⟨residue L a, ha⟩
  have hlen : Module.length (ResidueField L) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres, Module.length_eq_finrank]
    simp
  rw [IsLocalRing.length_restrictScalars L B (PointAlgebra I y), hlen, mul_one]
theorem proof : K1_13_5_4_2_4_1.c1 := by
  intro L _ _ I y hy
  let : Algebra (GeoRow 4) (Affine L) := (MvPolynomial.map (algebraMap GeometricX L)).toAlgebra
  let p := pointIdeal y
  let q := rationalIdeal (extendPoint L y)
  have hm : p.map (algebraMap (GeoRow 4) (Affine L)) = q := map_rationalIdeal y
  have hc : q.comap (algebraMap (GeoRow 4) (Affine L)) = p := comap_rationalIdeal y
  have hmin : q ∈ (extendIdeal L I).minimalPrimes :=
    map_minimal (algebraMap (GeoRow 4) (Affine L)) hy inferInstance hm hc
  have : q.LiesOver p := ⟨hc.symm⟩
  have : Module.Flat (GeoRow 4) (Affine L) := affine_flat
  let A := PointLocal y
  let B := PointLocal (extendPoint L y)
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower (GeoRow 4) A B := inferInstance
  have : IsLocalHom (algebraMap A B) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have hmap (J : Ideal (GeoRow 4)) :
      (J.map (algebraMap (GeoRow 4) A)).map (algebraMap A B) =
        (extendIdeal L J).map (algebraMap (Affine L) B) := by
    change _ = (J.map (algebraMap (GeoRow 4) (Affine L))).map (algebraMap (Affine L) B)
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), hmap]
    change (p.map (algebraMap (GeoRow 4) (Affine L))).map (algebraMap (Affine L) B) = _
    rw [hm, Localization.AtPrime.map_eq_maximalIdeal]
  let J := I.map (algebraMap (GeoRow 4) A)
  have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal B).1
  have hlen := IsLocalRing.length_baseChange A B (A ⧸ J)
  rw [hmax, Module.length_eq_one B (B ⧸ maximalIdeal B), mul_one] at hlen
  have hdim : Module.length L (PointAlgebra (extendIdeal L I) (extendPoint L y)) =
      pointLength I y := by
    rw [length_over_constants]
    change Module.length B (B ⧸ (extendIdeal L I).map (algebraMap (Affine L) B)) =
      Module.length A (A ⧸ J)
    rw [← hmap I]
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.length_eq.trans hlen
  have hfinite : pointLength I y < ⊤ := localLength_lt_top hy
  have : IsNoetherian L (PointAlgebra (extendIdeal L I) (extendPoint L y)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp (hdim.trans_lt hfinite).ne)).1
  refine ⟨hmin, inferInstance, ?_⟩
  simpa only [Module.length_eq_finrank, ENat.toNat_natCast] using congrArg ENat.toNat hdim
end
end K1_13_5_4_2_4_1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_5_4_3_2
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 Polynomial
open scoped BigOperators
@[simp] private theorem coeff_coeffDerivative (b : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative b).coeff m = derivative (b.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_C (g : Geom[X]) :
    coeffDerivative (MvPolynomial.C g : Row 3) = MvPolynomial.C (derivative g) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
@[simp] theorem coeffDerivative_X (i : Fin 3) :
    coeffDerivative (MvPolynomial.X i : Row 3) = 0 := by
  classical
  ext m
  simp only [coeff_coeffDerivative, MvPolynomial.coeff_X, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]
  split_ifs <;> simp
private theorem tangent_C (f : Row 3) (g : Geom[X]) :
    tangentNumerator f (MvPolynomial.C g) = separant f * MvPolynomial.C g.derivative := by
  simp [tangentNumerator, lowerTangent, coeffDerivative_C]
variable {f : Row 3} {P : Ideal (GeoRow 3)}
private abbrev Dual (f : Row 3) (P : Ideal (GeoRow 3)) :=
  TrivSqZeroExt (Chart f P) (Chart f P)
private def rowJet (f : Row 3) (P : Ideal (GeoRow 3)) : Row 3 →+* Dual f P where
  toFun b := (chartEval f P b, invSep f P * chartEval f P (tangentNumerator f b))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero _
    · rw [show (0 : Row 3) = MvPolynomial.C 0 by rw [map_zero], tangent_C]
      simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one _
    · rw [show (1 : Row 3) = MvPolynomial.C 1 by rw [map_one], tangent_C]
      simp
  map_add' b c := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · change _ * chartEval f P _ = _ * chartEval f P _ + _ * chartEval f P _
      rw [K1_13_5_4_3_1.tangentNumerator_add, map_add, mul_add]
  map_mul' b c := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change _ * chartEval f P _ =
        chartEval f P b * (_ * chartEval f P _) + (_ * chartEval f P _) * chartEval f P c
      rw [K1_13_5_4_3_1.tangentNumerator_mul, map_add, map_mul, map_mul]
      ring
private def chartJet (h : TangentStable f P) : Chart f P →+* Dual f P :=
  chartLift (rowJet f P) (fun b hb => by
    apply TrivSqZeroExt.ext
    · exact chart_zero f P hb
    · change invSep f P * chartEval f P (tangentNumerator f b) = 0
      rw [chart_zero f P (h b hb), mul_zero])
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.of_mul_eq_one _ (sep_mul_inv f P)))
private theorem chartJet_eval (h : TangentStable f P) (b : Row 3) :
    chartJet h (chartEval f P b) = rowJet f P b :=
  chartLift_eval _ _ _ b
private theorem chartJet_fst (h : TangentStable f P) (a : Chart f P) :
    (chartJet h a).fst = a := by
  let q := Ideal.Quotient.mk (localContraction f P)
  have he : (TrivSqZeroExt.fstHom (Chart f P) (Chart f P) (Chart f P)).toRingHom.comp
      ((chartJet h).comp q) = q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (separant f))
    apply RingHom.ext
    intro b
    change (chartJet h (chartEval f P b)).fst = chartEval f P b
    rw [chartJet_eval]
    rfl
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact RingHom.congr_fun he b
def delta (h : TangentStable f P) : Chart f P →+ Chart f P :=
  (TrivSqZeroExt.sndHom (R := Chart f P) (M := Chart f P)).toAddMonoidHom.comp
    (chartJet h).toAddMonoidHom
theorem delta_mul (h : TangentStable f P) (a b : Chart f P) :
    delta h (a * b) = a * delta h b + delta h a * b := by
  change (chartJet h (a * b)).snd = _
  rw [map_mul]
  change (chartJet h a).fst * delta h b + delta h a * (chartJet h b).fst = _
  rw [chartJet_fst, chartJet_fst]
theorem delta_eval (h : TangentStable f P) (b : Row 3) :
    delta h (chartEval f P b) = invSep f P * chartEval f P (tangentNumerator f b) := by
  change (chartJet h (chartEval f P b)).snd = _
  rw [chartJet_eval]
  rfl
theorem delta_coeff (h : TangentStable f P) (b : Geom[X]) :
    delta h (chartEval f P (MvPolynomial.C b)) =
      chartEval f P (MvPolynomial.C b.derivative) := by
  rw [delta_eval, tangent_C, map_mul, ← mul_assoc, mul_comm (invSep f P),
    sep_mul_inv, one_mul]
end
end K1_13_5_4_3_2
end
section
namespace K1_6
noncomputable section
open Polynomial Matrix
def shifts {A : Type} [CommRing A] (P : Fin 2 → A[X]) (L s : ℕ) :
    Matrix (Fin 2 × Fin L) (Fin s) A :=
  fun i j => (P i.1 * Polynomial.X ^ j.val).coeff i.2.val
def pairCoordinates {F : Type} [Field F] (P : Fin 2 → F[X][X]) (h : ℕ) :
    Fin 2 × Fin (h + 1) → F[X] :=
  fun i => (P i.1).coeff i.2.val
def maximalMinors {A row : Type} [CommRing A] {s : ℕ}
    (W : Matrix row (Fin s) A) (rows : Fin s → row) : A :=
  (W.submatrix rows id).det
end
end K1_6
end
