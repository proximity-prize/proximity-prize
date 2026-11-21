import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Regular.Flat
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.CurveList179925WitnessRank
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_6
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
structure CutInput (Γ : Finset K) (s : K → K[X]) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133671
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) ⟨4012, 1650, 550⟩
  weight : TrueWeightLE Q (3000 * 180265 - 1)
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
abbrev GenericField := FractionRing Geom[X]
abbrev GeoField := AlgebraicClosure GenericField
abbrev GeoJets := MvPolynomial (Fin 4) GeoField
def genericCoeffs : Geom[X] →+* GeoField :=
  (algebraMap GenericField GeoField).comp (algebraMap Geom[X] GenericField)
def toGeneric (P : Row 4) : GeoJets := MvPolynomial.map genericCoeffs P
def evalGeneric (S : Geom[X]) : GeoJets →+* GeoField :=
  MvPolynomial.eval (fun i => genericCoeffs (jet S i))
def markIdeal (S : Geom[X]) : Ideal GeoJets := RingHom.ker (evalGeneric S)
def intersectionIdeal (f Q : Row 4) : Ideal GeoJets :=
  Ideal.span {toGeneric f, toGeneric Q}
def divisorIdeal (surface : Ideal GeoJets) (E : Row 4) : Ideal GeoJets :=
  surface ⊔ Ideal.span {toGeneric E}
def cycleLength (J surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ :=
  letI := hp
  let L := Localization.AtPrime surface
  Module.length L (L ⧸ J.map (algebraMap GeoJets L))
def separant (g : Row 4) : Row 4 := MvPolynomial.pderiv 3 g
def coefficientDerivative (P : Row 4) : Row 4 :=
  ∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))
def partialFlow (P : Row 4) : Row 4 :=
  coefficientDerivative P +
  ∑ i : Fin 3, MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) *
    MvPolynomial.X i.succ * MvPolynomial.pderiv i.castSucc P
def flowNumerator (g P : Row 4) : Row 4 :=
  separant g * partialFlow P - partialFlow g * separant P
def clearedStep (g : Row 4) (a : ℕ) (P : Row 4) : Row 4 :=
  separant g * flowNumerator g P - (a : Row 4) * flowNumerator g (separant g) * P
def jetNumerator (g : Row 4) : ℕ → Row 4
  | 0 => MvPolynomial.X 0
  | n+1 => clearedStep g (2*n) (jetNumerator g n)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength+1)
def Invariant (g : Row 4) (surface : Ideal GeoJets) : Prop :=
  ∀ P : Row 4, toGeneric P ∈ surface → toGeneric (flowNumerator g P) ∈ surface
def CanonicalChart (f : Row 4) (surface : Ideal GeoJets) (r : ℕ) : Prop :=
  r < (shape f).t ∧ (∀ j ≤ r, toGeneric ((separant^[j]) f) ∈ surface) ∧
    toGeneric (separant ((separant^[r]) f)) ∉ surface
structure HighChart (f Q : Row 4) (l : ℕ) (S : Geom[X])
    (surface : Ideal GeoJets) (r : ℕ) : Prop where
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  point : surface ≤ markIdeal S
  chart : CanonicalChart f surface r
  regular : atJet (separant ((separant^[r]) f)) S ≠ 0
  invariant : Invariant ((separant^[r]) f) surface
def HighMark (f Q : Row 4) (l : ℕ) (S : Geom[X]) : Prop :=
  ∃ surface r, HighChart f Q l S surface r
def MixedMark (f Q : Row 4) (l : ℕ) (S : Geom[X]) : Prop :=
  ∃ surface r, HighChart f Q l S surface r ∧
    let g := (separant^[r]) f
    toGeneric (membershipTest g) ∉ surface ∧ ∃ C,
      ∃ hc : (divisorIdeal surface (membershipTest g)).IsMinimalPrime C,
        C ≤ markIdeal S ∧
        (cycleLength (divisorIdeal surface (membershipTest g)) C hc.isPrime ≠ 1 ∨
          toGeneric (nextTest g) ∉ C)
def ContinuedMark (f Q : Row 4) (l : ℕ) (S : Geom[X]) : Prop :=
  ∃ surface r, HighChart f Q l S surface r ∧
    let g := (separant^[r]) f
    toGeneric (membershipTest g) ∈ surface ∨ ∃ C,
      ∃ hc : (divisorIdeal surface (membershipTest g)).IsMinimalPrime C,
        toGeneric (membershipTest g) ∉ surface ∧ C ≤ markIdeal S ∧
        cycleLength (divisorIdeal surface (membershipTest g)) C hc.isPrime = 1 ∧
        toGeneric (nextTest g) ∈ C
def CurveSections (Γ : Finset K) (s : K → K[X]) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    (Γ.filter fun γ => (s γ).eval x = a).card ≤ d
structure Pieces (Γ : Finset K) where
  n : ℕ
  piece : Fin n → Finset K
  subset : ∀ i, piece i ⊆ Γ
  degree : Fin n → ℕ
def Pieces.union {Γ : Finset K} (C : Pieces Γ) : Finset K := by
  classical exact Finset.univ.biUnion C.piece
def Pieces.total {Γ : Finset K} (C : Pieces Γ) : ℕ := ∑ i, C.degree i
def Pieces.curves {Γ : Finset K} (C : Pieces Γ) (s : K → K[X]) : Prop :=
  ∀ i, CurveSections (C.piece i) s (C.degree i)
def SurfaceSections (Γ : Finset K) (s : K → K[X]) (d : ℕ) : Prop := by
  classical
  exact ∀ x a : K, (∃ γ ∈ Γ, (s γ).eval x ≠ a) →
    let H := Γ.filter fun γ => (s γ).eval x = a
    ∃ C : Pieces H, H ⊆ C.union ∧ C.curves s ∧ (∀ i, 0 < C.degree i) ∧ C.total ≤ d
def Pieces.surfaces {Γ : Finset K} (C : Pieces Γ) (s : K → K[X]) : Prop :=
  ∀ i, SurfaceSections (C.piece i) s (C.degree i)
abbrev cutterBox : Shape := ⟨4013, 1650, 550⟩
def auxCurves32 (x : Shape) : ℕ :=
  let p := x.chamber
  let h := chart taylorLength p
  mixed32 p cutterBox (cutterBox.plus (p.scale 4)) h + 2*x.t*mixed32 p p p h
def auxPoints32 (x : Shape) : ℕ :=
  let p := x.chamber
  mixed32 p cutterBox (cutterBox.plus (p.scale 4)) p + 2*x.t*mixed32 p p p p
def membershipDegree (x : Shape) : ℕ :=
  x.b * cutterBox.b * (chart (taylorLength+1) x.chamber).b
end
end K1_13_6
end
section
namespace K1_13_6
noncomputable section
open Polynomial Finset K1 K1_13
open ProximityPrize.Benchmark
open scoped BigOperators
private theorem occupancy {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (marks : Finset α) (nodes : Finset ι) (T : α → Finset ι) (x t d : ℕ)
    (hT : ∀ a ∈ marks, T a ⊆ nodes ∧ (T a).card = x)
    (hpair : ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b → (T a ∩ T b).card ≤ t)
    (hocc : ∀ i ∈ nodes, (marks.filter fun a => i ∈ T a).card ≤ d) :
    (marks.card * x)^2 ≤ nodes.card * (marks.card * (x + (marks.card - 1)*t)) ∧
      marks.card * x ≤ nodes.card * d := by
  classical
  let occ (i : ι) := (marks.filter fun a => i ∈ T a).card
  have section_eq (V : Finset ι) (hV : V ⊆ nodes) :
      (nodes.filter fun i => i ∈ V) = V := by
    ext i
    exact mem_filter.trans ⟨And.right, fun hi => ⟨hV hi, hi⟩⟩
  have first : ∑ i ∈ nodes, occ i = marks.card * x := by
    calc
      _ = ∑ a ∈ marks, (T a).card := by
        simp only [occ, card_filter]
        rw [sum_comm]
        refine sum_congr rfl fun a ha => ?_
        rw [sum_boole, Nat.cast_id, section_eq _ (hT a ha).1]
      _ = _ := by rw [sum_congr rfl (fun a ha => (hT a ha).2), sum_const, smul_eq_mul]
  have second : ∑ i ∈ nodes, occ i ^ 2 =
      ∑ a ∈ marks, ∑ b ∈ marks, (T a ∩ T b).card := by
    simp only [occ, sq, card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have identity (i : ι) :
        (if i ∈ T a then 1 else 0 : ℕ) * (if i ∈ T b then 1 else 0) =
          if i ∈ T a ∩ T b then 1 else 0 := by
      by_cases h₁ : i ∈ T a <;> by_cases h₂ : i ∈ T b <;> simp [h₁, h₂]
    simp_rw [identity]
    rw [sum_boole, Nat.cast_id, section_eq _ (inter_subset_left.trans (hT a ha).1)]
  have row (a : α) (ha : a ∈ marks) :
      ∑ b ∈ marks, (T a ∩ T b).card ≤ x + (marks.card - 1) * t := by
    rw [← add_sum_erase marks _ ha, inter_self, (hT a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b ∈ marks.erase a, t := sum_le_sum fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _ := by rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
  have second_le :
      ∑ i ∈ nodes, occ i ^ 2 ≤ marks.card * (x + (marks.card - 1) * t) := by
    rw [second]
    exact (sum_le_sum row).trans_eq (by rw [sum_const, smul_eq_mul])
  have cs := sq_sum_le_card_mul_sum_sq (s := nodes) (f := occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le), ?_⟩
  rw [← first, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hocc
private theorem incidence_arithmetic (m x : ℕ) (d : ℕ)
    (hm : 0 < m) (hx : 46594 ≤ x)
    (hsec : (m*x)^2 ≤ (x+81879) * (m * (x + (m-1)*(x-46594))))
    (hfirst : m*x ≤ (x+81879)*d) :
    46594*m ≤ 81879*d + 46594 := by
  have hcancel :
      m*x^2 ≤ (x+81879) * (x + (m-1)*(x-46594)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsec
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := by
    exact Int.ofNat_sub (by omega)
  have hX : ((x - 46594 : ℕ) : ℤ) = (x : ℤ)-46594 := Int.ofNat_sub hx
  have hcancelZ := (Int.ofNat_le.mpr hcancel)
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := (Int.ofNat_le.mpr hfirst)
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*81879 - ((m : ℤ)-1)*46594)*x ≥
      ((m : ℤ)-1)*81879*46594 := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(d : ℤ))*x ≤ (d : ℤ)*81879 := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbad : (d : ℤ)*81879 < ((m : ℤ)-1)*46594 := by omega
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*81879 - ((m : ℤ)-1)*46594 < ((m : ℤ)-(d : ℤ))*81879 := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (by norm_num : (0 : ℤ) ≤ 81879)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(d : ℤ))*81879*x ≤ (d : ℤ)*81879*81879 from by
        convert right using 1; ring))
  have bigger := mul_lt_mul_of_pos_right hbad (by norm_num : (0 : ℤ) < 81879)
  nlinarith only [impossible, bigger]
theorem section_capacity {w Γ s} (h : Messages w Γ s) (d : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) →
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ d) :
    46594 * Γ.card ≤ 81879*d + 46594 := by
  classical
  by_cases hm : Γ.card ≤ 1
  · omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ Γ, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ Γ) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ Γ) : 180265 ≤ (hits γ).card := by
    obtain ⟨T, hT, ht⟩ := h.hits γ hγ
    exact hT.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, ht i hi⟩)
  have pair_count (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ 133671 := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < Γ.card)
  have hcommon : common.card ≤ 133671 :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 180265 - common.card
  let t := 133671 - common.card
  have ht : t = x - 46594 := by dsimp [t, x]; omega
  have hx : 46594 ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 81879 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) :
      ∃ T : Finset I, γ ∈ Γ → T ⊆ hits γ \ common ∧ T.card = x := by
    by_cases hγ : γ ∈ Γ
    · have hc := hit_count γ hγ
      have hd : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨T, hT, hcT⟩ := exists_subset_card_eq hd
      exact ⟨T, fun _ => ⟨hT, hcT⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose T hT using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ Γ) : T γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hT γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ Γ) (b : K) (hb : b ∈ Γ) (hab : a ≠ b) :
      (T a ∩ T b).card ≤ t := by
    have cover : (T a ∩ T b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with ht' | hc
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hT a ha).1 (mem_inter.mp ht').1)).1,
          (mem_sdiff.mp ((hT b hb).1 (mem_inter.mp ht').2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hc, common_le b hb hc⟩
    have disj : Disjoint (T a ∩ T b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) :
      (Γ.filter fun γ => i ∈ T γ).card ≤ d := by
    have proper : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hT γ hγ).1 hi)).1).2⟩
  obtain ⟨sec, first⟩ := occupancy Γ nodes T x t d
    (fun γ hγ => ⟨into_nodes γ hγ, (hT γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at sec
  rw [hnodes] at first
  exact incidence_arithmetic _ _ _ (by omega) hx sec first
theorem curve_capacity {w Γ s d} (h : Messages w Γ s) (hc : CurveSections Γ s d) :
    46594 * Γ.card ≤ 81879*d + 46594 :=
  section_capacity h d (fun i => hc (node i) (w i))
theorem curve_capacity_integral {w Γ s d} (h : Messages w Γ s)
    (hc : CurveSections Γ s d) (hd : 0 < d) : Γ.card ≤ 2*d := by
  have := curve_capacity h hc
  omega
theorem Pieces.curve_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) : 46594 * C.union.card ≤ 81879 * C.total + 46594 * C.n := by
  classical
  have hc' (i : Fin C.n) := K1_13_6.curve_capacity (h.mono (C.subset i)) (hc i)
  calc
    _ ≤ 46594 * ∑ i, (C.piece i).card :=
      Nat.mul_le_mul_left _ (by exact card_biUnion_le)
    _ = ∑ i, 46594 * (C.piece i).card := by rw [mul_sum]
    _ ≤ ∑ i : Fin C.n, (81879 * C.degree i + 46594) := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, sum_add_distrib, mul_sum, Nat.mul_comm]
theorem Pieces.curve_capacity_integral {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 2*C.total := by
  classical
  have hc' (i : Fin C.n) := K1_13_6.curve_capacity_integral (h.mono (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 2 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
theorem surface_capacity {w Γ s d} (h : Messages w Γ s)
    (hs : SurfaceSections Γ s d) (hd : 0 < d) : Γ.card ≤ 4*d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter fun γ => (s γ).eval (node i) = w i).card ≤ 2*d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := h.mono (filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (card_le_card hC).trans ((C.curve_capacity_integral hH hc hpos).trans
      (Nat.mul_le_mul_left 2 hdeg))
  have := section_capacity h (2*d) hsection
  omega
theorem Pieces.surface_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.surfaces s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 4*C.total := by
  classical
  have hc' (i : Fin C.n) := K1_13_6.surface_capacity (h.mono (C.subset i)) (hc i) (hd i)
  calc
    _ ≤ ∑ i, (C.piece i).card := card_biUnion_le
    _ ≤ ∑ i : Fin C.n, 4 * C.degree i := sum_le_sum fun i _ => hc' i
    _ = _ := by simp [Pieces.total, mul_sum]
end
end K1_13_6
end
section
namespace K1_13_6
noncomputable section
open Polynomial K1_13
open scoped BigOperators
@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coefficientDerivative_C (p : Geom[X]) :
    coefficientDerivative (MvPolynomial.C p) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P+Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp
private theorem coefficientDerivative_mul_X (P : Row 4) (j : Fin 4) :
    coefficientDerivative (P * MvPolynomial.X j) = coefficientDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem eval_chain (P : Row 4) (a : Fin 4 → Geom[X]) :
    derivative (MvPolynomial.eval a P) = MvPolynomial.eval a (coefficientDerivative P) +
      ∑ i, derivative (a i) * MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [coefficientDerivative_C]
  | add P Q hP hQ =>
    simp only [map_add, coefficientDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    rw [map_mul, MvPolynomial.eval_X, derivative_mul, ih, coefficientDerivative_mul_X,
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
private theorem derivative_hasse (S : Geom[X]) (k : ℕ) :
    derivative (hasseDeriv k S) = C ((k+1 : ℕ) : Geom) * hasseDeriv (k+1) S := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := Geom) 1 k) S
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul, C_eq_natCast, Nat.add_comm, add_mul] using h
private theorem eval_partialFlow (P : Row 4) (S : Geom[X]) :
    derivative (atJet P S) = atJet (partialFlow P) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant P) S := by
  unfold atJet partialFlow separant
  rw [eval_chain, Fin.sum_univ_castSucc, map_add, map_sum]
  rw [← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jet, derivative_hasse, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Fin.val_castSucc, Fin.val_succ]
theorem eval_flowNumerator (g P : Row 4) (S : Geom[X]) (hg : atJet g S = 0) :
    atJet (flowNumerator g P) S = atJet (separant g) S * derivative (atJet P S) := by
  have hz : atJet (partialFlow g) S +
      derivative (jet S (3 : Fin 4)) * atJet (separant g) S = 0 := by
    rw [← eval_partialFlow, hg, map_zero]
  unfold flowNumerator
  rw [eval_partialFlow]
  change (MvPolynomial.eval (jet S)) (_ - _) = _
  rw [map_sub, map_mul, map_mul]
  change atJet (separant g) S * atJet (partialFlow P) S -
      atJet (partialFlow g) S * atJet (separant P) S = _
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
theorem eval_jetNumerator (g : Row 4) (S : Geom[X]) (hg : atJet g S = 0) (n : ℕ) :
    atJet (jetNumerator g n) S =
      atJet (separant g) S ^ (2*n) * ((derivative (R := Geom))^[n]) S := by
  induction n with
  | zero =>
    simp [jetNumerator, atJet, jet]
  | succ n ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
    change e (clearedStep g (2*n) (jetNumerator g n)) = _
    unfold clearedStep
    rw [map_sub, map_mul, map_mul, map_mul, map_natCast]
    change atJet (separant g) S * atJet (flowNumerator g (jetNumerator g n)) S -
      (↑(2*n) : Geom[X]) * atJet (flowNumerator g (separant g)) S *
        atJet (jetNumerator g n) S = _
    rw [eval_flowNumerator _ _ _ hg, eval_flowNumerator _ _ _ hg, ih,
      cleared_product_rule,
      show 2*(n+1) = 2*n+2 by omega, Function.iterate_succ_apply']
private theorem eval_jetNumerator_zero (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (n : ℕ) (hS : S.natDegree < n) :
    atJet (jetNumerator g n) S = 0 := by
  rw [eval_jetNumerator _ _ hg, iterate_derivative_eq_zero hS, mul_zero]
theorem eval_membership_tests (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hS : S.natDegree ≤ 133671) :
    atJet (membershipTest g) S = 0 ∧ atJet (nextTest g) S = 0 :=
  ⟨eval_jetNumerator_zero g S hg taylorLength (Nat.lt_succ_of_le hS),
    eval_jetNumerator_zero g S hg (taylorLength+1)
      ((Nat.lt_succ_of_le hS).trans (Nat.lt_succ_self _))⟩
end
end K1_13_6
end
section
namespace K1_13_6
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
def c1 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)
def c2 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ, MixedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * l * (2 * C.total + B.card) ≤ surfaceNumerator32 (shape f).chamber cutterBox
def c3 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ C D : Pieces Γ,
      C.curves s ∧ D.surfaces s ∧ (∀ i, 0 < C.degree i) ∧ (∀ i, 0 < D.degree i) ∧
      (∀ γ ∈ Γ, ContinuedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ D.union) ∧
      l * C.total ≤ membershipDegree (shape f) ∧
      2 * D.total ≤ 133671 * (shape f).b * cutterBox.b
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
private theorem mem_markIdeal {P : Row 4} {S : Geom[X]} :
    toGeneric P ∈ markIdeal S ↔ atJet P S = 0 := by
  unfold markIdeal
  rw [RingHom.mem_ker]
  change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs P) = 0 ↔ _
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = 0 ↔ _
  rw [← MvPolynomial.eval₂_comp]
  exact map_eq_zero_iff _ genericCoeffs_injective
theorem highMark_cases {f Q l S} (hS : S.natDegree ≤ 133671)
    (hh : HighMark f Q l S) : MixedMark f Q l S ∨ ContinuedMark f Q l S := by
  obtain ⟨surface, r, hc⟩ := hh
  let g := (separant^[r]) f
  have hg : atJet g S = 0 := mem_markIdeal.mp (hc.point (hc.chart.2.1 r le_rfl))
  have hE : toGeneric (membershipTest g) ∈ markIdeal S :=
    mem_markIdeal.mpr (eval_membership_tests g S hg hS).1
  by_cases onSurface : toGeneric (membershipTest g) ∈ surface
  · exact Or.inr ⟨surface, r, hc, Or.inl onSurface⟩
  have hl : divisorIdeal surface (membershipTest g) ≤ markIdeal S :=
    sup_le hc.point ((Ideal.span_singleton_le_iff_mem _).mpr hE)
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  obtain ⟨curve, hcurve, hpoint⟩ := Ideal.exists_minimalPrimes_le hl
  by_cases hsimple : cycleLength (divisorIdeal surface (membershipTest g)) curve hcurve.isPrime = 1
  · by_cases hnext : toGeneric (nextTest g) ∈ curve
    · exact Or.inr ⟨surface, r, hc, Or.inr ⟨curve, hcurve, onSurface, hpoint, hsimple, hnext⟩⟩
    · exact Or.inl ⟨surface, r, hc, onSurface, curve, hcurve, hpoint, Or.inr hnext⟩
  · exact Or.inl ⟨surface, r, hc, onSurface, curve, hcurve, hpoint, Or.inl hsimple⟩
private theorem le_ceil {n d count : ℕ} (hd : 0 < d) (h : count*d ≤ n) :
    count ≤ ceilDiv n d := by
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
private theorem price_formula (x : Shape) (l : ℕ) :
    physicalPrice x l =
      ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
        ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l +
      2 * (133671 * x.b * cutterBox.b) +
      ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594) := by
  simp only [physicalPrice, auxCurves32, auxPoints32, membershipDegree, Nat.mul_assoc]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13.c6 := by
  classical
  intro w Γ s hm f hf hOn l hl hCut
  obtain ⟨Q, hproper, hbox, hweight, horder⟩ := hCut
  have input : CutInput Γ s f Q l := ⟨hm.distinct, hm.degree, hf, hOn, hl,
    hproper, hbox, hweight, horder⟩
  obtain ⟨A, AB, hA, haCover, haCurves, haPoints⟩ := h1 Γ s f Q l input
  obtain ⟨C, CB, hC, hcPos, hcCover, hcBudget⟩ := h2 Γ s f Q l input
  obtain ⟨D, F, hD, hF, hdPos, hfPos, hdCover, hdBudget, hfBudget⟩ := h3 Γ s f Q l input
  let aux := A.union.card + AB.card
  let mixed := C.union.card + CB.card
  have cover : Γ ⊆ (A.union ∪ AB) ∪ (C.union ∪ CB) ∪ D.union ∪ F.union := by
    intro γ hγ
    by_cases hh : HighMark f Q l (extend (s γ))
    · have hdeg : (extend (s γ)).natDegree ≤ 133671 := by
        simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
      rcases highMark_cases hdeg hh with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (hcCover γ hγ h)))
      · rcases Finset.mem_union.mp (hdCover γ hγ h) with hd | hf
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hd)
        · exact Finset.mem_union_right _ hf
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (haCover γ hγ hh)))
  have card : Γ.card ≤ aux + mixed + D.union.card + F.union.card := by
    refine (Finset.card_le_card cover).trans ?_
    calc
      _ ≤ (((A.union ∪ AB) ∪ (C.union ∪ CB)) ∪ D.union).card + F.union.card :=
        Finset.card_union_le _ _
      _ ≤ ((A.union ∪ AB) ∪ (C.union ∪ CB)).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (A.union ∪ AB).card + (C.union ∪ CB).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ _ := by
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)) _) _
  let x := shape f
  have aux_bound : aux ≤
      ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594) := by
    apply le_ceil (by decide)
    have hA' := A.curve_capacity hm hA
    change 32 * A.total ≤ auxCurves32 x at haCurves
    change 32 * (AB.card + A.n) ≤ 2 * auxPoints32 x at haPoints
    dsimp only [aux]
    omega
  have mixed_bound : l * mixed ≤ ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 := by
    apply le_ceil (by decide)
    have hC' := Nat.add_le_add_right (C.curve_capacity_integral hm hC hcPos) CB.card
    have h := (Nat.mul_le_mul_left (32*l) hC').trans hcBudget
    simpa only [mixed, x, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have curve_bound : l * D.union.card ≤
      ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594 := by
    apply le_ceil (by decide)
    have hD' := Nat.mul_le_mul_left l (D.curve_capacity_integral hm hD hdPos)
    change l * D.total ≤ membershipDegree x at hdBudget
    have hD'' : l * D.union.card ≤ 2 * membershipDegree x := by
      rw [Nat.mul_left_comm] at hD'
      omega
    omega
  have main_bound : mixed + D.union.card ≤
      ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
        ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l := by
    apply le_ceil hl
    rw [Nat.add_mul, Nat.mul_comm mixed l, Nat.mul_comm D.union.card l]
    exact Nat.add_le_add mixed_bound curve_bound
  have surface_bound : F.union.card ≤ 2*(133671*x.b*cutterBox.b) := by
    have hF' := F.surface_capacity hm hF hfPos
    change 2 * F.total ≤ 133671*x.b*cutterBox.b at hfBudget
    omega
  rw [price_formula]
  change Γ.card ≤
    ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
      ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l +
    2*(133671*x.b*cutterBox.b) +
    ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594)
  omega
end
end K1_13_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial K1_13 K1_13_6
abbrev TaylorIndex := Fin taylorLength
abbrev GeoPoint := Fin 4 → GeoField
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def GeoFits (g : GeoJets) (p : Shape) : Prop :=
  g.totalDegree ≤ p.b ∧ g.weightedTotalDegree Fin.val ≤ p.j ∧ g.degreeOf 3 ≤ p.t
structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
  initial : ∀ i : Fin 4,
    numerator (i.castLE (by decide : 4 ≤ taylorLength)) = MvPolynomial.X i * denom
def TaylorChart.Fits (C : TaylorChart) (h : Shape) : Prop :=
  GeoFits C.denom h ∧ ∀ i, GeoFits (C.numerator i) h
def TaylorChart.Recovers (C : TaylorChart) (S : Geom[X]) : Prop :=
  evalGeneric S C.denom ≠ 0 ∧
    ∀ i, evalGeneric S (C.numerator i) =
      evalGeneric S C.denom * genericCoeffs (hasseDeriv i.val S)
abbrev AffineForm := GeoField × (TaylorIndex → GeoField)
def TaylorChart.pullback (C : TaylorChart) (a : AffineForm) : GeoJets :=
  MvPolynomial.C a.1 * C.denom + ∑ i, MvPolynomial.C (a.2 i) * C.numerator i
def Isolated (f g u v : GeoJets) (y : GeoPoint) : Prop :=
  RingHom.ker (MvPolynomial.eval y) ∈ (Ideal.span ({f, g, u, v} : Set GeoJets)).minimalPrimes
def SliceBound (f g : GeoJets) (C : TaylorChart) (d : ℕ) : Prop :=
  ∀ a b : AffineForm, ∀ points : Finset GeoPoint,
    (∀ y ∈ points, Isolated f g (C.pullback a) (C.pullback b) y ∧
      MvPolynomial.eval y C.denom ≠ 0) → points.card ≤ d
end
end K1_13_7_1
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
abbrev anchorBox (f : Row 4) : Shape := (shape f).chamber
def HasMark (Γ : Finset K) (s : K → K[X]) (surface : Ideal GeoJets) : Prop :=
  ∃ γ ∈ Γ, surface ≤ markIdeal (extend (s γ))
def tangentCut (g P : Row 4) (a : ℕ) : Row 4 :=
  (flowNumerator g)^[a] P
def DerivativeWeight (f : Row 4) (surface : Ideal GeoJets) (r w : ℕ) : Prop :=
  let g := (separant^[r]) f
  ¬ f ∣ g ∧ InBox (shape g) (anchorBox f) ∧ 0 < w ∧
    ∃ hZ : (intersectionIdeal f g).IsMinimalPrime surface,
      cycleLength (intersectionIdeal f g) surface hZ.isPrime = (w : ℕ∞)
def SurfaceCut (f Q : Row 4) (surface : Ideal GeoJets) (P : Row 4) : Prop :=
  ∃ (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (v w : ℕ),
    0 < v ∧ cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
    (w = 0 ∨ ∃ r, 0 < r ∧ r < (shape f).t ∧ DerivativeWeight f surface r w) ∧
    toGeneric P ∉ surface ∧
    InBox (shape P) (cutterBox.plus ((anchorBox f).scale (4*v + 2*w)))
structure CurveOnFactor (f : Row 4) (C : Ideal GeoJets) : Prop where
  prime : C.IsPrime
  dim : ringKrullDim (GeoJets ⧸ C) = 1
  contains : toGeneric f ∈ C
abbrev SectionIndex (a : Shape) := Fin 4 → Fin (a.b + 1)
abbrev SectionField (a : Shape) := FractionRing (MvPolynomial (SectionIndex a) GeoField)
abbrev SectionJets (a : Shape) := MvPolynomial (Fin 4) (SectionField a)
def boxMonomials (a : Shape) : Finset (SectionIndex a) :=
  Finset.univ.filter fun m =>
    (∑ i, (m i).val) ≤ a.b ∧
      (∑ i, i.val * (m i).val) ≤ a.j ∧ (m 3).val ≤ a.t
def genericSection (a : Shape) : SectionJets a :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) GeoField)
      (SectionField a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def sectionDegree (C : Ideal GeoJets) (a : Shape) : ℕ :=
  let J := C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
    Ideal.span {genericSection a}
  Module.finrank (SectionField a) (SectionJets a ⧸ J)
end
end K1_13_6_1
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open RingTheory.Sequence
open scoped Pointwise
theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
theorem toGeneric_injective : Function.Injective toGeneric :=
  MvPolynomial.map_injective _ genericCoeffs_injective
private theorem mem_smul_top_iff_dvd {R : Type*} [CommRing R] (f x : R) :
    x ∈ f • (⊤ : Submodule R R) ↔ f ∣ x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, smul_eq_mul]
  exact exists_congr fun _ => eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem proper_generic (f g : Row 4) (hf : Irreducible f) (hg : ¬ f ∣ g) :
    IsRelPrime (toGeneric f) (toGeneric g) := by
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hreg : IsWeaklyRegular (Row 4) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨mul_right_injective₀ hp.ne_zero, ?_⟩
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
    intro x hx
    exact (mem_smul_top_iff_dvd f x).mpr
      ((hp.dvd_mul.mp ((mem_smul_top_iff_dvd f (g * x)).mp hx)).resolve_left hg)
  let _ : Algebra Geom[X] GeoField := genericCoeffs.toAlgebra
  let _ : Module.IsTorsionFree Geom[X] GeoField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr genericCoeffs_injective
  have hflat : Module.Flat (Row 4) GeoJets :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv Geom[X] (Row 4) GeoField GeoJets).symm.toLinearEquiv
  have h := hreg.of_flat (S := GeoJets)
  change IsWeaklyRegular GeoJets [toGeneric f, toGeneric g] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  rintro a ⟨b, hb⟩ ⟨c, hc⟩
  have hzero : toGeneric f ≠ 0 := fun hz => hp.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm))
  have hprod : toGeneric g * b = toGeneric f * c := by rw [hc, hb]; ring
  have hdiv : toGeneric f ∣ b := (mem_smul_top_iff_dvd _ _).mp
    (mem_of_isSMulRegular_quotient_of_smul_mem h.2
      ((mem_smul_top_iff_dvd _ _).mpr ⟨c, hprod⟩))
  obtain ⟨q, hq⟩ := hdiv
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hb ▸ hzero)
  have hu : a * q = 1 := mul_left_cancel₀ hb0 (by
    calc
      b * (a * q) = (a * b) * q := by ring
      _ = b := by rw [← hb, ← hq]
      _ = b * 1 := (mul_one _).symm)
  exact ⟨⟨a, q, hu, by rw [mul_comm, hu]⟩, rfl⟩
end
end K1_13_7_1
end
section
namespace K1_13_6_1_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def FullChamber (a : Shape) : Prop := Chamber a ∧ 0 < a.t
abbrev PairSectionIndex (a h : Shape) := SectionIndex a ⊕ SectionIndex h
abbrev PairSectionField (a h : Shape) :=
  FractionRing (MvPolynomial (PairSectionIndex a h) GeoField)
def sectionWith {σ : Type*} (a : Shape) (ι : SectionIndex a → σ) :
    MvPolynomial (Fin 4) (FractionRing (MvPolynomial σ GeoField)) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial σ GeoField)
      (FractionRing (MvPolynomial σ GeoField)) (MvPolynomial.X (ι m))) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def surfaceDegree (surface : Ideal GeoJets) (a h : Shape) : ℕ :=
  let F := PairSectionField a h
  let I := surface.map (MvPolynomial.map (algebraMap GeoField F)) ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  Module.finrank F (MvPolynomial (Fin 4) F ⧸ I)
abbrev pairIdeal (F G : GeoJets) : Ideal GeoJets := Ideal.span {F, G}
end
end K1_13_6_1_4
end
section
namespace K1_13_6_1_4
noncomputable section
open MvPolynomial K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
private theorem krullDim_of_polynomial_normalization {k R : Type*} [Field k]
    [CommRing R] [IsDomain R] {d : ℕ} [Algebra (MvPolynomial (Fin d) k) R]
    [FaithfulSMul (MvPolynomial (Fin d) k) R] [Module.Finite (MvPolynomial (Fin d) k) R] :
    ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨b, hb, hd⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ :=
      Algebra.IsIntegral.comap_surjective B R (⟨b, hb⟩ : PrimeSpectrum B)
    have hz' : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hz'] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hd.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
private theorem krullDim_of_finite_hom {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    {d : ℕ} (g : MvPolynomial (Fin d) k →+* R) (hg : Function.Injective g)
    (hgfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul (MvPolynomial (Fin d) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let finite : Module.Finite (MvPolynomial (Fin d) k) R := hgfin
  exact @krullDim_of_polynomial_normalization k R _ _ _ d algebra faithful finite
private theorem dim_eq_Hilbert {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hH := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
  rw [Nat.card_fin] at hH
  rw [hH]
  exact krullDim_of_finite_hom g.toRingHom hg hgfin
theorem pair_dimension {F G : GeoJets} (hF : F ≠ 0) (hproper : IsRelPrime F G)
    {surface : Ideal GeoJets} (hZ : (pairIdeal F G).IsMinimalPrime surface) :
    ringKrullDim (GeoJets ⧸ surface) = 2 := by
  let := hZ.isPrime
  have hFZ : Ideal.span {F} ≤ surface :=
    le_trans (Ideal.span_mono (by simp)) hZ.le
  obtain ⟨D, hD, hDZ⟩ := Ideal.exists_minimalPrimes_le hFZ
  let := hD.isPrime
  have hD0 : D ≠ ⊥ := fun e =>
    hF (Ideal.mem_bot.mp (e ▸ hD.le (Ideal.subset_span (by simp))))
  have hDh : D.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD0))
  obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hD.isPrime hD0
  have heq := Ideal.eq_span_singleton_of_height_eq_one hDh ha hap
  have hGD : G ∉ D := by
    intro hG
    have hFa : a ∣ F := Ideal.mem_span_singleton.mp (heq ▸ hD.le (Ideal.subset_span (by simp)))
    have hGa : a ∣ G := Ideal.mem_span_singleton.mp (heq ▸ hG)
    exact hap.not_isUnit (hproper hFa hGa)
  have hpair : pairIdeal F G ≤ D ⊔ Ideal.span {G} := by
    rw [pairIdeal, Ideal.span_insert]
    exact sup_le (hD.le.trans le_sup_left) le_sup_right
  have hcut : (D ⊔ Ideal.span {G}).IsMinimalPrime surface :=
    ⟨⟨hZ.isPrime, sup_le hDZ ((Ideal.span_mono (by simp)).trans hZ.le)⟩,
      fun J hJ hJZ => hZ.2 ⟨hJ.1, hpair.trans hJ.2⟩ hJZ⟩
  have hDdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
  have hZdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hGD hcut
  rw [Nat.card_fin] at hDdeg
  have hdeg : (affineHilbertPolynomial surface).natDegree = 2 := by omega
  simp [dim_eq_Hilbert surface, hdeg]
theorem curve_of_proper_cut {f P : Row 4} {surface C : Ideal GeoJets}
    (hZ : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (hf : toGeneric f ∈ surface) (hP : toGeneric P ∉ surface)
    (hC : (divisorIdeal surface P).IsMinimalPrime C) : CurveOnFactor f C := by
  let := hZ
  let := hC.isPrime
  have hZdeg : (affineHilbertPolynomial surface).natDegree = 2 := by
    have hd := (dim_eq_Hilbert surface).symm.trans hdim
    exact_mod_cast hd
  have hCdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hP hC
  have hd : (affineHilbertPolynomial C).natDegree = 1 := by omega
  have hle : surface ≤ C := (show surface ≤ divisorIdeal surface P from le_sup_left).trans hC.le
  exact ⟨hC.isPrime, by simp [dim_eq_Hilbert C, hd], hle hf⟩
end
end K1_13_6_1_4
end
