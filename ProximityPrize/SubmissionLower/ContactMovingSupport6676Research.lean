import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLeadingCancellationResearch
import ProximityPrize.SubmissionLower.ContactFlagPoleInequality6543Research

/-! . -/
namespace ProximityPrize.SubmissionLower.ContactMovingSupport6676Research
open scoped Classical BigOperators WithZero
open ContactGenericCoefficientAvoidanceResearch ContactLeadingCancellationResearch
open ContactSparsePoleSupportResearch ContactFlagBezout6543Research
open ContactLocalPoleBound
noncomputable section
set_option maxHeartbeats 1000000

def liftExponent (d : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) + Finsupp.single 2 (d 2)
def shiftExponent (d : Fin 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  liftExponent d + Finsupp.single 3 1
abbrev quadraticSupport := flagSupport (2 • unitAllFlag)
abbrev linearSupport := flagSupport unitYZFlag
def movingSupport : Finset (Fin 4 →₀ ℕ) :=
  quadraticSupport.image liftExponent ∪ linearSupport.image shiftExponent

theorem liftExponent_injective : Function.Injective liftExponent := by
  intro d e h
  ext i
  have hh := DFunLike.congr_fun h i.castSucc
  fin_cases i <;> simpa [liftExponent] using hh

theorem shiftExponent_injective : Function.Injective shiftExponent := by
  intro d e h
  exact liftExponent_injective (add_right_cancel h)

theorem mem_movingSupport (d : Fin 4 →₀ ℕ) :
    d ∈ movingSupport ↔ d 0+d 1+d 2+d 3 ≤ 2 ∧ d 3 ≤ 1 ∧ d 1+2*d 3 ≤ 2 := by
  classical
  constructor
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
      have he := (mem_flagSupport_iff _ _).mp he
      simp only [InFlag, nsmul_zOnly, nsmul_yz, nsmul_all, unitAllFlag] at he
      simp [liftExponent]
      omega
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
      have he := (mem_flagSupport_iff _ _).mp he
      simp only [InFlag, unitYZFlag] at he
      simp [shiftExponent,liftExponent]
      omega
  · rintro ⟨ht,hw,hr⟩
    let e := exponentOfTriple (d 0,d 1,d 2)
    have heq0 : e 0=d 0 ∧ e 1=d 1 ∧ e 2=d 2 := by simp [e,exponentOfTriple]
    have hdw : d 3=0 ∨ d 3=1 := by omega
    rcases hdw with hdw | hdw
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨e,?_,?_⟩
      · rw [mem_flagSupport_iff]
        simp [InFlag,unitAllFlag,heq0.1,heq0.2.1,heq0.2.2]
        omega
      · ext i; fin_cases i <;> simp [liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨e,?_,?_⟩
      · rw [mem_flagSupport_iff]
        simp [InFlag,unitYZFlag,heq0.1,heq0.2.1,heq0.2.2]
        omega
      · ext i; fin_cases i <;> simp [shiftExponent,liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]

theorem movingSupport_downwardClosed : ExponentSetDownwardClosed movingSupport := by
  intro d hd e he
  rw [mem_movingSupport] at hd ⊢
  have h0 := he 0; have h1 := he 1; have h2 := he 2; have h3 := he 3
  omega
theorem zero_mem_movingSupport : (0 : Fin 4 →₀ ℕ) ∈ movingSupport := by
  simp [mem_movingSupport]

def quadraticIndex (d : quadraticSupport) : movingSupport :=
  ⟨liftExponent d.1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
def linearIndex (d : linearSupport) : movingSupport :=
  ⟨shiftExponent d.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
theorem quadraticIndex_injective : Function.Injective quadraticIndex :=
  fun _ _ h ↦ Subtype.ext (liftExponent_injective (congrArg Subtype.val h))
theorem linearIndex_injective : Function.Injective linearIndex :=
  fun _ _ h ↦ Subtype.ext (shiftExponent_injective (congrArg Subtype.val h))

def supportIndex : quadraticSupport ⊕ linearSupport → movingSupport :=
  Sum.elim quadraticIndex linearIndex
theorem supportIndex_bijective : Function.Bijective supportIndex := by
  constructor
  · intro d e h
    cases d with
    | inl d =>
      cases e with
      | inl e => exact congrArg Sum.inl (quadraticIndex_injective h)
      | inr e => have hh := DFunLike.congr_fun (congrArg Subtype.val h) 3
                 simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
    | inr d =>
      cases e with
      | inl e => have hh := DFunLike.congr_fun (congrArg Subtype.val h) 3
                 simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
      | inr e => exact congrArg Sum.inr (linearIndex_injective h)
  · intro d
    rcases Finset.mem_union.mp d.2 with hd | hd
    · obtain ⟨e,he,h⟩ := Finset.mem_image.mp hd
      exact ⟨Sum.inl ⟨e,he⟩,Subtype.ext h⟩
    · obtain ⟨e,he,h⟩ := Finset.mem_image.mp hd
      exact ⟨Sum.inr ⟨e,he⟩,Subtype.ext h⟩

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
def restrictQ : (movingSupport → K) →ₗ[K] (quadraticSupport → K) :=
  LinearMap.funLeft K K quadraticIndex
def restrictU : (movingSupport → K) →ₗ[K] (linearSupport → K) :=
  LinearMap.funLeft K K linearIndex
theorem restrictQ_surjective : Function.Surjective (restrictQ (K := K)) :=
  LinearMap.funLeft_surjective_of_injective K K _ quadraticIndex_injective
theorem restrictU_surjective : Function.Surjective (restrictU (K := K)) :=
  LinearMap.funLeft_surjective_of_injective K K _ linearIndex_injective
def quadraticPolynomial (c : movingSupport → K) := polynomialOfSupport quadraticSupport (restrictQ c)
def linearPolynomial (c : movingSupport → K) := polynomialOfSupport linearSupport (restrictU c)
theorem quadraticPolynomial_inFlag (c : movingSupport → K) :
    PolynomialInFlag (2 • unitAllFlag) (quadraticPolynomial c) :=
  (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)
theorem linearPolynomial_inFlag (c : movingSupport → K) :
    PolynomialInFlag unitYZFlag (linearPolynomial c) :=
  (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)

def movingCoordinates (x : Fin 3 → L) (w : L) : Fin 4 → L := ![x 0,x 1,x 2,w]
theorem evaluation_lift (x : Fin 3 → L) (w : L) (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
      (MvPolynomial.monomial (liftExponent d) a) =
    MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a) := by
  simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
    Fin.prod_univ_three,liftExponent,movingCoordinates]
theorem evaluation_shift (x : Fin 3 → L) (w : L) (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
      (MvPolynomial.monomial (shiftExponent d) a) =
    MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a) * w := by
  simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
    Fin.prod_univ_three,shiftExponent,liftExponent,movingCoordinates,mul_assoc]

theorem coefficientEvaluation_eq (x : Fin 3 → L) (w : L) (c : movingSupport → K) :
    coefficientEvaluation (movingCoordinates x w) movingSupport c =
      MvPolynomial.eval₂Hom (algebraMap K L) x (quadraticPolynomial c) +
      MvPolynomial.eval₂Hom (algebraMap K L) x (linearPolynomial c) * w := by
  let e := Equiv.ofBijective supportIndex supportIndex_bijective
  change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _) = _
  simp only [polynomialOfSupport,map_sum]
  rw [← e.sum_comp]
  simp only [Fintype.sum_sum_type,e,Equiv.ofBijective_apply,supportIndex,Sum.elim_inl,
    Sum.elim_inr,quadraticIndex,linearIndex]
  simp only [evaluation_lift,evaluation_shift]
  simp [quadraticPolynomial,linearPolynomial,polynomialOfSupport,map_sum,
    Finset.sum_mul,restrictQ,restrictU,LinearMap.funLeft,quadraticIndex,linearIndex]

theorem coordinate_mem (i : Fin 3) : Finsupp.single i.castSucc 1 ∈ movingSupport := by
  fin_cases i <;> simp [mem_movingSupport]
theorem exists_coordinate_evaluation (x : Fin 3 → L) (w : L) (i : Fin 3) :
    ∃ c : movingSupport → K,
      coefficientEvaluation (movingCoordinates x w) movingSupport c = x i := by
  refine ⟨deltaCoefficient movingSupport ⟨Finsupp.single i.castSucc 1,coordinate_mem i⟩,?_⟩
  change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _) = _
  rw [polynomialOfSupport_deltaCoefficient]
  fin_cases i <;> simp [MvPolynomial.eval₂Hom_monomial,movingCoordinates]

theorem exponentSetPoleWeight_moving (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (w : L) :
    exponentSetPoleWeight v (movingCoordinates x w) movingSupport =
      max (2 * max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
        (max (poleOrder v (x 0)) (poleOrder v (x 2)) + poleOrder v w) := by
  let q : Fin 4 → ℤ := fun i ↦ poleOrder v (movingCoordinates x w i)
  let a := max (q 1) (max (q 0) (q 2))
  let b := max (q 0) (q 2)
  have hq : ∀ i, 0 ≤ q i := fun i ↦ le_max_left _ _
  have ha0 : q 0 ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have ha1 : q 1 ≤ a := le_max_left _ _
  have ha2 : q 2 ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  have hb0 : q 0 ≤ b := le_max_left _ _
  have hb2 : q 2 ≤ b := le_max_right _ _
  have ha : 0 ≤ a := (hq 1).trans ha1
  change exponentSetPoleWeight v (movingCoordinates x w) movingSupport = max (2*a) (b+q 3)
  have hweight (d : Fin 4 →₀ ℕ) : exponentPoleWeight v (movingCoordinates x w) d =
      (d 0 : ℤ)*q 0+(d 1 : ℤ)*q 1+(d 2 : ℤ)*q 2+(d 3 : ℤ)*q 3 := by
    simp [exponentPoleWeight,Fin.sum_univ_four,q]
  apply le_antisymm
  · unfold exponentSetPoleWeight
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (by omega : 0 ≤ 2*a).trans (le_max_left _ _)
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hz
    rcases (mem_movingSupport d).mp hd with ⟨ht,hw,hr⟩
    rw [hweight]
    have hdw : d 3=0 ∨ d 3=1 := by omega
    rcases hdw with hdw | hdw
    · have ht' : (d 0 : ℤ)+d 1+d 2 ≤ 2 := by exact_mod_cast (by omega : d 0+d 1+d 2 ≤ 2)
      have h0 := mul_le_mul_of_nonneg_left ha0 (Int.natCast_nonneg (d 0))
      have h1 := mul_le_mul_of_nonneg_left ha1 (Int.natCast_nonneg (d 1))
      have h2 := mul_le_mul_of_nonneg_left ha2 (Int.natCast_nonneg (d 2))
      simp only [hdw,Nat.cast_zero,zero_mul,add_zero]
      apply le_trans _ (le_max_left _ _)
      nlinarith
    · have hd1 : d 1=0 := by omega
      have ht' : (d 0 : ℤ)+d 2 ≤ 1 := by exact_mod_cast (by omega : d 0+d 2 ≤ 1)
      have hb : 0 ≤ b := (hq 0).trans hb0
      have h0 := mul_le_mul_of_nonneg_left hb0 (Int.natCast_nonneg (d 0))
      have h2 := mul_le_mul_of_nonneg_left hb2 (Int.natCast_nonneg (d 2))
      simp only [hdw,hd1,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
      apply le_trans _ (le_max_right _ _)
      nlinarith
  · have hmem (d : Fin 4 →₀ ℕ) (hd : d ∈ movingSupport) :
        exponentPoleWeight v (movingCoordinates x w) d ≤
          exponentSetPoleWeight v (movingCoordinates x w) movingSupport := by
      apply Finset.le_max'
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
    have hs (i : Fin 3) : 2*q i.castSucc ≤ exponentSetPoleWeight v (movingCoordinates x w) movingSupport := by
      have hm : Finsupp.single i.castSucc 2 ∈ movingSupport := by fin_cases i <;> simp [mem_movingSupport]
      have hh := hmem _ hm
      fin_cases i <;> simpa [hweight] using hh
    have hw (i : Fin 3) (hi : i=0 ∨ i=2) : q i.castSucc+q 3 ≤
        exponentSetPoleWeight v (movingCoordinates x w) movingSupport := by
      have hm : Finsupp.single i.castSucc 1+Finsupp.single 3 1 ∈ movingSupport := by
        rcases hi with rfl | rfl <;> simp [mem_movingSupport]
      have hh := hmem _ hm
      rcases hi with rfl | rfl <;> simpa [hweight] using hh
    have hs0 := hs 0; have hs1 := hs 1; have hs2 := hs 2
    have hw0 := hw 0 (Or.inl rfl); have hw2 := hw 2 (Or.inr rfl)
    dsimp [a,b] at *
    omega

theorem quadratic_max_signed_eq_truncated (a b w : ℤ) (ha : 0 ≤ a) (hb : b ≤ a) :
    max (2*a) (b+w)=max (2*a) (b+max 0 w) := by omega


end
end ProximityPrize.SubmissionLower.ContactMovingSupport6676Research
