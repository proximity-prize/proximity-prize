import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN002 RCN005 RCN011 RCN371 RCN009 RCN012

noncomputable section

variable {K : Type} [Field K]

def seedZeroOrder : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

def seedOneOrder : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans (Equiv.swap 1 2)

theorem seedZeroOrder_base : seedZeroOrder 0 = 1 := by decide
theorem seedOneOrder_base : seedOneOrder 0 = 2 := by decide

private theorem seedZeroOrder_outer : seedZeroOrder 1 = 0 := by decide
private theorem seedZeroOrder_inner : seedZeroOrder 2 = 2 := by decide
private theorem seedOneOrder_outer : seedOneOrder 1 = 0 := by decide
private theorem seedOneOrder_inner : seedOneOrder 2 = 1 := by decide

theorem seedZero_resultant_degree (G T : MvPolynomial (Fin 3) K)
    (y₀ y₁ z₀ z₁ : ℕ)
    (hGy : G.degreeOf 0 ≤ y₀) (hTy : T.degreeOf 0 ≤ y₁)
    (hGz : G.degreeOf 2 ≤ z₀) (hTz : T.degreeOf 2 ≤ z₁) :
    (Polynomial.resultant (planeMap K seedZeroOrder G) (planeMap K seedZeroOrder T)).natDegree ≤
      y₁ * z₀ + y₀ * z₁ := by
  have hmixed := planeMap_resultant_natDegree_le K seedZeroOrder G T
  rw [seedZeroOrder_outer, seedZeroOrder_inner] at hmixed
  exact hmixed.trans (Nat.add_le_add (Nat.mul_le_mul hTy hGz) (Nat.mul_le_mul hGy hTz))

theorem seedOne_resultant_degree (G T : MvPolynomial (Fin 3) K)
    (y₀ y₁ t₀ t₁ : ℕ) (hy : y₀ ≤ t₀) (hTne : T ≠ 0)
    (hGy : G.degreeOf 0 ≤ y₀) (hTy : T.degreeOf 0 ≤ y₁)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ t₀)
    (hTt : ∀ d ∈ T.support, d 0 + d 1 ≤ t₁) :
    (Polynomial.resultant (planeMap K seedOneOrder G) (planeMap K seedOneOrder T)).natDegree ≤
      y₁ * t₀ + y₀ * t₁ - y₁ * y₀ := by
  apply planeMap_trapezoid_resultant_natDegree_le K seedOneOrder G T y₀ y₁ t₀ t₁ _ hTne
  · apply (planeMap_natDegree_le K seedOneOrder G).trans
    simpa only [seedOneOrder_outer] using hGy
  · apply (planeMap_natDegree_le K seedOneOrder T).trans
    simpa only [seedOneOrder_outer] using hTy
  · apply rationalMap_joint_support_of_original
    simpa only [seedOneOrder_outer, seedOneOrder_inner] using hGt
  · apply rationalMap_joint_support_of_original
    simpa only [seedOneOrder_outer, seedOneOrder_inner] using hTt
  · intro m hm
    exact RCN121.trapezoid_budget_mono y₀ y₁ t₀ t₁ m hy hm

theorem long_tail_seed_projection_finite_separable
    (useZ₁ : Bool) (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (G T : MvPolynomial (Fin 3) K) [CharP K 2130706433]
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hGy : G.degreeOf 0 ≤ 22) (hTy : T.degreeOf 0 ≤ 5505004)
    (hGz : G.degreeOf 2 ≤ 162) (hTz : T.degreeOf 2 ≤ 42467166)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ 200)
    (hTt : ∀ d ∈ T.support, d 0 + d 1 ≤ 52166458)
    (ht : Transcendental K (coordinate K P ((if useZ₁ then seedOneOrder else seedZeroOrder) 0)))
    (hpositive : 0 < (planeMap K (if useZ₁ then seedOneOrder else seedZeroOrder) G).natDegree) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P ((if useZ₁ then seedOneOrder else seedZeroOrder) 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  let order := if useZ₁ then seedOneOrder else seedZeroOrder
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P (order 0) ht
  have houter : (planeMap K order G).natDegree < 2130706433 := by
    have ho : order 1 = 0 := by cases useZ₁ <;>
      simp [order, seedOneOrder_outer, seedZeroOrder_outer]
    exact (planeMap_natDegree_le K order G).trans_lt (by rw [ho]; omega)
  have htne : T ≠ 0 := by
    intro hz
    exact hproper (by rw [hz]; exact dvd_zero G)
  have hresultant : (Polynomial.resultant (planeMap K order G) (planeMap K order T)
      (planeMap K order G).natDegree (planeMap K order T).natDegree).natDegree <
      2130706433 := by
    cases useZ₁
    · exact (seedZero_resultant_degree G T 22 5505004 162 42467166
        hGy hTy hGz hTz).trans_lt (by decide)
    · exact (seedOne_resultant_degree G T 22 5505004 200 52166458 (by decide) htne
        hGy hTy hGt hTt).trans_lt (by decide)
  obtain ⟨hfd, hsep, _⟩ := RCN010.actual_finite_separable_finrank_bound
    K order P ht 2130706433 G T hG hGmem hTmem hproper hpositive houter hresultant
  exact ⟨hfd, hsep⟩

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
