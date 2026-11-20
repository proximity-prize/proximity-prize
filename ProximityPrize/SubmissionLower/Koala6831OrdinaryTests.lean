import ProximityPrize.SubmissionLower.Koala6831OrdinaryShortTest
import ProximityPrize.SubmissionLower.Koala6831OrdinaryCurveCount
import ProximityPrize.SubmissionLower.Koala6831MovingTaylorDivision
import ProximityPrize.SubmissionLower.Koala6831MovingShortening



namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open scoped Classical BigOperators Polynomial
open Koala6831OrdinaryIncidence
open Koala6831Intrinsic (implicitRegularity)

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3200000

variable {K E I : Type} [Field K] [Field E]

theorem exists_ordinary_agreement_tests (φ : K[X] →+* E) (hφ : Function.Injective φ) (F : Carrier K)
    (nodes : Finset I) (x : I ↪ K) (u₀ u₁ : I → K) (w y t : ℕ)
    (hy : 1 ≤ y) (hyt : y ≤ t)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t) :
    ∃ test : ShortenedAgreementTests nodes (ordinarySurface φ (implicitRegularity F)) w y t,
      test.full = fun i => fullOrdinaryTest φ F w (x i) (u₀ i) (u₁ i) := by
  classical
  let S := ordinarySurface φ (implicitRegularity F)
  let full (i : I) := fullOrdinaryTest φ F w (x i) (u₀ i) (u₁ i)
  let D (C : Ideal (MvPolynomial (Fin 3) E)) := identityNodes nodes full C
  let c := φ.comp Polynomial.C
  let center := φ Polynomial.X
  let locator (C : Ideal (MvPolynomial (Fin 3) E)) := (Lagrange.nodal (D C) x).map c
  let base₀ (C : Ideal (MvPolynomial (Fin 3) E)) := (Lagrange.interpolate (D C) x u₀).map c
  let base₁ (C : Ideal (MvPolynomial (Fin 3) E)) := (Lagrange.interpolate (D C) x u₁).map c
  have hcenter (C : Ideal (MvPolynomial (Fin 3) E)) : (locator C).eval center ≠ 0 := by
    change ((Lagrange.nodal (D C) x).map (φ.comp Polynomial.C)).eval (φ Polynomial.X) ≠ 0
    rw [← polynomialHom_eval]
    exact fun h => Lagrange.nodal_ne_zero (hφ (h.trans φ.map_zero.symm))
  have hex (C : Ideal (MvPolynomial (Fin 3) E)) (i : I) :=
    Koala6831Moving.exists_shortened_affine_weights.{0}
      (locator C) (base₀ C) (base₁ C) center (c (x i)) (c (u₀ i)) (c (u₁ i))
      (w - (D C).card) (hcenter C)
  choose weights a b hwts using hex
  let short (C : Ideal (MvPolynomial (Fin 3) E)) (i : I) :=
    shortOrdinaryTest φ F (w - (D C).card) (weights C i) (a C i) (b C i)
  have hcompat {M : Type} [Field M] [Algebra E M]
      (C : Ideal (MvPolynomial (Fin 3) E)) (hD : (D C).card ≤ w)
      (v : Fin 3 → M) (hS : MvPolynomial.aeval v S ≠ 0)
      (hidentity : ∀ j ∈ D C, MvPolynomial.aeval v (full j) = 0) (i : I) :
      MvPolynomial.aeval v (short C i) = 0 ↔ MvPolynomial.aeval v (full i) = 0 := by
    let f := algebraMap E M
    let Φ := reconstructedOrdinary φ F v w
    have heval (j : I) : MvPolynomial.aeval v (full j) =
        MvPolynomial.aeval v S ^ (2 * w) *
          (Φ.eval (f (c (x j))) - (f (c (u₀ j)) + v 0 * f (c (u₁ j)))) :=
      eval_fullOrdinaryTest φ F w (x j) (u₀ j) (u₁ j) v hS
    have hident (j : I) (hj : j ∈ D C) :
        Φ.eval ((f.comp c) (x j)) = (f.comp c) (u₀ j) + v 0 * (f.comp c) (u₁ j) := by
      have he := hidentity j hj
      rw [heval, mul_eq_zero, or_iff_right (pow_ne_zero _ hS), sub_eq_zero] at he
      exact he
    obtain ⟨Q, hQ, hfactor, -⟩ := Koala6831Moving.exists_identity_shortened_tail
      (f.comp c) (D C) x u₀ u₁ x.injective.injOn w hD (v 0) Φ
      (reconstructedOrdinary_degree φ F v w) hident
    have hfactor' : Φ = (base₀ C).map f + Polynomial.C (v 0) * (base₁ C).map f +
        (locator C).map f * Q := by
      simpa only [base₀, base₁, locator, Polynomial.map_map] using hfactor
    have hweight := hwts C i f (v 0) Φ Q hQ hfactor'
    have hcoeff (j : ℕ) (hj : j ∈ Finset.range (w - (D C).card + 1)) :
        (Polynomial.taylor (f center) Φ).coeff j = ordinaryJet φ F v j :=
      reconstructedOrdinary_coeff φ F v w j
        (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (Nat.sub_le _ _))
    have hsum : (∑ j ∈ Finset.range (w - (D C).card + 1), f (weights C i j) *
          (Polynomial.taylor (f center) Φ).coeff j) =
        ∑ j ∈ Finset.range (w - (D C).card + 1), f (weights C i j) * ordinaryJet φ F v j := by
      exact Finset.sum_congr rfl (fun j hj => congrArg (f (weights C i j) * ·) (hcoeff j hj))
    rw [hsum] at hweight
    have hshort : MvPolynomial.aeval v (short C i) =
        MvPolynomial.aeval v S ^ (2 * (w - (D C).card)) *
          ((∑ j ∈ Finset.range (w - (D C).card + 1), f (weights C i j) * ordinaryJet φ F v j) -
            (f (a C i) + v 0 * f (b C i))) :=
      eval_shortOrdinaryTest φ F _ (weights C i) (a C i) (b C i) v hS
    rw [hshort, hweight, heval, mul_eq_zero, or_iff_right (pow_ne_zero _ hS),
      mul_eq_zero, or_iff_right (pow_ne_zero _ hS)]
  refine ⟨⟨full, short, ?_⟩, rfl⟩
  intro C hprime hS hD i hi
  have : C.IsPrime := hprime
  have hi' := Finset.mem_sdiff.mp hi
  have hfull : full i ∉ C := fun h => hi'.2 (Finset.mem_filter.mpr ⟨hi'.1, h⟩)
  let v := RCN002.coordinate E C
  have hker : RingHom.ker (MvPolynomial.aeval v).toRingHom = C := RCN002.aeval_coordinate_ker E C
  have hzero {A : MvPolynomial (Fin 3) E} :
      MvPolynomial.aeval v A = 0 ↔ A ∈ C := by
    change A ∈ RingHom.ker (MvPolynomial.aeval v).toRingHom ↔ _
    rw [hker]
  refine ⟨fun hs => hfull (hzero.mp ((hcompat C hD v (fun hr => hS (hzero.mp hr))
    (fun j hj => hzero.mpr (Finset.mem_filter.mp hj).2) i).mp (hzero.mpr hs))), ?_, ?_⟩
  · exact shortOrdinaryTest_in_cutFlag φ F _ (weights C i) (a C i) (b C i) y t hy hyt hcap
  · intro point hideal hreg he
    exact (hcompat C hD point hreg (fun j hj => hideal (Finset.mem_filter.mp hj).2) i).mpr he

end

end ProximityPrize.SubmissionLower.Koala6831Ordinary
