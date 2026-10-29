import ProximityPrize.SubmissionBinaryLower.P64C6TwistTransfer

/-!
# Positive-bias factors, including Frobenius descent
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6All

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Finite P64C6Retained
  P64C6TwistTransfer

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] [PerfectRing F 2]
  [Fintype ι] [DecidableEq ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "ev" => BCHKSSubstitutionVanish.triEval

noncomputable def gap (R : Tri) (ω : ι ↪ F) (y : ι → F[X]) (D N : ℕ) : ℕ :=
  R.natDegree * (D + N) - ∑ i, lineOrd R (ω i) (y i)

lemma gap_frobLift (R : Tri) (hR : R ≠ 0) (ω : ι ↪ F) (y : ι → F[X]) (D N : ℕ) :
    gap (frobLift R) ω y D N = 2 * gap R ω (fun i => Polynomial.expand F 2 (y i)) D N := by
  unfold gap
  rw [natDegree_frobLift]
  simp_rw [lineOrd_frobLift R hR]
  rw [← Finset.mul_sum]
  rw [show R.natDegree * 2 * (D + N) = 2 * (R.natDegree * (D + N)) by ring]
  omega

lemma yz_le_twice (R : Tri) (hR : R ≠ 0) (q d : ℕ) (hq : 0 < q)
    (hw : WtLE 0 q 1 d R) : P64Caps.YZ.yzSupportDegree R 1 ≤ 2 * d := by
  have hqh := outer_weight_le R hR q d hw
  have hh : R.natDegree ≤ d := by
    have hm := Nat.mul_le_mul_right R.natDegree (Nat.succ_le_of_lt hq)
    nlinarith
  unfold P64Caps.YZ.yzSupportDegree
  apply Finset.sup_le
  intro j hj
  have hjh : j ≤ R.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
  have hcoef : Polynomial.Bivariate.degreeX (R.coeff j) ≤ d := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a _
    exact coefficient_parameter_degree R q d hw j a
  omega

theorem card_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D q d n N : ℕ) (hq : 0 < q) (hRyz : WtLE 0 q 1 d R)
    (hn : Fintype.card ι ≤ n) (hnlarge : 625 ≤ n) (hN : 0 < N) (hNcap : N ≤ 500000)
    (hF : 2 * R.natDegree * wd R D < Fintype.card F)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hβ : 1000 * R.natDegree ≤ gap R ω y D N)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, ev R z (P z) = 0)
    (hcard : ∀ z ∈ S, D + N ≤ (A z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hsupport : ∀ z ∈ S, wd R D < ∑ i ∈ A z, lineOrd R (ω i) (y i)) :
    S.card ≤ 17 * n * d + 4 * R.natDegree * d := by
  classical
  generalize heq : R.natDegree = h
  induction h using Nat.strong_induction_on generalizing R q y S P A with
  | h h ih =>
    rw [← heq]
    by_cases hY : Polynomial.derivative R = 0
    · by_cases hX : P64Incidence.dXPoly R = 0
      · let T := twistPoly R
        have hback : frobLift T = R := frobLift_twistPoly R hY hX
        have hTi : Irreducible T := irreducible_twistPoly R hirr hY hX
        have hdeg : R.natDegree = T.natDegree * 2 := by rw [← hback, natDegree_frobLift]
        have hTpos : 1 ≤ T.natDegree := by omega
        have hTlt : T.natDegree < h := by omega
        have hspace : wd R D = 2 * wd T D := by
          rw [← hback, spatial_weight_frobLift T hTi.ne_zero D]
        let y' : ι → F[X] := fun i => Polynomial.expand F 2 (y i)
        let S' := S.image (sqrtF : F → F)
        let P' : F → F[X] := fun t => P (t ^ 2)
        let A' : F → Finset ι := fun t => A (t ^ 2)
        have hSq : ∀ t ∈ S', t ^ 2 ∈ S := by
          intro t ht
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
          simpa using hz
        have hScard : S'.card = S.card := Finset.card_image_of_injective S sqrtF_injective
        have hwt : WtLE 0 (2 * q) 1 d T := by
          apply parameter_weight_transfer T q d
          rwa [hback]
        have hy' : ∀ i, (y' i).natDegree ≤ 2 * q := by
          intro i
          dsimp [y']
          rw [Polynomial.natDegree_expand]
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 (hy i)
        have hF' : 2 * T.natDegree * wd T D < Fintype.card F := by
          calc _ ≤ 2 * R.natDegree * wd R D :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
            _ < _ := hF
        have hβ' : 1000 * T.natDegree ≤ gap T ω y' D N := by
          have hg : gap R ω y D N = 2 * gap T ω y' D N := by
            rw [← hback, gap_frobLift T hTi.ne_zero]
          rw [hg, hdeg] at hβ
          omega
        have hP' : ∀ t ∈ S', (P' t).natDegree ≤ D := fun t ht => hP _ (hSq t ht)
        have hcurve' : ∀ t ∈ S', ev T t (P' t) = 0 := by
          intro t ht
          have hc := hcurve _ (hSq t ht)
          rw [← hback] at hc
          have he : ev (frobLift T) (t ^ 2) (P' t) = (ev T t (P' t)) ^ 2 :=
            triEval_frobLift T t (P' t)
          have hp : (ev T t (P' t)) ^ 2 = 0 := he.symm.trans hc
          exact eq_zero_of_pow_eq_zero hp
        have hcard' : ∀ t ∈ S', D + N ≤ (A' t).card := fun t ht => hcard _ (hSq t ht)
        have hmatch' : ∀ t ∈ S', ∀ i ∈ A' t, (P' t).eval (ω i) = (y' i).eval t := by
          intro t ht i hi
          simpa [P', y', Polynomial.expand_eval] using hmatch _ (hSq t ht) i hi
        have hsupp' : ∀ t ∈ S', wd T D < ∑ i ∈ A' t, lineOrd T (ω i) (y' i) := by
          intro t ht
          have hs := hsupport _ (hSq t ht)
          have hm : ∀ i, lineOrd R (ω i) (y i) = 2 * lineOrd T (ω i) (y' i) := by
            intro i
            rw [← hback, lineOrd_frobLift T hTi.ne_zero]
          simp_rw [hm] at hs
          rw [← Finset.mul_sum, hspace] at hs
          change wd T D < ∑ i ∈ A (t ^ 2), lineOrd T (ω i) (y' i)
          exact (by omega)
        have hbT : S'.card ≤ 17 * n * d + 4 * T.natDegree * d := by
          exact ih T.natDegree hTlt (R := T) (hirr := hTi) (hh := hTpos)
            (q := 2 * q) (hq := by omega) (hRyz := hwt) (hF := hF')
            (y := y') (hy := hy') (hβ := hβ') (S := S') (P := P') (A := A')
            (hP := hP') (hcurve := hcurve') (hcard := hcard') (hmatch := hmatch')
            (hsupport := hsupp') (heq := rfl)
        rw [hScard] at hbT
        exact hbT.trans (Nat.add_le_add_left (Nat.mul_le_mul_right d
          (Nat.mul_le_mul_left 4 (by omega))) _)
      · have hc := P64Incidence.card_le_of_inseparable R hirr (by omega) hY hX (wd R D)
          (P64Resultant.coeff_natDegree_le_weighted R D) hF S P hcurve
        have hyz := yz_le_twice R hirr.ne_zero q d hq hRyz
        have hm := Nat.mul_le_mul_left (2 * R.natDegree) hyz
        nlinarith
    · let β := gap R ω y D N
      have hβpos : 0 < β := by dsimp [β]; omega
      have hsum : (∑ i, lineOrd R (ω i) (y i)) ≤ R.natDegree * (D + N) := by
        dsimp [β, gap] at hβpos
        omega
      have hβeq : (∑ i, lineOrd R (ω i) (y i)) + β = R.natDegree * (D + N) := by
        dsimp [β, gap]
        omega
      have hc := P64C6Case.separable_card_le R hirr hh hY D (wd R D) q d n N β hq le_rfl
        hRyz hn hnlarge hN hNcap hβ hF ω y hy hβeq S P A hP hcurve hcard hmatch hsupport
      nlinarith

end P64C6All
end ProximityPrize.SubmissionBinaryLower
