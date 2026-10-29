import ProximityPrize.SubmissionBinaryLower.P64C7Case
import ProximityPrize.SubmissionBinaryLower.P64C6All

/-!
# The low-bias bound with Frobenius descent

The profile inequality, low-bias condition, and full-line count are all
preserved when the two spatial variables descend through Frobenius.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7All

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6TwistTransfer P64C7Case

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] [PerfectRing F 2]
  [Fintype ι] [DecidableEq ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "ev" => BCHKSSubstitutionVanish.triEval

lemma degree_ge_three (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (hn : Fintype.card ι ≤ 2097152) (ω : ι ↪ F) (y : ι → F[X])
    (hfull : (fullLines R ω y).card < 208984)
    (hβ : R.natDegree * 1481911 < ∑ i, lineOrd R (ω i) (y i)) : 3 ≤ R.natDegree := by
  have ht : ∀ i, lineOrd R (ω i) (y i) ≤ R.natDegree - 1 + if i ∈ fullLines R ω y then 1 else 0 := by
    intro i
    have hm := lineOrd_le_natDegree_of_irreducible hirr hh (ω i) (y i)
    split_ifs with hi
    · omega
    · have he : lineOrd R (ω i) (y i) ≠ R.natDegree := by simpa [fullLines] using hi
      omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => ht i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const_zero, add_zero, mul_one] at hs
  have hm := Nat.mul_le_mul_right (R.natDegree - 1) hn
  omega

lemma fullLines_frobLift (R : Tri) (hR : R ≠ 0) (ω : ι ↪ F) (y : ι → F[X]) :
    fullLines (frobLift R) ω y = fullLines R ω (fun i => Polynomial.expand F 2 (y i)) := by
  ext i
  simp only [fullLines, Finset.mem_filter, Finset.mem_univ, true_and,
    natDegree_frobLift, lineOrd_frobLift R hR]
  omega

theorem card_le (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (q d : ℕ) (hq : 0 < q) (hRyz : WtLE 0 q 1 d R)
    (hn : Fintype.card ι ≤ 2097152)
    (hF : 2 * R.natDegree * wd R 1048575 < Fintype.card F)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q)
    (hβ : R.natDegree * 1481911 < ∑ i, lineOrd R (ω i) (y i))
    (hfull : (fullLines R ω y).card < 208984)
    (hprofile : 2 * (R.natDegree : ℤ) * wd R 1048575 - R.natDegree ^ 2 * 1048575 -
      (∑ i, (lineOrd R (ω i) (y i) : ℤ) ^ 2) ≤ 65536 * R.natDegree ^ 2)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ 1048575)
    (hcurve : ∀ z ∈ S, ev R z (P z) = 0)
    (hcard : ∀ z ∈ S, 1482911 ≤ (A z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ A z ↔ (P z).eval (ω i) = (y i).eval z)
    (hsupport : ∀ z ∈ S, wd R 1048575 < ∑ i ∈ A z, lineOrd R (ω i) (y i)) :
    S.card ≤ 41 * 2097152 * d + 4 * R.natDegree * d := by
  classical
  generalize heq : R.natDegree = h
  induction h using Nat.strong_induction_on generalizing R q y S P A with
  | h h ih =>
    rw [← heq]
    have hthree := degree_ge_three R hirr hh hn ω y hfull hβ
    by_cases hY : Polynomial.derivative R = 0
    · by_cases hX : P64Incidence.dXPoly R = 0
      · let T := twistPoly R
        have hback : frobLift T = R := frobLift_twistPoly R hY hX
        have hTi : Irreducible T := irreducible_twistPoly R hirr hY hX
        have hdeg : R.natDegree = T.natDegree * 2 := by rw [← hback, natDegree_frobLift]
        have hTpos : 1 ≤ T.natDegree := by omega
        have hTlt : T.natDegree < h := by omega
        have hspace : wd R 1048575 = 2 * wd T 1048575 := by
          rw [← hback, spatial_weight_frobLift T hTi.ne_zero 1048575]
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
        have hF' : 2 * T.natDegree * wd T 1048575 < Fintype.card F := by
          calc _ ≤ 2 * R.natDegree * wd R 1048575 :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
            _ < _ := hF
        have hm : ∀ i, lineOrd R (ω i) (y i) = 2 * lineOrd T (ω i) (y' i) := by
          intro i
          rw [← hback, lineOrd_frobLift T hTi.ne_zero]
        have hβ' : T.natDegree * 1481911 < ∑ i, lineOrd T (ω i) (y' i) := by
          simp_rw [hm] at hβ
          rw [← Finset.mul_sum, hdeg] at hβ
          apply Nat.lt_of_mul_lt_mul_left (a := 2)
          convert hβ using 1 <;> ring
        have hfull' : (fullLines T ω y').card < 208984 := by
          rwa [← hback, fullLines_frobLift T hTi.ne_zero] at hfull
        have hprofile' : 2 * (T.natDegree : ℤ) * wd T 1048575 - T.natDegree ^ 2 * 1048575 -
            (∑ i, (lineOrd T (ω i) (y' i) : ℤ) ^ 2) ≤ 65536 * T.natDegree ^ 2 := by
          rw [hdeg, hspace] at hprofile
          simp_rw [hm, Nat.cast_mul, Nat.cast_ofNat, mul_pow] at hprofile
          rw [← Finset.mul_sum] at hprofile
          nlinarith only [hprofile]
        have hP' : ∀ t ∈ S', (P' t).natDegree ≤ 1048575 := fun t ht => hP _ (hSq t ht)
        have hcurve' : ∀ t ∈ S', ev T t (P' t) = 0 := by
          intro t ht
          have hc := hcurve _ (hSq t ht)
          rw [← hback] at hc
          have he : ev (frobLift T) (t ^ 2) (P' t) = (ev T t (P' t)) ^ 2 :=
            triEval_frobLift T t (P' t)
          exact eq_zero_of_pow_eq_zero (he.symm.trans hc)
        have hcard' : ∀ t ∈ S', 1482911 ≤ (A' t).card := fun t ht => hcard _ (hSq t ht)
        have hmatch' : ∀ t ∈ S', ∀ i, i ∈ A' t ↔ (P' t).eval (ω i) = (y' i).eval t := by
          intro t ht i
          simpa [P', y', Polynomial.expand_eval] using hmatch _ (hSq t ht) i
        have hsupp' : ∀ t ∈ S', wd T 1048575 < ∑ i ∈ A' t, lineOrd T (ω i) (y' i) := by
          intro t ht
          have hs := hsupport _ (hSq t ht)
          simp_rw [hm] at hs
          rw [← Finset.mul_sum, hspace] at hs
          change wd T 1048575 < ∑ i ∈ A (t ^ 2), lineOrd T (ω i) (y' i)
          omega
        have hbT : S'.card ≤ 41 * 2097152 * d + 4 * T.natDegree * d := by
          exact ih T.natDegree hTlt (R := T) (hirr := hTi) (hh := hTpos)
            (q := 2 * q) (hq := by omega) (hRyz := hwt) (hF := hF')
            (y := y') (hy := hy') (hβ := hβ') (hfull := hfull') (hprofile := hprofile')
            (S := S') (P := P') (A := A') (hP := hP') (hcurve := hcurve')
            (hcard := hcard') (hmatch := hmatch') (hsupport := hsupp') (heq := rfl)
        rw [hScard] at hbT
        exact hbT.trans (Nat.add_le_add_left (Nat.mul_le_mul_right d
          (Nat.mul_le_mul_left 4 (by omega))) _)
      · have hc := P64Incidence.card_le_of_inseparable R hirr (by omega) hY hX (wd R 1048575)
          (P64Resultant.coeff_natDegree_le_weighted R 1048575) hF S P hcurve
        have hyz := P64C6All.yz_le_twice R hirr.ne_zero q d hq hRyz
        have hm := Nat.mul_le_mul_left (2 * R.natDegree) hyz
        nlinarith
    · have hc := separable_card_le R hirr hthree hY (wd R 1048575) q d 2097152 hq le_rfl hRyz
        hn hF ω y hy hprofile (by omega) S P A hP hcurve hcard hmatch hsupport
      nlinarith

end P64C7All
end ProximityPrize.SubmissionBinaryLower
