import ProximityPrize.SubmissionLower.Koala6831IntrinsicPowers
import Mathlib.RingTheory.Polynomial.Subring

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open Polynomial RCN002 RCN005 RCN009 RCN011 RCN371

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K E : Type} [Field K] [Field E]

private theorem polynomial_eval₂_mem_powerField (p : ℕ) [ExpChar E p]
    (φ : K →+* E) (hφ : ∀ a, φ a ∈ powerField E p)
    (x : E) (hx : x ∈ powerField E p) (f : Polynomial K) :
    f.eval₂ φ x ∈ powerField E p := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [Polynomial.eval₂_add]
      exact (powerField E p).add_mem hf hg
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      exact (powerField E p).mul_mem (hφ a) ((powerField E p).pow_mem hx n)

private theorem coefficients_zero_over_nonpower (p : ℕ) [ExpChar E p] (hp : p.Prime)
    (r : E) (hr : r ∉ powerField E p) (F : Polynomial E)
    (hpow : ∀ j, F.coeff j ∈ powerField E p)
    (hdeg : F.natDegree < p) (heval : F.eval r = 0) :
    F = 0 := by
  classical
  let S := (powerField E p).toSubring
  have hsub : (↑F.coeffs : Set E) ⊆ S := by
    intro a ha
    have ha' : a ∈ F.coeffs := ha
    rw [Polynomial.coeffs] at ha'
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha'
    exact hpow j
  let f : Polynomial (powerField E p) := F.toSubring S hsub
  have hm : f.map (algebraMap (powerField E p) E) = F :=
    Polynomial.map_toSubring F S hsub
  have hfdeg : f.natDegree < p := by
    exact (Polynomial.natDegree_toSubring F S hsub).trans_lt hdeg
  have hfroot : aeval r f = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hm, heval]
  rw [← hm, eq_zero_of_aeval_powerField p hp r hr f hfdeg hfroot, Polynomial.map_zero]

theorem plane_dvd_of_inner_power [Algebra K E] (p : ℕ) [ExpChar E p] (hp : p.Prime)
    (y z : E) (hy : y ∈ powerField E p) (hz : z ∉ powerField E p)
    (hcoeff : ∀ a : K, algebraMap K E a ∈ powerField E p)
    (G T : Polynomial (Polynomial K)) (hG : Irreducible G)
    (hGz : G.natDegree < p) (hTz : T.natDegree < p)
    (hGroot : RCN361.planeEval K E y z G = 0)
    (hTroot : RCN361.planeEval K E y z T = 0) :
    G ∣ T := by
  let φ := Polynomial.eval₂RingHom (algebraMap K E) y
  have houter (P : Polynomial (Polynomial K)) (hdeg : P.natDegree < p)
      (hroot : RCN361.planeEval K E y z P = 0) :
      P.map φ = 0 := by
    apply coefficients_zero_over_nonpower p hp z hz
    · intro j
      rw [Polynomial.coeff_map]
      exact polynomial_eval₂_mem_powerField p (algebraMap K E) hcoeff y hy (P.coeff j)
    · exact Polynomial.natDegree_map_le.trans_lt hdeg
    · exact hroot
  have hcoeffG (j : ℕ) : aeval y (G.coeff j) = 0 := by
    have h := congrArg (fun P : Polynomial E => P.coeff j) (houter G hGz hGroot)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, φ,
      Polynomial.coe_eval₂RingHom, Polynomial.aeval_def] using h
  have hcoeffT (j : ℕ) : aeval y (T.coeff j) = 0 := by
    have h := congrArg (fun P : Polynomial E => P.coeff j) (houter T hTz hTroot)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, φ,
      Polynomial.coe_eval₂RingHom, Polynomial.aeval_def] using h
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hG.ne_zero
  have hyint : IsIntegral K y := isAlgebraic_iff_isIntegral.mp
    ⟨G.coeff j, Polynomial.mem_support_iff.mp hj, hcoeffG j⟩
  have hnonunit : ¬ IsUnit (Polynomial.C (minpoly K y) : Polynomial (Polynomial K)) := by
    intro h
    have hu := Polynomial.isUnit_C.mp h
    exact (minpoly.natDegree_pos hyint).ne' (Polynomial.natDegree_eq_zero_of_isUnit hu)
  have hdivG : Polynomial.C (minpoly K y) ∣ G :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr (fun j => minpoly.dvd K y (hcoeffG j))
  have hdivT : Polynomial.C (minpoly K y) ∣ T :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr (fun j => minpoly.dvd K y (hcoeffT j))
  exact ((hG.dvd_iff.mp hdivG).resolve_left hnonunit).dvd.trans hdivT

section Curve

variable {F : Type} [Field F]
variable (P : Ideal (MvPolynomial (Fin 3) F)) [P.IsPrime]

theorem rationalBaseEmbedding_mem_powerField (i : Fin 3)
    (ht : Transcendental F (coordinate F P i)) (p : ℕ)
    [ExpChar (CoordinateField F P) p] [PerfectRing F p]
    (hi : coordinate F P i ∈ powerField (CoordinateField F P) p) (a : RatFunc F) :
    rationalBaseEmbedding F P i ht a ∈ powerField (CoordinateField F P) p := by
  have hpoly (g : Polynomial F) : rationalBaseEmbedding F P i ht
      (algebraMap (Polynomial F) (RatFunc F) g) ∈ powerField (CoordinateField F P) p := by
    rw [rationalBaseEmbedding_polynomial, Polynomial.aeval_def]
    exact polynomial_eval₂_mem_powerField p _ (algebraMap_mem_powerField p) _ hi g
  rw [← RatFunc.num_div_denom a, map_div₀]
  exact (powerField (CoordinateField F P) p).div_mem (hpoly a.num) (hpoly a.denom)

theorem proper_curve_projection_has_nonpower
    (order : Fin 3 ≃ Fin 3) (ht : Transcendental F (coordinate F P (order 0)))
    (p : ℕ) [ExpChar (CoordinateField F P) p] [PerfectRing F p] (hp : p.Prime)
    (hz : coordinate F P (order 1) ∉ powerField (CoordinateField F P) p)
    (G T : MvPolynomial (Fin 3) F)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hGdegree : G.degreeOf (order 1) < p) (hTdegree : T.degreeOf (order 1) < p) :
    coordinate F P (order 0) ∉ powerField (CoordinateField F P) p ∨
      coordinate F P (order 2) ∉ powerField (CoordinateField F P) p := by
  by_contra h
  push Not at h
  obtain ⟨hbase, hinner⟩ := h
  letI : Algebra (RatFunc F) (CoordinateField F P) := rationalBaseAlgebra F P (order 0) ht
  have hdvd : planeMap F order G ∣ planeMap F order T := by
    apply plane_dvd_of_inner_power p hp (coordinate F P (order 2)) (coordinate F P (order 1))
      hinner hz (rationalBaseEmbedding_mem_powerField P (order 0) ht p hbase)
    · exact planeMap_irreducible_of_component (K := F) (order := order) (P := P)
        (ht := ht) G hG hGmem
    · exact (planeMap_natDegree_le F order G).trans_lt hGdegree
    · exact (planeMap_natDegree_le F order T).trans_lt hTdegree
    · exact (actualPlane_root_iff F order P ht G).mpr hGmem
    · exact (actualPlane_root_iff F order P ht T).mpr hTmem
  exact hproper ((planeMap_dvd_iff_of_component (K := F) (order := order) (P := P)
    (ht := ht) G T hG hGmem).mp hdvd)

end Curve

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
