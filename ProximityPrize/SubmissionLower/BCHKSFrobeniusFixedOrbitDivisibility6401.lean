import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveOrbitOverlapDescent6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveNormTerminal6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusHilbert90Normalization6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusFixedOrbitDivisibility6401
open Polynomial
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusHilbert90Normalization6401
open BCHKSExtremePrimitiveRecursiveNormTerminal6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section Generic
variable {F : Type} [Field F]
theorem map_dvd_of_dvd_fixed6401
    (sigma : F →+* F) (P H : F[X])
    (hfixed : H.map sigma = H) (hdiv : P ∣ H) :
    P.map sigma ∣ H := by
  obtain ⟨T, hT⟩ := hdiv
  refine ⟨T.map sigma, ?_⟩
  calc
    H = H.map sigma := hfixed.symm
    _ = (P * T).map sigma := by rw [← hT]
    _ = P.map sigma * T.map sigma := by rw [Polynomial.map_mul]
theorem all_six_orbitFactors_dvd_fixed6401
    (sigma : F →+* F) (P H : F[X])
    (hfixed : H.map sigma = H) (hdiv : P ∣ H) :
    P ∣ H ∧
      frobeniusOne6401 sigma P ∣ H ∧
      frobeniusTwo6401 sigma P ∣ H ∧
      frobeniusThree6401 sigma P ∣ H ∧
      frobeniusFour6401 sigma P ∣ H ∧
      frobeniusFive6401 sigma P ∣ H := by
  have h1 : frobeniusOne6401 sigma P ∣ H := by
    simpa [frobeniusOne6401] using
      map_dvd_of_dvd_fixed6401 sigma P H hfixed hdiv
  have h2 : frobeniusTwo6401 sigma P ∣ H := by
    simpa [frobeniusTwo6401] using
      map_dvd_of_dvd_fixed6401 sigma
        (frobeniusOne6401 sigma P) H hfixed h1
  have h3 : frobeniusThree6401 sigma P ∣ H := by
    simpa [frobeniusThree6401] using
      map_dvd_of_dvd_fixed6401 sigma
        (frobeniusTwo6401 sigma P) H hfixed h2
  have h4 : frobeniusFour6401 sigma P ∣ H := by
    simpa [frobeniusFour6401] using
      map_dvd_of_dvd_fixed6401 sigma
        (frobeniusThree6401 sigma P) H hfixed h3
  have h5 : frobeniusFive6401 sigma P ∣ H := by
    simpa [frobeniusFive6401] using
      map_dvd_of_dvd_fixed6401 sigma
        (frobeniusFour6401 sigma P) H hfixed h4
  exact ⟨hdiv, h1, h2, h3, h4, h5⟩
def SuccessivelyCoprimeSixOrbit6401
    (sigma : F →+* F) (P : F[X]) : Prop :=
  IsCoprime P (frobeniusOne6401 sigma P) ∧
    IsCoprime (P * frobeniusOne6401 sigma P)
      (frobeniusTwo6401 sigma P) ∧
    IsCoprime (P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P) (frobeniusThree6401 sigma P) ∧
    IsCoprime (P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P * frobeniusThree6401 sigma P)
      (frobeniusFour6401 sigma P) ∧
    IsCoprime (P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P * frobeniusThree6401 sigma P *
      frobeniusFour6401 sigma P) (frobeniusFive6401 sigma P)
theorem polynomialFrobeniusNormSix_dvd_fixed6401
    (sigma : F →+* F) (P H : F[X])
    (hfixed : H.map sigma = H) (hdiv : P ∣ H)
    (hcoprime : SuccessivelyCoprimeSixOrbit6401 sigma P) :
    polynomialFrobeniusNormSix sigma P ∣ H := by
  have hd := all_six_orbitFactors_dvd_fixed6401 sigma P H hfixed hdiv
  have hd01 : P * frobeniusOne6401 sigma P ∣ H :=
    hcoprime.1.mul_dvd hd.1 hd.2.1
  have hd012 : P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P ∣ H :=
    hcoprime.2.1.mul_dvd hd01 hd.2.2.1
  have hd0123 : P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P * frobeniusThree6401 sigma P ∣ H :=
    hcoprime.2.2.1.mul_dvd hd012 hd.2.2.2.1
  have hd01234 : P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P * frobeniusThree6401 sigma P *
      frobeniusFour6401 sigma P ∣ H :=
    hcoprime.2.2.2.1.mul_dvd hd0123 hd.2.2.2.2.1
  have hd012345 : P * frobeniusOne6401 sigma P *
      frobeniusTwo6401 sigma P * frobeniusThree6401 sigma P *
      frobeniusFour6401 sigma P * frobeniusFive6401 sigma P ∣ H :=
    hcoprime.2.2.2.2.mul_dvd hd01234 hd.2.2.2.2.2
  simpa [polynomialFrobeniusNormSix, frobeniusOne6401,
    frobeniusTwo6401, frobeniusThree6401, frobeniusFour6401,
    frobeniusFive6401] using hd012345
theorem exists_fixedOrbitResidual6401
    (sigma : F →+* F) (P H : F[X]) (K d : Nat)
    (hP : P ≠ 0) (hH : H ≠ 0)
    (hPdegree : P.natDegree = d) (hHdegree : H.natDegree ≤ K)
    (hfixed : H.map sigma = H) (hdiv : P ∣ H)
    (hcoprime : SuccessivelyCoprimeSixOrbit6401 sigma P) :
    ∃ T : F[X],
      T ≠ 0 ∧ H = polynomialFrobeniusNormSix sigma P * T ∧
      6 * d + T.natDegree = H.natDegree ∧
      T.natDegree ≤ K - 6 * d := by
  have hnormDiv := polynomialFrobeniusNormSix_dvd_fixed6401
    sigma P H hfixed hdiv hcoprime
  obtain ⟨T, hTfactor⟩ := hnormDiv
  have hnormNe := polynomialFrobeniusNormSix_ne_zero6401 sigma P hP
  have hT : T ≠ 0 := by
    intro hzero
    apply hH
    rw [hTfactor, hzero, mul_zero]
  have hnormDegree :
      (polynomialFrobeniusNormSix sigma P).natDegree = 6 * d := by
    rw [polynomialFrobeniusNormSix_natDegree_eq6401 sigma P hP]
    omega
  have hdegree : 6 * d + T.natDegree = H.natDegree := by
    rw [hTfactor, Polynomial.natDegree_mul hnormNe hT, hnormDegree]
  refine ⟨T, hT, hTfactor, hdegree, ?_⟩
  omega
end Generic
theorem benchmark_fixedOrbitResidual_degree_le_18536_6401
    {F : Type} [Field F]
    (sigma : F →+* F) (P H : F[X])
    (hP : P ≠ 0) (hH : H ≠ 0)
    (hPdegree : P.natDegree = 22507)
    (hHdegree : H.natDegree ≤ 153578)
    (hfixed : H.map sigma = H) (hdiv : P ∣ H)
    (hcoprime : SuccessivelyCoprimeSixOrbit6401 sigma P) :
    ∃ T : F[X],
      T ≠ 0 ∧ H = polynomialFrobeniusNormSix sigma P * T ∧
      T.natDegree ≤ 18536 := by
  obtain ⟨T, hT, hfactor, _hdegree, hbound⟩ :=
    exists_fixedOrbitResidual6401 sigma P H 153578 22507
      hP hH hPdegree hHdegree hfixed hdiv hcoprime
  exact ⟨T, hT, hfactor, by norm_num at hbound ⊢; exact hbound⟩
end BCHKSFrobeniusFixedOrbitDivisibility6401
end ProximityPrize.SubmissionLower
