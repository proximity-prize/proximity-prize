import ProximityPrize.SubmissionLower.Numeric2Aux

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace H2429ConjugateResidues

open Polynomial P1
open scoped Polynomial

private theorem map_residue {E Q S : K[X]} {z : K} (τ : K →+* K)
    (fixed : S.map τ = S) (residue : E ∣ S - C z * Q) :
    E.map τ ∣ S - C (τ z) * Q.map τ := by
  simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, fixed]
    using Polynomial.map_dvd τ residue

private theorem cross_of_residues {E Q S S₀ : K[X]} {z z₀ a b : K}
    (h : E ∣ S - C z * Q) (h₀ : E ∣ S₀ - C z₀ * Q)
    (cancel : C a * C z = C b * C z₀) : E ∣ C a * S - C b * S₀ := by
  have eq : C a * (S - C z * Q) - C b * (S₀ - C z₀ * Q) =
      C a * S - C b * S₀ := by
    calc
      _ = (C a * S - C b * S₀) - (C a * C z - C b * C z₀) * Q := by ring
      _ = _ := by simp only [cancel, sub_self, zero_mul, sub_zero]
  rw [← eq]
  exact dvd_sub (h.mul_left _) (h₀.mul_left _)

private theorem coprime_of_sub_dvd {E U V : K[X]}
    (hc : IsCoprime U E) (hd : E ∣ V - U) : IsCoprime V E := by
  obtain ⟨a, b, hab⟩ := hc
  obtain ⟨q, hq⟩ := hd
  refine ⟨a, b - a * q, ?_⟩
  linear_combination hab + a * hq

private theorem coprime_const {a : K} (ha : a ≠ 0) (E : K[X]) : IsCoprime (C a) E := by
  refine ⟨C (a⁻¹), 0, ?_⟩
  rw [zero_mul, add_zero, ← C_mul, inv_mul_cancel₀ ha, C_1]

section

variable {ι : Type*}
variable {E Q : K[X]} {τ : K →+* K} {Γ : Finset ι}
variable {S : ι → K[X]} {z : ι → K} {j₀ : ι}

/-- The common positive-degree divisor forces one proportionality for all marked slopes. -/
theorem proportional {G : K[X]} (hG : 0 < G.natDegree)
    (left : G ∣ E) (right : G ∣ E.map τ) (unitQ : IsCoprime Q E)
    (residue : ∀ j ∈ Γ, E ∣ S j - C (z j) * Q)
    (fixed : ∀ j ∈ Γ, (S j).map τ = S j) (hj₀ : j₀ ∈ Γ) :
    ∀ j ∈ Γ, τ (z j) * z j₀ = z j * τ (z j₀) := by
  intro j hj
  have conjugate : G ∣ C (τ (z j)) * S j₀ - C (τ (z j₀)) * S j :=
    right.trans (cross_of_residues (map_residue τ (fixed _ hj₀) (residue _ hj₀))
      (map_residue τ (fixed _ hj) (residue _ hj)) (mul_comm _ _))
  have original : G ∣ C (τ (z j)) * (S j₀ - C (z j₀) * Q) -
      C (τ (z j₀)) * (S j - C (z j) * Q) :=
    dvd_sub ((left.trans (residue _ hj₀)).mul_left _) ((left.trans (residue _ hj)).mul_left _)
  have product : G ∣ Q * C (τ (z j) * z j₀ - z j * τ (z j₀)) := by
    have eq : Q * C (τ (z j) * z j₀ - z j * τ (z j₀)) =
        (C (τ (z j)) * S j₀ - C (τ (z j₀)) * S j) -
        (C (τ (z j)) * (S j₀ - C (z j₀) * Q) -
          C (τ (z j₀)) * (S j - C (z j) * Q)) := by
      rw [C_sub, C_mul, C_mul]
      ring
    rw [eq]
    exact dvd_sub conjugate original
  have hd := (unitQ.of_isCoprime_of_dvd_right left).symm.dvd_of_dvd_mul_left product
  apply sub_eq_zero.mp
  by_contra hn
  have hC : (C (τ (z j) * z j₀ - z j * τ (z j₀)) : K[X]) ≠ 0 := by
    intro h
    exact hn (C_inj.mp (by simpa only [map_zero] using h))
  have hdeg := natDegree_le_of_dvd hd hC
  simp only [natDegree_C] at hdeg
  omega

/-- A common multiple with the least-common-multiple property carries the combined residues. -/
theorem proper_residue {H : K[X]} (monic : H.Monic) (hH : 0 < H.natDegree)
    (left : E ∣ H) (right : E.map τ ∣ H)
    (least : ∀ D : K[X], E ∣ D → E.map τ ∣ D → H ∣ D)
    (unitQ : IsCoprime Q E) (residue : ∀ j ∈ Γ, E ∣ S j - C (z j) * Q)
    (fixed : ∀ j ∈ Γ, (S j).map τ = S j)
    (hj₀ : j₀ ∈ Γ) (hz₀ : z j₀ ≠ 0)
    (prop : ∀ j ∈ Γ, τ (z j) * z j₀ = z j * τ (z j₀)) :
    let R := (C ((z j₀)⁻¹) * S j₀) %ₘ H
    R.natDegree < H.natDegree ∧ IsCoprime R H ∧
      (∀ j ∈ Γ, H ∣ S j - C (z j) * R) := by
  intro R
  let T := C ((z j₀)⁻¹) * S j₀
  have hRT : H ∣ R - T := dvd_modByMonic_sub T H
  have hS₀ : IsCoprime (S j₀) E :=
    coprime_of_sub_dvd ((coprime_const hz₀ E).mul_left unitQ) (residue _ hj₀)
  have hS₀τ : IsCoprime (S j₀) (E.map τ) := by
    have h := hS₀.map (mapRingHom τ)
    change IsCoprime ((S j₀).map τ) (E.map τ) at h
    rwa [fixed _ hj₀] at h
  have hS₀H : IsCoprime (S j₀) H :=
    (hS₀.mul_right hS₀τ).of_isCoprime_of_dvd_right
      (least _ (dvd_mul_right E (E.map τ)) (dvd_mul_left (E.map τ) E))
  have hT : IsCoprime T H := (coprime_const (inv_ne_zero hz₀) H).mul_left hS₀H
  have hne : H ≠ 1 := by intro h; simpa [h] using hH
  refine ⟨natDegree_modByMonic_lt T monic hne, coprime_of_sub_dvd hT hRT, ?_⟩
  intro j hj
  have cross : H ∣ C (z j₀) * S j - C (z j) * S j₀ := by
    apply least
    · exact cross_of_residues (residue _ hj) (residue _ hj₀) (mul_comm _ _)
    · apply cross_of_residues (map_residue τ (fixed _ hj) (residue _ hj))
        (map_residue τ (fixed _ hj₀) (residue _ hj₀))
      rw [← C_mul, ← C_mul, mul_comm (z j₀), prop _ hj]
  have hinv : (C ((z j₀)⁻¹) * C (z j₀) : K[X]) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hz₀, C_1]
  have eq : C ((z j₀)⁻¹) * (C (z j₀) * S j - C (z j) * S j₀) -
      C (z j) * (R - T) = S j - C (z j) * R := by
    calc
      _ = (C ((z j₀)⁻¹) * C (z j₀)) * S j - C (z j) * R := by
        dsimp only [T]
        ring
      _ = _ := by rw [hinv, one_mul]
  rw [← eq]
  exact dvd_sub (cross.mul_left _) (hRT.mul_left _)

/-- A monic least common multiple divides the product and has at least the old degree. -/
theorem exists_monic_lcm (monic : E.Monic) :
    ∃ H : K[X], H.Monic ∧ E ∣ H ∧ E.map τ ∣ H ∧
      (∀ D : K[X], E ∣ D → E.map τ ∣ D → H ∣ D) ∧
      H ∣ E * E.map τ ∧ E.natDegree ≤ H.natDegree := by
  let L := GCDMonoid.lcm E (E.map τ)
  have hleft : E ∣ L := dvd_lcm_left _ _
  have hright : E.map τ ∣ L := dvd_lcm_right _ _
  have hleast (D : K[X]) (h₁ : E ∣ D) (h₂ : E.map τ ∣ D) : L ∣ D := lcm_dvd h₁ h₂
  have hprod : L ∣ E * E.map τ :=
    hleast _ (dvd_mul_right E (E.map τ)) (dvd_mul_left (E.map τ) E)
  have hL : L ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hprod
    exact (mul_ne_zero monic.ne_zero (monic.map τ).ne_zero) hprod
  have hnormalized := monic_normalize hL
  have hdiv : E ∣ normalize L := dvd_normalize_iff.mpr hleft
  exact ⟨normalize L, hnormalized, hdiv, dvd_normalize_iff.mpr hright,
    fun D h₁ h₂ => normalize_dvd_iff.mpr (hleast D h₁ h₂),
    normalize_dvd_iff.mpr hprod, natDegree_le_of_dvd hdiv hnormalized.ne_zero⟩

end

end H2429ConjugateResidues
