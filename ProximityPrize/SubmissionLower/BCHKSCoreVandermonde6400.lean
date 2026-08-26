import ProximityPrize.SubmissionLower.BCHKSFullCoreLineArrangement6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSCoreVandermonde6400
open Polynomial
open scoped BigOperators
open BCHKSFullCoreLineArrangement6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
theorem exists_coreQuotient_natDegree_le
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (P Q : F[X]) (k s : ℕ)
    (hcard : E.card + s = k)
    (hPdeg : P.natDegree ≤ k) (hQdeg : Q.natDegree ≤ k)
    (heval : ∀ x ∈ E, P.eval x = Q.eval x) :
    ∃ Cq : F[X], Cq.natDegree ≤ s ∧
      P = Q + coreLocator E * Cq := by
  classical
  let D : F[X] := P - Q
  have hDdeg : D.natDegree ≤ k := by
    dsimp [D]
    exact (Polynomial.natDegree_sub_le P Q).trans (max_le hPdeg hQdeg)
  have hDzero : ∀ x ∈ E, D.eval x = 0 := by
    intro x hx
    simp [D, heval x hx]
  obtain ⟨Cq, hfac⟩ :=
    coreLocator_dvd_of_eval_eq_zero E D hDzero
  have hCdeg : Cq.natDegree ≤ s := by
    by_cases hCq : Cq = 0
    · simp [hCq]
    · have hdegEq : D.natDegree = E.card + Cq.natDegree := by
        rw [hfac, (coreLocator_monic E).natDegree_mul' hCq,
          coreLocator_natDegree]
      omega
  refine ⟨Cq, hCdeg, ?_⟩
  dsimp [D] at hfac
  linear_combination hfac
theorem quotient_crossRelation_of_evaluations
    {F : Type*} [Field F] [DecidableEq F]
    (T : Finset F) (R0 R1 Rz : F[X]) (s : ℕ)
    (z0 z1 z : F)
    (hcard : T.card = s + 1)
    (hR0 : R0.natDegree ≤ s)
    (hR1 : R1.natDegree ≤ s)
    (hRz : Rz.natDegree ≤ s)
    (heval : ∀ x ∈ T,
      (z1 - z0) * (Rz.eval x - R0.eval x) =
        (z - z0) * (R1.eval x - R0.eval x)) :
    Polynomial.C (z1 - z0) * (Rz - R0) =
      Polynomial.C (z - z0) * (R1 - R0) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      (Polynomial.C (z1 - z0) * (Rz - R0))
      (Polynomial.C (z - z0) * (R1 - R0)) T
  · intro x hx
    simpa using heval x hx
  · have hleft :
        (Polynomial.C (z1 - z0) * (Rz - R0)).natDegree ≤ s :=
      (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_sub_le Rz R0).trans (max_le hRz hR0))
    have hright :
        (Polynomial.C (z - z0) * (R1 - R0)).natDegree ≤ s :=
      (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_sub_le R1 R0).trans (max_le hR1 hR0))
    rw [hcard]
    omega
theorem quotient_eval_crossRelation_of_owner_matches
    {F : Type*} [Field F]
    (G B0 B1 R0 R1 Rz P0 P1 Pz : F[X])
    (U0 U1 : F → F) (x z0 z1 z : F)
    (hG : G.eval x ≠ 0)
    (hP0 : P0 = B0 + Polynomial.C z0 * B1 + G * R0)
    (hP1 : P1 = B0 + Polynomial.C z1 * B1 + G * R1)
    (hPz : Pz = B0 + Polynomial.C z * B1 + G * Rz)
    (hm0 : P0.eval x = U0 x + z0 * U1 x)
    (hm1 : P1.eval x = U0 x + z1 * U1 x)
    (hmz : Pz.eval x = U0 x + z * U1 x) :
    (z1 - z0) * (Rz.eval x - R0.eval x) =
      (z - z0) * (R1.eval x - R0.eval x) := by
  have hE0 : G.eval x * R0.eval x =
      (U0 x - B0.eval x) + z0 * (U1 x - B1.eval x) := by
    rw [hP0] at hm0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hm0
    linear_combination hm0
  have hE1 : G.eval x * R1.eval x =
      (U0 x - B0.eval x) + z1 * (U1 x - B1.eval x) := by
    rw [hP1] at hm1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hm1
    linear_combination hm1
  have hEz : G.eval x * Rz.eval x =
      (U0 x - B0.eval x) + z * (U1 x - B1.eval x) := by
    rw [hPz] at hmz
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hmz
    linear_combination hmz
  apply mul_left_cancel₀ hG
  calc
    G.eval x * ((z1 - z0) * (Rz.eval x - R0.eval x)) =
        (z1 - z0) * (G.eval x * Rz.eval x - G.eval x * R0.eval x) := by ring
    _ = (z1 - z0) *
        (((U0 x - B0.eval x) + z * (U1 x - B1.eval x)) -
          ((U0 x - B0.eval x) + z0 * (U1 x - B1.eval x))) := by
      rw [hEz, hE0]
    _ = (z - z0) *
        (((U0 x - B0.eval x) + z1 * (U1 x - B1.eval x)) -
          ((U0 x - B0.eval x) + z0 * (U1 x - B1.eval x))) := by ring
    _ = (z - z0) *
        (G.eval x * R1.eval x - G.eval x * R0.eval x) := by
      rw [hE1, hE0]
    _ = G.eval x * ((z - z0) * (R1.eval x - R0.eval x)) := by ring
theorem owner_crossRelation_of_shared_tuple
    {F : Type*} [Field F] [DecidableEq F]
    (T : Finset F) (G B0 B1 R0 R1 Rz P0 P1 Pz : F[X])
    (U0 U1 : F → F) (s : ℕ) (z0 z1 z : F)
    (hcard : T.card = s + 1)
    (hR0 : R0.natDegree ≤ s)
    (hR1 : R1.natDegree ≤ s)
    (hRz : Rz.natDegree ≤ s)
    (hG : ∀ x ∈ T, G.eval x ≠ 0)
    (hP0 : P0 = B0 + Polynomial.C z0 * B1 + G * R0)
    (hP1 : P1 = B0 + Polynomial.C z1 * B1 + G * R1)
    (hPz : Pz = B0 + Polynomial.C z * B1 + G * Rz)
    (hm0 : ∀ x ∈ T, P0.eval x = U0 x + z0 * U1 x)
    (hm1 : ∀ x ∈ T, P1.eval x = U0 x + z1 * U1 x)
    (hmz : ∀ x ∈ T, Pz.eval x = U0 x + z * U1 x) :
    Polynomial.C (z1 - z0) * (Pz - P0) =
      Polynomial.C (z - z0) * (P1 - P0) := by
  have hR := quotient_crossRelation_of_evaluations T R0 R1 Rz s z0 z1 z
    hcard hR0 hR1 hRz (fun x hx ↦
      quotient_eval_crossRelation_of_owner_matches
        G B0 B1 R0 R1 Rz P0 P1 Pz U0 U1 x z0 z1 z
        (hG x hx) hP0 hP1 hPz (hm0 x hx) (hm1 x hx) (hmz x hx))
  rw [hP0, hP1, hPz]
  calc
    Polynomial.C (z1 - z0) *
          ((B0 + Polynomial.C z * B1 + G * Rz) -
            (B0 + Polynomial.C z0 * B1 + G * R0)) =
        Polynomial.C (z1 - z0) *
          (Polynomial.C (z - z0) * B1 + G * (Rz - R0)) := by
      simp only [Polynomial.C_sub]
      ring
    _ = Polynomial.C (z1 - z0) *
          (Polynomial.C (z - z0) * B1) +
        G * (Polynomial.C (z1 - z0) * (Rz - R0)) := by ring
    _ = Polynomial.C (z - z0) *
          (Polynomial.C (z1 - z0) * B1) +
        G * (Polynomial.C (z - z0) * (R1 - R0)) := by
      rw [hR]
      ring
    _ = Polynomial.C (z - z0) *
          ((B0 + Polynomial.C z1 * B1 + G * R1) -
            (B0 + Polynomial.C z0 * B1 + G * R0)) := by
      simp only [Polynomial.C_sub]
      ring
theorem owner_crossRelation_of_quotients
    {F : Type*} [Field F]
    (G B0 B1 R0 R1 Rz P0 P1 Pz : F[X])
    (z0 z1 z : F)
    (hP0 : P0 = B0 + Polynomial.C z0 * B1 + G * R0)
    (hP1 : P1 = B0 + Polynomial.C z1 * B1 + G * R1)
    (hPz : Pz = B0 + Polynomial.C z * B1 + G * Rz)
    (hR : Polynomial.C (z1 - z0) * (Rz - R0) =
      Polynomial.C (z - z0) * (R1 - R0)) :
    Polynomial.C (z1 - z0) * (Pz - P0) =
      Polynomial.C (z - z0) * (P1 - P0) := by
  rw [hP0, hP1, hPz]
  calc
    Polynomial.C (z1 - z0) *
          ((B0 + Polynomial.C z * B1 + G * Rz) -
            (B0 + Polynomial.C z0 * B1 + G * R0)) =
        Polynomial.C (z1 - z0) *
          (Polynomial.C (z - z0) * B1 + G * (Rz - R0)) := by
      simp only [Polynomial.C_sub]
      ring
    _ = Polynomial.C (z1 - z0) *
          (Polynomial.C (z - z0) * B1) +
        G * (Polynomial.C (z1 - z0) * (Rz - R0)) := by ring
    _ = Polynomial.C (z - z0) *
          (Polynomial.C (z1 - z0) * B1) +
        G * (Polynomial.C (z - z0) * (R1 - R0)) := by
      rw [hR]
      ring
    _ = Polynomial.C (z - z0) *
          ((B0 + Polynomial.C z1 * B1 + G * R1) -
            (B0 + Polynomial.C z0 * B1 + G * R0)) := by
      simp only [Polynomial.C_sub]
      ring
theorem exists_affineLine_of_owner_crossRelations
    {F : Type*} [Field F]
    (S : Finset F) (P : F → F[X]) (z0 z1 : F)
    (hz : z0 ≠ z1)
    (hcross : ∀ z ∈ S,
      Polynomial.C (z1 - z0) * (P z - P z0) =
        Polynomial.C (z - z0) * (P z1 - P z0)) :
    ∃ p0 p1 : F[X], ∀ z ∈ S,
      P z = p0 + Polynomial.C z * p1 := by
  let a : F := (z1 - z0)⁻¹
  let p1 : F[X] := Polynomial.C a * (P z1 - P z0)
  let p0 : F[X] := P z0 - Polynomial.C z0 * p1
  refine ⟨p0, p1, ?_⟩
  intro z hzS
  have hne : z1 - z0 ≠ 0 := sub_ne_zero.mpr hz.symm
  have hCne : Polynomial.C (z1 - z0) ≠ (0 : F[X]) :=
    by simpa using Polynomial.C_injective.ne hne
  have h := hcross z hzS
  have hdiff : P z - P z0 =
      Polynomial.C ((z1 - z0)⁻¹) *
        (Polynomial.C (z - z0) * (P z1 - P z0)) := by
    apply mul_left_cancel₀ (a := Polynomial.C (z1 - z0)) hCne
    rw [h]
    calc
      Polynomial.C (z - z0) * (P z1 - P z0) =
          (1 : F[X]) * (Polynomial.C (z - z0) * (P z1 - P z0)) := by
        rw [one_mul]
      _ = (Polynomial.C (z1 - z0) * Polynomial.C ((z1 - z0)⁻¹)) *
          (Polynomial.C (z - z0) * (P z1 - P z0)) := by
        rw [← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1]
      _ = Polynomial.C (z1 - z0) *
          (Polynomial.C ((z1 - z0)⁻¹) *
            (Polynomial.C (z - z0) * (P z1 - P z0))) := by ring
  dsimp [p0, p1, a]
  rw [(sub_eq_iff_eq_add).mp hdiff]
  simp only [Polynomial.C_sub]
  ring
theorem exists_degreeBoundedAffineLine_of_owner_crossRelations
    {F : Type*} [Field F]
    (S : Finset F) (P : F → F[X]) (z0 z1 : F) (k : ℕ)
    (hz : z0 ≠ z1)
    (hP0deg : (P z0).natDegree ≤ k)
    (hP1deg : (P z1).natDegree ≤ k)
    (hcross : ∀ z ∈ S,
      Polynomial.C (z1 - z0) * (P z - P z0) =
        Polynomial.C (z - z0) * (P z1 - P z0)) :
    ∃ p0 p1 : F[X], p0.natDegree ≤ k ∧ p1.natDegree ≤ k ∧
      ∀ z ∈ S, P z = p0 + Polynomial.C z * p1 := by
  let a : F := (z1 - z0)⁻¹
  let p1 : F[X] := Polynomial.C a * (P z1 - P z0)
  let p0 : F[X] := P z0 - Polynomial.C z0 * p1
  have hp1deg : p1.natDegree ≤ k := by
    dsimp [p1]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le (P z1) (P z0)).trans
        (max_le hP1deg hP0deg))
  have hp0deg : p0.natDegree ≤ k := by
    dsimp [p0]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hP0deg ((Polynomial.natDegree_C_mul_le _ _).trans hp1deg))
  refine ⟨p0, p1, hp0deg, hp1deg, ?_⟩
  intro z hzS
  have hne : z1 - z0 ≠ 0 := sub_ne_zero.mpr hz.symm
  have hCne : Polynomial.C (z1 - z0) ≠ (0 : F[X]) :=
    by simpa using Polynomial.C_injective.ne hne
  have h := hcross z hzS
  have hdiff : P z - P z0 =
      Polynomial.C ((z1 - z0)⁻¹) *
        (Polynomial.C (z - z0) * (P z1 - P z0)) := by
    apply mul_left_cancel₀ (a := Polynomial.C (z1 - z0)) hCne
    rw [h]
    calc
      Polynomial.C (z - z0) * (P z1 - P z0) =
          (1 : F[X]) * (Polynomial.C (z - z0) * (P z1 - P z0)) := by
        rw [one_mul]
      _ = (Polynomial.C (z1 - z0) * Polynomial.C ((z1 - z0)⁻¹)) *
          (Polynomial.C (z - z0) * (P z1 - P z0)) := by
        rw [← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1]
      _ = Polynomial.C (z1 - z0) *
          (Polynomial.C ((z1 - z0)⁻¹) *
            (Polynomial.C (z - z0) * (P z1 - P z0))) := by ring
  dsimp [p0, p1, a]
  rw [(sub_eq_iff_eq_add).mp hdiff]
  simp only [Polynomial.C_sub]
  ring
theorem exists_degreeBoundedAffineLine_of_sharedTuple_family
    {F : Type*} [Field F] [DecidableEq F]
    (T S : Finset F) (G B0 B1 : F[X]) (R P : F → F[X])
    (U0 U1 : F → F) (s k : ℕ)
    (hTcard : T.card = s + 1)
    (hScard : 1 < S.card)
    (hRdeg : ∀ z ∈ S, (R z).natDegree ≤ s)
    (hPdeg : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hG : ∀ x ∈ T, G.eval x ≠ 0)
    (hshape : ∀ z ∈ S,
      P z = B0 + Polynomial.C z * B1 + G * R z)
    (hmatch : ∀ z ∈ S, ∀ x ∈ T,
      (P z).eval x = U0 x + z * U1 x) :
    ∃ p0 p1 : F[X], p0.natDegree ≤ k ∧ p1.natDegree ≤ k ∧
      ∀ z ∈ S, P z = p0 + Polynomial.C z * p1 := by
  obtain ⟨z0, hz0, z1, hz1, hz01⟩ := Finset.one_lt_card.mp hScard
  have hcross : ∀ z ∈ S,
      Polynomial.C (z1 - z0) * (P z - P z0) =
        Polynomial.C (z - z0) * (P z1 - P z0) := by
    intro z hz
    exact owner_crossRelation_of_shared_tuple T G B0 B1
      (R z0) (R z1) (R z) (P z0) (P z1) (P z) U0 U1 s z0 z1 z
      hTcard (hRdeg z0 hz0) (hRdeg z1 hz1) (hRdeg z hz) hG
      (hshape z0 hz0) (hshape z1 hz1) (hshape z hz)
      (hmatch z0 hz0) (hmatch z1 hz1) (hmatch z hz)
  exact exists_degreeBoundedAffineLine_of_owner_crossRelations
    S P z0 z1 k hz01 (hPdeg z0 hz0) (hPdeg z1 hz1) hcross
end BCHKSCoreVandermonde6400
end ProximityPrize.SubmissionLower
