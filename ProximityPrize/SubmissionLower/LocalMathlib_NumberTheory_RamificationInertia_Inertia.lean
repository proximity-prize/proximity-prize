/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Finiteness_Quotient
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Ideal_Norm_AbsNorm

/-!
Permitted flat proof port of Mathlib.NumberTheory.RamificationInertia.Inertia.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 76a79db651e57cbb3f78c8cb8a94223caab520ffc0d29c2a6bb67559bda77085.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .






















 -/

section ProximityFlatProofPort


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

/-- .








 -/
noncomputable def inertiaDeg' : ℕ :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

--
@[simp]
theorem inertiaDeg'_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg' p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[deprecated (since := "2026-07-03")] alias inertiaDeg_of_subsingleton :=
  inertiaDeg'_of_subsingleton

@[simp]
theorem inertiaDeg'_algebraMap [P.LiesOver p] :
    inertiaDeg' p P = finrank (R ⧸ p) (S ⧸ P) := by
  rw [inertiaDeg', dif_pos (over_def P p).symm]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebraMap := inertiaDeg'_algebraMap

theorem inertiaDeg'_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

/-- . -/
theorem inertiaDeg'_pos' [P.IsPrime] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_pos' := inertiaDeg'_pos'

theorem inertiaDeg'_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    inertiaDeg' p P ≠ 0 :=
  (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_ne_zero := inertiaDeg'_ne_zero

lemma inertiaDeg'_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    inertiaDeg' p (P.comap e) = inertiaDeg' p P := by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e, comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
    exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg', dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
    rw [inertiaDeg', dif_neg (fun eq => h ⟨eq.symm⟩)]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_comap_eq := inertiaDeg'_comap_eq

lemma inertiaDeg'_map_eq (P : Ideal S)
    {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e : E) :
    inertiaDeg' p (P.map e) = inertiaDeg' p P := by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-03")] alias inertiaDeg_map_eq := inertiaDeg'_map_eq

theorem inertiaDeg'_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    [hP : P.LiesOver (⊥ : Ideal R)] :
    (⊥ : Ideal R).inertiaDeg' P = finrank R S := by
  rw [inertiaDeg', dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

@[deprecated (since := "2026-07-03")] alias inertiaDeg_bot := inertiaDeg'_bot

theorem inertiaDeg'_le_inertiaDeg' {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.Finite R T] (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P]
    [p.IsPrime] : inertiaDeg' P Q ≤ inertiaDeg' p Q := by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
  exact finrank_top_le_finrank_of_isScalarTower ..

@[deprecated (since := "2026-07-03")] alias inertiaDeg_le_inertiaDeg := inertiaDeg'_le_inertiaDeg'

end DecEq

section absNorm

lemma absNorm_eq_pow_inertiaDeg'_of_liesOver {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [IsDedekindDomain R] [Module.Free ℤ R] [Algebra S R] [Module.Finite S R]
    (P : Ideal R) (p : Ideal S) [P.LiesOver p] (hp : p.IsPrime) (hp_ne_bot : p ≠ ⊥) :
    absNorm P = absNorm p ^ (p.inertiaDeg' P) := by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  let _ : Field (S ⧸ p) := Quotient.field p
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

@[deprecated (since := "2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver :=
  absNorm_eq_pow_inertiaDeg'_of_liesOver

/-- .

 -/
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
    (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg' P) := by
  simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

/-- .

 -/
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℕ}
    (P : Ideal R) [P.LiesOver (span {(p : ℤ)})] (hp : p.Prime) :
    absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg' P) :=
  absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)

end absNorm

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- .

 -/
theorem inertiaDeg'_algebra_tower (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] : inertiaDeg' p I =
    inertiaDeg' p P * inertiaDeg' P I := by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg', dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  letI : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  letI : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₂.le
  letI : Algebra (R ⧸ p) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₃.le
  letI : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebra_tower := inertiaDeg'_algebra_tower

end tower

end Ideal
