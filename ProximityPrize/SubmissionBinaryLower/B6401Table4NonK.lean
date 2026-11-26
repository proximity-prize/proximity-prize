import ProximityPrize.SubmissionBinaryLower.B6401Table4Common
import ProximityPrize.SubmissionBinaryLower.B6401Char2ODE

set_option Elab.async false
set_option maxHeartbeats 2400000

/-!
# Table 4A Non-`K` Branches (`P0` and `b1c1`)

Proves exact satisfaction of `B6401T4Rows.buildT4ARows` for all 34 remaining Table 4A branches:
- `T4ABranch.p0 m21Nz rGt p0M10D4 q2M21M10` (10 valid branches, `nv = 23`),
- `T4ABranch.b1c1 rGt r4g4 bCase` (`bCase ∈ 0..5`, 24 branches, `nv = 21`),

plus reusable `AlgebraicClosure Fld`, squarefree decomposition, and `N_dom` char-2 ODE
helpers shared with `B6401Table4K`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401Table4NonK

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401IntFarkas B6401T4Rows B6401Char2ODE B6401Table4Common
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 1: Shared `AlgebraicClosure Fld`, Squarefree Decomposition, and `N_dom` ODE Helpers -/

lemma rootMultiplicity_pow_eq {E : Type*} [Field E] (f : E[X]) (hf : f ≠ 0) (n : ℕ) (a : E) :
    (f ^ n).rootMultiplicity a = n * f.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hf) hf), ih]; ring

lemma hasse_map_eq {E : Type*} [Field E] [CharP E 2] (ι : Fld →+* E) (k : ℕ) (f : Fld[X]) :
    hasse k (f.map ι) = (hasse k f).map ι := by
  apply Polynomial.ext; intro n
  rw [coeff_hasse, coeff_map, coeff_map, coeff_hasse, map_mul, map_natCast]

lemma zRaw_map {E : Type*} [Field E] [CharP E 2] (ι : Fld →+* E) (c0 c1 : Fld) (P Q : Fld[X]) :
    zRaw (ι c0) (ι c1) (P.map ι) (Q.map ι) = (zRaw c0 c1 P Q).map ι := by
  simp only [zRaw, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    derivative_map, hasse_map_eq]

lemma rootMultiplicity_comp_X_sq_map_nonK (f : Fld[X]) (hf : f ≠ 0) (a : AlgebraicClosure Fld) :
    ((f.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
      2 * (f.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hsq : (X - C a : E[X]) ^ 2 = X ^ 2 - C (a ^ 2) := by
    have h2 : (2 : E[X]) = 0 := CharTwo.two_eq_zero
    simp only [sub_eq_add_neg, CharTwo.neg_eq, map_pow]
    calc (X + C a) ^ 2 = X ^ 2 + 2 * X * C a + C a ^ 2 := by ring
      _ = X ^ 2 + C a ^ 2 := by rw [h2]; ring
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  have hfE : f.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hf
  have hfcE : (f.map ι).comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff _).mp hfE
  have hdvd_iff : ∀ k : ℕ, (X - C a) ^ (2 * k) ∣ (f.map ι).comp (X ^ 2) ↔ (X - C (a ^ 2)) ^ k ∣ f.map ι := by
    intro k; constructor
    · intro hd; rw [pow_mul, hsq] at hd
      have hcomp : ((X - C (a ^ 2)) ^ k).comp (X ^ 2) = (X ^ 2 - C (a ^ 2)) ^ k := by
        simp [pow_comp, sub_comp, X_comp, C_comp]
      rw [← hcomp] at hd; rcases hd with ⟨Q, hQ⟩
      have hQev : Q = (evenPart Q).comp (X ^ 2) := by
        have hdec := evenPart_add_X_oddPart Q
        have hodd : oddPart Q = 0 := by
          have h1 := congrArg Polynomial.derivative hQ
          rw [derivative_comp_X_sq_char2, derivative_mul, derivative_comp_X_sq_char2, zero_mul, zero_add] at h1
          have hQ' : Q.derivative = 0 := (mul_eq_zero.mp h1.symm).resolve_left (by
            rw [hcomp]; exact pow_ne_zero k (by rw [← hsq]; exact pow_ne_zero 2 (X_sub_C_ne_zero a)))
          have h2 := congrArg Polynomial.derivative hdec
          rw [derivative_even_odd_char2, hQ'] at h2; exact (comp_X_sq_eq_zero_iff _).mp h2
        rw [hodd, zero_comp, mul_zero, add_zero] at hdec; exact hdec.symm
      refine ⟨evenPart Q, ?_⟩
      apply sub_eq_zero.mp
      apply (comp_X_sq_eq_zero_iff _).mp; rw [sub_comp, mul_comp, hQ, ← hQev, sub_self]
    · rintro ⟨Q, hQ⟩; exact ⟨Q.comp (X ^ 2), by rw [pow_mul, hsq, hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp]⟩
  apply le_antisymm
  · have hd := pow_rootMultiplicity_dvd ((f.map ι).comp (X ^ 2)) a
    set r := ((f.map ι).comp (X ^ 2)).rootMultiplicity a
    have hr_ev : r % 2 = 0 := by
      by_contra hodd
      obtain ⟨Q, hQ⟩ := (hdvd_iff (r / 2)).mp ((pow_dvd_pow _ (by omega : 2 * (r / 2) ≤ r)).trans hd)
      have hQcomp : (f.map ι).comp (X ^ 2) = (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
        rw [hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp, ← hsq, ← pow_mul]
      have hmul_dvd : (X - C a) ^ (2 * (r / 2) + 1) ∣ (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
        rw [← hQcomp]; exact (pow_dvd_pow _ (by omega : 2 * (r / 2) + 1 ≤ r)).trans hd
      rw [pow_succ] at hmul_dvd
      have hd1 := (mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero a))).mp hmul_dvd
      have hQ0 : Q.eval (a ^ 2) = 0 := by simpa [IsRoot, eval_comp] using dvd_iff_isRoot.mp hd1
      rcases dvd_iff_isRoot.mpr hQ0 with ⟨W, hW⟩
      have hle := (le_rootMultiplicity_iff hfcE).mpr ((hdvd_iff (r / 2 + 1)).mpr ⟨W, by rw [hQ, hW]; ring⟩)
      omega
    have hle := (le_rootMultiplicity_iff hfE).mpr ((hdvd_iff (r / 2)).mp (by rw [show 2 * (r / 2) = r by omega]; exact hd))
    change r ≤ 2 * (f.map ι).rootMultiplicity (a ^ 2)
    omega
  · exact (le_rootMultiplicity_iff hfcE).mpr ((hdvd_iff _).mpr (pow_rootMultiplicity_dvd _ _))

/-- Exact squarefree decomposition over `Fld[X]`: every nonzero polynomial `f` factors as
`f = S^2 * H` with `Squarefree H`. -/
theorem exists_sq_mul_squarefree (f : Fld[X]) (hf : f ≠ 0) :
    ∃ S H : Fld[X], f = S ^ 2 * H ∧ Squarefree H := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | ind d ih =>
      by_cases hsf : Squarefree f
      · exact ⟨1, f, by simp, hsf⟩
      · unfold Squarefree at hsf; push Not at hsf
        obtain ⟨r, hr_dvd, hr_nu⟩ := hsf
        rcases hr_dvd with ⟨g, hg⟩
        have hr_ne : r ≠ 0 := by intro h0; subst h0; simp at hg; exact hf hg
        have hg_ne : g ≠ 0 := by intro h0; subst h0; simp at hg; exact hf hg
        have hr_pos : 0 < r.natDegree := by
          by_contra h0
          have hdeg0 : r.natDegree = 0 := by omega
          have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
          have hc0 : r.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hC; exact hr_ne hC
          exact hr_nu (by rw [hC]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
        have hlt : g.natDegree < d := by
          have hdeg := congrArg Polynomial.natDegree hg
          rw [natDegree_mul (mul_ne_zero hr_ne hr_ne) hg_ne, natDegree_mul hr_ne hr_ne] at hdeg
          omega
        obtain ⟨S', H, hSH, hHsf⟩ := ih g.natDegree hlt g hg_ne rfl
        refine ⟨r * S', H, ?_, hHsf⟩
        rw [hg, hSH]; ring

/-- In char 2 over the finite field `Fld`, a squarefree polynomial remains squarefree over
`E = AlgebraicClosure Fld` (every root has multiplicity `≤ 1`). -/
theorem rootMultiplicity_map_le_one_of_squarefree {H : Fld[X]} (hH : Squarefree H)
    (a : AlgebraicClosure Fld) :
    (H.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a ≤ 1 := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hHne : H ≠ 0 := hH.ne_zero
  by_contra hgt
  have h2 : 2 ≤ (H.map ι).rootMultiplicity a := by dsimp only [ι, E] at *; omega
  have hrootH : (H.map ι).eval a = 0 := by
    have hd : (X - C a) ^ 2 ∣ H.map ι := (pow_dvd_pow (X - C a) h2).trans (pow_rootMultiplicity_dvd _ a)
    rcases hd with ⟨w, hw⟩; rw [hw]; simp
  have hint : IsIntegral Fld a := (AlgebraicClosure.isAlgebraic Fld).isAlgebraic a |>.isIntegral
  let q : Fld[X] := minpoly Fld a
  have hq_irr : Irreducible q := minpoly.irreducible hint
  have hq_ne : q ≠ 0 := hq_irr.ne_zero
  have hq_dvd_H : q ∣ H := minpoly.dvd Fld a (by simpa [Polynomial.aeval_def, Polynomial.eval_map] using hrootH)
  rcases hq_dvd_H with ⟨H1, hH1⟩
  have hq'_ne : q.derivative ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := (derivative_eq_zero_iff_sq q).mp h0
    have hnu : ¬ IsUnit r := by
      intro hu; exact hq_irr.not_isUnit (by rw [hr]; exact hu.pow 2)
    have hmul := hq_irr.isUnit_or_isUnit (by rw [hr, sq] : q = r * r)
    exact hmul.elim hnu hnu
  have hq_cop_q' : IsCoprime q q.derivative := by
    have hndvd : ¬ q ∣ q.derivative := by
      intro hd
      have hle := natDegree_le_of_dvd hd hq'_ne
      have hlt : q.derivative.natDegree < q.natDegree := by
        have hpos : 0 < q.natDegree := by
          by_contra h0; apply hq'_ne
          have hC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : q.natDegree = 0)
          rw [hC, derivative_C]
        exact natDegree_derivative_lt (by omega)
      omega
    exact hq_irr.coprime_iff_not_dvd.mpr hndvd
  have hq_mult_le : (q.map ι).rootMultiplicity a ≤ 1 := by
    by_contra hq2
    have hd2 : (X - C a) ^ 2 ∣ q.map ι :=
      (pow_dvd_pow (X - C a) (by omega : 2 ≤ (q.map ι).rootMultiplicity a)).trans (pow_rootMultiplicity_dvd _ a)
    rcases hd2 with ⟨w, hw⟩
    have hd1 : X - C a ∣ q.map ι := (dvd_pow_self (X - C a) (by norm_num)).trans ⟨w, hw⟩
    have hd1' : X - C a ∣ (q.map ι).derivative := by
      have hsq : ((X - C a : E[X]) ^ 2).derivative = 0 := by
        rw [sq, derivative_mul, mul_comm ((X - C a : E[X]).derivative) (X - C a), CharTwo.add_self_eq_zero]
      rw [hw, derivative_mul, hsq, zero_mul, zero_add]
      exact dvd_mul_of_dvd_left (dvd_pow_self (X - C a) (by norm_num)) _
    have hcopE : IsCoprime (q.map ι) (q.map ι).derivative := by
      rw [derivative_map]; exact hq_cop_q'.map (Polynomial.mapRingHom ι)
    have hu := hcopE.isUnit_of_dvd' hd1 hd1'
    have h0 := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at h0; omega
  have hq_not_dvd_H1 : ¬ q ∣ H1 := by
    intro ⟨w, hw⟩
    have hq2H : q * q ∣ H := ⟨w, by rw [hH1, hw]; ring⟩
    exact hq_irr.not_isUnit (hH q hq2H)
  have hcop_q_H1 : IsCoprime (q.map ι) (H1.map ι) :=
    (hq_irr.coprime_iff_not_dvd.mpr hq_not_dvd_H1).map (Polynomial.mapRingHom ι)
  have hH1_eval : (H1.map ι).eval a ≠ 0 := by
    intro h0
    have hdq : X - C a ∣ q.map ι := dvd_iff_isRoot.mpr (by simpa [Polynomial.aeval_def, Polynomial.eval_map] using minpoly.aeval Fld a)
    have hdH1 : X - C a ∣ H1.map ι := dvd_iff_isRoot.mpr h0
    have hu := hcop_q_H1.isUnit_of_dvd' hdq hdH1
    have h0' := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at h0'; omega
  have hH1_mult : (H1.map ι).rootMultiplicity a = 0 :=
    rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hH1_eval)
  have hHmap : H.map ι = q.map ι * H1.map ι := by rw [hH1, Polynomial.map_mul]
  have hHmap_ne : H.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hHne
  rw [hHmap, rootMultiplicity_mul (by rwa [← hHmap]), hH1_mult, add_zero] at h2
  omega

/-- Over `E = AlgebraicClosure Fld`, the sum of `rootMultiplicity` of `p.map ι` over any
`Finset E` containing its roots equals `p.natDegree`. -/
theorem sum_rootMultiplicity_map_eq_natDegree [DecidableEq (AlgebraicClosure Fld)]
    (p : Fld[X]) (hp : p ≠ 0)
    (S_fin : Finset (AlgebraicClosure Fld))
    (hsub : (p.map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin) :
    ∑ a ∈ S_fin, (p.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a = p.natDegree := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have hpE : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hp
  have hdeg : (p.map ι).natDegree = p.natDegree := natDegree_map_eq_of_injective ι.injective p
  have hcard : (p.map ι).roots.card = (p.map ι).natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (p.map ι))
  rw [← hdeg, ← hcard]
  have hsum_roots : ∑ a ∈ (p.map ι).roots.toFinset, (p.map ι).rootMultiplicity a = (p.map ι).roots.card := by
    have hcnt : ∀ a ∈ (p.map ι).roots.toFinset, (p.map ι).rootMultiplicity a = (p.map ι).roots.count a :=
      fun a _ => (Polynomial.count_roots (p.map ι)).symm ▸ rfl
    rw [Finset.sum_congr rfl hcnt, Multiset.toFinset_sum_count_eq]
  rw [← hsum_roots]
  symm
  apply Finset.sum_subset hsub
  intro a _ hna
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hpE] at hna
  exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hna)

/-- Over `E = AlgebraicClosure Fld` in char 2, `a ↦ a^2` is bijective, so summing
`(p.map ι).rootMultiplicity (a^2)` over any `S_fin` containing all roots of `(p.comp (X^2)).map ι`
equals `p.natDegree`! -/
theorem sum_rootMultiplicity_sq_map_eq_natDegree [DecidableEq (AlgebraicClosure Fld)]
    (p : Fld[X]) (hp : p ≠ 0)
    (S_fin : Finset (AlgebraicClosure Fld))
    (hsub : ((p.comp (X ^ 2)).map (algebraMap Fld (AlgebraicClosure Fld))).roots.toFinset ⊆ S_fin) :
    ∑ a ∈ S_fin, (p.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity (a ^ 2) = p.natDegree := by
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  have h2mul : ∀ a : E, ((p.comp (X ^ 2)).map ι).rootMultiplicity a =
      2 * (p.map ι).rootMultiplicity (a ^ 2) := fun a => by
    rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
    -- Show (X - C a)^(2m) ∣ q(X^2) ↔ (X - C (a^2))^m ∣ q!
    have hq := p.map ι
    have hsq : (X - C a : E[X]) ^ 2 = X ^ 2 - C (a ^ 2) := by
      have h2 : (2 : E[X]) = 0 := CharTwo.two_eq_zero
      simp only [sub_eq_add_neg, CharTwo.neg_eq, map_pow]
      calc (X + C a) ^ 2 = X ^ 2 + 2 * X * C a + C a ^ 2 := by ring
        _ = X ^ 2 + C a ^ 2 := by rw [h2]; ring
    have hpE : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hp
    have hpcE : (p.map ι).comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff _).mp hpE
    have hdvd_iff : ∀ k : ℕ, (X - C a) ^ (2 * k) ∣ (p.map ι).comp (X ^ 2) ↔ (X - C (a ^ 2)) ^ k ∣ p.map ι := by
      intro k
      constructor
      · intro hd
        rw [pow_mul, hsq] at hd
        have hcomp : ((X - C (a ^ 2)) ^ k).comp (X ^ 2) = (X ^ 2 - C (a ^ 2)) ^ k := by
          simp [pow_comp, sub_comp, X_comp, C_comp]
        rw [← hcomp] at hd
        rcases hd with ⟨Q, hQ⟩
        have hQev : Q = (evenPart Q).comp (X ^ 2) := by
          have hdec := evenPart_add_X_oddPart Q
          have hodd : oddPart Q = 0 := by
            have h1 := congrArg Polynomial.derivative hQ
            rw [derivative_comp_X_sq_char2, derivative_mul, derivative_comp_X_sq_char2, zero_mul, zero_add] at h1
            have hQ' : Q.derivative = 0 := (mul_eq_zero.mp h1.symm).resolve_left (by
              rw [hcomp]; exact pow_ne_zero k (by rw [← hsq]; exact pow_ne_zero 2 (X_sub_C_ne_zero a)))
            have h2 := congrArg Polynomial.derivative hdec
            rw [derivative_even_odd_char2, hQ'] at h2
            exact (comp_X_sq_eq_zero_iff _).mp h2
          rw [hodd, zero_comp, mul_zero, add_zero] at hdec
          exact hdec.symm
        refine ⟨evenPart Q, ?_⟩
        apply sub_eq_zero.mp
        apply (comp_X_sq_eq_zero_iff _).mp
        rw [sub_comp, mul_comp, hQ, ← hQev, sub_self]
      · rintro ⟨Q, hQ⟩
        refine ⟨Q.comp (X ^ 2), ?_⟩
        rw [pow_mul, hsq, hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp]
    apply le_antisymm
    · have hd := pow_rootMultiplicity_dvd ((p.map ι).comp (X ^ 2)) a
      set r := ((p.map ι).comp (X ^ 2)).rootMultiplicity a
      have hr_ev : r % 2 = 0 := by
        by_contra hodd
        have h1 : (X - C a) ^ (2 * (r / 2)) ∣ (p.map ι).comp (X ^ 2) :=
          (pow_dvd_pow _ (by omega : 2 * (r / 2) ≤ r)).trans hd
        obtain ⟨Q, hQ⟩ := (hdvd_iff (r / 2)).mp h1
        have hQcomp : (p.map ι).comp (X ^ 2) = (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
          rw [hQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp, ← hsq, ← pow_mul]
        have hmul_dvd : (X - C a) ^ (2 * (r / 2) + 1) ∣ (X - C a) ^ (2 * (r / 2)) * Q.comp (X ^ 2) := by
          rw [← hQcomp]; exact (pow_dvd_pow _ (by omega : 2 * (r / 2) + 1 ≤ r)).trans hd
        rw [pow_succ] at hmul_dvd
        have hd1 : X - C a ∣ Q.comp (X ^ 2) :=
          (mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero a))).mp hmul_dvd
        have hQ0 : Q.eval (a ^ 2) = 0 := by
          have := dvd_iff_isRoot.mp hd1; simpa [IsRoot, eval_comp, eval_pow, eval_X] using this
        have hQd : X - C (a ^ 2) ∣ Q := dvd_iff_isRoot.mpr hQ0
        rcases hQd with ⟨W, hW⟩
        have hd2 : (X - C (a ^ 2)) ^ (r / 2 + 1) ∣ p.map ι := ⟨W, by rw [hQ, hW]; ring⟩
        have hle := (le_rootMultiplicity_iff hpcE).mpr ((hdvd_iff (r / 2 + 1)).mpr hd2)
        omega
      have h1 : (X - C (a ^ 2)) ^ (r / 2) ∣ p.map ι :=
        (hdvd_iff (r / 2)).mp (by rw [show 2 * (r / 2) = r by omega]; exact hd)
      have hle := (le_rootMultiplicity_iff hpE).mpr h1
      omega
    · exact (le_rootMultiplicity_iff hpcE).mpr ((hdvd_iff _).mpr (pow_rootMultiplicity_dvd _ _))
  have hsum := sum_rootMultiplicity_map_eq_natDegree (p.comp (X ^ 2))
    (mt (comp_X_sq_eq_zero_iff p).mp hp) S_fin hsub
  change ∑ a ∈ S_fin, ((p.comp (X ^ 2)).map ι).rootMultiplicity a = _ at hsum
  simp_rw [h2mul] at hsum
  rw [← Finset.mul_sum, natDegree_comp_X_sq] at hsum
  change ∑ a ∈ S_fin, (p.map ι).rootMultiplicity (a ^ 2) = p.natDegree
  omega

/-- Root multiplicity is preserved under field embedding `Fld →+* AlgebraicClosure Fld`. -/
lemma rootMultiplicity_map_eq (p : Fld[X]) (x : Fld) :
    (p.map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity
      (algebraMap Fld (AlgebraicClosure Fld) x) = p.rootMultiplicity x := by
  let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
  by_cases hp : p = 0
  · simp [hp]
  · have hpE : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hp
    apply le_antisymm
    · set m := (p.map ι).rootMultiplicity (ι x)
      have hd : (X - C (ι x)) ^ m ∣ p.map ι := pow_rootMultiplicity_dvd _ _
      have hd' : (X - C x) ^ m ∣ p := by
        apply pow_dvd_of_shift_coeff_zero p x m
        intro j hj
        apply ι.injective
        rw [map_zero, ← coeff_map, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]
        have hX : X ^ m ∣ (p.map ι).comp (C (ι x) + X) := by
          rcases hd with ⟨q, hq⟩
          refine ⟨q.comp (C (ι x) + X), ?_⟩
          rw [hq, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_left]
        exact X_pow_dvd_iff.mp hX j hj
      exact (le_rootMultiplicity_iff hp).mpr hd'
    · have hd : (X - C x) ^ p.rootMultiplicity x ∣ p := pow_rootMultiplicity_dvd p x
      rcases hd with ⟨q, hq⟩
      have hdE : (X - C (ι x)) ^ p.rootMultiplicity x ∣ p.map ι :=
        ⟨q.map ι, by
          conv_lhs => rw [hq]
          rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]⟩
      exact (le_rootMultiplicity_iff hpE).mpr hdE

/-- Any polynomial in `Fld[X]` whose nonzero coefficients occur only at indices divisible by 4
is a fourth power `L ^ 4`! Kept abstract in `tail` so the kernel never unfolds `Ndom`. -/
lemma exists_fourth_root_poly (tail : Fld[X]) (h4dvd : ∀ n, tail.coeff n ≠ 0 → 4 ∣ n) :
    ∃ L : Fld[X], L ^ 4 = tail := by
  let rt4 : Fld → Fld := fun a => (frobEquiv Fld).symm ((frobEquiv Fld).symm a)
  have hrt4 : ∀ a : Fld, (rt4 a) ^ 4 = a := fun a => by
    dsimp [rt4]
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, frobEquiv_symm_sq, frobEquiv_symm_sq]
  let L : Fld[X] := ∑ k ∈ Finset.range (tail.natDegree / 4 + 1), monomial k (rt4 (tail.coeff (4 * k)))
  refine ⟨L, ?_⟩
  have hpow4_sum : ∀ (s : Finset ℕ) (g : ℕ → Fld),
      (∑ k ∈ s, monomial k (g k)) ^ 4 = ∑ k ∈ s, monomial (4 * k) ((g k) ^ 4) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, zero_pow (by norm_num : 4 ≠ 0)]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, char2_add_pow_four, ih, Finset.sum_insert ha, monomial_pow, mul_comm a 4]
  dsimp only [L]; rw [hpow4_sum]
  apply Polynomial.ext; intro n
  rw [finset_sum_coeff]
  by_cases h4 : 4 ∣ n
  · obtain ⟨q, rfl⟩ := h4
    by_cases hq : q < tail.natDegree / 4 + 1
    · rw [Finset.sum_eq_single q]
      · rw [coeff_monomial, Finsupp.single_eq_same, hrt4]
      · intro k _ hne; rw [coeff_monomial, Finsupp.single_eq_of_ne (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr hq) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      apply Finset.sum_eq_zero; intro k hk
      have := Finset.mem_range.mp hk
      rw [coeff_monomial, Finsupp.single_eq_of_ne (by omega)]
  · have h0 : tail.coeff n = 0 := by by_contra h; exact h4 (h4dvd n h)
    rw [h0]
    apply Finset.sum_eq_zero; intro k _
    rw [coeff_monomial, Finsupp.single_eq_of_ne (by omega)]

/-- Exact structural decomposition of `Ndom` for char-2 ODE applications! -/
theorem Ndom_decomp :
    ∃ (c0 c1 : Fld) (L : Fld[X]),
      c0 ≠ 0 ∧
      Ndom = C c0 * X + C c1 * X ^ 2 + L ^ 4 ∧
      Ndom.natDegree = N ∧
      4 * L.natDegree = N ∧
      Ndom ≠ 0 ∧
      Ndom.derivative = C c0 ∧
      hasse 2 Ndom = C c1 ∧
      (∀ i : Idx, Ndom.rootMultiplicity (BinaryIRSProfile.domain i) = 1) ∧
      (∀ a : AlgebraicClosure Fld,
        (Ndom.map (algebraMap Fld (AlgebraicClosure Fld))).eval a = 0 ↔
          ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i)) := by
  obtain ⟨c0, c1, hc0, h4dvd⟩ := Ndom_structure
  obtain ⟨L, hL4⟩ := exists_fourth_root_poly (Ndom - C c0 * X - C c1 * X ^ 2) h4dvd
  have hNdom_eq : Ndom = C c0 * X + C c1 * X ^ 2 + L ^ 4 := by
    rw [hL4]; ring
  have hNdom_monic : Ndom.Monic := by
    unfold Ndom; exact Polynomial.monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hNdom_ne : Ndom ≠ 0 := hNdom_monic.ne_zero
  have hNdom_deg : Ndom.natDegree = N := by
    unfold Ndom
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      BinaryIRSProfile.card_index]
    rfl
  have hL4_deg : 4 * L.natDegree = N := by
    have hlt2 : (C c0 * X + C c1 * X ^ 2 : Fld[X]).natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le (((natDegree_C_mul_le _ _).trans natDegree_X_le).trans (by omega))
        ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 2)))
    have htail_deg : (Ndom - C c0 * X - C c1 * X ^ 2).natDegree = N := by
      have hNgt : 2 < N := by norm_num [N]
      have hrew : Ndom - C c0 * X - C c1 * X ^ 2 = Ndom - (C c0 * X + C c1 * X ^ 2) := by ring
      rw [hrew, sub_eq_add_neg, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_neg, hNdom_deg]; omega), hNdom_deg]
    rw [← natDegree_pow, hL4, htail_deg]
  have hd1 : Ndom.derivative = C c0 := by
    rw [hNdom_eq, derivative_add, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X, mul_one, derivative_mul, derivative_C, zero_mul, zero_add,
      char2_derivative_sq, mul_zero, add_zero, char2_derivative_pow_four, add_zero]
  have hd2 : hasse 2 Ndom = C c1 := by
    rw [hNdom_eq, hasse_add, hasse_add, char2_hasse_two_pow_four, add_zero]
    have h1 : hasse 2 (C c0 * X) = 0 := by
      apply Polynomial.ext; intro n; rw [coeff_hasse, coeff_C_mul, coeff_X, if_neg (by omega), mul_zero, mul_zero, coeff_zero]
    have h2 : hasse 2 (C c1 * X ^ 2) = C c1 := by
      apply Polynomial.ext; intro n; rw [coeff_hasse, coeff_C_mul, coeff_X_pow, coeff_C]
      cases n with
      | zero => simp only [zero_add, ↓reduceIte, mul_one, one_mul, Nat.choose_self, Nat.cast_one]
      | succ m => simp only [show m + 1 + 2 ≠ 2 by omega, ↓reduceIte, mul_zero, zero_mul, Nat.succ_ne_zero]
    rw [h1, h2, zero_add]
  have hmult1 : ∀ i : Idx, Ndom.rootMultiplicity (BinaryIRSProfile.domain i) = 1 := by
    intro i
    have hfac : Ndom = (X - C (BinaryIRSProfile.domain i)) *
        ∏ j ∈ Finset.univ.erase i, (X - C (BinaryIRSProfile.domain j)) := by
      unfold Ndom; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hrest_eval : (∏ j ∈ Finset.univ.erase i, (X - C (BinaryIRSProfile.domain j))).eval
        (BinaryIRSProfile.domain i) ≠ 0 := by
      rw [eval_prod]; apply Finset.prod_ne_zero_iff.mpr; intro j hj
      rw [eval_sub, eval_X, eval_C, sub_ne_zero]
      intro heq; exact (Finset.mem_erase.mp hj).1 (BinaryIRSProfile.domain.injective heq).symm
    have hrest_mult : (∏ j ∈ Finset.univ.erase i, (X - C (BinaryIRSProfile.domain j))).rootMultiplicity
        (BinaryIRSProfile.domain i) = 0 :=
      rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hrest_eval)
    generalize ∏ j ∈ Finset.univ.erase i, (X - C (BinaryIRSProfile.domain j)) = rest at hfac hrest_mult
    have hprod_ne : (X - C (BinaryIRSProfile.domain i)) * rest ≠ 0 := hfac ▸ hNdom_ne
    rw [hfac, rootMultiplicity_mul hprod_ne, rootMultiplicity_X_sub_C, if_pos rfl, hrest_mult, add_zero]
  have heval_iff : ∀ a : AlgebraicClosure Fld,
      (Ndom.map (algebraMap Fld (AlgebraicClosure Fld))).eval a = 0 ↔
        ∃ i : Idx, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) := by
    intro a
    unfold Ndom
    rw [Polynomial.map_prod, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  exact ⟨c0, c1, L, hc0, hNdom_eq, hNdom_deg, hL4_deg, hNdom_ne, hd1, hd2, hmult1, heval_iff⟩

/-- Local mod-4 consequence of `zRaw c0 c1 P Q = 0` over `E = AlgebraicClosure Fld`. -/
lemma ode_mod4_of_zRaw_zero {E : Type*} [Field E] [CharP E 2] {c0 c1 : E} (hc0 : c0 ≠ 0)
    {P Q : E[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (hz : zRaw c0 c1 P Q = 0) (a : E) :
    (P.rootMultiplicity a + 3 * Q.rootMultiplicity a) % 4 = 0 ∨
    (P.rootMultiplicity a + 3 * Q.rootMultiplicity a) % 4 = 1 := by
  have hode := zRaw_eq_zero_imp_poly_ode hQ hz (show P * Q ^ 4 = Q * (P * Q ^ 3) by ring)
  have hmul := rootMultiplicity_mod_four_of_poly_ode hc0 (mul_ne_zero hP (pow_ne_zero 3 hQ)) hode a
  have hrm : (P * Q ^ 3).rootMultiplicity a = P.rootMultiplicity a + 3 * Q.rootMultiplicity a := by
    rw [rootMultiplicity_mul (mul_ne_zero hP (pow_ne_zero 3 hQ)),
      show (Q ^ 3).rootMultiplicity a = 3 * Q.rootMultiplicity a by
        rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, pow_add, pow_add, pow_one,
          rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hQ hQ) hQ),
          rootMultiplicity_mul (mul_ne_zero hQ hQ)]; ring]
  rwa [hrm] at hmul

/-- **The 10-line char-2 4th-power theorem (`b1c1` `B1_D2_holds`):**
If `Q * R_F = S^2`, `R_F * Ndom^3 + F1 = Q * Q0^4`, and `deg(Q * F1) < 3 * N`,
then `R_F` and `Q` have the same valuation mod 4 at EVERY `a ∈ AlgebraicClosure Fld`! -/
theorem char2_fourth_power_of_sq_ratio_poly
    {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
    (frobInv : K → K) (hfrob : ∀ a : K, (frobInv a) ^ 2 = a)
    {Nd Q R_F S F1 Q0 L : K[X]} {c0 c1 : K} {Nv : ℕ}
    (hNgt2 : 2 < Nv) (hc0 : c0 ≠ 0) (hNd_eq : Nd = C c0 * X + C c1 * X ^ 2 + L ^ 4)
    (hNd_deg : Nd.natDegree = Nv) (hL4_deg : 4 * L.natDegree = Nv) (hNd_ne : Nd ≠ 0)
    (hd1 : Nd.derivative = C c0)
    (hQ : Q ≠ 0) (hRF : R_F ≠ 0) (hF1 : F1 ≠ 0)
    (hsq : Q * R_F = S ^ 2)
    (hid : R_F * Nd ^ 3 + F1 = Q * Q0 ^ 4)
    (hdeg : (Q * F1).natDegree < 3 * Nv) :
    ∃ A0 B0 H0 : K[X], R_F = A0 ^ 4 * H0 ∧ Q = B0 ^ 4 * H0 := by
  obtain ⟨G, hG_eq⟩ : ∃ G : K[X], G = EuclideanDomain.gcd S Q := ⟨_, rfl⟩
  have hG_ne : G ≠ 0 := fun h0 => hQ (EuclideanDomain.gcd_eq_zero_iff.mp (hG_eq ▸ h0)).2
  rcases (hG_eq ▸ EuclideanDomain.gcd_dvd_left S Q) with ⟨A, hA⟩
  rcases (hG_eq ▸ EuclideanDomain.gcd_dvd_right S Q) with ⟨B, hB⟩
  have hA_ne : A ≠ 0 := by
    intro h0; subst h0; simp at hA; rw [hA, zero_pow (by norm_num)] at hsq
    exact mul_ne_zero hQ hRF hsq
  have hB_ne : B ≠ 0 := by intro h0; subst h0; simp at hB; exact hQ hB
  have hcop : IsCoprime A B := by
    have hbez : G = S * EuclideanDomain.gcdA S Q + Q * EuclideanDomain.gcdB S Q :=
      hG_eq.trans (EuclideanDomain.gcd_eq_gcd_ab S Q)
    refine ⟨EuclideanDomain.gcdA S Q, EuclideanDomain.gcdB S Q, ?_⟩
    apply mul_left_cancel₀ hG_ne
    calc G * (EuclideanDomain.gcdA S Q * A + EuclideanDomain.gcdB S Q * B)
        = (G * A) * EuclideanDomain.gcdA S Q + (G * B) * EuclideanDomain.gcdB S Q := by ring
      _ = S * EuclideanDomain.gcdA S Q + Q * EuclideanDomain.gcdB S Q := by rw [← hA, ← hB]
      _ = G := hbez.symm
      _ = G * 1 := (mul_one G).symm
  have hBRF : B * R_F = G * A ^ 2 := by
    apply mul_left_cancel₀ hG_ne
    calc G * (B * R_F) = (G * B) * R_F := by ring
      _ = Q * R_F := by rw [← hB]
      _ = S ^ 2 := hsq
      _ = (G * A) ^ 2 := by rw [hA]
      _ = G * (G * A ^ 2) := by ring
  have hB_dvd_G : B ∣ G := hcop.symm.pow_right.dvd_of_dvd_mul_right ⟨R_F, hBRF.symm⟩
  rcases hB_dvd_G with ⟨H0, hH0⟩
  have hH0_ne : H0 ≠ 0 := by intro h0; subst h0; simp at hH0; exact hG_ne hH0
  have hQ_eq : Q = B ^ 2 * H0 := by rw [hB, hH0]; ring
  have hRF_eq : R_F = A ^ 2 * H0 := by
    apply mul_left_cancel₀ hB_ne
    rw [hBRF, hH0]; ring
  have hF1_dvd : H0 ∣ F1 := by
    have hF1_eq : F1 = Q * Q0 ^ 4 + R_F * Nd ^ 3 := by
      have hadd := congrArg (· + R_F * Nd ^ 3) hid
      rw [add_comm (R_F * Nd ^ 3) F1, add_assoc, CharTwo.add_self_eq_zero, add_zero] at hadd
      exact hadd
    rw [hF1_eq, hQ_eq, hRF_eq]
    exact dvd_add ⟨B ^ 2 * Q0 ^ 4, by ring⟩ ⟨A ^ 2 * Nd ^ 3, by ring⟩
  rcases hF1_dvd with ⟨F2, hF2⟩
  have hF2_ne : F2 ≠ 0 := by intro h0; subst h0; simp at hF2; exact hF1 hF2
  have hred : A ^ 2 * Nd ^ 3 + F2 = (B * Q0 ^ 2) ^ 2 := by
    apply mul_left_cancel₀ hH0_ne
    calc H0 * (A ^ 2 * Nd ^ 3 + F2) = (A ^ 2 * H0) * Nd ^ 3 + H0 * F2 := by ring
      _ = R_F * Nd ^ 3 + F1 := by rw [← hRF_eq, ← hF2]
      _ = Q * Q0 ^ 4 := hid
      _ = H0 * (B * Q0 ^ 2) ^ 2 := by rw [hQ_eq]; ring
  have hdeg_BF2 : 2 * B.natDegree + F2.natDegree < 3 * Nv := by
    have hQF : Q * F1 = B ^ 2 * F2 * H0 ^ 2 := by rw [hQ_eq, hF2]; ring
    rw [hQF, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hB_ne) hF2_ne) (pow_ne_zero 2 hH0_ne),
      natDegree_mul (pow_ne_zero 2 hB_ne) hF2_ne, natDegree_pow] at hdeg
    omega
  let sqp : K[X] → K[X] := fun p => ∑ k ∈ Finset.range (p.natDegree + 1), monomial k (frobInv (p.coeff k))
  have hsqp_sq : ∀ p : K[X], (sqp p) ^ 2 = p.comp (X ^ 2) := by
    intro p
    have hsq_add : ∀ u v : K[X], (u + v) ^ 2 = u ^ 2 + v ^ 2 := fun u v => by
      have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
      calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
        _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
    have hsum : ∀ (s : Finset ℕ) (g : ℕ → K), (∑ k ∈ s, monomial k (g k)) ^ 2 = ∑ k ∈ s, monomial (2 * k) ((g k) ^ 2) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, hsq_add, ih, Finset.sum_insert ha, monomial_pow, mul_comm a 2]
    have hcomp_sum : ∀ (s : Finset ℕ) (g : ℕ → K), (∑ k ∈ s, monomial k (g k)).comp (X ^ 2) = ∑ k ∈ s, monomial (2 * k) (g k) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Polynomial.add_comp, ih, Finset.sum_insert ha,
            ← C_mul_X_pow_eq_monomial, Polynomial.mul_comp, C_comp, pow_comp, X_comp, ← pow_mul,
            C_mul_X_pow_eq_monomial]
    calc (sqp p) ^ 2
        = ∑ k ∈ Finset.range (p.natDegree + 1), monomial (2 * k) ((frobInv (p.coeff k)) ^ 2) := hsum _ _
      _ = ∑ k ∈ Finset.range (p.natDegree + 1), monomial (2 * k) (p.coeff k) :=
            Finset.sum_congr rfl fun k _ => by rw [hfrob]
      _ = (∑ k ∈ Finset.range (p.natDegree + 1), monomial k (p.coeff k)).comp (X ^ 2) := (hcomp_sum _ _).symm
      _ = p.comp (X ^ 2) := by rw [← p.as_sum_range]
  have hsqp_deg : ∀ p : K[X], (sqp p).natDegree = p.natDegree := fun p => by
    have h := congrArg Polynomial.natDegree (hsqp_sq p)
    rw [natDegree_pow, natDegree_comp_X_sq] at h; omega
  have hsqp_zero : ∀ p : K[X], sqp p = 0 ↔ p = 0 := fun p => by
    constructor
    · intro h; have h1 := hsqp_sq p; rw [h, zero_pow (by norm_num)] at h1
      exact (comp_X_sq_eq_zero_iff p).mp h1.symm
    · intro h; subst h
      have h1 := hsqp_sq 0; rw [zero_comp] at h1; exact sq_eq_zero_iff.mp h1
  set F20 : K[X] := sqp (evenPart F2)
  set F21 : K[X] := sqp (oddPart F2)
  have hF2_split : F2 = F20 ^ 2 + X * F21 ^ 2 := by
    rw [hsqp_sq, hsqp_sq, evenPart_add_X_oddPart]
  set M : K[X] := C (frobInv c1) * X + L ^ 2
  have hNd3 : Nd ^ 3 = (Nd * M) ^ 2 + X * (C (frobInv c0) * Nd) ^ 2 := by
    have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
    have h1 : M ^ 2 = C c1 * X ^ 2 + L ^ 4 := by
      dsimp only [M]
      calc (C (frobInv c1) * X + L ^ 2) ^ 2
          = C (frobInv c1) ^ 2 * X ^ 2 + 2 * (C (frobInv c1) * X) * L ^ 2 + (L ^ 2) ^ 2 := by ring
        _ = C c1 * X ^ 2 + L ^ 4 := by rw [h2, ← map_pow, hfrob]; ring
    have h0 : (C (frobInv c0) * Nd) ^ 2 = C c0 * Nd ^ 2 := by rw [mul_pow, ← map_pow, hfrob]
    rw [mul_pow, h1, h0]
    calc Nd ^ 3 = Nd ^ 2 * Nd := by ring
      _ = Nd ^ 2 * (C c0 * X + C c1 * X ^ 2 + L ^ 4) := by rw [← hNd_eq]
      _ = Nd ^ 2 * (C c1 * X ^ 2 + L ^ 4) + X * (C c0 * Nd ^ 2) := by ring
  have hodd_eq : F21 ^ 2 = (C (frobInv c0) * Nd * A) ^ 2 := by
    have hd := congrArg Polynomial.derivative hred
    rw [hNd3, hF2_split] at hd
    have hsq0 : ∀ f : K[X], (f ^ 2).derivative = 0 := fun f => char2_derivative_sq f
    have hd_rew : (A ^ 2 * ((Nd * M) ^ 2 + X * (C (frobInv c0) * Nd) ^ 2) + (F20 ^ 2 + X * F21 ^ 2)).derivative =
        (C (frobInv c0) * Nd * A) ^ 2 + F21 ^ 2 := by
      rw [mul_add, ← mul_pow, show A ^ 2 * (X * (C (frobInv c0) * Nd) ^ 2) = X * (C (frobInv c0) * Nd * A) ^ 2 by ring,
        derivative_add, derivative_add, derivative_add, hsq0, hsq0,
        derivative_mul, derivative_X, one_mul, hsq0, mul_zero, add_zero,
        derivative_mul, derivative_X, one_mul, hsq0, mul_zero, add_zero, zero_add, zero_add]
    rw [hd_rew, hsq0] at hd
    have hadd := congrArg (· + F21 ^ 2) hd
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd
    exact hadd.symm
  have hrc0 : frobInv c0 ≠ 0 := by intro h; apply hc0; rw [← hfrob c0, h]; ring
  have hF21_ne : F21 ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hodd_eq
    have : C (frobInv c0) * Nd * A = 0 := sq_eq_zero_iff.mp hodd_eq.symm
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hrc0) hNd_ne) hA_ne this
  have hdeg_AB : 2 * A.natDegree + 2 * B.natDegree + 1 < Nv := by
    have hF21_deg : 2 * F21.natDegree + 1 ≤ F2.natDegree := by
      have h := two_mul_natDegree_add_one_le_even_odd (evenPart F2) (oddPart F2)
        (by intro h0; apply hF21_ne; dsimp [F21]; rw [h0]; exact (hsqp_zero 0).mpr rfl)
      rw [evenPart_add_X_oddPart] at h
      have hsqd : F21.natDegree = (oddPart F2).natDegree := hsqp_deg _
      omega
    have h2deg := congrArg Polynomial.natDegree hodd_eq
    rw [natDegree_pow, natDegree_pow, natDegree_mul (mul_ne_zero (C_ne_zero.mpr hrc0) hNd_ne) hA_ne,
      natDegree_mul (C_ne_zero.mpr hrc0) hNd_ne, natDegree_C, zero_add, hNd_deg] at h2deg
    omega
  have heven_sq : (Nd * M * A + F20) ^ 2 = (B * Q0 ^ 2) ^ 2 := by
    have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
    calc (Nd * M * A + F20) ^ 2
        = (Nd * M * A) ^ 2 + 2 * (Nd * M * A) * F20 + F20 ^ 2 := by ring
      _ = A ^ 2 * (Nd * M) ^ 2 + F20 ^ 2 := by rw [h2]; ring
      _ = A ^ 2 * (Nd * M) ^ 2 + X * (C (frobInv c0) * Nd * A) ^ 2 + (F20 ^ 2 + X * F21 ^ 2) := by
          rw [hodd_eq]; have hz := CharTwo.add_self_eq_zero (X * (C (frobInv c0) * Nd * A) ^ 2); linear_combination -hz
      _ = A ^ 2 * Nd ^ 3 + F2 := by rw [hNd3, ← hF2_split]; ring
      _ = (B * Q0 ^ 2) ^ 2 := hred
  have heven : Nd * M * A + F20 = B * Q0 ^ 2 := by
    have hdiff : (Nd * M * A + F20 + B * Q0 ^ 2) ^ 2 = 0 := by
      have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
      calc (Nd * M * A + F20 + B * Q0 ^ 2) ^ 2
          = (Nd * M * A + F20) ^ 2 + 2 * (Nd * M * A + F20) * (B * Q0 ^ 2) + (B * Q0 ^ 2) ^ 2 := by ring
        _ = (B * Q0 ^ 2) ^ 2 + (B * Q0 ^ 2) ^ 2 := by rw [h2, heven_sq]; ring
        _ = 0 := CharTwo.add_self_eq_zero _
    have h0 := sq_eq_zero_iff.mp hdiff
    have hadd := congrArg (· + B * Q0 ^ 2) h0
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd; exact hadd
  have hM' : M.derivative = C (frobInv c1) := by
    dsimp [M]; rw [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      char2_derivative_sq, add_zero]
  have helim : Nd * M * (B * A.derivative + B.derivative * A) +
      (C c0 * M + Nd * C (frobInv c1)) * B * A +
      (B * F20.derivative + B.derivative * F20) = 0 := by
    have hd := congrArg Polynomial.derivative heven
    rw [derivative_add, derivative_mul, derivative_mul, hd1, hM',
      derivative_mul, char2_derivative_sq, mul_zero, add_zero] at hd
    have h1 := congrArg (· * B) hd
    have h2 := congrArg (· * B.derivative) heven
    have hadd := congrArg₂ (· + ·) h1 h2
    have hz := CharTwo.add_self_eq_zero (B * B.derivative * Q0 ^ 2)
    linear_combination hadd + hz
  have hM_deg : M.natDegree = Nv / 2 := by
    dsimp [M]
    have hL2_deg : (L ^ 2).natDegree = Nv / 2 := by rw [natDegree_pow]; omega
    have hlin : (C (frobInv c1) * X : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    rw [natDegree_add_eq_right_of_natDegree_lt (by omega), hL2_deg]
  have hM_ne : M ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hM_deg; omega
  have hwr_zero : B * A.derivative + B.derivative * A = 0 := by
    by_contra hne
    have hT1_deg : (Nd * M * (B * A.derivative + B.derivative * A)).natDegree ≥ Nv + Nv / 2 := by
      rw [natDegree_mul (mul_ne_zero hNd_ne hM_ne) hne, natDegree_mul hNd_ne hM_ne, hNd_deg, hM_deg]; omega
    have hT2_deg : ((C c0 * M + Nd * C (frobInv c1)) * B * A).natDegree < Nv + Nv / 2 := by
      have h1 : (C c0 * M + Nd * C (frobInv c1)).natDegree ≤ Nv :=
        (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by omega))
          (natDegree_mul_le.trans (by rw [hNd_deg, natDegree_C]; omega)))
      have h2 := natDegree_mul_le (p := (C c0 * M + Nd * C (frobInv c1)) * B) (q := A)
      have h3 := natDegree_mul_le (p := C c0 * M + Nd * C (frobInv c1)) (q := B)
      omega
    have hF20_deg : 2 * F20.natDegree ≤ F2.natDegree := by
      by_cases h0 : F20 = 0
      · simp [h0]
      · have h := two_mul_natDegree_le_even_odd (evenPart F2) (oddPart F2)
          (by intro he; apply h0; dsimp [F20]; rw [he]; exact (hsqp_zero 0).mpr rfl)
        rw [evenPart_add_X_oddPart] at h
        have hsqd : F20.natDegree = (evenPart F2).natDegree := hsqp_deg _
        omega
    have hT3_deg : (B * F20.derivative + B.derivative * F20).natDegree < Nv + Nv / 2 := by
      have h1 : (B * F20.derivative).natDegree ≤ B.natDegree + F20.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add le_rfl (natDegree_derivative_le _ |>.trans (Nat.sub_le _ _)))
      have h2 : (B.derivative * F20).natDegree ≤ B.natDegree + F20.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add (natDegree_derivative_le _ |>.trans (Nat.sub_le _ _)) le_rfl)
      have hadd := (natDegree_add_le (B * F20.derivative) (B.derivative * F20)).trans (max_le h1 h2)
      omega
    have h23_deg : ((C c0 * M + Nd * C (frobInv c1)) * B * A + (B * F20.derivative + B.derivative * F20)).natDegree <
        (Nd * M * (B * A.derivative + B.derivative * A)).natDegree := by
      have := natDegree_add_le ((C c0 * M + Nd * C (frobInv c1)) * B * A) (B * F20.derivative + B.derivative * F20)
      omega
    have htot_deg := natDegree_add_eq_left_of_natDegree_lt h23_deg
    rw [show Nd * M * (B * A.derivative + B.derivative * A) +
        ((C c0 * M + Nd * C (frobInv c1)) * B * A + (B * F20.derivative + B.derivative * F20)) = 0 by linear_combination helim,
      natDegree_zero] at htot_deg
    omega
  have hA' : A.derivative = 0 := by
    have hd : A ∣ A.derivative := hcop.dvd_of_dvd_mul_left ⟨B.derivative, by
      have hadd := congrArg (· + B.derivative * A) hwr_zero
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd; rw [hadd, mul_comm]⟩
    by_contra hne
    have hle := natDegree_le_of_dvd hd hne
    have hA_deg : A.natDegree ≠ 0 := by intro h0; apply hne; rw [Polynomial.eq_C_of_natDegree_eq_zero h0, derivative_C]
    have hlt := natDegree_derivative_lt hA_deg; omega
  have hB' : B.derivative = 0 := by
    have hd : B ∣ B.derivative := hcop.symm.dvd_of_dvd_mul_left ⟨A.derivative, by
      have hadd := congrArg (· + B * A.derivative) hwr_zero
      rw [add_comm (B * A.derivative), add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd
      rw [mul_comm A B.derivative, hadd, mul_comm]⟩
    by_contra hne
    have hle := natDegree_le_of_dvd hd hne
    have hB_deg : B.natDegree ≠ 0 := by intro h0; apply hne; rw [Polynomial.eq_C_of_natDegree_eq_zero h0, derivative_C]
    have hlt := natDegree_derivative_lt hB_deg; omega
  have hA0 : A = (sqp (evenPart A)) ^ 2 := by
    have hdec := evenPart_add_X_oddPart A
    have hodd : oddPart A = 0 := by
      have h := congrArg Polynomial.derivative hdec
      rw [derivative_even_odd_char2, hA'] at h; exact (comp_X_sq_eq_zero_iff (oddPart A)).mp h
    rw [hodd, zero_comp, mul_zero, add_zero] at hdec; rw [hsqp_sq]; exact hdec.symm
  have hB0 : B = (sqp (evenPart B)) ^ 2 := by
    have hdec := evenPart_add_X_oddPart B
    have hodd : oddPart B = 0 := by
      have h := congrArg Polynomial.derivative hdec
      rw [derivative_even_odd_char2, hB'] at h; exact (comp_X_sq_eq_zero_iff (oddPart B)).mp h
    rw [hodd, zero_comp, mul_zero, add_zero] at hdec; rw [hsqp_sq]; exact hdec.symm
  refine ⟨sqp (evenPart A), sqp (evenPart B), H0, ?_, ?_⟩
  · conv_lhs => rw [hRF_eq, hA0]
    ring
  · conv_lhs => rw [hQ_eq, hB0]
    ring

theorem char2_fourth_power_of_sq_ratio
    {Q R_F S F1 Q0 : Fld[X]} (hQ : Q ≠ 0) (hRF : R_F ≠ 0) (hF1 : F1 ≠ 0)
    (hsq : Q * R_F = S ^ 2)
    (hid : R_F * Ndom ^ 3 + F1 = Q * Q0 ^ 4)
    (hdeg : (Q * F1).natDegree < 3 * N) :
    ∃ A0 B0 H0 : Fld[X], R_F = A0 ^ 4 * H0 ∧ Q = B0 ^ 4 * H0 := by
  obtain ⟨c0, c1, L, hc0, hNdom_eq, hNdom_deg, hL4_deg, hNdom_ne, hd1, _, _, _⟩ := Ndom_decomp
  exact char2_fourth_power_of_sq_ratio_poly (frobEquiv Fld).symm frobEquiv_symm_sq
    (by norm_num [N] : 2 < N) hc0 hNdom_eq hNdom_deg hL4_deg hNdom_ne hd1 hQ hRF hF1 hsq hid hdeg

/-! ### Part 2: `T4ABranch.p0` (10 valid branches, `nv = 23`) -/

private lemma rowValidSat_two_cI {nv : ℕ} (x : Fin nv → ℚ) {i j : ℕ} (hi : i < nv) (hj : j < nv)
    {a b : ℕ} (hxi : x ⟨i, hi⟩ = (a : ℚ) / (N : ℚ)) (hxj : x ⟨j, hj⟩ = (b : ℚ) / (N : ℚ))
    (hle : a ≤ b) :
    RowValid nv (mkStat [(i, cI 1), (j, cI (-1))] 0 false) ∧
    RowSatLe x (mkStat [(i, cI 1), (j, cI (-1))] 0 false) := by
  refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
  rw [rowSatLe_mkStat_iff]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hi, hj, ↓reduceDIte,
    hxi, hxj, cI_mul_div_N]
  have hQ : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hle
  push_cast; linarith

private lemma rowValidSat_four_cI {nv : ℕ} (x : Fin nv → ℚ) {i1 i2 i3 i4 : ℕ}
    (h1 : i1 < nv) (h2 : i2 < nv) (h3 : i3 < nv) (h4 : i4 < nv)
    {a1 a2 a3 a4 : ℕ} (hx1 : x ⟨i1, h1⟩ = (a1 : ℚ) / (N : ℚ)) (hx2 : x ⟨i2, h2⟩ = (a2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨i3, h3⟩ = (a3 : ℚ) / (N : ℚ)) (hx4 : x ⟨i4, h4⟩ = (a4 : ℚ) / (N : ℚ))
    (hle : a1 + a4 ≤ a3 + a2) :
    RowValid nv (mkStat [(i1, cI 1), (i2, cI (-1)), (i3, cI (-1)), (i4, cI 1)] 0 false) ∧
    RowSatLe x (mkStat [(i1, cI 1), (i2, cI (-1)), (i3, cI (-1)), (i4, cI 1)] 0 false) := by
  refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
  rw [rowSatLe_mkStat_iff]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1, h2, h3, h4, ↓reduceDIte,
    hx1, hx2, hx3, hx4, cI_mul_div_N]
  have hQ : (a1 : ℚ) + (a4 : ℚ) ≤ (a3 : ℚ) + (a2 : ℚ) := by exact_mod_cast hle
  push_cast; linarith

private def p0Vec (n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg RDeg UPDeg M21Deg M20Deg M10Deg
    n1U n2U n3U ntU a1U a2U a3U WF : ℕ) : Fin 23 → ℚ := fun j =>
  match j.val with
  | 0 => (n0 : ℚ) / (N : ℚ) | 1 => (n1 : ℚ) / (N : ℚ)
  | 2 => (n2 : ℚ) / (N : ℚ) | 3 => (n3 : ℚ) / (N : ℚ)
  | 4 => (nt : ℚ) / (N : ℚ) | 5 => (a0 : ℚ) / (N : ℚ)
  | 6 => (a1 : ℚ) / (N : ℚ) | 7 => (a2 : ℚ) / (N : ℚ)
  | 8 => (a3 : ℚ) / (N : ℚ) | 9 => (2 * pDeg : ℚ) / (N : ℚ)
  | 10 => (RDeg : ℚ) / (N : ℚ) | 11 => (UPDeg : ℚ) / (N : ℚ)
  | 12 => (M21Deg : ℚ) / (N : ℚ) | 13 => (M20Deg : ℚ) / (N : ℚ)
  | 14 => (M10Deg : ℚ) / (N : ℚ) | 15 => (n1U : ℚ) / (N : ℚ)
  | 16 => (n2U : ℚ) / (N : ℚ) | 17 => (n3U : ℚ) / (N : ℚ)
  | 18 => (ntU : ℚ) / (N : ℚ) | 19 => (a1U : ℚ) / (N : ℚ)
  | 20 => (a2U : ℚ) / (N : ℚ) | 21 => (a3U : ℚ) / (N : ℚ)
  | _ => (WF : ℚ) / (wY : ℚ)

private theorem table4_p0_rows_sat
    (m21Nz rGt p0M10D4 q2M21M10 : Bool)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg RDeg UPDeg M21Deg M20Deg M10Deg
      n1U n2U n3U ntU a1U a2U a3U WF : ℕ)
    (hBS : let x := p0Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg RDeg UPDeg M21Deg M20Deg M10Deg
             n1U n2U n3U ntU a1U a2U a3U WF
           let (ubB, eqB) := baseT4Rows 22 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
           (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r))
    (hU : n1U ≤ n1 ∧ n2U ≤ n2 ∧ n3U ≤ n3 ∧ ntU ≤ nt ∧
          a1U ≤ n1U ∧ a2U ≤ n2U ∧ a3U ≤ n3U ∧
          a1U ≤ a1 ∧ a2U ≤ a2 ∧ a3U ≤ a3 ∧
          a1 + n1U ≤ n1 + a1U ∧ a2 + n2U ≤ n2 + a2U ∧ a3 + n3U ≤ n3 + a3U)
    (hp_add_M20 : (pDeg : ℤ) + (M20Deg : ℤ) ≤ (WF : ℤ) - 3 * (wY : ℤ))
    (hp_add_M10 : (pDeg : ℤ) + (M10Deg : ℤ) ≤ (WF : ℤ) - 2 * (wY : ℤ))
    (hResZ : (4 * (n1 : ℤ) - 3 * (n1U : ℤ)) + (16 * (n2 : ℤ) - 5 * (n2U : ℤ)) +
        (34 * (n3 : ℤ) - 5 * (n3U : ℤ)) + 18 * (nt : ℤ) ≤ 9 * (WF : ℤ) - 25 * (wY : ℤ) + 5)
    (hf1Z : (2 * (a1 : ℤ) - (a1U : ℤ)) + (4 * (a2 : ℤ) - (a2U : ℤ)) +
        (6 * (a3 : ℤ) - (a3U : ℤ)) ≤ (WF : ℤ) - (wY : ℤ) + 1)
    (hQ2Z : ((n1 : ℤ) - (n1U : ℤ)) + (4 * (n2 : ℤ) - 2 * (n2U : ℤ)) +
        (8 * (n3 : ℤ) - 2 * (n3U : ℤ)) + 4 * (nt : ℤ) + 2 * (pDeg : ℤ) ≤ 2 * (WF : ℤ) - 6 * (wY : ℤ))
    (hM21_b : (m21Nz = false → 2 * (n2 : ℤ) + 4 * (n3 : ℤ) + 2 * (nt : ℤ) ≤ (WF : ℤ) - 2 * (wY : ℤ)) ∧
        (m21Nz = true → (pDeg : ℤ) + (M21Deg : ℤ) ≤ (WF : ℤ) - 4 * (wY : ℤ) ∧
          (RDeg : ℤ) + 2 * (M21Deg : ℤ) ≤ 2 * (WF : ℤ) - 7 * (wY : ℤ) + 1))
    (hQ2_b : (q2M21M10 = false → (RDeg : ℤ) + 2 * (M20Deg : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1 ∧
          ((n1 : ℤ) - (n1U : ℤ)) + (4 * (n2 : ℤ) - 2 * (n2U : ℤ)) +
          (8 * (n3 : ℤ) - 2 * (n3U : ℤ)) + 4 * (nt : ℤ) ≤ 2 * (M20Deg : ℤ)) ∧
        (q2M21M10 = true → (RDeg : ℤ) + 2 * (M10Deg : ℤ) ≤ 2 * (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
          ((n1 : ℤ) - (n1U : ℤ)) + (4 * (n2 : ℤ) - 2 * (n2U : ℤ)) +
          (8 * (n3 : ℤ) - 2 * (n3U : ℤ)) + 4 * (nt : ℤ) ≤ (M21Deg : ℤ) + (M10Deg : ℤ)))
    (hR_b : (rGt = true → 2 * (pDeg : ℤ) - (RDeg : ℤ) ≤ -(wY : ℤ) - 1 ∧
          (n1U : ℤ) + 3 * (n2U : ℤ) + 5 * (n3U : ℤ) + 2 * (ntU : ℤ) ≤ 4 * (RDeg : ℤ) + (WF : ℤ) - 5 * (wY : ℤ) + 1 ∧
          UPDeg = RDeg) ∧
        (rGt = false → RDeg ≤ 2 * pDeg + wY ∧ UPDeg ≤ 2 * pDeg + wY ∧
          (n1U : ℤ) + 3 * (n2U : ℤ) + 5 * (n3U : ℤ) + 2 * (ntU : ℤ) ≤ 8 * (pDeg : ℤ) + (WF : ℤ) - (wY : ℤ) + 1))
    (hP0_b : (p0M10D4 = false → (n2 + n2U) + (3 * n3 + n3U) + 2 * nt ≤ 2 * RDeg + M21Deg) ∧
        (p0M10D4 = true → (RDeg : ℤ) + 2 * (M10Deg : ℤ) ≤ 2 * (WF : ℤ) - 3 * (wY : ℤ) + 1 ∧
          (n2 + n2U) + (3 * n3 + n3U) + 2 * nt ≤ 4 * pDeg + M10Deg)) :
    let br := T4ABranch.p0 m21Nz rGt p0M10D4 q2M21M10
    let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    let x := p0Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg RDeg UPDeg M21Deg M20Deg M10Deg
               n1U n2U n3U ntU a1U a2U a3U WF
    (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
    (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  let x := p0Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg RDeg UPDeg M21Deg M20Deg M10Deg
             n1U n2U n3U ntU a1U a2U a3U WF
  have hBV := baseT4Rows_valid (nv := 23) (ic := 22) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hc_nn : (0 : ℚ) ≤ (WF : ℚ) / (wY : ℚ) := by positivity
  have hCore : ∀ r ∈ ([
      mkStat [(9, cH 1), (13, cI 1), (22, cH (-1))] (-6),
      mkStat [(9, cH 1), (14, cI 1), (22, cH (-1))] (-4),
      mkStat [(15, cI 1), (1, cI (-1))] 0 false,
      mkStat [(16, cI 1), (2, cI (-1))] 0 false,
      mkStat [(17, cI 1), (3, cI (-1))] 0 false,
      mkStat [(18, cI 1), (4, cI (-1))] 0 false,
      mkStat [(19, cI 1), (15, cI (-1))] 0 false,
      mkStat [(20, cI 1), (16, cI (-1))] 0 false,
      mkStat [(21, cI 1), (17, cI (-1))] 0 false,
      mkStat [(19, cI 1), (6, cI (-1))] 0 false,
      mkStat [(20, cI 1), (7, cI (-1))] 0 false,
      mkStat [(21, cI 1), (8, cI (-1))] 0 false,
      mkStat [(6, cI 1), (19, cI (-1)), (1, cI (-1)), (15, cI 1)] 0 false,
      mkStat [(7, cI 1), (20, cI (-1)), (2, cI (-1)), (16, cI 1)] 0 false,
      mkStat [(8, cI 1), (21, cI (-1)), (3, cI (-1)), (17, cI 1)] 0 false,
      mkStat [(1, cI 4), (15, cI (-3)), (2, cI 16), (16, cI (-5)), (3, cI 34), (17, cI (-5)), (4, cI 18), (22, cH (-9))] (-50),
      { entries := [(6, cI 2), (19, cI (-1)), (7, cI 4), (20, cI (-1)), (8, cI 6), (21, cI (-1)), (22, cW (-1))]
        rhsNum := 4 * (-(wY : ℤ) + 1), rhsDen := BASE_DEN },
      mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (9, cI 1), (22, cI (-1))] (-12)
    ] : List SparseRow), RowValid 23 r ∧ RowSatLe x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 23 by omega, show (13 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
        x, p0Vec, cH_mul_div_N, cI_mul_div_N, cH_mul_c_eq]
      have hQ : (pDeg : ℚ) + (M20Deg : ℚ) ≤ (WF : ℚ) - 3 * (wY : ℚ) := by exact_mod_cast hp_add_M20
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 23 by omega, show (14 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
        x, p0Vec, cH_mul_div_N, cI_mul_div_N, cH_mul_c_eq]
      have hQ : (pDeg : ℚ) + (M10Deg : ℚ) ≤ (WF : ℚ) - 2 * (wY : ℚ) := by exact_mod_cast hp_add_M10
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.2.2.2.2.1
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl hU.2.2.2.2.2.2.2.2.2.1
    · exact rowValidSat_four_cI x (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl hU.2.2.2.2.2.2.2.2.2.2.1
    · exact rowValidSat_four_cI x (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl hU.2.2.2.2.2.2.2.2.2.2.2.1
    · exact rowValidSat_four_cI x (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl hU.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 23 by omega, show (15 : ℕ) < 23 by omega, show (2 : ℕ) < 23 by omega,
        show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
        show (4 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N, cH_mul_c_eq]
      have hQ : (4 * (n1 : ℚ) - 3 * (n1U : ℚ)) + (16 * (n2 : ℚ) - 5 * (n2U : ℚ)) +
          (34 * (n3 : ℚ) - 5 * (n3U : ℚ)) + 18 * (nt : ℚ) ≤ 9 * (WF : ℚ) - 25 * (wY : ℚ) + 5 := by
        exact_mod_cast hResZ
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨⟨base_den_pos, by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega⟩, ?_⟩
      unfold RowSatLe
      rw [mul_div_cancel_left₀ _ base_den_ne_zeroQ]
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 23 by omega, show (19 : ℕ) < 23 by omega, show (7 : ℕ) < 23 by omega,
        show (20 : ℕ) < 23 by omega, show (8 : ℕ) < 23 by omega, show (21 : ℕ) < 23 by omega,
        show (22 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N, cW_mul_div_wY]
      have hQ : (2 * (a1 : ℚ) - (a1U : ℚ)) + (4 * (a2 : ℚ) - (a2U : ℚ)) +
          (6 * (a3 : ℚ) - (a3U : ℚ)) ≤ (WF : ℚ) - (wY : ℚ) + 1 := by exact_mod_cast hf1Z
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 23 by omega, show (15 : ℕ) < 23 by omega, show (2 : ℕ) < 23 by omega,
        show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
        show (4 : ℕ) < 23 by omega, show (9 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega,
        ↓reduceDIte, x, p0Vec, cI_mul_div_N, cI_mul_c_eq]
      have hQ : ((n1 : ℚ) - (n1U : ℚ)) + (4 * (n2 : ℚ) - 2 * (n2U : ℚ)) +
          (8 * (n3 : ℚ) - 2 * (n3U : ℚ)) + 4 * (nt : ℚ) + 2 * (pDeg : ℚ) ≤
          2 * (WF : ℚ) - 6 * (wY : ℚ) := by exact_mod_cast hQ2Z
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
  have hM21_rows : ∀ r ∈ (if !m21Nz then [mkStat [(2, cI 2), (3, cI 4), (4, cI 2), (22, cH (-1))] (-4)]
      else [mkStat [(9, cH 1), (12, cI 1), (22, cH (-1))] (-8),
            mkStat [(10, cI 1), (12, cI 2), (22, cI (-1))] (-14)]),
      RowValid 23 r ∧ RowSatLe x r := by
    intro r hr
    cases hm : m21Nz
    · simp only [hm, Bool.not_false, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega, show (4 : ℕ) < 23 by omega,
        show (22 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N, cH_mul_c_eq]
      have hQ : 2 * (n2 : ℚ) + 4 * (n3 : ℚ) + 2 * (nt : ℚ) ≤ (WF : ℚ) - 2 * (wY : ℚ) := by
        exact_mod_cast hM21_b.1 hm
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 23 by omega, show (12 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
          x, p0Vec, cH_mul_div_N, cI_mul_div_N, cH_mul_c_eq]
        have hQ : (pDeg : ℚ) + (M21Deg : ℚ) ≤ (WF : ℚ) - 4 * (wY : ℚ) := by exact_mod_cast (hM21_b.2 hm).1
        push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 23 by omega, show (12 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
          x, p0Vec, cI_mul_div_N, cI_mul_c_eq]
        have hQ : (RDeg : ℚ) + 2 * (M21Deg : ℚ) ≤ 2 * (WF : ℚ) - 7 * (wY : ℚ) + 1 := by exact_mod_cast (hM21_b.2 hm).2
        push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
  have hQ2_rows : ∀ r ∈ (if !q2M21M10 then
        [mkStat [(10, cI 1), (13, cI 2), (22, cI (-1))] (-10),
         mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (13, cI (-2))] 0]
      else
        [mkStat [(10, cI 1), (14, cI 2), (22, cI (-1))] (-6),
         mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (12, cI (-1)), (14, cI (-1))] 0]),
      RowValid 23 r ∧ RowSatLe x r := by
    intro r hr
    cases hq : q2M21M10
    · simp only [hq, Bool.not_false, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 23 by omega, show (13 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
          x, p0Vec, cI_mul_div_N, cI_mul_c_eq]
        have hQ : (RDeg : ℚ) + 2 * (M20Deg : ℚ) ≤ 2 * (WF : ℚ) - 5 * (wY : ℚ) + 1 := by exact_mod_cast (hQ2_b.1 hq).1
        push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (1 : ℕ) < 23 by omega, show (15 : ℕ) < 23 by omega, show (2 : ℕ) < 23 by omega,
          show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
          show (4 : ℕ) < 23 by omega, show (13 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
        have hQ : ((n1 : ℚ) - (n1U : ℚ)) + (4 * (n2 : ℚ) - 2 * (n2U : ℚ)) +
            (8 * (n3 : ℚ) - 2 * (n3U : ℚ)) + 4 * (nt : ℚ) ≤ 2 * (M20Deg : ℚ) := by exact_mod_cast (hQ2_b.1 hq).2
        push_cast; linarith only [hQ]
    · simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 23 by omega, show (14 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
          x, p0Vec, cI_mul_div_N, cI_mul_c_eq]
        have hQ : (RDeg : ℚ) + 2 * (M10Deg : ℚ) ≤ 2 * (WF : ℚ) - 3 * (wY : ℚ) + 1 := by exact_mod_cast (hQ2_b.2 hq).1
        push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (1 : ℕ) < 23 by omega, show (15 : ℕ) < 23 by omega, show (2 : ℕ) < 23 by omega,
          show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
          show (4 : ℕ) < 23 by omega, show (12 : ℕ) < 23 by omega, show (14 : ℕ) < 23 by omega,
          ↓reduceDIte, x, p0Vec, cI_mul_div_N]
        have hQ : ((n1 : ℚ) - (n1U : ℚ)) + (4 * (n2 : ℚ) - 2 * (n2U : ℚ)) +
            (8 * (n3 : ℚ) - 2 * (n3U : ℚ)) + 4 * (nt : ℚ) ≤
            (M21Deg : ℚ) + (M10Deg : ℚ) := by exact_mod_cast (hQ2_b.2 hq).2
        push_cast; linarith only [hQ]
  have hR_rows :
      let (rR, eqR) :=
        if !rGt then
          ([mkStat [(9, cI (-1)), (10, cI 1)] 2,
            mkStat [(9, cI (-1)), (11, cI 1)] 2,
            mkStat [(15, cI 1), (16, cI 3), (17, cI 5), (18, cI 2), (9, cI (-4)), (22, cH (-1))] (-2)], [])
        else
          ([mkStat [(9, cI 1), (10, cI (-1))] (-2),
            mkStat [(15, cI 1), (16, cI 3), (17, cI 5), (18, cI 2), (10, cI (-4)), (22, cH (-1))] (-10)],
           [mkEq [(10, cI 1), (11, cI (-1))] 0])
      (∀ r ∈ rR, RowValid 23 r ∧ RowSatLe x r) ∧ (∀ r ∈ eqR, RowValid 23 r ∧ RowSatEq x r) := by
    cases hr : rGt
    · simp only [hr, Bool.not_false, ↓reduceIte]
      have hRb := hR_b.2 hr
      constructor
      · intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 23 by omega, show (10 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
          have hQ : (RDeg : ℚ) ≤ 2 * (pDeg : ℚ) + (wY : ℚ) := by exact_mod_cast hRb.1
          push_cast; rw [hN_eq]; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 23 by omega, show (11 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
          have hQ : (UPDeg : ℚ) ≤ 2 * (pDeg : ℚ) + (wY : ℚ) := by exact_mod_cast hRb.2.1
          push_cast; rw [hN_eq]; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (15 : ℕ) < 23 by omega, show (16 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
            show (18 : ℕ) < 23 by omega, show (9 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega,
            ↓reduceDIte, x, p0Vec, cI_mul_div_N, cH_mul_c_eq]
          have hQ : (n1U : ℚ) + 3 * (n2U : ℚ) + 5 * (n3U : ℚ) + 2 * (ntU : ℚ) ≤
              8 * (pDeg : ℚ) + (WF : ℚ) - (wY : ℚ) + 1 := by exact_mod_cast hRb.2.2
          push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · intro r hr'; simp at hr'
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hRb := hR_b.1 hr
      constructor
      · intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 23 by omega, show (10 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
          have hQ : 2 * (pDeg : ℚ) - (RDeg : ℚ) ≤ -(wY : ℚ) - 1 := by exact_mod_cast hRb.1
          push_cast; rw [hN_eq]; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (15 : ℕ) < 23 by omega, show (16 : ℕ) < 23 by omega, show (17 : ℕ) < 23 by omega,
            show (18 : ℕ) < 23 by omega, show (10 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega,
            ↓reduceDIte, x, p0Vec, cI_mul_div_N, cH_mul_c_eq]
          have hQ : (n1U : ℚ) + 3 * (n2U : ℚ) + 5 * (n3U : ℚ) + 2 * (ntU : ℚ) ≤
              4 * (RDeg : ℚ) + (WF : ℚ) - 5 * (wY : ℚ) + 1 := by exact_mod_cast hRb.2.1
          push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
        refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatEq_mkEq_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 23 by omega, show (11 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
        rw [hRb.2.2]; push_cast; ring
  have hP0_rows : ∀ r ∈ (if !p0M10D4 then
        [mkStat [(2, cI 1), (16, cI 1), (3, cI 3), (17, cI 1), (4, cI 2), (10, cI (-2)), (12, cI (-1))] 0]
      else
        [mkStat [(10, cI 1), (14, cI 2), (22, cI (-1))] (-6),
         mkStat [(2, cI 1), (16, cI 1), (3, cI 3), (17, cI 1), (4, cI 2), (9, cI (-2)), (14, cI (-1))] 0]),
      RowValid 23 r ∧ RowSatLe x r := by
    intro r hr
    cases hp0 : p0M10D4
    · simp only [hp0, Bool.not_false, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < 23 by omega, show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega,
        show (17 : ℕ) < 23 by omega, show (4 : ℕ) < 23 by omega, show (10 : ℕ) < 23 by omega,
        show (12 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
      have hQ : ((n2 : ℚ) + (n2U : ℚ)) + (3 * (n3 : ℚ) + (n3U : ℚ)) + 2 * (nt : ℚ) ≤
          2 * (RDeg : ℚ) + (M21Deg : ℚ) := by exact_mod_cast hP0_b.1 hp0
      push_cast; linarith only [hQ]
    · simp only [hp0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (10 : ℕ) < 23 by omega, show (14 : ℕ) < 23 by omega, show (22 : ℕ) < 23 by omega, ↓reduceDIte,
          x, p0Vec, cI_mul_div_N, cI_mul_c_eq]
        have hQ : (RDeg : ℚ) + 2 * (M10Deg : ℚ) ≤ 2 * (WF : ℚ) - 3 * (wY : ℚ) + 1 := by exact_mod_cast (hP0_b.2 hp0).1
        push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (2 : ℕ) < 23 by omega, show (16 : ℕ) < 23 by omega, show (3 : ℕ) < 23 by omega,
          show (17 : ℕ) < 23 by omega, show (4 : ℕ) < 23 by omega, show (9 : ℕ) < 23 by omega,
          show (14 : ℕ) < 23 by omega, ↓reduceDIte, x, p0Vec, cI_mul_div_N]
        have hQ : ((n2 : ℚ) + (n2U : ℚ)) + (3 * (n3 : ℚ) + (n3U : ℚ)) + 2 * (nt : ℚ) ≤
            4 * (pDeg : ℚ) + (M10Deg : ℚ) := by exact_mod_cast (hP0_b.2 hp0).2
        push_cast; linarith only [hQ]
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | ((((hr | hr) | hr) | hr) | hr)
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · exact hCore r hr
    · exact hM21_rows r hr
    · exact hQ2_rows r hr
    · exact hR_rows.1 r hr
    · exact hP0_rows r hr
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨hBV.2 r hr, hBS.2 r hr⟩
    · exact hR_rows.2 r hr

/-- **Theorem (`T4ABranch.p0`):** For any `S : KerD45Syzygy D` with `S.P0 ≠ 0`, `D` satisfies
all rows of `buildT4ARows (.p0 m21Nz rGt p0M10D4 q2M21M10)` for an exact valid branch tuple! -/
theorem table4_p0_sat {D : KerD45Data} (S : KerD45Syzygy D) (hP0 : S.P0 ≠ 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    ∃ (m21Nz rGt p0M10D4 q2M21M10 : Bool),
      (m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false) ∧
      let br := T4ABranch.p0 m21Nz rGt p0M10D4 q2M21M10
      let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin (t4aNumVars br) → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by dsimp only [br, t4aNumVars]; omega⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨22, by dsimp only [br, t4aNumVars]; omega⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  classical
  let m21Nz : Bool := decide (S.M21 ≠ 0)
  let rGt : Bool := decide (2 * S.p.natDegree + wY < S.R.natDegree)
  let p0M10D4 : Bool :=
    if !m21Nz then true
    else decide (S.M10 ≠ 0 ∧ (S.q = 0 ∨ 2 * S.q.natDegree + S.M21.natDegree ≤ 4 * S.p.natDegree + S.M10.natDegree))
  let q2M21M10 : Bool :=
    if !m21Nz then false
    else decide (S.M10 ≠ 0 ∧ 2 * S.M20.natDegree < S.M21.natDegree + S.M10.natDegree)
  refine ⟨m21Nz, rGt, p0M10D4, q2M21M10, ?_, ?_⟩
  · intro hm; simp [p0M10D4, q2M21M10, hm]
  let x : Fin 23 → ℚ := p0Vec D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3
    S.p.natDegree S.R.natDegree S.UP.natDegree S.M21.natDegree S.M20.natDegree S.M10.natDegree
    S.n1U S.n2U S.n3U S.ntU S.a1U S.a2U S.a3U D.W_F
  refine ⟨x, fun j => by dsimp only [x, p0Vec]; split <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hBS := D.baseT4Rows_sat (nv := 23) (ic := 22) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hU := S.U_counts_ineqs
  have hp_add_M20 : S.p.natDegree + S.M20.natDegree ≤ D.W_F - 3 * wY := by
    by_cases hM20 : S.M20 = 0
    · rw [hM20, natDegree_zero, add_zero]
      have hM21 : S.M21 ≠ 0 := by
        intro h0; apply S.Q2_ne_zero; unfold KerD45Syzygy.Q2; rw [hM20, h0]; simp
      have := S.natDegree_p_add_M21_le hM21; omega
    · exact S.natDegree_p_add_M20_le hM20
  have hp_add_M10 : S.p.natDegree + S.M10.natDegree ≤ D.W_F - 2 * wY := by
    by_cases hM10 : S.M10 = 0
    · rw [hM10, natDegree_zero, add_zero]
      have hM21 : S.M21 ≠ 0 := by
        intro h0; apply hP0; unfold KerD45Syzygy.P0; rw [hM10, h0]; simp
      have := S.natDegree_p_add_M21_le hM21; omega
    · exact S.natDegree_p_add_M10_le hM10
  have hR_add_2M21 : S.M21 ≠ 0 → S.R.natDegree + 2 * S.M21.natDegree ≤ 2 * D.W_F - 7 * wY + 1 := fun hM21 => by
    by_cases hR0 : S.R = 0
    · rw [hR0, natDegree_zero, zero_add]; have := S.natDegree_p_add_M21_le hM21; omega
    · have h := S.natDegree_R_mul_M21_le
      rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff _).mp hM21), natDegree_comp_X_sq] at h; exact h
  have hR_add_2M20 : S.R.natDegree + 2 * S.M20.natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
    by_cases hM20 : S.M20 = 0
    · rw [hM20, natDegree_zero, mul_zero, add_zero]
      have hM21 : S.M21 ≠ 0 := by
        intro h0; apply S.Q2_ne_zero; unfold KerD45Syzygy.Q2; rw [hM20, h0]; simp
      have := hR_add_2M21 hM21; omega
    · by_cases hR0 : S.R = 0
      · rw [hR0, natDegree_zero, zero_add]; have := S.natDegree_p_add_M20_le hM20; omega
      · have h := S.natDegree_R_mul_M20_le
        rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff _).mp hM20), natDegree_comp_X_sq] at h; exact h
  have hR_add_2M10 : S.M10 ≠ 0 → S.R.natDegree + 2 * S.M10.natDegree ≤ 2 * D.W_F - 3 * wY + 1 := fun hM10 => by
    by_cases hR0 : S.R = 0
    · rw [hR0, natDegree_zero, zero_add]; have := S.natDegree_p_add_M10_le hM10; omega
    · have h := S.natDegree_R_mul_M10_le
      rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff _).mp hM10), natDegree_comp_X_sq] at h; exact h
  have hResB := S.ResY_U_bound.trans D.natDegree_ResY_le
  have hf1 := S.f1_eval_P_U_bound
  have hQ2B := S.Q2_U_bound
  have hQ2D := S.two_mul_natDegree_p_add_Q2_le
  exact table4_p0_rows_sat m21Nz rGt p0M10D4 q2M21M10
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
    D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3
    S.p.natDegree S.R.natDegree S.UP.natDegree S.M21.natDegree S.M20.natDegree S.M10.natDegree
    S.n1U S.n2U S.n3U S.ntU S.a1U S.a2U S.a3U D.W_F hBS
    ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1,
     hU.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.2.1,
     hU.2.2.2.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.2.2.2.2⟩
    (by omega) (by omega)
    (by have := hU.1; have := hU.2.1; have := hU.2.2.1; omega)
    (by have := hU.2.2.2.2.2.2.2.1; have := hU.2.2.2.2.2.2.2.2.1; have := hU.2.2.2.2.2.2.2.2.2.1; omega)
    (by have := hU.1; have := hU.2.1; have := hU.2.2.1; omega)
    ⟨fun hm => by
        have hm0 : S.M21 = 0 := by simpa [m21Nz] using hm
        have hM10 : S.M10 ≠ 0 := by intro h0; apply hP0; unfold KerD45Syzygy.P0; rw [hm0, h0]; simp
        have hB := S.pM10_bound_of_M21_zero hm0 hM10; omega,
     fun hm => by
        have hm1 : S.M21 ≠ 0 := by simpa [m21Nz] using hm
        have h1 := S.natDegree_p_add_M21_le hm1; have h2 := hR_add_2M21 hm1; exact ⟨by omega, by omega⟩⟩
    ⟨fun hq => by
        have hQ2_deg : S.Q2.natDegree ≤ 2 * S.M20.natDegree := by
          by_cases h0 : S.M21 = 0 ∨ S.M10 = 0
          · rcases h0 with h | h
            · unfold KerD45Syzygy.Q2; rw [h, zero_mul, add_zero, natDegree_pow]
            · unfold KerD45Syzygy.Q2; rw [h, mul_zero, add_zero, natDegree_pow]
          · push Not at h0
            have hm1 : m21Nz = true := by simp [m21Nz, h0.1]
            simp only [q2M21M10, hm1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not,
              not_and, not_lt] at hq
            have hle := hq h0.2
            unfold KerD45Syzygy.Q2
            exact (natDegree_add_le _ _).trans (max_le natDegree_pow_le (natDegree_mul_le.trans hle))
        have := hU.1; have := hU.2.1; have := hU.2.2.1
        exact ⟨by omega, by omega⟩,
     fun hqt => by
        have hm1 : m21Nz = true := by
          by_contra hf; have hm0 : m21Nz = false := Bool.eq_false_of_not_eq_true hf
          simp only [q2M21M10, hm0, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hqt
        simp only [q2M21M10, hm1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hqt
        have hQ2_deg : S.Q2.natDegree ≤ S.M21.natDegree + S.M10.natDegree := by
          unfold KerD45Syzygy.Q2
          exact (natDegree_add_le _ _).trans (max_le (natDegree_pow_le.trans (by omega)) natDegree_mul_le)
        have hB := hR_add_2M10 hqt.1
        have := hU.1; have := hU.2.1; have := hU.2.2.1
        exact ⟨by omega, by omega⟩⟩
    ⟨fun hrt => by
        have hr : 2 * S.p.natDegree + wY < S.R.natDegree := by simpa [rGt] using hrt
        have hB := S.H1_U_bound.trans (S.natDegree_H1_le_of_gt hr)
        exact ⟨by omega, by omega, S.natDegree_UP_eq_of_gt hr⟩,
     fun hrf => by
        have hle : S.R.natDegree ≤ 2 * S.p.natDegree + wY := by
          have : ¬ (2 * S.p.natDegree + wY < S.R.natDegree) := by simpa [rGt] using hrf
          omega
        have hB := S.H1_U_bound.trans (S.natDegree_H1_le_of_le hle)
        exact ⟨hle, S.natDegree_UP_le_of_le hle, by omega⟩⟩
    ⟨fun hp0 => by
        have hm1 : m21Nz = true := by
          by_contra hf; have hm0 : m21Nz = false := Bool.eq_false_of_not_eq_true hf
          simp only [p0M10D4, hm0, Bool.not_false, ↓reduceIte, Bool.true_eq_false] at hp0
        simp only [p0M10D4, hm1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not] at hp0
        have hP0_deg : S.P0.natDegree ≤ 2 * S.R.natDegree + S.M21.natDegree := by
          unfold KerD45Syzygy.P0
          by_cases hM10 : S.M10 = 0
          · rw [hM10, mul_zero, zero_add]
            exact natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [S.natDegree_q_eq_R])) le_rfl)
          · have hlt : 4 * S.p.natDegree + S.M10.natDegree < 2 * S.q.natDegree + S.M21.natDegree := by
              push Not at hp0; exact (hp0 hM10).2
            rw [S.natDegree_q_eq_R] at hlt
            exact (natDegree_add_le _ _).trans (max_le
              (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl) |>.trans (by omega))
              (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [S.natDegree_q_eq_R])) le_rfl)))
        exact (S.P0_U_bound hP0).trans hP0_deg,
     fun hp0t => by
        have hM10 : S.M10 ≠ 0 := by
          by_cases hm : m21Nz = false
          · have hm0 : S.M21 = 0 := by simpa [m21Nz] using hm
            intro h0; apply hP0; unfold KerD45Syzygy.P0; rw [hm0, h0]; simp
          · have hmt : m21Nz = true := Bool.eq_true_of_not_eq_false hm
            simp only [p0M10D4, hmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hp0t
            exact hp0t.1
        have hP0_deg : S.P0.natDegree ≤ 4 * S.p.natDegree + S.M10.natDegree := by
          unfold KerD45Syzygy.P0
          by_cases hm : S.M21 = 0
          · rw [hm, mul_zero, add_zero]; exact natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl)
          · have hmt : m21Nz = true := by simp [m21Nz, hm]
            simp only [p0M10D4, hmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hp0t
            rcases hp0t.2 with hq0 | hle
            · rw [hq0, zero_pow (by norm_num), zero_mul, add_zero]
              exact natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl)
            · exact (natDegree_add_le _ _).trans (max_le
                (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl))
                (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl) |>.trans hle))
        have hB := hR_add_2M10 hM10
        exact ⟨by omega, (S.P0_U_bound hP0).trans hP0_deg⟩⟩

/-! ### Part 3: `T4ABranch.b1c1` (24 branches, `bCase ∈ 0..5`, `nv = 21`) -/

private def b1c1Vec (n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg
    e1 e2 erem H1Deg D1Deg WF : ℕ) : Fin 21 → ℚ := fun j =>
  match j.val with
  | 0 => (n0 : ℚ) / (N : ℚ) | 1 => (n1 : ℚ) / (N : ℚ)
  | 2 => (n2 : ℚ) / (N : ℚ) | 3 => (n3 : ℚ) / (N : ℚ)
  | 4 => (nt : ℚ) / (N : ℚ) | 5 => (a0 : ℚ) / (N : ℚ)
  | 6 => (a1 : ℚ) / (N : ℚ) | 7 => (a2 : ℚ) / (N : ℚ)
  | 8 => (a3 : ℚ) / (N : ℚ) | 9 => (2 * pDeg : ℚ) / (N : ℚ)
  | 10 => (g2Deg : ℚ) / (N : ℚ) | 11 => (M20Deg : ℚ) / (N : ℚ)
  | 12 => (RDeg : ℚ) / (N : ℚ) | 13 => (UPDeg : ℚ) / (N : ℚ)
  | 14 => (e1 : ℚ) / (N : ℚ) | 15 => (e2 : ℚ) / (N : ℚ)
  | 16 => (erem : ℚ) / (N : ℚ) | 17 => (H1Deg : ℚ) / (N : ℚ)
  | 18 => (D1Deg : ℚ) / (N : ℚ) | 19 => 0
  | _ => (WF : ℚ) / (wY : ℚ)

private lemma b1c1Vec_nonneg (n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg
    e1 e2 erem H1Deg D1Deg WF : ℕ) (j : Fin 21) :
    0 ≤ b1c1Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg e1 e2 erem H1Deg D1Deg WF j := by
  unfold b1c1Vec; split <;> positivity

private theorem table4_b1c1_rows_sat
    (rGt r4g4 : Bool) (bCase : ℕ)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg
      e1 e2 erem H1Deg D1Deg WF : ℕ)
    (hBS : let x := b1c1Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg e1 e2 erem H1Deg D1Deg WF
           let (ubB, eqB) := baseT4Rows 20 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
           (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r))
    (hWF_hi : WF < 6 * wY)
    (heq0 : n2 + 3 * n3 + 2 * nt + e1 + e2 + erem = M20Deg)
    (he1_le : e1 ≤ n1) (he2_le : e2 ≤ n2 + n3) (hD1_le : D1Deg ≤ pDeg)
    (hH1_base : ((n1 : ℤ) - (e1 : ℤ)) + 3 * ((n2 : ℤ) + (n3 : ℤ) - (e2 : ℤ)) ≤ (H1Deg : ℤ))
    (hRes_col1a : 8 * (M20Deg : ℤ) + (H1Deg : ℤ) - (g2Deg : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4)
    (hRes_col1b : (n1 : ℤ) + 11 * (n2 : ℤ) + 29 * (n3 : ℤ) + 18 * (nt : ℤ) - (g2Deg : ℤ) ≤ 8 * (WF : ℤ) - 20 * (wY : ℤ) + 4)
    (hg2_lo : n3 + 2 * nt ≤ g2Deg)
    (hg2_hi : (g2Deg : ℤ) ≤ (WF : ℤ) - 5 * (wY : ℤ) + 1)
    (hpM20_g2 : 2 * (pDeg : ℤ) + 2 * (M20Deg : ℤ) - (g2Deg : ℤ) ≤ (WF : ℤ) - (wY : ℤ))
    (hR_2M20 : 2 * (M20Deg : ℤ) + (RDeg : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1)
    (hUP_2M20 : 2 * (M20Deg : ℤ) + (UPDeg : ℤ) ≤ 2 * (WF : ℤ) - 5 * (wY : ℤ) + 1)
    (hUP_a12 : a1 + a2 ≤ e1 + e2 + erem + UPDeg)
    (hRes_ord1 : n1 + 11 * n2 + 29 * n3 + 18 * nt ≤ 8 * M20Deg + H1Deg)
    (hRes_ord2 : n1 + 8 * n2 + 20 * n3 + 10 * nt ≤ 5 * M20Deg + H1Deg)
    (hRes_ord3 : n1 + 6 * n2 + 12 * n3 + 6 * nt ≤ 3 * M20Deg + H1Deg)
    (h4D1_H1 : 4 * D1Deg ≤ H1Deg)
    (h2D1_H1 : 2 * (D1Deg : ℤ) + (n1 : ℤ) + 3 * (n2 : ℤ) + 3 * (n3 : ℤ) - (e1 : ℤ) - 3 * (e2 : ℤ) - (erem : ℤ) ≤ (H1Deg : ℤ))
    (hR_b : (rGt = true → 2 * (pDeg : ℤ) - (RDeg : ℤ) ≤ -(wY : ℤ) - 1 ∧ UPDeg = RDeg) ∧
        (rGt = false → RDeg ≤ 2 * pDeg + wY ∧ UPDeg ≤ 2 * pDeg + wY))
    (hT_b : (r4g4 = true → H1Deg ≤ 4 * RDeg + g2Deg) ∧
        (r4g4 = false → (H1Deg : ℤ) - 8 * (pDeg : ℤ) ≤ (WF : ℤ) - (wY : ℤ) + 1))
    (hB_b :
      let thrLe := 6 * n0 + 4 * n1 + 2 * e1 + 6 * e2 + 10 * pDeg + 2 * M20Deg ≤ 3 * N
      let thrGe := 3 * N ≤ 6 * n0 + 4 * n1 + 2 * e1 + 6 * e2 + 10 * pDeg + 2 * M20Deg
      let b1Eq := g2Deg + H1Deg = n0 + n1 + 3 * n2 + 7 * n3 + 4 * nt + 10 * pDeg + 2 * e1 + 2 * e2 + 2 * erem
      let b1R1 := 2 * (g2Deg : ℤ) - 2 * (H1Deg : ℤ) + 2 * (n1 : ℤ) + 6 * (n2 : ℤ) - 6 * (nt : ℤ) -
          2 * (n0 : ℤ) - 10 * (e1 : ℤ) - 22 * (e2 : ℤ) - 14 * (erem : ℤ) ≤ 0
      let b1R2 := (g2Deg : ℤ) - (H1Deg : ℤ) + (n1 : ℤ) + 3 * (n2 : ℤ) - (n3 : ℤ) - 4 * (nt : ℤ) -
          (n0 : ℤ) - 5 * (e1 : ℤ) - 8 * (e2 : ℤ) - 3 * (erem : ℤ) ≤ 0
      let r203 := 3 * (n1 : ℤ) + 3 * (n2 : ℤ) + 3 * (n3 : ℤ) - 3 * (e1 : ℤ) - 3 * (e2 : ℤ) -
          2 * (erem : ℤ) - 2 * (D1Deg : ℤ) ≤ (H1Deg : ℤ)
      let r211 := 2 * (n1 : ℤ) + 3 * (n2 : ℤ) + 3 * (n3 : ℤ) - 2 * (e1 : ℤ) - 3 * (e2 : ℤ) - (erem : ℤ) ≤ (H1Deg : ℤ)
      let r214 := 8 * pDeg + 3 * n2 + 3 * n3 ≤ 2 * n0 + n1 + 4 * e2 + 2 * g2Deg + H1Deg
      let rW2b := 2 * (n1 : ℤ) + 4 * (n2 : ℤ) + 4 * (n3 : ℤ) - 2 * (e1 : ℤ) - 4 * (e2 : ℤ) ≤ (H1Deg : ℤ) + (g2Deg : ℤ)
      let d2Le := 6 * (n0 : ℤ) + 4 * (n1 : ℤ) + 2 * (e1 : ℤ) + 6 * (e2 : ℤ) + (g2Deg : ℤ) + (WF : ℤ) - (wY : ℤ) + 1 + 8 * (pDeg : ℤ) ≤ 3 * (N : ℤ)
      let d2Ge := 3 * (N : ℤ) ≤ 6 * (n0 : ℤ) + 4 * (n1 : ℤ) + 2 * (e1 : ℤ) + 6 * (e2 : ℤ) + (g2Deg : ℤ) + (WF : ℤ) - (wY : ℤ) + 1 + 8 * (pDeg : ℤ)
      (bCase = 0 → thrLe ∧ b1Eq ∧ d2Le ∧ r203 ∧ b1R1 ∧ b1R2) ∧
      (bCase = 1 → thrLe ∧ b1Eq ∧ d2Ge) ∧
      (bCase = 2 → thrGe ∧ r211 ∧ b1R1 ∧ b1R2) ∧
      (bCase = 3 → thrGe ∧ r214) ∧
      (bCase = 4 → thrLe ∧ rW2b ∧ r211 ∧ b1R1 ∧ b1R2) ∧
      (bCase ≠ 0 → bCase ≠ 1 → bCase ≠ 2 → bCase ≠ 3 → bCase ≠ 4 → thrLe ∧ rW2b ∧ r214)) :
    let br := T4ABranch.b1c1 rGt r4g4 bCase
    let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    let x := b1c1Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg e1 e2 erem H1Deg D1Deg WF
    (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
    (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  let x := b1c1Vec n0 n1 n2 n3 nt a0 a1 a2 a3 pDeg g2Deg M20Deg RDeg UPDeg e1 e2 erem H1Deg D1Deg WF
  have hBV := baseT4Rows_valid (nv := 21) (ic := 20) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hc_nn : (0 : ℚ) ≤ (WF : ℚ) / (wY : ℚ) := by positivity
  have hWF_lt6 : (WF : ℚ) / (wY : ℚ) < 6 := by
    rw [div_lt_iff₀ wY_posQ]
    have : (WF : ℚ) < 6 * (wY : ℚ) := by exact_mod_cast hWF_hi
    linarith only [this]
  have heq0_sat : ∀ r ∈ [mkEq [(2, cI 1), (3, cI 3), (4, cI 2), (14, cI 1), (15, cI 1), (16, cI 1), (11, cI (-1))] 0],
      RowValid 21 r ∧ RowSatEq x r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatEq_mkEq_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega,
      show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega,
      show (11 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : (n2 : ℚ) + 3 * (n3 : ℚ) + 2 * (nt : ℚ) + (e1 : ℚ) + (e2 : ℚ) + (erem : ℚ) = (M20Deg : ℚ) := by
      exact_mod_cast heq0
    push_cast; linarith only [hQ]
  have hrCore_sat : ∀ r ∈ ([
      mkStat [(14, cI 1), (1, cI (-1))] 0 false,
      mkStat [(15, cI 1), (2, cI (-1)), (3, cI (-1))] 0 false,
      mkStat [(19, cI 1), (18, cI (-1))] 0 false,
      mkStat [(18, cI 1), (19, cI 1), (9, cH (-1))] 0,
      mkStat [(1, cI 1), (2, cI 3), (3, cI 3), (14, cI (-1)), (15, cI (-3)), (17, cI (-1))] 0,
      mkStat [(11, cI 8), (17, cI 1), (10, cI (-1)), (20, cI (-4))] (-40),
      mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (10, cI (-1)), (20, cI (-4))] (-40),
      mkStat [(3, cI 1), (4, cI 2), (10, cI (-1))] 0,
      mkStat [(10, cI 1), (20, cH (-1))] (-10),
      mkStat [(9, cH 1), (10, cH (-1)), (11, cI 1), (20, cQ (-1))] (-1),
      mkStat [(11, cI 2), (12, cI 1), (20, cI (-1))] (-10),
      mkStat [(11, cI 2), (13, cI 1), (20, cI (-1))] (-10),
      mkStat [(6, cI 1), (7, cI 1), (14, cI (-1)), (15, cI (-1)), (16, cI (-1)), (13, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (11, cI (-8)), (17, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 8), (3, cI 20), (4, cI 10), (11, cI (-5)), (17, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 6), (3, cI 12), (4, cI 6), (11, cI (-3)), (17, cI (-1))] 0,
      mkStat [(18, cI 4), (17, cI (-1))] 0,
      mkStat [(18, cI 2), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 3), (14, cI (-1)), (15, cI (-3)), (16, cI (-1))] 0
    ] : List SparseRow), RowValid 21 r ∧ RowSatLe x r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rowValidSat_two_cI x (by omega) (by omega) rfl rfl he1_le
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (15 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (e2 : ℚ) ≤ (n2 : ℚ) + (n3 : ℚ) := by exact_mod_cast he2_le
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (19 : ℕ) < 21 by omega, show (18 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hnn : (0 : ℚ) ≤ (D1Deg : ℚ) := by positivity
      push_cast; linarith only [hnn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 21 by omega, show (19 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, ↓reduceDIte,
        x, b1c1Vec, cI_mul_div_N, cH_mul_div_N]
      have hQ : (D1Deg : ℚ) ≤ (pDeg : ℚ) := by exact_mod_cast hD1_le
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
        show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, ↓reduceDIte,
        x, b1c1Vec, cI_mul_div_N]
      have hQ : ((n1 : ℚ) - (e1 : ℚ)) + 3 * ((n2 : ℚ) + (n3 : ℚ) - (e2 : ℚ)) ≤ (H1Deg : ℚ) := by exact_mod_cast hH1_base
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (11 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega,
        show (20 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cI_mul_c_eq]
      have hQ : 8 * (M20Deg : ℚ) + (H1Deg : ℚ) - (g2Deg : ℚ) ≤ 8 * (WF : ℚ) - 20 * (wY : ℚ) + 4 := by exact_mod_cast hRes_col1a
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
        show (4 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cI_mul_c_eq]
      have hQ : (n1 : ℚ) + 11 * (n2 : ℚ) + 29 * (n3 : ℚ) + 18 * (nt : ℚ) - (g2Deg : ℚ) ≤
          8 * (WF : ℚ) - 20 * (wY : ℚ) + 4 := by exact_mod_cast hRes_col1b
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (3 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, ↓reduceDIte,
        x, b1c1Vec, cI_mul_div_N]
      have hQ : (n3 : ℚ) + 2 * (nt : ℚ) ≤ (g2Deg : ℚ) := by exact_mod_cast hg2_lo
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cH_mul_c_eq]
      have hQ : (g2Deg : ℚ) ≤ (WF : ℚ) - 5 * (wY : ℚ) + 1 := by exact_mod_cast hg2_hi
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (9 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega,
        show (20 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cH_mul_div_N, cI_mul_div_N, cQ_mul_c_eq]
      have hQ : 2 * (pDeg : ℚ) + 2 * (M20Deg : ℚ) - (g2Deg : ℚ) ≤ (WF : ℚ) - (wY : ℚ) := by exact_mod_cast hpM20_g2
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (11 : ℕ) < 21 by omega, show (12 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cI_mul_c_eq]
      have hQ : 2 * (M20Deg : ℚ) + (RDeg : ℚ) ≤ 2 * (WF : ℚ) - 5 * (wY : ℚ) + 1 := by exact_mod_cast hR_2M20
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (11 : ℕ) < 21 by omega, show (13 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cI_mul_c_eq]
      have hQ : 2 * (M20Deg : ℚ) + (UPDeg : ℚ) ≤ 2 * (WF : ℚ) - 5 * (wY : ℚ) + 1 := by exact_mod_cast hUP_2M20
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < 21 by omega, show (7 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
        show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega, show (13 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (a1 : ℚ) + (a2 : ℚ) ≤ (e1 : ℚ) + (e2 : ℚ) + (erem : ℚ) + (UPDeg : ℚ) := by exact_mod_cast hUP_a12
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
        show (4 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (n1 : ℚ) + 11 * (n2 : ℚ) + 29 * (n3 : ℚ) + 18 * (nt : ℚ) ≤ 8 * (M20Deg : ℚ) + (H1Deg : ℚ) := by exact_mod_cast hRes_ord1
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
        show (4 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (n1 : ℚ) + 8 * (n2 : ℚ) + 20 * (n3 : ℚ) + 10 * (nt : ℚ) ≤ 5 * (M20Deg : ℚ) + (H1Deg : ℚ) := by exact_mod_cast hRes_ord2
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
        show (4 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (n1 : ℚ) + 6 * (n2 : ℚ) + 12 * (n3 : ℚ) + 6 * (nt : ℚ) ≤ 3 * (M20Deg : ℚ) + (H1Deg : ℚ) := by exact_mod_cast hRes_ord3
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : 4 * (D1Deg : ℚ) ≤ (H1Deg : ℚ) := by exact_mod_cast h4D1_H1
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (18 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
        show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
        show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : 2 * (D1Deg : ℚ) + (n1 : ℚ) + 3 * (n2 : ℚ) + 3 * (n3 : ℚ) -
          (e1 : ℚ) - 3 * (e2 : ℚ) - (erem : ℚ) ≤ (H1Deg : ℚ) := by exact_mod_cast h2D1_H1
      push_cast; linarith only [hQ]
  have hR_sat :
      let (rR, eqR) :=
        if !rGt then ([mkStat [(9, cI (-1)), (12, cI 1)] 2, mkStat [(9, cI (-1)), (13, cI 1)] 2], [])
        else ([mkStat [(9, cI 1), (12, cI (-1))] (-2)], [mkEq [(12, cI 1), (13, cI (-1))] 0])
      (∀ r ∈ rR, RowValid 21 r ∧ RowSatLe x r) ∧ (∀ r ∈ eqR, RowValid 21 r ∧ RowSatEq x r) := by
    cases hr : rGt
    · simp only [hr, Bool.not_false, ↓reduceIte]
      have hRb := hR_b.2 hr
      constructor
      · intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 21 by omega, show (12 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
          have hQ : (RDeg : ℚ) ≤ 2 * (pDeg : ℚ) + (wY : ℚ) := by exact_mod_cast hRb.1
          push_cast; rw [hN_eq]; linarith only [hQ]
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (9 : ℕ) < 21 by omega, show (13 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
          have hQ : (UPDeg : ℚ) ≤ 2 * (pDeg : ℚ) + (wY : ℚ) := by exact_mod_cast hRb.2
          push_cast; rw [hN_eq]; linarith only [hQ]
      · intro r hr'; simp at hr'
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hRb := hR_b.1 hr
      constructor
      · intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
        refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (9 : ℕ) < 21 by omega, show (12 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
        have hQ : 2 * (pDeg : ℚ) - (RDeg : ℚ) ≤ -(wY : ℚ) - 1 := by exact_mod_cast hRb.1
        push_cast; rw [hN_eq]; linarith only [hQ]
      · intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
        refine ⟨rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega), ?_⟩
        rw [rowSatEq_mkEq_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (12 : ℕ) < 21 by omega, show (13 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
        rw [hRb.2]; push_cast; ring
  have hT_sat : ∀ r ∈ (if !r4g4 then [mkStat [(17, cI 1), (9, cI (-4)), (20, cH (-1))] (-2)]
      else [mkStat [(17, cI 1), (10, cI (-1)), (12, cI (-4))] 0]), RowValid 21 r ∧ RowSatLe x r := by
    intro r hr
    cases h4 : r4g4
    · simp only [h4, Bool.not_false, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (17 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cH_mul_c_eq]
      have hQ : (H1Deg : ℚ) - 8 * (pDeg : ℚ) ≤ (WF : ℚ) - (wY : ℚ) + 1 := by exact_mod_cast hT_b.2 h4
      push_cast; rw [hN_eq]; linarith only [hQ, hc_nn]
    · simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
      refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (17 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (12 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (H1Deg : ℚ) ≤ 4 * (RDeg : ℚ) + (g2Deg : ℚ) := by exact_mod_cast hT_b.1 h4
      push_cast; linarith only [hQ]
  let b1Rows_L : List SparseRow := [
    mkStat [(10, cI 1), (17, cI (-1)), (1, cI 1), (2, cI 3), (4, cI (-3)), (0, cI (-1)), (14, cI (-5)), (15, cI (-11)), (16, cI (-7))] 0,
    mkStat [(10, cI 1), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI (-1)), (4, cI (-4)), (0, cI (-1)), (14, cI (-5)), (15, cI (-8)), (16, cI (-3))] 0
  ]
  have hb1Rows_sat :
      (2 * (g2Deg : ℤ) - 2 * (H1Deg : ℤ) + 2 * (n1 : ℤ) + 6 * (n2 : ℤ) - 6 * (nt : ℤ) -
        2 * (n0 : ℤ) - 10 * (e1 : ℤ) - 22 * (e2 : ℤ) - 14 * (erem : ℤ) ≤ 0) →
      ((g2Deg : ℤ) - (H1Deg : ℤ) + (n1 : ℤ) + 3 * (n2 : ℤ) - (n3 : ℤ) - 4 * (nt : ℤ) -
        (n0 : ℤ) - 5 * (e1 : ℤ) - 8 * (e2 : ℤ) - 3 * (erem : ℤ) ≤ 0) →
      ∀ r ∈ b1Rows_L, RowValid 21 r ∧ RowSatLe x r := by
    intro hB1 hB2 r hr
    simp only [b1Rows_L, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
        show (2 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega, show (0 : ℕ) < 21 by omega,
        show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega,
        ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : 2 * (g2Deg : ℚ) - 2 * (H1Deg : ℚ) + 2 * (n1 : ℚ) + 6 * (n2 : ℚ) - 6 * (nt : ℚ) -
          2 * (n0 : ℚ) - 10 * (e1 : ℚ) - 22 * (e2 : ℚ) - 14 * (erem : ℚ) ≤ 0 := by exact_mod_cast hB1
      push_cast; linarith only [hQ]
    · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
      rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
        show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega,
        show (0 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega,
        show (16 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      have hQ : (g2Deg : ℚ) - (H1Deg : ℚ) + (n1 : ℚ) + 3 * (n2 : ℚ) - (n3 : ℚ) - 4 * (nt : ℚ) -
          (n0 : ℚ) - 5 * (e1 : ℚ) - 8 * (e2 : ℚ) - 3 * (erem : ℚ) ≤ 0 := by exact_mod_cast hB2
      push_cast; linarith only [hQ]
  have hrow_thr_le : 6 * n0 + 4 * n1 + 2 * e1 + 6 * e2 + 10 * pDeg + 2 * M20Deg ≤ 3 * N →
      RowValid 21 (mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12) ∧
      RowSatLe x (mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12) := by
    intro hle
    refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatLe_mkStat_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (0 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
      show (15 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega,
      ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : 6 * (n0 : ℚ) + 4 * (n1 : ℚ) + 2 * (e1 : ℚ) + 6 * (e2 : ℚ) + 10 * (pDeg : ℚ) + 2 * (M20Deg : ℚ) ≤ 3 * (N : ℚ) := by
      exact_mod_cast hle
    push_cast; linarith only [hQ]
  have hrow_thr_ge : 3 * N ≤ 6 * n0 + 4 * n1 + 2 * e1 + 6 * e2 + 10 * pDeg + 2 * M20Deg →
      RowValid 21 (mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12)) ∧
      RowSatLe x (mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12)) := by
    intro hge
    refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatLe_mkStat_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (0 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
      show (15 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, show (11 : ℕ) < 21 by omega,
      ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : 3 * (N : ℚ) ≤ 6 * (n0 : ℚ) + 4 * (n1 : ℚ) + 2 * (e1 : ℚ) + 6 * (e2 : ℚ) + 10 * (pDeg : ℚ) + 2 * (M20Deg : ℚ) := by
      exact_mod_cast hge
    push_cast; linarith only [hQ]
  have hrow_211_sat : 2 * (n1 : ℤ) + 3 * (n2 : ℤ) + 3 * (n3 : ℤ) - 2 * (e1 : ℤ) - 3 * (e2 : ℤ) - (erem : ℤ) ≤ (H1Deg : ℤ) →
      RowValid 21 (mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0) ∧
      RowSatLe x (mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0) := by
    intro hZ
    refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatLe_mkStat_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
      show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega,
      show (17 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : 2 * (n1 : ℚ) + 3 * (n2 : ℚ) + 3 * (n3 : ℚ) - 2 * (e1 : ℚ) - 3 * (e2 : ℚ) - (erem : ℚ) ≤ (H1Deg : ℚ) := by
      exact_mod_cast hZ
    push_cast; linarith only [hQ]
  have hrow_214_sat : 8 * pDeg + 3 * n2 + 3 * n3 ≤ 2 * n0 + n1 + 4 * e2 + 2 * g2Deg + H1Deg →
      RowValid 21 (mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0) ∧
      RowSatLe x (mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0) := by
    intro hB
    refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatLe_mkStat_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (9 : ℕ) < 21 by omega, show (0 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
      show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega,
      show (10 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega,
      show (3 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : 8 * (pDeg : ℚ) + 3 * (n2 : ℚ) + 3 * (n3 : ℚ) ≤
        2 * (n0 : ℚ) + (n1 : ℚ) + 4 * (e2 : ℚ) + 2 * (g2Deg : ℚ) + (H1Deg : ℚ) := by exact_mod_cast hB
    have hnn0 : (0 : ℚ) ≤ (n0 : ℚ) := by positivity
    have hnn1 : (0 : ℚ) ≤ (n1 : ℚ) := by positivity
    have hnne1 : (0 : ℚ) ≤ (e1 : ℚ) := by positivity
    have hnne2 : (0 : ℚ) ≤ (e2 : ℚ) := by positivity
    have hnner : (0 : ℚ) ≤ (erem : ℚ) := by positivity
    push_cast; linarith only [hQ, hnn0, hnn1, hnne1, hnne2, hnner]
  have hrow_W2b_sat : 2 * (n1 : ℤ) + 4 * (n2 : ℤ) + 4 * (n3 : ℤ) - 2 * (e1 : ℤ) - 4 * (e2 : ℤ) ≤ (H1Deg : ℤ) + (g2Deg : ℤ) →
      RowValid 21 (mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0) ∧
      RowSatLe x (mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0) := by
    intro hZ
    refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
    rw [rowSatLe_mkStat_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (17 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
      show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
      show (15 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
    have hQ : 2 * (n1 : ℚ) + 4 * (n2 : ℚ) + 4 * (n3 : ℚ) - 2 * (e1 : ℚ) - 4 * (e2 : ℚ) ≤ (H1Deg : ℚ) + (g2Deg : ℚ) := by
      exact_mod_cast hZ
    push_cast; linarith only [hQ]
  have hB1_eq_rows : g2Deg + H1Deg = n0 + n1 + 3 * n2 + 7 * n3 + 4 * nt + 10 * pDeg + 2 * e1 + 2 * e2 + 2 * erem →
      (RowValid 21 (mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0) ∧
       RowSatLe x (mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0)) ∧
      (RowValid 21 (mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0) ∧
       RowSatLe x (mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0)) := by
    intro hEqN
    have hEqQ : (g2Deg : ℚ) + (H1Deg : ℚ) =
        (n0 : ℚ) + (n1 : ℚ) + 3 * (n2 : ℚ) + 7 * (n3 : ℚ) + 4 * (nt : ℚ) +
        10 * (pDeg : ℚ) + 2 * (e1 : ℚ) + 2 * (e2 : ℚ) + 2 * (erem : ℚ) := by exact_mod_cast hEqN
    refine ⟨⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩,
            ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩⟩
    · rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
        show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega,
        show (0 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
        show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      push_cast; linarith only [hEqQ]
    · rw [rowSatLe_mkStat_iff]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (10 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega,
        show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega, show (4 : ℕ) < 21 by omega,
        show (0 : ℕ) < 21 by omega, show (9 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
        show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
      push_cast; linarith only [hEqQ]
  have hB_sat : ∀ r ∈ (
      if bCase == 0 then
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0,
         mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0,
         mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (10, cI 1), (20, cH 1), (9, cI 4)] 14,
         mkStat [(1, cI 3), (2, cI 3), (3, cI 3), (14, cI (-3)), (15, cI (-3)), (16, cI (-2)), (18, cI (-2)), (17, cI (-1))] 0] ++ b1Rows_L
      else if bCase == 1 then
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0,
         mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0,
         mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (10, cI (-1)), (20, cH (-1)), (9, cI (-4))] (-14)]
      else if bCase == 2 then
        [mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12),
         mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0] ++ b1Rows_L
      else if bCase == 3 then
        [mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12),
         mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0]
      else if bCase == 4 then
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0,
         mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0] ++ b1Rows_L
      else
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0,
         mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0]),
      RowValid 21 r ∧ RowSatLe x r := by
    intro r hr
    by_cases h0 : bCase = 0
    · have ⟨hthr, hEq, hd2, h203, hR1, hR2⟩ := hB_b.1 h0
      have ⟨hB1a, hB1b⟩ := hB1_eq_rows hEq
      simp only [h0, beq_self_eq_true, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | hr
      · exact hrow_thr_le hthr
      · exact hB1a
      · exact hB1b
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (0 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
          show (15 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
          show (9 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cH_mul_c_eq]
        have hQ : 6 * (n0 : ℚ) + 4 * (n1 : ℚ) + 2 * (e1 : ℚ) + 6 * (e2 : ℚ) + (g2Deg : ℚ) +
            (WF : ℚ) - (wY : ℚ) + 1 + 8 * (pDeg : ℚ) ≤ 3 * (N : ℚ) := by exact_mod_cast hd2
        push_cast; rw [hN_eq] at hQ ⊢; linarith only [hQ, hWF_lt6]
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (1 : ℕ) < 21 by omega, show (2 : ℕ) < 21 by omega, show (3 : ℕ) < 21 by omega,
          show (14 : ℕ) < 21 by omega, show (15 : ℕ) < 21 by omega, show (16 : ℕ) < 21 by omega,
          show (18 : ℕ) < 21 by omega, show (17 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N]
        have hQ : 3 * (n1 : ℚ) + 3 * (n2 : ℚ) + 3 * (n3 : ℚ) - 3 * (e1 : ℚ) - 3 * (e2 : ℚ) -
            2 * (erem : ℚ) - 2 * (D1Deg : ℚ) ≤ (H1Deg : ℚ) := by exact_mod_cast h203
        push_cast; linarith only [hQ]
      · exact hb1Rows_sat hR1 hR2 r hr
    · by_cases h1 : bCase = 1
      · have ⟨hthr, hEq, hd2⟩ := hB_b.2.1 h1
        have ⟨hB1a, hB1b⟩ := hB1_eq_rows hEq
        simp only [h1, show (1 == 0) = false by decide, show (1 == 1) = true by decide,
          Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hrow_thr_le hthr
        · exact hB1a
        · exact hB1b
        · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
          rw [rowSatLe_mkStat_iff]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            show (0 : ℕ) < 21 by omega, show (1 : ℕ) < 21 by omega, show (14 : ℕ) < 21 by omega,
            show (15 : ℕ) < 21 by omega, show (10 : ℕ) < 21 by omega, show (20 : ℕ) < 21 by omega,
            show (9 : ℕ) < 21 by omega, ↓reduceDIte, x, b1c1Vec, cI_mul_div_N, cH_mul_c_eq]
          have hQ : 3 * (N : ℚ) ≤ 6 * (n0 : ℚ) + 4 * (n1 : ℚ) + 2 * (e1 : ℚ) + 6 * (e2 : ℚ) +
              (g2Deg : ℚ) + (WF : ℚ) - (wY : ℚ) + 1 + 8 * (pDeg : ℚ) := by exact_mod_cast hd2
          push_cast; rw [hN_eq] at hQ ⊢; linarith only [hQ, hc_nn]
      · by_cases h2 : bCase = 2
        · have ⟨hthr, h211, hR1, hR2⟩ := hB_b.2.2.1 h2
          simp only [h2, show (2 == 0) = false by decide, show (2 == 1) = false by decide,
            show (2 == 2) = true by decide, Bool.false_eq_true, ↓reduceIte,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with (rfl | rfl) | hr
          · exact hrow_thr_ge hthr
          · exact hrow_211_sat h211
          · exact hb1Rows_sat hR1 hR2 r hr
        · by_cases h3 : bCase = 3
          · have ⟨hthr, h214⟩ := hB_b.2.2.2.1 h3
            simp only [h3, show (3 == 0) = false by decide, show (3 == 1) = false by decide,
              show (3 == 2) = false by decide, show (3 == 3) = true by decide, Bool.false_eq_true, ↓reduceIte,
              List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact hrow_thr_ge hthr
            · exact hrow_214_sat h214
          · by_cases h4 : bCase = 4
            · have ⟨hthr, hW2b, h211, hR1, hR2⟩ := hB_b.2.2.2.2.1 h4
              simp only [h4, show (4 == 0) = false by decide, show (4 == 1) = false by decide,
                show (4 == 2) = false by decide, show (4 == 3) = false by decide,
                show (4 == 4) = true by decide, Bool.false_eq_true, ↓reduceIte,
                List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with (rfl | rfl | rfl) | hr
              · exact hrow_thr_le hthr
              · exact hrow_W2b_sat hW2b
              · exact hrow_211_sat h211
              · exact hb1Rows_sat hR1 hR2 r hr
            · have ⟨hthr, hW2b, h214⟩ := hB_b.2.2.2.2.2 h0 h1 h2 h3 h4
              have hne0 : (bCase == 0) = false := beq_false_of_ne h0
              have hne1 : (bCase == 1) = false := beq_false_of_ne h1
              have hne2 : (bCase == 2) = false := beq_false_of_ne h2
              have hne3 : (bCase == 3) = false := beq_false_of_ne h3
              have hne4 : (bCase == 4) = false := beq_false_of_ne h4
              simp only [hne0, hne1, hne2, hne3, hne4, Bool.false_eq_true, ↓reduceIte,
                List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact hrow_thr_le hthr
              · exact hrow_W2b_sat hW2b
              · exact hrow_214_sat h214
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | (((hr | hr) | hr) | hr)
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · exact hrCore_sat r hr
    · exact hR_sat.1 r hr
    · exact hT_sat r hr
    · exact hB_sat r hr
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | (hr | hr)
    · exact ⟨hBV.2 r hr, hBS.2 r hr⟩
    · exact heq0_sat r hr
    · exact hR_sat.2 r hr

/-- **Theorem (`T4ABranch.b1c1`):** For any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 = 0`,
`D` satisfies all rows of `buildT4ARows (.b1c1 rGt r4g4 bCase)` for an exact `(rGt, r4g4, bCase)`
with `bCase < 6`! -/
theorem table4_b1c1_sat {D : KerD45Data} (S : KerD45Syzygy D) (hP0 : S.P0 = 0) (hM21 : S.M21 = 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    ∃ (rGt r4g4 : Bool) (bCase : ℕ), bCase < 6 ∧
      let br := T4ABranch.b1c1 rGt r4g4 bCase
      let rows := buildT4ARows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin (t4aNumVars br) → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by dsimp only [br, t4aNumVars]; omega⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by dsimp only [br, t4aNumVars]; omega⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨20, by dsimp only [br, t4aNumVars]; omega⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  classical
  -- Step 1: M10 = 0, M20 ≠ 0, Cj 1 = Bj 1 = Pj 1 = gj 1 = 0!
  have hM10 : S.M10 = 0 := by
    have h := hP0; unfold KerD45Syzygy.P0 at h; rw [hM21, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 4 S.hp)
  have hM20_ne : S.M20 ≠ 0 := by
    intro h0; apply S.Q2_ne_zero; unfold KerD45Syzygy.Q2; rw [h0, hM21]; simp
  have hpM20_ne : S.p * S.M20 ≠ 0 := mul_ne_zero S.hp hM20_ne
  have hBj1 : D.Bj 1 = 0 := by
    have h1 := S.p_mul_M21; rw [hM21, mul_zero] at h1
    have h2 := S.p_mul_M10; rw [hM10, mul_zero] at h2
    have hmul : (S.p * S.M20) * D.Bj 1 = 0 := by
      rw [S.p_mul_M20]
      have hz := CharTwo.add_self_eq_zero (D.Cj 1 * D.Bj 2 * D.Bj 0)
      linear_combination D.Bj 0 * h1.symm + D.Bj 2 * h2.symm - hz
    exact (mul_eq_zero.mp hmul).resolve_left hpM20_ne
  have hCj1 : D.Cj 1 = 0 := by
    have h1 := S.p_mul_M21; rw [hM21, mul_zero, hBj1, mul_zero, zero_add] at h1
    have h2 := S.p_mul_M10; rw [hM10, mul_zero, hBj1, mul_zero, add_zero] at h2
    have hmul : (S.p * S.M20) * D.Cj 1 = 0 := by
      rw [S.p_mul_M20]
      linear_combination D.Cj 2 * h2.symm + D.Cj 0 * h1.symm
    exact (mul_eq_zero.mp hmul).resolve_left hpM20_ne
  have hgj1 : D.gj 1 = 0 := by unfold KerD45Data.gj; rw [hCj1, hBj1]; simp
  have hH1_eq : S.H1 = S.p.comp (X ^ 2) ^ 4 * D.gj 0 + S.R ^ 4 * D.gj 2 := by
    unfold KerD45Syzygy.H1; rw [hgj1, mul_zero, add_zero]
  have hf1_eval_eq : D.f1.eval D.P = D.gj 0 + D.gj 2 * D.P ^ 4 := by
    rw [D.f1_eq_sum, Fin.sum_univ_three]
    simp [hgj1, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have hResY_eq : D.ResY = S.H1 * (S.M20.comp (X ^ 2)) ^ 4 := by
    rw [S.ResY_eq_H1_mul_Q2_sq]; unfold KerD45Syzygy.Q2
    rw [hM21, zero_mul, add_zero, pow_comp]; ring
  have hResY_deg : D.ResY.natDegree = S.H1.natDegree + 8 * S.M20.natDegree := by
    rw [hResY_eq, natDegree_mul S.H1_ne_zero (pow_ne_zero 4 (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne)),
      natDegree_pow, natDegree_comp_X_sq]; ring
  -- Master b1c1 identity: H1 + p(X^2)^4 * f1(X, P) = g2 * UP^4!
  have hb1c1_id : S.H1 + S.p.comp (X ^ 2) ^ 4 * D.f1.eval D.P = D.gj 2 * S.UP ^ 4 := by
    rw [hH1_eq, hf1_eval_eq]
    have hUP4 : S.UP ^ 4 = S.p.comp (X ^ 2) ^ 4 * D.P ^ 4 + S.R ^ 4 := by
      unfold KerD45Syzygy.UP; rw [char2_add_pow_four, mul_pow]
    rw [hUP4]
    have hz1 := CharTwo.add_self_eq_zero (S.p.comp (X ^ 2) ^ 4 * D.gj 0)
    linear_combination hz1
  -- Master b1c1 Wronskian identity: g2' * H1 + g2 * H1' = p(X^2)^5 * M20(X^2)!
  have hb1c1_wr : (D.gj 2 * S.H1).derivative = S.p.comp (X ^ 2) ^ 5 * S.M20.comp (X ^ 2) := by
    have hg0' : (D.gj 0).derivative = (D.Bj 0).comp (X ^ 2) := derivative_even_odd_char2 (D.Cj 0) (D.Bj 0)
    have hg2' : (D.gj 2).derivative = (D.Bj 2).comp (X ^ 2) := derivative_even_odd_char2 (D.Cj 2) (D.Bj 2)
    have hH1' : S.H1.derivative = S.p.comp (X ^ 2) ^ 4 * (D.Bj 0).comp (X ^ 2) + S.R ^ 4 * (D.Bj 2).comp (X ^ 2) := by
      rw [hH1_eq, derivative_add, derivative_mul, char2_derivative_pow_four, zero_mul, zero_add, hg0',
        derivative_mul, char2_derivative_pow_four, zero_mul, zero_add, hg2']
    rw [derivative_mul, hH1', hg2', hH1_eq]
    have hM20c : (S.p * S.M20).comp (X ^ 2) = (D.Cj 2).comp (X ^ 2) * (D.Bj 0).comp (X ^ 2) +
        (D.Cj 0).comp (X ^ 2) * (D.Bj 2).comp (X ^ 2) := by
      rw [S.p_mul_M20, add_comp, mul_comp, mul_comp]
    rw [mul_comp] at hM20c
    have hterm : D.gj 2 * (D.Bj 0).comp (X ^ 2) + (D.Bj 2).comp (X ^ 2) * D.gj 0 =
        S.p.comp (X ^ 2) * S.M20.comp (X ^ 2) := by
      unfold KerD45Data.gj
      have hz := CharTwo.add_self_eq_zero (X * (D.Bj 2).comp (X ^ 2) * (D.Bj 0).comp (X ^ 2))
      linear_combination -hM20c + hz
    have hzR := CharTwo.add_self_eq_zero ((D.Bj 2).comp (X ^ 2) * S.R ^ 4 * D.gj 2)
    calc (D.Bj 2).comp (X ^ 2) * (S.p.comp (X ^ 2) ^ 4 * D.gj 0 + S.R ^ 4 * D.gj 2) +
          D.gj 2 * (S.p.comp (X ^ 2) ^ 4 * (D.Bj 0).comp (X ^ 2) + S.R ^ 4 * (D.Bj 2).comp (X ^ 2))
        = S.p.comp (X ^ 2) ^ 4 * (D.gj 2 * (D.Bj 0).comp (X ^ 2) + (D.Bj 2).comp (X ^ 2) * D.gj 0) +
            ((D.Bj 2).comp (X ^ 2) * S.R ^ 4 * D.gj 2 + (D.Bj 2).comp (X ^ 2) * S.R ^ 4 * D.gj 2) := by ring
      _ = S.p.comp (X ^ 2) ^ 5 * S.M20.comp (X ^ 2) := by rw [hterm, hzR, add_zero]; ring
  -- Step 2: Partition Idx into the 5 domain buckets!
  let I0 : Finset Idx := Finset.univ.filter fun i => D.k i = 0
  let I1U : Finset Idx := Finset.univ.filter fun i => D.k i = 1 ∧ S.isU0 i
  let I1noU : Finset Idx := Finset.univ.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i
  let I2U : Finset Idx := Finset.univ.filter fun i => 2 ≤ D.k i ∧ S.isU0 i
  let I2noU : Finset Idx := Finset.univ.filter fun i => 2 ≤ D.k i ∧ ¬ S.isU0 i
  let e1_cnt : ℕ := I1noU.card
  let e2_cnt : ℕ := I2noU.card
  have he1_le : e1_cnt ≤ D.n1 := by
    unfold e1_cnt I1noU KerD45Data.n1
    exact Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1)
  have hI0_card : I0.card = D.n0 := by
    unfold I0 KerD45Data.n0
    apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hI1_sum : I1U.card + e1_cnt = D.n1 := by
    have hdisj : Disjoint I1U I1noU := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.2 h1.2
    have hunion : I1U ∪ I1noU = Finset.univ.filter fun i => D.k i = 1 := by
      ext i; simp only [I1U, I1noU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.elim And.left And.left, fun h => by by_cases hU : S.isU0 i; exact Or.inl ⟨h, hU⟩; exact Or.inr ⟨h, hU⟩⟩
    unfold e1_cnt KerD45Data.n1
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hI2_sum : I2U.card + e2_cnt = D.n2 + D.n3 := by
    have hdisj : Disjoint I2U I2noU := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.2 h1.2
    have hunion : I2U ∪ I2noU = Finset.univ.filter fun i => 2 ≤ D.k i := by
      ext i; simp only [I2U, I2noU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.elim And.left And.left, fun h => by by_cases hU : S.isU0 i; exact Or.inl ⟨h, hU⟩; exact Or.inr ⟨h, hU⟩⟩
    have h23 : (Finset.univ.filter fun i => 2 ≤ D.k i).card = D.n2 + D.n3 := by
      have hd23 : Disjoint (Finset.univ.filter fun i : Idx => D.k i = 2)
          (Finset.univ.filter fun i : Idx => 3 ≤ D.k i) :=
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hu23 : (Finset.univ.filter fun i : Idx => D.k i = 2) ∪
          (Finset.univ.filter fun i : Idx => 3 ≤ D.k i) = Finset.univ.filter fun i => 2 ≤ D.k i := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      unfold KerD45Data.n2 KerD45Data.n3
      rw [← hu23, Finset.card_union_of_disjoint hd23]
    unfold e2_cnt
    rw [← Finset.card_union_of_disjoint hdisj, hunion, h23]
  have he2_le : e2_cnt ≤ D.n2 + D.n3 := by omega
  -- Base M20 order at each i : Idx!
  let baseM20 : Idx → ℕ := fun i =>
    if D.k i = 0 then 0
    else if D.k i = 1 then (if S.isU0 i then 0 else 1)
    else if S.isU0 i then 2 * D.k i - 3 else 2 * D.k i - 2
  have hbaseM20_dvd : ∀ i : Idx, (X - C (BinaryIRSProfile.domain i ^ 2)) ^ baseM20 i ∣ S.M20 := by
    intro i
    have hM20sh : S.M20sh (D.y i) = S.M20 := by unfold KerD45Syzygy.M20sh; rw [hM21, mul_zero, add_zero]
    have hloc := S.local_shifted_minor_ords i
    rw [hM20sh] at hloc
    dsimp [baseM20]
    split_ifs with h0 h1 hU hU2
    · simp
    · simp
    · have hle := (hloc.2 hU).2.1; rw [if_neg h0, if_pos h1] at hle; exact hle
    · have hle := hloc.1.2.1; rw [if_neg (by omega)] at hle; exact hle
    · have hle := (hloc.2 hU2).2.1; rw [if_neg h0, if_neg h1] at hle; exact hle
  have hbaseM20_sum : ∑ i : Idx, baseM20 i = D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt := by
    have hgen : ∀ S0 : Finset Idx,
        ∑ i ∈ S0, baseM20 i =
          (S0.filter fun i => D.k i = 2).card + 3 * (S0.filter fun i => 3 ≤ D.k i).card +
          2 * ∑ i ∈ S0, (D.k i - 3) + (S0.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i).card +
          (S0.filter fun i => 2 ≤ D.k i ∧ ¬ S.isU0 i).card := by
      intro S0
      have hrew : (S0.filter fun i => D.k i = 2).card + 3 * (S0.filter fun i => 3 ≤ D.k i).card +
          2 * ∑ i ∈ S0, (D.k i - 3) + (S0.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i).card +
          (S0.filter fun i => 2 ≤ D.k i ∧ ¬ S.isU0 i).card =
          ∑ i ∈ S0, ((if D.k i = 2 then 1 else 0) + (if 3 ≤ D.k i then 3 else 0) +
            2 * (D.k i - 3) + (if D.k i = 1 ∧ ¬ S.isU0 i then 1 else 0) +
            (if 2 ≤ D.k i ∧ ¬ S.isU0 i then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
          add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; dsimp [baseM20]
      by_cases hU : S.isU0 i <;> simp only [hU, not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
    unfold KerD45Data.n2 KerD45Data.n3 KerD45Data.nt e1_cnt e2_cnt I1noU I2noU
    exact hgen Finset.univ
  have hbaseM20_le : D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt ≤ S.M20.natDegree := by
    rw [← hbaseM20_sum]
    exact sum_ord_le_natDegree_of_dvd Finset.univ (fun i => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective S.M20 hM20_ne baseM20 (fun i _ => hbaseM20_dvd i)
  let erem_cnt : ℕ := S.M20.natDegree - (D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt)
  -- Step 3: Build S_0, S_1U, S_1noU, S_2U, S_2noU, S_hit, S_mis, R_F, Q_raw, G_b, S_b, H_b!
  let linProd : Finset Idx → Fld[X] := fun s => ∏ i ∈ s, (X - C (BinaryIRSProfile.domain i))
  have hlin_monic : ∀ s : Finset Idx, (linProd s).Monic := fun s =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hlin_ne : ∀ s : Finset Idx, linProd s ≠ 0 := fun s => (hlin_monic s).ne_zero
  have hlin_deg : ∀ s : Finset Idx, (linProd s).natDegree = s.card := fun s => by
    unfold linProd; rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp [natDegree_X_sub_C]
  have hlin_rm : ∀ (s : Finset Idx) (a : AlgebraicClosure Fld),
      ((linProd s).map (algebraMap Fld (AlgebraicClosure Fld))).rootMultiplicity a =
        if ∃ i ∈ s, a = algebraMap Fld (AlgebraicClosure Fld) (BinaryIRSProfile.domain i) then 1 else 0 := by
    intro s a
    let ι : Fld →+* AlgebraicClosure Fld := algebraMap Fld (AlgebraicClosure Fld)
    have hmap : (linProd s).map ι = ∏ i ∈ s, (X - C (ι (BinaryIRSProfile.domain i))) := by
      unfold linProd; rw [Polynomial.map_prod]; apply Finset.prod_congr rfl; intro i _; simp
    rw [hmap]
    split_ifs with h
    · obtain ⟨i, hi, rfl⟩ := h
      rw [← Finset.mul_prod_erase _ _ hi, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _)), rootMultiplicity_X_sub_C, if_pos rfl]
      have h0 : (∏ j ∈ s.erase i, (X - C (ι (BinaryIRSProfile.domain j)))).rootMultiplicity
          (ι (BinaryIRSProfile.domain i)) = 0 := by
        apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
        rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
        obtain ⟨j, hj, hje⟩ := hr
        rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hje
        exact (Finset.mem_erase.mp hj).1 (BinaryIRSProfile.domain.injective (ι.injective hje)).symm
      rw [h0, add_zero]
    · apply rootMultiplicity_eq_zero_iff.mpr; intro hr; exfalso
      rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hr
      obtain ⟨i, hi, hie⟩ := hr
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hie
      exact h ⟨i, hi, hie⟩
  let S0 := linProd I0; let S1U := linProd I1U; let S1noU := linProd I1noU
  let S2U := linProd I2U; let S2noU := linProd I2noU
  let Smis : Fld[X] := S0 * S1noU * S2noU
  let Shit : Fld[X] := S1U * S2U ^ 3
  have hNdom_fac : Ndom = S0 * S1U * S1noU * S2U * S2noU := by
    have hdisj : ∀ s t : Finset Idx, Disjoint s t → linProd (s ∪ t) = linProd s * linProd t :=
      fun s t h => Finset.prod_union h
    have hd1 : Disjoint I0 I1U := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hd2 : Disjoint (I0 ∪ I1U) I1noU := Finset.disjoint_left.mpr fun i h1 h2 => by
      simp only [I0, I1U, I1noU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with h1 | h1
      · omega
      · exact h2.2 h1.2
    have hd3 : Disjoint (I0 ∪ I1U ∪ I1noU) I2U := Finset.disjoint_left.mpr fun i h1 h2 => by
      simp only [I0, I1U, I1noU, I2U, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have hd4 : Disjoint (I0 ∪ I1U ∪ I1noU ∪ I2U) I2noU := Finset.disjoint_left.mpr fun i h1 h2 => by
      simp only [I0, I1U, I1noU, I2U, I2noU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ((h1 | h1) | h1) | h1 <;> first | omega | exact h2.2 h1.2
    have huniv : I0 ∪ I1U ∪ I1noU ∪ I2U ∪ I2noU = Finset.univ := by
      ext i; simp only [I0, I1U, I1noU, I2U, I2noU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_cases h0 : D.k i = 0
      · left; left; left; left; exact h0
      · by_cases h1 : D.k i = 1
        · by_cases hU : S.isU0 i
          · left; left; left; right; exact ⟨h1, hU⟩
          · left; left; right; exact ⟨h1, hU⟩
        · by_cases hU : S.isU0 i
          · left; right; exact ⟨by omega, hU⟩
          · right; exact ⟨by omega, hU⟩
    change linProd Finset.univ = _
    rw [← huniv, hdisj _ _ hd4, hdisj _ _ hd3, hdisj _ _ hd2, hdisj _ _ hd1]
  have hSmis_Shit : Smis * Shit = Ndom * S2U ^ 2 := by
    dsimp [Smis, Shit]; rw [hNdom_fac]; ring
  have hSmis_ne : Smis ≠ 0 := mul_ne_zero (mul_ne_zero (hlin_ne _) (hlin_ne _)) (hlin_ne _)
  have hShit_ne : Shit ≠ 0 := mul_ne_zero (hlin_ne _) (pow_ne_zero 3 (hlin_ne _))
  have hSmis_deg : Smis.natDegree = D.n0 + e1_cnt + e2_cnt := by
    dsimp [Smis]
    rw [natDegree_mul (mul_ne_zero (hlin_ne I0) (hlin_ne I1noU)) (hlin_ne I2noU),
      natDegree_mul (hlin_ne I0) (hlin_ne I1noU), hlin_deg, hlin_deg, hlin_deg, hI0_card]
  have hShit_deg : Shit.natDegree = I1U.card + 3 * I2U.card := by
    dsimp [Shit]; rw [natDegree_mul (hlin_ne _) (pow_ne_zero 3 (hlin_ne _)), natDegree_pow, hlin_deg, hlin_deg]
  -- Shit ∣ H1, so H1 = Shit * R_F!
  have hShit_dvd_H1 : Shit ∣ S.H1 := by
    have hcop_12 : IsCoprime S1U (S2U ^ 3) := by
      apply IsCoprime.pow_right
      dsimp [S1U, S2U, linProd]
      apply IsCoprime.prod_left; intro i hi
      apply IsCoprime.prod_right; intro j hj
      have hne : BinaryIRSProfile.domain j - BinaryIRSProfile.domain i ≠ 0 := by
        apply sub_ne_zero.mpr; intro heq
        have hij := BinaryIRSProfile.domain.injective heq
        subst hij
        simp only [I1U, I2U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega
      refine ⟨C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹,
              -C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹, ?_⟩
      calc C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ * (X - C (BinaryIRSProfile.domain i)) +
              -C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ * (X - C (BinaryIRSProfile.domain j))
          = C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ *
              C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i) := by rw [map_sub]; ring
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h1 : S1U ∣ S.H1 := by
      dsimp [S1U, linProd]
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        have hne : BinaryIRSProfile.domain j - BinaryIRSProfile.domain i ≠ 0 :=
          sub_ne_zero.mpr (fun h => hij (BinaryIRSProfile.domain.injective h.symm))
        exact ⟨C _⁻¹, -C _⁻¹, by rw [show C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ *
          (X - C (BinaryIRSProfile.domain i)) + -C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ *
          (X - C (BinaryIRSProfile.domain j)) = C _⁻¹ * C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i) by
          rw [map_sub]; ring, ← map_mul, inv_mul_cancel₀ hne, map_one]⟩
      · intro i hi
        simp only [I1U, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simpa [hi.1] using S.pow_dvd_H1_of_isU0 i hi.2
    have h2 : S2U ^ 3 ∣ S.H1 := by
      dsimp [S2U, linProd]; rw [← Finset.prod_pow]
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij; apply IsCoprime.pow
        have hne : BinaryIRSProfile.domain j - BinaryIRSProfile.domain i ≠ 0 :=
          sub_ne_zero.mpr (fun h => hij (BinaryIRSProfile.domain.injective h.symm))
        exact ⟨C _⁻¹, -C _⁻¹, by rw [show C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ *
          (X - C (BinaryIRSProfile.domain i)) + -C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i)⁻¹ *
          (X - C (BinaryIRSProfile.domain j)) = C _⁻¹ * C (BinaryIRSProfile.domain j - BinaryIRSProfile.domain i) by
          rw [map_sub]; ring, ← map_mul, inv_mul_cancel₀ hne, map_one]⟩
      · intro i hi
        simp only [I2U, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact (pow_dvd_pow _ (by omega : 3 ≤ 2 * D.k i - 1)).trans (S.pow_dvd_H1_of_isU0 i hi.2)
    exact hcop_12.mul_dvd h1 h2
  rcases hShit_dvd_H1 with ⟨R_F, hRF_def⟩
  have hRF_ne : R_F ≠ 0 := by intro h0; rw [h0, mul_zero] at hRF_def; exact S.H1_ne_zero hRF_def
  have hRF_deg : R_F.natDegree + I1U.card + 3 * I2U.card = S.H1.natDegree := by
    have := congrArg Polynomial.natDegree hRF_def
    rw [natDegree_mul hShit_ne hRF_ne, hShit_deg] at this; omega
  -- Master ODE polynomials Q_raw, F1_raw, G_b, S_b, H_b!
  let Q_raw : Fld[X] := Smis ^ 3 * S1U ^ 2 * D.gj 2
  let F1_raw : Fld[X] := Smis ^ 3 * S1U ^ 2 * S.p.comp (X ^ 2) ^ 4 * D.f1.eval D.P
  have hQ_raw_ne : Q_raw ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmis_ne) (pow_ne_zero 2 (hlin_ne _))) D.g2_ne_zero
  have hF1_raw_ne : F1_raw ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmis_ne) (pow_ne_zero 2 (hlin_ne _)))
      (pow_ne_zero 4 (mt (comp_X_sq_eq_zero_iff _).mp S.hp))) D.f1_eval_P_ne_zero
  have hode_id : R_F * Ndom ^ 3 + F1_raw = Q_raw * S.UP ^ 4 := by
    have hmul := congrArg (· * (Smis ^ 3 * S1U ^ 2)) hb1c1_id
    rw [hRF_def] at hmul
    have hN3 : (Shit * R_F) * (Smis ^ 3 * S1U ^ 2) = R_F * Ndom ^ 3 := by
      dsimp [Shit, Smis]; rw [hNdom_fac]; ring
    dsimp [F1_raw, Q_raw]; linear_combination hmul - hN3
  -- Squarefree decomposition of G_b * R_F = S_b^2 * H_b!
  obtain ⟨c0, c1, L, hc0, hNdom_eq, hNdom_deg, hL4_deg, hNdom_ne, hd1, hd2, hNmult1, hNeval⟩ := Ndom_decomp
  let G_b : Fld[X] := D.gj 2 * Smis
  have hGb_ne : G_b ≠ 0 := mul_ne_zero D.g2_ne_zero hSmis_ne
  obtain ⟨S_b, H_b, hGbRF_eq, hHb_sf⟩ := exists_sq_mul_squarefree (G_b * R_F) (mul_ne_zero hGb_ne hRF_ne)
  have hSb_ne : S_b ≠ 0 := by intro h0; rw [h0, zero_pow (by norm_num), zero_mul] at hGbRF_eq; exact mul_ne_zero hGb_ne hRF_ne hGbRF_eq
  have hHb_ne : H_b ≠ 0 := hHb_sf.ne_zero
  -- Exact Wronskian-Hb identity: S2U^2 * S_b^2 * (C c0 * H_b + Ndom * H_b') = Smis^2 * p(X^2)^5 * M20(X^2)!
  have hHb_wr : S2U ^ 2 * S_b ^ 2 * (C c0 * H_b + Ndom * H_b.derivative) =
      Smis ^ 2 * S.p.comp (X ^ 2) ^ 5 * S.M20.comp (X ^ 2) := by
    have hbase : Ndom * S2U ^ 2 * (S_b ^ 2 * H_b) = Smis ^ 2 * (D.gj 2 * S.H1) := by
      rw [← hGbRF_eq, hRF_def, ← hSmis_Shit]; dsimp [G_b]; ring
    have hd := congrArg Polynomial.derivative hbase
    have hL : (Ndom * S2U ^ 2 * (S_b ^ 2 * H_b)).derivative =
        S2U ^ 2 * S_b ^ 2 * (C c0 * H_b + Ndom * H_b.derivative) := by
      rw [show Ndom * S2U ^ 2 * (S_b ^ 2 * H_b) = (S2U * S_b) ^ 2 * (Ndom * H_b) by ring,
        derivative_mul, char2_derivative_sq, zero_mul, zero_add, derivative_mul, hd1]; ring
    have hR : (Smis ^ 2 * (D.gj 2 * S.H1)).derivative =
        Smis ^ 2 * S.p.comp (X ^ 2) ^ 5 * S.M20.comp (X ^ 2) := by
      rw [derivative_mul, char2_derivative_sq, zero_mul, zero_add, hb1c1_wr]; ring
    rw [hL, hR] at hd; exact hd
  have hHb_rhs_ne : Smis ^ 2 * S.p.comp (X ^ 2) ^ 5 * S.M20.comp (X ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hSmis_ne) (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff _).mp S.hp)))
      (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne)
  have hHb_op_ne : C c0 * H_b + Ndom * H_b.derivative ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hHb_wr; exact hHb_rhs_ne hHb_wr.symm
  -- Exact degree identity from hHb_wr!
  have hHb_deg_id : (C c0 * H_b + Ndom * H_b.derivative).natDegree +
      (D.gj 2).natDegree + S.H1.natDegree =
      H_b.natDegree + N + 10 * S.p.natDegree + 2 * S.M20.natDegree := by
    have h1 := congrArg Polynomial.natDegree hHb_wr
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 (hlin_ne _)) (pow_ne_zero 2 hSb_ne)) hHb_op_ne,
      natDegree_mul (pow_ne_zero 2 (hlin_ne _)) (pow_ne_zero 2 hSb_ne), natDegree_pow, natDegree_pow,
      hlin_deg, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hSmis_ne) (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff _).mp S.hp)))
        (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne),
      natDegree_mul (pow_ne_zero 2 hSmis_ne) (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff _).mp S.hp)),
      natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq, hSmis_deg] at h1
    have h2 := congrArg Polynomial.natDegree hGbRF_eq
    rw [natDegree_mul hGb_ne hRF_ne, natDegree_mul D.g2_ne_zero hSmis_ne, hSmis_deg,
      natDegree_mul (pow_ne_zero 2 hSb_ne) hHb_ne, natDegree_pow] at h2
    have hNsum := D.n_sum_eq_N
    omega
  -- Step 4: Set up finite root set S_fin over E = AlgebraicClosure Fld for pointwise STEP 0B & ODE!
  let E := AlgebraicClosure Fld
  let ι : Fld →+* E := algebraMap Fld E
  let p1 : Fld[X] := S.p / S.D2
  have hp_fac : S.p = S.D2 * p1 := (EuclideanDomain.mul_div_cancel' S.D2_ne_zero S.D2_dvd_p).symm
  have hp1_ne : p1 ≠ 0 := by intro h0; rw [h0, mul_zero] at hp_fac; exact S.hp hp_fac
  have hS_fin_def : ∃ S_fin : Finset E,
      (∀ i : Idx, ι (BinaryIRSProfile.domain i) ∈ S_fin) ∧
      ((D.gj 2).map ι).roots.toFinset ⊆ S_fin ∧
      (R_F.map ι).roots.toFinset ⊆ S_fin ∧
      (S.H1.map ι).roots.toFinset ⊆ S_fin ∧
      (S_b.map ι).roots.toFinset ⊆ S_fin ∧
      (H_b.map ι).roots.toFinset ⊆ S_fin ∧
      (S.D1.map ι).roots.toFinset ⊆ S_fin ∧
      ((S.M20.comp (X ^ 2)).map ι).roots.toFinset ⊆ S_fin ∧
      ((p1.comp (X ^ 2)).map ι).roots.toFinset ⊆ S_fin ∧
      ((S.p.comp (X ^ 2)).map ι).roots.toFinset ⊆ S_fin ∧
      ((D.ResY).map ι).roots.toFinset ⊆ S_fin := by
    refine ⟨Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ∪
        ((D.gj 2).map ι).roots.toFinset ∪ (R_F.map ι).roots.toFinset ∪ (S.H1.map ι).roots.toFinset ∪
        (S_b.map ι).roots.toFinset ∪ (H_b.map ι).roots.toFinset ∪ (S.D1.map ι).roots.toFinset ∪
        ((S.M20.comp (X ^ 2)).map ι).roots.toFinset ∪ ((p1.comp (X ^ 2)).map ι).roots.toFinset ∪
        ((S.p.comp (X ^ 2)).map ι).roots.toFinset ∪ (D.ResY.map ι).roots.toFinset, ?_⟩
    refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; left; left; left; left; left; left; left; left; exact ⟨i, rfl⟩
    all_goals intro a ha; simp [ha]
  obtain ⟨S_fin, hS_dom, hS_g2, hS_RF, hS_H1, hS_Sb, hS_Hb, hS_D1, hS_M20, hS_p1, hS_p, hS_Res⟩ := hS_fin_def
  -- Key helper: D1^5 ∣ H1 implies 2*deg(D1) + (n1 - e1) + 3*(n2 + n3 - e2) ≤ deg(H1)!
  have hD1_H1_row183 : 2 * S.D1.natDegree + I1U.card + 3 * I2U.card ≤ S.H1.natDegree := by
    have hpt : ∀ a ∈ S_fin,
        2 * (S.D1.map ι).rootMultiplicity a +
          ((S1U.map ι).rootMultiplicity a + 3 * (S2U.map ι).rootMultiplicity a) ≤
        (S.H1.map ι).rootMultiplicity a := by
      intro a _
      have hd1 : (S.D1.map ι).rootMultiplicity a ≤ 1 := by
        have := S.D1_rootMultiplicity_le_one
        have hD1sf : Squarefree S.D1 := by
          intro r hr
          have hr2 : (r ^ 2).natDegree = 2 * r.natDegree := natDegree_pow r 2
          have hsq : r ^ 2 ∣ S.D1 := by rw [sq]; exact hr
          rcases hsq with ⟨w, hw⟩
          have hsq2 : (r ^ 2) ^ 2 ∣ S.D2.comp (X ^ 2) := by rw [← S.D1_sq, hw]; exact ⟨w ^ 2, by ring⟩
          have hr_ev : (r ^ 2) = (evenPart (r ^ 2)).comp (X ^ 2) := by
            have hdec := evenPart_add_X_oddPart (r ^ 2)
            have hodd : oddPart (r ^ 2) = 0 := by
              have h1 := congrArg Polynomial.derivative hdec
              rw [derivative_even_odd_char2, char2_derivative_sq] at h1
              exact (comp_X_sq_eq_zero_iff _).mp h1
            rw [hodd, zero_comp, mul_zero, add_zero] at hdec; exact hdec.symm
          have hD2d : (evenPart (r ^ 2)) ^ 2 ∣ S.D2 := by
            rcases hsq2 with ⟨W, hW⟩
            have hW_ev : W = (evenPart W).comp (X ^ 2) := by
              have hdec := evenPart_add_X_oddPart W
              have hodd : oddPart W = 0 := by
                have h1 := congrArg Polynomial.derivative hW
                rw [derivative_comp_X_sq_char2, derivative_mul, char2_derivative_sq, zero_mul, zero_add] at h1
                have hW' : W.derivative = 0 := (mul_eq_zero.mp h1.symm).resolve_left (by
                  intro h0; rw [h0, zero_mul] at hW; exact (mt (comp_X_sq_eq_zero_iff _).mp S.D2_ne_zero) hW)
                have h2 := congrArg Polynomial.derivative hdec
                rw [derivative_even_odd_char2, hW'] at h2
                exact (comp_X_sq_eq_zero_iff _).mp h2
              rw [hodd, zero_comp, mul_zero, add_zero] at hdec; exact hdec.symm
            refine ⟨evenPart W, ?_⟩
            apply sub_eq_zero.mp
            apply (comp_X_sq_eq_zero_iff _).mp
            rw [sub_comp, mul_comp, pow_comp, ← hr_ev, ← hW_ev, hW, sub_self]
          have hu := S.D2_squarefree (evenPart (r ^ 2)) (by rw [← sq]; exact hD2d)
          have h0 : (evenPart (r ^ 2)).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
          have hr0 : r.natDegree = 0 := by
            have := congrArg Polynomial.natDegree hr_ev
            rw [natDegree_pow, natDegree_comp_X_sq, h0] at this; omega
          have hC := Polynomial.eq_C_of_natDegree_eq_zero hr0
          have hrne : r ≠ 0 := by intro h; subst h; simp at hw; exact S.D1_ne_zero hw
          have hc0 : r.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hC; exact hrne hC
          rw [hC]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
        exact rootMultiplicity_map_le_one_of_squarefree hD1sf a
      have h5 : 5 * (S.D1.map ι).rootMultiplicity a ≤ (S.H1.map ι).rootMultiplicity a := by
        rcases S.D1_pow5_dvd_H1 with ⟨w, hw⟩
        have hwE : S.H1.map ι = (S.D1.map ι) ^ 5 * w.map ι := by rw [hw, Polynomial.map_mul, Polynomial.map_pow]
        have hH1E : S.H1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr S.H1_ne_zero
        have hD1E : S.D1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
        have hwne : w.map ι ≠ 0 := fun h0 => hH1E (by rw [hwE, h0, mul_zero])
        rw [hwE, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 5 hD1E) hwne), rootMultiplicity_pow_eq (S.D1.map ι) hD1E 5 a]
        omega
      have hshit_le : (S1U.map ι).rootMultiplicity a + 3 * (S2U.map ι).rootMultiplicity a ≤
          (S.H1.map ι).rootMultiplicity a := by
        have hwE : S.H1.map ι = S1U.map ι * (S2U.map ι) ^ 3 * R_F.map ι := by
          rw [hRF_def]; dsimp [Shit]; simp only [Polynomial.map_mul, Polynomial.map_pow]
        have hS1E : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
        have hS2E : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2U)
        have hRFE : R_F.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hRF_ne
        rw [hwE, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)) hRFE),
          rootMultiplicity_mul (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)),
          rootMultiplicity_pow_eq (S2U.map ι) hS2E 3 a]
        exact Nat.le_add_right _ _
      have h1U : (S1U.map ι).rootMultiplicity a ≤ 1 := by rw [hlin_rm]; split_ifs <;> omega
      have h2U : (S2U.map ι).rootMultiplicity a ≤ 1 := by rw [hlin_rm]; split_ifs <;> omega
      have hdisj : (S1U.map ι).rootMultiplicity a = 0 ∨ (S2U.map ι).rootMultiplicity a = 0 := by
        rw [hlin_rm, hlin_rm]; split_ifs with h1 h2
        · exfalso; rcases h1 with ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, heq⟩
          have hij := BinaryIRSProfile.domain.injective (ι.injective heq); subst hij
          simp only [I1U, I2U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega
        · right; rfl
        · left; rfl
        · left; rfl
      omega
    have hsum := Finset.sum_le_sum hpt
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hS1U_sub : (S1U.map ι).roots.toFinset ⊆ S_fin := fun a ha => by
      have hne1 : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne1] at ha
      have hrm : (S1U.map ι).rootMultiplicity a ≠ 0 := fun h0 => hne1 ((rootMultiplicity_eq_zero_iff.mp h0) ha)
      rw [hlin_rm] at hrm; split_ifs at hrm with h
      · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
      · exact absurd rfl hrm
    have hS2U_sub : (S2U.map ι).roots.toFinset ⊆ S_fin := fun a ha => by
      have hne2 : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2U)
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne2] at ha
      have hrm : (S2U.map ι).rootMultiplicity a ≠ 0 := fun h0 => hne2 ((rootMultiplicity_eq_zero_iff.mp h0) ha)
      rw [hlin_rm] at hrm; split_ifs at hrm with h
      · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
      · exact absurd rfl hrm
    rw [sum_rootMultiplicity_map_eq_natDegree S.D1 S.D1_ne_zero S_fin hS_D1,
      sum_rootMultiplicity_map_eq_natDegree S1U (hlin_ne I1U) S_fin hS1U_sub,
      sum_rootMultiplicity_map_eq_natDegree S2U (hlin_ne I2U) S_fin hS2U_sub,
      sum_rootMultiplicity_map_eq_natDegree S.H1 S.H1_ne_zero S_fin hS_H1,
      hlin_deg, hlin_deg] at hsum
    omega
  -- Step 5: Master `ODE_holds` theorem (proves BOTH `b1Rows` AND row 211/218 when `zRaw c0 c1 R_F Q_raw = 0`)!
  have hODE_holds_bounds : zRaw c0 c1 R_F Q_raw = 0 →
      (2 * ((D.gj 2).natDegree : ℤ) - 2 * (S.H1.natDegree : ℤ) + 2 * (D.n1 : ℤ) + 6 * (D.n2 : ℤ) -
        6 * (D.nt : ℤ) - 2 * (D.n0 : ℤ) - 10 * (e1_cnt : ℤ) - 22 * (e2_cnt : ℤ) - 14 * (erem_cnt : ℤ) ≤ 0) ∧
      (((D.gj 2).natDegree : ℤ) - (S.H1.natDegree : ℤ) + (D.n1 : ℤ) + 3 * (D.n2 : ℤ) - (D.n3 : ℤ) -
        4 * (D.nt : ℤ) - (D.n0 : ℤ) - 5 * (e1_cnt : ℤ) - 8 * (e2_cnt : ℤ) - 3 * (erem_cnt : ℤ) ≤ 0) ∧
      (2 * (I1U.card : ℤ) + 3 * (I2U.card : ℤ) - (erem_cnt : ℤ) ≤ (S.H1.natDegree : ℤ)) := by
    intro hz0
    have hzE : zRaw (ι c0) (ι c1) (R_F.map ι) (Q_raw.map ι) = 0 := by
      have hmap : zRaw (ι c0) (ι c1) (R_F.map ι) (Q_raw.map ι) = (zRaw c0 c1 R_F Q_raw).map ι := by
        unfold zRaw
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
          derivative_map, hasse_map_eq]
      rw [hmap, hz0, Polynomial.map_zero]
    have hRF_E : R_F.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hRF_ne
    have hQ_E : Q_raw.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ_raw_ne
    have hc0E : ι c0 ≠ 0 := mt (fun h => ι.injective (by rw [map_zero]; exact h)) hc0
    -- Local quantities at every a ∈ S_fin!
    let n0_l : E → ℕ := fun a => (S0.map ι).rootMultiplicity a
    let m1_l : E → ℕ := fun a => (S1U.map ι).rootMultiplicity a
    let e1_l : E → ℕ := fun a => (S1noU.map ι).rootMultiplicity a
    let e2_l : E → ℕ := fun a => (S2noU.map ι).rootMultiplicity a
    let k2hit_l : E → ℕ := fun a => (S2U.map ι).rootMultiplicity a
    let nu_l : E → ℕ := fun a => n0_l a + m1_l a + e1_l a + k2hit_l a + e2_l a
    let L_l : E → ℕ := fun a =>
      if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then
        let i := Classical.choose h
        if 3 ≤ D.k i then 2 * (D.k i - 2) else 0
      else 0
    let erem_l : E → ℕ := fun a =>
      (S.M20.map ι).rootMultiplicity (a ^ 2) -
        (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0)
    let d2_l : E → ℕ := fun a => (S.D1.map ι).rootMultiplicity a
    let a1_l : E → ℕ := fun a => (p1.map ι).rootMultiplicity (a ^ 2)
    let g_l : E → ℕ := fun a => (S_b.map ι).rootMultiplicity a
    let b_l : E → ℕ := fun a => (H_b.map ι).rootMultiplicity a
    let rF_l : E → ℕ := fun a => (R_F.map ι).rootMultiplicity a
    let c_l : E → ℕ := fun a => ((D.gj 2).map ι).rootMultiplicity a
    -- Verify all hypotheses of step0B_bound1 & step0B_bound2 & k1U_row at EVERY a ∈ S_fin!
    have hpt_all : ∀ a ∈ S_fin,
        (2 * ((c_l a : ℤ) - (rF_l a : ℤ)) ≤
          2 * (n0_l a : ℤ) + 8 * (e1_l a : ℤ) + 16 * (e2_l a : ℤ) + 14 * (erem_l a : ℤ) + 3 * (L_l a : ℤ)) ∧
        (((c_l a : ℤ) - (rF_l a : ℤ)) ≤
          (n0_l a : ℤ) + 4 * (e1_l a : ℤ) + 5 * (e2_l a : ℤ) + 3 * (erem_l a : ℤ) + 2 * (L_l a : ℤ)) ∧
        (2 * (m1_l a : ℤ) + 3 * (k2hit_l a : ℤ) - (erem_l a : ℤ) ≤ ((S.H1.map ι).rootMultiplicity a : ℤ)) := by
      intro a _
      have hd2_le : d2_l a ≤ 1 := by
        dsimp [d2_l]
        -- D1^2 = D2(X^2) ⇒ D1.rootMultiplicity a = D2.rootMultiplicity (a^2) ≤ 1!
        have hD1_rm : (S.D1.map ι).rootMultiplicity a = (S.D2.map ι).rootMultiplicity (a ^ 2) := by
          have h2 : 2 * (S.D1.map ι).rootMultiplicity a = 2 * (S.D2.map ι).rootMultiplicity (a ^ 2) := by
            have hL : ((S.D1 ^ 2).map ι).rootMultiplicity a = 2 * (S.D1.map ι).rootMultiplicity a := by
              rw [Polynomial.map_pow, sq, rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)
                ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero))]; ring
            have hR : ((S.D2.comp (X ^ 2)).map ι).rootMultiplicity a = 2 * (S.D2.map ι).rootMultiplicity (a ^ 2) := by
              -- Use rootMultiplicity_map_eq if a in Fld, else directly from D2_squarefree!
              have hsq : (X - C a : E[X]) ^ 2 = X ^ 2 - C (a ^ 2) := by
                have h2 : (2 : E[X]) = 0 := CharTwo.two_eq_zero
                simp only [sub_eq_add_neg, CharTwo.neg_eq, map_pow]
                calc (X + C a) ^ 2 = X ^ 2 + 2 * X * C a + C a ^ 2 := by ring
                  _ = X ^ 2 + C a ^ 2 := by rw [h2]; ring
              rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
              have hD2E : S.D2.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D2_ne_zero
              have hD2cE : (S.D2.map ι).comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff _).mp hD2E
              have hd1 : (S.D2.map ι).rootMultiplicity (a ^ 2) ≤ 1 :=
                rootMultiplicity_map_le_one_of_squarefree S.D2_squarefree (a ^ 2)
              have hev : ((S.D2.map ι).comp (X ^ 2)).eval a = (S.D2.map ι).eval (a ^ 2) := by
                simp [eval_comp]
              by_cases h0 : (S.D2.map ι).eval (a ^ 2) = 0
              · have hrm1 : (S.D2.map ι).rootMultiplicity (a ^ 2) = 1 := by
                  have hge1 : 1 ≤ (S.D2.map ι).rootMultiplicity (a ^ 2) :=
                    (le_rootMultiplicity_iff hD2E).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h0)
                  omega
                rw [hrm1, mul_one]
                have hd2 : (X - C a) ^ 2 ∣ (S.D2.map ι).comp (X ^ 2) := by
                  rcases dvd_iff_isRoot.mpr h0 with ⟨q, hq⟩
                  exact ⟨q.comp (X ^ 2), by rw [hq, mul_comp, sub_comp, X_comp, C_comp, hsq]⟩
                have hge2 : 2 ≤ ((S.D2.map ι).comp (X ^ 2)).rootMultiplicity a := (le_rootMultiplicity_iff hD2cE).mpr hd2
                have hle2 : ((S.D2.map ι).comp (X ^ 2)).rootMultiplicity a ≤ 2 := by
                  by_contra h3
                  have hd3 : (X - C a) ^ 3 ∣ (S.D2.map ι).comp (X ^ 2) :=
                    (pow_dvd_pow _ (by omega : 3 ≤ ((S.D2.map ι).comp (X ^ 2)).rootMultiplicity a)).trans
                      (pow_rootMultiplicity_dvd _ a)
                  rcases dvd_iff_isRoot.mpr h0 with ⟨q, hq⟩
                  have hq0 : q.eval (a ^ 2) ≠ 0 := by
                    intro hq0'
                    have hdq : (X - C (a ^ 2)) ^ 2 ∣ S.D2.map ι := by
                      rcases dvd_iff_isRoot.mpr hq0' with ⟨w, hw⟩; exact ⟨w, by rw [hq, hw]; ring⟩
                    have := (le_rootMultiplicity_iff hD2E).mpr hdq; omega
                  have hfac : (S.D2.map ι).comp (X ^ 2) = (X - C a) ^ 2 * q.comp (X ^ 2) := by
                    rw [hq, mul_comp, sub_comp, X_comp, C_comp, hsq]
                  rw [hfac, show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one] at hd3
                  have hdq1 : X - C a ∣ q.comp (X ^ 2) :=
                    (mul_dvd_mul_iff_left (pow_ne_zero 2 (X_sub_C_ne_zero a))).mp hd3
                  exact hq0 (by simpa [IsRoot, eval_comp] using dvd_iff_isRoot.mp hdq1)
                omega
              · have hrm0 : (S.D2.map ι).rootMultiplicity (a ^ 2) = 0 :=
                  rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr h0)
                have hrm0' : ((S.D2.map ι).comp (X ^ 2)).rootMultiplicity a = 0 :=
                  rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd (by rwa [← hev]) h0)
                rw [hrm0, hrm0', mul_zero]
            rw [← hL, ← hR, S.D1_sq]
          omega
        rw [hD1_rm]; exact rootMultiplicity_map_le_one_of_squarefree S.D2_squarefree (a ^ 2)
      have hb_le : b_l a ≤ 1 := rootMultiplicity_map_le_one_of_squarefree hHb_sf a
      have hL_ev : L_l a % 2 = 0 := by dsimp [L_l]; split_ifs <;> omega
      have htot : c_l a + rF_l a + (n0_l a + e1_l a + e2_l a) = 2 * g_l a + b_l a := by
        have hEq := congrArg (fun f : Fld[X] => (f.map ι).rootMultiplicity a) hGbRF_eq
        have hSmisE : Smis.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hSmis_ne
        have hGbE : G_b.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGb_ne
        have hSbE : S_b.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hSb_ne
        have hHbE : H_b.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hHb_ne
        have hS0E : S0.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hS1nE : S1noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hS2nE : S2noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hSmis_rm : (Smis.map ι).rootMultiplicity a = n0_l a + e1_l a + e2_l a := by
          dsimp [Smis, n0_l, e1_l, e2_l]
          rw [Polynomial.map_mul, Polynomial.map_mul,
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS0E hS1nE) hS2nE),
            rootMultiplicity_mul (mul_ne_zero hS0E hS1nE)]
        have hg2E : (D.gj 2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
        simp only [Polynomial.map_mul, Polynomial.map_pow] at hEq
        rw [rootMultiplicity_mul (mul_ne_zero hGbE hRF_E),
          show (G_b.map ι).rootMultiplicity a = c_l a + (Smis.map ι).rootMultiplicity a by
            dsimp [G_b, c_l]; rw [Polynomial.map_mul, rootMultiplicity_mul (mul_ne_zero hg2E hSmisE)],
          hSmis_rm, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSbE) hHbE),
          sq, rootMultiplicity_mul (mul_ne_zero hSbE hSbE)] at hEq
        dsimp [rF_l, g_l, b_l] at hEq ⊢; omega
      have hS_bound : g_l a ≤ (n0_l a + e1_l a + e2_l a) +
          (L_l a + e1_l a + 2 * e2_l a + erem_l a) + 5 * (a1_l a + d2_l a) := by
        -- From hHb_wr: S2U^2 * S_b^2 ∣ Smis^2 * p(X^2)^5 * M20(X^2)!
        have hdvd : (S2U.map ι) ^ 2 * (S_b.map ι) ^ 2 ∣
            (Smis.map ι) ^ 2 * ((S.p.comp (X ^ 2)).map ι) ^ 5 * ((S.M20.comp (X ^ 2)).map ι) :=
          ⟨(C c0 * H_b + Ndom * H_b.derivative).map ι, by
            have := congrArg (Polynomial.map ι) hHb_wr
            simp only [Polynomial.map_mul, Polynomial.map_pow] at this; exact this.symm⟩
        have hRHS_ne : (Smis.map ι) ^ 2 * ((S.p.comp (X ^ 2)).map ι) ^ 5 * ((S.M20.comp (X ^ 2)).map ι) ≠ 0 := by
          have := (Polynomial.map_ne_zero_iff ι.injective).mpr hHb_rhs_ne
          simpa [Polynomial.map_mul, Polynomial.map_pow] using this
        have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hRHS_ne hdvd a
        have hSmisE : Smis.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hSmis_ne
        have hpE : (S.p.comp (X ^ 2)).map ι ≠ 0 :=
          (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp S.hp)
        have hM20E : (S.M20.comp (X ^ 2)).map ι ≠ 0 :=
          (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne)
        have hS2UE : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hSbE : S_b.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hSb_ne
        have hLHS_rm : ((S2U.map ι) ^ 2 * (S_b.map ι) ^ 2).rootMultiplicity a = 2 * k2hit_l a + 2 * g_l a := by
          rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hS2UE) (pow_ne_zero 2 hSbE)),
            sq, sq, rootMultiplicity_mul (mul_ne_zero hS2UE hS2UE), rootMultiplicity_mul (mul_ne_zero hSbE hSbE)]
          dsimp [k2hit_l, g_l]; ring
        have hp_rm : ((S.p.comp (X ^ 2)).map ι).rootMultiplicity a = 2 * (a1_l a + d2_l a) := by
          have hp_comp : S.p.comp (X ^ 2) = S.D1 ^ 2 * p1.comp (X ^ 2) := by
            rw [hp_fac, mul_comp, S.D1_sq]
          have hp1c_rm : ((p1.comp (X ^ 2)).map ι).rootMultiplicity a = 2 * a1_l a :=
            rootMultiplicity_comp_X_sq_map_nonK p1 hp1_ne a
          rw [hp_comp, Polynomial.map_mul, Polynomial.map_pow,
            rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero))
              ((Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp hp1_ne))),
            sq, rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)
              ((Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero)), hp1c_rm]
          dsimp [d2_l]; ring
        have hM20_rm : ((S.M20.comp (X ^ 2)).map ι).rootMultiplicity a = 2 * (S.M20.map ι).rootMultiplicity (a ^ 2) :=
          rootMultiplicity_comp_X_sq_map_nonK S.M20 hM20_ne a
        have hSmis_rm : (Smis.map ι).rootMultiplicity a = n0_l a + e1_l a + e2_l a := by
          dsimp [Smis, n0_l, e1_l, e2_l]
          rw [Polynomial.map_mul, Polynomial.map_mul,
            rootMultiplicity_mul (mul_ne_zero (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I0))
              ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1noU)))
              ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2noU))),
            rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I0))
              ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1noU)))]
        have hRHS_rm : ((Smis.map ι) ^ 2 * ((S.p.comp (X ^ 2)).map ι) ^ 5 * ((S.M20.comp (X ^ 2)).map ι)).rootMultiplicity a =
            2 * (n0_l a + e1_l a + e2_l a) + 10 * (a1_l a + d2_l a) + 2 * (S.M20.map ι).rootMultiplicity (a ^ 2) := by
          rw [rootMultiplicity_mul hRHS_ne, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hSmisE) (pow_ne_zero 5 hpE)),
            sq, rootMultiplicity_mul (mul_ne_zero hSmisE hSmisE), hSmis_rm, hM20_rm,
            rootMultiplicity_pow_eq ((S.p.comp (X ^ 2)).map ι) hpE 5 a, hp_rm]; ring
        rw [hLHS_rm, hRHS_rm] at hle
        -- Compare (S.M20.map ι).rootMultiplicity (a^2) - k2hit_l a with L_l a + e1_l a + 2 * e2_l a + erem_l a!
        have hM20_eq : (S.M20.map ι).rootMultiplicity (a ^ 2) ≤ k2hit_l a + L_l a + e1_l a + 2 * e2_l a + erem_l a := by
          by_cases hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
          · have hi := Classical.choose_spec hdom
            set i := Classical.choose hdom
            have hbase_le : baseM20 i ≤ (S.M20.map ι).rootMultiplicity (a ^ 2) := by
              rw [hi, ← map_pow, rootMultiplicity_map_eq]
              exact (le_rootMultiplicity_iff hM20_ne).mpr (hbaseM20_dvd i)
            have herem_def : erem_l a = (S.M20.map ι).rootMultiplicity (a ^ 2) - baseM20 i := by
              dsimp [erem_l]; rw [dif_pos hdom]
            have hL_def : L_l a = if 3 ≤ D.k i then 2 * (D.k i - 2) else 0 := by
              dsimp [L_l]; rw [dif_pos hdom]
            have hk2h : k2hit_l a = if 2 ≤ D.k i ∧ S.isU0 i then 1 else 0 := by
              dsimp [k2hit_l]; rw [hlin_rm]
              by_cases h2 : 2 ≤ D.k i ∧ S.isU0 i
              · rw [if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, hi⟩, if_pos h2]
              · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I2U, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact h2 hj
            have he1_def : e1_l a = if D.k i = 1 ∧ ¬ S.isU0 i then 1 else 0 := by
              dsimp [e1_l]; rw [hlin_rm]
              by_cases h2 : D.k i = 1 ∧ ¬ S.isU0 i
              · rw [if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, hi⟩, if_pos h2]
              · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I1noU, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact h2 hj
            have he2_def : e2_l a = if 2 ≤ D.k i ∧ ¬ S.isU0 i then 1 else 0 := by
              dsimp [e2_l]; rw [hlin_rm]
              by_cases h2 : 2 ≤ D.k i ∧ ¬ S.isU0 i
              · rw [if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, hi⟩, if_pos h2]
              · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I2noU, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact h2 hj
            rw [herem_def, hL_def, hk2h, he1_def, he2_def]
            dsimp [baseM20] at hbase_le ⊢
            by_cases hU : S.isU0 i <;>
              simp only [hU, not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte] at hbase_le ⊢ <;>
              split_ifs at hbase_le ⊢ <;> omega
          · have herem_def : erem_l a = (S.M20.map ι).rootMultiplicity (a ^ 2) := by
              dsimp [erem_l]; rw [dif_neg hdom, Nat.sub_zero]
            omega
        omega
      -- ODE mod-4 condition at a!
      have hode_raw := ode_mod4_of_zRaw_zero hc0E hRF_E hQ_E hzE a
      have hQ_rm : (Q_raw.map ι).rootMultiplicity a = 3 * (n0_l a + e1_l a + e2_l a) + 2 * m1_l a + c_l a := by
        dsimp [Q_raw, Smis, n0_l, m1_l, e1_l, e2_l, c_l]
        have hS0E : S0.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hS1nE : S1noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hS2nE : S2noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hS1UE : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
        have hg2E : (D.gj 2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
        have hSmE : (S0.map ι * S1noU.map ι * S2noU.map ι) ≠ 0 := mul_ne_zero (mul_ne_zero hS0E hS1nE) hS2nE
        simp only [Polynomial.map_mul, Polynomial.map_pow]
        rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmE) (pow_ne_zero 2 hS1UE)) hg2E),
          rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 3 hSmE) (pow_ne_zero 2 hS1UE)),
          show ((S0.map ι * S1noU.map ι * S2noU.map ι) ^ 3).rootMultiplicity a =
              3 * (S0.map ι * S1noU.map ι * S2noU.map ι).rootMultiplicity a by
            rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, pow_add, pow_add, pow_one,
              rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hSmE hSmE) hSmE),
              rootMultiplicity_mul (mul_ne_zero hSmE hSmE)]; ring,
          rootMultiplicity_mul hSmE, rootMultiplicity_mul (mul_ne_zero hS0E hS1nE),
          sq, rootMultiplicity_mul (mul_ne_zero hS1UE hS1UE)]
        ring
      rw [hQ_rm] at hode_raw
      have hode1 : (4 * d2_l a + 3 * (n0_l a + e1_l a + e2_l a) + 2 * m1_l a + c_l a - rF_l a) % 4 ≠ 1 := by
        dsimp [rF_l] at hode_raw ⊢; omega
      -- Now split on whether a is a domain point or non-domain point to verify hpt, hrF, hirr_a1, hk1_c0, htri!
      have hpt_cases :
          (n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0 ∧ nu_l a = 0 ∧ L_l a = 0) ∨
          (n0_l a = 1 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0 ∧ nu_l a = 1 ∧ L_l a = 0) ∨
          (n0_l a = 0 ∧ m1_l a = 1 ∧ e1_l a = 0 ∧ e2_l a = 0 ∧ nu_l a = 1 ∧ L_l a = 0) ∨
          (n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 1 ∧ e2_l a = 0 ∧ nu_l a = 1 ∧ L_l a = 0) ∨
          (n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0 ∧ nu_l a = 1) ∨
          (n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 1 ∧ nu_l a = 1) := by
        by_cases hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
        · have hi := Classical.choose_spec hdom
          set i := Classical.choose hdom
          have hmem_rm : ∀ s : Finset Idx, ((linProd s).map ι).rootMultiplicity a = if i ∈ s then 1 else 0 := fun s => by
            rw [hlin_rm]
            by_cases h2 : i ∈ s
            · rw [if_pos ⟨i, h2, hi⟩, if_pos h2]
            · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
              have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this; exact h2 hj
          have hn0 : n0_l a = if D.k i = 0 then 1 else 0 := by dsimp [n0_l, S0]; rw [hmem_rm]; simp [I0]
          have hm1 : m1_l a = if D.k i = 1 ∧ S.isU0 i then 1 else 0 := by dsimp [m1_l, S1U]; rw [hmem_rm]; simp [I1U]
          have he1 : e1_l a = if D.k i = 1 ∧ ¬ S.isU0 i then 1 else 0 := by dsimp [e1_l, S1noU]; rw [hmem_rm]; simp [I1noU]
          have hk2 : k2hit_l a = if 2 ≤ D.k i ∧ S.isU0 i then 1 else 0 := by dsimp [k2hit_l, S2U]; rw [hmem_rm]; simp [I2U]
          have he2 : e2_l a = if 2 ≤ D.k i ∧ ¬ S.isU0 i then 1 else 0 := by dsimp [e2_l, S2noU]; rw [hmem_rm]; simp [I2noU]
          have hL : L_l a = if 3 ≤ D.k i then 2 * (D.k i - 2) else 0 := by dsimp [L_l]; rw [dif_pos hdom]
          by_cases hk0 : D.k i = 0
          · right; left; dsimp [nu_l]; rw [hn0, hm1, he1, hk2, he2, hL]; simp [hk0]
          · by_cases hk1 : D.k i = 1
            · by_cases hU : S.isU0 i
              · right; right; left; dsimp [nu_l]; rw [hn0, hm1, he1, hk2, he2, hL]; simp [hk1, hU]
              · right; right; right; left; dsimp [nu_l]; rw [hn0, hm1, he1, hk2, he2, hL]; simp [hk1, hU]
            · by_cases hU : S.isU0 i
              · right; right; right; right; left; dsimp [nu_l]; rw [hn0, hm1, he1, hk2, he2]
                simp [show 2 ≤ D.k i by omega, show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, hU]
              · right; right; right; right; right; dsimp [nu_l]; rw [hn0, hm1, he1, hk2, he2]
                simp [show 2 ≤ D.k i by omega, show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, hU]
        · left
          have hzero : ∀ s : Finset Idx, ((linProd s).map ι).rootMultiplicity a = 0 := fun s => by
            rw [hlin_rm, if_neg (fun ⟨i, _, hi⟩ => hdom ⟨i, hi⟩)]
          dsimp [nu_l, n0_l, m1_l, e1_l, k2hit_l, e2_l, L_l, S0, S1U, S1noU, S2U, S2noU]
          rw [hzero, hzero, hzero, hzero, hzero, dif_neg hdom]; simp
      -- Verify hrF_k2hit, hrF_k2mis, hirr_a1, hk1_c0, htri!
      have hrF_k2hit : nu_l a = 1 → n0_l a = 0 → m1_l a = 0 → e1_l a = 0 → e2_l a = 0 →
          L_l a ≤ rF_l a + 8 * erem_l a := by
        intro hnu hn0 hm1 he1 he2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h
          have : nu_l a = 0 := by
            dsimp [nu_l, n0_l, m1_l, e1_l, k2hit_l, e2_l, S0, S1U, S1noU, S2U, S2noU]
            repeat rw [hlin_rm, if_neg (fun ⟨i, _, hi⟩ => h ⟨i, hi⟩)]
          omega
        have hi := Classical.choose_spec hdom
        set i := Classical.choose hdom
        have hk2U : 2 ≤ D.k i ∧ S.isU0 i := by
          have hk21 : k2hit_l a = 1 := by dsimp [nu_l] at hnu; omega
          dsimp [k2hit_l] at hk21; rw [hlin_rm] at hk21; split_ifs at hk21 with h
          rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
          have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
          exact (Finset.mem_filter.mp hj).2
        have hH1_ge : 2 * D.k i - 1 ≤ (S.H1.map ι).rootMultiplicity a := by
          rw [hi, rootMultiplicity_map_eq]; exact (le_rootMultiplicity_iff S.H1_ne_zero).mpr (S.pow_dvd_H1_of_isU0 i hk2U.2)
        have hH1_eq_rF : (S.H1.map ι).rootMultiplicity a = 3 + rF_l a := by
          have hwE : S.H1.map ι = S1U.map ι * (S2U.map ι) ^ 3 * R_F.map ι := by
            rw [hRF_def]; dsimp [Shit]; simp only [Polynomial.map_mul, Polynomial.map_pow]
          have hS1E : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
          have hS2E : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
          rw [hwE, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)) hRF_E),
            rootMultiplicity_mul (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)),
            rootMultiplicity_pow_eq (S2U.map ι) hS2E 3 a]
          change m1_l a + 3 * k2hit_l a + rF_l a = 3 + rF_l a
          have : k2hit_l a = 1 := by dsimp [nu_l] at hnu; omega
          omega
        have hL_def : L_l a = if 3 ≤ D.k i then 2 * (D.k i - 2) else 0 := by dsimp [L_l]; rw [dif_pos hdom]
        rw [hL_def]; split_ifs <;> omega
      have hrF_k2mis : e2_l a = 1 → L_l a ≤ rF_l a + 5 + 8 * erem_l a := by
        intro he2
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          dsimp [e2_l] at he2; rw [hlin_rm] at he2; split_ifs at he2 with h
          rcases h with ⟨i, _, hi⟩; exact ⟨i, hi⟩
        have hi := Classical.choose_spec hdom
        set i := Classical.choose hdom
        have hk2nU : 2 ≤ D.k i ∧ ¬ S.isU0 i := by
          dsimp [e2_l] at he2; rw [hlin_rm] at he2; split_ifs at he2 with h
          rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
          have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
          exact (Finset.mem_filter.mp hj).2
        have hL_def : L_l a = if 3 ≤ D.k i then 2 * (D.k i - 2) else 0 := by dsimp [L_l]; rw [dif_pos hdom]
        rw [hL_def]
        by_cases hk3 : 3 ≤ D.k i
        · rw [if_pos hk3]
          have hRes_ge : 34 + 18 * (D.k i - 3) ≤ D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) := by
            have := (le_rootMultiplicity_iff D.ResY_ne_zero).mpr (S.pow_dvd_ResY_U1 i hk2nU.2)
            unfold KerD45Data.resOrdU1 at this
            simpa [show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, show D.k i ≠ 2 by omega] using this
          have hRes_fac : D.ResY.rootMultiplicity (BinaryIRSProfile.domain i) =
              S.H1.rootMultiplicity (BinaryIRSProfile.domain i) +
              8 * S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
            rw [hResY_eq, rootMultiplicity_mul (by rw [← hResY_eq]; exact D.ResY_ne_zero)]
            have hMne := mt (comp_X_sq_eq_zero_iff _).mp hM20_ne
            rw [rootMultiplicity_pow_eq (S.M20.comp (X ^ 2)) hMne 4 _, rootMultiplicity_comp_X_sq S.M20 hM20_ne]; ring
          have hH1_eq_rF : S.H1.rootMultiplicity (BinaryIRSProfile.domain i) = rF_l a := by
            rw [← rootMultiplicity_map_eq, ← hi]
            have hwE : S.H1.map ι = S1U.map ι * (S2U.map ι) ^ 3 * R_F.map ι := by
              rw [hRF_def]; dsimp [Shit]; simp only [Polynomial.map_mul, Polynomial.map_pow]
            have hS1E : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
            have hS2E : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
            rw [hwE, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)) hRF_E),
              rootMultiplicity_mul (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)),
              rootMultiplicity_pow_eq (S2U.map ι) hS2E 3 a]
            change m1_l a + 3 * k2hit_l a + rF_l a = rF_l a
            have hm0 : m1_l a = 0 := by rcases hpt_cases with h | h | h | h | h | h <;> omega
            have hk0 : k2hit_l a = 0 := by rcases hpt_cases with h | h | h | h | h | h <;> dsimp [nu_l] at h <;> omega
            omega
          have hM20_eq : S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) = (2 * D.k i - 2) + erem_l a := by
            have h1 : (S.M20.map ι).rootMultiplicity (a ^ 2) = S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
              rw [hi, ← map_pow, rootMultiplicity_map_eq]
            have hbase : baseM20 i = 2 * D.k i - 2 := by
              dsimp [baseM20]; simp [show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, hk2nU.2]
            have hbase_le : baseM20 i ≤ S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) :=
              (le_rootMultiplicity_iff hM20_ne).mpr (hbaseM20_dvd i)
            have herem_def : erem_l a = (S.M20.map ι).rootMultiplicity (a ^ 2) - baseM20 i := by
              dsimp [erem_l]; rw [dif_pos hdom]
            rw [h1, hbase] at herem_def; rw [hbase] at hbase_le; omega
          omega
        · rw [if_neg hk3]; omega
      have hirr_a1 : (m1_l a = 1 ∨ (nu_l a = 1 ∧ n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0)) →
          d2_l a = 0 → a1_l a = 0 := by
        intro hUcase hd20
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          by_contra h
          have : m1_l a = 0 ∧ nu_l a = 0 := by
            rcases hpt_cases with h' | h' | h' | h' | h' | h'
            · exact ⟨h'.2.1, h'.2.2.2.2.1⟩
            all_goals
              exfalso; apply h
              have hsum : n0_l a + m1_l a + e1_l a + k2hit_l a + e2_l a = 1 := by dsimp [nu_l] at h'; omega
              have hzero : ∀ s : Finset Idx, ((linProd s).map ι).rootMultiplicity a = 0 := fun s => by
                rw [hlin_rm, if_neg (fun ⟨i, _, hi⟩ => h ⟨i, hi⟩)]
              dsimp [n0_l, m1_l, e1_l, k2hit_l, e2_l, S0, S1U, S1noU, S2U, S2noU] at hsum
              repeat rw [hzero] at hsum
              omega
          rcases hUcase with h1 | h2 <;> omega
        have hi := Classical.choose_spec hdom
        set i := Classical.choose hdom
        have hU0 : S.isU0 i := by
          rcases hUcase with hm1 | h2
          · dsimp [m1_l] at hm1; rw [hlin_rm] at hm1; split_ifs at hm1 with h
            rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
            have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            exact (Finset.mem_filter.mp hj).2.2
          · have hk2 : k2hit_l a = 1 := by dsimp [nu_l] at h2; omega
            dsimp [k2hit_l] at hk2; rw [hlin_rm] at hk2; split_ifs at hk2 with h
            rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
            have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            exact (Finset.mem_filter.mp hj).2.2
        have hp_ne : S.p.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          intro hp0
          have hD20 : S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 := (S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hU0⟩
          have hD10 : S.D1.eval (BinaryIRSProfile.domain i) = 0 := (sqrtPoly_eval_eq_zero_iff S.D2 _).mpr hD20
          have h1 : 1 ≤ d2_l a := by
            dsimp [d2_l]; rw [hi, rootMultiplicity_map_eq]
            exact (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hD10)
          omega
        have hp1_ne_ev : p1.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          intro h0; apply hp_ne; rw [hp_fac, eval_mul, h0, mul_zero]
        dsimp [a1_l]; rw [hi, ← map_pow, rootMultiplicity_map_eq]
        exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hp1_ne_ev)
      have hk1_c0 : m1_l a = 1 → d2_l a = 0 → erem_l a = 0 → c_l a = 0 := by
        intro hm1 hd20 herem0
        have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
          dsimp [m1_l] at hm1; rw [hlin_rm] at hm1; split_ifs at hm1 with h
          rcases h with ⟨i, _, hi⟩; exact ⟨i, hi⟩
        have hi := Classical.choose_spec hdom
        set i := Classical.choose hdom
        have hk1U : D.k i = 1 ∧ S.isU0 i := by
          dsimp [m1_l] at hm1; rw [hlin_rm] at hm1; split_ifs at hm1 with h
          rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
          have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
          exact (Finset.mem_filter.mp hj).2
        have hp_ne : S.p.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          intro hp0
          have hD20 := (S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hk1U.2⟩
          have hD10 := (sqrtPoly_eval_eq_zero_iff S.D2 _).mpr hD20
          have h1 : 1 ≤ d2_l a := by
            dsimp [d2_l]; rw [hi, rootMultiplicity_map_eq]
            exact (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hD10)
          omega
        have hM20_ev_ne : S.M20.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
          intro h0
          have h1 : 1 ≤ (S.M20.map ι).rootMultiplicity (a ^ 2) := by
            rw [hi, ← map_pow, rootMultiplicity_map_eq]
            exact (le_rootMultiplicity_iff hM20_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h0)
          have hb0 : baseM20 i = 0 := by dsimp [baseM20]; simp [hk1U.1, hk1U.2]
          dsimp [erem_l] at herem0; rw [dif_pos hdom, hb0, Nat.sub_zero] at herem0; omega
        -- Evaluate p * M20 = A1sh 2 * Bsh 0 + A1sh 0 * Bsh 2 at t_i = x_i^2!
        set x0 := BinaryIRSProfile.domain i
        set y0 := D.y i
        set t0 := x0 ^ 2
        have hA10 : (D.A1sh x0 y0 0).eval t0 = 0 := by
          have hd := (D.local_shifted_ords i 0).2.1
          rw [hk1U.1, Fin.val_zero, Nat.sub_zero, pow_one] at hd
          exact dvd_iff_isRoot.mp hd
        have hpM20_id : S.p * S.M20 = D.A1sh x0 y0 2 * D.Bsh y0 0 + D.A1sh x0 y0 0 * D.Bsh y0 2 := by
          have h := (S.shifted_minor_identities x0 y0).2.1.1
          unfold KerD45Syzygy.M20sh at h; rw [hM21, mul_zero, add_zero] at h; exact h
        have hA12_ne : (D.A1sh x0 y0 2).eval t0 ≠ 0 := by
          intro h0
          have hev := congrArg (Polynomial.eval t0) hpM20_id
          rw [eval_mul, eval_add, eval_mul, eval_mul, h0, zero_mul, hA10, zero_mul, add_zero] at hev
          exact mul_ne_zero hp_ne hM20_ev_ne hev
        have hg2_ne_ev : (D.gj 2).eval x0 ≠ 0 := by
          have hg2_sh : D.gj 2 = (D.A1sh x0 y0 2).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 2).comp (X ^ 2) := by
            simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_two, add_comp, mul_comp, C_comp,
              sub_eq_add_neg, CharTwo.neg_eq]
            have hz := CharTwo.add_self_eq_zero (C x0 * (D.Bj 2).comp (X ^ 2))
            linear_combination -hz
          rw [hg2_sh, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
            eval_comp, eval_pow, eval_X]
          exact hA12_ne
        dsimp [c_l]; rw [hi, rootMultiplicity_map_eq]
        exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hg2_ne_ev)
      have htri : 1 ≤ a1_l a ∨ 1 ≤ d2_l a →
          let m0 := n0_l a + e1_l a + e2_l a
          let vc0 :=
            if nu_l a = 1 ∧ ((n0_l a = 0 ∧ m1_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0) ∨ e2_l a = 1) then min (c_l a) (L_l a + 3)
            else if m1_l a = 1 ∨ e1_l a = 1 then min (c_l a) 1
            else 0
          let t1 := 8 * a1_l a + 8 * d2_l a + 3 * m0 + 2 * m1_l a + vc0
          let t3 := 3 * nu_l a + rF_l a
          let t4 := 4 * d2_l a + 3 * m0 + 2 * m1_l a + c_l a
          t4 > t3 → t1 ≤ t3 := by
        intro _ m0 vc0 t1 t3 t4 hgt
        -- From hode_id: R_F * Ndom^3 + F1_raw = Q_raw * UP^4!
        have hF1_eq : F1_raw.map ι = Q_raw.map ι * (S.UP.map ι) ^ 4 + R_F.map ι * (Ndom.map ι) ^ 3 := by
          have hidE := congrArg (Polynomial.map ι) hode_id
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at hidE
          have hadd := congrArg (· + R_F.map ι * (Ndom.map ι) ^ 3) hidE
          have hz := CharTwo.add_self_eq_zero (R_F.map ι * (Ndom.map ι) ^ 3)
          linear_combination hadd - hz
        have hQUP_ge : t4 ≤ (Q_raw.map ι * (S.UP.map ι) ^ 4).rootMultiplicity a := by
          have hUPE : S.UP.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr S.UP_ne_zero
          rw [rootMultiplicity_mul (mul_ne_zero hQ_E (pow_ne_zero 4 hUPE)), hQ_rm]
          have hD1_UP : 4 * d2_l a ≤ ((S.UP.map ι) ^ 4).rootMultiplicity a := by
            rcases S.D1_dvd_UP with ⟨w, hw⟩
            have hd : (S.D1.map ι) ^ 4 ∣ (S.UP.map ι) ^ 4 :=
              ⟨(w.map ι) ^ 4, by rw [hw, Polynomial.map_mul, mul_pow]⟩
            have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd (pow_ne_zero 4 hUPE) hd a
            have h4 : ((S.D1.map ι) ^ 4).rootMultiplicity a = 4 * d2_l a := by
              have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
              exact rootMultiplicity_pow_eq (S.D1.map ι) hD1E 4 a
            omega
          dsimp [t4, m0]; omega
        have hRFN_eq : (R_F.map ι * (Ndom.map ι) ^ 3).rootMultiplicity a = t3 := by
          have hNE : Ndom.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne
          rw [rootMultiplicity_mul (mul_ne_zero hRF_E (pow_ne_zero 3 hNE)),
            rootMultiplicity_pow_eq (Ndom.map ι) hNE 3 a]
          have hN_rm : (Ndom.map ι).rootMultiplicity a = nu_l a := by
            rw [hNdom_fac]
            simp only [Polynomial.map_mul]
            have h0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I0)
            have h1 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
            have h2 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1noU)
            have h3 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2U)
            have h4 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2noU)
            rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4),
                rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3),
                rootMultiplicity_mul (mul_ne_zero (mul_ne_zero h0 h1) h2),
                rootMultiplicity_mul (mul_ne_zero h0 h1)]
          rw [hN_rm]; dsimp [t3, rF_l]; ring
        -- Ultrametric equality: since v(Q*UP^4) ≥ t4 > t3 = v(R_F*Ndom^3), v(F1_raw) = t3!
        have hF1_le : (F1_raw.map ι).rootMultiplicity a ≤ t3 := by
          by_contra hlt
          have ht3_1 : t3 + 1 ≤ (F1_raw.map ι).rootMultiplicity a := by omega
          have hd1 : (X - C a) ^ (t3 + 1) ∣ F1_raw.map ι :=
            (pow_dvd_pow _ ht3_1).trans (pow_rootMultiplicity_dvd _ a)
          have hd2 : (X - C a) ^ (t3 + 1) ∣ Q_raw.map ι * (S.UP.map ι) ^ 4 :=
            (pow_dvd_pow _ (by omega : t3 + 1 ≤ (Q_raw.map ι * (S.UP.map ι) ^ 4).rootMultiplicity a)).trans
              (pow_rootMultiplicity_dvd _ a)
          have hd3 : (X - C a) ^ (t3 + 1) ∣ R_F.map ι * (Ndom.map ι) ^ 3 := by
            have heq : R_F.map ι * (Ndom.map ι) ^ 3 = F1_raw.map ι + Q_raw.map ι * (S.UP.map ι) ^ 4 := by
              rw [hF1_eq, add_comm (Q_raw.map ι * (S.UP.map ι) ^ 4), add_assoc, CharTwo.add_self_eq_zero, add_zero]
            rw [heq]; exact dvd_add hd1 hd2
          have hle := (le_rootMultiplicity_iff (mul_ne_zero hRF_E (pow_ne_zero 3 ((Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne)))).mpr hd3
          omega
        -- Lower bound v(F1_raw) ≥ t1!
        have hF1_ge : t1 ≤ (F1_raw.map ι).rootMultiplicity a := by
          have hSmisE : Smis.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hSmis_ne
          have hS1UE : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
          have hpE : (S.p.comp (X ^ 2)).map ι ≠ 0 :=
            (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp S.hp)
          have hf1E : (D.f1.eval D.P).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr D.f1_eval_P_ne_zero
          have hF1_rm : (F1_raw.map ι).rootMultiplicity a =
              3 * m0 + 2 * m1_l a + 8 * a1_l a + 8 * d2_l a + ((D.f1.eval D.P).map ι).rootMultiplicity a := by
            dsimp [F1_raw]; simp only [Polynomial.map_mul, Polynomial.map_pow]
            rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmisE) (pow_ne_zero 2 hS1UE)) (pow_ne_zero 4 hpE)) hf1E),
              rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmisE) (pow_ne_zero 2 hS1UE)) (pow_ne_zero 4 hpE)),
              rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 3 hSmisE) (pow_ne_zero 2 hS1UE))]
            have h3 : ((Smis.map ι) ^ 3).rootMultiplicity a = 3 * m0 := by
              have hS0E : S0.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
              have hS1nE : S1noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
              have hS2nE : S2noU.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
              rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, pow_add, pow_add, pow_one,
                rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hSmisE hSmisE) hSmisE),
                rootMultiplicity_mul (mul_ne_zero hSmisE hSmisE)]
              have hsm : (Smis.map ι).rootMultiplicity a = m0 := by
                dsimp [Smis, m0, n0_l, e1_l, e2_l]; simp only [Polynomial.map_mul]
                rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS0E hS1nE) hS2nE),
                  rootMultiplicity_mul (mul_ne_zero hS0E hS1nE)]
              rw [hsm]; ring
            have h2 : ((S1U.map ι) ^ 2).rootMultiplicity a = 2 * m1_l a := by
              rw [sq, rootMultiplicity_mul (mul_ne_zero hS1UE hS1UE)]; dsimp [m1_l]; ring
            have h4 : (((S.p.comp (X ^ 2)).map ι) ^ 4).rootMultiplicity a = 8 * a1_l a + 8 * d2_l a := by
              have hp_comp : S.p.comp (X ^ 2) = S.D1 ^ 2 * p1.comp (X ^ 2) := by rw [hp_fac, mul_comp, S.D1_sq]
              have hd : ((S.p.comp (X ^ 2)).map ι).rootMultiplicity a = 2 * (a1_l a + d2_l a) := by
                have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
                have hp1cE := (Polynomial.map_ne_zero_iff ι.injective).mpr (mt (comp_X_sq_eq_zero_iff _).mp hp1_ne)
                rw [hp_comp, Polynomial.map_mul, Polynomial.map_pow,
                  rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hD1E) hp1cE),
                  rootMultiplicity_pow_eq (S.D1.map ι) hD1E 2 a,
                  rootMultiplicity_comp_X_sq_map_nonK p1 hp1_ne a]
                dsimp [a1_l, d2_l]; ring
              rw [rootMultiplicity_pow_eq ((S.p.comp (X ^ 2)).map ι) hpE 4 a, hd]; ring
            rw [h3, h2, h4]; ring
          -- Prove vc0 ≤ ((D.f1.eval D.P).map ι).rootMultiplicity a!
          have hvc0_le : vc0 ≤ ((D.f1.eval D.P).map ι).rootMultiplicity a := by
            dsimp [vc0]
            split_ifs with h1 h2
            · -- k ≥ 2 domain point: f1(X, P) = (g0 + y_i^4 g2) + (P + y_i)^4 g2!
              have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
                by_contra h
                have : nu_l a = 0 := by
                  dsimp [nu_l, n0_l, m1_l, e1_l, k2hit_l, e2_l, S0, S1U, S1noU, S2U, S2noU]
                  repeat rw [hlin_rm, if_neg (fun ⟨i, _, hi⟩ => h ⟨i, hi⟩)]
                omega
              have hi := Classical.choose_spec hdom
              set i := Classical.choose hdom
              have hk2 : 2 ≤ D.k i := by
                have hk0 : D.k i ≠ 0 := by
                  intro h0; have : n0_l a = 1 := by dsimp [n0_l, S0]; rw [hlin_rm, if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩, hi⟩]
                  rcases h1.2 with h' | he2
                  · omega
                  · rcases hpt_cases with hp | hp | hp | hp | hp | hp <;> omega
                have hk1 : D.k i ≠ 1 := by
                  intro h1'
                  by_cases hU : S.isU0 i
                  · have : m1_l a = 1 := by dsimp [m1_l, S1U]; rw [hlin_rm, if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1', hU⟩, hi⟩]
                    rcases h1.2 with h' | he2
                    · omega
                    · rcases hpt_cases with hp | hp | hp | hp | hp | hp <;> omega
                  · have : e1_l a = 1 := by dsimp [e1_l, S1noU]; rw [hlin_rm, if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1', hU⟩, hi⟩]
                    rcases h1.2 with h' | he2
                    · omega
                    · rcases hpt_cases with hp | hp | hp | hp | hp | hp <;> omega
                omega
              have hL_eq : L_l a + 3 = 2 * D.k i - 1 := by
                dsimp [L_l]; rw [dif_pos hdom]
                change (if 3 ≤ D.k i then 2 * (D.k i - 2) else 0) + 3 = 2 * D.k i - 1
                split_ifs <;> omega
              have hc_eq : c_l a = (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) := by
                dsimp [c_l]; rw [hi, rootMultiplicity_map_eq]
              rw [hc_eq, hL_eq, hi, rootMultiplicity_map_eq]
              have hsplit : D.f1.eval D.P = (D.gj 0 + C (D.y i ^ 4) * D.gj 2) + (D.P + C (D.y i)) ^ 4 * D.gj 2 := by
                rw [hf1_eval_eq, char2_add_pow_four, ← map_pow]
                have hz := CharTwo.add_self_eq_zero (C (D.y i ^ 4) * D.gj 2)
                linear_combination -hz
              have hpart1 : (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣
                  D.gj 0 + C (D.y i ^ 4) * D.gj 2 := by
                have hgsh : D.gj 0 + C (D.y i ^ 4) * D.gj 2 =
                    (D.A1sh (BinaryIRSProfile.domain i) (D.y i) 0).comp (X ^ 2) +
                      (X - C (BinaryIRSProfile.domain i)) * (D.Bsh (D.y i) 0).comp (X ^ 2) := by
                  simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, hCj1, hBj1,
                    mul_zero, add_zero, add_comp, mul_comp, C_comp, sub_eq_add_neg, CharTwo.neg_eq]
                  have hz := CharTwo.add_self_eq_zero (C (BinaryIRSProfile.domain i) *
                    ((D.Bj 0).comp (X ^ 2) + C (D.y i ^ 4) * (D.Bj 2).comp (X ^ 2)))
                  linear_combination -hz
                rw [hgsh]
                have hloc := D.local_shifted_ords i 0
                apply dvd_add
                · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 * (D.k i - 0))).trans
                    ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.1)
                · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 1 + 2 * (D.k i - 1 - 0))).trans
                    (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.2))
              have hpart2 : (X - C (BinaryIRSProfile.domain i)) ^ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) ∣
                  (D.P + C (D.y i)) ^ 4 * D.gj 2 :=
                dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd _ _) _
              refine (le_rootMultiplicity_iff D.f1_eval_P_ne_zero).mpr ?_
              rw [hsplit]
              exact dvd_add ((pow_dvd_pow _ (min_le_right _ _)).trans hpart1)
                ((pow_dvd_pow _ (min_le_left _ _)).trans hpart2)
            · -- k = 1 domain point: min c 1!
              have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
                rcases h2 with hm1 | he1
                · dsimp [m1_l] at hm1; rw [hlin_rm] at hm1; split_ifs at hm1 with h
                  rcases h with ⟨i, _, hi⟩; exact ⟨i, hi⟩
                · dsimp [e1_l] at he1; rw [hlin_rm] at he1; split_ifs at he1 with h
                  rcases h with ⟨i, _, hi⟩; exact ⟨i, hi⟩
              have hi := Classical.choose_spec hdom
              set i := Classical.choose hdom
              have hk1 : D.k i = 1 := by
                rcases h2 with hm1 | he1
                · dsimp [m1_l] at hm1; rw [hlin_rm] at hm1; split_ifs at hm1 with h
                  rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
                  have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                  exact (Finset.mem_filter.mp hj).2.1
                · dsimp [e1_l] at he1; rw [hlin_rm] at he1; split_ifs at he1 with h
                  rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
                  have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                  exact (Finset.mem_filter.mp hj).2.1
              have hc_eq : c_l a = (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) := by
                dsimp [c_l]; rw [hi, rootMultiplicity_map_eq]
              rw [hc_eq, hi, rootMultiplicity_map_eq]
              have hsplit : D.f1.eval D.P = (D.gj 0 + C (D.y i ^ 4) * D.gj 2) + (D.P + C (D.y i)) ^ 4 * D.gj 2 := by
                rw [hf1_eval_eq, char2_add_pow_four, ← map_pow]
                have hz := CharTwo.add_self_eq_zero (C (D.y i ^ 4) * D.gj 2)
                linear_combination -hz
              have hpart1 : (X - C (BinaryIRSProfile.domain i)) ^ 1 ∣ D.gj 0 + C (D.y i ^ 4) * D.gj 2 := by
                have hgsh : D.gj 0 + C (D.y i ^ 4) * D.gj 2 =
                    (D.A1sh (BinaryIRSProfile.domain i) (D.y i) 0).comp (X ^ 2) +
                      (X - C (BinaryIRSProfile.domain i)) * (D.Bsh (D.y i) 0).comp (X ^ 2) := by
                  simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, hCj1, hBj1,
                    mul_zero, add_zero, add_comp, mul_comp, C_comp, sub_eq_add_neg, CharTwo.neg_eq]
                  have hz := CharTwo.add_self_eq_zero (C (BinaryIRSProfile.domain i) *
                    ((D.Bj 0).comp (X ^ 2) + C (D.y i ^ 4) * (D.Bj 2).comp (X ^ 2)))
                  linear_combination -hz
                rw [hgsh]
                have hloc := D.local_shifted_ords i 0
                apply dvd_add
                · exact (pow_dvd_pow _ (by omega : 1 ≤ 2 * (D.k i - 0))).trans
                    ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.1)
                · rw [pow_one]; exact dvd_mul_right _ _
              have hpart2 : (X - C (BinaryIRSProfile.domain i)) ^ (D.gj 2).rootMultiplicity (BinaryIRSProfile.domain i) ∣
                  (D.P + C (D.y i)) ^ 4 * D.gj 2 :=
                dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd _ _) _
              refine (le_rootMultiplicity_iff D.f1_eval_P_ne_zero).mpr ?_
              rw [hsplit]
              exact dvd_add ((pow_dvd_pow _ (min_le_right _ _)).trans hpart1)
                ((pow_dvd_pow _ (min_le_left _ _)).trans hpart2)
            · omega
          rw [hF1_rm]; dsimp [t1]; omega
        omega
      -- Call step0B_bound1 and step0B_bound2!
      have hb1 := step0B_bound1 (n0_l a) (m1_l a) (e1_l a) (e2_l a) (erem_l a) (d2_l a) (L_l a)
        (nu_l a) (a1_l a) (g_l a) (b_l a) (rF_l a) (c_l a) hL_ev
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        hd2_le (by rcases hpt_cases with h | h | h | h | h | h <;> omega) hb_le
        hpt_cases hS_bound htot hrF_k2hit hrF_k2mis hirr_a1 hk1_c0 hode1 htri
      have hb2 := step0B_bound2 (n0_l a) (m1_l a) (e1_l a) (e2_l a) (erem_l a) (d2_l a) (L_l a)
        (nu_l a) (a1_l a) (g_l a) (b_l a) (rF_l a) (c_l a) hL_ev
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        (by rcases hpt_cases with h | h | h | h | h | h <;> omega)
        hd2_le (by rcases hpt_cases with h | h | h | h | h | h <;> omega) hb_le
        hpt_cases hS_bound htot hrF_k2hit hrF_k2mis hirr_a1 hk1_c0 hode1 htri
      -- Also prove local bound for row 211/218: 2 m1 + 3 k2hit - erem ≤ v_a(H1)!
      have hrow211 : 2 * (m1_l a : ℤ) + 3 * (k2hit_l a : ℤ) - (erem_l a : ℤ) ≤ ((S.H1.map ι).rootMultiplicity a : ℤ) := by
        have hH1_rm : (S.H1.map ι).rootMultiplicity a = m1_l a + 3 * k2hit_l a + rF_l a := by
          have hwE : S.H1.map ι = S1U.map ι * (S2U.map ι) ^ 3 * R_F.map ι := by
            rw [hRF_def]; dsimp [Shit]; simp only [Polynomial.map_mul, Polynomial.map_pow]
          have hS1E : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
          have hS2E : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)
          rw [hwE, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)) hRF_E),
            rootMultiplicity_mul (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)),
            rootMultiplicity_pow_eq (S2U.map ι) hS2E 3 a]
        rw [hH1_rm]
        by_cases hm1 : m1_l a = 1
        · by_cases hd2 : d2_l a = 1
          · -- D1^5 ∣ H1 ⇒ v_a(H1) ≥ 5!
            have h5 : 5 ≤ (S.H1.map ι).rootMultiplicity a := by
              rcases S.D1_pow5_dvd_H1 with ⟨w, hw⟩
              have hd : (S.D1.map ι) ^ 5 ∣ S.H1.map ι := ⟨w.map ι, by rw [hw, Polynomial.map_mul, Polynomial.map_pow]⟩
              have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd ((Polynomial.map_ne_zero_iff ι.injective).mpr S.H1_ne_zero) hd a
              have hD1E := (Polynomial.map_ne_zero_iff ι.injective).mpr S.D1_ne_zero
              have hpow : ((S.D1.map ι) ^ 5).rootMultiplicity a = 5 * d2_l a :=
                rootMultiplicity_pow_eq (S.D1.map ι) hD1E 5 a
              omega
            have hk0 : k2hit_l a = 0 := by rcases hpt_cases with h | h | h | h | h | h <;> dsimp [nu_l] at h <;> omega
            rw [hH1_rm] at h5; omega
          · by_cases her : erem_l a = 0
            · have hc0 := hk1_c0 hm1 (by omega) her
              have hm0z : n0_l a = 0 ∧ e1_l a = 0 ∧ e2_l a = 0 := by
                rcases hpt_cases with h | h | h | h | h | h <;> omega
              have hrF_pos : 1 ≤ rF_l a := by
                -- hode_raw: (rF_l a + 3 * (0 + 2 + 0)) % 4 ∈ {0, 1} ⇒ (rF_l a + 6) % 4 ∈ {0, 1} ⇒ rF_l a ≠ 0!
                rw [hm0z.1, hm0z.2.1, hm0z.2.2, hm1, hc0] at hode_raw
                dsimp [rF_l] at hode_raw ⊢; omega
              omega
            · omega
        · have hm0 : m1_l a = 0 := by rcases hpt_cases with h | h | h | h | h | h <;> omega
          omega
      exact ⟨hb1, hb2, hrow211⟩
    -- Sum hpt_all over a ∈ S_fin!
    have hsum_dom : ∀ (s : Finset Idx), ∑ a ∈ S_fin, ((linProd s).map ι).rootMultiplicity a = s.card := fun s => by
      have hsub : ((linProd s).map ι).roots.toFinset ⊆ S_fin := fun a ha => by
        have hne_s : (linProd s).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne s)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne_s] at ha
        have hrm : ((linProd s).map ι).rootMultiplicity a ≠ 0 := fun h0 => hne_s ((rootMultiplicity_eq_zero_iff.mp h0) ha)
        rw [hlin_rm] at hrm; split_ifs at hrm with h
        · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
        · exact absurd rfl hrm
      rw [sum_rootMultiplicity_map_eq_natDegree _ (hlin_ne _) S_fin hsub, hlin_deg]
    have hsum_L : ∑ a ∈ S_fin, L_l a = 2 * D.n3 + 2 * D.nt := by
      have himg : Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ⊆ S_fin := fun a ha => by
        rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; exact hS_dom i
      rw [← Finset.sum_subset himg (fun a _ hna => by
        dsimp [L_l]; rw [dif_neg]; intro ⟨i, hi⟩; apply hna; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)]
      rw [Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
      have hterm : ∀ i : Idx, L_l (ι (BinaryIRSProfile.domain i)) = (if 3 ≤ D.k i then 2 else 0) + 2 * (D.k i - 3) := fun i => by
        dsimp [L_l]; rw [dif_pos ⟨i, rfl⟩]
        have heq : Classical.choose (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
          BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
        rw [heq]; split_ifs <;> omega
      have hgen : ∀ S0 : Finset Idx,
          ∑ i ∈ S0, L_l (ι (BinaryIRSProfile.domain i)) =
            2 * (S0.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S0, (D.k i - 3) := by
        intro S0
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul]; ring
      unfold KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
    have hsum_erem : ∑ a ∈ S_fin, erem_l a = erem_cnt := by
      have hle_pt : ∀ a ∈ S_fin,
          (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) ≤
          (S.M20.map ι).rootMultiplicity (a ^ 2) := fun a _ => by
        split_ifs with h
        · set i := Classical.choose h
          have hi : a = ι (BinaryIRSProfile.domain i) := Classical.choose_spec h
          have h1 : (S.M20.map ι).rootMultiplicity (a ^ 2) = S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
            rw [hi, ← map_pow, rootMultiplicity_map_eq]
          rw [h1]
          exact (le_rootMultiplicity_iff hM20_ne).mpr (hbaseM20_dvd i)
        · exact Nat.zero_le _
      have hadd : (∑ a ∈ S_fin, erem_l a) +
          (∑ a ∈ S_fin, if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) =
          ∑ a ∈ S_fin, (S.M20.map ι).rootMultiplicity (a ^ 2) := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a ha
        have := hle_pt a ha; dsimp [erem_l]; omega
      have hbase_tot : (∑ a ∈ S_fin, if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) =
          D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt := by
        have himg : Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ⊆ S_fin := fun a ha => by
          rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; exact hS_dom i
        rw [← Finset.sum_subset himg (fun a _ hna => by
          rw [dif_neg]; intro ⟨i, hi⟩; apply hna; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)]
        rw [Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
        have hterm : ∀ i : Idx,
            (if h : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j) then baseM20 (Classical.choose h) else 0) =
            baseM20 i := fun i => by
          rw [dif_pos ⟨i, rfl⟩]
          have heq : Classical.choose (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
            BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
          rw [heq]
        simp_rw [hterm]; exact hbaseM20_sum
      rw [hbase_tot, sum_rootMultiplicity_sq_map_eq_natDegree S.M20 hM20_ne S_fin hS_M20] at hadd
      dsimp [erem_cnt]; omega
    have hsum_c : ∑ a ∈ S_fin, c_l a = (D.gj 2).natDegree :=
      sum_rootMultiplicity_map_eq_natDegree (D.gj 2) D.g2_ne_zero S_fin hS_g2
    have hsum_rF : ∑ a ∈ S_fin, rF_l a = R_F.natDegree :=
      sum_rootMultiplicity_map_eq_natDegree R_F hRF_ne S_fin hS_RF
    have hsum_H1 : ∑ a ∈ S_fin, (S.H1.map ι).rootMultiplicity a = S.H1.natDegree :=
      sum_rootMultiplicity_map_eq_natDegree S.H1 S.H1_ne_zero S_fin hS_H1
    have h1 := Finset.sum_le_sum fun a ha => (hpt_all a ha).1
    have h2 := Finset.sum_le_sum fun a ha => (hpt_all a ha).2.1
    have h3 := Finset.sum_le_sum fun a ha => (hpt_all a ha).2.2
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum] at h1 h2 h3
    rw [hsum_c, hsum_rF, hsum_dom I0, hsum_dom I1noU, hsum_dom I2noU, hsum_erem, hsum_L] at h1 h2
    rw [hsum_dom I1U, hsum_dom I2U, hsum_erem, hsum_H1] at h3
    change _ ≤ _ at h1 h2 h3
    rw [hI0_card] at h1 h2
    refine ⟨by omega, by omega, by omega⟩
  -- Step 6: Master `ODE_fail` bound (proves row 214/222 when `zRaw c0 c1 R_F Q_raw ≠ 0`)!
  have hODE_fail_bound : zRaw c0 c1 R_F Q_raw ≠ 0 →
      8 * S.p.natDegree + 3 * D.n2 + 3 * D.n3 ≤
        2 * D.n0 + D.n1 + 4 * e2_cnt + 2 * (D.gj 2).natDegree + S.H1.natDegree := by
    intro hzne
    obtain ⟨Z_ode, hZ_eq⟩ := pow5_mul_sq_dvd_zRaw c0 c1 R_F Smis S1U (D.gj 2)
    have hZ_ne : Z_ode ≠ 0 := by intro h0; rw [h0, mul_zero] at hZ_eq; exact hzne hZ_eq
    have hZ_deg := natDegree_zOde_pow5_le hSmis_ne (hlin_ne _) D.g2_ne_zero hZ_ne hZ_eq
    rw [hSmis_deg, hlin_deg] at hZ_deg
    -- Lower bound Z_ode.natDegree ≥ 4 * (2 * S.p.natDegree) - D.n0 via rootMultiplicity_zOde_ge + δ^4 shift!
    let S_finZ : Finset E := S_fin ∪ (Z_ode.map ι).roots.toFinset
    have hZ_sub : (Z_ode.map ι).roots.toFinset ⊆ S_finZ := Finset.subset_union_right
    have hp_sub : ((S.p.comp (X ^ 2)).map ι).roots.toFinset ⊆ S_finZ :=
      hS_p.trans Finset.subset_union_left
    have hS0_sub : (S0.map ι).roots.toFinset ⊆ S_finZ := by
      have hS0_fin : (S0.map ι).roots.toFinset ⊆ S_fin := fun a ha => by
        have hne0 : S0.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I0)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne0] at ha
        have hrm : (S0.map ι).rootMultiplicity a ≠ 0 := fun h0 => hne0 ((rootMultiplicity_eq_zero_iff.mp h0) ha)
        rw [hlin_rm] at hrm; split_ifs at hrm with h
        · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
        · exact absurd rfl hrm
      exact hS0_fin.trans Finset.subset_union_left
    have hNdom_E : Ndom.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hNdom_ne
    have hd1E : (Ndom.map ι).derivative = C (ι c0) := by rw [derivative_map, hd1, Polynomial.map_C]
    have hd2E : hasse 2 (Ndom.map ι) = C (ι c1) := by
      rw [hasse_map_eq, hd2, Polynomial.map_C]
    have hdivE : zRaw (ι c0) (ι c1) (R_F.map ι) ((Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * (D.gj 2).map ι) =
        (Smis.map ι) ^ 5 * (S1U.map ι) ^ 2 * Z_ode.map ι := by
      rw [show (Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * (D.gj 2).map ι = (Smis ^ 3 * S1U ^ 2 * D.gj 2).map ι by
        simp only [Polynomial.map_mul, Polynomial.map_pow]]
      rw [zRaw_map, hZ_eq]
      simp only [Polynomial.map_mul, Polynomial.map_pow]
    have hptZ : ∀ a ∈ S_finZ,
        4 * ((S.p.comp (X ^ 2)).map ι).rootMultiplicity a ≤
          (Z_ode.map ι).rootMultiplicity a + (S0.map ι).rootMultiplicity a := by
      intro a _
      by_cases hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i)
      · rcases hdom with ⟨i, rfl⟩
        set x0 := BinaryIRSProfile.domain i
        set δ : Fld := D.P.eval x0 + D.y i
        -- Shifted identity: R_F * Ndom^3 + p(X^2)^4 * (Smis^3 * S1U^2 * E_i) = (Smis^3 * S1U^2 * g2) * (UP + C δ * p(X^2))^4!
        let E_i : Fld[X] := D.f1.eval D.P + C (δ ^ 4) * D.gj 2
        let Q0_i : Fld[X] := S.UP + C δ * S.p.comp (X ^ 2)
        have hode_i : R_F * Ndom ^ 3 + S.p.comp (X ^ 2) ^ 4 * (Smis ^ 3 * S1U ^ 2 * E_i) =
            (Smis ^ 3 * S1U ^ 2 * D.gj 2) * Q0_i ^ 4 := by
          have hQ04 : Q0_i ^ 4 = S.UP ^ 4 + C (δ ^ 4) * S.p.comp (X ^ 2) ^ 4 := by
            dsimp [Q0_i]; rw [char2_add_pow_four, mul_pow, ← map_pow]
          rw [hQ04]; dsimp [E_i, F1_raw, Q_raw] at hode_id ⊢
          linear_combination hode_id
        have hode_iE : R_F.map ι * (Ndom.map ι) ^ 3 +
            ((S.p.comp (X ^ 2)).map ι) ^ 4 * ((Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * E_i.map ι) =
            ((Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * (D.gj 2).map ι) * (Q0_i.map ι) ^ 4 := by
          have h := congrArg (Polynomial.map ι) hode_i
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at h
          exact h
        have hrm := (rootMultiplicity_zOde_ge
          ((Polynomial.map_ne_zero_iff ι.injective).mpr hSmis_ne)
          ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))
          ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
          hNdom_E hd1E hd2E hdivE hode_iE (ι x0)).2
          (by rw [rootMultiplicity_map_eq]; exact hNmult1 i)
        -- Evaluate E_i order at x0: E_i = (g0 + y_i^4 g2) + (P + y_i + δ)^4 * g2!
        have hEi_eq : E_i = (D.gj 0 + C (D.y i ^ 4) * D.gj 2) + (D.P + C (D.y i) + C δ) ^ 4 * D.gj 2 := by
          dsimp [E_i]; rw [hf1_eval_eq, char2_add_pow_four, char2_add_pow_four, ← map_pow, ← map_pow]
          have hz := CharTwo.add_self_eq_zero (C (D.y i ^ 4) * D.gj 2)
          linear_combination -hz
        have hEi_dvd : (X - C x0) ^ min (2 * D.k i - 1) (4 + (D.gj 2).rootMultiplicity x0) ∣ E_i := by
          rw [hEi_eq]
          have h1 : (X - C x0) ^ (2 * D.k i - 1) ∣ D.gj 0 + C (D.y i ^ 4) * D.gj 2 := by
            by_cases hk0 : D.k i = 0
            · simp [hk0]
            · have hgsh : D.gj 0 + C (D.y i ^ 4) * D.gj 2 =
                  (D.A1sh x0 (D.y i) 0).comp (X ^ 2) + (X - C x0) * (D.Bsh (D.y i) 0).comp (X ^ 2) := by
                simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, hCj1, hBj1,
                  mul_zero, add_zero, add_comp, mul_comp, C_comp, sub_eq_add_neg, CharTwo.neg_eq]
                have hz := CharTwo.add_self_eq_zero (C x0 * ((D.Bj 0).comp (X ^ 2) + C (D.y i ^ 4) * (D.Bj 2).comp (X ^ 2)))
                linear_combination -hz
              rw [hgsh]; have hloc := D.local_shifted_ords i 0
              apply dvd_add
              · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 * (D.k i - 0))).trans
                  ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.1)
              · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 1 + 2 * (D.k i - 1 - 0))).trans
                  (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.2))
          have h2 : (X - C x0) ^ (4 + (D.gj 2).rootMultiplicity x0) ∣ (D.P + C (D.y i) + C δ) ^ 4 * D.gj 2 := by
            have hlin : X - C x0 ∣ D.P + C (D.y i) + C δ := by
              rw [dvd_iff_isRoot, IsRoot, eval_add, eval_add, eval_C, eval_C]
              dsimp [δ]; exact CharTwo.add_self_eq_zero _
            rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hlin 4) (pow_rootMultiplicity_dvd _ x0)
          exact dvd_add ((pow_dvd_pow _ (min_le_left _ _)).trans h1) ((pow_dvd_pow _ (min_le_right _ _)).trans h2)
        have hEi_ne : E_i ≠ 0 := by
          intro h0
          -- If E_i = 0, then R_F * Ndom^3 = Q_raw * Q0_i^4, hence zRaw R_F Q_raw = 0, contradiction!
          rw [h0, mul_zero, mul_zero, add_zero] at hode_i
          have hz0 := zRaw_ode_fail_identity (E := Fld) hd1 hd2
            (show R_F * Ndom ^ 3 + 1 ^ 4 * (0 : Fld[X]) = Q_raw * Q0_i ^ 4 by simpa [Q_raw] using hode_i)
          have hzr0 : zRaw c0 c1 (0 : Fld[X]) (Q_raw * Ndom ^ 3) = 0 := by
            unfold zRaw; simp [hasse]
          rw [hzr0, mul_zero] at hz0
          exact hzne ((mul_eq_zero.mp hz0).resolve_left (pow_ne_zero 9 hNdom_ne))
        have hEi_rm : min (2 * D.k i - 1) (4 + (D.gj 2).rootMultiplicity x0) ≤ (E_i.map ι).rootMultiplicity (ι x0) := by
          rw [rootMultiplicity_map_eq]; exact (le_rootMultiplicity_iff hEi_ne).mpr hEi_dvd
        have hg2_rm : ((D.gj 2).map ι).rootMultiplicity (ι x0) = (D.gj 2).rootMultiplicity x0 :=
          rootMultiplicity_map_eq _ _
        have hSmis_rm : (Smis.map ι).rootMultiplicity (ι x0) =
            (if D.k i = 0 then 1 else 0) + (if D.k i = 1 ∧ ¬ S.isU0 i then 1 else 0) +
            (if 2 ≤ D.k i ∧ ¬ S.isU0 i then 1 else 0) := by
          dsimp [Smis]; simp only [Polynomial.map_mul]
          rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))
            ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))) ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))),
            rootMultiplicity_mul (mul_ne_zero ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))
              ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _)))]
          have hmem : ∀ s : Finset Idx, ((linProd s).map ι).rootMultiplicity (ι x0) = if i ∈ s then 1 else 0 := fun s => by
            rw [hlin_rm]
            by_cases h2 : i ∈ s
            · rw [if_pos ⟨i, h2, rfl⟩, if_pos h2]
            · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this; exact h2 hj
          rw [hmem, hmem, hmem]; simp [I0, I1noU, I2noU]
        have hS1U_rm : (S1U.map ι).rootMultiplicity (ι x0) = if D.k i = 1 ∧ S.isU0 i then 1 else 0 := by
          rw [hlin_rm]
          by_cases h2 : D.k i = 1 ∧ S.isU0 i
          · rw [if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, rfl⟩, if_pos h2]
          · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            exact h2 (Finset.mem_filter.mp hj).2
        have hS0_rm : (S0.map ι).rootMultiplicity (ι x0) = if D.k i = 0 then 1 else 0 := by
          rw [hlin_rm]
          by_cases h2 : D.k i = 0
          · rw [if_pos ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, rfl⟩, if_pos h2]
          · rw [if_neg h2, if_neg]; rintro ⟨j, hj, heq⟩; have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            exact h2 (Finset.mem_filter.mp hj).2
        rw [hSmis_rm, hS1U_rm, hg2_rm] at hrm
        rw [hS0_rm]
        by_cases hk0 : D.k i = 0
        · simp [hk0] at hrm ⊢; omega
        · by_cases hk1 : D.k i = 1
          · by_cases hU : S.isU0 i
            · simp [hk1, hU] at hrm hEi_rm ⊢; omega
            · simp [hk1, hU] at hrm hEi_rm ⊢; omega
          · by_cases hU : S.isU0 i
            · by_cases hs0 : (D.gj 2).rootMultiplicity x0 = 0
              · -- g2(x0) ≠ 0 ⇒ D1(x0) ≠ 0 ⇒ D2(x0^2) ≠ 0 ⇒ (since U = 0) p(x0^2) ≠ 0!
                have hp_ne : S.p.eval (x0 ^ 2) ≠ 0 := by
                  intro hp0
                  have hD20 := (S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hU⟩
                  have hD10 := (sqrtPoly_eval_eq_zero_iff S.D2 x0).mpr hD20
                  have hg20 : (D.gj 2).eval x0 = 0 := by
                    rcases S.D1_dvd_gj 2 with ⟨w, hw⟩
                    rw [hw, eval_mul]; unfold KerD45Syzygy.D1; rw [hD10, zero_mul]
                  have hge1 : 1 ≤ (D.gj 2).rootMultiplicity x0 :=
                    (le_rootMultiplicity_iff D.g2_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hg20)
                  omega
                have hp0 : ((S.p.comp (X ^ 2)).map ι).rootMultiplicity (ι x0) = 0 := by
                  rw [rootMultiplicity_map_eq, rootMultiplicity_comp_X_sq S.p S.hp,
                    rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hp_ne), mul_zero]
                rw [hp0]; omega
              · simp [show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, hU] at hrm hEi_rm ⊢; omega
            · simp [show D.k i ≠ 0 by omega, show D.k i ≠ 1 by omega, show 2 ≤ D.k i by omega, hU] at hrm hEi_rm ⊢; omega
      · -- Non-domain point: Ndom.map ι eval a ≠ 0!
        have hodeE : R_F.map ι * (Ndom.map ι) ^ 3 +
            ((S.p.comp (X ^ 2)).map ι) ^ 4 * ((Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * (D.f1.eval D.P).map ι) =
            ((Smis.map ι) ^ 3 * (S1U.map ι) ^ 2 * (D.gj 2).map ι) * (S.UP.map ι) ^ 4 := by
          dsimp [F1_raw, Q_raw] at hode_id
          have := congrArg (Polynomial.map ι) hode_id
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] at this
          linear_combination this
        have hrm := (rootMultiplicity_zOde_ge
          ((Polynomial.map_ne_zero_iff ι.injective).mpr hSmis_ne)
          ((Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne _))
          ((Polynomial.map_ne_zero_iff ι.injective).mpr hZ_ne)
          hNdom_E hd1E hd2E hdivE hodeE a).1 (mt (hNeval a).mp hdom)
        omega
    have hsumZ := Finset.sum_le_sum hptZ
    rw [← Finset.mul_sum, Finset.sum_add_distrib,
      sum_rootMultiplicity_map_eq_natDegree (S.p.comp (X ^ 2)) (mt (comp_X_sq_eq_zero_iff _).mp S.hp) S_finZ hp_sub,
      sum_rootMultiplicity_map_eq_natDegree Z_ode hZ_ne S_finZ hZ_sub,
      sum_rootMultiplicity_map_eq_natDegree S0 (hlin_ne I0) S_finZ hS0_sub,
      natDegree_comp_X_sq, hlin_deg, hI0_card] at hsumZ
    omega
  -- Step 7: Pick exact (rGt, r4g4, bCase) and construct x : Fin 21 → ℚ!
  let rGt : Bool := decide (2 * S.p.natDegree + wY < S.R.natDegree)
  let r4g4 : Bool := decide (S.R ≠ 0 ∧ 8 * S.p.natDegree + D.W_F - wY + 1 < 4 * S.R.natDegree + (D.gj 2).natDegree)
  let thr_B1 : Bool := decide (6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N)
  let hb_const : Bool := decide (H_b.derivative = 0)
  let ode_holds : Bool := decide (zRaw c0 c1 R_F Q_raw = 0)
  let d2_holds : Bool :=
    decide (6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + (D.gj 2).natDegree +
      D.W_F - wY + 1 + 8 * S.p.natDegree < 3 * N)
  let bCase : ℕ :=
    if thr_B1 then
      if hb_const then (if d2_holds then 0 else 1)
      else (if ode_holds then 4 else 5)
    else
      (if ode_holds then 2 else 3)
  have hbCase_lt : bCase < 6 := by dsimp [bCase]; split_ifs <;> omega
  refine ⟨rGt, r4g4, bCase, hbCase_lt, ?_⟩
  let x : Fin 21 → ℚ := b1c1Vec D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3
    S.p.natDegree (D.gj 2).natDegree S.M20.natDegree S.R.natDegree S.UP.natDegree
    e1_cnt e2_cnt erem_cnt S.H1.natDegree S.D1.natDegree D.W_F
  refine ⟨x, b1c1Vec_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hBS := D.baseT4Rows_sat (nv := 21) (ic := 20) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hUP_a12 : D.a1 + D.a2 ≤ e1_cnt + e2_cnt + erem_cnt + S.UP.natDegree := by
    have h1 : D.a1 ≤ S.a1U + e1_cnt := by
      have hs1 : S.a1U = (D.Az.filter fun i => D.k i = 1 ∧ S.isU0 i).card := by
        unfold KerD45Syzygy.a1U; congr 1
      have ha1 : D.a1 = (D.Az.filter fun i => D.k i = 1).card := by
        unfold KerD45Data.a1; congr 1
      have hd : Disjoint (D.Az.filter fun i => D.k i = 1 ∧ S.isU0 i)
          (D.Az.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i) := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.2 h1.2
      have hu : (D.Az.filter fun i => D.k i = 1 ∧ S.isU0 i) ∪ (D.Az.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i) =
          D.Az.filter fun i => D.k i = 1 := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hA, hk, _⟩ | ⟨hA, hk, _⟩) <;> exact ⟨hA, hk⟩
        · rintro ⟨hA, hk⟩; by_cases hU : S.isU0 i
          · exact Or.inl ⟨hA, hk, hU⟩
          · exact Or.inr ⟨hA, hk, hU⟩
      have ha1_split : D.a1 = S.a1U + (D.Az.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i).card := by
        rw [ha1, hs1, ← Finset.card_union_of_disjoint hd, hu]
      have hle : (D.Az.filter fun i => D.k i = 1 ∧ ¬ S.isU0 i).card ≤ e1_cnt :=
        Finset.card_le_card fun i hi => by
          simp only [I1noU, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2
      omega
    have h2 : D.a2 ≤ S.a2U + e2_cnt := by
      have hs2 : S.a2U = (D.Az.filter fun i => D.k i = 2 ∧ S.isU0 i).card := by
        unfold KerD45Syzygy.a2U; congr 1
      have ha2 : D.a2 = (D.Az.filter fun i => D.k i = 2).card := by
        unfold KerD45Data.a2; congr 1
      have hd : Disjoint (D.Az.filter fun i => D.k i = 2 ∧ S.isU0 i)
          (D.Az.filter fun i => D.k i = 2 ∧ ¬ S.isU0 i) := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.2 h1.2
      have hu : (D.Az.filter fun i => D.k i = 2 ∧ S.isU0 i) ∪ (D.Az.filter fun i => D.k i = 2 ∧ ¬ S.isU0 i) =
          D.Az.filter fun i => D.k i = 2 := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hA, hk, _⟩ | ⟨hA, hk, _⟩) <;> exact ⟨hA, hk⟩
        · rintro ⟨hA, hk⟩; by_cases hU : S.isU0 i
          · exact Or.inl ⟨hA, hk, hU⟩
          · exact Or.inr ⟨hA, hk, hU⟩
      have ha2_split : D.a2 = S.a2U + (D.Az.filter fun i => D.k i = 2 ∧ ¬ S.isU0 i).card := by
        rw [ha2, hs2, ← Finset.card_union_of_disjoint hd, hu]
      have hle : (D.Az.filter fun i => D.k i = 2 ∧ ¬ S.isU0 i).card ≤ e2_cnt :=
        Finset.card_le_card fun i hi => by
          simp only [I2noU, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact ⟨by omega, hi.2.2⟩
      omega
    have hUP := S.aU_sum_le_UP
    omega
  have hR_2M20 : S.R.natDegree + 2 * S.M20.natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
    by_cases hR0 : S.R = 0
    · rw [hR0, natDegree_zero, zero_add]; have := S.natDegree_p_add_M20_le hM20_ne; omega
    · have h := S.natDegree_R_mul_M20_le
      rw [natDegree_mul hR0 (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne), natDegree_comp_X_sq] at h; exact h
  have hUP_2M20 : S.UP.natDegree + 2 * S.M20.natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
    have h := S.natDegree_UP_mul_M20_le
    rw [natDegree_mul S.UP_ne_zero (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne), natDegree_comp_X_sq] at h; exact h
  have hRes_ord := D.resOrdU0_le_natDegree
  have hH1_fH : ∀ i : Idx, (X - C (BinaryIRSProfile.domain i)) ^ (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i - 5) ∣ S.H1 := by
    intro i; split_ifs with hU
    · exact S.pow_dvd_H1_of_isU0 i hU
    · by_cases hk3 : 3 ≤ D.k i
      · set x0 := BinaryIRSProfile.domain i
        have hrew : S.H1 = S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (D.y i ^ 4) * D.gj 2) +
            (S.R + C (D.y i) * S.p.comp (X ^ 2)) ^ 4 * D.gj 2 := by
          rw [hH1_eq, char2_add_pow_four, mul_pow, ← map_pow]
          have hz := CharTwo.add_self_eq_zero (S.p.comp (X ^ 2) ^ 4 * C (D.y i ^ 4) * D.gj 2)
          linear_combination -hz
        have hg0y : (X - C x0) ^ (2 * D.k i - 1) ∣ D.gj 0 + C (D.y i ^ 4) * D.gj 2 := by
          have hgsh : D.gj 0 + C (D.y i ^ 4) * D.gj 2 =
              (D.A1sh x0 (D.y i) 0).comp (X ^ 2) + (X - C x0) * (D.Bsh (D.y i) 0).comp (X ^ 2) := by
            simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, hCj1, hBj1,
              mul_zero, add_zero, add_comp, mul_comp, C_comp, sub_eq_add_neg, CharTwo.neg_eq]
            have hz := CharTwo.add_self_eq_zero (C x0 * ((D.Bj 0).comp (X ^ 2) + C (D.y i ^ 4) * (D.Bj 2).comp (X ^ 2)))
            linear_combination -hz
          rw [hgsh]; have hloc := D.local_shifted_ords i 0
          apply dvd_add
          · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 2 * (D.k i - 0))).trans
              ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.1)
          · exact (pow_dvd_pow _ (by omega : 2 * D.k i - 1 ≤ 1 + 2 * (D.k i - 1 - 0))).trans
              (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ _ _).mpr hloc.2.2))
        rw [hrew]
        exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans hg0y) _)
          (dvd_mul_of_dvd_right (D.pow_dvd_g2_of_k i) _)
      · rw [show 2 * D.k i - 5 = 0 by omega, pow_zero]; exact one_dvd _
  have hH1_sum_fH : ∑ i : Idx, (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i - 5) ≤ S.H1.natDegree :=
    sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain
      BinaryIRSProfile.domain.injective S.H1 S.H1_ne_zero _ (fun i _ => hH1_fH i)
  have hRes_ord2 : D.n1 + 8 * D.n2 + 20 * D.n3 + 10 * D.nt ≤ 5 * S.M20.natDegree + S.H1.natDegree := by
    have hgen : ∀ S0 : Finset Idx,
        (S0.filter fun i => D.k i = 1).card + 8 * (S0.filter fun i => D.k i = 2).card +
          20 * (S0.filter fun i => 3 ≤ D.k i).card + 10 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 1 else 0) + 8 * (if D.k i = 2 then 1 else 0) +
          20 * (if 3 ≤ D.k i then 1 else 0) + 10 * (D.k i - 3)) := by
      intro S0
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    have hlhs : D.n1 + 8 * D.n2 + 20 * D.n3 + 10 * D.nt ≤
        ∑ i : Idx, (5 * baseM20 i + (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i - 5)) := by
      unfold KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
      rw [hgen Finset.univ]
      apply Finset.sum_le_sum; intro i _; dsimp [baseM20]; split_ifs <;> omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hlhs
    omega
  have hRes_ord3 : D.n1 + 6 * D.n2 + 12 * D.n3 + 6 * D.nt ≤ 3 * S.M20.natDegree + S.H1.natDegree := by
    have hgen : ∀ S0 : Finset Idx,
        (S0.filter fun i => D.k i = 1).card + 6 * (S0.filter fun i => D.k i = 2).card +
          12 * (S0.filter fun i => 3 ≤ D.k i).card + 6 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 1 else 0) + 6 * (if D.k i = 2 then 1 else 0) +
          12 * (if 3 ≤ D.k i then 1 else 0) + 6 * (D.k i - 3)) := by
      intro S0
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    have hlhs : D.n1 + 6 * D.n2 + 12 * D.n3 + 6 * D.nt ≤
        ∑ i : Idx, (3 * baseM20 i + (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i - 5)) := by
      unfold KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
      rw [hgen Finset.univ]
      apply Finset.sum_le_sum; intro i _; dsimp [baseM20]; split_ifs <;> omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hlhs
    omega
  have hRes_col1 := D.natDegree_ResY_le_col1
  have h5D1_H1 : 5 * S.D1.natDegree ≤ S.H1.natDegree := by
    have h := natDegree_le_of_dvd S.D1_pow5_dvd_H1 S.H1_ne_zero
    rwa [natDegree_pow] at h
  have hg2_lo : D.n3 + 2 * D.nt ≤ (D.gj 2).natDegree := by
    have hsum : D.n3 + 2 * D.nt = ∑ i : Idx, (2 * D.k i - 5) := by
      have hgen : ∀ S0 : Finset Idx,
          (S0.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S0, (D.k i - 3) = ∑ i ∈ S0, (2 * D.k i - 5) := by
        intro S0
        have hrew : (S0.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S0, (D.k i - 3) =
            ∑ i ∈ S0, ((if 3 ≤ D.k i then 1 else 0) + 2 * (D.k i - 3)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        rw [hrew]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
      unfold KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
    rw [hsum]; exact sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain
      BinaryIRSProfile.domain.injective (D.gj 2) D.g2_ne_zero _ (fun i _ => D.pow_dvd_g2_of_k i)
  have hg2_hi := D.natDegree_gj_le 2
  have hpM20_g2 : 2 * S.p.natDegree + 2 * S.M20.natDegree ≤ (D.gj 2).natDegree + D.W_F - wY := by
    have hB := S.two_mul_natDegree_p_mul_M20_le_with_g2
    rw [natDegree_mul S.hp hM20_ne] at hB; omega
  have hD1_le_p : S.D1.natDegree ≤ S.p.natDegree := by rw [S.D1_natDegree]; exact S.D2_natDegree_le_p
  have hW2b_ineq : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N →
      H_b.derivative ≠ 0 →
      2 * (D.n1 : ℤ) + 4 * (D.n2 : ℤ) + 4 * (D.n3 : ℤ) - 2 * (e1_cnt : ℤ) - 4 * (e2_cnt : ℤ) ≤
        (S.H1.natDegree : ℤ) + ((D.gj 2).natDegree : ℤ) := by
    intro hthr hHb'
    have h1 := congrArg Polynomial.natDegree hHb_wr
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 (hlin_ne _)) (pow_ne_zero 2 hSb_ne)) hHb_op_ne,
      natDegree_mul (pow_ne_zero 2 (hlin_ne _)) (pow_ne_zero 2 hSb_ne), natDegree_pow, natDegree_pow, hlin_deg,
      natDegree_mul (mul_ne_zero (pow_ne_zero 2 hSmis_ne) (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff _).mp S.hp)))
        (mt (comp_X_sq_eq_zero_iff _).mp hM20_ne),
      natDegree_mul (pow_ne_zero 2 hSmis_ne) (pow_ne_zero 5 (mt (comp_X_sq_eq_zero_iff _).mp S.hp)),
      natDegree_pow, natDegree_pow, natDegree_comp_X_sq, natDegree_comp_X_sq, hSmis_deg] at h1
    have hNsum := D.n_sum_eq_N
    have hop_lt : (C c0 * H_b + Ndom * H_b.derivative).natDegree < N := by omega
    have hHb_ge_N : N ≤ H_b.natDegree := by
      by_contra hlt
      have hterm2 : (Ndom * H_b.derivative).natDegree = N + H_b.derivative.natDegree := by
        rw [natDegree_mul hNdom_ne hHb', hNdom_deg]
      have hterm1 : (C c0 * H_b).natDegree < (Ndom * H_b.derivative).natDegree := by
        have := natDegree_C_mul_le c0 H_b; omega
      have heq := natDegree_add_eq_right_of_natDegree_lt hterm1
      omega
    have hHb_le : H_b.natDegree ≤ (D.gj 2).natDegree + Smis.natDegree + R_F.natDegree := by
      have h2 := congrArg Polynomial.natDegree hGbRF_eq
      rw [natDegree_mul hGb_ne hRF_ne, natDegree_mul D.g2_ne_zero hSmis_ne,
        natDegree_mul (pow_ne_zero 2 hSb_ne) hHb_ne] at h2
      omega
    rw [hSmis_deg] at hHb_le; omega
  have hB1_nat : H_b.derivative = 0 →
      ((D.gj 2).natDegree + S.H1.natDegree =
        D.n0 + D.n1 + 3 * D.n2 + 7 * D.n3 + 4 * D.nt + 10 * S.p.natDegree + 2 * e1_cnt + 2 * e2_cnt + 2 * erem_cnt) ∧
      H_b.natDegree = 0 := by
    intro hHb'
    obtain ⟨qH, hqH⟩ := (derivative_eq_zero_iff_sq H_b).mp hHb'
    have hqH_u : IsUnit qH := hHb_sf qH (by rw [hqH, sq])
    have hHb_deg0 : H_b.natDegree = 0 := by
      rw [hqH, natDegree_pow, natDegree_eq_zero_of_isUnit hqH_u, mul_zero]
    have hop_deg0 : (C c0 * H_b + Ndom * H_b.derivative).natDegree = 0 := by
      rw [hHb', mul_zero, add_zero]
      have hle := natDegree_C_mul_le c0 H_b; omega
    rw [hHb_deg0, hop_deg0, zero_add, zero_add] at hHb_deg_id
    have hNsum := D.n_sum_eq_N
    have herem_id : D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt + erem_cnt = S.M20.natDegree := by
      dsimp [erem_cnt]; omega
    exact ⟨by omega, hHb_deg0⟩
  have hB0_proof : H_b.derivative = 0 →
      6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + (D.gj 2).natDegree + D.W_F - wY + 1 + 8 * S.p.natDegree < 3 * N →
      zRaw c0 c1 R_F Q_raw = 0 ∧
      3 * (D.n1 : ℤ) + 3 * (D.n2 : ℤ) + 3 * (D.n3 : ℤ) - 3 * (e1_cnt : ℤ) -
        3 * (e2_cnt : ℤ) - 2 * (erem_cnt : ℤ) - 2 * (S.D1.natDegree : ℤ) ≤ (S.H1.natDegree : ℤ) := by
    intro hhb hd2h
    have hHb0 := (hB1_nat hhb).2
    have hQF_deg_lt : (Q_raw * F1_raw).natDegree < 3 * N := by
      have hQ_deg : Q_raw.natDegree = 3 * Smis.natDegree + 2 * S1U.natDegree + (D.gj 2).natDegree := by
        dsimp [Q_raw]
        rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hSmis_ne) (pow_ne_zero 2 (hlin_ne _))) D.g2_ne_zero,
          natDegree_mul (pow_ne_zero 3 hSmis_ne) (pow_ne_zero 2 (hlin_ne _)),
          natDegree_pow, natDegree_pow]
      have hF1_deg : F1_raw.natDegree ≤ 3 * Smis.natDegree + 2 * S1U.natDegree +
          8 * S.p.natDegree + (D.W_F - wY + 1) := by
        dsimp [F1_raw]
        have hp4 : (S.p.comp (X ^ 2) ^ 4).natDegree = 8 * S.p.natDegree := by
          rw [natDegree_pow, natDegree_comp_X_sq]; ring
        refine natDegree_mul_le.trans (Nat.add_le_add ?_ D.natDegree_f1_eval_P_le)
        refine natDegree_mul_le.trans (Nat.add_le_add ?_ (le_of_eq hp4))
        exact natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le natDegree_pow_le)
      have hmul := natDegree_mul_le (p := Q_raw) (q := F1_raw)
      rw [hQ_deg, hSmis_deg, hlin_deg] at hmul
      rw [hSmis_deg, hlin_deg] at hF1_deg
      omega
    have hQ_RF_sq : ∃ Sq : Fld[X], Q_raw * R_F = Sq ^ 2 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hHb0
      set rtH : Fld := (frobEquiv Fld).symm (H_b.coeff 0)
      refine ⟨C rtH * Smis * S1U * S_b, ?_⟩
      have hsqC : (C rtH : Fld[X]) ^ 2 = H_b := by
        rw [← map_pow, frobEquiv_symm_sq, ← hC]
      calc Q_raw * R_F = (Smis * S1U) ^ 2 * (G_b * R_F) := by dsimp [Q_raw, G_b]; ring
        _ = (Smis * S1U) ^ 2 * (S_b ^ 2 * H_b) := by rw [hGbRF_eq]
        _ = (C rtH * Smis * S1U * S_b) ^ 2 := by rw [← hsqC]; ring
    obtain ⟨Sq, hSq⟩ := hQ_RF_sq
    obtain ⟨A0, B0, H0, hRF4, hQ4⟩ := char2_fourth_power_of_sq_ratio hQ_raw_ne hRF_ne hF1_raw_ne hSq hode_id hQF_deg_lt
    have hz0_B1 : zRaw c0 c1 R_F Q_raw = 0 := by
      rw [hRF4, hQ4, zRaw_mul_common]
      have h1 : zRaw c0 c1 (A0 ^ 4) (B0 ^ 4) = 0 := by
        unfold zRaw
        rw [char2_hasse_two_pow_four, char2_derivative_pow_four, char2_hasse_two_pow_four, char2_derivative_pow_four]
        ring
      rw [h1, mul_zero]
    refine ⟨hz0_B1, ?_⟩
    have hA0_ne : A0 ≠ 0 := by intro h0; rw [h0, zero_pow (by norm_num), zero_mul] at hRF4; exact hRF_ne hRF4
    have hB0_ne : B0 ≠ 0 := by intro h0; rw [h0, zero_pow (by norm_num), zero_mul] at hQ4; exact hQ_raw_ne hQ4
    have hH0_ne : H0 ≠ 0 := by intro h0; rw [h0, mul_zero] at hRF4; exact hRF_ne hRF4
    have hpt203 : ∀ a ∈ S_fin,
        3 * ((S1U.map ι).rootMultiplicity a : ℤ) + 3 * ((S2U.map ι).rootMultiplicity a : ℤ) -
          2 * (((S.M20.map ι).rootMultiplicity (a ^ 2) -
            (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) : ℕ) : ℤ) -
          2 * ((S.D1.map ι).rootMultiplicity a : ℤ) ≤
        ((S.H1.map ι).rootMultiplicity a : ℤ) := by
      intro a _
      have hH1_ge : (S1U.map ι).rootMultiplicity a + 3 * (S2U.map ι).rootMultiplicity a ≤
          (S.H1.map ι).rootMultiplicity a := by
        have hwE : S.H1.map ι = S1U.map ι * (S2U.map ι) ^ 3 * R_F.map ι := by
          rw [hRF_def]; dsimp [Shit]; simp only [Polynomial.map_mul, Polynomial.map_pow]
        have hS1E := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
        have hS2E := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2U)
        have hRFE := (Polynomial.map_ne_zero_iff ι.injective).mpr hRF_ne
        rw [hwE, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)) hRFE),
          rootMultiplicity_mul (mul_ne_zero hS1E (pow_ne_zero 3 hS2E)),
          rootMultiplicity_pow_eq (S2U.map ι) hS2E 3 a]
        exact Nat.le_add_right _ _
      by_cases hm1 : (S1U.map ι).rootMultiplicity a = 1
      · have hk2z : (S2U.map ι).rootMultiplicity a = 0 := by
          rw [hlin_rm] at hm1 ⊢; split_ifs at hm1 with h1
          split_ifs with h2
          · exfalso; rcases h1 with ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, heq⟩
            have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            simp only [I1U, I2U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega
          · rfl
        rw [hm1, hk2z]
        by_cases hd1 : 1 ≤ (S.D1.map ι).rootMultiplicity a
        · omega
        · have hd1z : (S.D1.map ι).rootMultiplicity a = 0 := by omega
          have hdom : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) := by
            rw [hlin_rm] at hm1; split_ifs at hm1 with h
            rcases h with ⟨i, _, hi⟩; exact ⟨i, hi⟩
          have hi := Classical.choose_spec hdom
          set i := Classical.choose hdom
          have hk1U : D.k i = 1 ∧ S.isU0 i := by
            rw [hlin_rm] at hm1; split_ifs at hm1 with h
            rcases h with ⟨j, hj, heq⟩; rw [hi] at heq
            have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
            exact (Finset.mem_filter.mp hj).2
          have herem_pos : 1 ≤ (S.M20.map ι).rootMultiplicity (a ^ 2) -
              (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) := by
            by_contra h0
            have hb0 : baseM20 i = 0 := by dsimp [baseM20]; simp [hk1U.1, hk1U.2]
            have hM20z : (S.M20.map ι).rootMultiplicity (a ^ 2) = 0 := by
              rw [dif_pos hdom, hb0, Nat.sub_zero] at h0; omega
            have hp_ne : S.p.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
              intro hp0
              have hD20 := (S.D2_eval_eq_zero_iff i).mpr ⟨hp0, hk1U.2⟩
              have hD10 := (sqrtPoly_eval_eq_zero_iff S.D2 _).mpr hD20
              have h1 : 1 ≤ (S.D1.map ι).rootMultiplicity a := by
                rw [hi, rootMultiplicity_map_eq]
                exact (le_rootMultiplicity_iff S.D1_ne_zero).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr hD10)
              omega
            have hSb_ne_ev : S_b.eval (BinaryIRSProfile.domain i) ≠ 0 := by
              intro hSb0
              have hwr_ev := congrArg (Polynomial.eval (BinaryIRSProfile.domain i)) hHb_wr
              rw [eval_mul, eval_mul, eval_pow, eval_pow, hSb0, zero_pow (by norm_num), mul_zero, zero_mul] at hwr_ev
              have hSm_ne : Smis.eval (BinaryIRSProfile.domain i) ≠ 0 := by
                dsimp [Smis, S0, S1noU, S2noU, linProd]; simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C]
                refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;>
                  (apply Finset.prod_ne_zero_iff.mpr; intro j hj; apply sub_ne_zero.mpr; intro heq
                   have := BinaryIRSProfile.domain.injective heq; subst this
                   simp only [I0, I1noU, I2noU, Finset.mem_filter, Finset.mem_univ, true_and] at hj
                   first | omega | exact hj.2 hk1U.2)
              have hM20_ne_ev : S.M20.eval (BinaryIRSProfile.domain i ^ 2) ≠ 0 := by
                intro h0'; apply (show (S.M20.map ι).rootMultiplicity (a ^ 2) ≠ 0 by
                  rw [hi, ← map_pow, rootMultiplicity_map_eq]
                  have := (le_rootMultiplicity_iff hM20_ne).mpr (by rw [pow_one]; exact dvd_iff_isRoot.mpr h0')
                  omega) hM20z
              rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_comp, eval_comp, eval_pow, eval_X] at hwr_ev
              exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hSm_ne) (pow_ne_zero 5 hp_ne)) hM20_ne_ev hwr_ev.symm
            have hHb_ne_ev : H_b.eval (BinaryIRSProfile.domain i) ≠ 0 := by
              have hC := Polynomial.eq_C_of_natDegree_eq_zero hHb0
              rw [hC, eval_C]; intro hc0'; rw [hc0', map_zero] at hC; exact hHb_ne hC
            have hGbRF_ne : (G_b * R_F).eval (BinaryIRSProfile.domain i) ≠ 0 := by
              rw [hGbRF_eq, eval_mul, eval_pow]; exact mul_ne_zero (pow_ne_zero 2 hSb_ne_ev) hHb_ne_ev
            have hg2_ne_ev : (D.gj 2).eval (BinaryIRSProfile.domain i) ≠ 0 := fun h0' =>
              hGbRF_ne (by dsimp [G_b]; rw [eval_mul, eval_mul, h0', zero_mul, zero_mul])
            have hRF_ne_ev : R_F.eval (BinaryIRSProfile.domain i) ≠ 0 := fun h0' =>
              hGbRF_ne (by rw [eval_mul, h0', mul_zero])
            have hRF_0 : R_F.rootMultiplicity (BinaryIRSProfile.domain i) = 0 :=
              rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hRF_ne_ev)
            have hQ_2 : Q_raw.rootMultiplicity (BinaryIRSProfile.domain i) = 2 := by
              rw [← rootMultiplicity_map_eq, ← hi]
              have hS0z : (S0.map ι).rootMultiplicity a = 0 := by
                rw [hlin_rm, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and] at hj; omega
              have hS1nz : (S1noU.map ι).rootMultiplicity a = 0 := by
                rw [hlin_rm, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I1noU, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj.2 hk1U.2
              have hS2nz : (S2noU.map ι).rootMultiplicity a = 0 := by
                rw [hlin_rm, if_neg]; rintro ⟨j, hj, heq⟩; rw [hi] at heq
                have := BinaryIRSProfile.domain.injective (ι.injective heq); subst this
                simp only [I2noU, Finset.mem_filter, Finset.mem_univ, true_and] at hj; omega
              have hg2z : ((D.gj 2).map ι).rootMultiplicity a = 0 := by
                rw [hi, rootMultiplicity_map_eq]; exact rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hg2_ne_ev)
              dsimp [Q_raw, Smis]; simp only [Polynomial.map_mul, Polynomial.map_pow]
              have hS0E := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I0)
              have hS1nE := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1noU)
              have hS2nE := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2noU)
              have hS1UE := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
              have hg2E := (Polynomial.map_ne_zero_iff ι.injective).mpr D.g2_ne_zero
              have hSmE := mul_ne_zero (mul_ne_zero hS0E hS1nE) hS2nE
              rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hSmE) (pow_ne_zero 2 hS1UE)) hg2E),
                rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 3 hSmE) (pow_ne_zero 2 hS1UE)),
                rootMultiplicity_pow_eq _ hSmE 3 a,
                rootMultiplicity_mul hSmE, rootMultiplicity_mul (mul_ne_zero hS0E hS1nE),
                rootMultiplicity_pow_eq _ hS1UE 2 a,
                hS0z, hS1nz, hS2nz, hm1, hg2z]
            have hmodRF : R_F.rootMultiplicity (BinaryIRSProfile.domain i) =
                4 * A0.rootMultiplicity (BinaryIRSProfile.domain i) + H0.rootMultiplicity (BinaryIRSProfile.domain i) := by
              rw [hRF4, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 hA0_ne) hH0_ne),
                rootMultiplicity_pow_eq A0 hA0_ne 4 _]
            have hmodQ : Q_raw.rootMultiplicity (BinaryIRSProfile.domain i) =
                4 * B0.rootMultiplicity (BinaryIRSProfile.domain i) + H0.rootMultiplicity (BinaryIRSProfile.domain i) := by
              rw [hQ4, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 hB0_ne) hH0_ne),
                rootMultiplicity_pow_eq B0 hB0_ne 4 _]
            omega
          omega
      · have hm0 : (S1U.map ι).rootMultiplicity a = 0 := by rw [hlin_rm] at hm1 ⊢; split_ifs at hm1 ⊢ <;> omega
        rw [hm0] at hH1_ge ⊢; omega
    have hsum203 := Finset.sum_le_sum hpt203
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum] at hsum203
    have hsum_S1U : ∑ a ∈ S_fin, (S1U.map ι).rootMultiplicity a = I1U.card := by
      have hsub : (S1U.map ι).roots.toFinset ⊆ S_fin := fun a ha => by
        have hne1 : S1U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I1U)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne1] at ha
        have hrm : (S1U.map ι).rootMultiplicity a ≠ 0 := fun h0 => hne1 ((rootMultiplicity_eq_zero_iff.mp h0) ha)
        rw [hlin_rm] at hrm; split_ifs at hrm with h
        · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
        · exact absurd rfl hrm
      rw [sum_rootMultiplicity_map_eq_natDegree _ (hlin_ne I1U) S_fin hsub, hlin_deg]
    have hsum_S2U : ∑ a ∈ S_fin, (S2U.map ι).rootMultiplicity a = I2U.card := by
      have hsub : (S2U.map ι).roots.toFinset ⊆ S_fin := fun a ha => by
        have hne2 : S2U.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr (hlin_ne I2U)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne2] at ha
        have hrm : (S2U.map ι).rootMultiplicity a ≠ 0 := fun h0 => hne2 ((rootMultiplicity_eq_zero_iff.mp h0) ha)
        rw [hlin_rm] at hrm; split_ifs at hrm with h
        · rcases h with ⟨i, _, rfl⟩; exact hS_dom i
        · exact absurd rfl hrm
      rw [sum_rootMultiplicity_map_eq_natDegree _ (hlin_ne I2U) S_fin hsub, hlin_deg]
    have hsum_er : ∑ a ∈ S_fin, ((S.M20.map ι).rootMultiplicity (a ^ 2) -
        (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0)) = erem_cnt := by
      have hadd : (∑ a ∈ S_fin, ((S.M20.map ι).rootMultiplicity (a ^ 2) -
          (if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0))) +
          (∑ a ∈ S_fin, if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) =
          ∑ a ∈ S_fin, (S.M20.map ι).rootMultiplicity (a ^ 2) := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
        split_ifs with h
        · set i := Classical.choose h
          have hi : a = ι (BinaryIRSProfile.domain i) := Classical.choose_spec h
          have hle : baseM20 i ≤ (S.M20.map ι).rootMultiplicity (a ^ 2) := by
            have h1 : (S.M20.map ι).rootMultiplicity (a ^ 2) = S.M20.rootMultiplicity (BinaryIRSProfile.domain i ^ 2) := by
              rw [hi, ← map_pow, rootMultiplicity_map_eq]
            rw [h1]; exact (le_rootMultiplicity_iff hM20_ne).mpr (hbaseM20_dvd i)
          omega
        · omega
      have hbase_tot : (∑ a ∈ S_fin, if h : ∃ i : Idx, a = ι (BinaryIRSProfile.domain i) then baseM20 (Classical.choose h) else 0) =
          D.n2 + 3 * D.n3 + 2 * D.nt + e1_cnt + e2_cnt := by
        have himg : Finset.univ.image (fun i : Idx => ι (BinaryIRSProfile.domain i)) ⊆ S_fin := fun a ha => by
          rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩; exact hS_dom i
        rw [← Finset.sum_subset himg (fun a _ hna => by
          rw [dif_neg]; intro ⟨i, hi⟩; apply hna; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)]
        rw [Finset.sum_image (fun i _ j _ h => BinaryIRSProfile.domain.injective (ι.injective h))]
        have hterm : ∀ i : Idx,
            (if h : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j) then baseM20 (Classical.choose h) else 0) =
            baseM20 i := fun i => by
          rw [dif_pos ⟨i, rfl⟩]
          have heq : Classical.choose (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j)) = i :=
            BinaryIRSProfile.domain.injective (ι.injective (Classical.choose_spec (⟨i, rfl⟩ : ∃ j : Idx, ι (BinaryIRSProfile.domain i) = ι (BinaryIRSProfile.domain j))).symm)
          rw [heq]
        simp_rw [hterm]; exact hbaseM20_sum
      rw [hbase_tot, sum_rootMultiplicity_sq_map_eq_natDegree S.M20 hM20_ne S_fin hS_M20] at hadd
      dsimp [erem_cnt]; omega
    rw [hsum_S1U, hsum_S2U, hsum_er,
      sum_rootMultiplicity_map_eq_natDegree S.D1 S.D1_ne_zero S_fin hS_D1,
      sum_rootMultiplicity_map_eq_natDegree S.H1 S.H1_ne_zero S_fin hS_H1] at hsum203
    omega
  exact table4_b1c1_rows_sat rGt r4g4 bCase
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
    D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3
    S.p.natDegree (D.gj 2).natDegree S.M20.natDegree S.R.natDegree S.UP.natDegree
    e1_cnt e2_cnt erem_cnt S.H1.natDegree S.D1.natDegree D.W_F hBS
    (by have := D.hWF_hi; omega) (by dsimp [erem_cnt]; omega)
    he1_le he2_le hD1_le_p (by omega) (by omega) (by omega) hg2_lo (by omega) (by omega)
    (by omega) (by omega) hUP_a12 (by omega) hRes_ord2 hRes_ord3 (by omega) (by omega)
    ⟨fun hrt => by
        have hr : 2 * S.p.natDegree + wY < S.R.natDegree := by simpa [rGt] using hrt
        exact ⟨by omega, S.natDegree_UP_eq_of_gt hr⟩,
     fun hrf => by
        have hle : S.R.natDegree ≤ 2 * S.p.natDegree + wY := by
          have : ¬ (2 * S.p.natDegree + wY < S.R.natDegree) := by simpa [rGt] using hrf
          omega
        exact ⟨hle, S.natDegree_UP_le_of_le hle⟩⟩
    ⟨fun h4t => by
        have h4 : S.R ≠ 0 ∧ 8 * S.p.natDegree + D.W_F - wY + 1 < 4 * S.R.natDegree + (D.gj 2).natDegree := by
          simpa [r4g4] using h4t
        rw [hH1_eq]
        have hg0 := D.natDegree_gj_le 0
        have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
        exact (natDegree_add_le _ _).trans (max_le
          (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega))
          (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl))),
     fun h4f => by
        have h4 : ¬ (S.R ≠ 0 ∧ 8 * S.p.natDegree + D.W_F - wY + 1 < 4 * S.R.natDegree + (D.gj 2).natDegree) := by
          simpa [r4g4] using h4f
        have hH1_le : S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 := by
          rw [hH1_eq]
          have hg0 := D.natDegree_gj_le 0
          have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
          refine (natDegree_add_le _ _).trans (max_le
            (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)) ?_)
          by_cases hR0 : S.R = 0
          · rw [hR0, zero_pow (by norm_num), zero_mul, natDegree_zero]; exact Nat.zero_le _
          · have hle : 4 * S.R.natDegree + (D.gj 2).natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 := by
              push Not at h4; exact h4 hR0
            exact (natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le le_rfl)).trans hle
        omega⟩
    ⟨fun hb0 => by
        have hflags : thr_B1 = true ∧ hb_const = true ∧ d2_holds = true := by
          cases h1 : thr_B1 <;> cases h2 : hb_const <;> cases h3 : d2_holds <;> cases h4 : ode_holds <;>
            simp [bCase, h1, h2, h3, h4] at hb0 ⊢
        have hthr : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N := by
          simpa [thr_B1] using hflags.1
        have hhb : H_b.derivative = 0 := by simpa [hb_const] using hflags.2.1
        have hd2h : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + (D.gj 2).natDegree + D.W_F - wY + 1 + 8 * S.p.natDegree < 3 * N := by
          simpa [d2_holds] using hflags.2.2
        have ⟨hz0_B1, h203⟩ := hB0_proof hhb hd2h
        have ⟨hB1, hB2, _⟩ := hODE_holds_bounds hz0_B1
        exact ⟨by omega, (hB1_nat hhb).1, by omega, h203, hB1, hB2⟩,
     fun hb1 => by
        have hflags : thr_B1 = true ∧ hb_const = true ∧ d2_holds = false := by
          cases h1 : thr_B1 <;> cases h2 : hb_const <;> cases h3 : d2_holds <;> cases h4 : ode_holds <;>
            simp [bCase, h1, h2, h3, h4] at hb1 ⊢
        have hthr : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N := by
          simpa [thr_B1] using hflags.1
        have hhb : H_b.derivative = 0 := by simpa [hb_const] using hflags.2.1
        have hd2f : ¬ (6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + (D.gj 2).natDegree + D.W_F - wY + 1 + 8 * S.p.natDegree < 3 * N) := by
          simpa [d2_holds] using hflags.2.2
        exact ⟨by omega, (hB1_nat hhb).1, by omega⟩,
     fun hb2 => by
        have hflags : thr_B1 = false ∧ ode_holds = true := by
          cases h1 : thr_B1 <;> cases h2 : hb_const <;> cases h3 : d2_holds <;> cases h4 : ode_holds <;>
            simp [bCase, h1, h2, h3, h4] at hb2 ⊢
        have hthrf : ¬ (6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N) := by
          simpa [thr_B1] using hflags.1
        have hode : zRaw c0 c1 R_F Q_raw = 0 := by simpa [ode_holds] using hflags.2
        have ⟨hB1, hB2, h3⟩ := hODE_holds_bounds hode
        exact ⟨by omega, by omega, hB1, hB2⟩,
     fun hb3 => by
        have hflags : thr_B1 = false ∧ ode_holds = false := by
          cases h1 : thr_B1 <;> cases h2 : hb_const <;> cases h3 : d2_holds <;> cases h4 : ode_holds <;>
            simp [bCase, h1, h2, h3, h4] at hb3 ⊢
        have hthrf : ¬ (6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N) := by
          simpa [thr_B1] using hflags.1
        have hode : zRaw c0 c1 R_F Q_raw ≠ 0 := by simpa [ode_holds] using hflags.2
        exact ⟨by omega, hODE_fail_bound hode⟩,
     fun hb4 => by
        have hflags : thr_B1 = true ∧ hb_const = false ∧ ode_holds = true := by
          cases h1 : thr_B1 <;> cases h2 : hb_const <;> cases h3 : d2_holds <;> cases h4 : ode_holds <;>
            simp [bCase, h1, h2, h3, h4] at hb4 ⊢
        have hthr : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N := by
          simpa [thr_B1] using hflags.1
        have hhb : H_b.derivative ≠ 0 := by simpa [hb_const] using hflags.2.1
        have hode : zRaw c0 c1 R_F Q_raw = 0 := by simpa [ode_holds] using hflags.2.2
        have ⟨hB1, hB2, h3⟩ := hODE_holds_bounds hode
        exact ⟨by omega, hW2b_ineq hthr hhb, by omega, hB1, hB2⟩,
     fun h0 h1 h2 h3 h4 => by
        have hflags : thr_B1 = true ∧ hb_const = false ∧ ode_holds = false := by
          cases hc1 : thr_B1 <;> cases hc2 : hb_const <;> cases hc3 : d2_holds <;> cases hc4 : ode_holds <;>
            simp [bCase, hc1, hc2, hc3, hc4] at h0 h1 h2 h3 h4 ⊢
        have hthr : 6 * D.n0 + 4 * D.n1 + 2 * e1_cnt + 6 * e2_cnt + 10 * S.p.natDegree + 2 * S.M20.natDegree < 3 * N := by
          simpa [thr_B1] using hflags.1
        have hhb : H_b.derivative ≠ 0 := by simpa [hb_const] using hflags.2.1
        have hode : zRaw c0 c1 R_F Q_raw ≠ 0 := by simpa [ode_holds] using hflags.2.2
        exact ⟨by omega, hW2b_ineq hthr hhb, hODE_fail_bound hode⟩⟩

end B6401Table4NonK
end ProximityPrize.SubmissionBinaryLower
