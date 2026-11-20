import ProximityPrize.SubmissionLower.Koala6844VirtualHighGermDegrees
import Mathlib.FieldTheory.AlgebraicClosure


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial Koala6844Normalization Koala6844VirtualHigh
open scoped Classical

noncomputable section

set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

def germFirst (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (ζ : E) (j : Fin 2) : E :=
  (D.A0 j).eval₂ embed ζ

def germSecond (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (ζ : E) (j : Fin 2) : E :=
  ((D.A0 j).map σ.toRingHom).eval₂ embed ζ

structure ActiveResultantGerm (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) where
  center : E
  order : ℕ
  c : E
  c_ne : c ≠ 0
  d0_ne : D.d0.eval₂ embed center ≠ 0
  first_ne : germFirst D embed center 0 ≠ 0 ∨ germFirst D embed center 1 ≠ 0
  second_zero_ne : germSecond D embed center 0 ≠ 0
  second_seed_ne : ∀ g ∈ D.seeds,
    germSecond D embed center 0 + embed (σ g) * germSecond D embed center 1 ≠ 0
  relation : ∀ g ∈ D.seeds, ∃ V : Polynomial E,
    Polynomial.taylor center ((D.d0 * D.selected g + Polynomial.C g * D.C1).map embed) =
      Polynomial.X ^ order * V ∧
    V.eval 0 * (germSecond D embed center 0 + embed (σ g) * germSecond D embed center 1) =
      (germFirst D embed center 0 + embed g * germFirst D embed center 1) * c * embed (σ g)

private theorem taylor_X_sub_center (ζ : E) :
    Polynomial.taylor ζ (Polynomial.X - Polynomial.C ζ) = Polynomial.X := by
  simp [Polynomial.taylor_X]

private theorem eval_taylor_zero (ζ : E) (p : Polynomial E) :
    (Polynomial.taylor ζ p).eval 0 = p.eval ζ := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.taylor_coeff_zero]

private theorem coprime_X_of_constant_ne (P : Polynomial E) (h : P.eval 0 ≠ 0) :
    IsCoprime (Polynomial.X : Polynomial E) P := by
  apply (Polynomial.irreducible_X (R := E)).coprime_iff_not_dvd.mpr
  intro hdiv
  exact h (by simpa only [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero] using hdiv)

theorem exists_active_resultant_germ [IsAlgClosed E]
    (D : CenteredVirtualData x nodes σ w agreement errors excess) (embed : K →+* E) :
    Nonempty (ActiveResultantGerm D embed) := by
  classical
  let d := D.d1.map embed
  let b := D.D1.map embed
  have hdn : d ≠ 0 := Polynomial.map_ne_zero D.d1_ne
  have hbn : b ≠ 0 := by
    apply Polynomial.map_ne_zero
    intro hz
    exact D.active (hz ▸ dvd_zero D.d1)
  have hnodvd : ¬ d ∣ b := fun h => D.active ((Polynomial.map_dvd_map' embed).mp h)
  have hnr : ¬ d.roots ≤ b.roots := fun h =>
    hnodvd (((IsAlgClosed.splits d).dvd_iff_roots_le_roots hdn hbn).mpr h)
  rw [Multiset.le_iff_count] at hnr
  push Not at hnr
  obtain ⟨ζ, hζ⟩ := hnr
  simp only [Polynomial.count_roots] at hζ
  let k := b.rootMultiplicity ζ
  have hkd : k < d.rootMultiplicity ζ := hζ
  have hroot : d.IsRoot ζ := (Polynomial.rootMultiplicity_pos hdn).mp (Nat.zero_lt_of_lt hkd)
  have hroot' : D.d1.eval₂ embed ζ = 0 := by
    rw [← Polynomial.eval_map]
    exact hroot
  obtain ⟨bq,hbq,hbqUnit⟩ := b.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hbn ζ
  let c := bq.eval ζ
  have hc : c ≠ 0 := fun h => hbqUnit (Polynomial.dvd_iff_isRoot.mpr h)
  obtain ⟨dq,hdq⟩ : (Polynomial.X - Polynomial.C ζ)^(k+1) ∣ d :=
    (Polynomial.le_rootMultiplicity_iff hdn).mp hkd
  refine ⟨{
    center := ζ
    order := k
    c := c
    c_ne := hc
    d0_ne := eval₂_ne_zero_of_coprime_root D.d0 D.d1 D.coprime_content embed ζ hroot'
    first_ne := ?_
    second_zero_ne := ?_
    second_seed_ne := ?_
    relation := ?_ }⟩
  · by_contra! h
    exact (eval₂_ne_zero_of_coprime_root (D.A0 0) (D.A0 1) D.coprime_A0 embed ζ h.2) h.1
  · have h := D.coprime_denominator1 0 D.zero_mem
    have he : specializeAffine D.A0 0 = D.A0 0 := by simp [specializeAffine]
    rw [he] at h
    exact eval₂_ne_zero_of_coprime_root _ _ h embed ζ hroot'
  · intro g hg
    have h := eval₂_ne_zero_of_coprime_root _ _ (D.coprime_denominator1 g hg) embed ζ hroot'
    simpa [germSecond, specializeAffine, Polynomial.eval₂_add, Polynomial.eval₂_mul] using h
  · intro g hg
    let A := specializeAffine D.A0 g
    let B := A.map σ.toRingHom
    let AT := Polynomial.taylor ζ (A.map embed)
    let BT := Polynomial.taylor ζ (B.map embed)
    let Q := Polynomial.taylor ζ ((D.normalized g).map embed)
    let Bq := Polynomial.taylor ζ bq
    have hA0 : AT.eval 0 = germFirst D embed ζ 0 + embed g * germFirst D embed ζ 1 := by
      simp [AT, A, germFirst, eval_taylor_zero, Polynomial.eval_map, specializeAffine]
    have hB0 : BT.eval 0 = germSecond D embed ζ 0 + embed (σ g) * germSecond D embed ζ 1 := by
      simp [BT, B, A, germSecond, eval_taylor_zero, Polynomial.eval_map, specializeAffine]
    have hBne : BT.eval 0 ≠ 0 := by
      simpa [BT, eval_taylor_zero, Polynomial.eval_map] using
        eval₂_ne_zero_of_coprime_root B D.d1 (D.coprime_denominator1 g hg) embed ζ hroot'
    have hD : Polynomial.taylor ζ d = Polynomial.X^(k+1) * Polynomial.taylor ζ dq := by
      rw [hdq, Polynomial.taylor_mul, Polynomial.taylor_pow, taylor_X_sub_center]
    have hB : Polynomial.taylor ζ b = Polynomial.X^k * Bq := by
      rw [hbq, Polynomial.taylor_mul, Polynomial.taylor_pow, taylor_X_sub_center]
    have heq : BT * Q = Polynomial.taylor ζ d *
        Polynomial.taylor ζ (((D.selected g).map σ.toRingHom).map embed) +
        Polynomial.C (embed (σ g)) * Polynomial.taylor ζ b := by
      have e := congrArg (fun P : Polynomial K => Polynomial.taylor ζ (P.map embed))
        (D.equation1 g hg)
      simpa [BT, B, A, Q, d, b, Polynomial.taylor_mul, Polynomial.taylor_C] using e
    let L := Polynomial.taylor ζ dq *
      Polynomial.taylor ζ (((D.selected g).map σ.toRingHom).map embed)
    have heq' : BT * Q = Polynomial.X^k * (Polynomial.X * L + Polynomial.C (embed (σ g)) * Bq) := by
      rw [heq,hD,hB,pow_succ]
      dsimp only [L]
      ring
    have hQdiv : (Polynomial.X : Polynomial E)^k ∣ Q :=
      ((coprime_X_of_constant_ne BT hBne).pow_left (m := k)).dvd_of_dvd_mul_left ⟨_,heq'⟩
    obtain ⟨Qq,hQq⟩ := hQdiv
    have hres : BT * Qq = Polynomial.X * L + Polynomial.C (embed (σ g)) * Bq := by
      apply mul_left_cancel₀ (pow_ne_zero k (Polynomial.X_ne_zero (R := E)))
      calc
        _ = BT * Q := by rw [hQq]; ring
        _ = _ := heq'
    have hres0 := congrArg (Polynomial.eval 0) hres
    have hres0' : BT.eval 0 * Qq.eval 0 = embed (σ g) * c := by
      simpa [c, Bq, eval_taylor_zero] using hres0
    refine ⟨AT * Qq, ?_, ?_⟩
    · have e := congrArg (fun P : Polynomial K => Polynomial.taylor ζ (P.map embed))
        (D.equation0 g hg)
      have hAQ : AT * Q = Polynomial.taylor ζ ((D.d0 * D.selected g +
          Polynomial.C g * D.C1).map embed) := by
        simpa [AT, A, Q, Polynomial.taylor_mul] using e
      rw [← hAQ, hQq]
      ring
    · rw [Polynomial.eval_mul, ← hA0, ← hB0]
      calc
        _ = AT.eval 0 * (BT.eval 0 * Qq.eval 0) := by ring
        _ = _ := by rw [hres0']; ring

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
