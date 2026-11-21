import ProximityPrize.SubmissionLower.Rect51MixedPoly
import ProximityPrize.SubmissionLower.Rect51Hilbert
import ProximityPrize.SubmissionLower.Rect51TangentTaylor
import ProximityPrize.SubmissionLower.Rect51TangentGraph

/-! Rectangular single-cut estimate based on the public kaankolcu 69.50 note,
submission f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
namespace Rect51Budget
noncomputable section

open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing rootIdeal graphIdeal tangentEquation)
open Rect51Tangent (SeedBound Axes Section TaylorSections baseDegree taylorAxis)
open Rect51MixedPoly (diagonal directionalCoeff rootDirection tangentDirection)
open scoped Polynomial

def sectionIdeal {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (T : TaylorSections J B D v (J.ell+1)) : Ideal JetRing :=
  graphIdeal J B D ⊔ Ideal.span {(T.numerator (Fin.last (J.ell+1))).affine}

def feeAxis (J : Input) (v : Axes) (r : ℕ) : Fin 4→ℕ :=
  ![baseDegree J r,r,taylorAxis J v r 0,taylorAxis J v r 1]

theorem feeAxis_le (J : Input) {v : Axes} {r b c k : ℕ}
    (he : 4≤J.e) (hb : v 0≤b) (hc : v 1≤c) (hk : 0<k)
    (h0 : 2*J.w≤k*b) (h1 : 2*J.w≤k*c) :
    ∀ i, feeAxis J v r i≤(r+k)*diagonal J.e b c i := by
  intro i
  fin_cases i
  · change 1+(J.e-3)*r≤(r+k)*(J.e-3)
    have hh := Nat.mul_le_mul (show 1≤k by omega) (show 1≤J.e-3 by omega)
    rw [Nat.add_mul,Nat.mul_comm r]
    omega
  · change r≤(r+k)*1
    omega
  · change r*v 0+2*J.w≤(r+k)*b
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hb) h0
  · change r*v 1+2*J.w≤(r+k)*c
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hc) h1

theorem cut_profile (J : Input) (B : ResidueLift J) (D : Factors J B) {v : Axes}
    (he : 4≤J.e) (hf : SeedBound J.f v) (T : TaylorSections J B D v (J.ell+1)) (b c : ℕ) :
    ∃ p, Rect51Hilbert.IsProfile (sectionIdeal T) p ∧ Rect51Hilbert.NonnegativeTop p ∧
      p.totalDegree≤1 ∧ ∃ offset : ℚ, ∀ n : ℕ,
        MvPolynomial.eval (fun i=>(n:ℚ)*(diagonal J.e b c i:ℚ)) p ≤
          n*directionalCoeff J.e (v 0) (v 1) b c (fun i=>feeAxis J v (J.ell+1) i)+offset := by
  let S := T.numerator (Fin.last (J.ell+1))
  obtain ⟨F,G,hF,hG,_⟩ := Rect51Tangent.graph_sections J B D hf
  obtain ⟨p₁,hp₁,hp₁t⟩ := Rect51Hilbert.profile_exists (rootIdeal D)
  obtain ⟨p₂,hp₂,hp₂t⟩ := Rect51Hilbert.profile_exists (graphIdeal J B D)
  obtain ⟨p₃,hp₃,hp₃t⟩ := Rect51Hilbert.profile_exists (sectionIdeal T)
  have hFne : F.affine≠0 := by
    rw [hF]
    exact Polynomial.C_ne_zero.mpr (HighCore82706Tangent_3_2.proper_ne_zero D)
  have hFreg : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal JetRing) F.affine) := by
    letI : (⊥ : Ideal JetRing).IsPrime := Ideal.isPrime_bot
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hFne
  have hFmem : F.affine∈rootIdeal D := by rw [hF]; exact Ideal.subset_span (Set.mem_singleton _)
  have d₁ := Rect51Hilbert.cut_gap F bot_le hFmem hFreg Rect51Hilbert.ambient_profile hp₁
  obtain ⟨hGreg,hSreg⟩ := Rect51Tangent.regular_graph_cut T
  have gh : rootIdeal D≤graphIdeal J B D := by
    rw [rootIdeal,Ideal.span_singleton_le_iff_mem]
    exact HighCore82706Tangent_3.proper_mem_graph J B D
  have hGmem : G.affine∈graphIdeal J B D := by
    rw [hG]
    exact HighCore82706Tangent_3.le_saturate _ _ (Ideal.subset_span (by simp))
  have d₂ := Rect51Hilbert.cut_gap G gh hGmem (hG.symm ▸ hGreg) hp₁ hp₂
  have hSspan : Ideal.span {S.affine}≤sectionIdeal T := le_sup_right
  have hSmem := hSspan (Ideal.subset_span (Set.mem_singleton S.affine))
  have d₃ := Rect51Hilbert.cut_gap S (show graphIdeal J B D≤sectionIdeal T from le_sup_left)
    hSmem hSreg hp₂ hp₃
  let a := feeAxis J v (J.ell+1)
  let q := Rect51MixedPoly.difference (Rect51MixedPoly.difference
    (Rect51MixedPoly.difference Rect51MixedPoly.ambient (rootDirection J.e (v 0) (v 1)))
    (tangentDirection J.e (v 0) (v 1))) a
  have htop : p₃.totalDegree≤1 ∧ Rect51MixedPoly.Top 1 (q-p₃) :=
    Rect51MixedPoly.three_cut_top _ p₁ p₂ p₃ _ _ _ Rect51MixedPoly.ambient_degree hp₁t hp₂t hp₃t d₁ d₂ d₃
  refine ⟨p₃,hp₃,hp₃t,htop.1,MvPolynomial.eval 0 q-(q-p₃).coeff 0,fun n=>?_⟩
  have hk := Rect51MixedPoly.constant_le_eval_of_top (q-p₃) htop.2
    (x:=fun i=>(n:ℚ)*(diagonal J.e b c i:ℚ)) (fun i=>by positivity)
  rw [map_sub] at hk
  have hq : MvPolynomial.eval (fun i=>(n:ℚ)*(diagonal J.e b c i:ℚ)) q =
      n*directionalCoeff J.e (v 0) (v 1) b c (fun i=>a i)+MvPolynomial.eval 0 q :=
    Rect51MixedPoly.directional_eq J.e (v 0) (v 1) b c (by omega) a n
  linarith only [hk,hq]

#print axioms cut_profile
end
end Rect51Budget
