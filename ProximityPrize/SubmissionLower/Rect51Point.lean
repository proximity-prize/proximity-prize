import ProximityPrize.SubmissionLower.Rect51Hilbert
import ProximityPrize.SubmissionLower.Rect51HilbertProbe

/-! Rectangular two-chart point counting from the public kaankolcu note,
submission f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false
namespace Rect51Point
noncomputable section

open P1 (K)
open K1_14 (FX)
open HighCore82706Tangent_3 (JetRing seedVar)
open Rect51Hilbert
open MvPolynomial Finset
open scoped Polynomial BigOperators

private theorem affine_X_h₀ : dehom (MvPolynomial.X h₀) = 1 := by simp [dehom,affineCoord,h₀]
private theorem affine_X_v₀ : dehom (MvPolynomial.X v₀) = 1 := by simp [dehom,affineCoord,v₀]
private theorem affine_X_seed00 : dehom (MvPolynomial.X (seed₀ 0)) = 1 := by
  simp [dehom,affineCoord,seed₀]
private theorem affine_X_seed01 : dehom (MvPolynomial.X (seed₀ 1)) = seedVar 0 := by
  simp [dehom,affineCoord,seed₀,show (1:Fin 2)≠0 by decide]
private theorem affine_X_seed10 : dehom (MvPolynomial.X (seed₁ 0)) = 1 := by
  simp [dehom,affineCoord,seed₁]

private theorem mark_separator {U : Finset K} {ev : K → JetRing →ₐ[FX] FX}
    (hinj : Set.InjOn (fun γ => ev γ (seedVar 0)) (U : Set K))
    (h t s c : ℕ) (hs : U.card ≤ s) (γ : U) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (nefDegree h t s c) ∧
      ∀ η : U, ev η (dehom p) = if η = γ then 1 else 0 := by
  classical
  let E := (Finset.univ : Finset U).erase γ
  let sep (η : U) : Cox := MvPolynomial.X (seed₀ 1) - C (ev η (seedVar 0)) * MvPolynomial.X (seed₀ 0)
  have sep_eval (η θ : U) :
      ev η (dehom (sep θ)) = ev η (seedVar 0) - ev θ (seedVar 0) := by
    simp only [sep, map_sub, map_mul, affine_X_seed01, affine_X_seed00, mul_one]
    rw [show dehom (C (ev θ (seedVar 0))) = algebraMap FX JetRing (ev θ (seedVar 0)) by
      simp [dehom], (ev η.val).commutes]
    rfl
  let poly := ∏ η ∈ E, sep η
  have hγ : ev γ (dehom poly) ≠ 0 := by
    rw [show ev γ (dehom poly) = ∏ η ∈ E, ev γ (dehom (sep η)) by simp [poly, map_prod]]
    apply Finset.prod_ne_zero_iff.mpr
    intro η hη
    rw [sep_eval, sub_ne_zero]
    exact fun hEq => (Finset.mem_erase.mp hη).1 (Subtype.ext (hinj η.property γ.property hEq.symm))
  let pad : Cox := MvPolynomial.X h₀ ^ (h+2*t) * MvPolynomial.X v₀ ^ t * MvPolynomial.X (seed₀ 0) ^ (s-E.card) * MvPolynomial.X (seed₁ 0) ^ c
  let p := C (ev γ (dehom poly))⁻¹ * (poly * pad)
  have hhom (η : U) : (sep η).IsWeightedHomogeneous coxWeight (0,0,1,0) := by
    exact (isWeightedHomogeneous_X FX coxWeight (seed₀ 1)).sub
      ((isWeightedHomogeneous_X FX coxWeight (seed₀ 0)).C_mul _)
  have hsum : (∑ _η ∈ E, ((0,0,1,0) : Degree)) = (0,0,E.card,0) := by
    rw [Finset.sum_const]
    simp [Prod.smul_mk]
  have hpoly : poly.IsWeightedHomogeneous coxWeight (0,0,E.card,0) := by
    rw [← hsum]
    exact IsWeightedHomogeneous.prod E sep (fun _ => (0,0,1,0)) (fun η _ => hhom η)
  have hp := ((hpoly.mul (((isWeightedHomogeneous_X FX coxWeight h₀).pow (h+2*t)).mul
    ((isWeightedHomogeneous_X FX coxWeight v₀).pow t) |>.mul
    ((isWeightedHomogeneous_X FX coxWeight (seed₀ 0)).pow (s-E.card)) |>.mul
    ((isWeightedHomogeneous_X FX coxWeight (seed₁ 0)).pow c))).C_mul
    (ev γ (dehom poly))⁻¹)
  have hc : E.card ≤ s := (Finset.card_le_card (Finset.erase_subset _ _)).trans
    (by simpa only [Finset.card_univ, Fintype.card_coe] using hs)
  refine ⟨p, ?_, ?_⟩
  · have hdeg : (0, 0, E.card, 0) + ((h+2*t) • coxWeight h₀ +
        t • coxWeight v₀ + (s-E.card) • coxWeight (seed₀ 0) + c • coxWeight (seed₁ 0)) = nefDegree h t s c := by
      simp [coxWeight, h₀, v₀, seed₀, seed₁, nefDegree, Prod.smul_mk, Prod.mk_add_mk,
        Nat.add_sub_of_le hc]
    exact hdeg ▸ hp
  · intro η
    have hpad : dehom pad = 1 := by simp [pad, affine_X_h₀, affine_X_v₀, affine_X_seed00, affine_X_seed10]
    have hval : ev η (dehom p) = (ev γ (dehom poly))⁻¹ * ev η (dehom poly) := by
      simp only [p, map_mul, hpad, mul_one]
      rw [show dehom (C (ev γ (dehom poly))⁻¹) =
        algebraMap FX JetRing (ev γ (dehom poly))⁻¹ by simp [dehom],
        (ev η.val).commutes]
      rfl
    rw [hval]
    split_ifs with h
    · subst η
      exact inv_mul_cancel₀ hγ
    · have hη : η ∈ E := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      have hz : ev η (dehom poly) = 0 := by
        rw [show ev η (dehom poly) = ∏ θ ∈ E, ev η (dehom (sep θ)) by simp [poly, map_prod]]
        exact Finset.prod_eq_zero hη (by rw [sep_eval, sub_self])
      rw [hz, mul_zero]

theorem count_cox (Q : Ideal JetRing) (hQ : Q.IsPrime) (G : Probe Q) (h t s c : ℕ)
    (S : CoxSection Q (nefDegree h t s c)) (hS : S.affine ∉ Q)
    (U : Finset K) (ev : K → JetRing →ₐ[FX] FX)
    (hinj : Set.InjOn (fun γ => ev γ (seedVar 0)) (U : Set K))
    (hI : ∀ γ ∈ U, Q ≤ RingHom.ker (ev γ).toRingHom)
    (hz : ∀ γ ∈ U, ev γ S.affine = 0) :
    (U.card:ℚ) ≤ (h:ℚ)*G.coeff 0+(t:ℚ)*G.coeff 1+(s:ℚ)*G.coeff 2+(c:ℚ)*G.coeff 3 := by
  classical
  let N := G.threshold+2*S.order+U.card
  let A := gradedPiece Q (nefDegree N N N N)
  let B := gradedPiece Q (nefDegree (N+h) (N+t) (N+s) (N+c))
  let qev (γ : U) : JetRing ⧸ Q→ₐ[FX] FX :=
    Ideal.Quotient.liftₐ Q (ev γ) (hI γ γ.property)
  let E : B→ₗ[FX] (U→FX) :=
    LinearMap.pi fun γ=>(qev γ).toLinearMap.comp B.subtype
  have eval_mk (γ : U) (q : JetRing) : qev γ (Ideal.Quotient.mk Q q) = ev γ q := rfl
  have hsurj : Function.Surjective E := by
    have hlarge : U.card≤N+s := by dsimp only [N]; omega
    choose p hp he using fun γ : U => mark_separator hinj (N+h) (N+t) (N+s) (N+c) hlarge γ
    let v (γ : U) : B := ⟨qmap Q (p γ),Submodule.mem_map.mpr ⟨_,hp γ,rfl⟩⟩
    have hv (γ η : U) : E (v γ) η = if η=γ then 1 else 0 := by
      change qev η (Ideal.Quotient.mk Q (dehom (p γ))) = _
      rw [eval_mk]
      exact he γ η
    intro f
    refine ⟨∑ γ : U, f γ • v γ,?_⟩
    ext η
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv]
    simp
  let bySection := LinearMap.mulLeft FX (Ideal.Quotient.mk Q S.affine)
  have hto (a : A) : bySection a.val∈B := by
    have hn : 2*S.order≤N := by dsimp only [N]; omega
    have hh := relativeSection_mul_gradedPiece S (t:=N) (s₀:=N) (s₁:=N) hn a.property
    have heq : nefDegree N N N N + nefDegree h t s c =
        nefDegree (N+h) (N+t) (N+s) (N+c) := by
      simp only [nefDegree,Prod.mk_add_mk]
      congr 1
      ring
    rw [heq] at hh
    exact hh
  let M : A→ₗ[FX] B := (bySection.comp A.subtype).codRestrict B hto
  have hk (a : A) : M a∈LinearMap.ker E := by
    rw [LinearMap.mem_ker]
    ext γ
    change qev γ ((Ideal.Quotient.mk Q S.affine)*a.val) = 0
    rw [map_mul,eval_mk,hz γ γ.property,zero_mul]
  let MK := M.codRestrict (LinearMap.ker E) hk
  letI : Q.IsPrime := hQ
  have hmk : Ideal.Quotient.mk Q S.affine≠0 := fun h0=>hS (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hminj : Function.Injective MK := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel₀ hmk
    exact congrArg (fun x : LinearMap.ker E=>x.val.val) hab
  have hd := LinearMap.finrank_le_finrank_of_injective hminj
  have hr := E.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at hr
  have hg : G.threshold≤N := by dsimp only [N]; omega
  have hA := G.profile N N N N hg hg hg hg
  have hB := G.profile (N+h) (N+t) (N+s) (N+c)
    (hg.trans (Nat.le_add_right _ _)) (hg.trans (Nat.le_add_right _ _))
    (hg.trans (Nat.le_add_right _ _)) (hg.trans (Nat.le_add_right _ _))
  have hdim : U.card + Module.finrank FX A ≤ Module.finrank FX B :=
    (Nat.add_le_add_left hd _).trans_eq hr
  have hcast := (Nat.cast_le (α:=ℚ)).mpr hdim
  change ((U.card+hilbert Q N N N N:ℕ):ℚ)≤hilbert Q (N+h) (N+t) (N+s) (N+c) at hcast
  rw [Nat.cast_add,hA,hB] at hcast
  push_cast at hcast
  linarith only [hcast,add_mul (N:ℚ) (h:ℚ) (G.coeff 0),add_mul (N:ℚ) (t:ℚ) (G.coeff 1),
    add_mul (N:ℚ) (s:ℚ) (G.coeff 2),add_mul (N:ℚ) (c:ℚ) (G.coeff 3)]

theorem count_relative_section (Q : Ideal JetRing) (hQ : Q.IsPrime) (G : Probe Q)
    {h t : ℕ} {v : Rect51Tangent.Axes} (S : Rect51Tangent.Section Q h t v) (hS : S.affine ∉ Q)
    (U : Finset K) (ev : K → JetRing →ₐ[FX] FX)
    (hinj : Set.InjOn (fun γ => ev γ (seedVar 0)) (U : Set K))
    (hI : ∀ γ ∈ U, Q ≤ RingHom.ker (ev γ).toRingHom)
    (hz : ∀ γ ∈ U, ev γ S.affine = 0) :
    (U.card:ℚ) ≤ G.mass h t (v 0) (v 1) := by
  obtain ⟨A,hA,eA⟩ := lift S.affine_bound S.affine_weight
  obtain ⟨B,hB,eB⟩ := lift S.inverse_bound S.inverse_weight
  have eq : nefDegree h t (v 0) (v 1)+S.order • (1,0,0,0) = (h+2*t+S.order,t,v 0,v 1) := by
    simp [nefDegree,Prod.mk_add_mk,Prod.smul_mk]
  let T : CoxSection Q (nefDegree h t (v 0) (v 1)) :=
    ⟨S.order,A,B,by rw [eq]; exact hA,by rw [eq]; exact hB,by rw [eA,eB]; exact S.glue⟩
  have he : T.affine=S.affine := eA
  exact count_cox Q hQ G h t (v 0) (v 1) T (he.symm ▸ hS) U ev hinj hI (fun γ hγ=>he.symm ▸ hz γ hγ)

#print axioms count_relative_section
end
end Rect51Point
