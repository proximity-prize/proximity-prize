import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_8Defs
set_option autoImplicit true
namespace K21_8

noncomputable section

open Polynomial K21

/-- A generic rank-three dependence with both amplitude contents removed.
Beta is recorded before coefficient Frobenius. The two remaining scalar
X-contents have also been made coprime. -/
structure AmplitudeDirection (U V : Bivar) where
  α : Fin 2 → K[X]
  β : Fin 2 → K[X]
  a : K[X]
  b : K[X]
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  scalar_coprime : IsCoprime a b
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  direction : sameDirection U V (threeU a β) (threeV b α)

end

end K21_8
end Port_K1_8Defs

section Port_K1_8Exponent
set_option autoImplicit true
-- Parameterized definitions are declared alongside K1Defs.
end Port_K1_8Exponent

section Port_K1_8Puncture
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_8

noncomputable section

open Polynomial K21 FrobeniusLocator ProximityPrize.Benchmark

def seedInclusion : K[X] →+* Frac := algebraMap K[X] Frac

theorem seedInclusion_injective : Function.Injective seedInclusion :=
  IsFractionRing.injective K[X] Frac

theorem extendSeed_injective : Function.Injective extendSeed :=
  Polynomial.map_injective seedInclusion seedInclusion_injective

theorem mem_fixed_iff {u : Words} {T : TwoActive u} (R : Relation T) (i : I) :
    i ∈ fixedNodes R ↔ (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0 := by
  classical
  simp [fixedNodes]

theorem eval_liftX (f : K[X]) (x : K) : (liftX f).eval (C x) = C (f.eval x) := by
  simp [liftX, eval_map]

theorem lift_locator_dvd (S : Finset I) (P : Bivar)
    (hz : ∀ i ∈ S, P.eval (C (node i)) = 0) : liftX (locator node S) ∣ P := by
  classical
  apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective
    ((locator_monic node S).map Polynomial.C)).mp
  rw [Polynomial.map_map, locator_map]
  apply Strata.locator_dvd_of_eval_zero _
    ((seedInclusion_injective.comp Polynomial.C_injective).comp IRSProfile.domain.injective)
  intro i hi
  change (P.map seedInclusion).eval (seedInclusion (C (node i))) = 0
  rw [Polynomial.eval_map_apply, hz i hi, map_zero]

theorem coprime_after_factor (G A B : Frac[X])
    (hg : G ≠ 0) (ha : A ≠ 0) (hmax : ∀ D, D ∣ G * A → D ∣ G * B → D ∣ G) :
    IsCoprime A B := by
  classical
  apply EuclideanDomain.isCoprime_of_dvd (fun h => ha h.1)
  intro d hnonunit _ hda hdb
  obtain ⟨q, hq⟩ := hmax (G * d) (mul_dvd_mul_left G hda) (mul_dvd_mul_left G hdb)
  have heq : 1 = d * q := mul_left_cancel₀ hg (by
    calc
      G * 1 = G := mul_one _
      _ = (G * d) * q := hq
      _ = G * (d * q) := mul_assoc _ _ _)
  exact hnonunit (isUnit_iff_dvd_one.mpr ⟨q, heq⟩)

private theorem certificate_output_zero {F ι : Type} [Field F] {q k H : ℕ} {x a b : ι → F}
    (R : Strata.PolynomialRelationCertificate q x a b k H) (i : ι)
    (hU : (Principal.assemble (fun j => R.coefficients (0, j))).eval (C (x i)) = 0)
    (hV : (Principal.assemble (fun j => R.coefficients (1, j))).eval (C (x i)) = 0) :
    R.output.eval (C (x i)) = 0 := by
  simpa only [hU, hV, zero_mul, zero_add] using (R.nodes i).symm

theorem puncture {u : Words} {T : TwoActive u} (R : Relation T)
    (hs : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ))
    (hgcd : IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R))) : Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
  have h := hs γ hγ M
  let B := fixedNodes R
  let G := liftX (locator node B)
  have hG : G.Monic := (locator_monic node B).map Polynomial.C
  have hGd : G.natDegree = B.card := by
    change ((locator node B).map Polynomial.C).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, locator_natDegree]
  obtain ⟨U, hU⟩ := lift_locator_dvd B (leftU R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).1)
  obtain ⟨V, hV⟩ := lift_locator_dvd B (leftV R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).2)
  obtain ⟨W, hW⟩ := lift_locator_dvd B R.output (fun i hi => by
    have hroot := (mem_fixed_iff R i).mp hi
    exact certificate_output_zero R i hroot.1 hroot.2)
  have hu : U ≠ 0 := by
    intro hz
    apply h.U_ne
    rw [hU, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hv : V ≠ 0 := by
    intro hz
    apply h.V_ne
    rw [hV, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hdeg : max (leftU R).natDegree (leftV R).natDegree = T.height := by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact Nat.le_of_not_gt fun hlt => h.valid (Or.inl hlt)
  have hdu := congrArg Polynomial.natDegree hU
  have hdv := congrArg Polynomial.natDegree hV
  change (leftU R).natDegree = (G * U).natDegree at hdu
  change (leftV R).natDegree = (G * V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu, hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv, hGd] at hdv
  let H := max U.natDegree V.natDegree
  have hH : H + B.card = T.height := by
    dsimp [H]
    omega
  have hout : W.degree < (131072 + H : ℕ) := by
    by_cases hzero : W = 0
    · rw [hzero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout : R.output ≠ 0 := by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd := (natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G * W).natDegree < _ at hd
    rw [natDegree_mul hG.ne_zero hzero, hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop : IsCoprime (extendSeed U) (extendSeed V) := by
    apply coprime_after_factor (extendSeed G) _ _ hgcd.1
      (fun hz => hu (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · simpa only [hU, extendSeed, Polynomial.map_mul] using hqu
    · simpa only [hV, extendSeed, Polynomial.map_mul] using hqv
  exact ⟨⟨U, V, W, H, hH, rfl, hu, hv, hcop, hU, hV, hW, hout,
    fun γ hn M => (hs γ hn M).fixed_errors⟩⟩


end

end K21_8
end Port_K1_8Puncture

section Port_K1_8NodeTransfer
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_8

noncomputable section

open Polynomial K21 FrobeniusLocator

/-- The certificate uses the field instance's power. The benchmark also
has a separate concrete power instance, implemented by repeated squaring. -/
private def fieldPower {F : Type*} [Field F] (x : F) (n : ℕ) : F := x ^ n

private theorem fieldPower_zero {F : Type*} [Field F] (x : F) :
    fieldPower x 0 = 1 := pow_zero x

private theorem fieldPower_succ {F : Type*} [Field F] (x : F) (n : ℕ) :
    fieldPower x (n + 1) = fieldPower x n * x := pow_succ x n

private theorem native_field_power (x : K) (n : ℕ) : fieldPower x n = x ^ n := by
  rw [CompPoly.Extension.Ext.pow_def]
  induction n with
  | zero => rw [fieldPower_zero, npowBinRec_zero]
  | succ n ih => rw [fieldPower_succ, npowBinRec_succ, ih]

private theorem native_nodes {q k H : ℕ} {x a b : I → K}
    (R : Strata.PolynomialRelationCertificate q x a b k H) (i : I) :
    (Principal.assemble (fun j => R.coefficients (0, j))).eval (C (x i)) *
        (C (a i) + Polynomial.X (R := K) * C (b i)) +
      (Principal.assemble (fun j => R.coefficients (1, j))).eval (C (x i)) *
        (C (a i ^ q) + Polynomial.X (R := K) ^ q * C (b i ^ q)) =
      R.output.eval (C (x i)) := by
  rw [← native_field_power (a i) q, ← native_field_power (b i) q]
  unfold fieldPower
  exact R.nodes i

private theorem cancel_and_scale {A : Type*} [CommRing A] [IsDomain A]
    {g U V W a b e : A} (hg : g ≠ 0)
    (h : (g * U) * a + (g * V) * b = g * W) : (e * U) * a + (e * V) * b = e * W := by
  have h₀ : U * a + V * b = W :=
    mul_left_cancel₀ hg (by simpa only [mul_add, mul_assoc] using h)
  simpa only [mul_add, mul_assoc] using congrArg (fun t => e * t) h₀

private theorem transfer_at {u : Words} {q k H : ℕ}
    (R : Strata.PolynomialRelationCertificate q node (u 0) (u 1) k H)
    (S : Finset I) (G U V W : Bivar)
    (hG : ∀ i ∉ S, G.eval (C (node i)) ≠ 0)
    (hU : Principal.assemble (fun j => R.coefficients (0, j)) = G * U)
    (hV : Principal.assemble (fun j => R.coefficients (1, j)) = G * V)
    (hW : R.output = G * W) (e : K[X]) :
    relationOnAt q u S (C e * U) (C e * V) (C e * W) := by
  intro i hi
  have hn := @native_nodes q k H node (u 0) (u 1) R i
  simp only [hU, hV, hW, eval_mul] at hn
  simpa only [eval_mul, eval_C] using
    (cancel_and_scale (e := e) (hG i hi) hn)

theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : K[X]) :
    relationOn u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output) := by
  let G := liftX (locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (C (node i)) ≠ 0 := by
    intro i hi
    change (liftX (locator node (fixedNodes R))).eval (C (node i)) ≠ 0
    rw [eval_liftX, C_ne_zero]
    exact fun hz => hi ((Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  change relationOnAt p u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output)
  exact @transfer_at u p 131072 T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e

end

end K21_8
end Port_K1_8NodeTransfer

section Port_K1_8RankThree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 850000

namespace K21_8

noncomputable section

open Polynomial K21 FrobeniusLocator

def extendSeedHom : Bivar →+* Frac[X] := Polynomial.mapRingHom seedInclusion

private theorem liftX_degree (P : K[X]) : (liftX P).natDegree = P.natDegree :=
  natDegree_map_eq_of_injective Polynomial.C_injective P

private theorem seed_pow_height (n : ℕ) : (seed ^ n).natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact natDegree_pow_le.trans (by simp [seed])

private theorem two_term_height (P Q : K[X]) (n : ℕ) :
    (liftX P + seed ^ n * liftX Q).natDegree ≤ amplitudeDegree P Q := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · rw [liftX_degree]
    exact le_max_left _ _
  · apply natDegree_mul_le.trans
    rw [seed_pow_height, zero_add, liftX_degree]
    exact le_max_right _ _

private theorem threeU_height_at (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    (threeUAt q a β).natDegree ≤ a.natDegree + amplitudeDegree (β 0) (β 1) := by
  unfold threeUAt
  apply natDegree_mul_le.trans
  rw [liftX_degree]
  apply Nat.add_le_add_left
  exact (two_term_height _ _ q).trans
    (max_le_max natDegree_map_le natDegree_map_le)

private theorem threeUAt_native : threeUAt p = (threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt threeU
  rfl

private theorem threeU_height (a : K[X]) (β : Fin 2 → K[X]) :
    (threeU a β).natDegree ≤ a.natDegree + amplitudeDegree (β 0) (β 1) := by
  rw [← threeUAt_native]
  exact threeU_height_at p a β

private theorem threeV_height (b : K[X]) (α : Fin 2 → K[X]) :
    (threeV b α).natDegree ≤ b.natDegree + amplitudeDegree (α 0) (α 1) := by
  unfold threeV
  rw [natDegree_neg]
  apply natDegree_mul_le.trans
  rw [liftX_degree]
  apply Nat.add_le_add_left
  simpa only [pow_one] using two_term_height (α 0) (α 1) 1

private theorem common_multiplier {L : Type*} [CommRing L] {A B P Q : L}
    (hcop : IsCoprime A B) (hcross : A * Q = B * P) :
    ∃ E, P = E * A ∧ Q = E * B := by
  obtain ⟨r, t, hbez⟩ := hcop
  refine ⟨r * P + t * Q, ?_, ?_⟩
  · calc
      P = (r * A + t * B) * P := by rw [hbez, one_mul]
      _ = r * (A * P) + t * (B * P) := by ring
      _ = r * (A * P) + t * (A * Q) := by rw [hcross]
      _ = (r * P + t * Q) * A := by ring
  · calc
      Q = (r * A + t * B) * Q := by rw [hbez, one_mul]
      _ = r * (A * Q) + t * (B * Q) := by ring
      _ = r * (B * P) + t * (B * Q) := by rw [hcross]
      _ = (r * P + t * Q) * B := by ring

private theorem multiplier_degree_zero {A B P Q E : Frac[X]} {H : ℕ}
    (ha : A ≠ 0) (hb : B ≠ 0) (hp : P = E * A) (hq : Q = E * B)
    (hmax : max A.natDegree B.natDegree = H)
    (hpd : P.natDegree ≤ H) (hqd : Q.natDegree ≤ H) : E.natDegree = 0 := by
  by_cases he : E = 0
  · simp [he]
  rw [hp, natDegree_mul he ha] at hpd
  rw [hq, natDegree_mul he hb] at hqd
  omega

private theorem seed_scalar_coeff {P Q : Bivar} {s : Frac} (j : ℕ)
    (h : extendSeedHom P = C s * extendSeedHom Q) :
    seedInclusion (P.coeff j) = s * seedInclusion (Q.coeff j) := by
  have hc := congrArg (fun F : Frac[X] => F.coeff j) h
  change (P.map seedInclusion).coeff j = (C s * Q.map seedInclusion).coeff j at hc
  simpa only [coeff_C_mul, coeff_map] using hc

private theorem descend_scalar {ι : Type*} [Fintype ι]
    (A B : ι → K[X]) (hprim : PrimitiveVector.IsPrimitive A) (s : Frac)
    (hB : ∀ i, seedInclusion (B i) = s * seedInclusion (A i)) :
    ∃ e : K[X], seedInclusion e = s := by
  obtain ⟨w, hw⟩ := (PrimitiveVector.primitive_iff_bezout A).mp hprim
  refine ⟨∑ i, w i * B i, ?_⟩
  calc
    seedInclusion (∑ i, w i * B i) =
        ∑ i, seedInclusion (w i) * (s * seedInclusion (A i)) := by
      simp only [map_sum, map_mul, hB]
    _ = s * ∑ i, seedInclusion (w i) * seedInclusion (A i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = s * seedInclusion (∑ i, w i * A i) := by simp only [map_sum, map_mul]
    _ = s := by rw [hw, map_one, mul_one]

/-- A bounded canonical direction differs from the reduced relation by a
polynomial in the seed alone. The Bezout identity comes from the original
seed-primitive certificate, before the fixed locator was removed. -/
theorem seed_multiplier {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ e : K[X], P = C e * D.U ∧ Q = C e * D.V := by
  have hext (F : Bivar) : (extendSeedHom F).natDegree = F.natDegree :=
    natDegree_map_eq_of_injective seedInclusion_injective F
  have hne (F : Bivar) (hF : F ≠ 0) : extendSeedHom F ≠ 0 :=
    fun hz => hF (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm))
  have hxy : extendSeedHom D.U * extendSeedHom Q = extendSeedHom D.V * extendSeedHom P := by
    have h := congrArg extendSeedHom hcross
    simpa only [map_mul] using h
  have hcop : IsCoprime (extendSeedHom D.U) (extendSeedHom D.V) := D.coprime
  obtain ⟨E, heP, heQ⟩ := common_multiplier hcop hxy
  have hEd := multiplier_degree_zero (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s := E.coeff 0
  have hE : E = C s := eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G := liftX (locator node (fixedNodes R))
  have hLeftU : extendSeedHom (G * P) = C s * extendSeedHom (leftU R) := by
    rw [D.U_factor]
    change extendSeedHom (G * P) = C s * extendSeedHom (G * D.U)
    rw [map_mul, map_mul, heP]
    ac_rfl
  have hLeftV : extendSeedHom (G * Q) = C s * extendSeedHom (leftV R) := by
    rw [D.V_factor]
    change extendSeedHom (G * Q) = C s * extendSeedHom (G * D.V)
    rw [map_mul, map_mul, heQ]
    ac_rfl
  let F : Fin 2 → Bivar := ![G * P, G * Q]
  let A : Fin 2 × Fin (T.height + 1) → K[X] :=
    fun j => (F j.1).coeff j.2.val
  have hA : ∀ j, seedInclusion (A j) = s * seedInclusion (R.coefficients j) := by
    rintro ⟨i, j⟩
    fin_cases i
    · have hc := seed_scalar_coeff j.val hLeftU
      rw [leftU, Principal.assemble_coeff] at hc
      exact hc
    · have hc := seed_scalar_coeff j.val hLeftV
      rw [leftV, Principal.assemble_coeff] at hc
      exact hc
  obtain ⟨e, he⟩ := descend_scalar R.coefficients A R.primitive s hA
  have hmapC : extendSeedHom (C e) = C s := by
    change (C e).map seedInclusion = C s
    rw [Polynomial.map_C, he]
  refine ⟨e, extendSeed_injective ?_, extendSeed_injective ?_⟩
  · change extendSeedHom P = extendSeedHom (C e * D.U)
    rw [map_mul, hmapC, heP]
  · change extendSeedHom Q = extendSeedHom (C e * D.V)
    rw [map_mul, hmapC, heQ]

theorem canonical_output {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ W : Bivar, W.degree < (131072 + D.height : ℕ) ∧ relationOn u (fixedNodes R) P Q W := by
  obtain ⟨e, rfl, rfl⟩ := seed_multiplier D P Q hcross hp hq
  refine ⟨C e * D.output, ?_, ?_⟩
  · have hdeg : (C e * D.output).degree ≤ D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact reduced_scaled_relation D e

private theorem proportional_amplitudes {α β : Fin 2 → K[X]}
    (ha : IsCoprime (α 0) (α 1)) (hb : IsCoprime (β 0) (β 1))
    (hd : α 0 * β 1 = α 1 * β 0) :
    ∃ t : K, t ≠ 0 ∧ ∀ i, β i = C t * α i := by
  obtain ⟨c, h0, h1⟩ := common_multiplier (A := α 0) (B := α 1) ha hd
  obtain ⟨r, s, h⟩ := hb
  have hunit : IsUnit c := isUnit_iff_dvd_one.mpr ⟨r * α 0 + s * α 1, by
    calc
      1 = r * β 0 + s * β 1 := h.symm
      _ = c * (r * α 0 + s * α 1) := by rw [h0, h1]; ring⟩
  have hc : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hunit)
  refine ⟨c.coeff 0, ?_, ?_⟩
  · intro hz
    apply hunit.ne_zero
    rw [hc, hz, C_0]
  · intro i
    fin_cases i
    · change β 0 = C (c.coeff 0) * α 0
      exact h0.trans (congrArg (fun z => z * α 0) hc)
    · change β 1 = C (c.coeff 0) * α 1
      exact h1.trans (congrArg (fun z => z * α 1) hc)

private theorem rescale_at (q : ℕ) (a : K[X]) (α β : Fin 2 → K[X]) (t : K)
    (heq : ∀ i, (β i).map twist = C t * (α i).map twist) :
    threeUAt q (a * C t) α = threeUAt q a β := by
  simp only [threeUAt, heq, liftX, Polynomial.map_mul, Polynomial.map_C]
  ring

private theorem rescale_threeU (a : K[X]) (α β : Fin 2 → K[X]) (t : K)
    (heq : ∀ i, (β i).map twist = C t * (α i).map twist) :
    threeU (a * C t) α = threeU a β := by
  rw [← threeUAt_native]
  exact rescale_at p a α β t heq

theorem rank_three_branch {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (hr : columnRank D.U D.V = 3) (S : AmplitudeDirection D.U D.V)
    (ha : S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ D.height)
    (hb : S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height) :
    ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  obtain ⟨W, hW, hnodes⟩ := canonical_output D _ _ S.direction
    ((threeU_height _ _).trans ha) ((threeV_height _ _).trans hb)
  by_cases hd : S.α 0 * S.β 1 - S.α 1 * S.β 0 = 0
  · obtain ⟨t, ht, htβ⟩ := proportional_amplitudes S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ : twist t ≠ 0 := fun hz => ht (twist.injective (hz.trans (map_zero twist).symm))
    let a := S.a * C (twist t)
    have heq (i : Fin 2) : (S.β i).map twist = C (twist t) * (S.α i).map twist := by
      rw [htβ i, Polynomial.map_mul, Polynomial.map_C]
    have hU : threeU a S.α = threeU S.a S.β := rescale_threeU S.a S.α S.β (twist t) heq
    have hdeg (i : Fin 2) : (S.β i).natDegree = (S.α i).natDegree := by
      rw [htβ i, natDegree_C_mul ht]
    have ha' : a.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height := by
      simpa only [a, natDegree_mul_C htσ, amplitudeDegree, hdeg] using ha
    have hdir : sameDirection D.U D.V (threeU a S.α) (threeV S.b S.α) := by
      rw [hU]
      exact S.direction
    have hn : relationOn u (fixedNodes R) (threeU a S.α) (threeV S.b S.α) W := by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr, S.α, S.α, a, S.b, mul_ne_zero S.a_ne (C_ne_zero.mpr htσ), S.b_ne,
      S.α_primitive, S.α_primitive, ha', hb, hdir, W, hW, hn⟩, Or.inr rfl⟩
  · exact ⟨⟨hr, S.α, S.β, S.a, S.b, S.a_ne, S.b_ne,
      S.α_primitive, S.β_primitive, ha, hb, S.direction, W, hW, hnodes⟩, Or.inl hd⟩

end

end K21_8
end Port_K1_8RankThree

section Port_K1_8ColumnRank
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_8

noncomputable section

open Polynomial K21

private def fourColumns {F : Type*} [Field F] (A B : F[X]) (p : ℕ) : Fin 4 → F[X] :=
  ![A, (Polynomial.X (R := F)) * A, B, (Polynomial.X (R := F)) ^ p * B]

private theorem first_pair_independent {F : Type*} [Field F] (A : F[X]) (hA : A ≠ 0) :
    LinearIndependent F ![A, (Polynomial.X (R := F)) * A] := by
  apply linearIndependent_fin2.mpr
  refine ⟨mul_ne_zero X_ne_zero hA, ?_⟩
  intro c hc
  change c • ((Polynomial.X (R := F)) * A) = A at hc
  rw [smul_eq_C_mul, ← mul_assoc] at hc
  have h : C c * (Polynomial.X (R := F)) = 1 := mul_right_cancel₀ hA (hc.trans (one_mul _).symm)
  have hc₀ := congrArg (fun Q : F[X] => Q.coeff 0) h
  simp only [coeff_C_mul, coeff_X_zero, mul_zero, coeff_one_zero, zero_ne_one] at hc₀

private theorem span_degree_interval {F : Type*} [Field F] {A W : F[X]}
    (hA : A ≠ 0) (hW : W ≠ 0) (hm : W ∈ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])) :
    A.natDegree ≤ W.natDegree ∧ W.natDegree ≤ A.natDegree + 1 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hm
  have h : C (c 0) * A + C (c 1) * ((Polynomial.X (R := F)) * A) = W := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_C_mul] using hc
  let P := C (c 0) + C (c 1) * (Polynomial.X (R := F))
  have hW' : W = P * A := by rw [← h]; dsimp [P]; ring
  have hP : P ≠ 0 := fun hz => hW (by rw [hW', hz, zero_mul])
  have hPd : P.natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    exact max_le (by simp) (natDegree_mul_le.trans (by simp))
  have he := congrArg Polynomial.natDegree hW'
  rw [natDegree_mul hP hA] at he
  omega

private theorem lower_of_extra_column {F : Type*} [Field F] (A B : F[X]) (p : ℕ)
    (hA : A ≠ 0) (j : Fin 4)
    (hj : fourColumns A B p j ∉ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])) :
    3 ≤ Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) := by
  let f : Fin 3 → F[X] := Fin.snoc ![A, (Polynomial.X (R := F)) * A] (fourColumns A B p j)
  have hf : LinearIndependent F f := linearIndependent_finSnoc.mpr ⟨first_pair_independent A hA, hj⟩
  have hs : Set.range f ⊆ Set.range (fourColumns A B p) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨j, rfl⟩
  have := Module.Finite.span_of_finite F (Set.finite_range (fourColumns A B p))
  have hd := Submodule.finrank_mono (R := F) (Submodule.span_mono hs)
  simpa only [finrank_span_eq_card hf, Fintype.card_fin] using hd

private theorem three_or_four_of_columns {F : Type*} [Field F] (A B : F[X]) (p : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hp : 1 < p) :
    Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) = 4 ∨
      Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) = 3 := by
  have hle : Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) ≤ 4 := by
    simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := F) (fourColumns A B p)
  have hge : 3 ≤ Module.finrank F (Submodule.span F (Set.range (fourColumns A B p))) := by
    by_cases hm : B ∈ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])
    · apply lower_of_extra_column A B p hA 3
      change (Polynomial.X (R := F)) ^ p * B ∉ Submodule.span F (Set.range ![A, (Polynomial.X (R := F)) * A])
      intro hpow
      have hne : (Polynomial.X (R := F)) ^ p * B ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hB
      have hBdeg := (span_degree_interval hA hB hm).1
      have hpowdeg := (span_degree_interval hA hne hpow).2
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hB, (monic_X (R := F)).natDegree_pow,
        natDegree_X, Nat.mul_one] at hpowdeg
      omega
    · exact lower_of_extra_column A B p hA 2 hm
  omega

private theorem column_family (U V : Bivar) (q : ℕ) :
    (fun j : Fin 4 => extendSeed (Bivariate.swap
      (if j = 0 then U else if j = 1 then seed * U else if j = 2 then V else seed ^ q * V))) =
    fourColumns (extendSeed (Bivariate.swap U)) (extendSeed (Bivariate.swap V)) q := by
  funext j
  fin_cases j <;> simp [fourColumns, seed, Bivariate.swap_X, extendSeed, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X]

private theorem rank_cases_at (q : ℕ) (hq : 1 < q)
    (U V : Bivar) (hu : U ≠ 0) (hv : V ≠ 0) :
    columnRankAt q U V = 4 ∨ columnRankAt q U V = 3 := by
  let A := extendSeed (Bivariate.swap U)
  let B := extendSeed (Bivariate.swap V)
  have hs (W : Bivar) (hn : W ≠ 0) : extendSeed (Bivariate.swap W) ≠ 0 := by
    intro h
    apply hn
    apply (Bivariate.swap (R := K)).injective
    apply extendSeed_injective
    simpa only [map_zero, extendSeed, Polynomial.map_zero] using h
  unfold columnRankAt
  rw [column_family]
  exact three_or_four_of_columns A B q (hs U hu) (hs V hv) hq

theorem rank_cases (U V : Bivar) (hu : U ≠ 0) (hv : V ≠ 0) :
    columnRank U V = 4 ∨ columnRank U V = 3 :=
  rank_cases_at p (by decide) U V hu hv

end

end K21_8
end Port_K1_8ColumnRank

section Port_K1_8Fixed
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace K21_8

noncomputable section

open Polynomial K21 FrobeniusLocator ProximityPrize.Benchmark

private def constantsInFrac : K →+* Frac :=
  seedInclusion.comp Polynomial.C

private theorem extend_liftX (G : K[X]) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G

private theorem fixed_case_maximal {u : Words} {T : TwoActive u} (R : Relation T)
    (hi : ¬ InvalidLeft R) (hf : FixedLeftGCD R) :
    ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
      H ∣ extendSeed (liftX (locator node (fixedNodes R))) := by
  classical
  obtain ⟨g, hg, hgu, hgv, hgmax⟩ := hf
  change g.map constantsInFrac ≠ 0 at hg
  change g.map constantsInFrac ∣ _ at hgu hgv
  change ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
    H ∣ g.map constantsInFrac at hgmax
  have hg0 : g ≠ 0 := by
    intro hz
    exact hg (by rw [hz, Polynomial.map_zero])
  let g₀ := g * C g.leadingCoeff⁻¹
  have hm : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hnorm (P : Frac[X]) (hd : g.map constantsInFrac ∣ P) :
      g₀.map constantsInFrac ∣ P := by
    apply ((Polynomial.map_dvd_map' constantsInFrac).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P : Bivar) (hd : g.map constantsInFrac ∣ extendSeed P) :
      liftX g₀ ∣ P := by
    apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective (hm.map Polynomial.C)).mp
    change extendSeed (liftX g₀) ∣ extendSeed P
    rw [extend_liftX]
    exact hnorm _ hd
  have hu := hlift _ hgu
  have hv := hlift _ hgv
  have hdom : g₀ ∣ locator node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀, hm.ne_zero, hu, hv, h⟩)
  obtain ⟨S, _, _, t, ht, hS⟩ :=
    Strata.split_divisor_locator_factor node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub : S ⊆ fixedNodes R := by
    intro i his
    have hz : g₀.eval (node i) = 0 := by
      rw [hS, eval_smul, locator_eval_zero node S i his, smul_zero]
    have hlzero : (liftX g₀).eval (C (node i)) = 0 := by
      rw [eval_liftX, hz, C_0]
    obtain ⟨U, hU⟩ := hu
    obtain ⟨V, hV⟩ := hv
    exact (mem_fixed_iff R i).mpr ⟨by rw [hU, eval_mul, hlzero, zero_mul],
      by rw [hV, eval_mul, hlzero, zero_mul]⟩
  have hg₀dvd : g₀ ∣ locator node (fixedNodes R) := by
    rw [hS, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _
      (fun i his => locator_eval_zero node _ i (hsub his))
  intro H hU hV
  rw [extend_liftX]
  exact (hgmax H hU hV).trans
    ((Polynomial.map_dvd_map' constantsInFrac).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))

theorem fixed_gcd {u : Words} {T : TwoActive u} (R : Relation T)
    (hu : leftU R ≠ 0) (hm : ¬ MovingGCD R) (hi : ¬ InvalidLeft R) :
    IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R)) := by
  classical
  let S := fixedNodes R
  let Δ := liftX (locator node S)
  let A := extendSeed (leftU R)
  let B := extendSeed (leftV R)
  have hΔ : Δ.Monic := (locator_monic node S).map Polynomial.C
  have hΔ0 : extendSeed Δ ≠ 0 := (hΔ.map seedInclusion).ne_zero
  have hA0 : A ≠ 0 :=
    fun h => hu (extendSeed_injective (h.trans (Polynomial.map_zero _).symm))
  have hΔA : extendSeed Δ ∣ A := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftU R) (fun i h => ((mem_fixed_iff R i).mp h).1))
  have hΔB : extendSeed Δ ∣ B := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftV R) (fun i h => ((mem_fixed_iff R i).mp h).2))
  refine ⟨hΔ0, hΔA, hΔB, ?_⟩
  by_cases hf : FixedLeftGCD R
  · exact fixed_case_maximal R hi hf
  let G := EuclideanDomain.gcd A B
  have hGA : G ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hGB : G ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hG : G ≠ 0 := fun hz => hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd : G.natDegree ≤ S.card := by
    apply Nat.le_of_not_gt
    exact fun h => hm ⟨hf, G, hG, hGA, hGB, h⟩
  have hΔd : (extendSeed Δ).natDegree = S.card := by
    rw [extend_liftX, natDegree_map_eq_of_injective constantsInFrac.injective, locator_natDegree]
  obtain ⟨q, hq⟩ := EuclideanDomain.dvd_gcd hΔA hΔB
  change G = extendSeed Δ * q at hq
  have hq0 : q ≠ 0 := by intro h; exact hG (by rw [hq, h, mul_zero])
  have hd := congrArg Polynomial.natDegree hq
  rw [natDegree_mul hΔ0 hq0, hΔd] at hd
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have hqU : IsUnit q := by
    rw [hqC, isUnit_C, isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz, C_0] at hqC)
  intro H hHA hHB
  have hHG : H ∣ G := EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq, hqU.dvd_mul_right] at hHG

end

end K21_8
end Port_K1_8Fixed

section Port_K1_8Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_8

noncomputable section

open Polynomial K21

/-- Extract a primitive amplitude direction from the dependence of the
four columns over the fraction field in the evaluation coordinate. -/
def c1 : Prop :=
  ∀ U V : Bivar, U ≠ 0 → V ≠ 0 → columnRank U V = 3 →
    Nonempty (AmplitudeDirection U V)

/-- The small X-height rules out a positive-X-degree cancellation
between the primitive affine amplitude and the Frobenius-seed amplitude. -/
def c2 : Prop :=
  ∀ (U V : Bivar) (H : ℕ), U ≠ 0 → V ≠ 0 →
    IsCoprime (extendSeed U) (extendSeed V) →
    max U.natDegree V.natDegree = H → H < p - 1 →
    ∀ S : AmplitudeDirection U V,
      S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ H ∧
      S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ H

theorem of_children (h1 : c1) (h2 : c2) : K21.c8 := by
  intro u _ T R hmove hinvalid hsat hw
  have hu : leftU R ≠ 0 := by
    obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
    intro hz
    exact (hsat γ hγ M).U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨D⟩ := puncture R hsat hw (fixed_gcd R hu hmove hinvalid)
  refine ⟨D, ?_⟩
  rcases rank_cases D.U D.V D.U_ne D.V_ne with hfour | hthree
  · exact Or.inl hfour
  · obtain ⟨S⟩ := h1 D.U D.V D.U_ne D.V_ne hthree
    have hsmall : D.height < p - 1 := by
      have hh := D.height_eq
      have hc := T.inactive
      unfold TwoActive.height at hh
      change D.height < 2130706432
      omega
    obtain ⟨ha, hb⟩ := h2 D.U D.V D.height D.U_ne D.V_ne D.coprime D.max_degree hsmall S
    exact Or.inr (rank_three_branch D hthree S ha hb)

end

end K21_8
end Port_K1_8Split

section Port_K1_8_2Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_8_2

open Polynomial K21

noncomputable section

private def shape {R : Type*} [CommSemiring R] (n : ℕ) (u v : R) : R[X] :=
  C u + Polynomial.X (R := R) ^ n * C v

private theorem shape_coeffs {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0) (u v : R) :
    (shape n u v).coeff 0 = u ∧ (shape n u v).coeff n = v := by
  constructor
  · simp [shape, mul_comm (Polynomial.X (R := R) ^ n) (C v), Ne.symm hn]
  · simp [shape, mul_comm (Polynomial.X (R := R) ^ n) (C v), coeff_C_of_ne_zero hn]

private theorem primitive_shape {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0)
    {u v : F[X]} (hcop : IsCoprime u v) : (shape n u v).IsPrimitive := by
  intro d hd
  obtain ⟨h0, hn'⟩ := shape_coeffs hn u v
  have h := (C_dvd_iff_dvd_coeff _ _).mp hd
  exact hcop.isUnit_of_dvd' (h0 ▸ h 0) (hn' ▸ h n)

private theorem scalar_relPrime {F : Type*} [Field F] {a : F[X]} {P : F[X][X]}
    (ha : a ≠ 0) (hP : P.IsPrimitive) : IsRelPrime (C a) P := by
  intro d hda hdP
  have hdeg : d.natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_le_of_dvd hda (C_ne_zero.mpr ha)).trans_eq (natDegree_C a))
  rw [eq_C_of_natDegree_eq_zero hdeg] at hdP ⊢
  exact (hP _ hdP).map C

/-- The arguments of this function are seed-outer polynomials. -/
private def xHeight {F : Type*} [Field F] (P : F[X][X]) : ℕ :=
  (Bivariate.swap P).natDegree

private theorem xHeight_C {F : Type*} [Field F] (a : F[X]) : xHeight (C a) = a.natDegree := by
  rw [xHeight, Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]

private theorem xHeight_mul {F : Type*} [Field F] {P Q : F[X][X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : xHeight (P * Q) = xHeight P + xHeight Q := by
  unfold xHeight
  rw [map_mul]
  exact natDegree_mul (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hP)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hQ)

private theorem xHeight_pow {F : Type*} [Field F] (P : F[X][X]) (n : ℕ) :
    xHeight (P ^ n) = n * xHeight P := by
  rw [xHeight, map_pow, natDegree_pow, xHeight]

private theorem xHeight_shape {F : Type*} [Field F] {n : ℕ} (hn : n ≠ 0) (u v : F[X]) :
    xHeight (shape n u v) = max u.natDegree v.natDegree := by
  have hc (i : ℕ) :
      (Bivariate.swap (shape n u v)).coeff i = shape n (u.coeff i) (v.coeff i) := by
    rw [shape, map_add, map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_C, Bivariate.swap_Y,
      ← C_pow, coeff_add, coeff_C_mul, coeff_map, coeff_map, shape]
  unfold xHeight
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [hc, coeff_eq_zero_of_natDegree_lt ((le_max_left _ _).trans_lt hi),
      coeff_eq_zero_of_natDegree_lt ((le_max_right _ _).trans_lt hi)]
    simp [shape]
  · apply max_le
    · by_cases hu : u = 0
      · simp [hu]
      apply le_natDegree_of_ne_zero
      intro hz
      have h := congrArg (fun W : F[X] => W.coeff 0) ((hc u.natDegree).symm.trans hz)
      rw [(shape_coeffs hn _ _).1, coeff_zero] at h
      exact hu (leadingCoeff_eq_zero.mp h)
    · by_cases hv : v = 0
      · simp [hv]
      apply le_natDegree_of_ne_zero
      intro hz
      have h := congrArg (fun W : F[X] => W.coeff n) ((hc v.natDegree).symm.trans hz)
      rw [(shape_coeffs hn _ _).2, coeff_zero] at h
      exact hv (leadingCoeff_eq_zero.mp h)

private theorem cross_heights {F : Type*} [Field F] {U V P Q : F[X][X]}
    (hU : U ≠ 0) (hV : V ≠ 0) (hcop : IsRelPrime P Q) (hcross : U * Q = V * P) :
    xHeight P ≤ xHeight U ∧ xHeight Q ≤ xHeight V := by
  have hp : P ∣ U := hcop.dvd_of_dvd_mul_right (by rw [hcross]; exact dvd_mul_left _ _)
  have hq : Q ∣ V := hcop.symm.dvd_of_dvd_mul_right (by rw [← hcross]; exact dvd_mul_left _ _)
  exact ⟨natDegree_le_of_dvd (_root_.map_dvd Bivariate.swap hp)
      (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU),
    natDegree_le_of_dvd (_root_.map_dvd Bivariate.swap hq)
      (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)⟩

/-- A common nonunit seed factor forces the sparse amplitude to be a
unit scalar multiple of the full Frobenius power of the affine amplitude. -/
private theorem affine_sparse {F : Type*} [Field F] (q : ℕ) [ExpChar F q] (hq : q ≠ 0)
    {u v r s : F[X]} (huv : IsCoprime u v) (hrs : IsCoprime r s) :
    IsRelPrime (shape 1 u v) (shape q r s) ∨
      ∃ t : F[X], IsUnit t ∧ shape q r s = C t * (shape 1 u v) ^ q := by
  by_cases hv : v = 0
  · left
    subst v
    have hu : IsUnit u := huv.isUnit_of_dvd (dvd_zero _)
    simpa [shape] using (hu.map (C : F[X] →+* F[X][X])).isRelPrime_left
  have hAffine : shape 1 u v = C v * Polynomial.X (R := F[X]) + C u := by
    rw [shape, pow_one, add_comm, mul_comm (Polynomial.X (R := F[X]))]
  have hirr : Irreducible (shape 1 u v) := by
    rw [hAffine]
    exact irreducible_C_mul_X_add_C hv huv.symm.isRelPrime
  rcases hirr.dvd_or_isRelPrime (n := shape q r s) with hdiv | hcop
  · right
    have hpow : (shape 1 u v) ^ q = shape q (u ^ q) (v ^ q) := by
      simp only [shape, pow_one, add_pow_expChar _ _ q, mul_pow, ← C_pow]
    have hdiff : C (v ^ q) * shape q r s - C s * (shape 1 u v) ^ q =
        C (v ^ q * r - s * u ^ q) := by
      rw [hpow]
      simp only [shape, map_mul, map_sub]
      ring
    have hc : shape 1 u v ∣ C (v ^ q * r - s * u ^ q) := by
      rw [← hdiff]
      exact dvd_sub (hdiv.mul_left _) ((dvd_pow_self _ hq).mul_left _)
    have hcross : v ^ q * r = s * u ^ q := by
      apply sub_eq_zero.mp
      by_contra hne
      have hd := natDegree_le_of_dvd hc (C_ne_zero.mpr hne)
      rw [hAffine, natDegree_linear hv, natDegree_C] at hd
      omega
    have hp : IsCoprime (u ^ q) (v ^ q) := huv.pow
    obtain ⟨e, f, hbez⟩ := hp
    let t := e * r + f * s
    have hr : r = t * u ^ q := by
      calc
        r = (e * u ^ q + f * v ^ q) * r := by rw [hbez, one_mul]
        _ = t * u ^ q := by
          dsimp [t]
          linear_combination f * hcross
    have hs : s = t * v ^ q := by
      calc
        s = (e * u ^ q + f * v ^ q) * s := by rw [hbez, one_mul]
        _ = t * v ^ q := by
          dsimp [t]
          linear_combination - e * hcross
    have ht : shape q r s = C t * (shape 1 u v) ^ q := by
      rw [hpow, hr, hs]
      simp only [shape, map_mul]
      ring
    exact ⟨t, primitive_shape hq hrs t (ht ▸ dvd_mul_right _ _), ht⟩
  · exact Or.inl hcop

private theorem height_bound {F : Type*} [Field F] (q : ℕ) [ExpChar F q] (hq : 1 < q)
    {U₀ V : F[X][X]} {H : ℕ} (hU₀ : U₀ ≠ 0) (hV : V ≠ 0)
    (hU₀H : xHeight U₀ ≤ H) (hVH : xHeight V ≤ H) (hsmall : H < q - 1)
    {a b u v r s : F[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) (huv : IsCoprime u v) (hrs : IsCoprime r s)
    (hdir : U₀ * -(C b * shape 1 u v) = V * (C a * shape q r s)) :
    a.natDegree + max r.natDegree s.natDegree ≤ H ∧
      b.natDegree + max u.natDegree v.natDegree ≤ H := by
  have hq0 : q ≠ 0 := by omega
  let U := -U₀
  have hU : U ≠ 0 := neg_ne_zero.mpr hU₀
  have hUH : xHeight U ≤ H := by
    simpa only [U, xHeight, map_neg, natDegree_neg] using hU₀H
  have hcross : U * (C b * shape 1 u v) = V * (C a * shape q r s) := by
    exact (neg_mul_comm U₀ (C b * shape 1 u v)).trans hdir
  let A := shape 1 u v
  let B := shape q r s
  have hA : A.IsPrimitive := primitive_shape one_ne_zero huv
  have hB : B.IsPrimitive := primitive_shape hq0 hrs
  have hab' : IsRelPrime (C a) (C b) := (hab.map C).isRelPrime
  have hAd : xHeight A = max u.natDegree v.natDegree := xHeight_shape one_ne_zero _ _
  have hBd : xHeight B = max r.natDegree s.natDegree := xHeight_shape hq0 _ _
  rcases affine_sparse q hq0 huv hrs with hcop | ⟨t, ht, hpow⟩
  · have hcop' : IsRelPrime (C a * B) (C b * A) :=
      (hab'.mul_right (scalar_relPrime ha hA)).mul_left
        ((scalar_relPrime hb hB).symm.mul_right hcop.symm)
    obtain ⟨hP, hQ⟩ := cross_heights hU hV hcop' hcross
    rw [xHeight_mul (C_ne_zero.mpr ha) hB.ne_zero, xHeight_C, hBd] at hP
    rw [xHeight_mul (C_ne_zero.mpr hb) hA.ne_zero, xHeight_C, hAd] at hQ
    exact ⟨hP.trans hUH, hQ.trans hVH⟩
  · change B = C t * A ^ q at hpow
    let D := C a * C t * A ^ (q - 1)
    have hD : IsRelPrime D (C b) :=
      (hab'.mul_left ((ht.map C).isRelPrime_left)).mul_left
        (scalar_relPrime hb hA).symm.pow_left
    have hfactor : C a * B = D * A := by
      have hqpow : A ^ q = A ^ (q - 1) * A := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]
      simp only [D, hpow, hqpow, mul_assoc]
    have hnew : U * C b = V * D := by
      apply mul_right_cancel₀ hA.ne_zero
      calc
        (U * C b) * A = U * (C b * A) := mul_assoc _ _ _
        _ = V * (C a * B) := hcross
        _ = (V * D) * A := by rw [hfactor, mul_assoc V D A]
    obtain ⟨hDle, hble⟩ := cross_heights hU hV hD hnew
    have ht0 : t.natDegree = 0 := natDegree_eq_zero_of_isUnit ht
    have hDa : xHeight D = a.natDegree + (q - 1) * xHeight A := by
      dsimp [D]
      rw [xHeight_mul (mul_ne_zero (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero))
            (pow_ne_zero _ hA.ne_zero),
        xHeight_mul (C_ne_zero.mpr ha) (C_ne_zero.mpr ht.ne_zero), xHeight_C, xHeight_C,
        xHeight_pow, ht0, add_zero]
    have hzero : xHeight A = 0 := by
      by_contra hn
      have hle := (Nat.mul_le_mul_left (q - 1) (Nat.one_le_iff_ne_zero.mpr hn))
      rw [Nat.mul_one] at hle
      rw [hDa] at hDle
      omega
    have hBzero : xHeight B = 0 := by
      rw [hpow, xHeight_mul (C_ne_zero.mpr ht.ne_zero) (pow_ne_zero _ hA.ne_zero),
        xHeight_C, xHeight_pow, hzero, ht0, Nat.mul_zero, add_zero]
    rw [hDa, hzero, Nat.mul_zero, add_zero] at hDle
    rw [xHeight_C] at hble
    rw [← hBd, ← hAd, hBzero, hzero, add_zero, add_zero]
    exact ⟨hDle.trans hUH, hble.trans hVH⟩

private theorem swap_threeUAt (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    Bivariate.swap (K21_8.threeUAt q a β) = C a * shape q ((β 0).map twist) ((β 1).map twist) := by
  simp only [K21_8.threeUAt, shape, liftX, seed, map_add, map_mul, map_pow, Bivariate.swap_map_C,
    Bivariate.swap_X]

private theorem threeU_native : K21_8.threeUAt p = threeU := by
  unfold K21_8.threeUAt threeU
  rfl

private theorem swap_threeV (b : K[X]) (α : Fin 2 → K[X]) :
    Bivariate.swap (threeV b α) = -(C b * shape 1 (α 0) (α 1)) := by
  simp only [threeV, shape, liftX, seed, map_add, map_mul, map_neg, Bivariate.swap_map_C,
    Bivariate.swap_X, pow_one]

private theorem native_height_at (q : ℕ) [ExpChar K q] (hq : 1 < q)
    (U V : Bivar) (H : ℕ) (hU : U ≠ 0) (hV : V ≠ 0)
    (hmax : max U.natDegree V.natDegree = H) (hsmall : H < q - 1)
    (a b : K[X]) (α β : Fin 2 → K[X]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) (hα : IsCoprime (α 0) (α 1)) (hβ : IsCoprime (β 0) (β 1))
    (hdir : sameDirection U V (K21_8.threeUAt q a β) (threeV b α)) :
    a.natDegree + amplitudeDegree (β 0) (β 1) ≤ H ∧
      b.natDegree + amplitudeDegree (α 0) (α 1) ≤ H := by
  have hUH : U.natDegree ≤ H := hmax ▸ le_max_left _ _
  have hVH : V.natDegree ≤ H := hmax ▸ le_max_right _ _
  have hcross : Bivariate.swap U * -(C b * shape 1 (α 0) (α 1)) =
      Bivariate.swap V * (C a * shape q ((β 0).map twist) ((β 1).map twist)) := by
    have h := congrArg (Bivariate.swap (R := K)) hdir
    change Bivariate.swap (U * threeV b α) = Bivariate.swap (V * K21_8.threeUAt q a β) at h
    rwa [map_mul, map_mul, swap_threeV, swap_threeUAt] at h
  have hxU : xHeight (Bivariate.swap U) = U.natDegree := by
    rw [xHeight, Bivariate.swap_swap_apply]
  have hxV : xHeight (Bivariate.swap V) = V.natDegree := by
    rw [xHeight, Bivariate.swap_swap_apply]
  have hβ' : IsCoprime ((β 0).map twist) ((β 1).map twist) :=
    hβ.map (Polynomial.mapRingHom twist)
  have h := height_bound (F := K) q hq
    (U₀ := Bivariate.swap U) (V := Bivariate.swap V) (H := H)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hU)
    (Bivariate.swap.toRingEquiv.map_ne_zero_iff.mpr hV)
    (hxU ▸ hUH) (hxV ▸ hVH) hsmall
    (a := a) (b := b) (u := α 0) (v := α 1)
    (r := (β 0).map twist) (s := (β 1).map twist)
    ha hb hab hα hβ' hcross
  simpa only [amplitudeDegree, natDegree_map_eq_of_injective twist.injective] using h

theorem proof : K21_8.c2 := by
  intro U V H hU hV _ hmax hsmall S
  apply native_height_at p (by decide) U V H hU hV hmax hsmall S.a S.b S.α S.β
    S.a_ne S.b_ne S.scalar_coprime S.α_primitive S.β_primitive
  rw [threeU_native]
  exact S.direction

end

end K21_8_2
end Port_K1_8_2Proof

section Port_K1_8_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K21_8_1

noncomputable section

open Polynomial K21 K21_8 FrobeniusLocator
open scoped BigOperators

private def evaluationFraction : Bivar →+* Frac[X] :=
  extendSeedHom.comp (Bivariate.swap (R := K)).toRingEquiv.toRingHom

private theorem evaluationFraction_injective : Function.Injective evaluationFraction :=
  extendSeed_injective.comp (Bivariate.swap (R := K)).injective

private theorem evaluationFraction_lift (f : K[X]) :
    evaluationFraction (liftX f) = C (seedInclusion f) := by
  change (Bivariate.swap (f.map C)).map seedInclusion = _
  rw [Bivariate.swap_map_C, Polynomial.map_C]

private def columns (q : ℕ) (U V : Bivar) (i : Fin 4) : Bivar :=
  if i = 0 then U else if i = 1 then seed * U else if i = 2 then V else seed ^ q * V

/-- Choose a dependence over the evaluation fraction field, and clear its
denominators simultaneously before descending along the swap. -/
private theorem polynomial_dependence {U V : Bivar} (hr : columnRank U V = 3) :
    ∃ f : Fin 4 → K[X], f ≠ 0 ∧ ∑ i, liftX (f i) * columns p U V i = 0 := by
  classical
  have hdep : ¬ LinearIndependent Frac (fun i => evaluationFraction (columns p U V i)) := by
    intro h
    have hdim : columnRank U V = 4 := by
      change Module.finrank Frac
        (Submodule.span Frac (Set.range fun i => evaluationFraction (columns p U V i))) = 4
      simpa only [Fintype.card_fin] using finrank_span_eq_card h
    omega
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors K[X]) c
  choose f hf using hd
  have hcoeff (i : Fin 4) : seedInclusion (f i) = seedInclusion (d : K[X]) * c i := by
    simpa only [Algebra.smul_def, seedInclusion] using hf i
  have hdn : seedInclusion (d : K[X]) ≠ 0 := by
    intro hz
    exact nonZeroDivisors.ne_zero d.property
      (seedInclusion_injective (hz.trans (map_zero seedInclusion).symm))
  refine ⟨f, ?_, ?_⟩
  · intro hzero
    have hj' := hcoeff j
    rw [hzero, Pi.zero_apply, map_zero] at hj'
    exact hj ((mul_eq_zero.mp hj'.symm).resolve_left hdn)
  · have hscaled :
        ∑ i, evaluationFraction (liftX (f i)) * evaluationFraction (columns p U V i) =
          C (seedInclusion (d : K[X])) * ∑ i, c i • evaluationFraction (columns p U V i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [evaluationFraction_lift, hcoeff, Polynomial.C_mul, smul_eq_C_mul, mul_assoc]
    apply evaluationFraction_injective
    rw [map_zero, map_sum]
    simp only [map_mul, hscaled, hc, mul_zero]

private def amplitude (q : ℕ) (u v : K[X]) : Bivar :=
  liftX u + seed ^ q * liftX v

private theorem amplitude_zero (q : ℕ) : amplitude q 0 0 = 0 := by
  simp only [amplitude, liftX, Polynomial.map_zero, mul_zero, add_zero]

private theorem amplitude_scale (q : ℕ) (d u v : K[X]) :
    amplitude q (d * u) (d * v) = liftX d * amplitude q u v := by
  simp only [amplitude, liftX, Polynomial.map_mul]
  ring

private theorem amplitude_eq_zero {q : ℕ} (hq : 0 < q) {u v : K[X]}
    (h : amplitude q u v = 0) : u = 0 ∧ v = 0 := by
  have hswap : C u + (Polynomial.X (R := K[X])) ^ q * C v = 0 := by
    simpa only [amplitude, seed, liftX, map_add, map_mul, map_pow, map_zero,
      Bivariate.swap_X, Bivariate.swap_map_C] using congrArg (Bivariate.swap (R := K)) h
  have hu := congrArg (fun W : Bivar => W.coeff 0) hswap
  have hv := congrArg (fun W : Bivar => W.coeff q) hswap
  have hshift : ((Polynomial.X (R := K[X])) ^ q * C v).coeff q = v := by
    simpa only [Nat.zero_add, coeff_C_zero] using (coeff_X_pow_mul (C v : Bivar) q 0)
  constructor
  · simpa only [coeff_add, coeff_C_zero, coeff_X_pow_mul', Nat.not_le_of_lt hq,
      ite_false, add_zero, coeff_zero] using hu
  · simpa only [coeff_add, hshift, coeff_C, hq.ne', ite_false, zero_add, coeff_zero] using hv

private theorem group_dependence {q : ℕ} {U V : Bivar} {f : Fin 4 → K[X]}
    (h : ∑ i, liftX (f i) * columns q U V i = 0) :
    amplitude 1 (f 0) (f 1) * U + amplitude q (f 2) (f 3) * V = 0 := by
  have h0 : columns q U V 0 = U := rfl
  have h1 : columns q U V 1 = seed * U := rfl
  have h2 : columns q U V 2 = V := rfl
  have h3 : columns q U V 3 = seed ^ q * V := rfl
  rw [Fin.sum_univ_four, h0, h1, h2, h3] at h
  simpa only [amplitude, pow_one, add_mul, mul_assoc, mul_left_comm, add_assoc] using h

private theorem nonzero_pairs {q : ℕ} (hq : 0 < q) {U V : Bivar} (hu : U ≠ 0) (hv : V ≠ 0)
    {f : Fin 4 → K[X]} (hf : f ≠ 0)
    (h : amplitude 1 (f 0) (f 1) * U + amplitude q (f 2) (f 3) * V = 0) :
    (![f 0, f 1] : Fin 2 → K[X]) ≠ 0 ∧ (![f 2, f 3] : Fin 2 → K[X]) ≠ 0 := by
  constructor
  · intro hz
    have h0 : f 0 = 0 := congrFun hz 0
    have h1 : f 1 = 0 := congrFun hz 1
    rw [h0, h1, amplitude_zero, zero_mul, zero_add] at h
    have hz' : amplitude q (f 2) (f 3) = 0 := (mul_eq_zero.mp h).resolve_right hv
    obtain ⟨h2, h3⟩ := amplitude_eq_zero hq hz'
    apply hf
    funext i
    fin_cases i <;> assumption
  · intro hz
    have h2 : f 2 = 0 := congrFun hz 0
    have h3 : f 3 = 0 := congrFun hz 1
    rw [h2, h3, amplitude_zero, zero_mul, add_zero] at h
    have hz' : amplitude 1 (f 0) (f 1) = 0 := (mul_eq_zero.mp h).resolve_right hu
    obtain ⟨h0, h1⟩ := amplitude_eq_zero Nat.zero_lt_one hz'
    apply hf
    funext i
    fin_cases i <;> assumption

private theorem normalize_pair {u v : K[X]} (h : (![u, v] : Fin 2 → K[X]) ≠ 0) :
    ∃ (d : K[X]) (w : Fin 2 → K[X]), d ≠ 0 ∧
      u = d * w 0 ∧ v = d * w 1 ∧ IsCoprime (w 0) (w 1) := by
  obtain ⟨d, w, hd, hw, hprim⟩ := PrimitiveVector.exists_normalization ![u, v] h
  obtain ⟨r, hr⟩ := (PrimitiveVector.primitive_iff_bezout w).mp hprim
  exact ⟨d, w, hd, hw 0, hw 1, r 0, r 1, by simpa only [Fin.sum_univ_two] using hr⟩

private def twistEquiv : K ≃+* K :=
  RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩

private def untwist : K →+* K := twistEquiv.symm.toRingHom

private theorem map_untwist_twist (f : K[X]) : (f.map untwist).map twist = f := by
  rw [Polynomial.map_map]
  have h : twist.comp untwist = RingHom.id K := by
    apply RingHom.ext
    intro x
    exact twistEquiv.apply_symm_apply x
  rw [h, Polynomial.map_id]

private theorem liftX_ne_zero {f : K[X]} (hf : f ≠ 0) : liftX f ≠ 0 := by
  intro h
  exact hf (Polynomial.map_injective Polynomial.C Polynomial.C_injective
    (h.trans (Polynomial.map_zero _).symm))

private theorem cross_of_scaled_dependence {d a b : K[X]} (hd : d ≠ 0) {U V F G : Bivar}
    (h : (liftX (d * b) * F) * U + (liftX (d * a) * G) * V = 0) :
    U * -(liftX b * F) = V * (liftX a * G) := by
  have hscaled : liftX d * (U * (liftX b * F) + V * (liftX a * G)) = 0 := by
    rw [← h]
    simp only [liftX, Polynomial.map_mul]
    ring
  have hz := (mul_eq_zero.mp hscaled).resolve_left (liftX_ne_zero hd)
  exact (_root_.mul_neg U (liftX b * F)).trans (neg_eq_iff_add_eq_zero.mpr hz)

private theorem primitive_dependence {q : ℕ} (hq : 0 < q) {U V : Bivar}
    (hU : U ≠ 0) (hV : V ≠ 0) {f : Fin 4 → K[X]} (hf : f ≠ 0)
    (hsum : ∑ i, liftX (f i) * columns q U V i = 0) :
    ∃ (α β : Fin 2 → K[X]) (a b : K[X]), a ≠ 0 ∧ b ≠ 0 ∧ IsCoprime a b ∧
      IsCoprime (α 0) (α 1) ∧ IsCoprime (β 0) (β 1) ∧
      sameDirection U V (threeUAt q a β) (threeV b α) := by
  have hrel := group_dependence (q := q) (U := U) (V := V) (f := f) hsum
  obtain ⟨hleft, hright⟩ := nonzero_pairs hq hU hV hf hrel
  obtain ⟨b₀, α, hb₀, h0, h1, hα⟩ := normalize_pair hleft
  obtain ⟨a₀, βσ, ha₀, h2, h3, hβσ⟩ := normalize_pair hright
  have hab₀ : (![a₀, b₀] : Fin 2 → K[X]) ≠ 0 := fun h => ha₀ (congrFun h 0)
  obtain ⟨d, ab, hd, ha, hb, hab⟩ := normalize_pair hab₀
  let β : Fin 2 → K[X] := fun i => (βσ i).map untwist
  have ha' : ab 0 ≠ 0 := fun hz => ha₀ (by rw [ha, hz, mul_zero])
  have hb' : ab 1 ≠ 0 := fun hz => hb₀ (by rw [hb, hz, mul_zero])
  refine ⟨α, β, ab 0, ab 1, ha', hb', hab, hα,
    hβσ.map (Polynomial.mapRingHom untwist), ?_⟩
  rw [h0, h1, h2, h3, ha, hb] at hrel
  simp only [amplitude_scale] at hrel
  have hcross := cross_of_scaled_dependence hd hrel
  simpa only [sameDirection, threeUAt, threeV, β, map_untwist_twist, amplitude, pow_one]
    using hcross

private theorem threeUAt_native : threeUAt p = (threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt threeU
  rfl

/-- A rank-three dependence gives the two primitive amplitudes and coprime
scalar contents. The stored second amplitude is before coefficient Frobenius. -/
theorem proof : K21_8.c1 := by
  intro U V hU hV hr
  have hp : 0 < p := by decide
  obtain ⟨f, hf, hsum⟩ := polynomial_dependence hr
  obtain ⟨α, β, a, b, ha, hb, hab, hα, hβ, hdir⟩ :=
    primitive_dependence (q := p) (U := U) (V := V) (f := f) hp hU hV hf hsum
  refine ⟨⟨α, β, a, b, ha, hb, hab, hα, hβ, ?_⟩⟩
  simpa only [threeUAt_native] using hdir

end

end K21_8_1
end Port_K1_8_1Proof
