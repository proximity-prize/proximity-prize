import ProximityPrize.SubmissionLower.HighCore82209Data
import ProximityPrize.SubmissionLower.UpperBranch7

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false

namespace FrontCore82209

noncomputable section

open Polynomial
open P1 (K I node twist p)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum seedEmbedding)
open K1_14_1 (PoleData MarkResidues nodeL)
open P1_7 (Reduced singularDegree singularFee)
open P1_7_7 (poleProduct)
open scoped BigOperators Polynomial
open private commonChart common_recovers from ProximityPrize.SubmissionLower.UpperBranch7

abbrev AnchorModel (u : P1.Words) (D : Finset I) := P1.ModelAt HighCore82209.heightCap u D
abbrev AnchoredFamily {u D} (M : AnchorModel u D) (Γ : Finset K) :=
  P1.FamilyAt HighCore82209.agreement M Γ

def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
theorem adjacent_chart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
theorem chart_poles {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      fun i => by fin_cases i <;> first | exact hm | exact hm',
      fun i => by fin_cases i <;> first | exact hd | exact hd',
      hcop, fun i => by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D, rfl, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
theorem resultant_count {u del} (M : AnchorModel u del) {f : Equation} {v : ℕ}
    (hf : Reduced f) (hs : SeedBound f v) (hp : singularDegree f.natDegree v < p)
    (T : Finset K) (he : ∀ γ ∈ T, graphEval (M.label γ) (f.resultant f.derivative) = 0) :
    T.card ≤ singularFee f.natDegree v := by
  classical
  obtain ⟨hn, hd⟩ := P1_7.resultant_bounds hf hs
  let C : K1_14_3.SeedCover := ⟨_, hn, ∅⟩
  have hz := K1_14_3.seed_count (T := T) (label := M.label)
    (fun _ _ _ _ h => sub_left_inj.mp h) C (hd.trans_lt hp) (fun γ hγ => Or.inl (he γ hγ))
  exact (show T.card ≤ (p+1)*(f.resultant f.derivative).totalDegree by
    simpa only [C, Finset.card_empty, Nat.add_zero] using hz).trans (Nat.mul_le_mul_left _ hd)
theorem fixed_count {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (T : Finset K) (hT : T ⊆ Γ) {f : Equation} (hf : 0 < f.natDegree) (hs : SeedBound f 0)
    (hr : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) : T.card ≤ f.natDegree := by
  classical
  let g := f.map (graphEval 0)
  have hc (z : K) (i : ℕ) : graphEval z (f.coeff i) = (f.coeff i).coeff 0 := by
    have h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hs i))
    conv_lhs => rw [h]
    simp [graphEval]
  have he (z : K) : f.map (graphEval z) = g := by
    ext i
    simp only [g, coeff_map, hc]
  have hn : g ≠ 0 := by
    intro hz
    have hlead := congrArg (fun G : FX[X] => G.coeff f.natDegree) hz
    simp only [g, coeff_map, hc, coeff_zero] at hlead
    have h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero (hs f.natDegree))
    have hfn : f ≠ 0 := fun h0 => by simp [h0] at hf
    exact (leadingCoeff_ne_zero.mpr hfn) (h.trans (by rw [hlead, map_zero]))
  let val := fun γ => atX (F.scalar γ)
  have hi : Set.InjOn val (T : Set K) :=
    fun _ ha _ hb h => F.distinct (hT ha) (hT hb) (K1_14_3.scalar_atX_injective h)
  calc
    T.card = (T.image val).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ g.natDegree := Polynomial.card_le_degree_of_subset_roots (by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
      apply (Polynomial.mem_roots hn).mpr
      change g.eval (val γ) = 0
      rw [← he (M.label γ), Polynomial.eval_map]
      exact hr γ hγ)
    _ ≤ f.natDegree := Polynomial.natDegree_map_le
theorem pole_data {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {H : L[X]} (h : AdjacentChart M F H) :
    (poleProduct H).Monic ∧ (poleProduct H).natDegree = 2 * M.overhead.toNat ∧
    (poleProduct H).eval (algebraMap L[X] FX Polynomial.X) ≠ 0 ∧
    ∀ j : I, (poleProduct H).eval (seedEmbedding (node j)) ≠ 0 := by
  obtain ⟨hm, hd, _, hm', hd', _, _, hn, _, _, _⟩ := h
  let B := H * H.map (frobenius L p)
  let incl := algebraMap L[X] FX
  have hb : B.Monic := hm.mul hm'
  have hdeg : B.natDegree = 2 * M.overhead.toNat := by
    rw [show B = H * H.map (frobenius L p) from rfl,
      Polynomial.natDegree_mul hm.ne_zero hm'.ne_zero, hd, hd']
    omega
  refine ⟨hb.map _, (hb.natDegree_map _).trans hdeg, ?_, ?_⟩
  · have heval : (poleProduct H).eval (incl Polynomial.X) = incl B := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) (incl Polynomial.X) = incl B
      rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr hb.ne_zero
  · intro j
    let x := algebraMap K L (node j)
    have heval : (poleProduct H).eval (seedEmbedding (node j)) = incl (Polynomial.C (B.eval x)) := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) ((incl.comp Polynomial.C) x) = _
      rw [Polynomial.eval₂_hom]
      rfl
    have hval : B.eval x ≠ 0 := by
      rw [show B = H * H.map (frobenius L p) from rfl, Polynomial.eval_mul]
      exact mul_ne_zero (hn j).1 (hn j).2
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr
      ((map_ne_zero_iff _ Polynomial.C_injective).mpr hval)
theorem crt_chart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hw : 0 < M.overhead.toNat) (hH : AdjacentChart M F H) :
    ∃ C : P1_7_7.CRTChart M.overhead.toNat, ∀ γ ∈ Γ,
      C.Recovers (poleProduct H) (M.label γ) (F.scalar γ) := by
  obtain ⟨D, hD, _, hmarks⟩ := chart_poles M F H hH
  obtain ⟨B, hd, hn⟩ := P1_7_7_1.bounded_crt D
  refine ⟨commonChart hw B hd hn, ?_⟩
  intro γ hγ
  rw [P1_7_7.poleProduct, ← hD]
  exact common_recovers hw B hd hn (hmarks γ hγ)

#print axioms adjacent_chart
#print axioms crt_chart
end
end FrontCore82209
