import ProximityPrize.SubmissionBinaryLower.P64C7Counts

/-!
# A global auxiliary from the residual rank bound

The coefficient restriction maps a globally bounded polynomial to its local
box. A nonzero kernel element gives residual divisibility in the original
line coordinates.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Auxiliary

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Weights P64C6Boxes
  P64C7Truncation P64C7Boxes P64C7Rank Module

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

noncomputable def xLine (x : F) : Tri :=
  Polynomial.C (Polynomial.X - Polynomial.C (Polynomial.C x))

noncomputable def yLine (y : F[X]) : Tri :=
  Polynomial.X - Polynomial.C (Polynomial.C y)

def Residual (R H : Tri) (x : F) (y : F[X]) (s : ℕ) : Prop :=
  ∃ A B : Tri, yLine y ^ s * H = xLine x ^ s * A + R * B

lemma lineShift_degree_le (R : Tri) (x : F) (y : F[X]) :
    (lineShift R x y).natDegree ≤ R.natDegree := by
  change (Polynomial.map _ (Polynomial.taylor _ R)).natDegree ≤ R.natDegree
  exact Polynomial.natDegree_map_le.trans_eq (Polynomial.natDegree_taylor R _)

noncomputable def restriction (x : F) (y : F[X]) (D W q e h s : ℕ) :
    supp (F := F) (auxiliary D W q e h) →ₗ[F] supp (F := F) (inputBox s h q e) :=
  LinearMap.codRestrict (supp (inputBox s h q e))
    ((cut (inputBox s h q e)).comp
      ((P64C6Flat.lineShiftLM x y).comp (supp (auxiliary D W q e h)).subtype))
    (fun H => cut_mem _ _)

lemma restriction_val (x : F) (y : F[X]) (D W q e h s : ℕ)
    (H : supp (F := F) (auxiliary D W q e h)) :
    (restriction x y D W q e h s H).1 = cut (inputBox s h q e) (lineShift H.1 x y) := rfl

lemma shift_covered (x : F) (y : F[X]) (D W q e h s : ℕ)
    (hy : y.natDegree ≤ q) (H : Tri) (hH : H ∈ supp (auxiliary D W q e h)) :
    ∀ a b l, a < s → c3 (lineShift H x y) a b l ≠ 0 →
      (a, b, l) ∈ inputBox s h q e := by
  intro a b l ha hn
  have hne : H ≠ 0 := by
    intro hz
    simp [hz, lineShift, Polynomial.Bivariate.shift, c3] at hn
  have hc := auxiliary_caps D W q e h hne hH
  have hw := lineShift_weight H x y q e hc.2.2 hy a b l hn
  have hb0 : (lineShift H x y).coeff b ≠ 0 := by
    intro hz
    simp [c3, hz] at hn
  have hb := (Polynomial.le_natDegree_of_ne_zero hb0).trans (lineShift_degree_le H x y)
  exact (mem_input s h q e a b l).mpr ⟨ha, hb.trans_lt hc.2.1, by simpa using hw⟩

lemma residual_of_mem (R H : Tri) (x : F) (y : F[X]) (s : ℕ)
    (hm : (Polynomial.X : Tri) ^ s * lineShift H x y ∈ residualIdeal s (lineShift R x y)) :
    Residual R H x y s := by
  obtain ⟨A, B, he⟩ := Ideal.mem_span_pair.mp hm
  let inv := shiftHom (-(Polynomial.C x)) (-y)
  have hi (G : Tri) : inv (lineShift G x y) = G := by
    change shiftHom (-(Polynomial.C x)) (-y) (shiftHom (Polynomial.C x) y G) = G
    simpa [inv] using shiftHom_inverse (-(Polynomial.C x)) (-y) G
  have hx : inv (U : Tri) = xLine x := by
    simp [inv, U, xLine, shiftHom, Polynomial.taylor_apply, sub_eq_add_neg]
  have hv : inv (Polynomial.X : Tri) = yLine y := by
    simp [inv, yLine, shiftHom, Polynomial.taylor_apply, sub_eq_add_neg]
  have he' := congrArg inv he
  simp only [map_add, map_mul, map_pow, hi, hx, hv] at he'
  exact ⟨inv A, inv B, by simpa only [mul_comm] using he'.symm⟩

/-- The finite DLT dimension inequality gives a bounded, nonzero residual auxiliary. -/
theorem exists_auxiliary (R : Tri) (x : F) (y : F[X]) (D W q e h d s μ ν : ℕ)
    (R'' : Polynomial (Polynomial F)) (hy : y.natDegree ≤ q)
    (hRμ : OrdGE R x y μ)
    (hR0 : (lineShift R x y).map (Polynomial.constantCoeff (R := Polynomial F)) =
      Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) (hY : R.natDegree ≤ h) (hW : WtLE 0 q 1 d R)
    (hμh : μ ≤ h) (hμs : μ ≤ s) (hνs : ν ≤ s) (hqd : q * μ ≤ d)
    (hdim : P64C7Counts.upper s h q d μ ν e < (auxiliary D W q e h).card) :
    ∃ H : Tri, H ≠ 0 ∧ P64Caps.Weighted.weightedSupportDegree H D ≤ W ∧
      H.natDegree < h ∧ WtLE 0 q 1 e H ∧ Residual R H x y s := by
  classical
  let S := lineShift R x y
  let f := (phi S s h q e).comp (restriction x y D W q e h s)
  have hr := P64C7Counts.rank_upper S s μ ν h q d e R'' hRμ hR0 hu
    ((lineShift_degree_le R x y).trans hY) (lineShift_weight R x y q d hW hy)
    hμh hμs hνs hqd
  have hf : finrank F (LinearMap.range f) ≤ P64C7Counts.upper s h q d μ ν e :=
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans hr
  have hk : LinearMap.ker f ≠ ⊥ := by
    intro hz
    have he := f.finrank_range_add_finrank_ker
    rw [hz, finrank_bot, add_zero, finrank_supp] at he
    omega
  obtain ⟨H, hH, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hn' : H.1 ≠ 0 := fun hz => hn (Subtype.ext hz)
  have hc := auxiliary_caps D W q e h hn' H.2
  refine ⟨H.1, hn', hc.1, hc.2.1, hc.2.2, residual_of_mem R H.1 x y s ?_⟩
  have hm : (Polynomial.X : Tri) ^ s * cut (inputBox s h q e) (lineShift H.1 x y) ∈
      residualIdeal s S := by
    change Ideal.Quotient.mkₐ F _ _ = 0 at hH
    rw [Ideal.Quotient.mkₐ_eq_mk] at hH
    exact Ideal.Quotient.eq_zero_iff_mem.mp hH
  obtain ⟨A, hA⟩ := U_pow_dvd_sub_cut s (inputBox s h q e) (lineShift H.1 x y)
    (shift_covered x y D W q e h s hy H.1 H.2)
  have hd : lineShift H.1 x y - cut (inputBox s h q e) (lineShift H.1 x y) ∈
      residualIdeal s S := by
    rw [hA]
    exact Ideal.mul_mem_right _ _ (residual_U_mem s S)
  have ht := add_mem (Ideal.mul_mem_left _ ((Polynomial.X : Tri) ^ s) hd) hm
  simpa only [mul_sub, sub_add_cancel] using ht

end P64C7Auxiliary
end ProximityPrize.SubmissionBinaryLower
