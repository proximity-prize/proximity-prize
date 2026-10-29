import ProximityPrize.SubmissionBinaryLower.P64C7Boxes

/-!
# The dimension contribution of multiples of the local equation
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Multiples

open Polynomial P64Found P64C7Boxes P64C7Truncation Module

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma product_covered (S G : Tri) (s h q d e : ℕ) (hY : S.natDegree ≤ h)
    (hW : WtLE 0 q 1 d S) (hG : G ∈ supp (multiplesBox s q d e))
    (a b l : ℕ) (ha : a < s) (hne : c3 (S * G) a b l ≠ 0) :
    (a, b, l) ∈ broadBox s h q e := by
  classical
  by_contra hnot
  apply hne
  rw [c3_mul]
  refine Finset.sum_eq_zero fun bb hbb => Finset.sum_eq_zero fun aa haa =>
    Finset.sum_eq_zero fun ll hll => ?_
  by_cases hs : c3 S aa.1 bb.1 ll.1 = 0
  · simp [hs]
  by_cases hg : c3 G aa.2 bb.2 ll.2 = 0
  · simp [hg]
  have hSb : S.coeff bb.1 ≠ 0 := by
    intro hz
    simp [c3, hz] at hs
  have hb1 : bb.1 ≤ h := (Polynomial.le_natDegree_of_ne_zero hSb).trans hY
  have hp : (aa.2, bb.2, ll.2) ∈ multiplesBox s q d e := by
    by_contra hp
    exact hg (hG aa.2 bb.2 ll.2 hp)
  have hM := (mem_multiples s q d e aa.2 bb.2 ll.2).mp hp
  have hS := hW aa.1 bb.1 ll.1 hs
  have hb := Finset.HasAntidiagonal.mem_antidiagonal.mp hbb
  have hl := Finset.HasAntidiagonal.mem_antidiagonal.mp hll
  have ht : (a, b, l) ∈ broadBox s h q e := by
    apply (mem_broad s h q e a b l).mpr
    refine ⟨ha, by omega, ?_⟩
    rw [← hb, ← hl]
    nlinarith only [hS, hM.2.2]
  exact False.elim (hnot ht)

noncomputable def quotientMap (s : ℕ) (S : Tri) (BT : Finset (ℕ × ℕ × ℕ)) :
    supp (F := F) BT →ₗ[F] (Tri ⧸ residualIdeal s S) :=
  (Ideal.Quotient.mkₐ F (residualIdeal s S)).toLinearMap.domRestrict (supp BT)

theorem multiples_le_kernel (S : Tri) (s h q d e : ℕ)
    (hS : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0)
    (hY : S.natDegree ≤ h) (hW : WtLE 0 q 1 d S) :
    (multiplesBox s q d e).card ≤
      finrank F (LinearMap.ker (quotientMap s S (broadBox s h q e))) := by
  let BT := broadBox s h q e
  let MT := multiplesBox s q d e
  have hMT : ∀ p ∈ MT, p.1 < s := by
    rintro ⟨a, b, l⟩ hp
    exact ((mem_multiples s q d e a b l).mp hp).1
  have hcov : ∀ G ∈ supp (F := F) MT, ∀ a b l,
      a < s → c3 (S * G) a b l ≠ 0 → (a, b, l) ∈ BT :=
    fun G hG a b l ha hn => product_covered S G s h q d e hY hW hG a b l ha hn
  have hinj := multipleMap_injective S s BT MT hS hMT hcov
  have hsub : LinearMap.range (multipleMap S BT MT) ≤
      LinearMap.ker (quotientMap s S BT) := by
    rintro _ ⟨G, rfl⟩
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mkₐ F _ _ = 0
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (multipleMap_mem S s BT MT hcov G)
  calc MT.card = finrank F (supp (F := F) MT) := (finrank_supp MT).symm
    _ = finrank F (LinearMap.range (multipleMap S BT MT)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono hsub

theorem quotient_budget (S : Tri) (s h q d e : ℕ)
    (hS : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0)
    (hY : S.natDegree ≤ h) (hW : WtLE 0 q 1 d S) :
    finrank F (LinearMap.range (quotientMap s S (broadBox s h q e))) +
      (multiplesBox s q d e).card ≤ (broadBox s h q e).card := by
  have hm := multiples_le_kernel S s h q d e hS hY hW
  have hr := LinearMap.finrank_range_add_finrank_ker (quotientMap s S (broadBox s h q e))
  rw [finrank_supp] at hr
  omega

end P64C7Multiples
end ProximityPrize.SubmissionBinaryLower
