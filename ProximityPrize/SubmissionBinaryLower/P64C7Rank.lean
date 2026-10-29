import ProximityPrize.SubmissionBinaryLower.P64C7Lift
import ProximityPrize.SubmissionBinaryLower.P64C7Multiples

/-!
# The bounded-pole count in rank form

The image of `V^s` times the input box and the independent lifted monomials
form disjoint subspaces of the broad-box image. Truncated multiples of `S`
provide the complementary lower bound on its kernel.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Rank

open Polynomial P64Found P64C7 P64C7Boxes P64C7Truncation P64C7Multiples P64C7Lift Module

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma Vpow_support (G : Tri) (s h q e : ℕ) (hG : G ∈ supp (inputBox s h q e)) :
    (Polynomial.X : Tri) ^ s * G ∈ supp (broadBox s h q e) := by
  intro a b l hnot
  unfold c3
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hb
  · apply hG a (b - s) l
    intro hp
    have hm := (mem_input s h q e a (b - s) l).mp hp
    apply hnot
    apply (mem_broad s h q e a b l).mpr
    refine ⟨hm.1, by omega, ?_⟩
    have heq : q * b = q * (b - s) + q * s := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hb]
    omega
  · simp

lemma lifted_subset_broad (Λ : Finset (ℕ × ℕ)) (s h q e ν : ℕ)
    (hΛ : ∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s) :
    lifted Λ q (e + q * s) ⊆ broadBox s h q e := by
  rintro ⟨a, b, l⟩ hp
  obtain ⟨hpair, hwt⟩ := (mem_lifted Λ q (e + q * s) a b l).mp hp
  have hb := hΛ (a, b) hpair
  exact (mem_broad s h q e a b l).mpr ⟨hb.1, by omega, hwt⟩

lemma residual_le_box (s : ℕ) (S : Tri) : residualIdeal s S ≤ boxIdeal s S := by
  apply Ideal.span_le.mpr
  intro R hR
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
  rcases hR with rfl | rfl
  · simpa [U] using U_pow_mem s S
  · exact S_mem _ _

noncomputable def phi (S : Tri) (s h q e : ℕ) :
    supp (F := F) (inputBox s h q e) →ₗ[F] (Tri ⧸ residualIdeal s S) :=
  (Ideal.Quotient.mkₐ F (residualIdeal s S)).toLinearMap.comp
    ((LinearMap.mulLeft F ((Polynomial.X : Tri) ^ s)).comp (supp (inputBox s h q e)).subtype)

lemma range_phi_le (S : Tri) (s h q e : ℕ) :
    LinearMap.range (phi S s h q e) ≤
      LinearMap.range (quotientMap s S (broadBox s h q e)) := by
  rintro _ ⟨G, rfl⟩
  exact ⟨⟨_, Vpow_support G.1 s h q e G.2⟩, rfl⟩

lemma range_lift_le (S : Tri) (Λ : Finset (ℕ × ℕ)) (s h q e ν : ℕ)
    (hΛ : ∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s) :
    LinearMap.range (quotientMap s S (lifted Λ q (e + q * s))) ≤
      LinearMap.range (quotientMap s S (broadBox s h q e)) := by
  rintro _ ⟨G, rfl⟩
  exact ⟨⟨G.1, supp_mono (lifted_subset_broad Λ s h q e ν hΛ) G.2⟩, rfl⟩

lemma lifted_map_injective (S : Tri) (s : ℕ) (LT : Finset (ℕ × ℕ × ℕ))
    (hind : ∀ R ∈ supp (F := F) LT, R ∈ boxIdeal s S → R = 0) :
    Function.Injective (quotientMap s S LT) := by
  apply (injective_iff_map_eq_zero (quotientMap s S LT)).mpr
  intro G hG
  apply Subtype.ext
  apply hind G.1 G.2
  apply residual_le_box s S
  change Ideal.Quotient.mkₐ F _ G.1 = 0 at hG
  rw [Ideal.Quotient.mkₐ_eq_mk] at hG
  exact Ideal.Quotient.eq_zero_iff_mem.mp hG

lemma ranges_disjoint (S : Tri) (s h q e : ℕ) (LT : Finset (ℕ × ℕ × ℕ))
    (hind : ∀ R ∈ supp (F := F) LT, R ∈ boxIdeal s S → R = 0) :
    Disjoint (LinearMap.range (phi S s h q e)) (LinearMap.range (quotientMap s S LT)) := by
  rw [disjoint_iff_inf_le]
  rintro v ⟨⟨G, hG⟩, ⟨L, hL⟩⟩
  have heq : Ideal.Quotient.mkₐ F (residualIdeal s S) L.1 =
      Ideal.Quotient.mkₐ F (residualIdeal s S) ((Polynomial.X : Tri) ^ s * G.1) := hL.trans hG.symm
  simp only [Ideal.Quotient.mkₐ_eq_mk] at heq
  have hd := Ideal.Quotient.eq.mp heq
  have hv : (Polynomial.X : Tri) ^ s * G.1 ∈ boxIdeal s S :=
    Ideal.mul_mem_right _ _ (V_pow_mem s S)
  have hLj : L.1 ∈ boxIdeal s S := by
    have hh := add_mem (residual_le_box s S hd) hv
    simpa only [sub_add_cancel] using hh
  have hzero := hind L.1 L.2 hLj
  rw [Submodule.mem_bot]
  calc v = quotientMap s S LT L := hL.symm
    _ = 0 := by
      change Ideal.Quotient.mkₐ F _ L.1 = 0
      rw [hzero, map_zero]

theorem rank_bound_of_independent (S : Tri) (s h q d e ν : ℕ) (Λ : Finset (ℕ × ℕ))
    (hS : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0)
    (hY : S.natDegree ≤ h) (hW : WtLE 0 q 1 d S)
    (hΛ : ∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s)
    (hind : ∀ R ∈ supp (F := F) (lifted Λ q (e + q * s)), R ∈ boxIdeal s S → R = 0) :
    finrank F (LinearMap.range (phi S s h q e)) + (multiplesBox s q d e).card +
      (lifted Λ q (e + q * s)).card ≤ (broadBox s h q e).card := by
  let L := LinearMap.range (quotientMap s S (lifted Λ q (e + q * s)))
  let V := LinearMap.range (phi S s h q e)
  have hLdim : finrank F L = (lifted Λ q (e + q * s)).card := by
    rw [LinearMap.finrank_range_of_inj (lifted_map_injective S s _ hind), finrank_supp]
  have hdis : Disjoint V L := ranges_disjoint S s h q e _ hind
  have hsup : V ⊔ L ≤ LinearMap.range (quotientMap s S (broadBox s h q e)) :=
    sup_le (range_phi_le S s h q e) (range_lift_le S Λ s h q e ν hΛ)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq V L
  rw [hdis.eq_bot, finrank_bot, add_zero, hLdim] at hd
  have hu := Submodule.finrank_mono hsup
  have hm := quotient_budget S s h q d e hS hY hW
  change finrank F V + (multiplesBox s q d e).card + (lifted Λ q (e + q * s)).card ≤ _
  omega

/-- Theorem DLT in rank form, including the independent-monomial cardinality bound. -/
theorem rank_bound (S : Tri) (s μ ν h q d e : ℕ) (R'' : Polynomial (Polynomial F))
    (hS : OrdAtLeast μ S)
    (hS0 : S.map (Polynomial.constantCoeff (R := Polynomial F)) = Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) (hY : S.natDegree ≤ h) (hW : WtLE 0 q 1 d S) :
    ∃ Λ : Finset (ℕ × ℕ), (∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s) ∧
      (tri s).card - (tri (s - μ)).card ≤ Λ.card ∧
      finrank F (LinearMap.range (phi S s h q e)) + (multiplesBox s q d e).card +
        (lifted Λ q (e + q * s)).card ≤ (broadBox s h q e).card := by
  have hR'' : R'' ≠ 0 := by intro hz; simp [hz] at hu
  have hSmap : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0 := by
    rw [hS0]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hR''
  obtain ⟨Λ, hΛ, hcard, hind⟩ := exists_lifted_independent s μ ν S R'' hS hS0 hu
  exact ⟨Λ, hΛ, hcard, rank_bound_of_independent S s h q d e ν Λ hSmap hY hW hΛ (hind q _)⟩

end P64C7Rank
end ProximityPrize.SubmissionBinaryLower
