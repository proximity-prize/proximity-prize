import ProximityPrize.SubmissionLower.ThetaFlag
import ProximityPrize.SubmissionLower.Fast068

/-!
The theta rank bound for the contact blocks of the primary interpolation.
-/

namespace ThetaBlock
open MvPolynomial K1_13 K1_13_2 K1_13_2_2 ThetaCore

noncomputable section

theorem geom_char (n : ℕ) (h0 : 0 < n) (hn : n < K1.p) : ((n : ℕ) : Geom) ≠ 0 := by
  haveI : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  intro h
  have hd := (CharP.cast_eq_zero_iff Geom K1.p n).mp h
  have := Nat.le_of_dvd h0 hd
  omega

theorem shear_eq : shearImage = shear (k := Geom) := by
  funext j
  fin_cases j <;> first | rfl | simp [shearImage, shear]

/-- The theta count of a flag: monomials of its degree with index from
`lower - 3 (upper + 1 - order)` to `order - 1`. -/
def thetaCount (F : Flag) : ℤ :=
  cumulative F.degree (F.order - 1) -
    cumulative F.degree (F.lower - 3 * (F.upper + 1 - F.order) - 1)

theorem window_finite (d l u R : ℤ) : (window d l u R).Finite :=
  finite_of_grade (d := d) fun _ h => h.1

def windowColumns (d l u R : ℤ) : Finset JetExp := (window_finite d l u R).toFinset

theorem window_card (h : CumulativeCount) (d l u R : ℤ) (hlo : l - 3 * (u + 1 - R) ≤ R) :
    ((windowColumns d l u R).card : ℤ) =
      cumulative d (R - 1) - cumulative d (l - 3 * (u + 1 - R) - 1) := by
  classical
  have hsub : cumulativeColumns d (l - 3 * (u + 1 - R) - 1) ⊆ cumulativeColumns d (R - 1) := by
    intro e he
    rw [mem_cumulativeColumns] at he ⊢
    exact ⟨he.1, by have := he.2; omega⟩
  have heq : windowColumns d l u R =
      cumulativeColumns d (R - 1) \ cumulativeColumns d (l - 3 * (u + 1 - R) - 1) := by
    ext e
    rw [windowColumns, Set.Finite.mem_toFinset, Finset.mem_sdiff, mem_cumulativeColumns,
      mem_cumulativeColumns]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h3⟩, fun hh => ?_⟩
      have a : (e.weight oldWeight : ℤ) ≤ l - 3 * (u + 1 - R) - 1 := hh.2
      have b : l - 3 * (u + 1 - R) ≤ (e.weight oldWeight : ℤ) := h2
      omega
    · rintro ⟨⟨h1, h3⟩, h4⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hc' : ¬ (l - 3 * (u + 1 - R) ≤ (e.weight oldWeight : ℤ)) := hc
      exact h4 ⟨h1, by omega⟩
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), h, h]

/-- The theta rank bound for a flag. -/
theorem flag_rank (F : Flag) (hu : 0 ≤ F.upper) (hup : F.upper < 2130706433)
    (hR0 : 0 ≤ F.order) (hR : F.order ≤ F.upper + 1)
    (hlo : F.lower - 3 * (F.upper + 1 - F.order) ≤ F.order) :
    (Module.finrank Geom (LinearMap.range (flagContact F)) : ℤ) ≤ thetaCount F := by
  haveI : Module.Finite Geom (restrictSupport Geom (oldExponents F)) :=
    restrictSupport_finite (oldExponents_finite F)
  haveI : Module.Finite Geom
      (restrictSupport Geom (window F.degree F.lower F.upper F.order)) :=
    restrictSupport_finite (window_finite _ _ _ _)
  have h := theta_rank (k := Geom) (s := oldExponents F) F.degree F.lower F.upper F.order
    (fun e he => ⟨he.1, he.2.1, he.2.2.1⟩) hu hR0 hR
    (fun n h0 hn => geom_char n h0 (by have : K1.p = 2130706433 := rfl; omega))
    (flagContact F) (fun x => by rw [← shear_eq]; rfl)
  have hfin : Module.finrank Geom
      (restrictSupport Geom (window F.degree F.lower F.upper F.order)) =
      (windowColumns F.degree F.lower F.upper F.order).card := by
    conv_lhs => rw [← (window_finite F.degree F.lower F.upper F.order).coe_toFinset]
    exact finrank_restrictSupport_finset _
  have h' := h.trans (le_of_eq hfin)
  have hc := window_card K1_13_2_2_2.proof F.degree F.lower F.upper F.order hlo
  unfold thetaCount
  exact (Int.ofNat_le.mpr h').trans (le_of_eq hc)

/-- The theta rank bound for the block `i` of the primary interpolation. -/
theorem block_rank (i : BlockIndex) (h1 : 2999 ≤ i.1.val + i.2.val)
    (h2 : i.1.val + i.2.val ≤ 4650) :
    (Module.finrank Geom (LinearMap.range (originBlock i)) : ℤ) ≤
      thetaCount (activeFlag i) := by
  have h := K1_13_2_2_1.proof i
  have hj := i.2.isLt
  have hf := flag_rank (activeFlag i)
    (by show (0 : ℤ) ≤ min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)); omega)
    (by show min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)) < 2130706433; omega)
    (by show (0 : ℤ) ≤ 3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650); omega)
    (by
      show 3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650) ≤
        min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)) + 1
      omega)
    (by
      show -((i.2.val : ℤ) - 1650) - 3 * (min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)) + 1 -
        (3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650))) ≤
          3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650)
      omega)
  have h' : (Module.finrank Geom (LinearMap.range (originBlock i)) : ℤ) ≤
      (Module.finrank Geom (LinearMap.range (flagContact (activeFlag i))) : ℤ) := by
    exact_mod_cast h
  exact h'.trans hf


end
end ThetaBlock
