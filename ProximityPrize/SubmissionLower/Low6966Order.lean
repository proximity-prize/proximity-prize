import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.Fat6966Defs
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false

-- merged module Fat6966Family
section Merged_Fat6966Family

-- merged module ModelExactPole6966
section Merged_ModelExactPole6966

set_option Elab.async false
namespace ModelExactPole6966
noncomputable section
open P1 (I K node)
open K1_13 (Geom embed extend)
open Polynomial
open scoped Polynomial

/-- A common shift by a multiple of the pole preserves all labeled residues. -/
theorem exists_shifted {cap u del Γ A n} (M : P1.ModelAt cap u del) (F : P1.FamilyAt A M Γ)
    (T : (Polynomial K)) (multiple : M.E ∣ T) (positive : 1 ≤ n) (small : n ≤ 2600)
    (available : n ≤ M.E.natDegree) (degree : ∀ γ ∈ Γ, (F.scalar γ - T).natDegree ≤ 131071 + n) :
    ∃ P : K1_13.PoleData Γ (fun γ => F.scalar γ - T), P.H.natDegree = n := by
  have hmax : n ≤ (extend M.E).natDegree := by simpa only [extend, natDegree_map] using available
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : (Polynomial K)} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [P1.ModelAt.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩, ?_⟩
  · rw [hd]
    exact ⟨positive, small⟩
  · intro i hz
    obtain ⟨U, hU⟩ := hdiv
    have he : (extend M.E).eval (embed (node i)) ≠ 0 := by
      rw [Polynomial.eval_map_apply]
      exact (map_ne_zero embed).mpr (M.E_nodes i)
    apply he
    change (M.E.map embed).eval _ = 0
    rw [hU, Polynomial.eval_mul, hz, zero_mul]
  · intro γ hγ
    rw [hd]
    exact degree γ hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn := (F.mark γ hγ).identity
    have orig : M.factor * M.amplitude γ * F.scalar γ + C (M.label γ) * M.Q =
        M.E * M.decoder (F.mark γ hγ).bad := by rw [← eqn]; ring
    have mapped := congrArg (Polynomial.map embed) orig
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at mapped
    rw [← amp]
    have residue := mapped ▸ hdiv.trans (dvd_mul_right (extend M.E) (extend (M.decoder (F.mark γ hγ).bad)))
    have shift := hdiv.trans (Polynomial.map_dvd embed multiple)
    have sub := dvd_sub residue (shift.mul_left (extend M.factor * extend (M.amplitude γ)))
    simpa only [extend, Polynomial.map_sub, mul_sub, sub_add_eq_add_sub] using sub
  · exact hd

/-- Trim the pole to the actual overhead without changing any marked residue. -/
theorem exists_pole {cap u D Γ A} (M : P1.ModelAt cap u D) (F : P1.FamilyAt A M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2600) :
    ∃ P : K1_13.PoleData Γ F.scalar, P.H.natDegree = M.overhead.toNat := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    change M.overhead.toNat ≤ M.E.natDegree
    unfold P1.ModelAt.overhead
    omega
  have degree : ∀ γ ∈ Γ, (F.scalar γ - 0).natDegree ≤ 131071 + M.overhead.toNat := by
    intro γ hg
    rw [sub_zero]
    rcases (F.mark γ hg).scalar_degree with zero | h
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  let HasPole (s : K → (Polynomial K)) : Prop :=
    ∃ P : K1_13.PoleData Γ s, P.H.natDegree = M.overhead.toNat
  have eq : (fun γ => F.scalar γ - 0) = F.scalar := funext fun γ => sub_zero _
  apply (congrArg HasPole eq).mp
  exact exists_shifted M F 0 (dvd_zero _) (by omega : 1 ≤ M.overhead.toNat)
    (by omega) (by simpa only [extend, natDegree_map] using hmax) degree

end
end ModelExactPole6966

end Merged_ModelExactPole6966

-- merged module R6960Low6960Primary
section Merged_R6960Low6960Primary

noncomputable section
set_option Elab.async false
namespace LowProfile6966
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)
open scoped Polynomial

abbrev agreement : ℕ := 179769
abbrev physicalDegree : ℕ := 133400


abbrev need : ℕ := layerNeed agreement physicalDegree






























end LowProfile6966

end
end Merged_R6960Low6960Primary

-- merged module R6960Low6966Fat
section Merged_R6960Low6966Fat


set_option Elab.async false
section
namespace Low6966Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open P3_6_4 (eval_cleared order_cleared)
















































end
end Low6966Fat
end


namespace LowProfile6966
open K1_13 (extend)
open Low6966Fat (Holds)












end LowProfile6966

end Merged_R6960Low6966Fat

end Merged_Fat6966Family

-- merged module Low6966Order
section Merged_Low6966Order

-- merged module R6960Low6966Profile
section Merged_R6960Low6966Profile

set_option Elab.async false

namespace LowProfile6966
open P3 (I K node)
open K1_13 (Row Shape InBox shape OrderAt extend)
open scoped Polynomial BigOperators




















end LowProfile6966

end Merged_R6960Low6966Profile

-- merged module R6960Low6966Order
section Merged_R6960Low6966Order
set_option Elab.async false
namespace Low6966Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)

















end
end Low6966Order
section
namespace Low6966OrderProof
noncomputable section
open P3 (I K)

open K1_13 (Row InBox shape Contact)





end
end Low6966OrderProof
end
section
namespace Low6966OrderProof
noncomputable section
open Polynomial
open P3 (I K node)



open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)

























































































































end
end Low6966OrderProof
end
section
set_option maxRecDepth 12000
namespace Low6966OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)



open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open K1_13_3_1 (eval_line line_contacts_zero)
open K1_13_3_1 (order_of_locator_lines)






















































































































end
end Low6966OrderProof_1
end
section
namespace Low6966OrderProof_2
noncomputable section
open Polynomial

open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open P0_9_3_2 (translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd)























































































end
end Low6966OrderProof_2
end
section
namespace Low6966OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)


open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

























































































































































































































end
end Low6966OrderProof_3
end
namespace Low6966Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial





































end
end Low6966Order

end Merged_R6960Low6966Order

end Merged_Low6966Order
