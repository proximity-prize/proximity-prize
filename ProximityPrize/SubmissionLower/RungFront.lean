import ProximityPrize.SubmissionLower.PortFrontA
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open K1_8 (certificate_output_zero)
theorem eval_liftX (f : (Polynomial K)) (x : K) : (liftX f).eval (C x) = C (f.eval x) :=
  K1_8.eval_liftX f x
def constantsInFrac : K →+* Frac :=
  K1_8.seedInclusion.comp Polynomial.C
theorem extend_liftX (G : (Polynomial K)) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G
end
end P1
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0 (type_one_bad_count_of_syndromes)
open P0 (constantRankCount nativeMoments independent_nativeMoments)
open K1_1
theorem excludes_full_rank {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ q = x i) (u v : ι → F) (γ : F) (k l t : ℕ)
    (hsize : k + l + t ≤ Fintype.card ι) (P : (Polynomial F)) (hp : P.degree < k)
    (S : Finset ι) (hs : S.card ≤ t) (hagree : ∀ i ∉ S, u i + γ * v i = P.eval (x i)) :
    ((stacked q x u v l t).map (evalRingHom γ)).rank ≠ t + 1 := by
  classical
  let E := locator x S
  have hd : E.natDegree ≤ t := (locator_natDegree x S).le.trans hs
  let z : Fin (t+1) → F := fun j => E.coeff j.val
  let B := (stacked q x u v l t).map (evalRingHom γ)
  have hv : B.mulVecLin z = 0 :=
    locator_annihilates_stacked q x hx hfixed u v γ k l t hsize P hp S hs hagree
  intro hr
  have hi := Strata.matrix_injective_of_full_column_rank B (by rwa [Fintype.card_fin])
  have hz : z = 0 := hi (hv.trans (map_zero B.mulVecLin).symm)
  have h := congrFun hz (⟨E.natDegree, by omega⟩ : Fin (t+1))
  change E.coeff E.natDegree = 0 at h
  exact one_ne_zero ((locator_monic x S).coeff_natDegree.symm.trans h)
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P1
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1_6 (certificate_shifts_annihilate_generic)
open K1_6 (lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator common_node_count)
theorem count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc
end P1
end
