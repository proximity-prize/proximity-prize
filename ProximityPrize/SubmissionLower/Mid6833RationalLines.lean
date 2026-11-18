/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833OrbitLines
import ProximityPrize.SubmissionLower.Mid6833ResidueInstances
import ProximityPrize.SubmissionLower.Mid6833ResidueCode
namespace Genuine.OrbitLines
open Polynomial Finset Frontier.ResidueOrbit
open scoped Polynomial BigOperators Classical Function
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 8000
variable {F K I G J : Type*} [Field F] [Field K] [Algebra F K] [Fintype I] [Fintype G] [Fintype J]
local instance mid6833Local_RationalLines_11  : DecidableEq K := Classical.decEq _

theorem map_fixed_powers (τ : K →ₐ[F] K) (P : K[X]) (h : P.map τ.toRingHom=P) (n:ℕ) :
    P.map (τ^n).toRingHom = P := by
  ext i
  have eq : τ (P.coeff i)=P.coeff i := by simpa [coeff_map] using congrArg (fun q:K[X] => q.coeff i) h
  simp only [coeff_map,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,AlgHom.coe_pow]
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply,eq] using ih

private theorem lcm_safe (f : J → K[X]) (t : K) (dj : ∀j, (f j).eval t≠0) :
    (univ.lcm f).eval t≠0 := by
  have divides : univ.lcm f ∣ ∏ j, f j := by
    apply Finset.lcm_dvd_iff.mpr
    intro j hj
    exact Finset.dvd_prod_of_mem f hj
  obtain ⟨R,hr⟩ := divides
  have all : ((∏ j, f j) : K[X]).eval t≠0 := by
    rw [eval_prod]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => dj j)
  rw [hr,eval_mul] at all
  exact left_ne_zero_of_mul all

theorem actual_pole_line (x : I ↪ K) (hn : Fintype.card I=262144)
    (τ : K →ₐ[F] K) (jval : J → ℕ) (jsize : Fintype.card J=6)
    (D : K[X]) (degD : D.natDegree=9554)
    (disjoint : Pairwise (IsCoprime on fun j:J => D.map (τ^jval j).toRingHom))
    (safe : ∀ i, D.eval (x i)≠0) (xfix : ∀i, τ (x i)=x i)
    (c : G ↪ F) (origin v : K) (vn : v≠0) (word : I → F)
    (ag : ∀g : G, ∃P : K[X], P.natDegree≤131071 ∧
      179740 ≤ (univ.filter (fun i => P.eval (x i)=
        (algebraMap F K (word i) + (origin+c g • v))/(D.eval (x i)))).card) :
    Fintype.card G≤596 := by
  classical
  let θ (j : J) := τ ^ jval j
  let seed (g:G) := origin+c g • v
  have nz : D≠0 := fun h => by rw [h,natDegree_zero] at degD; contradiction
  have sinj : Function.Injective seed := by
    intro g h eq
    apply c.injective
    change origin + _ = origin + _ at eq
    have e := add_left_cancel eq
    exact (FaithfulSMul.algebraMap_injective F K) (mul_right_cancel₀ vn (by simpa only [Algebra.smul_def] using e))
  have get (g:G) : ∃T : K[X], T.natDegree≤140625 ∧ T.map τ.toRingHom=T ∧
      D∣T+C (seed g) ∧ 179740≤(univ.filter (fun i => T.eval (x i)=algebraMap F K (word i))).card := by
    obtain ⟨P,hp,good⟩ := ag g
    let S := univ.filter (fun i => P.eval (x i)=(algebraMap F K (word i)+seed g)/(D.eval (x i)))
    have size : 179740 ≤ S.card := good
    obtain ⟨T,dt,fix,res,fit⟩ := (Frontier.LinearKernel.residue_iff τ.toRingHom x (fun i => algebraMap F K (word i))
      D 9554 131071 (seed g) S (fun i _ => xfix i) (fun i _ => τ.commutes _)
      degD nz (fun i _ => safe i) (by omega)).mp
      ⟨P,hp,fun i hi => (mem_filter.mp hi).2⟩
    exact ⟨T,dt,fix,res,size.trans (card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _,fit i hi⟩))⟩
  choose T dt fix res fit using get
  have inj : Function.Injective T := by
    intro g h eq
    apply sinj
    by_contra neq
    have div : D ∣ C (seed g-seed h) := by
      have a := dvd_sub (res g) (res h)
      rw [eq,add_sub_add_left_eq_sub,←map_sub] at a
      exact a
    have d := natDegree_le_of_dvd div (C_ne_zero.mpr (sub_ne_zero.mpr neq))
    rw [degD,natDegree_C] at d
    omega
  let f (j:J) := D.map (θ j).toRingHom
  have regular (i:I) : (univ.lcm f).eval (x i)≠0 := by
    have dj (j:J) : (f j).eval (x i)≠0 := by
      have h := (θ j).injective.ne (safe i)
      rw [map_zero] at h
      have itfix (n:ℕ) : (τ^n) (x i)=x i := by
        simp only [AlgHom.coe_pow]; induction n with
        | zero => rfl
        | succ n ih => simpa only [Function.iterate_succ_apply,xfix] using ih
      have ev := eval_map_apply (p:=D) (θ j).toRingHom (x i)
      change (f j).eval (θ j (x i)) = θ j (D.eval (x i)) at ev
      rw [show θ j (x i)=x i from itfix _] at ev
      intro hz
      exact h (ev.symm.trans hz)
    exact lcm_safe f _ dj
  have ld := orbit_degree θ D nz disjoint
  rw [jsize,degD] at ld
  have result := line_cap x (fun i => algebraMap F K (word i)) θ
    D D 1 1 140625 83301 179740 597 3 409 dvd_rfl (⟨0,1,by simp⟩) regular (by omega)
    (by omega) (by rw [hn]; intro s h; omega) (by rw [hn]; decide +kernel)
    c origin v ⟨T,inj⟩ (fun g =>
      ⟨dt g,fun j => map_fixed_powers τ _ (fix g) _,by simpa [seed] using res g⟩) fit
  omega

end
#print axioms actual_pole_line
end Genuine.OrbitLines
