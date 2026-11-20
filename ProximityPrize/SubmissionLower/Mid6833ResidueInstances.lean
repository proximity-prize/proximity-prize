/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833ResidueRank
import CompPoly.Fields.KoalaBear.Ext6
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Coprime.Lemmas
namespace Frontier.ResidueOrbit
open Polynomial Finset KoalaBear
open scoped Polynomial Classical BigOperators Function
noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 200000
local instance mid6833Local_ResidueInstances_11  {K : Type*} : DecidableEq K := Classical.decEq _
private theorem koala_finrank : Module.finrank KoalaBear.Field Ext6 = 6 := by
  have eq := Module.card_eq_pow_finrank (K:=KoalaBear.Field) (V:=Ext6)
  rw [KoalaBear.card_ext6,show Fintype.card KoalaBear.Field = fieldSize from ZMod.card _] at eq
  exact pow_right_injective₀ (by decide : 0<fieldSize) (by decide : fieldSize≠1) eq.symm

/-- Coprime conjugates contribute their full degree to the orbit lcm. -/
theorem orbit_degree {F K J : Type*} [Field F] [Field K] [Algebra F K] [Fintype J]
    (θ : J → K →ₐ[F] K) (D : K[X]) (hn : D≠0)
    (disjoint : Pairwise (IsCoprime on fun j => D.map (θ j).toRingHom)) :
    Fintype.card J * D.natDegree ≤ (univ.lcm (fun j => D.map (θ j).toRingHom)).natDegree := by
  classical
  let f (j:J) := D.map (θ j).toRingHom
  have nz (j:J) : f j≠0 := Polynomial.map_ne_zero hn
  have dl : (∏ j, f j)∣univ.lcm f := Fintype.prod_dvd_of_coprime disjoint
    (fun j => Finset.dvd_lcm (mem_univ j))
  have ln : univ.lcm f≠0 := Finset.lcm_ne_zero_iff.mpr (fun j _ => nz j)
  have deg : (∏ j, f j).natDegree=Fintype.card J*D.natDegree := by
    rw [natDegree_prod _ _ (fun j _ => nz j)]
    simp [f]
  exact deg ▸ natDegree_le_of_dvd dl ln

/-- Direct Koala seed count for degree-bounded CRT-structured words, without
any repeated-word charge when the normalized word map is injective. -/
theorem orbit_seed_count {F K I J : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype I] [Fintype J]
    (nI : Fintype.card I=262144) (six : Module.finrank F K=6)
    (θ : J → K →ₐ[F] K) (D D' H L : K[X]) (W : ℕ)
    (low : W≤164806) (part : D'∣D) (cop : IsCoprime D' H)
    (large : W<(univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree)
    (x : I ↪ K) (word : I → K) (E : Finset K)
    (g₀ : K) (T : E ↪ K[X])
    (deg : ∀ g, (T g).natDegree≤W) (fixed : ∀g j, (T g).map (θ j).toRingHom=T g)
    (res : ∀g:E, D∣H*T g+C (g.val-g₀)*L)
    (ag : ∀g, 179740≤(univ.filter (fun i => (T g).eval (x i)=word i)).card) :
    E.card≤70308 := by
  classical
  let S : Finset K[X] := (univ : Finset E).map T
  have rr (P : K[X]) (hP : P∈S) : ∃ z : K, (z,P)∈pairs θ D H L W := by
    change P∈univ.map T at hP
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hP
    exact ⟨g.val-g₀,deg g,fixed g,res g⟩
  have rk := short_orbit_rank θ D D' H L W part cop large S rr
  rw [six] at rk
  have n := small_carrier_count x nI word S rk (by
    intro P hP
    change P∈univ.map T at hP
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hP
    exact (deg g).trans low) (by
    intro P hP
    change P∈univ.map T at hP
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hP
    exact ag g)
  simpa only [S,Finset.card_map,Finset.card_univ,Fintype.card_coe] using n

/-- Specialize the generic statement before elaborating the lcm.  This keeps
the polynomial normalization instance on the Koala extension definitionally
identical to the one in the generic orbit theorem. -/
def koala_orbit_seeds {J : Type*} [Fintype J] :=
  orbit_seed_count (J:=J) (F:=KoalaBear.Field) (K:=Ext6) (I:=Fin 262144)
    (Fintype.card_fin 262144) koala_finrank

#print axioms orbit_degree
#print axioms orbit_seed_count
#print axioms koala_orbit_seeds
end
end Frontier.ResidueOrbit
