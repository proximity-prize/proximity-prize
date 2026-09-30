import ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceSourceCounts6814
open SecondJetSupport SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

def Bounds (P : WholeSpaceCube6814.Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, 2*e 1+e 3 ≤ 31 ∧ e 1 ≤ 14 ∧
    e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff (e 1)

theorem exists_contact_kernel
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (hb : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hu : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hl : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hd : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K) (bound : ℕ)
    (hcard : bound+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (D h+B-1)/w) ≤ Fintype.card I) :
    ∃ V : Submodule K (WholeSpaceCube6814.Poly (K := K)), Module.Finite K V ∧
      bound ≤ Module.finrank K V ∧
      (∀ P ∈ V, ∀ d ∈ P.support, d ∈ Set.range e) ∧
      (∀ P ∈ V, ∀ n, MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes n) (u0 n) (u1 n) P)) := by
  classical
  let caps := fun h => (D h+B-1)/w
  let f := SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K
      (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetRelaxedSpace.source (K := K) m L B s U caps :=
    (coefficientLocal e m (nodes n) (u0 n) (u1 n)).codRestrict _
      (SecondJetRelaxedGlobalMap.coefficientLocal_mem e m L B s U w D hw
        (nodes n) (u0 n) (u1 n) hb hs hu hl hd)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have htarget : Module.finrank K (N → f.range) ≤
      Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U caps := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    exact Nat.mul_le_mul_left _
      (SecondJetRelaxedGlobalMap.local_rank_le_count m L B s U caps)
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hdimI : Module.finrank K (I → K)=Fintype.card I := by simp
  have hkernel : bound ≤ Module.finrank K g.ker := by
    dsimp only [caps] at htarget
    omega
  let recon : g.ker →ₗ[K] WholeSpaceCube6814.Poly (K := K) :=
    (FiniteMonomials.reconstruct e).comp g.ker.subtype
  have hrecon : Function.Injective recon := by
    intro a b hh
    apply Subtype.ext
    exact FiniteMonomials.reconstruct_injective e he hh
  let V := recon.range
  have hdimV : bound ≤ Module.finrank K V := by
    rw [LinearMap.finrank_range_of_inj hrecon]
    exact hkernel
  refine ⟨V,inferInstance,hdimV,?_,?_⟩
  · rintro P ⟨c,rfl⟩
    exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c.val,rfl⟩
  · rintro P ⟨c,rfl⟩ n
    have hc : g c.val=0 := c.property
    have hz := congrArg Subtype.val (congrFun hc n)
    change SecondJetRank.contactMap (K := K) m
      (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val)=0 at hz
    have hc' : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    have hh := untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom
      Polynomial.X m _ SecondJetLocal.contact_X hc'
    exact SecondJetGlobalDifferentiation.nested_to_flat_contact _ m hh

end
end ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
