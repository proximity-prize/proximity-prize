import ProximityPrize.SubmissionLower.Numeric2Aux
import ProximityPrize.SubmissionLower.Fast040

set_option Elab.async false
namespace ModelExactPole
noncomputable section
open P1 (I K node)
open K1_13 (Geom embed extend)
open Polynomial
open scoped Polynomial

/-- A common shift by a multiple of the pole preserves all labeled residues. -/
theorem exists_shifted {cap u del Γ A n} (M : P1.ModelAt cap u del) (F : P1.FamilyAt A M Γ)
    (T : K[X]) (multiple : M.E ∣ T) (positive : 1 ≤ n) (small : n ≤ 2600)
    (available : n ≤ M.E.natDegree) (degree : ∀ γ ∈ Γ, (F.scalar γ - T).natDegree ≤ 131071 + n) :
    ∃ P : K1_13.PoleData Γ (fun γ => F.scalar γ - T), P.H.natDegree = n := by
  have hmax : n ≤ (extend M.E).natDegree := by simpa only [extend, natDegree_map] using available
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
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
  let HasPole (s : K → K[X]) : Prop :=
    ∃ P : K1_13.PoleData Γ s, P.H.natDegree = M.overhead.toNat
  have eq : (fun γ => F.scalar γ - 0) = F.scalar := funext fun γ => sub_zero _
  apply (congrArg HasPole eq).mp
  exact exists_shifted M F 0 (dvd_zero _) (by omega : 1 ≤ M.overhead.toNat)
    (by omega) (by simpa only [extend, natDegree_map] using hmax) degree

end
end ModelExactPole
