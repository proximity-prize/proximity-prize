import ProximityPrize.SubmissionLower.ZoU8PJb
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R_3_2_3
noncomputable section
open MvPolynomial
private theorem mem_radical_annihilator_of_torsion {R:Type} [CommRing R]
    [IsNoetherianRing R] (a :R) (K:Submodule R R)
    (h : ∀ x∈K,∃ n:ℕ,a^n*x=0) :
    a∈K.annihilator.radical:= by
  let f :=LinearMap.mulLeft R a
  obtain ⟨n,hn⟩:=Filter.eventually_atTop.mp f.eventually_iSup_ker_pow_eq
  refine Ideal.mem_radical_iff.mpr ⟨n,Module.mem_annihilator.mpr ?_⟩
  intro x
  obtain ⟨m,hm⟩:=h x x.property
  have hker : (x :R)∈LinearMap.ker (f^m) := by
    rw [LinearMap.pow_mulLeft,LinearMap.mem_ker]
    exact hm
  have hinf :=(le_iSup (fun i=>LinearMap.ker (f^i)) m) hker
  rw [hn n le_rfl] at hinf
  rw [LinearMap.pow_mulLeft,LinearMap.mem_ker] at hinf
  exact Subtype.ext hinf
private theorem pow_inf_eq_bot {R:Type} [CommRing R] [IsNoetherianRing R]
    (M:Ideal R) (K:Submodule R R) (h:M≤K.annihilator.radical) :
    ∃ N :ℕ,∀ b≥N,(M^b:Submodule R R) ⊓ K = ⊥ := by
  obtain ⟨n,hn⟩:=Ideal.exists_pow_le_of_le_radical_of_fg h M.fg_of_isNoetherianRing
  obtain ⟨s,hs⟩:=M.exists_pow_inf_eq_pow_smul K
  refine ⟨s+n,fun b hb => ?_⟩
  have hpow:M^(b - s)≤K.annihilator :=
    (Ideal.pow_le_pow_right (by omega)).trans hn
  have hs' := hs b (by omega)
  have htop (i:ℕ) :M^i•(⊤ : Submodule R R)=(M^i:Submodule R R) :=
    Ideal.mul_top _
  simp only [htop] at hs'
  rw [hs']
  exact le_bot_iff.mp (by
    calc
      M^(b - s)•((M^s :Submodule R R) ⊓ K)≤K.annihilator•K :=
        Submodule.smul_mono hpow inf_le_right
      _ = ⊥ := Submodule.annihilator_smul _)
end
end K1_14_3R_3_2_3
