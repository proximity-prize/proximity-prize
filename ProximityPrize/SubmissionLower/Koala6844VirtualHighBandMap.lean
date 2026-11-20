import ProximityPrize.SubmissionLower.Koala6844VirtualHighGlobalBox


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical
noncomputable section
set_option autoImplicit false

variable {K : Type} [Field K]

abbrev BandIndex (gain y b c : ℕ) :=
  Fin gain × Fin (y + 1) × Fin (b + 1) × Fin (c + 1)

private def bandExponent {gain y b c : ℕ} (low w : ℕ) (i : BandIndex gain y b c) :
    Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![(low - w * i.2.1.val) + i.1.val, i.2.1.val, i.2.2.1.val, i.2.2.2.val]

def bandMap (K : Type) [Field K] (low w gain y b c : ℕ) :
    MvPolynomial (Fin 4) K →ₗ[K] (BandIndex gain y b c → K) :=
  LinearMap.pi fun i => MvPolynomial.lcoeff K (bandExponent low w i)

theorem mem_low_of_bandMap_zero {high low w gain y b c : ℕ}
    (hw : high ≤ low + gain) {Q : MvPolynomial (Fin 4) K}
    (hq : Q ∈ globalBox K high w y b c)
    (hz : bandMap K low w gain y b c Q = 0) :
    Q ∈ globalBox K low w y b c := by
  rw [mem_globalBox] at hq ⊢
  intro e he
  have ⟨hhigh, hy, hb, hc⟩ := hq e he
  refine ⟨?_, hy, hb, hc⟩
  by_contra! hn
  let i : BandIndex gain y b c :=
    ⟨⟨e 0 - (low - w * e 1), by omega⟩,
      ⟨e 1, Nat.lt_succ_of_le hy⟩,
      ⟨e 2, Nat.lt_succ_of_le hb⟩,
      ⟨e 3, Nat.lt_succ_of_le hc⟩⟩
  have eqe : bandExponent low w i = e := by
    ext j
    fin_cases j <;> simp [bandExponent, i, Matrix.cons_val_two, Matrix.cons_val_three]
    omega
  exact (MvPolynomial.mem_support_iff.mp he) (by
    have eq := congrFun hz i
    change MvPolynomial.lcoeff K (bandExponent low w i) Q = 0 at eq
    rw [eqe] at eq
    exact eq)

theorem finrank_bandMap_ker_lower {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (low w gain y b c : ℕ) (q : V →ₗ[K] MvPolynomial (Fin 4) K) :
    Module.finrank K V ≤
      gain * (y + 1) * (b + 1) * (c + 1) +
      Module.finrank K (LinearMap.ker ((bandMap K low w gain y b c).comp q)) := by
  let f := (bandMap K low w gain y b c).comp q
  have hr : Module.finrank K f.range ≤ gain * (y + 1) * (b + 1) * (c + 1) := by
    apply f.range.finrank_le.trans
    rw [Module.finrank_fintype_fun_eq_card]
    simp [BandIndex, Nat.mul_assoc]
  rw [← f.finrank_range_add_finrank_ker]
  exact Nat.add_le_add_right hr _

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

