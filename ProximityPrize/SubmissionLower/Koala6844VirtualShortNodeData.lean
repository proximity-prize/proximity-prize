import ProximityPrize.SubmissionLower.Koala6844VirtualShortNode
import ProximityPrize.SubmissionLower.Koala6844VirtualShortContactRank


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open SecondJetSupport SecondJetGlobalSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

variable {K : Type*} [Field K]

def embedDisplacement : Polynomial K →ₐ[K] Poly (K := K) :=
  Polynomial.aeval (MvPolynomial.X 0)

def normalizedDenominator (A₀ A₁ : Polynomial K) : Poly (K := K) :=
  embedDisplacement A₀ + embedDisplacement A₁*MvPolynomial.X 4

def normalizedNumerator (d₀ C₁ : Polynomial K) : Poly (K := K) :=
  embedDisplacement d₀*MvPolynomial.X 2 + embedDisplacement C₁*MvPolynomial.X 4

private theorem localize_embed (x u0 u1 : K) (P : Polynomial K) :
    localize x u0 u1 (embedDisplacement P) = embedDisplacement (Polynomial.taylor x P) := by
  have h : (localize x u0 u1).comp (embedDisplacement (K := K)) =
      embedDisplacement.comp (Polynomial.taylorAlgHom x) := by
    apply Polynomial.algHom_ext
    simp [embedDisplacement, localize, Polynomial.taylor_X, add_comm]
  exact DFunLike.congr_fun h P

theorem fits_add {u : LocalCaps} {F G : Poly (K := K)}
    (hF : FitsLocal u F) (hG : FitsLocal u G) : FitsLocal u (F+G) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hF _ h
  · exact hG _ h

private abbrev pure : LocalCaps := ⟨0,0,0,0,0,0⟩

private theorem fits_const (c : K) : FitsLocal pure (MvPolynomial.C c) := by
  intro e he
  have hz := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp

private theorem fits_T : FitsLocal pure (MvPolynomial.X 0 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X,Finset.mem_singleton] at he
  subst e
  simp [Fin.ext_iff]

theorem fits_embed (P : Polynomial K) : FitsLocal pure (embedDisplacement P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add]
    exact fits_add hP hQ
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    have h := (fits_const c).mul ((fits_T (K := K)).pow n)
    simpa [embedDisplacement, LocalCaps.plus, LocalCaps.times, pure] using h

theorem fits_local_value :
    FitsLocal ⟨1,0,0,1,1,0⟩ (MvPolynomial.X 2 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at he
  subst e
  simp [Fin.ext_iff]

theorem fits_seed :
    FitsLocal ⟨0,0,0,0,1,1⟩ (MvPolynomial.X 4 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at he
  subst e
  simp [Fin.ext_iff]

theorem from_pure_bound (u : LocalCaps) (h : 0 ≤ u.alphaMinusT)
    (P : Poly (K := K)) (hP : FitsLocal pure P) : FitsLocal u P := by
  intro e he
  have hb := hP e he
  dsimp only at hb
  exact ⟨hb.1.trans h, by omega, by omega, by omega, by omega, by omega⟩

theorem exists_nodePoleData (x u0 u1 v : K) (m : ℕ)
    (A₀ A₁ d₀ C₁ : Polynomial K)
    (h0 : d₀.eval x*u0 = v*A₀.eval x)
    (h1 : d₀.eval x*u1+C₁.eval x = v*A₁.eval x)
    (hLead : A₁.eval x ≠ 0) :
    Nonempty (NodePoleData m
      (localize x u0 u1 (normalizedDenominator A₀ A₁))
      (localize x u0 u1 (normalizedNumerator d₀ C₁))) := by
  let td := Polynomial.taylor x d₀
  let tc := Polynomial.taylor x C₁
  let ta := Polynomial.taylor x A₀
  let tb := Polynomial.taylor x A₁
  obtain ⟨R₀,hR₀⟩ := translated_germ_coefficient_dvd d₀ 0 A₀ x u0 v
    (by simpa using h0)
  obtain ⟨R₁,hR₁⟩ := translated_germ_coefficient_dvd d₀ C₁ A₁ x u1 v h1
  change Polynomial.taylorAlgHom x _ = _ at hR₀ hR₁
  have hr0 : td*Polynomial.C u0 - Polynomial.C v*ta = Polynomial.X*R₀ := by
    simpa only [td, ta, map_sub, map_add, map_mul, map_zero, add_zero, Polynomial.taylorAlgHom_apply, Polynomial.taylor_C] using hR₀
  have hr1 : td*Polynomial.C u1+tc-Polynomial.C v*tb = Polynomial.X*R₁ := by
    simpa only [td, tb, tc, map_sub, map_add, map_mul, Polynomial.taylorAlgHom_apply, Polynomial.taylor_C] using hR₁
  let base := embedDisplacement ta
  let lead := embedDisplacement tb
  let shift := embedDisplacement (Polynomial.C v*tb + Polynomial.X*R₁)
  let numerator := embedDisplacement (tb*R₀-ta*R₁) +
    embedDisplacement (tb*td)*MvPolynomial.X 2
  have hz : localize x u0 u1 (MvPolynomial.X 4) = MvPolynomial.X 4 := by simp [localize]
  have hy : localize x u0 u1 (MvPolynomial.X 2) =
      MvPolynomial.C u0 + MvPolynomial.C u1*MvPolynomial.X 4+
        MvPolynomial.X 0*MvPolynomial.X 2 := by simp [localize]
  have ha : localize x u0 u1 (normalizedDenominator A₀ A₁) =
      base+lead*MvPolynomial.X 4 := by
    simp only [normalizedDenominator, map_add, map_mul, localize_embed, hz, base,lead,ta,tb]
  have hb : localize x u0 u1 (normalizedNumerator d₀ C₁) =
      embedDisplacement td*(MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
        MvPolynomial.X 0*MvPolynomial.X 2)+embedDisplacement tc*MvPolynomial.X 4 := by
    simp only [normalizedNumerator,map_mul,map_add,localize_embed,hy,hz,td,tc]
  constructor
  refine ⟨lead,base,shift,numerator,?_,?_,?_,?_,fits_embed _,fits_embed _,fits_embed _,?_⟩
  · rw [ha]
    ring
  · rw [ha,hb]
    have h0' := congrArg (embedDisplacement (K := K)) hr0
    have h1' := congrArg (embedDisplacement (K := K)) hr1
    simp only [map_sub,map_mul,map_add,embedDisplacement,Polynomial.aeval_C,
      Polynomial.aeval_X] at h0' h1'
    dsimp [shift,numerator,lead,base]
    simp only [map_sub,map_mul,map_add,embedDisplacement,Polynomial.aeval_X,
      Polynomial.aeval_C,MvPolynomial.C_eq_algebraMap]
    linear_combination
      Polynomial.aeval (MvPolynomial.X 0) tb*h0' +
        Polynomial.aeval (MvPolynomial.X 0) tb*MvPolynomial.X 4*h1'
  · rw [ha]
    apply fits_add (from_pure_bound _ (by decide) _ (fits_embed _))
    simpa [LocalCaps.plus,pure] using (fits_embed (K := K) tb).mul (fits_seed (K := K))
  · apply fits_add (from_pure_bound _ (by decide) _ (fits_embed _))
    simpa [LocalCaps.plus,pure] using (fits_embed (K := K) (tb*td)).mul (fits_local_value (K := K))
  · have hn : tb.eval 0 ≠ 0 := by simpa [tb, Polynomial.taylor_eval] using hLead
    let φ := (flatContact (K := K)).comp (embedDisplacement (K := K))
    have hp := (isCoprime_local_leading_X_pow tb m hn).map φ.toRingHom
    simpa [φ,lead,embedDisplacement,flatContact_T] using hp

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
