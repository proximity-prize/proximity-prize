import ProximityPrize.SubmissionLower.PortBase
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P0_4
noncomputable section
open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open private certificate_output_zero from ProximityPrize.SubmissionLower.Fast068
private theorem eval_liftX (f : K[X]) (x : K) : (liftX f).eval (C x) = C (f.eval x) :=
  K1_8.eval_liftX f x
private theorem mem_fixed_iff {u : Words} {T : TwoActive u} (R : Relation T) (i : I) :
    i ∈ fixedNodes R ↔ (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0 := by
  classical
  simp [fixedNodes]
private def constantsInFrac : K →+* Frac :=
  K1_8.seedInclusion.comp Polynomial.C
private theorem extend_liftX (G : K[X]) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G
private theorem fixed_case_maximal {u : Words} {T : TwoActive u} (R : Relation T)
    (hi : ¬ InvalidLeft R) (hf : FixedLeftGCD R) :
    ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
      H ∣ extendSeed (liftX (locator node (fixedNodes R))) := by
  classical
  obtain ⟨g, hg, hgu, hgv, hgmax⟩ := hf
  change g.map constantsInFrac ≠ 0 at hg
  change g.map constantsInFrac ∣ _ at hgu hgv
  change ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
    H ∣ g.map constantsInFrac at hgmax
  have hg0 : g ≠ 0 := by
    intro hz
    exact hg (by rw [hz, Polynomial.map_zero])
  let g₀ := g * C g.leadingCoeff⁻¹
  have hm : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hnorm (P : Frac[X]) (hd : g.map constantsInFrac ∣ P) :
      g₀.map constantsInFrac ∣ P := by
    apply ((Polynomial.map_dvd_map' constantsInFrac).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P : Bivar) (hd : g.map constantsInFrac ∣ extendSeed P) :
      liftX g₀ ∣ P := by
    apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective (hm.map Polynomial.C)).mp
    change extendSeed (liftX g₀) ∣ extendSeed P
    rw [extend_liftX]
    exact hnorm _ hd
  have hu := hlift _ hgu
  have hv := hlift _ hgv
  have hdom : g₀ ∣ locator node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀, hm.ne_zero, hu, hv, h⟩)
  obtain ⟨S, _, _, t, ht, hS⟩ :=
    Strata.split_divisor_locator_factor node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub : S ⊆ fixedNodes R := by
    intro i his
    have hz : g₀.eval (node i) = 0 := by
      rw [hS, eval_smul, locator_eval_zero node S i his, smul_zero]
    have hlzero : (liftX g₀).eval (C (node i)) = 0 := by
      rw [eval_liftX, hz, C_0]
    obtain ⟨U, hU⟩ := hu
    obtain ⟨V, hV⟩ := hv
    exact (mem_fixed_iff R i).mpr ⟨by rw [hU, eval_mul, hlzero, zero_mul],
      by rw [hV, eval_mul, hlzero, zero_mul]⟩
  have hg₀dvd : g₀ ∣ locator node (fixedNodes R) := by
    rw [hS, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _
      (fun i his => locator_eval_zero node _ i (hsub his))
  intro H hU hV
  rw [extend_liftX]
  exact (hgmax H hU hV).trans
    ((Polynomial.map_dvd_map' constantsInFrac).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))
theorem fixed_gcd {u : Words} {T : TwoActive u} (R : Relation T)
    (hu : leftU R ≠ 0) (hm : ¬ MovingGCD R) (hi : ¬ InvalidLeft R) :
    IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R)) := by
  classical
  let S := fixedNodes R
  let Δ := liftX (locator node S)
  let A := extendSeed (leftU R)
  let B := extendSeed (leftV R)
  have hΔ : Δ.Monic := (locator_monic node S).map Polynomial.C
  have hΔ0 : extendSeed Δ ≠ 0 := (hΔ.map seedInclusion).ne_zero
  have hA0 : A ≠ 0 :=
    fun h => hu (extendSeed_injective (h.trans (Polynomial.map_zero _).symm))
  have hΔA : extendSeed Δ ∣ A := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftU R) (fun i h => ((mem_fixed_iff R i).mp h).1))
  have hΔB : extendSeed Δ ∣ B := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftV R) (fun i h => ((mem_fixed_iff R i).mp h).2))
  refine ⟨hΔ0, hΔA, hΔB, ?_⟩
  by_cases hf : FixedLeftGCD R
  · exact fixed_case_maximal R hi hf
  let G := EuclideanDomain.gcd A B
  have hGA : G ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hGB : G ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hG : G ≠ 0 := fun hz => hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd : G.natDegree ≤ S.card := by
    apply Nat.le_of_not_gt
    exact fun h => hm ⟨hf, G, hG, hGA, hGB, h⟩
  have hΔd : (extendSeed Δ).natDegree = S.card := by
    rw [extend_liftX, natDegree_map_eq_of_injective constantsInFrac.injective, locator_natDegree]
  obtain ⟨q, hq⟩ := EuclideanDomain.dvd_gcd hΔA hΔB
  change G = extendSeed Δ * q at hq
  have hq0 : q ≠ 0 := by intro h; exact hG (by rw [hq, h, mul_zero])
  have hd := congrArg Polynomial.natDegree hq
  rw [natDegree_mul hΔ0 hq0, hΔd] at hd
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have hqU : IsUnit q := by
    rw [hqC, isUnit_C, isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz, C_0] at hqC)
  intro H hHA hHB
  have hHG : H ∣ G := EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq, hqU.dvd_mul_right] at hHG
theorem puncture {u : Words} {T : TwoActive u} (R : Relation T)
    (hs : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ))
    (hgcd : IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R))) : Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
  have h := hs γ hγ M
  let B := fixedNodes R
  let G := liftX (locator node B)
  have hG : G.Monic := (locator_monic node B).map Polynomial.C
  have hGd : G.natDegree = B.card := by
    change ((locator node B).map Polynomial.C).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, locator_natDegree]
  obtain ⟨U, hU⟩ := lift_locator_dvd B (leftU R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).1)
  obtain ⟨V, hV⟩ := lift_locator_dvd B (leftV R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).2)
  obtain ⟨W, hW⟩ := lift_locator_dvd B R.output (fun i hi => by
    have hroot := (mem_fixed_iff R i).mp hi
    exact certificate_output_zero R i hroot.1 hroot.2)
  have hu : U ≠ 0 := by
    intro hz
    apply h.U_ne
    rw [hU, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hv : V ≠ 0 := by
    intro hz
    apply h.V_ne
    rw [hV, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hdeg : max (leftU R).natDegree (leftV R).natDegree = T.height := by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact Nat.le_of_not_gt fun hlt => h.valid (Or.inl hlt)
  have hdu := congrArg Polynomial.natDegree hU
  have hdv := congrArg Polynomial.natDegree hV
  change (leftU R).natDegree = (G * U).natDegree at hdu
  change (leftV R).natDegree = (G * V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu, hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv, hGd] at hdv
  let H := max U.natDegree V.natDegree
  have hH : H + B.card = T.height := by
    dsimp [H]
    omega
  have hout : W.degree < (k + H : ℕ) := by
    by_cases hzero : W = 0
    · rw [hzero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout : R.output ≠ 0 := by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd := (natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G * W).natDegree < _ at hd
    rw [natDegree_mul hG.ne_zero hzero, hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop : IsCoprime (extendSeed U) (extendSeed V) := by
    apply coprime_after_factor (extendSeed G) _ _ hgcd.1
      (fun hz => hu (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · rw [hU, extendSeed, Polynomial.map_mul]
      exact hqu
    · rw [hV, extendSeed, Polynomial.map_mul]
      exact hqv
  exact ⟨⟨U, V, W, H, hH, rfl, hu, hv, hcop, hU, hV, hW, hout,
    fun γ hn M => (hs γ hn M).fixed_errors⟩⟩
end
end P0_4
end
section
set_option maxRecDepth 12000
namespace P0_4
noncomputable section
open Polynomial P0
private theorem threeUAt_eq (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    threeUAt q a β = K1_8.threeUAt q a β := by
  delta threeUAt K1_8.threeUAt P0.liftX K1.liftX P0.seed K1.seed P0.twist K1.twist P0.p K1.p
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem relationOnAt_eq (q : ℕ) (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOnAt q u S U V W = K1_8.relationOnAt q u S U V W := by
  delta relationOnAt K1_8.relationOnAt P0.node K1.node P0.Words K1.Words P0.I K1.I
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem columnRankAt_eq (q : ℕ) (U V : Bivar) :
    columnRankAt q U V = K1_8.columnRankAt q U V := by
  delta columnRankAt K1_8.columnRankAt P0.seed K1.seed P0.extendSeed K1.extendSeed
    P0.Bivar K1.Bivar P0.Frac K1.Frac P0.K K1.K
  rfl
open private K1_8.threeUAt_native from ProximityPrize.SubmissionLower.Fast068
private theorem native_threeU :
    threeUAt P0.p = (P0.threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt P0.threeU
  rfl
theorem threeU_eq (a : K[X]) (β : Fin 2 → K[X]) :
    P0.threeU a β = K1.threeU a β := by
  calc
    P0.threeU a β = threeUAt P0.p a β := congrFun (congrFun native_threeU.symm a) β
    _ = K1_8.threeUAt P0.p a β := threeUAt_eq P0.p a β
    _ = K1_8.threeUAt K1.p a β := congrArg (fun q => K1_8.threeUAt q a β) (show P0.p = K1.p from rfl)
    _ = K1.threeU a β := congrFun (congrFun K1_8.threeUAt_native a) β
theorem relationOn_eq (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOn u S U V W = K1_8.relationOnAt K1.p u S U V W := by
  calc
    _ = relationOnAt P0.p u S U V W := by delta P0.relationOn relationOnAt; rfl
    _ = K1_8.relationOnAt P0.p u S U V W := relationOnAt_eq P0.p u S U V W
    _ = K1_8.relationOnAt K1.p u S U V W :=
      congrArg (fun q => K1_8.relationOnAt q u S U V W) (show P0.p = K1.p from rfl)
theorem columnRank_eq (U V : Bivar) : columnRank U V = K1.columnRank U V := by
  calc
    _ = columnRankAt P0.p U V := by delta P0.columnRank columnRankAt; rfl
    _ = K1_8.columnRankAt P0.p U V := columnRankAt_eq P0.p U V
    _ = K1_8.columnRankAt K1.p U V := congrArg (fun q => K1_8.columnRankAt q U V) (show P0.p = K1.p from rfl)
    _ = _ := by delta K1_8.columnRankAt K1.columnRank; rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_4
noncomputable section
open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open private transfer_at from ProximityPrize.SubmissionLower.Fast068
open private threeU_height threeV_height common_multiplier multiplier_degree_zero
  seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU from ProximityPrize.SubmissionLower.Fast068
private theorem sameDirection_eq (U V P Q : Bivar) :
    sameDirection U V P Q = K1.sameDirection U V P Q := by
  delta P0.sameDirection K1.sameDirection
  rfl
private theorem threeV_eq (b : K[X]) (α : Fin 2 → K[X]) :
    threeV b α = K1.threeV b α := by
  delta P0.threeV K1.threeV P0.liftX K1.liftX P0.seed K1.seed
  rfl
private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : K[X]) :
    relationOn u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output) := by
  let G := liftX (locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (C (node i)) ≠ 0 := by
    intro i hi
    change (K1.liftX (locator node (fixedNodes R))).eval (C (node i)) ≠ 0
    rw [K1_8.eval_liftX, C_ne_zero]
    exact fun hz => hi ((Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  rw [relationOn_eq]
  exact @transfer_at u K1.p k T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem seed_multiplier {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ e : K[X], P = C e * D.U ∧ Q = C e * D.V := by
  have hext (F : Bivar) : (extendSeedHom F).natDegree = F.natDegree :=
    natDegree_map_eq_of_injective seedInclusion_injective F
  have hne (F : Bivar) (hF : F ≠ 0) : extendSeedHom F ≠ 0 :=
    fun hz => hF (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm))
  have hxy : extendSeedHom D.U * extendSeedHom Q = extendSeedHom D.V * extendSeedHom P := by
    have h := congrArg extendSeedHom hcross
    simpa only [map_mul] using h
  have hcop : IsCoprime (extendSeedHom D.U) (extendSeedHom D.V) := D.coprime
  obtain ⟨E, heP, heQ⟩ := common_multiplier hcop hxy
  have hEd := multiplier_degree_zero (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s := E.coeff 0
  have hE : E = C s := eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G := liftX (locator node (fixedNodes R))
  have hLeftU : extendSeedHom (G * P) = C s * extendSeedHom (leftU R) := by
    rw [D.U_factor]
    change extendSeedHom (G * P) = C s * extendSeedHom (G * D.U)
    rw [map_mul, map_mul, heP]
    ac_rfl
  have hLeftV : extendSeedHom (G * Q) = C s * extendSeedHom (leftV R) := by
    rw [D.V_factor]
    change extendSeedHom (G * Q) = C s * extendSeedHom (G * D.V)
    rw [map_mul, map_mul, heQ]
    ac_rfl
  let F : Fin 2 → Bivar := ![G * P, G * Q]
  let A : Fin 2 × Fin (T.height + 1) → K[X] :=
    fun j => (F j.1).coeff j.2.val
  have hA : ∀ j, seedInclusion (A j) = s * seedInclusion (R.coefficients j) := by
    rintro ⟨i, j⟩
    fin_cases i
    · have hc := seed_scalar_coeff j.val hLeftU
      rw [leftU, Principal.assemble_coeff] at hc
      exact hc
    · have hc := seed_scalar_coeff j.val hLeftV
      rw [leftV, Principal.assemble_coeff] at hc
      exact hc
  obtain ⟨e, he⟩ := descend_scalar R.coefficients A R.primitive s hA
  have hmapC : extendSeedHom (C e) = C s := by
    change (C e).map seedInclusion = C s
    rw [Polynomial.map_C, he]
  refine ⟨e, extendSeed_injective ?_, extendSeed_injective ?_⟩
  · change extendSeedHom P = extendSeedHom (C e * D.U)
    rw [map_mul, hmapC, heP]
  · change extendSeedHom Q = extendSeedHom (C e * D.V)
    rw [map_mul, hmapC, heQ]
private theorem canonical_output {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ W : Bivar, W.degree < (k + D.height : ℕ) ∧ relationOn u (fixedNodes R) P Q W := by
  obtain ⟨e, rfl, rfl⟩ := seed_multiplier D P Q hcross hp hq
  refine ⟨C e * D.output, ?_, ?_⟩
  · have hdeg : (C e * D.output).degree ≤ D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact reduced_scaled_relation D e
theorem rank_three_branch {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (hr : columnRank D.U D.V = 3) (S : AmplitudeDirection D.U D.V)
    (ha : S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ D.height)
    (hb : S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height) :
    ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hdir : sameDirection D.U D.V (threeU S.a S.β) (threeV S.b S.α) := by
    rw [threeU_eq, threeV_eq, sameDirection_eq]
    exact S.direction
  have hUdeg : (threeU S.a S.β).natDegree ≤ D.height := by
    rw [threeU_eq]
    exact (threeU_height _ _).trans ha
  have hVdeg : (threeV S.b S.α).natDegree ≤ D.height := by
    rw [threeV_eq]
    exact (threeV_height _ _).trans hb
  obtain ⟨W, hW, hnodes⟩ := canonical_output D _ _ hdir hUdeg hVdeg
  by_cases hd : S.α 0 * S.β 1 - S.α 1 * S.β 0 = 0
  · obtain ⟨t, ht, htβ⟩ := proportional_amplitudes S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ : twist t ≠ 0 := fun hz => ht (twist.injective (hz.trans (map_zero twist).symm))
    let a := S.a * C (twist t)
    have heq (i : Fin 2) : (S.β i).map twist = C (twist t) * (S.α i).map twist := by
      rw [htβ i, Polynomial.map_mul, Polynomial.map_C]
    have hU : threeU a S.α = threeU S.a S.β :=
      (threeU_eq _ _).trans ((rescale_threeU S.a S.α S.β (twist t) heq).trans (threeU_eq _ _).symm)
    have hdeg (i : Fin 2) : (S.β i).natDegree = (S.α i).natDegree := by
      rw [htβ i, natDegree_C_mul ht]
    have ha' : a.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height := by
      simpa only [a, natDegree_mul_C htσ, amplitudeDegree, hdeg] using ha
    have hdir' : sameDirection D.U D.V (threeU a S.α) (threeV S.b S.α) := by
      rw [hU]
      exact hdir
    have hn : relationOn u (fixedNodes R) (threeU a S.α) (threeV S.b S.α) W := by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr, S.α, S.α, a, S.b, mul_ne_zero S.a_ne (C_ne_zero.mpr htσ), S.b_ne,
      S.α_primitive, S.α_primitive, ha', hb, hdir', W, hW, hn⟩, Or.inr rfl⟩
  · exact ⟨⟨hr, S.α, S.β, S.a, S.b, S.a_ne, S.b_ne,
      S.α_primitive, S.β_primitive, ha, hb, hdir, W, hW, hnodes⟩, Or.inl hd⟩
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace P0_5
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open private seedCoeff_degree from ProximityPrize.SubmissionLower.Fast068
abbrev heightBound : ℕ := 32781
structure PolarData (u : Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
abbrev PolarData.amp {u : Words} (D : PolarData u) := pencil (D.A 0) (D.A 1)
private theorem pow_eq_twist (z : K) : z ^ P0.p = twist z :=
  (frobenius_def P0.p z).symm
private theorem threeUAt_native : threeUAt P0.p = P0.threeU := by
  unfold threeUAt P0.threeU
  rfl
private theorem relationOnAt_native : relationOnAt P0.p = P0.relationOn := by
  unfold relationOnAt P0.relationOn
  rfl
private theorem coefficientsAt (q : ℕ) (hq : 1 < q) (hσ : ∀ z : K, z ^ q = twist z)
    (u : Words) (deleted : Finset I) (a b : K[X]) (A B : Fin 2 → K[X])
    (output : P0.Bivar) (hp : A = B)
    (hn : relationOnAt q u deleted (threeUAt q a B) (P0.threeV b A) output)
    (i : I) (hi : i ∉ deleted) :
    (seedCoeff output 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff output 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff output q).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff output (q + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  subst B
  exact K1_9.coefficients_at_node u a b A i q hq hσ output (threeUAt q a A)
    (K1_9.eval_first a A i q) (hn i hi).symm
private theorem coefficients {u : Words} {T : P0.TwoActive u} {R : P0.Relation T}
    {D : P0.Reduction u T R} (B : P0.RankThree u T R D) (hp : P0.Parallel B)
    (i : I) (hi : i ∉ P0.fixedNodes R) :
    CoefficientIdentities u B.a B.b B.α B.output i := by
  have hnodes : relationOnAt P0.p u (P0.fixedNodes R) (threeUAt P0.p B.a B.β)
      (P0.threeV B.b B.α) B.output := by
    rw [threeUAt_native, relationOnAt_native]
    exact B.nodes
  exact coefficientsAt P0.p (by decide) pow_eq_twist u (P0.fixedNodes R)
    B.a B.b B.α B.β B.output hp hnodes i hi
private theorem polarData_of_set {u : Words} (S : Finset I) (height : ℕ)
    (a b : K[X]) (A : Fin 2 → K[X]) (output : P0.Bivar)
    (hh : height + S.card ≤ heightBound)
    (hout : output.degree < (k + height : ℕ))
    (hfirst : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K1.sixNorm a ≠ K1.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let v (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (v j).degree < (k + heightBound : ℕ) := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (k + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show k + height + g.natDegree ≤ k + heightBound by omega))
  have ha : (g * a).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (v 0) (v 1) s) (pencil (v K1.p) (v (K1.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K1.p) (hd (K1.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, v, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, v, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring
theorem polarData_of_parallel {u : Words} {T : P0.TwoActive u} {R : P0.Relation T}
    {D : P0.Reduction u T R} (B : P0.RankThree u T R D)
    (hp : P0.Parallel B) (hn : ¬ P0.UnitNorm B) : Nonempty (PolarData u) := by
  have hh : D.height + (P0.fixedNodes R).card ≤ heightBound := by
    rw [D.height_eq, P0.TwoActive.height]
    have h₁ := T.ab
    have h₂ := T.active
    have h₃ := T.degreeSum
    dsimp only [P0.t, P0.blockLength, P0.agreement, k, heightBound] at h₂ h₃ ⊢
    omega
  have hfirst := (congrArg (fun A : Fin 2 → K[X] =>
    B.a.natDegree + amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (P0.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive (coefficients B hp)
end
end P0_5
end
section
set_option autoImplicit false
namespace P0_7
noncomputable section
open P0 MvPolynomial
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V
abbrev Puncture := K1_11.Puncture
open K1_11 (sourceWeights scalarWeightY scalarWeightYS scalarWeightT
  contactLift contactWeight contactShift polynomialView scalarImages)
structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
inductive Bank
  | w22 | w12 | w21 | w13 | w23 | w31 | w32 | w33
def Bank.dS : Bank → ℕ
  | .w22 | .w21 | .w23 => 2
  | .w12 | .w13 => 1
  | .w31 | .w32 | .w33 => 3
def Bank.dT : Bank → ℕ
  | .w22 | .w12 | .w32 => 2
  | .w21 | .w31 => 1
  | .w13 | .w23 | .w33 => 3
def Bank.s : Bank → ℕ
  | .w22 => 10
  | .w12 => 14
  | .w21 => 9
  | _ => 8
def Bank.t : Bank → ℕ
  | .w22 => 10
  | .w12 => 9
  | .w21 => 14
  | _ => 8
def Bank.heightFloor : Bank → ℕ
  | .w22 | .w12 | .w21 => 24573
  | _ => 32764
def Bank.a (b : Bank) : ℕ := b.s + 5 * b.dS
def Bank.b (b : Bank) : ℕ := b.t + 5 * (b.dT - 1)
def Bank.E (b : Bank) : ℕ := b.a + b.b
def Bank.M (b : Bank) : ℕ := (2 * 131071 - 1) * (b.E - 1) + 1
def Bank.zeroFee (b : Bank) : ℕ := b.a + p * b.b
def Bank.chartRate (b : Bank) : ℚ := (43691 / 16382 : ℚ) * b.M
def Bank.chartFee (b : Bank) : ℚ := b.E * b.chartRate ^ 2
abbrev weightedCutoff : ℕ := 4 * agreement - 1
abbrev nodeCut := K1_11.nodeCut
def Bank.relationBounds (b : Bank) (H : ℕ) : Fin 4 → ℕ := ![131071 + H, 1, b.dS, b.dT]
structure ContactInput (u : Words) {deleted : Finset I} (P : Puncture deleted)
    (b : Bank) (H : ℕ) where
  L : MvPolynomial (Fin 5) K
  L_ne : L ≠ 0
  degrees : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j
  order_one : ∀ i : Fin P.N,
    (contactLift contactWeight
      (contactShift (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i) ^ p) (u 1 (P.index i) ^ p) L)).natTrailingDegree = 1
  numerator : MvPolynomial (Fin 4) K
  denominator : MvPolynomial (Fin 4) K
  denominator_ne : denominator ≠ 0
  linear : polynomialView L =
    Polynomial.C denominator * Polynomial.X - Polynomial.C numerator
  primitive : (Polynomial.C denominator * Polynomial.X - Polynomial.C numerator).IsPrimitive
  numerator_Y : numerator.weightedTotalDegree scalarWeightY ≤ 1
  denominator_Y : denominator.weightedTotalDegree scalarWeightY ≤ 0
  numerator_S : numerator.weightedTotalDegree scalarWeightYS ≤ b.dS
  denominator_S : denominator.weightedTotalDegree scalarWeightYS ≤ b.dS
  numerator_T : numerator.weightedTotalDegree scalarWeightT ≤ b.dT
  denominator_T : denominator.weightedTotalDegree scalarWeightT ≤ b.dT - 1
abbrev scalarWeightTotal := K1_11.scalarWeightTotal
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end P0_7
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P0_7
open P0 Finset
open K1_11 (V J)
private def countRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (s + 1 - i) * (t + 1 - j)
private def gradeRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (i + j) * ((s + 1 - i) * (t + 1 - j))
private def count (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), countRow B s t i
private def grade (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), gradeRow B s t i
private def contactRow (m s t i : ℕ) : ℕ :=
  ∑ j ∈ range (m - i), (m - i - j) * (s + 1 - i) * (t + 1 - j)
private theorem V_affine (D w B s t : ℕ) (hB : w * B ≤ D + 1) :
    V D w B s t + w * grade B s t = (D + 1) * count B s t := by
  unfold V count grade countRow gradeRow
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hij : i + j ≤ B := by
    simp only [mem_range] at hi hj
    omega
  have hw := (Nat.mul_le_mul_left w hij).trans hB
  calc
    _ = ((D + 1 - w * (i + j)) + w * (i + j)) * ((s + 1 - i) * (t + 1 - j)) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hw]
private theorem surplus_of_stats (h H e N lo s t ds dt c g c' g' j : ℕ)
    (hlo : lo ≤ h) (hmax : h ≤ 32766) (hH : H + e = h) (hN : N + e = 262144)
    (hc : count 5 s t = c) (hg : grade 5 s t = g)
    (hc' : count 4 (s-ds) (t-dt) = c') (hg' : grade 4 (s-ds) (t-dt) = g')
    (hj : J 4 s t - J 3 (s-ds) (t-dt) = j) (hgain : c' ≤ j)
    (hmargin : 262144 * j + (589797 - lo) * c' + 131071 * g <
      720868 * c + 131071 * g') :
    N * (J 4 s t - J 3 (s-ds) (t-dt)) + V (720867 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 720867 131071 5 s t := by
  have hv := V_affine 720867 131071 5 s t (by decide)
  have hv' := V_affine (720867 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc, hg] at hv
  rw [hc', hg'] at hv'
  have hw : 720867 - 131071 - H + 1 ≤ (589797 - lo) + e := by omega
  have hm : N * j + (720867 - 131071 - H + 1) * c' ≤
      262144 * j + (589797 - lo) * c' := by
    calc
      _ ≤ N * j + ((589797 - lo) + e) * c' :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) _
      _ = N * j + e * c' + (589797 - lo) * c' := by ring
      _ ≤ N * j + e * j + (589797 - lo) * c' :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hgain) _) _
      _ = _ := by rw [← Nat.add_mul, hN]
  rw [hj]
  omega
private theorem dims_5_10_10 : count 5 10 10 = 1806 ∧ grade 5 10 10 = 5544 := by
  constructor
  · have r0 : countRow 5 10 10 0 = 561 := by decide
    have r1 : countRow 5 10 10 1 = 450 := by decide
    have r2 : countRow 5 10 10 2 = 342 := by decide
    have r3 : countRow 5 10 10 3 = 240 := by decide
    have r4 : countRow 5 10 10 4 = 147 := by decide
    have r5 : countRow 5 10 10 5 = 66 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 10 10 0 = 1210 := by decide
    have r1 : gradeRow 5 10 10 1 = 1250 := by decide
    have r2 : gradeRow 5 10 10 2 = 1152 := by decide
    have r3 : gradeRow 5 10 10 3 = 944 := by decide
    have r4 : gradeRow 5 10 10 4 = 658 := by decide
    have r5 : gradeRow 5 10 10 5 = 330 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_8_8 : count 4 8 8 = 870 ∧ grade 4 8 8 = 2124 := by
  constructor
  · have r0 : countRow 4 8 8 0 = 315 := by decide
    have r1 : countRow 4 8 8 1 = 240 := by decide
    have r2 : countRow 4 8 8 2 = 168 := by decide
    have r3 : countRow 4 8 8 3 = 102 := by decide
    have r4 : countRow 4 8 8 4 = 45 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 8 8 0 = 540 := by decide
    have r1 : gradeRow 4 8 8 1 = 560 := by decide
    have r2 : gradeRow 4 8 8 2 = 490 := by decide
    have r3 : gradeRow 4 8 8 3 = 354 := by decide
    have r4 : gradeRow 4 8 8 4 = 180 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_5_14_9 : count 5 14 9 = 2310 ∧ grade 5 14 9 = 7154 := by
  constructor
  · have r0 : countRow 5 14 9 0 = 675 := by decide
    have r1 : countRow 5 14 9 1 = 560 := by decide
    have r2 : countRow 5 14 9 2 = 442 := by decide
    have r3 : countRow 5 14 9 3 = 324 := by decide
    have r4 : countRow 5 14 9 4 = 209 := by decide
    have r5 : countRow 5 14 9 5 = 100 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 14 9 0 = 1425 := by decide
    have r1 : gradeRow 5 14 9 1 = 1540 := by decide
    have r2 : gradeRow 5 14 9 2 = 1482 := by decide
    have r3 : gradeRow 5 14 9 3 = 1272 := by decide
    have r4 : gradeRow 5 14 9 4 = 935 := by decide
    have r5 : gradeRow 5 14 9 5 = 500 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_13_7 : count 4 13 7 = 1255 ∧ grade 4 13 7 = 3104 := by
  constructor
  · have r0 : countRow 4 13 7 0 = 420 := by decide
    have r1 : countRow 4 13 7 1 = 338 := by decide
    have r2 : countRow 4 13 7 2 = 252 := by decide
    have r3 : countRow 4 13 7 3 = 165 := by decide
    have r4 : countRow 4 13 7 4 = 80 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 13 7 0 = 700 := by decide
    have r1 : gradeRow 4 13 7 1 = 780 := by decide
    have r2 : gradeRow 4 13 7 2 = 732 := by decide
    have r3 : gradeRow 4 13 7 3 = 572 := by decide
    have r4 : gradeRow 4 13 7 4 = 320 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_5_9_14 : count 5 9 14 = 2310 ∧ grade 5 9 14 = 7154 := by
  constructor
  · have r0 : countRow 5 9 14 0 = 750 := by decide
    have r1 : countRow 5 9 14 1 = 585 := by decide
    have r2 : countRow 5 9 14 2 = 432 := by decide
    have r3 : countRow 5 9 14 3 = 294 := by decide
    have r4 : countRow 5 9 14 4 = 174 := by decide
    have r5 : countRow 5 9 14 5 = 75 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 9 14 0 = 1700 := by decide
    have r1 : gradeRow 5 9 14 1 = 1665 := by decide
    have r2 : gradeRow 5 9 14 2 = 1472 := by decide
    have r3 : gradeRow 5 9 14 3 = 1162 := by decide
    have r4 : gradeRow 5 9 14 4 = 780 := by decide
    have r5 : gradeRow 5 9 14 5 = 375 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_7_13 : count 4 7 13 = 1255 ∧ grade 4 7 13 = 3104 := by
  constructor
  · have r0 : countRow 4 7 13 0 = 480 := by decide
    have r1 : countRow 4 7 13 1 = 350 := by decide
    have r2 : countRow 4 7 13 2 = 234 := by decide
    have r3 : countRow 4 7 13 3 = 135 := by decide
    have r4 : countRow 4 7 13 4 = 56 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 7 13 0 = 880 := by decide
    have r1 : gradeRow 4 7 13 1 = 840 := by decide
    have r2 : gradeRow 4 7 13 2 = 690 := by decide
    have r3 : gradeRow 4 7 13 3 = 470 := by decide
    have r4 : gradeRow 4 7 13 4 = 224 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_5_8_8 : count 5 8 8 = 1106 ∧ grade 5 8 8 = 3304 := by
  constructor
  · have r0 : countRow 5 8 8 0 = 351 := by decide
    have r1 : countRow 5 8 8 1 = 280 := by decide
    have r2 : countRow 5 8 8 2 = 210 := by decide
    have r3 : countRow 5 8 8 3 = 144 := by decide
    have r4 : countRow 5 8 8 4 = 85 := by decide
    have r5 : countRow 5 8 8 5 = 36 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
  · have r0 : gradeRow 5 8 8 0 = 720 := by decide
    have r1 : gradeRow 5 8 8 1 = 760 := by decide
    have r2 : gradeRow 5 8 8 2 = 700 := by decide
    have r3 : gradeRow 5 8 8 3 = 564 := by decide
    have r4 : gradeRow 5 8 8 4 = 380 := by decide
    have r5 : gradeRow 5 8 8 5 = 180 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, r5, zero_add]
private theorem dims_4_7_5 : count 4 7 5 = 455 ∧ grade 4 7 5 = 1064 := by
  constructor
  · have r0 : countRow 4 7 5 0 = 160 := by decide
    have r1 : countRow 4 7 5 1 = 126 := by decide
    have r2 : countRow 4 7 5 2 = 90 := by decide
    have r3 : countRow 4 7 5 3 = 55 := by decide
    have r4 : countRow 4 7 5 4 = 24 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 7 5 0 = 240 := by decide
    have r1 : gradeRow 4 7 5 1 = 280 := by decide
    have r2 : gradeRow 4 7 5 2 = 258 := by decide
    have r3 : gradeRow 4 7 5 3 = 190 := by decide
    have r4 : gradeRow 4 7 5 4 = 96 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_4_6_5 : count 4 6 5 = 385 ∧ grade 4 6 5 = 889 := by
  constructor
  · have r0 : countRow 4 6 5 0 = 140 := by decide
    have r1 : countRow 4 6 5 1 = 108 := by decide
    have r2 : countRow 4 6 5 2 = 75 := by decide
    have r3 : countRow 4 6 5 3 = 44 := by decide
    have r4 : countRow 4 6 5 4 = 18 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 6 5 0 = 210 := by decide
    have r1 : gradeRow 4 6 5 1 = 240 := by decide
    have r2 : gradeRow 4 6 5 2 = 215 := by decide
    have r3 : gradeRow 4 6 5 3 = 152 := by decide
    have r4 : gradeRow 4 6 5 4 = 72 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_4_5_7 : count 4 5 7 = 455 ∧ grade 4 5 7 = 1064 := by
  constructor
  · have r0 : countRow 4 5 7 0 = 180 := by decide
    have r1 : countRow 4 5 7 1 = 130 := by decide
    have r2 : countRow 4 5 7 2 = 84 := by decide
    have r3 : countRow 4 5 7 3 = 45 := by decide
    have r4 : countRow 4 5 7 4 = 16 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 7 0 = 300 := by decide
    have r1 : gradeRow 4 5 7 1 = 300 := by decide
    have r2 : gradeRow 4 5 7 2 = 244 := by decide
    have r3 : gradeRow 4 5 7 3 = 156 := by decide
    have r4 : gradeRow 4 5 7 4 = 64 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_4_5_6 : count 4 5 6 = 385 ∧ grade 4 5 6 = 889 := by
  constructor
  · have r0 : countRow 4 5 6 0 = 150 := by decide
    have r1 : countRow 4 5 6 1 = 110 := by decide
    have r2 : countRow 4 5 6 2 = 72 := by decide
    have r3 : countRow 4 5 6 3 = 39 := by decide
    have r4 : countRow 4 5 6 4 = 14 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 6 0 = 240 := by decide
    have r1 : gradeRow 4 5 6 1 = 250 := by decide
    have r2 : gradeRow 4 5 6 2 = 208 := by decide
    have r3 : gradeRow 4 5 6 3 = 135 := by decide
    have r4 : gradeRow 4 5 6 4 = 56 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem dims_4_5_5 : count 4 5 5 = 315 ∧ grade 4 5 5 = 714 := by
  constructor
  · have r0 : countRow 4 5 5 0 = 120 := by decide
    have r1 : countRow 4 5 5 1 = 90 := by decide
    have r2 : countRow 4 5 5 2 = 60 := by decide
    have r3 : countRow 4 5 5 3 = 33 := by decide
    have r4 : countRow 4 5 5 4 = 12 := by decide
    simp only [count, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
  · have r0 : gradeRow 4 5 5 0 = 180 := by decide
    have r1 : gradeRow 4 5 5 1 = 200 := by decide
    have r2 : gradeRow 4 5 5 2 = 172 := by decide
    have r3 : gradeRow 4 5 5 3 = 114 := by decide
    have r4 : gradeRow 4 5 5 4 = 48 := by decide
    simp only [grade, sum_range_succ, sum_range_zero, r0, r1, r2, r3, r4, zero_add]
private theorem jets_4_10_10 : J 4 10 10 = 2096 := by
  change (∑ i ∈ range 4, contactRow 4 10 10 i) = 2096
  have r0 : contactRow 4 10 10 0 = 1100 := by decide
  have r1 : contactRow 4 10 10 1 = 620 := by decide
  have r2 : contactRow 4 10 10 2 = 288 := by decide
  have r3 : contactRow 4 10 10 3 = 88 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_8_8 : J 3 8 8 = 721 := by
  change (∑ i ∈ range 3, contactRow 3 8 8 i) = 721
  have r0 : contactRow 3 8 8 0 = 450 := by decide
  have r1 : contactRow 3 8 8 1 = 208 := by decide
  have r2 : contactRow 3 8 8 2 = 63 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_4_14_9 : J 4 14 9 = 2631 := by
  change (∑ i ∈ range 4, contactRow 4 14 9 i) = 2631
  have r0 : contactRow 4 14 9 0 = 1350 := by decide
  have r1 : contactRow 4 14 9 1 = 784 := by decide
  have r2 : contactRow 4 14 9 2 = 377 := by decide
  have r3 : contactRow 4 14 9 3 = 120 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_13_7 : J 3 13 7 = 1011 := by
  change (∑ i ∈ range 3, contactRow 3 13 7 i) = 1011
  have r0 : contactRow 3 13 7 0 = 616 := by decide
  have r1 : contactRow 3 13 7 1 = 299 := by decide
  have r2 : contactRow 3 13 7 2 = 96 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_4_9_14 : J 4 9 14 = 2631 := by
  change (∑ i ∈ range 4, contactRow 4 9 14 i) = 2631
  have r0 : contactRow 4 9 14 0 = 1400 := by decide
  have r1 : contactRow 4 9 14 1 = 774 := by decide
  have r2 : contactRow 4 9 14 2 = 352 := by decide
  have r3 : contactRow 4 9 14 3 = 105 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_7_13 : J 3 7 13 = 1011 := by
  change (∑ i ∈ range 3, contactRow 3 7 13 i) = 1011
  have r0 : contactRow 3 7 13 0 = 640 := by decide
  have r1 : contactRow 3 7 13 1 = 287 := by decide
  have r2 : contactRow 3 7 13 2 = 84 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_4_8_8 : J 4 8 8 = 1356 := by
  change (∑ i ∈ range 4, contactRow 4 8 8 i) = 1356
  have r0 : contactRow 4 8 8 0 = 720 := by decide
  have r1 : contactRow 4 8 8 1 = 400 := by decide
  have r2 : contactRow 4 8 8 2 = 182 := by decide
  have r3 : contactRow 4 8 8 3 = 54 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, r3, zero_add]
private theorem jets_3_7_5 : J 3 7 5 = 411 := by
  change (∑ i ∈ range 3, contactRow 3 7 5 i) = 411
  have r0 : contactRow 3 7 5 0 = 256 := by decide
  have r1 : contactRow 3 7 5 1 = 119 := by decide
  have r2 : contactRow 3 7 5 2 = 36 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_3_6_5 : J 3 6 5 = 356 := by
  change (∑ i ∈ range 3, contactRow 3 6 5 i) = 356
  have r0 : contactRow 3 6 5 0 = 224 := by decide
  have r1 : contactRow 3 6 5 1 = 102 := by decide
  have r2 : contactRow 3 6 5 2 = 30 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_3_5_7 : J 3 5 7 = 411 := by
  change (∑ i ∈ range 3, contactRow 3 5 7 i) = 411
  have r0 : contactRow 3 5 7 0 = 264 := by decide
  have r1 : contactRow 3 5 7 1 = 115 := by decide
  have r2 : contactRow 3 5 7 2 = 32 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_3_5_6 : J 3 5 6 = 356 := by
  change (∑ i ∈ range 3, contactRow 3 5 6 i) = 356
  have r0 : contactRow 3 5 6 0 = 228 := by decide
  have r1 : contactRow 3 5 6 1 = 100 := by decide
  have r2 : contactRow 3 5 6 2 = 28 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
private theorem jets_3_5_5 : J 3 5 5 = 301 := by
  change (∑ i ∈ range 3, contactRow 3 5 5 i) = 301
  have r0 : contactRow 3 5 5 0 = 192 := by decide
  have r1 : contactRow 3 5 5 1 = 85 := by decide
  have r2 : contactRow 3 5 5 2 = 24 := by decide
  simp only [sum_range_succ, sum_range_zero, r0, r1, r2, zero_add]
theorem bank_surplus (b : Bank) (h H e N : ℕ) (hlo : b.heightFloor ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  cases b with
  | w22 =>
    exact surplus_of_stats h H e N 24573 10 10 2 2 1806 5544 870 2124 1375
      hlo hmax hH hN dims_5_10_10.1 dims_5_10_10.2 dims_4_8_8.1 dims_4_8_8.2
      (by rw [jets_4_10_10, jets_3_8_8]) (by decide) (by decide)
  | w12 =>
    exact surplus_of_stats h H e N 24573 14 9 1 2 2310 7154 1255 3104 1620
      hlo hmax hH hN dims_5_14_9.1 dims_5_14_9.2 dims_4_13_7.1 dims_4_13_7.2
      (by rw [jets_4_14_9, jets_3_13_7]) (by decide) (by decide)
  | w21 =>
    exact surplus_of_stats h H e N 24573 9 14 2 1 2310 7154 1255 3104 1620
      hlo hmax hH hN dims_5_9_14.1 dims_5_9_14.2 dims_4_7_13.1 dims_4_7_13.2
      (by rw [jets_4_9_14, jets_3_7_13]) (by decide) (by decide)
  | w13 =>
    exact surplus_of_stats h H e N 32764 8 8 1 3 1106 3304 455 1064 945
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_7_5.1 dims_4_7_5.2
      (by rw [jets_4_8_8, jets_3_7_5]) (by decide) (by decide)
  | w23 =>
    exact surplus_of_stats h H e N 32764 8 8 2 3 1106 3304 385 889 1000
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_6_5.1 dims_4_6_5.2
      (by rw [jets_4_8_8, jets_3_6_5]) (by decide) (by decide)
  | w31 =>
    exact surplus_of_stats h H e N 32764 8 8 3 1 1106 3304 455 1064 945
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_7.1 dims_4_5_7.2
      (by rw [jets_4_8_8, jets_3_5_7]) (by decide) (by decide)
  | w32 =>
    exact surplus_of_stats h H e N 32764 8 8 3 2 1106 3304 385 889 1000
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_6.1 dims_4_5_6.2
      (by rw [jets_4_8_8, jets_3_5_6]) (by decide) (by decide)
  | w33 =>
    exact surplus_of_stats h H e N 32764 8 8 3 3 1106 3304 315 714 1055
      hlo hmax hH hN dims_5_8_8.1 dims_5_8_8.2 dims_4_5_5.1 dims_4_5_5.2
      (by rw [jets_4_8_8, jets_3_5_5]) (by decide) (by decide)
private theorem rational_fee (E M exceptionFee limit a b : ℕ) (hb : 0 < b)
    (h : exceptionFee * b^2 + 5 * E * (a*M)^2 ≤ limit * b^2) :
    (exceptionFee : ℚ) + 5 * ((E : ℚ) * (((a : ℚ) / b) * M)^2) ≤ limit := by
  have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
  have h' : (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 ≤
      (limit : ℚ) * (b : ℚ)^2 := by exact_mod_cast h
  refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
  calc
    _ = (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 := by
      field_simp
    _ ≤ _ := h'
def Bank.regularCap : Bank → ℕ
  | .w22 => 98881751603308737
  | .w12 => 82585573997687680
  | .w21 => 82585573997687680
  | .w13 => 68185902430167102
  | .w23 => 107777690559483786
  | .w31 => 68185881123102782
  | .w32 => 107777679905951626
  | .w33 => 160322346563912056
theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * b.chartFee ≤ b.regularCap := by
  cases b with
  | w22 => exact rational_fee 35 8912795 31960596515 98881751603308737 43691 16382 (by decide) (by decide)
  | w12 => exact rational_fee 33 8388513 29829890081 82585573997687680 43691 16382 (by decide) (by decide)
  | w21 => exact rational_fee 33 8388513 29829890081 82585573997687680 43691 16382 (by decide) (by decide)
  | w13 => exact rational_fee 31 7864231 38352715807 68185902430167102 43691 16382 (by decide) (by decide)
  | w23 => exact rational_fee 36 9174936 38352715812 107777690559483786 43691 16382 (by decide) (by decide)
  | w31 => exact rational_fee 31 7864231 17045651487 68185881123102782 43691 16382 (by decide) (by decide)
  | w32 => exact rational_fee 36 9174936 27699183652 107777679905951626 43691 16382 (by decide) (by decide)
  | w33 => exact rational_fee 41 10485641 38352715817 160322346563912056 43691 16382 (by decide) (by decide)
theorem bank_cap (b : Bank) : b.regularCap ≤ 160322346563912056 := by
  cases b <;> decide
theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ b.chartRate := by
  have hm : (262144 : ℕ) ≤ b.M := by cases b <;> decide
  have hr : (1 : ℚ) ≤ 43691 / 16382 := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 16382)).mpr
    rw [one_mul]
    exact_mod_cast (show (16382 : ℕ) ≤ 43691 by decide)
  exact (by exact_mod_cast hm : (262144 : ℚ) ≤ b.M).trans
    (by simpa only [one_mul, Bank.chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℚ) ≤ b.M))
end P0_7
end
