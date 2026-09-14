import ProximityPrize.SubmissionLower.MovingFiberProjection6811

/-! Feed the source-sensitive projection bounds into the actual native curve
budget. This bounds a pure polynomial cut on the moving fiber and charges no
multiplicity-weighted moving-degree term that the consumer does not need.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
open scoped Classical BigOperators
open RCN002 RCN022 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN093 RCN095 RCN135 RCN136 RCN207
open RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 40000
variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance : DecidableEq Ω := Classical.decEq Ω
local notation "Poly3" => MvPolynomial (Fin 3) Ω

def linearZ : Poly3 := MvPolynomial.X 2
def linearU (a : Ω) : Poly3 := MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 2
def linearA (b a : Ω) : Poly3 := MvPolynomial.X 1 + MvPolynomial.C b * MvPolynomial.X 0 +
  MvPolynomial.C (b*a) * MvPolynomial.X 2

omit [IsAlgClosed Ω] in
private theorem flag_X (i : Fin 3) (p : FlagDegree)
    (hi : InFlag p (Finsupp.single i 1)) : PolynomialInFlag p (MvPolynomial.X i : Poly3) := by
  intro e he
  have : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
omit [IsAlgClosed Ω] in
private theorem flag_add {p : FlagDegree} {A B : Poly3}
    (hA : PolynomialInFlag p A) (hB : PolynomialInFlag p B) : PolynomialInFlag p (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
omit [IsAlgClosed Ω] in
private theorem flag_scale {p : FlagDegree} {A : Poly3} (c : Ω)
    (hA : PolynomialInFlag p A) : PolynomialInFlag p (MvPolynomial.C c*A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_flag : PolynomialInFlag unitZFlag (linearZ : Poly3) :=
  flag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_flag (a : Ω) : PolynomialInFlag unitYZFlag (linearU a) :=
  flag_add (flag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (flag_scale a (flag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_flag (b a : Ω) : PolynomialInFlag unitAllFlag (linearA b a) :=
  flag_add (flag_add (flag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (flag_scale b (flag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (flag_scale (b*a) (flag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem exists_common_native_unit {G N R : Poly3} (p q : FlagDegree)
    (base : ∀ C : RegularComponent Ω G N R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω G N R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hG : Irreducible G) (hproper : ¬ G ∣ N)
    (hGflag : PolynomialInFlag p G) (hNflag : PolynomialInFlag q N) :
    ∃ (unit : AdaptiveUnitProjectionFamily base p q) (a b : Ω),
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
        coordinateEvaluation Ω C.1 linearZ) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
        coordinateEvaluation Ω C.1 (linearU a)) ∧
      (∀ C : RegularComponent Ω G N R, coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        coordinateEvaluation Ω C.1 (linearA b a)) := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  let unit := adaptiveUnitProjectionFamily_of_nested p q base hY hZ hderiv D hG hproper
    ((support_subset_flagSupport_iff _ _).mpr hGflag) ((support_subset_flagSupport_iff _ _).mpr hNflag)
  refine ⟨unit,D.lam,D.mu,?_,?_,?_⟩
  · intro C
    exact unit.zValue C
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 D.lam := by
      change coordinateValue Ω (CoordinateField Ω C.1)
        (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
      exact coordinateOfGate_value _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearU,affineU,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
  · intro C
    have hv : coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
        affineV Ω C.1 D.mu (D.mu*D.lam) := by
      change (elementEmbedding Ω (CoordinateField Ω C.1)
        (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
      exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _
    rw [hv,coordinateEvaluation_eq_aeval]
    simp only [linearA,affineV,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]

theorem pure_cut_on_moving_fiber
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : Irreducible carrier) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : (k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) carrier ≠ 0)
    (hproper : ¬ carrier ∣ movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target))
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff), SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff), LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff), LiteralProjectionGate C 2)
    (cut : Poly3) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    (k+1)*points.card ≤ flagMixed p (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) W := by
  classical
  let N := movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target
  let R := surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff
  let V := SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0
  obtain ⟨unit,a,b,hzv,hyv,hav⟩ := exists_common_native_unit p q base hY hZ hderiv hcarrier hproper hflag hNflag
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfe : (k.factorial : Ext) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne hfact
  have hdeg : p.zOnly+p.yz+p.all < c := by omega
  have cut_degree (ell : Poly3) (q0 : FlagDegree) (hell : PolynomialInFlag q0 ell)
      (hq : q0.zOnly+q0.yz+q0.all = 1)
      (projection : ∀ C : RegularComponent Ω carrier N R, Coordinate Ω (CoordinateField Ω C.1))
      (hvalue : ∀ C : RegularComponent Ω carrier N R,
        coordinateValue Ω (CoordinateField Ω C.1) (projection C) = coordinateEvaluation Ω C.1 ell) :
      (k+1)*(∑ C : RegularComponent Ω carrier N R, coordinateDegree Ω (CoordinateField Ω C.1) (projection C)) ≤
        flagMixed p q0 V := by
    apply sum_coordinate_projection_degrees (E := Ext) phi F carrier p q0 hcarrier.ne_zero hcarrierF hflag ell hell
      c hdeg (by rw [hq,mul_one]; exact hunit) P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2e hfe
      Q A target hQ hA id Function.injective_id projection hvalue
  have hz := cut_degree linearZ unitZFlag linearZ_flag (by rfl) unit.zProjection hzv
  have hy := cut_degree (linearU a) unitYZFlag (linearU_flag a) (by rfl) unit.yzProjection hyv
  have ha := cut_degree (linearA b a) unitAllFlag (linearA_flag b a) (by rfl) unit.allProjection hav
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card ≤ ∑ C : RegularComponent Ω carrier N R, budget.weightedCost W C := by
    apply (card_le_sum_componentSeeds Ω carrier N R points id
      (fun x hx => (hpoints x hx).1) (fun x hx => (hpoints x hx).2.1)
      (fun x hx => (hpoints x hx).2.2.1)).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he : (componentSeeds Ω carrier N R points id C).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω carrier N R points id C hx
      have hxC := componentSeeds_on_prime Ω carrier N R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (regularComponent_ne_point Ω carrier N R C)
          hxC (regularComponent_G_mem Ω carrier N R C) (regularComponent_T_mem Ω carrier N R C))
      · intro y hy
        exact componentSeeds_on_prime Ω carrier N R points id C y hy
      · intro y hy
        exact (hpoints y (componentSeeds_subset Ω carrier N R points id C hy)).2.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have hbudget : (k+1)*(∑ C : RegularComponent Ω carrier N R, budget.weightedCost W C) ≤ flagMixed p V W := by
    have h := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left W.zOnly hz)
      (Nat.mul_le_mul_left W.yz hy)) (Nat.mul_le_mul_left W.all ha)
    convert h using 1
    · simp only [budget,PrimeFlagBudgetFamily.weightedCost,
        AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
        AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    · simp only [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
      ring
  exact (Nat.mul_le_mul_left (k+1) hcard).trans hbudget

theorem isolated_pure_cut_on_moving_fiber
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : (k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target))
    (cut : Poly3) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    (k+1)*points.card ≤ flagMixed p (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) W := by
  classical
  let H := surfaceMap phi (polyH K F)
  let N := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R := H*surfaceMap phi (asS P).leadingCoeff
  let V := SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0
  have hdeg : p.zOnly+p.yz+p.all < c := by omega
  have hderiv : H ∈ Ideal.span
      ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3) := by
    let I := Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3)
    have hc : carrier ∈ I := Ideal.subset_span (by simp)
    have hd : MvPolynomial.pderiv (1 : Fin 3) carrier ∈ I := Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩ := hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∈ I
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact I.add_mem (I.mul_mem_right b hd) (I.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) b) hc)
  have hcover : ∀ x ∈ points, ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval x g.1 = 0 := by
    intro x hx
    have hp := hpoints x hx
    have hh : MvPolynomial.eval x H ≠ 0 := by
      have hr : MvPolynomial.eval x H * MvPolynomial.eval x (surfaceMap phi (asS P).leadingCoeff) ≠ 0 := by
        simpa only [map_mul] using hp.2.2.1
      exact (mul_ne_zero_iff.mp hr).1
    exact exists_active_factor_of_isolated carrier N cut R hcarrier x hp.1 hp.2.2.2 hp.2.2.1
      (map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval x) carrier H hderiv hp.1 hh) (hisolated x hx)
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g : ↥(activeFactors carrier N)) : Finset (Fin 3 → Ω) :=
    points.filter (fun x => MvPolynomial.eval x g.1 = (0:Ω))
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g : ↥(activeFactors carrier N)) : (k+1)*(S g).card ≤ flagMixed (exactFlag g.1) V W := by
    have hg := activeFactors_spec carrier N g
    have hgtotal : (exactFlag g.1).zOnly+(exactFlag g.1).yz+(exactFlag g.1).all ≤
        p.zOnly+p.yz+p.all := by
      rw [(exactFlag_cumulative g.1).2.2]
      exact (weightedTotalDegree_le_of_dvd_fin3 flagTotalWeights g.1 carrier hg.2.1 hcarrier).trans
        (inFlag_weight_caps carrier p hflag).2.2
    apply pure_cut_on_moving_fiber phi F g.1 (exactFlag g.1) q W hg.1
      (dvd_trans hg.2.1 hcarrierF) (polynomialIn_exactFlag g.1) P B U T s k n0
      hS hP hBU hUT hdn hB hn hdiv c (by omega) h2 hfact Q A target hQ hA
      hg.2.2.2 hg.2.2.1 hNflag (base g) (hY g) (hZ g) cut hcut (S g)
    · intro x hx
      have hs := Finset.mem_filter.mp hx
      have hp := hpoints x hs.1
      exact ⟨hs.2,hp.2.1,hp.2.2.1,hp.2.2.2⟩
    · intro x hx D hd hnot hpoint hG hN
      exact hisolated x (Finset.mem_filter.mp hx).1 D hd hnot hpoint
        (D.mem_of_dvd hg.2.1 hG) hN
  calc
    (k+1)*points.card ≤ (k+1)*∑ g : ↥(activeFactors carrier N), (S g).card :=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le)
    _ = ∑ g : ↥(activeFactors carrier N), (k+1)*(S g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : ↥(activeFactors carrier N), flagMixed (exactFlag g.1) V W := Finset.sum_le_sum (fun g _ => hcount g)
    _ ≤ _ := activeFactors_mixed_sum_le carrier N hcarrier p V W hflag

#print axioms exists_common_native_unit
#print axioms pure_cut_on_moving_fiber
#print axioms isolated_pure_cut_on_moving_fiber
end
end ProximityPrize.SubmissionLower.MovingFiberNativeBudget6811
