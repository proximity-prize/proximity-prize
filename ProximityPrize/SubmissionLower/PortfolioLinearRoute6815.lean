import ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
import ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814
namespace ProximityPrize.SubmissionLower.PortfolioLinearRoute6815
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 900000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234 RCN244
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceDenominatorChange6814 MovingSourceReducedTailWeights6814
open MovingSourceReducedGamma6814 MovingSourceReducedCycle6814 MovingSourceCarrierField6814

variable {K : Type} [Field K]

structure Route (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (firstFlag delayFlag : FlagDegree) : Prop where
  denominator : carrierMap F (linearH J)≠0
  cross : ∀ n, F∣(linearH J)^(2*n)*RCN313.numerator K F n-
    (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n
  first : PolynomialInFlag firstFlag (reducedTailSurface (linearH J) (linearG J))
  later : ∀ mu delay : ℕ, 1≤mu → delay≤mu → PolynomialInFlag (mu • delayFlag)
    (surfaceMap (polynomialEmbedding K)
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay)))

def firstFlag (r y t : ℕ) : FlagDegree :=
  ⟨(t-y)*131072,1+(y-r)*131072,r*131072⟩
def delayFlag (r y t : ℕ) : FlagDegree :=
  ⟨(t-y)*131073,1+(y-r)*131073,r*131073⟩

theorem route_of_weights [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (hJ : J≠0) (hS : J.degreeOf 1=1)
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (cap : ℕ) (hT : ∀ e∈J.support, e 1+e 2+e 3+e 4≤cap)
    (hFT : cap<wt residualTotalWeights F)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0)
    (r y t : ℕ) (hry : r≤y) (hyt : y≤t)
    (hw : ∀ n, wt residualSWeights (numerators (linearH J) (linearG J) n)≤r*n ∧
      wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+y*n ∧
      wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+t*n) :
    Route F J (firstFlag r y t) (delayFlag r y t) := by
  refine ⟨linearH_nonzero_on_carrier J hJ hS F cap hT hFT,
    linear_denominator_change J hJ hS F hpos hchar cap hT hFT hroot,?_,?_⟩
  · have hh := hw 131072
    have he := surface_flag_of_caps (polynomialEmbedding K) _ (r*131072) (1+y*131072) (1+t*131072)
      (by omega) (by omega) hh.1 hh.2.1 hh.2.2
    convert he using 1 <;> simp only [firstFlag,RCN326.w,reducedTailSurface]
    · congr 1 <;> omega
  · intro mu d hm hd
    have hh := hw (RCN326.w+1+d)
    have hr : wt residualSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(r*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left r hd,Nat.mul_le_mul_left (r*131072) hm]
    have hy : wt residualYSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+y*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left y hd,Nat.mul_le_mul_left (y*131072) hm]
    have ht : wt residualTotalWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+t*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left t hd,Nat.mul_le_mul_left (t*131072) hm]
    have he := surface_flag_of_caps (polynomialEmbedding K) _ (mu*(r*131073))
      (mu*(1+y*131073)) (mu*(1+t*131073)) (by nlinarith) (by nlinarith) hr hy ht
    have eqflag : (⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩ : FlagDegree)=mu • delayFlag r y t := by
      have hz : (1+t*131073)-(1+y*131073)=(t-y)*131073 := by
        rw [Nat.sub_mul t y 131073]
        omega
      have hyz : (1+y*131073)-r*131073=1+(y-r)*131073 := by
        rw [Nat.sub_mul y r 131073]
        exact Nat.add_sub_assoc (Nat.mul_le_mul_right 131073 hry) 1
      change (⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩ : FlagDegree)=
        ⟨mu*((t-y)*131073),mu*(1+(y-r)*131073),mu*(r*131073)⟩
      rw [←Nat.mul_sub mu (1+t*131073) (1+y*131073),
        ←Nat.mul_sub mu (1+y*131073) (r*131073),hz,hyz]
    rw [eqflag] at he
    exact he

variable {I : Type} {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
variable {first delay : FlagDegree}

theorem denominator_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (J : Poly (K:=K)) (hroute : Route S.F J first delay) :
    ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
  have hF : Irreducible S.F := Fact.out
  have hn : ¬S.F∣linearH J := fun hd => hroute.denominator ((carrierMap_zero_iff S.F _).mpr hd)
  have hrel := MovingSourceDenominatorSeeds6814.surfaceMap_relPrime S.F (linearH J) hF.ne_zero
    (hF.isRelPrime_iff_not_dvd.mpr hn)
  intro hd
  exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hd)

end
end ProximityPrize.SubmissionLower.PortfolioLinearRoute6815
