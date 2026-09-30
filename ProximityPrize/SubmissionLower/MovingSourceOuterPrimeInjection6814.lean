import ProximityPrize.SubmissionLower.MovingSourceOuterMovingBudget6814
namespace ProximityPrize.SubmissionLower.MovingSourceOuterPrimeInjection6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 30000
open scoped Classical
open RCN002 RCN074 RCN084 RCN086 RCN095 RCN134 RCN135 RCN136 RCN137 RCN156 RCN159 RCN243 RCN244 RCN264 RCN267 RCN313
open WeightedSliceAssignment6807 ActiveSliceAssembly6807 MovingSourceSlicePrimeFamily6814
variable {K I J : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {p errorCap : ℕ} [CharP (GenericField K) p]
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "Poly" => MvPolynomial (Fin 3) Ω
local notation "w" => RCN326.w

theorem outer_stage_primes_injective
    (Gamma : J → Finset K) (flag : J → FlagDegree)
    (S : ∀ j, Stage K I (Gamma j) x p (flag j) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ j, (S j).F=F)
    (hG : ∀ j, (S j).G∈normalizedFactorSet (surfaceMap (polynomialEmbedding K) F))
    (hGinj : Function.Injective (fun j => (S j).G))
    (hproper : ∀ j, ¬(S j).G∣globalTailCut (polynomialEmbedding K) (S j).F (w+1)) :
    Function.Injective (fun a : (j : J) × FirstTailComponent (S j) => a.2.1) := by
  let carrier := surfaceMap (polynomialEmbedding K) F
  have hcar : carrier≠0 := by
    intro hz
    exact hF (surfaceMap_injective (polynomialEmbedding K) (polynomialEmbedding_injective K)
      (by simpa only [carrier,map_zero] using hz))
  rintro ⟨i,Ci⟩ ⟨j,Cj⟩ he
  have hg : (S i).G=(S j).G := by
    by_contra hne
    have hsubset : ({(S i).G,(S j).G} : Finset Poly)⊆normalizedFactorSet carrier := by
      intro P hP
      simp only [Finset.mem_insert,Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact hG i
      · exact hG j
    have hprod : (S i).G*(S j).G∣carrier := by
      have hh := (Finset.prod_dvd_prod_of_subset {(S i).G,(S j).G} (normalizedFactorSet carrier) id hsubset).trans
        (normalizedFactorSet_product_dvd carrier hcar)
      simpa only [Finset.prod_pair hne,id_eq] using hh
    have hiG : (S i).G∈Ci.1 := regularComponent_G_mem Ω (S i).G _ _ Ci
    have hjG : (S j).G∈Ci.1 := by
      have hh := regularComponent_G_mem Ω (S j).G _ _ Cj
      exact (congrArg (fun P : Ideal Poly => (S j).G∈P) he).mpr hh
    have hd := derivative_mem_of_two_factors carrier (S i).G (S j).G Ci.1 hprod hiG hjG
    apply regularComponent_H_not_mem Ω (S i).G _ _ Ci
    change surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) (S i).F)∈Ci.1
    have hr : surfaceMap (polynomialEmbedding K) (MvPolynomial.pderiv (2 : Fin 4) (S i).F)=
        MvPolynomial.pderiv (1 : Fin 3) carrier := by
      rw [hSF i]
      exact (surfaceMap_pderiv_R (polynomialEmbedding K) F).symm
    exact (congrArg (fun P : Poly => P∈Ci.1) hr).mpr hd
  have hi : i=j := hGinj hg
  cases hi
  exact congrArg (fun C : FirstTailComponent (S i) => (⟨i,C⟩ : (j : J) × FirstTailComponent (S j)))
    (Subtype.ext he)

end
end ProximityPrize.SubmissionLower.MovingSourceOuterPrimeInjection6814
