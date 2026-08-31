import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BU
namespace ProximityPrize.SubmissionLower.RCN286
open RCN169 RCN167
open RCN079 RCN080
open RCN290 RCN293
open RCN135 RCN136 RCN138
open RCN082 RCN081 RCN174 RCN319
noncomputable section
variable {K:Type*} [Field K]
def RegularSolution (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ F=0∧
   specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0
def LiftedSolutionPair
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ q.1=0∧
   specialization K P γ (MvPolynomial.pderiv (1:Fin 4) q.1)≠0∧
   RegularSolution q.2 P γ
theorem solution_regular_or_auxiliary
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ Q=0):
   specialization K P γ (singularAuxiliary Q)=0∨
     ∃ F∈positiveRFactors Q,RegularSolution F P γ:=by
 classical
 let φ:=polynomialEmbedding K
 let v:Fin 3 → GenericField K:=fun i => initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [canonical_geometricSurfaceMap] using (actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨F,hF,_hi,hpos,hz,hregular⟩:=
   surface_zero_singular_or_regular φ (polynomialEmbedding_injective K)
     Q hQ v ((heval Q).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨F,Finset.mem_filter.mpr ⟨hF,hpos⟩,
     (heval F).mp hz,(heval _).not.mp hregular⟩
theorem directFactor_data
   (Q F:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s)
   (hF:F∈positiveRFactors Q):
   Irreducible F∧0 < F.degreeOf 2∧F∈globalCoefficientBox K D w L s:=by
 obtain ⟨hi,hd,hr⟩:=positiveRFactors_spec Q F hF
 exact ⟨hi,hr,mem_globalCoefficientBox_of_dvd F Q D w L s hQ hd hbox⟩
theorem directFactor_input_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w) (hbox:Q∈globalCoefficientBox K D w L s):
   (∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
     (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
     (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L:=
 separated_factor_caps_of_prod_dvd (positiveRFactors Q) id Q D w L s hw hQ hbox
   (positiveRFactors_product_dvd Q hQ)
theorem implicitPair_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:J∈globalCoefficientBox K D w j 0)
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (hq:q∈implicitPairSet J):
   Irreducible q.1∧Irreducible q.2∧q.2.degreeOf 2=1∧
     q.1∈globalCoefficientBox K D w j 0∧
     q.2∈globalCoefficientBox K D w j 1∧¬ q.2∣q.1:=by
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain ⟨hiA,hdA,hrA,hyA,hiG,hdG,hrG,hproper⟩:=
   implicitPair_spec J q.1 q.2 hJ hR hq
 have hAbox:=mem_globalCoefficientBox_of_dvd q.1 J D w j 0 hJ hdA hbox
 have hGbox:=mem_globalCoefficientBox_of_dvd q.2 (implicitLift q.1) D w j 1
   (implicitLift_nonzero q.1 hrA hyA) hdG
   (implicitLift_mem_box q.1 D w j hw hDw hAbox)
 exact ⟨hiA,hiG,hrG,hAbox,hGbox,hproper⟩
theorem solution_implicit_pair_or_exceptional
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (P:Polynomial K) (γ:K) (D w j:ℕ)
   (hw:1 ≤ w) (hDw:w < D) (hbox:J∈globalCoefficientBox K D w j 0)
   (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ q∈implicitPairSet J,LiftedSolutionPair q P γ:=by
 classical
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain haux | ⟨A,hA,hi,hd,_hAR,_hAY,hsolA,hregA⟩:=
   solution_exceptional_or_implicit_regular J hJ hR P γ hsolution
 · exact Or.inl haux
 · have hy:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
     intro hz
     exact hregA (by rw [hz,map_zero])
   have hAmem:A∈implicitBaseFactors J:=Finset.mem_filter.mpr ⟨hA,hy⟩
   have hAbox:=mem_globalCoefficientBox_of_dvd A J D w j 0 hJ hd hbox
   obtain ⟨G,hG,_hiG,_hrG,_hGbox,hsolG,hregG,_hproper⟩:=
     exists_regular_lift_factor_of_solution A hi.ne_zero P γ D w j hw hDw hAbox hsolA hregA
   exact Or.inr ⟨⟨A,G⟩,(mem_implicitPairSet J A G).mpr ⟨hAmem,hG⟩,
     hsolA,hregA,hsolG,hregG⟩
def exceptionalSeeds (J:MvPolynomial (Fin 4) K) (seeds:Finset K)
   (selected:K → Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => specialization K (selected γ) γ (exceptionalAuxiliary J)=0)
theorem exceptionalSeeds_subset (J:MvPolynomial (Fin 4) K)
   (seeds:Finset K) (selected:K → Polynomial K):exceptionalSeeds J seeds selected ⊆ seeds:=by
 classical
 exact Finset.filter_subset _ _
theorem exceptionalSeeds_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j)
   (seeds:Finset K) (selected:K → Polynomial K):
   (exceptionalSeeds J seeds selected).card ≤ 2*j^2:=by
 classical
 apply exceptional_solution_seed_card_le J hJ hR j p hj hsmall hY hZ
 intro γ hγ
 exact ⟨selected γ,(Finset.mem_filter.mp hγ).2⟩
theorem solution_three_way
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ Q=0):
   (∃ F∈positiveRFactors Q,RegularSolution F P γ)∨
     (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q P γ)∨
     specialization K P γ (exceptionalAuxiliary (singularAuxiliary Q))=0:=by
 obtain haux | hregular:=solution_regular_or_auxiliary Q hQ P γ hsolution
 · have hJ:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
   obtain hexceptional | himplicit:=solution_implicit_pair_or_exceptional
     (singularAuxiliary Q) hJ.1 P γ ((2*s-1)*D) w ((2*s-1)*L)
     hw hDw hJ.2 haux
   · exact Or.inr (Or.inr hexceptional)
   · exact Or.inr (Or.inl himplicit)
 · exact Or.inl hregular
theorem selected_seed_decomposition
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (seeds:Finset K) (selected:K → Polynomial K)
   (hsolutions:∀ γ∈seeds,specialization K (selected γ) γ Q=0):
   (exceptionalSeeds (singularAuxiliary Q) seeds selected).card ≤
       2*((2*s-1)*L)^2∧
     (∀ γ∈seeds,γ∉exceptionalSeeds (singularAuxiliary Q) seeds selected →
       (∃ F∈positiveRFactors Q,RegularSolution F (selected γ) γ)∨
         (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q (selected γ) γ))∧
     ((∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
       (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
       (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L)∧
     ((∑ q∈implicitPairSet (singularAuxiliary Q),pairYCost q) ≤ (2*s-1)*L∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairRCost q) ≤
         2*(((2*s-1)*D-1)/w)*((2*s-1)*L)∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairZCost q) ≤
         ((2*s-1)*D-1)/w):=by
 classical
 have hwpos:0 < w:=by omega
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=Nat.eq_zero_of_le_zero
   (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ (2*s-1)*L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:=degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 refine ⟨exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR ((2*s-1)*L)
     p hj hjSmall hJY hJZ seeds selected,?_,
   directFactor_input_budgets Q hQ D w L s hwpos hbox,
   implicitPair_input_budgets (singularAuxiliary Q) hJ ((2*s-1)*D) w
     ((2*s-1)*L) hwpos hJbox⟩
 intro γ hγ hnot
 obtain hregular | himplicit | hexceptional:=solution_three_way
   Q hQ D w L s p hs hsmall hw hDw hbox (selected γ) γ (hsolutions γ hγ)
 · exact Or.inl hregular
 · exact Or.inr himplicit
 · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hγ,hexceptional⟩))
end
end ProximityPrize.SubmissionLower.RCN286
