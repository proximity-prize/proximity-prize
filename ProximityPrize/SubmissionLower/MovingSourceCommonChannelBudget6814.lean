import ProximityPrize.SubmissionLower.MovingSourceSuppliedFrame6814

/-! Discharge H-free for the common frame and supply the actual coprime
Sources to the OUTER coordinate count. No first-cut or pair-count budget
is a premise at the endpoint. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCommonChannelBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136 RCN156 RCN207 RCN208 RCN244 RCN248 RCN264 RCN313 RCN341 RCN344
open HFree6812 HFreeDir6813 CommonLinearChannels6807 MovingFiberThreeSources6811
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceExtendedThickPair6814
open MovingSourceOuterChannel6814 MovingSourceCoupledClearing6814
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

def commonChannel (lam mu : Ω) : Fin 3 → MvPolynomial (Fin 3) Ω :=
  ![linearZ,linearU lam,linearA mu lam]

private theorem cast_ne {n : ℕ} (h0 : 0<n) (hn : n<2130706433) : (n : K)≠0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

private theorem slice_budget
    (F : MvPolynomial (Fin 4) K) (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9 : N≤9678) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (hFD : surfaceMap (HFree6812.phiE K E) F∈D)
    (hHD : surfaceMap (HFree6812.phiE K E) (polyH K F)∉D) (d : Fin 3)
    (c : Fin 3 → Ω) (i : Fin 3) (hci : c i=1) (q : Fin 3 → Polynomial K)
    (hqd : DirShape d q) (hq : ∀ m, polynomialEmbedding K (q m)=c m) (hq1 : i=1 ∨ q 1=0)
    (hslice : MvPolynomial.C (sliceValue Ω E)-scalarPolynomialMap Ω E
      (∑ m, MvPolynomial.C (c m)*MvPolynomial.X m)∈D) :
    HFreeSliceBudgetCap (HFree6812.phiE K E) F D unitAllFlag (infCap d) := by
  have hNK : ∀ n : ℕ, 0<n → n≤N → (n : K)≠0 := fun n h0 hn => cast_ne h0 (by omega)
  exact ⟨hfree_slice_budget_dir d F D sep hFD hHD c i hci q hqd hq hslice
    (by exact_mod_cast cast_ne (K:=K) (n:=2) (by decide) (by decide))
    (hchar_gap F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap F D hHD c i hci q hq hq1 hslice N hN hNK)⟩

theorem common_channel_hfree
    (F : MvPolynomial (Fin 4) K) (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤N)
    (hN9 : N≤9678) (lam mu : Ω)
    (hlam : lam∈Set.range (polynomialEmbedding K)) (hmu : mu∈Set.range (polynomialEmbedding K))
    (j : Fin 3) : HFreeChannelDir (E:=E) F (commonChannel lam mu j) unitAllFlag j := by
  intro D _ sep hFD hsl hHD
  obtain ⟨ql,hql⟩ := hlam
  obtain ⟨qm,hqm⟩ := hmu
  have go := slice_budget (E:=E) F N hN hN9 D sep hFD hHD j
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![0,0,1] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearZ := by simp [linearZ,Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![1,0,lam] 0 rfl ![1,0,ql] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp [hql]) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![1,0,lam] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearU lam := by simp [linearU,Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![mu,1,mu*lam] 1 rfl ![qm,1,qm*ql] trivial
      (fun m => by fin_cases m <;> simp [hql,hqm]) (Or.inl rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![mu,1,mu*lam] : Fin 3 → Ω) m)*MvPolynomial.X m :
        MvPolynomial (Fin 3) Ω)=linearA mu lam := by simp [linearA,Fin.sum_univ_three]; ring
    rw [he]; exact hsl

variable {I A : Type} [Fintype A] [CharP E 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}

include E in
theorem outer_first_cut_from_sources
    (Gamma : A → Finset K) (flag : A → FlagDegree)
    (S : ∀ a, Stage K I (Gamma a) x 2130706433 (flag a) errorCap stageSupport)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0) (hSF : ∀ a, (S a).F=F)
    (parent : FlagDegree)
    (hp : ∀ (L : Type) [Field L] (phi : Polynomial K →+* L), PolynomialInFlag parent (surfaceMap phi F))
    (hproper : ∀ a, ¬(S a).G∣globalTailCut (polynomialEmbedding K) (S a).F (w+1))
    (old : ∀ a, FirstTailComponent (S a)) (hold : Function.Injective (fun a => (old a).1))
    (lam mu : Ω) (hlam : lam∈Set.range (polynomialEmbedding K)) (hmu : mu∈Set.range (polynomialEmbedding K))
    (j : Fin 3) (projection : ∀ a, Coordinate Ω (CoordinateField Ω (old a).1))
    (hvalue : ∀ a, coordinateValue Ω (CoordinateField Ω (old a).1) (projection a)=
      coordinateEvaluation Ω (old a).1 (commonChannel lam mu j))
    (hlinear : 2*(parent.zOnly+parent.yz+parent.all)<2130706433)
    (SZ SP SQ : Source F) (hleading : ∀ a, SZ.leading (polynomialEmbedding K)∉(old a).1)
    (r v z : ℕ) (hr : 3≤r) (hv : 2≤v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : MvPolynomial.weightedTotalDegree residualTotalWeights F≤r+v+z) (hsmall : r+v+z≤9678)
    (hpos : 0<F.degreeOf 2) (hcharF : F.degreeOf 2<2130706433)
    (hcop : IsRelPrime SP.P SQ.P) (delta : ℕ) (hd : 0<delta)
    (hP : delta≤SP.d) (hQ : delta≤SQ.d) (hchar : delta≤2130706433) (hZchar : SZ.k<2130706433)
    (hz : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433) :
    3*(SZ.d*delta)*(∑ a, localMultiplicity (S a) (canonicalLocalDVRFamily (S a) (hproper a)) (old a)*
      coordinateDegree Ω (CoordinateField Ω (old a).1) (projection a))≤
      (SZ.d*delta)*flagMixed parent (direction j) (hfreeFlagDir j r v z unitAllFlag)+
        4*(w+1)*((direction j).zOnly*(delta*flagMixed parent unitZFlag SZ.flag)+
          (direction j).yz*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)+
          (direction j).all*(SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)) := by
  have hell : PolynomialInFlag (direction j) (commonChannel lam mu j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag lam
    · exact linearA_in_flag mu lam
  have hq : (direction j).zOnly+(direction j).yz+(direction j).all=1 := by fin_cases j <;> rfl
  have hAll' : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ) := Or.inr (by exact_mod_cast hAll)
  exact outer_first_cut_coordinate_channel (E:=E) Gamma flag S F hF hSF parent (hp _ _)
    hproper old hold (commonChannel lam mu j) (direction j) hell projection hvalue (by omega)
    (by rw [hq,mul_one]; exact hlinear) SZ hleading j r v z hr hv hR hYR hAll' unitAllFlag
    (common_channel_hfree F (r+v+z) hAll hsmall lam mu hlam hmu j) _ _ _ _
    (fun Q U hden hQf hUf => extended_sources_point_budget (algebraMap Ω E) F hF hpos hcharF
      SP SQ hcop delta hd hP hQ hchar SZ hZchar parent (hp _ _) hlinear Q U hden hQf hUf hz hu)

#print axioms common_channel_hfree
#print axioms outer_first_cut_from_sources
end
end ProximityPrize.SubmissionLower.MovingSourceCommonChannelBudget6814
