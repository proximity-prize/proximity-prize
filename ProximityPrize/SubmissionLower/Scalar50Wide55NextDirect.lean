import ProximityPrize.SubmissionLower.CurveListScalarWide55Defs
import ProximityPrize.SubmissionLower.CurveListWideBands
import ProximityPrize.SubmissionLower.CurveListRectangularRoots
import ProximityPrize.SubmissionLower.ScalarRootRows
import ProximityPrize.SubmissionLower.Scalar50Wide55NextPrice

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Scalar50Wide55NextDirect
open CJ0 CJ0_3 Finset MvPolynomial PolynomialDifferential CurveListWideBands
open scoped BigOperators Polynomial
open Scalar50Wide55NextPrice (lowerWidth lowerIndex lowerTop lowerCap)
open private exists_interpolant stack_le_of_prefix from ProximityPrize.SubmissionLower.CurveListCornerSource

private abbrev A := 179895
private abbrev S := CurveListScalarWide55.support
private abbrev R := 150777
private abbrev SB := residualShape S
theorem widthOK : S.m ≤ S.m*A-N*S.B := by decide
theorem residualOK : ShapeOK SB := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,?_⟩ <;> simp
private theorem enough (x : ℕ)
    (h : x + N*(∑ j ∈ S.E, j.q) < S.m*A*S.E.card + (∑ j ∈ S.E, j.v)) :
    x < Fintype.card (ColumnIndex A S) := by
  have hd := source_dimension A S CurveListScalarWide55.shapeOK widthOK
  omega
theorem columnRoom : n*R < Fintype.card (ColumnIndex A S) := by
  apply enough
  obtain ⟨hx,hy,hz⟩ := CurveListScalarWide55.moments
  rw [hx,hy,hz]
  decide +kernel
theorem shiftRoom : n*R + (∑ v, degreeCharge A S 75 v) < Fintype.card (ColumnIndex A S) := by
  apply enough
  obtain ⟨hx,hy,hz⟩ := CurveListScalarWide55.moments
  rw [hx,hy,hz]
  decide +kernel
theorem bandRoom0 : n*R + (∑ j : IndexMark S 63 22, indexCharge A j)
    < Fintype.card (ColumnIndex A S) := by
  apply enough
  obtain ⟨hx,hy,hz⟩ := CurveListScalarWide55.moments
  rw [hx,hy,hz]
  decide +kernel
theorem bandRoom1 : n*R + (∑ j : IndexMark S 67 21, indexCharge A j)
    < Fintype.card (ColumnIndex A S) := by
  apply enough
  obtain ⟨hx,hy,hz⟩ := CurveListScalarWide55.moments
  rw [hx,hy,hz]
  decide +kernel
theorem bandRoom2 : n*R + (∑ j : IndexMark S 70 20, indexCharge A j)
    < Fintype.card (ColumnIndex A S) := by
  apply enough
  obtain ⟨hx,hy,hz⟩ := CurveListScalarWide55.moments
  rw [hx,hy,hz]
  decide +kernel

abbrev Residual := DifferentialPolynomial K 1
private abbrev band (t : Fin 4) : Source := {S with B := lowerWidth t, J := lowerIndex t}
abbrev residualCount (t : Fin 4) : ℕ := ![1,2,3,3] t

private def covers (w : Node → K) (P D : Equation) (G : List Residual) : Prop :=
  ∀ f ∈ close A w, differentialSpecialization P f = 0 →
    differentialSpecialization D f = 0 ∨ ∃ g ∈ G, differentialSpecialization g f = 0

private theorem extend {w : Node → K} {P D E : Equation} {G : List Residual} {g : Residual}
    (hc : covers w P D G)
    (h : ∀ f ∈ close A w, differentialSpecialization D f = 0 →
      differentialSpecialization E f = 0 ∨ differentialSpecialization g f = 0) : covers w P E (g::G) := by
  intro f hf hp
  rcases hc f hf hp with hd | ⟨r,hr,hz⟩
  · rcases h f hf hd with he | hg
    · exact Or.inl he
    · exact Or.inr ⟨g,by simp,hg⟩
  · exact Or.inr ⟨r,List.mem_cons_of_mem _ hr,hz⟩

theorem extend_order {G : List Residual} {g : Residual}
    (ho : ∀ r ∈ G, OrderOne SB r) (hg : OrderOne SB g) :
    ∀ r ∈ g::G, OrderOne SB r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hg
  · exact ho r hr

theorem narrow (rank : prefixRank S 76 ≤ R) (w : Node → K) {P : Equation}
    (hp : OrderTwo S P) :
    ∃ (t : Fin 4) (D : Equation) (G : List Residual), OrderTwo (band t) D ∧ D ∣ P ∧
      G.length ≤ residualCount t ∧ (∀ g ∈ G, OrderOne SB g) ∧ covers w P D G := by
  obtain ⟨D0,G0,hD0,hdiv0,hB0,hlen0,horder0,hcov0⟩ := refine_degree
    CurveListScalarWide55.shapeOK CurveListScalarWide55.facet widthOK (by decide) rank shiftRoom w 0 hp hp.2.1
  obtain ⟨D1,F1,hD1,hB1,hc1,hdiv1',hF1,hstep1⟩ := refine_index
    CurveListScalarWide55.shapeOK CurveListScalarWide55.facet widthOK (by decide) rank (by decide)
    bandRoom0 w hD0 hB0
  let G1 := F1::G0
  have hcov1 : covers w P D1 G1 := extend hcov0 hstep1
  have horder1 : ∀ g ∈ G1, OrderOne SB g := extend_order horder0 hF1
  have hlen1 : G1.length ≤ 1 := Nat.succ_le_succ hlen0
  have hdiv1 : D1 ∣ P := hdiv1'.trans hdiv0
  rcases hc1 with hsmall | hindex
  · exact ⟨0,D1,G1,⟨hD1.1,Nat.le_of_lt_succ hsmall,hD1.2.2⟩,hdiv1,
      hlen1,horder1,hcov1⟩
  have hidx1 : OrderTwo {S with J := 21} D1 :=
    ⟨hD1.1,hD1.2.1,Nat.le_of_lt_succ hindex,hD1.2.2.2⟩
  obtain ⟨D2,F2,hD2,hB2,hc2,hdiv2',hF2,hstep2⟩ := refine_index
    CurveListScalarWide55.shapeOK CurveListScalarWide55.facet widthOK (by decide) rank (by decide)
    bandRoom1 w hidx1 hB1
  let G2 := F2::G1
  have hcov2 : covers w P D2 G2 := extend hcov1 hstep2
  have horder2 : ∀ g ∈ G2, OrderOne SB g := extend_order horder1 hF2
  have hlen2 : G2.length ≤ 2 := Nat.succ_le_succ hlen1
  have hdiv2 : D2 ∣ P := hdiv2'.trans hdiv1
  rcases hc2 with hsmall | hindex
  · exact ⟨1,D2,G2,⟨hD2.1,Nat.le_of_lt_succ hsmall,hD2.2.2⟩,hdiv2,
      hlen2,horder2,hcov2⟩
  have hidx2 : OrderTwo {S with J := 20} D2 :=
    ⟨hD2.1,hD2.2.1,Nat.le_of_lt_succ hindex,hD2.2.2.2⟩
  obtain ⟨D3,F3,hD3,hB3,hc3,hdiv3',hF3,hstep3⟩ := refine_index
    CurveListScalarWide55.shapeOK CurveListScalarWide55.facet widthOK (by decide) rank (by decide)
    bandRoom2 w hidx2 hB2
  let G3 := F3::G2
  have hcov3 : covers w P D3 G3 := extend hcov2 hstep3
  have horder3 : ∀ g ∈ G3, OrderOne SB g := extend_order horder2 hF3
  have hlen3 : G3.length ≤ 3 := Nat.succ_le_succ hlen2
  have hdiv3 : D3 ∣ P := hdiv3'.trans hdiv2
  rcases hc3 with hsmall | hindex
  · exact ⟨2,D3,G3,⟨hD3.1,Nat.le_of_lt_succ hsmall,hD3.2.2⟩,hdiv3,
      hlen3,horder3,hcov3⟩
  have hidx3 : OrderTwo {S with J := 19} D3 :=
    ⟨hD3.1,hD3.2.1,Nat.le_of_lt_succ hindex,hD3.2.2.2⟩
  exact ⟨3,D3,G3,⟨hidx3.1,hB3,hidx3.2.2⟩,hdiv3,hlen3,horder3,hcov3⟩

theorem top_index (g : K1_13.Row 3) :
    g.degreeOf 2 ≤ K1_13.indexDegree g / 2 := by
  classical
  rw [K1_13_1.indexDegree_eq,MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro x hx
  have h := Finsupp.apply_smul_le_weight (fun i : Fin 3 => i.val) x (2 : Fin 3)
  have htwo : (2 : Fin 3).val = 2 := rfl
  have hw : 2 * x 2 ≤ x.weight (fun i : Fin 3 => i.val) := by
    simpa only [smul_eq_mul,Nat.mul_comm,htwo] using h
  have hm := hw.trans (le_weightedTotalDegree (fun i : Fin 3 => i.val) hx)
  omega

theorem of_lower (rank : prefixRank S 76 ≤ R)
    (lower : ∀ (t : Fin 4) w Γ s, Scalar50Wide55NextPrice.Messages w Γ s →
    ∀ g, Scalar50Wide55NextPrice.LowerRow t g →
    (∀ γ ∈ Γ, K1_13.atJet g (K1_13.extend (s γ)) = 0) → Γ.card ≤ lowerCap t) :
    ScalarList A 1710834581234467 := by
  classical
  apply ScalarRootRows.list_of_indexed (by decide)
  · rw [Sol1.C64.native_field_card]
    decide
  intro w Γ s hinj hclose
  let e := Function.Embedding.refl (ColumnIndex A S)
  have hsmall := (stack_le_of_prefix CurveListScalarWide55.shapeOK widthOK rank w).trans_lt columnRoom
  obtain ⟨P,hP,hPf,hwt,hloc,_⟩ := exists_interpolant e CurveListScalarWide55.shapeOK
    CurveListScalarWide55.facet widthOK w hsmall
  obtain ⟨t,D,G,hD,hDP,hG,horder,hroot⟩ := narrow rank w hP
  have hdwt : differentialWeightedDegree N D < S.m*A :=
    (weightedTotalDegree_le_of_dvd (differentialWeight N) hDP hP.1).trans_lt hwt
  obtain ⟨row,hrow,hrowB,hrowJ,hrowC,hrowW,hrowRoot⟩ := ScalarRootRows.row_of_native hD hdwt
  let reg := Γ.filter fun γ => differentialSpecialization D (s γ) = 0
  let rest (g : DifferentialPolynomial K 1) := Γ.filter fun γ => differentialSpecialization g (s γ) = 0
  have msg : Scalar50Wide55NextPrice.Messages w Γ s := by
    exact ⟨hinj, fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).1,
      fun γ hγ => (ScalarRootRows.close_data (hclose γ hγ)).2⟩
  have hj : row.degreeOf 2 ≤ lowerIndex t / 2 :=
    (top_index row).trans (Nat.div_le_div_right hrowJ)
  have htop : row.degreeOf 2 ≤ lowerTop t :=
    (le_min (show row.degreeOf 2 ≤ 10 from hrowC) hj).trans (by fin_cases t <;> decide)
  have rowOK : Scalar50Wide55NextPrice.LowerRow t row := ⟨hrow,hrowB,hrowJ,htop,fun m hm =>
    (hrowW m hm).le.trans (by decide : S.m*A ≤ Scalar50Wide55NextPrice.anchorCutoff)⟩
  have hreg : reg.card ≤ lowerCap t := lower t w reg s (msg.mono (filter_subset _ _)) row rowOK
    (fun γ hγ => hrowRoot (s γ) (mem_filter.mp hγ).2)
  have hA : AgreementOK A := ⟨by decide,by decide,by decide,by decide⟩
  have hrest (g) (hg : g ∈ G.toFinset) : (rest g).card ≤ 496991961877 := by
    have hp := CurveListRectangularRoots.first_order_price hA residualOK
      (horder g (List.mem_toFinset.mp hg)) ((rest g).image s)
      (fun _ hf => by obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hf; exact hclose γ (mem_filter.mp hγ).1)
      (fun _ hf => by obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hf; exact (mem_filter.mp hγ).2)
    rw [card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (filter_subset _ _)))] at hp
    have hfee : CurveListRectangularRoots.curveFactor A * R₁ SB + (H SB : ℚ)^2 < 496991961878 :=
      by decide +kernel
    exact Nat.le_of_lt_succ (by exact_mod_cast hp.trans_lt hfee)
  have hcover : Γ ⊆ reg ∪ G.toFinset.biUnion rest := by
    intro γ hγ
    have hc := hclose γ hγ
    rcases hroot (s γ) hc (specializes hwt hloc (s γ) hc) with hd' | ⟨g,hg,hz⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hd'⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨g,List.mem_toFinset.mpr hg,mem_filter.mpr ⟨hγ,hz⟩⟩)
  have hsum := (card_le_card hcover).trans ((card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _))
  have htotal : (∑ g ∈ G.toFinset, (rest g).card) ≤ residualCount t * 496991961877 := by
    refine (sum_le_sum hrest).trans ?_
    rw [sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ ((List.toFinset_card_le G).trans hG)
  have hcap : lowerCap t + residualCount t * 496991961877 ≤ 1710834581234467 := by
    fin_cases t <;> decide
  exact hsum.trans ((Nat.add_le_add hreg htotal).trans hcap)

end Scalar50Wide55NextDirect
