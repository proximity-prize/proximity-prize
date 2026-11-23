import ProximityPrize.SubmissionLower.Shared50ShapeRank
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Shared50Multiplicity
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Shared50ChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Final50SharedPrice (slope coord)

private theorem weighted_pow (w : Fin 4 → ℕ) {P : Row 4} (h : P ≠ 0) (a : ℕ) :
    (P^a).weightedTotalDegree w=a*P.weightedTotalDegree w:=by
  induction a with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ h) h,ih,Nat.succ_mul]

private theorem valuation_factorization {f P : Row 4} (hf : f ≠ 0)
    (hpos:0 < f.totalDegree) (hP:P≠0) :
    ∃ a:ℕ, ∃ G:Row 4,P=f^a*G ∧ G≠0 ∧ ¬ f ∣ G:=by
  have hm : FiniteMultiplicity f P := by
    refine ⟨P.totalDegree, ?_⟩
    intro hd
    have hle:=weightedTotalDegree_le_of_dvd (1:Fin 4→ℕ) hd hP
    rw [weighted_pow _ hf,weightedTotalDegree_one,weightedTotalDegree_one] at hle
    have ht:=Nat.mul_le_mul_left (P.totalDegree+1) hpos
    simp only [Nat.mul_one] at ht
    omega
  obtain ⟨G,hG,hd⟩:=hm.exists_eq_pow_mul_and_not_dvd
  exact ⟨_,G,hG,fun h0 => hP (by rw [hG,h0,mul_zero]),hd⟩

private theorem weight_coord (i : Fin 3) (P : Row 4) :
    coord (shape P) i =
      P.weightedTotalDegree (![fun _:Fin 4 => 1,Fin.val,Pi.single 3 1] i):=by
  fin_cases i
  · exact (weightedTotalDegree_one P).symm
  · exact K1_13_1.indexDegree_eq P
  · exact (weightedTotalDegree_piSingle (3:Fin 4) P).symm

theorem shape_product {f Q G : Row 4} (hf : f ≠ 0) (hG : G ≠ 0)
    {a:ℕ} (he:Q=f^a*G) (i:Fin 3) :
    coord (shape Q) i=a*coord (shape f) i+coord (shape G) i:=by
  simp only [weight_coord,he,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hf) hG,weighted_pow _ hf]

private theorem cap_coords {Q : Row 4} {r : ℕ}
    (hQ : ∀ m ∈ Q.support,Final50ShapeGate.fits r m) (i:Fin 3) :
    coord (shape Q) i≤r*coord slope i:=by
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs:=hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Final50SharedPrice.coord,
      Final50SharedPrice.slope,Pi.single_apply] using hs.2.2

private theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hf:Irreducible f) (hproper : ¬f∣G) (hP:P.height=2)
    (hF:toGeneric f∈P) (hG:toGeneric G∈P) :
    (intersectionIdeal f G).IsMinimalPrime P:=by
  have hsub : intersectionIdeal f G ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact hF
    · exact hG
  obtain ⟨P',hmin,hle⟩:=Ideal.exists_minimalPrimes_le hsub
  have hzero:=K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  have hrel:=K1_13_7_1.proper_generic f G hf hproper
  have hht:P'.height=2:=pair_height hzero hrel hmin
  letI:P'.IsPrime:=hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs:=Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin

private theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn:0<n) (hQ:VanishesTo P Q n):Q∈P:=by
  let L:=Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)

structure SuitableSurface (f : Row 4) (s : ℕ) (P : Ideal GeoJets) : Prop where
  prime:P.IsPrime
  height:P.height=2
  contains:toGeneric f ∈ P
  low : ¬ @VanishesTo _ _ P prime (toGeneric f) (s+1)

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut {w Γ s} (hm : Final50Price.Messages w Γ s)
    (f:Row 4) (hf:Irreducible f) (hpos:0<f.totalDegree)
    (multiplicityCap:ℕ) (pivot:Fin 3)
    (hguard:multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces:Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces,Shared50Persistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces,SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i,a*coord (shape f) i+coord (shape G) i≤r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a:ℕ):ℕ∞)≤cycleLength (intersectionIdeal f G) P h.isPrime:=by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩:=Shared50ShapeRank.exists_polynomial hm surfaces hp
  obtain ⟨a,G,hfac,hG,hind⟩:=valuation_factorization hf.ne_zero hpos hQ
  have hbound (i : Fin 3) : a*coord (shape f) i+coord (shape G) i ≤ r*coord slope i := by
    rw [← shape_product hf.ne_zero hG hfac i]
    exact cap_coords hs i
  have hres : 0<r-multiplicityCap*a := Shared50ShapeRankBase.residual_order_pos hr hguard
    ((Nat.le_add_right _ _).trans (hbound pivot))
  refine ⟨r,a,hr,hres,G,hG,hind,hbound,?_⟩
  intro P hP
  have hdata:=hh P hP
  letI:=hdata.prime
  have hmap : toGeneric Q = (toGeneric f)^a*toGeneric G := by
    simp [hfac,toGeneric,map_mul,map_pow]
  have hGo : VanishesTo P (toGeneric G) (r-multiplicityCap*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul_hasse P hdata.low
    rw [← hmap]
    exact ho P hP
  have hmin:=minimal_pair hf hind hdata.height hdata.contains (mem_of_order hres hGo)
  exact ⟨hmin,hGo,cycleLength_ge_order hdata.height hdata.contains hGo⟩

#print axioms exists_cut
end
end Shared50ChooseCut
