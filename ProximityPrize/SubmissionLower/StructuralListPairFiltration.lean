import ProximityPrize.SubmissionLower.StructuralListPairArithmetic

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial

noncomputable section

/-- The rank removed by multiplication with the source equation is exact. -/
theorem quotientBand_rank (T : Chart 2) (hE : T.equation ≠ 0) (a d e : ℕ) :
    let b := T.equation.totalDegree
    let j := T.equation.weightedTotalDegree Fin.val
    let c := T.equation.degreeOf (Fin.last 2)
    Module.finrank Geo (quotientBand T (a+b) (d+j) (e+c)) +
      Module.finrank Geo (bandSpace a d e) =
      Module.finrank Geo (bandSpace (a+b) (d+j) (e+c)) := by
  dsimp only
  let b := T.equation.totalDegree
  let j := T.equation.weightedTotalDegree Fin.val
  let c := T.equation.degreeOf (Fin.last 2)
  let W := bandSpace (a+b) (d+j) (e+c)
  let F := (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = quotientBand T (a+b) (d+j) (e+c) :=
    LinearMap.range_domRestrict W _
  let mul := (LinearMap.mulLeft Geo T.equation).domRestrict (bandSpace a d e)
  have hmul (p : bandSpace a d e) : mul p ∈ W := by
    have hband : T.equation ∈ bandSpace b j c := mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
    simpa only [mul, W, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, Nat.add_comm]
      using mul_mem_bandSpace hband p.property
  let g : bandSpace a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : bandSpace a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (sourceIdeal T) (T.equation * p.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val, rfl⟩)
  let G := g.codRestrict (LinearMap.ker F) hg
  have hG : Function.Injective G := by
    intro p q hpq
    have he : T.equation * p.val = T.equation * q.val :=
      congrArg (fun x : LinearMap.ker F => x.val.val) hpq
    exact Subtype.ext (mul_left_cancel₀ hE he)
  have hsurj : Function.Surjective G := by
    intro p
    have hmem : p.val.val ∈ (sourceIdeal T) := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp p.property)
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    have hqb : q ∈ bandSpace a d e := by
      by_cases hqz : q = 0
      · simp [hqz]
      obtain ⟨ht, hi, hc⟩ := mem_bandSpace.mp p.val.property
      rw [hq] at ht hi hc
      rw [totalDegree_mul_of_isDomain hE hqz] at ht
      rw [weightedTotalDegree_mul _ _ _ hE hqz] at hi
      rw [← weightedTotalDegree_piSingle, weightedTotalDegree_mul _ _ _ hE hqz,
        weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hc
      apply mem_bandSpace.mpr
      dsimp only [b, j, c] at ht hi hc
      exact ⟨by omega, by omega, by omega⟩
    refine ⟨⟨q, hqb⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hq.symm)
  have hdim := LinearEquiv.finrank_eq (LinearEquiv.ofBijective G ⟨hG, hsurj⟩)
  have hRank := F.finrank_range_add_finrank_ker
  rw [hF, ← hdim] at hRank
  exact hRank


/-- The ideal of the cut equation in the quotient by the chart equation. -/
def cutIdeal (T : Chart 2) (Q : InitialRing 2) : Ideal (InitialRing 2 ⧸ sourceIdeal T) :=
  Ideal.span {Ideal.Quotient.mk (sourceIdeal T) Q}

def cutBand (T : Chart 2) (Q : InitialRing 2) (a d e : ℕ) :
    Submodule Geo ((InitialRing 2 ⧸ sourceIdeal T) ⧸ cutIdeal T Q) :=
  (quotientBand T a d e).map (Ideal.Quotient.mkₐ Geo (cutIdeal T Q)).toLinearMap

instance (T : Chart 2) (Q : InitialRing 2) (a d e : ℕ) : Module.Finite Geo (cutBand T Q a d e) :=
  Module.Finite.map _ _

/-- Bound the rank of the cut filtration by charging the multiples of the cut equation. -/
theorem cutBand_rank_le (T : Chart 2) (hT : ChartOK T) (Q : InitialRing 2)
    (hQ : Q ∉ sourceIdeal T) (a d e b j c : ℕ) (hQband : Q ∈ bandSpace b j c) :
    Module.finrank Geo (cutBand T Q (a+b) (d+j) (e+c)) +
      Module.finrank Geo (quotientBand T a d e) ≤
      Module.finrank Geo (quotientBand T (a+b) (d+j) (e+c)) := by
  have hprime : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let := hprime
  let W := quotientBand T (a+b) (d+j) (e+c)
  let F := (Ideal.Quotient.mkₐ Geo (cutIdeal T Q)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = cutBand T Q (a+b) (d+j) (e+c) :=
    LinearMap.range_domRestrict W _
  let q := Ideal.Quotient.mk (sourceIdeal T) Q
  have hqn : q ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hQ
  let mul := (LinearMap.mulLeft Geo q).domRestrict (quotientBand T a d e)
  have hmul (p : quotientBand T a d e) : mul p ∈ W := by
    obtain ⟨u, hu, hmap⟩ := p.property
    refine ⟨Q * u, ?_, ?_⟩
    · change Q * u ∈ bandSpace (a+b) (d+j) (e+c)
      simpa only [Nat.add_comm] using mul_mem_bandSpace hQband hu
    · change Ideal.Quotient.mk (sourceIdeal T) (Q * u) = q * p.val
      rw [map_mul]
      congr 1
  let g : quotientBand T a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : quotientBand T a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (cutIdeal T Q) (q * p.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val, rfl⟩)
  let G := g.codRestrict (LinearMap.ker F) hg
  have hG : Function.Injective G := by
    intro p p' hp
    have he : q * p.val = q * p'.val := congrArg (fun x : LinearMap.ker F => x.val.val) hp
    exact Subtype.ext (mul_left_cancel₀ hqn he)
  have hRank := F.finrank_range_add_finrank_ker
  rw [hF] at hRank
  exact (Nat.add_le_add_left (LinearMap.finrank_le_finrank_of_injective hG) _).trans_eq hRank


open Filter
open private surfaceBound from ProximityPrize.SubmissionLower.ListProofA

/-- A proper cut has asymptotic filtered rank at most the mixed band volume. -/
theorem eventually_cutBand_rank (T : Chart 2) (hT : ChartOK T) (Q : InitialRing 2)
    (hQ : Q ∉ sourceIdeal T) (a d e L : ℕ) (hda : d < a) (hed : 2 * e < d) (he : 0 < e)
    (hQband : Q ∈ bandSpace (L*a) (L*d) (L*e)) :
    ∃ v : ℚ, ∀ᶠ m : ℕ in atTop,
      (Module.finrank Geo (cutBand T Q (m*a) (m*d) (m*e)) : ℚ) ≤
        (L : ℚ) * surfaceBound a d e T.equation.totalDegree
          (T.equation.weightedTotalDegree Fin.val : ℕ) (T.equation.degreeOf (Fin.last 2)) * (m : ℚ) + v := by
  let b := T.equation.totalDegree
  let j := T.equation.weightedTotalDegree Fin.val
  let c := T.equation.degreeOf (Fin.last 2)
  have decode (x : ℕ) (hx : b+j+c ≤ x) :
      (Module.finrank Geo (quotientBand T (x*a) (x*d) (x*e)) : ℚ) =
        bandCount (x*a) (x*d) (x*e) - bandCount (x*a-b) (x*d-j) (x*e-c) := by
    have ha₀ : x ≤ x*a := by simpa using Nat.mul_le_mul_left x (show 1 ≤ a by omega)
    have hd₀ : x ≤ x*d := by simpa using Nat.mul_le_mul_left x (show 1 ≤ d by omega)
    have he₀ : x ≤ x*e := by simpa using Nat.mul_le_mul_left x (show 1 ≤ e by omega)
    have hd₁ : x*d+x ≤ x*a := by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left x (Nat.succ_le_of_lt hda)
    have he₁ : 2*(x*e)+x ≤ x*d := by
      simpa only [Nat.mul_succ, Nat.mul_left_comm x 2 e] using
        Nat.mul_le_mul_left x (Nat.succ_le_of_lt hed)
    have h1 : b ≤ x*a := by omega
    have h2 : j ≤ x*d := by omega
    have h3 : c ≤ x*e := by omega
    have h := quotientBand_rank T hT.irreducible.ne_zero (x*a-b) (x*d-j) (x*e-c)
    change Module.finrank Geo (quotientBand T (x*a-b+b) (x*d-j+j) (x*e-c+c)) +
      Module.finrank Geo (bandSpace (x*a-b) (x*d-j) (x*e-c)) =
      Module.finrank Geo (bandSpace (x*a-b+b) (x*d-j+j) (x*e-c+c)) at h
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2, Nat.sub_add_cancel h3] at h
    have hq := congrArg ((↑) : ℕ → ℚ) h
    rw [Nat.cast_add,
      CJ0_4_2.proof (x*a-b) (x*d-j) (x*e-c) (by omega) (by omega),
      CJ0_4_2.proof (x*a) (x*d) (x*e) (by omega) (by omega)] at hq
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3] at hq
    linarith only [hq]
  obtain ⟨v, hv⟩ := bandDoubleDifference (a : ℚ) d e b j c L
  refine ⟨v, ?_⟩
  filter_upwards [eventually_ge_atTop (L+b+j+c)] with m hm
  have hL : L ≤ m := by omega
  have haeq : (m-L)*a + L*a = m*a := by rw [← Nat.add_mul, Nat.sub_add_cancel hL]
  have hdeq : (m-L)*d + L*d = m*d := by rw [← Nat.add_mul, Nat.sub_add_cancel hL]
  have heeq : (m-L)*e + L*e = m*e := by rw [← Nat.add_mul, Nat.sub_add_cancel hL]
  have hm' : b+j+c ≤ m-L := by omega
  have h := cutBand_rank_le T hT Q hQ ((m-L)*a) ((m-L)*d) ((m-L)*e) (L*a) (L*d) (L*e) hQband
  rw [haeq, hdeq, heeq] at h
  have hRat := Nat.cast_le (α := ℚ) |>.mpr h
  rw [Nat.cast_add, decode m (by omega), decode (m-L) hm', Nat.cast_sub hL] at hRat
  rw [← hv (m : ℚ)]
  linarith only [hRat]

end

end StructuralList
