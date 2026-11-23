import ProximityPrize.SubmissionLower.Final50ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low49ActiveVolume
import Mathlib.Algebra.MvPolynomial.Coeff

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open private diagonal_unit grade_sum diagonal_sum coeff_congr
  from ProximityPrize.SubmissionLower.Low48BentCycleCap
open private ambient_list from ProximityPrize.SubmissionLower.Low48BentCyclePrice
open Low49ActiveVolume (fits_scale point_scale point_zero)

private def integr (a:Cap):ℚ:=integral a

private def signed (p : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p))

private theorem base_signed (p : Shape) :
    Final50Price.tiltedSurface p Final50Price.primaryBox=(signed p).toNat:=by
  change Low48Price.ambientMix (slots.map (caps p))=_
  exact ambient_list (caps p)

private theorem base_normalize (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p) (positiveDiagonal J)))=(signed p:ℚ):=by
  have H:=Low48BentPolarization.remove_baseline (caps p)
  change _=_ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5=integr a / 60:=by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p : Shape} (h : ∀ i, Chamber (caps p i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p)) ⊥ Finset.univ ≤
      (Final50Price.tiltedSurface p Final50Price.primaryBox:ℚ):=by
  rw [mul_assoc,ambient_cap (caps p) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize,base_signed]
  exact_mod_cast (show signed p≤((signed p).toNat:ℤ) by omega)

private theorem fits_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s,Fits (a i) (c i)) :
    Fits (Low48BentLattice.Sum s a) (∑ i ∈ s,c i):=by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Fits,Low48BentLattice.Sum]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs:=ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hm:=Low49ActiveLattice.fits_add (h i (Finset.mem_insert_self _ _)) hs
    simpa only [Low48BentLattice.Sum,Finset.sum_insert hi,Low48BentLattice.Add,Shape.plus] using hm

private theorem points_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s,Fits (a i) (c i)) :
    (∑ i ∈ s,points (a i) (c i))=points (Low48BentLattice.Sum s a) (∑ i ∈ s,c i):=by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Low48BentLattice.Sum] using point_zero.symm
  | insert i s hi ih =>
    have hs (j:Fin 5) (hj:j ∈ s):=h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hs,
      Low49ActiveLattice.add (h i (Finset.mem_insert_self _ _)) (fits_sum s a c hs)]
    simp only [Low48BentLattice.Sum,Low48BentLattice.Add,Finset.sum_insert hi,Shape.plus]

private def clipSum (p:Shape) (K:ℕ) (t:Grade):ℕ := ∑ i,t i*clips p K i

private theorem active_diagonal {p : Shape} {K : ℕ} (t : Grade)
    (h : ∀ i,Fits (caps p i) (clips p K i)) :
    diagonalExponents (activeFamily p K) t=points (capSum (caps p) t) (clipSum p K t):=by
  have h0:=(active_doubled h).double_zero
  calc
    _ = ∑ i : Fin 5, diagonalExponents (activeFamily p K) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, points (Scale (t i) (caps p i)) (t i * clips p K i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul,diagonal_unit _ h0]
      exact point_scale _ _ (h i) _
    _=_:=points_sum _ _ _ (fun i _ => fits_scale (h i) _)

private theorem fifth_difference (v : Fin 5 → ℚ) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (∑ i,(positiveDiagonal J i:ℚ)*v i)^5)=120 * ∏ i,v i:=by
  let f:Form:=(∑ i:Fin 5,C (v i)*MvPolynomial.X i)^5
  have hlin : (∑ i : Fin 5, (C (v i) * MvPolynomial.X i : Form)).IsHomogeneous 1 := by
    change _ ∈ homogeneousSubmodule (Fin 5) ℚ 1
    apply Submodule.sum_mem
    intro i _
    exact (isHomogeneous_X ℚ i).C_mul _
  have hf : f.IsHomogeneous 5 := by
    simpa only [Nat.mul_one] using hlin.pow 5
  have hsum:=cube_extract (Finset.univ:Finset (Fin 5)) f
  simp only [Finset.card_univ,Fintype.card_fin] at hsum
  simp_rw [line_coeff,homogeneousComponent_eq_self hf] at hsum
  have he (J : Finset (Fin 5)) :
      eval (fun i => (positiveDiagonal J i:ℚ)) f=(∑ i,(positiveDiagonal J i:ℚ)*v i)^5:=by
    simp [f,mul_comm]
  simp_rw [he] at hsum
  rw [hsum]
  unfold f
  simp only [← smul_eq_C_mul]
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hu (i:Fin 5):squarefree Finset.univ i=1:=by simp [squarefree_apply]
  have hd : (squarefree (Finset.univ : Finset (Fin 5))).degree = 5 := by
    simp [K1_13_6_2_4_1.squarefree_degree]
  have hh : (squarefree (Finset.univ : Finset (Fin 5))).support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff,hu]
  have hsum' : (squarefree (Finset.univ:Finset (Fin 5))).sum (fun _ m => m)=5:=hd
  simp [hsum', Finsupp.multinomial_eq, Finsupp.prod, hh, hu, Nat.multinomial,
    Finset.sum_const,Nat.factorial]

private theorem clips_prod (p : Shape) (K : ℕ) (ht : 3 ≤ p.t)
    (h : ∀ i,Fits (caps p i) (clips p K i)) :
    (Final50Price.activeLoss (Final50Price.activeClips p K) : ℚ) =
      480 * ((∏ i, (clips p K i : ℚ)) -
        (∏ i,((clips p K i:ℚ) - 2*((caps p i).2:ℚ)))):=by
  rw [← clip_list p K ht]
  unfold Final50Price.activeLoss
  have hi (i:Fin 5):2*(caps p i).2≤clips p K i:=(h i).2.2.2.2.1
  have hle : (∏ i, (clips p K i - 2 * (caps p i).2)) ≤ ∏ i, clips p K i :=
    Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
  have hp (a : Fin 5 → ℕ) : (slots.map a).prod = ∏ i, a i := by
    rw [← List.prod_toFinset a (show slots.Nodup by decide)]
    rw [show slots.toFinset=Finset.univ by decide]
  simp only [List.map_map,Function.comp_apply,hp]
  rw [Nat.cast_mul,Nat.cast_sub hle]
  push_cast [Nat.cast_sub,hi]
  norm_num

theorem active_budget {p : Shape} {K : ℕ} (ht : 3 ≤ p.t)
    (h : ∀ i,Fits (caps p i) (clips p K i)) :
    (60 * 32 : ℚ) * mixedDegree (activeFamily p K) ⊥ Finset.univ ≤
      (Final50Price.tiltedSurfaceActive p Final50Price.primaryBox K:ℚ):=by
  classical
  have hcoeff (J : Finset (Fin 5)) :
      (affineHilbertPolynomial (Ideal.comap
        (monomialMap GeoField (diagonalExponents (activeFamily p K) (positiveDiagonal J))) ⊥)).coeff 5 =
      (integr (capSum (caps p) (positiveDiagonal J)) -
        4 * ((clipSum p K (positiveDiagonal J) : ℚ)^5 -
          ((clipSum p K (positiveDiagonal J) : ℚ) -
            2*((capSum (caps p) (positiveDiagonal J)).2:ℚ))^5)) / 60:=by
    rw [coeff_congr _ _ (active_diagonal _ h)]
    have hs := fits_sum Finset.univ (fun i => Scale (positiveDiagonal J i) (caps p i))
      (fun i => positiveDiagonal J i*clips p K i) (fun i _ => fits_scale (h i) _)
    let a:=capSum (caps p) (positiveDiagonal J)
    let c:=clipSum p K (positiveDiagonal J)
    change (affineHilbertPolynomial ((⊥ : Ideal K1_13_6_2.GeoJets5).comap
      (monomialMap GeoField (points a c)).toRingHom)).coeff 5=_
    rw [Low49ActiveVolume.ambient_coeff a c hs]
    unfold integr integral
    rw [Low48BentVolume.cast_price_integral a]
  have hc (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J):ℚ) = ∑ i,(positiveDiagonal J i:ℚ)*clips p K i:=by
    unfold clipSum
    push_cast
    rfl
  have hcd (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) -
          2*((capSum (caps p) (positiveDiagonal J)).2:ℚ) =
        ∑ i,(positiveDiagonal J i:ℚ)*((clips p K i:ℚ) - 2*((caps p i).2:ℚ)):=by
    rw [hc]
    simp only [capSum, Low48BentLattice.Sum, Scale, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum,
      Finset.sum_sub_distrib,mul_sub]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold mixedDegree
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [show (2 : ℚ)^5 = 32 by norm_num, mul_assoc, ← mul_div_assoc (32 : ℚ),
    mul_div_cancel_left₀ _ (by norm_num:(32:ℚ)≠0)]
  simp_rw [hcoeff, ← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num:(60:ℚ)≠0)]
  have hsum_rearr (A C D : Finset (Fin 5) → ℚ) :
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (A J - 4*(C J - D J))) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * A J) -
        4 * ((∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * C J) -
          (∑ J ∈ (Finset.univ:Finset (Fin 5)).powerset,(-1:ℚ) ^ (5 - J.card)*D J)):=by
    simp only [mul_sub,Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw [hsum_rearr,base_normalize]
  simp_rw [hcd,hc]
  simp_rw [fifth_difference]
  rw [show 4 * (120 * (∏ i, (clips p K i : ℚ)) -
      120 * ∏ i,((clips p K i:ℚ) - 2*((caps p i).2:ℚ))) =
      (Final50Price.activeLoss (Final50Price.activeClips p K):ℚ) by rw [clips_prod p K ht h]; ring]
  unfold Final50Price.tiltedSurfaceActive
  rw [base_signed]
  exact_mod_cast (show signed p - (Final50Price.activeLoss (Final50Price.activeClips p K) : ℤ) ≤
    (((signed p).toNat - Final50Price.activeLoss (Final50Price.activeClips p K):ℕ):ℤ) by omega)

end
end Final50ActiveCycle
