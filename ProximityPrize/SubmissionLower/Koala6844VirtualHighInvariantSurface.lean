import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantIncidence
import ProximityPrize.SubmissionLower.Koala6831IntrinsicFrobeniusSlice


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN002 RCN005 RCN135 RCN136 RCN264 RCN267 RCN341 RCN344
open Koala6831OrdinaryIncidence

open scoped Classical BigOperators

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option maxRecDepth 14000

variable {K I : Type} [Field K]

theorem persistent_surface_fixed_word_seed_bound
    (F : Carrier K) (w bound p b c : ℕ) [CharP (GenericField K) p]
    (G : MvPolynomial (Fin 3) (GenericField K)) (irreducible : Irreducible G)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hy : 0 < G.degreeOf 0) (hyp : G.degreeOf 0 < p) (hzp : G.degreeOf 2 < p)
    (persist : ∀ j, G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F (w+j)))
    (hbound : 2 ≤ bound) (hw : w+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,w,0,0] : Fin 4 → ℕ) F < bound)
    (ht : ∀ d ∈ F.support, d 2 ≤ b) (hz : ∀ d ∈ F.support, d 3 ≤ c)
    (x : I ↪ K) (word : I → K) (nodes : Finset I) (A : ℕ)
    (hwA : w < A) (hAn : A ≤ nodes.card) (haverage : nodeAverage nodes.card w A ≤ 4)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hgraph : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (hG : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) (implicitRegularity F) ≠ 0)
    (hagree : ∀ g ∈ seeds, A ≤ (nodes.filter fun i => (selected g).eval (x i) = word i).card)
    (hinj : Set.InjOn selected ↑seeds) :
    seeds.card ≤ (4*(b+1+p*c)+1) * G.degreeOf 0 := by
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let H := surfaceMap φ (implicitRegularity F)
  let T := frobeniusSlice Ω p
  let Curve := RegularComponent Ω G T H
  let V := selectedGraphPoint p selected
  have regular (a : Curve) : MvPolynomial.pderiv 0 G ∉ a.1 := by
    intro hbad
    apply regularComponent_H_not_mem Ω G T H a
    obtain ⟨Q, hQ⟩ := hdiv
    change surfaceMap φ (implicitRegularity F) ∈ a.1
    rw [show surfaceMap φ (implicitRegularity F) = MvPolynomial.pderiv 0 (surfaceMap φ F)
        from (surfaceMap_pderiv φ F 0).symm, hQ, MvPolynomial.pderiv_mul]
    exact a.1.add_mem (a.1.mul_mem_right _ hbad)
      (a.1.mul_mem_right _ (regularComponent_G_mem Ω G T H a))
  letI : ∀ a : Curve, Algebra (RatFunc Ω) (CoordinateField Ω a.1) :=
    fun a => rationalBaseAlgebra Ω a.1 1 (frobeniusSlice_seed_transcendental p G H a (regular a))
  let d (a : Curve) := Module.finrank (RatFunc Ω) (CoordinateField Ω a.1)
  obtain ⟨fields, hsum⟩ := frobeniusSlice_projection_budget p G H irreducible hyp hzp regular hy
  let selectedCurve := componentSeeds Ω G T H seeds V
  have cover : seeds.card ≤ ∑ a : Curve, (selectedCurve a).card :=
    frobeniusSlice_seed_cover p F G seeds selected hG hreg
  have localBound (a : Curve) : (selectedCurve a).card ≤ (4*(b+1+p*c)+1)*d a := by
    let hx := frobeniusSlice_seed_transcendental p G H a (regular a)
    let B : SeparableLiteralCoordinate a.1 :=
      ⟨1, hx, (fields a).1, (fields a).2⟩
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω a.1) := (fields a).1
    have pol (W : Finset (Place Ω (CoordinateField Ω a.1))) :=
      frobeniusSlice_component_poles p a.1 (regularComponent_T_mem Ω G T H a)
        hx (fields a).1 (fields a).2 W
    have hsub : selectedCurve a ⊆ seeds := Finset.filter_subset _ _
    have fmem : surfaceMap φ F ∈ a.1 :=
      a.1.mem_of_dvd hdiv (regularComponent_G_mem Ω G T H a)
    have tmem (j : ℕ) : surfaceMap φ (tailNumerator F (w+j)) ∈ a.1 :=
      a.1.mem_of_dvd (persist j) (regularComponent_G_mem Ω G T H a)
    have bound' := persistent_curve_fixed_word_seed_bound F w bound p b c a.1 B (d a) (p*d a)
      (fun W => (pol W).1) (fun W => by rw [Nat.cast_mul]; exact (pol W).2)
      fmem (regularComponent_H_not_mem Ω G T H a) tmem hbound hw hchar hweight ht hz
      x word nodes A hwA hAn haverage (selectedCurve a) selected (fun g => g^p)
      (fun g hg => hdegree g (hsub hg)) (fun g hg => hgraph g (hsub hg))
      (fun g hg => by
        rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
        exact hreg g (hsub hg))
      (fun g hg => (Finset.mem_filter.mp hg).2)
      (fun g hg => hagree g (hsub hg)) (hinj.mono hsub)
    have hpos : 1 ≤ d a := Module.finrank_pos
    refine bound'.trans ?_
    have poly : 4 * ((b+1)*d a + c*(p*d a)) = 4*(b+1+p*c)*d a := by ring
    rw [poly, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left hpos _
  calc
    _ ≤ ∑ a : Curve, (selectedCurve a).card := cover
    _ ≤ ∑ a : Curve, (4*(b+1+p*c)+1)*d a := Finset.sum_le_sum fun a _ => localBound a
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hsum

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
