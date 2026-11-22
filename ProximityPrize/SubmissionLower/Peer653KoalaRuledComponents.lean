-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, KoalaRuledComponents.lean.
import ProximityPrize.SubmissionLower.Peer653KoalaRuledGraph
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace SplitCut.Rect
noncomputable section
open MvPolynomial

variable {F : Type*} [Field F] {σ : Type*} [Finite σ]

private theorem regular_avoids_minimal {R : Type*} [CommRing R] {I Q : Ideal R}
    (hQ : Q ∈ I.minimalPrimes) {s : R} (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    s ∉ Q := by
  rw [Ideal.minimalPrimes_eq_comap] at hQ
  obtain ⟨P,hP,rfl⟩ := hQ
  intro hm
  have hm' : (Ideal.Quotient.mk I) s ∈ P := hm
  apply (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hm' hP)
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact (isLeftRegular_iff_right_eq_zero_of_mul.mp hs) x ((mul_comm _ _).trans hx)

private theorem pullback_cut {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (I : Ideal A) {s : A} {u : R} (hu : φ u = s) :
    (I ⊔ Ideal.span {s}).comap φ = I.comap φ ⊔ Ideal.span {u} := by
  apply le_antisymm
  · intro x hx
    change φ x ∈ I ⊔ Ideal.span {s} at hx
    obtain ⟨p,hp,q,hq,he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hq
    obtain ⟨b,hb⟩ := hφ a
    have hq' : φ (u*b) = q := by rw [map_mul,hu,hb,← ha]
    have hp' : x-u*b ∈ I.comap φ := by
      change φ (x-u*b) ∈ I
      rw [map_sub,hq',← he,add_sub_cancel_right]
      exact hp
    exact Submodule.mem_sup.mpr ⟨_,hp',_,Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _),
      sub_add_cancel _ _⟩
  · apply sup_le (Ideal.comap_mono le_sup_left)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change φ u ∈ I ⊔ Ideal.span {s}
    rw [hu]
    exact (show Ideal.span {s} ≤ I ⊔ Ideal.span {s} from le_sup_right) (Ideal.mem_span_singleton_self _)

theorem regular_comap {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    {I : Ideal A} {s : A} {u : R} (hu : φ u = s)
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    IsLeftRegular (Ideal.Quotient.mk (I.comap φ) u) := by
  let q := Ideal.quotientMap I φ (le_rfl : I.comap φ ≤ I.comap φ)
  have he : q (Ideal.Quotient.mk (I.comap φ) u) = Ideal.Quotient.mk I s := congrArg (Ideal.Quotient.mk I) hu
  have hq : Function.Injective q := Ideal.quotientMap_injective
  intro x y hxy
  apply hq
  apply hs
  have h := congrArg q hxy
  simpa only [map_mul, he] using h

theorem saturation_regular {R : Type*} [CommRing R] {I G : Ideal R} {u : R}
    (hSat : ∀ x, x ∈ G ↔ ∃ n : ℕ, u^n*x ∈ I) :
    IsLeftRegular (Ideal.Quotient.mk G u) := by
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro q
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective q
  intro hx
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
  obtain ⟨n,hn⟩ := (hSat (u*x)).mp hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (hSat x).mpr ⟨n+1, by simpa only [pow_succ, mul_assoc] using hn⟩

theorem saturation_components {R : Type*} [CommRing R] {I G : Ideal R} {u : R} (hIG : I ≤ G)
    (hSat : ∀ x, x ∈ G ↔ ∃ n : ℕ, u^n*x ∈ I) : G.minimalPrimes ⊆ I.minimalPrimes := by
  intro P hP
  letI := hP.isPrime
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (hIG.trans hP.le)
  have huP := regular_avoids_minimal hP (saturation_regular hSat)
  have hGQ : G ≤ Q := by
    intro x hx
    obtain ⟨n,hn⟩ := (hSat x).mp hx
    have hq := hQ.le hn
    exact (hQ.isPrime.mul_mem_iff_mem_or_mem.mp hq).resolve_left fun h =>
      huP (hP.isPrime.mem_of_pow_mem n (hQP h))
  have he : P = Q := le_antisymm (hP.2 ⟨hQ.isPrime,hGQ⟩ hQP) hQP
  simpa only [he] using hQ

/-- A regular cut of a pure embedded ideal has the expected dimension on every component. -/
theorem cut_pure {A : Type*} [CommRing A] (φ : MvPolynomial σ F →+* A)
    (hφ : Function.Surjective φ) {I : Ideal A} {s : A}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s))
    (hproper : (I ⊔ Ideal.span {s}) ≠ ⊤) {n : ℕ} (hn : 0<n)
    (hDim : (affineHilbertPolynomial (I.comap φ)).natDegree = n)
    (hpure : ∀ P ∈ (I.comap φ).minimalPrimes, (affineHilbertPolynomial P).natDegree = n) :
    let J := (I ⊔ Ideal.span {s}).comap φ
    (affineHilbertPolynomial J).natDegree = n-1 ∧
      ∀ P ∈ J.minimalPrimes, (affineHilbertPolynomial P).natDegree = n-1 := by
  classical
  let K := I.comap φ
  let L : Ideal A := I ⊔ Ideal.span {s}
  let J := L.comap φ
  obtain ⟨u,hu⟩ := hφ s
  have hJ : J = K ⊔ Ideal.span {u} := pullback_cut φ hφ I hu
  have hreg := regular_comap φ hu hs
  have hcomponents (P : Ideal (MvPolynomial σ F)) (hP : P ∈ J.minimalPrimes) :
      (affineHilbertPolynomial P).natDegree = n-1 := by
    letI := hP.isPrime
    rw [hJ] at hP
    obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hP.le : K ≤ P)
    letI := hQ.isPrime
    have huQ : u ∉ Q := regular_avoids_minimal hQ hreg
    have hPm : P ∈ (Q ⊔ Ideal.span {u}).minimalPrimes :=
      ⟨⟨hP.isPrime,sup_le hQP (le_sup_right.trans hP.le)⟩,
       fun _ h' hle => hP.2 ⟨h'.1, (sup_le_sup hQ.le le_rfl).trans h'.2⟩ hle⟩
    have hqd := hpure Q hQ
    have hh := principalCut_natDegree_affineHilbertPolynomial_add_one huQ hPm
    omega
  have hupper : (affineHilbertPolynomial J).natDegree ≤ n-1 := by
    rw [hJ]
    refine (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg
      (le_rfl : u.totalDegree ≤ u.totalDegree)).1.trans ?_
    exact (congrArg (·-1) hDim).le
  have hbase : J ≠ ⊤ := by
    intro h
    apply hproper
    change L = ⊤
    rw [← Ideal.map_comap_of_surjective φ hφ L, show L.comap φ = ⊤ from h, Ideal.map_top]
  obtain ⟨P,hP⟩ := Ideal.nonempty_minimalPrimes hbase
  have hlower : n-1 ≤ (affineHilbertPolynomial J).natDegree := by
    rw [← hcomponents P hP]
    exact natDegree_affineHilbertPolynomial_le_of_le hP.le
  exact ⟨le_antisymm hupper hlower, hcomponents⟩

/-- Cutting the embedded root hypersurface by a regular tangent section gives pure surfaces. -/
theorem graph_pure (φ : MvPolynomial σ F →ₐ[F] Ring F) (hφ : Function.Surjective φ)
    {g s : Ring F} (hg : g ≠ 0)
    (hs : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {g}) s))
    (hproper : (Ideal.span {g} ⊔ Ideal.span {s} : Ideal (Ring F)) ≠ ⊤) :
    let J := (Ideal.span {g} ⊔ Ideal.span {s}).comap φ
    (affineHilbertPolynomial J).natDegree = 2 ∧
      ∀ P ∈ J.minimalPrimesFinset, (affineHilbertPolynomial P).natDegree = 2 := by
  classical
  let I : Ideal (Ring F) := Ideal.span {g}
  let J : Ideal (Ring F) := I ⊔ Ideal.span {s}
  let K := I.comap φ
  obtain ⟨u,hu⟩ := hφ s
  obtain ⟨g',hg'⟩ := hφ g
  have hK : K = RingHom.ker φ ⊔ Ideal.span {g'} := by
    change (Ideal.span {g}).comap φ = _
    rw [← hg']
    exact Ideal.comap_span_singleton_of_surjective φ.toRingHom hφ g'
  have hJ : J.comap φ = K ⊔ Ideal.span {u} := pullback_cut φ.toRingHom hφ I hu
  have hreg := regular_comap φ.toRingHom hu hs
  have hg'' : g' ∉ RingHom.ker φ := by
    intro h
    apply hg
    simpa only [RingHom.mem_ker, hg'] using h
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ.toRingHom
  have hdegreeKer : (affineHilbertPolynomial (RingHom.ker φ)).natDegree = 4 := by
    rw [natDegree_affineHilbertPolynomial_ker_of_surjective φ hφ, Nat.card_fin]
  have hcomponents (P : Ideal (MvPolynomial σ F)) (hP : P ∈ (J.comap φ).minimalPrimes) :
      (affineHilbertPolynomial P).natDegree = 2 := by
    letI := hP.isPrime
    rw [hJ] at hP
    obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hP.le : K ≤ P)
    letI := hQ.isPrime
    have hqd : (affineHilbertPolynomial Q).natDegree = 3 := by
      rw [hK] at hQ
      have hh := principalCut_natDegree_affineHilbertPolynomial_add_one hg'' hQ
      omega
    have huQ : u ∉ Q := regular_avoids_minimal hQ hreg
    have hPm : P ∈ (Q ⊔ Ideal.span {u}).minimalPrimes :=
      ⟨⟨hP.isPrime,sup_le hQP (le_sup_right.trans hP.le)⟩,
       fun _ h' hle => hP.2 ⟨h'.1, (sup_le_sup hQ.le le_rfl).trans h'.2⟩ hle⟩
    have hh := principalCut_natDegree_affineHilbertPolynomial_add_one huQ hPm
    omega
  have hi : I ≠ ⊤ := by
    intro h
    apply hproper
    change I ⊔ Ideal.span {s} = ⊤
    rw [h]
    exact sup_eq_left.mpr le_top
  have hdK : (affineHilbertPolynomial K).natDegree = 3 := by
    have hh := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective φ hφ hg hi
    rw [show Nat.card (Fin 4) = 4 from Nat.card_fin _] at hh
    exact Nat.add_right_cancel (show (affineHilbertPolynomial K).natDegree+1 = 3+1 from hh)
  have hupper : (affineHilbertPolynomial (J.comap φ)).natDegree ≤ 2 := by
    rw [hJ]
    refine (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg
      (le_rfl : u.totalDegree ≤ u.totalDegree)).1.trans ?_
    change (affineHilbertPolynomial K).natDegree - 1 ≤ 2
    rw [hdK]
  have hbase : J.comap φ ≠ ⊤ := by
    intro h
    change J.comap φ.toRingHom = ⊤ at h
    apply hproper
    change J = ⊤
    rw [← Ideal.map_comap_of_surjective φ.toRingHom hφ J,h, Ideal.map_top]
  obtain ⟨P,hP⟩ := Ideal.nonempty_minimalPrimes hbase
  have hlower : 2 ≤ (affineHilbertPolynomial (J.comap φ)).natDegree := by
    rw [← hcomponents P hP]
    exact natDegree_affineHilbertPolynomial_le_of_le hP.le
  exact ⟨le_antisymm hupper hlower, fun P hP => hcomponents P (Ideal.mem_minimalPrimesFinset.mp hP)⟩

#print axioms graph_pure
#print axioms saturation_components
#print axioms cut_pure
end
end SplitCut.Rect
