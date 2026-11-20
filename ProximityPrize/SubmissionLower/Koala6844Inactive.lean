import ProximityPrize.SubmissionLower.Koala6844Primitive
import ProximityPrize.SubmissionLower.Koala6844ScalarList
import ProximityPrize.SubmissionLower.Koala6844NormalizationData



namespace ProximityPrize.SubmissionLower.Koala6844Inactive

open Polynomial
open ProximityPrize.Benchmark
open Koala6844Normalization
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem product_dvd_of_inactive {K : Type} [Field K]
    (σ : K ≃+* K) (d₀ d₁ Q B P D : Polynomial K) (g : K)
    (hd₁ : d₁ ≠ 0) (hcoprime : IsCoprime d₀ d₁)
    (hden : IsCoprime (B.map σ.toRingHom) d₁)
    (hinactive : d₁ ∣ D)
    (heq : B.map σ.toRingHom * Q = d₁ * P.map σ.toRingHom + C (σ g) * D)
    (hhomogeneous : d₁ * Q.map σ.toRingHom = d₀.map σ.toRingHom * Q) :
    d₀ * d₁ ∣ Q := by
  have hdiv₁ : d₁ ∣ Q := by
    apply hden.symm.dvd_of_dvd_mul_left
    rw [heq]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hinactive _)
  obtain ⟨R, hR⟩ := hdiv₁
  have hmap : Q.map σ.toRingHom = d₀.map σ.toRingHom * R := by
    apply mul_left_cancel₀ hd₁
    calc
      d₁ * Q.map σ.toRingHom = d₀.map σ.toRingHom * Q := hhomogeneous
      _ = d₁ * (d₀.map σ.toRingHom * R) := by rw [hR]; ring
  have hcomp : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id K := by
    ext t
    exact σ.symm_apply_apply t
  have hdiv₀ : d₀ ∣ Q := ⟨R.map σ.symm.toRingHom, by
    simpa only [Polynomial.map_mul, Polynomial.map_map, hcomp, Polynomial.map_id]
      using congrArg (Polynomial.map σ.symm.toRingHom) hmap⟩
  exact hcoprime.mul_dvd hdiv₀ ⟨R, hR⟩

private theorem fixed_quotient_fiber_le {K : Type} [Field K] [DecidableEq K]
    (seeds : Finset K) (P R : K → Polynomial K) (d A₀ A₁ C₁ Q : Polynomial K)
    (w e : ℕ) (hd : d ≠ 0)
    (hdegree : ∀ g ∈ seeds, (P g).natDegree ≤ w)
    (hequation : ∀ g ∈ seeds, d * P g = A₀ * R g + C g * (A₁ * R g - C₁))
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (seeds.filter (fun g => P g = p₀ + C g * p₁)).card ≤ e + 1) :
    (seeds.filter (fun g => R g = Q)).card ≤ e + 1 := by
  classical
  let fiber := seeds.filter (fun g => R g = Q)
  apply Koala6844Cramer.card_le_of_common_denominator fiber P d
    (A₀ * Q) (A₁ * Q - C₁) hd w e
  · exact fun g hg => hdegree g (Finset.mem_filter.mp hg).1
  · intro g hg
    obtain ⟨hs, hQ⟩ := Finset.mem_filter.mp hg
    simpa only [hQ] using hequation g hs
  · intro p₀ p₁ h₀ h₁
    refine (Finset.card_le_card ?_).trans (hpencil p₀ p₁ h₀ h₁)
    intro g hg
    obtain ⟨hf, hp⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, hp⟩

private theorem eval_injOn_degree_le {K I : Type} [Field K] [Fintype I]
    (domain : I ↪ K) (w : ℕ) (hsize : w < Fintype.card I) :
    Set.InjOn (fun (Q : Polynomial K) i => Q.eval (domain i)) {Q | Q.natDegree ≤ w} := by
  classical
  intro P hP Q hQ heq
  by_contra hne
  have hnonzero : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hroot : ((Finset.univ : Finset I).image domain).card ≤ (P - Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply (Polynomial.mem_roots hnonzero).mpr
    change (P - Q).eval (domain i) = 0
    have hvalue : P.eval (domain i) = Q.eval (domain i) := congrFun heq i
    rw [Polynomial.eval_sub, hvalue, sub_self]
  rw [Finset.card_image_of_injective _ domain.injective, Finset.card_univ] at hroot
  exact (not_le_of_gt hsize) (hroot.trans ((Polynomial.natDegree_sub_le _ _).trans (max_le hP hQ)))

private theorem filter_card_mono {ι : Type} {p : ι → Prop}
    (left right : DecidablePred p) {S T : Finset ι} (hST : S ⊆ T)
    {a : ℕ} (h : a ≤ (@Finset.filter _ p left S).card) :
    a ≤ (@Finset.filter _ p right T).card := by
  have hsame : right = left := Subsingleton.elim _ _
  subst right
  have hfilter : @Finset.filter _ p left S ⊆ @Finset.filter _ p left T := by
    intro i hi
    obtain ⟨hiS, hp⟩ := (@Finset.mem_filter _ p left S i).mp hi
    exact (@Finset.mem_filter _ p left T i).mpr ⟨hST hiS, hp⟩
  exact h.trans (Finset.card_le_card hfilter)

private theorem quotient_list_card_le
    (seeds : Finset IRSProfile.Field)
    (R : IRSProfile.Field → Polynomial IRSProfile.Field)
    (nodes : Finset IRSProfile.Index) (received : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ g ∈ seeds, (R g).natDegree ≤ 131071)
    (hclose : ∀ g ∈ seeds, 180958 ≤
      (nodes.filter (fun i => (R g).eval (IRSProfile.domain i) = received i)).card) :
    (seeds.image R).card ≤ 113387658701 := by
  let evalWord (Q : Polynomial IRSProfile.Field) (i : IRSProfile.Index) :=
    Q.eval (IRSProfile.domain i)
  let words := (seeds.image R).image evalWord
  have hsize : 131071 < Fintype.card IRSProfile.Index := by
    rw [IRSProfile.card_index]
    decide
  have hinj : Set.InjOn evalWord (↑(seeds.image R) : Set (Polynomial IRSProfile.Field)) := by
    apply (eval_injOn_degree_le IRSProfile.domain 131071 hsize).mono
    intro Q hQ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    exact hdegree g hg
  have hcard : words.card = (seeds.image R).card :=
    Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply Koala6844ScalarList.irs_scalar_finite_list_card_le received words
  · intro word hw
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    change evalWord (R g) ∈ ReedSolomon.code IRSProfile.domain 131072
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (R g)
      (Nat.lt_succ_of_le (hdegree g hg)) (fun _ => rfl)
  · intro word hw
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    exact filter_card_mono _ _ (Finset.subset_univ nodes) (hclose g hg)

theorem card_le_of_inactive
    (σ : IRSProfile.Field ≃+* IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (selected normalized : IRSProfile.Field → Polynomial IRSProfile.Field)
    (nodes : Finset IRSProfile.Index) (fixedWord : IRSProfile.Index → IRSProfile.Field)
    (A : Fin 2 → Polynomial IRSProfile.Field)
    (d₀ d₁ C₁ D₁ : Polynomial IRSProfile.Field)
    (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (hcoprime : IsCoprime d₀ d₁)
    (hdomain : ∀ i ∈ nodes, (d₀ * d₁).eval (IRSProfile.domain i) ≠ 0)
    (hinactive : d₁ ∣ D₁)
    (hden : ∀ g ∈ seeds, IsCoprime ((specializeAffine A g).map σ.toRingHom) d₁)
    (heq₀ : ∀ g ∈ seeds, specializeAffine A g * normalized g =
      d₀ * selected g + C g * C₁)
    (heq₁ : ∀ g ∈ seeds, (specializeAffine A g).map σ.toRingHom * normalized g =
      d₁ * (selected g).map σ.toRingHom + C (σ g) * D₁)
    (hhomogeneous : ∀ g ∈ seeds, d₁ * (normalized g).map σ.toRingHom =
      d₀.map σ.toRingHom * normalized g)
    (hselected : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hnormalized : ∀ g ∈ seeds, (normalized g).natDegree ≤ 131071 + d₀.natDegree)
    (hclose : ∀ g ∈ seeds, 180958 ≤
      (nodes.filter (fun i => (normalized g).eval (IRSProfile.domain i) = fixedWord i)).card)
    (hpencil : ∀ p₀ p₁ : Polynomial IRSProfile.Field,
       p₀.natDegree ≤ 131071 → p₁.natDegree ≤ 131071 →
       (seeds.filter (fun g => selected g = p₀ + C g * p₁)).card ≤ 81187) :
    seeds.card ≤ 9205603846958087 := by
  let d := d₀ * d₁
  have hd : d ≠ 0 := mul_ne_zero hd₀ hd₁
  have hdiv (g : IRSProfile.Field) (hg : g ∈ seeds) : d ∣ normalized g :=
    product_dvd_of_inactive σ d₀ d₁ (normalized g) (specializeAffine A g)
      (selected g) D₁ g hd₁ hcoprime (hden g hg) hinactive (heq₁ g hg)
      (hhomogeneous g hg)
  let R (g : IRSProfile.Field) : Polynomial IRSProfile.Field :=
    if hg : g ∈ seeds then Classical.choose (hdiv g hg) else 0
  have hR g (hg : g ∈ seeds) : normalized g = d * R g := by
    simpa only [R, dite_eq_left hg] using (Classical.choose_spec (hdiv g hg))
  have hRdegree (g : IRSProfile.Field) (hg : g ∈ seeds) : (R g).natDegree ≤ 131071 := by
    by_cases hzero : R g = 0
    · simp [hzero]
    have hdeg := hnormalized g hg
    rw [hR g hg, Polynomial.natDegree_mul hd hzero,
      show d.natDegree = d₀.natDegree + d₁.natDegree from Polynomial.natDegree_mul hd₀ hd₁] at hdeg
    omega
  let received (i : IRSProfile.Index) := fixedWord i / d.eval (IRSProfile.domain i)
  have hRclose g (hg : g ∈ seeds) :
      180958 ≤ (nodes.filter (fun i => (R g).eval (IRSProfile.domain i) = received i)).card := by
    refine (hclose g hg).trans (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨hinode, heval⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hinode, (eq_div_iff (hdomain i hinode)).mpr ?_⟩
    rw [hR g hg, Polynomial.eval_mul] at heval
    exact (mul_comm _ _).trans heval
  have hlist := quotient_list_card_le seeds R nodes received hRdegree hRclose
  have hrel g (hg : g ∈ seeds) :
      d₀ * selected g = (A 0 * d) * R g + C g * ((A 1 * d) * R g - C₁) := by
    have h := heq₀ g hg
    rw [specializeAffine, hR g hg] at h
    linear_combination -h
  let fibers (Q : Polynomial IRSProfile.Field) := seeds.filter (fun g => R g = Q)
  have hcover : seeds ⊆ (seeds.image R).biUnion fibers := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨R g, Finset.mem_image_of_mem _ hg, Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
  calc
    seeds.card ≤ ((seeds.image R).biUnion fibers).card := Finset.card_le_card hcover
    _ ≤ ∑ Q ∈ seeds.image R, (fibers Q).card := Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ seeds.image R, 81187 := Finset.sum_le_sum (fun Q _ =>
      fixed_quotient_fiber_le seeds selected R d₀ (A 0 * d) (A 1 * d) C₁ Q
        131071 81186 hd₀ hselected hrel hpencil)
    _ = (seeds.image R).card * 81187 := by simp
    _ ≤ 9205603846958087 := Nat.mul_le_mul_right 81187 hlist

end

end ProximityPrize.SubmissionLower.Koala6844Inactive

