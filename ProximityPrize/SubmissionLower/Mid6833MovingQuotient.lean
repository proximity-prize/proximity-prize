/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833CommonContent
import ProximityPrize.SubmissionLower.Koala6831Cramer
import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsNormalForm
import Mathlib.Tactic
namespace Frontier6969.Moving
open Polynomial
open scoped Polynomial
variable {K : Type*} [Field K]
noncomputable section

/-- If the same separated quotient occurs at two distinct seeds, elimination forces
the moving determinant to be divisible by the fixed denominator. -/
theorem repeat_divides (d a₀ a₁ c₀ c₁ P Q L : K[X]) (g h : K) (ne : g≠h)
    (hg : d*P+(c₀+C g*c₁)=(a₀+C g*a₁)*L)
    (hh : d*Q+(c₀+C h*c₁)=(a₀+C h*a₁)*L) : d ∣ a₀*c₁-a₁*c₀ := by
  have nz : g-h≠0 := sub_ne_zero.mpr ne
  have he : C (g-h)*(a₀*c₁-a₁*c₀)=d*((a₀+C g*a₁)*Q-(a₀+C h*a₁)*P) := by
    rw [map_sub]
    linear_combination (a₀+C h*a₁)*hg-(a₀+C g*a₁)*hh
  refine ⟨C ((g-h)⁻¹)*((a₀+C g*a₁)*Q-(a₀+C h*a₁)*P),?_⟩
  have z := congrArg ((C ((g-h)⁻¹)) * ·) he
  rw [←mul_assoc,←map_mul,inv_mul_cancel₀ nz,map_one,one_mul] at z
  rw [z];ring

theorem injective (S : Finset K) (d a₀ a₁ c₀ c₁ : K[X]) (P L : K → K[X])
    (obstruction : ¬ d ∣ a₀*c₁-a₁*c₀)
    (row : ∀ g∈S, d*P g+(c₀+C g*c₁)=(a₀+C g*a₁)*L g) :
    Function.Injective (fun g : ↥S => L g) := by
  intro g h eq
  by_contra ne
  have gh : (g:K)≠(h:K) := fun e => ne (Subtype.ext e)
  exact obstruction (repeat_divides d a₀ a₁ c₀ c₁ (P g) (P h) (L g) g h gh
    (row g g.property) (by change L g = L h at eq; rw [eq]; exact row h h.property))

theorem quotient_degree (d a₀ a₁ c₀ c₁ P L : K[X]) (g : K) (w m k : ℕ)
    (hn : a₀+C g*a₁≠0) (hd : d.natDegree+w≤m) (hc₀ : c₀.natDegree≤m)
    (hc₁ : c₁.natDegree≤m) (hp : P.natDegree≤w) (ha : k≤(a₀+C g*a₁).natDegree)
    (he : d*P+(c₀+C g*c₁)=(a₀+C g*a₁)*L) : L.natDegree≤m-k := by
  by_cases hl : L=0
  · simp [hl]
  have h := natDegree_add_le (d*P) (c₀+C g*c₁)
  have h₁ := (natDegree_mul_le (p := d) (q := P)).trans (Nat.add_le_add_left hp _)
  have h₂ := (natDegree_add_le c₀ (C g*c₁)).trans (max_le hc₀ ((natDegree_C_mul_le _ _).trans hc₁))
  rw [he,natDegree_mul hn hl] at h
  omega


open ProximityPrize.SubmissionLower
open Koala6831Separation (pairDegree NormalForm Seeds)
open Koala6831Comparison (SymbolicRow primitiveSelected)
open Koala6831Moving
variable {I : Type*}

theorem leading_regular (E : Finset K) (A : Fin 2 → K[X]) (cp : IsCoprime (A 0) (A 1)) :
    ∃ S ⊆ E, E.card ≤ S.card+1 ∧ ∀ g∈S,
      A 0+C g*A 1≠0 ∧ pairDegree A≤(A 0+C g*A 1).natDegree := by
  classical
  let k := pairDegree A
  let a := (A 0).coeff k
  let b := (A 1).coeff k
  have nz : a≠0 ∨ b≠0 := by
    by_contra! bz
    obtain ⟨i,hi⟩ := cp
    have both : A 0=0 ∧ A 1=0 := by
      by_cases le : (A 0).natDegree≤(A 1).natDegree
      · have h1 : A 1=0 := by simpa [b,k,pairDegree,max_eq_right le] using bz.2
        have eq : (A 0).natDegree=(A 1).natDegree := by rw [h1,natDegree_zero] at le ⊢;omega
        exact ⟨by simpa [a,k,pairDegree,←eq] using bz.1,h1⟩
      · have h0 : A 0=0 := by simpa [a,k,pairDegree,max_eq_left (le_of_not_ge le)] using bz.1
        rw [h0,natDegree_zero] at le
        omega
    obtain ⟨j,h⟩ := hi
    simp [both.1,both.2] at h
  let S := E.filter (fun g => a+g*b≠0)
  have unique : (E\S).card≤1 := by
    apply Finset.card_le_one.mpr
    intro g hg h hh
    have z (x) (hx : x∈E\S) : a+x*b=0 := by
      by_contra ne
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1,ne⟩)
    have zg := z g hg
    have zh := z h hh
    have nb : b≠0 := by intro h;rw [h,mul_zero,add_zero] at zg;exact nz.elim (· zg) (· h)
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (g-h)*b=0 by linear_combination zg-zh)).resolve_right nb
  have sub : S⊆E := Finset.filter_subset _ _
  have card := Finset.card_sdiff_add_card_eq_card sub
  refine ⟨S,sub,by omega,?_⟩
  intro g hg
  have ne := (Finset.mem_filter.mp hg).2
  have nea : (A 0+C g*A 1).coeff k≠0 := by simpa [a,b] using ne
  exact ⟨fun e => by rw [e,coeff_zero] at nea;exact nea rfl,le_natDegree_of_ne_zero nea⟩

/-- Inputs are the original normal form, its good-node equations and selected
polynomial identities. The degree estimate charges both moving denominators. -/
theorem normalized_embedding {q : SymbolicRow (Seeds K)} {w δ p : ℕ}
    (N : NormalForm q w δ) (σ : K →+* K) (hδ : δ<p)
    (nodes : Finset I) (x : I → K) (u v : I → K)
    (good : ∀ i∈nodes, q.atNode (MvPolynomial.C (x i)) (Koala6831SeparationFactors.affine 0 (u i) (v i))
      (Koala6831SeparationFactors.affine 1 (σ (u i)) (σ (v i)))=0)
    (E : Finset K) (P : K → K[X]) (hd : ∀ g∈E,(P g).natDegree≤w)
    (hz : ∀ g∈E, primitiveSelected σ p q P g=0)
    (hpow : ∀ g, σ g=g^p) (prim : Koala6831Comparison.IsPrimitiveRow q)
    (obstruction : (¬ N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0) ∨ (¬ N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0) ∨ ¬ IsCoprime N.d₀ N.d₁) :
    ∃ S⊆E, E.card≤S.card+(nodes.card+2+(p+1)*δ) ∧
      ∃ T : ↥S ↪ K[X], ∃ word : I → K, ∀ g : S,
        (T g).natDegree≤w+δ-pairDegree N.B-pairDegree N.A ∧
        ∀ i∈nodes, (P g).eval (x i)=u i+(g:K)*v i → (T g).eval (x i)=word i := by
  classical
  obtain ⟨S₀,sub,hcard,word,L,_,props⟩ :=
    normalForm_exists_retained_normalized_words N σ p hδ nodes x u v good E P hd hz
  obtain ⟨S,sub',hcard',lead⟩ := leading_regular S₀ N.A N.A_coprime
  have H (g) (hg:g∈S) := (props g (sub' hg)).2.1
  have inj : Function.Injective (fun g : ↥S => L g) := by
    have rightRow (g : K) (hg:g∈S) :
        N.d₁*(P g).map σ+(-N.D 0+C (σ g)*(-N.D 1))=(N.B 0+C (σ g)*N.B 1)*L g := by
      have z := normalForm_specialized_compatibility N σ p P g (hz g (sub (sub' hg)))
      have hleft := H g hg
      dsimp only [affineDenominator] at z hleft
      rw [←hpow] at z
      apply mul_left_cancel₀ ((lead g hg).1)
      linear_combination z+(N.B 0+C (σ g)*N.B 1)*hleft
    intro g h eq
    by_contra ne
    have gh : σ (g:K)≠σ (h:K) := fun e => ne (Subtype.ext (σ.injective e))
    change L g=L h at eq
    rcases obstruction with left | right | content
    · exact ne (injective S N.d₀ (N.A 0) (N.A 1) (N.C 0) (N.C 1) P L left H eq)
    · have rightD := repeat_divides N.d₁ (N.B 0) (N.B 1) (-N.D 0) (-N.D 1)
        ((P g).map σ) ((P h).map σ) (L g) (σ (g:K)) (σ (h:K)) gh (rightRow g g.property)
        (by change L g=L h at eq;rw [eq];exact rightRow h h.property)
      obtain ⟨J,hJ⟩ := rightD
      exact right ⟨-J,by linear_combination -hJ⟩
    · have gne : (g:K)≠(h:K) := fun e => ne (Subtype.ext e)
      have left := Frontier6969.Content.repeated_coeffs N.d₀ (N.A 0) (N.A 1) (N.C 0) (N.C 1)
        (P g) (P h) (L g) g h gne (H g g.property) (by rw [eq];exact H h h.property)
      have right := Frontier6969.Content.repeated_coeffs N.d₁ (N.B 0) (N.B 1) (-N.D 0) (-N.D 1)
        ((P g).map σ) ((P h).map σ) (L g) (σ (g:K)) (σ (h:K)) gh (rightRow g g.property)
        (by rw [eq];exact rightRow h h.property)
      exact content (Frontier6969.Content.coprime_of_repetition N prim (L g) left (by simpa using right))
  refine ⟨S,sub'.trans sub,by omega,⟨_,inj⟩,word,?_⟩
  intro g
  have a := N.first_degree
  have b := N.left_degree
  have c0 : (N.C 0).natDegree≤pairDegree N.C := le_max_left _ _
  have c1 : (N.C 1).natDegree≤pairDegree N.C := le_max_right _ _
  exact ⟨quotient_degree N.d₀ (N.A 0) (N.A 1) (N.C 0) (N.C 1) (P g) (L g) g w
    (w+δ-pairDegree N.B) (pairDegree N.A) (lead g g.property).1
    (by omega) (by omega) (by omega) (hd g (sub (sub' g.property))) (lead g g.property).2 (H g g.property),
    (props g (sub' g.property)).2.2⟩
#print axioms normalized_embedding
#print axioms repeat_divides
#print axioms injective
#print axioms quotient_degree
end
end Frontier6969.Moving
