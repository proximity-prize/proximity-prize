/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Tactic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.FieldTheory.Finite.Basic
namespace Genuine.CrossRatio
open Polynomial Finset Function
open scoped Polynomial Classical BigOperators
noncomputable section
variable {K E L J : Type*} [Field K] [Field E] [Field L]

def norm (a b c x : K) : K := (x-a)*(b-c)/((x-c)*(b-a))

private theorem map_norm (f : K →+* E) (a b c x : K) :
    f (norm a b c x) = norm (f a) (f b) (f c) (f x) := by simp [norm]

private theorem inj_norm (a b c : K) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    {x y : K} (xc : x≠c) (yc : y≠c) (eq : norm a b c x=norm a b c y) : x=y := by
  unfold norm at eq
  have ba := sub_ne_zero.mpr ab.symm
  have h := (div_eq_div_iff (mul_ne_zero (sub_ne_zero.mpr xc) ba)
    (mul_ne_zero (sub_ne_zero.mpr yc) ba)).mp eq
  have prod : (x-y)*((a-c)*(b-c)*(b-a))=0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ac) (sub_ne_zero.mpr bc)) ba))

/-- At a visible pole the residue equation is a fractional linear change
of the challenge, taking values in a potentially different finite field. -/
structure Chart (S : Finset K) (ι : K →+* E) (l : L →+* E) where
  a : E
  b : E
  c : E
  d : E
  visible : d*a-c*b≠0
  value : K → L
  relation : ∀g∈S, (a+b*ι g)*l (value g)=c+d*ι g

private theorem denominator {S : Finset K} {ι : K →+* E} {l : L →+* E}
    (C : Chart S ι l) (x : K) (hx : x∈S) : C.a+C.b*ι x≠0 := by
  intro zero
  have rhs := C.relation x hx
  rw [zero,zero_mul] at rhs
  apply C.visible
  linear_combination C.d * zero + C.b * rhs

private theorem diff {S : Finset K} {ι : K →+* E} {l : L →+* E}
    (C : Chart S ι l) {x y : K} (hx : x∈S) (hy : y∈S) :
    l (C.value x)-l (C.value y)=
      ((C.d*C.a-C.c*C.b)*(ι x-ι y))/((C.a+C.b*ι x)*(C.a+C.b*ι y)) := by
  apply (eq_div_iff (mul_ne_zero (denominator C x hx) (denominator C y hy))).mpr
  linear_combination (C.a+C.b*ι y)*C.relation x hx - (C.a+C.b*ι x)*C.relation y hy

theorem transport {S : Finset K} {ι : K →+* E} {l : L →+* E}
    (C : Chart S ι l) {a b c x : K} (ha : a∈S) (hb : b∈S) (hc : c∈S) (hx : x∈S)
    (ab : a≠b) (xc : x≠c) :
    l (norm (C.value a) (C.value b) (C.value c) (C.value x))=ι (norm a b c x) := by
  rw [map_norm,map_norm]; unfold norm
  rw [diff C hx ha,diff C hb hc,diff C hx hc,diff C hb ha]
  have h1 := denominator C a ha
  have h2 := denominator C b hb
  have h3 := denominator C c hc
  have h4 := denominator C x hx
  have h5 := sub_ne_zero.mpr (ι.injective.ne ab.symm)
  have h6 := sub_ne_zero.mpr (ι.injective.ne xc)
  let Δ := C.d*C.a-C.c*C.b
  have hn : Δ≠0 := C.visible
  change (Δ*_/_)*(Δ*_/_)/((Δ*_/_)*(Δ*_/_))=_
  field_simp
  have nonzeroA : C.a+ι a*C.b≠0 := by simpa only [mul_comm] using h1
  have nonzeroX : C.a+ι x*C.b≠0 := by simpa only [mul_comm] using h4
  field_simp [nonzeroA,nonzeroX]

theorem period_of_chart [Fintype L] {S : Finset K} {ι : K →+* E} {l : L →+* E}
    (C : Chart S ι l) {p m : ℕ} (size : Fintype.card L=p^m)
    {a b c x : K} (ha : a∈S) (hb : b∈S) (hc : c∈S) (hx : x∈S)
    (ab : a≠b) (xc : x≠c) :
    IsPeriodicPt (fun z : K => z^p) m (norm a b c x) := by
  change ((fun z : K => z^p)^[m]) _=_
  rw [pow_iterate]
  apply ι.injective
  rw [map_pow,←transport C ha hb hc hx ab xc,←map_pow,←size,FiniteField.pow_card]

/-- Independent pole fields constrain the same normalized cross-ratio. The
intersection degree is the gcd of the challenge degree and all pole degrees. -/
theorem count_gcd [Fintype J] (S : Finset K) (p e : ℕ) (m : J → ℕ)
    (q : 1<p) (e6 : ∀x:K, IsPeriodicPt (fun z:K => z^p) e x)
    (vis : ∀a∈S, ∀b∈S, ∀c∈S, ∀x∈S, a≠b → x≠c →
      ∀j, IsPeriodicPt (fun z:K => z^p) (m j) (norm a b c x))
    (one : Nat.gcd e (univ.gcd m)=1) : S.card≤p+1 := by
  classical
  by_cases small : S.card≤2
  · omega
  obtain ⟨a,ha,b,hb,c,hc,ab,ac,bc⟩ := two_lt_card.mp (by omega : 2<S.card)
  let N := norm a b c
  let T := S.erase c
  have rr (x:K) (hx:x∈T) : (N x)^p=N x := by
    have h := mem_erase.mp hx
    have a1 := (e6 (N x)).minimalPeriod_dvd
    have a2 : minimalPeriod (fun z:K => z^p) (N x) ∣ univ.gcd m := by
      apply Finset.dvd_gcd_iff.mpr
      intro j _
      exact (vis a ha b hb c hc x h.2 ab h.1 j).minimalPeriod_dvd
    have divided := Nat.dvd_gcd a1 a2
    rw [one] at divided
    exact isPeriodicPt_iff_minimalPeriod_dvd.mpr divided
  let P : K[X] := X^p-X
  have dP : P.natDegree=p := (natDegree_sub_eq_left_of_natDegree_lt (by simpa using q :
    (X:K[X]).natDegree < (X^p:K[X]).natDegree)).trans (natDegree_X_pow _)
  have nz : P≠0 := fun h => by rw [h,natDegree_zero] at dP; omega
  have inRoots : T.image N ⊆ P.roots.toFinset := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hr
    apply Multiset.mem_toFinset.mpr ((mem_roots nz).mpr ?_)
    simp [Polynomial.IsRoot,P,rr x hx]
  have inj : Set.InjOn N (T : Set K) := fun x hx y hy h => inj_norm a b c ab ac bc
    (mem_erase.mp hx).1 (mem_erase.mp hy).1 h
  have bound := (card_le_card inRoots).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' P))
  rw [card_image_of_injOn inj,dP] at bound
  have erase := card_erase_add_one hc
  change T.card+1=S.card at erase
  omega

/-- A common algebraic closure is optional. Each pole can be checked in
its own overfield using a separate pair of field embeddings. -/
theorem charts_count [Fintype K] [Fintype J] (S : Finset K) (p e : ℕ) (m : J → ℕ)
    (q : 1<p) (sizeK : Fintype.card K=p^e)
    (L E : J → Type*) [∀j, Field (L j)] [∀j, Field (E j)] [∀j, Fintype (L j)]
    (ι : ∀j, K →+* E j) (l : ∀j, L j →+* E j) (charts : ∀j, Chart S (ι j) (l j))
    (sizes : ∀j, Fintype.card (L j)=p^(m j))
    (one : Nat.gcd e (univ.gcd m)=1) : S.card≤p+1 := by
  apply count_gcd S p e m q _ _ one
  · intro x
    change ((fun z:K => z^p)^[e]) x=x
    rw [pow_iterate]
    simpa only [sizeK] using FiniteField.pow_card x
  · intro a ha b hb c hc x hx ab xc j
    exact period_of_chart (charts j) (sizes j) ha hb hc hx ab xc

end
#print axioms transport
#print axioms period_of_chart
#print axioms count_gcd
#print axioms charts_count
end Genuine.CrossRatio
