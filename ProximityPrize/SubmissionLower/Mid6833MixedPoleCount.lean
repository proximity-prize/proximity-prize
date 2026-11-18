/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833CrossRatioPoles
import ProximityPrize.SubmissionLower.Mid6833FrobeniusModule
import ProximityPrize.SubmissionLower.Mid6833NormalizedTwist
import ProximityPrize.SubmissionLower.Mid6833GenuineTypes
namespace ProximityPrize.SubmissionLower.Genuine6969
open Polynomial Finset ProximityPrize.Benchmark Frontier6969.GenuineMoving
open Koala6831Comparison Koala6831Separation Koala6831Moving
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open Koala6831BenchmarkField (prime)
open K6969Global
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

private theorem different_at_pole {K L : Type*} [Field K] [Field L] (ι : K →+* L)
    (α : L) (D : K[X]) (A B : Fin 2 → K[X]) (s r : K) (ne : s≠r) (Ps Pr Ts Tr : K[X])
    (pole : D.eval₂ ι α=0) (det : (A 0*B 1-A 1*B 0).eval₂ ι α≠0)
    (rs : D*Ps+affineDenominator (B 0) (B 1) s=affineDenominator (A 0) (A 1) s*Ts)
    (rr : D*Pr+affineDenominator (B 0) (B 1) r=affineDenominator (A 0) (A 1) r*Tr) :
    Ts.eval₂ ι α≠Tr.eval₂ ι α := by
  intro same
  have es := congrArg (Polynomial.eval₂ ι α) rs
  have er := congrArg (Polynomial.eval₂ ι α) rr
  simp only [affineDenominator,eval₂_add,eval₂_mul,eval₂_C,pole,zero_mul,zero_add,same] at es er
  apply (mul_ne_zero (sub_ne_zero.mpr (ι.injective.ne ne)) det)
  simp only [eval₂_sub,eval₂_mul]
  linear_combination ((A 0).eval₂ ι α+ι r*(A 1).eval₂ ι α)*es -
    ((A 0).eval₂ ι α+ι s*(A 1).eval₂ ι α)*er

private theorem retained_mixed {K I J : Type} [Field K] [Algebra KoalaBear.Field K]
    [Fintype K] [Fintype I] [Fintype J]
    (x : I ↪ K) (σ : K →+* K) (xf : ∀i, σ (x i)=x i) (power : ∀t,σ t=t^prime)
    (sizeK : Fintype.card K=prime^6) (U : Received K I) (E : Finset K)
    (P : SelectionMap K) (q : SymbolicRow (Seeds K)) (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (short : primitiveExcess 131071 q≤12136)
    (L Ω : J → Type) [∀j,Field (L j)] [∀j,Field (Ω j)] [∀j,Fintype (L j)]
    (ι : ∀j,K→+*Ω j) (l : ∀j,L j→+*Ω j) (b : ∀j, KoalaBear.Field→+*L j)
    (comm : ∀j,(ι j).comp (algebraMap KoalaBear.Field K)=(l j).comp (b j))
    (α : ∀j,L j) (m : J → ℕ) (sizes : ∀j,Fintype.card (L j)=prime^(m j))
    (one : Nat.gcd 6 (univ.gcd m)=1)
    (poles : ∀j,N.d₀.eval₂ (ι j) (l j (α j))=0)
    (visible : ∀j,(N.A 0*N.C 1-N.A 1*N.C 0).eval₂ (ι j) (l j (α j))≠0) :
    E.card≤prime+1+(Fintype.card I+1+(prime+1)*primitiveExcess 131071 q) := by
  classical
  obtain ⟨S,_,cut,T,_,fit⟩ := retained_solutions x σ xf U E P q h N short
  suffices S.card≤prime+1 by omega
  by_cases small : S.card≤1
  · omega
  obtain ⟨r,hr,s,hs,rs⟩ := Finset.one_lt_card.mp (by omega : 1<S.card)
  have has : Nonempty J := by
    by_contra no
    let _ : IsEmpty J := not_nonempty_iff.mp no
    simp at one
  let j₀ := Classical.choice has
  have distinct (j:J) : (T s).eval₂ (ι j) (l j (α j)) ≠ (T r).eval₂ (ι j) (l j (α j)) :=
    different_at_pole _ _ N.d₀ N.A N.C s r rs.symm (P s) (P r) (T s) (T r)
      (poles j) (visible j) (fit s hs).2.1 (fit r hr).2.1
  have varies : T s≠T r := fun e => distinct j₀ (congrArg _ e)
  have na : N.A 0≠0 ∨ N.A 1≠0 := by
    by_contra! z
    have v := visible j₀
    simp [z] at v
  obtain ⟨k,nk⟩ : ∃k,N.A k≠0 := na.elim (fun h=>⟨0,h⟩) (fun h=>⟨1,h⟩)
  let a := N.d₁*(N.A k).map σ
  let d := N.d₀.map σ*N.B k
  obtain ⟨H,Q,_,_,_,_,factor,_⟩ := KoalaFrontier.normalized_affine_family σ a d
    (fun g:S => T g) ⟨r,hr⟩ (fun _ : Unit => (0:K)) (fun _ => (0:K)) (fun _ => map_zero σ)
    (mul_ne_zero N.d₁_ne (Polynomial.map_ne_zero nk)) (offset σ N k)
    (fun g => by linear_combination (fit _ g.property).2.2.2 k) ⟨⟨s,hs⟩,varies⟩
  let Q' (g:K) : K[X] := if z:g∈S then Q ⟨g,z⟩ else 0
  have factor' (g:K) (hg:g∈S) : T g-T r=H*Q' g := by
    simpa only [Q',dif_pos hg] using (factor (⟨g,hg⟩:S)).2
  have sf : (FiniteField.frobeniusAlgHom KoalaBear.Field K).toRingHom=σ := by
    ext z
    change (FiniteField.frobeniusAlgHom KoalaBear.Field K) z=σ z
    rw [FiniteField.coe_frobeniusAlgHom, power,show Fintype.card KoalaBear.Field=prime from ZMod.card _]
  have fixedQ (g:K) (hg:g∈S) : (Q' g).map (FiniteField.frobeniusAlgHom KoalaBear.Field K).toRingHom=Q' g := by
    rw [sf]; simpa only [Q',dif_pos hg] using (factor (⟨g,hg⟩:S)).1
  have residues (g:K) (hg:g∈S) :
      N.d₀∣(N.A 0+C g*N.A 1)*(T r+H*Q' g)-(N.C 0+C g*N.C 1) := by
    refine ⟨P g,?_⟩
    rw [←factor' g hg]
    have eq := (fit g hg).2.1
    simp only [affineDenominator] at eq
    linear_combination -eq
  have vis (j:J) : (H*(N.A 0*N.C 1-N.A 1*N.C 0)).eval₂ (ι j) (l j (α j)) ≠ 0 := by
    rw [eval₂_mul]
    apply mul_ne_zero _ (visible j)
    intro hz
    have ev := congrArg (Polynomial.eval₂ (ι j) (l j (α j))) (factor' s hs)
    rw [eval₂_sub,eval₂_mul,hz,zero_mul] at ev
    exact distinct j (sub_eq_zero.mp ev)
  apply _root_.Genuine.CrossRatio.charts_count S prime 6 m (by decide) sizeK L Ω ι l _ sizes one
  exact fun j => _root_.Genuine.CrossRatio.chartFromFixed S (b j) (ι j) (l j) (comm j)
    (α j) N.d₀ (N.A 0) (N.A 1) (N.C 0) (N.C 1) (T r) H Q' (poles j) fixedQ residues (vis j)

/-- Mixed pole-field price for the actual retained KoalaBear comparison object.
No denominator nonvanishing for an unknown generator is assumed. -/
theorem mixed_pole_price {J : Type} [Fintype J] (U : Received F IRSProfile.Index) (E : Finset F)
    (P : SelectionMap F) (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (short : primitiveExcess 131071 q≤12136)
    (L Ω : J → Type) [∀j,Field (L j)] [∀j,Field (Ω j)] [∀j,Fintype (L j)]
    (ι : ∀j,F→+*Ω j) (l : ∀j,L j→+*Ω j) (b : ∀j,KoalaBear.Field→+*L j)
    (comm : ∀j,(ι j).comp (algebraMap KoalaBear.Field F)=(l j).comp (b j))
    (α : ∀j,L j) (m : J → ℕ) (sizes : ∀j,Fintype.card (L j)=prime^(m j))
    (one : Nat.gcd 6 (univ.gcd m)=1)
    (poles : ∀j,N.d₀.eval₂ (ι j) (l j (α j))=0)
    (visible : ∀j,(N.A 0*N.C 1-N.A 1*N.C 0).eval₂ (ι j) (l j (α j))≠0) :
    E.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget := by
  have hc := retained_mixed Dmn σ Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply KoalaBear.card_ext6 U E P q h N short L Ω ι l b comm α m sizes one poles visible
  rw [IRSProfile.card_index] at hc
  unfold prime budget at *
  omega

end
#print axioms mixed_pole_price
end ProximityPrize.SubmissionLower.Genuine6969
