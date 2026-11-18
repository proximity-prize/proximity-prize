/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833InfinityBounds
import ProximityPrize.SubmissionLower.Mid6833FixedPoles
namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Moving (affineDenominator)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open K6969Global (RetainedComparison)
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open scoped Polynomial Classical
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
variable {K I : Type} [Field K] [Fintype I]

private theorem top_identity {q : SymbolicRow (Seeds K)} {w δ : ℕ} (N : NormalForm q w δ)
    (g h : K) (Pg Ph Tg Th : K[X]) (dg : Pg.natDegree≤w) (dh : Ph.natDegree≤w)
    (rg : N.d₀*Pg+affineDenominator (N.C 0) (N.C 1) g=affineDenominator (N.A 0) (N.A 1) g*Tg)
    (rh : N.d₀*Ph+affineDenominator (N.C 0) (N.C 1) h=affineDenominator (N.A 0) (N.A 1) h*Th)
    (high : w+N.d₀.natDegree+pairDegree N.A < (N.A 0*N.C 1-N.A 1*N.C 0).natDegree)
    (same : g=h → Tg=Th) :
    (affineDenominator (N.A 0) (N.A 1) g).leadingCoeff *
    (affineDenominator (N.A 0) (N.A 1) h).leadingCoeff * (Tg-Th).leadingCoeff =
      (g-h)*(N.A 0*N.C 1-N.A 1*N.C 0).leadingCoeff := by
  by_cases eq : g=h
  · simp [eq,same eq]
  let A := affineDenominator (N.A 0) (N.A 1)
  let M := N.A 0*N.C 1-N.A 1*N.C 0
  let L := N.d₀*(A h*Pg-A g*Ph)
  have cross : A g * A h * (Tg-Th) = L+C (g-h)*M := by
    dsimp [A,affineDenominator,L,M] at rg rh ⊢
    rw [map_sub]
    linear_combination -(N.A 0+C h*N.A 1)*rg+(N.A 0+C g*N.A 1)*rh
  have dega (t : K) : (A t).natDegree ≤ pairDegree N.A :=
    (natDegree_add_le _ _).trans (max_le (le_max_left _ _) ((natDegree_C_mul_le _ _).trans (le_max_right _ _)))
  have dl : L.natDegree ≤ w+N.d₀.natDegree+pairDegree N.A := by
    have e1 := natDegree_sub_le (A h*Pg) (A g*Ph)
    have e2 := @natDegree_mul_le _ _ (A h) Pg
    have e3 := @natDegree_mul_le _ _ (A g) Ph
    have e4 := @natDegree_mul_le _ _ N.d₀ (A h*Pg-A g*Ph)
    have a := dega h
    have b := dega g
    dsimp only [L]
    omega
  have dr : L.degree < (C (g-h)*M).degree := by
    apply degree_lt_degree (p:=L)
    rw [natDegree_C_mul (sub_ne_zero.mpr eq)]
    exact dl.trans_lt high
  have leads := congrArg Polynomial.leadingCoeff cross
  simpa only [leadingCoeff_add_of_degree_lt dr,leadingCoeff_mul,leadingCoeff_C,A,M] using leads

theorem infinity_large (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (hσ : ∀ a, σ a = a^prime)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (short : primitiveExcess 131071 q ≤ 12136)
    (high : 131071+N.d₀.natDegree+pairDegree N.A < (N.A 0*N.C 1-N.A 1*N.C 0).natDegree) :
    E.card ≤ prime + (Fintype.card I+2+(prime+1)*primitiveExcess 131071 q) := by
  classical
  obtain ⟨S,sub,card,T,v,fit⟩ := retained_solutions x σ fixed U E P q h N short
  obtain ⟨G,inc,gcard,active⟩ := _root_.Frontier6969.Moving.leading_regular S N.A N.A_coprime
  suffices G.card≤prime by omega
  by_cases empty : G=∅
  · simp [empty]
  obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  let M := N.A 0*N.C 1-N.A 1*N.C 0
  let f : G → K := fun g => (T g-T r).leadingCoeff
  let u := (N.A 0).coeff (pairDegree N.A)
  let z := (N.A 1).coeff (pairDegree N.A)
  let A := affineDenominator (N.A 0) (N.A 1)
  have lc (g) (hg:g∈G) : (A g).leadingCoeff = u+g*z := by
    have deg : (A g).natDegree=pairDegree N.A :=
      Nat.le_antisymm ((natDegree_add_le _ _).trans (max_le (le_max_left _ _)
        ((natDegree_C_mul_le _ _).trans (le_max_right _ _)))) (active g hg).2
    rw [←coeff_natDegree,deg]
    simp [A,affineDenominator,u,z]
  have ur : u+r*z≠0 := by rw [←lc r hr];exact leadingCoeff_ne_zero.mpr (active r hr).1
  have mn : M.leadingCoeff≠0 := by
    apply leadingCoeff_ne_zero.mpr
    intro m
    change _ < M.natDegree at high
    simp [m] at high
  have eq (g : G) : (u+(g:K)*z)*(u+r*z)*f g=((g:K)-r)*M.leadingCoeff := by
    have e := top_identity N g r (P g) (P r) (T g) (T r) (h.selection.degree_le _ (sub (inc g.property)))
      (h.selection.degree_le _ (sub (inc hr))) (fit _ (inc g.property)).2.1 (fit _ (inc hr)).2.1 high
      (fun he => congrArg T he)
    change (A g).leadingCoeff*(A r).leadingCoeff*f g=_ at e
    rwa [lc _ g.property,lc _ hr] at e
  have inj : Function.Injective f := by
    intro g k same
    apply Subtype.ext
    apply sub_eq_zero.mp
    have eg := eq g
    rw [same] at eg
    have e : ((g:K)-(k:K))*(u+r*z)*M.leadingCoeff=0 := by
      linear_combination (u+(g:K)*z)*eq k-(u+(k:K)*z)*eg
    exact (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_right mn)).resolve_right ur
  have na : N.A 0≠0 ∨ N.A 1≠0 := by
    by_contra! zz
    simp [M,zz] at mn
  obtain ⟨j,jn⟩ : ∃ j, N.A j≠0 := na.elim (fun h=>⟨0,h⟩) (fun h=>⟨1,h⟩)
  let l := (N.d₁*(N.A j).map σ).leadingCoeff
  let b := (N.d₀.map σ*N.B j).leadingCoeff
  have ln : l≠0 := leadingCoeff_ne_zero.mpr (mul_ne_zero N.d₁_ne (Polynomial.map_ne_zero jn))
  have leadEq (g : G) : l*(f g)^prime=b*f g := by
    have eq' := congrArg Polynomial.leadingCoeff (homogeneous_difference σ N
      (fit _ (inc g.property)).2.2.2 (fit _ (inc hr)).2.2.2 j)
    simpa only [leadingCoeff_mul,leadingCoeff_map,hσ,l,b,f] using eq'
  let Q : K[X] := C l*Polynomial.X^prime-C b*Polynomial.X
  have top : (C l*Polynomial.X^prime : K[X]).natDegree=prime := by rw [natDegree_C_mul ln]; simp
  have low : (C b*Polynomial.X : K[X]).natDegree < prime := by apply (natDegree_C_mul_le _ _).trans_lt; simpa using (by decide : 1<prime)
  have order : (C b*Polynomial.X : K[X]).natDegree < (C l*Polynomial.X^prime).natDegree := by
    rw [top]; exact low
  have deg : Q.natDegree=prime := (natDegree_sub_eq_left_of_natDegree_lt order).trans top
  have qnz : Q≠0 := by intro e; rw [e,natDegree_zero] at deg; exact (by decide : (0:ℕ)≠prime) deg
  let values := univ.image f
  have count : values.card≤prime := by
    rw [←deg]
    apply Polynomial.card_le_degree_of_subset_roots
    intro val hv
    obtain ⟨g,_,rfl⟩ := mem_image.mp hv
    apply (Polynomial.mem_roots qnz).mpr
    change Q.eval (f g)=0
    simp only [Q,eval_sub,eval_mul,eval_C,eval_pow,eval_X,leadEq,sub_self]
  simpa only [values,card_image_of_injective _ inj,card_univ,Fintype.card_coe] using count

#print axioms infinity_large
end
end Frontier6969.GenuineMoving
