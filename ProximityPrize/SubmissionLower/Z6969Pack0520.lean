import ProximityPrize.SubmissionLower.Z6969Pack0096
import ProximityPrize.SubmissionLower.Z6969Pack0427
import ProximityPrize.SubmissionLower.R6966ProofNativeSeedDegree
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ProximityPrize.SubmissionLower.Fast070

set_option Elab.async false

-- Source: Research6969.JointProjection
section Z6969Source0532
set_option autoImplicit true
namespace Research6969.JointProjection
noncomputable section
open Finset Polynomial
open K1_14 (Equation Seeds)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)
open Research6966
open scoped Classical

/-- An empty collection contributes the unit ordinate to both the degree
sum and the marked-word invoice. -/
def Product (S:Finset Surface) (f:Equation):Prop:=ProjectedProduct S f ∨ S=∅ ∧ f=1

theorem exists_product (S:Finset Surface) (geo:∀q∈S, Parent q):∃ f,Product S f:=by
  by_cases live:S.Nonempty
  · obtain ⟨f,p⟩:=K1_14_3_7.proof S live geo
    exact ⟨f,Or.inl p⟩
  · exact ⟨1,Or.inr ⟨not_nonempty_iff_eq_empty.mp live,rfl⟩⟩

theorem Product.primitive {S f} (a:Product S f):f.IsPrimitive:=by
  rcases a with a|⟨_,rfl⟩
  · exact a.primitive
  · simp

theorem Product.separable {S f} (a:Product S f):(f.map (algebraMap Seeds SeedField)).Separable:=by
  rcases a with a|⟨_,rfl⟩
  · exact a.separable
  · simp

theorem Product.vanishes {S f} (a:Product S f) {q} (m:q∈S):C f∈q.asIdeal:=by
  rcases a with a|⟨rfl,_⟩
  · exact a.vanishes q m
  · simp at m

theorem Product.divides {S f} (a:Product S f) {D:Equation} (vanish:∀q∈S,C D∈q.asIdeal) : f∣D:=by
  rcases a with a|⟨_,rfl⟩
  · exact NativeOrdinateMass.divides_of_member a vanish
  · exact one_dvd _

theorem exclusive {A B f g h} (a:Product A f) (b:Product B g) (c:Product (A∪B) h) :
    ∃e:Equation,h=f*e ∧ e∣g ∧ e≠0 ∧ f.natDegree+e.natDegree=h.natDegree ∧
      (e.map (algebraMap Seeds SeedField)).Separable := by
  obtain ⟨e,eq⟩:=a.divides (fun q hq=>c.vanishes (mem_union_left B hq))
  have dvd:h∣f*g:=c.divides (by
    intro q hq
    rw [map_mul]
    rcases mem_union.mp hq with left|right
    · exact q.asIdeal.mul_mem_right _ (a.vanishes left)
    · exact q.asIdeal.mul_mem_left _ (b.vanishes right))
  obtain ⟨x,hx⟩:=dvd
  rw [eq,mul_assoc] at hx
  have ne:e≠0:=right_ne_zero_of_mul (eq ▸ c.primitive.ne_zero)
  have sp:=c.separable
  rw [eq,Polynomial.map_mul] at sp
  refine ⟨e,eq,⟨_,mul_left_cancel₀ a.primitive.ne_zero hx⟩,ne,?_,sp.of_mul_right⟩
  rw [eq,natDegree_mul a.primitive.ne_zero ne]

theorem remainder {f g:Equation} {S} (b:Product S g) (dvd:f∣g):
    f.IsPrimitive ∧ K1_14_4.seedDegree f≤K1_14_4.seedDegree g := by
  obtain ⟨q,eq⟩:=dvd
  have ne:f*q≠0:=eq ▸ b.primitive.ne_zero
  refine ⟨Polynomial.isPrimitive_of_dvd b.primitive ⟨q,eq⟩,?_⟩
  rw [eq,K1_14_4.seedDegree_mul (left_ne_zero_of_mul ne) (right_ne_zero_of_mul ne)]
  omega

theorem measures {S f} (project:Product S f) (sources:Finset (Ideal Ambient))
    (active:∀J∈sources,Active J) (origin:∀q∈S,∃J∈sources,q.asIdeal=J.comap toJet) :
    f.natDegree≤mass sources 0 ∧ K1_14_4.seedDegree f≤mass sources 1 := by
  rcases project with project|⟨rfl,rfl⟩
  · exact ⟨NativeOrdinateMass.projected_degree project sources active origin,
      (K1_14_4.seedDegree_le_iff ..).mpr (NativeSeedDegree.projected_seed project sources active origin)⟩
  · simp [K1_14_4.seedDegree]

theorem credit {S f} (project:Product S f) (sources:Finset (Ideal Ambient))
    (active:∀J∈sources,Active J) (origin:∀q∈S,∃J∈sources,q.asIdeal=J.comap toJet)
    (weights:Fin 4→ℕ) {e v:ℕ} (deg:e≤f.natDegree) (seed:v≤K1_14_4.seedDegree f) :
    weights 0*e+(weights 1+weights 2)*v≤∑k,weights k*mass sources k := by
  obtain ⟨d,s⟩:=measures project sources active origin
  have m1:=seed.trans s
  have m2:=m1.trans (MixedSectionCredit.mass_le sources active)
  have d0:=Nat.mul_le_mul_left (weights 0) (deg.trans d)
  have d1:=Nat.mul_le_mul_left (weights 1) m1
  have d2:=Nat.mul_le_mul_left (weights 2) m2
  rw [Nat.add_mul]
  simp only [Fin.sum_univ_succ]
  change _ ≤ weights 0*mass sources 0+(weights 1*mass sources 1+
    (weights 2*mass sources 2+(weights 3*mass sources 3+0)))
  omega

end
end Research6969.JointProjection
end Z6969Source0532

-- Source: Research6969.AdaptiveIncidence
section Z6969Source0533
set_option autoImplicit true
namespace Research6969.AdaptiveIncidence
noncomputable section
open Finset MvPolynomial
open scoped BigOperators Classical

variable {F σ ι : Type*} [Field F] [Finite σ]

/-- Node tests may be rebuilt on each subset of words. The test fee is
measured per surviving agreement node after shortening at that subset. -/
def Tests (W:Finset (σ→F)) (R:ℚ) : Prop :=
  ∀ T:Finset (σ→F), T⊆W → 1<T.card →
    ∃ (nodes:Finset ι) (required b:ℕ) (row:ι→MvPolynomial σ F),
      0<required ∧ (nodes.card:ℚ)*b≤R*required ∧
      (∀ i∈nodes, (row i).totalDegree≤b ∧ ∃ x∈T, aeval x (row i)≠0) ∧
      ∀ x∈T, required≤(nodes.filter (fun i=>aeval x (row i)=0)).card

/-- Each proper cut spends one factor of R. This holds at every dimension
and includes the components on which the seed coordinates are constant. -/
theorem prime_count (W : Finset (σ→F)) {R:ℚ} (one:1≤R) (tests:Tests (ι:=ι) W R)
    (P:Ideal (MvPolynomial σ F)) [P.IsPrime] (T:Finset (σ→F)) (sub:T⊆W)
    (on:∀ x∈T,x∈zeroLocus F P) :
    (T.card:ℚ)≤affineDegree P*R^(affineHilbertPolynomial P).natDegree := by
  classical
  have nonneg : 0≤R:=zero_le_one.trans one
  generalize dim : (affineHilbertPolynomial P).natDegree = d
  induction d using Nat.strong_induction_on generalizing P T with
  | ind d ih =>
    rcases T.eq_empty_or_nonempty with rfl|⟨x₀,hx₀⟩
    · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg nonneg d)
    by_cases small : T.card≤1
    · calc (T.card:ℚ)≤1 := by exact_mod_cast small
        _ ≤ affineDegree P * R^d := by
          simpa using mul_le_mul (K1_11.one_le_degree_of_point P x₀ (on x₀ hx₀))
            (one_le_pow₀ one (n:=d)) (by positivity) (affineDegree_nonneg P)
    cases d with
    | zero =>
      have bound:=finite_zeroLocus_and_ncard_le_affineDegree (K:=F) P dim
      have size:=Set.ncard_le_ncard (show (T:Set (σ→F))⊆_ from fun _ hx=>on _ hx) bound.1
      rw [Set.ncard_coe_finset] at size
      simpa using (show (T.card:ℚ)≤_ by exact_mod_cast size).trans bound.2
    | succ d =>
      obtain ⟨nodes,h,b,rows,hpos,ratio,source,enough⟩:=tests T sub (by omega)
      let hit (i:ι):=T.filter (fun x=>aeval x (rows i)=0)
      have per (i:ι) (hi:i∈nodes) : ((hit i).card:ℚ)≤b*affineDegree P*R^d := by
        obtain ⟨bound,x,hx,miss⟩:=source i hi
        have proper : rows i ∉ P := fun hmem=>miss (on x hx _ hmem)
        have size : ((T:Set (σ→F))∩{x|aeval x (rows i)=0}).ncard=(hit i).card := by
          rw [← Set.ncard_coe_finset,Finset.coe_filter]
          rfl
        rw [← size]
        apply ncard_inter_cut_le_of_retained_le (1:MvPolynomial σ F) proper bound T
          (fun x hx=>⟨on x hx,by simp⟩) (pow_nonneg nonneg d)
        intro Q hQ
        have minimal := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        have : Q.IsPrime := minimal.isPrime
        have reduced := principalCut_natDegree_affineHilbertPolynomial_add_one proper minimal
        rw [K1_11.ncard_inter_filter]
        exact ih d (by omega) Q (T.filter (·∈zeroLocus F Q))
          (fun _ hx=>sub (mem_filter.mp hx).1) (fun _ hx=>(mem_filter.mp hx).2) (by omega)
      have tally : T.card*h ≤ ∑ i∈nodes,(hit i).card := by
        calc T.card*h = ∑ _x∈T,h := by simp
          _ ≤ ∑ x∈T,(nodes.filter (fun i=>aeval x (rows i)=0)).card := sum_le_sum enough
          _ = _ := by simp only [hit,card_filter];rw [sum_comm]
      have start : (T.card:ℚ)*h≤∑ i∈nodes,((hit i).card:ℚ) := by exact_mod_cast tally
      have step := start.trans (sum_le_sum per)
      simp only [sum_const,nsmul_eq_mul] at step
      have hcalc : (T.card:ℚ)*h ≤ (affineDegree P*R^(d+1))*h := calc
        _ ≤ (nodes.card:ℚ)*(b*affineDegree P*R^d) := step
        _ = ((nodes.card:ℚ)*b)*(affineDegree P*R^d) := by ring
        _ ≤ R*h*(affineDegree P*R^d) := mul_le_mul_of_nonneg_right ratio
          (mul_nonneg (affineDegree_nonneg _) (pow_nonneg nonneg _))
        _ = _ := by ring
      exact le_of_mul_le_mul_right hcalc (by exact_mod_cast hpos : (0:ℚ)<h)

end
end Research6969.AdaptiveIncidence
end Z6969Source0533
