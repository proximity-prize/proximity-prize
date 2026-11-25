import ProximityPrize.SubmissionLower.R6966ProofPadePowers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option Elab.async false

set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 12
namespace Research6966.PadeRank
open Polynomial Finset Module
open Pade (Row totalJet totalJet_le totalJet_mul)
open scoped Polynomial
noncomputable section

/-- Bounds are exclusive, so empty quotient boxes have dimension zero. -/
def positions (b j : ℕ) : Finset (ℕ×ℕ) :=
  ((range j) ×ˢ (range b)).filter (fun t=>t.1+t.2<b)

private theorem position {b j l i:ℕ} :
    (l,i)∈positions b j ↔ l<j ∧ i+l<b := by
  simp [positions,Nat.add_comm];omega

variable {K : Type*} [Field K]
abbrev Plane (K:Type*) [Semiring K] := K[X][X]

def box (K:Type*) [Field K] (b j:ℕ) : Submodule K (Plane K) where
  carrier := {P | ∀ l i, (l,i)∉positions b j → (P.coeff l).coeff i=0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hp hq l i out
    simp only [coeff_add,hp l i out,hq l i out,add_zero]
  smul_mem' := by
    intro c P hp l i out
    simp [hp l i out]

private def readBox (b j:ℕ) : box K b j →ₗ[K] (positions b j→K) where
  toFun P x:=((P.val.coeff x.val.1).coeff x.val.2)
  map_add' := by intro x y;funext i;simp
  map_smul' := by intro r x;funext i;simp

private theorem read_injective (b j:ℕ) : Function.Injective (readBox (K:=K) b j) := by
  intro P Q eq
  apply Subtype.ext
  ext l i
  by_cases yes:(l,i)∈positions b j
  · exact congrFun eq ⟨(l,i),yes⟩
  · rw [P.property l i yes,Q.property l i yes]

private def pack (b j:ℕ) (f:positions b j→K) : Plane K :=
  ∑ s:positions b j,monomial s.val.1 (monomial s.val.2 (f s))

private theorem pack_coeff (b j:ℕ) (f:positions b j→K) (l i:ℕ) :
    ((pack b j f).coeff l).coeff i = if h:(l,i)∈positions b j then f ⟨(l,i),h⟩ else 0 := by
  classical
  simp only [pack,finsetSum_coeff]
  have zero (s:positions b j) (ne:s.val≠(l,i)) :
      (((monomial s.val.1 (monomial s.val.2 (f s)) : Plane K).coeff l).coeff i)=0 := by
    by_cases h:s.val.1=l
    · have q:s.val.2≠i:=fun e=>ne (Prod.ext h e)
      simp [coeff_monomial,h,q]
    · simp [coeff_monomial,h]
  split
  · rename_i yes
    let s:positions b j:=⟨(l,i),yes⟩
    rw [Finset.sum_eq_single s]
    · simp [s,coeff_monomial]
    · intro t _ ne;exact zero t (fun h=>ne (Subtype.ext h))
    · simp
  · rename_i no
    exact sum_eq_zero (fun s _=>zero s (fun eq=>no (eq ▸ s.property)))

instance (b j:ℕ) : FiniteDimensional K (box K b j) :=
  Module.Finite.of_injective (readBox b j) (read_injective b j)

theorem box_dimension (b j:ℕ) : finrank K (box K b j)=(positions b j).card := by
  classical
  have onto : Function.Surjective (readBox (K:=K) b j) := by
    intro f
    have member:pack b j f∈box K b j := by
      intro l i no;rw [pack_coeff,dite_eq_right no]
    refine ⟨⟨_,member⟩,?_⟩
    funext s
    change ((pack b j f).coeff s.val.1).coeff s.val.2=_
    rw [pack_coeff,dite_eq_left s.property]
  have eq:=LinearEquiv.ofBijective (readBox (K:=K) b j) ⟨read_injective b j,onto⟩
  simpa using eq.finrank_eq

theorem mem_box {P:Plane K} {b j:ℕ} (nz:P≠0) :
    P∈box K b j ↔ totalJet P<b ∧ P.natDegree<j := by
  constructor
  · intro inside
    have top₁ : P.coeff P.natDegree≠0 := by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz
    have top₂ : (P.coeff P.natDegree).coeff (P.coeff P.natDegree).natDegree≠0 := by
      rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr top₁
    have atTop := position.mp (show (_,_)∈positions b j from by by_contra no;exact top₂ (inside _ _ no))
    have bound:totalJet P≤b-1 := (totalJet_le _ _).mpr (by
      intro l i ne
      have hit := position.mp (show (l,i)∈positions b j from by by_contra no;exact ne (inside l i no))
      omega)
    exact ⟨by omega,atTop.1⟩
  · rintro ⟨total,slope⟩ l i no
    by_contra ne
    have sum := (totalJet_le P _).mp le_rfl l i ne
    have active:P.coeff l≠0 := by intro eq;exact ne (by rw [eq,coeff_zero])
    have top:=le_natDegree_of_ne_zero active
    exact no (position.mpr ⟨by omega,by omega⟩)

private def restriction (A B:K[X]) (j:ℕ) : Plane K →ₗ[K] K[X] where
  toFun Q:= ∑ i∈range j,Q.coeff i*B^i*A^(j-1-i)
  map_add' := by intro P Q;simp [add_mul,sum_add_distrib]
  map_smul' := by intro r P;simp [Finset.smul_sum]

private theorem restriction_eq (A B:K[X]) {Q:Plane K} {j:ℕ} (hj:Q.natDegree<j) :
    restriction A B j Q=TerminalProjection.cleared A B Q (j-1) := by
  rw [TerminalProjection.cleared,Q.sum_over_range' (fun _=>by simp) j hj]
  rfl

#print axioms box_dimension
#print axioms mem_box

private theorem restriction_zero (G:Row K) (gp:G.primitive) {P:Plane K} {j:ℕ}
    (cap:P.natDegree<j) (dv:G.polynomial∣P) : restriction G.a G.b j P=0 := by
  rw [restriction_eq G.a G.b cap]
  let L:=FractionRing K[X]
  let f:=algebraMap K[X] L
  have inj:=IsFractionRing.injective K[X] L
  have den:f G.a≠0 := (map_ne_zero_iff _ inj).mpr gp.1
  let t:=f G.b/f G.a
  have eq : f G.a*t=f G.b := by dsimp [t];field_simp
  apply inj
  rw [map_zero,TerminalProjection.map_cleared f _ _ _ eq _ _ (by omega)]
  obtain ⟨q,rfl⟩:=dv
  have root:eval₂ f t G.polynomial=0 := by simp [Row.polynomial,eq]
  rw [eval₂_mul,root,zero_mul,mul_zero]

private theorem mem_quotient_box {G:Row K} (gp:G.primitive) {Q:Plane K} {b j:ℕ}
    (mem:G.polynomial*Q∈box K b j) : Q∈box K (b-G.graphDegree) (j-1) := by
  by_cases z:Q=0
  · rw [z];exact (box ..).zero_mem
  obtain ⟨first,second⟩ := (mem_box (mul_ne_zero (G.polynomial_ne gp) z)).mp mem
  rw [totalJet_mul (G.polynomial_ne gp) z,G.total_polynomial gp] at first
  rw [natDegree_mul (G.polynomial_ne gp) z,G.slope_degree gp] at second
  exact (mem_box z).mpr ⟨by omega,by omega⟩

private theorem mem_product_box {G:Row K} (gp:G.primitive) {Q:Plane K} {b j:ℕ}
    (mem:Q∈box K (b-G.graphDegree) (j-1)) : G.polynomial*Q∈box K b j := by
  by_cases z:Q=0
  · rw [z,mul_zero];exact (box ..).zero_mem
  obtain ⟨first,second⟩ := (mem_box z).mp mem
  apply (mem_box (mul_ne_zero (G.polynomial_ne gp) z)).mpr
  rw [totalJet_mul (G.polynomial_ne gp) z,G.total_polynomial gp,
    natDegree_mul (G.polynomial_ne gp) z,G.slope_degree gp]
  exact ⟨by omega,by omega⟩

private theorem slope_lt {Q:Plane K} {b j:ℕ} (pos:0<j) (h:Q∈box K b j) : Q.natDegree<j := by
  by_cases z:Q=0
  · simpa [z] using pos
  exact ((mem_box z).mp h).2

private theorem effective_slope {Q:Plane K} {b j:ℕ} (bp:0<b) (jp:0<j) (h:Q∈box K b j) :
    Q.natDegree < min b j := by
  by_cases z:Q=0
  · simp only [z,natDegree_zero];exact lt_min bp jp
  have ⟨bt,sj⟩ := (mem_box z).mp h
  have ne:Q.coeff Q.natDegree≠0 := by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr z
  have le:=(totalJet_le Q _).mp le_rfl Q.natDegree (Q.coeff Q.natDegree).natDegree
    (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr ne)
  exact lt_min (by omega) sj

private theorem range_slice {G:Row K} (gp:G.primitive) (b j:ℕ) (bp:0<b) (jp:0<j) :
    finrank K ((restriction G.a G.b (min b j)).domRestrict (box K b j)).range ≤
      (positions b j).card - (positions (b-G.graphDegree) (j-1)).card := by
  classical
  let V:=box K b j
  let T:=box K (b-G.graphDegree) (j-1)
  have finiteV : FiniteDimensional K ↥V := by dsimp [V]; infer_instance
  let p:V→ₗ[K]K[X]:=(restriction G.a G.b (min b j)).comp V.subtype
  let mult: T →ₗ[K] V :=
    (((Algebra.lmul K (Plane K) G.polynomial).comp T.subtype).codRestrict V (fun q=>mem_product_box gp q.property))
  let inKer:T→ₗ[K]p.ker:=mult.codRestrict _ (by
    intro q
    change restriction G.a G.b (min b j) (G.polynomial*q.val)=0
    exact restriction_zero G gp (effective_slope bp jp (mem_product_box gp q.property)) (dvd_mul_right ..))
  have inject: Function.Injective inKer := by
    intro x y eq
    exact Subtype.ext (mul_left_cancel₀ (G.polynomial_ne gp)
      (congrArg (fun z:p.ker=>(z.val:Plane K)) eq))
  have finiteK : FiniteDimensional K ↥p.ker := Module.Finite.of_injective p.ker.subtype p.ker.subtype_injective
  have size:=LinearMap.finrank_le_finrank_of_injective inject
  have rank:=LinearMap.finrank_range_add_finrank_ker (K:=K) (V:=↥V) (V₂:=K[X]) p
  change finrank K T≤finrank K p.ker at size
  change finrank K p.range+finrank K p.ker=finrank K V at rank
  change finrank K p.range≤_
  rw [show finrank K T=(positions (b-G.graphDegree) (j-1)).card from box_dimension ..] at size
  rw [show finrank K V=(positions b j).card from box_dimension ..] at rank
  omega

private theorem divisible_dimension (U:Submodule K K[X]) (D:K[X]) (dn:D≠0) (length:ℕ)
    (div:∀P∈U,D∣P) (cap:∀P∈U,P≠0 → P.natDegree<length) :
    finrank K U≤length-D.natDegree := by
  let T:=U.comap (Algebra.lmul K K[X] D)
  let mult:T→ₗ[K]U:=((Algebra.lmul K K[X] D).comp T.subtype).codRestrict U (fun q=>q.property)
  have bij:Function.Bijective mult := by
    constructor
    · intro x y eq;exact Subtype.ext (mul_left_cancel₀ dn (congrArg Subtype.val eq))
    · intro p
      obtain ⟨q,eq⟩:=div p.val p.property
      exact ⟨⟨q,by change D*q∈U;rw [←eq];exact p.property⟩,Subtype.ext eq.symm⟩
  let L:=length-D.natDegree
  have sub:T≤degreeLT K L := by
    intro q hq
    by_cases zero:q=0
    · rw [zero];exact (degreeLT K L).zero_mem
    have paid:=cap (D*q) hq (mul_ne_zero dn zero)
    rw [natDegree_mul dn zero] at paid
    apply (mem_degreeLT).mpr
    rw [degree_eq_natDegree zero,Nat.cast_lt]
    dsimp [L];omega
  rw [←(LinearEquiv.ofBijective mult bij).finrank_eq]
  apply (Submodule.finrank_mono sub).trans
  have eq:finrank K (degreeLT K L)=L := by simpa using (degreeLTEquiv K L).finrank_eq
  exact eq.le

/-- Number of independent restrictions remaining after the n independent
ordinate conditions, in an exclusive (b,j) box. -/
def imageAllowance (b j a n k:ℕ) := b+(a-1)*min (b-1) (j-1) - n*k

private theorem restricted_range {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (b j k:ℕ) (bp:0<b) (jp:0<j)
    (V:Submodule K (Plane K)) (sub:V≤box K b j)
    (contact:∀ (Q:Plane K),Q∈V → ∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K ((restriction G.a G.b (min b j)).domRestrict V).range ≤ imageAllowance b j G.graphDegree ys.card k := by
  classical
  let p:V→ₗ[K] K[X]:=(restriction G.a G.b (min b j)).comp V.subtype
  let d:K[X]:=(∏ y∈ys,(X-C y))^k
  have nz:d≠0:=pow_ne_zero _ (prod_ne_zero_iff.mpr (fun y _=>X_sub_C_ne_zero y))
  have dn:d.natDegree=ys.card*k := by
    dsimp [d];rw [natDegree_pow,natDegree_prod _ _ (fun y _=>X_sub_C_ne_zero y)]
    simp [Nat.mul_comm]
  let n:=b+(G.graphDegree-1)*min (b-1) (j-1)
  change finrank K p.range≤n-ys.card*k
  rw [←dn]
  apply divisible_dimension p.range d nz n
  · rintro _ ⟨Q,rfl⟩
    have fit:=effective_slope bp jp (sub Q.property)
    change d∣restriction G.a G.b (min b j) Q.val
    rw [restriction_eq G.a G.b fit]
    apply TerminalProjection.all_sheets G.a G.b _ ys v _ k (by omega)
    intro y hy
    have hit:=sub_eq_zero.mp (graph y hy)
    have regular:G.a.eval y≠0 := by
      intro zero
      change G.a.eval y*v y=G.b.eval y at hit
      obtain ⟨l,w,bz⟩:=gp.2
      have test:=congrArg (eval y) bz
      simp [←hit,zero] at test
    exact ⟨regular,hit,contact Q.val Q.property y hy⟩
  · rintro _ ⟨Q,rfl⟩ pn
    have qn:Q.val≠0:=by intro z;apply pn;change restriction G.a G.b (min b j) Q.val=0;rw [z,map_zero]
    obtain ⟨bt,sj⟩ := (mem_box qn).mp (sub Q.property)
    have fit := effective_slope bp jp (sub Q.property)
    change (restriction G.a G.b (min b j) Q.val).natDegree<n
    rw [restriction_eq G.a G.b fit]
    have width:=TerminalProjection.ordinate_width G.a G.b Q.val ((min b j)-1) G.graphDegree (b-1)
      (by omega) (by unfold Row.graphDegree;omega) (by unfold Row.graphDegree;omega)
      (le_max_right ..) (fun i hi=>by
        have ne:=mem_support_iff.mp hi
        have bh:=(totalJet_le Q.val _).mp le_rfl i (Q.val.coeff i).natDegree
          (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr ne)
        omega)
    dsimp [n];rw [show min (b-1) (j-1)=min b j-1 by omega];omega

/-- Rank gained by successively restricting to the same graph. The two
shape arguments are exclusive lengths. -/
def gain (a n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,_=>0
  | k+1,b,j=>
    if b=0 ∨ j=0 then 0 else
      (positions b j).card - (positions (b-a) (j-1)).card - imageAllowance b j a n (k+1) +
        gain a n k (b-a) (j-1)

/-- The recurrence bounds any subspace of the actual contact kernel, over
any field. Thus the choices of slope and chart at the selected ordinates
do not enter the numerical rank receipt. -/
theorem gain_bound {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (k b j:ℕ) (V:Submodule K (Plane K))
    (sub:V≤box K b j) (contact:∀ Q∈V,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K V + gain G.graphDegree ys.card k b j ≤ (positions b j).card := by
  classical
  have basic := (Submodule.finrank_mono sub).trans_eq (box_dimension b j)
  induction k generalizing b j V with
  | zero => simpa [gain] using basic
  | succ k ih =>
    by_cases empty : b=0 ∨ j=0
    · simpa [gain,empty] using basic
    have bp:0<b:=by omega
    have jp:0<j:=by omega
    let a:=G.graphDegree
    let cut:=restriction G.a G.b (min b j)
    let f:=cut.domRestrict V
    let T:Submodule K (Plane K):=(V ⊓ cut.ker).comap (Algebra.lmul K (Plane K) G.polynomial)
    have fit:T≤box K (b-a) (j-1) := by
      intro Q h
      exact mem_quotient_box gp (sub h.1)
    have newContact : ∀ Q∈T,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k := by
      intro Q h y hy
      have hit:=sub_eq_zero.mp (graph y hy)
      have reg:G.a.eval y≠0 := by
        intro z
        change G.a.eval y*v y=G.b.eval y at hit
        obtain ⟨l,w,bz⟩:=gp.2
        have bad:=congrArg (eval y) bz
        simp [←hit,z] at bad
      exact PadeJetOrder.strip G.a G.b Q y (v y) k reg hit (contact _ h.1 y hy)
    let mult:T→ₗ[K]V:=((Algebra.lmul K (Plane K) G.polynomial).comp T.subtype).codRestrict V
      (fun q=>q.property.1)
    let into:T→ₗ[K]f.ker:=mult.codRestrict _ (fun q=>q.property.2)
    have bij:Function.Bijective into := by
      constructor
      · intro x y eq
        exact Subtype.ext (mul_left_cancel₀ (G.polynomial_ne gp) (congrArg (fun z:f.ker=>(z.val:Plane K)) eq))
      · intro p
        have div:G.polynomial∣(p.val:Plane K) := by
          by_contra nd
          have hj:=effective_slope bp jp (sub p.val.property)
          have no:=TerminalProjection.nonzero_of_avoids G.a G.b (p.val:Plane K) (min b j-1)
            (by omega) gp.1 (G.polynomial_primitive gp) nd
          apply no
          rw [←restriction_eq G.a G.b hj]
          exact p.property
        obtain ⟨q,eq⟩:=div
        have qt:q∈T := by
          change G.polynomial*q∈V ⊓ cut.ker
          rw [←eq]
          exact ⟨p.val.property,p.property⟩
        exact ⟨⟨q,qt⟩,Subtype.ext (Subtype.ext eq.symm)⟩
    have kerRank:finrank K T=finrank K f.ker := (LinearEquiv.ofBijective into bij).finrank_eq
    have finV : FiniteDimensional K ↥V := Module.Finite.of_injective (Submodule.inclusion sub) (Submodule.inclusion_injective sub)
    have dim:=LinearMap.finrank_range_add_finrank_ker (K:=K) (V:=↥V) (V₂:=K[X]) f
    have imageFits : f.range≤(cut.domRestrict (box K b j)).range := by
      rintro _ ⟨x,rfl⟩;exact ⟨⟨x.val,sub x.property⟩,rfl⟩
    have slice:finrank K f.range≤(positions b j).card-(positions (b-a) (j-1)).card :=
      (Submodule.finrank_mono imageFits).trans (range_slice gp b j bp jp)
    have roots:=restricted_range gp ys v graph b j (k+1) bp jp V sub contact
    change finrank K f.range ≤ imageAllowance b j a ys.card (k+1) at roots
    have previous:=ih (b-a) (j-1) T fit newContact
      ((Submodule.finrank_mono fit).trans_eq (box_dimension (b-a) (j-1)))
    have contain : positions (b-a) (j-1) ⊆ positions b j := by
      rintro ⟨l,i⟩ h
      have h':=position.mp h
      exact position.mpr ⟨by omega,by omega⟩
    have count:=card_le_card contain
    rw [gain,ite_eq_right empty]
    change finrank K V+((positions b j).card-(positions (b-a) (j-1)).card-
      imageAllowance b j a ys.card (k+1)+gain a ys.card k (b-a) (j-1))≤_
    change finrank K T+gain a ys.card k (b-a) (j-1)≤_ at previous
    omega

#print axioms gain_bound
end
end Research6966.PadeRank
