import ArkLib.Data.MvPolynomial.WeightedOrder
import ArkLib.Data.MvPolynomial.WeightAtMost
import ArkLib.Data.Finset.WeightedSimplex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

set_option Elab.async false

-- merged module R6966ProofWordSurfaceJets
section Merged_R6966ProofWordSurfaceJets

namespace Research6966.WordSurfaceJets
open Finset Module MvPolynomial
variable {σ K:Type*} [Fintype σ] [DecidableEq σ] [Field K]
noncomputable section
set_option maxHeartbeats 500000

abbrev Pol (σ K:Type*) [CommSemiring K] := MvPolynomial σ K

def high (σ K:Type*) [Field K] (k:ℕ) : Ideal (Pol σ K) :=
  restrictSupportIdeal K {e : σ →₀ ℕ | k≤e.degree} (by
    intro a b h hp
    exact (show k≤a.degree from hp).trans (Finsupp.degree_mono h))

def low (σ K:Type*) [Field K] (k:ℕ) : Submodule K (Pol σ K) :=
  restrictSupport K {e | e.degree<k}

abbrev Local (σ K:Type*) [Field K] (k:ℕ) := Pol σ K ⧸ high σ K k

theorem mem_high {P:Pol σ K} {k:ℕ} : P∈high σ K k ↔ ∀ e∈P.support,k≤e.degree := Iff.rfl

theorem high_eq (k:ℕ) :
    (high σ K k).restrictScalars K=restrictWeightedOrder (R:=K) (fun _:σ=>1) k := by
  ext P
  change (∀ e∈P.support,k≤e.degree) ↔ ∀ e∈P.support,k≤e.weight (fun _:σ=>1)
  simp only [Finsupp.degree_eq_weight_one,Pi.one_def]

theorem high_mul {a b:ℕ} {P Q:Pol σ K} (hp:P∈high σ K a) (hq:Q∈high σ K b) :
    P*Q∈high σ K (a+b) := by
  change P∈(high σ K a).restrictScalars K at hp
  change Q∈(high σ K b).restrictScalars K at hq
  change P*Q∈(high σ K (a+b)).restrictScalars K
  rw [high_eq] at hp hq ⊢
  exact mul_mem_restrictWeightedOrder hp hq

theorem high_pow {a:ℕ} {P:Pol σ K} (hp:P∈high σ K a) (n:ℕ) : P^n∈high σ K (n*a) := by
  induction n with
  | zero=>simp [mem_high]
  | succ n ih=>rw [pow_succ,Nat.succ_mul];exact high_mul ih hp

theorem high_one {P:Pol σ K} : P∈high σ K 1 ↔ constantCoeff P=0 := by
  constructor
  · intro h
    by_contra ne
    exact (by simpa using mem_high.mp h 0 (mem_support_iff.mpr ne) : False)
  · intro hz
    apply mem_high.mpr
    intro e he
    by_contra! small
    have zero:e=0:=by
      ext i
      have cap:=Finsupp.le_degree (s:=i) (f:=e)
      simp only [Finsupp.zero_apply];omega
    exact (mem_support_iff.mp he) (zero ▸ hz)

def trunc (k:ℕ) : Pol σ K →ₗ[K] low σ K k :=
  (weightedTruncation (fun _:σ=>1) k).codRestrict _ (fun P=>by
    change ∀ e∈((weightedTruncation (fun _:σ=>1) k) P).support,e.degree<k
    intro e he
    have alive : ((weightedTruncation (fun _:σ=>1) k) P).coeff e≠0 := mem_support_iff.mp he
    by_contra h
    apply alive
    rw [coeff_weightedTruncation,ite_eq_right]
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using h)

theorem trunc_class (k:ℕ) (P:Pol σ K) :
    Ideal.Quotient.mk (high σ K k) ((trunc k P).val) = Ideal.Quotient.mk _ P := by
  apply Ideal.Quotient.eq.mpr
  apply mem_high.mpr
  intro e he
  by_contra! small
  apply mem_support_iff.mp he
  change (weightedTruncation _ k P-P).coeff e=0
  rw [coeff_sub,coeff_weightedTruncation,ite_eq_left,sub_self]
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using small

def read (k:ℕ) : low σ K k →ₗ[K] Local σ K k :=
  ((Ideal.Quotient.mkₐ K (high σ K k)).toLinearMap).comp (low σ K k).subtype

theorem read_bijective (k:ℕ) : Function.Bijective (read (σ:=σ) (K:=K) k) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro P h
    have hp:P.val∈high σ K k:=Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp h)
    apply Subtype.ext
    by_contra ne
    obtain ⟨e,he⟩:=Finset.nonempty_iff_ne_empty.mpr (show P.val.support≠∅ from by simpa using ne)
    exact (Nat.not_lt_of_ge (mem_high.mp hp e he)) (P.property he)
  · intro z
    obtain ⟨P,rfl⟩:=Ideal.Quotient.mk_surjective z
    exact ⟨trunc k P,trunc_class k P⟩

theorem local_dimension (k:ℕ) :
    finrank K (Local σ K (k+1))=(k+Fintype.card σ).choose (Fintype.card σ) := by
  rw [←(LinearEquiv.ofBijective _ (read_bijective (σ:=σ) (K:=K) (k+1))).finrank_eq]
  unfold low
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  let equiv : {e:σ→₀ℕ // e.degree<k+1} ≃ {e:σ→₀ℕ // e.weight (fun _:σ=>1)≤k} :=
    Equiv.subtypeEquivRight (fun _=>by simp [Finsupp.degree_eq_weight_one,Pi.one_def])
  change Nat.card {e:σ→₀ℕ // e.degree<k+1}=_
  rw [Nat.card_congr equiv,Finset.card_finsupp_weight_le_eq_card_natWeightedSimplex _ (by simp),
    Finset.card_natWeightedSimplex_one]

instance (k:ℕ) : FiniteDimensional K (low σ K k) := by
  apply restrictSupport_finite
  exact (Finsupp.finite_of_degree_le k).subset (fun _ h=>Nat.le_of_lt h)

instance (k:ℕ) : FiniteDimensional K (Local σ K k) :=
  Module.Finite.of_surjective (read k) (read_bijective k).2

/-- Truncating a multiplier one degree earlier preserves its product by
any relation vanishing at this point. This holds also at singular points. -/
theorem relation_image (k:ℕ) (F Q:Pol σ K) (hz:constantCoeff F=0) :
    Ideal.Quotient.mk (high σ K (k+1)) (F*Q)=
      Ideal.Quotient.mk _ (F*(trunc k Q).val) := by
  apply Ideal.Quotient.eq.mpr
  rw [←mul_sub]
  have diff:=Ideal.Quotient.eq.mp (trunc_class k Q).symm
  simpa only [Nat.add_comm 1 k] using high_mul (high_one.mpr hz) diff

/-- A separator nonzero at its own point is a unit in every truncated
local ring there. -/
theorem local_unit (k:ℕ) {P:Pol σ K} (atOrigin:constantCoeff P≠0) :
    IsUnit (Ideal.Quotient.mk (high σ K k) P) := by
  let π:=Ideal.Quotient.mk (high σ K k)
  let c:=constantCoeff P
  have hz:constantCoeff (P-C c)=0:=by simp [c]
  have nil:IsNilpotent (π (P-C c)):=by
    refine ⟨k,?_⟩
    rw [←map_pow,Ideal.Quotient.eq_zero_iff_mem]
    simpa using high_pow (high_one.mpr hz) k
  have unit:IsUnit (π (C c)) := (atOrigin.isUnit.map (C:K→+*Pol σ K)).map π
  have sum:=nil.isUnit_add_right_of_commute unit (Commute.all _ _)
  simpa [map_sub] using sum

end
end Research6966.WordSurfaceJets

end Merged_R6966ProofWordSurfaceJets

-- merged module R6966ProofWordSurfaceInterpolation
section Merged_R6966ProofWordSurfaceInterpolation

namespace Research6966.WordSurfaceInterpolation
open Finset Module MvPolynomial WordSurfaceJets
variable {σ K ι:Type*} [Fintype σ] [DecidableEq σ] [Field K]
noncomputable section

def shift (p:σ→K) : Pol σ K →ₐ[K] Pol σ K := bind₁ (fun i=>X i+C (p i))

theorem shift_inverse (p:σ→K) (Q:Pol σ K) : shift p (shift (-p) Q)=Q := by
  have id:(shift p).comp (shift (-p))=AlgHom.id K (Pol σ K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [shift]
  exact AlgHom.congr_fun id Q

theorem shift_origin (p:σ→K) (Q:Pol σ K) : constantCoeff (shift p Q)=eval p Q := by
  have id:(constantCoeff (σ:=σ) (R:=K)).comp (shift p).toRingHom=eval p := by
    apply MvPolynomial.ringHom_ext
    · intro c;simp [shift,RingHom.comp_apply]
    · intro i;simp [shift,RingHom.comp_apply]
  exact RingHom.congr_fun id Q

def rect (σ K:Type*) [Field K] (cap:σ→ℕ) : Submodule K (Pol σ K) :=
  restrictSupport K {e | ∀ i,e i≤cap i}

theorem in_rect {Q:Pol σ K} {cap:σ→ℕ} : Q∈rect σ K cap ↔ ∀ i,Q.degreeOf i≤cap i := by
  change (∀ e∈Q.support,∀ i,e i≤cap i) ↔ _
  simp only [MvPolynomial.degreeOf_le_iff]
  exact ⟨fun h i e he=>h e he i,fun h e he i=>h i e he⟩

private def boxEquiv (cap:σ→ℕ) : {e:σ→₀ℕ // ∀ i,e i≤cap i} ≃ (∀ i,Fin (cap i+1)) where
  toFun e i:=⟨e.val i,Nat.lt_succ_of_le (e.property i)⟩
  invFun x:=⟨Finsupp.equivFunOnFinite.symm (fun i=>(x i).val),fun i=>Nat.le_of_lt_succ (x i).isLt⟩
  left_inv _:=Subtype.ext (by ext;rfl)
  right_inv _:=by funext i;exact Fin.ext rfl

instance (cap:σ→ℕ) : FiniteDimensional K (rect σ K cap) := by
  letI : Finite {e:σ→₀ℕ // ∀ i,e i≤cap i}:=Finite.of_equiv _ (boxEquiv cap).symm
  exact Module.Finite.of_basis (basisRestrictSupport K {e:σ→₀ℕ | ∀ i,e i≤cap i})

theorem rectangle_dimension (cap:σ→ℕ) : finrank K (rect σ K cap)=∏i, (cap i+1) := by
  unfold rect
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {e:σ→₀ℕ // ∀ i,e i≤cap i}=_
  rw [Nat.card_congr (boxEquiv cap),Nat.card_eq_fintype_card,Fintype.card_pi]
  simp

private theorem low_shift_axis (p:σ→K) (k:ℕ) (pos:0<k) (Q:low σ K k) (i:σ) :
    (shift p Q.val).degreeOf i≤k-1 := by
  let w:σ→ℕ:=fun _=>1
  have lowBound:Q.val∈restrictWeightAtMost w (k-1) := by
    intro e he
    have h:e.degree<k:=Q.property he
    change e.weight w≤k-1
    have eq:e.weight w=e.degree:=by rw [Finsupp.degree_eq_weight_one]
    omega
  have shifted:shift p Q.val ∈ restrictWeightAtMost w (k-1) :=
    bind₁_mem_restrictWeightAtMost (w:=w) (fun z=>(restrictWeightAtMost w (w z)).add_mem
      (X_mem_restrictWeightAtMost _ _ le_rfl) (C_mem_restrictWeightAtMost _ (Nat.zero_le _) _)) lowBound
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  exact (Finsupp.le_degree (s:=i) (f:=e)).trans (by
    rw [Finsupp.degree_eq_weight_one];exact mem_restrictWeightAtMost.mp shifted e he)

def atPoint (p:σ→K) (k:ℕ) : Pol σ K →ₐ[K] Local σ K k := (Ideal.Quotient.mkₐ K (high σ K k)).comp (shift p)
def atPoints (p:ι→σ→K) (k:ℕ) : Pol σ K →ₗ[K] (ι→Local σ K k) :=
  LinearMap.pi (fun i=>(atPoint (p i) k).toLinearMap)

/-- Multijet interpolation with an explicit box of global coordinate
degrees. The local inverse of each separator has a Taylor representative
of total degree at most k-1 in all characteristics. -/
theorem interpolate_on [Fintype ι] (p:ι→σ→K) (k:ℕ) (V:Submodule K (Pol σ K))
    (sep:ι→Pol σ K) (fits:∀ i (Q:low σ K k),sep i*shift (-(p i)) Q.val∈V)
    (own:∀ i,eval (p i) (sep i)≠0) (other:∀ i j,i≠j → shift (p i) (sep j) ∈ high σ K k) :
    Function.Surjective ((atPoints p k).domRestrict V) := by
  classical
  intro target
  have patch (i:ι) : ∃ R:low σ K k,(atPoint (p i) k (sep i))*read k R=target i := by
    have unit:IsUnit (atPoint (p i) k (sep i)) :=
      local_unit k ((shift_origin (p i) (sep i)) ▸ own i)
    obtain ⟨x,eq⟩:=(unit.dvd : atPoint (p i) k (sep i) ∣ target i)
    obtain ⟨R,rx⟩:=(read_bijective k).2 x
    exact ⟨R,rx ▸ eq.symm⟩
  choose jet correct using patch
  let term (i:ι):=sep i*shift (-(p i)) (jet i).val
  refine ⟨⟨∑i,term i,Submodule.sum_mem _ (fun i _=>fits i (jet i))⟩,?_⟩
  funext i
  change atPoint (p i) k (∑j,term j)=target i
  rw [map_sum,Finset.sum_eq_single i]
  · dsimp only [term]
    rw [map_mul]
    change _*Ideal.Quotient.mk _ (shift (p i) (shift (-p i) (jet i).val))=_
    rw [shift_inverse];exact correct i
  · intro j _ ne
    change atPoint (p i) k (sep j*_) = 0
    rw [map_mul]
    have zero:atPoint (p i) k (sep j)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (other i j ne.symm)
    rw [zero,zero_mul]
  · simp

theorem interpolate [Fintype ι] (p:ι→σ→K) (k:ℕ) (pos:0<k) (D:σ→ℕ)
    (sep:ι→Pol σ K) (cap:∀ i j,(sep i).degreeOf j≤D j)
    (own:∀ i,eval (p i) (sep i)≠0) (other:∀ i j,i≠j → shift (p i) (sep j) ∈ high σ K k) :
    Function.Surjective ((atPoints p k).domRestrict (rect σ K (fun i=>D i+(k-1)))) := by
  apply interpolate_on p k _ sep _ own other
  intro i Q
  exact in_rect.mpr (fun z=>(degreeOf_mul_le z ..).trans
    (Nat.add_le_add (cap i z) (low_shift_axis _ k pos Q z)))

end
end Research6966.WordSurfaceInterpolation

end Merged_R6966ProofWordSurfaceInterpolation
