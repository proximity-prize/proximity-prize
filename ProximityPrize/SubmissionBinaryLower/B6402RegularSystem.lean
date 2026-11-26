import ProximityPrize.SubmissionBinaryLower.B6402PrimarySystem
import ProximityPrize.SubmissionBinaryLower.P64C6Flat
import ProximityPrize.SubmissionBinaryLower.P64C6Weights

/-! The actual regular-fibre equations on the translated resultant. Their
output is indexed by the even spatial slices and bounded seed coefficients. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402RegularSystem
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402MixedDegree B6402SeedCoordinates B6402PrimarySystem B6402QuotientSpace
open P64Found P64LineOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] [CharP K 2]

private theorem slice_weight {F : ContactPoly (Polynomial K)} {q h : ℕ}
    (hf : mixed q F≤h) (k : ℕ) : WtLE 0 q 1 h (F.coeff k) := by
  intro a b l hc
  let p := ((F.coeff k).coeff b).coeff a
  have hcoeff : p.coeff l ≠ 0 := hc
  have hp : p≠0 := fun e => hcoeff (by simp [e])
  have lo := le_natDegree_of_ne_zero hcoeff
  have hi := (mixed_le_iff q h F).mp hf k b a hp
  change p.natDegree + q*(b+k) ≤ _ at hi
  simp only [zero_mul,zero_add,one_mul]; rw [Nat.mul_add] at hi; omega

private theorem pow_weight {q h : ℕ} {p : BiPoly (Polynomial K)} (hp : WtLE 0 q 1 h p) (b : ℕ) :
    WtLE 0 q 1 (b*h) (p^b) := by
  induction b with
  | zero =>
    intro i j l hn
    by_cases hj : j=0 <;> by_cases hi : i=0 <;> by_cases hl : l=0 <;>
      simp_all [c3,coeff_one]
  | succ b ih =>
    simpa only [Nat.succ_mul,pow_succ] using ih.mul hp

noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial K))) := AddMonoidAlgebra.commRing

theorem resultant_weight (F G : ContactPoly (Polynomial K)) (q H T s : ℕ)
    (hf : mixed q F ≤ H) (hg : mixed q G ≤ T) :
    WtLE (F:=K) 0 q 1 (T+s*H) (show BiPoly (Polynomial K) from Polynomial.resultant F G 1 s) := by
  rw [resultant_deg1_char2]
  intro a b l hn
  rw [c3_sum] at hn
  obtain ⟨j,hj,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hl := (slice_weight hg j).mul (pow_weight (slice_weight hf 0) j)
  have hb := (hl.mul (pow_weight (slice_weight hf 1) (s-j))) a b l hc
  have : j+(s-j)=s := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [←this,Nat.add_mul]; omega

def start (m s i : ℕ) := 2*m+3*s-2*i
abbrev Slice (m s b J : ℕ) := Σ i : Fin b, Fin (J+4*s-start m s i+1)
abbrev Tests (m s b J cap : ℕ) := Slice m s b J × Fin (cap+1)

variable {w W s q T : ℕ}
noncomputable def phi (F : ContactPoly (Polynomial K)) (x : K) (y : K[X])
    (u : Global K w W s q T) : BiPoly (Polynomial K) :=
  lineShiftHom x y (resultant F (source q T u) 1 s)

theorem phi_add (F : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (u v : Global K w W s q T) :
    phi F x y (u+v)=phi F x y u+phi F x y v := by
  simp only [phi,source_add,resultant_deg1_char2,coeff_add,add_mul,Finset.sum_add_distrib,map_add]

theorem phi_smul (F : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (c : K) (u : Global K w W s q T) :
    phi F x y (c • u)=c • phi F x y u := by
  unfold phi
  rw [source_smul]
  simp only [resultant_deg1_char2,cC,coeff_C_mul,mul_assoc,← Finset.mul_sum,map_mul,lineShiftHom_CC]
  rw [Algebra.smul_def]; rfl

noncomputable def equations (F : ContactPoly (Polynomial K)) (x : K) (y : K[X])
    (m b J cap : ℕ) : Global K w W s q T →ₗ[K] (Tests m s b J cap → K) where
  toFun u r := c3 (phi F x y u) (2*r.1.1.val) (start m s r.1.1+r.1.2.val) r.2.val
  map_add' u v := by funext r; simp only [phi_add,c3_add,Pi.add_apply]
  map_smul' c u := by funext r; simp only [phi_smul,c3_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

theorem tests_zero (F : ContactPoly (Polynomial K)) (x : K) (y : K[X]) (m b J H : ℕ)
    (hw : 0<w) (hy : y.natDegree≤q) (hf : mixed q F≤H) (u : Global K w W s q T)
    (hu : equations F x y m b J (T+s*H) u=0)
    (i j : ℕ) (hi : i<b) (low : 2*m+3*s≤2*i+j) (high : j≤J+4*s) :
    ((phi F x y u).coeff j).coeff (2*i)=0 := by
  ext l
  have hlow : start m s i≤j := by unfold start; omega
  have hj : j-start m s i < J+4*s-start m s i+1 := by omega
  by_cases hl : l<T+s*H+1
  · have hz := congrFun hu (⟨⟨⟨i,hi⟩,⟨j-start m s i,hj⟩⟩,⟨l,hl⟩⟩ : Tests m s b J (T+s*H))
    change (((phi F x y u).coeff (start m s i+(j-start m s i))).coeff (2*i)).coeff l=0 at hz
    simpa only [Nat.add_sub_of_le hlow,coeff_zero] using hz
  · rw [coeff_zero]
    by_contra hn
    have hr := resultant_weight F (source q T u) q H T s hf (source_bounds hw u).2.2.2
    have hwgt := P64C6Weights.lineShift_weight _ x y q (T+s*H) hr hy (2*i) j l hn
    simp only [zero_mul,zero_add,one_mul] at hwgt
    omega

theorem card_tests (m s b J cap : ℕ) (hm : 2*m≤J+s) (hb : b≤m) :
    Fintype.card (Tests m s b J cap)=(b*(J+s-2*m+1)+b*(b-1))*(cap+1) := by
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  congr 1
  calc _ = ∑ i : Fin b, (J+4*s-start m s i+1) := Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)
       _ = ∑ i ∈ Finset.range b, (J+4*s-start m s i+1) := Fin.sum_univ_eq_sum_range (fun i : ℕ => J+4*s-start m s i+1) b
       _ = _ := B6402QuotientDimension.regular_layers J s m b hm hb

#print axioms resultant_weight
#print axioms tests_zero
#print axioms card_tests
end ProximityPrize.SubmissionBinaryLower.B6402RegularSystem
