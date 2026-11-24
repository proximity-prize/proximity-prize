import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentSupport

set_option autoImplicit false

namespace Low49ActiveSupport
open MvPolynomial
open K1_13 (Row Shape shape InBox)
open K1_13_6 (genericCoeffs separant)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_2 (generic5 rawGraph denominator padded)
open K1_13_6_2_4 (Exponent)
open Low48BentLattice (Cap Allowed coords)
open Low48BentSupport (graph lifted)
open Low49ActiveLattice (Active points)
open K1_13_6_2_2_1 (support_bounds)
noncomputable section

def Fits (P : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K

def Raw (a : Cap) (c : ℕ) (m : Exponent) : Prop :=
  Allowed a m ∧ m 0+2*Active m+3*m 4+c ≤ a.1.b+a.1.j

def Box (a : Cap) (c : ℕ) (D : GeoJets5) : Prop :=
  ∀ m ∈ D.support, Raw a c m

private def w : Fin 5 → ℕ := ![1,2,2,2,3]

private theorem w0 : w 0 = 1 := by decide
private theorem w1 : w 1 = 2 := by decide
private theorem w2 : w 2 = 2 := by decide
private theorem w3 : w 3 = 2 := by decide
private theorem w4 : w 4 = 3 := by decide

private theorem fits_weight {P : Row 4} {K : ℕ} :
    Fits P K ↔ P.weightedTotalDegree (w ∘ Fin.castSucc) ≤ K := by
  unfold Fits MvPolynomial.weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_four, Function.comp_apply, smul_eq_mul,
    show Fin.castSucc (0 : Fin 4) = 0 by rfl, show Fin.castSucc (1 : Fin 4) = 1 by rfl,
    show Fin.castSucc (2 : Fin 4) = 2 by rfl, show Fin.castSucc (3 : Fin 4) = 3 by rfl,
    w0,w1,w2,w3,Nat.mul_comm,one_mul]

theorem separant_fits {P : Row 4} {K : ℕ} (h : Fits P K) (n : ℕ) :
    Fits ((separant^[n]) P) K := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    apply fits_weight.mpr
    have h1 := fits_weight.mp ih
    exact (weightedTotalDegree_pderiv_le_sub _ _ _).trans
      ((Nat.sub_le _ _).trans h1)

theorem raw_zero (a : Cap) (c : ℕ) (hc : c≤a.1.b+a.1.j) : Raw a c 0 := by
  simp [Raw, Allowed, Active, hc]

theorem raw_pair {a : Cap} {c : ℕ} {m n : Exponent} (hm : Raw a c m) (hn : Raw a c n) :
    m+n ∈ points a c := by
  simp only [points, Set.mem_ofPred_eq, coords, Finsupp.add_apply, Active]
  obtain ⟨hm,hm'⟩ := hm
  obtain ⟨hn,hn'⟩ := hn
  unfold Allowed at hm hn
  unfold Active at hm' hn'
  omega

private theorem to_box {a : Cap} {P : Row 5} {c K : ℕ}
    (h0 : Low48BentSupport.Box a (generic5 P))
    (hw : P.weightedTotalDegree w ≤ K) (hc : K+c≤a.1.b+a.1.j) :
    Box a c (generic5 P) := by
  intro m hm
  refine ⟨h0 m hm,?_⟩
  have hs := MvPolynomial.support_map_subset genericCoeffs P hm
  have hb := (le_weightedTotalDegree w hs).trans hw
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_five, smul_eq_mul, w0,w1,w2,w3,w4,mul_one] at hb
  unfold Active
  omega

theorem chart_support {p : Shape} {g : Row 4}
    (hp : p.j ≤ p.b ∧ 3*p.t ≤ p.j) (ht : 1≤p.t)
    (hf : InBox (shape g) p) {c cg : ℕ} (hc : 2≤c)
    (h0 : Fits g (p.b + p.j-c)) (hc0 : c≤p.b-p.j) (hcg : cg≤c) :
    Box (graph p) cg (generic5 (rawGraph g)) ∧
      ∀ (k cl : ℕ), cl≤2+k*(c-2) →
        Box (lifted p k) cl (generic5 (denominator g k)) ∧
        ∀ i≤k+4, Box (lifted p k) cl (generic5 (padded g k i)) := by
  have hrect := Low48BentSupport.chart_support hp ht hf
  have hw := support_bounds w 1 (fun i => by fin_cases i <;> decide)
    (by decide) (fun i => by fin_cases i <;> decide)
    (fits_weight.mp h0) (by
      change 2 ≤ p.b+p.j-c
      have hj := hp.2
      have hb := hp.1
      omega)
  refine ⟨to_box hrect.1 hw.1 ?_,?_⟩
  · dsimp [graph]
    have hb := le_max_left p.b (p.j+1)
    omega
  · intro k cl hl
    have hB (P : Row 5) (hP : Low48BentSupport.Box (lifted p k) (generic5 P))
        (hh : P.weightedTotalDegree w ≤ 3+k*(p.b+p.j-c-2+1)) :
        Box (lifted p k) cl (generic5 P) := by
      apply to_box hP hh
      have hpj : 3≤p.j := by have := hp.2; omega
      have hpb := hp.1
      have he : (p.b+p.j-c-2+1)+(c-2) = (p.b-1)+(p.j-2) := by omega
      have hMul : k*(p.b+p.j-c-2+1)+k*(c-2) = k*(p.b-1)+k*(p.j-2) := by
        calc
          _ = k*((p.b+p.j-c-2+1)+(c-2)) := (Nat.mul_add _ _ _).symm
          _ = k*((p.b-1)+(p.j-2)) := by rw [he]
          _ = _ := Nat.mul_add _ _ _
      calc
        _ ≤ (3+k*(p.b+p.j-c-2+1))+(2+k*(c-2)) := Nat.add_le_add_left hl _
        _ = (lifted p k).1.b + (lifted p k).1.j := by
          dsimp [lifted]
          omega
    exact ⟨hB _ (hrect.2 k).1 (hw.2 k).1,
      fun i hi => hB _ ((hrect.2 k).2 i hi) ((hw.2 k).2 i hi)⟩

end
end Low49ActiveSupport
