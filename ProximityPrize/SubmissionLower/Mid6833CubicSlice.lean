/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Adaptation of Lucieno's two-sided Frobenius comparison in PR 618.
   The preliminary Cramer algebra uses the promoted 68.32 release (Apache-2.0). -/
import ProximityPrize.SubmissionLower.Koala6831Cramer
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
namespace Frontier6969
open Polynomial
open scoped BigOperators Classical Matrix Polynomial
open ProximityPrize.SubmissionLower.Koala6831Cramer
variable {K I : Type*} [Field K]

/-- b0..bTT are the six coefficients of the negative constant term of the comparison row. -/
structure Form (R : Type*) where
  a₀ : R
  ax : R
  ay : R
  c₀ : R
  cx : R
  cy : R
  r₀ : R
  rx : R
  ry : R
  rxx : R
  rxy : R
  ryy : R

def Form.flip {R} (f : Form R) : Form R :=
  ⟨f.c₀,f.cy,f.cx,f.a₀,f.ay,f.ax,f.r₀,f.ry,f.rx,f.ryy,f.rxy,f.rxx⟩

/-- Coefficients of (h₀+h₁Z)*a+(h₂+h₃T)*c. -/
def NoRel {R} [CommRing R] (f : Form R) : Prop := ∀ (h₀ h₁ h₂ h₃ : R),
  f.a₀*h₀ + f.c₀*h₂=0 →
  f.ax*h₀ + f.a₀*h₁ + f.cx*h₂=0 →
  f.ay*h₀ + f.cy*h₂ + f.c₀*h₃=0 →
  f.ax*h₁=0 → f.ay*h₁ + f.cx*h₃=0 → f.cy*h₃=0 →
  h₀=0 ∧ h₁=0 ∧ h₂=0 ∧ h₃=0

def live {R} [CommRing R] (f : Form R) (t : R) : Prop :=
  f.ax*((f.a₀+t*f.ay)*f.cx-(f.c₀+t*f.cy)*f.ax) ≠ 0

theorem flip_noRel {R} [CommRing R] (f : Form R) (h : NoRel f) : NoRel f.flip := by
  intro x y z t h0 hx hy hxx hxy hyy
  obtain ⟨h1,h2,h3,h4⟩ := h z t x y
    (by simpa [Form.flip,add_comm] using h0)
    (by simpa [Form.flip,add_comm,add_left_comm,add_assoc] using hy)
    (by simpa [Form.flip,add_comm,add_left_comm,add_assoc] using hx)
    (by simpa [Form.flip] using hyy) (by simpa [Form.flip,add_comm] using hxy)
    (by simpa [Form.flip] using hxx)
  exact ⟨h3,h4,h1,h2⟩

private theorem first_live {R} [CommRing R] [IsDomain R] (f : Form R)
    (h : NoRel f) (hx : f.ax≠0) : live f 0 ∨ live f 1 := by
  by_contra! both
  simp [live,hx] at both
  obtain ⟨e0,e1⟩ := both
  have ez : f.ay*f.cx-f.cy*f.ax=0 := by linear_combination e1-e0
  have v := h f.cx 0 (-f.ax) 0 (by linear_combination e0) (by ring)
    (by linear_combination ez) (by ring) (by ring) (by ring)
  exact hx (neg_eq_zero.mp v.2.2.1)

/-- Every nonsingular affine-in-the-two-seeds row has a nonsingular
three-coordinate slice in one orientation at t=0 or t=1. -/
theorem orientation {R} [CommRing R] [IsDomain R] (f : Form R) (h : NoRel f) :
    (live f 0 ∨ live f 1) ∨ (live f.flip 0 ∨ live f.flip 1) := by
  by_cases hx : f.ax=0
  · right
    apply first_live _ (flip_noRel f h)
    change f.cy≠0
    intro hy
    obtain ⟨c0,cx,a0,ay⟩ := h f.c₀ f.cx (-f.a₀) (-f.ay)
      (by ring) (by rw [hx]; ring) (by rw [hy];ring)
      (by rw [hx];ring) (by ring) (by rw [hy];ring)
    obtain ⟨one,-⟩ := h 1 0 0 0 (by simp [neg_eq_zero.mp a0]) (by simp [hx])
      (by simp [neg_eq_zero.mp ay]) (by simp) (by simp) (by simp)
    exact one_ne_zero one
  · exact Or.inl (first_live f h hx)

noncomputable def mat (f : Form K[X]) (t : K) : Matrix (Fin 3) (Fin 3) K[X] :=
  !![f.a₀+C t*f.ay,0,f.c₀+C t*f.cy; f.ax,f.a₀+C t*f.ay,f.cx; 0,f.ax,0]
noncomputable def rhs (f : Form K[X]) (t : K) : Fin 3 → K[X] :=
  ![f.r₀+C t*f.ry+C (t*t)*f.ryy,f.rx+C t*f.rxy,f.rxx]

structure Caps (f : Form K[X]) (w δ : ℕ) : Prop where
  a₀ : f.a₀.natDegree≤δ
  ax : f.ax.natDegree≤δ
  ay : f.ay.natDegree≤δ
  c₀ : f.c₀.natDegree≤δ
  cx : f.cx.natDegree≤δ
  cy : f.cy.natDegree≤δ
  r₀ : f.r₀.natDegree≤w+δ
  rx : f.rx.natDegree≤w+δ
  ry : f.ry.natDegree≤w+δ
  rxx : f.rxx.natDegree≤w+δ
  rxy : f.rxy.natDegree≤w+δ
  ryy : f.ryy.natDegree≤w+δ

structure Fits (f : Form K[X]) (x u v s t : K) : Prop where
  h0 : f.a₀.eval x*u+f.c₀.eval x*s=f.r₀.eval x
  hx : f.ax.eval x*u+f.a₀.eval x*v+f.cx.eval x*s=f.rx.eval x
  hy : f.ay.eval x*u+f.cy.eval x*s+f.c₀.eval x*t=f.ry.eval x
  hxx : f.ax.eval x*v=f.rxx.eval x
  hxy : f.ay.eval x*v+f.cx.eval x*t=f.rxy.eval x
  hyy : f.cy.eval x*t=f.ryy.eval x

theorem sliced_relation [DecidableEq K] (dom : I ↪ K) (seeds : Finset K) (ag : K → Finset I)
    (sel : K → K[X]) (u v s t : I → K) (f : Form K[X]) (b : K)
    (κ : K → K) (w δ : ℕ) (hc : Caps f w δ) (hl : live f (C b))
    (hf : ∀ g∈seeds, ∀ i∈ag g, Fits f (dom i) (u i) (v i) (s i) (t i))
    (hd : ∀ g∈seeds, (sel g).natDegree≤w)
    (ha : ∀ g∈seeds, w+3*δ<(ag g).card)
    (hv : ∀ g∈seeds, ∀ i∈ag g, (sel g).eval (dom i)=u i+κ g*v i)
    : ∃ D F G : K[X], D≠0 ∧ ∀ g∈seeds, D*sel g=F+C (κ g)*G := by
  let M := mat f b
  let r := rhs f b
  have hn : M.det≠0 := by
    have eq : M.det = -(f.ax*((f.a₀+C b*f.ay)*f.cx-(f.c₀+C b*f.cy)*f.ax)) := by
      simp [M,mat,Matrix.det_fin_three]
      ring
    rw [eq]; exact neg_ne_zero.mpr hl
  have combine (l j : K[X]) (a : K) (k) (h₁ : l.natDegree≤k) (h₂ : j.natDegree≤k) :
      (l+C a*j).natDegree≤k :=
    (natDegree_add_le _ _).trans (max_le h₁ ((natDegree_C_mul_le _ _).trans h₂))
  have hM : ∀ i j, (M i j).natDegree≤δ := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M,mat,hc.ax,hc.cx,combine _ _ b δ hc.a₀ hc.ay,combine _ _ b δ hc.c₀ hc.cy]
  have hr : ∀ i, (r i).natDegree≤w+δ := by
    intro i
    fin_cases i
    · exact combine _ _ (b*b) _ (combine _ _ b _ hc.r₀ hc.ry) hc.ryy
    · exact combine _ _ b _ hc.rx hc.rxy
    · exact hc.rxx
  let n0 := (M.updateCol 0 r).det
  let n1 := (M.updateCol 1 r).det
  refine ⟨M.det,n0,n1,hn,?_⟩
  intro g hg
  apply equation_of_node_agreement dom (ag g) M.det (sel g) n0 n1 (κ g) w (3*δ)
    (by simpa using det_natDegree_le_of_column_bounds M (fun _ => δ) hM)
    (hd g hg) (cramer_natDegree_le M r 0 w δ hM hr) (cramer_natDegree_le M r 1 w δ hM hr)
    (ha g hg)
  intro i hi
  let values : Fin 3 → K := ![u i,v i,s i+b*t i]
  have fit := hf g hg i hi
  have he : (evalRingHom (dom i)).mapMatrix M *ᵥ values = fun k => (r k).eval (dom i) := by
    funext k
    fin_cases k <;> simp [values,M,r,mat,rhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · linear_combination fit.h0+b*fit.hy+b^2*fit.hyy
    · linear_combination fit.hx+b*fit.hxy
    · exact fit.hxx
  have h₀ := eval_cramer_identity M r (dom i) values 0 he
  have h₁ := eval_cramer_identity M r (dom i) values 1 he
  change _ * u i = n0.eval (dom i) at h₀
  change _ * v i = n1.eval (dom i) at h₁
  rw [hv g hg i hi,← h₀,← h₁]; ring

theorem sliced [DecidableEq K] (dom : I ↪ K) (seeds : Finset K) (ag : K → Finset I)
    (sel : K → K[X]) (u v s t : I → K) (f : Form K[X]) (b : K)
    (w δ e : ℕ) (hc : Caps f w δ) (hl : live f (C b))
    (hf : ∀ g∈seeds, ∀ i∈ag g, Fits f (dom i) (u i) (v i) (s i) (t i))
    (hd : ∀ g∈seeds, (sel g).natDegree≤w)
    (ha : ∀ g∈seeds, w+3*δ<(ag g).card)
    (hv : ∀ g∈seeds, ∀ i∈ag g, (sel g).eval (dom i)=u i+g*v i)
    (hp : ∀ F G : K[X], F.natDegree≤w → G.natDegree≤w →
      (seeds.filter (fun g => sel g=F+C g*G)).card≤e+1) : seeds.card≤e+1 := by
  obtain ⟨D,F,G,hn,he⟩ := sliced_relation dom seeds ag sel u v s t f b id w δ hc hl hf hd ha hv
  exact card_le_of_common_denominator seeds sel D F G hn w e hd he hp

theorem flip_fits (f : Form K[X]) (x u v s t : K) (hf : Fits f x u v s t) :
    Fits f.flip x s t u v := by
  constructor <;> simp only [Form.flip]
  · linear_combination hf.h0
  · linear_combination hf.hy
  · linear_combination hf.hx
  · exact hf.hyy
  · linear_combination hf.hxy
  · exact hf.hxx

theorem both_orientations [DecidableEq K] (σ : K ≃+* K) (dom : I ↪ K) (hfix : ∀ i, σ (dom i)=dom i)
    (seeds : Finset K) (ag : K → Finset I) (sel : K → K[X]) (u v : I → K)
    (f : Form K[X]) (w δ e : ℕ) (hc : Caps f w δ) (hnorel : NoRel f)
    (hf : ∀ g∈seeds, ∀ i∈ag g, Fits f (dom i) (u i) (v i) (σ (u i)) (σ (v i)))
    (hd : ∀ g∈seeds, (sel g).natDegree≤w)
    (ha : ∀ g∈seeds, w+3*δ<(ag g).card)
    (hv : ∀ g∈seeds, ∀ i∈ag g, (sel g).eval (dom i)=u i+g*v i)
    (hp : ∀ F G : K[X], F.natDegree≤w → G.natDegree≤w →
      (seeds.filter (fun g => sel g=F+C g*G)).card≤e+1) : seeds.card≤e+1 := by
  have unpack (q : Form K[X]) (h : live q 0 ∨ live q 1) : ∃ b : K, live q (C b) := by
    rcases h with h | h
    · exact ⟨0,by simpa using h⟩
    · exact ⟨1,by simpa using h⟩
  rcases orientation f hnorel with l | r
  · obtain ⟨b,hb⟩ := unpack _ l
    exact sliced dom seeds ag sel u v _ _ f b w δ e hc hb hf hd ha hv hp
  obtain ⟨b,hb⟩ := unpack _ r
  have c : Caps f.flip w δ :=
    ⟨hc.c₀,hc.cy,hc.cx,hc.a₀,hc.ay,hc.ax,hc.r₀,hc.ry,hc.rx,hc.ryy,hc.rxy,hc.rxx⟩
  obtain ⟨D,F,G,hn,he⟩ := sliced_relation dom seeds ag (fun g => (sel g).map (σ : K →+* K))
    (fun i => σ (u i)) (fun i => σ (v i)) u v f.flip b σ w δ c hb
    (fun g hg i hi => flip_fits _ _ _ _ _ _ (hf g hg i hi))
    (fun g hg => natDegree_map_le.trans (hd g hg)) ha (by
      intro g hg i hi
      have h := Polynomial.eval_map_apply (σ : K →+* K) (dom i) (p := sel g)
      simpa only [RingEquiv.coe_toRingHom,hfix,hv g hg i hi,map_add,map_mul] using h)
  apply card_le_of_common_denominator seeds sel (D.map (σ.symm : K →+* K)) (F.map (σ.symm : K →+* K))
    (G.map (σ.symm : K →+* K)) (by simpa using hn) w e hd _ hp
  intro g hg
  have h := congrArg (Polynomial.map (σ.symm : K →+* K)) (he g hg)
  simpa only [Polynomial.map_mul,Polynomial.map_add,Polynomial.map_C,Polynomial.map_map,
    RingEquiv.symm_comp,RingEquiv.coe_toRingHom,RingEquiv.symm_apply_apply,Polynomial.map_id] using h

#print axioms both_orientations
#print axioms orientation
#print axioms sliced
end Frontier6969
