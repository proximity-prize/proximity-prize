import ProximityPrize.SubmissionLower.R6966ProofPadeCoverage
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.GaussLemma

set_option Elab.async false

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K E : Type*} [Field K] [Field E]

def Row.map (f:K→+*E) (G:Row K) : Row E := ⟨G.a.map f,G.b.map f⟩

theorem Row.degree_map (f:K→+*E) (G:Row K) :
    (G.map f).graphDegree=G.graphDegree := by
  simp [Row.map,Row.graphDegree,natDegree_map_eq_of_injective f.injective]

theorem Row.primitive_map (f:K→+*E) {G:Row K} :
    (G.map f).primitive ↔ G.primitive := by
  simp only [Row.primitive,Row.map,Polynomial.isCoprime_map]
  rw [show G.a.map f≠0 ↔ G.a≠0 from map_ne_zero_iff (mapRingHom f) (map_injective f f.injective)]

private theorem err_at_map (f:K→+*E) (G:Row K) (x z:K) :
    (G.map f).a.eval (f x)*f z-(G.map f).b.eval (f x) =
      f (G.a.eval x*z-G.b.eval x) := by
  simp only [Row.map,eval_map_apply,map_sub,map_mul]

variable [Algebra K E]

theorem Controls.conjugate {sheet:E→E→Prop} {c:ℕ} {G:Row E} (h:Controls G sheet c)
    (stable : ∀ (σ:E≃ₐ[K]E) x y,sheet x y → sheet (σ x) (σ y))
    (σ:E≃ₐ[K]E) : Controls (G.map σ.toRingHom) sheet c := by
  classical
  intro s v hv
  let t:=s.image σ.symm
  let w (x:E):=σ.symm (v (σ x))
  have cnt := h t w (by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hx
    have hy':=hv y hy
    refine ⟨by simpa [w] using stable σ.symm _ _ hy'.1,?_⟩
    intro zero
    apply hy'.2
    have eq:=err_at_map σ.toRingHom G (σ.symm y) (w (σ.symm y))
    change G.a.eval (σ.symm y)*w (σ.symm y)-G.b.eval (σ.symm y)=0 at zero
    rw [zero,map_zero] at eq
    simpa [Row.err,w] using eq)
  have eq:t.card=s.card:=card_image_of_injective _ σ.symm.injective
  rwa [eq,←Row.degree_map σ.toRingHom G] at cnt

private theorem polynomial_descent [IsGalois K E] (p:E[X])
    (fixed : ∀ σ:E≃ₐ[K]E,p.map σ.toRingHom=p) :
    ∃ q:K[X],q.map (algebraMap K E)=p := by
  apply (mem_lifts p).mp
  apply (lifts_iff_coeff_lifts p).mpr
  intro j
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K) _).mpr
  intro σ
  change σ.toRingHom (p.coeff j)=p.coeff j
  rw [←coeff_map]
  exact congrArg (fun v:E[X]=>v.coeff j) (fixed σ)

/-- Descent uses the actual unique normalized graph over a Galois field.
In positive characteristic this is applied to separable sheet coordinates. -/
theorem descend_control [IsGalois K E] (sheet:E→E→Prop) (e c:ℕ) (gap:2*c<e)
    (initial : ∃ (s:Finset E) (v:E→E),s.card=e ∧ ∀x∈s,sheet x (v x))
    (stable : ∀ (σ:E≃ₐ[K]E) x y,sheet x y → sheet (σ x) (σ y))
    {F:Row E} (fp:F.primitive) (control:Controls F sheet c) :
    ∃ G:Row K,G.primitive ∧ G.graphDegree=F.graphDegree ∧
      Controls (G.map (algebraMap K E)) sheet c := by
  let t:=F.a.leadingCoeff⁻¹
  have tn:t≠0 := inv_ne_zero (leadingCoeff_ne_zero.mpr fp.1)
  let G:=F.scale t
  have monic:G.a.Monic := by simpa [G,Row.scale,t,mul_comm] using monic_mul_leadingCoeff_inv fp.1
  have gp:G.primitive := Row.primitive_scale fp tn
  have gc:Controls G sheet c := control.scale tn
  have invariant (σ:E≃ₐ[K]E) : G.map σ.toRingHom=G :=
    unique_monic_control sheet e c gap initial gp ((Row.primitive_map σ.toRingHom).mpr gp)
      monic (monic.map σ.toRingHom) gc (gc.conjugate stable σ)
  obtain ⟨a,ha⟩:=polynomial_descent (K:=K) G.a (fun σ=>congrArg Row.a (invariant σ))
  obtain ⟨b,hb⟩:=polynomial_descent (K:=K) G.b (fun σ=>congrArg Row.b (invariant σ))
  let H:Row K:=⟨a,b⟩
  have actual:H.map (algebraMap K E)=G := by
    change Row.mk (a.map _) (b.map _) = G
    rw [ha,hb]
  refine ⟨H,(Row.primitive_map _).mp (actual ▸ gp),?_,actual ▸ gc⟩
  rw [←Row.degree_map (algebraMap K E) H,actual]
  exact Row.degree_scale F tn

#print axioms descend_control
end
end Research6966.Pade
