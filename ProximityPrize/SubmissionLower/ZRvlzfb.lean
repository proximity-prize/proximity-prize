import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option Elab.async false
open _root_ renaming Polynomial → zM1, Polynomial.derivative_map → zU4, Polynomial.eval_map_apply → zdm, PowerSeries → zpm, PowerSeries.constantCoeff_C → zr8
set_option autoImplicit true
namespace qYzLClc
noncomputable section
open Polynomial
variable {F:Type*} [Field F]
local notation "T" => (PowerSeries.X:PowerSeries F)
local notation "ct" => (PowerSeries.constantCoeff :PowerSeries F →+* F)
private def newton (p:zM1 (zpm F)) (x :zpm F) :zpm F :=
  x-(p.derivative.eval x)⁻¹*p.eval x
private theorem newton_step (p:zM1 (zpm F)) (x :zpm F) (n:ℕ)
    (h:T^(n+1)∣p.eval x) (hd:ct (p.derivative.eval x)≠0) :
    (T^(n+1)∣newton p x - x)∧(T^(n+2)∣p.eval (newton p x)) := by
  let y := -((p.derivative.eval x)⁻¹*p.eval x)
  have hy :T^(n+1)∣y :=dvd_neg.mpr (dvd_mul_of_dvd_right h _)
  have hxy :newton p x=x+y :=sub_eq_add_neg ..
  have hlin:p.derivative.eval x*y+p.eval x=0:= by
    dsimp [y]
    rw [mul_neg,← mul_assoc,PowerSeries.mul_inv_cancel _ hd,one_mul,neg_add_cancel]
  obtain ⟨c,hc⟩:=p.exists_mul_sq_add_linear_part_eq_eval_add x y
  refine ⟨by simpa [hxy] using hy,?_⟩
  rw [hxy,← hc,add_assoc,hlin,add_zero]
  apply dvd_mul_of_dvd_right
  apply dvd_trans (pow_dvd_pow T (show n+2≤(n+1)*2 by omega))
  rw [pow_mul]
  exact pow_dvd_pow_of_dvd hy 2
theorem lift_root (p:zM1 (zpm F)) (a :F)
    (h: (p.map ct).eval a=0) (hd: (p.map ct).derivative.eval a≠0) :
    ∃ x :zpm F,ct x=a∧p.eval x=0:= by
  let f :ℕ→zpm F:=Nat.rec (PowerSeries.C a) fun _ x=>newton p x
  have hf (n:ℕ) :ct (f n)=a∧T^(n+1)∣p.eval (f n) := by
    induction n with
    | zero =>
      refine ⟨zr8 _,?_⟩
      rw [zero_add,pow_one,PowerSeries.X_dvd_iff]
      change ct (p.eval (PowerSeries.C a))=0
      rwa [← zdm ct,zr8]
    | succ n ih =>
      have hd' : ct (p.derivative.eval (f n))≠0:= by
        rwa [← zdm ct,ih.1,← zU4]
      obtain ⟨hs,ht⟩:=newton_step p (f n) n ih.2 hd'
      have hX:T∣f (n+1) - f n:= by
        simpa only [pow_one] using (pow_dvd_pow T (show 1≤n+1 by omega)).trans hs
      have hz :=PowerSeries.X_dvd_iff.mp hX
      rw [map_sub,sub_eq_zero] at hz
      exact ⟨hz.trans ih.1,ht⟩
  have hs (n:ℕ) :T^(n+1)∣f (n+1) - f n:= by
    apply (newton_step p (f n) n (hf n).2 ?_).1
    rwa [← zdm ct,(hf n).1,← zU4]
  let I:Ideal (zpm F) :=Ideal.span {T}
  have congr_dvd {n:ℕ} {x y :zpm F} :
      x ≡ y [SMOD (I^n • ⊤ : Submodule (zpm F) (zpm F))]↔T^n∣x-y := by
    simp only [I,SModEq.sub_mem,smul_eq_mul,Ideal.mul_top,Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hC {m n:ℕ} (hmn:m≤n) :
      f m ≡ f n [SMOD (I^m • ⊤ : Submodule (zpm F) (zpm F))] := by
    induction n,hmn using Nat.le_induction with
    | base=>rfl
    | succ n hmn ih =>
      exact ih.trans (congr_dvd.mpr ((pow_dvd_pow T (by omega)).trans (hs n))).symm
  obtain ⟨x,hx⟩:=(inferInstance :IsPrecomplete I (zpm F)).prec hC
  have hx0:=PowerSeries.X_dvd_iff.mp (by simpa only [pow_one] using (congr_dvd.mp (hx 1)))
  rw [map_sub,sub_eq_zero,(hf 1).1] at hx0
  refine ⟨x,hx0.symm,PowerSeries.ext fun n => ?_⟩
  have hdif :=(congr_dvd.mp (hx (n+1)).symm).trans (Polynomial.sub_dvd_eval_sub x (f (n+1)) p)
  have hp:=(pow_dvd_pow T (Nat.le_succ (n+1))).trans (hf (n+1)).2
  have hz :T^(n+1)∣p.eval x := by
    simpa using dvd_add hdif hp
  simpa using PowerSeries.X_pow_dvd_iff.mp hz n (Nat.lt_succ_self n)
end
end qYzLClc
