import Mathlib.RingTheory.AdicCompletion.Completeness
import ProximityPrize.SubmissionLower.ZaLaX1b
set_option Elab.async false
open _root_ renaming Ideal.Quotient.mk → zVv, Ideal.mul_mem_right → zx6, Ideal.neg_mem_iff → z0X, Ideal.one_eq_top → zjK, Ideal.pow_le_pow_right → zdr, Ideal.smul_eq_mul → zHM, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂_mul → zR5, MvPolynomial.pderiv → zWe, Polynomial.X → z7y, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8
namespace qz11UBb
noncomputable section
open Polynomial
open scoped Polynomial Ring
open cu (L)
private theorem liftRoot {R:Type*} [CommRing R] {I:Ideal R} [IsAdicComplete I R]
    (f :R[X]) (a₀:R) (h₁:f.eval a₀∈I)
    (h₂:IsUnit (zVv I (f.derivative.eval a₀))) :
    ∃ a,f.eval a=0∧a-a₀∈I:= by
  let c:ℕ→R:= fun n=>Nat.recOn n a₀
    fun _ b=>b - f.eval b*(f.derivative.eval b)⁻¹ʳ
  have hc (n:ℕ) :c (n+1)=c n - f.eval (c n)*(f.derivative.eval (c n))⁻¹ʳ:=rfl
  have hm (n:ℕ) :c n ≡ a₀ [SMOD I] := by
    induction n with
    | zero=>rfl
    | succ n ih =>
      rw [hc,sub_eq_add_neg,← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero,z0X]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hu (n:ℕ) :IsUnit (f.derivative.eval (c n)) := by
    have :=isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (zVv I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hm n).eval _)
  have hf (n:ℕ) :f.eval (c n)∈I^(n+1) := by
    induction n with
    | zero =>
      change f.eval a₀∈I^1
      simpa only [pow_one] using h₁
    | succ n ih =>
      let e :=f.eval (c n)*(f.derivative.eval (c n))⁻¹ʳ
      have he :e∈I^(n+1) :=zx6 _ _ ih
      obtain ⟨b,hb⟩:=exists_mul_sq_add_linear_part_eq_eval_add f (c n) (-e)
      have hcancel:f.eval (c n)+f.derivative.eval (c n)*(-e)=0:= by
        dsimp [e]
        rw [mul_neg,mul_left_comm,Ring.mul_inverse_cancel _ (hu n),mul_one,add_neg_cancel]
      rw [hc,sub_eq_add_neg]
      change f.eval (c n + -e)∈_
      rw [← hb,add_assoc (b*(-e)^2),add_comm (f.derivative.eval (c n) * -e),hcancel,add_zero]
      refine Ideal.mul_mem_left _ _ (zdr (show n+1+1≤(n+1)*2 by omega) ?_)
      rw [pow_mul]
      exact Ideal.pow_mem_pow ((z0X _).mpr he) 2
  have hstep (n:ℕ) :c n ≡ c (n+1) [SMOD (I^n:Ideal R)] := by
    rw [hc]
    apply SModEq.sub_mem.mpr
    simpa only [sub_sub_cancel] using
      zdr (Nat.le_succ n) (zx6 _ _ (hf n))
  have hchain (m n:ℕ) (h:m≤n) :c m ≡ c n [SMOD (I^m • ⊤ : Ideal R)] := by
    rw [← zjK,zHM,mul_one]
    induction n,h using Nat.le_induction with
    | base=>rfl
    | succ n h ih =>
      refine ih.trans ?_
      apply SModEq.sub_mem.mpr
      exact zdr h (SModEq.sub_mem.mp (hstep n))
  obtain ⟨a,ha⟩:=IsPrecomplete.prec' c (hchain _ _)
  refine ⟨a,?_,?_⟩
  · apply IsHausdorff.haus' (I:=I)
    intro n
    have hh:=(ha n).symm.eval f
    rw [← zjK,zHM,mul_one] at hh ⊢
    exact hh.trans (SModEq.zero.mpr (zdr (Nat.le_succ n) (hf n)))
  · have hh:=(ha 1).symm
    rw [← zjK,zHM,mul_one,pow_one] at hh
    exact SModEq.sub_mem.mp (hh.trans (hm 1))
private theorem deriv_eval₂ {R S:Type*} [CommRing R] [CommRing S]
    (φ:R →+* S) (f :MvPolynomial (Fin 2) R) (i:Fin 2) (s :Fin 2→S) :
    (zSZ (C.comp φ) (fun j=>if j=i then z7y else C (s j)) f).derivative =
      zSZ (C.comp φ) (fun j=>if j=i then z7y else C (s j))
        (zWe i f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp
  | add a b ha hb =>
    simp only [MvPolynomial.eval₂_add,map_add,ha,hb]
  | mul_X a j ha =>
    by_cases hj:j=i
    · subst j
      simp [zR5,derivative_mul,Derivation.leibniz,ha,mul_comm]
    · simp [zR5,derivative_mul,Derivation.leibniz,ha,hj,mul_comm]
theorem formalLift:q1vkLGd.FormalLift:= by
  intro q z i hz hi
  let s (j:Fin 2) :zpm L:=zMG (z j)+PowerSeries.X
  let e :=zOD (C.comp zMG)
    (fun j=>if j=i then z7y else C (s j))
  let f :=e q
  let a (t:zpm L) (j:Fin 2) :=if j=i then t else s j
  have ev (g:qQ9yWTb.Curve) (t:zpm L) :
      (e g).eval t=zSZ zMG (a t) g:= by
    have he : (evalRingHom t).comp e=zOD zMG (a t) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [e]
      · intro j
        by_cases hj:j=i <;> simp [e,a,hj]
    exact DFunLike.congr_fun he g
  have ac (j:Fin 2) :zbO (a (zMG (z i)) j)=z j:= by
    by_cases hj:j=i
    · simp [a,hj]
    · simp [a,s,hj]
  have residue (g:qQ9yWTb.Curve) :
      zbO ((e g).eval (zMG (z i)))=MvPolynomial.eval z g:= by
    rw [ev,MvPolynomial.hom_eval₂]
    simp [ac,show PowerSeries.constantCoeff.comp (zMG (R:=L))=RingHom.id L from
      RingHom.ext zr8]
  let I:Ideal (zpm L) := .span {PowerSeries.X}
  have hI:RingHom.ker (zbO (R:=L))=I :=
    PowerSeries.ker_coeff_eq_max_ideal.trans PowerSeries.maximalIdeal_eq_span_X
  have h₁:f.eval (zMG (z i))∈I:= by
    rw [← hI,RingHom.mem_ker,residue,hz]
  have h₂:IsUnit (zVv I (f.derivative.eval (zMG (z i)))) := by
    apply IsUnit.map
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    change zbO (((e q).derivative).eval (zMG (z i)))≠0
    have hder : (e q).derivative=e (zWe i q) :=deriv_eval₂ _ _ _ _
    rw [hder,residue]
    exact hi
  obtain ⟨t,ht,ht'⟩:=liftRoot f (zMG (z i)) h₁ h₂
  rw [← hI,RingHom.mem_ker,map_sub,zr8,sub_eq_zero] at ht'
  refine ⟨a t,fun j => ?_,(ev q t).symm.trans ht,fun j hj=>ite_eq_right hj⟩
  by_cases hj:j=i <;> simp [a,s,hj,ht']
end
end qz11UBb
