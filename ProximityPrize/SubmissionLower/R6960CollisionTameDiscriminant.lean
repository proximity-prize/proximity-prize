import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.LinearAlgebra.Matrix.BilinearForm
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Matrix
open scoped Matrix BigOperators Pointwise
section Gram
variable {A M ι : Type*} [CommRing A] [AddCommMonoid M] [Module A M] [Fintype ι] [DecidableEq ι]
def tupleGram (tr : LinearMap.BilinForm A M) (u : ι→M) : Matrix ι ι A :=
  fun i j=>tr (u i) (u j)
def gramIdeal (tr : LinearMap.BilinForm A M) : Ideal A :=
  Ideal.span (Set.range (fun u : ι→M=>(tupleGram tr u).det))
theorem gramIdeal_mem (tr : LinearMap.BilinForm A M) (u : ι→M) :
    (tupleGram tr u).det∈gramIdeal (ι:=ι) tr := Ideal.subset_span ⟨u,rfl⟩
omit [Fintype ι] [DecidableEq ι] in
theorem tupleGram_smul (tr : LinearMap.BilinForm A M) (u : ι→M) (g : A) :
    tupleGram tr (fun i=>g • u i)=g^2 • tupleGram tr u := by
  apply Matrix.ext
  intro i j
  change tr (g • u i) (g • u j)=g^2*tr (u i) (u j)
  rw [tr.map_smul,LinearMap.smul_apply,(tr (u i)).map_smul]
  simp only [smul_eq_mul]
  ring
omit [DecidableEq ι] in
theorem tupleGram_change (tr : LinearMap.BilinForm A M) (u : ι→M) (T : Matrix ι ι A) :
    tupleGram tr (fun j=>∑ i,T i j • u i)=T.transpose*tupleGram tr u*T := by
  rw [mul_assoc]
  apply Matrix.ext
  intro i j
  simp only [tupleGram,Matrix.mul_apply,Matrix.transpose_apply,map_sum,LinearMap.sum_apply,
    LinearMap.map_smul,LinearMap.smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum,mul_comm (T _ j)]
  exact Finset.sum_comm
theorem gramIdeal_clear (tr : LinearMap.BilinForm A M) (u : ι→M) (g : A)
    (clear : ∀ x : M,∃ t : ι→A,∑ i,t i • u i=g • x) :
    ∀ a∈gramIdeal (ι:=ι) tr, (tupleGram tr u).det∣g^(2*Fintype.card ι)*a := by
  let I := Ideal.span ({(tupleGram tr u).det} : Set A)
  have witnesses : gramIdeal (ι:=ι) tr ≤ Submodule.comap (LinearMap.mul A A (g^(2*Fintype.card ι))) I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    change g^(2*Fintype.card ι)*(tupleGram tr v).det∈I
    choose t ht using fun j=>clear (v j)
    let T : Matrix ι ι A := fun i j=>t j i
    have eq : tupleGram tr (fun j=>g • v j)=T.transpose*tupleGram tr u*T := by
      rw [←tupleGram_change tr u T]
      exact congrArg (tupleGram tr) (funext fun i=>(ht i).symm)
    rw [tupleGram_smul] at eq
    have det := congrArg Matrix.det eq
    rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,←pow_mul] at det
    change g^(2*Fintype.card ι)*(tupleGram tr v).det∈Ideal.span {(tupleGram tr u).det}
    rw [det,Ideal.mem_span_singleton]
    exact ⟨T.det^2,by ring⟩
  intro a ha
  exact Ideal.mem_span_singleton.mp (witnesses ha)
theorem gramIdeal_basis (tr : LinearMap.BilinForm A M) (b : Module.Basis ι A M) :
    gramIdeal (ι:=ι) tr=Ideal.span {(tupleGram tr b).det} := by
  apply le_antisymm
  · intro a ha
    apply Ideal.mem_span_singleton.mpr
    have h := gramIdeal_clear tr b 1 (fun x=>⟨b.equivFun x,by
      rw [one_smul]
      exact (b.equivFun_symm_apply (b.equivFun x)).symm.trans (b.equivFun.symm_apply_apply x)⟩) a ha
    simpa only [one_pow,one_mul] using h
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (gramIdeal_mem tr b)
end Gram
section Principal
variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [IsNoetherianRing A]
omit [IsDomain A] in
theorem principal_of_clears (I : Ideal A)
    (patch : ∀ (P : Ideal A),P.IsMaximal→∃ (g d : A) (n : ℕ),g∉P ∧ d∈I ∧
      ∀ a∈I,d∣g^n*a) : I.IsPrincipal := by
  classical
  let : NormalizedGCDMonoid A := Classical.arbitrary _
  obtain ⟨G,hG⟩ := IsNoetherian.noetherian I
  let δ := G.gcd id
  have divides : I≤Ideal.span {δ} := by
    rw [←hG]
    apply Ideal.span_le.mpr
    exact fun _ h=>Ideal.mem_span_singleton.mpr (Finset.gcd_dvd h)
  have δmem : δ∈I := by
    by_contra notmem
    let J : Ideal A := Submodule.comap (LinearMap.mul A A δ) I
    have proper : J≠⊤ := by
      intro all
      have h : (1:A)∈J := all.symm ▸ Submodule.mem_top
      change δ*1∈I at h
      exact notmem (by simpa only [mul_one] using h)
    obtain ⟨P,hP,JP⟩ := Ideal.exists_le_maximal J proper
    obtain ⟨g,d,n,gn,dI,h⟩ := patch P hP
    have each : d∣G.gcd (fun r=>g^n*r) := Finset.dvd_gcd_iff.mpr fun a ha=>
      h a (hG ▸ Ideal.subset_span ha)
    have δdiv : d∣g^n*δ := each.trans (Finset.gcd_mul_left' (s:=G) (f:=id) (g^n)).dvd
    have inside : g^n∈J := by
      change δ*g^n∈I
      rw [mul_comm]
      obtain ⟨c,hc⟩ := δdiv
      rw [hc]
      exact I.mul_mem_right c dI
    exact gn (hP.isPrime.mem_of_pow_mem _ (JP inside))
  exact ⟨δ,le_antisymm divides ((Ideal.span_singleton_le_iff_mem _).mpr δmem)⟩
end Principal
#print axioms gramIdeal_clear
#print axioms principal_of_clears
end
end Lower6960.CollisionTame
