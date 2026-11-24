import ProximityPrize.SubmissionLower.Z7r9bnb
import ProximityPrize.SubmissionLower.ZbnhR9d
import ProximityPrize.SubmissionLower.ZXfrSsa
set_option Elab.async false
set_option autoImplicit true
namespace q1yhP8b
noncomputable section
open qFAh60c (width)
open aR (ao Shape jF)
open jA
open NR (Lq TT amn O8 aVU)
open qzLARrc (windowBudget oneDebit)
open private simple_bound from ProximityPrize.SubmissionLower.ZrgYIVd
open private cFT bCP from ProximityPrize.SubmissionLower.DG
open private bDY from ProximityPrize.SubmissionLower.E2
open scoped Polynomial BigOperators
def c1 :Prop :=qzLARrc.c2
def c2 :Prop :=qzLARrc.c3
private theorem separable (h1 :c1) (a :Shape) (U r :ℕ)
    (hU:a.b≤U) (hbudget:windowBudget a U≤ r)
    {Γ s} (P:jF Γ s) (L:kH P)
    (V:Submodule ao jK) [Module.Finite ao V]
    (hcap : ∀ F∈V,Jn a F∧gY F≤U) (hsep:P.H.Separable) :
    TT V (amn P L a (jH P.H))≤P.H.natDegree*r := by
  classical
  let T:Finset ao:=⟨P.H.roots,Polynomial.nodup_roots hsep⟩
  have hcard:T.card=P.H.natDegree :=IsAlgClosed.card_roots_eq_natDegree
  have hroot (α:ao) (hα:α∈T) :P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod: (∏ α∈T,O8 α)=jH P.H := by
    have he : (∏ α∈T,(Polynomial.X-Polynomial.C α))=P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _=Polynomial.mapRingHom (algebraMap ao kS) P.H
    rw [← he,map_prod]
    simp [O8]
  let W:ao→Submodule ao jK:= fun α=>amn P L a (O8 α)
  have hlocal (α:ao) (hα:α∈T) :TT V (W α)≤ r :=
    simple_bound qxRGmlc.proof h1 a U r hU hbudget P L α V hcap (hroot α hα)
      (hsep.eval₂_derivative_ne_zero (RingHom.id ao) (hroot α hα))
  have hsub:T.inf W≤amn P L a (jH P.H) := by
    intro F hF
    have hcop:=Polynomial.pairwise_coprime_X_sub_C
      (FaithfulSMul.algebraMap_injective ao kS)
    have h:=Finset.prod_dvd_of_coprime (t:=T)
      (s := fun α=>(MvPolynomial.C (O8 α) :Lq)^(a.b+a.j))
      (fun α _ β _ hne=>(IsCoprime.map (f :=MvPolynomial.C) (hcop hne)).pow)
      (fun α hα=>(aVU P L a _ _).mp
        ((Finset.inf_le hα:T.inf W≤W α) hF))
    rw [Finset.prod_pow,← map_prod MvPolynomial.C,hprod] at h
    exact (aVU P L a _ _).mpr h
  have hdim:=bCP V T W r hlocal
  rw [hcard] at hdim
  exact (cFT V hsub).trans hdim
theorem of_children (h1 :c1) (h2 :c2) :qFAh60c.c3:= by
  intro x P b V hV hcap
  let:Module.Finite ao V:=hV
  have hb:windowBudget b.box b.U≤oneDebit b:= by
    cases b
    · exact h2
    · exact qYzmxYc.proof
  let r :=(width b+1)*b.basePole+b.poleExcess
  have h:=bDY _ _ P.data P.bY b.box V (P.data.H.natDegree*r) hV
    (fun P' L' _ hdeg hsep=>hdeg ▸
      separable h1 b.box (width b) r (width_ge_box b) (resized_budget b hb) P' L' V hcap hsep)
  rw [P.height] at h
  exact h
end
end q1yhP8b
