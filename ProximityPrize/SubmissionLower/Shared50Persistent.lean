import ProximityPrize.SubmissionLower.Final50Order
set_option Elab.async false

namespace Shared50Persistent
noncomputable section

open P3 (K)
open K1_13 (Geom Row extend atJet shape InBox OrderAt)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder VanishesTo hasse_inBox hasse_atJet_eq_zero map_hassePartial)
open MvPolynomial Polynomial

/-- Include every admissible-width row that vanishes at the marked messages. -/
def vanishing (Γ : Finset K) (s : K → K[X]) : Submodule Geom (Row 4) where
  carrier := {P | P.totalDegree≤4012 ∧ ∀ γ ∈ Γ,atJet P (extend (s γ))=0}
  zero_mem' := ⟨by simp,fun _ _ => by simp [atJet]⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨(totalDegree_add p q).trans (max_le hp.1 hq.1),fun γ hγ => by
      simp only [atJet,map_add]
      change atJet p (extend (s γ))+atJet q (extend (s γ))=0
      rw [hp.2 γ hγ,hq.2 γ hγ,add_zero]⟩
  smul_mem' := by
    intro a p hp
    refine ⟨(totalDegree_smul_le a p).trans hp.1,fun γ hγ => ?_⟩
    change (MvPolynomial.eval _) (a • p)=0
    rw [Algebra.smul_def,map_mul]
    change _*atJet p (extend (s γ))=0
    rw [hp.2 γ hγ,mul_zero]

def Persistent (Γ : Finset K) (s : K → K[X]) (P : Ideal GeoJets) : Prop :=
  ∀ R ∈ vanishing Γ s,toGeneric R ∈ P

/-- Select one row for a finite set of nonpersistent surfaces. -/
theorem common_avoider (Γ : Finset K) (s : K → K[X]) (surfaces : Finset (Ideal GeoJets))
    (hZ : ∀ P ∈ surfaces, ¬ Persistent Γ s P) :
    ∃ R ∈ vanishing Γ s, ∀ P ∈ surfaces,toGeneric R ∉ P:=by
  classical
  let M:=vanishing Γ s
  let forbidden (P : surfaces) : Submodule Geom M :=
    ((P.val.comap (MvPolynomial.map K1_13_6.genericCoeffs):Ideal (Row 4)).restrictScalars Geom).comap M.subtype
  have hproper (P : surfaces) : forbidden P ≠ ⊤ := by
    intro h
    apply hZ P.val P.property
    intro R hR
    have hmem:(⟨R,hR⟩:M) ∈ forbidden P:=h ▸ Submodule.mem_top
    exact hmem
  obtain ⟨R,hR⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := ↥surfaces) (K:=Geom) (M:=M) forbidden hproper
  exact ⟨R.val,R.property,fun P hP => hR ⟨P,hP⟩⟩

theorem derivative_mem {Γ s P R n} (hp : Persistent Γ s P)
    (hb:InBox (shape R) Final50Price.primaryBox)
    (ho : ∀ γ ∈ Γ,OrderAt R (extend (s γ)) n)
    (a:Fin 4 →₀ ℕ) (ha:multiOrder a < n) :
    hassePartial a (toGeneric R) ∈ P:=by
  unfold toGeneric
  rw [← map_hassePartial]
  exact hp _ ⟨(hasse_inBox a hb).1,fun γ hγ => hasse_atJet_eq_zero ha (ho γ hγ)⟩

theorem local_order {Γ s R n} {P : Ideal GeoJets} [P.IsPrime] (hp : Persistent Γ s P)
    (hb:InBox (shape R) Final50Price.primaryBox)
    (ho : ∀ γ ∈ Γ,OrderAt R (extend (s γ)) n):VanishesTo P (toGeneric R) n :=
  K1_13_6_1_2_2.vanishesTo_of_hasse _ P n (fun a ha => derivative_mem hp hb ho a ha)

#print axioms common_avoider
#print axioms local_order
end
end Shared50Persistent
