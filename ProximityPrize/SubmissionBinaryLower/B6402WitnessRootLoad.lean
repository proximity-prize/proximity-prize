import ProximityPrize.SubmissionBinaryLower.B6402MissWitness
import ProximityPrize.SubmissionBinaryLower.B6402MissedFibres

/-! From the primary, regular-miss and exceptional-miss root orders to
vanishing on the original labelled polynomial. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402WitnessRootLoad
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402PrimarySystem
open B6402MissWitness B6402MissedFibres BCHKSSubstitutionVanish
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K I : Type*} [Field K] [CharP K 2] [Fintype I] [DecidableEq I]

theorem specialize_degree (w W : ℕ) (G : ContactPoly (Polynomial K)) (hw : wdeg w G≤W) (z : K) :
    wdeg w (evalZContact G z)≤W := by
  rw [wdeg_le_iff] at hw ⊢
  intro k j i hn
  apply hw k j i
  intro h
  apply hn
  simp [evalZContact,coeff_map,h]

theorem fitted {w W WF s d : ℕ} (x : K) (y : K[X]) (z : K) (P : K[X])
    (fc : KerDIdx w WF d → K[X]) (gc : KerDIdx w W s → K[X]) (V : LocalPoly (Polynomial K))
    (m : ℕ) (hc : twOrdGE (localized x y gc-localized x y fc*V) m)
    (onF : evalContact (evalZContact (∑ e,cC (fc e)*kerDBasisPoly e.1) z) P=0) (fit : P.eval x=y.eval z) :
    (Polynomial.X-C x)^(2*m) ∣ evalContact (evalZContact (∑ e,cC (gc e)*kerDBasisPoly e.1) z) P := by
  have h := pow_two_mul_dvd_evalLocal_of_twOrdGE x (y.eval z) P fit (twOrdGE_evalZLocal hc z)
  change (Polynomial.X-C x)^(2*m) ∣ evAt x y z P (localized x y gc - localized x y fc*V) at h
  rwa [map_sub,map_mul,ev_localized,ev_localized,onF,zero_mul,sub_zero] at h

theorem witness_vanish {w W WF s d : ℕ} (hw : 1≤w)
    (x : I ↪ K) (y : I → K[X]) (z : K) (P : K[X]) (hp : P.natDegree≤w)
    (fc : KerDIdx w WF d → K[X]) (gc : KerDIdx w W s → K[X]) (V : I → LocalPoly (Polynomial K))
    (F G : ContactPoly (Polynomial K)) (hf : F=∑ e,cC (fc e)*kerDBasisPoly e.1)
    (hg : G=∑ e,cC (gc e)*kerDBasisPoly e.1) (sF : F.natDegree=d) (sd : 1≤d)
    (sG : G.natDegree≤s) (hW : wdeg w G≤W)
    (marked fits : Finset I) (m b : ℕ) (hb : b≤m)
    (primary : ∀ i,twOrdGE (localized (x i) (y i) gc - localized (x i) (y i) fc*V i)
        (if i∈marked then m else m-b))
    (onF : evalContact (evalZContact F z) P=0) (fit : ∀ i∈fits,P.eval (x i)=(y i).eval z)
    (misses : ∀ i∈marked,i∉fits → (Polynomial.X-C (x i))^(2*b) ∣ evalContact (evalZContact G z) P)
    (budget : W<2*((m-b)*fits.card+b*marked.card)) :
    evalContact (evalZContact G z) P=0 ∧ triEval (resultant F G d s) z P=0 := by
  have hfit (i : I) (hi : i∈fits) :
      (Polynomial.X-C (x i))^(2*(if i∈marked then m else m-b)) ∣ evalContact (evalZContact G z) P := by
    rw [hg]
    exact fitted (x i) (y i) z P fc gc (V i) _ (primary i) (hf ▸ onF) (fit i hi)
  have he := (natDegree_evalContact_le w W hw (evalZContact G z) P hp (specialize_degree w W G hW z)).trans_lt budget
  have hg0 := zero_of_fit_and_miss x fits marked (evalContact (evalZContact G z) P) m b hb hfit misses he
  exact ⟨hg0,triEval_resultant_eq_zero F G d s sF.le sG (by omega) z P onF hg0⟩

#print axioms witness_vanish
end ProximityPrize.SubmissionBinaryLower.B6402WitnessRootLoad
