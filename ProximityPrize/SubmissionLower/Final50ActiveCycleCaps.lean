import ProximityPrize.SubmissionLower.Final50ActiveCycleBound
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low49ActiveSupport

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle
noncomputable section
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField genericCoeffs toGeneric)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (Exponent oldEmbedding)
open Final50Price (primaryBox taylorLength evenClip)
open Low48BentLattice (Cap Allowed Chamber)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily)
open Low49ActiveLattice (points Active)
open Low49ActiveSupport (Raw)
open MvPolynomial

def caps (p : Shape) : Fin 5 → Cap :=
  ![(p, 0), (primaryBox, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]




def baseClip (p : Shape) (K : ℕ) : ℕ := evenClip p 0 (p.b + p.j - K)

def graphClip (p : Shape) (K : ℕ) : ℕ :=
  evenClip ⟨p.b, p.j + 1, p.t + 1⟩ 1 (baseClip p K)

def liftClip (p : Shape) (K k : ℕ) : ℕ :=
  evenClip (lifted p k).1 (k + 1) (2 + k * (baseClip p K - 2))

def clips (p : Shape) (K : ℕ) : Fin 5 → ℕ :=
  ![baseClip p K, 498, graphClip p K, liftClip p K (taylorLength - 4),
    liftClip p K (taylorLength - 3)]










def activeFamily (p : Shape) (K : ℕ) : Family := fun i => points (caps p i) (clips p K i)

instance (p : Shape) (K : ℕ) (i : Fin 5) : Finite (activeFamily p K i) :=
  (Low49ActiveLattice.finite _ _).to_subtype



end
end Final50ActiveCycle
