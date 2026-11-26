import ProximityPrize.SubmissionBinaryLower.B6402PrimarySystem

/-! Interpolate over the original seed field. A surplus counts all primary
coefficients, extra missed-fibre rows and their auxiliary columns together. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402CombinedInterpolation
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402SeedCoordinates B6402QuotientSpace B6402PrimarySystem B6402QuotientDimension
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K ι β ε : Type*} [Field K] [CharP K 2] [Fintype ι] [Fintype β] [Fintype ε]
variable {w W WF s d q T H : ℕ}

theorem interpolate (hw : 0<w) (hd : d≤s) (hH : H≤T)
    (m k : ι → ℕ) (x : ι → K) (y : ι → K[X]) (hy : ∀ i, (y i).natDegree≤q)
    (fc : KerDIdx w WF d → K[X]) (F : ContactPoly (Polynomial K))
    (hF : F=∑ e,cC (fc e)*kerDBasisPoly e.1) (height : B6402MixedDegree.mixed q F≤H)
    (hirr : Irreducible F) (hR : 0<F.natDegree) (dF : contactDeriv F=0)
    (hirrK : Irreducible (liftCRat F))
    (ord : ∀ i, twOrdGE (localized (x i) (y i) fc) (k i))
    (exactOrd : ∀ i, ∃ a b, a+b=k i ∧ twCoeff (localized (x i) (y i) fc) a b ≠ 0)
    (extra : ((Global K w W s q T × Aux K m k s d q T H) × (β → K)) →ₗ[K] (ε → K))
    (extra_unique : ∀ z, extra ((0,0),z)=0 → z=0)
    (surplus : (∑ i, Fintype.card (Seeds (m i) s q T)) + Fintype.card ε +
        Fintype.card (Slots w (W-wdeg w F) (s-F.natDegree) q (T-B6402MixedDegree.mixed q F)) <
        Fintype.card (Slots w W s q T) +
        (∑ i, Fintype.card (Seeds (m i-k i) (s-d) q (T-H))) + Fintype.card β) :
    ∃ (u : Global K w W s q T) (v : Aux K m k s d q T H) (z : β → K),
      extra ((u,v),z)=0 ∧ resultant F (source q T u) F.natDegree s≠0 ∧
      (∀ i, twOrdGE (localized (x i) (y i) (decode (width q T) u) -
         localized (x i) (y i) fc*multiplier (decode (localWidth q (T-H)) (v i))) (m i)) ∧
      contactDeriv (source q T u)=0 ∧ (source q T u).natDegree≤s ∧
        wdeg w (source q T u)≤W ∧ B6402MixedDegree.mixed q (source q T u)≤T := by
  classical
  let rows := ((primary m k x y fc).comp (LinearMap.fst K _ (β → K))).prod extra
  let out := (LinearMap.fst K (Global K w W s q T) (Aux K m k s d q T H)).comp (LinearMap.fst K _ (β → K))
  have hfc := hF ▸ height
  have unique : ∀ a, rows a=0 → out a=0 → a=0 := by
    rintro ⟨⟨u,v⟩,z⟩ hz hu
    have hp : primary m k x y fc (u,v)=0 := congrArg Prod.fst hz
    have he : extra ((u,v),z)=0 := congrArg Prod.snd hz
    change u=0 at hu
    have hv : v=0 := zero_aux m k x y fc hw hd hH hy hfc ord exactOrd (u,v) hp hu
    subst u; subst v
    have hh := extra_unique z he
    subst z; rfl
  have hdim : Module.finrank K (Rows K m s q T × (ε → K)) +
      Module.finrank K (Global K w (W-wdeg w F) (s-F.natDegree) q (T-B6402MixedDegree.mixed q F)) <
      Module.finrank K ((Global K w W s q T × Aux K m k s d q T H) × (β → K)) := by
    simpa only [Rows,Global,Aux,Module.finrank_prod,Module.finrank_pi,Module.finrank_pi_fintype] using surplus
  obtain ⟨⟨⟨u,v⟩,z⟩,hz,hout⟩ := exists_outside_multiples rows out (multiples F w W s q T) unique hdim
  have hp : primary m k x y fc (u,v)=0 := congrArg Prod.fst hz
  exact ⟨u,v,z,congrArg Prod.snd hz,proper_resultant F w W s q T hw hirr hR dF hirrK u hout,
    kernel_contact m k x y fc hw hd hH hy hfc (u,v) hp,source_bounds hw u⟩

#print axioms interpolate
end ProximityPrize.SubmissionBinaryLower.B6402CombinedInterpolation
