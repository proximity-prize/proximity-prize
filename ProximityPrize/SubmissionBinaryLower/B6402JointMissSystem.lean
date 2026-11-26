import ProximityPrize.SubmissionBinaryLower.B6402RegularSystem
import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalInterpolation

/-! One map imposes all added equations on all order-two fibres. The columns
at exceptional fibres are indexed separately for each local ordinate degree. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402JointMissSystem
open Polynomial B6401ContactKerD B6401QuotInterp
open B6402SeedCoordinates B6402PrimarySystem B6402ExceptionalSystem
open B6402ExceptionalSupport B6402ExceptionalInterpolation
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K Reg Bad V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
variable {w W s q T : ℕ}

abbrev Columns (Bad : Type*) (s J T H b : ℕ) (d : Bad → ℕ) :=
  Σ i : Bad, Σ a : Fin b, ↥(auxBox s J T H (d i) a.val)

abbrev Targets (Reg Bad : Type*) (s m b J T H : ℕ) :=
  (Reg × B6402RegularSystem.Tests m s b J (T+s*H)) ⊕
    (Σ _i : Bad, Σ a : Fin b, ↥(testBox s J T H a.val))

abbrev Unknowns (K Reg Bad V : Type*) (w W s q T H b J : ℕ) (d : Bad → ℕ) :=
  (Global K w W s q T × V) × (Columns Bad s J T H b d → K)

private noncomputable def badProj (s J T H b : ℕ) (d : Bad → ℕ) (i : Bad) :
    (Columns Bad s J T H b d → K) →ₗ[K] ACols K s J T H (d i) b :=
  LinearMap.pi fun j => LinearMap.pi fun t => LinearMap.proj ⟨i,j,t⟩

variable (F : ContactPoly (Polynomial K)) (rx : Reg → K) (ry : Reg → K[X])
variable (bx : Bad → K) (byv : Bad → K[X]) (bf : Bad → (Fibre K)[X]) (a L : Bad → Fibre K)
variable (m b J H : ℕ) (d : Bad → ℕ)

noncomputable def joint :
    Unknowns K Reg Bad V w W s q T H b J d →ₗ[K] (Targets Reg Bad s m b J T H → K) :=
  let get := (LinearMap.fst K (Global K w W s q T) V).comp (LinearMap.fst K _ (Columns Bad s J T H b d → K))
  LinearMap.pi fun r => match r with
    | .inl (i,j) => (LinearMap.proj j).comp <|
        (B6402RegularSystem.equations F (rx i) (ry i) m b J (T+s*H)).comp get
    | .inr ⟨i,j,t⟩ => (LinearMap.proj t).comp <| (LinearMap.proj j).comp <|
        (tests (bf i) (a i) (L i) (localSource (bx i) (byv i))).comp <|
          get.prod ((badProj s J T H b d i).comp (LinearMap.snd K _ _))

theorem all_regular (u : Unknowns K Reg Bad V w W s q T H b J d)
    (zero : joint F rx ry bx byv bf a L m b J H d u=0) (i : Reg) :
    B6402RegularSystem.equations F (rx i) (ry i) m b J (T+s*H) u.1.1=0 := by
  funext j
  exact congrFun zero (.inl (i,j))

theorem all_exceptional (u : Unknowns K Reg Bad V w W s q T H b J d)
    (zero : joint F rx ry bx byv bf a L m b J H d u=0) (i : Bad) :
    tests (bf i) (a i) (L i) (localSource (bx i) (byv i))
      (u.1.1, badProj s J T H b d i u.2)=0 := by
  funext j t
  exact congrFun zero (.inr ⟨i,j,t⟩)

theorem no_extra_kernel (z : Columns Bad s J T H b d → K)
    (zero : joint (V:=V) (w:=w) (W:=W) (q:=q) F rx ry bx byv bf a L m b J H d ((0,0),z)=0)
    (hH : H≤T) (hd : ∀ i,d i≤J) (hLne : ∀ i,L i≠0)
    (hF : ∀ i j, Bounds ((bf i).coeff (j+1)) (3*(j+1)) 5 H)
    (ha : ∀ i, Bounds (a i) 0 5 0) (hL : ∀ i, Bounds (L i) 0 (d i) H) : z=0 := by
  funext r; rcases r with ⟨i,j,t⟩
  let g := localSource (w:=w) (W:=W) (s:=s) (q:=q) (T:=T) (bx i) (byv i)
  have hz := all_exceptional F rx ry bx byv bf a L m b J H d ((0,0),z) zero i
  have hG (j : ℕ) : Bounds ((g 0).coeff j) (s+3*j) J T := by
    simp only [map_zero,coeff_zero]
    exact (in_box _ _ _ _).mp (Submodule.zero_mem _)
  have hv := unique_aux (bf i) (a i) (L i) g (0,badProj s J T H b d i z)
    hH (hd i) (hLne i) (hF i) (ha i) (hL i) hG hz g.map_zero
  exact congrFun (congrFun hv j) t

#print axioms no_extra_kernel
end ProximityPrize.SubmissionBinaryLower.B6402JointMissSystem
