import ProximityPrize.SubmissionLower.ZlPdtnc
import ProximityPrize.SubmissionLower.Ztdy5wb
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qXmh4Jb
noncomputable section
open Polynomial Finset
open P5 (K p dw)
open P5_7_1 (Input degree)
open qHEUR1a (quota weight)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel)
open qkgz7gb (UJ)
open P5_7_3_5_2 (Sheet BranchBudget)


open scoped Classical BigOperators
def c3:Prop :=
  ∀ {q:Curve} {C:CurveModel q} {z :K→K} {s :K→K[X]}
    (S:Sheet C z s) (D e W:ℕ),0<D→2≤S.d→S.d≤e→e<p→e*D ≤W →
    (2*e-1)*W-e^2*D <p→S.weight D W→(∀ γ∈S.marks,(s γ).natDegree≤D) →
    BranchBudget S D (6+2*e) ((6*e-2)*W-3*e^2*D)
def c4 :Prop :=
  ∀ {q:Curve} {C:CurveModel q} {z :K→K} {s :K→K[X]}
    (S:Sheet C z s) (D W:ℕ),0<D→D ≤W→S.d = 1 →
    S.weight D W→(∀ γ∈S.marks,(s γ).natDegree≤D) →
    BranchBudget S D 0 (2*W-D)
private theorem marks (x :Input) (T:Finset K) (hT:T⊆x.Γ) :
    UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,?_,?_,?_⟩
  · intro γ hγ
    exact (P5_7_1.aic (hT hγ)).trans
      (Nat.add_le_add_left (P5_7_1.emz x).2 _)
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(show quota≤dw by decide).trans m.bad.dw,m.scalar_hits⟩
  · obtain ⟨P⟩:=P5_7_1.poles x
    exact ⟨x.h,(show 0<P5_7_1.lo by decide).trans_le (P5_7_1.emz x).1,
      P.D,fun γ hγ=>P.marks γ (hT hγ)⟩
end
end qXmh4Jb
end
section
set_option autoImplicit true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace qXrbKzb
open P5_7_2 (fO)
open qoK3iCb (BandWitness)

open scoped qoK3iCb
private abbrev b:fO:=⟨9,by decide⟩
private def data :ℕ:=0x39000a0059937e3c39024214291ab4a43900f2088f5bd3543940020010eaffac498002000d2b2f5c31000a00638a172531024216238a4c8f3100f20926a6fc10310002001273bb13418002000e64e0f441400a004ecff039394242120d9ecb163940f207ee7d2292394062033537de99498002000e04e20839000a005a4e624c390242145054f3f23100f2089b28e76839403201a399c1cc4980320146c3ff0a41400a004c1bb6c041424211844b80713940f207c577f7fa41403201755ac71a51c032012185cd503940320194123004397873cd0cebfba03957a2c92f755fcc4980320144bb3f0862003200fd1991364140320175a79b1d417873af2c2b86f63957a2c0459ef6224140320171d8a3f959c032011ea7cf7a4980320150c6e9fa49b8738ad3d5fcec4157a2b56cabe1c059c03201198f964a72403200da4e1cc8414032018057450c417873b9b13ed0f83940320192038e8259c032011c28e17272403200dd9c9f354140320184ba4ef2417873be0460e080498032014cf0f5c06a403200eed3b12e82c03200bb2a38b65180320137ecafc449b873725788150c59c0320120475e327a803200c9840a1aa34032009c92cc71518032013caef35d49b8737706ed29de518032013a6b3eb272403200db50ea5993003200aa47a3325a0032010e3acf2f59c03201118acad272403200e2b247caa34032009e31fc5fcc4032007ad7c6d0
private theorem w:BandWitness b:=witnesses!
theorem band9:y8 b 5:=grid_of_tests (data :=data) w (by
  intro o t
  fin_cases o <;> fin_cases t <;> (exact az (.inl checked!)))
end qXrbKzb
end
