import ProximityPrize.SubmissionLower.KoalaAt2428Gate9Data

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate9
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 72).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem loss0 : lossChunk 1 envelope plain boxes 0 24 = 9721650112909 :=
  by decide +kernel

private theorem loss24 : lossChunk 1 envelope plain boxes 24 24 = 8484932988504 :=
  by decide +kernel

private theorem loss48 : lossChunk 1 envelope plain boxes 48 24 = 2639662418364 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20846245519777 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20846245519777 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9721650112909 loss0
      |>.append 24 8484932988504 loss24
      |>.append 24 2639662418364 loss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20846245519777,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate9

#print axioms KoalaAt2428Gate9.loss_bound
#print axioms KoalaAt2428Gate9.receipt
