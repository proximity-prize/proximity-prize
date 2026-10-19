/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.BinaryCodegen
import VCVio.OracleComp.RunIO

/-!
# Executed binary Toy IOP regressions

Use the production field, sampler, and a restriction of the production domain.
Small code dimensions exercise encoding, proving, verification, and extraction
without evaluating a production-size witness. Uniformity is proved separately;
the deterministic sampler trace checks limb count, range, and coefficient order.

Run with `lake env lean --run scripts/BinaryToyRuntime.lean`.
-/

namespace BinaryToyRuntime

open OracleSpec ProtocolSpec
open ToyProblem.Impl.IRS
open ProximityPrize.Benchmark

abbrev Field := BinaryIRSProfile.Field

def word (n : Nat) : BF64 := BF64.ofBitVec (BitVec.ofNat 64 n)

def fieldWord (n : Nat) : Field := CompPoly.Extension.Ext.ofBase (word n)

def testDomain : Fin 4 ↪ Field where
  toFun i := BinaryIRSProfile.domain ⟨i.val, by omega⟩
  inj' := by
    intro i j hij
    have h := BinaryIRSProfile.domain.injective hij
    exact Fin.ext (congrArg (fun z : BinaryIRSProfile.Index => z.val) h)

theorem two_dvd_four : 2 ∣ 4 := by decide

def messageOne : Fin 4 → Field :=
  ![fieldWord 1, fieldWord 2, fieldWord 3, fieldWord 4]

def messageTwo : Fin 4 → Field :=
  ![fieldWord 4, fieldWord 3, fieldWord 2, fieldWord 1]

def encodedOne := encoder 4 2 two_dvd_four testDomain messageOne

def encodedTwo := encoder 4 2 two_dvd_four testDomain messageTwo

def constraint : Fin 4 → Field :=
  ![fieldWord 3, fieldWord 5, fieldWord 7, fieldWord 9]

def inputStatement : ToyProblem.Spec.Statement (F := Field) 4 ×
    (∀ i, ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → Field) i) :=
  ((constraint, ∑ j, messageOne j * constraint j,
      ∑ j, messageTwo j * constraint j), ![encodedOne, encodedTwo])

-- A challenge outside the base field exercises all extension coefficients.
def gamma : Field := BinarySampling.coeffsEquiv #v[word 3, word 5, word 7]

def combinedMessage : Fin 4 → Field := messageOne + gamma • messageTwo

/-- Two uncorrupted columns suffice for each degree-`< 2` scalar row. -/
def erasureStatement : ToyProblem.Spec.Statement (F := Field) 4 ×
    (∀ i, ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → Field) i) :=
  (inputStatement.1,
    ![fun j row ↦ if j.val < 2 then encodedOne j row else encodedOne j row + 1,
      encodedTwo])

def runEmptyOracleComp {α : Type} :
    OracleComp ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) α → α
  | .pure x => x
  | .liftBind q _ => nomatch q

def testTranscript (g : Fin 4 → Field) :
    (ToyProblem.Spec.pSpec (ι := Fin 4) (F := Field) 4 1).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma
    | ⟨1, _⟩ => g
    | ⟨2, _⟩ => fun _ ↦ 0

def proverPasses (_ : Unit) : Bool :=
  let prover := ToyProblem.Spec.prover
    (ι := Fin 4) (F := Field) (A := Fin 2 → Field) (k := 4) (t := 1)
  let initial := prover.input (inputStatement, ![messageOne, messageTwo])
  let receive := runEmptyOracleComp (prover.receiveChallenge ⟨0, by decide⟩ initial)
  let sent := runEmptyOracleComp (prover.sendMessage ⟨1, by decide⟩ (receive gamma))
  let g : Fin 4 → Field := sent.1
  g == combinedMessage

def runOracleVerifier (g : Fin 4 → Field)
    (stmt := inputStatement) :
    Option (ToyProblem.Spec.OutputStatement ×
      ∀ i, ToyProblem.Spec.OutputOracleStatement i) :=
  let verifier := ToyProblem.Spec.oracleVerifier
    (k := 4) (t := 1) (encoder 4 2 two_dvd_four testDomain)
  runEmptyOracleComp <| simulateQ
    (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
      (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → Field))
      ToyProblem.Spec.instOracleInterfaceOracleStatement _
      (ToyProblem.Spec.pSpec (ι := Fin 4) (F := Field) 4 1).Message
      (ToyProblem.Spec.instOracleInterfaceMessagePSpec 4 1) stmt.2
      (testTranscript g).messages)
    (verifier.toVerifier.run stmt (testTranscript g)).run

def extractStraightline (_ : Unit) : Option (ToyProblem.Spec.Witness (F := Field) 4) :=
  runEmptyOracleComp <|
    (straightlineExtractor 4 2 1 two_dvd_four testDomain
      erasureStatement () (testTranscript combinedMessage)
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))).run

def simplifiedTranscript :
    (ToyProblem.SimplifiedIOR.pSpec (F := Field)).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma

def extractSimplifiedStraightline (_ : Unit) : Option (ToyProblem.Spec.Witness (F := Field) 4) :=
  runEmptyOracleComp <|
    (simplifiedStraightlineExtractor 4 2 two_dvd_four testDomain
      erasureStatement combinedMessage simplifiedTranscript
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))).run

def extractSimplifiedRbr (_ : Unit) : ToyProblem.Spec.Witness (F := Field) 4 :=
  let extractor : Extractor.RoundByRound (emptySpec.{0, 0})
      (ToyProblem.Spec.Statement (F := Field) 4 ×
        (∀ i, ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → Field) i))
      (ToyProblem.Spec.Witness (F := Field) 4)
      (ToyProblem.SimplifiedIOR.OutputWitness (F := Field) 4)
      (ToyProblem.SimplifiedIOR.pSpec (F := Field))
      (simplifiedRbrWitMid (F := Field) 4) :=
    simplifiedRbrExtractor 4 2 two_dvd_four testDomain
  extractor.extractMid 0 erasureStatement simplifiedTranscript combinedMessage

def querySimplifiedOutput (j : Fin 4) : Fin 2 → Field :=
  let verifier := ToyProblem.SimplifiedIOR.oracleVerifier
    (ι := Fin 4) (F := Field) (A := Fin 2 → Field) (k := 4)
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → Field))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        (ToyProblem.SimplifiedIOR.pSpec (F := Field)).Message
        ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
        inputStatement.2 simplifiedTranscript.messages)
      (verifier.simulateOutputQuery simplifiedTranscript.challenges ⟨0, j⟩)

def fieldArithmeticPasses (_ : Unit) : Bool :=
  let x := BinarySampling.coeffsEquiv #v[word 81985529216486895, word 5, word 7]
  let y := BinarySampling.coeffsEquiv #v[word 11, word 13, word 18446744073709551615]
  (x * y) / x == y

def encodeDecodePasses (_ : Unit) : Bool :=
  erasureDecodeOrZero 4 2 two_dvd_four testDomain {0, 1} encodedOne == messageOne

def transitionPasses (_ : Unit) : Bool :=
  let extracted := transitionExtractor 4 2 two_dvd_four testDomain
    erasureStatement gamma combinedMessage
  extracted 0 == messageOne && extracted 1 == messageTwo

def rejectedTransitionPasses (_ : Unit) : Bool :=
  let nodes := gammaAgreementSet 4 2 two_dvd_four testDomain
    encodedOne encodedTwo 0 (0 : Fin 4 → Field)
  let extracted := transitionExtractor 4 2 two_dvd_four testDomain
    inputStatement 0 (0 : Fin 4 → Field)
  nodes.card == 0 && extracted 0 == 0 && extracted 1 == 0

def straightlinePasses (_ : Unit) : Bool :=
  match extractStraightline () with
  | some extracted => extracted 0 == messageOne && extracted 1 == messageTwo
  | none => false

def simplifiedStraightlinePasses (_ : Unit) : Bool :=
  match extractSimplifiedStraightline () with
  | some extracted => extracted 0 == messageOne && extracted 1 == messageTwo
  | none => false

def verifierAcceptRejectPasses (_ : Unit) : Bool :=
  (runOracleVerifier combinedMessage).isSome && !(runOracleVerifier 0).isSome

def verifierRejectsWrongConstraint (_ : Unit) : Bool :=
  let badStatement := ((constraint, inputStatement.1.2.1 + 1,
    inputStatement.1.2.2), inputStatement.2)
  !(runOracleVerifier combinedMessage badStatement).isSome

def simplifiedRbrPasses (_ : Unit) : Bool :=
  let extracted := extractSimplifiedRbr ()
  extracted 0 == messageOne && extracted 1 == messageTwo

def simplifiedVirtualOutputPasses (_ : Unit) : Bool :=
  (List.finRange 4).all fun j ↦
    querySimplifiedOutput j == encodedOne j + gamma • encodedTwo j

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"binary Toy IOP runtime check failed: {name}"

def checkRuntime (name : String) (test : Unit → Bool) : IO Unit := do
  IO.eprintln s!"checking {name}"
  check name (test ())

def samplerTracePasses : IO Unit := do
  let draws := #[0, 18446744073709551615, 81985529216486895]
  let count ← IO.mkRef 0
  let result ← simulateQ (spec := unifSpec) (fun n => do
    check "64-bit sampler query range" (n == 18446744073709551615)
    let i ← count.get
    check "exactly three sampler queries" (i < draws.size)
    count.set (i + 1)
    pure (Fin.ofNat (n + 1) draws[i]!)) BinarySampling.sample
  check "three independent limb queries" ((← count.get) == 3)
  check "polynomial-basis coefficient order"
    (result == BinarySampling.coeffsEquiv
      #v[word 0, word 18446744073709551615, word 81985529216486895])
  -- Also exercise VCVio's IO interpreter on the canonical challenge sampler.
  let _ ← OracleComp.runIO BinaryCodegen.samplerProbe

def run : IO Unit := do
  samplerTracePasses
  checkRuntime "BF64.Ext3 arithmetic" fieldArithmeticPasses
  check "binary domain indices remain distinct"
    ((List.finRange 4).all fun i => (List.finRange 4).all fun j =>
      i == j || testDomain i != testDomain j)
  checkRuntime "IRS encode/decode" encodeDecodePasses
  check "rejected erasure pattern"
    (ToyProblem.Spec.rsErasureDecoder 2 testDomain ({0} : Finset (Fin 4))
      (fun _ ↦ 0) == none)
  checkRuntime "honest prover" proverPasses
  check "partial agreement set"
    (gammaAgreementSet 4 2 two_dvd_four testDomain (erasureStatement.2 0)
      (erasureStatement.2 1) gamma combinedMessage == ({0, 1} : Finset (Fin 4)))
  checkRuntime "dynamic agreement extraction" transitionPasses
  checkRuntime "rejected dynamic agreement" rejectedTransitionPasses
  checkRuntime "C6.2 straightline extractor" straightlinePasses
  checkRuntime "C6.2 verifier accept/reject" verifierAcceptRejectPasses
  checkRuntime "C6.2 linear constraint rejection" verifierRejectsWrongConstraint
  checkRuntime "C6.9 straightline extractor" simplifiedStraightlinePasses
  checkRuntime "C6.9 round-by-round extractor" simplifiedRbrPasses
  checkRuntime "C6.9 virtual output oracle" simplifiedVirtualOutputPasses
  IO.println "binary Toy IOP runtime checks passed"

end BinaryToyRuntime

def main : IO Unit := BinaryToyRuntime.run
