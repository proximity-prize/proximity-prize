/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.BinaryIRSProfile

/-!
# Code-generation gates for the concrete binary Toy IOP

These definitions specialize ArkLib's algorithms to the production binary
profile outside any noncomputable section. The IR checks guard their executable
implementations; the companion runtime test uses small code dimensions.
-/

namespace ProximityPrize.Benchmark.BinaryCodegen

open BinaryIRSProfile

def samplerProbe : ProbComp Field := uniformSample Field

def arithmeticProbe (x y : Field) : Field := (x * y) / x

def domainProbe := domain

def encoderProbe := encoder

def proverProbe := ToyProblem.Spec.prover
  (ι := Index) (F := Field) (A := Fin interleaving → Field)
  (k := totalDimension) (t := repetitions)

def oracleVerifierProbe := ToyProblem.Spec.oracleVerifier
  (k := totalDimension) (t := repetitions) encoder

def oracleReductionProbe := ToyProblem.Spec.oracleReduction
  (k := totalDimension) (t := repetitions) encoder

def erasureDecoderProbe := ToyProblem.Impl.IRS.erasureDecodeOrZero
  totalDimension interleaving interleaving_dvd_totalDimension domain

def transitionExtractorProbe := ToyProblem.Impl.IRS.transitionExtractor
  totalDimension interleaving interleaving_dvd_totalDimension domain

def rbrExtractorProbe := ToyProblem.Impl.IRS.rbrExtractor
  totalDimension interleaving repetitions interleaving_dvd_totalDimension domain

def straightlineExtractorProbe := ToyProblem.Impl.IRS.straightlineExtractor
  totalDimension interleaving repetitions interleaving_dvd_totalDimension domain

def simplifiedProverProbe := ToyProblem.SimplifiedIOR.prover
  (ι := Index) (F := Field) (A := Fin interleaving → Field) (k := totalDimension)

def simplifiedVerifierProbe := ToyProblem.SimplifiedIOR.oracleVerifier
  (ι := Index) (F := Field) (A := Fin interleaving → Field) (k := totalDimension)

def simplifiedReductionProbe := ToyProblem.SimplifiedIOR.oracleReduction
  (ι := Index) (F := Field) (A := Fin interleaving → Field) (k := totalDimension)

def simplifiedRbrExtractorProbe := ToyProblem.Impl.IRS.simplifiedRbrExtractor
  totalDimension interleaving interleaving_dvd_totalDimension domain

def simplifiedStraightlineExtractorProbe :=
  ToyProblem.Impl.IRS.simplifiedStraightlineExtractor
    totalDimension interleaving interleaving_dvd_totalDimension domain

assert_toy_ir BinarySampling.baseSampleableType
assert_toy_ir BinarySampling.sampleableType
assert_toy_ir BinarySampling.sample
assert_toy_ir samplerProbe
assert_toy_ir arithmeticProbe
assert_toy_ir domainProbe
assert_toy_ir encoderProbe
assert_toy_ir proverProbe
assert_toy_ir oracleVerifierProbe
assert_toy_ir oracleReductionProbe
assert_toy_ir erasureDecoderProbe
assert_toy_ir transitionExtractorProbe
assert_toy_ir rbrExtractorProbe
assert_toy_ir straightlineExtractorProbe
assert_toy_ir simplifiedProverProbe
assert_toy_ir simplifiedVerifierProbe
assert_toy_ir simplifiedReductionProbe
assert_toy_ir simplifiedRbrExtractorProbe
assert_toy_ir simplifiedStraightlineExtractorProbe

end ProximityPrize.Benchmark.BinaryCodegen
