/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.IRSProfile
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.Benchmark.TargetUpper

import ProximityPrize.Benchmark.BinaryIRSProfile
import ProximityPrize.Benchmark.BinaryCodegen
import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.Benchmark.BinaryTargetUpper

-- Not used by anything above: this import is what compiles the contract and
-- geometry guards. Dropping it as unused would leave them unchecked.
import ProximityPrize.Benchmark.ContractShape

/-!
# Proximity Prize — interleaved-RS reduction thresholds

The public library exposes the fixed IRS profile together with lower and upper
certificates for the ABF26 reduction threshold.
-/
