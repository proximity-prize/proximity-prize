import ProximityPrize.SubmissionLower.R6961Front6961Assembly

set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6961 337210382 1073741824 :=
  Lower6961.protocol_6961

#print axioms ProximityPrize.Benchmark.candidate
