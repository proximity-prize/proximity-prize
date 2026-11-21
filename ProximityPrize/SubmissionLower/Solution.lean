import ProximityPrize.SubmissionLower.KoalaSoundness6949
import ProximityPrize.SubmissionLower.KoalaRawCount

set_option Elab.async false

private theorem raw_incidence_6949 : KoalaDiagonalPrice.RawIncidence := by
  intro J B D hword v w hdegree
  obtain ⟨hk, hv, hw⟩ := KoalaDiagonalPrice.liftIndex_spec J.hi v w
  let k := KoalaDiagonalPrice.liftIndex J.hi v w
  have hcount := SplitCut.RawCount.proper_count J B D v w k hk
    (by simpa only [Nat.mul_comm] using hv)
    (by simpa only [Nat.mul_comm] using hw)
    hdegree hword J.agreement_gap
  refine hcount.trans_eq ?_
  simp only [SplitCut.RawCount.rootDegree, SplitCut.RawCount.firstDegree, SplitCut.RawCount.weight,
    KoalaDiagonalPrice.properBudget, KoalaDiagonalPrice.surfaceDegree, HighCore82209_5.nodeVelocity,
    HighCore82209.lambdaNum, HighCore82209.muNum, HighCore82209.gap, k]
  ring

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6949 2892507229422860772 9223372036854718577 :=
  KoalaSoundness6949.of_incidence raw_incidence_6949

#print axioms ProximityPrize.Benchmark.candidate
