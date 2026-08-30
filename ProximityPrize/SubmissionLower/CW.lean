import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
variable {A B:Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (P:Ideal B) (p:Ideal A) [P.LiesOver p]
instance module_finite_of_liesOver [Module.Finite A B]:Module.Finite (A ⧸ p) (B ⧸ P):=
 Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)
example [Module.Finite A B]:Module.Finite (A ⧸ P.under A) (B ⧸ P):=inferInstance
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B]:
   Algebra.FiniteType (A ⧸ p) (B ⧸ P):=
 Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)
instance isNoetherian_of_liesOver [IsNoetherian A B]:IsNoetherian (A ⧸ p) (B ⧸ P):=
 isNoetherian_of_tower A inferInstance
instance QuotientMapQuotient.isNoetherian [IsNoetherian A B]:
   IsNoetherian (A ⧸ p) (B ⧸ p.map (algebraMap A B)):=
 isNoetherian_of_tower A <|
   isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap <|
     LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
