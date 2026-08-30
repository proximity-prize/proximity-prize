import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.IA
import ProximityPrize.SubmissionLower.V8
section ProximityFlatProofPort
open QuotientAddGroup Set ZMod
variable (n:ℕ) {A R:Type*} [AddGroup A] [Ring R]
namespace Int
def quotientSpanNatEquivZMod:ℤ ⧸ Ideal.span {(n:ℤ)} ≃+*ZMod n:=
 (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans <|
   RingHom.quotientKerEquivOfRightInverse <|
     show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast
def quotientSpanEquivZMod (a:ℤ):ℤ ⧸ Ideal.span ({a}:Set ℤ) ≃+*ZMod a.natAbs:=
 (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
@[simp]
theorem quotientSpanNatEquivZMod_comp_Quotient_mk (n:ℕ):
   (Int.quotientSpanNatEquivZMod n:_ →+*_).comp (Ideal.Quotient.mk (Ideal.span {(n:ℤ)}))=
     Int.castRingHom (ZMod n):=rfl
@[simp]
theorem quotientSpanNatEquivZMod_comp_castRingHom (n:ℕ):
   ((Int.quotientSpanNatEquivZMod n).symm:_ →+*_).comp (Int.castRingHom (ZMod n))=
     Ideal.Quotient.mk (Ideal.span {(n:ℤ)}):=by ext;simp
@[simp]
theorem quotientSpanEquivZMod_comp_Quotient_mk (n:ℤ):
   (Int.quotientSpanEquivZMod n:_ →+*_).comp (Ideal.Quotient.mk (Ideal.span {(n:ℤ)}))=
     Int.castRingHom (ZMod n.natAbs):=rfl
@[simp]
theorem quotientSpanEquivZMod_comp_castRingHom (n:ℤ):
   ((Int.quotientSpanEquivZMod n).symm:_ →+*_).comp (Int.castRingHom (ZMod n.natAbs))=
     Ideal.Quotient.mk (Ideal.span {(n:ℤ)}):=by ext;simp
instance {n:ℤ} [NeZero n]:Finite (ℤ ⧸ Ideal.span {n}):=
 Finite.of_equiv _ n.quotientSpanEquivZMod.symm.toEquiv
end Int
noncomputable section ChineseRemainder
open Ideal
open scoped Function in
def ZMod.prodEquivPi {ι:Type*} [Fintype ι] (a:ι → ℕ)
   (coprime:Pairwise (Nat.Coprime on a)):ZMod (∏ i,a i) ≃+*Π i,ZMod (a i):=
 have:Pairwise fun i j => IsCoprime (span {(a i:ℤ)}) (span {(a j:ℤ)}):=
   fun _i _j h↦(isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R:=ℤ))
 Int.quotientSpanNatEquivZMod _ |>.symm.trans <|
 quotEquivOfEq (iInf_span_singleton_natCast (R:=ℤ) coprime) |>.symm.trans <|
 quotientInfRingEquivPiQuotient _ this |>.trans <|
 RingEquiv.piCongrRight fun i↦Int.quotientSpanNatEquivZMod (a i)
open Finset Function in
@[simp]
theorem ZMod.prodEquivPi_apply {ι:Type*} [Fintype ι] (a:ι → ℕ)
   (coprime:Pairwise (Nat.Coprime on a)) (b:ZMod (∏ i,a i)) (i:ι):
   prodEquivPi a coprime b i=castHom (dvd_prod_of_mem a (mem_univ i)) _ b:=
 RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom (fun _↦ZMod _) i).comp
   (prodEquivPi a coprime).toRingHom) _) b
def ZMod.equivPi (hn:n≠0):
   ZMod n ≃+*Π (p:n.primeFactors),ZMod (p^(n.factorization p)):=
 (ringEquivCongr <| Nat.prod_primeFactors_coe_pow_factorization hn).trans
   <| prodEquivPi (fun (p:n.primeFactors)↦(p:ℕ)^(n.factorization p))
     n.pairwise_coprime_pow_primeFactors_factorization
end ChineseRemainder
