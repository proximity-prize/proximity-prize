import ProximityPrize.SubmissionLower.CT
import ProximityPrize.SubmissionLower.I8
namespace ProximityPrize.SubmissionLower.RCN188
open RCN078
variable {K R S:Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (M:Submonoid R) [IsLocalization M S]
def derivationDualAlgHom (D:Derivation K R R):R →ₐ[K] DualNumber S where
 toFun r:=(algebraMap R S r,algebraMap R S (D r))
 map_one':=by
   apply DualNumber.ext <;> simp
 map_mul' x y:=by
   apply DualNumber.ext
   · simp
   · simp [D.leibniz]
     exact mul_comm _ _
 map_zero':=by
   apply DualNumber.ext <;> simp
 map_add' x y:=by
   apply DualNumber.ext <;> simp
 commutes' k:=by
   apply DualNumber.ext
   · exact (IsScalarTower.algebraMap_apply K R S k).symm
   · simp
theorem derivationDualAlgHom_isUnit (D:Derivation K R R) (y:M):
   IsUnit (derivationDualAlgHom (S:=S) D y):=by
 apply DualNumber.isUnit_of_isUnit_fst
 simpa [derivationDualAlgHom] using IsLocalization.map_units S y
noncomputable def localizedDualAlgHom (D:Derivation K R R):
   S →ₐ[K] DualNumber S:=
 IsLocalization.liftAlgHom (derivationDualAlgHom_isUnit M D)
@[simp]
theorem localizedDualAlgHom_algebraMap (D:Derivation K R R) (r:R):
   localizedDualAlgHom M D (algebraMap R S r)=
     (algebraMap R S r,algebraMap R S (D r)):=by
 simp [localizedDualAlgHom,derivationDualAlgHom]
theorem localizedDualAlgHom_fst (D:Derivation K R R) (x:S):
   (localizedDualAlgHom M D x).fst=x:=by
 have hhom:
     (DualNumber.fstHom (K:=K) (R:=S)).comp
       (localizedDualAlgHom M D)=AlgHom.id K S:=by
   have hr:
       ((DualNumber.fstHom (K:=K) (R:=S)).comp
         (localizedDualAlgHom M D)).toRingHom=
         (AlgHom.id K S).toRingHom:=by
     apply IsLocalization.ringHom_ext M
     ext r
     simp [DualNumber.fstHom]
   exact AlgHom.ext fun x => RingHom.congr_fun hr x
 exact AlgHom.congr_fun hhom x
noncomputable def localizationDerivation (D:Derivation K R R):Derivation K S S:=
 Derivation.mk'
   ((DualNumber.sndHom (R:=S)).restrictScalars K |>.comp
     (localizedDualAlgHom M D).toLinearMap)
   (by
     intro x y
     change (localizedDualAlgHom M D (x*y)).snd=
       x*(localizedDualAlgHom M D y).snd+
         y*(localizedDualAlgHom M D x).snd
     rw [map_mul,DualNumber.snd_mul,
       localizedDualAlgHom_fst M D x,localizedDualAlgHom_fst M D y]
     simp
     ring)
@[simp]
theorem localizationDerivation_algebraMap (D:Derivation K R R) (r:R):
   localizationDerivation M D (algebraMap R S r)=algebraMap R S (D r):=by
 change (localizedDualAlgHom M D (algebraMap R S r)).snd=_
 rw [localizedDualAlgHom_algebraMap]
end ProximityPrize.SubmissionLower.RCN188
