import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.RCN078
def DualNumber (R:Type*):=R × R
namespace DualNumber
variable {K R:Type*}
instance [Zero R]:Zero (DualNumber R):=inferInstanceAs (Zero (R × R))
instance [Add R]:Add (DualNumber R):=inferInstanceAs (Add (R × R))
instance [Neg R]:Neg (DualNumber R):=inferInstanceAs (Neg (R × R))
instance [Sub R]:Sub (DualNumber R):=inferInstanceAs (Sub (R × R))
instance [AddCommMonoid R]:AddCommMonoid (DualNumber R):=
 inferInstanceAs (AddCommMonoid (R × R))
instance [AddCommGroup R]:AddCommGroup (DualNumber R):=
 inferInstanceAs (AddCommGroup (R × R))
instance [SMul K R]:SMul K (DualNumber R):=inferInstanceAs (SMul K (R × R))
instance {L:Type*} [SMul L K] [SMul L R] [SMul K R] [IsScalarTower L K R]:
   IsScalarTower L K (DualNumber R):=
 inferInstanceAs (IsScalarTower L K (R × R))
instance [Semiring K] [AddCommMonoid R] [Module K R]:Module K (DualNumber R):=
 inferInstanceAs (Module K (R × R))
instance [One R] [Zero R]:One (DualNumber R):=⟨(1,0)⟩
instance [Mul R] [Add R]:Mul (DualNumber R):=
 ⟨fun x y => (x.1*y.1,x.1*y.2+x.2*y.1)⟩
@[ext]
theorem ext {x y:DualNumber R} (h₁:x.1=y.1) (h₂:x.2=y.2):x=y:=
 Prod.ext h₁ h₂
@[simp] theorem fst_zero [Zero R]:(0:DualNumber R).1=0:=rfl
@[simp] theorem snd_zero [Zero R]:(0:DualNumber R).2=0:=rfl
@[simp] theorem fst_add [Add R] (x y:DualNumber R):(x+y).1=x.1+y.1:=rfl
@[simp] theorem snd_add [Add R] (x y:DualNumber R):(x+y).2=x.2+y.2:=rfl
@[simp] theorem fst_one [One R] [Zero R]:(1:DualNumber R).1=1:=rfl
@[simp] theorem snd_one [One R] [Zero R]:(1:DualNumber R).2=0:=rfl
@[simp] theorem fst_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).1=x.1*y.1:=rfl
@[simp] theorem snd_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).2=x.1*y.2+x.2*y.1:=rfl
instance [CommRing R]:CommRing (DualNumber R) where
 mul_assoc x y z:=by ext <;> simp [mul_assoc,mul_add,add_mul];ring
 one_mul x:=by ext <;> simp
 mul_one x:=by ext <;> simp
 left_distrib x y z:=by ext <;> simp [mul_add];ring
 right_distrib x y z:=by ext <;> simp [add_mul];ring
 zero_mul x:=by ext <;> simp
 mul_zero x:=by ext <;> simp
 mul_comm x y:=by ext <;> simp [mul_comm,add_comm]
def inlRingHom [CommRing R]:R →+*DualNumber R where
 toFun r:=(r,0)
 map_one':=rfl
 map_mul' _ _:=by ext <;> simp
 map_zero':=rfl
 map_add' _ _:=by ext <;> simp
instance [CommRing K] [CommRing R] [Algebra K R]:Algebra K (DualNumber R) where
 algebraMap:=inlRingHom.comp (algebraMap K R)
 commutes' k x:=by ext <;> simp [mul_comm]
 smul_def' k x:=by
   apply Prod.ext
   · change k • x.1=algebraMap K R k*x.1
     exact Algebra.smul_def k x.1
   · change k • x.2=algebraMap K R k*x.2+0*x.1
     simp [Algebra.smul_def]
@[simp]
theorem algebraMap_apply [CommRing K] [CommRing R] [Algebra K R] (k:K):
   algebraMap K (DualNumber R) k=(algebraMap K R k,0):=rfl
def fstHom [CommRing K] [CommRing R] [Algebra K R]:DualNumber R →ₐ[K] R where
 toFun x:=x.1
 map_one':=rfl
 map_mul' _ _:=rfl
 map_zero':=rfl
 map_add' _ _:=rfl
 commutes' _:=rfl
def sndHom [CommRing R]:DualNumber R →ₗ[R] R where
 toFun x:=x.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
theorem isUnit_of_isUnit_fst [CommRing R] {x:DualNumber R} (hx:IsUnit x.1):
   IsUnit x:=by
 rcases x with ⟨a,b⟩
 rcases hx with ⟨u,hu⟩
 change (u:R)=a at hu
 subst a
 refine ⟨{
   val:=((u:R),b)
   inv:=((↑u⁻¹:R), -((↑u⁻¹:R)*b*(↑u⁻¹:R)))
   val_inv:=?_
   inv_val:=?_},rfl⟩
 · ext <;> simp [mul_assoc]
 · ext <;> simp [mul_assoc]
end DualNumber
end ProximityPrize.SubmissionLower.RCN078
