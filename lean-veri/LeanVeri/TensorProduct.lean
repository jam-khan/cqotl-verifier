import Mathlib.LinearAlgebra.TensorProduct.Basic


namespace TensorProduct

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module S P] [Module S Q]
variable {σ : R →+* S}

noncomputable def liftAuxₛₗ (f : M →ₛₗ[σ] N →ₛₗ[σ] P) : M ⊗[R] N →+ P :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f.toAddMonoidHom)
    fun r m n => by
      dsimp
      rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ]

theorem liftAux_tmulₛₗ (f : M →ₛₗ[σ] N →ₛₗ[σ] P) (m n) : liftAuxₛₗ f (m ⊗ₜ n) = f m n :=
  rfl

@[simp]
theorem liftAux.smulₛₗ {f : M →ₛₗ[σ] N →ₛₗ[σ] P} (r : R) (x : M ⊗[R] N) : liftAuxₛₗ f (r • x) = (σ r) • liftAuxₛₗ f x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmulₛₗ, (f p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAuxₛₗ f).map_add, ih1, ih2, smul_add]

noncomputable def liftₛₗ (f : M →ₛₗ[σ] N →ₛₗ[σ] P) : M ⊗[R] N →ₛₗ[σ] P :=
  { liftAuxₛₗ f with map_smul' := liftAux.smulₛₗ }


noncomputable def mapₛₗ (f : M →ₛₗ[σ] P) (g : N →ₛₗ[σ] Q) : M ⊗[R] N →ₛₗ[σ] P ⊗[S] Q :=
  liftₛₗ <| LinearMap.comp (LinearMap.compl₂ (mk _ _ _) g) f

end TensorProduct
