/-
Copyright (c) 2025 Jam Kabeer Ali Khan, Iván Renison. All rights reserved.
Authors: Iván Renison, Jam Kabeer Ali Khan
-/

import LeanVeri.LinearMapPropositions
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
This file formalizes the basic properties of the quantum computing
operations based on the lemma A.7 and lemma A.8 of the LICS2025 paper:
Complete Quantum Relational Hoare Logics from Optimal Transport Duality
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable? [HilbertSpace 𝕜 F] => [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable [FiniteDimensional 𝕜 E]
variable [FiniteDimensional 𝕜 F]

omit [CompleteSpace E]
omit [CompleteSpace F]
omit [FiniteDimensional 𝕜 F]

open scoped TensorProduct

-- lemma A.7
namespace BasicProperties

/-
This lemma shows the `Scalar product equal 1` property `⟨φ|φ⟩ = 1`
-/
omit [FiniteDimensional 𝕜 E] in
lemma scalar_product_eq_one (_ : 𝕜) (φ : E) (h: ‖φ‖ = 1) :
    inner 𝕜 φ φ = 1 := (inner_eq_one_iff_of_norm_one h h).mpr rfl

/-
This lemma shows the `Scalar product` property `⟨φ|(c•A)|φ⟩ = c * ⟨φ|A|φ⟩`.
-/

omit [FiniteDimensional 𝕜 E] in
lemma scalar_product (c : 𝕜) (φ : E) (A : E →ₗ[𝕜] E) :
    inner 𝕜 φ ((c • A) φ) = c * inner 𝕜 φ (A φ) := by
  rw [@LinearMap.smul_apply, @inner_smul_right]

/-
This lemma shows the `Addition` property `⟨φ|(A₁ + A₂)|φ⟩ = ⟨φ|A₁|φ⟩ + ⟨φ|A₁|φ⟩`.
-/
omit [FiniteDimensional 𝕜 E] in
lemma addition (φ : E) (A₁ A₂ : E →ₗ[𝕜] E) :
    inner 𝕜 φ ((A₁ + A₂) φ) = inner 𝕜 φ (A₁ φ) + inner 𝕜 φ (A₂ φ) := by
  rw [@LinearMap.add_apply, @inner_add_right]

end BasicProperties

-- lemma A.8
namespace AlgebraicProperties


/-
This lemma shows projection `T` is self-adjoint `T† = T`
-/
lemma adjointeql (T: E →ₗ[𝕜] E) (hT : IsStarProjection T) : T.adjoint = T := by
  rw [← LinearMap.star_eq_adjoint]
  exact hT.isSelfAdjoint

omit [FiniteDimensional 𝕜 E]

/-
This lemma shows the `Zero_Multiplication` property `0A = 0`.
-/
lemma zero_mul (A : E →ₗ[𝕜] E) :
    0 • A = (0 : E →ₗ[𝕜] E) :=
  zero_nsmul A

/-
This lemma shows the `One_Multiplication` property `1A = A`.
-/
lemma one_mul (A : E →ₗ[𝕜] E) :
    1 • A = A :=
  one_nsmul A

/-
This lemma shows the `Mult_Associativity` property `a(bA) = (ab)A`.
-/
lemma mult_assoc (a b : 𝕜) (A : E →ₗ[𝕜] E) :
    a • (b • A) = (a * b) • A :=
  smul_smul a b A

/-
This lemma shows the `Zero_Add_Identity` property `0 + A = A`.
-/
lemma zero_add (A : E →ₗ[𝕜] E):
    (0 : E →ₗ[𝕜] E) + A = A := by
  rw [add_eq_right]

/-
This lemma shows the `Add_Zero_Identity` property `A + 0 = A`.
-/
lemma add_zero (A : E →ₗ[𝕜] E) :
    A + (0 : E →ₗ[𝕜] E) = A :=
  by rw [add_eq_left]

/-
This lemma shows the `Zero_Add_Add_Zero_Eqv` property `A + 0 = 0 + A`.
-/
lemma zero_add_add_zero_eq (A : E →ₗ[𝕜] E) :
    A + (0 : E →ₗ[𝕜] E) = (0 : E →ₗ[𝕜] E) + A := by
  rw [add_zero, zero_add]
/-
This lemma shows the `Add_Commutativity` property `A₁ + A₂ = A₂ + A₁`.
-/
lemma add_comm (A₁ A₂ : E →ₗ[𝕜] E) :
    A₁ + A₂ = A₂ + A₁ := by
  rw [@AddCommMonoidWithOne.add_comm]

/-
This lemma shows the `Add_Right_Associativity` property `A₁ + A₂ + A₃ = A₁ + (A₂ + A₃)`.
-/
lemma add_right_associativity (A₁ A₂ A₃ : E →ₗ[𝕜] E) : A₁ + A₂ + A₃ = A₁ + (A₂ + A₃) :=
  add_assoc A₁ A₂ A₃

/-
This lemma shows the `Add_Left_Associativity` property `A₁ + A₂ + A₃ = (A₁ + A₂) + A₃`.
-/
lemma add_left_associativity (A₁ A₂ A₃ : E →ₗ[𝕜] E) : A₁ + A₂ + A₃ = (A₁ + A₂) + A₃ := rfl

/-
This lemma shows the `Add_Left_Right_Associativity_Eqv` property `A₁ + (A₂ + A₃) = (A₁ + A₂) + A₃`.
-/
lemma add_left_right_associativity_eqv (A₁ A₂ A₃ : E →ₗ[𝕜] E) :
    A₁ + (A₂ + A₃) = (A₁ + A₂) + A₃ := Eq.symm (add_assoc A₁ A₂ A₃)
/-
This lemma shows the `Zero_Prod_Identity` property `0 ⊗ A = 0`.
-/
lemma zero_prod_identity (A : E →ₗ[𝕜] E) :
  TensorProduct.map (0 : F →ₗ[𝕜] F) A = 0 := TensorProduct.map_zero_left A

/-
This lemma shows the `Prod_Zero_Identity` property `A ⊗ 0 = 0`.
-/
lemma prod_zero_identity (A : E →ₗ[𝕜] E) :
  TensorProduct.map A (0 : F →ₗ[𝕜] F) = 0 := TensorProduct.map_zero_right A

/-
This lemma shows the `zero_prod_prod_zero_eqv` property `0 ⊗ A = A ⊗ 0`.
-/
lemma zero_tmulmap_eq_tmulmap_zero (A :  E →ₗ[𝕜] E) :
    TensorProduct.map (0 : E →ₗ[𝕜] E) A  = TensorProduct.map A (0 : E →ₗ[𝕜] E) := by
  rw [prod_zero_identity, zero_prod_identity]

end AlgebraicProperties
