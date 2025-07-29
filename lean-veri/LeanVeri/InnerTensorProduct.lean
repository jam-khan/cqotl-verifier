/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.OuterProduct
import LeanVeri.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib

/-!
Instance of `Inner` for tensor products for the specific case of `EuclideanSpace`.
-/

variable (𝕜 : Type*) {E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

open scoped TensorProduct
open scoped ComplexOrder

namespace TensorProduct

private
noncomputable def linner : E ⊗[𝕜] F →ₗ⋆[𝕜] E ⊗[𝕜] F →ₗ[𝕜] 𝕜 :=
  LinearMap.compr₂ (lift (mapBilinear 𝕜 E F 𝕜 𝕜)) (LinearMap.mul' 𝕜 𝕜) ∘ₛₗ mapₛₗ (innerₛₗ 𝕜 (E := E)) (innerₛₗ 𝕜 (E := F))

private
lemma linner_tmul (x₀ x₁ : E) (y₀ y₁ : F) :
    linner 𝕜 (x₀ ⊗ₜ y₀) (x₁ ⊗ₜ y₁) = inner 𝕜 x₀ x₁ * inner 𝕜 y₀ y₁ :=
  rfl

private
lemma linner_ladd (x y : E ⊗[𝕜] F) (z : E ⊗[𝕜] F) :
    linner 𝕜 (x + y) z = linner 𝕜 x z + linner 𝕜 y z := by
  simp

private
lemma linner_radd (x : E ⊗[𝕜] F) (y z : E ⊗[𝕜] F) :
    linner 𝕜 x (y + z) = linner 𝕜 x y + linner 𝕜 x z := by
  simp

private
lemma linner_conj_inner_symm (x y : E ⊗[𝕜] F) :
    starRingEnd 𝕜 (linner 𝕜 y x) = linner 𝕜 x y := by
  induction x with
    | zero =>
      simp
    | tmul x₀ x₁ =>
      induction y with
      | zero =>
        simp
      | tmul y₀ y₁ =>
        repeat rw [linner_tmul]
        rw [map_mul]
        repeat rw [inner_conj_symm]
      | add x y hx hy =>
        rw [linner_ladd, linner_radd]
        rw [map_add]
        rw [hx, hy]
    | add x z hx hz =>
      rw [linner_ladd, linner_radd]
      rw [map_add]
      rw [hx, hz]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

private
lemma linner_nonneg (x : E ⊗[𝕜] F) : 0 ≤ linner 𝕜 x x := by
  let ⟨_, bE', _⟩ := exists_orthonormalBasis 𝕜 E
  let ⟨_, bF', _⟩ := exists_orthonormalBasis 𝕜 F
  let bE := bE'.toBasis
  let bF := bF'.toBasis
  let b := Module.Basis.tensorProduct bE bF
  rw [← b.sum_repr x, map_sum (linner 𝕜), LinearMap.sum_apply]
  simp +contextual only [map_sum]
  apply Finset.sum_nonneg'
  intro ⟨i₀, j₀⟩
  apply Finset.sum_nonneg'
  intro ⟨i₁, j₁⟩
  repeat rw [bE.tensorProduct_apply' bF]
  repeat rw [smul_tmul']
  simp only
  rw [linner_tmul, inner_smul_left, inner_smul_right]
  by_cases hi : i₀ = i₁
  · by_cases hj : j₀ = j₁
    · rw [hi, hj]
      ring_nf
      rw [mul_assoc]
      apply Left.mul_nonneg
      · exact star_mul_self_nonneg _
      · apply Left.mul_nonneg <;>
        rw [RCLike.nonneg_iff] <;>
        apply And.intro inner_self_nonneg (inner_self_im _)
    · repeat rw [OrthonormalBasis.coe_toBasis]
      rw [bF'.inner_eq_zero hj]
      simp
  · repeat rw [OrthonormalBasis.coe_toBasis]
    rw [bE'.inner_eq_zero hi]
    simp

private
lemma re_linner_nonneg (x : E ⊗[𝕜] F) : 0 ≤ RCLike.re (linner 𝕜 x x) :=
  (RCLike.nonneg_iff.mp (linner_nonneg 𝕜 x)).left

noncomputable instance InnerProductSpace_Core_TensorProduct : InnerProductSpace.Core 𝕜 (E ⊗[𝕜] F) where
  inner x y := linner 𝕜 x y
  conj_inner_symm := linner_conj_inner_symm 𝕜
  re_inner_nonneg := re_linner_nonneg 𝕜
  add_left x y z := linner_ladd 𝕜 x y z
  smul_left x y r := by
    rw [map_smulₛₗ, LinearMap.smul_apply]
    rfl
  definite x h := by
    let ⟨_, bE', _⟩ := exists_orthonormalBasis 𝕜 E
    let ⟨_, bF', _⟩ := exists_orthonormalBasis 𝕜 F
    let bE := bE'.toBasis
    let bF := bF'.toBasis
    let b := Module.Basis.tensorProduct bE bF
    rw [← b.sum_repr x, map_sum (linner 𝕜), LinearMap.sum_apply] at h
    simp +contextual only [map_sum] at h

    have hijij : ∀ij₀, ∀ ij₁, ij₁ ≠ ij₀ → ((linner 𝕜) ((b.repr x) ij₀ • b ij₀)) ((b.repr x) ij₁ • b ij₁) = 0 := by
      intro ⟨i₀, j₀⟩ ⟨i₁, j₁⟩ hij
      simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, map_eq_zero]
      right
      right
      repeat rw [bE.tensorProduct_apply' bF]
      rw [linner_tmul]
      simp only [mul_eq_zero]
      simp only [ne_eq, Prod.mk.injEq, not_and] at hij
      repeat rw [OrthonormalBasis.coe_toBasis]
      by_cases hi : i₁ = i₀
      · have hj: j₁ ≠ j₀ := hij hi
        right
        rw [bF'.inner_eq_zero hj.symm]
      · rw [← Ne.eq_def] at hi
        left
        rw [bE'.inner_eq_zero hi.symm]

    have hij := fun ij ↦ Fintype.sum_eq_single ij (hijij ij)

    simp +contextual only [hij] at h

    have hij' : 0 ≤ fun ij ↦ ((linner 𝕜) ((b.repr x) ij • b ij)) ((b.repr x) ij • b ij) := by
      intro ⟨i, j⟩
      simp only [Pi.zero_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, ge_iff_le]
      rw [← mul_assoc]
      apply Left.mul_nonneg
      · exact mul_star_self_nonneg _
      · repeat rw [bE.tensorProduct_apply' bF]
        simp [linner_tmul]
        apply Left.mul_nonneg <;>
          rw [RCLike.nonneg_iff] <;>
          apply And.intro inner_self_nonneg (inner_self_im _)

    rw [Fintype.sum_eq_zero_iff_of_nonneg hij', funext_iff] at h

    rw [← b.sum_repr x]
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ _
    have hij'' := h ⟨i, j⟩
    simp only [Pi.zero_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at hij''
    repeat rw [bE.tensorProduct_apply' bF] at hij''
    repeat rw [bE.tensorProduct_apply' bF]
    rw [linner_tmul] at hij''
    simp only [mul_eq_zero, map_eq_zero, inner_self_eq_zero, or_self_left] at hij''
    simp only [smul_eq_zero]
    cases hij'' with
    | inl hx =>
      exact Or.inl hx
    | inr hij''' =>
      right
      cases hij''' with
      | inl hi =>
        rw [hi]
        exact zero_tmul E (bF j)
      | inr hj =>
        rw [hj]
        exact tmul_zero F (bE i)

noncomputable instance : NormedAddCommGroup (E ⊗[𝕜] F) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := InnerProductSpace_Core_TensorProduct 𝕜)

noncomputable instance : InnerProductSpace 𝕜 (E ⊗[𝕜] F) := InnerProductSpace.ofCore (InnerProductSpace_Core_TensorProduct 𝕜)

lemma inner_tmul (x₀ x₁ : E) (y₀ y₁ : F) :
    inner 𝕜 (x₀ ⊗ₜ[𝕜] y₀) (x₁ ⊗ₜ[𝕜] y₁) = inner 𝕜 x₀ x₁ * inner 𝕜 y₀ y₁ :=
  rfl

variable {G H : Type*}

variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]

lemma outerProduct_tmul (x : E) (y : F) (z : G) (w : H) :
    outerProduct 𝕜 (x ⊗ₜ[𝕜] y) (z ⊗ₜ[𝕜] w) = mapBilinear 𝕜 G H E F (outerProduct 𝕜 x z) (outerProduct 𝕜 y w) := by
  ext u v
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars, outerProduct_def,
    mapBilinear_apply, map_tmul, tmul_smul]
  rw [inner_tmul, ← smul_tmul', smul_smul, mul_comm]

end TensorProduct
