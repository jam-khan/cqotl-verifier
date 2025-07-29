/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import Mathlib.Analysis.InnerProductSpace.Trace
import LeanVeri.LinearMapPropositions

/-!
This file defines the outer product of two vectors as a linear map,
and proves basic properties of the outer product.
-/

variable (𝕜 : Type*) {E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The outer product of two vectors -/
def outerProduct (x : E) (y : F) : F →ₗ[𝕜] E where
  toFun := fun z => (inner 𝕜 y z) • x
  map_add' z w := by
    rw [← Module.add_smul, inner_add_right y z w]
  map_smul' m z := by
    rw [RingHom.id_apply, inner_smul_right_eq_smul y z m]
    exact IsScalarTower.smul_assoc m (inner 𝕜 y z) x


lemma outerProduct_def (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x y z = (inner 𝕜 y z) • x := rfl

/-- The outer product is distributive `(∣x⟩ + |y⟩)⟨z| = ∣x⟩⟨z| + |y⟩⟨z|` -/
lemma outerProduct_add_dist_left (x : E) (y : E) (z : F) :
    outerProduct 𝕜 (x + y) z = outerProduct 𝕜 x z + outerProduct 𝕜 y z := by
  ext
  simp only [LinearMap.add_apply]
  repeat rw [outerProduct_def]
  simp [smul_add]

/-- The outer product is distributive `∣x⟩(⟨y| + ⟨z|) = ∣x⟩⟨y| + |x⟩⟨z|` -/
lemma outerProduct_add_dist_right (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x (y + z) = outerProduct 𝕜 x y + outerProduct 𝕜 x z := by
  ext
  simp only [LinearMap.add_apply]
  repeat rw [outerProduct_def]
  rw [inner_add_left, add_smul]

/-- The outer product is distributive `(∣x⟩ - |y⟩)⟨z| = ∣x⟩⟨z| - |y⟩⟨z|` -/
lemma outerProduct_sub_dist_left (x : F) (y : F) (z : E) :
    outerProduct 𝕜 (x - y) z = outerProduct 𝕜 x z - outerProduct 𝕜 y z := by
  ext
  simp only [LinearMap.sub_apply]
  repeat rw [outerProduct_def]
  simp [smul_sub]

/-- The outer product is distributive `∣x⟩(⟨y| - ⟨z|) = ∣x⟩⟨y| - |x⟩⟨z|` -/
lemma outerProduct_sub_dist_right (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x (y - z) = outerProduct 𝕜 x y - outerProduct 𝕜 x z := by
  ext
  simp only [LinearMap.sub_apply]
  repeat rw [outerProduct_def]
  rw [inner_sub_left, sub_smul]

/-- The outer product is associative `(∣x⟩⟨y|)|z⟩ = ∣x⟩⟨y|z⟩` -/
lemma outerProduct_assoc_right (x : E) (y : F) (z : F) :
    (outerProduct 𝕜 x y) z = (@inner 𝕜 _ _ y z) • x := rfl

/-- The outer product scalar multiplication `(c|x⟩)⟨y| = c(|x⟩⟨y|) `-/
lemma outerProduct_smul_assoc_left (c : 𝕜) (x : E) (y : F) :
    (outerProduct 𝕜 (c • x) y) = (c : 𝕜) • (outerProduct 𝕜 x y) := by
  ext
  simp only [LinearMap.smul_apply]
  repeat rw [outerProduct_def]
  rw [smul_algebra_smul_comm]

/-- The outer product scalar multiplication `(c|x⟩)⟨y| = c(|x⟩⟨y|) `-/
lemma outerProduct_smul_assoc_right (c : 𝕜) (x : E) (y : F) :
    (outerProduct 𝕜 x (c • y)) = (starRingEnd 𝕜 c) • (outerProduct 𝕜 x y) := by
  ext
  simp only [LinearMap.smul_apply]
  repeat rw [outerProduct_def]
  rw [starRingEnd_apply, smul_algebra_smul_comm, inner_smul_left, starRingEnd_apply, mul_smul]
  simp only [RCLike.star_def]
  rw [smul_algebra_smul_comm]

lemma inner_outerProduct_eq_inner_mul_inner (x : E) (y z : F) (w : E) :
    inner 𝕜 ((outerProduct 𝕜 x y) z) w = inner 𝕜 z y * inner 𝕜 x w := by
  repeat rw [outerProduct_def]
  rw [inner_smul_left, inner_conj_symm]

lemma outerProduct_comp_outerProduct_eq_inner_smul_outerProduct (x : E) (y z : F) (w : E) :
    outerProduct 𝕜 x y ∘ₗ outerProduct 𝕜 z w = inner 𝕜 y z • outerProduct 𝕜 x w := by
  ext v
  simp only [LinearMap.comp_apply, outerProduct_def, map_smul, LinearMap.smul_apply]
  rw [smul_algebra_smul_comm]

lemma outerProduct_mul_outerProduct_eq_inner_smul_outerProduct (x y z w : E) :
    outerProduct 𝕜 x y * outerProduct 𝕜 z w = inner 𝕜 y z • outerProduct 𝕜 x w := by
  rw [Module.End.mul_eq_comp]
  exact outerProduct_comp_outerProduct_eq_inner_smul_outerProduct 𝕜 x y z w

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

lemma adjoint_outerProduct (x : E) (y : F) :
    (outerProduct 𝕜 x y).adjoint = outerProduct 𝕜 y x := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro v w
  repeat rw [outerProduct_def]
  rw [inner_smul_left, inner_conj_symm, inner_smul_right]
  exact mul_comm _ _

lemma star_outerProduct (x y : E) :
    star (outerProduct 𝕜 x y) = outerProduct 𝕜 y x := by
  rw [LinearMap.star_eq_adjoint, adjoint_outerProduct]

lemma IsSelfAdjoint_outerProduct_self (x : E) :
    IsSelfAdjoint (outerProduct 𝕜 x x) := by
  unfold IsSelfAdjoint
  rw [LinearMap.star_eq_adjoint, adjoint_outerProduct]

lemma IsSymmetric_outerProduct_self (x : E) : (outerProduct 𝕜 x x).IsSymmetric :=
  (outerProduct 𝕜 x x).isSymmetric_iff_isSelfAdjoint.mpr (IsSelfAdjoint_outerProduct_self 𝕜 x)

lemma isPositive_outerProduct_self (x : E) :
    (outerProduct 𝕜 x x).IsPositive := by
  apply And.intro (IsSymmetric_outerProduct_self 𝕜 x)
  intro y
  simp only [outerProduct_def]
  rw [inner_smul_left, InnerProductSpace.conj_inner_symm, inner_mul_symm_re_eq_norm]
  exact norm_nonneg (inner 𝕜 y x * inner 𝕜 x y)

lemma IsStarProjection_outerProduct_self_of_norm_eq_one {x : E} (h : ‖x‖ = 1) :
    IsStarProjection (outerProduct 𝕜 x x) := by
  constructor
  · ext y
    rw [Module.End.mul_eq_comp]
    simp only [LinearMap.coe_comp, Function.comp_apply, outerProduct_def]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, h]
    simp
  · exact IsSelfAdjoint_outerProduct_self 𝕜 x

lemma IsSelfAdjoint_outerProduct_add (x y : E) :
    IsSelfAdjoint (outerProduct 𝕜 x y + outerProduct 𝕜 y x) := by
  rw [LinearMap.isSelfAdjoint_iff', map_add]
  repeat rw [adjoint_outerProduct]
  abel

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma sum_outerProduct (f g : ι → E) (x : E) :
    (∑ i, outerProduct 𝕜 (f i) (g i)) x = ∑ i, outerProduct 𝕜 (f i) (g i) x := by
  simp only [LinearMap.sum_apply]

omit [DecidableEq ι] in
lemma sum_outerProduct_OrthonormalBasis (b : OrthonormalBasis ι 𝕜 E) :
    ∑i, outerProduct 𝕜 (b i) (b i) = 1 := by
  ext x
  rw [← LinearIsometryEquiv.map_eq_iff b.repr]
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, Module.End.one_apply, outerProduct_def]
  congr
  exact b.sum_repr' x

lemma trace_outerProduct (x y : E) (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E (outerProduct 𝕜 x y) = inner 𝕜 y x := by
  rw [(outerProduct 𝕜 x y).trace_eq_sum_inner b]
  simp +contextual [outerProduct_def, inner_smul_right]
  simp +contextual [show ∀i, inner 𝕜 y (b i) * inner 𝕜 (b i) x = inner 𝕜 (b i) x * inner 𝕜 y (b i) by intro i; apply mul_comm]
  simp +contextual [← inner_smul_right, ← outerProduct_def]
  rw [← inner_sum, ← sum_outerProduct, sum_outerProduct_OrthonormalBasis 𝕜 b, Module.End.one_apply]
