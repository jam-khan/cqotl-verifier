/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
/-!
This file extends the file `Mathlib.Analysis.InnerProductSpace.Spectrum` but with some lemmas
probed only for when the dimension is two.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

namespace LinearMap

omit [FiniteDimensional 𝕜 E] in
private lemma eq_iff_eq_zero_of_inner_eq_zero {x y : E} (h : inner 𝕜 x y = 0) : x = y ↔ x = 0 ∧ y = 0 := by
  apply Iff.intro
  · intro hxy
    apply And.intro
    · rw [← hxy] at h
      exact inner_self_eq_zero.mp h
    · rw [hxy] at h
      exact inner_self_eq_zero.mp h
  · intro hxy
    rw [hxy.left, hxy.right]

lemma IsSymmetric.zero_eigenvalues_eq_rank_ker_of_finrank_eq_two (hT : T.IsSymmetric)
    (h2 : Module.finrank 𝕜 E = 2) :
    Finset.card {i : Fin 2 | hT.eigenvalues h2 i = 0} = Module.finrank 𝕜 (LinearMap.ker T) := by
  rw [← Module.End.eigenspace_zero T, Finset.card_filter, Fin.sum_univ_two]
  let base : OrthonormalBasis (Fin 2) 𝕜 E := hT.eigenvectorBasis h2
  by_cases h0 : hT.eigenvalues h2 0 = 0 <;> by_cases h1 : hT.eigenvalues h2 1 = 0
  <;> simp only [Fin.isValue, h0, ↓reduceIte, h1, add_zero, zero_add]
  · have hT0 : T = 0 := by
      ext x
      simp only [zero_apply]
      rw [← OrthonormalBasis.sum_repr base x, map_sum]
      simp only [map_smul, Fin.sum_univ_two, Fin.isValue]
      repeat rw [hT.apply_eigenvectorBasis]
      simp [h0, h1]
    rw [hT0, Module.End.eigenspace_zero, LinearMap.ker_zero, finrank_top]
    exact h2.symm
  · rw [Module.End.eigenspace_zero]
    apply le_antisymm
    · rw [Submodule.one_le_finrank_iff]
      intro hker
      rw [ker_eq_bot'] at hker
      have hb0 : T (base 0) = 0 := by
        rw [apply_eigenvectorBasis, h0]
        simp
      have hb0' : base 0 = 0 := hker (base 0) hb0
      have hb0norm : ‖base 0‖ = 1 := base.norm_eq_one 0
      simp_all
    · rw [Nat.le_iff_lt_add_one, one_add_one_eq_two, ← h2]
      apply Submodule.finrank_lt
      intro hker
      rw [ker_eq_top] at hker
      have hb1 : T (base 1) = 0 := by
        simp [hker]
      have hb1norm : ‖base 1‖ = 1 := base.norm_eq_one 1
      have hb1' : T (base 1) ≠ 0 := by
        rw [apply_eigenvectorBasis, propext (smul_ne_zero_iff_left (base.orthonormal.ne_zero 1))]
        exact RCLike.ofReal_ne_zero.mpr h1
      exact hb1' hb1
  · rw [Module.End.eigenspace_zero]
    apply le_antisymm
    · rw [Submodule.one_le_finrank_iff]
      intro hker
      rw [ker_eq_bot'] at hker
      have hb1 : T (base 1) = 0 := by
        rw [apply_eigenvectorBasis, h1]
        simp
      have hb1' : base 1 = 0 := hker (base 1) hb1
      have hb1norm : ‖base 1‖ = 1 := base.norm_eq_one 1
      simp_all
    · rw [Nat.le_iff_lt_add_one, one_add_one_eq_two, ← h2]
      apply Submodule.finrank_lt
      intro hker
      rw [ker_eq_top] at hker
      have hb0 : T (base 0) = 0 := by
        simp [hker]
      have hb0norm : ‖base 0‖ = 1 := base.norm_eq_one 0
      have hb0' : T (base 0) ≠ 0 := by
        rw [apply_eigenvectorBasis, propext (smul_ne_zero_iff_left (base.orthonormal.ne_zero 0))]
        exact RCLike.ofReal_ne_zero.mpr h0
      exact hb0' hb0
  · symm
    rw [Module.End.eigenspace_zero, Submodule.finrank_eq_zero, ker_eq_bot']
    intro x hx
    rw [← OrthonormalBasis.sum_repr base x, Fin.sum_univ_two, map_add] at hx
    repeat rw [map_smul, apply_eigenvectorBasis] at hx
    rw [add_eq_zero_iff_neg_eq] at hx
    repeat rw [smul_smul] at hx
    have hinner : inner 𝕜 (-((base.repr x 0 * ↑(hT.eigenvalues h2 0)) • (hT.eigenvectorBasis h2) 0))
        ((base.repr x 1 * ↑(hT.eigenvalues h2 1)) • (hT.eigenvectorBasis h2) 1) = 0 := by
      simp [inner_neg_left, inner_smul_left, inner_smul_right]
    have h := (eq_iff_eq_zero_of_inner_eq_zero hinner).mp hx
    have h0' := h.left
    have h1' := h.right
    rw [neg_eq_zero, smul_eq_zero_iff_left (base.orthonormal.ne_zero 0), mul_eq_zero_iff_right (RCLike.ofReal_ne_zero.mpr h0)] at h0'
    rw [smul_eq_zero_iff_left (base.orthonormal.ne_zero 1), mul_eq_zero_iff_right (RCLike.ofReal_ne_zero.mpr h1)] at h1'
    rw [← base.repr.map_eq_zero_iff]
    ext i
    fin_cases i <;> simp [h0', h1']


lemma IsSymmetric.zero_eigenvalue_zero_or_one_of_finrank_ker_eq_one_of_finrank_eq_two (hT : T.IsSymmetric)
      (h2 : Module.finrank 𝕜 E = 2) (hker : Module.finrank 𝕜 (LinearMap.ker T) = 1) :
    hT.eigenvalues h2 0 = 0 ∨ hT.eigenvalues h2 1 = 0 := by
  have h := hT.zero_eigenvalues_eq_rank_ker_of_finrank_eq_two h2
  rw [hker, Finset.card_eq_one] at h
  rcases h with ⟨i, hi⟩
  have hi' : hT.eigenvalues h2 i = 0 := by
    rw [Finset.eq_singleton_iff_unique_mem] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.left
  fin_cases i
  · exact Or.inl hi'
  · exact Or.inr hi'

end LinearMap
