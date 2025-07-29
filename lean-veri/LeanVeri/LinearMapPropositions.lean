/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison, Jam Khan
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace

open scoped ComplexOrder

/-!
# Some basic propositions about `LinearMap`

This file contains some basic propositions about `LinearMap` that are not already in Mathlib.
Some of this may be later added to Mathlib.

For positive operators we use `LinearMap.IsPositive` from Mathlib, and for orthogonal projections
we use `IsStarProjection` from Mathlib.

-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

variable? [HilbertSpace 𝕜 F] => [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [FiniteDimensional 𝕜 F]

namespace LinearMap

/-- Partial density operators. -/
def isPartialDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.IsPositive ∧ trace 𝕜 E T ≤ 1

/-- Density operators. -/
def isDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.IsPositive ∧ trace 𝕜 E T = 1

/-- Quantum predicate. -/
def isEffect (T : E →ₗ[𝕜] E) : Prop :=
  T.IsPositive ∧ (id - T).IsPositive

/-- Isometry operators. -/
def isIsometry (T : E →ₗ[𝕜] F) : Prop :=
  T.adjoint ∘ₗ T = id

/-- Unitary operators. The same as isometry, but for `E →ₗ[𝕜] E`.
In Mathlib we have `IsUnit T`, but it is a different thing. -/
def isUnitary (T : E →ₗ[𝕜] E) : Prop :=
  T.isIsometry

/-- Pure state operators. -/
def isPureState (T : E →ₗ[𝕜] E) : Prop :=
  T.isDensityOperator ∧ T.rank = 1

/-- A pair of projection that covers the full space -/
def areProjMeas (T S : E →ₗ[𝕜] E) : Prop :=
  IsStarProjection T ∧ IsStarProjection S ∧ T + S = 1

omit [CompleteSpace E]

lemma IsStarProjection.apply_range {T : E →ₗ[𝕜] E} (hT : IsStarProjection T) {x : E} (hx : x ∈ range T) :
    T x = x := by
  obtain ⟨y, hy⟩ := hx
  rw [← hy, ← comp_apply, ← Module.End.mul_eq_comp, hT.isIdempotentElem]

lemma IsStarProjection.isSymmetric {T : E →ₗ[𝕜] E} (hT : IsStarProjection T) : T.IsSymmetric :=
  (isSymmetric_iff_isSelfAdjoint T).mpr hT.isSelfAdjoint

lemma IsStarProjection.comp_self {T : E →ₗ[𝕜] E} (hT : IsStarProjection T) :
    T ∘ₗ T = T := hT.isIdempotentElem

omit [FiniteDimensional 𝕜 E] in
lemma IsPositive.sub_of_LoewnerOrder {T S : E →ₗ[𝕜] E} (h : T ≤ S) :
    (S - T).IsPositive :=
  And.intro h.isSymmetric h.right

omit [FiniteDimensional 𝕜 E] in
lemma eq_zero_iff_forall_re_inner_eq_zero (T : E →ₗ[𝕜] E) :
    T = 0 ↔ ∀x y : E, RCLike.re (inner 𝕜 (T x) y) = 0 := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h
    apply LinearMap.ext
    intro x
    have hTx := h x (T x)
    rw [inner_self_eq_norm_mul_norm, mul_self_eq_zero] at hTx
    exact norm_eq_zero.mp hTx

lemma IsSelfAdjoint.eq_zero_iff_re_inner_app_self_eq_zero {T : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T) :
    T = 0 ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) = 0 := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h
    have aux : ∀x y : E, RCLike.re (inner 𝕜 (T x) y) = RCLike.re ((inner 𝕜 (T (x + y)) (x + y) - inner 𝕜 (T (x - y)) (x - y))) / 4 := by
      intro x y
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, map_sub, map_add, inner_re_symm (T y) x]
      rw [(isSymmetric_iff_isSelfAdjoint T).mpr hT]
      ring_nf
    have h' : ∀x y : E, RCLike.re (inner 𝕜 (T x) y) = 0 := by
      intro x y
      rw [aux, map_sub, h (x + y), h (x - y)]
      ring
    apply (eq_zero_iff_forall_re_inner_eq_zero T).mpr h'

lemma IsSelfAdjoint.eq_iff_forall_re_inner_app_self_eq {T N : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T)
    (hN : IsSelfAdjoint N) :
    T = N ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) = RCLike.re (inner 𝕜 (N x) x) := by
  have hT' : T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT
  have hN' : N.IsSymmetric := (isSymmetric_iff_isSelfAdjoint N).mpr hN
  have hTN : IsSelfAdjoint (T - N) := (isSymmetric_iff_isSelfAdjoint (T - N)).mp (hT'.sub hN')
  apply Iff.intro
  · intro h x
    rw [h]
  · intro h
    have hTN' : ∀x : E, RCLike.re (inner 𝕜 ((T - N) x) x) = 0 := by
      intro x
      rw [sub_apply, inner_sub_left, map_sub, sub_eq_zero]
      exact h x
    rw [← sub_eq_zero]
    exact (eq_zero_iff_re_inner_app_self_eq_zero hTN).mpr hTN'

/--
Characterization of when `RCLike.re (inner 𝕜 (T x) x)` is zero.
The proof works be decomposing `x` in the eigenbasis of `T`.
-/
lemma IsPositive.re_inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) = 0 ↔ T x = 0 := by
  -- Maybe there is a simple more abstract proof
  have hTsymm : T.IsSymmetric := hT.isSymmetric
  let n : ℕ := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  let base : OrthonormalBasis (Fin n) 𝕜 E := hTsymm.eigenvectorBasis hn
  let x_repr : EuclideanSpace 𝕜 (Fin n) := base.repr x
  apply Iff.intro
  · intro hx
    let diag : Finset (Fin n × Fin n) := Finset.univ.filter fun i ↦ i.1 = i.2
    have : RCLike.re (inner 𝕜 (T x) x) = ∑ i, ‖base.repr x i‖ ^ 2 * hTsymm.eigenvalues hn i := calc
      RCLike.re (inner 𝕜 (T x) x)
        = RCLike.re (inner 𝕜 (T (∑ i, base.repr x i • base i)) (∑ i, base.repr x i • base i)) := by rw [OrthonormalBasis.sum_repr base x]
      _ = RCLike.re (inner 𝕜 (∑ i, T (base.repr x i • base i)) (∑ i, base.repr x i • base i)) := by rw [map_sum T _ Finset.univ]
      _ = ∑ i, ∑ j, RCLike.re (inner 𝕜 (base.repr x j • T (base j)) (base.repr x i • base i)) := by simp [inner_sum, sum_inner]
      _ = ∑ i, ∑ j, RCLike.re (starRingEnd 𝕜 (base.repr x j) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn j) * (base.repr x i * inner 𝕜 (base j) (base i)))
        ) := by
          apply Fintype.sum_congr _ _
          intro i
          apply Fintype.sum_congr _ _
          intro j
          rw [hTsymm.apply_eigenvectorBasis, InnerProductSpace.smul_left, InnerProductSpace.smul_left, inner_smul_right_eq_smul]
          rfl
      _ = ∑ i, RCLike.re (starRingEnd 𝕜 (base.repr x i) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn i) * (base.repr x i * inner 𝕜 (base i) (base i)))
        ) := by
          have hij : ∀i, ∀j, j ≠ i → RCLike.re (starRingEnd 𝕜 (base.repr x j) *
            (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn j) * (base.repr x i * inner 𝕜 (base j) (base i))))= 0 := by
            intro i j hnij
            simp [base.inner_eq_zero hnij]
          have hi := fun i ↦ Fintype.sum_eq_single i (hij i)
          simp +contextual only [hi]
      _ = ∑ i, RCLike.re (starRingEnd 𝕜 (base.repr x i) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn i) * base.repr x i)
        ) := by simp +contextual [base.inner_eq_one]
      _ = ∑ i, RCLike.re (starRingEnd 𝕜 (base.repr x i) * base.repr x i * ↑(hTsymm.eigenvalues hn i)
        ) := by
          apply Fintype.sum_congr _ _
          intro i
          rw [RCLike.conj_ofReal]
          ring_nf
      _ = ∑ i, RCLike.re ((‖base.repr x i‖ : 𝕜)^2 * ↑(hTsymm.eigenvalues hn i)) := by
          simp +contextual [RCLike.conj_mul]
      _ = ∑ i, ‖base.repr x i‖^2 * hTsymm.eigenvalues hn i := by
          apply Fintype.sum_congr _ _
          intro i
          rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    rw [this] at hx
    have : ∀i, 0 ≤ ‖base.repr x i‖ ^ 2 * hTsymm.eigenvalues hn i := by
      intro i
      rw [mul_nonneg_iff]
      apply Or.inl
      apply And.intro
      · exact sq_nonneg ‖base.repr x i‖
      · exact hT.nonneg_eigenvalues hn i
    rw [Fintype.sum_eq_zero_iff_of_nonneg this, funext_iff] at hx
    simp only [Pi.zero_apply, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at hx
    rw [← base.sum_repr x, map_sum T _ Finset.univ]
    simp only [map_smul]
    simp_rw [base, hTsymm.apply_eigenvectorBasis]
    simp +contextual only [smul_smul]
    apply Fintype.sum_eq_zero
    intro i
    apply smul_eq_zero_of_left
    have hxi : base.repr x i = 0 ∨ hTsymm.eigenvalues hn i = 0 := hx i
    apply hxi.elim
    · intro hxi0
      exact mul_eq_zero_of_left hxi0 ↑(hTsymm.eigenvalues hn i)
    · intro hxi0
      apply mul_eq_zero_of_right
      exact RCLike.ofReal_eq_zero.mpr hxi0
  · intro hx
    rw [hx]
    simp

theorem IsPositive.inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    inner 𝕜 (T x) x = 0 ↔ T x = 0 := by
  apply Iff.intro
  · intro hx
    have hx' : RCLike.re (inner 𝕜 (T x) x) = 0 := by
      rw [hx]
      exact RCLike.zero_re
    exact (re_inner_app_eq_zero_iff_app_eq_zero hT x).mp hx'
  · intro hx
    rw [hx]
    simp

omit [FiniteDimensional 𝕜 E] in
lemma isDensityOperator.neZero {T : E →ₗ[𝕜] E} (hT : T.isDensityOperator) : T ≠ 0 := by
  intro h
  have htr := hT.right
  rw [h] at htr
  simp_all

lemma LoewnerOrder_iff_of_IsPositive {T N : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hN : N.IsPositive) :
    T ≤ N ↔ ∀x : E, 0 ≤ RCLike.re (inner 𝕜 ((N - T) x) x) := by
  apply Iff.intro
  · intro h
    exact (IsPositive.sub_of_LoewnerOrder h).right
  · intro h
    exact And.intro
      ((isSymmetric_iff_isSelfAdjoint _).mpr (IsSelfAdjoint.sub hN.isSelfAdjoint hT.isSelfAdjoint))
      h

lemma LoewnerOrder_iff_of_IsPositive' {T N : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hN : N.IsPositive) :
    T ≤ N ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (N x) x) := by
  rw [LoewnerOrder_iff_of_IsPositive hT hN]
  apply forall_congr'
  intro x
  calc
    0 ≤ RCLike.re (inner 𝕜 ((N - T) x) x)
    ↔ 0 ≤ RCLike.re (inner 𝕜 (N x - T x) x) := by rfl
  _ ↔ 0 ≤ RCLike.re (inner 𝕜 (N x) x - inner 𝕜 (T x) x) := by rw [inner_sub_left]
  _ ↔ 0 ≤ RCLike.re (inner 𝕜 (N x) x) - RCLike.re (inner 𝕜 (T x) x) := by rw [map_sub]
  _ ↔ RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (N x) x) := by apply sub_nonneg

end LinearMap
