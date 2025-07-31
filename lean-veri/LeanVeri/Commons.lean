/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct
import LeanVeri.Projection
import LeanVeri.ProjectionSubmodule
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
Some vectors and linear maps that are commonly used in quantum computing.
-/

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

open LinearMap

/-- Ket zero, usually denoted as |0⟩. -/
def ket0 : 𝕜² := !₂[1, 0]

/-- Ket one, usually denoted as |1⟩. -/
def ket1 : 𝕜² := !₂[0, 1]

/-- Ket plus, usually denoted as |+⟩. -/
noncomputable def ketP : 𝕜² := (1/√2 : 𝕜) • (ket0 + ket1)

/-- Ket minus, usually denoted as |-⟩. -/
noncomputable def ketM : 𝕜² := (1/√2 : 𝕜) • (ket0 - ket1)

/-- Ket one times bra one, usually denoted as |1⟩⟨1|. -/
def ketbra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ket1

/-- Ket one times bra one, usually denoted as |1⟩⟨0|. -/
def ket1bra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ket0

/-- Ket one times bra one, usually denoted as |0⟩⟨1|. -/
def ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ket1

/-- Ket zero times bra zero, usually denoted as |0⟩⟨0|. -/
def ketbra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ket0

/-- Ket plus times bra plus, usually denoted as |+⟩⟨+|. -/
noncomputable def ketbraP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ketP

/-- Ket minus times bra minus, usually denoted as |-⟩⟨-|. -/
noncomputable def ketbraM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ketM

/-- Ket plus times bra minus, usually denoted as |+⟩⟨-|. -/
noncomputable def ketPbraM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ketM

/-- Ket minus times bra plus, usually denoted as |-⟩⟨+|. -/
noncomputable def ketMbraP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ketP

/-- Ket zero times bra plus, usually denoted as |0⟩⟨+|. -/
noncomputable def ket0braP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ketP

/-- Ket one times bra plus, usually denoted as |1⟩⟨+|. -/
noncomputable def ket1braP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ketP

/-- Ket zero times bra minus, usually denoted as |0⟩⟨-|. -/
noncomputable def ket0braM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ketM

/-- Ket one times bra minus, usually denoted as |1⟩⟨-|. -/
noncomputable def ket1braM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ketM

/-- Ket plus times bra zero, usually denoted as |+⟩⟨0|. -/
noncomputable def ketPbra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ket0

/-- Ket plus times bra one, usually denoted as |+⟩⟨1|. -/
noncomputable def ketPbra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ket1

/-- Ket minus times bra zero, usually denoted as |-⟩⟨0|. -/
noncomputable def ketMbra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ket0

/-- Ket minus times bra one, usually denoted as |-⟩⟨1|. -/
noncomputable def ketMbra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ket1

/-- Hadamard gate, usually denoted as H. -/
noncomputable def Hadamard : 𝕜² →ₗ[𝕜] 𝕜² := ket0braP + ket1braM

noncomputable def PauliX : 𝕜² →ₗ[𝕜] 𝕜² := ket0bra1 + ket1bra0

lemma ketP_eq : ketP = (!₂[1/√2, 1/√2] : 𝕜²) := by
  unfold ketP ket0 ket1
  simp [← WithLp.toLp_add, ← WithLp.toLp_smul]

lemma ketM_eq : ketM = (!₂[1/√2, -1/√2] : 𝕜²) := by
  unfold ketM ket0 ket1
  simp only [← WithLp.toLp_sub, ← WithLp.toLp_smul]
  field_simp

lemma norm_ket0 : norm (ket0 : 𝕜²) = 1 := by
  unfold norm PiLp.instNorm
  simp [ket0]

lemma norm_ket1 : norm (ket1 : 𝕜²) = 1 := by
  unfold norm PiLp.instNorm
  simp [ket1]

lemma norm_ketP : norm (ketP : 𝕜²) = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketP, ket0, ket1]

lemma norm_ketM : norm (ketM : 𝕜²) = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketM, ket0, ket1]

lemma isSelfAdjoint_ketbra0 : IsSelfAdjoint (ketbra0 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isSelfAdjoint_outerProduct_self 𝕜 ket0

lemma isSelfAdjoint_ketbra1 : IsSelfAdjoint (ketbra1 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isSelfAdjoint_outerProduct_self 𝕜 ket1

lemma IsStarProjection_ketbraP : IsStarProjection (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isStarProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketP

lemma IsStarProjection_ketbraM : IsStarProjection (ketbraM : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isStarProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketM


lemma inner_ket0_ket0 : inner 𝕜 (ket0 : 𝕜²) ket0 = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ket0 norm_ket0).mpr rfl

lemma inner_ket1_ket1 : inner 𝕜 (ket1 : 𝕜²) ket1 = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ket1 norm_ket1).mpr rfl

lemma inner_ket0_ket1 : inner 𝕜 (ket0 : 𝕜²) ket1 = 0 := by
  unfold ket0 ket1
  simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, map_one, mul_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_zero, mul_zero, add_zero]

lemma inner_ket1_ket0 : inner 𝕜 (ket1 : 𝕜²) ket0 = 0 := by
  unfold ket1 ket0
  simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, map_zero, mul_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_one, mul_one, add_zero]

lemma inner_ketP_ketP : inner 𝕜 (ketP : 𝕜²) ketP = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketP norm_ketP).mpr rfl

lemma inner_ketM_ketM : inner 𝕜 (ketM : 𝕜²) ketM = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketM norm_ketM).mpr rfl

lemma neZero_ket0 : (ket0 : 𝕜²) ≠ 0 := by
  rw [← norm_pos_iff, norm_ket0]
  exact Real.zero_lt_one

lemma neZero_ket1 : (ket1 : 𝕜²) ≠ 0 := by
  rw [← norm_pos_iff, norm_ket1]
  exact Real.zero_lt_one

lemma neZero_ketP : (ketP : 𝕜²) ≠ 0 := by
  rw [← norm_pos_iff, norm_ketP]
  exact Real.zero_lt_one

lemma neZero_ketM : (ketM : 𝕜²) ≠ 0 := by
  rw [← norm_pos_iff, norm_ketM]
  exact Real.zero_lt_one

lemma isPositive_ketbra0 : LinearMap.IsPositive (ketbra0 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isPositive_outerProduct_self 𝕜 ket0

lemma isPositive_ketbra1 : LinearMap.IsPositive (ketbra1 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isPositive_outerProduct_self 𝕜 ket1

lemma IsStarProjection_ketbra0 : IsStarProjection (ketbra0 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isStarProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ket0

lemma IsStarProjection_ketbra1 : IsStarProjection (ketbra1 : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isStarProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ket1

lemma isSelfAdjoint_ketbraP : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbraP :=
  isSelfAdjoint_outerProduct_self 𝕜 ketP

lemma isSelfAdjoint_ketbraM : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbraM :=
  isSelfAdjoint_outerProduct_self 𝕜 ketM

lemma isPositive_ketbraP : LinearMap.IsPositive (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isPositive_outerProduct_self 𝕜 ketP

lemma isPositive_ketbraM : LinearMap.IsPositive (ketbraM : 𝕜² →ₗ[𝕜] 𝕜²) :=
  isPositive_outerProduct_self 𝕜 ketM

lemma inner_ketP_ket0 : inner 𝕜 (ketP : 𝕜²) ket0 = 1/√2 :=
  calc
    inner 𝕜 (ketP : 𝕜²) ket0
      = inner 𝕜 ((1/√2 : 𝕜) • (ket0 + ket1)) ket0 := rfl
    _ = (1/√2 : 𝕜) * inner 𝕜 (ket0 + ket1 : 𝕜²) ket0 := by rw [inner_smul_left]; simp
    _ = (1/√2 : 𝕜) * (inner 𝕜 ket0 ket0 + inner 𝕜 ket1 ket0) := by rw [inner_add_left]
    _ = (1/√2 : 𝕜) * (1 + 0) := by rw [inner_ket0_ket0, inner_ket1_ket0]
    _ = 1/√2 := by simp

lemma inner_ket0_ketP : inner 𝕜 (ket0 : 𝕜²) ketP = 1/√2 := by
  rw [← inner_conj_symm, inner_ketP_ket0]
  simp

lemma inner_ketP_ket1 : inner 𝕜 (ketP : 𝕜²) ket1 = 1/√2 :=
  calc
    inner 𝕜 (ketP : 𝕜²) ket1
      = inner 𝕜 ((1/√2 : 𝕜) • (ket0 + ket1)) ket1 := rfl
    _ = (1/√2 : 𝕜) * inner 𝕜 (ket0 + ket1 : 𝕜²) ket1 := by rw [inner_smul_left]; simp
    _ = (1/√2 : 𝕜) * (inner 𝕜 ket0 ket1 + inner 𝕜 ket1 ket1) := by rw [inner_add_left]
    _ = (1/√2 : 𝕜) * (0 + 1) := by rw [inner_ket0_ket1, inner_ket1_ket1]
    _ = 1/√2 := by simp

lemma inner_ket1_ketP : inner 𝕜 (ket1 : 𝕜²) ketP = 1/√2 := by
  rw [← inner_conj_symm, inner_ketP_ket1]
  simp

lemma inner_ketM_ket0 : inner 𝕜 (ketM : 𝕜²) ket0 = 1/√2 :=
  calc
    inner 𝕜 (ketM : 𝕜²) ket0
      = inner 𝕜 ((1/√2 : 𝕜) • (ket0 - ket1)) ket0 := rfl
    _ = (1/√2 : 𝕜) * inner 𝕜 (ket0 - ket1 : 𝕜²) ket0 := by rw [inner_smul_left]; simp
    _ = (1/√2 : 𝕜) * (inner 𝕜 ket0 ket0 - inner 𝕜 ket1 ket0) := by rw [inner_sub_left]
    _ = (1/√2 : 𝕜) * (1 - 0) := by rw [inner_ket0_ket0, inner_ket1_ket0]
    _ = 1/√2 := by simp

lemma inner_ket0_ketM : inner 𝕜 (ket0 : 𝕜²) ketM = 1/√2 := by
  rw [← inner_conj_symm, inner_ketM_ket0]
  simp

lemma inner_ketM_ket1 : inner 𝕜 (ketM : 𝕜²) ket1 = - (1/√2) :=
  calc
    inner 𝕜 (ketM : 𝕜²) ket1
      = inner 𝕜 ((1/√2 : 𝕜) • (ket0 - ket1)) ket1 := rfl
    _ = (1/√2 : 𝕜) * inner 𝕜 (ket0 - ket1 : 𝕜²) ket1 := by rw [inner_smul_left]; simp
    _ = (1/√2 : 𝕜) * (inner 𝕜 ket0 ket1 - inner 𝕜 ket1 ket1) := by rw [inner_sub_left]
    _ = (1/√2 : 𝕜) * (0 - 1) := by rw [inner_ket0_ket1, inner_ket1_ket1]
    _ = - (1/√2) := by simp

lemma inner_ket1_ketM : inner 𝕜 (ket1 : 𝕜²) ketM = - (1/√2) := by
  rw [← inner_conj_symm, inner_ketM_ket1]
  simp

lemma inner_ketM_ketP : inner 𝕜 (ketM : 𝕜²) ketP = 0 :=
  calc
    inner 𝕜 (ketM : 𝕜²) ketP
      = inner 𝕜 ((1/√2 : 𝕜) • (ket0 - ket1)) ((1/√2 : 𝕜) • (ket0 + ket1)) := rfl
    _ = starRingEnd 𝕜 (1/√2 : 𝕜) * (1/√2 : 𝕜) * inner 𝕜 (ket0 - ket1) (ket0 + ket1) := by rw [inner_smul_left, inner_smul_right, mul_assoc]
    _ = 1/2 * @inner 𝕜 𝕜² _ (ket0 - ket1) (ket0 + ket1) := by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]
    _ = 1/2 * (inner 𝕜 ket0 (ket0 + ket1) - inner 𝕜 ket1 (ket0 + ket1)) := by rw [inner_sub_left]
    _ = 1/2 * (inner 𝕜 ket0 ket0 + inner 𝕜 ket0 ket1 - (inner 𝕜 ket1 ket0 + inner 𝕜 ket1 ket1)) := by repeat rw [inner_add_right]
    _ = 1/2 * (1 + 0 - (0 + 1)) := by rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
    _ = 0 := by ring

lemma inner_ketP_ketM : @inner 𝕜 𝕜² _ ketP ketM = 0 :=
  inner_eq_zero_symm.mp inner_ketM_ketP

lemma adjoint_ketbra0 : ketbra0.adjoint = ketbra0 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket0 ket0
lemma adjoint_ket0bra1 : ket0bra1.adjoint = ket1bra0 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket0 ket1
lemma adjoint_ket1bra0 : ket1bra0.adjoint = ket0bra1 (𝕜 := 𝕜) := adjoint_outerProduct  𝕜 ket1 ket0
lemma adjoint_ketbra1 : ketbra1.adjoint = ketbra1 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket1 ket1
lemma adjoint_ketbraP : ketbraP.adjoint = ketbraP (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketP ketP
lemma adjoint_ketbraM : ketbraM.adjoint = ketbraM (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketM ketM
lemma adjoint_ketPbraM : ketPbraM.adjoint = ketMbraP (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketP ketM
lemma adjoint_ketMbraP : ketMbraP.adjoint = ketPbraM (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketM ketP
lemma adjoint_ket0braP : ket0braP.adjoint = ketPbra0 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket0 ketP
lemma adjoint_ket1braP : ket1braP.adjoint = ketPbra1 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket1 ketP
lemma adjoint_ket0braM : ket0braM.adjoint = ketMbra0 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket0 ketM
lemma adjoint_ket1braM : ket1braM.adjoint = ketMbra1 (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ket1 ketM
lemma adjoint_ketPbra0 : ketPbra0.adjoint = ket0braP (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketP ket0
lemma adjoint_ketPbra1 : ketPbra1.adjoint = ket1braP (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketP ket1
lemma adjoint_ketMbra0 : ketMbra0.adjoint = ket0braM (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketM ket0
lemma adjoint_ketMbra1 : ketMbra1.adjoint = ket1braM (𝕜 := 𝕜) := adjoint_outerProduct 𝕜 ketM ket1

lemma ket0_eq_ketP_add_ketM : (ket0 : 𝕜²) = (1/√2 : 𝕜) • (ketP + ketM) := by
  unfold ketM ketP
  rw [← smul_add, add_add_sub_cancel, smul_smul,
    show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat],
    smul_add, ← add_smul, add_halves, one_smul]

lemma ket1_eq_ketP_sub_ketM : (ket1 : 𝕜²) = (1/√2 : 𝕜) • (ketP - ketM) := by
  unfold ketM ketP
  rw [← smul_sub, add_sub_sub_cancel, smul_smul,
    show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat],
    smul_add, ← add_smul, add_halves, one_smul]

lemma ketbra0_add_ketbra1_eq : ketbra0 + ketbra1 = (1 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ketbra0 ketbra1
  refine LinearMap.ext_iff.mpr ?_
  simp only [LinearMap.add_apply, Module.End.one_apply]
  intro x
  repeat rw [outerProduct_assoc_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, Fin.isValue]
  unfold ket0 ket1
  simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, map_one, mul_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero, mul_zero, add_zero, zero_add]
  ext i
  simp
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, mul_one, mul_zero, add_zero]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, mul_one, zero_add]

lemma ketbra1_add_ketbra0_eq : ketbra1 + ketbra0 = (1 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  rw [add_comm]
  exact ketbra0_add_ketbra1_eq

lemma ketbra0_eq : ketbra0 = (1/2 : 𝕜) • ketbraP + (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM :=
  calc
    ketbra0
      = outerProduct 𝕜 ket0 ket0 := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ketP + ketM)) ket0 := by nth_rw 1 [ket0_eq_ketP_add_ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ketP + ketM) ket0 := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ketP ket0 + outerProduct 𝕜 ketM ket0) := by rw [RCLike.ofReal_alg, outerProduct_add_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ket0 + (1/√2 : 𝕜) • outerProduct 𝕜 ketM ket0 := by rw [smul_add]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ((1/√2 : 𝕜) • (ketP + ketM)) + (1/√2 : 𝕜) • outerProduct 𝕜 ketM ((1/√2 : 𝕜) • (ketP + ketM)) := by
      repeat rw [ket0_eq_ketP_add_ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketP (ketP + ketM) + (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketM (ketP + ketM) := by
      rw [← smul_add]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_add]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ketP (ketP + ketM) + (1/2 : 𝕜) • outerProduct 𝕜 ketM (ketP + ketM) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbraP + (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM := by
      repeat rw [outerProduct_add_right]
      simp only [smul_add]
      rw [← ketbraM, ← ketMbraP, ← ketPbraM, ← ketbraP]
      abel

lemma ketbra1_eq : ketbra1 = (1/2 : 𝕜) • ketbraP - (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM :=
  calc
    ketbra1
      = outerProduct 𝕜 ket1 ket1 := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ketP - ketM)) ket1 := by nth_rw 1 [ket1_eq_ketP_sub_ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ketP - ketM) ket1 := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ketP ket1 - outerProduct 𝕜 ketM ket1) := by
      rw [RCLike.ofReal_alg, outerProduct_sub_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ket1 - (1/√2 : 𝕜) • outerProduct 𝕜 ketM ket1 := by
      rw [smul_sub]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ((1/√2 : 𝕜) • (ketP - ketM)) - (1/√2 : 𝕜) • outerProduct 𝕜 ketM ((1/√2 : 𝕜) • (ketP - ketM)) := by
      repeat rw [ket1_eq_ketP_sub_ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketP (ketP - ketM) - (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketM (ketP - ketM) := by
      rw [← smul_sub]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_sub]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ketP (ketP - ketM) - (1/2 : 𝕜) • outerProduct 𝕜 ketM (ketP - ketM) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbraP - (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM := by
      repeat rw [outerProduct_sub_right]
      simp only [smul_sub]
      rw [← ketbraM, ← ketMbraP, ← ketPbraM, ← ketbraP]
      abel

lemma ketbraP_eq : ketbraP = (1/2 : 𝕜) • ketbra0 + (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 :=
  calc
    ketbraP
      = outerProduct 𝕜 ketP ketP := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ket0 + ket1)) ketP  := by nth_rw 1 [ketP]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ket0 + ket1) ketP    := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ket0 ketP + outerProduct 𝕜 ket1 ketP) := by
      rw [RCLike.ofReal_alg, outerProduct_add_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ketP + (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ketP := by
      rw [smul_add]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ((1/√2 : 𝕜) • (ket0 + ket1)) + (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ((1/√2 : 𝕜) • (ket0 + ket1)) := by
      repeat rw [ketP]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 + ket1) + (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 + ket1) := by
      rw [← smul_add]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_add]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 + ket1) + (1/2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 + ket1) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbra0 + (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 := by
      repeat rw [outerProduct_add_right]
      simp only [smul_add]
      rw [← ketbra0, ← ket1bra0, ← ket0bra1, ← ketbra1]
      abel

lemma ketbraM_eq : ketbraM = (1/2 : 𝕜) • ketbra0 - (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) • ket1bra0 + (1/2 : 𝕜) • ketbra1 :=
  calc
    ketbraM
      = outerProduct 𝕜 ketM ketM                          := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ket0 - ket1)) ketM  := by nth_rw 1 [ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ket0 - ket1) ketM    := by
      apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ket0 ketM - outerProduct 𝕜 ket1 ketM) := by
      rw [RCLike.ofReal_alg, outerProduct_sub_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ketM - (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ketM := by
      rw [smul_sub]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ((1/√2 : 𝕜) • (ket0 - ket1)) - (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ((1/√2 : 𝕜) • (ket0 - ket1)) := by
      repeat rw [ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 - ket1) - (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 - ket1) := by
      rw [← smul_sub]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal]
      rw [smul_sub]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 - ket1) - (1/2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 - ket1) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbra0 - (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 := by
      repeat rw [outerProduct_sub_right]
      simp only [smul_sub]
      rw [← ketbra0, ← ket1bra0, ← ket0bra1, ← ketbra1]
      abel

lemma ketbraP_eq_one_sub_ketbraM : ketbraP = (1 : 𝕜² →ₗ[𝕜] 𝕜²) - ketbraM := by
  rw [eq_sub_iff_add_eq]
  rw [ketbraP_eq, ketbraM_eq]
  simp only
  abel_nf
  repeat rw [← smul_assoc]
  repeat rw [one_div]
  simp only [zsmul_eq_mul, Int.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.mul_inv_cancel, one_smul]
  apply ketbra0_add_ketbra1_eq

lemma ketbraP_add_ketbraM_eq : ketbraP + ketbraM = (1 : 𝕜² →ₗ[𝕜] 𝕜²)  := by
  rw [← eq_sub_iff_add_eq]
  apply ketbraP_eq_one_sub_ketbraM

lemma ket1bra0_comp_ket1bra0_eq : ket1bra0 ∘ₗ ket1bra0 = (0 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ket1bra0
  rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct, inner_ket0_ket1]
  simp

lemma ket0bra1_comp_ket0bra1_eq : ket0bra1 ∘ₗ ket0bra1 = (0 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ket0bra1
  rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct, inner_ket1_ket0]
  simp

lemma ket1bra0_comp_ket0bra1_eq : ket1bra0 ∘ₗ ket0bra1 = (ketbra1 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ket1bra0 ket0bra1 ketbra1
  rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct, inner_ket0_ket0]
  simp

lemma ket0bra1_comp_ket1bra0_eq : ket0bra1 ∘ₗ ket1bra0 = (ketbra0 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ket0bra1 ket1bra0 ketbra0
  rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct, inner_ket1_ket1]
  simp

lemma ketbraP_ket0_eq : (ketbraP ket0 : 𝕜²) = (1 / √2 : 𝕜) • ketP := by
  unfold ketbraP
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ketP_ket0]

lemma ketbraP_ket1_eq : (ketbraP ket1 : 𝕜²) = (1 / √2 : 𝕜) • ketP := by
  unfold ketbraP
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ketP_ket1]

lemma ketbra0_ketP_eq : (ketbra0 ketP : 𝕜²) = (1 / √2 : 𝕜) • ket0 := by
  unfold ketbra0
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ket0_ketP]

lemma ketbra1_ketP_eq : (ketbra1 ketP : 𝕜²) = (1 / √2 : 𝕜) • ket1 := by
  unfold ketbra1
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ket1_ketP]

lemma hadamard_ketP_eq : Hadamard ketP = (ket0 : 𝕜²) := by
  unfold Hadamard ket0braP ket1braM
  rw [LinearMap.add_apply, outerProduct_def, outerProduct_def, inner_ketP_ketP, inner_ketM_ketP]
  simp

lemma adj_Hadamard_eq : Hadamard.adjoint = outerProduct 𝕜 ketP ket0 + outerProduct 𝕜 ketM ket1 := by
  unfold Hadamard ket0braP ket1braM
  simp [adjoint_outerProduct]

lemma adj_Hadamard_ketbraP_eq' :
    Hadamard.adjoint * (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) * Hadamard = ketbra0 := by
  rw [adj_Hadamard_eq, Hadamard]
  unfold ket0braP ket1braM ketbraP
  rw [left_distrib]
  repeat rw [right_distrib]
  repeat rw [outerProduct_mul_outerProduct_eq_inner_smul_outerProduct]
  repeat rw [smul_mul_assoc]
  repeat rw [outerProduct_mul_outerProduct_eq_inner_smul_outerProduct]
  repeat rw [inner_ketP_ket0, inner_ket0_ketP, inner_ketP_ket1, inner_ket1_ketP]
  repeat rw [smul_smul]
  repeat rw [show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
  rw [← ketbraP, ← ketMbraP, ← ketPbraM, ← ketbraM, ketbra0_eq]
  abel

lemma adj_Hadamard_ketbraP_eq :
    Hadamard.adjoint ∘ₗ (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) ∘ₗ Hadamard = ketbra0 := by
  repeat rw [← Module.End.mul_eq_comp]
  rw [← mul_assoc]
  exact adj_Hadamard_ketbraP_eq'

lemma isSymmetric_Hadamard : LinearMap.IsSymmetric (Hadamard (𝕜 := 𝕜)) := by
  intro x y
  unfold Hadamard
  repeat rw [LinearMap.add_apply]
  rw [inner_add_left, inner_add_right]
  unfold ket0braP ket1braM
  repeat rw [outerProduct_def]
  repeat rw [inner_smul_left, inner_smul_right]
  unfold ketP ketM
  repeat rw [inner_smul_left]
  repeat rw [inner_add_left, inner_sub_left]
  ring_nf
  repeat rw [map_add, map_sub]
  repeat rw [(starRingEnd 𝕜).map_mul]
  repeat rw [RCLike.conj_conj]
  repeat rw [InnerProductSpace.conj_inner_symm]
  simp only [map_inv₀, RCLike.conj_ofReal]
  ring

lemma isSelfAdjoint_Hadamard : IsSelfAdjoint (Hadamard (𝕜 := 𝕜)) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp isSymmetric_Hadamard

lemma isUnitary_Hadamard : LinearMap.isUnitary (Hadamard (𝕜 := 𝕜)) := by
  unfold LinearMap.isUnitary LinearMap.isIsometry
  rw [isSymmetric_Hadamard.adjoint_eq]
  unfold Hadamard
  rw [LinearMap.comp_add]
  repeat rw [LinearMap.add_comp]
  unfold ket0braP ket1braM
  repeat rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct]
  rw [inner_ketP_ket0, inner_ketP_ket1, inner_ketM_ket0, inner_ketM_ket1]
  unfold ketP ketM
  repeat rw [outerProduct_smul_assoc_right]
  repeat rw [smul_smul]
  simp only [one_div, map_inv₀, RCLike.conj_ofReal]
  field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]
  repeat rw [outerProduct_add_right, outerProduct_sub_right]
  repeat rw [smul_add, smul_sub]
  repeat rw [neg_div]
  repeat rw [neg_smul]
  abel_nf
  repeat rw [two_zsmul]
  repeat rw [← two_smul 𝕜]
  repeat rw [smul_smul]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, one_smul]
  rw [← ketbra0, ← ketbra1, ketbra0_add_ketbra1_eq]
  rfl

lemma isSelfAdjoint_PauliX : IsSelfAdjoint (PauliX (𝕜 := 𝕜)) := by
  unfold PauliX
  rw [LinearMap.isSelfAdjoint_iff', map_add, adjoint_ket0bra1, adjoint_ket1bra0, add_comm]

lemma isUnitary_PauliX : LinearMap.isUnitary (PauliX (𝕜 := 𝕜)) := by
  unfold LinearMap.isUnitary LinearMap.isIsometry
  rw [LinearMap.isSelfAdjoint_iff'.mp isSelfAdjoint_PauliX]
  unfold PauliX
  rw [LinearMap.comp_add]
  repeat rw [LinearMap.add_comp]
  simp [ket1bra0_comp_ket1bra0_eq, ket0bra1_comp_ket0bra1_eq, ket1bra0_comp_ket0bra1_eq,
    ket0bra1_comp_ket1bra0_eq, ketbra1_add_ketbra0_eq]
  rfl

lemma span_ketP_eq_span_ketM_comp : (𝕜 ∙ ketP : Submodule 𝕜 𝕜²) = (𝕜 ∙ ketM)ᗮ :=
  Submodule.span_singleton_eq_orthogonal_of_inner_eq_zero finrank_euclideanSpace_fin
  neZero_ketP neZero_ketM inner_ketP_ketM

lemma span_ketM_eq_span_ketP_comp : (𝕜 ∙ ketM : Submodule 𝕜 𝕜²) = (𝕜 ∙ ketP)ᗮ :=
  Submodule.span_singleton_eq_orthogonal_of_inner_eq_zero finrank_euclideanSpace_fin
  neZero_ketM neZero_ketP inner_ketM_ketP

lemma ker_ketbraP_eq : LinearMap.ker (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) = 𝕜 ∙ ketM := by
  ext x
  simp only [LinearMap.mem_ker]
  unfold ketbraP
  rw [outerProduct_def, smul_eq_zero_iff_left neZero_ketP]
  exact Submodule.inner_eq_zero_iff_mem_span_singleton_of_inner_eq_zero
    finrank_euclideanSpace_fin neZero_ketP neZero_ketM inner_ketP_ketM

lemma ker_ketbraM_eq : LinearMap.ker (ketbraM : 𝕜² →ₗ[𝕜] 𝕜²) = 𝕜 ∙ ketP := by
  ext x
  simp only [LinearMap.mem_ker]
  unfold ketbraM
  rw [outerProduct_def, smul_eq_zero_iff_left neZero_ketM]
  exact Submodule.inner_eq_zero_iff_mem_span_singleton_of_inner_eq_zero
    finrank_euclideanSpace_fin neZero_ketM neZero_ketP inner_ketM_ketP

lemma toSubmodule_ketbraP_eq : (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²).toSubmodule = 𝕜 ∙ ketP := by
  unfold LinearMap.toSubmodule
  rw [ker_ketbraP_eq]
  exact span_ketP_eq_span_ketM_comp.symm

lemma toSubmodule_ketbraM_eq : (ketbraM : 𝕜² →ₗ[𝕜] 𝕜²).toSubmodule = 𝕜 ∙ ketM := by
  unfold LinearMap.toSubmodule
  rw [ker_ketbraM_eq]
  exact span_ketM_eq_span_ketP_comp.symm

lemma finrank_toSubmodule_ketbraP : Module.finrank 𝕜 (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²).toSubmodule = 1 := by
  rw [toSubmodule_ketbraP_eq]
  exact finrank_span_singleton neZero_ketP

lemma finrank_toSubmodule_ketbraM : Module.finrank 𝕜 (ketbraM : 𝕜² →ₗ[𝕜] 𝕜²).toSubmodule = 1 := by
  rw [toSubmodule_ketbraM_eq]
  exact finrank_span_singleton neZero_ketM

def stBasis_val : Fin 2 → 𝕜²
  | 0 => ket0
  | 1 => ket1

lemma Orthonormal_stBasis_val : Orthonormal 𝕜 (E := 𝕜²) stBasis_val := by
  apply And.intro
  · intro i
    fin_cases i
    · exact norm_ket0
    · exact norm_ket1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
    · simp only [stBasis_val]
      exact inner_ket0_ket1
    · simp only [stBasis_val]
      exact inner_ket1_ket0

noncomputable def stBasis : Module.Basis (Fin 2) 𝕜 𝕜² :=
  basisOfOrthonormalOfCardEqFinrank Orthonormal_stBasis_val finrank_euclideanSpace_fin.symm

lemma stBasis_eq_stBasis_val : (stBasis : Fin 2 → 𝕜²) = stBasis_val := by
  apply funext_iff.mpr
  intro i
  simp [stBasis]

lemma Orthonormal_stBasis : Orthonormal 𝕜 (E := 𝕜²) stBasis := by
  rw [stBasis_eq_stBasis_val]
  exact Orthonormal_stBasis_val

noncomputable def stOrthonormalBasis : OrthonormalBasis (Fin 2) 𝕜 𝕜² :=
  stBasis.toOrthonormalBasis (E := 𝕜²) Orthonormal_stBasis

lemma stOrthonormalBasis_eq_stBasis_val :
    (stOrthonormalBasis (𝕜 := 𝕜) : Fin 2 → 𝕜²) = stBasis_val := by
  simp only [stOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis]
  exact stBasis_eq_stBasis_val

lemma trace_ketbra0 : ketbra0.trace 𝕜 𝕜² = 1 := by
  unfold ketbra0
  rw [trace_outerProduct ket0 ket0 stOrthonormalBasis]
  exact inner_ket0_ket0

lemma trace_ketbra1 : ketbra1.trace 𝕜 𝕜² = 1 := by
  unfold ketbra1
  rw [trace_outerProduct ket1 ket1 stOrthonormalBasis]
  exact inner_ket1_ket1

lemma trace_ketbraP : ketbraP.trace 𝕜 𝕜² = 1 := by
  unfold ketbraP
  rw [trace_outerProduct ketP ketP stOrthonormalBasis]
  exact inner_ketP_ketP

lemma trace_ketbraM : ketbraM.trace 𝕜 𝕜² = 1 := by
  unfold ketbraM
  rw [trace_outerProduct ketM ketM stOrthonormalBasis]
  exact inner_ketM_ketM

lemma trace_ket0bra1 : ket0bra1.trace 𝕜 𝕜² = 0 := by
  unfold ket0bra1
  rw [trace_outerProduct ket0 ket1 stOrthonormalBasis]
  exact inner_ket1_ket0

lemma trace_ket1bra0 : ket1bra0.trace 𝕜 𝕜² = 0 := by
  unfold ket1bra0
  rw [trace_outerProduct ket1 ket0 stOrthonormalBasis]
  exact inner_ket0_ket1

lemma trace_ketPbraM : ketPbraM.trace 𝕜 𝕜² = 0 := by
  unfold ketPbraM
  rw [trace_outerProduct ketP ketM stOrthonormalBasis]
  exact inner_ketM_ketP

lemma trace_ketMbraP : ketMbraP.trace 𝕜 𝕜² = 0 := by
  unfold ketMbraP
  rw [trace_outerProduct ketM ketP stOrthonormalBasis]
  exact inner_ketP_ketM

lemma trace_ket0braP : ket0braP.trace 𝕜 𝕜² = 1/√2 := by
  unfold ket0braP
  rw [trace_outerProduct ket0 ketP stOrthonormalBasis]
  exact inner_ketP_ket0

lemma trace_ket1braP : ket1braP.trace 𝕜 𝕜² = 1/√2 := by
  unfold ket1braP
  rw [trace_outerProduct ket1 ketP stOrthonormalBasis]
  exact inner_ketP_ket1

lemma trace_ket0braM : ket0braM.trace 𝕜 𝕜² = 1/√2 := by
  unfold ket0braM
  rw [trace_outerProduct ket0 ketM stOrthonormalBasis]
  exact inner_ketM_ket0

lemma trace_ket1braM : ket1braM.trace 𝕜 𝕜² = - (1/√2) := by
  unfold ket1braM
  rw [trace_outerProduct ket1 ketM stOrthonormalBasis]
  exact inner_ketM_ket1

lemma areProjMeas_ketbra0_ketbra1 : LinearMap.areProjMeas (𝕜 := 𝕜) ketbra0 ketbra1 :=
  ⟨IsStarProjection_ketbra0, IsStarProjection_ketbra1, ketbra0_add_ketbra1_eq⟩
