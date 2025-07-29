import LeanVeri.CommonsTensor
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

open scoped TensorProduct

lemma obligation1 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le ketbra11 (ketbra10 + ketbra01 + ketbra11 + ketbra00) := by
  rw [LinearMap.le_def, add_sub_assoc, add_assoc, add_sub_cancel]
  exact LinearMap.IsPositive.add
    (LinearMap.IsPositive.add (isPositive_outerProduct_self 𝕜 ket10) (isPositive_outerProduct_self 𝕜 ket01))
    (isPositive_outerProduct_self 𝕜 ket00)

noncomputable def X : 𝕜² →ₗ[𝕜] 𝕜² := PauliX

lemma obligation2 :
    LinearMap.instLoewnerPartialOrder.le
      ketbra10
      (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 (X.adjoint)
        ∘ₗ ketbra11
        ∘ₗ TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 X
      ) := by
  rw [ketbra11_eq]
  repeat rw [TensorProduct.mapBilinear_apply]
  repeat rw [← TensorProduct.map_comp]
  unfold X PauliX
  simp only [map_add]
  repeat rw [Module.End.one_eq_id]
  rw [LinearMap.comp_id, LinearMap.id_comp]
  repeat rw [LinearMap.add_comp]
  repeat rw [LinearMap.comp_add]
  unfold ket0bra1 ketbra1 ket1bra0
  repeat rw [adjoint_outerProduct]
  repeat rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct]
  rw [inner_ket1_ket0, inner_ket1_ket1]
  simp
  repeat rw [outerProduct_comp_outerProduct_eq_inner_smul_outerProduct]
  rw [inner_ket0_ket1, inner_ket1_ket1]
  simp
  rw [← ketbra0, ← ketbra1]
  rw [← TensorProduct.mapBilinear_apply]
  rw [← ketbra10_eq]

lemma obligation3 :
    LinearMap.instLoewnerPartialOrder.le
      (LinearMap.SubmoduleInf
        (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 1)
        (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 ketbra0))
      ketbra10 := sorry

lemma obligation4 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le
      ketbra0
      (Hadamard.adjoint ∘ₗ ketbraP ∘ₗ ketbraP.adjoint ∘ₗ Hadamard) := by
  rw [(isPositive_ketbraP (𝕜 := 𝕜)).isSymmetric.adjoint_eq]
  nth_rw 2 [← LinearMap.comp_assoc]
  rw [LinearMap.IsStarProjection.comp_self (𝕜 := 𝕜) IsStarProjection_ketbraP]
  rw [adj_Hadamard_ketbraP_eq]

lemma obligation5 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le
      (ketbraP ∘ₗ ketbraP.adjoint)
      (ketbra1.SasakiImp ketbra1) :=
  sorry

lemma obligation6 : (Hadamard (𝕜 := 𝕜)).isUnitary :=
  isUnitary_Hadamard

lemma obligation7 : LinearMap.areProjMeas (𝕜 := 𝕜) ketbra0 ketbra1 :=
  areProjMeas_ketbra0_ketbra1


lemma obligation8 : (X (𝕜 := 𝕜)).isUnitary :=
  isUnitary_PauliX
