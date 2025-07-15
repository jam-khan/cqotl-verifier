import LeanVeri.CommonsTensor
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

open scoped TensorProduct

lemma obligation1 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le ketbra11 (ketbra10 + ketbra01 + ketbra11 + ketbra00) :=
  sorry

noncomputable def X : 𝕜² →ₗ[𝕜] 𝕜² := PauliX

lemma obligation2 :
    LinearMap.instLoewnerPartialOrder.le
      ketbra10
      (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 (X.adjoint)
        ∘ₗ ketbra11
        ∘ₗ TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 X
      ) :=
  sorry

lemma obligation3 :
    LinearMap.instLoewnerPartialOrder.le
      (LinearMap.SubmoduleInf
        (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 1)
        (TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 ketbra0))
      ketbra10 := sorry

lemma obligation4 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le
      ketbra0
      (Hadamard.adjoint ∘ₗ ketbraP ∘ₗ ketbraP.adjoint ∘ₗ Hadamard) := sorry

lemma obligation5 :
    (LinearMap.instLoewnerPartialOrder (𝕜 := 𝕜)).le
      (ketbraP ∘ₗ ketbraP.adjoint)
      (ketbra1.SasakiImp ketbra1) :=
  sorry

lemma obligation6 : (Hadamard (𝕜 := 𝕜)).isUnitary :=
  sorry

lemma obligation7 : LinearMap.areProjMeas (𝕜 := 𝕜) ketbra0 ketbra1 :=
  sorry

lemma obligation8 : (X (𝕜 := 𝕜)).isUnitary :=
  sorry
