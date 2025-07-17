import LeanVeri.Commons
import LeanVeri.InnerTensorProduct

open scoped TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)
local notation "𝕜²²" => 𝕜² ⊗[𝕜] 𝕜²

noncomputable def ket00 : 𝕜²² := ket0 ⊗ₜ ket0
noncomputable def ket01 : 𝕜²² := ket0 ⊗ₜ ket1
noncomputable def ket10 : 𝕜²² := ket1 ⊗ₜ ket0
noncomputable def ket11 : 𝕜²² := ket1 ⊗ₜ ket1

noncomputable def ketbra00 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket00 ket00
noncomputable def ket00bra01 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket00 ket01
noncomputable def ket00bra10 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket00 ket10
noncomputable def ket00bra11 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket00 ket11
noncomputable def ket01bra00 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket01 ket00
noncomputable def ketbra01 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket01 ket01
noncomputable def ket01bra10 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket01 ket10
noncomputable def ket01bra11 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket01 ket11
noncomputable def ket10bra00 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket10 ket00
noncomputable def ket10bra01 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket10 ket01
noncomputable def ketbra10 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket10 ket10
noncomputable def ket10bra11 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket10 ket11
noncomputable def ket11bra00 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket11 ket00
noncomputable def ket11bra01 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket11 ket01
noncomputable def ket11bra10 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket11 ket10
noncomputable def ketbra11 : 𝕜²² →ₗ[𝕜] 𝕜²² := outerProduct 𝕜 ket11 ket11

lemma isSelfAdjoint_ketbra00 : IsSelfAdjoint (ketbra00 : 𝕜²² →ₗ[𝕜] 𝕜²²) := IsSelfAdjoint_outerProduct_self 𝕜 ket00
lemma isSelfAdjoint_ketbra01 : IsSelfAdjoint (ketbra01 : 𝕜²² →ₗ[𝕜] 𝕜²²) := IsSelfAdjoint_outerProduct_self 𝕜 ket01
lemma isSelfAdjoint_ketbra10 : IsSelfAdjoint (ketbra10 : 𝕜²² →ₗ[𝕜] 𝕜²²) := IsSelfAdjoint_outerProduct_self 𝕜 ket10
lemma isSelfAdjoint_ketbra11 : IsSelfAdjoint (ketbra11 : 𝕜²² →ₗ[𝕜] 𝕜²²) := IsSelfAdjoint_outerProduct_self 𝕜 ket11

lemma isPositive_ketbra00 : (ketbra00 : 𝕜²² →ₗ[𝕜] 𝕜²²).IsPositive := isPositive_outerProduct_self 𝕜 ket00
lemma isPositive_ketbra01 : (ketbra01 : 𝕜²² →ₗ[𝕜] 𝕜²²).IsPositive := isPositive_outerProduct_self 𝕜 ket01
lemma isPositive_ketbra10 : (ketbra10 : 𝕜²² →ₗ[𝕜] 𝕜²²).IsPositive := isPositive_outerProduct_self 𝕜 ket10
lemma isPositive_ketbra11 : (ketbra11 : 𝕜²² →ₗ[𝕜] 𝕜²²).IsPositive := isPositive_outerProduct_self 𝕜 ket11

lemma ketbra00_eq : ketbra00 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra0 ketbra0 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket0 ket0 ket0
lemma ket00bra01_eq : ket00bra01 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra0 ket0bra1 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket0 ket0 ket1
lemma ket00bra10_eq : ket00bra10 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket0bra1 ketbra0 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket0 ket1 ket0
lemma ket00bra11_eq : ket00bra11 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket0bra1 ket0bra1 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket0 ket1 ket1
lemma ket01bra00_eq : ket01bra00 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra0 ket1bra0 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket1 ket0 ket0
lemma ketbra01_eq : ketbra01 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra0 ketbra1 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket1 ket0 ket1
lemma ket01bra10_eq : ket01bra10 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket0bra1 ket1bra0 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket1 ket1 ket0
lemma ket01bra11_eq : ket01bra11 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket0bra1 ketbra1 := TensorProduct.outerProduct_tmul 𝕜 ket0 ket1 ket1 ket1
lemma ket10bra00_eq : ket10bra00 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket1bra0 ketbra0 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket0 ket0 ket0
lemma ket10bra01_eq : ket10bra01 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket1bra0 ket0bra1 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket0 ket0 ket1
lemma ketbra10_eq : ketbra10 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 ketbra0 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket0 ket1 ket0
lemma ket10bra11_eq : ket10bra11 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 ket0bra1 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket0 ket1 ket1
lemma ket11bra00_eq : ket11bra00 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket1bra0 ket1bra0 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket1 ket0 ket0
lemma ket11bra01_eq : ket11bra01 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ket1bra0 ketbra1 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket1 ket0 ket1
lemma ket11bra10_eq : ket11bra10 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 ket1bra0 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket1 ket1 ket0
lemma ketbra11_eq : ketbra11 = TensorProduct.mapBilinear 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 ketbra1 := TensorProduct.outerProduct_tmul 𝕜 ket1 ket1 ket1 ket1

