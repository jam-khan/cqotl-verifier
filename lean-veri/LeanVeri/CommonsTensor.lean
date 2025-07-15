import LeanVeri.Commons
import LeanVeri.InnerTensorProduct

open scoped TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

noncomputable def ket00 : 𝕜² ⊗[𝕜] 𝕜² := ket0 ⊗ₜ ket0
noncomputable def ket01 : 𝕜² ⊗[𝕜] 𝕜² := ket0 ⊗ₜ ket1
noncomputable def ket10 : 𝕜² ⊗[𝕜] 𝕜² := ket1 ⊗ₜ ket0
noncomputable def ket11 : 𝕜² ⊗[𝕜] 𝕜² := ket1 ⊗ₜ ket1

noncomputable def ketbra00 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket00 ket00
noncomputable def ket00bra01 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket00 ket01
noncomputable def ket00bra10 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket00 ket10
noncomputable def ket00bra11 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket00 ket11
noncomputable def ket01bra00 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket01 ket00
noncomputable def ketbra01 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket01 ket01
noncomputable def ket01bra10 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket01 ket10
noncomputable def ket01bra11 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket01 ket11
noncomputable def ket10bra00 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket10 ket00
noncomputable def ket10bra01 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket10 ket01
noncomputable def ketbra10 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket10 ket10
noncomputable def ket10bra11 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket10 ket11
noncomputable def ket11bra00 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket11 ket00
noncomputable def ket11bra01 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket11 ket01
noncomputable def ket11bra10 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket11 ket10
noncomputable def ketbra11 : 𝕜² ⊗[𝕜] 𝕜² →ₗ[𝕜] 𝕜² ⊗[𝕜] 𝕜² := outerProduct 𝕜 ket11 ket11
