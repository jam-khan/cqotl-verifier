/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.LinearMapPropositions
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
There is a one to one correspondence between the projection operators and the subspaces.
Note that we use the name `Submodule` for the subspaces, as in `Mathlib`.
In this file we define this correspondence and prove some basic properties about it.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The `Submodule` corresponding to a projection. This definition works for any `LinearMap`, but only makes sense for
projections. -/
def LinearMap.toSubmodule (T : E →ₗ[𝕜] E) : Submodule 𝕜 E := (LinearMap.ker T)ᗮ

namespace Submodule

/-- Sasaki implication. -/
def SasakiImp (K₀ K₁ : Submodule 𝕜 E) : Submodule 𝕜 E := K₀ᗮ ⊔ (K₀ ⊓ K₁)

/-- The projection corresponding to a `Submodule` as a `LinearMap` -/
noncomputable def toProjection (K : Submodule 𝕜 E) : E →ₗ[𝕜] E :=
  K.subtype ∘ₗ K.orthogonalProjection

lemma toProjection_eq (K : Submodule 𝕜 E) (x : E) :
    K.toProjection x = K.orthogonalProjection x := rfl

lemma toProjection_valid (K : Submodule 𝕜 E) :
    K.toProjection.isProjection := by
  constructor
  · constructor
    · rw [← LinearMap.isSymmetric_iff_isSelfAdjoint]
      unfold LinearMap.IsSymmetric
      intro x y
      unfold toProjection
      simp only [LinearMap.coe_comp]
      exact inner_orthogonalProjection_left_eq_right K x y
    · intro x
      unfold toProjection
      simp only [LinearMap.coe_comp]
      exact re_inner_orthogonalProjection_nonneg K x
  · rw [LinearMap.ext_iff]
    unfold toProjection
    simp

lemma toSubmodule_toProjection_eq (K : Submodule 𝕜 E) :
    K.toProjection.toSubmodule = K := by
  unfold toProjection
  unfold LinearMap.toSubmodule
  rw [← orthogonalComplement_eq_orthogonalComplement, orthogonal_orthogonal, Submodule.ext_iff]
  intro x
  rw [LinearMap.mem_ker, ← orthogonalProjection_eq_zero_iff]
  simp

lemma eq_iff_toProjection_eq (K₀ K₁ : Submodule 𝕜 E) :
    K₀ = K₁ ↔ K₀.toProjection = K₁.toProjection := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    rw [← K₀.toSubmodule_toProjection_eq, ← K₁.toSubmodule_toProjection_eq, h]

end Submodule

namespace LinearMap

namespace isProjection

lemma toSubmodule_eq_range {T : E →ₗ[𝕜] E} (hT : T.isProjection) :
    T.toSubmodule = range T := by
  rw [eq_comm]
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    unfold toSubmodule
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hT.apply_range hx, ← (isSymmetric_iff_isSelfAdjoint T).mpr hT.left.left, hu]
    exact inner_zero_left x
  · unfold toSubmodule
    rw [Nat.eq_sub_of_add_eq' (ker T).finrank_add_finrank_orthogonal, eq_tsub_iff_add_eq_of_le (ker T).finrank_le]
    exact finrank_range_add_finrank_ker T

lemma toProjection_toSubmodule_eq {T : E →ₗ[𝕜] E} (hT : T.isProjection) :
    T.toSubmodule.toProjection = T := by
  rw [LinearMap.ext_iff]
  intro x
  have hx := Submodule.exists_add_mem_mem_orthogonal (ker T) x
  obtain ⟨y, hy, z, hz, hxyz⟩ := hx
  rw [hxyz]
  rw [LinearMap.map_add, LinearMap.map_add]
  apply Mathlib.Tactic.LinearCombination.add_eq_eq
  · rw [Submodule.toProjection_eq]
    unfold LinearMap.toSubmodule
    rw [Submodule.orthogonalProjection_orthogonal_val, Submodule.orthogonalProjection_eq_self_iff.mpr hy, sub_self, hy]
  · rw [Submodule.toProjection_eq]
    unfold LinearMap.toSubmodule
    rw [Submodule.orthogonalProjection_orthogonal_val, Submodule.orthogonalProjection_eq_zero_iff.mpr hz,
      ZeroMemClass.coe_zero, sub_zero]
    have hz' : z ∈ range T := by
      rw [← hT.toSubmodule_eq_range]
      exact hz
    exact (hT.apply_range hz').symm

lemma eq_iff_toSubmodule_eq {T N : E →ₗ[𝕜] E} (hT : T.isProjection) (hN : N.isProjection) :
    T = N ↔ T.toSubmodule = N.toSubmodule := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    rw [← hT.toProjection_toSubmodule_eq, ← hN.toProjection_toSubmodule_eq, h]

end isProjection

omit [FiniteDimensional 𝕜 E] in
lemma toSubmodule_zero : (0 : E →ₗ[𝕜] E).toSubmodule = ⊥ := by
  rw [toSubmodule, ker_zero, Submodule.orthogonal_eq_bot_iff]

lemma eq_zero_of_toSubmodule_eq_bot (T : E →ₗ[𝕜] E) (h : T.toSubmodule = ⊥) :
    T = 0 := by
  unfold toSubmodule at h
  rw [Submodule.orthogonal_eq_bot_iff] at h
  exact ker_eq_top.mp h

lemma eq_zero_of_toSubmodule_le_bot (T : E →ₗ[𝕜] E) (h : T.toSubmodule ≤ ⊥) :
    T = 0 := by
  rw [le_bot_iff] at h
  exact eq_zero_of_toSubmodule_eq_bot T h

lemma eq_zero_iff_toSubmodule_eq_bot (T : E →ₗ[𝕜] E) :
    T = 0 ↔ T.toSubmodule = ⊥ := by
  apply Iff.intro
  · intro h
    rw [h]
    exact toSubmodule_zero
  · exact eq_zero_of_toSubmodule_eq_bot T

omit [FiniteDimensional 𝕜 E] in
lemma toSubmodule_one : (1 : E →ₗ[𝕜] E).toSubmodule = ⊤ := by
  rw [toSubmodule, Submodule.orthogonal_eq_top_iff]
  rfl

lemma isProjection.eq_one_of_toSubmodule_eq_top {T : E →ₗ[𝕜] E} (hT : T.isProjection) (h : T.toSubmodule = ⊤) :
    T = 1 := by
  rw [hT.eq_iff_toSubmodule_eq isProjection.one, toSubmodule_one]
  exact h

lemma isProjection.eq_one_of_top_le_toSubmodule {T : E →ₗ[𝕜] E} (hT : T.isProjection) (h : ⊤ ≤ T.toSubmodule) :
    T = 1 := by
  rw [top_le_iff] at h
  exact hT.eq_one_of_toSubmodule_eq_top h

lemma isProjection.eq_one_iff_toSubmodule_eq_top {T : E →ₗ[𝕜] E} (hT : T.isProjection) :
    T = 1 ↔ T.toSubmodule = ⊤ := by
  apply Iff.intro
  · intro h
    rw [h]
    exact toSubmodule_one
  · exact hT.eq_one_of_toSubmodule_eq_top

/-- The projection corresponding to the orthogonal complement of the submodule of the given linear map. -/
noncomputable def SubmoduleComplement (T : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmoduleᗮ).toProjection

/-- The projection corresponding to the intersection of the submodules of the given linear maps. -/
noncomputable def SubmoduleInf (T N : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmodule ⊓ N.toSubmodule).toProjection

/-- The projection corresponding to the sum of the submodules of the given linear maps. -/
noncomputable def SubmoduleSup (T N : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmodule ⊔ N.toSubmodule).toProjection

/-- Sasaki implication for linear maps -/
noncomputable def SasakiImp (T N : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmodule.SasakiImp N.toSubmodule).toProjection

lemma isProjection.SubmoduleComplement_eq {T : E →ₗ[𝕜] E} (hT : T.isProjection) : T.SubmoduleComplement = 1 - T := by
  ext x
  unfold SubmoduleComplement
  rw [Submodule.toProjection_eq, Submodule.orthogonalProjection_orthogonal_val, ← Submodule.toProjection_eq,
    hT.toProjection_toSubmodule_eq]
  rfl

lemma isProjection.SubmoduleComplement_eq_valid {T : E →ₗ[𝕜] E} (hT : T.isProjection) : (1 - T).isProjection := by
  rw [← hT.SubmoduleComplement_eq]
  unfold SubmoduleComplement
  exact Submodule.toProjection_valid _

lemma isProjection.comp_Complement {T : E →ₗ[𝕜] E} (hT : T.isProjection) : T ∘ₗ T.SubmoduleComplement = 0 := by
  rw [hT.SubmoduleComplement_eq, comp_sub, Module.End.one_eq_id, comp_id, hT.right]
  exact sub_self T

lemma SubmoduleInf_comm (T N : E →ₗ[𝕜] E) : T.SubmoduleInf N = N.SubmoduleInf T := by
  unfold SubmoduleInf
  rw [inf_comm]

lemma SubmoduleSup_comm (T N : E →ₗ[𝕜] E) : T.SubmoduleSup N = N.SubmoduleSup T := by
  unfold SubmoduleSup
  rw [sup_comm]

lemma SubmoduleInf_assoc (T N M : E →ₗ[𝕜] E) :
    (T.SubmoduleInf N).SubmoduleInf M = T.SubmoduleInf (N.SubmoduleInf M) := by
  unfold SubmoduleInf
  rw [Submodule.toSubmodule_toProjection_eq, Submodule.toSubmodule_toProjection_eq, inf_assoc]

lemma SubmoduleSup_assoc (T N M : E →ₗ[𝕜] E) :
    (T.SubmoduleSup N).SubmoduleSup M = T.SubmoduleSup (N.SubmoduleSup M) := by
  unfold SubmoduleSup
  rw [Submodule.toSubmodule_toProjection_eq, Submodule.toSubmodule_toProjection_eq, sup_assoc]

variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)

lemma isProjection.eigenvalues_eq_zero_or_one {T : E →ₗ[𝕜] E} (hT : T.isProjection) (i) :
    hT.isSymmetric.eigenvalues hn i ∈ ({0, 1} : Finset ℝ) := by
  let hTsymm : T.IsSymmetric := hT.isSymmetric
  let x : E := hTsymm.eigenvectorBasis hn i
  let c : ℝ := hTsymm.eigenvalues hn i
  have hT' : T (T x) = T x := LinearMap.ext_iff.mp hT.right x
  have hc : (c * c : 𝕜) • x = (c : 𝕜) • x := by
    rw [hTsymm.apply_eigenvectorBasis, map_smul, hTsymm.apply_eigenvectorBasis,
      show hTsymm.eigenvalues hn i = c by rfl,
      show hTsymm.eigenvectorBasis hn i = x by rfl, smul_smul] at hT'
    exact hT'
  have hx : x ≠ 0 := by
    intro hx
    have hx' : ‖x‖ = 1 := (hTsymm.eigenvectorBasis hn).norm_eq_one i
    rw [hx, norm_zero] at hx'
    exact zero_ne_one hx'
  have hc' : (c * c : 𝕜) = c := smul_left_injective 𝕜 hx hc
  rw [mul_right_eq_self₀, FaithfulSMul.algebraMap_eq_one_iff, RCLike.ofReal_eq_zero] at hc'
  unfold c hTsymm at hc'
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact hc'.symm

lemma IsPositive.isProjection_of_eigenvalues_eq_zero_or_one {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive)
    (h : ∀i, hT.isSymmetric.eigenvalues hn i ∈ ({0, 1} : Finset ℝ)) :
    T.isProjection := by
  apply And.intro hT
  ext x
  rw [coe_comp, Function.comp_apply]
  have hTsymm : T.IsSymmetric := hT.isSymmetric
  let base : OrthonormalBasis (Fin n) 𝕜 E := hTsymm.eigenvectorBasis hn
  let x_repr : EuclideanSpace 𝕜 (Fin n) := base.repr x
  rw [← OrthonormalBasis.sum_repr base x]
  repeat rw [map_sum]
  apply Fintype.sum_congr
  intro i
  repeat rw [map_smul]
  rw [hTsymm.apply_eigenvectorBasis, map_smul, hTsymm.apply_eigenvectorBasis]
  have hi := h i
  rw [Finset.mem_insert, Finset.mem_singleton] at hi
  cases hi <;> simp [*]

lemma IsPositive.isProjection_iff_eigenvalues_eq_zero_or_one {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive) :
    T.isProjection ↔ ∀i, hT.isSymmetric.eigenvalues hn i ∈ ({0, 1} : Finset ℝ) :=
  Iff.intro (fun hTproj ↦ hTproj.eigenvalues_eq_zero_or_one hn)
    (hT.isProjection_of_eigenvalues_eq_zero_or_one hn)

end LinearMap
