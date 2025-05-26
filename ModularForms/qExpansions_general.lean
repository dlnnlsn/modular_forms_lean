import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import ModularForms.CuspFormSubspace

open CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open ModularFormClass
open Complex Topology Manifold
open PowerSeries

open scoped Real MatrixGroups CongruenceSubgroup

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)
variable{N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
variable {z : ℍ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam
local notation "i" => Complex.I

lemma modularForms_is_periodic {τ : ℂ} {f : ModularForm Γ(1) k} : f (ofComplex (τ + 1)) = f (ofComplex τ) := by sorry

lemma modularForms_is_differentiable {f : ModularForm Γ(1) k} : ∀ᶠ (z : ℂ) in I∞, DifferentiableAt ℂ (⇑f ∘ ↑ofComplex) z := by
  have : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f) := by apply f.holo'
  simp_rw [← mdifferentiableAt_iff_differentiableAt]
  convert this
  simp_all only [eventually_comap, eventually_atTop, ge_iff_le, iff_true]
  sorry

lemma modularForms_is_BoundedAtFilter {f : ModularForm Γ(1) k} : I∞.BoundedAtFilter (⇑f ∘ ↑ofComplex) := by sorry

--lemma eq_multilin : f = qExpansionFormalMultilinearSeries 1 f
lemma modularForm_TendsTo_Filter_at_zero {f : ModularForm Γ(1) k} (hyp : (coeff ℂ 0) (qExpansion 1 f) = 0 ): Filter.Tendsto f (Filter.comap UpperHalfPlane.im Filter.atTop) (𝓝 0) := by
      convert @Function.Periodic.tendsto_at_I_inf 1 (⇑f ∘ ofComplex) _ _ _ _
      · ext F
        constructor
        · intro h
          simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
            using (h).comp tendsto_comap_im_ofComplex
        · intro h₁ s h₂
          obtain ⟨t, h₃⟩ := h₁ h₂
          use t
          simp_all only [Nat.cast_one, mem_atTop_sets, ge_iff_le, true_and]
          obtain ⟨left, right⟩ := h₃
          obtain ⟨w, h_1⟩ := left
          convert right
          simp_all only [coeff_zero_eq_constantCoeff, iff_true]
          intro r h₃

          simp_all only [Set.mem_preimage]
          refine Set.mem_preimage.mp ?_
          have thing: (r : ℂ)  ∈ (Complex.im ⁻¹' t) := by apply h₃
          have thing1  : (r : ℂ) ∈ ⇑f ∘ ↑ofComplex ⁻¹' s := by apply right; convert thing
          convert thing1
          simp_all only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, Set.mem_preimage, coe_im,
            comp_apply, ofComplex_apply]
      · unfold qExpansion at hyp
        simp_all only [coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
        unfold SlashInvariantFormClass.cuspFunction at hyp
        convert hyp
        simp_all only [Nat.cast_one]
        simp_all only [Nat.cast_one]
      · simp
      · simp_all only [coeff_zero_eq_constantCoeff, Nat.cast_one, Periodic, ofReal_one, comp_apply]
        intro x
        apply modularForms_is_periodic
      · apply modularForms_is_differentiable
      · apply modularForms_is_BoundedAtFilter

theorem zeroAtInfty_iff_CuspForm {f : ModularForm Γ(1) k} : (∀ A : SL(2, ℤ), IsZeroAtImInfty (f.toFun ∣[(k : ℤ)] A)) ↔ (qExpansion 1 f).coeff ℂ 0 = 0 := by
  constructor
  · intro h
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul]
    unfold IsZeroAtImInfty ZeroAtFilter at h
    unfold SlashInvariantFormClass.cuspFunction
    apply Periodic.cuspFunction_zero_of_zero_at_inf
    simp
    simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
    using (h 1).comp tendsto_comap_im_ofComplex
  · intro h
    have cloneh : (coeff ℂ 0) (qExpansion 1 f) = 0 := h
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] at h
    intro A
    rw [f.slash_action_eq' A]
    unfold SlashInvariantFormClass.cuspFunction at h
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne] at h
    unfold IsZeroAtImInfty
    simp_all only [Nat.cast_one, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe]
    unfold ZeroAtFilter atImInfty
    convert modularForm_TendsTo_Filter_at_zero cloneh
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] at cloneh
    rw [Gamma_one_top]
    simp only [Subgroup.mem_top]

lemma lemma1 {f g : ModularForm Γ(1) k} {h : qExpansion 1 f = qExpansion 1 g}:  qExpansionFormalMultilinearSeries 1 f = qExpansionFormalMultilinearSeries 1 g := by
      unfold qExpansionFormalMultilinearSeries
      rw [h]

lemma lemma2 {f g : ModularForm Γ(1) k} {h : qExpansion 1 f = qExpansion 1 g}: HasFPowerSeriesOnBall (SlashInvariantFormClass.cuspFunction 1 g) (qExpansionFormalMultilinearSeries 1 f) 0 1 := by
      rw [lemma1]
      apply hasFPowerSeries_cuspFunction 1 g
      apply h

theorem qExpansion_congr {f g : ModularForm Γ(1) k}: qExpansion 1 f = qExpansion 1 g  ↔ ∀ n : ℕ, (qExpansion 1 f).coeff ℂ n • 𝕢 1 z ^ n = (qExpansion 1 g).coeff ℂ n • 𝕢 1 z ^ n := by
  constructor
  · intro h n
    simp only [smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
    left
    rw [h]
  · intro h
    ext n
    simp only [smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq] at h
    have : 𝕢 1 ↑z ≠ 0 := by
      intro h₁
      unfold Periodic.qParam at h₁
      simp_all only [ofReal_one, div_one, exp_ne_zero]
    have : (coeff ℂ n) (qExpansion 1 f) = (coeff ℂ n) (qExpansion 1 g) := by
      convert h n
      simp_all only [false_and, or_false, ne_eq]
    apply this
