import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open Real UpperHalfPlane Matrix
open Complex hiding eta

noncomputable
def eta (z: ℍ): ℂ := cexp (π * Complex.I * z / 12) *
    ∏' n: ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z))

lemma eta_of_smul_T (z: ℍ): eta (ModularGroup.T • z) = cexp (π * Complex.I / 12) * eta z := by
  have h_cexp_T_smul (n: ℕ): cexp (2 * π * Complex.I * n * ((1: ℝ) +ᵥ z))
      = cexp (2 * π * Complex.I * n * z) := by
    rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm _ (n: ℂ),
        Complex.exp_nat_mul_two_pi_mul_I, one_mul]
  rw [modular_T_smul, eta]
  simp_rw [h_cexp_T_smul]
  rw [coe_vadd, ofReal_one, mul_add, add_div, mul_one, Complex.exp_add, mul_assoc (cexp _)]
  rfl

lemma eta_of_smul_S (z: ℍ): eta (ModularGroup.S • z) = (-Complex.I * z)^((1: ℂ)/2) * eta z := by
  -- very very very
  sorry
