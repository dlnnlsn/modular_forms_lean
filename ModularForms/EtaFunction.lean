import Mathlib

-- open Real Complex UpperHalfPlane SlashAction ModularGroup Matrix MatrixGroups
open Real Complex UpperHalfPlane Matrix MatrixGroups CongruenceSubgroup ModularForm SlashAction EisensteinSeries

noncomputable
def eta (z: ℍ): ℂ := cexp (π * Complex.I * z / 12) * ∏' n: ℕ, (1 - cexp (2 * π * Complex.I * n * z))

lemma eta_of_smul_T (z: ℍ): _root_.eta (ModularGroup.T • z) = cexp (π * Complex.I / 12) * _root_.eta z := by
  have h_cexp_T_smul (n: ℕ): cexp (2 * π * Complex.I * n * ((1: ℝ) +ᵥ z)) = cexp (2 * π * Complex.I * n * z) := by
    rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm _ (n: ℂ), Complex.exp_nat_mul_two_pi_mul_I, one_mul]
  rw [modular_T_smul, _root_.eta]
  simp_rw [h_cexp_T_smul]
  rw [show cexp (π * Complex.I * ((1: ℝ) +ᵥ z) / 12) = cexp (π * Complex.I / 12) * cexp (π * Complex.I * z / 12) from by
    rw [←Complex.exp_add, coe_vadd, ofReal_one, mul_add, add_div, mul_one]
  ]
  rw [mul_assoc (cexp _)]
  rfl

lemma eta_of_smul_S (z: ℍ): _root_.eta (ModularGroup.S • z) = (-Complex.I * z)^((1: ℂ)/2) * _root_.eta z := by
  -- very very very
  sorry
