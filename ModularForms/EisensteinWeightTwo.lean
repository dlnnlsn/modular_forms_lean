import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import ModularForms.Analysis
import ModularForms.ProdOnZ
import ModularForms.SpecialFunctions
import Mathlib.Tactic.CancelDenoms.Core

open Real Complex UpperHalfPlane Filter Function Topology Matrix MatrixGroups

lemma tendsto_const_div_linear_atTop_nhds_zero (a b c: ℂ) (hb: b ≠ 0):
    Tendsto (λ n: ℕ ↦ a/(b*n + c)) atTop (𝓝 0) := by
  convert Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall <| λ n hn ↦ _)) _
  exact λ n: ℕ ↦ (n: ℂ)⁻¹ * (a/(b + c * (n: ℂ)⁻¹))
  field_simp [Nat.cast_ne_zero.mpr hn]
  have h_lim_one_div_n: Tendsto (λ n: ℕ ↦ (n: ℂ)⁻¹) atTop (𝓝 0) := by
    apply RCLike.tendsto_inverse_atTop_nhds_zero_nat
  have h_lim_c_div_n: Tendsto (λ n: ℕ ↦ c * (n: ℂ)⁻¹) atTop (𝓝 0) := by
    simpa  using Tendsto.mul tendsto_const_nhds h_lim_one_div_n
  have h_lim_denom: Tendsto (λ n: ℕ ↦ (b + c * (n: ℂ)⁻¹)) atTop (𝓝 b) := by
    simpa using Tendsto.add tendsto_const_nhds h_lim_c_div_n
  have h_lim_frac: Tendsto (λ n: ℕ ↦ a/(b + c * (n: ℂ)⁻¹)) atTop (𝓝 (a/b)) := by
    simpa using Tendsto.div tendsto_const_nhds h_lim_denom hb
  simpa using Tendsto.mul h_lim_one_div_n h_lim_frac

noncomputable
def double_sum_lemma_summand_part (m n: ℤ) (z: ℍ): ℂ := 1/(m*z + n)

noncomputable
def double_sum_lemma_summand (m n: ℤ) (z: ℍ): ℂ := double_sum_lemma_summand_part m n z - double_sum_lemma_summand_part m (n + 1) z

lemma eisenstein_double_sum_telescopes (m: ℤ) (z: ℍ):
    HasSumOnZ ⊤ (double_sum_lemma_summand m · z) 0 := by
  let f: ℤ → ℂ := λ n ↦ 1/(m*(z: ℂ) + n)
  have h_neg: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 0) := by simpa [f, add_comm] using tendsto_const_div_linear_atTop_nhds_zero 1 (-1) (m*z)
  have h_pos: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 0) := by simpa [f, add_comm] using tendsto_const_div_linear_atTop_nhds_zero 1 1 (m*z)
  simpa using HasSumOnZ.sum_sub_range h_neg h_pos

lemma eisenstein_double_sum_0 (z: ℍ): HasSumOnZ (⊤ \ {0}) (λ m ↦ ∑_ℤ n, double_sum_lemma_summand m n z) 0 := by
  simp_rw [λ m ↦ (eisenstein_double_sum_telescopes m z).z_sum_eq]
  apply HasSumOnZ.sum_const_zero

lemma eisenstein_double_sum_summable (z: ℍ) (n: ℤ): SummableOnZ (⊤ \ {0}) (double_sum_lemma_summand · n z) := by sorry

open Classical in
lemma eisenstein_double_sum_2piiz (z: ℍ): HasSumOnZ ⊤ (∑_ℤ' m, double_sum_lemma_summand m · z) (-((2 * π * Complex.I) / (z: ℂ))) := by
  unfold HasSumOnZ sum_within_radius
  simp_rw [exchange_z_sum_finsum <| (λ m _ ↦ eisenstein_double_sum_summable z m)]
  simp_rw [show ∀ N: ℕ, ∀ m: ℤ,  ∑ n ∈ Finset.filter (· ∈ (⊤: Set ℤ)) (Finset.Ico (-N: ℤ) N), double_sum_lemma_summand m n z
    = sum_within_radius N (⊤: Set ℤ) (double_sum_lemma_summand   m · z) from λ _ _ ↦ rfl]
  unfold double_sum_lemma_summand
  simp_rw [sum_within_radius_of_top_range_sub]
  unfold double_sum_lemma_summand_part
  simp_rw [z_sum'_eq_tsum_of_summable_of_pos_of_neg (by sorry)]
  have h_summand (m n: ℕ): 1/((m + 1: ℂ)*(z: ℂ) + (-n)) - 1/((m + 1)*z + n) + (1/(-(m + 1)*z + (-n)) - 1/(-(m + 1)*z + n))
    = 2/(z: ℂ) * (1/(-n/z + (m + 1)) + 1/(-n/z - (m + 1))):= by sorry
  push_cast at h_summand ⊢
  simp_rw [h_summand]
  simp_rw [Summable.tsum_mul_left (2/(z: ℂ)) (by sorry)]
  rw [show (-(2 * π * Complex.I / z)) = 2/(z: ℂ) * (π * (-Complex.I - (2 * π * Complex.I) * ∑' _: ℕ, 0) - 0) by
    rw [tsum_zero]
    ring
  ]
  apply Tendsto.const_mul
  simp_rw [λ n: ℕ ↦ eq_sub_of_add_eq' <| Eq.symm <| cotangent_expansion ((-n: ℂ)/z) (by sorry)]
  simp_rw [λ n: ℕ ↦ cotangent_dirichlet_expansion' ((π: ℂ) * ((-n: ℂ)/(z: ℂ))) (by sorry)]
  apply Tendsto.sub
  apply Tendsto.const_mul
  apply Tendsto.const_sub
  apply Tendsto.const_mul
  have bound_summable: Summable (λ d: ℕ ↦ ‖Complex.exp (-2 * π * Complex.I/z)‖^d) := by sorry
  apply interchange_limit_sum_of_dominated_convergence _ _ bound_summable
  sorry
  sorry
  simp_rw [show ∀ n: ℕ, 1/((-n: ℂ)/(z: ℂ)) = -(z: ℂ)/(1 * n + 0)  by
    intro n
    field_simp
    ring
  ]
  apply tendsto_const_div_linear_atTop_nhds_zero (-z: ℂ) 1 0 (Ne.symm <| zero_ne_one' ℂ)

noncomputable
def G₂ (z: ℍ): ℂ := ∑_ℤ' n, (1: ℂ)/n^2 + ∑_ℤ' m, ∑_ℤ n, 1/(m * (z: ℂ) + n)^2

theorem G₂_summableOnZ_inner_sum (z: ℍ) (m: ℤ): SummableOnZ ⊤ (λ n: ℤ ↦ (1/(m * (z: ℂ) + n)^2)) := by
  sorry

theorem G₂_summableOnZ_outer_sum (z: ℍ): SummableOnZ ((⊤: Set ℤ) \ {0}) (λ m ↦ ∑_ℤ n, 1/(m * (z: ℂ) + n)^2) := by
  sorry

noncomputable
def E₂ (z: ℍ): ℂ := -(1: ℂ)/(8*π^2) * G₂ z

lemma int_linear_combination_upper_half_plane_ne_zero (a b: ℤ) (ha: a ≠ 0) (z: ℍ): a * (z: ℂ) + b ≠ 0 := by
  intro h_eq
  apply congrArg Complex.im at h_eq
  norm_num at h_eq
  rcases h_eq with ha_zero | h_zim_zero
  exact ha ha_zero
  have h_zim_pos: 0 < z.im := z.property
  rw [h_zim_zero] at h_zim_pos
  exact (lt_self_iff_false 0).mp h_zim_pos

theorem G₂_abs_conv_formula (z: ℍ): G₂ z = ∑_ℤ' n, (1: ℂ)/n^2 + ∑_ℤ' m, ∑_ℤ n, 1/((m * (z: ℂ) + n)^2 * (m*z + n + 1))  := by
  rw [←sub_zero (G₂ z), ←HasSumOnZ.z_sum_eq <| eisenstein_double_sum_0 z, G₂, add_sub_assoc]
  apply congrArg
  rw [←SummableOnZ.z_sum_sub (by sorry) (by sorry)] 
  apply z_sum_congr (by rfl)
  intro m m_ne_zero
  replace m_ne_zero: m ≠ 0 := ((Set.mem_diff m).mp m_ne_zero).right
  rw [Pi.sub_apply]
  rw [←SummableOnZ.z_sum_sub (by sorry) (by sorry)]
  apply z_sum_congr (by rfl)
  intro n _
  rw [Pi.sub_apply]
  unfold double_sum_lemma_summand double_sum_lemma_summand_part
  apply (eq_div_iff _).mpr
  repeat rw [div_eq_mul_inv]
  rw [sub_mul, one_mul, one_mul, one_mul]
  rw [←mul_assoc (_⁻¹), inv_mul_cancel₀, one_mul]
  rw [sub_mul, ←mul_assoc (_⁻¹), pow_two, ←mul_assoc (_⁻¹), inv_mul_cancel₀, one_mul]
  rw [mul_comm (_⁻¹), mul_assoc, Lean.Grind.CommRing.intCast_add, add_assoc _ (n: ℂ) 1, Int.cast_one, mul_inv_cancel₀]
  ring
  exact_mod_cast int_linear_combination_upper_half_plane_ne_zero m (n + 1) m_ne_zero z
  exact int_linear_combination_upper_half_plane_ne_zero m n m_ne_zero z
  apply pow_ne_zero
  exact int_linear_combination_upper_half_plane_ne_zero m n m_ne_zero z
  apply mul_ne_zero
  apply pow_ne_zero
  exact int_linear_combination_upper_half_plane_ne_zero m n m_ne_zero z
  rw [←Int.cast_one, add_assoc, ←Lean.Grind.CommRing.intCast_add]
  exact int_linear_combination_upper_half_plane_ne_zero m (n + 1) m_ne_zero z

theorem G₂_of_smul_S' (z: ℍ): (z: ℂ)^(-2: ℤ) * G₂ (ModularGroup.S • z) = G₂ z - (2 * π * Complex.I)/z := by
  unfold G₂
  rw [modular_S_smul, coe_mk]
  rw [mul_add]
  simp_rw [←z_sum_const_mul]
  simp_rw [show ∀ m n: ℤ, (z: ℂ)^(-2: ℤ) * (1/(↑m * (-(z: ℂ))⁻¹ + ↑n)^2) = 1/(n * (z: ℂ) - ↑m)^2 by sorry]
  simp_rw [show ∀ m, ∑_ℤ n, 1/(n*(z: ℂ) - m)^2 = 1/(m: ℂ)^2 + ∑_ℤ' n, 1/(n*(z: ℂ) - m)^2 by
    intro m
    rw [eq_z_sum_of_add_of_z_sum'_of_eval_zero (by sorry)]
    rw [add_comm]
    ring 
  ]
  rw [sub_eq_add_neg, ←(eisenstein_double_sum_2piiz z).z_sum_eq]
  unfold double_sum_lemma_summand double_sum_lemma_summand_part
  congr
  sorry
