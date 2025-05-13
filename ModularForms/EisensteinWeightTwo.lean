import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import ModularForms.Analysis
import ModularForms.ProdOnZ
import ModularForms.SpecialFunctions

open Real Complex UpperHalfPlane Filter Function Topology

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
lemma eisenstein_double_sum_2piiz (z: ℍ): HasSumOnZ ⊤ (∑_ℤ' m, double_sum_lemma_summand m · z) ((-2 * π * Complex.I) / (z: ℂ)) := by
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
  rw [show -2 * π * Complex.I / z = 2/(z: ℂ) * (π * (-Complex.I - (2 * π * Complex.I) * ∑' _: ℕ, 0) - 0) by
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
