import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import ModularForms.ProdOnZ

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
def double_sum_lemma_summand (m n: ℤ) (z: ℍ): ℂ := 1/(m*z + n) - 1/(m*z + (n + 1))

lemma eisenstein_double_sum_telescopes (m: ℤ) (z: ℍ):
    HasSumOnZ ⊤ (double_sum_lemma_summand m · z) 0 := by
  let f: ℤ → ℂ := λ n ↦ 1/(m*(z: ℂ) + n)
  have h_neg: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 0) := by simpa [f, add_comm] using tendsto_const_div_linear_atTop_nhds_zero 1 (-1) (m*z)
  have h_pos: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 0) := by simpa [f, add_comm] using tendsto_const_div_linear_atTop_nhds_zero 1 1 (m*z)
  simp_rw [show ∀ n, double_sum_lemma_summand m n z = f n - f (n + 1) by
    unfold double_sum_lemma_summand f
    intro _; rw [Int.cast_add, Int.cast_one]
  ]
  simpa using HasSumOnZ.sum_sub_range h_neg h_pos

lemma eisenstein_double_sum_0 (z: ℍ): HasSumOnZ (⊤ \ {0}) (λ m ↦ ∑_ℤ n, double_sum_lemma_summand m n z) 0 := by
  simp_rw [λ m ↦ (eisenstein_double_sum_telescopes m z).z_sum_eq]
  apply HasSumOnZ.sum_const_zero

lemma eisenstein_double_sum_2piiz (z: ℍ): ∑_ℤ n, ∑_ℤ' m, double_sum_lemma_summand m n z = -(2 * π * Complex.I) / (z: ℂ) := by
  sorry

example: Filter.Tendsto (λ n: ℕ ↦ 1/(n: ℂ)) atTop (nhds 0) := by
  simp_rw [one_div]
  apply RCLike.tendsto_inverse_atTop_nhds_zero_nat


