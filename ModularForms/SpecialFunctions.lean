import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Complex.Trigonometric
import ModularForms.Analysis

open Real Complex UpperHalfPlane Filter Function Topology

theorem multipliableLocallyUniformlyOn_euler_sinc_prod:
    MultipliableLocallyUniformlyOn (fun n : ℕ ↦ fun z : ℂ ↦ 1 - z^2 / (n + 1)^2) ⊤ := by
  use (fun z ↦ ∏' k : ℕ, (1 - z^2 / (k + 1)^2))
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact _).mpr
  intro K _ Kcompact
  obtain ⟨B, hB⟩ := Kcompact.exists_bound_of_continuousOn continuousOn_id
  let u (n : ℕ) := B^2 / (n + 1)^2 
  have hu: Summable u := by
    apply Summable.mul_left
    exact_mod_cast (summable_nat_add_iff 1).mpr (summable_nat_pow_inv.mpr one_lt_two)
  let f (n : ℕ) (z : ℂ) := 1 - z^2 / (n + 1)^2
  have hfu : ∀ (n : ℕ), ∀ z ∈ K, ‖f n z - 1‖ ≤ u n := fun n z zelem ↦ by
    rw [sub_sub_cancel_left, norm_neg, norm_div, norm_pow, norm_pow]
    have h_cast := Complex.norm_natCast (n + 1)
    push_cast at h_cast
    rw [h_cast]
    exact div_le_div_of_nonneg_right
      (sq_le_sq.mpr (abs_le_abs_of_nonneg (norm_nonneg _) (hB z zelem))) (sq_nonneg _)
  exact TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded_of_complete hu hfu
  simp

theorem Complex.euler_sin_tprod (z : ℂ) :
    Complex.sin (π * z) = π * z * ∏' (n : ℕ), (1 - z^2 / (n + 1)^2) := by
  have h_sinc_prod := multipliableLocallyUniformlyOn_euler_sinc_prod.hasProdLocallyUniformlyOn
  replace h_sinc_prod := HasProdLocallyUniformlyOn.hasProd h_sinc_prod (show z ∈ ⊤ by trivial)
  have h_sin_prod := h_sinc_prod.tendsto_prod_nat.const_mul (π * z)
  exact tendsto_nhds_unique (Complex.tendsto_euler_sin_prod z) h_sin_prod

theorem tendsto_locally_uniformly_on_atTop_iff {α β ι: Type*} [TopologicalSpace α] [MetricSpace β] [Preorder ι] [IsDirected ι (λ x₁ x₂ ↦ x₁ ≤ x₂)] [Nonempty ι] {F: ι → α → β} {f: α → β} {S: Set α}
    (h: ∀ ε, 0 < ε → ∀ x ∈ S, ∃ t ∈ 𝓝[S] x, ∃ N: ι, ∀ n ≥ N, ∀ y ∈ t, dist (f y) (F n y) < ε):
    TendstoLocallyUniformlyOn F f atTop S := by
  unfold TendstoLocallyUniformlyOn
  simp_rw [eventually_atTop]
  let P: Set (β × β) → Prop := λ u ↦ ∀ x ∈ S, ∃ t ∈ 𝓝[S] x, ∃ a, ∀ b ≥ a, ∀ y ∈ t, (f y, F b y) ∈ u
  apply (Metric.uniformity_basis_dist.forall_iff (P := P) _).mpr
  unfold P
  simp_rw [Set.mem_setOf_eq]
  exact h
  unfold P
  intro T₁ T₂ h_subset hT₁ x hx
  obtain ⟨t, ⟨ht_neighborhood, ⟨a, ha⟩⟩⟩ := hT₁ x hx
  use t
  constructor
  exact ht_neighborhood
  use a
  intro b hb y hy
  exact h_subset <| ha b hb y hy

theorem tendsto_locally_uniformly_euler_sin_prod:
    TendstoLocallyUniformlyOn (fun s : Finset ℕ ↦ fun z: ℂ ↦ π * z * ∏ k ∈ s, (1 - z^2 / (k + 1)^2))
    (fun z ↦ sin (π * z)) atTop ⊤ := by
  have h_top_open : IsOpen (⊤ : Set ℂ) := by simp
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact h_top_open).mpr
  intro K Ksub Kcompact 
  have h_tendsto_unif := (tendstoLocallyUniformlyOn_iff_forall_isCompact h_top_open).mp
    multipliableLocallyUniformlyOn_euler_sinc_prod.hasProdLocallyUniformlyOn K Ksub Kcompact
  simp_rw [Complex.euler_sin_tprod]
  apply TendstoUniformlyOn.mul₀_of_continuousOn_of_compact (TendstoUniformlyOn.of_const _ _ _)
    h_tendsto_unif (continuous_mul_left (π : ℂ)).continuousOn _ Kcompact 
  apply h_tendsto_unif.continuousOn
  filter_upwards with n
  exact continuousOn_finset_prod _ fun i _ ↦ Continuous.continuousOn (by continuity)

theorem cotangent_expansion (z: ℂ) (h: ¬∃ n: ℤ, z = n): π * cot (π * z) = 1/z + ∑' k: ℕ, (1/(z + (k + 1)) + 1/(z - (k + 1))) := by sorry

theorem cotangent_expansion_H (z: ℍ): π * cot (π * z) = 1/z + ∑' k: ℕ, (1/((z: ℂ) + (k + 1)) + 1/(z - (k + 1))) := by
  have h_non_int: ¬∃ n: ℤ, (z: ℂ) = n := by
    rintro ⟨n, h_eq⟩
    replace h_eq: (z: ℂ).im = (n: ℂ).im := congrArg Complex.im h_eq
    rw [coe_im, intCast_im] at h_eq
    have h_im_pos: z.im > 0 := im_pos z
    rw [h_eq] at h_im_pos
    apply (lt_self_iff_false 0).mp h_im_pos
  exact cotangent_expansion z h_non_int

theorem cotangent_dirichlet_expansion (z: ℍ): cot z = -Complex.I - 2 * π * Complex.I * ∑' d: ℕ, Complex.exp (2 * π * Complex.I * (d + 1) * z) := by
  sorry

theorem cotangent_dirichlet_expansion' (z: ℂ) (h: z.im > 0): cot z = -Complex.I - 2 * π * Complex.I * ∑' d: ℕ, Complex.exp (2 * π * Complex.I * (d + 1) * z) :=
  cotangent_dirichlet_expansion { val := z, property := h }

example (f : ℂ → ℂ) : TendstoUniformly (fun (n : ℕ) ↦ f) f atTop := by
  refine Metric.tendstoUniformly_iff.mpr ?_
  aesop
