import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology Metric

--TODO: Convert this to the multiplicative version and use @[to_additive]
theorem sum_tail_tends_to_zero_of_summable {α: Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α] {f: ℕ → α} (h: Summable f):
    Tendsto (λ N: ℕ ↦ ∑' i: ℕ, f (i + N)) atTop (𝓝 0) := by
  simp_rw [λ N ↦ eq_sub_of_add_eq' <| Summable.sum_add_tsum_nat_add N h]
  rw [←sub_self <| tsum f]
  apply Filter.Tendsto.const_sub
  exact Summable.tendsto_sum_tsum_nat h

theorem interchange_limit_sum_of_dominated_convergence {α: Type*} [RCLike α] {f: ℕ → ℕ → α} {M: ℕ → ℝ} {f_lim: ℕ → α}
  (h_lim: ∀ k, Tendsto (f k ·) atTop (𝓝 (f_lim k)))
  (h_bound: ∀ k, ∀ n, ‖f k n‖ ≤ M k)
  (h_M_summable: Summable M)
  : Tendsto (∑' k, f k ·) atTop (𝓝 <| ∑' k, f_lim k)
:= by
  have M_k_nonneg: 0 ≤ M := λ k ↦ le_trans (norm_nonneg <| f k 0) (h_bound k 0)
  have f_summable (n: ℕ): Summable (f · n) := Summable.of_norm_bounded M h_M_summable (λ k ↦ h_bound k n)
  have norm_f_lim_le_M: norm ∘ f_lim ≤ M := by
    intro k
    have: Tendsto (λ _: ℕ ↦ M k) atTop (𝓝 <| M k) := by exact tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' (Tendsto.norm <| h_lim k) this (h_bound k)
  have f_lim_summable: Summable f_lim := Summable.of_norm_bounded M h_M_summable norm_f_lim_le_M
  have f_lim_norm_summable: Summable (norm ∘ f_lim) := Summable.of_nonneg_of_le (λ _ ↦ norm_nonneg _) norm_f_lim_le_M h_M_summable
  simp_rw [atTop_basis.tendsto_iff nhds_basis_ball, Set.mem_Ici, mem_ball, true_and]
  intro ε ε_pos
  have sum_M_tail_tendsto_zero := sum_tail_tends_to_zero_of_summable h_M_summable
  rw [atTop_basis.tendsto_iff <| nhds_basis_Ioo_pos 0] at sum_M_tail_tendsto_zero
  obtain ⟨N_M, hN_M⟩ := sum_M_tail_tendsto_zero (ε/3) (by positivity)
  simp only [true_and, Set.mem_Ici, zero_sub, zero_add, Set.mem_Ioo] at hN_M
  replace hN_M := And.right <| hN_M (N_M + 1) (Nat.le_succ _)
  have f_norm_summable (n: ℕ): Summable (λ k ↦ ‖f k n‖) := Summable.of_nonneg_of_le (λ _ ↦ norm_nonneg _) (λ k ↦ h_bound k n) h_M_summable
  replace f_norm_summable := λ n ↦ (summable_nat_add_iff (f := λ k ↦ ‖f k n‖) (N_M + 1)).mpr <| f_norm_summable n
  replace h_M_summable := (summable_nat_add_iff (N_M + 1)).mpr h_M_summable
  replace f_lim_norm_summable := (summable_nat_add_iff (N_M + 1)).mpr f_lim_norm_summable
  have fk_bound (k: ℕ): ∃ Nk, ∀ n ≥ Nk, ‖f k n - f_lim k‖ ≤ ε/(3*(N_M + 1)) := by
    have f_k_limit: Tendsto (λ n ↦ ‖f k n - f_lim k‖) atTop (𝓝 0) := by
      rw [show 0 = ‖(0: α)‖ from Eq.symm norm_zero]
      apply Tendsto.norm
      rw [←sub_self (f_lim k)]
      exact Tendsto.sub (h_lim k) tendsto_const_nhds
    rw [atTop_basis.tendsto_iff <| nhds_basis_Ioo_pos 0] at f_k_limit
    obtain ⟨Nk, hNk⟩ := f_k_limit (ε/(3*(N_M + 1))) (by positivity)
    simp only [Set.mem_Ici, zero_sub, zero_add, Set.mem_Ioo, true_and] at hNk
    use Nk
    intro n hn
    exact le_of_lt (hNk n hn).right
  let N_k: ℕ → ℕ := λ k ↦ (fk_bound k).choose
  let N_k_max := Finset.max' (Finset.image N_k <| Finset.range (N_M + 1)) (Finset.image_nonempty.mpr Finset.nonempty_range_succ)
  let N := max N_M N_k_max
  use N
  intro n hn
  rw [NormedAddGroup.dist_eq]
  calc
    ‖∑' k, f k n - ∑' k, f_lim k‖ = ‖(∑ k ∈ Finset.range (N_M + 1), f k n - ∑ k ∈ Finset.range (N_M + 1), f_lim k) + (∑' k, f (k + (N_M + 1)) n - ∑' k, f_lim (k + (N_M + 1)))‖ := by
      rw [←Summable.sum_add_tsum_nat_add (N_M + 1) (f_summable n)]
      rw [←Summable.sum_add_tsum_nat_add (N_M + 1) f_lim_summable]
      ring_nf -- No idea why ring fails to close the goal, but ring_nf works
    _ ≤ ‖∑ k ∈ Finset.range (N_M + 1), (f k n - f_lim k)‖ + (‖∑' k, f (k + (N_M + 1)) n‖ + ‖∑' k, f_lim (k + (N_M + 1))‖) := by
      apply le_trans (norm_add_le _ _)
      rw [Finset.sum_sub_distrib]
      apply add_le_add_left (norm_sub_le _ _)
    _ ≤ ∑ k ∈ Finset.range (N_M + 1), ‖f k n - f_lim k‖ + (∑' k, ‖f (k + (N_M + 1)) n‖ + ∑' k, ‖f_lim (k + (N_M + 1))‖) := by
      apply add_le_add
      apply norm_sum_le
      apply add_le_add
      exact norm_tsum_le_tsum_norm <| f_norm_summable n
      exact norm_tsum_le_tsum_norm f_lim_norm_summable
    _ ≤ ∑ k ∈ Finset.range (N_M + 1), (ε/(3*(N_M + 1))) + (∑' k, M (k + (N_M + 1)) + ∑' k, M (k + N_M + 1)) := by
      apply add_le_add
      apply Finset.sum_le_sum
      intro k hk
      have n_large := by calc
        n ≥ N_k_max := le_of_max_le_right hn
        _ ≥ N_k k := by
          apply Finset.le_max'
          rw [Finset.mem_image]
          use k
      exact (fk_bound k).choose_spec n n_large
      apply add_le_add
      apply Summable.tsum_le_tsum (λ k ↦ h_bound (k + (N_M + 1)) n)
      exact f_norm_summable n
      exact h_M_summable
      exact Summable.tsum_le_tsum (λ k ↦ norm_f_lim_le_M (k + (N_M + 1))) f_lim_norm_summable h_M_summable
    _ < ε/3 + ε/3 + ε/3 := by
      rw [add_assoc]
      apply add_lt_add_of_le_of_lt
      rw [Finset.sum_const, Finset.card_range]
      apply le_of_eq
      field_simp
      ring
      exact add_lt_add hN_M hN_M
    _ = ε := add_thirds ε
