import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

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
  -- have M_k_nonneg: 0 ≤ M := λ k ↦ le_trans (norm_nonneg <| f k 0) (h_bound k 0)
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
  replace f_norm_summable := λ n ↦ (summable_nat_add_iff (N_M + 1)).mpr <| f_norm_summable n
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

theorem le_exp_norm_sub_one {α : Type*} [NormedRing α] [Nontrivial α] [NormMulClass α] (x : α) :
    ‖x‖ ≤ Real.exp (‖x - 1‖) := calc
  ‖x‖ = ‖x - 1 + 1‖ := by
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
  _ ≤ ‖x - 1‖ + 1 := by
    apply le_trans (norm_add_le _ _) _
    rw [IsAbsoluteValue.abv_one' norm]
  _ ≤ Real.exp (‖x - 1‖) := Real.add_one_le_exp _

theorem List.prod_nonneg {α : Type*} [One α] [Preorder α] [MulZeroClass α] [PosMulMono α]
    [ZeroLEOneClass α] {l : List α} (h_nonneg : ∀ a ∈ l, 0 ≤ a) : 0 ≤ l.prod := by
  apply List.prod_induction (0 ≤ ·)
  exact fun _ _ ha hb ↦ mul_nonneg ha hb
  exact zero_le_one
  exact h_nonneg

theorem List.prod_le_prod₀ {α β: Type*} [One β] [Preorder β] [MulZeroClass β] [PosMulMono β]
    [MulPosMono β] [ZeroLEOneClass β] {f g : α → β} {l : List α} (hfg : ∀ i ∈ l, f i ≤ g i) 
    (hf: ∀ i ∈ l, 0 ≤ f i) (hg: ∀ i ∈ l, 0 ≤ g i) : (l.map f).prod ≤ (l.map g).prod := by
  induction' l with head tail h_tail 
  simp
  repeat rw [map_cons, prod_cons]
  apply mul_le_mul_of_nonneg
  exact hfg head mem_cons_self
  apply h_tail
  exact fun i hi ↦ hfg i (mem_cons_of_mem head hi)
  exact fun i hi ↦ hf i (mem_cons_of_mem head hi)
  exact fun i hi ↦ hg i (mem_cons_of_mem head hi)
  exact hf head mem_cons_self 
  apply List.prod_nonneg
  intro a ha
  obtain ⟨b, ⟨hb, heq⟩⟩ := mem_map.mp ha
  rw [←heq]
  exact hg b (mem_cons_of_mem head hb)

theorem List.le_prod_of_norm_of_sub_one_of_norm_of_sub_one {α : Type*} [NormedRing α] [Nontrivial α]
    [NormMulClass α] {l: List α} : ‖l.prod - 1‖ ≤ (l.map (‖· - 1‖ + 1)).prod - 1 := by
  induction' l with head tail h_tail
  simp
  rw [List.prod_cons, List.map_cons, List.prod_cons]
  calc
    ‖head * tail.prod - 1‖ = ‖head * (tail.prod - 1) + (head - 1)‖ := by
      rw [mul_sub, mul_one, add_sub, sub_eq_add_neg _ head, add_assoc, neg_add_cancel, add_zero]
    _ ≤ ‖head * (tail.prod - 1)‖ + ‖head - 1‖ := norm_add_le _ _
    _ ≤ ‖head‖ * ‖tail.prod - 1‖ + ‖head - 1‖ := add_le_add_right (norm_mul_le _ _) _
    _ ≤ ‖head‖ * ((tail.map (‖· - 1‖ + 1)).prod - 1) + ‖head - 1‖ :=
      add_le_add_right (mul_le_mul_of_nonneg_left h_tail (norm_nonneg _)) _
    _ ≤ (‖head - 1‖ + 1) * ((tail.map (‖· - 1‖ + 1)).prod - 1) + ‖head - 1‖ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right
      rw [←IsAbsoluteValue.abv_one' (norm : α → ℝ)]
      apply le_trans _ (norm_add_le _ _)
      rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
      exact le_trans (norm_nonneg _) h_tail
    _ = (‖head - 1‖ + 1) * (tail.map (‖· - 1‖ + 1)).prod - 1 := by ring

theorem List.norm_prod_sub_one_le_exp_sub_one {α : Type*} [NormedRing α] [Nontrivial α]
    [NormMulClass α] {l : List α} : ‖l.prod - 1‖ ≤ Real.exp ((l.map (‖· - 1‖)).sum) - 1 := by
  apply le_trans l.le_prod_of_norm_of_sub_one_of_norm_of_sub_one <| sub_le_sub_right _ _
  apply le_trans (List.prod_le_prod₀ (fun x _ ↦ Real.add_one_le_exp (‖x - 1‖)) _ _) _
  exact fun _ _ ↦ by positivity
  exact fun _ _ ↦ by positivity
  rw [Real.exp_list_sum, map_map]
  rfl

theorem Finset.norm_prod_sub_one_le_exp_sub_one {α ι : Type*} [NormedCommRing α]
    [Nontrivial α] [NormMulClass α] {s : Finset ι} {f : ι → α} :
    ‖∏ i ∈ s, f i - 1‖ ≤ Real.exp (∑ i ∈ s, ‖f i - 1‖) - 1 := by
  rw [←Finset.prod_map_toList, ←Finset.sum_map_toList]
  convert List.norm_prod_sub_one_le_exp_sub_one
  simp
  all_goals assumption

theorem List.norm_prod_le_exp_sum_norm_sub_one {α : Type*} [NormedRing α] [Nontrivial α]
    [NormMulClass α] [NormOneClass α] {l : List α} :
    ‖l.prod‖ ≤ Real.exp ((l.map (‖· - 1‖)).sum) := by
  rw [List.norm_prod]
  apply le_trans (l.prod_le_prod₀ (fun x _ ↦ le_exp_norm_sub_one x) _ _) _
  exact fun _ _ ↦ norm_nonneg _
  exact fun _ _ ↦ Real.exp_nonneg _
  rw [Real.exp_list_sum, map_map]
  rfl

theorem Finset.norm_prod_le_exp_sum_norm_sub_one {α ι : Type*} [NormedCommRing α] [Nontrivial α]
    [NormMulClass α] [NormOneClass α] {s : Finset ι} {f : ι → α} :
    ‖∏ i ∈ s, f i‖ ≤ Real.exp (∑ i ∈ s, ‖f i - 1‖) := by
  rw [←Finset.prod_map_toList, ←Finset.sum_map_toList]
  convert List.norm_prod_le_exp_sum_norm_sub_one
  simp
  all_goals assumption

-- Based on proof from
-- [course notes for Analytic Number Theory](https://pub.math.leidenuniv.nl/~evertsejh/ant20-0.pdf)
theorem uniformCauchySeqOn_prod {α ι R : Type*} [NormedCommRing R] [Nontrivial R] [NormMulClass R]
    [NormOneClass R] [DecidableEq ι] {f : ι → α → R} {u : ι → ℝ} {s : Set α} (hu : Summable u)
    (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i) :
    UniformCauchySeqOn (fun (t : Finset ι) ↦ fun (x : α) ↦  ∏ i ∈ t, f i x) atTop s := by
  by_cases s_nonempty : s.Nonempty
  have u_nonneg : 0 ≤ u := fun i ↦ le_trans (norm_nonneg _)
    (hfu i s_nonempty.choose s_nonempty.choose_spec)
  refine Metric.uniformCauchySeqOn_iff.mpr fun ε εpos ↦ ?_
  have h_tail := tendsto_tsum_compl_atTop_zero u
  have h_exp_lim : Tendsto (Real.exp · - 1) (𝓝 0) (𝓝 0) :=
    (Real.continuous_exp.sub continuous_const).tendsto' 0 0 (by norm_num)
  have h_exp_tail := h_exp_lim.comp h_tail
  replace h_exp_tail := (tendsto_order.mp h_exp_tail).right
    (ε / (2 * Real.exp (∑' i, u i))) (by positivity)
  simp only [Function.comp_apply, eventually_atTop] at h_exp_tail
  obtain ⟨N, hN⟩ := h_exp_tail
  use N
  intro m hm n hn x hx
  have h_lemma : ∀ n ≥ N, ‖∏ i ∈ n, f i x - ∏ i ∈ N, f i x‖ < ε/2 := fun n hn ↦ calc
    ‖∏ i ∈ n, f i x - ∏ i ∈ N, f i x‖ = ‖∏ i ∈ N, f i x‖ * ‖∏ i ∈ n \ N, f i x - 1‖ := by
      rw [←Finset.prod_sdiff hn, mul_comm]
      nth_rewrite 2 [←mul_one (∏ i ∈ N, f i x)]
      rw [←mul_sub, norm_mul]
    _ ≤ Real.exp (∑ i ∈ N, ‖f i x - 1‖) * (Real.exp (∑ i ∈ n \ N, ‖f i x - 1‖) - 1) := by
      apply mul_le_mul_of_nonneg
      exact Finset.norm_prod_le_exp_sum_norm_sub_one
      exact Finset.norm_prod_sub_one_le_exp_sub_one
      exact norm_nonneg _
      rw [le_sub_iff_add_le, zero_add]
      exact Real.one_le_exp <| Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    _ ≤ Real.exp (∑ i ∈ N, u i) * (Real.exp (∑ i ∈ n \ N, u i) - 1) := by
      apply mul_le_mul_of_nonneg
      apply Real.exp_monotone <| Finset.sum_le_sum (fun i _ ↦ hfu i x hx)
      apply sub_le_sub_right
      apply Real.exp_monotone <| Finset.sum_le_sum (fun i _ ↦ hfu i x hx)
      exact Real.exp_nonneg _
      rw [le_sub_iff_add_le, zero_add]
      apply Real.one_le_exp <| Finset.sum_nonneg fun i _ ↦ u_nonneg i
    _ ≤ Real.exp (∑' i, u i) * (Real.exp (∑' i : { x // x ∉ N }, u i) - 1) := by
      apply mul_le_mul_of_nonneg
      apply Real.exp_monotone
      exact hu.sum_le_tsum N (fun i _ ↦ u_nonneg i)
      apply sub_le_sub_right
      apply Real.exp_monotone
      rw [←Finset.tsum_subtype]
      let emb (x : { x // x ∈ n \ N }) : { x // x ∉ N } := {
        val := x.val
        property := (Finset.mem_sdiff.mp x.property).right
      }
      have emb_injective : Function.Injective emb := fun _ _ heq ↦ by
        apply_fun Subtype.val at heq
        exact Subtype.mk_eq_mk.mpr heq
      apply Summable.tsum_le_tsum_of_inj emb emb_injective 
      exact fun i _ ↦ u_nonneg i
      exact fun _ ↦ by rfl
      apply Summable.subtype hu
      apply Summable.subtype hu
      exact Real.exp_nonneg _
      rw [le_sub_iff_add_le, zero_add]
      apply Real.one_le_exp
      apply tsum_nonneg fun (i : { x // x ∉ N }) ↦ u_nonneg i.val 
    _ < Real.exp (∑' i, u i) * (ε / (2 * Real.exp (∑' i, u i))) := by
      exact (mul_lt_mul_left (Real.exp_pos _)).mpr (hN N (by rfl))
    _ = ε/2 := by field_simp; ring
  calc
    dist (∏ i ∈ m, f i x) (∏ i ∈ n, f i x) =
    ‖∏ i ∈ m, f i x - ∏ i ∈ N, f i x - (∏ i ∈ n, f i x - ∏ i ∈ N, f i x)‖ := by
      rw [dist_eq_norm]
      ring_nf
    _ ≤ ‖∏ i ∈ m, f i x - ∏ i ∈ N, f i x‖ + ‖∏ i ∈ n, f i x - ∏ i ∈ N, f i x‖ := norm_sub_le _ _
    _ < ε/2 + ε/2 := add_lt_add (h_lemma m hm) (h_lemma n hn)
    _ = ε := add_halves ε
  unfold UniformCauchySeqOn
  simp [Set.not_nonempty_iff_eq_empty.mp s_nonempty]

theorem TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded {α ι R : Type*} [NormedCommRing R]
    [Nontrivial R] [NormMulClass R] [NormOneClass R] [DecidableEq ι] {f : ι → α → R} {u : ι → ℝ}
    {s : Set α} (hu : Summable u) (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i)
    (hf : ∀ x ∈ s, Multipliable (f · x)) :
    TendstoUniformlyOn (fun (t : Finset ι) ↦ fun (x : α) ↦  ∏ i ∈ t, f i x)
    (fun x ↦ ∏' n, f n x) atTop s := by
  exact (uniformCauchySeqOn_prod hu hfu).tendstoUniformlyOn_of_tendsto fun x hx ↦ (hf x hx).hasProd

theorem Multipliable.of_norm_bounded_of_complete {α ι R : Type*} 
    [NormedCommRing R] [Nontrivial R] [NormMulClass R] [NormOneClass R] [CompleteSpace R
    ][DecidableEq ι] {f : ι → α → R} {u : ι → ℝ} {s : Set α} (hu : Summable u)
    (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i) :
    ∀ x ∈ s, Multipliable (f · x) := by
  intro x hx
  apply cauchySeq_tendsto_of_complete
  apply UniformCauchySeqOn.cauchySeq _ hx
  apply uniformCauchySeqOn_prod hu hfu

theorem TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded_of_complete {α ι R : Type*} 
    [NormedCommRing R] [Nontrivial R] [NormMulClass R] [NormOneClass R] [CompleteSpace R
    ][DecidableEq ι] {f : ι → α → R} {u : ι → ℝ} {s : Set α} (hu : Summable u)
    (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i) :
    TendstoUniformlyOn (fun (t : Finset ι) ↦ fun (x : α) ↦  ∏ i ∈ t, f i x)
    (fun x ↦ ∏' n, f n x) atTop s := by
  have hf := Multipliable.of_norm_bounded_of_complete hu hfu
  exact (uniformCauchySeqOn_prod hu hfu).tendstoUniformlyOn_of_tendsto fun x hx ↦ (hf x hx).hasProd

theorem TendstoUniformlyOn.of_prod_of_norm_bounded {α R : Type*} [NormedCommRing R] [Nontrivial R]
    [NormMulClass R] [NormOneClass R] {f : ℕ → α → R} {u : ℕ → ℝ} {s : Set α} (hu : Summable u)
    (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i) (hf : ∀ x ∈ s, Multipliable (f · x)) :
    TendstoUniformlyOn (fun n ↦ fun x ↦ ∏ i ∈ Finset.range n, f i x) (∏' n, f n ·) atTop s := by
  have h_abs_uniformly := TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded hu hfu hf
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn.mp h_abs_uniformly Finset.range
    tendsto_finset_range

theorem TendstoUniformlyOn.of_prod_of_norm_bounded_of_complete {α R : Type*} [NormedCommRing R]
    [Nontrivial R] [NormMulClass R] [NormOneClass R] [CompleteSpace R] {f : ℕ → α → R} {u : ℕ → ℝ}
    {s : Set α} (hu : Summable u) (hfu : ∀ i, ∀ x ∈ s, ‖f i x - 1‖ ≤ u i) :
    TendstoUniformlyOn (fun n ↦ fun x ↦ ∏ i ∈ Finset.range n, f i x) (∏' n, f n ·) atTop s := by
  have hf := Multipliable.of_norm_bounded_of_complete hu hfu
  exact TendstoUniformlyOn.of_prod_of_norm_bounded hu hfu hf

theorem TendstoUniformlyOn.mul₀_of_bounded {α ι R : Type*} [NormedRing R] {F G : ι → α → R}
    {f g : α → R} {l : Filter ι} {s : Set α} 
    (hf: TendstoUniformlyOn F f l s) (hg: TendstoUniformlyOn G g l s)
    (hf_bounded : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C) (hg_bounded : ∃ C, ∀ x ∈ s, ‖g x‖ ≤ C) :
    TendstoUniformlyOn (fun i x ↦ (F i x) * (G i x)) (f * g) l s := by
  by_cases s_nonempty : s.Nonempty
  obtain ⟨f_bound, hf_bound⟩ := hf_bounded
  obtain ⟨g_bound, hg_bound⟩ := hg_bounded
  have f_bound_nonneg : 0 ≤ f_bound := le_trans (norm_nonneg _) <|
    hf_bound s_nonempty.choose s_nonempty.choose_spec
  have g_bound_nonneg : 0 ≤ g_bound := le_trans (norm_nonneg _) <|
    hg_bound s_nonempty.choose s_nonempty.choose_spec
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε εpos
  let εg := ε/(2 * (f_bound + 1)) 
  let εf := ε/(2 * (εg + g_bound))
  filter_upwards [hf εf (by positivity), hg εg (by positivity)] with n hf hg x hx 
  simp_rw [dist_eq_norm] at hf hg ⊢
  calc
    ‖(f * g) x - F n x * G n x‖ = ‖f x * (g x - G n x) + (f x - F n x) * G n x‖ := by
      rw [mul_sub, sub_eq_add_neg _ (f x * _), add_assoc, sub_mul, sub_eq_add_neg (_ * G n x) _,
          ←add_assoc (-_), neg_add_cancel, zero_add, ←sub_eq_add_neg]
      rfl
    _ ≤ ‖f x‖ * ‖g x - G n x‖ + ‖f x - F n x‖ * ‖G n x‖ :=
      le_trans (norm_add_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ < (f_bound + 1) * εg + εf * (‖G n x - g x‖ + ‖g x‖) := by
      apply add_lt_add_of_lt_of_le
      exact mul_lt_mul_of_nonneg (by linarith [hf_bound x hx]) (hg x hx)
        (norm_nonneg _) (norm_nonneg _) 
      refine mul_le_mul_of_nonneg (le_of_lt <| hf x hx) ?_ (norm_nonneg _) (by positivity)
      convert norm_add_le (G n x - g x) (g x)
      exact Eq.symm <| sub_add_cancel (G n x) (g x)
    _ ≤ (f_bound + 1) * εg + εf * (εg + g_bound) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ (hg_bound x hx)
      rw [norm_sub_rev]
      exact le_of_lt <| hg x hx
    _ = ε := by
      unfold εf εg
      field_simp
      ring 
  unfold TendstoUniformlyOn
  replace s_nonempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp s_nonempty
  aesop

theorem TendstoUniformlyOn.mul₀_of_continuousOn_of_compact {α ι R : Type*} [TopologicalSpace α]
    [NormedRing R] {F G : ι → α → R} {f g : α → R} {l : Filter ι} {s : Set α} 
    (hf: TendstoUniformlyOn F f l s) (hg: TendstoUniformlyOn G g l s)
    (hf_cont : ContinuousOn f s) (hg_cont : ContinuousOn g s) (h_compact : IsCompact s) :
    TendstoUniformlyOn (fun i x ↦ (F i x) * (G i x)) (f * g) l s :=
  TendstoUniformlyOn.mul₀_of_bounded hf hg (h_compact.exists_bound_of_continuousOn hf_cont)
    (h_compact.exists_bound_of_continuousOn hg_cont)

theorem TendstoUniformly.of_const {α ι R : Type*} [UniformSpace R] (f : α → R) (l : Filter ι) :
    TendstoUniformly (fun (_ : ι) ↦ f) f l := by
  rw [tendstoUniformly_iff_tendsto, tendsto_prod_iff]
  exact fun _ h ↦ ⟨⊤, ⟨univ_mem, ⟨⊤, ⟨fun _ ↦ trivial, fun _ _ _ _ ↦ mem_uniformity_of_eq h rfl⟩⟩⟩⟩

theorem TendstoUniformlyOn.of_const {α ι R : Type*} [UniformSpace R] (f : α → R) (l : Filter ι)
    (s : Set α) : TendstoUniformlyOn (fun (_ : ι) ↦ f) f l s :=
  (TendstoUniformly.of_const f l).tendstoUniformlyOn

-- Based on a proof found on
-- [Wikipedia](https://en.wikipedia.org/wiki/Iterated_limit#Moore-Osgood_theorem_for_interchanging_limits)
theorem TendstoUniformlyOn.interchange_limits {ι R₁ R₂ : Type*} [Nonempty ι] [SemilatticeSup ι]
    [NormedRing R₂] [CompleteSpace R₂] {a : ι → R₁ → R₂} {b : R₁ → R₂} {c : ι → R₂}
    {l : Filter R₁} [l.NeBot] {s : Set R₁} (hb : TendstoUniformlyOn a b atTop s)
    (hc : ∀ᶠ n in atTop, Tendsto (fun x ↦ a n x) l (𝓝 (c n))) (hs : s ∈ l):
    ∃ L : R₂, Tendsto b l (𝓝 L) ∧ Tendsto c atTop (𝓝 L) := by
  rw [tendstoUniformlyOn_iff] at hb
  rw [eventually_atTop] at hc
  obtain ⟨N₁, hN₁⟩ := hc  
  have hcauchy : CauchySeq c := by
    refine Metric.cauchySeq_iff'.mpr fun ε εpos ↦ ?_
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp <| hb (ε/4) (by positivity)
    use max N₁ N₂
    intro n hn
    apply sup_le_iff.mp at hn
    rw [dist_eq_norm]
    have hdiff_tendsto : Tendsto (fun x ↦ ‖a n x - a (N₁ ⊔ N₂) x‖) l (𝓝 (‖c n - c (N₁ ⊔ N₂)‖)) :=
      Tendsto.norm <| Tendsto.sub (hN₁ n hn.left) (hN₁ _ le_sup_left)
    refine lt_of_le_of_lt (tendsto_le_of_eventuallyLE hdiff_tendsto tendsto_const_nhds ?_)
      (div_two_lt_of_pos εpos)
    filter_upwards [hs] with x hx
    apply le_of_lt
    calc
      ‖a n x - a (N₁ ⊔ N₂) x‖ = ‖(a n x - b x) - (a (N₁ ⊔ N₂) x - b x)‖ := by
        apply congrArg
        rw [sub_sub_sub_cancel_right]
      _ ≤ ‖a n x - b x‖ + ‖a (N₁ ⊔ N₂) x - b x‖ := norm_sub_le _ _
      _ = dist (b x) (a n x) + dist (b x) (a (N₁ ⊔ N₂) x) := by
        rw [norm_sub_rev, ←dist_eq_norm, norm_sub_rev, ←dist_eq_norm]
      _ < ε/4 + ε/4 := by
        apply add_lt_add
        exact hN₂ n hn.right x hx
        exact hN₂ (N₁ ⊔ N₂) le_sup_right x hx
      _ = ε/2 := by ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ⟨?_, hL⟩⟩
  refine Metric.tendsto_nhds.mpr fun ε εpos ↦ ?_
  obtain ⟨N₃, hN₃⟩ :=  eventually_atTop.mp <| Metric.tendsto_nhds.mp hL (ε/3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp <| hb (ε/3) (by positivity)
  let n := max (max N₁ N₂) N₃
  replace hN₁ := hN₁ n (le_sup_of_le_left le_sup_left)
  replace hN₂ := hN₂ n (le_sup_of_le_left le_sup_right)
  replace hN₃ := hN₃ n le_sup_right
  rw [Metric.tendsto_nhds] at hN₁
  filter_upwards [hN₁ (ε/3) (by positivity), hs] with x hx_dist hx_elem
  calc
    dist (b x) L = ‖(b x - a n x) + (a n x - c n) + (c n - L)‖ := by
      rw [dist_eq_norm, sub_add_sub_cancel, sub_add_sub_cancel]
    _ ≤ ‖b x - a n x‖ + ‖a n x - c n‖ + ‖c n - L‖ := by
      refine le_trans (norm_add_le _ _) ?_
      apply add_le_add_right <| norm_add_le _ _
    _ < ε/3 + ε/3 + ε/3 := by
      apply add_lt_add
      apply add_lt_add
      rw [←dist_eq_norm]
      exact hN₂ x hx_elem
      rwa [dist_eq_norm] at hx_dist
      rwa [dist_eq_norm] at hN₃
    _ = ε := add_thirds ε

theorem interchange_limit_prod_of_tendstoUniformlyOn {ι α R : Type*} [Nonempty ι] [SemilatticeSup ι]
    [DecidableEq ι] [NormedCommRing R] [CompleteSpace R] {f : ι → α → R} {g : ι → R} {l : Filter α} 
    [l.NeBot] {s : Set α}
    (h : TendstoUniformlyOn (fun (is : Finset ι) ↦ fun (a : α) ↦  ∏ i ∈ is, f i a)
    (fun a ↦ ∏' i, f i a) atTop s) (hlim : ∀ i : ι, Tendsto (f i ·) l (𝓝 (g i))) (hs : s ∈ l) :
    Tendsto (fun a ↦ ∏' i, f i a) l (𝓝 (∏' i, g i)) := by
  have hfin_prods_converge (is : Finset ι) :
      Tendsto (fun a ↦ ∏ i ∈ is, f i a) l (𝓝 (∏ i ∈ is, g i)) :=
    tendsto_finset_prod is (fun i _ ↦ hlim i)
  obtain ⟨L, ⟨hL₁, hL₂⟩⟩ := TendstoUniformlyOn.interchange_limits h
    (Eventually.of_forall hfin_prods_converge) hs
  rwa [←HasProd.tprod_eq hL₂] at hL₁

lemma aux_norm_prod {α : Type*} [NormedRing α] [Nontrivial α] [NormMulClass α] {x : ℝ} (hx₀ : 0 ≤ x)
    (hx₁ : x ≤ 1) (y : α) : 1 - (‖y - 1‖ + x) ≤ ‖y‖ * (1 - x) := by
  calc
    ‖y‖ * (1 - x) ≥ (1 - ‖y - 1‖) * (1 - x) := by
      refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg_of_le hx₁)
      rw [norm_sub_rev, ←IsAbsoluteValue.abv_one' (norm : α → ℝ)]
      convert norm_sub_norm_le _ _
      rw [sub_sub_cancel]
    _ = 1 - (‖y - 1‖ + x) + ‖y - 1‖ * x := by ring
    _ ≥ 1 - (‖y - 1‖ + x) :=
      le_add_of_le_of_nonneg (le_of_eq <| Eq.refl _) (mul_nonneg (norm_nonneg _) hx₀)

lemma List.one_sub_sum_norm_le_prod_norm {α : Type*} [NormedRing α] [Nontrivial α]
    [NormMulClass α] {l : List α} (h : (l.map (‖· - 1‖)).sum ≤ 1) :
    1 - (l.map (‖· - 1‖)).sum ≤ ‖l.prod‖ := by
  induction' l with head tail htail
  simp [IsAbsoluteValue.abv_one' (norm : α → ℝ)]
  rw [prod_cons, norm_mul, map_cons, sum_cons]
  have hsum_norm_tail_nonneg : 0 ≤ (tail.map (‖· - 1‖)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨_, ⟨_, hx_eq_norm⟩⟩ := List.mem_map.mp hx
    rw [←hx_eq_norm]
    exact norm_nonneg _
  have hsum_norm_tail_le_one : (tail.map (‖· - 1‖)).sum ≤ 1 := by
    apply le_trans _ h
    rw [map_cons, sum_cons]
    exact (le_add_iff_nonneg_left _).mpr (norm_nonneg _)
  refine le_trans (aux_norm_prod hsum_norm_tail_nonneg hsum_norm_tail_le_one head) ?_
  exact mul_le_mul_of_nonneg_left (htail hsum_norm_tail_le_one) (norm_nonneg _)

lemma Finset.one_sub_sum_norm_le_prod_norm {α ι: Type*} [NormedCommRing α] [Nontrivial α]
    [NormMulClass α] {s : Finset ι} {f : ι → α} (h : ∑ i ∈ s, ‖f i - 1‖ ≤ 1) :
    1 - ∑ i ∈ s, ‖f i - 1‖ ≤ ‖∏ i ∈ s, f i‖ := by
    rw [←Finset.prod_map_toList, ←Finset.sum_map_toList]
    rw [show (fun i : ι ↦ ‖f i - 1‖) = (fun a : α ↦ ‖a - 1‖) ∘ (fun i : ι ↦ f i) by rfl]
    rw [←List.map_map]
    apply List.one_sub_sum_norm_le_prod_norm
    simp [h]

-- Based on proof from
-- [course notes for Analytic Number Theory](https://pub.math.leidenuniv.nl/~evertsejh/ant20-0.pdf)
theorem product_nonzero_of_terms_nonzero_of_summable_norm {α ι R : Type*} [NormedCommRing R]
    [Nontrivial R] [NormMulClass R] [NormOneClass R] [DecidableEq ι] {f : ι → R}
    (hmultipliable : Multipliable f) (hsummable : Summable (fun i : ι ↦ ‖f i - 1‖))
    (hnon_zero : ∀ i, f i ≠ 0) : ∏' i : ι, f i ≠ 0 := by
  have htail_tendsto_zero := tendsto_tsum_compl_atTop_zero (fun i : ι ↦ ‖f i - 1‖)
  apply (atTop_basis.tendsto_iff (nhds_basis_Ioo_pos 0)).mp at htail_tendsto_zero
  obtain ⟨M, ⟨_, hM⟩⟩ := htail_tendsto_zero ((1 : ℝ) / 2) one_half_pos 
  replace hM := hM M (Set.mem_Ici.mpr (le_refl M))
  rw [Set.mem_Ioo] at hM
  replace hM := hM.right
  norm_num at hM
  have hpartial_sum_upper_bound (s : Finset ι) : ∑ i ∈ (s \ M), ‖f i - 1‖ ≤ (1 : ℝ) / 2 := by
    rw [←Finset.tsum_subtype]
    let emb (x : { x // x ∈ s \ M }) : { x // x ∉ M } := {
      val := x.val
      property := (Finset.mem_sdiff.mp x.property).right
    }
    have emb_injective : Function.Injective emb := fun _ _ heq ↦ by
      apply_fun Subtype.val at heq
      exact Subtype.mk_eq_mk.mpr heq
    refine le_trans ?_ (le_of_lt hM)
    apply Summable.tsum_le_tsum_of_inj emb emb_injective
    exact fun _ _ ↦ norm_nonneg _
    exact fun _ ↦ by rfl
    apply Summable.subtype hsummable  
    apply Summable.subtype hsummable  
  have hpartial_products_lower_bound (s : Finset ι) :
      1 - ∑ i ∈ (s \ M), ‖f i - 1‖ ≤ ‖∏ i ∈ (s \ M), f i‖ := by
    apply Finset.one_sub_sum_norm_le_prod_norm
    refine le_trans (hpartial_sum_upper_bound s) (by norm_num)
  replace hpartial_products_lower_bound (s : Finset ι) :
      (1 : ℝ) / 2 ≤ ‖∏ i ∈ (s \ M), f i‖ := by
    refine le_trans ?_ (hpartial_products_lower_bound s)
    linarith [hpartial_sum_upper_bound s]
  suffices ‖∏ i ∈ M, f i‖ * ((1 : ℝ) / 2) ≤ ‖∏' i : ι, f i‖ by
    have : ‖∏ i ∈ M, f i‖ > 0 := by
      rw [norm_prod]
      exact Finset.prod_pos fun i _ ↦ norm_pos_iff.mpr (hnon_zero i)
    apply norm_pos_iff.mp
    linarith
  refine ge_of_tendsto (Tendsto.norm (Multipliable.hasProd hmultipliable)) ?_
  filter_upwards [eventually_ge_atTop M] with s hsubset
  have hdisjoint : Disjoint M (s \ M) := Finset.disjoint_sdiff
  rw [←Finset.union_sdiff_of_subset hsubset, Finset.prod_union hdisjoint, norm_mul]
  exact mul_le_mul_of_nonneg_left (hpartial_products_lower_bound s) (norm_nonneg _)

