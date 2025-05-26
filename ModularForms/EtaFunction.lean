import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Defs.Filter
import ModularForms.Analysis

open Real UpperHalfPlane Matrix Filter Topology
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

lemma multipliableLocallyUniformlyOn_eta_product :
    MultipliableLocallyUniformlyOn (fun n : ℕ ↦ fun τ ↦ 1 - cexp (2 * π * Complex.I * ↑(n + 1) * τ))
      {z : ℂ | 0 < z.im } := by
  use fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * τ))
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact ?_).mpr ?_
  exact isOpen_lt continuous_const continuous_im
  intro K Ksubset Kcompact
  by_cases hK_nonempty : K.Nonempty
  obtain ⟨im_bound, ⟨him_bound_elem, him_bound⟩⟩ :=
    Kcompact.exists_isMinOn hK_nonempty continuous_im.continuousOn
  have : ∀ z ∈ K, im_bound.im ≤ z.im := by exact fun z a ↦ him_bound a
  let u := fun n : ℕ ↦ (rexp (-2 * π * im_bound.im))^(n + 1)
  apply TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded_of_complete (u := u)
  refine (summable_nat_add_iff 1).mpr <| summable_geometric_of_lt_one (exp_nonneg _) ?_
  refine exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos ?_ (Ksubset him_bound_elem)
  exact mul_neg_of_neg_of_pos (neg_neg_iff_pos.mpr two_pos) pi_pos
  intro n τ τelem
  unfold u
  rw [sub_right_comm, sub_self, norm_sub_rev, sub_zero, norm_exp, ←Real.exp_nat_mul]
  apply exp_le_exp.mpr
  rw [show (2 * π * Complex.I * ↑(n + 1) * τ).re = ↑(n + 1) * (-2 * π * τ.im) by
    simp only [Nat.cast_add, Nat.cast_one, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self,
      add_re, natCast_re, one_re, add_im, natCast_im, one_im, zero_add, zero_sub, neg_mul, mul_neg,
      neg_inj]
    ring
  ]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg' (n + 1))
  refine mul_le_mul_of_nonpos_left ?_ (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ?_)
  exact him_bound τelem
  exact le_of_lt pi_pos
  rw [Set.not_nonempty_iff_eq_empty.mp hK_nonempty]
  exact tendstoUniformlyOn_empty

lemma eta_differentiableOn_upperHalfPlane :
    DifferentiableOn ℂ (eta ∘ UpperHalfPlane.ofComplex) { τ : ℂ | 0 < τ.im } := by
  suffices DifferentiableOn ℂ (fun z : ℂ ↦ cexp (π * Complex.I * z / 12) *
    ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z))) {z : ℂ | 0 < z.im } by
      apply DifferentiableOn.congr this
      intro z hz
      lift z to ℍ using hz
      apply comp_ofComplex
  apply DifferentiableOn.mul
  apply Differentiable.differentiableOn
  apply Differentiable.comp Complex.differentiable_exp 
  apply Differentiable.div_const
  apply Differentiable.const_mul _
  rw [show (fun y : ℂ ↦ y) = id by rfl]
  exact differentiable_id
  apply TendstoLocallyUniformlyOn.differentiableOn
    multipliableLocallyUniformlyOn_eta_product.hasProdLocallyUniformlyOn
  filter_upwards with s τ hτ
  apply DifferentiableWithinAt.finset_prod
  intro n hn
  apply DifferentiableAt.differentiableWithinAt
  apply Differentiable.differentiableAt
  apply Differentiable.const_sub
  apply Differentiable.comp Complex.differentiable_exp
  apply Differentiable.const_mul
  rw [show (fun y : ℂ ↦ y) = id by rfl]
  exact differentiable_id
  exact isOpen_lt continuous_const continuous_im

theorem eta_theta_atImInfty : eta =Θ[atImInfty] (fun τ ↦ rexp (-π * τ.im / 12)) := by
  suffices h : Tendsto (fun z : ℍ ↦ ∏' n: ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z)))
      atImInfty (𝓝 1) by
    have hq12_theta : (fun τ : ℍ ↦ cexp (π * Complex.I * τ / 12)) =Θ[atImInfty]
        (fun τ : ℍ ↦ rexp (-π * τ.im / 12)) := by
      refine Asymptotics.IsTheta.of_norm_eventuallyEq (Eventually.of_forall fun τ ↦ ?_)
      simp [Complex.norm_exp]
    conv_rhs => ext _; rw [←mul_one (rexp _)]
    refine Asymptotics.IsTheta.mul hq12_theta ?_
    apply (atImInfty_basis.tendsto_iff (Metric.nhds_basis_ball)).mp at h
    obtain ⟨im_bound, ⟨_, him_bound⟩⟩ := h ((1 : ℝ) / 2) (by norm_num)
    constructor
    refine Asymptotics.IsBigO.of_bound ((3 : ℝ) / 2) ?_
    apply atImInfty_basis.eventually_iff.mpr
    refine ⟨im_bound, ⟨trivial, fun τ hτ ↦ ?_⟩⟩
    exact le_of_le_of_eq (le_of_lt <| norm_lt_of_mem_ball (him_bound τ hτ)) (by norm_num)
    refine Asymptotics.IsBigO.of_bound (2 : ℝ) ?_
    apply atImInfty_basis.eventually_iff.mpr
    refine ⟨im_bound, ⟨trivial, fun τ hτ ↦ ?_⟩⟩
    have := mem_ball_iff_norm.mp (him_bound τ hτ)
    rw [norm_sub_rev] at this
    have := le_trans (norm_sub_norm_le _ _) (le_of_lt this)
    rw [norm_one] at this ⊢
    linarith    
  let s := { τ : ℍ | τ.im ≥ 1 }
  have hprod_uniform : TendstoUniformlyOn (fun ns : Finset ℕ ↦ fun z : ℍ ↦
      ∏ n ∈ ns, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z))) 
      (fun z : ℍ ↦ ∏' n: ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z))) atTop s := by
    let u := fun n : ℕ ↦ (rexp (-2 * π))^(n + 1)
    have hu_summable : Summable u := by
      refine (summable_nat_add_iff 1).mpr <| summable_geometric_of_lt_one (exp_nonneg _) ?_
      exact exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (by norm_num) pi_pos
    apply TendstoUniformlyOn.absolutely_of_prod_of_norm_bounded_of_complete hu_summable 
    intro n τ hτ
    unfold u
    rw [sub_sub_cancel_left, norm_neg, Complex.norm_exp, ←Real.exp_nat_mul]
    rw [show (2 * π * Complex.I * ↑(n + 1) * τ).re = ↑(n + 1) * (-2 * π * τ.im) by
      simp only [Nat.cast_add, Nat.cast_one, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
        mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one,
        sub_self, add_re, natCast_re, one_re, add_im, natCast_im, one_im, coe_re, zero_add, coe_im,
        zero_sub, neg_mul, mul_neg, neg_inj]
      ring
    ]
    apply exp_le_exp.mpr
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg' (n + 1))
    nth_rw 2 [←mul_one (-2 * π)]
    refine mul_le_mul_of_nonpos_left ?_ (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ?_)
    exact hτ
    exact le_of_lt pi_pos
  have hpointwise_limit (n : ℕ) :
      Tendsto (fun τ : ℍ ↦ (1 - cexp (2 * π * Complex.I * ↑(n + 1) * τ))) atImInfty (𝓝 1) := by
    rw [show 𝓝 (1 : ℂ) = 𝓝 (1 - 0) by apply congrArg; exact Eq.symm <| sub_zero 1]
    apply Tendsto.const_sub
    refine UpperHalfPlane.isZeroAtImInfty_iff.mpr fun ε εpos ↦ ?_
    obtain ⟨R, hR⟩ := Set.mem_range.mp (show ε ∈ Set.range rexp by
      rw [Real.range_exp, Set.mem_Ioi]
      exact εpos
    )
    use (-R / (2 * π))
    intro τ hτ
    rw [Complex.norm_exp, ←hR]
    simp only [Nat.cast_add, Nat.cast_one, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self,
      add_re, natCast_re, one_re, add_im, natCast_im, one_im, coe_re, zero_add, coe_im, zero_sub,
      exp_le_exp]
    have := le_trans hτ (show τ.im ≤ ((n + 1) : ℝ) * τ.im by
      apply le_mul_of_one_le_left (le_of_lt τ.property)
      exact (le_add_iff_nonneg_left 1).mpr (Nat.cast_nonneg n)
    )
    apply (div_le_iff₀' two_pi_pos).mp at this
    rwa [←mul_assoc, neg_le] at this
  have atImInfty_neBot : atImInfty.NeBot := by
    refine neBot_iff.mpr fun heq ↦ ?_
    obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (empty_mem_iff_bot.mpr heq)
    let z : ℍ := {
      val := ⟨0, max A 1⟩
      property := lt_of_lt_of_le one_pos (le_max_right A 1)
    }
    exact hA z (le_max_left A 1)
  convert interchange_limit_prod_of_tendstoUniformlyOn hprod_uniform hpointwise_limit 
    ((atImInfty_mem s).mpr ⟨1, fun _ h ↦ h⟩)
  exact Eq.symm tprod_one

theorem eta_nonzero_on_upperHalfPlane (z : ℍ) : eta z ≠ 0 := fun heq ↦ by
  rw [eta, mul_eq_zero] at heq
  rcases heq with heq | heq
  exact Complex.exp_ne_zero _ heq
  have hsummable : Summable (fun n : ℕ ↦ ‖(1 - cexp (2 * π * Complex.I * ↑(n + 1) * z)) - 1‖) := by
    simp_rw [show ∀ n : ℕ, ‖(1 - cexp (2 * π * Complex.I * ↑(n + 1) * z)) - 1‖ 
        = (rexp (-2 * π * z.im))^(n + 1) by
      intro n
      simp only [Nat.cast_add, Nat.cast_one, sub_sub_cancel_left, norm_neg, norm_exp, mul_re,
        re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im,
        zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re, one_re, add_im,
        natCast_im, one_im, coe_re, zero_add, coe_im, zero_sub, neg_mul, ← Real.exp_nat_mul,
        mul_neg, exp_eq_exp, neg_inj]
      ring 
    ]
    refine (summable_nat_add_iff 1).mpr <| summable_geometric_of_lt_one (exp_nonneg _) ?_
    refine exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos ?_ z.property
    exact mul_neg_of_neg_of_pos (by norm_num) pi_pos
  refine product_nonzero_of_terms_nonzero_of_summable_norm (α := ℂ)
    (multipliableLocallyUniformlyOn_eta_product.multipliable z.property) hsummable ?_ heq
  intro n heq
  apply Lean.Grind.CommRing.sub_eq_zero_iff.mp at heq
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (Eq.symm heq)
  rw [mul_comm (k : ℂ) _, mul_assoc] at hk
  apply (mul_right_inj' (by norm_num [pi_ne_zero])).mp at hk
  apply_fun Complex.im at hk
  simp only [Nat.cast_add, Nat.cast_one, mul_im, add_re, natCast_re, one_re, add_im, natCast_im,
    one_im, add_zero, zero_mul, intCast_im, mul_eq_zero] at hk
  rcases hk with hk | hk
  exact Nat.cast_add_one_ne_zero n hk
  exact ne_of_gt z.property hk


