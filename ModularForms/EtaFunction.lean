import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import ModularForms.Analysis

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

