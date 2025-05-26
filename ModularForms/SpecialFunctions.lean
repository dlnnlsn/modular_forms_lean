import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import ModularForms.Analysis



open Real Complex UpperHalfPlane Filter Function Topology



theorem multipliableLocallyUniformlyOn_euler_sinc_prod :
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

theorem tendsto_locally_uniformly_euler_sin_prod :
    TendstoLocallyUniformlyOn (fun (s : Finset ℕ) (z : ℂ) ↦ π * z * ∏ k ∈ s, (1 - z^2 / (k + 1)^2))
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

lemma eventually_ne_atTop {α : Type*} [RCLike α] (z : α) : ∀ᶠ n : ℕ in atTop, (n : α) ≠ z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn heq
  apply congrArg norm at heq
  rw [RCLike.norm_natCast] at heq
  apply (Nat.cast_le (α := ℝ)).mpr at hn
  linarith

lemma cotangent_terms_isBigO (z : ℂ) : (fun n : ℕ ↦ 1/(z + (n + 1)) + 1/(z - (n + 1)))
    =O[atTop] (fun n : ℕ ↦ 1/((n : ℝ) + 1)^2) := by
  have h_eventually_plus_nonzero : ∀ᶠ n : ℕ in atTop, (z + (n + 1)) ≠ 0 := by
    filter_upwards [eventually_ne_atTop (-(z + 1))] with n hn heq
    rw [←add_assoc, add_comm z, add_assoc] at heq
    exact hn <|  eq_neg_of_add_eq_zero_left heq
  have h_eventually_minus_nonzero : ∀ᶠ n : ℕ in atTop, (z - (n + 1)) ≠ 0 := by
    filter_upwards [eventually_ne_atTop (z - 1)] with n hn heq
    apply Lean.Grind.CommRing.sub_eq_zero_iff.mp at heq
    exact hn <| Eq.symm <| Lean.Grind.CommRing.sub_eq_iff.mpr heq
  have h_eventually_prod_nonzero : ∀ᶠ n : ℕ in atTop, (n + 1)^2 - z^2 ≠ 0 := by
    filter_upwards [h_eventually_plus_nonzero, h_eventually_minus_nonzero] with n hnp hnm heq
    replace heq : z^2 - (n + 1)^2 = 0 := by apply zero_eq_neg.mp ; rw [←heq] ; ring
    rw [sq_sub_sq] at heq
    rcases mul_eq_zero.mp heq <;> trivial
  have h_eventually_eq : ∀ᶠ n : ℕ in atTop,
      1/(z + (n + 1)) + 1/(z - (n + 1)) = (-2 * z) * 1 / ((n + 1)^2 - z^2) := by
    filter_upwards [h_eventually_plus_nonzero, h_eventually_minus_nonzero,
                    h_eventually_prod_nonzero] with _ _ _ _
    field_simp
    ring
  refine Filter.EventuallyEq.trans_isBigO h_eventually_eq ?_
  refine Asymptotics.IsBigO.const_mul_left ?_ _
  rw [Asymptotics.IsBigO_def]
  use (4 : ℝ)/3
  rw [Asymptotics.isBigOWith_iff]
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * ‖z‖)
  filter_upwards [h_eventually_prod_nonzero, eventually_ge_atTop N] with n hprod hn
  apply (Nat.cast_le (α := ℝ)).mpr at hn
  apply (mul_le_mul_iff_of_pos_left (show ‖(n + 1)^2 - z^2‖ > 0 by positivity)).mp
  apply (mul_le_mul_iff_of_pos_left (show 3 * ((n : ℝ) + 1)^2 / 4 > 0 by positivity)).mp
  have := calc
    ‖(n + 1)^2 - z^2‖ ≥ ‖((n : ℂ) + 1)^2‖ - ‖z^2‖ := ge_iff_le.mpr <| norm_sub_norm_le _ _
    _ = ((n : ℝ) + 1)^2 - ‖z^2‖ := by norm_cast
    _ ≥ ((n : ℝ) + 1)^2 - ((n : ℝ) + 1)^2 / 4 := by
      apply ge_iff_le.mpr
      apply sub_le_sub_left
      rw [norm_pow]
      convert (sq_le_sq₀ ?_ ?_).mpr (show ‖z‖ ≤ ((n : ℝ) + 1) / 2 by linarith)
      ring
      all_goals positivity
    _ = (3 : ℝ) * (n + 1)^2 / 4 := by ring
  exact le_trans (le_of_eq_of_le (by field_simp; try ring) this)
                 (le_of_eq       (by field_simp; try ring))

theorem cotangent_expansion (z : ℂ) (h : ∀ n : ℤ, z ≠ n) :
    π * cot (π * z) = 1/z + ∑' k : ℕ, (1/(z + (k + 1)) + 1/(z - (k + 1))) := by
  have h_top_open : IsOpen (⊤ : Set ℂ) := by simp
  let z_wrapped : (⊤ : Set ℂ) := { val := z, property := by trivial }
  have h_differentiable (n : ℕ) : Differentiable ℂ (fun (z : ℂ) ↦ 1 - z^2 / (n + 1)^2) :=
    Differentiable.const_sub (Differentiable.div_const (differentiable_pow _) _) _
  have h_prod_differentiable (s : Finset ℕ) : Differentiable ℂ
      (fun z: ℂ ↦ ∏ k ∈ s, (1 - z^2 / (k + 1)^2)) :=
    Differentiable.finset_prod fun n _ ↦ h_differentiable n
  have h_prod_eventually_differentiable : ∀ᶠ (s : Finset ℕ) in atTop, DifferentiableOn ℂ
      (fun z: ℂ ↦ π * z * ∏ k ∈ s, (1 - z^2 / (k + 1)^2)) ⊤ :=  by
    filter_upwards with s
    simp_rw [mul_assoc]
    apply DifferentiableOn.const_mul
    exact DifferentiableOn.mul differentiableOn_id (h_prod_differentiable s).differentiableOn
  have h_sin_nonzero : Complex.sin (π * z) ≠ 0 := by
    rw [mul_comm]
    refine Complex.sin_ne_zero_iff.mpr fun n heq ↦ ?_
    apply mul_right_cancel₀ (ofReal_ne_zero.mpr pi_ne_zero) at heq
    exact h n heq
  have hlog_deriv := Complex.logDeriv_tendsto _ _ h_top_open
    z_wrapped tendsto_locally_uniformly_euler_sin_prod
    h_prod_eventually_differentiable h_sin_nonzero
  rw [show logDeriv (fun z ↦ Complex.sin (π * z)) z = π * Complex.cot (π * z) by
    have hlog_deriv := logDeriv_comp (x := z) (Complex.differentiableAt_sin)
      ((differentiableAt_const (π : ℂ)).mul differentiableAt_id)
    simp only [id_eq, Complex.logDeriv_sin] at hlog_deriv
    rw [mul_comm] at hlog_deriv
    rw [show deriv (fun y : ℂ ↦ π * y) z = (π : ℂ) by
      conv_rhs => rw [←mul_one π]
      apply HasDerivAt.deriv
      rw [ofReal_mul, ofReal_one]
      apply HasDerivAt.const_mul
      exact hasDerivAt_id z
    ] at hlog_deriv
    exact hlog_deriv
  ] at hlog_deriv
  refine tendsto_nhds_unique hlog_deriv ?_
  have hprod_terms_differentiable (k : ℕ) :
      HasDerivAt (fun z : ℂ ↦ 1 - z^2 / (k + 1)^2) (-(2 * z / (k + 1)^2)) z := by
    apply HasDerivAt.const_sub
    apply HasDerivAt.div_const
    convert hasDerivAt_pow 2 z
    rw [Nat.add_one_sub_one, pow_one]
  have hadd_nonzero (k : ℕ) : z + (k + 1) ≠ 0 := fun heq ↦ by
    apply eq_neg_of_add_eq_zero_left at heq
    have hneq := h (-(k + 1))
    push_cast at hneq
    exact hneq heq
  have hsub_nonzero (k : ℕ) : z - (k + 1) ≠ 0 := fun heq ↦ by
    apply Lean.Grind.CommRing.sub_eq_zero_iff.mp at heq
    have hneq := h (k + 1)
    push_cast at hneq
    exact hneq heq
  have hprod_terms_nonzero (k : ℕ) : 1 - z^2 / (k + 1)^2 ≠ 0 := fun heq ↦ by
    apply congrArg (fun z : ℂ ↦ (k + 1)^2 * z) at heq
    field_simp [Nat.cast_add_one_ne_zero k] at heq
    rw [sq_sub_sq] at heq
    rcases mul_eq_zero.mp heq with heq | heq
    apply hadd_nonzero k
    rwa [add_comm]
    apply hsub_nonzero k
    apply congrArg (-·) at heq
    rw [←Lean.Grind.CommRing.neg_zero, ←heq]
    ring
  suffices hlog_deriv : ∀ s : Finset ℕ,
      logDeriv (fun z : ℂ ↦ π * z * ∏ k ∈ s, (1 - z^2 / (k + 1)^2)) z_wrapped =
      1/z + ∑ k ∈ s, (1 / (z + (k + 1)) + 1 / (z - (k + 1))) by
    simp_rw [hlog_deriv]
    apply Tendsto.const_add
    apply Summable.hasSum
    refine summable_of_isBigO_nat ?_ (cotangent_terms_isBigO z)
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -2 < -1 by norm_num))
    convert this using 2 with n
    rw [rpow_neg (by positivity), inv_eq_one_div]
    field_simp
  intro s
  simp_rw [mul_assoc]
  rw [logDeriv_const_mul _ _ (ofReal_ne_zero.mpr pi_ne_zero)]
  rw [logDeriv_mul z]
  simp_rw [←Function.id_def]
  rw [logDeriv_id]
  apply congrArg
  rw [logDeriv_prod]
  suffices hlog_deriv : ∀ k : ℕ, logDeriv (fun z : ℂ ↦ 1 - z^2 / (k + 1)^2) z
      = 1/(z + (k + 1)) + 1/(z - (k + 1)) by simp_rw [hlog_deriv]
  intro k
  simp only [logDeriv, Pi.div_apply, (hprod_terms_differentiable k).deriv, one_div]
  apply (div_eq_iff (hprod_terms_nonzero k)).mpr
  field_simp [hadd_nonzero k, hsub_nonzero, Nat.cast_add_one_ne_zero k]
  ring
  exact fun k _ ↦ hprod_terms_nonzero k
  exact fun k _ ↦ (hprod_terms_differentiable k).differentiableAt
  convert h 0
  exact Eq.symm Lean.Grind.CommRing.intCast_zero
  apply Finset.prod_eq_zero_iff.not.mpr
  push_neg
  exact fun k _ ↦ hprod_terms_nonzero k
  exact differentiableAt_id
  exact DifferentiableAt.finset_prod fun k _ ↦ (hprod_terms_differentiable k).differentiableAt

theorem cotangent_expansion_H (z: ℍ): π * cot (π * z) = 1/z + ∑' k: ℕ, (1/((z: ℂ) + (k + 1)) + 1/(z - (k + 1))) := by
  have h_non_int : ∀ n : ℤ, (z : ℂ) ≠ n := fun n heq ↦ by
    apply congrArg Complex.im at heq
    rw [coe_im, intCast_im] at heq
    exact (lt_self_iff_false 0).mp <| lt_of_lt_of_eq (im_pos z) heq
  exact cotangent_expansion z h_non_int

local notation "i" => Complex.I
lemma cotagent_as_exp {z : ℍ}: (π * cot (π * z) - 1 / (z : ℂ)) =
π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by rw [Complex.cot_pi_eq_exp_ratio] ; field_simp ; ring_nf ; sorry

lemma cotagent_as_exp1 {z : ℍ} :  π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) =
- π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by
  calc
    π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) =
    π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) * cexp (π * i * z) / cexp (π * i * z) := by simp
    _ = π * i * (cexp (π * i * z) * cexp (π * i * z)  + cexp (- π * i * z)* cexp (π * i * z) ) / (cexp (π * i * z) * cexp (π * i * z) - cexp (-π * i * z) * cexp (π * i * z)) := by
      /- not-/ sorry
    _ = π * i * (cexp (2 * π * i * z)  + 1 ) / (cexp (2* π * i * z) - 1) := by
        simp_rw [← Complex.exp_add]
        simp only [neg_mul, neg_add_cancel, Complex.exp_zero]
        ring_nf
    _ = π * i * (cexp (2 * π * i * z) + cexp (2 * π * i * z) - cexp (2 * π * i * z)  + 1 ) / (cexp (2* π * i * z) - 1) := by simp only [add_sub_cancel_right]
    _ = π * i * (2 * cexp (2 * π * i * z) -  (cexp (2 * π * i * z) - 1) ) / (cexp (2* π * i * z) - 1) := by sorry --obvious
    _ = (2 * π * i *cexp (2 * π * i * z) - π * i * (cexp (2 * π * i * z) - 1)) / (cexp (2* π * i * z) - 1) := by ring_nf
    _ = 2 * π * i *cexp (2 * π * i * z) / (cexp (2* π * i * z) - 1) -  π * i := by sorry
    _ = - 2 * π * i *cexp (2 * π * i * z) / (1-cexp (2* π * i * z) ) -  π * i := by sorry -- I love cexp
    _ = - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by ring_nf

lemma cexp_series_HasSum (z : ℍ) : HasSum (fun n : ℕ => cexp (2 * π * i *z)^n) (1 - cexp (2 * π * i *z))⁻¹ := by
  have cexp_norm : ∀ τ: ℍ, ‖cexp (2 * π * i *τ)‖ < 1 := by
    intro τ
    have cexp_isreal : ‖cexp (2 * π * i *τ)‖ = Real.exp (-2 * π * im (τ : ℂ) :) := by
      simp only [norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
      mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, zero_sub,
      neg_mul]
    rw [cexp_isreal]
    simp_all only [neg_mul, coe_im, exp_lt_one_iff, Left.neg_neg_iff, gt_iff_lt]
    have τim : τ.im > 0 := τ.2
    have : 2 * π > 0 := by simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left] ; apply Real.pi_pos
    simp_all only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
  apply hasSum_geometric_of_norm_lt_one (cexp_norm z)

lemma cexp_eq_sum (z : ℍ) : cexp (2 * π * i  *z) / ( 1 - cexp (2 * π * i *z)) = ∑' n : ℕ, cexp (2 * π * i * (n + 1) * z) := by
  calc
    cexp (2 * π * i  *z) / ( 1 - cexp (2 * π * i *z)) = cexp (2 * π * i  *z) * ( 1 - cexp (2 * π * i *z))⁻¹ := by ring_nf
    _ =  cexp (2 * π * i  *z) * ∑' n : ℕ, cexp (2 * π * i *z)^n := by rw [← HasSum.tsum_eq (cexp_series_HasSum z) ]
    _ = cexp (2 * π * i  *z) • ∑' n : ℕ, cexp (2 * π * i *z)^n := by rw [← smul_eq_mul]
    _ = ∑' n : ℕ, cexp (2 * π * i  *z) • cexp (2 * π * i *z)^ n := by rw [Summable.tsum_const_smul] ; use (1 - cexp (2 * π * i *z))⁻¹ ; convert (cexp_series_HasSum z)
    _ = ∑' n : ℕ, cexp (2 * π * i  *z) * cexp (2 * π * i *z)^ n := by simp_rw [smul_eq_mul]
    _ = ∑' n : ℕ,  cexp (2 * π * i *z)^ (n + 1) := by ring_nf
    _ = ∑' n : ℕ,  cexp (2 * π * i *z)^ (n + 1 : ℤ) := by norm_cast
    _ = ∑' n : ℕ,  cexp (2 * π * i * (n + 1 ) * z) := by simp_rw [← Complex.exp_int_mul (2 * π * i * z) _] ; norm_cast ; congr ; ext x ; ring_nf

lemma cotagent_as_exp2 {z : ℍ} : - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) =
- π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by
  have : - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) = - π * i - 2 * π * i * (cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) )) := by ring_nf
  rw [this]
  rw [cexp_eq_sum z]

lemma cotangent_dirichlet_expansion''  (z : ℍ) : (π * cot (π * z) - 1 / (z : ℂ))
= - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by
  calc
    (π * cot (π * z) - 1 / (z : ℂ)) = π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by apply cotagent_as_exp
    _  = - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by apply cotagent_as_exp1
    _  = - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by apply cotagent_as_exp2

theorem cotangent_dirichlet_expansion (z: ℍ): cot z = -Complex.I - 2 * π * Complex.I * ∑' d: ℕ, Complex.exp (2 * π * Complex.I * (d + 1) * z) := by
  sorry

theorem cotangent_dirichlet_expansion' (z: ℂ) (h: z.im > 0): cot z = -Complex.I - 2 * π * Complex.I * ∑' d: ℕ, Complex.exp (2 * π * Complex.I * (d + 1) * z) :=
  cotangent_dirichlet_expansion { val := z, property := h }

#min_imports
