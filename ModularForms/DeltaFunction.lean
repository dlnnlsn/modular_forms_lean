import Mathlib.Algebra.Field.Power
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Topology.Defs.Filter
import ModularForms.EtaFunction

open Real UpperHalfPlane Matrix MatrixGroups CongruenceSubgroup ModularForm SlashAction 
     EisensteinSeries
open Complex hiding eta

noncomputable
def delta (z: ℍ): ℂ := (eta z)^24

theorem delta_product_formula (z : ℍ) : delta z =
    cexp (2 * π * Complex.I * z) * (∏' n : ℕ, (1 - cexp (2 * π * Complex.I * ↑(n + 1) * z)))^24 := by
  unfold delta eta
  rw [mul_pow, ←Complex.exp_nat_mul]
  ring_nf

theorem delta_theta_q_atImInfty : delta =Θ[atImInfty] (fun τ : ℍ ↦ rexp (-2 * π * τ.im)) := by
  convert eta_theta_atImInfty.pow 24
  rw [←Real.exp_nat_mul]
  ring_nf

theorem delta_nonzero_on_upperHalfPlane (z : ℍ) : delta z ≠ 0 := by sorry

lemma delta_slash_T: delta ∣[(12: ℤ)] ModularGroup.T = delta := by
  ext z
  rw [SL_slash, slash_def, slash, ModularGroup.det_coe, ofReal_one, _root_.one_zpow, mul_one,
      ←ModularGroup.sl_moeb, delta, eta_of_smul_T, mul_pow, ←Complex.exp_nat_mul,
      Complex.exp_eq_one_iff.mpr, one_mul,
      _root_.zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| z.denom_ne_zero _),
      denom, ModularGroup.T
  ]
  unfold delta
  simp
  use 1; ring

lemma delta_slash_S: delta ∣[(12: ℤ)] ModularGroup.S = delta := by
  ext z
  rw [SL_slash, slash_def, slash, ModularGroup.det_coe, ofReal_one, _root_.one_zpow, mul_one,
      _root_.zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| z.denom_ne_zero _),
      delta, ←ModularGroup.sl_moeb, eta_of_smul_S, mul_pow, ←cpow_nat_mul,
  ]
  norm_num
  rw [Even.neg_pow (by decide), mul_pow, show Complex.I^12 = (Complex.I^2)^6 from by ring]
  norm_num; rw [mul_comm]; rfl

lemma delta_slash_apply (γ : SL(2, ℤ)) : delta ∣[(12: ℤ)] γ = delta := by
  have hγ: γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction' hγ using Subgroup.closure_induction with γ hγ σ τ hσ_elem hτ_elem hσ hτ γ hγ_elem hγ
  rcases hγ with hS | hT
  rw [hS]; exact delta_slash_S
  rw [hT]; exact delta_slash_T
  exact slash_one 12 delta
  rw [slash_mul, hσ, hτ]
  rw [←hγ, ←slash_mul, mul_inv_cancel, slash_one, hγ]

noncomputable
def delta_SIF: SlashInvariantForm Γ(1) 12 where
  toFun := delta
  slash_action_eq' A _ := delta_slash_apply A

noncomputable
def delta_CF: CuspForm Γ(1) 12 where
  toFun := delta_SIF.toFun
  slash_action_eq' := delta_SIF.slash_action_eq'
  holo' := by
    intro z
    have : DifferentiableAt ℂ (delta ∘ UpperHalfPlane.ofComplex) z.val := by
      unfold delta
      apply DifferentiableAt.pow
      apply DifferentiableOn.differentiableAt eta_differentiableOn_upperHalfPlane
      apply IsOpen.mem_nhds 
      exact isOpen_lt continuous_const continuous_im
      exact z.property
    have := MDifferentiableAt.comp z (DifferentiableAt.mdifferentiableAt this) z.mdifferentiable_coe
    rwa [show (delta ∘ UpperHalfPlane.ofComplex) ∘ Subtype.val = delta by
      exact funext fun _ ↦ comp_ofComplex _ _
    ] at this
  zero_at_infty' := fun A ↦ by
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp delta_theta_q_atImInfty.isBigO
    obtain ⟨B, hB⟩ := (UpperHalfPlane.atImInfty_mem _).mp hc
    refine isZeroAtImInfty_iff.mpr fun ε εpos ↦ ?_
    have hc_pos : 0 < c := by
      let z : ℍ := {
        val := ⟨0, (max B 1)⟩
        property := by simp only [lt_sup_iff, zero_lt_one, or_true]
      }
      have := hB z (le_max_left B 1)
      simp only [neg_mul, norm_eq_abs, Real.abs_exp, Set.mem_setOf_eq] at this
      nlinarith [norm_pos_iff.mpr (delta_nonzero_on_upperHalfPlane z),
                 exp_pos (-(2 * π * z.im))]
    obtain ⟨R, hR⟩ := Set.mem_range.mp (show ε/c ∈ Set.range rexp by
      rw [Real.range_exp, Set.mem_Ioi]
      positivity
    )
    use max B (-R / (2 * π))
    intro τ hτ
    rw [show ⇑delta_SIF = delta by rfl, delta_slash_apply A]
    calc
      ‖delta τ‖ ≤ c * ‖rexp (-2 * π * τ.im)‖ := hB τ (le_of_max_le_left hτ)
      _ = c * rexp (-2 * π * τ.im) := by
        rw [Real.norm_eq_abs, Real.abs_exp]
      _ ≤ c * rexp R := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hc_pos)
        refine exp_le_exp_of_le ?_
        have := le_of_max_le_right hτ
        apply (mul_inv_le_iff₀ (show 0 < 2 * π by positivity)).mp at this
        linarith
      _ = ε := by
        rw [hR]
        field_simp

theorem slash_action_div_delta {m : ℤ} (f : SlashInvariantForm Γ(1) m) :
    ∀ γ ∈ Γ(1), (f.toFun / delta) ∣[m - 12] γ = f.toFun / delta := fun γ hγ ↦ by
  ext z
  rw [SL_slash, slash_def, slash, ModularGroup.det_coe, ofReal_one, one_zpow, mul_one]
  have h_sif_smul {m: ℤ} (f: SlashInvariantForm Γ(1) m) (γ: SL(2, ℤ)) (z: ℍ) :
      f.toFun ((γ: GL(2, ℝ)⁺) • z) = (denom γ z)^m * f.toFun z := by
    rw [show f.toFun z = (f.toFun ∣[m] γ) z from by rw [f.slash_action_eq' γ (mem_Gamma_one γ)]]
    rw [SL_slash, slash_def, slash, ModularGroup.det_coe, ofReal_one, one_zpow, mul_one,
        mul_comm, mul_assoc, zpow_neg_mul_zpow_self _ (z.denom_ne_zero _), mul_one]
  repeat rw [show (f.toFun / delta) _ = (f.toFun _) / (delta_SIF.toFun _) from rfl]
  repeat rw [h_sif_smul]
  rw [show delta_SIF.toFun = delta by rfl, neg_sub, zpow_sub₀ (denom_ne_zero γ z)] 
  field_simp [denom_ne_zero γ z, zpow_ne_zero m (denom_ne_zero γ z),
    zpow_ne_zero 12 (denom_ne_zero γ z), delta_nonzero_on_upperHalfPlane ((γ : ↥GL(2, ℝ)⁺) • z),
    delta_nonzero_on_upperHalfPlane z]
  ring

noncomputable
def modular_form_of_div_delta_of_cusp_form {k: ℤ} (f: CuspForm Γ(1) k) :
    ModularForm Γ(1) (k - 12) where
  toFun := f.toFun / delta
  slash_action_eq' := slash_action_div_delta f.toSlashInvariantForm
  holo' :=  by
    intro z
    suffices DifferentiableAt ℂ
        (f.toFun ∘ UpperHalfPlane.ofComplex / delta ∘ UpperHalfPlane.ofComplex) z.val by
      convert MDifferentiableAt.comp z (DifferentiableAt.mdifferentiableAt this)
        z.mdifferentiable_coe
      exact funext fun _ ↦ (comp_ofComplex _ _).symm
    apply DifferentiableAt.div
    exact UpperHalfPlane.mdifferentiableAt_iff.mp f.holo'.mdifferentiableAt
    exact UpperHalfPlane.mdifferentiableAt_iff.mp delta_CF.holo'.mdifferentiableAt
    simp [delta_nonzero_on_upperHalfPlane]
  bdd_at_infty' := fun A ↦ by
    simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
      SlashInvariantForm.coe_mk, SL_slash]
    show IsBoundedAtImInfty ((f.toFun / delta) ∣[k - 12] A)
    rw [slash_action_div_delta f.toSlashInvariantForm A (mem_Gamma_one A)]
    show (fun τ ↦ f τ/ delta τ) =O[atImInfty] 1
    simp_rw [div_eq_mul_inv]
    have hf_isBigO := CuspFormClass.exp_decay_atImInfty 1 f
    have hdelta_inv_isBigO := delta_theta_q_atImInfty.isBigO_symm.inv_rev (by aesop)
    convert hf_isBigO.mul hdelta_inv_isBigO 
    simp only [Pi.one_apply, neg_mul, Nat.cast_one, div_one, ne_eq, Real.exp_ne_zero,
      not_false_eq_true, mul_inv_cancel₀]

def a: Fin 2 → ZMod (1: ℕ+) := λ _ ↦ 0
lemma delta_from_eisenstein: delta = (eisensteinSeries_SIF a 4)^3 - (eisensteinSeries_SIF a 6)^2 := by
  sorry
