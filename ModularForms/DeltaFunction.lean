import Mathlib.Algebra.Field.Power
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ModularForms.LevelOne
import ModularForms.EtaFunction

open Real Complex UpperHalfPlane Matrix MatrixGroups CongruenceSubgroup ModularForm SlashAction EisensteinSeries

noncomputable
def delta (z: ℍ): ℂ := (_root_.eta z)^24

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

lemma delta_slash_apply (γ: SL(2, ℤ)): delta ∣[(12: ℤ)] γ = delta := by
  suffices h_closure: ∀ γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T}, delta ∣[(12: ℤ)] γ = delta
  apply h_closure
  rw [SpecialLinearGroup.SL2Z_generators]
  trivial
  intro γ hγ
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
  slash_action_eq' A hA := by apply delta_slash_apply

noncomputable
def delta_CF: CuspForm Γ(1) 12 where
  toFun := delta_SIF.toFun
  slash_action_eq' := delta_SIF.slash_action_eq'
  holo' := sorry
  zero_at_infty' := sorry

noncomputable
def modular_form_of_div_delta_of_cusp_form {k: ℤ} (f: CuspForm Γ(1) k): ModularForm Γ(1) (k - 12) where
  toFun := λ z ↦ (f z) / (delta z)
  slash_action_eq' := sorry
  holo' := sorry
  bdd_at_infty' := sorry

def a: Fin 2 → ZMod (1: ℕ+) := λ _ ↦ 0
lemma delta_from_eisenstein: delta = (eisensteinSeries_SIF a 4)^3 - (eisensteinSeries_SIF a 6)^2 := by
  sorry

