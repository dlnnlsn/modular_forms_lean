import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

open EisensteinSeries CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function ModularFormClass
open scoped Real MatrixGroups CongruenceSubgroup

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)
variable {z : ℍ}

lemma Eisenstein_0th_coeff_one {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
PowerSeries.coeff ℂ 0 (qExpansion n (eisensteinSeries_MF hk a)) = 1 := sorry

lemma Eisenstein_series_ne_zero {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
 qExpansion n (eisensteinSeries_MF hk a) ≠ 0 := by
  intro h
  rw [← PowerSeries.forall_coeff_eq_zero] at h
  have h₁ : PowerSeries.coeff ℂ 0 (qExpansion n (eisensteinSeries_MF hk a)) = 1 := by exact Eisenstein_0th_coeff_one n hk a
  rw [h 0] at h₁
  have : 0 = (1:ℂ) → False := by simp --contradiction didn't work
  apply this ; apply h₁

instance CuspForm_is_Subspace {N : ℕ+}(hk : 3 ≤ k) (a : Fin 2 → ZMod ↑N): Submodule ℂ (ModularForm Γ(N) k) where
  carrier := sorry
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

--this is a product of types, so I don't know if this is strong enough
theorem ModularForms_decompose_CuspForms_Eisenstein {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod ↑N):
 ModularForm Γ(↑1) k = Prod (CuspForm_is_Subspace hk a) (vectorSpan ℂ {eisensteinSeries_MF hk a})  := sorry
