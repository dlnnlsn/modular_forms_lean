import Mathlib

open Complex ModularForm SlashInvariantForm CongruenceSubgroup Matrix MatrixGroups UpperHalfPlane

def levelOne_rank (k: ℤ): ℕ :=
  if k < 0 then 0
  else if k % 2 = 1 then 0
  else if k % 12 = 2 then Int.toNat (k/12)
  else Int.toNat (k/12) + 1

lemma levelOne_rank_of_add_twelve (k: ℤ) (hk: k ≥ 0) (h_even: Even k): levelOne_rank (k + 12) = levelOne_rank k + 1 := by
  replace h_even: k % 2 = 0 := Int.even_iff.mp h_even
  have h_k_plus_twelve_even: (k + 12) % 2 = 0 := by omega
  simp [levelOne_rank, Int.not_lt.mpr hk, show ¬(k + 12 < 0) from by linarith, h_even, h_k_plus_twelve_even]
  by_cases h_k_mod: k % 12 = 2 <;> simp [h_k_mod] <;> omega

lemma levelOne_eq_zero_of_odd_weight (k: ℤ) (h_odd: Odd k) (f: SlashInvariantForm Γ(1) k): f = 0 := by
  let M : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by norm_num [Matrix.det_fin_two_of]⟩
  ext z
  have := f.slash_action_eq' M (mem_Gamma_one M)
  have f_of_M_z := (slash_action_eq'_iff k f M z).mp (congrFun this z)
  simp [specialLinearGroup_apply, M, Odd.neg_one_zpow h_odd] at f_of_M_z
  exact CharZero.eq_neg_self_iff.mp f_of_M_z

lemma levelOne_rank_zero_of_odd_weight {k: ℤ} (h_odd: Odd k): Module.rank ℂ (ModularForm Γ(1) k) = 0 := by
  apply rank_eq_zero_iff.mpr
  intro f; use 1
  constructor
  exact one_ne_zero
  rw [one_smul]
  ext z
  rw [show f z = f.toSlashInvariantForm z from by rfl]
  rw [levelOne_eq_zero_of_odd_weight k h_odd f.toSlashInvariantForm]
  rfl

theorem levelOne_weight_k_rank (k: ℤ): Module.rank ℂ (ModularForm Γ(1) k) = levelOne_rank k := by
  by_cases h_neg: k < 0
  simp [ModularForm.levelOne_neg_weight_rank_zero h_neg, levelOne_rank, h_neg]
  lift k to ℕ using (le_of_not_gt h_neg)
  induction' k using Nat.strong_induction_on with k hk
  match k with
  | 0 => exact ModularForm.levelOne_weight_zero_rank_one
  | 1 => exact levelOne_rank_zero_of_odd_weight (by decide)
  | 2 => /- very -/ sorry
  | k + 3 =>
    by_cases h_odd: Odd (k + 3)
    rw [levelOne_rank_zero_of_odd_weight <| (Int.odd_coe_nat _).mpr h_odd]
    replace h_odd: ((k: ℤ) + 3) % 2 = 1 := by norm_cast; apply Nat.odd_iff.mp h_odd
    simp [levelOne_rank, h_neg, h_odd]
    sorry
