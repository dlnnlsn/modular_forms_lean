import Mathlib

open Complex ModularForm SlashInvariantForm CongruenceSubgroup Matrix MatrixGroups UpperHalfPlane

def levelOne_rank (k: ℤ): ℕ :=
  if k < 0 then 0
  else if k % 2 = 1 then 0
  else if k % 12 = 2 then Int.toNat (k/12)
  else Int.toNat (k/12) + 1

lemma levelOne_rank_formula_of_add_twelve (k: ℤ) (hk: k ≥ 0) (h_even: Even k): levelOne_rank (k + 12) = levelOne_rank k + 1 := by
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

lemma levelOne_rank_of_add_twelve (k: ℤ) (hk: k ≥ -9) (h_even: Even k):
  Module.rank ℂ (ModularForm Γ(1) (k + 12)) = Module.rank ℂ (ModularForm Γ(1) k) + 1 := by
  sorry

lemma levelOne_rank_one_of_even_weight_of_lt_twelve (k: ℤ) (h_nonneg: k ≥ 3) (h_upper: k < 12) (h_even: Even k):
  Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  let m := k - 12; have hm: k = m + 12 := by ring
  rw [hm] 
  rw [levelOne_rank_of_add_twelve m (by linarith)]
  rw [levelOne_neg_weight_rank_zero (by linarith)]
  exact zero_add 1
  apply Int.even_iff.mpr
  unfold m
  have: k % 2 = 0 := Int.even_iff.mp h_even
  omega

theorem levelOne_weight_k_rank' (k: ℤ): Module.rank ℂ (ModularForm Γ(1) k) = levelOne_rank k := by
  match k with
  | Int.negSucc _ => simp [levelOne_rank, ModularForm.levelOne_neg_weight_rank_zero]
  | Int.ofNat n =>
    induction' n using Nat.strong_induction_on with n hn
    match n with
    | 0 => exact ModularForm.levelOne_weight_zero_rank_one
    | 1 => exact levelOne_rank_zero_of_odd_weight (by decide)
    | 2 => /- very -/ sorry
    | n + 3 =>
      let k := Int.ofNat (n + 3); refold_let k
      by_cases h_odd: Odd k
      simp [levelOne_rank_zero_of_odd_weight h_odd, levelOne_rank, Int.odd_iff.mp h_odd]
      have h_even: Even k := Int.not_odd_iff_even.mp h_odd
      by_cases h_upper: k < 12
      have h_positive: k ≥ 3 := Int.ofNat_le_ofNat_of_le <| Nat.le_add_left 3 n
      rw [levelOne_rank_one_of_even_weight_of_lt_twelve k h_positive h_upper h_even]
      have h_mod: k % 12 ≠ 2 := by omega
      replace h_positive: ¬(k < 0) := Int.not_lt.mpr <| Int.zero_le_ofNat _
      simp [levelOne_rank, h_positive, h_odd, Int.even_iff.mp h_even, h_mod]
      norm_cast; omega
      let m := Int.natAbs (k - 12)
      have hm: k = m + 12 := by omega
      rw [hm, levelOne_rank_of_add_twelve, levelOne_rank_formula_of_add_twelve]
      rw [show (m: ℤ) = Int.ofNat m from rfl, hn m]
      norm_cast
      unfold m
      have: k - 12 ≥ 0 := by omega
      have: (k - 12).natAbs = k - 12 := Int.natAbs_of_nonneg this
      apply Int.ofNat_lt.mp
      rw [this]
      unfold k
      rw [show Int.ofNat (n + 3) = ((n + 3): ℤ) from rfl]
      omega
      exact Int.ofNat_zero_le m
      have := Int.even_iff.mp h_even
      apply Int.even_iff.mpr (by omega)
      linarith
      have := Int.even_iff.mp h_even
      apply Int.even_iff.mpr (by omega)
