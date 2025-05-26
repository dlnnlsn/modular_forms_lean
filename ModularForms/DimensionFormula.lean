import Mathlib.Algebra.Field.Power
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import ModularForms.CuspFormSubspace
import ModularForms.EisensteinVanishingBehaviour
import ModularForms.EisensteinEvenWeight


--import ModularForms.Modular_Forms --temporary \ModularForms\Modular_Forms.lean

open Complex ModularForm SlashInvariantForm CongruenceSubgroup Matrix MatrixGroups UpperHalfPlane
open scoped DirectSum

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

--theorem levelOne_rank_of_CuspFormSubspace_add_one {k : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
--Module.rank ℂ (ModularForm Γ(1) k) = Module.rank ℂ (Modular_Forms.CuspForm_Subspace Γ(1) k) + 1 := by
--  rw [← rank_ModulaForm_equiv_prod hk a, rank_prod',add_comm, rank_eisensteinSubspace_one]
--  rfl
instance modformascuspform {k : ℤ}{f : ModularForm Γ(1) k} (vanishatcusp : (∀ (A : SL(2, ℤ)),
IsZeroAtImInfty ((f : ModularForm Γ(1) k) ∣[k] A))) : CuspForm Γ(1) k where
  toFun := f.toSlashInvariantForm
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  zero_at_infty' := vanishatcusp

lemma subspacelemma {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+))
(x : Subspace ℂ  (ModularForm Γ(1) k)) :
x ≤ (Submodule.span ℂ {eisensteinSeries_MF hk a}) ↔
∀ f ∈ x, ∃ c : ℂ, f = c • (eisensteinSeries_MF hk a) := sorry

lemma subspacelemma2   {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+))
(x : Subspace ℂ  (ModularForm Γ(1) k)) :
x ≤ CuspForm_Subspace Γ(1) k ↔
∀ f ∈ x, ∀ (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A) := by
  constructor
  · intro h f h₁
    have h₁ : f ∈ CuspForm_Subspace Γ(1) k := by apply h ; apply h₁
    have h₂ : ∃ g : (CuspForm Γ(1) k), ((isom Γ(1) k).toFun g) = f := by
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
      exact h₁
    obtain ⟨g, hg⟩ := h₂
    rw [← hg]
    convert g.zero_at_infty'
  · intro h f h₁
    have h₂ : f ∈ CuspForm_Subspace Γ(1) k := by
        have h₂₁ : ∃ g : (CuspForm Γ(1) k), ((isom Γ(1) k).toFun g).1 = f := by
          use modformascuspform (h f h₁)
          rfl
        apply h₂₁
    apply h₂

lemma EisensteinSeries_in_EisensteinSubspace {k : ℤ}(c : ℂ) (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
c • (eisensteinSeries_MF hk a) ∈ Submodule.span ℂ {eisensteinSeries_MF hk a} := by
simp_all only [PNat.val_ofNat]
apply SMulMemClass.smul_mem
apply SetLike.mem_of_subset
· apply Submodule.subset_span
· simp_all only [Set.mem_singleton_iff]

lemma eisensteinSubspace_vanishing_is_zero  {k : ℤ}(hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+))
(f : ModularForm Γ(1) k) (finEis : f ∈  Submodule.span ℂ {eisensteinSeries_MF hk a})
(fvanishes : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((f : ModularForm Γ(1) k) ∣[k] A)) : f = 0 := sorry

theorem eisensteinSeries_comp_CuspForm {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
IsCompl (Submodule.span ℂ {eisensteinSeries_MF (by linarith) a}) (CuspForm_Subspace Γ(1) k) := by
  apply isCompl_iff.mpr
  constructor
  · unfold Disjoint
    intro x h₁ h₂
    rw [subspacelemma hk a] at h₁
    rw [subspacelemma2 hk a] at h₂
    intro f h₄
    simp
    have h₅ : ∃ c : ℂ, f = c • (eisensteinSeries_MF hk a) := by apply h₁ f; apply h₄
    rcases h₅ with ⟨c, h₅⟩
    have h₆ : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A) := by apply h₂ f; apply h₄
    rw [h₅] at h₆
    rw [h₅]
    apply eisensteinSubspace_vanishing_is_zero hk a
    apply EisensteinSeries_in_EisensteinSubspace c hk a
    apply h₆
  · unfold Codisjoint
    intro x h₁ h₂ f h₃
    by_cases h : (∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((f : ModularForm Γ(1) k) ∣[k] A))
    · have h₇ : f ∈ CuspForm_Subspace Γ(1) k := by
        have h₇₁ : ∃ g : (CuspForm Γ(1) k), ((isom Γ(1) k).toFun g).1 = f := by
          use modformascuspform h
          rfl
        apply h₇₁
      simp_all only [PNat.val_ofNat, Submodule.span_singleton_le_iff_mem, Submodule.mem_top, SL_slash]
      apply h₂
      simp_all only
    · have h₇ : f ∈ (Submodule.span ℂ {eisensteinSeries_MF hk a}) := by
        sorry --This is important
      simp_all only [PNat.val_ofNat, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_top, SL_slash, not_forall]
      obtain ⟨w, h⟩ := h
      apply h₇
      simp_all only [Set.singleton_subset_iff, SetLike.mem_coe,
      Set.mem_setOf_eq, Set.mem_range]
      apply Exists.intro
      · ext x_1 : 1
        simp_all only [Set.mem_iInter, SetLike.mem_coe]
        apply Iff.intro
        intro a_1
        on_goal 2 => {
          intro a_1 «i»
          exact a_1
        }
        simp_all only [forall_const]

instance idℂ : ℂ ≃* ℂ where
  toFun := fun z ↦ z
  invFun := fun z ↦ z
  left_inv := by tauto
  right_inv := by tauto
  map_mul' := by tauto

lemma idinj : Function.Bijective idℂ := by apply idℂ.bijective
#check MulEquiv.refl

--« ;) »
lemma rank_ModulaForm_equiv_prod {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
Module.rank ℂ ((Submodule.span ℂ {eisensteinSeries_MF hk a}) × (CuspForm_Subspace Γ((1 : ℕ+)) k))
= Module.rank ℂ (ModularForm Γ(↑1) k) := by
  apply rank_eq_of_equiv_equiv idℂ (LinearEquiv.toAddEquiv (Submodule.prodEquivOfIsCompl
  (Submodule.span ℂ {(eisensteinSeries_MF hk a : (ModularForm Γ((1 : ℕ+)) k))})
  (CuspForm_Subspace Γ((1 : ℕ+)) k)  (eisensteinSeries_comp_CuspForm hk a) ) )
  apply idinj
  intro r m
  simp [idℂ]

lemma rank_eisensteinSubspace_one {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
 Module.rank ℂ ↥(Submodule.span ℂ {eisensteinSeries_MF hk a}) = 1 := by
  rw [rank_submodule_eq_one_iff]
  use eisensteinSeries_MF hk a
  constructor
  · unfold Submodule.span
    simp
  constructor
  · apply Eisenstein_series_not_zero
  · tauto

theorem dimen {k : ℤ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
Module.rank ℂ (ModularForm Γ(1) k) = Module.rank ℂ (CuspForm_Subspace Γ(1) k) + 1 := by
  rw [← rank_ModulaForm_equiv_prod hk a, rank_prod',add_comm, rank_eisensteinSubspace_one]
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


--#min_imports
