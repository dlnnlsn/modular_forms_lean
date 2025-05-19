import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic

open Asymptotics Filter 

def EventuallyBoundedBelow {α ι : Type*} [One α] [Norm α] (l : Filter ι) (f : ι → α) :=
  (fun _ : ι ↦ (1 : α)) =O[l] f

lemma isBigO_cast {α β : Type*} [RCLike α] [RCLike β] {l : Filter ℕ} :
    (fun n : ℕ ↦ (n : α)) =O[l] (fun n : ℕ ↦ (n : β)) := IsBigO.of_bound 1 (by simp)

lemma isBigO_succ_pow_pow {α : Type*} [RCLike α] {d : ℕ} :
    (fun n : ℕ ↦ ((n : α) + 1)^d) =O[atTop] (fun n : ℕ ↦ (n : α)^d) := by
  by_cases hd : d ≠ 0
  refine IsBigO.of_bound (2^d) ?_
  simp only [norm_pow, RCLike.norm_natCast]
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  norm_cast
  rw [←mul_pow]
  apply pow_le_pow <;> omega
  rw [ne_eq, Decidable.not_not] at hd
  simp only [hd, pow_zero, isBigO_const_const_iff, one_ne_zero, imp_self]

lemma eventuallyBoundedBelow_pow {d : ℕ} :
    EventuallyBoundedBelow atTop (fun n : ℕ ↦ ((n : ℝ) + 1)^d) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with n
  norm_cast
  rw [one_mul]
  exact one_le_pow₀ (Nat.le_add_left 1 n)

theorem isBigO_nf_plus_c {α β : Type*} [RCLike α] [RCLike β] {f : ℕ → α} {g : ℕ → β} {l : Filter ℕ}
    (c : α) (hfg: f =O[l] g) (hg : EventuallyBoundedBelow l g) :
    (fun n : ℕ ↦ (n : α) * f n + c) =O[l] (fun n : ℕ ↦ ((n : β) + 1) * g n) := by
  have c_big_o : (fun _ : ℕ ↦ c) =O[l] (fun n : ℕ ↦ ((n : β) + 1) * g n) := by
    rw [←mul_one c]
    unfold EventuallyBoundedBelow at hg
    refine IsBigO.mul ?_ (IsBigO.of_bound hg.bound.choose (by exact_mod_cast hg.bound.choose_spec))
    refine IsBigO.of_bound ‖c‖ ?_
    filter_upwards with n
    norm_cast; push_cast
    rw [mul_add, mul_one, le_add_iff_nonneg_left]
    positivity
  refine IsBigO.add (IsBigO.mul (IsBigO.of_bound 1 ?_) hfg) c_big_o
  filter_upwards with n
  norm_cast
  simp only [one_mul, le_add_iff_nonneg_right, zero_le]

theorem isBigO_nf_ng_plus_c {α β : Type*} [RCLike α] [RCLike β] {f : ℕ → α} {g : ℕ → β} 
    (c : β) (hfg: f =O[atTop] g) (hg : EventuallyBoundedBelow atTop g) :
    (fun n : ℕ ↦ (n : α) * f n) =O[atTop] (fun n : ℕ ↦ (n : β) * g n + c) := by
  obtain ⟨A, hA⟩ := (isBigO_cast.mul hfg).bound
  obtain ⟨B, hB⟩ := hg.bound
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + B) * ‖c‖)
  refine IsBigO.of_bound (A * (1 + B)) ?_
  filter_upwards [hA, hB, Filter.eventually_ge_atTop N] with n hA hB h_geN
  rw [norm_one] at hB
  have hB_nonneg : 0 ≤ B := by nlinarith [norm_nonneg (g n)]
  have hA_nonneg : 0 ≤ A := by
    simp only [norm_mul, RCLike.norm_natCast] at hA
    apply (Nat.cast_le (α := ℝ)).mpr at h_geN
    have hn_pos : 0 < (n : ℝ) := by nlinarith [norm_nonneg c]
    rw [←mul_assoc, mul_comm A, mul_assoc] at hA
    apply (mul_le_mul_iff_of_pos_left hn_pos).mp at hA
    nlinarith [norm_nonneg (f n)]
  rw [mul_assoc]
  refine le_trans hA <| mul_le_mul_of_nonneg_left ?_ hA_nonneg
  calc
    ‖n * g n‖ = ‖(n * g n + c) - c‖ := by ring_nf
    _ ≤ ‖n * g n + c‖ + ‖c‖ := norm_sub_le _ _
  rw [add_mul, one_mul]
  refine add_le_add_left ?_ _
  calc
    ‖c‖ ≤ B * ‖n * g n‖ - B * ‖c‖ := by
      rw [le_sub_iff_add_le]
      nth_rw 1 [←one_mul ‖c‖, ←add_mul]
      refine le_trans (le_of_lt hN) <| le_trans (Nat.cast_le.mpr h_geN) ?_
      rw [norm_mul, RCLike.norm_natCast, ←mul_assoc, mul_comm B, mul_assoc]
      nth_rewrite 1 [←mul_one (n : ℝ)]
      exact mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg' n)
    _ ≤ B * ‖n * g n + c‖ := by
      rw [←mul_sub]
      exact mul_le_mul_of_nonneg_left (norm_sub_le_norm_add _ _) hB_nonneg
   
theorem eventuallyBoundedBelow_nf_plus_c {α : Type*} [RCLike α] {f : ℕ → α} {c : α}
    (hf: EventuallyBoundedBelow atTop f) :
    EventuallyBoundedBelow atTop (fun n : ℕ ↦ n * f n + c) := by
  unfold EventuallyBoundedBelow at hf ⊢
  obtain ⟨A, hA⟩ := hf.bound
  obtain ⟨N, hN⟩ := exists_nat_ge (A * ‖c‖ + 1)
  refine IsBigO.of_bound A ?_
  filter_upwards [hA, Filter.eventually_ge_atTop N] with n hA hn
  rw [norm_one] at hA ⊢
  have hA_nonneg : 0 ≤ A := by nlinarith [norm_nonneg (f n)]
  refine le_trans ?_ <| mul_le_mul_of_nonneg_left (norm_sub_le_norm_add _ _) hA_nonneg
  rw [mul_sub, norm_mul, RCLike.norm_natCast]
  apply (Nat.cast_le (α := ℝ)).mpr at hn
  nlinarith

def natPoly_from_list {α : Type*} [RCLike α] (p : List α) (a : ℕ) :=
  match p with
  | [] => (0 : α)
  | head :: tail => head + (a : α) * (natPoly_from_list tail a)

theorem natPoly_from_list_cons {α : Type*} [RCLike α] (head : α) (tail : List α) (a : ℕ) :
    natPoly_from_list (head :: tail) a = head + (a : α) * (natPoly_from_list tail a) := by
  simp only [natPoly_from_list]

theorem natPoly_from_list_cons_fun {α : Type*} [RCLike α] (head : α) (tail : List α) :
    natPoly_from_list (head :: tail) = fun a : ℕ ↦ head + (a : α) * (natPoly_from_list tail a) := by
  simp only [natPoly_from_list]

theorem eventuallyBoundedBelow_natPoly_from_list {α : Type*} [RCLike α] (p : List α)
    (h_nonempty : p ≠ []) (h_leading : p.getLast h_nonempty ≠ 0) :
    EventuallyBoundedBelow atTop <| natPoly_from_list p := by
  induction' p with head tail htail
  contradiction
  match tail with
  | [] =>
    rw [List.getLast_singleton] at h_leading
    apply IsBigO.of_bound (1 / ‖head‖)
    field_simp [natPoly_from_list]
  | snd :: rest =>
    simp_rw [natPoly_from_list_cons_fun head, add_comm head]
    exact eventuallyBoundedBelow_nf_plus_c <| htail (List.cons_ne_nil _ _) h_leading
     
theorem isBigO_pow_degree_natPoly_from_list {α : Type*} [RCLike α] (p : List α)
    (h_nonempty : p ≠ []) (h_lead : p.getLast h_nonempty ≠ 0) :
    (fun n : ℕ ↦ (n : ℝ)^(p.length - 1)) =O[atTop] (natPoly_from_list p) := by
  induction' p with head tail htail
  contradiction
  match tail with
  | [] =>
    simp only [List.length_cons, List.length_nil, zero_add, tsub_self, pow_zero]
    refine IsBigO.trans ?_ <| eventuallyBoundedBelow_natPoly_from_list [head] h_nonempty h_lead
    simp only [isBigO_const_const_iff, one_ne_zero, imp_self]
  | snd :: rest =>
    convert isBigO_nf_ng_plus_c head (htail (List.cons_ne_nil _ _) h_lead)
      (eventuallyBoundedBelow_natPoly_from_list _ (List.cons_ne_nil _ _) h_lead)
    simp only [List.length_cons, add_tsub_cancel_right, pow_one]
    rw [pow_add, pow_one, mul_comm]
    rw [natPoly_from_list_cons, add_comm]

theorem isBigO_natPoly_from_list_pow_degree' {α : Type*} [RCLike α] (p : List α)
    (h_nonempty : p ≠ []) (h_lead : p.getLast h_nonempty ≠ 0) :
    (natPoly_from_list p) =O[atTop] (fun n : ℕ ↦ ((n : ℝ) + 1)^(p.length - 1)) := by
  induction' p with head tail htail
  contradiction
  match tail with
  | [] => simp only [natPoly_from_list, mul_zero, add_zero, List.length_cons, List.length_nil,
    zero_add, tsub_self, pow_zero, isBigO_const_const_iff, one_ne_zero, IsEmpty.forall_iff]
  | snd :: rest =>
    convert isBigO_nf_plus_c head (htail (List.cons_ne_nil _ _) h_lead) eventuallyBoundedBelow_pow
    rw [natPoly_from_list_cons, add_comm]
    simp only [List.length_cons, add_tsub_cancel_right, pow_one]
    rw [pow_add, pow_one, mul_comm]

theorem isBigO_natPoly_from_list_pow_degree {α : Type*} [RCLike α] (p : List α)
    (h_nonempty : p ≠ []) (h_lead : p.getLast h_nonempty ≠ 0) :
    (natPoly_from_list p) =O[atTop] (fun n : ℕ ↦ (n : ℝ)^(p.length - 1)) :=
  IsBigO.trans (isBigO_natPoly_from_list_pow_degree' p h_nonempty h_lead) isBigO_succ_pow_pow

theorem isTheta_natPoly_from_list_pow_degree {α : Type*} [RCLike α] (p : List α)
    (h_nonempty : p ≠ []) (h_lead : p.getLast h_nonempty ≠ 0) :
    (natPoly_from_list p) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ)^(p.length - 1)) := 
  ⟨isBigO_natPoly_from_list_pow_degree p h_nonempty h_lead,
   isBigO_pow_degree_natPoly_from_list p h_nonempty h_lead⟩

theorem isTheta_natPaly_from_list_div_natPoly_from_list_pow_degree_sub_degree {α : Type*} [RCLike α]
    (num : List α) (num_nonempty : num ≠ []) (num_lead : num.getLast num_nonempty ≠ 0)
    (denom : List α) (denom_nonempty : denom ≠ []) (denom_lead : denom.getLast denom_nonempty ≠ 0) :
    (fun n : ℕ ↦ (natPoly_from_list num n) / (natPoly_from_list denom n)) =Θ[atTop]
    (fun n : ℕ ↦ (n : ℝ)^((num.length : ℤ) - denom.length)) := by
  refine IsTheta.trans_eventuallyEq (IsTheta.div
    (isTheta_natPoly_from_list_pow_degree num num_nonempty num_lead)
    (isTheta_natPoly_from_list_pow_degree denom denom_nonempty denom_lead)) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [show ∀ m : ℕ, (n : ℝ)^m = (n : ℝ)^(m : ℤ) by intro m; rfl]
  rw [←zpow_sub₀ (Nat.cast_ne_zero.mpr hn)]
  apply congrArg
  have := List.eq_nil_iff_length_eq_zero.not.mp num_nonempty
  have := List.eq_nil_iff_length_eq_zero.not.mp denom_nonempty
  omega

