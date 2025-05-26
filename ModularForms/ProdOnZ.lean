import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open Filter Function Topology

variable {α: Type*}
variable [CommMonoid α]

open Classical in
@[to_additive]
noncomputable def prod_within_radius (r: ℕ) (S: Set ℤ) (f: ℤ → α): α :=
  ∏ i ∈ (Finset.Ico (-r: ℤ) r).filter (· ∈ S), f i

open Classical in
@[to_additive]
lemma prod_over_union_within_radius (r: ℕ) {S T: Set ℤ} (h: S ∩ T = ∅) (f: ℤ → α):
    prod_within_radius r (S ∪ T) f = (prod_within_radius r S f) * (prod_within_radius r T f) := by
  unfold prod_within_radius
  rw [←Finset.prod_union]
  congr
  rw [←Finset.filter_or]
  simp_rw [Set.mem_union]
  rw [Finset.disjoint_filter]
  intro _ _ hS hT
  simpa [h] using Set.mem_inter hS hT

open Classical in
@[to_additive]
lemma prod_within_radius_of_top (r: ℕ) (f: ℤ → α):
    prod_within_radius r ⊤ f = ∏ i ∈ Finset.Ico (-r: ℤ) r, f i := by
  unfold prod_within_radius
  congr
  apply Finset.filter_true_of_mem (λ _ _ ↦ by trivial)

@[to_additive]
lemma prod_within_radius_of_prod (r: ℕ) (S: Set ℤ) (f g: ℤ → α):
    prod_within_radius r S (f * g) = prod_within_radius r S f * prod_within_radius r S g := Finset.prod_mul_distrib

@[to_additive]
lemma prod_within_radius_of_inv {α: Type*} [DivisionCommMonoid α] [TopologicalSpace α] (r: ℕ) (S: Set ℤ) (f: ℤ → α):
    prod_within_radius r S (f⁻¹) = (prod_within_radius r S f)⁻¹ := Finset.prod_inv_distrib

@[to_additive]
lemma prod_of_set_eq {β: Type*} {A B: Finset β} {f: β → α} (h: A = B): ∏ i ∈ A, f i = ∏ i ∈ B, f i := by congr

@[to_additive]
lemma prod_within_radius_of_top_range_div {α: Type*} [CommGroup α] (r: ℕ) (f: ℤ → α):
    prod_within_radius r ⊤ (λ n ↦ f n / f (n + 1)) = f (-r: ℤ) / f r := by
  rw [prod_within_radius_of_top]
  induction' r with r hr
  simp
  have h_union: Finset.Ico (-(r + 1): ℤ) (r + 1) = {(-(r + 1): ℤ)} ∪ Finset.Ico (-r: ℤ) r ∪ {(r: ℤ)} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
    omega
  rw_mod_cast [prod_of_set_eq h_union] 
  rw [Finset.prod_union, Finset.prod_union, hr, Finset.prod_singleton, Finset.prod_singleton]
  rw [Int.neg_ofNat_eq_negSucc_add_one_iff.mpr rfl]
  simp [div_eq_mul_inv, mul_assoc]
  all_goals {
    rw [Finset.disjoint_iff_ne] 
    intro a ha b hb
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at *
    omega
  }

lemma prod_within_radius_of_top_range_div₀ {α: Type*} [CommGroupWithZero α] (r: ℕ) (f: ℤ → α) (h: ∀ n, f n ≠ 0):
    prod_within_radius r ⊤ (λ n ↦ (f n) / (f (n + 1))) = f (-r: ℤ) / f r := by
  rw [prod_within_radius_of_top]
  induction' r with r hr
  simp [h]
  have h_union: Finset.Ico (-(r + 1): ℤ) (r + 1) = {(-(r + 1): ℤ)} ∪ Finset.Ico (-r: ℤ) r ∪ {(r: ℤ)} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
    omega
  rw_mod_cast [prod_of_set_eq h_union] 
  rw [Finset.prod_union, Finset.prod_union, hr, Finset.prod_singleton, Finset.prod_singleton]
  rw [Int.neg_ofNat_eq_negSucc_add_one_iff.mpr rfl]
  simp [div_eq_mul_inv, mul_assoc, h]
  all_goals {
    rw [Finset.disjoint_iff_ne] 
    intro a ha b hb
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at *
    omega
  }

variable [TopologicalSpace α]

open Classical in
@[to_additive]
def HasProdOnZ (S: Set ℤ) (f: ℤ → α) (a: α): Prop :=
  Filter.Tendsto (prod_within_radius · S f) atTop (𝓝 a)

@[to_additive]
def MultipliableOnZ (S: Set ℤ) (f: ℤ → α): Prop :=
  ∃ a, HasProdOnZ S f a

@[to_additive]
theorem HasProdOnZ.multipliableOnZ {S: Set ℤ} {f: ℤ → α} {a: α} (h: HasProdOnZ S f a):
    MultipliableOnZ S f := sorry

open Classical in
@[to_additive]
noncomputable irreducible_def z_prod (S: Set ℤ) (f: ℤ → α): α :=
  if h: MultipliableOnZ S f then h.choose else 1

@[to_additive]
theorem HasProdOnZ.unique [T2Space α] {S: Set ℤ} {f: ℤ → α} {a₁ a₂: α}:
    HasProdOnZ S f a₁ → HasProdOnZ S f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique

open Classical in
@[to_additive]
theorem HasProdOnZ.congr {S₁ S₂: Set ℤ} {f₁ f₂: ℤ → α} {a: α} (hS: S₁ = S₂) (hf: ∀ k ∈ S₂, f₁ k = f₂ k) (h: HasProdOnZ S₁ f₁ a): HasProdOnZ S₂ f₂ a := by
  unfold HasProdOnZ
  have h_prod (r: ℕ): prod_within_radius r S₁ f₁ = prod_within_radius r S₂ f₂ := by
    apply Finset.prod_congr
    apply Finset.filter_congr
    intro x _
    rw [hS]
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hf x hx.right
  simp_rw [←h_prod]
  exact h

@[to_additive]
theorem MultipliableOnZ.congr {S₁ S₂: Set ℤ} {f₁ f₂: ℤ → α} (hS: S₁ = S₂) (hf: ∀ k ∈ S₂, f₁ k = f₂ k): MultipliableOnZ S₁ f₁ ↔ MultipliableOnZ S₂ f₂ := by
  constructor
  exact λ ⟨a, ha⟩ ↦ ⟨a, HasProdOnZ.congr hS hf ha⟩
  replace hf: ∀ k ∈ S₁, f₂ k = f₁ k := by
    intro k hk
    rw [hS] at hk
    exact Eq.symm <| hf k hk
  symm at hS
  exact λ ⟨a, ha⟩ ↦ ⟨a, HasProdOnZ.congr hS hf ha⟩

@[to_additive]
theorem MultipliableOnZ.of_z_prod_ne_one {S: Set ℤ} {f: ℤ → α} (h: z_prod S f ≠ 1):
    MultipliableOnZ S f := by
  by_contra h_not_multiplialbe
  simp [z_prod, h_not_multiplialbe] at h

@[to_additive]
theorem MultipliableOnZ.hasProdOnZ {S: Set ℤ} {f: ℤ → α} (h: MultipliableOnZ S f):
    HasProdOnZ S f (z_prod S f) := by
  simp only [z_prod, h, dite_true, h.choose_spec]

@[to_additive]
theorem HasProdOnZ.z_prod_eq [T2Space α] {S: Set ℤ} {f: ℤ → α} {a: α} (h: HasProdOnZ S f a): z_prod S f = a :=
  (MultipliableOnZ.hasProdOnZ ⟨a, h⟩).unique h

@[to_additive]
theorem MultipliableOnZ.z_prod_congr [T2Space α] {S₁ S₂: Set ℤ} {f₁ f₂: ℤ → α} (hS: S₁ = S₂) (hf: ∀ k ∈ S₂, f₁ k = f₂ k) (h: MultipliableOnZ S₁ f₁):
    z_prod S₁ f₁ = z_prod S₂ f₂ := by
  obtain ⟨a, ha⟩ := h
  have hb := HasProdOnZ.congr hS hf ha
  rw [HasProdOnZ.z_prod_eq ha, HasProdOnZ.z_prod_eq hb]

@[to_additive]
theorem HasProdOnZ.of_z_prod_ne_one {S: Set ℤ} {f: ℤ → α} (h: z_prod S f ≠ 1):
    HasProdOnZ S f (z_prod S f) := (MultipliableOnZ.of_z_prod_ne_one h).hasProdOnZ

open Classical in
@[to_additive]
theorem HasProdOnZ.of_union [ContinuousMul α] {S T: Set ℤ} {f: ℤ → α} {s t: α} (h: S ∩ T = ∅) (hS: HasProdOnZ S f s) (hT: HasProdOnZ T f t):
    HasProdOnZ (S ∪ T) f (s * t) := by
  unfold HasProdOnZ at hS hT ⊢
  simp_rw [prod_over_union_within_radius _ h f]
  exact Filter.Tendsto.mul hS hT

@[to_additive]
theorem HasProdOnZ.prod_const_one (S: Set ℤ): HasProdOnZ S (λ _ ↦ (1: α)) 1 := by
  unfold HasProdOnZ prod_within_radius
  simp_rw [Finset.prod_const_one]
  exact tendsto_const_nhds

theorem HasProdOnZ.prod_div_range₀ {α: Type*} [CommGroupWithZero α] [TopologicalSpace α] [ContinuousMul α] [HasContinuousInv₀ α] {f: ℤ → α} {a b: α}
    (ha: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 a)) (hb: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 b)) (hf: ∀ n, f n ≠ 0) (hb_ne_zero: b ≠ 0):
    HasProdOnZ ⊤ (λ n ↦ f n / f (n + 1)) (a/b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_top_range_div₀ _ _ hf]
  exact Filter.Tendsto.div ha hb hb_ne_zero

@[to_additive]
theorem HasProdOnZ.prod_div_range {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousInv α] {f: ℤ → α} {a b: α}
    (ha: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 a)) (hb: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 b)):
    HasProdOnZ ⊤ (λ n ↦ f n / f (n + 1)) (a/b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_top_range_div, div_eq_mul_inv]
  exact Filter.Tendsto.mul ha (Filter.Tendsto.inv hb)

@[to_additive]
theorem HasProdOnZ.prod [ContinuousMul α] {f g : ℤ → α} {a b: α} {S: Set ℤ} (hf: HasProdOnZ S f a) (hg: HasProdOnZ S g b):
    HasProdOnZ S (f * g) (a * b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_prod]
  exact Filter.Tendsto.mul hf hg

@[to_additive]
theorem HasProdOnZ.inv {α: Type*} [DivisionCommMonoid α] [TopologicalSpace α] [ContinuousInv α] {f: ℤ → α} {a: α} {S: Set ℤ} (hf: HasProdOnZ S f a): HasProdOnZ S (f⁻¹) (a⁻¹) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_inv]
  exact Filter.Tendsto.inv hf

@[to_additive]
theorem HasProdOnZ.div {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousInv α]  {f g: ℤ → α} {a b: α} {S: Set ℤ} (hf: HasProdOnZ S f a) (hg: HasProdOnZ S g b):
    HasProdOnZ S (f/g) (a/b) := by
  repeat rw [div_eq_mul_inv]
  exact HasProdOnZ.prod hf (HasProdOnZ.inv hg)

@[to_additive]
theorem HasProdOnZ.exchange_prod_finprod {β: Type*} [DecidableEq β] [ContinuousMul α] {S: Set ℤ} {T: Finset β} {f: β → ℤ → α} {g: β → α}
    (h: ∀ b ∈ T, HasProdOnZ S (f b ·) (g b)):
    HasProdOnZ S (∏ b ∈ T, f b ·) (∏ b ∈ T, g b) := by
  induction' T using Finset.induction_on' with b T' _ _ h_nelem h_ind
  · simp [HasProdOnZ.prod_const_one]
  · simp_rw [Finset.prod_insert h_nelem]
    apply HasProdOnZ.prod
    exact h b <| Finset.mem_insert_self b T'
    apply h_ind
    intro b hb
    exact h b <| Finset.mem_insert_of_mem hb

@[to_additive]
theorem exchange_z_prod_finprod {β: Type*} [T2Space α] [DecidableEq β] [ContinuousMul α] {S: Set ℤ} {T: Finset β} {f : β → ℤ → α}
    (h: ∀ b ∈ T, MultipliableOnZ S (f b ·)): 
    ∏ b ∈ T, z_prod S (f b ·) = z_prod S (∏ b ∈ T, f b ·) := by
  let g := λ b: β ↦ z_prod S (f b ·)
  have h: ∀ b ∈ T, HasProdOnZ S (f b ·) (g b) := λ b hb ↦ MultipliableOnZ.hasProdOnZ (h b hb)
  symm
  apply HasProdOnZ.z_prod_eq
  exact HasProdOnZ.exchange_prod_finprod h

@[to_additive]
theorem MultipliableOnZ.z_prod_prod [T2Space α] [ContinuousMul α] {S: Set ℤ} {f g: ℤ → α} (hf: MultipliableOnZ S f) (hg: MultipliableOnZ S g):
    z_prod S (f * g) = z_prod S f * z_prod S g := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have h_fg_prod: HasProdOnZ S (f * g) (a * b) := HasProdOnZ.prod ha hb
  rw [HasProdOnZ.z_prod_eq ha, HasProdOnZ.z_prod_eq hb, HasProdOnZ.z_prod_eq h_fg_prod]

@[to_additive]
theorem MultipliableOnZ.z_prod_div {α: Type*} [CommGroup α] [TopologicalSpace α] [T2Space α] [ContinuousMul α] [ContinuousInv α]  {f g: ℤ → α} {S: Set ℤ} (hf: MultipliableOnZ S f) (hg: MultipliableOnZ S g):
    z_prod S (f/g) = z_prod S f / z_prod S g := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have h_fg_prod: HasProdOnZ S (f / g) (a / b) := HasProdOnZ.div ha hb
  rw [HasProdOnZ.z_prod_eq ha, HasProdOnZ.z_prod_eq hb, HasProdOnZ.z_prod_eq h_fg_prod]

open Classical in
@[to_additive]
theorem z_prod_congr [T2Space α] {S₁ S₂: Set ℤ} {f₁ f₂: ℤ → α} (hS: S₁ = S₂) (hf: ∀ k ∈ S₂, f₁ k = f₂ k): z_prod S₁ f₁ = z_prod S₂ f₂ :=
  if h: MultipliableOnZ S₁ f₁ then MultipliableOnZ.z_prod_congr hS hf h else by
  have h_f₂_not_multipliable: ¬MultipliableOnZ S₂ f₂ := (MultipliableOnZ.congr hS hf).not.mp h
  simp only [z_prod, h, ↓reduceDIte, h_f₂_not_multipliable]

notation3 "∏_ℤ "(...)", "r:67:(scoped f => z_prod ⊤ f) => r
notation3 "∏_ℤ' "(...)", "r:67:(scoped f => z_prod ((⊤: Set ℤ) \ {0}) f) => r
notation3 "∑_ℤ "(...)", "r:67:(scoped f => z_sum ⊤ f) => r
notation3 "∑_ℤ' "(...)", "r:67:(scoped f => z_sum ((⊤: Set ℤ) \ {0}) f) => r

def ℤ_neg := { x: ℤ | x < 0 }
def ℤ_nonneg := { x: ℤ | x ≥ 0 }

open Classical in
@[to_additive]
theorem HasProdOnZ.of_nat_of_neg {S: Set ℤ} {a b: α} {f: ℤ → α}
    (h_nat: Tendsto (λ N ↦ ∏ k ∈ (Finset.range N).filter (λ k: ℕ ↦ (k: ℤ) ∈ S), f k) atTop (𝓝 a))
    (h_neg: Tendsto (λ N ↦ ∏ k ∈ (Finset.range N).filter (λ k: ℕ ↦ (-(k + 1): ℤ) ∈ S), f (-(k + 1))) atTop (𝓝 b)):
    HasProdOnZ S f (a * b) := by
  sorry


open Classical in
@[to_additive]
theorem HasProdOnZ.of_prod {S: Set ℤ} {a: α} {f: ℤ → α} (h: HasProd (λ k ↦ if k ∈ S then f k else 1) a): HasProdOnZ S f a := by
  unfold HasProd at h
  unfold HasProdOnZ
  let f' := λ k ↦ if k ∈ S then f k else 1
  simp_rw [show ∀ r: ℕ, prod_within_radius r S f = ∏ k ∈ Finset.Ico (-r: ℤ) r, f' k by
    intro r
    unfold prod_within_radius
    rw [Finset.prod_ite f (λ _ ↦ 1), Finset.prod_const_one, mul_one]
  ]
  rw [atTop_basis.tendsto_iff <| nhds_basis_opens a] at h ⊢
  intro b b_open_around_a
  obtain ⟨S, hS⟩ := h b b_open_around_a
  let R: ℕ := if h_nonempty: S.Nonempty then 1 + (Finset.image Int.natAbs S).max' (Finset.image_nonempty.mpr h_nonempty) else 0
  have h_contained (r: ℕ) (hr: r ≥ R): S ⊆ Finset.Ico (-r: ℤ) r := by
    intro x x_elem
    have h_nonempty: S.Nonempty := Finset.nonempty_of_ne_empty <| Finset.ne_empty_of_mem x_elem
    have h_x_natAbs: x.natAbs < R := by
      unfold R
      simp only [h_nonempty, ↓reduceDIte]
      have h_elem: x.natAbs ∈ Finset.image Int.natAbs S := Finset.mem_image_of_mem Int.natAbs x_elem
      have := Finset.le_max' (Finset.image Int.natAbs S) x.natAbs h_elem
      exact Nat.lt_one_add_iff.mpr this
    rw [Finset.mem_Ico]
    omega
  use R
  constructor
  trivial
  intro r hr
  exact hS.right (Finset.Ico (-r: ℤ) r) (h_contained r hr)

open Classical in
@[to_additive]
theorem MultipliableOnZ.of_multipliable {S: Set ℤ} {f: ℤ → α} (h: Multipliable (λ k ↦ if k ∈ S then f k else 1)): MultipliableOnZ S f :=
  HasProdOnZ.multipliableOnZ <| HasProdOnZ.of_prod <| Multipliable.hasProd h

open Classical in
@[to_additive]
theorem z_prod_eq_tprod_of_multipliable [T2Space α] {S: Set ℤ} {f: ℤ → α} (h: Multipliable (λ k ↦ if k ∈ S then f k else 1)):
    z_prod S f = ∏' k, if k ∈ S then f k else 1 := by
  let f' := λ k ↦ if k ∈ S then f k else 1
  have h_multipliableOnZ: MultipliableOnZ S f := MultipliableOnZ.of_multipliable h
  have h_hasProd: HasProd f' (∏' k, f' k) := by exact Multipliable.hasProd h
  have h_hasProdOnZ_prod: HasProdOnZ S f (∏' k, f' k) := by exact HasProdOnZ.of_prod h_hasProd
  apply HasProdOnZ.z_prod_eq h_hasProdOnZ_prod

@[to_additive]
theorem z_prod'_eq_tprod_of_multipliable_of_pos_of_neg [T2Space α] {f: ℤ → α} (h: Multipliable (λ k ↦ if k = 0 then 1 else f k)):
    ∏_ℤ' k, f k = ∏' k: ℕ, (f (k + 1) * f (-(k + 1): ℤ)) := by
  sorry

theorem HasSumOnZ.const_mul {α: Type*} [CommRing α] [TopologicalSpace α] [ContinuousMul α] {S: Set ℤ} {a: α} {f: ℤ → α} (h: HasSumOnZ S f a) (c: α): HasSumOnZ S (λ k ↦ c * f k) (c * a) := by
  unfold HasSumOnZ
  unfold sum_within_radius
  simp_rw [←Finset.mul_sum]
  exact Tendsto.mul tendsto_const_nhds h

theorem SummableOnZ.const_mul {α: Type*} [CommRing α] [TopologicalSpace α] [ContinuousMul α] {S: Set ℤ} {f: ℤ → α} (c: α):
    SummableOnZ S f → SummableOnZ S (λ k ↦ c * f k) :=
  λ ⟨a, ha⟩ ↦ ⟨c * a, HasSumOnZ.const_mul ha c⟩

theorem SummableOnZ.const_mul_iff {α: Type*} [Field α] [TopologicalSpace α] [ContinuousMul α] {S: Set ℤ} {f: ℤ → α} {c: α} (hc: c ≠ 0):
    SummableOnZ S f ↔ SummableOnZ S (λ k ↦ c * f k) := by
  constructor
  exact SummableOnZ.const_mul c
  intro h_summable
  rw [show f = λ k ↦ c⁻¹ * (c * f k) by
    funext k
    rw [←mul_assoc, inv_mul_cancel₀ hc, one_mul]
  ]
  exact SummableOnZ.const_mul (c⁻¹) h_summable

theorem SummableOnZ.z_sum_const_mul {α: Type*} [CommRing α] [TopologicalSpace α] [T2Space α] [ContinuousMul α] {S: Set ℤ} {f: ℤ → α} {c: α} (h: SummableOnZ S f):
    z_sum S (λ k ↦ c * f k) = c * z_sum S f := by
  obtain ⟨a, ha⟩ := h
  rw [ha.z_sum_eq, (ha.const_mul c).z_sum_eq]

open Classical in
theorem z_sum_const_mul {α: Type*} [Field α] [TopologicalSpace α] [T2Space α] [ContinuousMul α] {S: Set ℤ} {f: ℤ → α} {c: α}:
    z_sum S (λ k ↦ c * f k) = c * z_sum S f :=
  if h_zero: c = 0 then by
    simp_rw [h_zero, zero_mul]
    exact (HasSumOnZ.sum_const_zero S).z_sum_eq
  else if h_summable: SummableOnZ S f then
    SummableOnZ.z_sum_const_mul h_summable
  else by
    have h_cf_not_summable := (SummableOnZ.const_mul_iff h_zero).not.mp h_summable
    simp [z_sum_def, h_summable, h_cf_not_summable]

@[to_additive]
theorem HasProdOnZ.of_singleton (f: ℤ → α) (b: ℤ): HasProdOnZ {b} f (f b) := by
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_atTop]
  use b.natAbs + 1
  intro n hn
  have h_set: (Finset.Ico (-n: ℤ) n).filter (· ∈ ({b}: Set ℤ)) = { b } := by
    ext x
    constructor
    simp only [Set.mem_singleton_iff, Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton,
      and_imp, imp_self, implies_true]
    simp only [Finset.mem_singleton, Set.mem_singleton_iff, Finset.mem_filter, Finset.mem_Ico]
    omega
  unfold prod_within_radius
  rw [←Finset.prod_singleton f b]
  congr
  convert h_set

@[to_additive]
theorem MultipliableOnZ.of_singleton (f: ℤ → α) (b: ℤ): MultipliableOnZ ({b}: Set ℤ) f := (HasProdOnZ.of_singleton f b).multipliableOnZ

open Classical in
@[to_additive]
lemma prod_within_radius_of_sdiff {α: Type*} [CommGroup α] {S T: Set ℤ} (r: ℕ) (f: ℤ → α) (h_subset: T ⊆ S):
    prod_within_radius r (S \ T) f * prod_within_radius r T f = prod_within_radius r S f := by
  unfold prod_within_radius
  let S' := (Finset.Ico (-r: ℤ) r).filter (· ∈ S)
  let T' := (Finset.Ico (-r: ℤ) r).filter (· ∈ T)
  replace h_subset: T' ⊆ S' := by
    unfold S' T'
    intro x hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hT.left, h_subset hT.right⟩
  have h_sdiff: S' \ T' = (Finset.Ico (-r: ℤ) r).filter (· ∈ S \ T) := by
    aesop
  refold_let S'  T'
  have h_sdiff_prod := Finset.prod_sdiff (f := f) h_subset 
  rw [h_sdiff] at h_sdiff_prod
  convert h_sdiff_prod

@[to_additive]
theorem HasProdOnZ.of_sdiff {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousDiv α] {S T: Set ℤ} {s t: α} {f: ℤ → α}
    (h_subset: T ⊆ S) (hS: HasProdOnZ S f s) (hT: HasProdOnZ T f t):
    HasProdOnZ (S \ T) f (s / t) := by
  unfold HasProdOnZ
  have h_prod_radius (r: ℕ) := eq_div_iff_mul_eq'.mpr <| prod_within_radius_of_sdiff r f h_subset
  simp_rw [h_prod_radius]
  apply Tendsto.div' hS hT

@[to_additive]
theorem MultipliableOnZ.of_union [ContinuousMul α] {S T: Set ℤ} {f: ℤ → α} (h: S ∩ T = ∅): MultipliableOnZ S f → MultipliableOnZ T f →
    MultipliableOnZ (S ∪ T) f := λ ⟨s, hS⟩ ⟨t, hT⟩ ↦ ⟨s * t, HasProdOnZ.of_union h hS hT⟩

@[to_additive]
theorem MultipliableOnZ.of_union_iff {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousDiv α] {S T: Set ℤ} {f: ℤ → α} (h: S ∩ T = ∅) (h_multipliable: MultipliableOnZ S f):
    MultipliableOnZ (S ∪ T) f ↔ MultipliableOnZ T f := by
  constructor
  intro h_multipliable_union
  rw [show T = (S ∪ T) \ S from Eq.symm (Set.union_diff_cancel_left (Set.subset_empty_iff.mpr h))]
  obtain ⟨s, hs⟩ := h_multipliable
  obtain ⟨st, hst⟩ := h_multipliable_union
  use st / s
  exact HasProdOnZ.of_sdiff Set.subset_union_left hst hs
  exact λ hT ↦ MultipliableOnZ.of_union h h_multipliable hT

@[to_additive]
lemma eq_z_prod_of_mul_of_z_prod'_of_eval_zero {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousDiv α] [T2Space α]
    {f: ℤ → α} (h: MultipliableOnZ (⊤ \ {0}) f): ∏_ℤ k, f k = (∏_ℤ' k, f k) * f 0 := by
  have h_union: ⊤ = ((⊤: Set ℤ) \ { 0 }) ∪ { 0 } := Eq.symm <| Set.diff_union_of_subset (λ _ _ ↦ trivial)
  obtain ⟨a, ha⟩ := h
  have h_prod := HasProdOnZ.of_union Set.diff_inter_self ha (HasProdOnZ.of_singleton f 0) 
  rw [←ha.z_prod_eq] at h_prod
  convert h_prod.z_prod_eq

@[to_additive]
lemma eq_z_prod_of_mul_of_z_prod'_of_eval_zero' {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousDiv α] [T2Space α] 
    {f: ℤ → α} (h: MultipliableOnZ ⊤ f): ∏_ℤ k, f k = (∏_ℤ' k, f k) * f 0 := by
  rw [show ⊤ = {0} ∪ ((⊤: Set ℤ) \ {0}) by aesop] at h
  apply eq_z_prod_of_mul_of_z_prod'_of_eval_zero
  exact (MultipliableOnZ.of_union_iff (Set.inter_diff_self {0} ⊤) (MultipliableOnZ.of_singleton f 0)).mp h
