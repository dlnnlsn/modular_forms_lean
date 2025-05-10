import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open Filter Function Topology

variable {α: Type*} [CommMonoid α]

open Classical in
@[to_additive]
noncomputable def prod_within_radius (r: ℕ) (S: Set ℤ) (f: ℤ → α): α :=
  ∏ i ∈ (Finset.Icc (-r: ℤ) r).filter (· ∈ S), f i

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
    prod_within_radius r ⊤ f = ∏ i ∈ Finset.Icc (-r: ℤ) r, f i := by
  unfold prod_within_radius
  congr
  apply Finset.filter_true_of_mem (λ _ _ ↦ by trivial)

@[to_additive]
lemma prod_within_radius_of_prod (r: ℕ) (S: Set ℤ) (f g: ℤ → α):
    prod_within_radius r S (f * g) = prod_within_radius r S f * prod_within_radius r S g := Finset.prod_mul_distrib

@[to_additive]
lemma prod_within_radius_of_top_split_neg_nonneg (r: ℕ) (f: ℤ → α):
    prod_within_radius r ⊤ f = (∏ i ∈ Finset.range r, f (-(i + 1))) * (∏ i ∈ Finset.range (r + 1), f i) := by
  rw [prod_within_radius_of_top]
  have := Finset.Ico_union_Ico_eq_Ico
    (show (-r: ℤ) ≤ 0 from Int.neg_natCast_le_ofNat r 0) (show (0: ℤ) ≤ (r + 1) from Int.zero_le_ofNat (r + 1))
  rw [show Finset.Icc (-r: ℤ) r = Finset.Ico (-r: ℤ) (r + 1) by rfl]
  rw [←this]
  rw [Finset.prod_union]
  have h_neg: ∏ i ∈ Finset.Ico (-r: ℤ) 0, f i = ∏ i ∈ Finset.range r, f (-(i + 1)) := by
    rw [Finset.prod_bij (λ r _ ↦ (-r - 1).toNat)]
    · intro a ha
      rw [Finset.mem_Ico] at ha
      rw [Finset.mem_range]
      omega
    · intro a₁ ha₁ a₂ ha₂
      rw [Finset.mem_Ico] at ha₁ ha₂
      omega
    · intro b hb
      use (-b: ℤ) - 1
      rw [Finset.mem_range] at hb
      rw [exists_prop, Finset.mem_Ico]
      omega
    · intro a ha
      congr
      rw [Finset.mem_Ico] at ha
      omega
  have h_pos: ∏ i ∈ Finset.Ico (0: ℤ) (r + 1), f i = ∏ i ∈ Finset.range (r + 1), f i := by
    apply Finset.prod_bij (λ r _ ↦ r.toNat)
    · intro a ha
      rw [Finset.mem_Ico] at ha
      rw [Finset.mem_range]
      omega
    · intro a₁ ha₁ a₂ ha₂
      rw [Finset.mem_Ico] at ha₁ ha₂
      omega
    · intro b hb
      use b
      rw [exists_prop, Finset.mem_Ico]
      rw [Finset.mem_range] at hb
      omega
    · intro a ha
      congr
      rw [Finset.mem_Ico] at ha
      omega
  rw [h_neg, h_pos]
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  rw [Finset.mem_Ico] at ha hb
  omega

@[to_additive]
lemma prod_of_set_eq {β: Type*} {A B: Finset β} {f: β → α} (h: A = B): ∏ i ∈ A, f i = ∏ i ∈ B, f i := by congr

@[to_additive]
lemma prod_within_radius_of_top_range_div {α: Type*} [CommGroup α] (r: ℕ) (f: ℤ → α):
    prod_within_radius r ⊤ (λ n ↦ (f n) / (f (n + 1))) = (f (-r: ℤ)) / (f (r + 1)) := by
  rw [prod_within_radius_of_top]
  induction' r with r hr
  simp
  have h_union: Finset.Icc (-(r + 1): ℤ) (r + 1) = {(-(r + 1): ℤ)} ∪ Finset.Icc (-r: ℤ) r ∪ {((r + 1): ℤ)} := by sorry
  rw_mod_cast [prod_of_set_eq h_union] 
  rw [Finset.prod_union, Finset.prod_union, hr, Finset.prod_singleton, Finset.prod_singleton]
  rw [Int.neg_ofNat_eq_negSucc_add_one_iff.mpr rfl]
  simp [div_eq_mul_inv, mul_assoc]
  all_goals {
    rw [Finset.disjoint_iff_ne] 
    intro a ha b hb
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at *
    omega
  }

lemma prod_within_radius_of_top_range_div₀ {α: Type*} [CommGroupWithZero α] (r: ℕ) (f: ℤ → α) (h: ∀ n, f n ≠ 0):
    prod_within_radius r ⊤ (λ n ↦ (f n) / (f (n + 1))) = (f (-r: ℤ)) / (f (r + 1)) := by
  rw [prod_within_radius_of_top]
  induction' r with r hr
  simp
  have h_union: Finset.Icc (-(r + 1): ℤ) (r + 1) = {(-(r + 1): ℤ)} ∪ Finset.Icc (-r: ℤ) r ∪ {((r + 1): ℤ)} := by sorry
  rw_mod_cast [prod_of_set_eq h_union] 
  rw [Finset.prod_union, Finset.prod_union, hr, Finset.prod_singleton, Finset.prod_singleton]
  rw [Int.neg_ofNat_eq_negSucc_add_one_iff.mpr rfl]
  simp [div_eq_mul_inv, mul_assoc, h]
  all_goals {
    rw [Finset.disjoint_iff_ne] 
    intro a ha b hb
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at *
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

open Classical in
@[to_additive]
theorem HasProdOnZ.hasProd {S: Set ℤ} {f: ℤ → α} {a: α} (h_nonneg: ∀ s ∈ S, s ≥ 0) (h: HasProdOnZ S f a):
    HasProd (λ n ↦ if n ∈ S then f n else 1) a := by
  sorry

@[to_additive]
theorem hasProdOnZ_of_hasProd {f: ℤ → α} {a: α} (h: HasProd f a): HasProdOnZ ⊤ f a := by
  sorry

@[to_additive]
theorem hasProdOnZ_nat_of_hasProd_nat {f: ℤ → α} {a: α} (h: HasProd (λ n: ℕ ↦ f n) a): HasProdOnZ ⊤ f a := by
  sorry

-- @[to_additive]
-- theorem hasProdOnZ_nat_of_hasProd_nat {f: ℤ → α}

theorem HasProdOnZ.prod_div_range₀ {α: Type*} [CommGroupWithZero α] [TopologicalSpace α] [ContinuousMul α] [HasContinuousInv₀ α] {f: ℤ → α} {a b: α}
    (ha: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 a)) (hb: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 b)) (hf: ∀ n, f n ≠ 0) (hb_ne_zero: b ≠ 0):
    HasProdOnZ ⊤ (λ n ↦ f n / f (n + 1)) (a/b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_top_range_div₀ _ _ hf]
  apply Filter.Tendsto.div ha _ hb_ne_zero
  exact (tendsto_add_atTop_iff_nat 1).mpr hb

@[to_additive]
theorem HasProdOnZ.prod_div_range {α: Type*} [CommGroup α] [TopologicalSpace α] [ContinuousMul α] [ContinuousInv α] {f: ℤ → α} {a b: α}
    (ha: Tendsto (λ n: ℕ ↦ f (-n: ℤ)) atTop (𝓝 a)) (hb: Tendsto (λ n: ℕ ↦ f n) atTop (𝓝 b)):
    HasProdOnZ ⊤ (λ n ↦ f n / f (n + 1)) (a/b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_top_range_div, div_eq_mul_inv]
  apply Filter.Tendsto.mul ha
  exact_mod_cast (tendsto_add_atTop_iff_nat 1).mpr <| Filter.Tendsto.inv hb

@[to_additive]
theorem HasProdOnZ.prod [ContinuousMul α] {f g : ℤ → α} {a b: α} {S: Set ℤ} (hf: HasProdOnZ S f a) (hg: HasProdOnZ S g b):
    HasProdOnZ S (f * g) (a * b) := by
  unfold HasProdOnZ
  simp_rw [prod_within_radius_of_prod]
  exact Filter.Tendsto.mul hf hg

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

notation3 "∏_ℤ "(...)", "r:67:(scoped f => z_prod ⊤ f) => r
notation3 "∏_ℤ' "(...)", "r:67:(scoped f => z_prod ((⊤: Set ℤ) \ {0}) f) => r
notation3 "∑_ℤ "(...)", "r:67:(scoped f => z_sum ⊤ f) => r
notation3 "∑_ℤ' "(...)", "r:67:(scoped f => z_sum ((⊤: Set ℤ) \ {0}) f) => r
