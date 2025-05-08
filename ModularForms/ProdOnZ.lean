import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Defs.Filter

open Filter Function Topology

variable {α: Type*}
variable [CommMonoid α]

open Classical in
@[to_additive]
noncomputable def prod_within_radius (r: ℤ) (S: Set ℤ) (f: ℤ → α): α :=
  ∏ i ∈ (Finset.Icc (-r) r).filter (· ∈ S), f i

open Classical in
@[to_additive]
lemma prod_over_union_within_radius (r: ℤ) {S T: Set ℤ} (h: S ∩ T = ∅) (f: ℤ → α):
    prod_within_radius r (S ∪ T) f = (prod_within_radius r S f) * (prod_within_radius r T f) := by
  unfold prod_within_radius
  rw [←Finset.prod_union]
  congr
  rw [←Finset.filter_or]
  simp_rw [Set.mem_union]
  rw [Finset.disjoint_filter]
  intro _ _ hS hT
  simpa [h] using Set.mem_inter hS hT

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
    MultipliableOnZ S f :=
  ⟨a, h⟩

open Classical in
@[to_additive]
noncomputable irreducible_def z_prod (S: Set ℤ) (f: ℤ → α): α :=
  if h: MultipliableOnZ S f then h.choose else 1

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
theorem HasProdOnZ.of_z_prod_ne_one {S: Set ℤ} {f: ℤ → α} (h: z_prod S f ≠ 1):
    HasProdOnZ S f (z_prod S f) := (MultipliableOnZ.of_z_prod_ne_one h).hasProdOnZ

open Classical in
@[to_additive]
theorem HasProdOnZ.of_union [ContinuousMul α] {S T: Set ℤ} {f: ℤ → α} {s t: α} (h: S ∩ T = ∅) (hS: HasProdOnZ S f s) (hT: HasProdOnZ T f t):
    HasProdOnZ (S ∪ T) f (s * t) := by
  unfold HasProdOnZ at hS hT ⊢
  simp_rw [prod_over_union_within_radius _ h f]
  exact Filter.Tendsto.mul hS hT

notation3 "∏_ℤ "(...)", "r:67:(scoped f => z_prod ⊤ f) => r
notation3 "∏_ℤ' "(...)", "r:67:(scoped f => z_prod ((⊤: Set ℤ) \ {0}) f) => r
notation3 "∑_ℤ "(...)", "r:67:(scoped f => z_sum ⊤ f) => r
notation3 "∑_ℤ' "(...)", "r:67:(scoped f => z_sum ((⊤: Set ℤ) \ {0}) f) => r
