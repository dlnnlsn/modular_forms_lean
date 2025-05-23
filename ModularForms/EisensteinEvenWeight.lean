import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Polish

open EisensteinSeries CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open Complex Topology
open Classical


open scoped Real MatrixGroups CongruenceSubgroup

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)
variable{N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
variable {z : ℍ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam
notation "i" => Complex.I

instance fintoprod : (Fin 2 → ℤ) ≃ ℤ × ℤ where
  toFun := fun v => (v 0, v 1)
  invFun := fun v => fun n => if n = 0 then v.1 else v.2
  left_inv := by
    intro v ;
    simp_all only [Fin.isValue] ;
    ext b ;
    split
    next h =>
      subst h
      simp_all only [Fin.isValue]
    next h =>
      have : b = 1 := by exact Fin.eq_one_of_ne_zero b h
      rw [this]
  right_inv := by
    intro v
    simp_all only [Fin.isValue, ↓reduceIte, one_ne_zero, Prod.mk.eta]

lemma gammaSet_eq_coprime_int  (a : Fin 2 → ZMod 1): fintoprod.toFun '' gammaSet 1 a = {x : ℤ × ℤ | IsCoprime x.1 x.2} := by
  ext x
  constructor
  · intro h
    apply Membership.mem.out at h
    obtain ⟨a₁, h₁⟩ := h
    simp only [Equiv.toFun_as_coe] at h₁
    unfold fintoprod at h₁
    simp only [Fin.isValue, Equiv.coe_fn_mk] at h₁
    have h₂ : a₁ ∈ gammaSet 1 a := by apply h₁.1
    have h₃ : (a₁ 0 , a₁ 1) = x := by apply h₁.2
    apply Membership.mem.out at h₂
    have h₄ : x.1 = a₁ 0 := by
      subst h₃ ; simp_all only [Fin.isValue, and_true]
    have h₅ : x.2 = a₁ 1 := by subst h₃ ; simp_all only [Fin.isValue, and_true]
    have h₆ : IsCoprime x.1 x.2 := by rw [h₄, h₅] ; apply h₂.2
    subst h₃
    simp_all only [Fin.isValue, and_true, Set.mem_setOf_eq]
  · intro h
    apply Membership.mem.out at h
    unfold fintoprod
    simp_all only [Fin.isValue, Set.mem_image]
    obtain ⟨x₁, x₂⟩ := x
    simp_all only [Fin.isValue, Prod.mk.injEq]
    use (fun n => if n = 0 then x₁ else x₂)
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, and_self, and_true]
    have h₁ : gammaSet 1 a = gammaSet 1 ((fun n ↦ if n = 0 then x₁ else x₂)) := by apply gammaSet_one_eq
    rw [h₁]
    unfold gammaSet
    simp_all only [Fin.isValue, Set.mem_setOf_eq, ↓reduceIte, one_ne_zero, and_true]
    ext x : 1
    simp_all only [Fin.isValue, comp_apply, Int.cast_ite]

theorem eisensteinSeries_eq_CoprimeSum {k : ℕ} (a : Fin 2 → ZMod 1) :
eisensteinSeries a k = fun z : ℍ => ∑' x : {x : ℤ × ℤ | IsCoprime x.1 x.2}, (x.1.1 *  (z : ℂ) + x.1.2) ^ (- k: ℤ) := by
unfold eisensteinSeries
ext z
rw [← gammaSet_eq_coprime_int a, ]
rw [@tsum_image ℂ (ℤ × ℤ) (Fin 2 → ℤ)  _ _ fintoprod.toFun (fun x => (x.1 * z + x.2) ^ (-k:ℤ)) (gammaSet 1 a) _ ]
congr
refine Injective.injOn ?_
intro v v₁ h
simp_all only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]

@[simp]
lemma factoroutGCD {k : ℕ} {m n : ℤ} {mornne0 : m ≠ 0 ∨ n ≠ 0}: (m * (z : ℂ) + n) ^ (-k : ℤ) =
(Int.gcd m n) ^ (- k : ℤ) * (m / Int.gcd m n * (z : ℂ) + n / Int.gcd m n) ^ (-k : ℤ) := by
field_simp; ring_nf ; simp ;
simp_all only [ne_eq]
cases mornne0 with
| inl h =>
  simp_all only [ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, Int.gcd_eq_zero_iff, false_and, not_false_eq_true,
    mul_inv_cancel_right₀]
| inr h_1 =>
  simp_all only [ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, Int.gcd_eq_zero_iff, and_false, false_and,
    not_false_eq_true, mul_inv_cancel_right₀]

instance NCoptoℤxℤ : {n : ℕ | n > 0} × {x : ℤ × ℤ | IsCoprime x.1 x.2} ≃ {x : ℤ × ℤ | x ≠ 0} where
  toFun := fun x => ⟨⟨ x.1.1 * x.2.1.1, x.1.1 * x.2.1.2⟩, by
    have : x.2.1.1 ≠ 0 ∨ x.2.1.2 ≠ 0 := by
      simp_all only [Set.mem_setOf_eq, Set.coe_setOf, ne_eq]
      obtain ⟨x₁, x₂⟩ := x
      obtain ⟨v, vh⟩ := x₂
      --obtain ⟨x₃, x₂⟩ := v
      simp_all only
      simp_all only [Set.mem_setOf_eq]
      have vh' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by apply IsCoprime.ne_zero_or_ne_zero vh
      simp_all only [ne_eq]
    rw [Set.mem_setOf]
    simp_all only [Set.mem_setOf_eq, Set.coe_setOf, ne_eq, Prod.mk_eq_zero, mul_eq_zero, Int.natCast_eq_zero,
      PNat.ne_zero, false_or, not_and]
    intro a_1
    simp_all only [not_or]
    obtain ⟨fst, snd⟩ := x
    obtain ⟨val, property⟩ := fst
    obtain ⟨val_1, property_1⟩ := snd
    obtain ⟨fst, snd⟩ := val_1
    simp_all only
    simp_all only [gt_iff_lt, Set.mem_setOf_eq]
    cases this with
    | inl h =>
      cases a_1 with
      | inl h_1 =>
        subst h_1
        simp_all only [lt_self_iff_false]
      | inr h_2 =>
        subst h_2
        simp_all only [not_true_eq_false]
    | inr h_1 =>
      cases a_1 with
      | inl h =>
        subst h
        simp_all only [lt_self_iff_false]
      | inr h_2 =>
        subst h_2
        simp_all only [not_false_eq_true, and_true]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [lt_self_iff_false] ⟩
  invFun := fun x => ⟨⟨Int.gcd x.1.1 x.1.2, by
    simp_all only [gt_iff_lt, ne_eq, Set.mem_setOf_eq, Int.gcd_pos_iff]
    obtain ⟨val, property⟩ := x
    obtain ⟨fst, snd⟩ := val
    simp_all only
    simp_all only [ne_eq, Set.mem_setOf_eq, Prod.mk_eq_zero, not_and]
    by_cases h : fst = 0
    · right
      apply property h
    · simp_all only [IsEmpty.forall_iff, not_false_eq_true, true_or]⟩,
  ⟨⟨x.1.1 / (Int.gcd x.1.1 x.1.2), x.1.2 / (Int.gcd x.1.1 x.1.2)⟩, by
    simp_all only [ne_eq, Set.mem_setOf_eq]
    obtain ⟨val, property⟩ := x
    obtain ⟨fst, snd⟩ := val
    simp_all only
    simp_all only [ne_eq, Set.mem_setOf_eq, Prod.mk_eq_zero, not_and]
    have : ∃ u v ,fst * u + snd * v = fst.gcd snd := by
      have : ∃ (x : ℤ) (y : ℤ), gcd fst snd = fst * x + snd * y := by
        apply exists_gcd_eq_mul_add_mul
      obtain ⟨x ,y, hxy⟩ := this
      have : (Nat.gcd (fst.natAbs) (snd.natAbs)) = Int.gcd fst snd := by
        congr
      use x ; use y ; simp_rw [← hxy] ; norm_cast
    obtain ⟨u,v,h⟩ := this
    use u ; use v
    have fact:  ((fst.gcd snd) : ℤ) ≠ 0 := by simp_all only [ne_eq, Int.gcd_eq_zero_iff, not_and, not_false_eq_true, implies_true] ; simp_all only [Int.natCast_eq_zero,
      Int.gcd_eq_zero_iff, not_and, not_false_eq_true, implies_true]
    simp_all only [ne_eq, Int.natCast_eq_zero, Int.gcd_eq_zero_iff, not_and, not_false_eq_true, implies_true]
    sorry
    ⟩ ⟩
  left_inv := by
    simp_all only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq]
    intro S
    simp_all only
    obtain ⟨fst, snd⟩ := S
    obtain ⟨val, property⟩ := fst
    obtain ⟨val_1, property_1⟩ := snd
    obtain ⟨fst, snd⟩ := val_1
    simp_all only [Prod.mk.injEq, Subtype.mk.injEq]
    simp_all only [gt_iff_lt]
    apply And.intro
    · have property_1clone : IsCoprime fst snd := by apply property_1
      obtain ⟨u, v , h₁⟩ := property_1
      refine Int.gcd_eq_iff.mpr ?_
      simp_all only [dvd_mul_right, true_and]
      intro c a_1 a_2
      have h₂: c ∣ val * fst ∧ c ∣ val * snd := by exact ⟨a_1,a_2 ⟩
      sorry --silly proof
    · apply And.intro
      · sorry
      · sorry
  right_inv := sorry

lemma isomrw : {x : ℤ × ℤ | x ≠ 0} = NCoptoℤxℤ '' Set.univ  := by
  refine Set.ext ?_
  intro x
  constructor
  · intro h
    simp_all only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, Set.image_univ, EquivLike.range_eq_univ,
      Subtype.range_coe_subtype, not_false_eq_true]
  · intro h
    simp_all only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, Set.image_univ, EquivLike.range_eq_univ,
      Subtype.range_coe_subtype, not_false_eq_true]

lemma NCoptoℤxℤ_set_inj : ∀ s : Set ({n : ℕ | n > 0} × {x : ℤ × ℤ | IsCoprime x.1 x.2}), Set.InjOn NCoptoℤxℤ s := by sorry

lemma DoubleSum_eq_Prod {k : ℕ} : ∑' x : {x : ℤ × ℤ | x ≠ 0},(x.1.1 * (z : ℂ) + x.1.2) ^ (- k : ℤ ) =
∑' N : ℕ, 1/(N + 1) ^ k* ∑' x : {x : ℤ × ℤ | IsCoprime x.1 x.2}, (x.1.1 *  (z : ℂ) + x.1.2) ^ (- k : ℤ):= by
  rw [isomrw]
   --simp_all only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, zpow_neg, zpow_natCast, one_div]
  convert @tsum_image ℂ _ _ _ _ _ (fun x => (x.1.1 * (z : ℂ) + x.1.2) ^ (- k : ℤ )) _ (NCoptoℤxℤ_set_inj Set.univ)-- (fun x => ((x.1.1 * ↑z + x.1.2) ^ k)⁻¹) (NCoptoℤxℤ_set_inj Set.univ)
  simp only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, zpow_neg, zpow_natCast]
  congr 1
  simp_all only [Set.image_univ, EquivLike.range_eq_univ, Subtype.range_coe_subtype, Set.coe_setOf]
  · sorry--I believe this is clearly true but not easy to show for some reason
    --have : { x : ℤ × ℤ | ¬x = 0 } = (@Set.univ  )  := by
  · refine hfunext ?_ ?_
    · sorry
    · intro a a' ha
      simp_all only [heq_eq_eq, inv_inj]
      obtain ⟨a_1, property⟩ := a
      obtain ⟨val_1, h_2⟩ := a'
      obtain ⟨b_1, b_2⟩ := a_1
      obtain ⟨val, h_3⟩ := val_1
      obtain ⟨c_1, c_2⟩ := val
      simp_all only
      congr
      --rw [heq_eq_eq ⟨(b_1, b_2), property⟩ ⟨⟨(c_1, c_2), h_3⟩, h_2⟩] at ha
      · sorry --need more coercions instances or something?
      · sorry
  · simp only [one_div, Set.coe_setOf, Set.mem_setOf_eq, zpow_neg, zpow_natCast, ne_eq]
    unfold NCoptoℤxℤ
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Equiv.coe_fn_mk, Int.cast_mul,
      Int.cast_natCast]
    rw [@tsum_univ ℂ (({ x : ℕ // x > 0 } × { x : ℤ × ℤ // IsCoprime x.1 x.2 })) _ _ (fun x =>
     ((x.1.1 * x.2.1.1 * ↑z + x.1.1 * ↑x.2.1.2) ^ k)⁻¹) ]
    rw [Summable.tsum_prod]
    ring_nf -- more lengthy computation
    sorry
    sorry --summability


lemma eisensteinSeries_as_SumOver_ℤ_ℤ {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
∑' x : {x : ℤ × ℤ | x ≠ 0}, (x.1.1 * (z : ℂ) + x.1.2) ^ (- k : ℤ ) =
 ∑' N : ℕ, 1/(N + 1) ^ k * (eisensteinSeries a k z) := by
  rw [eisensteinSeries_eq_CoprimeSum]
  simp only
  rw [DoubleSum_eq_Prod]

lemma eisensteinSeries_as_SumOver_ℤ_ℤ_fun {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
(fun z : ℍ => ∑' x : {x : ℤ × ℤ | x ≠ 0}, (x.1.1 * ( z : ℂ) + x.1.2) ^ (- k : ℤ )) =( fun z : ℍ =>
 ∑' N : ℕ, 1/(N + 1) ^ k * (eisensteinSeries a k z) ):= by
 ext τ
 rw [eisensteinSeries_as_SumOver_ℤ_ℤ]

lemma eisensteinseries_splitoff_zeta {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
  ∑' N : ℕ, 1/(N + 1) ^ k * (eisensteinSeries a k z) = (∑' N : ℕ, 1/(N + 1) ^ k) * (eisensteinSeries a k z) := by
    sorry --follows from uniform convergence

lemma eisensteinseries_splitoff_zeta_fun {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
  (fun z : ℍ => ∑' N : ℕ, 1/(N + 1) ^ k * (eisensteinSeries a k z)) =
 ( fun z => (∑' N : ℕ, 1/(N + 1) ^ k) * (eisensteinSeries a k z)) := by
 ext τ
 rw [eisensteinseries_splitoff_zeta]

lemma DoubleSUm_relatesto_Bernoulli {k m: ℕ} (a : Fin 2 → ZMod (1:ℕ+)) (keven : k = 2 * m) (mne0 : m ≠ 0):
∑' x : {x : ℤ × ℤ | x ≠ 0}, (x.1.1 * (z : ℂ) + x.1.2) ^ (- k : ℤ ) =
   ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (Nat.factorial (2 * k))) * (eisensteinSeries a k z) := by
  rw [eisensteinSeries_as_SumOver_ℤ_ℤ a, eisensteinseries_splitoff_zeta a]
  subst keven
  --rw [ HasSum.tsum_eq (hasSum_zeta_nat mne0)]
  sorry


lemma compllemma : (@Finset.toSet (ℤ × ℤ) {0})ᶜ = {x : ℤ × ℤ | x ≠ 0} := by
simp_all only [Finset.coe_singleton, ne_eq]
rfl

lemma summablenonsense {k : ℕ} : Summable (fun x : ℤ × ℤ => (x.1 * ( z : ℂ) + x.2) ^ (- k : ℤ )) := by sorry

theorem Ihateleantheorem {k : ℕ} (kne0 : k ≠ 0):
 ∑' x : {x : ℤ × ℤ | x ≠ 0}, (x.1.1 * ( z : ℂ) + x.1.2) ^ (- k : ℤ ) =
  ∑' x : ℤ × ℤ, (x.1 * ( z : ℂ) + x.2) ^ (- k : ℤ ) := by
  rw [← @Summable.sum_add_tsum_compl _ _ _ _ _ _ _ {(0 : ℤ × ℤ)} summablenonsense ]
  rw_mod_cast [compllemma]
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, zpow_neg, zpow_natCast, Finset.sum_singleton,
    Prod.fst_zero, Int.cast_zero, zero_mul, Prod.snd_zero, add_zero, right_eq_add, inv_eq_zero,
    pow_eq_zero_iff', true_and]
  apply kne0

lemma complofzero : (@Finset.toSet ℤ {0})ᶜ = {x : ℤ | x ≠ 0} := by
simp only [Finset.coe_singleton, ne_eq]
rfl

lemma sumsplit {k : ℕ} (kne0 : k ≠ 0) :
 ∑' x : ℤ × ℤ , (x.1 * ( z : ℂ) + x.2) ^ (- k : ℤ ) =
 ∑'(n : ℤ), (n : ℂ) ^ (-k : ℤ) + ∑'(n : {x : ℤ | x ≠ 0})(m : ℤ), (n * (z : ℂ) + m) ^ (- k : ℤ) := by
rw [Summable.tsum_prod summablenonsense]
simp only [zpow_neg, zpow_natCast]
rw [← @Summable.sum_add_tsum_compl _ _ _ _ _ _ _ {(0 : ℤ)} _ ]
simp only [Finset.sum_singleton, Int.cast_zero, zero_mul, zero_add]
rw [complofzero]
sorry --summable ignore for now...






--#min_imports
