import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ZetaValues

open EisensteinSeries CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open ModularFormClass
open Complex Topology Manifold
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


-- ## VERY USEFUL
--#check hasSum_zeta_nat




























def nonzero_pairs := {x : ℤ × ℤ | x ≠ 0}
def ℤxℤ' := {x : ℤ × ℤ // x ≠ 0}
def ℤxℤ := {x : ℤxℤ' | x.1 ≠ 0}

@[simp]
lemma ℤxℤisTop : IsTop ℤxℤ := by
  intro S
  simp only [Set.le_eq_subset]
  intro x h
  unfold ℤxℤ
  simp only [ne_eq, Set.mem_setOf_eq]
  push_neg
  unfold ℤxℤ' at S
 -- rw [Set.mem_setOf] at h
  sorry

instance morphbetween : nonzero_pairs ≃ ℤxℤ' where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by tauto
  right_inv := by tauto

@[simp]
lemma nonzeropairs_eq_ℤxℤ' : nonzero_pairs = morphbetween.invFun '' (ℤxℤ) := by
  simp_all only [Equiv.invFun_as_coe]
  ext x : 1
  simp_all
  obtain ⟨fst, snd⟩ := x
  apply Iff.intro
  · intro a
    simp_all only [exists_true_left]
    exact a
  · intro a
    obtain ⟨w, h⟩ := a
    simp_all only

@[simp]
lemma anotherequiv : nonzero_pairs = {fintoprod.toFun (fintoprod.invFun (x : ℤ × ℤ)) | x ≠ 0} := by
  simp [fintoprod]
  sorry

lemma anotherequiv2 {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
nonzero_pairs = fintoprod '' gammaSet 1 a := by sorry --convert gammaset_equiv ; sorry ; apply k

/-
lemma eisensteinSeries_as_SumOver_ℤ_ℤ {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
eisensteinSeries a k = ( fun z : ℍ => ∑' v : nonzero_pairs, 1 / ((v.1.1 : ℤ) * (z : ℂ) + v.1.2) ^ k) := by
  ext τ
  unfold eisensteinSeries eisSummand
  simp_all only [PNat.val_ofNat, Fin.isValue, zpow_neg, zpow_natCast]
  rw [anotherequiv2 a]
  symm
  convert @tsum_image ℂ _ _ _ _ fintoprod ((fun x ↦  1 / x.1 * τ + x.2) ^ k) (gammaSet 1 a)
  simp_all only [one_div, Fin.isValue, Pi.pow_apply]
  apply Iff.intro
  · intro a_1 hg
    simp_all only [fintoprod, Equiv.coe_fn_mk]
    norm_cast at a_1
    field_simp at a_1
    norm_cast at a_1
    norm_cast
    convert a_1
    · norm_cast
      sorry --weird coercion problem
    · sorry --same weird coercion problem
  · intro a_1
    sorry
  · sorry
  · sorry
  · apply k

def meq0 := { x : ℤ × ℤ | x ≠ 0 ∧ x.1 = 0}
def meq0' := { x : ℤxℤ' | x.1 = 0 }

instance anothermorph : meq0 ≃ meq0 where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by tauto
  right_inv := by tauto


@[simp]
instance meq0subsetofnonzeropairs : meq0 ⊆ nonzero_pairs := by
  intro v h
  obtain ⟨h₁, right⟩ := h
  intro h₂
  contradiction

@[simp]
lemma morphbetweeninj (S : Set ↑nonzero_pairs): Set.InjOn morphbetween S := by
  intro S_1 h S_2 h₁ h₂
  subst h₂
  obtain ⟨val, property⟩ := S_1
  obtain ⟨fst, snd⟩ := val
  rfl

@[simp]
lemma morphbetweenInvinj {S : Set ℤxℤ'} : Set.InjOn morphbetween.invFun S := by
  intro S_1 h S_2 h₁ h₂
  subst h₂
  obtain ⟨val, property⟩ := S_1
  obtain ⟨fst, snd⟩ := val
  rfl
-/
--lemma subtypevalsetoninj {S : @Set.Elem (ℤ × ℤ) Subtype.val '' (morphbetween.invFun '' ℤxℤ)} : Set.InjOn Subtype.val S := by
--  sorry

--@[simp]
--lemma morphbetweensubtypInv_inj {S : Set ℤxℤ'} : ↑(Subtype.val '' (morphbetween.invFun '' ℤxℤ))

--lemma sumsplitoff : ∑' v : nonzero_pairs, 1 / ((v.1.1 : ℤ) * (z : ℂ) + v.1.2) ^ k =
--  ∑' v : meq0, 1 / ((v.1.1 : ℤ) * (z : ℂ) + v.1.2) ^ k +
--   ∑' v : {x ∈ nonzero_pairs | x ∉ meq0}, 1 / ((v.1.1 : ℤ) * (z : ℂ) + v.1.2) ^ k := by
--  rw [nonzeropairs_eq_ℤxℤ']
 -- sorry
--  rw_mod_cast [tsum_image (fun v : (Subtype.val '' (morphbetween.invFun '' ℤxℤ)) =>  1 / (↑(↑v).1 * ↑z + ↑(↑v).2) ^ k ) _]



  --convert tsum_image ((fun (v : @Set.Elem (ℤ × ℤ) (Subtype.val '' (morphbetween.invFun '' ℤxℤ)))
  -- => 1 / ((@Int.cast ℂ AddGroupWithOne.toIntCast (↑v).1) * z + (@Int.cast ℂ AddGroupWithOne.toIntCast (↑v).2)) ^ k)) (_)
--
  --have h₁ : ∑' (v : ↑(Subtype.val '' (morphbetween.invFun '' ℤxℤ))), 1 / (↑(↑v).1 * ↑z + ↑(↑v).2) ^ k =
  --∑' (v : ↑(Subtype.val '' (morphbetween.invFun '' ℤxℤ))), 1 / (↑(↑v).1 * ↑z + ↑(↑v).2) ^ k := by
--    rw [tsum_image _ (morphbetweenInvinj)]

  --congr 1
  --simp_all only [Equiv.invFun_as_coe]
  --congr
  --convert Summable.tsum_subtype_add_tsum_subtype_compl _ meq0
  --all_goals try infer_instance


lemma sumsplitintwo : (fun z : ℍ => ∑' v : nonzero_pairs, 1 / ((v.1.1 : ℤ) * (z : ℂ) + v.1.2) ^ k) =
fun z:ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k:ℤ)) + ∑' y : ℕ, ∑' x : ℤ, ((y + 1)* (z : ℂ) + x) ^ (-(k:ℤ)) := by
  simp [nonzero_pairs]
  sorry

lemma eisensteinSeries_expand {k : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1:ℕ+)) :
eisensteinSeries a k  = fun z:ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k:ℤ)) + ∑' y : ℕ, ∑' x : ℤ, ((y + 1)* (z : ℂ) + x) ^ (-(k:ℤ)):= by
  ext z
  unfold eisensteinSeries eisSummand
  simp_all only [PNat.val_ofNat, Fin.isValue, zpow_neg, zpow_natCast]
  rw [gammaset_equiv]
  simp only [fintoprod]
  sorry
  sorry

theorem cotagent_Formula_HasSum: HasSum (fun (n : ℕ) => 1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by
  sorry

theorem cotagent_formula : ∑' (n : ℕ), (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) = (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by
  convert HasSum.tsum_eq cotagent_Formula_HasSum

lemma bernoulli_cotagent_Formula {k : ℕ } : HasSum (fun n : ℕ => (2 * π * i) ^ (2 * n) * (bernoulli' (2 * n)) / ((2 *n).factorial * z ^ (2 * n))) (π * z * cos (π * z)/ sin (π * z)):= by
  sorry

lemma cotagent_as_exp : (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) =
π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by sorry

lemma cotagent_as_exp1 :  π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) =
- π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by sorry

lemma cotagent_as_exp2 : - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) =
- π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by sorry

lemma cotagent_as_exp3 : (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ))  = - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by
  calc
    (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) = π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by apply cotagent_as_exp
    _  = - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by apply cotagent_as_exp1
    _  = - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by apply cotagent_as_exp2

-- ## Dylan's code
theorem cotangent_expansion (z : ℂ) (h : ∀ n : ℤ, z ≠ n) :
    π * cot (π * z) = 1/z + ∑' k : ℕ, (1/(z + (k + 1)) + 1/(z - (k + 1))) := by sorry

-- ## deriv_pow
lemma rw_of_cotangent_base_case :
 ∑' x : ℤ, ((z:ℂ) + (x : ℂ))^(- 2 : ℤ) =
 (2*π*i)^ 2* ∑' d : ℕ, (d + 1) * Complex.exp (2*π*i*(d + 1)*z) := by
  have h : ∀ z : ℍ, ∑' (n : ℕ), (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) = (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by intro τ ; convert cotagent_formula
  symm
  simp_rw [cotagent_as_exp3] at h
  have h₁ : ∀ z : ℍ, HasDerivAt (fun τ : ℂ => -π *i) 0 z := by sorry
  have h₂ {d : ℤ} : ∀ z : ℍ, HasDerivAt (fun z => 2 * π * i * (d + 1) * (z : ℂ))
    (2 * π * i * (d + 1)) z := by
    intro τ
    simp_rw [mul_comm ( 2 * ↑π * i * (d + 1))]
    apply hasDerivAt_mul_const ( 2 * ↑π * i * (d + 1))
  have h₂₁ {d : ℤ} : ∀ z : ℍ,HasDerivAt (fun z => cexp (2 * ↑π * i * (d + 1) * (z : ℂ)))
    ( cexp (2 * ↑π * i * (d + 1) * (z : ℂ)) * (2 * ↑π * i * (d + 1))) z := by
    intro τ
    apply HasDerivAt.cexp (h₂ τ)
  have h₃ {d : ℤ} : ∀ z : ℂ,HasDerivAt (fun z =>  2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (ofComplex z))) ((2 * ↑π * i) ^ 2 * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (ofComplex z : ℂ))) z := by sorry
  have h₄ {d : ℤ} : ∀ z : ℂ,HasDerivAt (fun z => (1 / ((z : ℂ)))) (1 / (z : ℂ) ^ 2) z := by sorry
  have h₅ : ∀ z : ℂ, HasDerivAt (fun z  => ∑' (n : ℕ), (1 / ((ofComplex z : ℂ) - (↑n + 1)))) (∑' (n : ℕ), (1 / ((ofComplex z : ℂ) + (↑n + 1)) ^ 2)) z := by sorry
  have h₆ : ∀ z : ℍ, HasDerivAt (fun z =>  ∑' (n : ℕ), (1 / ((z : ℂ) - (↑n + 1)) + 1 / ((z : ℂ) + (↑n + 1)))) (- ∑' (n : ℤ), (1 / ((z : ℂ) + (↑n))^2)) z := by sorry
  have h₇ : ∀ z : ℍ, HasDerivAt (fun z => -↑π * i - 2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (z : ℂ ))) (- (2 * ↑π * i) ^ 2 * ∑' (d : ℕ), (d + 1) * cexp (2 * ↑π * i * (↑d + 1) * ↑z)) z := by sorry
  have h₈ : ∀ z : ℍ, deriv (fun z  => ∑' (n : ℕ), (1 / ((ofComplex z : ℂ) - (↑n + 1)) + 1 / ((ofComplex z : ℂ) + (↑n + 1)))) z =
  deriv (fun z => -↑π * i - 2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * ↑(ofComplex z : ℂ))) z := by intro τ; congr; ext τ₁ ; simp_rw [h (ofComplex τ₁)]
  have h₉ : - ∑' (n : ℤ), (1 / ((z : ℂ) + (↑n))^2) = - (2 * ↑π * i) ^ 2 * ∑' (d : ℕ), (d + 1) * cexp (2 * ↑π * i * (↑d + 1) * z) := by rw [deriv_eq h₆] at h₈ ; symm ; rw [deriv_eq h₇] at h₈ ; simp only [ofComplex_apply] at h₈ ; rw [h₈]
  rw [neg_mul,neg_inj] at h₉
  simp_all only [one_div, neg_mul, forall_const, differentiableAt_const, zpow_neg]
  symm
  rw [← h₉]
  norm_cast

lemma cotagent_derivative_formula {k : ℕ} (hk : 2 ≤ k) :  ∀ z : ℍ, ((k - 1).factorial) * ∑' x : ℤ, 1/((z:ℂ) + (x : ℂ))^((k: ℤ)) =  (2*π*i)^ k * ∑' d : ℕ, (d + 1) ^ (k - 1) * Complex.exp (2*π*i*(d + 1)*z) := by
  induction' k with l ih
  linarith
  intro τ
  have h₃ : ∀ z : ℂ, HasDerivAt (fun z => ((l - 1).factorial : ℤ) * ∑' (x : ℤ), 1/((ofComplex z : ℂ) + x) ^ ((l : ℤ))) ( (l + 1 - 1).factorial * ∑' (n : ℤ), (1 / ((ofComplex z : ℂ) + (↑n))^(l + 1))) z := by sorry
  have h₄ : ∀ z : ℂ, HasDerivAt (fun z => (2 * π * i) ^ (l : ℤ) * ∑' (d : ℕ), ((d :ℤ) + 1) ^ (l - 1) * cexp (2 * π * i * ((d :ℤ) + 1) * (ofComplex z : ℂ))) ((2 * π * i) ^ (l + 1: ℤ) * ∑' (d : ℕ), ((d :ℤ) + 1) ^ (l) * cexp (2 * π * i * ((d :ℤ) + 1) * (ofComplex z : ℂ))) z := by sorry
  have deriv_ih : 2 ≤ l → (deriv (fun z => ((l - 1).factorial : ℤ) * ∑' (x : ℤ), 1/((ofComplex z : ℂ) + x) ^ ((l : ℤ)))) τ
   = deriv (fun z => (2 * π * i) ^ (l : ℤ) * ∑' (d : ℕ), ((d :ℤ) + 1) ^ (l - 1) * cexp (2 * π * i * ((d :ℤ) + 1) * (ofComplex z : ℂ))) τ := by
    intro hyp
    congr
    ext τ
    convert ih hyp (ofComplex τ)
  rw [deriv_eq h₃, deriv_eq h₄] at deriv_ih
  have deriv_ih : (fun x ↦  ↑(l + 1 - 1).factorial * ∑' (n : ℤ), 1 / (((ofComplex x): ℂ) + ↑n) ^ (l + 1)) τ =
    (fun x ↦ ( (2 * π * i) ^ (l +1: ℤ) * ∑' (d : ℕ), ((d :ℤ) + 1) ^ (l ) * cexp (2 * π * i * ((d :ℤ) + 1) * (ofComplex x : ℂ)))) τ := by apply deriv_ih ; sorry --have 2 ≤ l + 1
  simp only [add_tsub_cancel_right, ofComplex_apply, neg_mul, neg_inj] at deriv_ih
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one, Int.reduceNeg]
  norm_cast
  rw [deriv_ih]
  norm_cast

lemma rw_of_cotangent {k : ℕ } (hk : 2 ≤ k) :
 ∑' x : ℤ, ((z:ℂ) + (x : ℂ))^(-(k : ℤ)) =
 (2*π*i)^k* (Nat.factorial (k - 1) )^(-(1:ℤ)) * ∑' d : ℕ, (d + 1) ^ (k - 1) * Complex.exp (2*π*i*(d + 1)*z) := by
    have h₁ : ∀ z : ℍ, ((k - 1).factorial) * ∑' x : ℤ, 1/((z:ℂ) + (x : ℂ))^((k: ℤ)) =
    (2*π*i)^ k * ∑' d : ℕ, (d + 1) ^ (k - 1) * Complex.exp (2*π*i*(d + 1)*z) := by apply cotagent_derivative_formula hk
    have h₁ : ((k - 1).factorial) * ∑' x : ℤ, 1/((z:ℂ) + (x : ℂ))^((k: ℤ)) =
    (2*π*i)^ k * ∑' d : ℕ, (d + 1) ^ (k - 1) * Complex.exp (2*π*i*(d + 1)*z) := by
      apply h₁ z
    rw [mul_comm] at h₁
    symm at h₁
    rw [← @mul_inv_eq_iff_eq_mul₀,mul_comm, ← mul_assoc, @mul_comm ℂ _ (((k - 1).factorial)⁻¹ : ℂ)] at h₁
    symm at h₁
    simp_all only [zpow_natCast, one_div, zpow_neg, zpow_one]
    intro fakenews
    apply Nat.factorial_ne_zero (k -1)
    norm_cast at fakenews


theorem eisensteinSeries_eq_qExpansion {k : ℕ } (hk : 3 ≤ k) (a : Fin 2 → ZMod (1:ℕ+)) :
eisensteinSeries a k =  fun z:ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ,
∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, (m + 1)^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by
  rw [eisensteinSeries_expand hk a]
  ext (z: ℍ)
  have {y : ℕ}: ∑' x : ℤ, ((y + 1)* (z:ℂ) + (x : ℂ))^(-(k : ℤ)) = (2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, (d + 1) ^ (k -1 ) * Complex.exp (2*π*i*(d + 1)*(y + 1)*(z:ℂ)) := by
    have : ∃ s : ℍ, (s : ℂ) = (y + 1) * z := sorry
    rcases this with ⟨s, h⟩
    simp_rw [mul_assoc (2 * π * i * _)]
    rw [← h, rw_of_cotangent (by linarith)]
  simp only [this]
  have : ∑' (y : ℕ), ∑' (d : ℕ),(d + 1) ^(k -1)  * cexp (2*π*i*(d + 1)*(y + 1)*z) = ∑' (d : ℕ) (m : {s : ℕ | (s + 1) ∣ d + 1}), (m + 1)^(k-1) * cexp (2*π*i*(d + 1)*z) := sorry
  congr
  rw [tsum_mul_left]
  rw [this]


lemma isthisuseful {d : ℕ+} : (fun z ↦ Complex.exp (2*π*i*d*z)) = Function.Periodic.qParam (1/d) := by
  unfold Function.Periodic.qParam
  simp
  ring_nf
lemma isthisuseful2 {d : ℕ+} : Complex.exp (2*π*i*d*z) = Function.Periodic.qParam (1/d) z := by unfold Function.Periodic.qParam; simp; ring_nf
lemma isthisuseful3 {d : ℕ} : Complex.exp (2*π*i*d*z) = Function.Periodic.qParam (1/d) z := by unfold Function.Periodic.qParam; simp; ring_nf


lemma nnamme {d : ℕ+} : (fun z ↦ Complex.exp (2*π*i*d*z)) = Function.Periodic.cuspFunction (1/d : ℝ) (fun z ↦ z) := by
  rw [isthisuseful]
  ext x;
  unfold Periodic.cuspFunction Periodic.invQParam limUnder update
  simp
  refine eq_ite_iff.mpr ?_
  constructor
  constructor
  swap
  rw [lim]
  sorry
  sorry -- x = 0?


lemma eisenstein_sif_is {k : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1:ℕ+))  :
  eisensteinSeries_SIF a k = fun z:ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, ∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, (m + 1)^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by
  ext z
  rw [eisensteinSeries_SIF_apply, eisensteinSeries_eq_qExpansion hk]

lemma eisensteinSeries_MF_is {k : ℕ}  (hk : 3 ≤ (k:ℤ)) (a : Fin 2 → ZMod (1:ℕ+)) :
(eisensteinSeries_MF hk a).toFun = fun z : ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, ∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, (m + 1)^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by apply eisenstein_sif_is _ a ; norm_cast at hk

--THIS ONE IS BETTER
lemma eisensteinSeries_MF_is' {k : ℕ}  (hk : 3 ≤ (k:ℤ)) (a : Fin 2 → ZMod (1:ℕ+)) :
(eisensteinSeries_MF hk a) = fun z : ℍ ↦ 2 * ∑' x : ℕ, ((x +1 : ℂ)) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, ∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, (m + 1)^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by sorry -- apply eisenstein_sif_is _ a ; norm_cast at hk

open DirectSum
open scoped DirectSum

lemma bdd_at_infty_of_zero_at_infty (f : CuspForm Γ k) : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] A) := by
  intro A
  have h₁ : IsZeroAtImInfty (f ∣[k] A) := by
    apply CuspForm.zero_at_infty' f
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at h₁
  use 1
  apply h₁ _ _
  linarith

--they showed this already for ModularFormClass F Γ k with F π type
instance coe_CuspForm (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := by apply SlashInvariantForm.slash_action_eq'
  holo' := by apply CuspForm.holo'
  bdd_at_infty' := by apply bdd_at_infty_of_zero_at_infty

def coe_Hom' : CuspForm Γ k  →+ ModularForm Γ k where
  toFun := coe_CuspForm
  map_zero' := by rfl
  map_add' := by intro f g ; rfl

def coe_Hom : CuspForm Γ k →[ℂ] ModularForm Γ k where
  toFun := coe_Hom'
  map_smul' := by intro c f ; rfl

instance CuspForm_Subspace (Γ : Subgroup SL(2, ℤ)) (k : ℤ): Submodule ℂ (ModularForm Γ k) where
  carrier := Set.range coe_Hom
  add_mem' := by
    intro f g h h₁
    simp ; simp at h ; simp at h₁
    rcases h with ⟨f1, hf⟩ ; rcases h₁ with ⟨g1, hg⟩
    use (f1 + g1)
    rw [← hf,← hg]
    rfl
  zero_mem' := by simp ; use 0 ; rfl
  smul_mem' := by
    intro c f h
    simp ; simp at h
    rcases h with ⟨g, h₁⟩; use (c • g)
    simp ; rw [h₁]

lemma coee {f : CuspForm Γ k} :
coe_Hom f ∈ CuspForm_Subspace Γ k := by tauto

#check Classical.choose
lemma coe_hom_inj {f g : CuspForm Γ k} : (coe_Hom f = coe_Hom g) → f = g  := by intro h ; unfold coe_Hom coe_Hom' at *; sorry

lemma coe_hom_surj (f : ModularForm Γ k) (finCuspSub : f ∈ (CuspForm_Subspace Γ k)) :
∃ g : CuspForm Γ k, f = coe_Hom g := by
  have finCuspSub: f ∈ Set.range coe_Hom := by tauto
  have : (CuspForm_Subspace Γ k).carrier ⊆ Set.range coe_Hom := by rfl
  rw [Set.subset_range_iff_exists_image_eq] at this
  obtain ⟨t, tis⟩ := this
  have h₁: (CuspForm_Subspace Γ k).carrier = Set.range ⇑coe_Hom := rfl
  rw [h₁] at tis
  rw [← tis] at finCuspSub
  unfold Set.image at *
  have h₂ : ∃ a ∈ t, coe_Hom a = f := by apply finCuspSub
  obtain ⟨a, aint⟩ := h₂
  use a
  tauto

open Classical

noncomputable
instance isom (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
  (CuspForm Γ k) ≃ₗ[ℂ] CuspForm_Subspace Γ k where
    toFun := fun f => ⟨coe_Hom f , coee⟩
    map_add' := by intro x y; tauto
    map_smul' := by intro c x ; tauto
    invFun := fun ⟨f,finCusp⟩ => Exists.choose (coe_hom_surj f finCusp)
    left_inv := by
      intro x; simp;
      convert Classical.choose_eq _  ; constructor ;
      intro h₁ ; apply coe_hom_inj ; symm ; apply h₁
      intro h₁ ; rw [h₁]
    right_inv := by
      intro x ; simp
      obtain ⟨val, property⟩ := x
      simp_all only [Subtype.mk.injEq]


      --convert Classical.choose_eq _
      --simp
      --rw [Classical.choose_eq val]
      convert Classical.choose_eq _ ; simp ;
      refine ModularForm.ext_iff.mpr ?_
      intro τ

      sorry

-- ## Back to Eisenstein series


noncomputable def pow1 (k : ℕ)  := fun x : ℕ ↦ 2 * ((x : ℂ)) ^(-(k : ℤ))
noncomputable def pow2 (k : ℕ)  := fun x : ℕ ↦ (2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * (∑' m : {s : ℕ+ | (s : ℕ) ∣ x}, (m : ℕ)^(k-1))-- * 𝕢 x⁻¹ z-- Complex.exp (2*π*i*x*z)



lemma  zeta_HasSum_eq_bernoulli {k : ℕ} :
HasSum (pow1 k)  (- (2 * π * i) ^ k * (bernoulli' k) / (2 * Nat.factorial k)) := by sorry

lemma eisenstein_q_expansion {k : ℕ}  (hk : 3 ≤ (k:ℤ)) (a : Fin 2 → ZMod (1:ℕ+)) :
  qExpansion 1 (eisensteinSeries_MF hk a)  = .mk (pow1 k) +.mk ( pow2 k) := by
  unfold pow1 pow2 qExpansion SlashInvariantFormClass.cuspFunction
  unfold iteratedDeriv
  simp_all only [Nat.cast_one, PNat.val_ofNat, zpow_neg, zpow_natCast, Int.reduceNeg, zpow_one, Set.coe_setOf,
    Set.mem_setOf_eq]

  sorry
  --rw [eisensteinSeries_MF_is hk a] --maybe add another version of the above for this coercion?
  --unfold Periodic.cuspFunction --iteratedDeriv iteratedFDeriv
  --simp
  --ext n
  --simp only [iteratedDeriv_eq_iterate, Periodic.eq_cuspFunction]
  --unfold Periodic.cuspFunction
  --simp_rw [isthisuseful2,isthisuseful3]
  --sorry

lemma Eisenstein_series_ne_zero  {k : ℤ} {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
 qExpansion N (eisensteinSeries_MF hk a) ≠ 0 := by
  intro h
  rw [← PowerSeries.forall_coeff_eq_zero] at h
  have h₁ : PowerSeries.coeff ℂ 0 (qExpansion N (eisensteinSeries_MF hk a)) = 1 := by sorry --exact Eisenstein_0th_coeff_one N hk a
  rw [h 0] at h₁
  have : 0 = (1:ℂ) → False := by simp
  apply this ; apply h₁

lemma Eisenstein_series_not_zero {k : ℤ} {N : ℕ+} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
  eisensteinSeries_MF hk a ≠ 0 := by
  intro h
  have h₁ : qExpansion N (eisensteinSeries_MF hk a) = 0 := by
    rw [h]
    ext j
    simp
    unfold qExpansion
    simp
    right
    unfold SlashInvariantFormClass.cuspFunction

    --rw [Periodic.cuspFunction_zero_of_zero_at_inf]
    sorry
  apply Eisenstein_series_ne_zero
  exact h₁


theorem qExpansion_unique {f g : ModularForm Γ k} : qExpansion 1 f = qExpansion 1 g ↔ f = g := by sorry



lemma Zeta_function_eq {k : ℕ} : ∑' (x : ℕ), (x + 1: ℂ) ^ (-(k : ℤ)) = - (2 * π * i) ^ k * (bernoulli' k) / (2 * Nat.factorial k) := by
  sorry
lemma i_pow_k_of_even {k m: ℕ} (keven:  k = 2 * m) : i ^ k = (- 1) ^ m := sorry

lemma i_pow_k_of_even' {k m: ℕ} (keven:  k = 2 * m) : (2 * π * i) ^ k = (- 1) ^ m * (2 * π ) ^ k := sorry

theorem eisensteinSeries_apply_zero {k: ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+)):
    SlashInvariantFormClass.cuspFunction 0 (eisensteinSeries_MF hk a) 0 = - (2 * π * i) ^ k * (bernoulli' k) / (Nat.factorial k) := by
    sorry

lemma eq_CuspFunction {f : ModularForm Γ(1) k} : f.toFun = fun τ : ℍ ↦ SlashInvariantFormClass.cuspFunction 1 f (𝕢 1 τ) := sorry
--#check fun i, p i \smul continuous_linear_map.pi_algebra

open PowerSeries
noncomputable instance FPowerSeries_of_PowerSeries : ℂ⟦X⟧ →ₗ[ℂ] FormalMultilinearSeries ℂ ℂ ℂ where
  toFun ψ := fun m ↦ ψ.coeff ℂ m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  map_add' := by intro ψ φ ; simp ; ext m  ; ring_nf ; simp only [ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate, one_pow,
    smul_eq_mul, mul_one, FormalMultilinearSeries.add_apply, ContinuousMultilinearMap.add_apply]
  map_smul' := by
    intro c ψ ; simp_all only [map_smul, smul_eq_mul, RingHom.id_apply] ;
    ext m;
    simp_all only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul,
      FormalMultilinearSeries.smul_apply]
    ring_nf

@[simp]
lemma coe_inj :  Injective FPowerSeries_of_PowerSeries := by
  intro ψ φ h
  simp [FPowerSeries_of_PowerSeries] at h
  sorry

lemma modularForms_is_periodic {τ : ℂ} {f : ModularForm Γ(1) k} : f (ofComplex (τ + 1)) = f (ofComplex τ) := by sorry

lemma modularForms_is_differentiable {f : ModularForm Γ(1) k} : ∀ᶠ (z : ℂ) in I∞, DifferentiableAt ℂ (⇑f ∘ ↑ofComplex) z := by
  have : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f) := by apply f.holo'
  simp_rw [← mdifferentiableAt_iff_differentiableAt]
  convert this
  simp_all only [eventually_comap, eventually_atTop, ge_iff_le, iff_true]
  sorry

lemma modularForms_is_BoundedAtFilter {f : ModularForm Γ(1) k} : I∞.BoundedAtFilter (⇑f ∘ ↑ofComplex) := by sorry

--lemma eq_multilin : f = qExpansionFormalMultilinearSeries 1 f
lemma modularForm_TendsTo_Filter_at_zero {f : ModularForm Γ(1) k} (hyp : (coeff ℂ 0) (qExpansion 1 f) = 0 ): Filter.Tendsto f (Filter.comap UpperHalfPlane.im Filter.atTop) (𝓝 0) := by
      convert @Function.Periodic.tendsto_at_I_inf 1 (⇑f ∘ ofComplex) _ _ _ _
      · ext F
        constructor
        · intro h
          simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
            using (h).comp tendsto_comap_im_ofComplex
        · intro h₁ s h₂
          obtain ⟨t, h₃⟩ := h₁ h₂
          use t
          simp_all only [Nat.cast_one, mem_atTop_sets, ge_iff_le, true_and]
          obtain ⟨left, right⟩ := h₃
          obtain ⟨w, h_1⟩ := left
          convert right
          simp_all only [coeff_zero_eq_constantCoeff, iff_true]
          intro r h₃

          simp_all only [Set.mem_preimage]
          refine Set.mem_preimage.mp ?_
          have thing: (r : ℂ)  ∈ (Complex.im ⁻¹' t) := by apply h₃
          have thing1  : (r : ℂ) ∈ ⇑f ∘ ↑ofComplex ⁻¹' s := by apply right; convert thing
          convert thing1
          simp_all only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, Set.mem_preimage, coe_im,
            comp_apply, ofComplex_apply]
      · unfold qExpansion at hyp
        simp_all only [coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
        unfold SlashInvariantFormClass.cuspFunction at hyp
        convert hyp
        simp_all only [Nat.cast_one]
        simp_all only [Nat.cast_one]
      · simp
      · simp_all only [coeff_zero_eq_constantCoeff, Nat.cast_one, Periodic, ofReal_one, comp_apply]
        intro x
        apply modularForms_is_periodic
      · apply modularForms_is_differentiable
      · apply modularForms_is_BoundedAtFilter

theorem zeroAtInfty_iff_CuspForm {f : ModularForm Γ(1) k} : (∀ A : SL(2, ℤ), IsZeroAtImInfty (f.toFun ∣[(k : ℤ)] A)) ↔ (qExpansion 1 f).coeff ℂ 0 = 0 := by
  constructor
  · intro h
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul]
    unfold IsZeroAtImInfty ZeroAtFilter at h
    unfold SlashInvariantFormClass.cuspFunction
    apply Periodic.cuspFunction_zero_of_zero_at_inf
    simp
    simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
    using (h 1).comp tendsto_comap_im_ofComplex
  · intro h
    have cloneh : (coeff ℂ 0) (qExpansion 1 f) = 0 := h
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] at h
    intro A
    rw [f.slash_action_eq' A]
    unfold SlashInvariantFormClass.cuspFunction at h
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne] at h
    unfold IsZeroAtImInfty
    simp_all only [Nat.cast_one, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe]
    unfold ZeroAtFilter atImInfty
    convert modularForm_TendsTo_Filter_at_zero cloneh
    simp only [qExpansion, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] at cloneh
    rw [Gamma_one_top]
    simp only [Subgroup.mem_top]


--consider deleting this
lemma lemma1 {f g : ModularForm Γ(1) k} {h : qExpansion 1 f = qExpansion 1 g}:  qExpansionFormalMultilinearSeries 1 f = qExpansionFormalMultilinearSeries 1 g := by
      unfold qExpansionFormalMultilinearSeries
      rw [h]

lemma lemma2 {f g : ModularForm Γ(1) k} {h : qExpansion 1 f = qExpansion 1 g}: HasFPowerSeriesOnBall (SlashInvariantFormClass.cuspFunction 1 g) (qExpansionFormalMultilinearSeries 1 f) 0 1 := by
      rw [lemma1]
      apply hasFPowerSeries_cuspFunction 1 g
      apply h

theorem qExpansion_congr {f g : ModularForm Γ(1) k}: qExpansion 1 f = qExpansion 1 g  ↔ ∀ n : ℕ, (qExpansion 1 f).coeff ℂ n • 𝕢 1 z ^ n = (qExpansion 1 g).coeff ℂ n • 𝕢 1 z ^ n := by
  constructor
  · intro h n
    simp only [smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
    left
    rw [h]
  · intro h
    ext n
    simp only [smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq] at h
    have : 𝕢 1 ↑z ≠ 0 := by
      intro h₁
      unfold Periodic.qParam at h₁
      simp_all only [ofReal_one, div_one, exp_ne_zero]
    have : (coeff ℂ n) (qExpansion 1 f) = (coeff ℂ n) (qExpansion 1 g) := by
      convert h n
      simp_all only [false_and, or_false, ne_eq]
    apply this






lemma obvsthing {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) ((eisensteinSeries_MF hk a) z) := by
 convert hasSum_qExpansion 1 (eisensteinSeries_MF hk a) z
 norm_cast

lemma obvsthing' {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m) (hq : ‖q‖ < 1) :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • q ^ n) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
 apply hasSum_qExpansion_of_abs_lt
 apply hq

lemma obvsthing'' {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (hq : ‖q‖ < 1) :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z)) := by
have : SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z) = SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 (1:ℕ) z) := by
  simp only [PNat.val_ofNat, Nat.cast_one]
rw [this]
rw [SlashInvariantFormClass.eq_cuspFunction 1 (eisensteinSeries_MF hk a) z]
apply obvsthing hk a keven

lemma obvsthing4 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
(- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k
  + (2 * π * i) ^ k * (k - 1).factorial ^ (-(1 : ℤ)) *
   ∑' (d : ℕ) (m : {s | s + 1 ∣ d + 1}), ((m : ℂ)  + 1) ^ (k - 1) • 𝕢 1 z ^ (d + 1:ℕ) )=
    ∑' n : ℕ, (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n := by
  sorry

noncomputable def eisensteincoeff {k : ℕ} : ℕ → ℂ :=
  fun n => if n = 0 then (- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k)
  else (2 * π * i) ^ k * (k - 1).factorial ^ (-(1 : ℤ)) * ∑' (m : {s | s + 1 ∣ n }), ((m: ℂ) + 1) ^ (k - 1)

lemma eisensteinSeries_is_tsum_eisensteincoeff {k m : ℕ} (hk : 3 ≤ (k : ℤ)) --here we use all the tsum stuff above
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 eisensteinSeries_MF hk a z = (∑' (n : ℕ), @eisensteincoeff k n • 𝕢 1 z ^ n) := by
  rw [eisensteinSeries_MF_is']
  have :   ∑' (n : ℕ), @eisensteincoeff k n • 𝕢 1 ↑z ^ n = @eisensteincoeff k 0 +
  ∑' (n : ℕ), @eisensteincoeff k (n + 1) • 𝕢 1 ↑z ^ (n + 1):= by
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
    have : @eisensteincoeff (2*m) 0 =  ∑ «i» ∈ Finset.range 1, @eisensteincoeff (2*m) «i» := by
      simp only [Finset.range_one, Finset.sum_singleton]
    symm
    rw [this]
    have : ∑ «i» ∈ Finset.range 1, @eisensteincoeff (2*m) «i» = ∑ «i» ∈ Finset.range 1, @eisensteincoeff (2*m) «i» * 𝕢 1 z ^ «i» := by simp only [Finset.range_one,
      Finset.sum_singleton, pow_zero, mul_one]
    rw [this]
    have :  ∑' (n : ℕ), @eisensteincoeff (2*m) (n + 1) * 𝕢 1 ↑z ^ (n +1)  =  ∑' («i» : ℕ), @eisensteincoeff (2*m) («i» + 1) * 𝕢 1 ↑z ^ («i» +1 ) := by rfl
    rw [this]
    have summablehyp:  Summable (fun «i» => @eisensteincoeff (2*m) «i» * 𝕢 1 ↑z ^ «i») := by sorry
    rw [Summable.sum_add_tsum_nat_add 1 summablehyp]
  rw [this]
  unfold eisensteincoeff
  simp only [zpow_neg, zpow_natCast, Int.reduceNeg, zpow_one, Set.coe_setOf, Set.mem_setOf_eq,
    ↓reduceIte, neg_mul, Nat.add_eq_zero, one_ne_zero, and_false, smul_eq_mul]
  sorry --annoying compututations


lemma eisensteincoeff_zeroeq {k : ℕ} : @eisensteincoeff k 0 = - (2 * π * i) ^ k * (bernoulli' k) / (Nat.factorial k) := by
  rfl

lemma eisensteincoeeff_eq {k : ℕ} (n : ℕ) (ngeq0 : n > 0) : @eisensteincoeff k n = (2 * π * i) ^ k * (k - 1).factorial ^ (-(1 : ℤ)) * ∑' (m : {s | s + 1 ∣ n }), ((m : ℂ)+ 1 )^ (k - 1) := by
  unfold eisensteincoeff
  simp_all only [gt_iff_lt, neg_mul, Int.reduceNeg, zpow_neg, zpow_one, Set.coe_setOf, Set.mem_setOf_eq,
    ite_eq_right_iff]
  intro a
  subst a
  simp_all only [lt_self_iff_false]

lemma sillylemma {k : ℕ}:  2 * (-(2 * ↑π * i) ^ k * ↑(bernoulli' k) / (2 * ↑k.factorial)) =
- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k := by field_simp; ring_nf

lemma eisensteinSeries_is_tsum_eisensteincoeff' {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m):
 eisensteinSeries_MF hk a z = (∑' (n : ℕ), @eisensteincoeff k n • cexp (2 * π * i * z) ^ n) := by
  rw [eisensteinSeries_MF_is', Zeta_function_eq]
  have : (2 * ↑k.factorial : ℂ) ≠ 0 := by norm_num ; apply Nat.factorial_ne_zero
  rw [sillylemma, ← @eisensteincoeff_zeroeq k]
  simp_rw [← smul_eq_mul]
  rw [← Summable.tsum_const_smul]
  simp_rw [smul_eq_mul]
  --simp_rw [← eisensteincoeeff_eq _ (by linarith)]
  sorry
  sorry

theorem TendstoUniformlyLocally_of_EisensteinSeries_qExpansion
{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)
: TendstoLocallyUniformly (fun (s : Finset (ℕ)) ↦ (fun z : ℍ ↦ (∑ x ∈ s, @eisensteincoeff k x * (𝕢 1 z ^ x))))
(fun z => eisensteinSeries a k z) Filter.atTop := by
  sorry

theorem eisensteincoeff_isSummable (q : ℂ) {k m: ℕ } (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
Summable ( fun n => @eisensteincoeff k n * q ^ n  ) := by
  rw [← summable_norm_iff]

  sorry

theorem qexpansioneisensteincoeff_isSummableover𝕢 (z : ℍ) {k m: ℕ } (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
Summable ( fun n =>(qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n ) := by
  --rw [← summable_norm_iff]
  sorry -- cuspfunction should be used I think

theorem qexpansioneisensteincoeff_isSummable (q : ℂ) {k m: ℕ } (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
Summable ( fun n =>(qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • q ^ n ) := by
  --rw [← summable_norm_iff]
  sorry -- cuspfunction should be used I think

lemma sufficestoshowtsumseq_Eisenstein {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (@eisensteincoeff k n • 𝕢 1 z ^ n)) ((eisensteinSeries_MF hk a) z) := by
  rw [Summable.hasSum_iff]
  rw [eisensteinSeries_is_tsum_eisensteincoeff']
  congr
  unfold Periodic.qParam
  field_simp
  apply keven
  apply eisensteincoeff_isSummable (𝕢 1 z) hk a keven

lemma tsums_equal {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) :
∑' (n : ℕ), @eisensteincoeff k n • 𝕢 1 z ^ n = ∑'(n : ℕ),( (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) := by
  rw [HasSum.tsum_eq (sufficestoshowtsumseq_Eisenstein hk a keven), HasSum.tsum_eq (obvsthing hk a keven) ]

-- ## Dylan's Code
theorem interchange_limit_sum_of_dominated_convergence {α: Type*} [RCLike α] {f: ℕ → ℕ → α} {M: ℕ → ℝ} {f_lim: ℕ → α}
  (h_lim: ∀ k, Tendsto (f k ·) atTop (𝓝 (f_lim k)))
  (h_bound: ∀ k, ∀ n, ‖f k n‖ ≤ M k)
  (h_M_summable: Summable M)
  : Tendsto (∑' k, f k ·) atTop (𝓝 <| ∑' k, f_lim k)
:= by sorry

open Periodic

lemma filtercomp_eisenstein (x : ℂ) {k : ℕ} {n : ℕ} :
 @eisensteincoeff k n * 𝕢 1 x ^ n ≠ @eisensteincoeff k n * 0 := by sorry

lemma eisen_lim  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) (n : ℕ) ( nge0 : n > 0):
Tendsto (fun z ↦ @eisensteincoeff k n * 𝕢 1 ↑z ^ n) I∞ (𝓝[≠] (@eisensteincoeff k n * 0)) := by
have hh : 0 < 1 := by linarith
refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q ↦ @filtercomp_eisenstein _ k _)
apply Filter.Tendsto.const_mul
rw [tendsto_zero_iff_norm_tendsto_zero]
--simp only [norm_qParam]
--apply (tendsto_comap'_iff (m := fun y ↦ Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
--refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
--simpa using Real.pi_pos
sorry

lemma eisen_bounded  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) (n : ℕ):
∀ x : ℂ, ‖@eisensteincoeff k n * 𝕢 1 x ^ n‖ ≤ ‖@eisensteincoeff k n‖ := by  sorry

lemma eisen_summable {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) :
Summable fun n => ‖@eisensteincoeff k n‖  := by sorry

theorem partial_sum_tendsto {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) (n : ℕ) ( nge0 : n > 0):
Tendsto (fun z ↦ ∑ «i» ∈ Finset.range n, @eisensteincoeff k «i» * 𝕢 1 ↑z ^ «i») I∞ (𝓝 (@eisensteincoeff k 0)) := by
  have : @eisensteincoeff k 0 = @eisensteincoeff k 0 + 0 := by symm ; rw [add_zero]
  rw [this]
  have eis_lim  : ∀ m ∈ Finset.range n, Tendsto (fun z ↦ @eisensteincoeff k m * 𝕢 1 z ^ m)
    I∞ (𝓝 (@eisensteincoeff k m * 0)) := by sorry
  have : (fun z ↦ ∑ «i» ∈ Finset.range n, @eisensteincoeff k «i» * 𝕢 1 z ^ «i») = fun z ↦( @eisensteincoeff k 0 + ∑ «i» ∈ Finset.range n \ {0}, @eisensteincoeff k «i» * 𝕢 1 z ^ «i»):= by sorry--Finset.sum_eq_add
  rw [this]
  apply Filter.Tendsto.const_add
  have : 0 = @eisensteincoeff k n * 0 := by simp only [mul_zero]
  have : 0 = ( ∑ «i» ∈ Finset.range n \ {0}, @eisensteincoeff k «i» * 0) := by simp only [mul_zero,
    Finset.sum_const_zero]
  rw[this]
  apply tendsto_finset_sum
  intro j hj
  refine eis_lim j ?_
  sorry --finsets dont exactly match

lemma uniformcontinuity  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m)  :
TendstoUniformly (fun (N : ℕ) (x : ℂ) => ∑ n ∈ Finset.range N, @eisensteincoeff k n * 𝕢 1 x ^ n)
 (fun (x : ℂ) => ∑' (n : ℕ), @eisensteincoeff k n * 𝕢 1 x ^ n) Filter.atTop := by
  apply tendstoUniformly_tsum_nat (eisen_summable hk a keven) (eisen_bounded hk a keven )-- ?_

theorem tsumeisensteincoeff_tendsto {z : ℍ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) :
Tendsto (fun z => ∑' (n : ℕ), @eisensteincoeff k n * 𝕢 1 z ^ n) I∞ (𝓝[≠] @eisensteincoeff k 0) := by
  have h : HasSum (fun n => @eisensteincoeff k n * 𝕢 1 z ^ n) (eisensteinSeries_MF hk a z)  := by sorry
  rw [Summable.hasSum_iff_tendsto_nat (eisensteincoeff_isSummable (𝕢 1 z) hk a keven)] at h

  --apply interchange_limit_sum_of_dominated_convergence
  --have : Tendsto (fun z ↦ ∑' (n : ℕ), eisensteincoeff n * 𝕢 1 z ^ n) I∞ (𝓝 ∑' (n : ℕ), eisensteincoeff n * 𝕢 1 z ^ n ) :=
  --apply tendstoUniformly_tsum_nat
 -- simp_rw [Summable.tsum_eq_zero_add (eisensteincoeff_isSummable (𝕢 1 z) hk a keven)]
  sorry

--TendstoUniformlyOnFilter

#check Summable.tsum_eq_zero_add
lemma coeffzeroagree {z : ℍ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) :
  @eisensteincoeff k 0 = (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 := by
    have h : ∑' (n : ℕ), @eisensteincoeff k n • 𝕢 1 z ^ n = ∑'(n : ℕ),( (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) := by apply tsums_equal hk a keven
    simp_rw [smul_eq_mul] at h
    rw [Summable.tsum_eq_zero_add (eisensteincoeff_isSummable (𝕢 1 z) hk a keven)] at h
    simp_rw [← smul_eq_mul] at h
    rw [Summable.tsum_eq_zero_add (qexpansioneisensteincoeff_isSummable (𝕢 1 z) hk a keven) ] at h

lemma cuspfunctioneisensteinastsum {q : ℂ}{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) (qnorm : ‖q‖ < 1) :
cuspFunction 1 (⇑(eisensteinSeries_MF hk a) ∘ ↑ofComplex) q =  ∑' (n : ℕ), (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 *  q ^ n := by
  symm
  apply HasSum.tsum_eq
  convert obvsthing' hk a keven qnorm
  sorry
  sorry

lemma eisensteinSeriesCuspfunction_tendso_eisensteincoeff0 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) :
Tendsto (cuspFunction 1 ((eisensteinSeries_MF hk a) ∘ ofComplex)) (𝓝[≠] 0) (𝓝 (@eisensteincoeff k 0)) := by sorry

lemma obvsthing8 {q : ℂ}{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (hq : ‖q‖ < 1):
 HasSum (fun n : ℕ ↦ (@eisensteincoeff k n • q ^ n)) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
  rw [Summable.hasSum_iff]
  symm
  by_cases h : q ≠ 0
  · unfold SlashInvariantFormClass.cuspFunction
    rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    have : ((eisensteinSeries_MF hk a) ∘ ↑ofComplex) (Periodic.invQParam ((1 : ℕ): ℝ) q) =
       (eisensteinSeries_MF hk a) (ofComplex (Periodic.invQParam ((1 : ℕ): ℝ) q) ) := by
       subst keven
       simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_one, comp_apply]
    rw [this]
    simp only [Nat.cast_one]
    rw [eisensteinSeries_is_tsum_eisensteincoeff' hk a keven]
    field_simp
    congr
    ext n
    subst keven
    simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_one, comp_apply, mul_eq_mul_left_iff]
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]
    left
    have : cexp (2 * ↑π * i * (ofComplex (Periodic.invQParam 1 q))) ^ n = 𝕢 1 (ofComplex (Periodic.invQParam 1 q)) ^ n := by
      unfold Periodic.qParam
      field_simp
    --unfold Periodic.invQParam
    rw [this]
    push_neg at h
    have hh : (1 : ℝ)≠ 0 := by simp only [ne_eq, one_ne_zero, not_false_eq_true]
    have fact1 : ofComplex (Periodic.invQParam 1 q) = Periodic.invQParam 1 q := by
      simp_all only [ne_eq, one_ne_zero, not_false_eq_true]
      sorry/- ?-/
    rw [fact1]
    rw [Periodic.qParam_right_inv hh h]
    apply h
  · push_neg at h
    rw [h]
    unfold SlashInvariantFormClass.cuspFunction
    rw_mod_cast [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne 1 ((eisensteinSeries_MF hk a) ∘ ↑ofComplex)]
    simp only [PNat.val_ofNat, Nat.cast_pow, CharP.cast_eq_zero, smul_eq_mul]
    refine Tendsto.limUnder_eq ?_
    rw [Summable.tsum_eq_zero_add]
    simp only [pow_zero, mul_one, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, tsum_zero, add_zero]
    apply eisensteinSeriesCuspfunction_tendso_eisensteincoeff0 hk a keven
    sorry --silly thing
  · apply eisensteincoeff_isSummable q hk a keven

lemma HasSumforCuspFunctionover_𝕢 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 HasSum (fun n : ℕ ↦ (@eisensteincoeff k n • 𝕢 1 z ^ n)) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z)) := by
  rw [Summable.hasSum_iff]
  symm
  convert SlashInvariantFormClass.eq_cuspFunction 1 (eisensteinSeries_MF hk a) z
  symm
  simp only [Nat.cast_one]
  rw [eisensteinSeries_is_tsum_eisensteincoeff' hk a keven]
  unfold Periodic.qParam
  field_simp
  apply eisensteincoeff_isSummable (𝕢 1 z) hk a keven


lemma obvsthing9 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) (∑' (n : ℕ), @eisensteincoeff k n * 𝕢 1 z ^ n) := by
  unfold Periodic.qParam
  simp only [PNat.val_ofNat, ofReal_one, div_one, smul_eq_mul]
  convert @eisensteinSeries_is_tsum_eisensteincoeff' z k m hk a keven
  ext  x
  subst keven
  simp_all only [PNat.val_ofNat]
  apply Iff.intro
  · intro a_1
    sorry
  · intro a_1
    subst a_1
    sorry

open SlashInvariantFormClass

noncomputable def eisensteinFormalMultilinearSeries {k : ℕ} : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun m ↦ @eisensteincoeff k m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ

lemma hasFPowerSeries_eisen  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)  :
    HasFPowerSeriesOnBall (cuspFunction 1 (eisensteinSeries_MF hk a)) (@eisensteinFormalMultilinearSeries k) 0 1 := by
    have h₁ : 1 ≤ ((@eisensteinFormalMultilinearSeries k)).radius := by sorry
    have h₂ :  (0 : ENNReal) < 1 := by simp
    refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simp only [eisensteinFormalMultilinearSeries]
    simpa [eisensteinFormalMultilinearSeries] using (obvsthing8 hk a keven hy)

theorem EisensteinserieshasFPsum  {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)(hq : ‖q‖ < 1) :
 cuspFunction 1 (eisensteinSeries_MF hk a) q = (@eisensteinFormalMultilinearSeries k).sum q := by
  apply HasFPowerSeriesOnBall.unique (hasFPowerSeries_eisen hk a keven )
  convert FormalMultilinearSeries.hasFPowerSeriesOnBall (@eisensteinFormalMultilinearSeries k) _
  sorry --small things like radius arguments left
  sorry
  sorry


lemma eisensteinseries_FpowerseriesOnBall_difference_hassum {k m : ℕ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)
: HasFPowerSeriesOnBall ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 1 := by
  have h₁  :  1 ≤ ((@eisensteinFormalMultilinearSeries k) -
  (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))).radius := by sorry
  have h₂ :  (0 : ENNReal) < 1 := by simp
  refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
  apply HasSum.sub
  · rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simpa [eisensteinFormalMultilinearSeries] using (obvsthing8 hk a keven hy)
  · rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simpa [qExpansionFormalMultilinearSeries] using (obvsthing' hk a keven hy)

theorem eisensteinseries_FpowerseriesAt_difference_hassum {k m : ℕ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 HasFPowerSeriesAt ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 := by
  use 1
  apply eisensteinseries_FpowerseriesOnBall_difference_hassum hk a keven

theorem eisensteinSeries_Fpowerseries_difference_eq_zero {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 (@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0:= by
  apply HasFPowerSeriesAt.eq_zero
  rw [← sub_self (cuspFunction 1 (eisensteinSeries_MF hk a))]
  apply eisensteinseries_FpowerseriesAt_difference_hassum hk a keven

theorem TheFPSeriesagree {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  @eisensteinFormalMultilinearSeries k = qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) := by
  have h : (@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0 := by
    apply eisensteinSeries_Fpowerseries_difference_eq_zero hk a keven
  rw [← sub_eq_zero]
  apply h

lemma TheFPSeriesagree2 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)  :
 ∀ (n : ℕ), @eisensteinFormalMultilinearSeries k n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by
  apply FormalMultilinearSeries.ext_iff.mp
  apply TheFPSeriesagree hk a keven

theorem mkPiAlgebra_eq_iff (n : ℕ)  {z₁ z₂ : ℂ} :
    z₁ • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ  = z₂ • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ ↔
      z₁ = z₂ := by
    apply Iff.intro
    · intro a
      have h₁ :  (z₁ • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ) - (z₂ • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ)= 0 := by
        simp_all only [sub_self]
      rw [← sub_smul z₁ z₂ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ)] at h₁
      rw [smul_eq_zero] at h₁
      have h₂ : ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ ≠ 0 := by
        intro h₃
        simp [ContinuousMultilinearMap.mkPiAlgebraFin] at h₃
        unfold MultilinearMap.mkPiAlgebraFin at h₃
        sorry --not sure how to show this isnt zero
      have h₄ : ((z₁ - z₂ = 0) ∨ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ = 0)) ∧ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ ≠ 0) := by
        exact ⟨h₁, h₂⟩
      simp_all only [or_false, ne_eq, not_false_eq_true, true_or, true_and]
      symm
      calc
        z₂ = z₂ + 0 := by simp
        _ = z₂ + (z₁ - z₂) := by rw [h₁]
        _ = z₁ := by ring
    · intro a
      subst a
      simp_all only

theorem coeff_of_q_expansions_agree  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n = @eisensteincoeff k n := by
    have h₁ : @eisensteinFormalMultilinearSeries k n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by apply TheFPSeriesagree2 hk a keven
    unfold eisensteinFormalMultilinearSeries qExpansionFormalMultilinearSeries  at h₁
    rw [mkPiAlgebra_eq_iff] at h₁
    rw [h₁]

lemma Sumequivoverq {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  ∑' n : ℕ, @eisensteincoeff k n • 𝕢 1 z ^ n = ∑' n : ℕ, (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n := by
  unfold eisensteincoeff
  rw [← obvsthing4]
  rw [tsum_eq_zero_add']
  · simp only [↓reduceIte, neg_mul, pow_zero, smul_eq_mul, mul_one, Nat.add_eq_zero, one_ne_zero,
    and_false, Int.reduceNeg, zpow_neg, zpow_one, Set.coe_setOf, Set.mem_setOf_eq, add_right_inj,
    Nat.cast_mul, Nat.cast_ofNat]
    symm
    rw [← smul_eq_mul]
    symm
    simp_rw [← smul_eq_mul ((2 * ↑π * i) ^ k * (↑(k - 1).factorial)⁻¹) _]
    rw [← tsum_const_smul'' ((2 * ↑π * i) ^ k * (↑(k - 1).factorial)⁻¹ )]
    congr
    ext n
    rw [smul_mul_assoc]
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ofReal_eq_zero, false_or, I_ne_zero, or_false, ne_eq, _root_.inv_eq_zero, Nat.cast_eq_zero]
    left
    rw [mul_comm, ← smul_eq_mul (𝕢 1 ↑z ^ (n + 1))]
    symm
    rw [← tsum_const_smul'' (𝕢 1 ↑z ^ (n + 1))]
    simp_rw [mul_comm _ (𝕢 1 ↑z ^ (n + 1)),smul_eq_mul]
  · unfold Summable
    sorry
  · apply keven

  lemma obvsthing5' {z :ℍ }{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m):
(qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 = - (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k:= by
  have : @eisensteincoeff k 0 = (- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k) := rfl
  rw [← this]
  subst keven
  simp_all only [neg_mul, PNat.val_ofNat, coeff_zero_eq_constantCoeff]
  unfold qExpansion eisensteinSeries_MF eisensteinSeries_SIF eisensteinSeries
  simp_all only [PNat.val_ofNat, Nat.cast_mul, Nat.cast_ofNat, SlashInvariantForm.coe_mk, constantCoeff_mk,
    Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
  unfold eisSummand


  sorry

-- ## Stuff from before

lemma bernoulli_even_ne_zero (k : ℕ) {m : ℕ } (keven : k = 2 * m) : bernoulli' k ≠ 0 := by sorry

theorem Eisenstein_coeff_not_zero {k m : ℕ} (keven :  k = 2 * m) : @eisensteincoeff k 0 ≠ 0 := by
  unfold eisensteincoeff
  intro h
  simp_all only [Nat.cast_mul, Nat.cast_ofNat, neg_mul, zpow_neg, zpow_one, Set.coe_setOf,
    Set.mem_setOf_eq, ite_true, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, pow_eq_zero_iff',
    OfNat.ofNat_ne_zero, ofReal_eq_zero, false_or, I_ne_zero, or_false, ne_eq, Rat.cast_eq_zero,
    Nat.cast_eq_zero]
  repeat rw [← keven] at  h
  have h₁ : bernoulli' k ≠ 0 := by apply @bernoulli_even_ne_zero k m keven
  have h₂ : k.factorial ≠ 0 := by apply Nat.factorial_ne_zero
  simp_all only [or_false]
  have h₃ : π ≠ 0 := by apply Real.pi_ne_zero
  have h₃ : π = 0 := by apply h.1
  contradiction

lemma eisensteinSeries_not_zero_at_infty1 {q : ℂ}{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)
: ¬  ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a).toFun ∣[(k : ℤ)] A) := by
  rw [zeroAtInfty_iff_CuspForm]
  push_neg
  rw [coeff_of_q_expansions_agree 0 hk a keven]
  apply Eisenstein_coeff_not_zero keven


lemma eisensteinSeries_nin_CuspForm_Subspace {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  (eisensteinSeries_MF hk a) ∉ CuspForm_Subspace Γ(1) k := by
    intro h
    have h₁ : ∃ f : CuspForm Γ(1) k, eisensteinSeries_MF hk a = (isom Γ(1) k f : ModularForm Γ(1) k) := by
      have h₁₁: Surjective (isom Γ(1) k ) := by apply LinearEquiv.surjective
      unfold Surjective at h₁₁
      convert h₁₁ (⟨eisensteinSeries_MF hk a, h⟩)
      constructor
      · intro h₁₂
        simp_rw [h₁₂]
      · intro h₁₂
        simp_rw [h₁₂]
    obtain ⟨f, fiseis⟩ := h₁
    have h₂ : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a) ∣[(k : ℤ)] A) := by
      intro A
      rw [fiseis]
      have h₃ : ∀ B : SL(2,ℤ), IsZeroAtImInfty
        (⇑f.toSlashInvariantForm ∣[(k : ℤ)] B) := by apply f.zero_at_infty'
      simp_rw [isZeroAtImInfty_iff] at *
      intro ε εge0
      rcases h₃ A ε εge0 with ⟨δ, h₄⟩
      use δ
      intro z δlezIm
      have h₄ : ‖(⇑f.toSlashInvariantForm ∣[(k : ℤ)] A) z‖ ≤ ε := by apply h₄ z δlezIm
      convert h₄
    have h₃ : ¬ ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a) ∣[(k : ℤ)] A) := by apply eisensteinSeries_not_zero_at_infty1 hk a keven ; apply q
    contradiction

instance modformascuspform {f : ModularForm Γ(1) k} (vanishatcusp : (∀ (A : SL(2, ℤ)),
IsZeroAtImInfty ((f : ModularForm Γ(1) k) ∣[k] A))) : CuspForm Γ(1) k where
  toFun := f.toSlashInvariantForm
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  zero_at_infty' := vanishatcusp

lemma subspacelemma (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) (x : Subspace ℂ  (ModularForm Γ(1) k)) :
x ≤ (Submodule.span ℂ {eisensteinSeries_MF hk a}) ↔
∀ f ∈ x, ∃ c : ℂ, f = c • (eisensteinSeries_MF hk a) := sorry

lemma subspacelemma2  (x : Subspace ℂ  (ModularForm Γ(1) k)) :
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

lemma EisensteinSeries_in_EisensteinSubspace (c : ℂ) (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
c • (eisensteinSeries_MF hk a) ∈ Submodule.span ℂ {eisensteinSeries_MF hk a} := by
simp_all only [PNat.val_ofNat]
apply SMulMemClass.smul_mem
apply SetLike.mem_of_subset
· apply Submodule.subset_span
· simp_all only [Set.mem_singleton_iff]

lemma eisensteinSubspace_vanishing_is_zero (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+))
(f : ModularForm Γ(1) k) (finEis : f ∈  Submodule.span ℂ {eisensteinSeries_MF hk a})
(fvanishes : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((f : ModularForm Γ(1) k) ∣[k] A)) : f = 0 := sorry



theorem eisensteinSeries_comp_CuspForm (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
IsCompl (Submodule.span ℂ {eisensteinSeries_MF hk a}) (CuspForm_Subspace Γ(1) k) := by
  apply isCompl_iff.mpr
  constructor
  · unfold Disjoint
    intro x h₁ h₂
    rw [subspacelemma hk a] at h₁
    rw [subspacelemma2] at h₂
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

lemma idinj : Bijective idℂ := by apply idℂ.bijective
#check MulEquiv.refl

--« ;) »
lemma rank_ModulaForm_equiv_prod (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
Module.rank ℂ ((Submodule.span ℂ {eisensteinSeries_MF hk a}) × (CuspForm_Subspace Γ((1 : ℕ+)) k))
= Module.rank ℂ (ModularForm Γ(↑1) k) := by
  apply rank_eq_of_equiv_equiv idℂ (LinearEquiv.toAddEquiv (Submodule.prodEquivOfIsCompl
  (Submodule.span ℂ {(eisensteinSeries_MF hk a : (ModularForm Γ((1 : ℕ+)) k))})
  (CuspForm_Subspace Γ((1 : ℕ+)) k)  (eisensteinSeries_comp_CuspForm hk a) ) )
  apply idinj
  intro r m
  simp [idℂ]

lemma rank_eisensteinSubspace_one (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
 Module.rank ℂ ↥(Submodule.span ℂ {eisensteinSeries_MF hk a}) = 1 := by
  rw [rank_submodule_eq_one_iff]
  use eisensteinSeries_MF hk a
  constructor
  · unfold Submodule.span
    simp
  constructor
  · apply Eisenstein_series_not_zero
  · tauto

theorem dimen (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
Module.rank ℂ (ModularForm Γ(1) k) = Module.rank ℂ (CuspForm_Subspace Γ(1) k) + 1 := by
  rw [← rank_ModulaForm_equiv_prod hk a, rank_prod',add_comm, rank_eisensteinSubspace_one]
  rfl
