import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Topology.MetricSpace.Polish
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
  ∑' N : ℕ, 1/((N + 1): ℝ) ^ k * (eisensteinSeries a k z) = (∑' N : ℕ, 1/((N + 1): ℝ) ^ k) * (eisensteinSeries a k z) := by
    sorry --follows from uniform convergence

lemma eisensteinseries_splitoff_zeta_fun {k : ℕ} (a : Fin 2 → ZMod (1:ℕ+)) :
  (fun z : ℍ => ∑' N : ℕ, 1/((N + 1): ℝ) ^ k * (eisensteinSeries a k z)) =
 ( fun z => (∑' N : ℕ, 1/((N + 1): ℝ) ^ k) * (eisensteinSeries a k z)) := by
 ext τ
 rw [eisensteinseries_splitoff_zeta]

#check hasSum_zeta_nat
lemma DoubleSUm_relatesto_Bernoulli {k m: ℕ} (a : Fin 2 → ZMod (1:ℕ+)) (keven : k = 2 * m) (mne0 : m ≠ 0):
∑' x : {x : ℤ × ℤ | x ≠ 0}, (x.1.1 * (z : ℂ) + x.1.2) ^ (- k : ℤ ) =
   ((-1 : ℝ) ^ (k / 2 + 1) * (2 : ℝ) ^ (k - 1) * π ^ (k) *
        bernoulli k / (Nat.factorial (k))) * (eisensteinSeries a k z) := by
  rw [eisensteinSeries_as_SumOver_ℤ_ℤ a]
  have : ∑' (N : ℕ), 1 / ((N : ℂ) + 1) ^ k * eisensteinSeries a (↑k) z =
    ∑' (N : ℕ), 1 / ((N + 1) : ℝ)^ k * eisensteinSeries a (↑k) z := by norm_cast ; simp only [Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, one_div, ofReal_inv, ofReal_pow, ofReal_add, ofReal_natCast,
      ofReal_one]
  rw [this]
  rw [eisensteinseries_splitoff_zeta a]
  subst keven
  simp only [PNat.val_ofNat, Nat.cast_mul, Nat.cast_ofNat, ofReal_neg, ofReal_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, ofReal_ofNat,
    mul_eq_mul_right_iff]
  have : (∑' (N : ℕ), 1 / ((N : ℝ) + 1) ^ (2 * m)) = (∑' (N : ℕ), 1 / (N : ℝ) ^ (2 * m)) := by sorry
  rw [this]
  rw [HasSum.tsum_eq (hasSum_zeta_nat mne0)]
  left
  simp only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one, ofReal_ofNat,
    ofReal_ratCast, ofReal_natCast]


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

lemma complofzeroNat : (@Finset.toSet ℕ {0})ᶜ = {x : ℕ | x > 0} := by
simp_all only [Finset.coe_singleton, gt_iff_lt]
simp_rw [← Nat.ne_zero_iff_zero_lt]
rfl

lemma zerosetisrange1' : {0} =  (Finset.range 1) := by rfl

lemma zerosetisrange1 : @Finset.toSet ℕ {0} = @Finset.toSet ℕ (Finset.range 1) := by rfl

lemma simplifyingsumfurther {k l: ℕ} (kne0 : k ≠ 0) (keven : k = 2 * l):
∑'(n : ℤ), (n : ℂ) ^ (-k : ℤ) + ∑'(n : {x : ℤ | x ≠ 0})(m : ℤ), (n * (z : ℂ) + m) ^ (- k : ℤ)
=2 * ∑'(n : ℕ), (n : ℂ) ^ (-k : ℤ) + 2 * ∑'(n : ℕ)(m : ℤ), ((n + 1) * (z : ℂ) + m) ^ (- k : ℤ) := by
  subst keven
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at kne0
  have shouldbelemma : ∑'(n : ℤ), (n : ℂ) ^ (- 2 * l : ℤ) = 2 * ∑'(n : ℕ), (n : ℂ) ^ (- 2 * l : ℤ) := by
    rw [tsum_of_add_one_of_neg_add_one]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.reduceNeg, neg_mul, zpow_neg,
      Int.cast_zero, neg_add_rev, Int.cast_neg]
    field_simp
    ring_nf
    have opowzero: ((0 : ℂ) ^ ((l : ℤ) * 2))⁻¹ = 0 := by
      calc
        ((0 : ℂ)^ (l * 2))⁻¹ = (1 / 0) := by
          simp only [EuclideanDomain.div_zero,
          inv_eq_zero, pow_eq_zero_iff', ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, or_false,
          true_and] ; apply kne0
        _ =  0 := by rw [div_zero]
    rw [opowzero]
    simp only [add_zero]
    have : ∀ n : ℕ, ((-1 - (n : ℂ)) ^ ((l : ℤ) * 2))⁻¹ = ((1 + (n : ℂ)) ^ ((l : ℤ) * 2))⁻¹ := by
      intro j
      calc
        ((-1 - (j : ℂ)) ^ ((l : ℤ) * 2))⁻¹ = ((- 1) ^ ((l : ℤ) * 2) *(1 + (j : ℂ)) ^ ((l : ℤ) * 2))⁻¹ := by
          have : -(1 : ℂ) - j = -1 * 1 + -1 * j := by
            simp_all only [inv_eq_zero, mul_one, neg_mul, one_mul] ; rfl
          rw [this, ← mul_add]
          rw [mul_zpow (-1) (1 + (j : ℂ)) (l * 2)]
        _ = ((1 + (j : ℂ)) ^ ((l : ℤ) * 2))⁻¹ := by
          have : ∀ l₁ : ℕ, (-1 : ℂ) ^ ((l₁ : ℤ) * 2) = 1 := by
            intro l₁
            induction' l₁ with l ih
            simp only [CharP.cast_eq_zero, zero_mul, zpow_zero]
            calc
              (-1: ℂ) ^ (↑(l + 1) * 2) = (-1) ^ ((l : ℤ) * 2) * (-1) ^ (2) := by
                simp_all only [inv_eq_zero, even_two, Even.mul_left, Even.neg_pow, one_pow, mul_one]
              _ = 1 := by rw [ih] ; simp only [even_two, Even.neg_pow, one_pow, mul_one]
          rw [this l]
          simp only [one_mul]
    simp_rw [this]
    have : ∑' (n : ℕ), ((1 + (n : ℂ)) ^ ((l : ℤ) * 2))⁻¹ + ∑' (n : ℕ), ((1 + (n : ℂ)) ^ ((l : ℤ) * 2))⁻¹ =
      2* ∑' (n : ℕ), ((1 + (n : ℂ)) ^ ((l : ℤ) * 2))⁻¹ := by ring_nf
    rw [this]
    ring_nf
    have : 0 = (∑ n ∈ Finset.range 1, ((n : ℂ) ^ ((l : ℤ) * 2))⁻¹) * 2  := by simp_all only [inv_eq_zero,
      inv_inj, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [← zero_add ((∑' (n : ℕ), ((1 + n : ℂ) ^ ((l : ℤ) * 2))⁻¹) * 2)]
    rw [this]
    simp_rw [add_comm 1 (_ : ℂ)]
    norm_cast
    have : (∑ x ∈ Finset.range 1, ((x ^ (l * 2)) : ℂ )⁻¹) * 2 + (∑' (n : ℕ), ((((n + 1) : ℂ) ^ (l * 2)))⁻¹) * 2 =
     ∑ «i» ∈ Finset.range 1, ((«i» : ℂ) ^ (l * 2))⁻¹ * 2 + ∑' («i» : ℕ), (((«i» + 1) : ℂ) ^ (l * 2))⁻¹ * 2 := by
      simp only [Finset.range_one,
       Finset.sum_singleton, CharP.cast_eq_zero, add_right_inj] ; norm_cast ; exact Eq.symm tsum_mul_right
    rw_mod_cast [this, Summable.sum_add_tsum_nat_add]
    exact tsum_mul_right
    · sorry --skipping summable
    · sorry --skipping another summable
    · sorry --summable
  ring_nf at shouldbelemma
  ring_nf
  norm_cast
  norm_cast at shouldbelemma
  rw [shouldbelemma]
  simp only [Nat.cast_mul, Nat.cast_ofNat, zpow_neg, ne_eq, Set.coe_setOf, Set.mem_setOf_eq,
    add_right_inj]
  sorry --more lengthy computations like this one

-- ## use simplifying sum above
-- ## check k value here!
lemma eisensteinSeries_expand {z : ℍ} {k : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1:ℕ+)) :
(((-1 : ℝ) ^ (k / 2 + 1) * (2 : ℝ) ^ (k - 1) * π ^ k * (bernoulli k) / (Nat.factorial k)) * eisensteinSeries a k z) =
 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k:ℤ)) + ∑' y : ℕ, ∑' x : ℤ, ((y + 1)* (z : ℂ) + x) ^ (-(k:ℤ)):= by
  sorry

theorem cotagent_Formula_HasSum: HasSum (fun (n : ℕ) => 1 / ((z : ℂ) -
(n + 1)) + 1 / ((z : ℂ) + (n + 1))) (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by
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






--#min_imports
