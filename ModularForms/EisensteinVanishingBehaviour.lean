import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.ModularForms.Basic
import ModularForms.CuspFormSubspace
import Mathlib.NumberTheory.ModularForms.QExpansion
import ModularForms.EisensteinEvenWeight
import ModularForms.qExpansions_general


open EisensteinSeries CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open ModularFormClass Complex Topology Manifold
open PowerSeries SlashInvariantFormClass Periodic
open scoped Real MatrixGroups CongruenceSubgroup

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)
variable{N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
variable {z : ℍ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam
local notation "i" => Complex.I

/- This file is for showing that the eisenstein series q-expansion
  agrees with the one computed in the EisensteinEvenWeight file

  Then we can use this to show that the Eisenstein series are not
  in the Cusp form subspace as defined in the CuspFormSubspace file
-/


@[simp]
lemma qParam_has_bounded_norm {z : ℍ}: ‖𝕢 1 z‖ < 1 := by
  rw [norm_qParam]
  simp_all only [neg_mul, coe_im, div_one, Real.exp_lt_one_iff, Left.neg_neg_iff]
  have im_ge0: z.im > 0 := z.2
  have twopige0 : 2 * π > 0 := by
    simp_all only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    apply Real.pi_pos
  simp_all only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]

lemma qParam_has_bounded_norm_coe (z : ℍ): ‖𝕢 1 (z: ℂ)‖ < 1 := by
  simp

/- sanity check -/
lemma eisensteinseries_HasSum_generic {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n)
 ((eisensteinSeries_MF hk a) z) := by
 convert hasSum_qExpansion 1 (eisensteinSeries_MF hk a) z
 norm_cast

/- sanity check -/
lemma eisensteinSeries_HasSum_SI_generic_q {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ))
(a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m) (hq : ‖q‖ < 1) :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • q ^ n)
 (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
 apply hasSum_qExpansion_of_abs_lt
 apply hq

/- the above lemma, but specialised to 𝕢 -/
lemma eisensteinSeries_HasSum_SI_generic_𝕢 {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ))
(a : Fin 2 → ZMod (1 : ℕ+)) (keven :  k = 2 * m) :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n)
  (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z)) := by
have : SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z)
= SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 (1:ℕ) z) := by
  simp only [PNat.val_ofNat, Nat.cast_one]
rw [this]
rw [SlashInvariantFormClass.eq_cuspFunction 1 (eisensteinSeries_MF hk a) z]
apply eisensteinseries_HasSum_generic hk a keven

/- the coefficients of the q-expansion computed in EisensteinEvenWeight-/
noncomputable def eisensteincoeff' (k : ℕ) {m : ℕ} (keven : k = 2 * m) (mne0 : m ≠ 0)
: ℕ → ℂ :=
  fun n => if n = 0 then 2
  else (OurBernoulli m mne0)⁻¹ * (2 * (2 * π * i) ^ k) * (k - 1).factorial ^ (-(1 : ℤ))
  * ∑' (m : {s | s + 1 ∣ n }), ((m: ℂ) + 1) ^ (k - 1)

@[simp]
lemma eisensteincoeff'_at_zero (k : ℕ) {m : ℕ} (keven : k = 2 * m) (mne0 : m ≠ 0) :
  eisensteincoeff' k keven mne0 0 = 2 := by rfl

@[simp]
lemma eisensteincoeff'_nat_zero (k : ℕ) {m l: ℕ} (keven : k = 2 * m) (mne0 : m ≠ 0) (lne0 : l ≠ 0):
   eisensteincoeff' k keven mne0 l = (OurBernoulli m mne0)⁻¹ * (2 * (2 * π * i) ^ k) * (k - 1).factorial ^ (-(1 : ℤ))
  * ∑' (m : {s | s + 1 ∣ l }), ((m: ℂ) + 1) ^ (k - 1) := by
  unfold eisensteincoeff';
  subst keven
  simp_all only [ne_eq, ↓reduceIte, OurBenoullidef, inv_div, ofReal_div, ofReal_natCast, ofReal_mul, ofReal_pow,
    ofReal_neg, ofReal_one, ofReal_ofNat, ofReal_ratCast, Int.reduceNeg, zpow_neg, zpow_one, Set.coe_setOf,
    Set.mem_setOf_eq]

theorem eisensteinSeries_is_tsum_eisensteincoeff {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0){τ : ℍ}:
 eisensteinSeries_MF hk a τ = (∑' (n : ℕ), eisensteincoeff' k keven mne0 n • 𝕢 1 τ ^ n) := by
  rw [eisensteinSeries_MF_is hk a keven mne0]
  have :   ∑' (n : ℕ), eisensteincoeff' k keven mne0 n • 𝕢 1 ↑τ ^ n = eisensteincoeff' k keven mne0 0 +
  ∑' (n : ℕ), eisensteincoeff' k keven mne0 (n + 1) • 𝕢 1 ↑τ ^ (n + 1):= by
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
    simp_rw [← keven]
    have : eisensteincoeff' k keven mne0 0 =
     ∑ «i» ∈ Finset.range 1, eisensteincoeff' k keven mne0 «i» := by
      simp only [Finset.range_one, Finset.sum_singleton]
    symm
    rw [this]
    have : ∑ «i» ∈ Finset.range 1, eisensteincoeff' k keven mne0 «i» =
    ∑ «i» ∈ Finset.range 1, eisensteincoeff' k keven mne0 «i» * 𝕢 1 τ ^ «i» := by
      simp only [Finset.range_one,
      Finset.sum_singleton, pow_zero, mul_one]
    rw [this]
    have :  ∑' (n : ℕ), eisensteincoeff' k keven mne0 (n + 1) * 𝕢 1 ↑τ ^ (n +1)  =
     ∑' («i» : ℕ), eisensteincoeff' k keven mne0 («i» + 1) * 𝕢 1 ↑τ ^ («i» +1 )
     := by rfl
    rw [this]
    have summablehyp:  Summable (fun «i» => eisensteincoeff' k
    keven mne0 «i» * 𝕢 1 ↑τ ^ «i») := by sorry
    rw [Summable.sum_add_tsum_nat_add 1 summablehyp]
  rw [this, ourEisensteinSeries_normalised (by linarith) a keven mne0]
  rw [eisensteincoeff'_at_zero]
  congr ; rw [← smul_eq_mul,
  ← tsum_const_smul'' ((OurBernoulli m mne0)⁻¹ * (2 * (2 * π * i) ^ (2 * m))
  * (2 * m - 1).factorial ^ (-(1 : ℤ)) )]
  congr
  ext l
  rw [eisensteincoeff'_nat_zero k keven mne0 ]
  rw [smul_eq_mul] ; simp_rw [keven] ; unfold Periodic.qParam
  have : cexp (2 * ↑π * i * (τ : ℂ) / (1 : ℝ)) ^ (l + 1) =
  cexp (2 * ↑π * i * (l + 1) * ↑τ ) := by simp only [ofReal_one, div_one]; sorry
  rw [this] ; simp_rw [← smul_eq_mul _ (cexp (2 * ↑π * i * ((l : ℂ) + 1) * (τ : ℂ)))] ;
  rw [Summable.tsum_smul_const _ (cexp (2 * ↑π * i * ((l : ℂ) + 1) * (τ : ℂ)))]
  simp_rw [smul_eq_mul] ; symm ; rw [mul_assoc]; congr ; ext S ;
  have : (2 * m - 1 : ℕ) = 2 * (m : ℤ) -1 := by omega
  rw [← this] ; congr
  · sorry --summable
  · subst keven
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul, eisensteincoeff'_at_zero, ne_eq, Nat.add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, eisensteincoeff'_nat_zero, OurBenoullidef, inv_div, ofReal_div,
    ofReal_natCast, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one, ofReal_ofNat, ofReal_ratCast, Int.reduceNeg,
    zpow_neg, zpow_one, Set.coe_setOf, Set.mem_setOf_eq]

theorem eisensteinSeries_is_tsum_eisensteincoeff' {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0){τ : ℍ}:
 eisensteinSeries_MF hk a τ = (∑' (n : ℕ),
 eisensteincoeff' k keven mne0 n • cexp (2 * π * i * τ) ^ n) := by
  have : cexp (2 * π * i * τ) = 𝕢 1 τ := by
    rw [Periodic.qParam]
    subst keven
    simp_all only [ne_eq, Nat.cast_mul, Nat.cast_ofNat, ofReal_one, div_one]
  rw [this, eisensteinSeries_is_tsum_eisensteincoeff hk a keven mne0]

/- could exactly figure out how to show this using that other tsum is summable-/
theorem eisensteincoeff_isSummable {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)
 (q : ℂ) (hq : ‖q‖ < 1) :
Summable ( fun n => eisensteincoeff' k keven mne0 n * q ^ n  ) := by
  use (cuspFunction 1 (eisensteinSeries_MF hk a) q)
  refine HasSum.hasSum_of_sum_eq ?_ (eisensteinSeries_HasSum_SI_generic_q hk a keven hq)
  intro S
  sorry

theorem qexpansioneisensteincoeff_isSummable (q : ℂ) {k m: ℕ } (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
Summable ( fun n =>(qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • q ^ n ) := by
  --rw [← summable_norm_iff]
  sorry -- cuspfunction should be used I think

/- used to prove the theorem immediately below-/
lemma sufficestoshowtsumseq_Eisenstein {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)  :
 HasSum (fun n : ℕ ↦ (eisensteincoeff' k keven mne0 n • 𝕢 1 z ^ n)) ((eisensteinSeries_MF hk a) z) := by
  rw [Summable.hasSum_iff]
  rw [eisensteinSeries_is_tsum_eisensteincoeff' hk a keven mne0]
  congr
  unfold Periodic.qParam
  field_simp
  have : ‖𝕢 1 ↑z‖ < 1 := (by apply qParam_has_bounded_norm_coe z)
  apply eisensteincoeff_isSummable hk a keven mne0
  apply this

/- used to show that the tsums are equal at the top so that their-/
/- coefficients at zero agree-/
theorem tsums_equal {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0):
∑' (n : ℕ), eisensteincoeff' k keven mne0 n • 𝕢 1 z ^ n =
∑'(n : ℕ),( (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n) := by
  rw [HasSum.tsum_eq (sufficestoshowtsumseq_Eisenstein hk a keven mne0),
  HasSum.tsum_eq (eisensteinseries_HasSum_generic hk a keven) ]

lemma filtercomp_eisenstein {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)(x : ℂ)  :
 eisensteincoeff' k keven mne0 n * 𝕢 1 x ^ n ≠ eisensteincoeff' k keven mne0 n * 0 := by sorry

lemma eisensteincoeff'_lim  {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)
(n : ℕ) ( nge0 : n > 0):
Tendsto (fun z ↦ eisensteincoeff' k keven mne0 n * 𝕢 1 ↑z ^ n) I∞ (𝓝[≠]
(eisensteincoeff' k keven mne0 n * 0)) := by
have hh : 0 < 1 := by linarith
refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q ↦ @filtercomp_eisenstein _ k m hk a keven mne0 _)
apply Filter.Tendsto.const_mul
rw [tendsto_zero_iff_norm_tendsto_zero]
have {x : ℂ} : ‖((𝕢 1 x) ^ n)‖ = ‖𝕢 1 (n * x)‖ := by unfold qParam ; sorry
simp_rw [this]
simp only [norm_qParam]
--apply (tendsto_comap'_iff (m := fun y ↦ Real.exp (-2 * π * (n * y) / 1)) (range_im ▸ univ_mem)).mpr
--refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
--simpa using Real.pi_pos
sorry

-- ## Implementing that the limit as im.z → ∞
-- ## commutes with the infinite sum ∑ aₙ qⁿ
-- this goes nowhere for now...
-- dylan implemented code that could help, but specialised to something else
lemma eisen_bounded  {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)(n : ℕ):
∀ x : ℂ, ‖eisensteincoeff' k keven mne0 n * 𝕢 1 x ^ n‖ ≤ ‖eisensteincoeff' k keven mne0 n‖ := by  sorry

lemma eisen_summable {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
Summable fun n => ‖eisensteincoeff' k keven mne0 n‖  := by sorry

theorem partial_sum_tendsto {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)(n : ℕ) ( nge0 : n > 0):
Tendsto (fun z ↦ ∑ «i» ∈ Finset.range n, eisensteincoeff' k keven mne0 «i» * 𝕢 1 ↑z ^ «i») I∞ (𝓝 (eisensteincoeff' k keven mne0 0)) := by
  have : eisensteincoeff' k keven mne0 0 = eisensteincoeff' k keven mne0 0 + 0 := by symm ; rw [add_zero]
  rw [this]
  have eis_lim  : ∀ m ∈ Finset.range n, Tendsto (fun z ↦ eisensteincoeff' k keven mne0 m * 𝕢 1 z ^ m)
    I∞ (𝓝 (eisensteincoeff' k keven mne0 m * 0)) := by sorry
  have : (fun z ↦ ∑ «i» ∈ Finset.range n, eisensteincoeff' k keven mne0 «i» * 𝕢 1 z ^ «i») =
   fun z ↦( eisensteincoeff' k keven mne0 0 + ∑ «i» ∈ Finset.range n \ {0},
   eisensteincoeff' k keven mne0 «i» * 𝕢 1 z ^ «i»):= by sorry--Finset.sum_eq_add
  rw [this]
  apply Filter.Tendsto.const_add
  have : 0 = eisensteincoeff' k keven mne0 n * 0 := by simp only [mul_zero]
  have : 0 = ( ∑ «i» ∈ Finset.range n \ {0}, eisensteincoeff' k keven mne0 «i» * 0) := by simp only [mul_zero,
    Finset.sum_const_zero]
  rw[this]
  apply tendsto_finset_sum
  intro j hj
  refine eis_lim j ?_
  sorry --finsets dont exactly match

lemma uniformcontinuity  {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
TendstoUniformly (fun (N : ℕ) (x : ℂ) => ∑ n ∈ Finset.range N, eisensteincoeff' k keven mne0 n * 𝕢 1 x ^ n)
 (fun (x : ℂ) => ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 x ^ n) Filter.atTop := by
  apply tendstoUniformly_tsum_nat (eisen_summable hk a keven mne0) (eisen_bounded hk a keven mne0)-- ?_

theorem tsumeisensteincoeff_partial_tendsto {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) {z : ℍ} (N : ℕ):
Tendsto (fun z =>  ∑ n ∈ Finset.range N, eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n)
I∞ (𝓝[≠] eisensteincoeff' k keven mne0 0) := by
  sorry

theorem tsumeisensteincoeff_tendsto {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) {z : ℍ}:
Tendsto (fun z => ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n) I∞ (𝓝[≠] eisensteincoeff' k keven mne0 0) := by
  have h : HasSum (fun n => eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n) (eisensteinSeries_MF hk a z)  := by sorry
  rw [Summable.hasSum_iff_tendsto_nat (eisensteincoeff_isSummable hk a keven mne0 (𝕢 1 z) (by apply qParam_has_bounded_norm_coe z))] at h
  --apply Summable.tendsto_sum_tsum_nat
  --apply interchange_limit_sum_of_dominated_convergence
  --have : Tendsto (fun z ↦ ∑' (n : ℕ), eisensteincoeff n * 𝕢 1 z ^ n) I∞ (𝓝 ∑' (n : ℕ), eisensteincoeff n * 𝕢 1 z ^ n ) :=
  --apply tendstoUniformly_tsum_nat
 -- simp_rw [Summable.tsum_eq_zero_add (eisensteincoeff_isSummable (𝕢 1 z) hk a keven)]
  sorry

-- ## End of the limit attempt

/- the following theorems are used to show that the zero coefficients agree-/
theorem EventuallyEq_EisensteinSeries_atTop_im {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
 Filter.EventuallyEq (comap UpperHalfPlane.im atTop) ((fun z : ℍ => ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n))
((fun z : ℍ => ∑' (n : ℕ), (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n * 𝕢 1 z ^ n)) := by
unfold EventuallyEq
apply Eq.eventuallyEq
ext τ
convert tsums_equal hk a keven mne0

theorem EventuallyEqtsumeisensteincoeff {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
Filter.EventuallyEq (comap UpperHalfPlane.im atTop) ((fun z => ∑' (n : ℕ),
 eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n))
(fun z => eisensteincoeff' k keven mne0 0 ) := by sorry

theorem EventuallyEqtsumeisensteincoeff_qexpansion {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0)  :
Filter.EventuallyEq (comap UpperHalfPlane.im atTop) ((fun z => ∑' (n : ℕ),
 (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n * 𝕢 1 z ^ n))
(fun z => (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 ) := by sorry

theorem tsumeisensteincoeff_qexpansion_tendsto {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
Tendsto (fun z : ℍ  => ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n)
(comap UpperHalfPlane.im atTop) (𝓝 ((qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0)) := by
have : ∀ᶠ (x : ℍ) in comap UpperHalfPlane.im atTop,
  (fun z ↦ ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n) x =
    (fun z ↦ ∑' (n : ℕ), (coeff ℂ n) (qExpansion 1 (eisensteinSeries_MF hk a)) * 𝕢 1 z ^ n) x := by
      apply EventuallyEq_EisensteinSeries_atTop_im
refine @tendsto_nhds_of_eventually_eq ℂ _ ℍ ((qExpansion 1
 (eisensteinSeries_MF hk a)).coeff ℂ 0) (comap UpperHalfPlane.im atTop) (fun z ↦ ∑' (n : ℕ), eisensteincoeff' k keven mne0 n
 * 𝕢 1 z ^ n) ?_
--apply this
sorry

/- use the above theorems to prove this -/
lemma coeffzeroagree  {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
  eisensteincoeff' k keven mne0 0 = (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 := by
  have : Filter.EventuallyEq (comap UpperHalfPlane.im atTop) ((fun z =>
     eisensteincoeff' k keven mne0 0 )) (fun z => (qExpansion 1
      (eisensteinSeries_MF hk a)).coeff ℂ 0):= by
    have :  ∀ᶠ (x : ℍ) in comap UpperHalfPlane.im atTop,
  (fun z : ℍ↦ ∑' (n : ℕ), eisensteincoeff' k keven mne0 n * 𝕢 1 z ^ n) x = eisensteincoeff' k keven mne0 0 := by
      apply (EventuallyEqtsumeisensteincoeff hk a keven mne0)
    apply Filter.EventuallyEq.symm at this
    apply Filter.EventuallyEq.trans (this)
    have :  ∀ᶠ (x : ℍ) in comap UpperHalfPlane.im atTop,
  (fun z : ℍ↦ ∑' (n : ℕ), (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n * 𝕢 1 z ^ n) x =
  (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 := by
      apply (EventuallyEqtsumeisensteincoeff_qexpansion hk a keven mne0)
    apply Filter.EventuallyEq.symm at this
    apply Filter.EventuallyEq.symm
    apply Filter.EventuallyEq.trans (this)
    apply Filter.EventuallyEq.symm
    apply EventuallyEq_EisensteinSeries_atTop_im hk a keven mne0
  rw [Filter.eventuallyEq_iff_exists_mem] at this
  obtain ⟨s, h⟩ := this
  have h₁: Set.EqOn (fun z ↦ eisensteincoeff' k keven mne0 0) (fun z ↦
   (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a))) s := by
    apply h.2
  have : ∃ x ∈ s, (fun z : ℍ ↦ eisensteincoeff' k keven mne0 0) = (fun z ↦
   (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a))) := by
    sorry --trying to convert eventually eq to eq on constants
  obtain ⟨x,h₂⟩ := this
  have : (fun z : ℍ ↦ eisensteincoeff' k keven mne0 0) = fun z
  ↦ (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a)) := by
    apply h₂.2
  apply congrFun at this
  apply this x

lemma cuspfunctioneisensteinastsum {q : ℂ}{k m : ℕ} (hk : 3 ≤ (k : ℤ))
(a : Fin 2 → ZMod (1 : ℕ+))(keven : k = 2 * m) (qnorm : ‖q‖ < 1) :
cuspFunction 1 (⇑(eisensteinSeries_MF hk a) ∘ ↑ofComplex) q =
∑' (n : ℕ), (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ 0 *  q ^ n := by
  symm
  apply HasSum.tsum_eq
  convert eisensteinSeries_HasSum_SI_generic_q hk a keven qnorm
  sorry
  sorry

lemma eisensteinSeriesCuspfunction_tendso_eisensteincoeff0 {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
Tendsto (cuspFunction 1 ((eisensteinSeries_MF hk a) ∘ ofComplex))
(𝓝[≠] 0) (𝓝 (eisensteincoeff' k keven mne0 0)) := by
refine tendsto_nhds_of_eventually_eq ?_

sorry

theorem HasSum_eisensteincoeff_eq_eisensteinseries_cuspfun {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0){q : ℂ} (hq : ‖q‖ < 1):
 HasSum (fun n : ℕ ↦ (eisensteincoeff' k keven mne0 n • q ^ n))
 (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
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
    rw [eisensteinSeries_is_tsum_eisensteincoeff' hk a keven mne0]
    field_simp
    congr
    ext n
    subst keven
    simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_one, comp_apply, mul_eq_mul_left_iff]
    simp_all only [Nat.cast_mul, Nat.cast_ofNat]
    left
    have : cexp (2 * ↑π * i * (ofComplex (Periodic.invQParam 1 q))) ^ n =
    𝕢 1 (ofComplex (Periodic.invQParam 1 q)) ^ n := by
      unfold Periodic.qParam
      field_simp
    rw [this]
    push_neg at h
    have hh : (1 : ℝ)≠ 0 := by simp only [ne_eq, one_ne_zero, not_false_eq_true]
    have fact1 : ofComplex (Periodic.invQParam 1 q) = Periodic.invQParam 1 q := by
      simp_all only [ne_eq, one_ne_zero, not_false_eq_true]
      refine Complex.ext ?_ ?_
      · sorry/- ?-/
      · sorry
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
    · unfold Summable
      use 2
      unfold HasSum
      apply tendsto_nhds_of_eventually_eq ?_
      sorry  -- summable, true but skipping for now
  · apply eisensteincoeff_isSummable hk a keven mne0 q hq

lemma HasSumforCuspFunctionover_𝕢 {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0) :
 HasSum (fun n : ℕ ↦ (eisensteincoeff' k keven mne0 n • 𝕢 1 z ^ n))
 (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) (𝕢 1 z)) := by
  rw [Summable.hasSum_iff]
  symm
  convert SlashInvariantFormClass.eq_cuspFunction 1 (eisensteinSeries_MF hk a) z
  symm
  simp only [Nat.cast_one]
  rw [eisensteinSeries_is_tsum_eisensteincoeff' hk a keven mne0]
  unfold Periodic.qParam
  field_simp
  apply eisensteincoeff_isSummable hk a keven mne0 (𝕢 1 z) (by apply qParam_has_bounded_norm_coe z)

-- ## Implementing the FPowerSeries

noncomputable def eisensteinFormalMultilinearSeries {k m : ℕ} (keven :  k = 2 * m) (mne0 : m ≠ 0)  : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun m ↦ eisensteincoeff' k keven mne0 m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ

/- depends on the tsums equaling over the whole disk-/
lemma hasFPowerSeries_eisen  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m) (mne0 : m ≠ 0):
    HasFPowerSeriesOnBall (cuspFunction 1 (eisensteinSeries_MF hk a))
    (eisensteinFormalMultilinearSeries keven mne0) 0 1 := by
    have h₁ : 1 ≤ ((eisensteinFormalMultilinearSeries (keven :  k = 2 * m) (mne0 : m ≠ 0))).radius := by sorry
    have h₂ :  (0 : ENNReal) < 1 := by simp
    refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simp only [eisensteinFormalMultilinearSeries]
    simpa [eisensteinFormalMultilinearSeries] using (HasSum_eisensteincoeff_eq_eisensteinseries_cuspfun hk a keven mne0 hy)

theorem EisensteinserieshasFPsum  {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m)(mne0 : m ≠ 0)(hq : ‖q‖ < 1) :
 cuspFunction 1 (eisensteinSeries_MF hk a) q = (eisensteinFormalMultilinearSeries keven mne0).sum q := by
  apply HasFPowerSeriesOnBall.unique (hasFPowerSeries_eisen hk a keven mne0)
  convert FormalMultilinearSeries.hasFPowerSeriesOnBall (eisensteinFormalMultilinearSeries keven mne0) _
  sorry --small things like radius arguments left
  sorry
  sorry

lemma eisensteinseries_FpowerseriesOnBall_difference_hassum {k m : ℕ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m)(mne0 : m ≠ 0)
: HasFPowerSeriesOnBall ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((eisensteinFormalMultilinearSeries keven mne0) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 1 := by
  have h₁  :  1 ≤ ((eisensteinFormalMultilinearSeries keven mne0) -
  (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))).radius := by sorry
  have h₂ :  (0 : ENNReal) < 1 := by simp
  refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
  apply HasSum.sub
  · rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simpa [eisensteinFormalMultilinearSeries] using (HasSum_eisensteincoeff_eq_eisensteinseries_cuspfun hk a keven mne0 hy)
  · rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simpa [qExpansionFormalMultilinearSeries] using (eisensteinSeries_HasSum_SI_generic_q hk a keven hy)

theorem eisensteinseries_FpowerseriesAt_difference_hassum {k m : ℕ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m)(mne0 : m ≠ 0) :
 HasFPowerSeriesAt ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((eisensteinFormalMultilinearSeries keven mne0) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 := by
  use 1
  apply eisensteinseries_FpowerseriesOnBall_difference_hassum hk a keven

theorem eisensteinSeries_Fpowerseries_difference_eq_zero {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0):
 (eisensteinFormalMultilinearSeries keven mne0) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0:= by
  apply HasFPowerSeriesAt.eq_zero
  rw [← sub_self (cuspFunction 1 (eisensteinSeries_MF hk a))]
  apply eisensteinseries_FpowerseriesAt_difference_hassum hk a keven

theorem TheFPSeriesagree {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m) (mne0 : m ≠ 0):
  eisensteinFormalMultilinearSeries keven mne0 = qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) := by
  have h : (eisensteinFormalMultilinearSeries keven mne0) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0 := by
    apply eisensteinSeries_Fpowerseries_difference_eq_zero hk a keven
  rw [← sub_eq_zero]
  apply h

lemma TheFPSeriesagree2 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m) (mne0 : m ≠ 0) :
 ∀ (n : ℕ), eisensteinFormalMultilinearSeries keven mne0 n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by
  apply FormalMultilinearSeries.ext_iff.mp
  rw [TheFPSeriesagree hk a keven mne0]

/- this might be false actually-/

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
        cases h₁ with
        | inl h => refine false_of_true_eq_false ?_ ; sorry --oops
        | inr h_1 =>
          simp_all only [smul_zero]
          refine false_of_true_eq_false ?_
          sorry --apparently this is false
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

/- the coefficients agree thanks to FPowerSeries, but now I think this is probably unecessary-/
/- a better argument might have been to show proceed inductively as above and-/
/- show the coefficients agree by one by one and factor out 𝕢 1 z at each step-/
theorem coeff_of_q_expansions_agree  {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven :  k = 2 * m) (mne0 : m ≠ 0):
  (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n = eisensteincoeff' k keven mne0 n := by
    have h₁ : eisensteinFormalMultilinearSeries keven mne0 n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by apply TheFPSeriesagree2 hk a keven
    unfold eisensteinFormalMultilinearSeries qExpansionFormalMultilinearSeries  at h₁
    rw [mkPiAlgebra_eq_iff] at h₁ --actually false I think
    rw [h₁]


-- ## Combining everything to show that Eisenstein series
-- ##  are not in the CuspForm Subspace

theorem Eisenstein_coeff_not_zero {k m : ℕ} (keven :  k = 2 * m) (mne0 : m ≠ 0) :
eisensteincoeff' k keven mne0 0 ≠ 0 := by
  simp only [eisensteincoeff'_at_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

lemma eisensteinSeries_not_zero_at_infty1 {q : ℂ}{k m : ℕ} (hk : 3 ≤ (k : ℤ))
(a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)(mne0 : m ≠ 0) :
 ¬  ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a).toFun ∣[(k : ℤ)] A) := by
  rw [zeroAtInfty_iff_CuspForm]
  push_neg
  rw [coeff_of_q_expansions_agree 0 hk a keven]
  apply Eisenstein_coeff_not_zero keven mne0

lemma eisensteinSeries_nin_CuspForm_Subspace {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) (mne0 : m ≠ 0):
  (eisensteinSeries_MF hk a) ∉ CuspForm_Subspace Γ(1) k := by
    intro h
    have h₁ : ∃ f : CuspForm Γ(1) k, eisensteinSeries_MF hk a =
    (isom Γ(1) k f : ModularForm Γ(1) k) := by
      have h₁₁: Surjective (isom Γ(1) k ) := by apply LinearEquiv.surjective
      unfold Surjective at h₁₁
      convert h₁₁ (⟨eisensteinSeries_MF hk a, h⟩)
      constructor
      · intro h₁₂
        simp_rw [h₁₂]
      · intro h₁₂
        simp_rw [h₁₂]
    obtain ⟨f, fiseis⟩ := h₁
    have h₂ : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a) ∣[(k : ℤ)] A)
    := by
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
    have h₃ : ¬ ∀ (A : SL(2, ℤ)), IsZeroAtImInfty ((eisensteinSeries_MF hk a) ∣[(k : ℤ)] A)
     := by apply eisensteinSeries_not_zero_at_infty1 hk a keven mne0 ; apply q
    contradiction


lemma Eisenstein_series_ne_zero  {k m: ℕ} (hk : 3 ≤ (k: ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven : k = 2 * m)(mne0 : m ≠ 0) :
 qExpansion 1 (eisensteinSeries_MF hk a) ≠ 0 := by
  intro h
  rw [← PowerSeries.forall_coeff_eq_zero] at h
  have h₁ : (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a)) = 2 := by
    rw [← coeffzeroagree hk a keven mne0] ; simp only [eisensteincoeff'_at_zero]
  rw [h 0] at h₁
  have : 0 = (2:ℂ) → False := by simp
  apply this ; apply h₁

lemma Eisenstein_series_coeff_zero_eq_two {k m: ℕ} (hk : 3 ≤ (k: ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven : k = 2 * m)(mne0 : m ≠ 0) : (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a)) = 2  := by
rw [← coeffzeroagree hk a keven mne0] ; simp only [eisensteincoeff'_at_zero]

lemma Eisenstein_series_coeff_zero_ne_zero  {k m: ℕ} (hk : 3 ≤ (k: ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven : k = 2 * m)(mne0 : m ≠ 0) : (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a)) ≠ 0 := by
intro h
rw [Eisenstein_series_coeff_zero_eq_two hk a keven mne0] at h
have : 2 = 0 → False := by tauto
apply this ; convert h ; norm_cast

lemma Eisenstein_series_not_zero {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))
(keven : k = 2 * m)(mne0 : m ≠ 0) :
  eisensteinSeries_MF hk a ≠ 0 := by
  intro h
  have h₁ : (coeff ℂ 0) (qExpansion 1 (eisensteinSeries_MF hk a)) = 0 := by
    rw [h]
    simp_all only [PNat.val_ofNat, coeff_zero_eq_constantCoeff]
    unfold qExpansion
    simp only [constantCoeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero,
      one_mul]
    unfold SlashInvariantFormClass.cuspFunction
    rw [cuspFunction_zero_eq_limUnder_nhds_ne (1 : ℕ)]
    simp_all only [Nat.cast_one, coe_zero, Pi.zero_comp]
    rw [Filter.limUnder_eq_iff]
    · unfold Periodic.cuspFunction
      simp only [Pi.zero_comp]
      refine continuousAt_update_same.mp ?_
      simp only [update_idem, update_zero]
      refine Continuous.continuousAt ?_
      exact continuous_zero
    · use 0
      unfold Periodic.cuspFunction
      simp only [Pi.zero_comp]
      refine continuousAt_update_same.mp ?_
      simp only [update_idem, update_zero]
      refine Continuous.continuousAt ?_
      exact continuous_zero
  apply Eisenstein_series_coeff_zero_ne_zero hk a keven mne0 --Eisenstein_series_ne_zero hk a keven mne0
  rw [h₁]

#min_imports
