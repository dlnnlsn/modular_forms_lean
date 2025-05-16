import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.NumberTheory.Bernoulli

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
      have : b = 1 := by sorry
      rw [this]
  right_inv := by
    intro v
    simp_all only [Fin.isValue, ↓reduceIte, one_ne_zero, Prod.mk.eta]

instance gammaset {k : ℕ} (a : Fin 2 → ZMod 1) : gammaSet 1 a = {fintoprod.invFun (x : ℤ × ℤ) | x ≠ 0} where
  toFun := fun v => (v (0 : Fin 2), v (1 : Fin 2 ))
  invFun := fun v => fun x => if x = 0 then v 0 else v 1
  left_inv := sorry
  right_inv := sorry

lemma eisensteinSeries_expand {k : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod (1:ℕ+)) :
eisensteinSeries a k  = fun z:ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k:ℤ)) + ∑' y : ℕ, ∑' x : ℤ, ((y + 1)* (z : ℂ) + x) ^ (-(k:ℤ)):= by
  ext z
  unfold eisensteinSeries eisSummand
  simp_all only [PNat.val_ofNat, Fin.isValue, zpow_neg, zpow_natCast]
  unfold tsum
  --apply gammaset
  sorry

theorem cotagent_Formula_HasSum: HasSum (fun (n : ℕ) => 1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by
  sorry

theorem cotagent_formula : ∑' (n : ℕ), (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) = (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by
  convert HasSum.tsum_eq cotagent_Formula_HasSum

lemma bernoulli_cotagent_Formula {k : ℕ } : HasSum (fun n : ℕ => (2 * π * i) ^ (2 * n) * (bernoulli' (2 * n)) / ((2 *n).factorial * z ^ (2 * n))) (π * z * cos (π * z)/ sin (π * z)):= by
  sorry

lemma cotagent_as_exp : (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) = π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by sorry

lemma cotagent_as_exp1 :  π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) =
- π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by sorry

lemma cotagent_as_exp2 : - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) =
- π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by sorry

lemma cotagent_as_exp3 : (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ))  = - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by
  calc
    (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) = π * i * (cexp (π * i * z) + cexp (- π * i * z)) / (cexp (π * i * z) - cexp (-π * i * z)) := by apply cotagent_as_exp
    _  = - π * i - 2 * π * i * cexp (2 * π * i * z) /(1 -  cexp (2 * π * i * z) ) := by apply cotagent_as_exp1
    _  = - π * i - 2 * π *i * ∑'(d : ℕ), cexp (2 * π * i * (d + 1) *z) := by apply cotagent_as_exp2


lemma rw_of_cotangent_base_case :
 ∑' x : ℤ, ((z:ℂ) + (x : ℂ))^(- 2 : ℤ) =
 (2*π*i)^ 2* ∑' d : ℕ, (d + 1) * Complex.exp (2*π*i*(d + 1)*z) := by
  have h : ∀ z : ℍ, ∑' (n : ℕ), (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) = (π * cos (π * z)/ sin (π * z) - 1 / (z : ℂ)) := by intro τ ; convert cotagent_formula
  symm
  simp_rw [cotagent_as_exp3] at h
  have h₁ : ∀ z : ℂ, HasDerivAt (fun τ : ℂ => -π *i) 0 z := by sorry
  have h₂ {d : ℤ} : ∀ z : ℂ,HasDerivAt (fun z => cexp (2 * ↑π * i * (d + 1) * (ofComplex z : ℂ))) (2 * ↑π * i * (d + 1) * cexp (2 * ↑π * i * (d + 1) * (ofComplex z : ℂ))) z := by sorry
  have h₃ {d : ℤ} : ∀ z : ℂ,HasDerivAt (fun z =>  2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (ofComplex z))) ((2 * ↑π * i) ^ 2 * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (ofComplex z : ℂ))) z := by sorry
  have h₄ {d : ℤ} : ∀ z : ℂ,HasDerivAt (fun z => (1 / ((z : ℂ)))) (1 / (z : ℂ) ^ 2) z := by sorry
  have h₅ : ∀ z : ℂ, HasDerivAt (fun z  => ∑' (n : ℕ), (1 / ((ofComplex z : ℂ) - (↑n + 1)))) (∑' (n : ℕ), (1 / ((ofComplex z : ℂ) + (↑n + 1)) ^ 2)) z := by sorry
  have h₆ : ∀ z : ℂ, HasDerivAt (fun z =>  ∑' (n : ℕ), (1 / ((ofComplex z : ℂ) - (↑n + 1)) + 1 / ((ofComplex z : ℂ) + (↑n + 1)))) (- ∑' (n : ℤ), (1 / ((ofComplex z : ℂ) + (↑n))^2)) z := by sorry
  have h₇ : ∀ z : ℂ, HasDerivAt (fun z => -↑π * i - 2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * (ofComplex z : ℂ ))) (- (2 * ↑π * i) ^ 2 * ∑' (d : ℕ), (d + 1) * cexp (2 * ↑π * i * (↑d + 1) * ↑z)) z := by sorry
  have h₈ : deriv (fun z => ∑' (n : ℕ), (1 / ((ofComplex z : ℂ) - (↑n + 1)) + 1 / ((ofComplex z : ℂ) + (↑n + 1)))) z =
  deriv (fun z => -↑π * i - 2 * ↑π * i * ∑' (d : ℕ), cexp (2 * ↑π * i * (↑d + 1) * ↑(ofComplex z : ℂ))) z := by congr; ext τ; simp_rw [h (ofComplex τ)]
  have h₉ : - ∑' (n : ℤ), (1 / ((z : ℂ) + (↑n))^2) = - (2 * ↑π * i) ^ 2 * ∑' (d : ℕ), (d + 1) * cexp (2 * ↑π * i * (↑d + 1) * ↑z) := by rw [deriv_eq h₆] at h₈ ; symm ; rw [deriv_eq h₇] at h₈ ; simp only [ofComplex_apply] at h₈ ; rw [h₈]
  rw [neg_mul,neg_inj] at h₉
  simp_all
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
∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, m^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by
  rw [eisensteinSeries_expand hk a]
  ext (z: ℍ)
  have {y : ℕ}: ∑' x : ℤ, ((y + 1)* (z:ℂ) + (x : ℂ))^(-(k : ℤ)) = (2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, (d + 1) ^ (k -1 ) * Complex.exp (2*π*i*(d + 1)*(y + 1)*(z:ℂ)) := by
    have : ∃ s : ℍ, (s : ℂ) = (y + 1) * z := sorry
    rcases this with ⟨s, h⟩
    simp_rw [mul_assoc (2 * π * i * _)]
    rw [← h, rw_of_cotangent (by linarith)]
  simp only [this]
  have : ∑' (y : ℕ), ∑' (d : ℕ),(d + 1) ^(k -1)  * cexp (2*π*i*(d + 1)*(y + 1)*z) = ∑' (d : ℕ) (m : {s : ℕ | (s + 1) ∣ d + 1}), m^(k-1) * cexp (2*π*i*(d + 1)*z) := sorry
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
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, ∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, m^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by
  ext z
  rw [eisensteinSeries_SIF_apply, eisensteinSeries_eq_qExpansion hk]

lemma eisensteinSeries_MF_is {k : ℕ}  (hk : 3 ≤ (k:ℤ)) (a : Fin 2 → ZMod (1:ℕ+)) :
(eisensteinSeries_MF hk a).toFun = fun z : ℍ ↦ 2 * ∑' x : ℕ, ((x : ℂ) + 1) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ, ∑' m : {s : ℕ | (s + 1) ∣ (d + 1)}, m^(k-1) * Complex.exp (2*π*i*(d + 1)*z) := by apply eisenstein_sif_is _ a ; norm_cast at hk

--THIS ONE IS BETTER
lemma eisensteinSeries_MF_is' {k : ℕ}  (hk : 3 ≤ (k:ℤ)) (a : Fin 2 → ZMod (1:ℕ+)) :
(eisensteinSeries_MF hk a) = fun z : ℍ ↦ 2 * ∑' x : ℕ+, ((x : ℂ)) ^(-(k : ℤ)) +
(2*π*i)^k* (Nat.factorial (k-1))^(-(1:ℤ)) * ∑' d : ℕ+, ∑' m : {s : ℕ+ | s ∣ d}, m^(k-1) * Complex.exp (2*π*i*d*z) := by sorry -- apply eisenstein_sif_is _ a ; norm_cast at hk

open DirectSum
open scoped DirectSum

#check CuspForm.zero_at_infty'

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



lemma Zeta_function_eq {k : ℕ} : ∑' (x : ℕ+), (x : ℂ) ^ (-(k : ℤ)) = - (2 * π * i) ^ k * (bernoulli' k) / (2 * Nat.factorial k) := by
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
  map_add' := by intro ψ φ ; simp ; ext m h₁ ; ring_nf ; simp ; ring_nf
  map_smul' := by
    intro c ψ ; simp_all only [map_smul, smul_eq_mul, RingHom.id_apply] ;
    ext m h₁ ;
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

lemma obvsthing' {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • q ^ n) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
 sorry

lemma obvsthing4 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
(- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k
  + (2 * π * i) ^ k * (k - 1).factorial ^ (-(1 : ℤ)) *
   ∑' (d : ℕ+) (m : {s | s ∣ d}), ((m : ℕ+) : ℂ) ^ (k - 1) • 𝕢 1 z ^ (d:ℕ) )=
    ∑' n : ℕ, (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n • 𝕢 1 z ^ n := by
  sorry

noncomputable def eisensteincoeff {k : ℕ} : ℕ → ℂ :=
  fun n => if n = 0 then (- (2 * π * i) ^ k * (bernoulli' k) / Nat.factorial k)
  else (2 * π * i) ^ k * (k - 1).factorial ^ (-(1 : ℤ)) * ∑' (m : {s | s ∣ n }), (m : ℂ) ^ (k - 1)

lemma eisensteinSeries_is_tsum_eisensteincoeff {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 eisensteinSeries_MF hk a z = (∑' (n : ℕ), @eisensteincoeff k n • 𝕢 1 z ^ n) := by sorry

lemma eisensteinSeries_is_tsum_eisensteincoeff' {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ))
 (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 eisensteinSeries_MF hk a z = (∑' (n : ℕ), @eisensteincoeff k n • q ^ n) := by sorry

lemma obvsthing7 {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (@eisensteincoeff k n • 𝕢 1 z ^ n)) ((eisensteinSeries_MF hk a) z) := by
  rw [eisensteinSeries_is_tsum_eisensteincoeff]
  unfold HasSum Tendsto
  intro S h₁
  rename_i x
  subst x
  simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul, mem_map, mem_atTop_sets, ge_iff_le, Finset.le_eq_subset,
    Set.mem_preimage]
  sorry
  assumption

lemma obvsthing8 {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(_ :  k = 2 * m)  :
 HasSum (fun n : ℕ ↦ (@eisensteincoeff k n • q ^ n)) (SlashInvariantFormClass.cuspFunction 1 (eisensteinSeries_MF hk a) q) := by
  sorry

open SlashInvariantFormClass

theorem coeffiecients_cancel {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) : ∀ (n : ℕ), (@eisensteincoeff k n) -
((qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n) = 0 := by

  sorry

noncomputable def eisensteinFormalMultilinearSeries {k : ℕ} : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun m ↦ @eisensteincoeff k m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ

lemma hasFPowerSeries_eisen {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)  :
    HasFPowerSeriesOnBall (cuspFunction 1 (eisensteinSeries_MF hk a)) (@eisensteinFormalMultilinearSeries k) 0 1 := by
    have h₁ : 1 ≤ ((@eisensteinFormalMultilinearSeries k)).radius := by sorry
    have h₂ :  (0 : ENNReal) < 1 := by simp
    refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simp only [eisensteinFormalMultilinearSeries]
    simpa [eisensteinFormalMultilinearSeries] using (obvsthing8 hk a keven)

theorem EisensteinserieshasFPsum  {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 cuspFunction 1 (eisensteinSeries_MF hk a) q = (@eisensteinFormalMultilinearSeries k).sum q := by
  apply HasFPowerSeriesOnBall.unique (hasFPowerSeries_eisen hk a keven)
  convert FormalMultilinearSeries.hasFPowerSeriesOnBall (@eisensteinFormalMultilinearSeries k) _
  sorry --small things like radius arguments left
  sorry
  sorry


lemma eisensteinseries_FpowerseriesOnBall_difference_hassum {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m): HasFPowerSeriesOnBall ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 1 := by
  have h₁  :  1 ≤ ((@eisensteinFormalMultilinearSeries k) -
  (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))).radius := by sorry
  have h₂ :  (0 : ENNReal) < 1 := by simp
  refine ⟨h₁, h₂ ,  fun hy ↦ ?_⟩
  apply HasSum.sub
  simpa [eisensteinFormalMultilinearSeries] using (obvsthing8 hk a keven)
  simpa [qExpansionFormalMultilinearSeries] using (obvsthing' hk a keven)

theorem eisensteinseries_FpowerseriesAt_difference_hassum {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 HasFPowerSeriesAt ( cuspFunction 1 (eisensteinSeries_MF hk a) -  cuspFunction 1 (eisensteinSeries_MF hk a))
((@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a))) 0 := by
  use 1
  apply eisensteinseries_FpowerseriesOnBall_difference_hassum hk a keven ; apply q

theorem eisensteinSeries_Fpowerseries_difference_eq_zero {k m : ℕ} {q : ℂ}  (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
 (@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0:= by
  apply HasFPowerSeriesAt.eq_zero
  rw [← sub_self (cuspFunction 1 (eisensteinSeries_MF hk a))]
  apply eisensteinseries_FpowerseriesAt_difference_hassum hk a keven ; apply q

theorem TheFPSeriesagree {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  @eisensteinFormalMultilinearSeries k = qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) := by
  have h : (@eisensteinFormalMultilinearSeries k) - (qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a)) = 0 := by
    apply eisensteinSeries_Fpowerseries_difference_eq_zero hk a keven ; apply q
  rw [← sub_eq_zero]
  apply h

lemma TheFPSeriesagree2 {q : ℂ }{k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m)  :
 ∀ (n : ℕ), @eisensteinFormalMultilinearSeries k n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by
  apply FormalMultilinearSeries.ext_iff.mp
  apply TheFPSeriesagree hk a keven ; apply q

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

theorem coeff_of_q_expansions_agree  {q : ℂ} {k m : ℕ} (hk : 3 ≤ (k : ℤ)) (a : Fin 2 → ZMod (1 : ℕ+))(keven :  k = 2 * m) :
  (qExpansion 1 (eisensteinSeries_MF hk a)).coeff ℂ n = @eisensteincoeff k n := by
    have h₁ : @eisensteinFormalMultilinearSeries k n =
 qExpansionFormalMultilinearSeries 1 (eisensteinSeries_MF hk a) n := by apply TheFPSeriesagree2 hk a keven ; apply q
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
    have : ∑' («i» : ℕ+), ((2 * ↑π * i) ^ k * (↑(k - 1).factorial)⁻¹) • ∑' (m : { x // x ∣ «i» }), ↑↑↑m ^ (k - 1) * 𝕢 1 ↑z ^ («i» : ℕ)
    = ∑' («i» : ℕ), ((2 * ↑π * i) ^ k * (↑(k - 1).factorial)⁻¹) • ∑' (m : { x // x ∣ «i» +1 }), ↑↑↑m ^ (k - 1) * 𝕢 1 ↑z ^ ↑(«i» + 1) := by
      sorry
    rw [this]
    congr
    ext n
    rw [smul_mul_assoc]
    simp_all only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ofReal_eq_zero, false_or, I_ne_zero, or_false, ne_eq, _root_.inv_eq_zero, Nat.cast_eq_zero]
    left
    rw [mul_comm, ← smul_eq_mul (𝕢 1 ↑z ^ (n + 1))]
    symm
    rw [← tsum_const_smul'' (𝕢 1 ↑z ^ (n + 1))]
    simp_rw [mul_comm _ (𝕢 1 ↑z ^ (n + 1))]
    rfl
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
  repeat apply q


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

lemma subspacelemma (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) (x : Subspace ℂ  (ModularForm Γ(1) k)) :
x ≤ (Submodule.span ℂ {eisensteinSeries_MF hk a}) ↔
∀ f ∈ x, ∃ c : ℂ, f = c • (eisensteinSeries_MF hk a) := sorry

lemma subspacelemma2 (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) (x : Subspace ℂ  (ModularForm Γ(1) k)) :
x ≤ CuspForm_Subspace Γ(1) k ↔
∀ f ∈ x, ∀ (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A) := sorry


lemma EisensteinSeries_in_EisensteinSubspace (c : ℂ) (hk : 3 ≤ k) (a : Fin 2 → ZMod (1 : ℕ+)) :
c • (eisensteinSeries_MF hk a) ∈ Submodule.span ℂ {eisensteinSeries_MF hk a} := by sorry

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
    intro x h₁ h₂
    sorry

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
  apply rank_eq_of_equiv_equiv idℂ (LinearEquiv.toAddEquiv (Submodule.prodEquivOfIsCompl (Submodule.span ℂ {(eisensteinSeries_MF hk a : (ModularForm Γ((1 : ℕ+)) k))}) (CuspForm_Subspace Γ((1 : ℕ+)) k)  (eisensteinSeries_comp_CuspForm hk a) ) )
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
