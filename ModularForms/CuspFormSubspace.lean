import Mathlib.NumberTheory.ModularForms.Basic

open CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open ModularFormClass
open Complex Topology Manifold

open scoped Real MatrixGroups CongruenceSubgroup

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam
local notation "i" => Complex.I

lemma bdd_at_infty_of_zero_at_infty (f : CuspForm Γ k) : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] A) := by
  intro A
  have h₁ : IsZeroAtImInfty (f ∣[k] A) := by
    apply CuspForm.zero_at_infty' f
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at h₁
  use 1
  apply h₁ _ _
  linarith

@[coe]
instance coe_CuspForm (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := by apply SlashInvariantForm.slash_action_eq'
  holo' := by apply CuspForm.holo'
  bdd_at_infty' := by apply bdd_at_infty_of_zero_at_infty

@[congr]
lemma CuspForm_congr {f g : CuspForm Γ k} : coe_CuspForm f = coe_CuspForm g ↔
(coe_CuspForm f).toFun = (coe_CuspForm g).toFun := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext τ
    have : (coe_CuspForm f).toFun τ = (coe_CuspForm g).toFun τ := by
      rw [h]
    apply this

@[simp]
lemma CuspForm_inj {f g : CuspForm Γ k}  : coe_CuspForm f = coe_CuspForm g →
  f = g := by
    intro h
    ext z
    have : (coe_CuspForm f) z = (coe_CuspForm g) z := by congr
    apply this

@[simp]
lemma coe_CuspForm_apply (f : CuspForm Γ k) {x : ℍ} : (coe_CuspForm f).toFun x = f x := by rfl

def coe_Hom' : CuspForm Γ k  →+ ModularForm Γ k where
  toFun := coe_CuspForm
  map_zero' := by rfl
  map_add' := by intro f g ; rfl

@[simp]
lemma coehom_congr {f g : CuspForm Γ k} : coe_Hom' f = coe_Hom' g ↔
coe_CuspForm f = coe_CuspForm g := by
  tauto

@[simp]
lemma coe_Hom'_inj {f g : CuspForm Γ k} : coe_Hom' f = coe_Hom' g →
f = g := by
  intro h
  rw [coehom_congr] at h
  apply CuspForm_inj h

def coe_Hom : CuspForm Γ k →[ℂ] ModularForm Γ k where
  toFun := coe_Hom'
  map_smul' := by intro c f ; rfl

@[simp]
lemma coe_Hom_congr {f g : CuspForm Γ k} : coe_Hom f = coe_Hom g ↔
coe_Hom' f = coe_Hom' g := by
  tauto

@[simp]
lemma coe_hom_inj {f g : CuspForm Γ k} : (coe_Hom f = coe_Hom g) → f = g  := by
intro h ;
rw [coe_Hom_congr] at h
apply coe_Hom'_inj ; exact h

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

@[simp]
lemma coee {f : CuspForm Γ k} :
coe_Hom f ∈ CuspForm_Subspace Γ k := by tauto



@[simp]
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

theorem CuspForm_Subspace_zeroatinfty {f : CuspForm_Subspace Γ k} : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty (toSlashInvariantForm f.1 ∣[k] A)  := by
  have :  ∃ (g : CuspForm Γ k), f = coe_Hom g := by
    simp only [SetLike.coe_mem, coe_hom_surj]
  obtain ⟨g, h⟩ := this
  rw [h]
  have : ∀ (A : SL(2, ℤ)), IsZeroAtImInfty (CuspForm.toSlashInvariantForm g ∣[k] A) := by apply g.zero_at_infty'
  exact fun A ↦ this A

theorem CuspForm_Subspace_MDifferentiable {f : CuspForm_Subspace Γ k} :
MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (toSlashInvariantForm f.1) := by
have :  ∃ (g : CuspForm Γ k), f = coe_Hom g := by
    simp only [SetLike.coe_mem, coe_hom_surj]
obtain ⟨g, h⟩ := this
rw [h]
have : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (CuspForm.toSlashInvariantForm g)  := by apply g.holo'
exact fun A ↦ this A

def Coe_Hom_inv : CuspForm_Subspace Γ k → CuspForm Γ k :=
fun f => CuspForm.mk f (CuspForm_Subspace_MDifferentiable) (CuspForm_Subspace_zeroatinfty)

noncomputable
instance isom (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
  (CuspForm Γ k) ≃ₗ[ℂ] CuspForm_Subspace Γ k where
    toFun := fun f => ⟨coe_Hom f , coee⟩
    map_add' := by intro x y; tauto
    map_smul' := by intro c x ; tauto
    invFun := Coe_Hom_inv
    left_inv := by
      intro x; dsimp;
      rfl
    right_inv := by
      intro x; dsimp;
      rfl
