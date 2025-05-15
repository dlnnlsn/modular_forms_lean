import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.NumberTheory.Bernoulli

-# Hecke Algebra



-- ## FROM FLT PROJECT

open Complex UpperHalfPlane


lemma Set.Finite.of_injOn {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hm : MapsTo f s t) (hi : InjOn f s) (ht : t.Finite) : s.Finite :=
  Set.Finite.of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

-- not yet PRed
lemma Set.BijOn.finite_iff_finite {α β : Type*} {f : α → β} {s : Set α}
    {t : Set β} (h : BijOn f s t) : s.Finite ↔ t.Finite :=
  ⟨fun h1 ↦ h1.of_surjOn _ h.2.2, fun h1 ↦ h1.of_injOn h.1 h.2.1⟩

namespace FixedPoints
open MulAction

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G}

instance : AddCommMonoid (fixedPoints G A) :=
  AddSubmonoid.toAddCommMonoid (FixedPoints.addSubmonoid G A)

@[simp, norm_cast]
lemma coe_zero : ((0 : fixedPoints G A) : A) = 0 := rfl

@[simp, norm_cast]
lemma coe_add (a b : fixedPoints G A) :
    ((a + b : fixedPoints G A) : A) = a + b := rfl

-- note: `[SMulCommClass R G A]` is mathematically equivalent
-- to `[SMulCommClass G R A]` but we need a convention for an order here,
-- because `SMulCommClass X Y A → SMulCommClass Y X A` isn't
-- an instance because it would cause loops :-/
variable {R : Type*}

instance [SMul R A] [SMulCommClass G R A] :
    SMul R (fixedPoints G A) where
  smul r a := ⟨r • a.1, fun g ↦ by rw [smul_comm, a.2]⟩

@[simp, norm_cast]
lemma coe_smul [SMul R A] [SMulCommClass G R A] (r : R) (a : fixedPoints G A) :
    ((r • a : fixedPoints G A) : A) = r • a := rfl

instance [Monoid R] [MulAction R A] [SMulCommClass G R A] :
    MulAction R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]

-- Probably this should be a submodule instance and then get module instance for free
instance module [Ring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]
  smul_zero a := by
    ext
    push_cast
    simp
  smul_add r s a := by
    ext
    push_cast
    simp
  add_smul r s a := by
    ext
    push_cast
    simp [add_smul]
  zero_smul a := by
    ext
    push_cast
    simp

end FixedPoints

open scoped Pointwise

-- should maybe be in mathlib but not sure where to put it.
variable (G : Type*) [Group G] (U : Subgroup G) (X : Set G) {u : G} in
lemma Set.bijOn_smul (hu : u ∈ U) : Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) := by
  refine ⟨?_, Set.injOn_of_injective (MulAction.injective u), ?_⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨u * u', mul_mem hu hu', x, hx, by simp [mul_assoc]⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨(u⁻¹ * u') * x, ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', x, hx, rfl⟩, by simp [mul_assoc]⟩

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open MulAction

-- finiteness hypothesis we need to make Hecke operators work: UgV is
-- a finite number of left V-cosets.
variable (h : (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

/-- If a is fixed by V then `∑ᶠ g ∈ s, g • a` is independent of the choice `s` of
coset representatives in `G` for a subset of `G ⧸ V` -/
lemma eq_finsum_quotient_out_of_bijOn' (a : fixedPoints V A)
    {X : Set (G ⧸ V)}
    {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
    ∑ᶠ g ∈ s, g • (a : A) = ∑ᶠ g ∈ Quotient.out '' X, g • (a : A) := by
  let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
  have he₀ : Set.BijOn e s (Quotient.out '' X) := by
    refine Set.BijOn.comp ?_ hs
    exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
  have he₁ : ∀ g ∈ s, g • (a : A) = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
    intro g hgs
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    rw [hv, mul_smul, (show (v : G) • (a : A) = a from a.2 v)]
  exact finsum_mem_eq_of_bijOn e he₀ he₁


 section

/-- The Hecke operator T_g = [UgV] : A^V → A^U associated to the double coset UgV. -/
noncomputable def HeckeOperator_toFun (a : fixedPoints V A) : fixedPoints U A :=
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn' a] --distributes action and replaces quotient
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply Set.bijOn_smul _ _ _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

  noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
    toFun := HeckeOperator_toFun h
    map_zero' := by
      ext
      simp [HeckeOperator_toFun]
    map_add' a b := by
      ext
      simp [HeckeOperator_toFun, -Set.mem_image, finsum_mem_add_distrib (h.image Quotient.out)]

variable {R : Type*} [Ring R] [Module R A] [SMulCommClass G R A]

noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    ext
    simp [HeckeOperator_toFun, -Set.mem_image, finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    ext
    simp [-Set.mem_image, HeckeOperator_toFun, smul_comm, smul_finsum_mem (h.image Quotient.out)]

lemma HeckeOperator_apply (a : fixedPoints V A) :
    (HeckeOperator (R := R) h a : A) =
    ∑ᶠ (gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * g • ↑V) : Set (G ⧸ V))), gᵢ • (a : A) :=
  rfl

theorem comm {g₁ g₂ : G} (h₁ : (QuotientGroup.mk '' (U * g₁ • U) : Set (G ⧸ U)).Finite)
    (h₂ : (QuotientGroup.mk '' (U * g₂ • U) : Set (G ⧸ U)).Finite)
    (hcomm : ∃ s₁ s₂ : Set G,
      Set.BijOn QuotientGroup.mk s₁ (QuotientGroup.mk '' (U * g₁ • U) : Set (G ⧸ U)) ∧
      Set.BijOn QuotientGroup.mk s₂ (QuotientGroup.mk '' (U * g₂ • U) : Set (G ⧸ U)) ∧
      ∀ a ∈ s₁, ∀ b ∈ s₂, a * b = b * a) :
    (HeckeOperator h₁ ∘ₗ HeckeOperator h₂ : fixedPoints U A →ₗ[R] fixedPoints U A) =
    HeckeOperator h₂ ∘ₗ HeckeOperator h₁ := by
  ext a
  rcases hcomm with ⟨s₁, s₂, hs₁, hs₂, hcomm⟩
  simp only [LinearMap.coe_comp, Function.comp_apply]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₁]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₂]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₂]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₁]
  have hfs₁ : s₁.Finite := by rwa [hs₁.finite_iff_finite]
  have hfs₂ : s₂.Finite := by rwa [hs₂.finite_iff_finite]
  simp_rw [smul_finsum_mem hfs₁, smul_finsum_mem hfs₂, finsum_mem_comm _ hfs₁ hfs₂]
  -- I'm sure there's a better way to do this!
  congr; ext g₂; congr; ext hg₂; congr; ext g₁; congr; ext hg₁;
  rw [smul_smul, smul_smul, hcomm _ hg₁ _ hg₂]

end --ends random section
end AbstractHeckeOperator

--## END FLT CODE






section
open EisensteinSeries CongruenceSubgroup
open ModularForm Complex Filter UpperHalfPlane Function
open ModularFormClass
open Complex Topology Manifold Matrix
variable {Γ : outParam <| Subgroup SL(2, ℤ)} {k : outParam ℤ}
open MulAction

instance : MulAction (GL(2,ℚ)⁺) (ModularForm Γ k) where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
instance : SMul (GL(2,ℚ)⁺) (ModularForm Γ k) where
  smul := sorry


--notation "∣[k]" => GL₂ℚpos_acts_on_Mₖ

instance : HSMul (↥GL(2, ℚ)⁺) (Set ↥GL(2, ℚ)⁺) (outParam (Set ↥GL(2, ℚ)⁺))  where
  hSMul := sorry

instance Γ₁ (N : ℕ+): Subgroup (Matrix.GLPos (Fin 2) ℚ) where
  carrier := Set.range ((↑) : (Gamma1 N) → Matrix.GLPos (Fin 2) ℚ)
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n * m
    simp
  one_mem' := by use 1; simp
  inv_mem' := by
    rintro _ ⟨n, rfl⟩
    use n⁻¹
    simp

instance Gamma1_isom_GL_subgroup (N : ℕ+) : Γ₁ N ≃* Gamma1 N where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry


instance αΓ₁α' (N : ℕ+) (α : GL(2,ℚ)⁺): Subgroup (GL(2, ℚ)⁺) where
  carrier := {α⁻¹*γ*α | γ ∈ Γ₁ N} ∩ Γ₁ N
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

instance αΓ₁α (N : ℕ+) (α : GL(2,ℚ)⁺) : Subgroup (SL(2, ℤ)) where
  carrier := {α⁻¹*γ*α | γ ∈ Γ₁ N} ∩ {γ | ∃ γ₁ : Γ₁ N, γ = ((Gamma1_isom_GL_subgroup N) γ₁)}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

lemma αΓ₁α_is_CongruenceSubgroup (N : ℕ+) {α : GL(2,ℚ)⁺} :
CongruenceSubgroup.IsCongruenceSubgroup (αΓ₁α N α) := sorry

instance Γ₁action_on_MₖαΓα {N : ℕ+} {α : GL(2,ℚ)⁺} : MulAction (Γ₁ N) (ModularForm (αΓ₁α N α) k)  where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry

instance fixedpoints (N : ℕ+) {α : GL(2,ℚ)⁺}
{f : ModularForm (Gamma1 N) k}: ModularForm (αΓ₁α N α) k where
  toFun := α • f
  slash_action_eq' := sorry
  holo' := sorry
  bdd_at_infty' := sorry

variable {N : ℕ+} {α : GLPos (Fin 2) ℚ} (G : (QuotientGroup.mk '' ((Γ₁ N) * α • (Γ₁ N)) :
Set (GLPos (Fin 2) ℚ ⧸ ↑↑(Γ₁ N))).Finite)

noncomputable def HeckeOp {k : ℤ} {α : GLPos (Fin 2) ℚ}
 (f : ModularForm (Gamma1 N) k) : ModularForm (Gamma1 N) k where
  toFun := AbstractHeckeOperator.HeckeOperator G
  slash_action_eq' := _
  holo' := _
  bdd_at_infty' := _
