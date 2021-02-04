/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.subfield
import field_theory.tower
import ring_theory.algebraic

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `algebra K L`.
This file defines the type of fields in between `K` and `L`, `intermediate_field K L`.
An `intermediate_field K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `subfield L` and a `subalgebra K L`.

## Main definitions

 * `intermediate_field K L` : the type of intermediate fields between `K` and `L`.

 * `subalgebra.to_intermediate_field`: turns a subalgebra closed under `⁻¹`
   into an intermediate field

 * `subfield.to_intermediate_field`: turns a subfield containing the image of `K`
   into an intermediate field

* `intermediate_field.map`: map an intermediate field along an `alg_hom`

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/

open finite_dimensional
open_locale big_operators

variables (K L : Type*) [field K] [field L] [algebra K L]

section
set_option old_structure_cmd true

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field extends subalgebra K L, subfield L

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc intermediate_field.to_subalgebra

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
add_decl_doc intermediate_field.to_subfield

end

variables {K L} (S : intermediate_field K L)

namespace intermediate_field

instance : has_coe (intermediate_field K L) (set L) :=
⟨intermediate_field.carrier⟩

@[simp] lemma coe_to_subalgebra : (S.to_subalgebra : set L) = S := rfl

@[simp] lemma coe_to_subfield : (S.to_subfield : set L) = S := rfl

instance : has_coe_to_sort (intermediate_field K L) := ⟨Type*, λ S, S.carrier⟩

instance : has_mem L (intermediate_field K L) := ⟨λ m S, m ∈ (S : set L)⟩

@[simp] lemma mem_mk (s : set L) (hK : ∀ x, algebra_map K L x ∈ s)
  (ho hm hz ha hn hi) (x : L) :
  x ∈ intermediate_field.mk s ho hm hz ha hK hn hi ↔ x ∈ s := iff.rfl

@[simp] lemma mem_coe {x : L} : x ∈ (S : set L) ↔ x ∈ S := iff.rfl

@[simp] lemma mem_to_subalgebra (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subalgebra ↔ x ∈ s := iff.rfl

@[simp] lemma mem_to_subfield (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subfield ↔ x ∈ s := iff.rfl

/-- Two intermediate fields are equal if the underlying subsets are equal. -/
theorem ext' ⦃s t : intermediate_field K L⦄ (h : (s : set L) = t) : s = t :=
by { cases s, cases t, congr' }

/-- Two intermediate fields are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : intermediate_field K L} : s = t ↔ (s : set L) = t :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext] theorem ext {S T : intermediate_field K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
ext' $ set.ext h

/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem (x : K) : algebra_map K L x ∈ S :=
S.algebra_map_mem' x

/-- An intermediate field contains the ring's 1. -/
theorem one_mem : (1 : L) ∈ S := S.one_mem'

/-- An intermediate field contains the ring's 0. -/
theorem zero_mem : (0 : L) ∈ S := S.zero_mem'

/-- An intermediate field is closed under multiplication. -/
theorem mul_mem : ∀ {x y : L}, x ∈ S → y ∈ S → x * y ∈ S := S.mul_mem'

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S := S.to_subalgebra.smul_mem

/-- An intermediate field is closed under addition. -/
theorem add_mem : ∀ {x y : L}, x ∈ S → y ∈ S → x + y ∈ S := S.add_mem'

/-- An intermediate field is closed under subtraction -/
theorem sub_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
S.to_subfield.sub_mem hx hy

/-- An intermediate field is closed under negation. -/
theorem neg_mem : ∀ {x : L}, x ∈ S → -x ∈ S := S.neg_mem'

/-- An intermediate field is closed under inverses. -/
theorem inv_mem : ∀ {x : L}, x ∈ S → x⁻¹ ∈ S := S.inv_mem'

/-- An intermediate field is closed under division. -/
theorem div_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x / y ∈ S :=
S.to_subfield.div_mem hx hy

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
lemma list_prod_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.prod ∈ S :=
S.to_subfield.list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
lemma list_sum_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.sum ∈ S :=
S.to_subfield.list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
lemma multiset_prod_mem (m : multiset L) :
  (∀ a ∈ m, a ∈ S) → m.prod ∈ S :=
S.to_subfield.multiset_prod_mem m

/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
lemma multiset_sum_mem (m : multiset L) :
  (∀ a ∈ m, a ∈ S) → m.sum ∈ S :=
S.to_subfield.multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field. -/
lemma prod_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∏ i in t, f i ∈ S :=
S.to_subfield.prod_mem h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`. -/
lemma sum_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∑ i in t, f i ∈ S :=
S.to_subfield.sum_mem h

lemma pow_mem {x : L} (hx : x ∈ S) (n : ℤ) : x^n ∈ S :=
begin
  cases n,
  { exact @is_submonoid.pow_mem L _ S.to_subfield.to_submonoid x _ hx n, },
  { have h := @is_submonoid.pow_mem L _ S.to_subfield.to_submonoid x _ hx _,
    exact subfield.inv_mem S.to_subfield h, },
end

lemma gsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) :
  n •ℤ x ∈ S := S.to_subfield.gsmul_mem hx n

lemma coe_int_mem (n : ℤ) : (n : L) ∈ S :=
by simp only [← gsmul_one, gsmul_mem, one_mem]

end intermediate_field

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def subalgebra.to_intermediate_field (S : subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
  intermediate_field K L :=
{ neg_mem' := λ x, S.neg_mem,
  inv_mem' := inv_mem,
  .. S }

@[simp] lemma to_subalgebra_to_intermediate_field
  (S : subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
  (S.to_intermediate_field inv_mem).to_subalgebra = S :=
by { ext, refl }

@[simp] lemma to_intermediate_field_to_subalgebra
  (S : intermediate_field K L) (inv_mem : ∀ x ∈ S.to_subalgebra, x⁻¹ ∈ S) :
  S.to_subalgebra.to_intermediate_field inv_mem = S :=
by { ext, refl }


/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def subfield.to_intermediate_field (S : subfield L)
  (algebra_map_mem : ∀ x, algebra_map K L x ∈ S) :
  intermediate_field K L :=
{ algebra_map_mem' := algebra_map_mem,
  .. S }

namespace intermediate_field

/-- An intermediate field inherits a field structure -/
instance to_field : field S :=
S.to_subfield.to_field

@[simp, norm_cast] lemma coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_neg (x : S) : (↑(-x) : L) = -↑x := rfl
@[simp, norm_cast] lemma coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_inv (x : S) : (↑(x⁻¹) : L) = (↑x)⁻¹ := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : S) : L) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : S) : L) = 1 := rfl

instance algebra : algebra K S :=
S.to_subalgebra.algebra

instance to_algebra : algebra S L :=
S.to_subalgebra.to_algebra

/-
-- Instances for `coe_sort (coe S)`.
-- TODO: do we really want this?
instance to_field' : field (S : set L) := S.to_field
instance algebra' : algebra K (S : set L) := S.algebra
instance to_algebra' : algebra (S : set L) L := S.to_algebra
-/

instance : is_scalar_tower K S L :=
is_scalar_tower.subalgebra' _ _ _ S.to_subalgebra

variables {L' : Type*} [field L'] [algebra K L']

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') : intermediate_field K L' :=
{ inv_mem' := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, S.inv_mem hx, f.map_inv x⟩ },
  neg_mem' := λ x hx, (S.to_subalgebra.map f).neg_mem hx,
  .. S.to_subalgebra.map f}

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
S.to_subalgebra.val

@[simp] theorem coe_val : ⇑S.val = coe := rfl

@[simp] lemma val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x := rfl

@[simp] lemma coe_pow {x : S} (n : ℕ) : ↑(x^n) = (x : L)^n := S.val.map_pow x n

@[simp] lemma pow_mk {x : L} (hx : x ∈ S) (n : ℕ) :
  (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, S.pow_mem hx n⟩ :=
by { ext, simp }

variables {S}

lemma to_subalgebra_injective {S S' : intermediate_field K L}
  (h : S.to_subalgebra = S'.to_subalgebra) : S = S' :=
by { ext, rw [← mem_to_subalgebra, ← mem_to_subalgebra, h] }

lemma to_subalgebra_inj_iff {S S' : intermediate_field K L} :
  (S.to_subalgebra = S'.to_subalgebra) ↔ (S = S') :=
⟨to_subalgebra_injective, λ h, h ▸ rfl⟩

instance : partial_order (intermediate_field K L) :=
{ le := λ S T, (S : set L) ⊆ T,
  le_refl := λ S, set.subset.refl S,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

variables (S)

lemma set_range_subset : set.range (algebra_map K L) ⊆ S :=
S.to_subalgebra.range_subset

lemma field_range_le : (algebra_map K L).field_range ≤ S.to_subfield :=
λ x hx, S.to_subalgebra.range_subset (by rwa [set.mem_range, ← ring_hom.mem_field_range])

@[simp] lemma to_subalgebra_le_to_subalgebra {S S' : intermediate_field K L} :
  S.to_subalgebra ≤ S'.to_subalgebra ↔ S ≤ S' := iff.rfl

@[simp] lemma to_subalgebra_lt_to_subalgebra {S S' : intermediate_field K L} :
  S.to_subalgebra < S'.to_subalgebra ↔ S < S' := iff.rfl

variables {S}

section tower

/-- Lift an intermediate_field of an intermediate_field -/
def lift1 {F : intermediate_field K L} (E : intermediate_field K F) : intermediate_field K L :=
  map E (val F)

/-- Lift an intermediate_field of an intermediate_field -/
def lift2 {F : intermediate_field K L} (E : intermediate_field F L) : intermediate_field K L :=
{ carrier := E.carrier,
  zero_mem' := zero_mem E,
  add_mem' := λ x y, add_mem E,
  neg_mem' := λ x, neg_mem E,
  one_mem' := one_mem E,
  mul_mem' := λ x y, mul_mem E,
  inv_mem' := λ x, inv_mem E,
  algebra_map_mem' := λ x, algebra_map_mem E (algebra_map K F x) }

instance has_lift1 {F : intermediate_field K L} :
  has_lift_t (intermediate_field K F) (intermediate_field K L) := ⟨lift1⟩

instance has_lift2 {F : intermediate_field K L} :
  has_lift_t (intermediate_field F L) (intermediate_field K L) := ⟨lift2⟩

@[simp] lemma mem_lift2 {F : intermediate_field K L} {E : intermediate_field F L} {x : L} :
  x ∈ (↑E : intermediate_field K L) ↔ x ∈ E := iff.rfl

instance lift2_alg {F : intermediate_field K L} {E : intermediate_field F L} : algebra K E :=
{ to_fun := (algebra_map F E).comp (algebra_map K F),
  map_zero' := ((algebra_map F E).comp (algebra_map K F)).map_zero,
  map_one' := ((algebra_map F E).comp (algebra_map K F)).map_one,
  map_add' := ((algebra_map F E).comp (algebra_map K F)).map_add,
  map_mul' := ((algebra_map F E).comp (algebra_map K F)).map_mul,
  smul := λ a b, (((algebra_map F E).comp (algebra_map K F)) a) * b,
  smul_def' := λ _ _, rfl,
  commutes' := λ a b, mul_comm (((algebra_map F E).comp (algebra_map K F)) a) b }

instance lift2_tower {F : intermediate_field K L} {E : intermediate_field F L} :
  is_scalar_tower K F E :=
⟨λ a b c, by { simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc], refl }⟩

/-- `lift2` is isomorphic to the original `intermediate_field`. -/
def lift2_alg_equiv {F : intermediate_field K L} (E : intermediate_field F L) :
  (↑E : intermediate_field K L) ≃ₐ[K] E :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := λ x, rfl,
  right_inv := λ x, rfl,
  map_add' := λ x y, rfl,
  map_mul' := λ x y, rfl,
  commutes' := λ x, rfl }

end tower

section finite_dimensional

variables (F E : intermediate_field K L)

instance finite_dimensional_left [finite_dimensional K L] : finite_dimensional K F :=
finite_dimensional.finite_dimensional_submodule F.to_subalgebra.to_submodule

instance finite_dimensional_right [finite_dimensional K L] : finite_dimensional F L :=
right K F L

@[simp] lemma dim_eq_dim_subalgebra :
  vector_space.dim K F.to_subalgebra = vector_space.dim K F := rfl

@[simp] lemma findim_eq_findim_subalgebra :
  findim K F.to_subalgebra = findim K F := rfl

variables {F} {E}

@[simp] lemma to_subalgebra_eq_iff : F.to_subalgebra = E.to_subalgebra ↔ F = E :=
by { rw [subalgebra.ext_iff, intermediate_field.ext'_iff, set.ext_iff], refl }

lemma eq_of_le_of_findim_le [finite_dimensional K L] (h_le : F ≤ E)
  (h_findim : findim K E ≤ findim K F) : F = E :=
intermediate_field.ext'_iff.mpr (submodule.ext'_iff.mp (eq_of_le_of_findim_le
  (show F.to_subalgebra.to_submodule ≤ E.to_subalgebra.to_submodule, by exact h_le) h_findim))

lemma eq_of_le_of_findim_eq [finite_dimensional K L] (h_le : F ≤ E)
  (h_findim : findim K F = findim K E) : F = E :=
eq_of_le_of_findim_le h_le h_findim.ge

lemma eq_of_le_of_findim_le' [finite_dimensional K L] (h_le : F ≤ E)
  (h_findim : findim F L ≤ findim E L) : F = E :=
begin
  apply eq_of_le_of_findim_le h_le,
  have h1 := findim_mul_findim K F L,
  have h2 := findim_mul_findim K E L,
  have h3 : 0 < findim E L := findim_pos,
  nlinarith,
end

lemma eq_of_le_of_findim_eq' [finite_dimensional K L] (h_le : F ≤ E)
  (h_findim : findim F L = findim E L) : F = E :=
eq_of_le_of_findim_le' h_le h_findim.le

end finite_dimensional

section algebraic

lemma is_algebraic (S : intermediate_field K L)
  {x : S} (hx : is_algebraic K (x : L)) :
  is_algebraic K x :=
is_scalar_tower.is_algebraic (algebra_map S L).injective hx

end algebraic

end intermediate_field

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L) :
  subalgebra K L ≃o intermediate_field K L :=
{ to_fun := λ S, S.to_intermediate_field (λ x hx, S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S))),
  inv_fun := λ S, S.to_subalgebra,
  left_inv := λ S, to_subalgebra_to_intermediate_field _ _,
  right_inv := λ S, to_intermediate_field_to_subalgebra _ _,
  map_rel_iff' := λ S S', iff.rfl }

@[simp] lemma mem_subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L)
  {S : subalgebra K L} {x : L} :
  x ∈ subalgebra_equiv_intermediate_field alg S ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_subalgebra_equiv_intermediate_field_symm (alg : algebra.is_algebraic K L)
  {S : intermediate_field K L} {x : L} :
  x ∈ (subalgebra_equiv_intermediate_field alg).symm S ↔ x ∈ S :=
iff.rfl
