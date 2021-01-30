/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.intermediate_field
import field_theory.minimal_polynomial
import field_theory.splitting_field
import field_theory.fixed
import field_theory.minimal_polynomial
import ring_theory.adjoin_root

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_dim_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

open finite_dimensional
open_locale classical

namespace intermediate_field

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : intermediate_field F E :=
{ algebra_map_mem' := λ x, subfield.subset_closure (or.inl (set.mem_range_self x)),
  ..subfield.closure (set.range (algebra_map F E) ∪ S) }

end adjoin_def

section lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

@[simp] lemma adjoin_le_iff {S : set E} {T : intermediate_field F E} : adjoin F S ≤ T ↔ S ≤ T :=
⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subfield.subset_closure) H,
  λ H, (@subfield.closure_le E _ (set.range (algebra_map F E) ∪ S) T.to_subfield).mpr
  (set.union_subset (intermediate_field.set_range_subset T) H)⟩

lemma gc : galois_connection (adjoin F : set E → intermediate_field F E) coe := λ _ _, adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : galois_insertion (adjoin F : set E → intermediate_field F E) coe :=
{ choice := λ S _, adjoin F S,
  gc := intermediate_field.gc,
  le_l_u := λ S, (intermediate_field.gc (S : set E) (adjoin F S)).1 $ le_refl _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (intermediate_field F E) :=
galois_insertion.lift_complete_lattice intermediate_field.gi

instance : inhabited (intermediate_field F E) := ⟨⊤⟩

lemma mem_bot {x : E} : x ∈ (⊥ : intermediate_field F E) ↔ x ∈ set.range (algebra_map F E) :=
begin
  suffices : set.range (algebra_map F E) = (⊥ : intermediate_field F E),
  { rw this, refl },
  { change set.range (algebra_map F E) = subfield.closure (set.range (algebra_map F E) ∪ ∅),
    simp [←set.image_univ, ←ring_hom.map_field_closure] }
end

lemma mem_top {x : E} : x ∈ (⊤ : intermediate_field F E) :=
subfield.subset_closure $ or.inr trivial

@[simp] lemma bot_to_subalgebra : (⊥ : intermediate_field F E).to_subalgebra = ⊥ :=
by { ext, rw [mem_to_subalgebra, algebra.mem_bot, mem_bot] }

@[simp] lemma top_to_subalgebra : (⊤ : intermediate_field F E).to_subalgebra = ⊤ :=
by { ext, rw [mem_to_subalgebra, iff_true_right algebra.mem_top], exact mem_top }

/--  Construct an algebra isomorphism from an equality of subalgebras -/
def subalgebra.equiv_of_eq {X Y : subalgebra F E} (h : X = Y) : X ≃ₐ[F] Y :=
by refine { to_fun := λ x, ⟨x, _⟩, inv_fun := λ x, ⟨x, _⟩, .. }; tidy

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def bot_equiv : (⊥ : intermediate_field F E) ≃ₐ[F] F :=
(subalgebra.equiv_of_eq bot_to_subalgebra).trans (algebra.bot_equiv F E)

@[simp] lemma bot_equiv_def (x : F) :
  bot_equiv (algebra_map F (⊥ : intermediate_field F E) x) = x :=
alg_equiv.commutes bot_equiv x

noncomputable instance algebra_over_bot : algebra (⊥ : intermediate_field F E) F :=
  ring_hom.to_algebra intermediate_field.bot_equiv.to_alg_hom.to_ring_hom

instance is_scalar_tower_over_bot : is_scalar_tower (⊥ : intermediate_field F E) F E :=
is_scalar_tower.of_algebra_map_eq
begin
  intro x,
  let ϕ := algebra.of_id F (⊥ : subalgebra F E),
  let ψ := alg_equiv.of_bijective ϕ ((algebra.bot_equiv F E).symm.bijective),
  change (↑x : E) = ↑(ψ (ψ.symm ⟨x, _⟩)),
  rw alg_equiv.apply_symm_apply ψ ⟨x, _⟩,
  refl
end

/-- The top intermediate_field is isomorphic to the field. -/
noncomputable def top_equiv : (⊤ : intermediate_field F E) ≃ₐ[F] E :=
(subalgebra.equiv_of_eq top_to_subalgebra).trans algebra.top_equiv

@[simp] lemma top_equiv_def (x : (⊤ : intermediate_field F E)) : top_equiv x = ↑x :=
begin
  suffices : algebra.to_top (top_equiv x) = algebra.to_top (x : E),
  { rwa subtype.ext_iff at this },
  exact alg_equiv.apply_symm_apply (alg_equiv.of_bijective algebra.to_top
    ⟨λ _ _, subtype.mk.inj, λ x, ⟨x.val, by { ext, refl }⟩⟩ : E ≃ₐ[F] (⊤ : subalgebra F E))
    (subalgebra.equiv_of_eq top_to_subalgebra x),
end

@[simp] lemma coe_bot_eq_self (K : intermediate_field F E) : ↑(⊥ : intermediate_field K E) = K :=
by { ext, rw [mem_lift2, mem_bot], exact set.ext_iff.mp subtype.range_coe x }

@[simp] lemma coe_top_eq_top (K : intermediate_field F E) :
  ↑(⊤ : intermediate_field K E) = (⊤ : intermediate_field F E) :=
intermediate_field.ext'_iff.mpr (set.ext_iff.mpr (λ _, iff_of_true mem_top mem_top))

end lattice

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

lemma adjoin_eq_range_algebra_map_adjoin :
  (adjoin F S : set E) = set.range (algebra_map (adjoin F S) E) := (subtype.range_coe).symm

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
intermediate_field.algebra_map_mem (adjoin F S) x

lemma adjoin.range_algebra_map_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ← hf,
  exact adjoin.algebra_map_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.algebra_map_mem F S x⟩}

lemma subset_adjoin : S ⊆ adjoin F S :=
λ x hx, subfield.subset_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

@[mono] lemma adjoin.mono (T : set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
galois_connection.monotone_l gc h

lemma adjoin_contains_field_as_subfield (F : subfield E) : (F : set E) ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, hx⟩

lemma subset_adjoin_of_subset_left {F : subfield E} {T : set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
λ x hx, subset_adjoin F S (H hx)

@[simp] lemma adjoin_empty (F E : Type*) [field F] [field E] [algebra F E] :
  adjoin F (∅ : set E) = ⊥ :=
eq_bot_iff.mpr (adjoin_le_iff.mpr (set.empty_subset _))

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
lemma adjoin_le_subfield {K : subfield E} (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S).to_subfield ≤ K :=
begin
  apply subfield.closure_le.mpr,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, subfield.closure_le.mpr (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) : ↑(adjoin (adjoin F S) T) = adjoin F (S ∪ T) :=
begin
  rw intermediate_field.ext'_iff,
  change ↑(adjoin (adjoin F S) T) = _,
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { rintros _ ⟨⟨x, hx⟩, rfl⟩, exact adjoin.mono _ _ _ (set.subset_union_left _ _) hx },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

@[simp] lemma adjoin_insert_adjoin (x : E) :
  adjoin F (insert x (adjoin F S : set E)) = adjoin F (insert x S) :=
le_antisymm
  (adjoin_le_iff.mpr (set.insert_subset.mpr ⟨subset_adjoin _ _ (set.mem_insert _ _),
   adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (set.subset_insert _ _))⟩))
  (adjoin.mono _ _ _ (set.insert_subset_insert (subset_adjoin _ _)))

/-- `F[S][T] = F[T][S]` -/
lemma adjoin_adjoin_comm (T : set E) :
  ↑(adjoin (adjoin F S) T) = (↑(adjoin (adjoin F T) S) : (intermediate_field F E)) :=
by rw [adjoin_adjoin_left, adjoin_adjoin_left, set.union_comm]

lemma adjoin_map {E' : Type*} [field E'] [algebra F E'] (f : E →ₐ[F] E') :
  (adjoin F S).map f = adjoin F (f '' S) :=
begin
  ext x,
  show x ∈ (subfield.closure (set.range (algebra_map F E) ∪ S)).map (f : E →+* E') ↔
       x ∈ subfield.closure (set.range (algebra_map F E') ∪ f '' S),
  rw [ring_hom.map_field_closure, set.image_union, ← set.range_comp, ← ring_hom.coe_comp,
      f.comp_algebra_map],
  refl,
end

lemma algebra_adjoin_le_adjoin : algebra.adjoin F S ≤ (adjoin F S).to_subalgebra :=
algebra.adjoin_le (subset_adjoin _ _)

lemma adjoin_eq_algebra_adjoin (inv_mem : ∀ x ∈ algebra.adjoin F S, x⁻¹ ∈ algebra.adjoin F S) :
  (adjoin F S).to_subalgebra = algebra.adjoin F S :=
le_antisymm
  (show adjoin F S ≤
      { neg_mem' := λ x, (algebra.adjoin F S).neg_mem, inv_mem' := inv_mem, .. algebra.adjoin F S},
    from adjoin_le_iff.mpr (algebra.subset_adjoin))
  (algebra_adjoin_le_adjoin _ _)

lemma eq_adjoin_of_eq_algebra_adjoin (K : intermediate_field F E)
  (h : K.to_subalgebra = algebra.adjoin F S) : K = adjoin F S :=
begin
  apply to_subalgebra_injective,
  rw h,
  refine (adjoin_eq_algebra_adjoin _ _ _).symm,
  intros x,
  convert K.inv_mem,
  rw ← h,
  refl
end

@[elab_as_eliminator]
lemma adjoin_induction {s : set E} {p : E → Prop} {x} (h : x ∈ adjoin F s)
  (Hs : ∀ x ∈ s, p x) (Hmap : ∀ x, p (algebra_map F E x))
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ x, p x → p (-x))
  (Hinv : ∀ x, p x → p x⁻¹)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
subfield.closure_induction h (λ x hx, or.cases_on hx (λ ⟨x, hx⟩, hx ▸ Hmap x) (Hs x))
  ((algebra_map F E).map_one ▸ Hmap 1)
  Hadd Hneg Hinv Hmul

/--
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip
class insert {α : Type*} (s : set α) :=
(insert : α → set α)

@[priority 1000]
instance insert_empty {α : Type*} : insert (∅ : set α) :=
{ insert := λ x, @singleton _ _ set.has_singleton x }

@[priority 900]
instance insert_nonempty {α : Type*} (s : set α) : insert s :=
{ insert := λ x, set.insert x s }

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, insert.insert t h) ∅) `⟯` := adjoin K l

section adjoin_simple
variables (α : E)

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
subset_adjoin F {α} (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

@[simp] lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_adjoin_simple (β : E) : ↑F⟮α⟯⟮β⟯ = F⟮α, β⟯ :=
adjoin_adjoin_left _ _ _

lemma adjoin_simple_comm (β : E) : ↑F⟮α⟯⟮β⟯ = (↑F⟮β⟯⟮α⟯ : intermediate_field F E) :=
adjoin_adjoin_comm _ _ _

-- TODO: develop the API for `subalgebra.is_field_of_algebraic` so it can be used here
lemma adjoin_simple_to_subalgebra_of_integral (hα : is_integral F α) :
  (F⟮α⟯).to_subalgebra = algebra.adjoin F {α} :=
begin
  apply adjoin_eq_algebra_adjoin,
  intros x hx,
  by_cases x = 0,
  { rw [h, inv_zero], exact subalgebra.zero_mem (algebra.adjoin F {α}) },

  let ϕ := alg_equiv.adjoin_singleton_equiv_adjoin_root_minimal_polynomial F α hα,
  haveI := minimal_polynomial.irreducible hα,
  suffices : ϕ ⟨x, hx⟩ * (ϕ ⟨x, hx⟩)⁻¹ = 1,
  { convert subtype.mem (ϕ.symm (ϕ ⟨x, hx⟩)⁻¹),
    refine (eq_inv_of_mul_right_eq_one _).symm,
    apply_fun ϕ.symm at this,
    rw [alg_equiv.map_one, alg_equiv.map_mul, alg_equiv.symm_apply_apply] at this,
    rw [←subsemiring.coe_one, ←this, subsemiring.coe_mul, subtype.coe_mk] },

  rw mul_inv_cancel (mt (λ key, _) h),
  rw ← ϕ.map_zero at key,
  change ↑(⟨x, hx⟩ : algebra.adjoin F {α}) = _,
  rw [ϕ.injective key, submodule.coe_zero]
end

end adjoin_simple
end adjoin_def

section adjoin_intermediate_field_lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {α : E} {S : set E}

@[simp] lemma adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : intermediate_field F E) :=
by { rw [eq_bot_iff, adjoin_le_iff], refl, }

@[simp] lemma adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw adjoin_eq_bot_iff, exact set.singleton_subset_iff }

@[simp] lemma adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp] lemma adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp] lemma adjoin_int (n : ℤ) : F⟮(n : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

@[simp] lemma adjoin_nat (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

section adjoin_dim
open finite_dimensional vector_space

variables {K L : intermediate_field F E}

@[simp] lemma dim_eq_one_iff : dim F K = 1 ↔ K = ⊥ :=
by rw [← to_subalgebra_eq_iff, ← dim_eq_dim_subalgebra,
  subalgebra.dim_eq_one_iff, bot_to_subalgebra]

@[simp] lemma findim_eq_one_iff : findim F K = 1 ↔ K = ⊥ :=
by rw [← to_subalgebra_eq_iff, ← findim_eq_findim_subalgebra,
  subalgebra.findim_eq_one_iff, bot_to_subalgebra]

lemma dim_adjoin_eq_one_iff : dim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
iff.trans dim_eq_one_iff adjoin_eq_bot_iff

lemma dim_adjoin_simple_eq_one_iff : dim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw dim_adjoin_eq_one_iff, exact set.singleton_subset_iff }

lemma findim_adjoin_eq_one_iff : findim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
iff.trans findim_eq_one_iff adjoin_eq_bot_iff

lemma findim_adjoin_simple_eq_one_iff : findim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw [findim_adjoin_eq_one_iff], exact set.singleton_subset_iff }

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_dim_adjoin_eq_one (h : ∀ x : E, dim F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact dim_adjoin_simple_eq_one_iff.mp (h x),
end

lemma bot_eq_top_of_findim_adjoin_eq_one (h : ∀ x : E, findim F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact findim_adjoin_simple_eq_one_iff.mp (h x),
end

lemma subsingleton_of_dim_adjoin_eq_one (h : ∀ x : E, dim F F⟮x⟯ = 1) :
  subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_dim_adjoin_eq_one h)

lemma subsingleton_of_findim_adjoin_eq_one (h : ∀ x : E, findim F F⟮x⟯ = 1) :
  subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_findim_adjoin_eq_one h)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_findim_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, findim F F⟮x⟯ ≤ 1) : (⊥ : intermediate_field F E) = ⊤ :=
begin
  apply bot_eq_top_of_findim_adjoin_eq_one,
  exact λ x, by linarith [h x, show 0 < findim F F⟮x⟯, from findim_pos],
end

lemma subsingleton_of_findim_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, findim F F⟮x⟯ ≤ 1) : subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_findim_adjoin_le_one h)

end adjoin_dim
end adjoin_intermediate_field_lattice

section adjoin_integral_element

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] {α : E}
variables {K : Type*} [field K] [algebra F K]

lemma aeval_gen_minimal_polynomial (h : is_integral F α) :
  polynomial.aeval (adjoin_simple.gen F α) (minimal_polynomial h) = 0 :=
begin
  ext,
  convert minimal_polynomial.aeval h,
  conv in (polynomial.aeval α) { rw [← adjoin_simple.algebra_map_gen F α] },
  exact is_scalar_tower.algebra_map_aeval F F⟮α⟯ E _ _
end

/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
noncomputable def adjoin_root_equiv_adjoin (h : is_integral F α) :
  adjoin_root (minimal_polynomial h) ≃ₐ[F] F⟮α⟯ :=
alg_equiv.of_bijective (alg_hom.mk (adjoin_root.lift (algebra_map F F⟮α⟯)
  (adjoin_simple.gen F α) (aeval_gen_minimal_polynomial F h)) (ring_hom.map_one _)
  (λ x y, ring_hom.map_mul _ x y) (ring_hom.map_zero _) (λ x y, ring_hom.map_add _ x y)
  (by { exact λ _, adjoin_root.lift_of })) (begin
    set f := adjoin_root.lift _ _ (aeval_gen_minimal_polynomial F h),
    haveI := minimal_polynomial.irreducible h,
    split,
    { exact ring_hom.injective f },
    { suffices : F⟮α⟯.to_subfield ≤ ring_hom.field_range ((F⟮α⟯.to_subfield.subtype).comp f),
      { exact λ x, Exists.cases_on (this (subtype.mem x)) (λ y hy, ⟨y, subtype.ext hy.2⟩) },
      exact subfield.closure_le.mpr (set.union_subset (λ x hx, Exists.cases_on hx (λ y hy, ⟨y,
        ⟨subfield.mem_top y, by { rw [ring_hom.comp_apply, adjoin_root.lift_of], exact hy }⟩⟩))
        (set.singleton_subset_iff.mpr ⟨adjoin_root.root (minimal_polynomial h),
        ⟨subfield.mem_top (adjoin_root.root (minimal_polynomial h)),
        by { rw [ring_hom.comp_apply, adjoin_root.lift_root], refl }⟩⟩)) } end)

lemma adjoin_root_equiv_adjoin_apply_root (h : is_integral F α) :
  adjoin_root_equiv_adjoin F h (adjoin_root.root (minimal_polynomial h)) =
    adjoin_simple.gen F α :=
begin
  refine adjoin_root.lift_root,
  { exact minimal_polynomial h },
  { exact aeval_gen_minimal_polynomial F h }
end

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minimal_polynomial α` in `K`. -/
noncomputable def alg_hom_adjoin_integral_equiv (h : is_integral F α) :
  (F⟮α⟯ →ₐ[F] K) ≃ {x // x ∈ ((minimal_polynomial h).map (algebra_map F K)).roots} :=
let ϕ := adjoin_root_equiv_adjoin F h,
  swap1 : (F⟮α⟯ →ₐ[F] K) ≃ (adjoin_root (minimal_polynomial h) →ₐ[F] K) :=
  { to_fun := λ f, f.comp ϕ.to_alg_hom,
    inv_fun := λ f, f.comp ϕ.symm.to_alg_hom,
    left_inv := λ _, by { ext, simp only [alg_equiv.coe_alg_hom,
      alg_equiv.to_alg_hom_eq_coe, alg_hom.comp_apply, alg_equiv.apply_symm_apply]},
    right_inv := λ _, by { ext, simp only [alg_equiv.symm_apply_apply,
      alg_equiv.coe_alg_hom, alg_equiv.to_alg_hom_eq_coe, alg_hom.comp_apply] } },
  swap2 := adjoin_root.equiv F K (minimal_polynomial h) (minimal_polynomial.ne_zero h) in
swap1.trans swap2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintype_of_alg_hom_adjoin_integral (h : is_integral F α) :
  fintype (F⟮α⟯ →ₐ[F] K) :=
fintype.of_equiv _ (alg_hom_adjoin_integral_equiv F h).symm

lemma card_alg_hom_adjoin_integral (h : is_integral F α) (h_sep : (minimal_polynomial h).separable)
  (h_splits : (minimal_polynomial h).splits (algebra_map F K)) :
  @fintype.card (F⟮α⟯ →ₐ[F] K) (fintype_of_alg_hom_adjoin_integral F h) =
    (minimal_polynomial h).nat_degree :=
begin
  let s := ((minimal_polynomial h).map (algebra_map F K)).roots.to_finset,
  have H := λ x, multiset.mem_to_finset,
  rw [fintype.card_congr (alg_hom_adjoin_integral_equiv F h), fintype.card_of_subtype s H,
      polynomial.nat_degree_eq_card_roots h_splits, multiset.to_finset_card_of_nodup],
  exact polynomial.nodup_roots ((polynomial.separable_map (algebra_map F K)).mpr h_sep),
end

end adjoin_integral_element

section induction

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def fg (S : intermediate_field F E) : Prop := ∃ (t : finset E), adjoin F ↑t = S

lemma fg_adjoin_finset (t : finset E) : (adjoin F (↑t : set E)).fg :=
⟨t, rfl⟩

theorem fg_def {S : intermediate_field F E} : S.fg ↔ ∃ t : set E, set.finite t ∧ adjoin F t = S :=
⟨λ ⟨t, ht⟩, ⟨↑t, set.finite_mem_finset t, ht⟩,
 λ ⟨t, ht1, ht2⟩, ⟨ht1.to_finset, by rwa set.finite.coe_to_finset⟩⟩

theorem fg_bot : (⊥ : intermediate_field F E).fg :=
⟨∅, adjoin_empty F E⟩

lemma fg_of_fg_to_subalgebra (S : intermediate_field F E)
  (h : S.to_subalgebra.fg) : S.fg :=
begin
  cases h with t ht,
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩
end

lemma fg_of_noetherian (S : intermediate_field F E)
  [is_noetherian F E] : S.fg :=
S.fg_of_fg_to_subalgebra S.to_subalgebra.fg_of_noetherian

lemma induction_on_adjoin_finset (S : finset E) (P : intermediate_field F E → Prop) (base : P ⊥)
  (ih : ∀ (K : intermediate_field F E) (x ∈ S), P K → P ↑K⟮x⟯) : P (adjoin F ↑S) :=
begin
  apply finset.induction_on' S,
  { exact base },
  { intros a s h1 _ _ h4,
    rw [finset.coe_insert, set.insert_eq, set.union_comm, ←adjoin_adjoin_left],
    exact ih (adjoin F s) a h1 h4 }
end

lemma induction_on_adjoin_fg (P : intermediate_field F E → Prop)
  (base : P ⊥) (ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑K⟮x⟯)
  (K : intermediate_field F E) (hK : K.fg) : P K :=
begin
  obtain ⟨S, rfl⟩ := hK,
  exact induction_on_adjoin_finset S P base (λ K x _ hK, ih K x hK),
end

lemma induction_on_adjoin [fd : finite_dimensional F E] (P : intermediate_field F E → Prop)
  (base : P ⊥) (ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑K⟮x⟯)
  (K : intermediate_field F E) : P K :=
induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end induction

end intermediate_field
