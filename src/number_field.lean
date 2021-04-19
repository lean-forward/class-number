/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ashvni Narayanan, Anne Baanen
-/

import algebra.field
import data.rat.basic
import ring_theory.algebraic
import ring_theory.dedekind_domain
import ring_theory.integral_closure

/-!
# Number fields

This file defines a number field and the ring of integers corresponding to it.

## Main definitions

 - `is_number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Main results

 - `is_dedekind_domain_of_ring_of_integers`: Shows that the ring of integers of a number field is a
    Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags

number field, ring of integers
-/

/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class is_number_field (K : Type*) [field K] : Prop :=
[cz : char_zero K]
[fd : finite_dimensional ℚ K]

open function
open_locale classical big_operators

namespace number_field
variables (K : Type*) [field K] [is_number_field K]

@[priority 100] -- See note [lower instance priority]
instance char_zero : char_zero K := is_number_field.cz

lemma finite_dimensional_of_number_field : finite_dimensional ℚ K := is_number_field.fd

lemma is_algebraic_of_number_field : algebra.is_algebraic ℚ K :=
  @algebra.is_algebraic_of_finite ℚ K _ _ _ (finite_dimensional_of_number_field K)

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
@[nolint unused_arguments] -- There are multiple definitions of rings of integers.
def ring_of_integers := integral_closure ℤ K

namespace ring_of_integers

open fraction_map
local attribute [class] algebra.is_algebraic

-- TODO: we should make `fraction_map` extend `algebra`, so we don't need to add these instances.
instance : algebra int.fraction_map.codomain K := rat.algebra_rat
instance is_scalar_tower_int_rat :
  @is_scalar_tower ℤ int.fraction_map.codomain K int.fraction_map.algebra.to_has_scalar _ _ :=
is_scalar_tower.of_algebra_map_eq (λ x, by simp)
instance : char_zero int.fraction_map.codomain := show char_zero ℚ, by apply_instance
instance : finite_dimensional int.fraction_map.codomain K := ‹is_number_field K›.fd
instance : algebra.is_algebraic int.fraction_map.codomain K := is_algebraic_of_number_field K

variables {K}

lemma is_integral_coe (x : ring_of_integers K) : is_integral ℤ (x : K) :=
x.2

lemma char_zero.algebra_map_injective {R : Type*} [semiring R] [char_zero R]
  [algebra ℕ R] : function.injective (algebra_map ℕ R) :=
λ x y hxy, by simpa using hxy

lemma char_zero.of_algebra_map_injective {R : Type*} [semiring R] [algebra ℕ R]
  (h : function.injective (algebra_map ℕ R)) : char_zero R :=
⟨λ x y hxy, h (by simpa using hxy)⟩

lemma char_zero.iff_algebra_map_injective {R : Type*} [semiring R] [algebra ℕ R] :
  char_zero R ↔ function.injective (algebra_map ℕ R) :=
⟨λ h, @char_zero.algebra_map_injective _ _ h _,
 char_zero.of_algebra_map_injective⟩

variables (K)

instance : char_zero (ring_of_integers K) :=
char_zero.of_algebra_map_injective (injective.of_comp
  (show injective (algebra_map _ K ∘ _),
   from
   have inj : injective (algebra_map ℕ K) := char_zero.algebra_map_injective,
   have tower : is_scalar_tower ℕ (ring_of_integers K) K := infer_instance,
   by rwa [@is_scalar_tower.algebra_map_eq ℕ (ring_of_integers K) K _ _ _ _ _ _ (by convert tower)] at inj))

instance integral_closure_int.is_dedekind_domain : is_dedekind_domain (integral_closure ℤ K) :=
is_dedekind_domain.integral_closure int.fraction_map (principal_ideal_ring.is_dedekind_domain _)

instance is_dedekind_domain_of_ring_of_integers : is_dedekind_domain (ring_of_integers K) :=
integral_closure_int.is_dedekind_domain K

/-- `ring_of_integers.fraction_map K` is the map `O_K → K`, as a `fraction_map`. -/
protected def fraction_map : fraction_map (ring_of_integers K) K :=
integral_closure.fraction_map_of_finite_extension K int.fraction_map

end ring_of_integers

end number_field

namespace rat

open fraction_map
open number_field

instance rat.finite_dimensional : finite_dimensional ℚ ℚ :=
(infer_instance : is_noetherian ℚ ℚ)

instance rat.is_number_field : is_number_field ℚ :=
{ cz := infer_instance,
  fd := by { convert rat.finite_dimensional,
             -- The vector space structure of `ℚ` over itself can arise in multiple ways:
             -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
             -- all fields have a canonical embedding of `ℚ` (used in `is_number_field`).
             -- Show that these coincide:
             ext, simp [algebra.smul_def] } }

lemma subalgebra.coe_algebra_map {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]
  (S : subalgebra R A) :
  ⇑(algebra_map S A) = (coe : S → A) :=
rfl

noncomputable def rat.ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
ring_equiv.symm $
ring_equiv.of_bijective (algebra_map ℤ (ring_of_integers ℚ))
  ⟨λ x y hxy, int.cast_injective $
      show (x : ring_of_integers ℚ) = (y : ring_of_integers ℚ), by simpa using hxy,
   λ y, begin
     obtain ⟨x, hx⟩ := @unique_factorization_monoid.integer_of_integral ℤ ℚ _ _ _
       fraction_map.int.fraction_map (y : ℚ) (ring_of_integers.is_integral_coe y),
     use x,
     refine subtype.coe_injective _,
     rw [← hx, ← subalgebra.coe_algebra_map, ← is_scalar_tower.algebra_map_apply ℤ _ _,
         ring_hom.eq_int_cast (algebra_map ℤ ℚ), ring_hom.eq_int_cast],
     -- Again we have to show the vector space structures on ℚ coincide.
     convert @is_scalar_tower.of_algebra_map_eq ℤ (ring_of_integers ℚ) ℚ _ _ _ _ _ _ _,
     { ext, simp [algebra.smul_def] },
     { simp }
   end⟩

end rat
