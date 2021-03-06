# A formalization of Dedekind domains and class groups of global fields

This repository contains the source code for the paper "A formalization of Dedekind domains and class groups of global fields", [to be presented at ITP 2021](http://easyconferences.eu/itp2021/).

Dedekind domains and their class groups are notions in commutative algebra that are essential in algebraic number theory.
We formalized these structures and several fundamental properties, including number theoretic finiteness results for class groups, in the Lean prover as part of the [mathlib mathematical library](https://github.com/leanprover-community/mathlib).

## Installation instructions

The formalization has been developed for the community fork of Lean 3.
To install a full Lean development environment, please follow the "Regular install" instructions at <https://leanprover-community.github.io/get_started.html>.
After installation, you can run the command `leanproject get lean-forward/class-number` to obtain copies of the relevant source files and all dependencies.
We are currently in the process of merging our results into the Lean mathematical library mathlib.
An up-to-date version of our development is available at the [dedekind-domain-dev branch](https://github.com/leanprover-community/mathlib/tree/dedekind-domain-dev/).
The command `leanproject get mathlib:dedekind-domain-dev` will download a copy of this branch and the precompiled binaries.

When opening a Lean project in VS Code, you must use the "Open Folder" menu option to open the project's root directory.
On the command line, you can run `code path/to/class-number`.

## Code overview

The following files contain major contributions from our project:

 * [`src/algebraic_number_theory/class_number.lean`](src/class_number.lean)
 * [`src/algebraic_number_theory/class_number/admissible_absolute_value.lean`](src/admissible_absolute_value.lean)
 * [`src/algebraic_number_theory/function_field.lean`](src/function_field.lean)
 * [`src/algebraic_number_theory/number_field.lean`](src/number_field.lean)
 * [`src/field_theory/intermediate_field.lean`](src/intermediate_field.lean)
 * [`src/field_theory/subfield.lean`](src/subfield.lean)
 * [`src/ring_theory/class_group.lean`](src/class_group.lean)
 * [`src/ring_theory/dedekind_domain.lean`](src/dedekind_domain.lean)
 * [`src/ring_theory/fractional_ideal.lean`](src/fractional_ideal.lean)
 * [`src/ring_theory/power_basis.lean`](src/power_basis.lean)
 * [`src/ring_theory/trace.lean`](src/trace.lean)

The following files contain declarations mentioned in the paper or otherwise important to understanding our formalization:

 * [`src/group_theory/group_action/defs.lean`](src/defs.lean)
 * [`src/field_theory/adjoin.lean`](src/adjoin.lean)
 * [`src/field_theory/primitive_element.lean`](src/primitive_element.lean)
 * [`src/ring_theory/integral_closure.lean`](src/integral_closure.lean)
 * [`src/ring_theory/localization.lean`](src/localization.lean)
 * [`src/ring_theory/noetherian.lean`](src/noetherian.lean)
 * [`src/ring_theory/principal_ideal_domain.lean`](src/principal_ideal_domain.lean)
 * [`src/ring_theory/unique_factorization_domain.lean`](src/unique_factorization_domain.lean)

## Declarations mentioned in the paper

We will now provide an overview of the source code files containing results mentioned in the paper.

### Section 3

 * number fields: [`src/algebraic_number_theory/number_field.lean`](src/number_field.lean)
 * function fields: [`src/algebraic_number_theory/function_field.lean`](src/function_field.lean)
 * scalar towers: [`src/group_theory/group_action/defs.lean`](src/defs.lean)
 * ring of integers (of a number field): [`src/algebraic_number_theory/number_field.lean`](src/number_field.lean)
 * ring of integers (of a function field): [`src/algebraic_number_theory/function_field.lean`](src/function_field.lean)
 * subfield: [`src/field_theory/subfield.lean`](src/subfield.lean)
 * intermediate field: [`src/field_theory/intermediate_field.lean`](src/intermediate_field.lean)
 * fraction field, fraction map: [`src/ring_theory/localization.lean`](src/localization.lean)
 * power basis: [`src/ring_theory/power_basis.lean`](src/power_basis.lean)


### Section 4

 * Dedekind domain: [`src/ring_theory/dedekind_domain.lean`](src/dedekind_domain.lean)
 * Krull dimension: [`src/ring_theory/dedekind_domain.lean`](src/dedekind_domain.lean)
 * integral closure: [`src/ring_theory/integral_closure.lean`](src/integral_closure.lean)
 * Noetherian ring: [`src/ring_theory/noetherian.lean`](src/noetherian.lean)
 * fractional ideal: [`src/ring_theory/fractional_ideal.lean`](src/fractional_ideal.lean)

### Section 5
 * principal ideal domain: [`src/ring_theory/principal_ideal_domain.lean`](src/principal_ideal_domain.lean)
 * unique factorization monoid (UFM): [`src/ring_theory/unique_factorization_domain.lean`](src.unique_factorization_domain.lean)

### Section 6
 * trace form: [`src/ring_theory/trace.lean`](src/trace.lean)
 * minimal polynomial: [`src/ring_theory/power_basis.lean`](src/power_basis.lean)
 * conjugate element: [`src/ring_theory/trace.lean`](src/trace.lean)

### Section 7
 * class group: [`src/ring_theory/class_group.lean`](src/class_group.lean)
 * admissible absolute value: [`src/algebraic_number_theory/class_number/admissible_absolute_value.lean`](src/admissible_absolute_value.lean)
 * class number: [`src/algebraic_number_theory/class_number.lean`](src/class_number.lean)
 * ring of integers of ℚ: [`src/algebraic_number_theory/number_field.lean`](src/number_field.lean)
 * class number of ℚ: [`src/algebraic_number_theory/class_number.lean`](src/class_number.lean)
