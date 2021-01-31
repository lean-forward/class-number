/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson

-/
import algebra.gcd_monoid
import ring_theory.integral_domain
import ring_theory.noetherian

/--

# Unique factorization

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class wf_dvd_monoid (α : Type*) [comm_monoid_with_zero α] : Prop :=
(well_founded_dvd_not_unit : well_founded (@dvd_not_unit α _))

export wf_dvd_monoid (well_founded_dvd_not_unit)

@[priority 100]  -- see Note [lower instance priority]
instance is_noetherian_ring.wf_dvd_monoid [integral_domain α] [is_noetherian_ring α] :
  wf_dvd_monoid α :=
⟨by { convert inv_image.wf (λ a, ideal.span ({a} : set α)) (well_founded_submodule_gt _ _),
      ext,
      exact ideal.span_singleton_lt_span_singleton.symm }⟩

namespace wf_dvd_monoid

variables [comm_monoid_with_zero α]
open associates nat

theorem of_wf_dvd_monoid_associates (h : wf_dvd_monoid (associates α)): wf_dvd_monoid α :=
⟨begin
  haveI := h,
  refine (surjective.well_founded_iff mk_surjective _).2 wf_dvd_monoid.well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

variables [wf_dvd_monoid α]

instance wf_dvd_monoid_associates : wf_dvd_monoid (associates α) :=
⟨begin
  refine (surjective.well_founded_iff mk_surjective _).1 wf_dvd_monoid.well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

theorem well_founded_associates : well_founded ((<) : associates α → associates α → Prop) :=
subrelation.wf (λ x y, dvd_not_unit_of_lt) wf_dvd_monoid.well_founded_dvd_not_unit

local attribute [elab_as_eliminator] well_founded.fix

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
(irreducible_or_factor a ha).elim (λ hai, ⟨a, hai, dvd_refl _⟩)
  (well_founded.fix
    wf_dvd_monoid.well_founded_dvd_not_unit
    (λ a ih ha ha0 ⟨x, y, hx, hy, hxy⟩,
      have hx0 : x ≠ 0, from λ hx0, ha0 (by rw [← hxy, hx0, zero_mul]),
      (irreducible_or_factor x hx).elim
        (λ hxi, ⟨x, hxi, hxy ▸ by simp⟩)
        (λ hxf, let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy.symm⟩ hx hx0 hxf in
          ⟨i, hi.1, dvd.trans hi.2 (hxy ▸ by simp)⟩)) a ha ha0)

@[elab_as_eliminator] lemma induction_on_irreducible {P : α → Prop} (a : α)
  (h0 : P 0) (hu : ∀ u : α, is_unit u → P u)
  (hi : ∀ a i : α, a ≠ 0 → irreducible i → P a → P (i * a)) :
  P a :=
by haveI := classical.dec; exact
well_founded.fix wf_dvd_monoid.well_founded_dvd_not_unit
  (λ a ih, if ha0 : a = 0 then ha0.symm ▸ h0
    else if hau : is_unit a then hu a hau
    else let ⟨i, hii, ⟨b, hb⟩⟩ := exists_irreducible_factor hau ha0 in
      have hb0 : b ≠ 0, from λ hb0, by simp * at *,
      hb.symm ▸ hi _ _ hb0 hii (ih _ ⟨hb0, i,
        hii.1, by rw [hb, mul_comm]⟩))
  a

lemma exists_factors (a : α) : a ≠ 0 →
  ∃f : multiset α, (∀b ∈ f, irreducible b) ∧ associated f.prod a :=
wf_dvd_monoid.induction_on_irreducible a
  (λ h, (h rfl).elim)
  (λ u hu _, ⟨0, ⟨by simp [hu], associated.symm (by simp [hu, associated_one_iff_is_unit])⟩⟩)
  (λ a i ha0 hii ih hia0,
    let ⟨s, hs⟩ := ih ha0 in
    ⟨i ::ₘ s, ⟨by clear _let_match; finish,
      by { rw multiset.prod_cons,
           exact associated_mul_mul (by refl) hs.2 }⟩⟩)

end wf_dvd_monoid

theorem wf_dvd_monoid.of_well_founded_associates [comm_cancel_monoid_with_zero α]
  (h : well_founded ((<) : associates α → associates α → Prop)) : wf_dvd_monoid α :=
wf_dvd_monoid.of_wf_dvd_monoid_associates ⟨by { convert h, ext, exact associates.dvd_not_unit_iff_lt }⟩

theorem wf_dvd_monoid.iff_well_founded_associates [comm_cancel_monoid_with_zero α] :
  wf_dvd_monoid α ↔ well_founded ((<) : associates α → associates α → Prop) :=
⟨by apply wf_dvd_monoid.well_founded_associates, wf_dvd_monoid.of_well_founded_associates⟩
section prio
set_option default_priority 100 -- see Note [default priority]
/-- unique factorization monoids.

These are defined as `comm_cancel_monoid_with_zero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
class unique_factorization_monoid (α : Type*) [comm_cancel_monoid_with_zero α] extends wf_dvd_monoid α :
  Prop :=
(irreducible_iff_prime : ∀ {a : α}, irreducible a ↔ prime a)

instance ufm_of_gcd_of_wf_dvd_monoid [nontrivial α] [comm_cancel_monoid_with_zero α]
  [wf_dvd_monoid α] [gcd_monoid α] : unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, gcd_monoid.irreducible_iff_prime
  .. ‹wf_dvd_monoid α› }

instance associates.ufm [comm_cancel_monoid_with_zero α]
  [unique_factorization_monoid α] : unique_factorization_monoid (associates α) :=
{ irreducible_iff_prime := by { rw ← associates.irreducible_iff_prime_iff,
    apply unique_factorization_monoid.irreducible_iff_prime, }
  .. (wf_dvd_monoid.wf_dvd_monoid_associates : wf_dvd_monoid (associates α)) }

end prio

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 →
  ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a :=
by { simp_rw ← unique_factorization_monoid.irreducible_iff_prime,
     apply wf_dvd_monoid.exists_factors a }

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
begin
  simp_rw ← unique_factorization_monoid.irreducible_iff_prime at h₃,
  exact wf_dvd_monoid.induction_on_irreducible a h₁ h₂ h₃,
end

lemma factors_unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (irreducible_iff_prime.1 (hf p (by simp)))
      (λ q hq, irreducible_iff_prime.1 (hg _ hq)) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p ::ₘ f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

end unique_factorization_monoid

lemma prime_factors_unique [comm_cancel_monoid_with_zero α] : ∀ {f g : multiset α},
  (∀ x ∈ f, prime x) → (∀ x ∈ g, prime x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (irreducible_of_prime $ hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (hf p (by simp)) (λ q hq, hg _ hq) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p ::ₘ f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
lemma prime_factors_irreducible [comm_cancel_monoid_with_zero α] {a : α} {f : multiset α}
  (ha : irreducible a) (pfa : (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a) :
  ∃ p, a ~ᵤ p ∧ f = p ::ₘ 0 :=
begin
  haveI := classical.dec_eq α,
  refine multiset.induction_on f (λ h, (ha.1
    (associated_one_iff_is_unit.1 (associated.symm h))).elim) _ pfa.2 pfa.1,
  rintros p s _ ⟨u, hu⟩ hs,
  use p,
  have hs0 : s = 0,
  { by_contra hs0,
    obtain ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0,
    apply (hs q (by simp [hq])).2.1,
    refine (ha.2 ((p * ↑u) * (s.erase q).prod) _ _).resolve_left _,
    { rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons, multiset.cons_erase hq, ← hu,
        mul_comm, mul_comm p _, mul_assoc],
      simp, },
    apply mt is_unit_of_mul_is_unit_left (mt is_unit_of_mul_is_unit_left _),
    apply (hs p (multiset.mem_cons_self _ _)).2.1 },
  simp only [mul_one, multiset.prod_cons, multiset.prod_zero, hs0] at *,
  exact ⟨associated.symm ⟨u, hu⟩, rfl⟩,
end

section exists_prime_factors

variables [comm_cancel_monoid_with_zero α]
variables (pf : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a)

include pf

lemma wf_dvd_monoid.of_exists_prime_factors : wf_dvd_monoid α :=
⟨begin
  classical,
  apply rel_hom.well_founded (rel_hom.mk _ _) (with_top.well_founded_lt nat.lt_wf),
  { intro a,
    by_cases h : a = 0, { exact ⊤ },
    exact (classical.some (pf a h)).card },

  rintros a b ⟨ane0, ⟨c, hc, b_eq⟩⟩,
  rw dif_neg ane0,
  by_cases h : b = 0, { simp [h, lt_top_iff_ne_top] },
  rw [dif_neg h, with_top.coe_lt_coe],
  have cne0 : c ≠ 0, { refine mt (λ con, _) h, rw [b_eq, con, mul_zero] },
  calc multiset.card (classical.some (pf a ane0))
      < _ + multiset.card (classical.some (pf c cne0)) :
    lt_add_of_pos_right _ (multiset.card_pos.mpr (λ con, hc (associated_one_iff_is_unit.mp _)))
  ... = multiset.card (classical.some (pf a ane0) + classical.some (pf c cne0)) :
    (multiset.card_add _ _).symm
  ... = multiset.card (classical.some (pf b h)) :
    multiset.card_eq_card_of_rel (prime_factors_unique _ (classical.some_spec (pf _ h)).1 _),
  { convert (classical.some_spec (pf c cne0)).2.symm,
    rw [con, multiset.prod_zero] },
  { intros x hadd,
    rw multiset.mem_add at hadd,
    cases hadd; apply (classical.some_spec (pf _ _)).1 _ hadd },
  { rw multiset.prod_add,
    transitivity a * c,
    { apply associated_mul_mul; apply (classical.some_spec (pf _ _)).2 },
    { rw ← b_eq,
      apply (classical.some_spec (pf _ _)).2.symm, } }
end⟩

lemma irreducible_iff_prime_of_exists_prime_factors {p : α} : irreducible p ↔ prime p :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0] },
  refine ⟨λ h, _, irreducible_of_prime⟩,
  obtain ⟨f, hf⟩ := pf p hp0,
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf,
  rw prime_iff_of_associated hq,
  exact hf.1 q (multiset.mem_cons_self _ _)
end

theorem unique_factorization_monoid.of_exists_prime_factors :
  unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, irreducible_iff_prime_of_exists_prime_factors pf,
  .. wf_dvd_monoid.of_exists_prime_factors pf }

end exists_prime_factors

theorem unique_factorization_monoid.iff_exists_prime_factors [comm_cancel_monoid_with_zero α] :
  unique_factorization_monoid α ↔
    (∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ f.prod ~ᵤ a) :=
⟨λ h, @unique_factorization_monoid.exists_prime_factors _ _ h,
  unique_factorization_monoid.of_exists_prime_factors⟩

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [comm_cancel_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ f.prod ~ᵤ a)
  (uif : ∀ (f g : multiset α),
  (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g)
  (p : α) : irreducible p ↔ prime p :=
⟨by letI := classical.dec_eq α; exact λ hpi,
    ⟨hpi.ne_zero, hpi.1,
      λ a b ⟨x, hx⟩,
      if hab0 : a * b = 0
      then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
        (λ ha0, by simp [ha0])
        (λ hb0, by simp [hb0])
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from left_ne_zero_of_mul hab0,
        have hb0 : b ≠ 0, from right_ne_zero_of_mul hab0,
        begin
          cases eif x hx0 with fx hfx,
          cases eif a ha0 with fa hfa,
          cases eif b hb0 with fb hfb,
          have h : multiset.rel associated (p ::ₘ fx) (fa + fb),
          { apply uif,
            { exact λ i hi, (multiset.mem_cons.1 hi).elim (λ hip, hip.symm ▸ hpi) (hfx.1 _), },
            { exact λ i hi, (multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _), },
            calc multiset.prod (p ::ₘ fx)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact associated_mul_mul (by refl) hfx.2
              ... ~ᵤ (fa).prod * (fb).prod :
                associated_mul_mul hfa.2.symm hfb.2.symm
              ... = _ : by rw multiset.prod_add, },
          exact let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem h
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfa.2).1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfb.2).1
              (multiset.dvd_prod hqb))
        end⟩, irreducible_of_prime⟩

theorem unique_factorization_monoid.of_exists_unique_irreducible_factors
  [comm_cancel_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ f.prod ~ᵤ a)
  (uif : ∀ (f g : multiset α),
  (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g) :
  unique_factorization_monoid α :=
unique_factorization_monoid.of_exists_prime_factors (by
  { convert eif,
    simp_rw irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif })

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [decidable_eq α] [nontrivial α] [normalization_monoid α]
variables [unique_factorization_monoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : multiset α := if h : a = 0 then 0 else
multiset.map normalize $ classical.some (unique_factorization_monoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : associated (factors a).prod a :=
begin
  rw [factors, dif_neg ane0],
  refine associated.trans _ (classical.some_spec (exists_prime_factors a ane0)).2,
  rw [← associates.mk_eq_mk_iff_associated, ← associates.prod_mk, ← associates.prod_mk,
      multiset.map_map],
  congr' 2,
  ext,
  rw [function.comp_apply, associates.mk_normalize],
end

theorem prime_of_factor {a : α} : ∀ (x : α), x ∈ factors a → prime x :=
begin
  rw [factors],
  split_ifs with ane0, { simp },
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  rw prime_iff_of_associated (normalize_associated),
  exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).1 y hy,
end

theorem irreducible_of_factor {a : α} : ∀ (x : α), x ∈ factors a → irreducible x :=
λ x h, irreducible_of_prime (prime_of_factor x h)

theorem normalize_factor {a : α} : ∀ (x : α), x ∈ factors a → normalize x = x :=
begin
  rw factors,
  split_ifs with h, { simp },
  intros x hx,
  obtain ⟨y, hy, rfl⟩ := multiset.mem_map.1 hx,
  apply normalize_idem
end

lemma factors_irreducible {a : α} (ha : irreducible a) :
  factors a = normalize a ::ₘ 0 :=
begin
  obtain ⟨p, a_assoc, hp⟩ := prime_factors_irreducible ha
    ⟨prime_of_factor, factors_prod ha.ne_zero⟩,
  have p_mem : p ∈ factors a,
  { rw hp, apply multiset.mem_cons_self },
  convert hp,
  rwa [← normalize_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]
end

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p ::ₘ factors b) (factors a),
  from factors_unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_of_factor _))
    irreducible_of_factor
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p ::ₘ factors b) :
        by rw multiset.prod_cons; exact associated_mul_mul
          (associated.refl _)
          (associated.symm (factors_prod hb0))),
multiset.exists_mem_of_rel_of_mem this (by simp)

@[simp] lemma factors_zero : factors (0 : α) = 0 := dif_pos rfl

@[simp] lemma factors_one : factors (1 : α) = 0 :=
begin
  rw ← multiset.rel_zero_right,
  apply factors_unique irreducible_of_factor,
  { intros x hx,
    exfalso,
    apply multiset.not_mem_zero x hx },
  { simp [factors_prod one_ne_zero] },
  apply_instance
end

@[simp] lemma factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  factors (x * y) = factors x + factors y :=
begin
  have h : (normalize : α → α) = associates.out ∘ associates.mk,
  { ext, rw [function.comp_apply, associates.out_mk], },
  rw [← multiset.map_id' (factors (x * y)), ← multiset.map_id' (factors x),
    ← multiset.map_id' (factors y), ← multiset.map_congr normalize_factor,
    ← multiset.map_congr normalize_factor, ← multiset.map_congr normalize_factor,
    ← multiset.map_add, h, ← multiset.map_map associates.out, eq_comm,
    ← multiset.map_map associates.out],
  refine congr rfl _,
  apply multiset.map_mk_eq_map_mk_of_rel,
  apply factors_unique,
  { intros x hx,
    rcases multiset.mem_add.1 hx with hx | hx;
    exact irreducible_of_factor x hx },
  { exact irreducible_of_factor },
  { rw multiset.prod_add,
    exact associated.trans (associated_mul_mul (factors_prod hx) (factors_prod hy))
      (factors_prod (mul_ne_zero hx hy)).symm, }
end

@[simp] lemma factors_pow {x : α} (n : ℕ) :
  factors (x ^ n) = n •ℕ factors x :=
begin
  induction n with n ih,
  { simp },
  by_cases h0 : x = 0,
  { simp [h0, zero_pow n.succ_pos, smul_zero] },
  rw [pow_succ, succ_nsmul, factors_mul h0 (pow_ne_zero _ h0), ih],
end

lemma dvd_iff_factors_le_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  x ∣ y ↔ factors x ≤ factors y :=
begin
  split,
  { rintro ⟨c, rfl⟩,
    simp [hx, right_ne_zero_of_mul hy] },
  { rw [← dvd_iff_dvd_of_rel_left (factors_prod hx), ← dvd_iff_dvd_of_rel_right (factors_prod hy)],
    apply multiset.prod_dvd_prod }
end

@[simp] lemma factors_eq_factors_iff {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  factors x = factors y ↔ x ~ᵤ y :=
by rw [le_antisymm_iff, ← dvd_dvd_iff_associated,
       dvd_iff_factors_le_factors hx hy, dvd_iff_factors_le_factors hy hx]

end unique_factorization_monoid

namespace unique_factorization_monoid

open_locale classical
open multiset associates
noncomputable theory

variables [comm_cancel_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α]

/-- Noncomputably defines a `normalization_monoid` structure on a `unique_factorization_monoid`. -/
protected def normalization_monoid : normalization_monoid α :=
normalization_monoid_of_monoid_hom_right_inverse {
  to_fun := λ a : associates α, if a = 0 then 0 else ((factors a).map
    (classical.some mk_surjective.has_right_inverse : associates α → α)).prod,
  map_one' := by simp,
  map_mul' := λ x y, by {
    by_cases hx : x = 0, { simp [hx] },
    by_cases hy : y = 0, { simp [hy] },
    simp [hx, hy] } } begin
  intro x,
  dsimp,
  by_cases hx : x = 0, { simp [hx] },
  have h : associates.mk_monoid_hom ∘ (classical.some mk_surjective.has_right_inverse) =
           (id : associates α → associates α),
  { ext x,
    rw [function.comp_apply, mk_monoid_hom_apply,
      classical.some_spec mk_surjective.has_right_inverse x],
    refl },
  rw [if_neg hx, ← mk_monoid_hom_apply, monoid_hom.map_multiset_prod, map_map, h, map_id,
      ← associated_iff_eq],
  apply factors_prod hx
end

instance : inhabited (normalization_monoid α) := ⟨unique_factorization_monoid.normalization_monoid⟩

end unique_factorization_monoid

namespace unique_factorization_monoid

variables {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]

lemma no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0)
  (h : (∀ {d}, d ∣ a → d ∣ b → ¬ prime d)) : ∀ {d}, d ∣ a → d ∣ b → is_unit d :=
λ d, induction_on_prime d
  (by { simp only [zero_dvd_iff], intros, contradiction })
  (λ x hx _ _, hx)
  (λ d q hp hq ih dvd_a dvd_b,
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b)))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
lemma dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
  (∀ {d}, d ∣ a → d ∣ c → ¬ prime d) → a ∣ b * c → a ∣ b :=
begin
  refine induction_on_prime c _ _ _,
  { intro no_factors,
    simp only [dvd_zero, mul_zero, forall_prop_of_true],
    haveI := classical.prop_decidable,
    exact is_unit_iff_forall_dvd.mp
      (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _ },
  { rintros _ ⟨x, rfl⟩ _ a_dvd_bx,
    apply units.dvd_mul_right.mp a_dvd_bx },
  { intros c p hc hp ih no_factors a_dvd_bpc,
    apply ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_mul_of_dvd_right dvd_c _) hq),
    rw mul_left_comm at a_dvd_bpc,
    refine or.resolve_left (left_dvd_or_dvd_right_of_dvd_prime_mul hp a_dvd_bpc) (λ h, _),
    exact no_factors h (dvd_mul_right p c) hp }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
lemma dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬ prime d) : a ∣ b * c → a ∣ c :=
by simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

section multiplicity
variables [nontrivial R] [normalization_monoid R] [decidable_eq R]
variables [decidable_rel (has_dvd.dvd : R → R → Prop)]
open multiplicity multiset

lemma le_multiplicity_iff_repeat_le_factors {a b : R} {n : ℕ} (ha : irreducible a) (hb : b ≠ 0) :
  ↑n ≤ multiplicity a b ↔ repeat (normalize a) n ≤ factors b :=
begin
  rw ← pow_dvd_iff_le_multiplicity,
  revert b,
  induction n with n ih, { simp },
  intros b hb,
  split,
  { rintro ⟨c, rfl⟩,
    rw [ne.def, pow_succ, mul_assoc, mul_eq_zero, decidable.not_or_iff_and_not] at hb,
    rw [pow_succ, mul_assoc, factors_mul hb.1 hb.2, repeat_succ, factors_irreducible ha,
      cons_add, cons_le_cons_iff, zero_add, ← ih hb.2],
    apply dvd.intro _ rfl },
  { rw [multiset.le_iff_exists_add],
    rintro ⟨u, hu⟩,
    rw [← dvd_iff_dvd_of_rel_right (factors_prod hb), hu, prod_add, prod_repeat],
    apply dvd.trans (dvd_of_associated (associated_pow_pow _)) (dvd.intro u.prod rfl),
    apply associated_normalize }
end

lemma multiplicity_eq_count_factors {a b : R} (ha : irreducible a) (hb : b ≠ 0) :
  multiplicity a b = (factors b).count (normalize a) :=
begin
  apply le_antisymm,
  { apply enat.le_of_lt_add_one,
    rw [← enat.coe_one, ← enat.coe_add, lt_iff_not_ge, ge_iff_le,
      le_multiplicity_iff_repeat_le_factors ha hb, ← le_count_iff_repeat_le],
    simp },
  rw [le_multiplicity_iff_repeat_le_factors ha hb, ← le_count_iff_repeat_le],
end

end multiplicity

end unique_factorization_monoid


namespace associates
open unique_factorization_monoid associated multiset
variables [comm_cancel_monoid_with_zero α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [comm_cancel_monoid_with_zero α] :
  Type u :=
with_top (multiset { a : associates α // irreducible a })

local attribute [instance] associated.setoid

theorem factor_set.coe_add {a b : multiset { a : associates α // irreducible a }} :
  (↑(a + b) : factor_set α) = a + b :=
by norm_cast

lemma factor_set.sup_add_inf_eq_add [decidable_eq (associates α)] :
  ∀(a b : factor_set α), a ⊔ b + a ⊓ b = a + b
| none     b        := show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b, by simp
| a        none     := show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤, by simp
| (some a) (some b) := show (a : factor_set α) ⊔ b + a ⊓ b = a + b, from
  begin
    rw [← with_top.coe_sup, ← with_top.coe_inf, ← with_top.coe_add, ← with_top.coe_add,
      with_top.coe_eq_coe],
    exact multiset.union_add_inter _ _
  end

/-- Evaluates the product of a `factor_set` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def factor_set.prod : factor_set α → associates α
| none     := 0
| (some s) := (s.map coe).prod

@[simp] theorem prod_top : (⊤ : factor_set α).prod = 0 := rfl

@[simp] theorem prod_coe {s : multiset { a : associates α // irreducible a }} :
  (s : factor_set α).prod = (s.map coe).prod :=
rfl

@[simp] theorem prod_add : ∀(a b : factor_set α), (a + b).prod = a.prod * b.prod
| none b    := show (⊤ + b).prod = (⊤:factor_set α).prod * b.prod, by simp
| a    none := show (a + ⊤).prod = a.prod * (⊤:factor_set α).prod, by simp
| (some a) (some b) :=
  show (↑a + ↑b:factor_set α).prod = (↑a:factor_set α).prod * (↑b:factor_set α).prod,
    by rw [← factor_set.coe_add, prod_coe, prod_coe, prod_coe, multiset.map_add, multiset.prod_add]

theorem prod_mono : ∀{a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none b h := have b = ⊤, from top_unique h, by rw [this, prod_top]; exact le_refl _
| a none h := show a.prod ≤ (⊤ : factor_set α).prod, by simp; exact le_top
| (some a) (some b) h := prod_le_prod $ multiset.map_le_map $ with_top.coe_le_coe.1 $ h

/-- `bcount p s` is the multiplicity of `p` in the factor_set `s` (with bundled `p`)-/
def bcount [decidable_eq (associates α)] (p : {a : associates α // irreducible a}) :
  factor_set α → ℕ
| none := 0
| (some s) := s.count p

variables [dec_irr : Π (p : associates α), decidable (irreducible p)]
include dec_irr

/-- `count p s` is the multiplicity of the irreducible `p` in the factor_set `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count [decidable_eq (associates α)] (p : associates α) :
  factor_set α → ℕ :=
if hp : irreducible p then bcount ⟨p, hp⟩  else 0

@[simp] lemma count_some [decidable_eq (associates α)] {p : associates α} (hp : irreducible p)
  (s : multiset _) : count p (some s) = s.count ⟨p, hp⟩:=
by { dunfold count, split_ifs, refl }

@[simp] lemma count_zero [decidable_eq (associates α)] {p : associates α} (hp : irreducible p) :
  count p (0 : factor_set α) = 0 :=
by { dunfold count, split_ifs, refl }

lemma count_reducible [decidable_eq (associates α)] {p : associates α} (hp : ¬ irreducible p) :
  count p = 0 := dif_neg hp

omit dec_irr

/-- membership in a factor_set (bundled version) -/
def bfactor_set_mem : {a : associates α // irreducible a} → (factor_set α) → Prop
| _ ⊤ := true
| p (some l) := p ∈ l

include dec_irr

/-- `factor_set_mem p s` is the predicate that the irreducible `p` is a member of `s : factor_set α`.

If `p` is not irreducible, `p` is not a member of any `factor_set`. -/
def factor_set_mem (p : associates α) (s : factor_set α) : Prop :=
if hp : irreducible p then bfactor_set_mem ⟨p, hp⟩ s else false

instance : has_mem (associates α) (factor_set α) := ⟨factor_set_mem⟩

@[simp] lemma factor_set_mem_eq_mem (p : associates α) (s : factor_set α) :
  factor_set_mem p s = (p ∈ s) := rfl

lemma mem_factor_set_top {p : associates α} {hp : irreducible p} :
  p ∈ (⊤ : factor_set α) :=
begin
  dunfold has_mem.mem, dunfold factor_set_mem, split_ifs, exact trivial
end

lemma mem_factor_set_some {p : associates α} {hp : irreducible p}
   {l : multiset {a : associates α // irreducible a }} :
  p ∈ (l : factor_set α) ↔ subtype.mk p hp ∈ l :=
begin
  dunfold has_mem.mem, dunfold factor_set_mem, split_ifs, refl
end

lemma reducible_not_mem_factor_set {p : associates α} (hp : ¬ irreducible p)
  (s : factor_set α) : ¬ p ∈ s :=
λ (h : if hp : irreducible p then bfactor_set_mem ⟨p, hp⟩ s else false),
  by rwa [dif_neg hp] at h

omit dec_irr

variable [unique_factorization_monoid α]

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_monoid.factors_unique _ _ _),
  { exact assume a ha, ((irreducible_mk _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

variables [nontrivial α] [normalization_monoid α]

private theorem forall_map_mk_factors_irreducible [decidable_eq α] (x : α) (hx : x ≠ 0) :
  ∀(a : associates α), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (irreducible_mk c).2 (irreducible_of_factor _ hc)
end

theorem prod_le_prod_iff_le {p q : multiset (associates α)}
  (hp : ∀a∈p, irreducible a) (hq : ∀a∈q, irreducible a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
iff.intro
  begin
    classical,
    rintros ⟨⟨c⟩, eqc⟩,
    have : c ≠ 0, from (mt mk_eq_zero.2 $
      assume (hc : quot.mk setoid.r c = 0),
      have (0 : associates α) ∈ q, from prod_eq_zero_iff.1 $ eqc.symm ▸ hc.symm ▸ mul_zero _,
      not_irreducible_zero ((irreducible_mk 0).1 $ hq _ this)),
    have : associates.mk (factors c).prod = quot.mk setoid.r c,
      from mk_eq_mk_iff_associated.2 (factors_prod this),

    refine multiset.le_iff_exists_add.2 ⟨(factors c).map associates.mk, unique' hq _ _⟩,
    { assume x hx,
      rcases multiset.mem_add.1 hx with h | h,
      exact hp x h,
      exact forall_map_mk_factors_irreducible c ‹c ≠ 0› _ h },
    { simp [multiset.prod_add, prod_mk, *] at * }
  end
  prod_le_prod

variables [dec : decidable_eq α] [dec' : decidable_eq (associates α)]
include dec

/-- This returns the multiset of irreducible factors as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors' (a : α) :
  multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk _).2 ha⟩)
  (irreducible_of_factor)

@[simp] theorem map_subtype_coe_factors' {a : α} :
  (factors' a).map coe = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ~ᵤ b) :
  factors' a = factors' b :=
have multiset.rel associated (factors a) (factors b), from
  factors_unique irreducible_of_factor irreducible_of_factor
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
by simpa [(multiset.map_eq_map subtype.coe_injective).symm, rel_associated_iff_map_eq_map.symm]

include dec'

/-- This returns the multiset of irreducible factors of an associate as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors (a : associates α) :
  factor_set α :=
begin
  refine (if h : a = 0 then ⊤ else
    quotient.hrec_on a (λx h, some $ factors' x) _ h),
  assume a b hab,
  apply function.hfunext,
  { have : a ~ᵤ 0 ↔ b ~ᵤ 0, from
      iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0),
    simp only [associated_zero_iff_eq_zero] at this,
    simp only [quotient_mk_eq_mk, this, mk_eq_zero] },
  exact (assume ha hb eq, heq_of_eq $ congr_arg some $ factors'_cong
    (λ c, ha (mk_eq_zero.2 c)) (λ c, hb (mk_eq_zero.2 c)) hab)
end

@[simp] theorem factors_0 : (0 : associates α).factors = ⊤ :=
dif_pos rfl

@[simp] theorem factors_mk (a : α) (h : a ≠ 0) :
  (associates.mk a).factors = factors' a :=
by { classical, apply dif_neg, apply (mt mk_eq_zero.1 h) }

theorem prod_factors : ∀(s : factor_set α), s.prod.factors = s
| none     := by simp [factor_set.prod]; refl
| (some s) :=
  begin
    unfold factor_set.prod,
    generalize eq_a : (s.map coe).prod = a,
    rcases a with ⟨a⟩,
    rw quot_mk_eq_mk at *,

    have : (s.map (coe : _ → associates α)).prod ≠ 0, from assume ha,
      let ⟨⟨a, ha⟩, h, eq⟩ := multiset.mem_map.1 (prod_eq_zero_iff.1 ha) in
      have irreducible (0 : associates α), from eq ▸ ha,
      not_irreducible_zero ((irreducible_mk _).1 this),
    have ha : a ≠ 0, by simp [*] at *,
    suffices : (unique_factorization_monoid.factors a).map associates.mk = s.map coe,
    { rw [factors_mk a ha],
      apply congr_arg some _,
      simpa [(multiset.map_eq_map subtype.coe_injective).symm] },

    refine unique'
      (forall_map_mk_factors_irreducible _ ha)
      (assume a ha, let ⟨⟨x, hx⟩, ha, eq⟩ := multiset.mem_map.1 ha in eq ▸ hx)
      _,
    rw [prod_mk, eq_a, mk_eq_mk_iff_associated],
    exact factors_prod ha
  end

@[simp]
theorem factors_prod (a : associates α) : a.factors.prod = a :=
quotient.induction_on a $ assume a, decidable.by_cases
  (assume : associates.mk a = 0, by simp [quotient_mk_eq_mk, this])
  (assume : associates.mk a ≠ 0,
    have a ≠ 0, by simp * at *,
    by simp [this, quotient_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated.2 (factors_prod this)])

theorem eq_of_factors_eq_factors {a b : associates α} (h : a.factors = b.factors) : a = b :=
have a.factors.prod = b.factors.prod, by rw h,
by rwa [factors_prod, factors_prod] at this

omit dec dec'

theorem eq_of_prod_eq_prod {a b : factor_set α} (h : a.prod = b.prod) : a = b :=
begin
  classical,
  have : a.prod.factors = b.prod.factors, by rw h,
  rwa [prod_factors, prod_factors] at this
end

include dec dec'

@[simp] theorem factors_mul (a b : associates α) : (a * b).factors = a.factors + b.factors :=
eq_of_prod_eq_prod $ eq_of_factors_eq_factors $
  by rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono : ∀{a b : associates α}, a ≤ b → a.factors ≤ b.factors
| s t ⟨d, rfl⟩ := by rw [factors_mul] ; exact le_add_of_nonneg_right bot_le

theorem factors_le {a b : associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
iff.intro
  (assume h, have a.factors.prod ≤ b.factors.prod, from prod_mono h,
    by rwa [factors_prod, factors_prod] at this)
  factors_mono

omit dec dec'

theorem prod_le {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
begin
  classical,
  exact iff.intro
  (assume h, have a.prod.factors ≤ b.prod.factors, from factors_mono h,
    by rwa [prod_factors, prod_factors] at this)
  prod_mono
end

include dec dec'

noncomputable instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
noncomputable instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

noncomputable instance : bounded_lattice (associates α) :=
{ sup          := (⊔),
  inf          := (⊓),
  sup_le       :=
    assume a b c hac hbc, factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
  le_sup_left  := assume a b,
    le_trans (le_of_eq (factors_prod a).symm) $ prod_mono $ le_sup_left,
  le_sup_right := assume a b,
    le_trans (le_of_eq (factors_prod b).symm) $ prod_mono $ le_sup_right,
  le_inf :=
    assume a b c hac hbc, factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
  inf_le_left  := assume a b,
    le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a)),
  inf_le_right := assume a b,
    le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)),
  .. associates.partial_order,
  .. associates.order_top,
  .. associates.order_bot }

lemma sup_mul_inf (a b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b,
begin
  refine eq_of_factors_eq_factors _,
  rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]
end

include dec_irr

lemma dvd_of_mem_factors {a p : associates α} {hp : irreducible p}
  (hm : p ∈ factors a) : p ∣ a :=
begin
  by_cases ha0 : a = 0, { rw ha0, exact dvd_zero p },
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0,
  rw [← associates.factors_prod a],
  rw [← ha', factors_mk a0 nza] at hm ⊢,
  erw prod_coe,
  apply multiset.dvd_prod, apply multiset.mem_map.mpr,
  exact ⟨⟨p, hp⟩, mem_factor_set_some.mp hm, rfl⟩
end

omit dec'

lemma dvd_of_mem_factors' {a : α} {p : associates α} {hp : irreducible p} {hz : a ≠ 0}
  (h_mem : subtype.mk p hp ∈ factors' a) : p ∣ associates.mk a :=
by { haveI := classical.dec_eq (associates α),
  apply @dvd_of_mem_factors _ _ _ _ _ _ _ _ _ _ hp,
  rw factors_mk _ hz,
  apply mem_factor_set_some.2 h_mem }

omit dec_irr

lemma mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  subtype.mk (associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a :=
begin
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd,
  apply multiset.mem_pmap.mpr, use q, use hq,
  exact subtype.eq (eq.symm (mk_eq_mk_iff_associated.mpr hpq))
end

include dec_irr

lemma mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  subtype.mk (associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, apply dvd_of_mem_factors', apply ha0 },
  { apply mem_factors'_of_dvd ha0 }
end

include dec'

lemma mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  (associates.mk p) ∈ factors (associates.mk a) :=
begin
  rw factors_mk _ ha0, exact mem_factor_set_some.mpr (mem_factors'_of_dvd ha0 hp hd)
end

lemma mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  (associates.mk p) ∈ factors (associates.mk a) ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, apply dvd_of_mem_factors, exact (irreducible_mk p).mpr hp },
  { apply mem_factors_of_dvd ha0 hp }
end

lemma exists_prime_dvd_of_not_inf_one {a b : α}
  (ha : a ≠ 0) (hb : b ≠ 0) (h : (associates.mk a) ⊓ (associates.mk b) ≠ 1)  :
  ∃ (p : α), prime p ∧ p ∣ a ∧ p ∣ b :=
begin
  have hz : (factors (associates.mk a)) ⊓ (factors (associates.mk b)) ≠ 0,
  { contrapose! h with hf,
    change ((factors (associates.mk a)) ⊓ (factors (associates.mk b))).prod = 1,
    rw hf,
    exact multiset.prod_zero },
  rw [factors_mk a ha, factors_mk b hb, ← with_top.coe_inf] at hz,
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := multiset.exists_mem_of_ne_zero ((mt with_top.coe_eq_coe.mpr) hz),
  rw multiset.inf_eq_inter at p0_mem,
  obtain ⟨p, rfl⟩ : ∃ p, associates.mk p = p0 := quot.exists_rep p0,
  refine ⟨p, _, _, _⟩,
  { rw [← irreducible_iff_prime, ← irreducible_mk],
    exact p0_irr },
  { apply dvd_of_mk_le_mk,
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).left,
    apply ha, },
  { apply dvd_of_mk_le_mk,
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).right,
    apply hb }
end

theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
  (associates.mk a) ⊓ (associates.mk b) = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬ prime d :=
begin
  split,
  { intros hg p ha hb hp,
    refine ((associates.prime_mk _).mpr hp).not_unit (is_unit_of_dvd_one _ _),
    rw ← hg,
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb) },
  { contrapose,
    intros hg hc,
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg,
    exact hc hpa hpb hp }
end

omit dec_irr

theorem factors_prime_pow {p : associates α} (hp : irreducible p)
  (k : ℕ) : factors (p ^ k) = some (multiset.repeat ⟨p, hp⟩ k) :=
eq_of_prod_eq_prod (by rw [associates.factors_prod, factor_set.prod, multiset.map_repeat,
                           multiset.prod_repeat, subtype.coe_mk])

include dec_irr

theorem prime_pow_dvd_iff_le {m p : associates α} (h₁ : m ≠ 0)
  (h₂ : irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ count p m.factors :=
begin
  obtain ⟨a, nz, rfl⟩ := associates.exists_non_zero_rep h₁,
  rw [factors_mk _ nz, ← with_top.some_eq_coe, count_some, multiset.le_count_iff_repeat_le,
      ← factors_le, factors_prime_pow h₂, factors_mk _ nz],
  exact with_top.coe_le_coe
end

theorem le_of_count_ne_zero {m p : associates α} (h0 : m ≠ 0)
  (hp : irreducible p) : count p m.factors ≠ 0 → p ≤ m :=
begin
  rw [← nat.pos_iff_ne_zero],
  intro h,
  rw [← pow_one p],
  apply (prime_pow_dvd_iff_le h0 hp).2,
  simpa only
end

theorem count_mul {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) :
  count p (factors (a * b)) = count p a.factors + count p b.factors :=
begin
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha,
  obtain ⟨b0, nzb, hb'⟩ := exists_non_zero_rep hb,
  rw [factors_mul, ← ha', ← hb', factors_mk a0 nza, factors_mk b0 nzb, ← factor_set.coe_add,
      ← with_top.some_eq_coe, ← with_top.some_eq_coe, ← with_top.some_eq_coe, count_some hp,
      multiset.count_add, count_some hp, count_some hp]
end

theorem count_of_coprime {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {p : associates α} (hp : irreducible p) :
  count p a.factors = 0 ∨ count p b.factors = 0 :=
begin
  rw [or_iff_not_imp_left, ← ne.def],
  intro hca,
  contrapose! hab with hcb,
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    (irreducible_iff_prime.mp hp)⟩,
end

theorem count_mul_of_coprime {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) :
  count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors :=
begin
  cases count_of_coprime ha hb hab hp with hz hb0, { tauto },
  apply or.intro_right,
  rw [count_mul ha hb hp, hb0, add_zero]
end

theorem count_mul_of_coprime' {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) :
  count p (a * b).factors = count p a.factors
  ∨ count p (a * b).factors = count p b.factors :=
begin
  rw [count_mul ha hb hp],
  cases count_of_coprime ha hb hab hp with ha0 hb0,
  { apply or.intro_right, rw [ha0, zero_add] },
  { apply or.intro_left, rw [hb0, add_zero] }
end

theorem dvd_count_of_dvd_count_mul {a b : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  {p : associates α} (hp : irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d)
  {k : ℕ} (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors :=
begin
  cases count_of_coprime ha hb hab hp with hz h,
  { rw hz, exact dvd_zero k },
  { rw [count_mul ha hb hp, h] at habk, exact habk }
end

omit dec_irr

@[simp] lemma factors_one : factors (1 : associates α) = 0 :=
begin
  apply eq_of_prod_eq_prod,
  rw associates.factors_prod,
  exact multiset.prod_zero,
end

@[simp] theorem pow_factors {a : associates α} {k : ℕ} : (a ^ k).factors = k •ℕ a.factors :=
begin
  induction k with n h,
  { rw [zero_nsmul, pow_zero], exact factors_one },
  { rw [pow_succ, succ_nsmul, factors_mul, h] }
end

include dec_irr

lemma count_pow {a : associates α} (ha : a ≠ 0) {p : associates α} (hp : irreducible p)
  (k : ℕ) : count p (a ^ k).factors = k * count p a.factors :=
begin
  induction k with n h,
  { rw [pow_zero, factors_one, zero_mul, count_zero hp] },
  { rw [pow_succ, count_mul ha (pow_ne_zero _ ha) hp, h, nat.succ_eq_add_one], ring }
end

theorem dvd_count_pow {a : associates α} (ha : a ≠ 0) {p : associates α} (hp : irreducible p)
  (k : ℕ) : k ∣ count p (a ^ k).factors := by { rw count_pow ha hp, apply dvd_mul_right }

theorem is_pow_of_dvd_count {a : associates α} (ha : a ≠ 0) {k : ℕ}
  (hk : ∀ (p : associates α) (hp : irreducible p), k ∣ count p a.factors) :
  ∃ (b : associates α), a = b ^ k :=
begin
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha,
  rw [factors_mk a0 hz] at hk,
  have hk' : ∀ (p : {a : associates α // irreducible a}), k ∣ (factors' a0).count p,
  { intro p,
    have pp : p = ⟨p.val, p.2⟩, { simp only [subtype.coe_eta, subtype.val_eq_coe] },
    rw [pp, ← count_some p.2], exact hk p.val p.2 },
  obtain ⟨u, hu⟩ := multiset.exists_smul_of_dvd_count _ hk',
  use (u : factor_set α).prod,
  apply eq_of_factors_eq_factors,
  rw [pow_factors, prod_factors, factors_mk a0 hz, ← with_top.some_eq_coe, hu],
  exact with_bot.coe_nsmul u k
end

omit dec
omit dec_irr
omit dec'

theorem eq_pow_of_mul_eq_pow {a b c : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : associates α), a = d ^ k :=
begin
  classical,
  by_cases hk0 : k = 0,
  { use 1,
    rw [hk0, pow_zero] at h ⊢,
    apply (mul_eq_one_iff.1 h).1 },
  { refine is_pow_of_dvd_count ha _,
    intros p hp,
    apply dvd_count_of_dvd_count_mul ha hb hp hab,
    rw h,
    apply dvd_count_pow _ hp,
    rintros rfl,
    rw zero_pow' _ hk0 at h,
    cases mul_eq_zero.mp h; contradiction }
end

end associates

section
open associates unique_factorization_monoid

/-- `to_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def unique_factorization_monoid.to_gcd_monoid
  (α : Type*) [comm_cancel_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α]
  [normalization_monoid α] [decidable_eq (associates α)] [decidable_eq α] : gcd_monoid α :=
{ gcd := λa b, (associates.mk a ⊓ associates.mk b).out,
  lcm := λa b, (associates.mk a ⊔ associates.mk b).out,
  gcd_dvd_left := assume a b, (out_dvd_iff a (associates.mk a ⊓ associates.mk b)).2 $ inf_le_left,
  gcd_dvd_right := assume a b, (out_dvd_iff b (associates.mk a ⊓ associates.mk b)).2 $ inf_le_right,
  dvd_gcd := assume a b c hac hab, show a ∣ (associates.mk c ⊓ associates.mk b).out,
    by rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]; exact ⟨hac, hab⟩,
  lcm_zero_left := assume a, show (⊤ ⊔ associates.mk a).out = 0, by simp,
  lcm_zero_right := assume a, show (associates.mk a ⊔ ⊤).out = 0, by simp,
  gcd_mul_lcm := assume a b,
    show (associates.mk a ⊓ associates.mk b).out * (associates.mk a ⊔ associates.mk b).out =
      normalize (a * b),
    by rw [← out_mk, ← out_mul, mul_comm, sup_mul_inf]; refl,
  normalize_gcd := assume a b, by convert normalize_out _,
  .. ‹normalization_monoid α› }

end

namespace unique_factorization_monoid

variables {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]

lemma is_unit_of_no_prime_factor {a : R} :
  a ≠ 0 → (∀ {p}, prime p → ¬ p ∣ a) → is_unit a :=
induction_on_prime a (absurd rfl) (λ a ha _ _, ha)
  (λ a p _ hp ih _ no_factor, absurd (dvd_mul_right p a) (no_factor hp))

/-- In a unique factorization monoid, there are finitely many divisors of `x`, up to units. -/
noncomputable def finite_divisors
  {x : R} (x_ne : x ≠ 0) : fintype {y : associates R // y ∣ associates.mk x} :=
begin
  haveI : nontrivial R := ⟨⟨x, 0, x_ne⟩⟩,
  haveI := @unique_factorization_monoid.normalization_monoid R _ _ _,
  haveI := classical.dec_eq R,
  haveI := classical.dec_eq (associates R),
  set divisors := ((factors x).powerset.map (λ (s : multiset R), associates.mk s.prod)).to_finset,
  apply fintype.of_finset divisors,
  intro y,
  obtain ⟨y, rfl⟩ := associates.mk_surjective y,
  simp only [exists_prop, multiset.mem_to_finset, multiset.mem_powerset, exists_eq_right,
    multiset.mem_map, associates.mk_eq_mk_iff_associated],
  split,
  { rintros ⟨s, hs, hy⟩,
    apply associates.mk_dvd_mk.mpr,
    have prod_s_ne : s.prod ≠ 0,
    { intro hz,
      apply x_ne (eq_zero_of_zero_dvd _),
      rw multiset.prod_eq_zero_iff at hz,
      rw ← dvd_iff_dvd_of_rel_right (factors_prod x_ne),
      exact multiset.dvd_prod (multiset.mem_of_le hs hz) },
    have y_ne : y ≠ 0,
    { intro y_eq,
      rw [y_eq, associated_zero_iff_eq_zero] at hy,
      exact prod_s_ne hy },
    rw [← dvd_iff_dvd_of_rel_left hy, ← dvd_iff_dvd_of_rel_right (factors_prod x_ne)],
    exact multiset.prod_dvd_prod hs },
    { rintro (h : associates.mk y ∣ associates.mk x),
      rw associates.mk_dvd_mk at h,
      have hy : y ≠ 0, { refine mt (λ hy, _) x_ne, rwa [hy, zero_dvd_iff] at h },
      refine ⟨factors y, _, factors_prod hy⟩,
      exact (dvd_iff_factors_le_factors hy x_ne).mp h },
end

end unique_factorization_monoid
