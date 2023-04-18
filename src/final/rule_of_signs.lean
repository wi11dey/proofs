import data.list.destutter
import data.set.basic
import data.nat.modeq
import data.nat.parity
import data.real.basic
import data.real.sign
import data.polynomial.basic
import data.polynomial.derivative
import data.polynomial.eval
import data.polynomial.ring_division
import data.polynomial.degree.trailing_degree
import data.polynomial.inductions
import set_theory.cardinal.basic

open_locale polynomial

namespace polynomial

variable {R : Type}

theorem support_C [semiring R] {c : R} (h : c ≠ 0)
  : (C c).support = {0} :=
begin
  ext,
  simp only [mem_support_iff, ne.def, finset.mem_singleton],
  rw coeff_C,
  split_ifs,
  { split;
    intros;
    assumption },
  { split;
    contradiction }
end

theorem support_mul_X [semiring R] {p : R[X]}
  : (p * polynomial.X).support = finset.map (order_embedding.add_right 1).to_embedding p.support :=
begin
  sorry
end

theorem trailing_coeff_C [semiring R] (a : R) : (C a).trailing_coeff = a :=
begin
  unfold trailing_coeff,
  simp only [nat_trailing_degree_C, coeff_C_zero]
end

theorem trailing_coeff_mul_X [ring R] [no_zero_divisors R] [nontrivial R] {p : R[X]}
  : (p * X).trailing_coeff = p.trailing_coeff :=
begin
  rw trailing_coeff_mul,
  suffices : @trailing_coeff R _ X = 1,
  { rw [this, mul_one] },
  unfold trailing_coeff,
  simp only [nat_trailing_degree_X, coeff_X_one]
end

theorem trailing_coeff_neg {R : Type} [ring R] (p : R[X]) : (-p).trailing_coeff = -p.trailing_coeff := sorry

end polynomial

noncomputable def positive_roots (f : ℝ[X]) : multiset ℝ :=
  multiset.filter (λ a, 0 < a) (polynomial.roots f)

lemma card_positive_roots_of_pos_leading_trailing {f : ℝ[X]} (h : 0 < f.leading_coeff * f.trailing_coeff) : even (positive_roots f).card :=
begin
  rw mul_pos_iff at h,
  sorry
end

lemma card_positive_roots_of_neg_leading_trailing {f : ℝ[X]} (h : f.leading_coeff * f.trailing_coeff < 0) : odd (positive_roots f).card := sorry

lemma card_positive_roots_le_of_derivative {f : ℝ[X]} : (positive_roots f).card ≤ (positive_roots f.derivative).card + 1 := sorry

noncomputable def sign_changes (f : ℝ[X]) : ℕ :=
  (list.destutter (≠)
    (list.map 
      (real.sign ∘ f.coeff)
      (finset.sort (≤) f.support))).length - 1

theorem list.destutter'_map {α : Type} {R : α → α → Prop} [decidable_rel R] {f : R ≃r R} {s : list α} {a : α}
  : list.destutter' R (f a) (list.map f s) = list.map f (list.destutter' R a s) :=
begin
  induction s with hd tl ih generalizing a,
  { simp only [list.map, list.destutter'_nil, eq_self_iff_true, and_self] },
  rw list.map,
  by_cases h : R a hd,
  { rw list.destutter'_cons_pos,
    swap,
    { rwa ←f.map_rel_iff' at h },
    rw [list.destutter'_cons_pos _ h, list.map],
    congr,
    exact ih },
  { rw list.destutter'_cons_neg,
    swap,
    { rwa ←f.map_rel_iff' at h },
    rw [list.destutter'_cons_neg _ h],
    exact ih }
end

theorem list.destutter_map {α : Type} {R : α → α → Prop} [decidable_rel R] {f : R ≃r R} {s : list α}
  : list.destutter R (list.map f s) = list.map f (list.destutter R s) :=
begin
  induction s,
  { simp only [list.map_nil, list.destutter_nil] },
  rw [list.map, list.destutter_cons', list.destutter_cons'],
  exact list.destutter'_map
end

lemma sign_changes_neg {f : ℝ[X]} : sign_changes (-f) = sign_changes f :=
begin
  simp only [sign_changes, function.comp, real.sign_neg, polynomial.coeff_neg, polynomial.support_neg],
  rw [←function.comp, list.comp_map],
  congr' 1,
  let neg_rel_iso : (≠) ≃r (≠) := {
    to_equiv := equiv.neg ℝ,
    map_rel_iff' := by simp only [equiv.neg_apply, ne.def, neg_inj, iff_self, forall_const],
  },
  change (list.destutter ne (list.map neg_rel_iso _)).length = _,
  rw [list.destutter_map, list.length_map]
end

-- theorem finset.sort_map {α β : Type} [linear_order α] [linear_order β] {s : finset α} {f : α ↪o β}
--    : finset.sort (≤) (finset.map f.to_embedding s) = list.map f (finset.sort (≤) s) :=
-- begin
--   ext n el,
--   by_cases hn : n < (finset.sort (≤) s).length,
--   sorry,
--   sorry
-- end

-- lemma sign_changes_shift {f : ℝ[X]} : sign_changes (f * polynomial.X) = sign_changes f :=
-- begin
--   unfold sign_changes,
--   congr' 3,
--   nth_rewrite_lhs 0 list.comp_map,
--   nth_rewrite_rhs 0 list.comp_map,
--   congr' 1,
--   rw [polynomial.support_mul_X, finset.sort_map, list.map_map],
--   congr' 1 with n,
--   simp only [function.comp_app, order_embedding.add_right_apply, polynomial.coeff_mul_X]
-- end

lemma sign_changes_C {c : ℝ} : sign_changes (polynomial.C c) = 0 :=
begin
  unfold sign_changes,
  by_cases h0 : c = 0,
  { subst_vars,
    simp only [list.length, map_zero, polynomial.support_zero, finset.sort_empty, list.map_nil, list.destutter_nil] },
  rw polynomial.support_C h0,
  simp only [list.map, finset.sort_singleton, list.destutter_singleton, list.length_singleton]
end

lemma sign_changes_of_derivative_le {f : ℝ[X]} : sign_changes f.derivative ≤ sign_changes f :=
begin
  unfold sign_changes,
  sorry
end

theorem decartes_rule_of_signs'' (f : ℝ[X])
  : (positive_roots f).card ≡ sign_changes f [MOD 2] :=
begin
  by_cases h0 : f = 0,
  { subst_vars,
    unfold sign_changes,
    simp only [positive_roots, polynomial.roots_zero, multiset.filter_zero, multiset.card_zero, list.length, polynomial.support_zero, finset.sort_empty, list.map_nil, list.destutter_nil] },
  unfold nat.modeq,
  cases (sign_changes f).even_or_odd with heven hodd,
  { rw [nat.even_iff.mp heven, nat.even_iff.mp],
    apply card_positive_roots_of_pos_leading_trailing,
    rw mul_pos_iff,
    suffices
      : ∀ (p : ℝ[X]),
          p ≠ 0 →
          even (sign_changes p) →
          0 < p.leading_coeff → 0 < p.trailing_coeff,
    { rcases trichotomous_of (<) f.leading_coeff 0 with h | h | h,
      { specialize this (-f) _ _,
        { simp only [h0, ne.def, neg_eq_zero, not_false_iff] },
        { rwa sign_changes_neg },
        simp only [polynomial.leading_coeff_neg, polynomial.trailing_coeff_neg, right.neg_pos_iff] at this,
        apply or.inr,
        use ⟨h, this h⟩ },
      { rw polynomial.leading_coeff_eq_zero at h,
        contradiction },
      { use ⟨h, this f h0 heven h⟩ } },
    clear heven h0 f,
    intros p h0 heven hleading,
    sorry
    -- induction f using polynomial.rec_on_horner with p c hp hc ih _ hp ih,
    -- { -- Already handled above:
    --   contradiction },
    -- { by_cases h : p = 0,
    --   { simp only [h, hc.symm, polynomial.trailing_coeff_C, zero_add, polynomial.leading_coeff_C, and_self, lt_or_lt_iff_ne, ne.def, not_false_iff] },
    --   { specialize ih h,
    --     rw [add_comm, polynomial.leading_coeff_add_of_degree_lt],
    --     swap,
    --     { apply lt_of_eq_of_lt (polynomial.degree_C hc),
    --       by_contra hdegree,
    --       apply h,
    --       ext n,
    --       rw polynomial.coeff_zero,
    --       induction n with n ih,
    --       { exact hp },
    --       push_neg at hdegree,
    --       rw polynomial.degree_le_iff_coeff_zero at hdegree,
    --       simp only [with_bot.coe_pos] at hdegree,
    --       exact hdegree n.succ nat.succ_pos' },
    --     sorry } },
    -- { rw [polynomial.leading_coeff_mul_X, polynomial.trailing_coeff_mul_X],
    --   rw ←sign_changes_shift at heven,
    --   exact ih hp heven }
  },
  { rw [nat.odd_iff.mp hodd, nat.odd_iff.mp],
    apply card_positive_roots_of_neg_leading_trailing,
    rw mul_neg_iff,
    suffices
      : ∀ (p : ℝ[X]),
          p ≠ 0 →
          odd (sign_changes p) →
          0 < p.leading_coeff → p.trailing_coeff < 0,
    { rcases trichotomous_of (<) f.leading_coeff 0 with h | h | h,
      { specialize this (-f) _ _,
        { simp only [h0, ne.def, neg_eq_zero, not_false_iff] },
        { rwa sign_changes_neg },
        simp only [polynomial.leading_coeff_neg, polynomial.trailing_coeff_neg, right.neg_pos_iff, right.neg_neg_iff] at this,
        apply or.inr,
        use ⟨h, this h⟩ },
      { rw polynomial.leading_coeff_eq_zero at h,
        contradiction },
      { use ⟨h, this f h0 hodd h⟩ } },
    sorry }
end

theorem decartes_rule_of_signs' (f : ℝ[X])
  : (positive_roots f).card ≤ sign_changes f :=
begin
  by_cases h0 : f = 0,
  { subst_vars,
    unfold sign_changes,
    simp only [positive_roots, polynomial.roots_zero, multiset.filter_zero, multiset.card_zero, list.length, polynomial.support_zero, finset.sort_empty, list.map_nil, list.destutter_nil] },
  suffices : ∀ (n : ℕ) (p : ℝ[X]), p.degree = n → (positive_roots p).card ≤ sign_changes p,
  { exact this f.nat_degree f (polynomial.degree_eq_nat_degree h0) },
  intro,
  induction n with n ih,
  { introv hn,
    rw [polynomial.eq_C_of_degree_eq_zero hn, sign_changes_C],
    unfold positive_roots,
    simp only [polynomial.roots_C, multiset.filter_zero, multiset.card_zero] },
  introv hn,
  suffices : (positive_roots p).card ≤ sign_changes p + 1,
  { apply nat.modeq.le_of_lt_add,
    { exact decartes_rule_of_signs'' p },
    calc (positive_roots p).card ≤ sign_changes p + 1 : this
    ...                          < sign_changes p + 2 : lt_add_one _ },
  specialize ih p.derivative,
  rw polynomial.degree_eq_iff_nat_degree_eq at hn,
  swap,
  { by_contra h,
    rw [←polynomial.degree_eq_bot, hn] at h,
    contradiction },
  rw polynomial.degree_derivative_eq at ih,
  swap,
  { rw hn,
    exact nat.succ_pos' },
  rw hn at ih,
  simp only [nat.succ_sub_succ_eq_sub, tsub_zero, eq_self_iff_true, forall_true_left] at ih,
  have := decartes_rule_of_signs'' p.derivative,
  rw (nat.modeq_iff_dvd' ih) at this,
  let s := (sign_changes p.derivative - (positive_roots p.derivative).card)/2,
  calc (positive_roots p).card ≤ (positive_roots p.derivative).card + 1 : card_positive_roots_le_of_derivative
  ...                          = (sign_changes p.derivative) - 2*s + 1 :
    begin
      suffices : (positive_roots p.derivative).card = sign_changes p.derivative - 2*s,
      { rw this },
      rw [mul_comm, nat.div_mul_cancel this, nat.sub_sub_self ih]
    end
  ...                          ≤ (sign_changes p) - 2*s + 1 :
    begin
      simp only [add_le_add_iff_right, tsub_le_iff_right],
      rw nat.sub_add_cancel,
      swap,
      { dsimp [s],
        rw [mul_comm, nat.div_mul_cancel this],
        calc sign_changes p.derivative - _ ≤ sign_changes p.derivative : tsub_le_self
        ...                                ≤ sign_changes p : sign_changes_of_derivative_le },
      exact sign_changes_of_derivative_le
    end
  ...                          ≤ (sign_changes p) + 1 : by simp only [add_le_add_iff_right, tsub_le_self]
end

theorem decartes_rule_of_signs (f : ℝ[X])
  : (positive_roots f).card ≡ sign_changes f [MOD 2]
  ∧ (positive_roots f).card ≤ sign_changes f :=
⟨decartes_rule_of_signs'' f, decartes_rule_of_signs' f⟩
