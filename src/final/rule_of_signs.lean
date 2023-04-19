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

theorem trailing_coeff_C [semiring R] (a : R) : (C a).trailing_coeff = a :=
begin
  unfold trailing_coeff,
  simp only [nat_trailing_degree_C, coeff_C_zero]
end

theorem trailing_coeff_mul_X [ring R] [no_zero_divisors R] [nontrivial R] {p : R[X]}
  : (p * X).trailing_coeff = p.trailing_coeff :=
begin
  rw [trailing_coeff_mul],
  nth_rewrite_rhs 0 ←(mul_one p.trailing_coeff),
  congr,
  unfold trailing_coeff,
  simp only [nat_trailing_degree_X, coeff_X_one]
end

theorem trailing_coeff_neg {R : Type} [ring R] (p : R[X]) : (-p).trailing_coeff = -p.trailing_coeff := sorry

end polynomial

noncomputable def positive_roots (f : ℝ[X]) : multiset ℝ :=
  multiset.filter (λ a, 0 < a) (polynomial.roots f)

lemma card_positive_roots_of_pos_leading_trailing {f : ℝ[X]} (h : 0 < f.leading_coeff * f.trailing_coeff) : even (positive_roots f).card :=
begin
  generalize hnroots : (positive_roots f).dedup.card = nroots,
  induction nroots with nroots ih generalizing f,
  { rw [multiset.card_eq_zero, multiset.dedup_eq_zero] at hnroots,
    simp only [hnroots, multiset.card_zero, even_zero] },
  rw mul_pos_iff at h,
  sorry
end

lemma card_positive_roots_of_neg_leading_trailing {f : ℝ[X]} (h : f.leading_coeff * f.trailing_coeff < 0) : odd (positive_roots f).card :=
begin
  generalize hnroots : (positive_roots f).dedup.card = nroots,
  induction nroots with nroots ih generalizing f,
  { rw mul_neg_iff at h,
    exfalso,
    sorry },
  rw mul_neg_iff at h,
  sorry
end

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
  apply nat.sub_le_sub_right,
  change (list.destutter _ (list.map (_ ∘ (λ n, f.derivative.coeff n)) _)).length ≤ _,
  simp_rw polynomial.coeff_derivative,
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
      : ∀ p ≠ (0 : ℝ[X]),
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
    generalize hsupp : p.support = supp,
    have : supp.nonempty := by rwa [←hsupp, polynomial.nonempty_support_iff],
    induction this using finset.nonempty.cons_induction with supp a s h hs ih,
    { unfold polynomial.trailing_coeff polynomial.nat_trailing_degree polynomial.trailing_degree,
      unfold polynomial.leading_coeff polynomial.nat_degree polynomial.degree at hleading,
      rw hsupp at *,
      simp only [finset.min_singleton, option.get_or_else_coe, finset.max_singleton, with_bot.unbot'_coe] at *,
      exact hleading },
    { sorry } },
  { rw [nat.odd_iff.mp hodd, nat.odd_iff.mp],
    apply card_positive_roots_of_neg_leading_trailing,
    rw mul_neg_iff,
    suffices
      : ∀ p ≠ (0 : ℝ[X]),
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
  generalize hn : f.nat_degree = n,
  induction n with n ih generalizing f,
  { rw [polynomial.eq_C_of_nat_degree_eq_zero hn, sign_changes_C],
    unfold positive_roots,
    simp only [polynomial.roots_C, multiset.filter_zero, multiset.card_zero] },
  suffices : (positive_roots f).card ≤ sign_changes f + 1,
  { apply nat.modeq.le_of_lt_add,
    { exact decartes_rule_of_signs'' f },
    calc (positive_roots f).card ≤ sign_changes f + 1 : this
    ...                          < sign_changes f + 2 : lt_add_one _ },
  have hf'0 : f.derivative ≠ 0,
  { by_contra h,
    have := polynomial.nat_degree_eq_zero_of_derivative_eq_zero h,
    rw hn at this,
    contradiction },
  specialize ih f.derivative hf'0 _,
  { rw_mod_cast [←polynomial.degree_eq_iff_nat_degree_eq hf'0, polynomial.degree_derivative_eq f _, hn],
    swap,
    { rw hn,
      exact nat.succ_pos' },
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero] },
  have := decartes_rule_of_signs'' f.derivative,
  rw (nat.modeq_iff_dvd' ih) at this,
  let s := (sign_changes f.derivative - (positive_roots f.derivative).card)/2,
  calc (positive_roots f).card ≤ (positive_roots f.derivative).card + 1 : card_positive_roots_le_of_derivative
  ...                          = (sign_changes f.derivative) - 2*s + 1 :
    begin
      congr' 1,
      rw [mul_comm, nat.div_mul_cancel this, nat.sub_sub_self ih]
    end
  ...                          ≤ (sign_changes f) - 2*s + 1 :
    begin
      simp only [add_le_add_iff_right, tsub_le_iff_right],
      rw nat.sub_add_cancel,
      swap,
      { dsimp [s],
        rw [mul_comm, nat.div_mul_cancel this],
        calc sign_changes f.derivative - _ ≤ sign_changes f.derivative : tsub_le_self
        ...                                ≤ sign_changes f : sign_changes_of_derivative_le },
      exact sign_changes_of_derivative_le
    end
  ...                          ≤ (sign_changes f) + 1 : by simp only [add_le_add_iff_right, tsub_le_self]
end

theorem decartes_rule_of_signs (f : ℝ[X])
  : (positive_roots f).card ≡ sign_changes f [MOD 2]
  ∧ (positive_roots f).card ≤ sign_changes f :=
⟨decartes_rule_of_signs'' f, decartes_rule_of_signs' f⟩
