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

theorem trailing_coeff_neg [ring R] {f : R[X]} : (-f).trailing_coeff = -f.trailing_coeff :=
begin
  unfold trailing_coeff,
  simp only [nat_trailing_degree_neg, coeff_neg]
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

theorem erase_lead_trailing_coeff [semiring R] {p : R[X]} (h : p.support.card ≠ 1) : p.erase_lead.trailing_coeff = p.trailing_coeff :=
begin
  unfold polynomial.trailing_coeff,
  rw polynomial.erase_lead_coeff_of_ne,
  { congr' 1,
    unfold polynomial.nat_trailing_degree polynomial.trailing_degree,
    
    sorry },
  sorry
end

noncomputable def div_all_X [ring R] (p : R[X]) := p /ₘ polynomial.X^p.nat_trailing_degree

theorem coeff_div_all_X [ring R] {p : R[X]} (n : ℕ) : p.div_all_X.coeff n = p.coeff (n + p.nat_trailing_degree) := sorry

theorem leading_coeff_div_all_X [comm_ring R] [nontrivial R] {p : R[X]} : p.div_all_X.leading_coeff = p.leading_coeff :=
begin
  unfold leading_coeff,
  rw coeff_div_all_X,
  unfold div_all_X,
  rw nat_degree_div_by_monic,
  swap,
  { apply monic_X_pow },
  congr,
  rw [polynomial.nat_degree_X_pow, nat.sub_add_cancel],
  apply polynomial.nat_trailing_degree_le_nat_degree
end

theorem nat_trailing_degree_div_all_X [ring R] {p : R[X]} : p.div_all_X.nat_trailing_degree = 0 :=
begin
  by_contra h,
  have : p.div_all_X.is_root 0,
  { apply polynomial.zero_is_root_of_coeff_zero_eq_zero,
    apply polynomial.coeff_eq_zero_of_lt_nat_trailing_degree,
    exact nat.pos_of_ne_zero h },
  clear h,
  unfold div_all_X at this,
  sorry
end

theorem trailing_coeff_div_all_X [ring R] {p : R[X]} : p.div_all_X.trailing_coeff = p.trailing_coeff :=
begin
  unfold trailing_coeff,
  rw [coeff_div_all_X, nat_trailing_degree_div_all_X, zero_add],
end

theorem div_mul [ring R] {p q r : R[X]} : p /ₘ (q * r) = p /ₘ q /ₘ r := sorry

theorem div_by_monic_mul_pow_root_multiplicity_roots [comm_ring R] [is_domain R] [decidable_eq R] {p : R[X]} {a : R}
  : (p /ₘ (X - C a) ^ root_multiplicity a p).roots = multiset.filter (λ b, b ≠ a) p.roots := sorry

end polynomial

noncomputable def positive_roots (f : ℝ[X]) : multiset ℝ :=
  multiset.filter (λ a, 0 < a) (polynomial.roots f)

lemma positive_roots_neg {f : ℝ[X]} : positive_roots (-f) = positive_roots f :=
begin
  by_cases h0 : f = 0,
  { subst f,
    rw neg_zero },
  unfold positive_roots,
  congr' 1,
  rw ←neg_one_mul,
  rw polynomial.roots_mul,
  swap,
  { simp only [neg_mul, one_mul, ne.def, neg_eq_zero, h0, not_false_iff] },
  { have : (-1 : ℝ[X]) = (polynomial.C (-1 : ℝ)) := by simp only [map_neg, map_one],
    rw [add_left_eq_self, this, polynomial.roots_C] }
end

lemma positive_roots_div_all_X {f : ℝ[X]} : positive_roots f.div_all_X = positive_roots f :=
begin
  -- unfold polynomial.div_all_X,
  ext,
  unfold positive_roots,
  simp_rw multiset.count_filter,
  split_ifs,
  swap,
  { refl },
  
  sorry
end

-- lemma multiset.filter_dedup {α : Type} [decidable_eq α] {s : multiset α} {p : α → Prop} [decidable_pred p]
--   : multiset.filter p s.dedup = (multiset.filter p s).dedup :=
-- begin
--   sorry
-- end

-- lemma multiset.to_finset_erase {α : Type} [decidable_eq α] {s : multiset α} {a : α} : s.to_finset.erase a = (multiset.filter (λ (b : α), b ≠ a) s).to_finset :=
-- begin
--   unfold multiset.to_finset finset.erase,
--   conv_lhs
--   { change {finset . val := s.dedup.erase a, nodup := _},
--     congr,
--     rw multiset.nodup.erase_eq_filter _ (multiset.nodup_dedup s) },
--   congr,
--   rw multiset.filter_dedup
-- end

theorem list.even_induction {α : Type} {P : list α → Prop}
  (hnil : P list.nil)
  (hone : ∀ {a : α}, P [a])
  (htwo : ∀ {a b : α}, P [a, b])
  (hrest : ∀ {a b : α} {tl : list α}, P tl → P (a :: b :: tl))
  : ∀ l, P l
| [] := hnil
| [a] := hone
| [a, b] := htwo
| (a :: b :: tl) := hrest (list.even_induction tl)

lemma card_positive_roots_of_pos_leading_trailing {f : ℝ[X]} (h : 0 < f.leading_coeff * f.trailing_coeff) : even (positive_roots f).card :=
begin
  rw mul_pos_iff at h,
  wlog hleading : 0 < f.leading_coeff,
  { push_neg at hleading,
    cases eq_or_lt_of_le hleading with hleading hleading,
    { simp only [hleading, lt_self_iff_false, false_and, or_self] at h,
      contradiction },
    { specialize @this (-f) _ _,
      { apply or.inl,
        split,
        { simpa only [polynomial.leading_coeff_neg, right.neg_pos_iff] },
        { simp only [polynomial.trailing_coeff_neg, right.neg_pos_iff],
          rcases h with ⟨_, _⟩ | ⟨_, _⟩,
          { linarith },
          { assumption } } },
      { simpa only [polynomial.leading_coeff_neg, right.neg_pos_iff] },
      rwa [positive_roots_neg] at this } },
  rcases h with ⟨hleading', htrailing⟩ | ⟨_, _⟩,
  clear hleading',
  swap,
  { linarith },
  wlog hconst : f.nat_trailing_degree = 0,
  { specialize @this f.div_all_X _ _ _,
    { rwa [polynomial.leading_coeff_div_all_X] },
    { rwa [polynomial.trailing_coeff_div_all_X]},
    { exact polynomial.nat_trailing_degree_div_all_X },
    rwa [positive_roots_div_all_X] at this },
  generalize hroots : multiset.sort (≤) (positive_roots f) = roots,
  induction roots using list.even_induction with root₁ root₁ root₂ root₁ root₂ roots ih generalizing f,
  { -- No roots:
    rw [←(multiset.length_sort (≤)), hroots],
    simp only [list.length, even_zero] },
  { -- One root:
    exfalso,
    sorry },
  { -- Two roots:
    rw [←(multiset.length_sort (≤)), hroots],
    simp only [list.length, even_two] },
  let g := f /ₘ (polynomial.X - polynomial.C root₁) /ₘ (polynomial.X - polynomial.C root₂),
  specialize @ih g _ _ _ _,
  { rw [polynomial.leading_coeff_div_by_monic_of_monic, polynomial.leading_coeff_div_by_monic_of_monic],
    { exact hleading },
    { apply polynomial.monic_X_sub_C },
    { rw polynomial.degree_X_sub_C,
      sorry },
    { apply polynomial.monic_X_sub_C },
    { rw polynomial.degree_X_sub_C,
      sorry } },
  sorry,
  sorry,
  sorry,
  -- generalize hroots : (positive_roots f).to_finset = roots,
  -- induction roots using finset.induction_on with root roots hroot ih generalizing f,
  -- { rw multiset.to_finset_eq_empty at hroots,
  --   simp only [hroots, multiset.card_zero, even_zero] },
  -- let g := f /ₘ ((polynomial.X - polynomial.C root) ^ polynomial.root_multiplicity root f),
  -- specialize @ih g _ _ _ _,
  -- { dsimp [g],
  --   rw polynomial.leading_coeff_div_by_monic_of_monic,
  --   { exact hleading },
  --   { apply polynomial.monic.pow, 
  --     apply polynomial.monic_X_sub_C },
  --   { simp only [polynomial.degree_pow, polynomial.degree_X_sub_C, nat.smul_one_eq_coe],
  --     have fne0 : f ≠ 0,
  --     { rw ←polynomial.leading_coeff_ne_zero,
  --       linarith },
  --     rw_mod_cast [polynomial.degree_eq_nat_degree fne0, polynomial.root_multiplicity_le_iff fne0],
  --     apply polynomial.not_dvd_of_nat_degree_lt fne0,
  --     simp only [polynomial.nat_degree_pow, polynomial.nat_degree_X_sub_C, mul_one, lt_add_iff_pos_right, nat.lt_one_iff] } },
  -- { sorry },
  -- { sorry },
  -- { unfold positive_roots,
  --   rw [polynomial.div_by_monic_mul_pow_root_multiplicity_roots, ←(finset.erase_insert hroot), ←hroots],
  --   unfold positive_roots,
  --   simp_rw [multiset.filter_filter, and_comm, ←multiset.filter_filter, ←multiset.to_finset_erase] },
  sorry
end

lemma card_positive_roots_of_neg_leading_trailing {f : ℝ[X]} (h : f.leading_coeff * f.trailing_coeff < 0) : odd (positive_roots f).card :=
begin
  rw mul_neg_iff at h,
  wlog hleading : 0 < f.leading_coeff,
  { push_neg at hleading,
    cases eq_or_lt_of_le hleading with hleading hleading,
    { simp only [hleading, lt_self_iff_false, false_and, or_self] at h,
      contradiction },
    { specialize @this (-f) _ _,
      { apply or.inl,
        split,
        { simpa only [polynomial.leading_coeff_neg, right.neg_pos_iff] },
        { simp only [polynomial.trailing_coeff_neg, right.neg_pos_iff],
          rcases h with ⟨_, _⟩ | ⟨_, _⟩,
          { linarith },
          { simpa only [right.neg_neg_iff] } } },
      { simpa only [polynomial.leading_coeff_neg, right.neg_pos_iff] },
      rwa [positive_roots_neg] at this } },
  rcases h with ⟨hleading', htrailing⟩ | ⟨_, _⟩,
  clear hleading',
  swap,
  { linarith },
  wlog hconst : f.nat_trailing_degree = 0,
  { specialize @this f.div_all_X _ _ _,
    { rwa [polynomial.leading_coeff_div_all_X] },
    { rwa [polynomial.trailing_coeff_div_all_X]},
    { exact polynomial.nat_trailing_degree_div_all_X },
    rwa [positive_roots_div_all_X] at this },
  generalize hnroots : (positive_roots f).dedup.card = nroots,
  induction nroots using nat.strong_induction_on with nroots ih generalizing f,
  dsimp at ih,
  sorry
end

lemma card_positive_roots_le_of_derivative {f : ℝ[X]} : (positive_roots f).card ≤ (positive_roots f.derivative).card + 1 := sorry

noncomputable def sign_changes (f : ℝ[X]) : ℕ :=
  (list.destutter (≠) 
   $ list.map (real.sign ∘ f.coeff)
   $ finset.sort (≤) f.support).length - 1

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
  have : real.sign ∘ (λ (n : ℕ), f.coeff n * (↑n + 1)) = real.sign ∘ f.coeff,
  sorry,
  have : f.derivative.support = finset.image nat.pred f.support,
  sorry,
  rw this,
  change (list.destutter _ (list.map (_ ∘ (λ n, f.derivative.coeff n)) _)).length ≤ _,
  simp_rw polynomial.coeff_derivative,
  sorry
end

lemma real.sign_pos_iff {r : ℝ} : 0 < r ↔ 0 < r.sign :=
begin
  split,
  { intros h,
    rw real.sign_of_pos,
    { exact zero_lt_one },
    { exact h } },
  { rw real.sign,
    split_ifs;
    intros,
    { linarith },
    { assumption },
    { linarith } }
end

lemma real.sign_neg_iff {r : ℝ} : r < 0 ↔ r.sign < 0 :=
begin
  split,
  { intros h,
    rw real.sign_of_neg,
    { simp only [right.neg_neg_iff, zero_lt_one] },
    { exact h } },
  { rw real.sign,
    split_ifs;
    intros,
    { assumption },
    { linarith },
    { linarith } }
end

theorem decartes_rule_of_signs'' (f : ℝ[X])
  : (positive_roots f).card ≡ sign_changes f [MOD 2] :=
begin
  by_cases h0 : f = 0,
  { subst_vars,
    unfold sign_changes,
    simp only [positive_roots, polynomial.roots_zero, multiset.filter_zero, multiset.card_zero, list.length, polynomial.support_zero, finset.sort_empty, list.map_nil, list.destutter_nil] },
  wlog h : 0 < f.trailing_coeff,
  { specialize this (-f) _ _,
    { simp only [h0, neg_eq_zero, not_false_iff] },
    { simp only [polynomial.trailing_coeff_neg, right.neg_pos_iff],
      push_neg at h,
      cases eq_or_lt_of_le h,
      { rw ←polynomial.trailing_coeff_eq_zero at h0,
        contradiction },
      { assumption } },
    rwa [positive_roots_neg, sign_changes_neg] at this },
  have : f.leading_coeff.sign = (-1) ^ (sign_changes f),
  { generalize hsupp : f.support = supp,
    induction supp using finset.induction_on_max with lead supp hlead ih generalizing f,
    { rw polynomial.support_eq_empty at hsupp,
      contradiction },
    by_cases hconst : f.support.card = 1,
    { rw polynomial.card_support_eq_one at hconst,
      rcases hconst with ⟨k, x, hx, hconst⟩,
      subst f,
      simp only [polynomial.leading_coeff_mul, polynomial.leading_coeff_C, polynomial.leading_coeff_pow, polynomial.leading_coeff_X, one_pow, mul_one],
      sorry },
    specialize ih f.erase_lead _ _ _,
    { apply polynomial.erase_lead_ne_zero,
      rw ←polynomial.card_support_eq_zero at h0,
      rw nat.two_le_iff,
      exact ⟨h0, hconst⟩ },
    { rwa polynomial.erase_lead_trailing_coeff hconst },
    { rw [polynomial.erase_lead_support, polynomial.nat_degree, polynomial.degree, hsupp, finset.max_insert, max_def],
      split_ifs with hmax,
      { exfalso,
        have : supp.nonempty,
        { by_contra hempty,
          rw [finset.not_nonempty_iff_eq_empty] at hempty,
          subst supp,
          rw hsupp at hconst,
          simp only [insert_emptyc_eq, finset.card_singleton, eq_self_iff_true, not_true] at hconst,
          contradiction },
        cases finset.max_of_nonempty this with m hm,
        rw [hm, with_bot.coe_le_coe] at hmax,
        specialize hlead m (finset.mem_of_max hm),
        linarith },
      { simp only [with_bot.unbot'_coe, finset.erase_insert_eq_erase, finset.erase_eq_self],
        contrapose! hlead with hmem,
        refine ⟨lead, hmem, _⟩,
        refl } },
    by_cases hcoeff : f.leading_coeff.sign = f.erase_lead.leading_coeff.sign,
    { rw [hcoeff, ih],
      congr' 1,
      unfold sign_changes,
      sorry },
    sorry },
  unfold nat.modeq,
  cases (sign_changes f).even_or_odd with heven hodd,
  { rw [nat.even_iff.mp heven, nat.even_iff.mp],
    apply card_positive_roots_of_pos_leading_trailing,
    rw mul_pos_iff,
    apply or.inl,
    refine ⟨_, h⟩,
    rw [real.sign_pos_iff, this],
    apply even.pow_pos heven,
    { simp only [ne.def, neg_eq_zero, one_ne_zero, not_false_iff] } },
  { rw [nat.odd_iff.mp hodd, nat.odd_iff.mp],
    apply card_positive_roots_of_neg_leading_trailing,
    rw mul_neg_iff,
    apply or.inr,
    refine ⟨_, h⟩,
    rw [real.sign_neg_iff, this],
    apply odd.pow_neg hodd,
    simp only [right.neg_neg_iff, zero_lt_one] }
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
