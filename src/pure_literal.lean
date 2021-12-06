import assign
import general_assign

def get_pure_literals  (f : formula) : list literal := 
  list.filter (λ l, is_pure_literal l f) f.join

#eval get_pure_literals example_unsat_formula
#eval get_pure_literals example_sat_formula
#eval get_pure_literals example_complex_formula

def assign_pure_literals (f : formula) : formula := 
  assign_all f (get_pure_literals f)

#eval assign_pure_literals example_unsat_formula
#eval assign_pure_literals example_sat_formula
#eval assign_pure_literals example_complex_formula

lemma pure_literal_impl_correct (f : formula) (pures : list literal) 
: ↥(pures.all (λ l, is_pure_literal l f)) → 
  (sat f  ↔  sat (assign_all f pures)) :=
begin
  intro h,
  rw assign_all,
  induction' pures;
  simp,
  have h_f : ↥(pures.all (λ l, is_pure_literal l (assign_lit hd f))) := 
  begin
    rw list.all_iff_forall,
    rw list.all_iff_forall at h,
    intros a h_in,
    have h := h a,
    simp [h_in] at h,
    rw is_pure_literal,
    have sub : (assign_lit hd f).join ⊆ f.join := by apply assign_subset,
    have final : l_not a ∉ list.join (assign_lit hd f) := begin
      intro h_next,
      have in_f : l_not a ∈ f.join := begin
        apply sub,
        exact h_next,
      end,
      rw is_pure_literal' at h,
      simp [in_f] at h,
      contradiction,
    end,
    simp at final,
    simp,
    apply final,
  end,
  have ih := ih (assign_lit hd f) h_f,
  rw ←ih,

  apply general_assign,
  apply or.inr,
  rw list.all_iff_forall at h,
  apply h,
  simp,
end

lemma pure_literal_correct (f : formula) : 
sat f  ↔  sat (assign_pure_literals f) := begin
  apply pure_literal_impl_correct,
  rw list.all_iff_forall,
  rw get_pure_literals,
  intro a,
  apply list.of_mem_filter,
end

lemma pure_literals_leq_size (f : formula) 
: formula_size (assign_pure_literals f) ≤ formula_size f := 
by apply assign_all_leq_size
