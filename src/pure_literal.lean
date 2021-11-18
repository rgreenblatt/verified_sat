import assign

def is_pure_literal (l : literal) (f: formula) : bool := (l_not l) ∉ list.join f

def get_pure_literals  (f : formula) : list literal := 
list.filter (λ l, is_pure_literal l f) f.join

#eval get_pure_literals example_unsat_formula
#eval get_pure_literals example_sat_formula
#eval get_pure_literals example_complex_formula

def assign_pure_literals_impl (f : formula) (pures : list literal) (h : ↥(pures.all (λ l, is_pure_literal l f))) : formula := 
list.foldl (λ f l, assign_lit l f) f pures

def assign_pure_literals (f : formula) : formula := 
assign_pure_literals_impl f (get_pure_literals f) begin
  rw list.all_iff_forall,
  rw get_pure_literals,
  intro a,
  apply list.of_mem_filter,
end

lemma induction_helper (f : formula) (hd : literal) (pures : list literal) 
  (h : ↥((hd :: pures).all (λ (l : literal), is_pure_literal l f)))
  :  ↥(pures.all (λ l, is_pure_literal l (assign_lit hd f))) := 
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
    rw is_pure_literal at h,
    simp [in_f] at h,
    contradiction,
  end,
  simp [final],
end

lemma pure_literal_impl_correct (f : formula) (pures : list literal) 
  (h : ↥(pures.all (λ l, is_pure_literal l f))) 
  : sat f  ↔  sat (assign_pure_literals_impl f pures h) :=
begin
  induction' pures;
  rw assign_pure_literals_impl;
  simp,
  have h_f := induction_helper _ _ _ h,
  have ih := ih (assign_lit hd f) h_f,
  have eq : (list.foldl (λ (f : formula) (l : literal), assign_lit l f) (assign_lit hd f) pures) = 
  (assign_pure_literals_impl (assign_lit hd f) pures h_f) := begin
    rw assign_pure_literals_impl,
  end,
  rw eq,
  rw ←ih,

  apply iff.intro,
  {

    have hd_is_pure : is_pure_literal hd f := begin
      rw list.all_iff_forall at h,
      apply h,
      simp,
    end,

    intro is_sat,
    cases' is_sat,
    apply sat_implies_assign_sat_or_cant_exist,
    apply exists.intro (add_l_to_assign w hd),
    rw add_l_to_assign,
    apply and.intro,
    {
      rw formula_sat,
      intros c c_in_f,
      rw formula_sat at h_1,
      have h_1 := h_1 c c_in_f,
      cases' h_1,
      cases' h_2,
      apply exists.intro w_1,
      simp [right],
      have is_in : w_1 ∈ w.val.remove_all [l_not hd] ++ [hd] := begin
        simp,
        apply or.inl,
        rw list.remove_all,
        rw list.mem_filter,
        apply and.intro,
        {
          apply left,
        },
        {
          simp,
          intro h_eq,
          rw is_pure_literal at hd_is_pure,
          rw ←h_eq at hd_is_pure,
          simp at hd_is_pure,
          have hd_is_pure := hd_is_pure c c_in_f,
          contradiction,
        },
      end,
      apply is_in,
    },
    {
      have is_in : hd ∈ w.val.remove_all [l_not hd] ++ [hd] := by simp,
      apply is_in,
    },
  },
  {
    apply assign_sat_implies_sat,
  },
end

lemma pure_literal_correct (f : formula) : sat f  ↔  sat (assign_pure_literals f) := 
by apply pure_literal_impl_correct

lemma pure_literal_impl_leq_num_literals (f : formula) (pures : list literal) 
  (h : ↥(pures.all (λ l, is_pure_literal l f))) 
  : num_literals (assign_pure_literals_impl f pures h) ≤ num_literals f :=
begin
  induction' pures;
  rw assign_pure_literals_impl;
  simp,
  have h_f := induction_helper _ _ _ h,
  have ih := ih (assign_lit hd f) h_f,
  have eq : (list.foldl (λ (f : formula) (l : literal), assign_lit l f) (assign_lit hd f) pures) = 
  (assign_pure_literals_impl (assign_lit hd f) pures h_f) := begin
    rw assign_pure_literals_impl,
  end,
  rw eq,
  /- apply assign_leq_literals, -/
end

lemma pure_literals_leq_num_literals (f : formula): num_literals (assign_pure_literals f) ≤ num_literals f := by apply pure_literal_impl_leq_num_literals


#eval assign_pure_literals example_unsat_formula
#eval assign_pure_literals example_sat_formula
#eval assign_pure_literals example_complex_formula
