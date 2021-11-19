import assign

/- 
to generalize over a few different cases we have a lemma which takes the
'which_case' field

(honestly, this is pretty hacky, but it avoids copying around a bunch of terms
or having to define an overly general lemma)
-/

lemma general_assign_sub (f : formula) (l : literal) (w : assignment) 
(h : formula_sat w f) 
(which_case : [l] ∈ f ∨ is_pure_literal l f ∨ 
    ¬(l ∈ w ∨ l_not l ∈ w)) 
  : sat (assign_lit l f) :=
begin
  apply sat_implies_assign_sat_or_cant_exist,
  apply exists.intro (add_l_to_assign w l),
  rw add_l_to_assign,
  apply and.intro,
  {
    rw formula_sat,
    intros c c_in_f,
    rw formula_sat at h,
    have h := h c c_in_f,
    cases' h,
    cases' h_1,
    apply exists.intro w_1,
    simp [right],
    have is_in : w_1 ∈ w.val.remove_all [l_not l] ++ [l] := begin
      simp,
      cases' which_case,
      {
        rename h_1 is_unit,
        have is_sat := h [l] is_unit,
        rw clause_sat at is_sat,
        simp at is_sat,

        have h_eq : w.val.remove_all [l_not l] = w.val := begin
          rw list.remove_all,
          rw list.filter_eq_self,
          simp,
          intros a a_in,
          have p := w.property l is_sat,
          intro h,
          rw ←h at p,
          contradiction,
        end,

        simp at h_eq,
        rw h_eq,
        apply or.inl,
        apply left,
      },
      {
        cases' h_1,
        {
          apply or.inl,
          rw list.remove_all,
          rw list.mem_filter,
          apply and.intro,
          {
            apply left,
          },
          {
            rename h_1 hd_is_pure,
            simp,
            intro h_eq,
            rw is_pure_literal at hd_is_pure,
            rw ←h_eq at hd_is_pure,
            simp at hd_is_pure,
            have hd_is_pure := hd_is_pure c c_in_f,
            contradiction,
          },
        },
        {
          have h : w_1 ∈ w.val.remove_all [l_not l] := begin
            rw list.remove_all,
            apply list.mem_filter_of_mem,
            apply left,
            simp,
            intro h_eq,
            rw h_eq at left,
            simp [left] at h_1,
            contradiction,
          end,
          apply or.inl,
          apply h,
        }
      },
    end,
    apply is_in,
  },
  {
    have is_in : l ∈ w.val.remove_all [l_not l] ++ [l] := by simp,
    apply is_in,
  },
end

lemma general_assign (f : formula) (l : literal) 
  (which_case : [l] ∈ f ∨ is_pure_literal l f) 
  : sat f ↔ sat (assign_lit l f) :=
begin
  apply iff.intro,
  {
    intro is_sat,
    cases' is_sat,
    apply general_assign_sub _ _ _ h,
    cases' which_case;
    simp [h_1],
  },
  {
    apply assign_sat_implies_sat,
  },
end
