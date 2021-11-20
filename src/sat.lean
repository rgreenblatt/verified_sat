import assign
import simplify

lemma reduces (f : formula) (l : literal) 
  (h : l ∈ f.join ∨ l_not l ∈ f.join) : 
  num_literals (simplify (assign_lit l f)) < num_literals f := 
begin
  have first_assign : num_literals (assign_lit l f) < num_literals f := 
    assign_with_present_reduces_literals _ _ h,
  have leq := simplify_leq_num_literals (assign_lit l f),
  linarith,
end

def compute_sat (g : choice_func) : formula → bool
| [] := tt
| f := 

  -- this line is here just to make proving things easier
  if h : f.join = [] then ff else

  if [] ∈ f then ff else
  let non_empty_f := (subtype.mk f h) in
  let l := g.val non_empty_f in
  have in_joined : l ∈ f.join ∨ l_not l ∈ f.join := 
    by apply g.property non_empty_f,
  have in_joined_flip : l_not l ∈ f.join ∨ l_not (l_not l) ∈ f.join := 
  begin
    apply or.symm,
    rw l_inv,
    exact in_joined,
  end,

  have first : num_literals (simplify (assign_lit l f)) 
      < num_literals f := reduces _ _ in_joined,
  have second : num_literals (simplify (assign_lit (l_not l) f)) 
      < num_literals f := reduces _ _ in_joined_flip,

  compute_sat (simplify (assign_lit l f)) || 
    compute_sat (simplify (assign_lit (l_not l) f))
using_well_founded {rel_tac := λ _ _, 
                    `[exact ⟨_, measure_wf num_literals⟩]}

#eval compute_sat naive_choice_func example_sat_formula
#eval compute_sat naive_choice_func example_unsat_formula
#eval compute_sat naive_choice_func example_complex_formula

theorem compute_sat_correct (f : formula) (g : choice_func) : 
  (compute_sat g f = tt) ↔ sat f :=
begin
  induction h_eq : (num_literals f) using nat.strong_induction_on 
    with n ih generalizing f,
  cases' f,
  {
    rw compute_sat,
    simp,
    let empty_a : assignment := subtype.mk [] (by simp),
    apply exists.intro empty_a,
    rw formula_sat,
    simp,
  },
  {
    have nil_in_implies_unsat : [] ∈ hd :: f →  ¬ sat (hd :: f) := begin
      intro nil_in,
      intro is_sat,
      cases' is_sat,
      have is_sat := h [] nil_in,
      rw clause_sat at is_sat,
      simp at is_sat,
      contradiction,
    end,

    cases' classical.em ((hd :: f).join = []),
    {
      have is_false : compute_sat g (hd :: f) = ff := begin
        rw compute_sat,
        rw dif_pos,
        exact h,
      end,

      rw is_false,
      simp,

      apply nil_in_implies_unsat,
      simp at h,
      cases' h,
      rw left,
      simp,
    },
    cases' classical.em ([] ∈ (hd :: f)) with nil_in nil_n_in,
    {
      rw compute_sat,
      simp [h, nil_in],
      exact nil_in_implies_unsat nil_in,
    },
    {
      rw compute_sat,
      simp [h, nil_n_in],

      let non_empty_f : non_empty_formula := ⟨hd :: f, h⟩,
      let l := (g.val non_empty_f),


      have in_joined : l ∈ (hd :: f).join ∨ l_not l ∈ (hd :: f).join := 
        by apply g.property non_empty_f,
      have in_joined_flip : l_not l ∈ (hd :: f).join ∨ 
          l_not (l_not l) ∈ (hd :: f).join := 
      begin
        apply or.symm,
        rw l_inv,
        exact in_joined,
      end,

      have first : num_literals (simplify (assign_lit l (hd :: f))) < 
          num_literals (hd :: f) := 
        reduces _ _ in_joined,
      have second : num_literals (simplify (assign_lit (l_not l) (hd :: f))) < 
          num_literals (hd :: f) := 
        reduces _ _ in_joined_flip,

      apply iff.intro,
      {
        intro h_or,
        cases' h_or,
        {
          let sub_f := simplify (assign_lit l (hd :: f)),
          let m := num_literals (simplify (assign_lit l (hd :: f))),
          have ih := ih m (begin
            rw ←h_eq,
            simp only [m],
            exact first,
          end) sub_f (by refl),
          have is_true : compute_sat g sub_f = tt := by apply h_1,
          rw is_true at ih,
          simp at ih,
          rw simplify_correct at ih,
          apply assign_sat_implies_sat _ _ ih,
        },
        -- TODO: dedup?
        {
          let sub_f := simplify (assign_lit (l_not l) (hd :: f)),
          let m := num_literals (simplify (assign_lit (l_not l) (hd :: f))),
          have ih := ih m (begin
            rw ←h_eq,
            simp only [m],
            exact second,
          end) sub_f (by refl),
          have is_true : compute_sat g sub_f = tt := by apply h_1,
          rw is_true at ih,
          simp at ih,
          rw simplify_correct at ih,
          apply assign_sat_implies_sat _ _ ih,
        },
      },
      {
        intro is_sat,
        cases' is_sat,
        cases' classical.em (l ∈ w ∨ l_not l ∈ w),
        {
          cases' h_2,
          {
            apply or.inl,
            let sub_f := simplify (assign_lit l (hd :: f)),
            let m := num_literals (simplify (assign_lit l (hd :: f))),
            have ih := ih m (begin
              rw ←h_eq,
              simp only [m],
              exact first,
            end) sub_f (by refl),
            simp only [sub_f, l] at ih,
            simp at ih,
            rw simplify_correct at ih,
            rw ih,
            apply sat_implies_assign_sat_or_cant_exist,
            apply exists.intro w,
            simp [h_1],
            apply h_2,
          },
          -- TODO: dedup?
          {
            apply or.inr,
            let sub_f := simplify (assign_lit (l_not l) (hd :: f)),
            let m := num_literals (simplify (assign_lit (l_not l) (hd :: f))),
            have ih := ih m (begin
              rw ←h_eq,
              simp only [m],
              exact second,
            end) sub_f (by refl),
            simp only [sub_f, l] at ih,
            simp at ih,
            rw simplify_correct at ih,
            rw ih,
            apply sat_implies_assign_sat_or_cant_exist,
            apply exists.intro w,
            simp [h_1],
            apply h_2,
          },
        },
        {
          -- TODO: dedup?
          apply or.inl,
          let sub_f := simplify (assign_lit l (hd :: f)),
          let m := num_literals (simplify (assign_lit l (hd :: f))),
          have ih := ih m (begin
            rw ←h_eq,
            simp only [m],
            exact first,
          end) sub_f (by refl),
          simp only [sub_f, l] at ih,
          simp at ih,
          rw simplify_correct at ih,
          rw ih,
          apply general_assign_sub _ _ _ h_1,
          apply or.inr (or.inr h_2),
        },
      },
    },
  },
end
