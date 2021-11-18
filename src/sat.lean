import assign
import simplify

def compute_sat (g : choice_func) : formula → bool
| [] := tt
| f := 
  if h : f.join = [] then ff else 
  let non_empty_f := (subtype.mk f h) in
  let l := g.val non_empty_f in
  have in_joined : l ∈ f.join ∨ l_not l ∈ f.join := begin
    let p := g.property non_empty_f,
    have eq : l = g.val non_empty_f := by refl,
    rw eq,
    have eq : non_empty_f.val = f := by refl,
    rw eq at p,
    assumption,
  end,
  have first : num_literals (simplify (assign_lit l f)) < num_literals f, from begin
    apply assign_with_present_reduces_literals,
    assumption,
  end,
  have second : num_literals (simplify (assign_lit (l_not l) f)) < num_literals f, from begin
    apply assign_with_present_reduces_literals,
    rw l_inv,
    exact or.swap in_joined,
  end,
  compute_sat (simplify (assign_lit l f)) || compute_sat (simplify (assign_lit (l_not l) f))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf num_literals⟩]}

#eval compute_sat naive_choice_func example_sat_formula
#eval compute_sat naive_choice_func example_unsat_formula
#eval compute_sat naive_choice_func example_complex_formula

lemma erase_dup_nil_iff  {α  : Type} [decidable_eq α] (l : list α) : l.erase_dup = [] ↔ l = [] := begin
  apply iff.intro;
  intro h,
  {
    cases' l;
    simp,
    {
      have hd_in : hd ∈ (hd :: l).erase_dup := begin
        rw list.mem_erase_dup,
        simp,
      end,
      rw h at hd_in,
      simp at hd_in,
      exact hd_in,
    },
  },
  {
    rw h,
    simp,
  },
end

theorem check_sat_correct  : ∀ (f : formula) (g : choice_func), (compute_sat g f = tt) ↔ sat f :=
begin
  intros f g,
  induction' h : (num_literals f),
  {
    cases' f,
    {
      rw compute_sat,
      rw sat,
      apply iff.intro;
      simp,
      {
        let empty_a : assignment := subtype.mk [] (by simp),
        apply exists.intro empty_a,
        rw formula_sat,
        simp,
      },
    },
    {
      rw num_literals at h,
      rw num_distinct at h,

      have empty : (hd :: f).join.erase_dup = [] := list.length_eq_zero.mp h,
      have empty : (hd :: f).join = [] := begin
        rw erase_dup_nil_iff at empty,
        exact empty,
      end,

      simp at empty,
      cases' empty,

      have is_false : compute_sat g (hd :: f) = ff := begin
        rw compute_sat,
        simp,
        have h : hd = list.nil ∧ ∀ (a : list literal), a ∈ f → a = list.nil := begin
          simp [left],
          apply right,
        end,
        simp [h],
        /- simp [right], -/

        sorry,
      end,

      rw is_false,
      simp,
      intro h,
      cases' h,
      cases' h,
      rw formula_sat at h_1,
      let h := h_1 hd,
      simp at h,
      rw clause_sat at h,
      cases' h,
      cases' h,

      rw left at right_1,
      exact list.not_mem_nil w_1 right_1
    },
  },
  {
    have ih : ∀ (f : formula) (g : choice_func), num_literals f ≤ x → (compute_sat g f = tt ↔ sat f) := sorry,

    cases' f,
    {
      rw num_literals at h,
      rw num_distinct at h,
      simp at h,
      contradiction,
    },
    {
      rw compute_sat,

      have neq_nil : (hd :: f).join ≠ [] := begin
        rw num_literals at h,
        rw num_distinct at h,
        intro eq,
        rw eq at h,
        simp at h,
        contradiction,
      end,

      simp [neq_nil],
      let l := (g.val ⟨hd :: f, neq_nil⟩),
      apply iff.intro,
      {
        intro h_or,
        cases' h_or,
        {
          have ih := ih (assign_lit l (hd::f))  g _,
          {
            simp only [l] at ih,
            simp at ih,
            rw ih at h_1,
            apply assign_sat_implies_sat _ _ h_1,
          },
          {
            apply nat.lt_succ_iff.mp,
            rw ←h,
            apply assign_with_present_reduces_literals,
            apply g.property,
          },
        },
        {
          have ih := ih (assign_lit (l_not l) (hd::f))  g _,
          {
            simp only [l] at ih,
            simp at ih,
            rw ih at h_1,
            apply assign_sat_implies_sat _ _ h_1,
          },
          {
            apply nat.lt_succ_iff.mp,
            rw ←h,
            apply assign_with_present_reduces_literals,
            apply or.symm,
            rw l_inv,
            apply g.property,
          },
        },
      },
      {
        
      },

      
    },

  },
end
