import types

def assign_lit (l : literal) : formula → formula
| [] := []
| (x :: f) := 
  (if l ∈ x then [] else [list.remove_all x [l_not l]]) ++ assign_lit f

def assign_all (f : formula) (lits : list literal) :=
list.foldl (λ f l, assign_lit l f) f lits

lemma assign_removes : ∀ (f : formula) (l : literal), 
  l ∉ (assign_lit l f).join ∧ l_not l ∉ (assign_lit l f).join:=
begin
  intros f l,
  induction' f;
  rw assign_lit;
  simp,
  {
    apply and.intro,
    
    {
      intro h,
      cases' h;
      cases' h;
      cases' h,
      {
        cases' classical.em (l ∈ hd);
        simp [h] at left,
        {
          assumption,
        },
        {
          rw left at right,
          rw list.remove_all at right,
          simp [h] at right,
          assumption,
        },
      },
      {
        have not_in := ih l,
        simp at not_in,

        have not_in := (and.elim_left not_in) w left,
        exact not_in right,
      },
    },
    {
      intro h,
      cases' h;
      cases' h;
      cases' h,
      {
        cases' classical.em (l ∈ hd);
        simp [h] at left,
        {
          assumption,
        },
        {
          rw left at right,
          rw list.remove_all at right,
          simp [h] at right,
          assumption,
        },
        
      },
      {
        have not_in := ih l,
        simp at not_in,

        have not_in := (and.elim_right not_in) w left,
        exact not_in right,
      },
    },
  },
end

lemma assign_subset : ∀ (f : formula) (l : literal), 
  (assign_lit l f).join ⊆ f.join := 
begin
  intros f l_assign l h,
  induction f;
  rw assign_lit at h;
  simp [h],
  {
    apply h,
  },
  {
    simp at h,
    cases' h,
    {
      cases' h,
      cases' h,
      cases' classical.em (l_assign ∈ f_hd);
      simp [h] at left,
      {
        apply classical.by_contradiction,
        intros,
        assumption,
      },
      {
        rw left at right,
        have sub : list.remove_all f_hd [l_not l_assign] ⊆ f_hd := 
          by apply list.filter_subset,
        apply or.intro_left,
        apply sub,
        assumption,
      },
    },
    {
      cases' h,
      cases' h,
      apply or.intro_right,
      simp at f_ih,
      apply f_ih w left right,
    },
  },
end

lemma list_not_in_append {α : Type} (a b : list  α) (c : α) : c ∉ a ++ b ↔ c ∉ a ∧ c ∉ b :=
begin
  apply iff.intro,
  {
    intro h,
      
    induction' a,
    {
      simp at h,
      simp [h],
    },
    {
      simp [h],
      rw not_or_distrib,
      have n_in :=  list.ne_and_not_mem_of_not_mem_cons h,
      cases' n_in,
      simp [left],
      apply ih,
      exact right,
    },
  },
  {
    intro h,
    cases' h,
    exact list.not_mem_append left right,
  },
end

lemma assign_when_not_in_out : ∀ (f : formula) (l : literal) (c : clause), 
  c ∈ f → c ∉ assign_lit l f → l_not l ∈ c ∨ l ∈ c := 
begin 
  intros f l c c_f c_n_a_f,
  induction' f,
  {
    simp at c_f,
    contradiction,
  },
  {
    cases' classical.em (c ∈ f),
    {
      rw assign_lit at c_n_a_f,

      apply ih,
      {
        assumption,
      },
      {
        rw list_not_in_append at c_n_a_f,
        cases' c_n_a_f,
        assumption,
      },
    },
    {
      have eq : c = hd := begin
        cases' c_f,
        {
          assumption,
        },
        {
          contradiction,
        },
      end,
      rw assign_lit at c_n_a_f,
      rw eq,
      rw eq at c_n_a_f,

      apply classical.by_contradiction,
      intro h,
      rw not_or_distrib at h,
      cases h,
      simp [h_left, h_right] at c_n_a_f,
      rw not_or_distrib at c_n_a_f,
      cases c_n_a_f,
      
      have h_eq : list.remove_all hd [l_not l] = hd  := begin
        rw list.remove_all,
        simp,
        rw list.filter_eq_self,
        intros a h,
        intro h_eq,
        rw ←h_eq at h_left,
        contradiction,
      end,

      rw h_eq at c_n_a_f_left,
      contradiction,
    },
  },
end

lemma assign_with_present_reduces_literals : 
∀ (f : formula) (l : literal), 
l ∈ f.join ∨ l_not l ∈ f.join → 
num_literals (assign_lit l f) < num_literals f :=
begin 
  intros f l h,
  rw num_literals,
  rw num_literals,
  apply num_distinct_reduced,
  apply assign_subset,
  cases' h;
  simp at h;
  simp,
  {
    apply exists.intro l,
    
    apply and.intro,
    {
      assumption,
    },
    {
      have removed := and.elim_left (assign_removes f l),
      simp at removed,
      exact removed,
    },
  },
  {
    apply exists.intro (l_not l),
    apply and.intro,
    {
      assumption,
    },
    {
      have removed := and.elim_right (assign_removes f l),
      simp at removed,
      exact removed,
    },
  },
end

lemma assign_without_present_eq  (f : formula) (l : literal) : 
l ∉ f.join ∧ l_not l ∉ f.join → assign_lit l f = f :=
begin 
  intro h,
  induction' f;
  rw assign_lit,
  {
    simp at h,
    cases' h,
    rw not_or_distrib at left,
    rw not_or_distrib at right,
    cases' left,
    cases' right,
    simp [left],
    apply and.intro,
    {
      rw list.remove_all,
      rw list.filter_eq_self,
      simp,
      intros a h_in,
      intro eq,
      rw eq at h_in,
      contradiction,
    },
    {
      apply ih,
      simp [right, right_1],
    },
  },
end

lemma assign_leq_literals (f : formula) (l : literal) : 
num_literals (assign_lit l f) ≤ num_literals f :=
begin 
  cases' classical.em (l ∉ f.join ∧ l_not l ∉ f.join),
  {
    have h := assign_without_present_eq _ _ h,
    rw h,
  },
  {
    rw not_and_distrib at h,
    have h : l ∈ f.join ∨ l_not l ∈ f.join := begin
      simp,
      simp at h,
      apply h,
    end,

    have less := assign_with_present_reduces_literals _ _ h,
    linarith,
  },
end

lemma list_containment_l {α : Type} : ∀ (a b : list α) (c : α), 
  c ∉ b → c ∈ a ++ b → c ∈ a :=
begin
  intros a b c h_1 h_2,
  induction' a;
  finish,
end

lemma removed_literal_must_be_contained 
  (f : formula) (l : literal) (c : clause):
  c ∈ f → c ∉ assign_lit l f → l ∉ c → l_not l ∈ c → 
  c.remove_all [l_not l] ∈ assign_lit l f := 
begin
  intros h_in_f h_n_in_a_f l_n_in_c n_l_in_c,
  induction' f,
  {
    simp at h_in_f,
    contradiction,
  },
  {
    cases' classical.em (c = hd),
    {
      rw assign_lit,
      rw h at l_n_in_c,
      simp [l_n_in_c],
      apply or.inl,
      rw h,
    },
    {
      have in_f : c ∈ f := list.mem_of_ne_of_mem h h_in_f,
      rw assign_lit,
      simp,
      apply or.inr,
      apply ih _ _ l_n_in_c n_l_in_c in_f,

      rw assign_lit at h_n_in_a_f,
      simp at h_n_in_a_f,
      rw not_or_distrib at h_n_in_a_f,
      cases' h_n_in_a_f,
      assumption,
    },
  },
end

def add_l_to_assign (a : assignment) (l : literal) : assignment := 
subtype.mk (a.val.remove_all [l_not l] ++ [l]) begin
  intros l_other h_l_in,
  simp,
  rw not_or_distrib,
  cases' classical.em (l = l_other),
  {
    rw h,
    apply and.intro,
    {
      intro h_in,
      apply list.of_mem_filter h_in,
      simp,
    },
    {
      intro h_eq,
      have neq := l_not_neq l_other,
      rw h_eq at neq,
      contradiction,
    },
  },
  {
    apply and.intro,
    {
      have in_filtered : l_other ∈ a.val.remove_all [l_not l] := begin
        apply list_containment_l _ _ _ _ h_l_in,
        simp,
        intro h_eq,
        rw h_eq at h,
        contradiction,
      end,
      have other_in : l_other ∈ a.val := begin
        rw list.remove_all at in_filtered,
        rw list.mem_filter at in_filtered,
        cases' in_filtered,
        exact left,
      end,
      have not_not_in : l_not l_other  ∉ a.val := begin
        apply a.property,
        exact other_in,
      end,
      rw list.remove_all,
      rw list.mem_filter,
      rw not_and_distrib,
      apply or.inl not_not_in,
    },
    {
      intro h_eq,
      rw ←h_eq at h_l_in,
      simp at h_l_in,
      apply list.of_mem_filter h_l_in,
      simp,
    },
  },
end

lemma assign_sat_implies_sat :
∀ (f : formula) (l : literal), sat (assign_lit l f) → sat f := begin
  intros f l h,
  set a_f := assign_lit l f,
  cases' h,
  let assigned := [l],
  let filtered := (w.val.remove_all [l_not l]),
  let new_a := filtered ++ assigned,

  apply exists.intro (add_l_to_assign w l),
  rw add_l_to_assign,
  rw formula_sat,
  intros c h_in_f,
  rw clause_sat,

  cases' classical.em (c ∈ a_f),
  {
    rw formula_sat at h,
    cases' (h c h_1),
    apply exists.intro w_1,
    cases' h_2,
    simp [right],

    have actually_in : w_1 ∈ list.join (assign_lit l f) := begin
      simp,
      apply exists.intro c,
      simp [h_1, right],
    end,
    have w_neq : w_1 ≠ l_not l := begin
      cases' (assign_removes f l),
      intro h_eq,
      rw h_eq at actually_in,
      contradiction,
    end,

    have h_in : w_1 ∈ filtered := begin
      apply list.mem_filter_of_mem,
      assumption,
      simp,
      apply w_neq,
    end,

    have is_in : w_1 ∈ new_a := by simp [h_in],
    simp only [new_a, filtered] at is_in,
    apply is_in,
  },
  {
    cases' classical.em (l ∈ c),
    {
      apply exists.intro l,
      simp [h_2],
      have l_in : l ∈ (filtered ++ assigned) := begin
        simp only [assigned],
        simp,
      end,
      apply l_in,
    },
    {
      have either := assign_when_not_in_out _ _ _ h_in_f h_1,
      simp [h_2] at either,

      let removed := c.remove_all [l_not l],
      have removed_in : removed ∈ a_f := 
        removed_literal_must_be_contained _ _ _ h_in_f h_1 h_2 either,
      rw formula_sat at h,
      have h := h removed removed_in,
      cases' h,
      apply exists.intro w_1,
      cases' h_3,
      have removed_sub : removed ⊆ c := by apply list.filter_subset,
      have neq_l : w_1 ≠ l := begin
        intro h,
        rw h at right,
        have in_c : l ∈ c := begin
          apply removed_sub,
          exact right,
        end,
        contradiction,
      end,
      have neq_n_l : w_1 ≠ l_not l := begin
        intro h,
        rw h at right,
        apply list.of_mem_filter right,
        simp,
      end,
      apply and.intro,
      {
        apply list.mem_append_left,
        apply list.mem_filter_of_mem left,
        simp,
        exact neq_n_l,
      },
      {
        apply removed_sub,
        exact right,
      },
    },
  },
end

lemma must_exist_filtered_clause (f : formula) (l : literal) (c : clause):
c ∉ f → c ∈ assign_lit l f → 
(∃ (c' : clause), c'.remove_all [l_not l] = c ∧ c' ∈ f) := 
begin
  intros h_n_in_f h_in_a_f,
  induction' f,
  {
    rw assign_lit at h_in_a_f,
    simp at h_in_a_f,
    contradiction,
  },
  {
    cases' classical.em (hd.remove_all [l_not l] = c),
    {
      apply exists.intro hd,
      apply and.intro,
      {
        exact h,
      },
      {
        simp,
      },
    },
    {
      rw assign_lit at h_in_a_f,
      simp at h_in_a_f,
      cases' h_in_a_f,
      {
        cases' classical.em (l ∈ hd);
        simp [h_2] at h_1,
        {
          contradiction,
        },
        {
          rw h_1 at h,
          contradiction,
        },
      },
      {
        have ih := ih _ _ (list.not_mem_of_not_mem_cons h_n_in_f) h_1,
        cases' ih,
        apply exists.intro w,
        simp [h_2],
      },
    },
  },
end

lemma sat_implies_assign_sat_or_cant_exist (f : formula) (l : literal) :
(∃ (a : assignment), formula_sat a f ∧ l ∈ a) → 
sat (assign_lit l f) := 
begin
  intros assign_exists,
  cases' assign_exists,
  cases' h,
  apply exists.intro w,
  rw formula_sat,
  intros c c_in,
  rw formula_sat at left,
  cases' classical.em (c ∈ f),
  {
    exact left c h,
  },
  {
    have exists_filtered := must_exist_filtered_clause _ _ _ h c_in,
    cases' exists_filtered,
    cases' h_1,
    have clause_sat_other := left w_1 right_1,
    rw clause_sat at clause_sat_other,
    cases' clause_sat_other,
    apply exists.intro w_2,
    simp [h_1],
    rw ←left_1,
    apply list.mem_filter_of_mem,
    {
      simp [h_1],
    },
    {
      intro h,
      simp at h,
      cases' h_1,
      rw h at left_2,
      apply w.property _ right left_2,
    },
  },
end

lemma assign_all_leq_num_literals (f : formula) (lits : list literal)
: num_literals (assign_all f lits) ≤ num_literals f := 
begin
  rw assign_all,
  induction' lits;
  simp,
  have ih := ih (assign_lit hd f),
  have less : num_literals (assign_lit hd f) ≤ num_literals f := 
    by apply assign_leq_literals,
  linarith,
end
