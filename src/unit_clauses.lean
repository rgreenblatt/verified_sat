import assign
import general_assign

def get_unit_clause_op : clause → option literal
| [l] := option.some l
| _ := option.none

lemma is_none_on_multiple (c : clause) (a b : literal) : 
get_unit_clause_op (a :: b :: c) = option.none :=
by rw get_unit_clause_op

def get_unit_clauses := list.filter_map get_unit_clause_op 

#eval get_unit_clauses example_unsat_formula
#eval get_unit_clauses example_sat_formula
#eval get_unit_clauses example_complex_formula

def assign_unit_clauses (f : formula) : formula :=
assign_all f (get_unit_clauses f)

#eval assign_unit_clauses example_unsat_formula
#eval assign_unit_clauses example_sat_formula
#eval assign_unit_clauses example_complex_formula

lemma unit_clause_not_removed (f : formula) (l a : literal)
: [a] ∈ f → l.atom ≠ a.atom → [a] ∈ assign_lit l f := begin
  intros h_a h_neq,
  induction' f;
  rw assign_lit;
  simp [h_a],
  cases' classical.em ([a] ∈ f),
  {
    apply or.inr,
    apply ih,
    assumption,
    assumption,
  },
  {
    have eq : [a] = hd := begin
      simp [h] at h_a,
      exact h_a
    end,
    apply or.inl,
    have n_in : l ∉ [a] := begin
      simp,
      intro h,
      have h := atom_must_be_equal _ _ h,
      contradiction,
    end,
    rw ←eq,
    simp [n_in],

    have eq : [a].remove_all [l_not l] = [a] := begin
      rw list.remove_all,
      rw list.filter_eq_self,
      intros b h,
      simp at h,
      simp,
      intro eq,
      rw h at eq,
      rw eq at h_neq,
      simp at h_neq,
      exact h_neq
    end,
    rw eq,
  },
end

def unit_or_missing (f : formula) (l : literal) : bool := 
  [l] ∈ f ∨ (l ∉ f.join ∧ l_not l ∉ f.join)

lemma unit_clause_impl_correct (f : formula) (units : list literal) 
: ↥(units.all (unit_or_missing f)) → 
(sat f ↔ sat (assign_all f units)) :=
begin
  intro h,
  rw assign_all,
  induction' units;
  simp,

  have h_f : ↥(units.all (unit_or_missing (assign_lit hd f))) := begin
    rw list.all_iff_forall,
    rw list.all_iff_forall at h,
    intros a h_in,
    have h := h a,
    rw unit_or_missing at h,
    simp [h_in] at h,
    cases' h,
    {
      cases' classical.em (hd.atom = a.atom);
      rw unit_or_missing;
      simp,
      {
        apply or.inr,
        have removes := assign_removes f hd,
        simp at removes,
        rw eq_atom_iff at h_2,
        cases' h_2,
        {
          rw ←h_2,
          apply removes,
        },
        {
          have eq : a = l_not (l_not a) := by simp,
          rw ←h_2 at eq,
          rw eq,
          simp,
          exact and.comm.mp removes,
        },
      },
      {
        apply or.inl,
        apply unit_clause_not_removed,
        exact h_1,
        exact h_2,
      },
    },
    {
      cases' h_1,
      have n_in : a ∉ f.join := begin
        simp,
        exact left,
      end,
      have n_n_in : l_not a ∉ f.join := begin
        simp,
        exact right,
      end,
      have sub : (assign_lit hd f).join ⊆ f.join := by apply assign_subset,
      rw unit_or_missing,
      have not_in : a ∉ list.join (assign_lit hd f) := begin
        apply mt,
        apply sub,
        exact n_in,
      end,
      have n_not_in : l_not a ∉ list.join (assign_lit hd f) := begin
        apply mt,
        apply sub,
        exact n_n_in,
      end,
      simp [not_in, n_not_in],
    },
  end,

  have ih := ih (assign_lit hd f) h_f,
  rw ←ih,

  rw list.all_iff_forall at h,
  have h := h hd,
  rw unit_or_missing at h,
  simp at h,
  cases' h,
  {
    apply general_assign,
    apply or.inl h_1,
  },
  {
    have eq := assign_without_present_eq f hd,
    cases' h_1,
    simp at eq,
    have eq := eq left right,
    rw eq,
  },
end

lemma unit_clause_correct (f : formula) : 
sat f ↔ sat (assign_unit_clauses f) := begin
  apply unit_clause_impl_correct,
  rw list.all_iff_forall,
  rw get_unit_clauses,
  intros a ha,
  rw unit_or_missing,
  simp,
  apply or.inl,
  rw list.mem_filter_map at ha,
  cases' ha,
  cases' h,
  cases' w,
  {
    rw get_unit_clause_op at right,
    simp at right,
    contradiction,
  },
  {
    cases' w,
    {
      rw get_unit_clause_op at right,
      simp at right,
      rw right at left,
      exact left,
    },
    {
      have is_none := is_none_on_multiple w hd hd_1,
      rw is_none at right,
      simp at right,
      contradiction,
    },
  },
end

lemma unit_clauses_leq_size (f : formula) 
: formula_size (assign_unit_clauses f) ≤ formula_size f := 
by apply assign_all_leq_size
