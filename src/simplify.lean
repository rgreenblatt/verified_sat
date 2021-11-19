import assign
import pure_literal
import unit_clauses

def simplify : formula → formula
| f := 
let new_f := assign_unit_clauses (assign_pure_literals f) in 
if h : num_literals new_f < num_literals f then simplify new_f else new_f
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf num_literals⟩]}

lemma overall_leq (f : formula) : 
num_literals (assign_unit_clauses (assign_pure_literals f)) ≤ num_literals f := 
begin
  have leq_unit : num_literals (assign_unit_clauses (assign_pure_literals f)) ≤ num_literals (assign_pure_literals f) := 
  by apply unit_clauses_leq_num_literals,
  have leq_pure : num_literals (assign_pure_literals f) ≤ num_literals f :=
  by apply pure_literals_leq_num_literals,
  linarith,
end

-- TODO: consider generalizing induction approach here to avoid code dup

lemma simplify_leq_num_literals  : 
∀ (f : formula), num_literals (simplify f) ≤ num_literals f := begin
  intro f,
  induction h_eq : (num_literals f) using nat.strong_induction_on with n ih generalizing f,
  let is_less := num_literals (assign_unit_clauses (assign_pure_literals f)) < num_literals f,
  cases' classical.em is_less;
  rw simplify;
  simp only [is_less] at h;
  simp [h];
  have leq := overall_leq f,
  {
    rw h_eq at h,
    let sub_f := (assign_unit_clauses (assign_pure_literals f)),
    have ih := ih (num_literals sub_f) h sub_f (by refl),
    linarith,
  },
  {
    linarith,
  },
end

theorem simplify_correct (f : formula) : sat (simplify f) ↔ sat f := begin
  induction h_eq : (num_literals f) using nat.strong_induction_on with n ih generalizing f,
  let is_less := num_literals (assign_unit_clauses (assign_pure_literals f)) < num_literals f,
  cases' classical.em is_less;
  rw simplify;
  simp only [is_less] at h;
  simp [h],
  {
    rw h_eq at h,
    let sub_f := (assign_unit_clauses (assign_pure_literals f)),
    have ih := ih (num_literals sub_f) h sub_f (by refl),
    simp only [sub_f] at ih,
    rw ih,
    rw ←unit_clause_correct,
    rw ←pure_literal_correct,
  },
  {
    rw ←unit_clause_correct,
    rw ←pure_literal_correct,
  },
end
