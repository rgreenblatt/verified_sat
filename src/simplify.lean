import assign
import pure_literal
import unit_clauses

def simplify : formula → formula
| f := 
let new_f := assign_unit_clauses (assign_pure_literals f) in 
if h : formula_size new_f < formula_size f then simplify new_f else new_f
using_well_founded {rel_tac := λ _ _, 
                    `[exact ⟨_, measure_wf formula_size⟩]}


#eval simplify example_unsat_formula
#eval simplify example_sat_formula
#eval simplify example_complex_formula

lemma overall_leq (f : formula) : 
formula_size (assign_unit_clauses (assign_pure_literals f)) ≤ 
  formula_size f := 
begin
  have leq_unit : formula_size (assign_unit_clauses (assign_pure_literals f)) ≤ formula_size (assign_pure_literals f) := 
  by apply unit_clauses_leq_size,
  have leq_pure : formula_size (assign_pure_literals f) ≤ formula_size f :=
  by apply pure_literals_leq_size,
  linarith,
end

-- TODO: consider generalizing induction approach here to avoid code dup

lemma simplify_leq_size  : 
∀ (f : formula), formula_size (simplify f) ≤ formula_size f := begin
  intro f,
  induction h_eq : (formula_size f) using nat.strong_induction_on 
    with n ih generalizing f,
  let is_less := formula_size (assign_unit_clauses (assign_pure_literals f)) < 
    formula_size f,
  cases' classical.em is_less;
  rw simplify;
  simp only [is_less] at h;
  simp [h];
  have leq := overall_leq f,
  {
    rw h_eq at h,
    let sub_f := (assign_unit_clauses (assign_pure_literals f)),
    have ih := ih (formula_size sub_f) h sub_f (by refl),
    linarith,
  },
  {
    linarith,
  },
end

theorem simplify_correct (f : formula) : sat (simplify f) ↔ sat f := begin
  induction h_eq : (formula_size f) using nat.strong_induction_on 
    with n ih generalizing f,
  let is_less := formula_size (assign_unit_clauses (assign_pure_literals f)) < 
    formula_size f,
  cases' classical.em is_less;
  rw simplify;
  simp only [is_less] at h;
  simp [h],
  {
    rw h_eq at h,
    let sub_f := (assign_unit_clauses (assign_pure_literals f)),
    have ih := ih (formula_size sub_f) h sub_f (by refl),
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
