import assign
import pure_literal

def simplify (f : formula) : formula := assign_pure_literals f

lemma simplify_leq_num_literals (f : formula): 
num_literals (simplify f) ≤ num_literals f :=
begin 
  rw simplify,
apply assign_leq_literals,
end

theorem simplify_correct (f : formula) : sat (simplify f) ↔ sat f := begin
  rw simplify,
  rw ←pure_literal_correct,
end
