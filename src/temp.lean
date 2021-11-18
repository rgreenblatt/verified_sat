import data.set.finite
import tactic.induction
import tactic.linarith
import tactic.rcases

lemma less (a b : ℕ) : a < b.succ → a ≤ b := begin
  intro h,
  library_search,



end
