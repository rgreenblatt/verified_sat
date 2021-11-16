import data.set.finite
import tactic.induction
import tactic.linarith
import tactic.rcases

set_option trace.app_builder true

abbreviation atom := ℕ

@[derive [decidable_eq]]
structure literal :=
mk :: (atom : atom) (negated : bool)

@[instance] def literal.has_repr : has_repr literal :=
{
  repr := 
  λ x, match x with
  | {atom := atom, negated := n} := "{literal . atom := " ++ repr atom ++ ", negated := " ++ repr n ++ "}"
  end
}

def l_not : literal → literal
| {atom := a, negated := n} := {atom := a, negated := !n}


lemma l_inv : ∀ l, l_not (l_not l) = l := begin
  intro l,
  cases l,
  rw l_not,
  rw l_not,
  simp,
end


abbreviation clause := list literal

abbreviation formula := list clause

def assignment := {s : list literal // ∀ l, l ∈ s → l_not l ∉ s}

@[instance] def assignment.has_mem :
has_mem literal assignment :=
{
  mem := λ l as, l ∈ as.val
}

def clause_sat (a : assignment) (c : clause) := ∃ l, l ∈ a ∧ l ∈ c
def formula_sat (a : assignment) (f : formula) := ∀ c, c ∈ f → clause_sat a c 
def sat (f : formula) := ∃ a, formula_sat a f

def assign_lit (l : literal) : formula → formula
| [] := []
| (x :: f) := (if l ∈ x then [] else [list.remove_all x [l_not l]]) ++ assign_lit f

def formula_len (f : formula) : lex ℕ ℕ := (list.length f, list.length (list.join f))

lemma filter_reduces_length (α : Type) (p : α → Prop) [decidable_pred p] (l: list α)
: (list.filter p l).length ≤ l.length := begin
  induction' l,
  {
    simp,
  },
  {
    rw list.filter,
    cases' classical.em (p hd);
    simp [h];
    {
      have less : (list.filter p l).length ≤ l.length, by simp [ih],
      linarith,
    },
  },
end

def as_non_lex (x : lex ℕ ℕ) : ℕ × ℕ := x

lemma assign_keep_size (l : literal) (f : formula) : as_non_lex (formula_len (assign_lit l f)) ≤ as_non_lex (formula_len f) :=
begin
  induction' f,
  {
    rw assign_lit,
  },
  {
    rw assign_lit,
    rw formula_len,
    rw formula_len,
    rw as_non_lex,
    rw as_non_lex,
    let ih := ih l,
    rw formula_len at ih,
    rw formula_len at ih,
    rw as_non_lex at ih,
    rw as_non_lex at ih,
    rw list.join,
    simp,
    simp at ih,
    cases' ih,
    have eq : (list.remove_all hd [l_not l]).length ≤ hd.length, by begin
      rw list.remove_all,
      apply filter_reduces_length,
    end,

    cases' classical.em (l ∈ hd);
    simp [h];
    apply and.intro;
    linarith,
  },
end

lemma measure_lex {α : Type} (f : α → lex ℕ ℕ) : well_founded (inv_image (<) f) :=
inv_image.wf f (prod.lex_wf nat.lt_wf nat.lt_wf)

def check_sat : formula → bool
| [] := tt
| (x :: f_end) := 
  match x with
  | [] := ff
  | l :: k  := 
  let x := (l :: k) in
  let f := (x :: f_end) in
  have def_x : x = l :: k, from by refl,
  have in_x : l ∈ x, from begin
    rw def_x,
    exact list.mem_cons_self l k,
  end,
  have first : formula_len (assign_lit l ((l :: k) :: f_end)) < formula_len (x :: f_end), from begin
    rw formula_len,
    rw formula_len,
    rw assign_lit,

    simp [in_x],

    apply prod.lex.left,

    let h := assign_keep_size l f_end,
    rw formula_len at h,
    rw formula_len at h,
    rw as_non_lex at h,
    rw as_non_lex at h,
    cases' h,
    linarith,
  end,
  have second : formula_len (assign_lit (l_not l) ((l :: k) :: f_end)) < formula_len (x :: f_end), from begin
    rw formula_len,
    rw formula_len,

    rw assign_lit,

    rw l_inv,

    let h := assign_keep_size (l_not l) f_end,
    rw formula_len at h,
    rw formula_len at h,
    rw as_non_lex at h,
    rw as_non_lex at h,
    cases' h,
    simp at left,
    simp at right,

    cases' classical.em (l_not l ∈ x);

    simp [h],
    {
      apply prod.lex.left,
      linarith,
    },
    {

      cases' classical.em (list.length (assign_lit (l_not l) f_end) = f_end.length),
      {
        rw h_1,
        have eq : (f_end.length + 1 = 1 + f_end.length), by linarith,
        rw eq,

        apply prod.lex.right (1 + f_end.length),

        have less : (list.remove_all x [l]).length ≤ k.length, by begin
            rw list.remove_all,
            rw def_x,
            rw list.filter,
            simp,
            apply filter_reduces_length,
        end,

        linarith,
      },
      {
        have less : list.length (assign_lit (l_not l) f_end) < f_end.length, by exact (ne.le_iff_lt h_1).mp left,
        apply prod.lex.left,
        linarith,
      },
    },
  end,
  check_sat (assign_lit l f) || check_sat (assign_lit (l_not l) f)
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_lex formula_len⟩]}


theorem check_sat_correct  : ∀ (f : formula), (check_sat f = tt) ↔ sat f :=
begin
  intro f,
  -- TODO: this isn't going to work, we need custom induction!
  induction' f,
  {
    rw check_sat,
    simp,
    rw sat,
    let a : assignment := subtype.mk [] (by simp),
    apply exists.intro a,
    rw formula_sat,
    intro c,
    simp,
  },
  {
    rw check_sat,
    cases' hd,
    {
      simp,
      rw check_sat,
      rw sat,
      simp,
      intro a,
      intro h,
      let h := h list.nil,
      have nil_in_f : list.nil ∈ list.nil :: f, by simp,
      have nil_clause_sat : ∃ l, l ∈ a ∧ l ∈ list.nil := h nil_in_f,
      cases' nil_clause_sat,
      cases' h_1,
      apply right,
    },
    {
      let overall_f := (hd :: hd_1) :: f,
      simp,
      rw check_sat,
      let first_ret := check_sat (assign_lit hd ((hd :: hd_1) :: f)),
      let second_ret := check_sat (assign_lit (l_not hd) ((hd :: hd_1) :: f)),
      have implies_sat_first : first_ret = tt → sat overall_f := begin
        intro h,

      end,

      have implies_sat_second : second_ret = tt → sat overall_f := begin
        intro h,
        sorry,
      end,

      have both_false : first_ret = ff ∧ second_ret = ff → ¬ sat overall_f := begin
        sorry,
      end,

    
      cases' classical.em (check_sat (assign_lit hd ((hd :: hd_1) :: f)) = tt),
      {
        have is_sat : sat overall_f := begin
          apply implies_sat_first,
          apply h,
        end,
        simp [is_sat],
        apply or.inl h,
      },
      {
      cases' classical.em (check_sat (assign_lit (l_not hd) ((hd :: hd_1) :: f)) = tt),
      {
        have is_sat : sat overall_f := begin
          apply implies_sat_second,
          apply h_1,
        end,
        simp [is_sat],
        apply or.inr h_1,
      },
      {
        simp at h,
        simp at h_1,

        have is_unsat : ¬ sat overall_f := begin
          apply both_false,
          apply and.intro h h_1,
        end,

        simp [is_unsat, h, h_1],
      },
      },
    },

  },
end

def example_sat_formula : formula := [[{atom := 3, negated := bool.tt}]]
def example_unsat_formula : formula := [[{atom := 3, negated := bool.tt}], [{atom := 3, negated := bool.ff}]]

#eval check_sat example_sat_formula
#eval check_sat example_unsat_formula

def is_pure_literal (l : literal) (f: formula) : bool := (l_not l) ∉ list.join f

def get_pure_literals  (f : formula) : list literal := 
list.filter (λ l, is_pure_literal l f) f.join


def example_complex_formula : formula := [
  [{atom := 3, negated := bool.tt}, {atom := 2, negated := bool.ff}],
  [{atom := 3, negated := bool.tt}, {atom := 2, negated := bool.ff}],
  [{atom := 1, negated := bool.tt}, {atom := 2, negated := bool.ff}],
  [{atom := 1, negated := bool.tt}, {atom := 3, negated := bool.ff}]
]

#eval get_pure_literals example_unsat_formula
#eval get_pure_literals example_sat_formula
#eval get_pure_literals example_complex_formula

def assign_pure_literals (f : formula) : formula := 
list.foldl (λ f l, assign_lit l f) f (get_pure_literals f)

lemma filter_eq (α : Type) (p : α → Prop) [decidable_pred p] (l : list α) : 
(∀ x, x ∈ l → p x) →
list.filter p l = l :=
begin
  intro h,
  induction l,
  {
    simp,
  },
  {
    simp [h],
    apply l_ih,
    intros x h_in,
    simp [*],
  },
end

lemma assign_on_pure_is_subset : ∀ (f : formula) (l : literal), is_pure_literal l f → assign_lit l f ⊆ f :=
begin
  intros f l h c h_c,
  rw is_pure_literal at h,
  simp at h,
  induction' f,
  {
    rw assign_lit at h_c,
    simp [h_c],
  },
  {
    cases' classical.em (hd = c);
      simp [h_1],
    {
       apply or.inr,
       apply ih l,
       {
         rw assign_lit at h_c,
         cases' classical.em (l ∈ hd);
         simp [h_2] at h_c,
         {
          assumption,
         },
         {
          have eq : list.remove_all hd [l_not l] = hd := begin
            rw list.remove_all,
            have no_such : ∀ x ∈ hd, x ∉ [l_not l] := begin
              intros x h_other,
              simp,
              let h_k := h hd,
              simp at h_k,
              intro h,
              rw h at h_other,
              finish [h_k, h_other],
            end,

            apply filter_eq,
            finish,
          end,

          rw eq at h_c,
          apply or.elim h_c,
          {
            intro h_3,
            rw h_3 at h_1,
            apply false.elim,
            apply h_1,
            refl,
          },
          {
            simp,
          },
         },
       },
       {
        intros x h_in,
        apply h x,
        simp [h_in],
       },
    },
  },
end

#eval assign_pure_literals example_unsat_formula
#eval assign_pure_literals example_sat_formula
#eval assign_pure_literals example_complex_formula

lemma pure_literals_is_subset : ∀ (f : formula), assign_pure_literals f ⊆ f :=
begin
  intros f c h_c,
  rw assign_pure_literals at h_c,
  /- apply assign_on_pure_is_subset, -/
  sorry,

end

lemma containment_2 {α : Type} : ∀ (a b : list α) (c : α), c ∉ b → c ∈ a ++ b → c ∈ a :=
begin
  intros a b c h_1 h_2,
  induction' a;
  finish,
end

-- TODO: add here!
             
/- !any_clause_empty (x :: f) && bool.tt -/

/- example : sat example_formula := begin -/
/-   rw sat, -/
/-   apply exists.intro ((subtype.mk [{literal . atom := 3, negated := bool.tt}] begin -/
/-   intro l, -/
/-   intro h, -/

/-   cases h, -/
/-   { -/ 
/-     rw h, -/
/-     rw l_not, -/
/-     rw bnot, -/
/-     refine imp_false.mp _, -/
/-     intro h, -/
/-     induction h, -/
/-     { -/
/-       simp at h_1, -/
/-       assumption, -/
/-     }, -/
/-     { -/
/-       rw list.mem at h_1, -/
/-       assumption, -/
/-     }, -/
/-     }, -/
/-   { -/
/-     rw list.mem at h, -/

    
/-   } -/


    
/-   end) : assignment), -/
/- end -/

/- #eval if [1, 1, 1, 1] ⊆ [2] then 1 else 0 -/

/- def all_assignment_literals (as : assignment) : set atom := {a | ∃ n, ({literal . atom := a, negated := n} ∈ as)} -/
/- def all_clause_literals (c : clause) : set atom := {a | ∃ n, ({literal . atom := a, negated := n} ∈ c)} -/
/- def all_formula_literals (f : formula) : set atom := { a | ∃ c, c ∈ f ∧ a ∈ all_clause_literals c} -/
