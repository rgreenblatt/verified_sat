import num_distinct

abbreviation atom := ℕ

@[derive [decidable_eq]]
structure literal :=
mk :: (atom : atom) (negated : bool)

@[instance] def literal.has_repr : has_repr literal :=
{
  repr := 
  λ x, match x with
  | {atom := atom, negated := n} := 
    "{literal . atom := " ++ repr atom ++ ", negated := " ++ repr n ++ "}"
  end
}

def l_not : literal → literal
| {atom := a, negated := n} := {atom := a, negated := !n}

@[simp] lemma literal_neq : ∀ l, l ≠ l_not l := begin
  intro l,
  cases' l,
  rw l_not,
  simp,
  intro h,
  cases' negated;
  finish,
end

@[simp] lemma l_inv : ∀ l, l_not (l_not l) = l := begin
  intro l,
  cases l,
  rw l_not,
  rw l_not,
  simp,
end

@[simp] lemma not_preserves_atom : ∀ l, (l_not l).atom = l.atom := begin
  intro l,
  cases l,
  rw l_not,
end

@[simp] lemma atom_must_be_equal : ∀ (a b : literal), 
a = b → a.atom = b.atom := 
begin
  intros a b,
  cases' a,
  cases' b,
  simp,
  intros h _,
  assumption,
end

@[simp] lemma eq_atom_iff : ∀ (a b : literal), 
  a.atom = b.atom ↔ a = b ∨ a = l_not b := 
begin
  intros a b,
  apply iff.intro;
  intro h;
  cases' a;
  cases' b;
  simp at h,
  {
    rw h,
    rw l_not,
    simp,
    cases' negated;
    cases' negated_1;
    simp,
  },
  {
    rw l_not at h,
    simp at h,
    simp,
    cases' h;
    simp [h],
  },
end

@[simp] lemma bool_neq_neg : ∀ (b : bool),  b ≠ !b := begin
  intro b,
  cases' b;
  simp,
end

@[simp] lemma l_not_neq : ∀ l, l ≠ l_not l := begin
  intro l,
  cases l,
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
def formula_sat (a : assignment) (f : formula) := 
  ∀ c, c ∈ f → clause_sat a c 
def sat (f : formula) := ∃ a, formula_sat a f

def num_literals (f : formula) : ℕ := num_distinct f.join

def non_empty_formula := {f : formula // f.join ≠ []}

def choice_func := 
  {g : non_empty_formula → literal // 
   ∀ (f : non_empty_formula),
     g f ∈ f.val.join ∨ l_not (g f) ∈ f.val.join}

def non_empty_list {α : Type} := {l : list α // l ≠ []}

def extract_first  {α : Type} : non_empty_list → α
| ⟨[], h⟩ := (h rfl).elim
| ⟨a::_, h⟩ := a

def naive_choice_func : choice_func := subtype.mk 
(λ f, extract_first (subtype.mk f.val.join f.property))
(begin
  intro f,
  apply or.inl,
  cases' joined : f.val.join,
  {
    apply classical.by_contradiction,
    intros,
    exact f.property joined,
  },
  {
    let non_empty_first : non_empty_list := ⟨list.join f.val, f.property⟩,
    have eq : non_empty_first = ⟨hd::x, by simp⟩ := begin
      simp,
      rw ←joined,
      simp,
    end,
    simp only [non_empty_first] at eq,
    rw eq,
    rw extract_first,
    rw joined,
    simp,
  },
end)


def example_sat_formula : formula := [[{atom := 3, negated := tt}]]
def example_unsat_formula : formula := 
  [[{atom := 3, negated := tt}], [{atom := 3, negated := ff}]]
def example_complex_formula : formula := [
  [{atom := 3, negated := tt}, {atom := 2, negated := ff}],
  [{atom := 3, negated := tt}, {atom := 2, negated := ff}],
  [{atom := 1, negated := tt}, {atom := 2, negated := ff}],
  [{atom := 1, negated := tt}, {atom := 3, negated := ff}]
]

def is_pure_literal (l : literal) (f: formula) : bool := 
  (l_not l) ∉ list.join f
