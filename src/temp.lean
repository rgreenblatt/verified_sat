import sat

lemma outer {α : Type} : ∀ (x : α) (l k : list α), x ∉ k ∧ l ⊆ k → x ∉ l := begin
  intros x l k h,
  cases' h,
  library_search, -- ...
end

theorem pure_literal_correct : ∀ (f : formula), sat f  ↔  sat (assign_pure_literals f) :=
begin
  intro f,
  apply iff.intro,
  {
    sorry
    /- intro h, -/
    /- cases' h, -/
    /- rw sat, -/
    /- apply exists.intro w, -/
    /- rw formula_sat, -/
    /- intros c h_c, -/
    /- rw clause_sat, -/
    /- have contained : c ∈ f := begin -/
    /-   apply pure_literals_is_subset f, -/
    /-   assumption, -/
    /- end, -/
    /- let other := h c contained, -/
    /- apply other, -/
  },
  {
    intro h,
    cases' h,
    rw sat,
    let pures := get_pure_literals f,
    let filtered := (list.filter (λ l, l ∉ pures ∧ l_not l ∉ pures) (subtype.val w)),
    let w_new := filtered ++ pures,
    let w_new : assignment := subtype.mk w_new (sorry/-begin
      intros l h,
      cases' classical.em (l ∉ pures ∧ l_not l ∉ pures),
      {
        have contained : l ∈ filtered := begin
          apply containment_2 filtered pures l;
          finish,
        end,
        simp [h_1] at contained,
        let prop := (subtype.property w) l,
        finish,
      },
      {
        have not_in_list : l ∉ filtered := by finish,
        have neg_not_in_list : l_not l ∉ filtered := begin
          simp [h_1],
          intros h_4 h_5,
          rw l_inv,
          finish,
        end,

        simp at h_1,

        have contained : l ∈ pures := begin
          apply containment_2 pures filtered l;
          finish,
        end,

        have h_new : l ∈ get_pure_literals f := contained,
        rw get_pure_literals at h_new,
        have pure: is_pure_literal l f := by finish,
        rw is_pure_literal at pure,

        have not_contained : l_not l ∉ pures := begin
          have sub : pures ⊆ f.join := by apply list.filter_subset, 

          have not_in_formula : l_not l ∉ f.join := begin
            simp,
            intro x,
            simp at pure,
            apply pure,
          end,

          apply outer,
          apply and.intro,
          {
            exact not_in_formula,
          },
          {
            assumption,
          },
        end,

        finish,
      },
    end-/),
    apply exists.intro w_new,
    rw formula_sat,
    intros c h_c,
    rw clause_sat,
    cases' classical.em (c ∈ assign_pure_literals f),
    {
      rw formula_sat at h,
      let h_new := h c h_1,
      rw clause_sat at h_new,
      cases' h_new,
      apply exists.intro w_1,
      cases h_2,
      apply and.intro,
      {
        have not_in : w_1 ∉ pures := begin
          
          
        end,
        sorry,
      },
      {
        assumption,
      },


    },
    {
    },

  },
end
