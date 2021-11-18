import data.set.finite
import tactic.induction
import tactic.linarith
import tactic.rcases

def num_distinct {α : Type} [decidable_eq α] (a : list α) := a.erase_dup.length

lemma num_distinct_reduced {α : Type} [decidable_eq α] :
∀ (a b : list α), 
a ⊆ b → 
(∃ x ∈ b, x ∉ a) → 
num_distinct a < num_distinct b := 
begin
  intros a b h_sub,
  intro elim_exists,
  rw num_distinct,
  rw num_distinct,

  induction' h_in : a.erase_dup;
  cases' elim_exists;
  cases' h;
  have has_elim : w ∈ b.erase_dup := begin
    rw list.mem_erase_dup,
    apply w_1,
  end;
  have non_empty : b.erase_dup.length > 0 := list.length_pos_of_mem has_elim;
  simp,
  {
    exact non_empty,
  },
  {
    have sub : a.erase_dup ⊆ b.erase_dup := begin
      intros x h,
      rw list.mem_erase_dup at h,
      rw list.mem_erase_dup,
      apply h_sub,
      assumption,
    end,
      
    have a_nodup : a.erase_dup.nodup := list.nodup_erase_dup a,
    have b_nodup : b.erase_dup.nodup := list.nodup_erase_dup b,
    have contained_a : hd ∈ a.erase_dup := by simp [h_in],
    have contained_b : hd ∈ b.erase_dup := begin
      apply sub,
      assumption,
    end,
    let b_rec := b.erase_dup.erase hd,
    let ih := ih x b_rec,

    have eq : b.erase_dup.length = b_rec.length + 1 := begin
      simp only [b_rec],
      have equiv : (b.erase_dup.erase hd).length = b.erase_dup.length.pred := begin
        apply list.length_erase_of_mem,
        apply sub,
        simp [h_in],
      end,

      rw equiv,

      have eq : b.erase_dup.length.pred + 1 = b.erase_dup.length := nat.succ_pred_eq_of_pos non_empty,

      rw eq,
    end,
    rw eq,
    simp,
    have eq : b_rec.erase_dup = b_rec := begin
      rw list.erase_dup_eq_self,
      simp only [b_rec],
      apply list.nodup_erase_of_nodup,
      assumption,
    end,
    have neq : w ≠ hd := begin
      intro eq,
      rw eq at h,
      rw list.mem_erase_dup at contained_a,
      exact h contained_a,
    end,

    rw eq at ih,
    apply ih,
    {
      intros l h,
      have contained_l_a : l ∈ a.erase_dup := by simp [h_in, h],

      rw list.mem_erase_of_ne,
      {
        apply sub,
        assumption,
      },
      {
        intro eq,
        rw ←eq at h_in,
        have n_d : (l :: x).nodup := begin
          rw ←h_in,
          assumption,
        end,
        have n_n_d : ¬(l :: x).nodup := list.not_nodup_cons_of_mem h,
        exact n_n_d n_d,
      },
    },
    {
      apply exists.intro w,
      simp,
      apply and.intro,
      {
        rw list.mem_erase_of_ne neq,
        assumption,
      },
      {
        intro contradict,
        have next : w ∈ a.erase_dup := by simp [h_in, contradict],
        rw list.mem_erase_dup at next,
        exact h next,
      },
    },
    {
      have x_nodup : x.nodup := begin
        rw h_in at a_nodup,
        exact list.nodup_of_nodup_cons a_nodup,
      end,
      exact list.nodup.erase_dup x_nodup,
    },
  }
end
