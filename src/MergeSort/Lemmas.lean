import tactic
import data.nat.log

lemma log_monotonic : ∀ {a b : ℕ} , a ≤ b → nat.log 2 a ≤ nat.log 2 b
| 0       := begin intros b _, rw nat.log, exact bot_le, end
| (a + 1) := have (a + 1) / 2 < a + 1, from nat.div_lt_self' a 0,
begin
  intros b h,
  cases b,
  { finish, },

  have half_leq : (a + 1) / 2 ≤ (b + 1) / 2 := nat.div_le_div_right h,

  rw nat.log,
  split_ifs,
  { refine ge.le _, rw nat.log, split_ifs,
    { refine add_le_add (log_monotonic half_leq) _, exact rfl.ge, },
    {
      have b_small := not_and_distrib.mp h_2,
      simp only [le_refl, not_le, not_true, or_false, nat.one_lt_bit0_iff]
           at b_small,

      cases b_small with b_small b_small,
      {
        have a_leq_zero := nat.succ_le_succ_iff.mp h,
        have a_is_zero  := eq_bot_iff.mpr a_leq_zero,
        rw a_is_zero at h_1,
        cases h_1 with absurd _,
        by_contradiction,
        exact not_and.mp h_2 absurd b_small,
      },
      by_contra,
      have succ_b_leq_zero := nat.succ_le_succ_iff.mp b_small,
      exact nat.not_succ_le_zero b succ_b_leq_zero,
    },
  },
  exact bot_le,
end

lemma log_pred : ∀ (a : ℕ) , nat.log 2 a - 1 = nat.log 2 (a / 2)
| 0 := by simp
| 1 := by norm_num
| (a + 2) :=
begin
  rw nat.log,
  split_ifs,
  { simp, },
  simp only [le_refl, not_true, zero_le, nat.one_lt_bit0_iff, and_self, le_add_iff_nonneg_left]
       at h,
  cases h,
end

lemma log_2_val : nat.log 2 2 = 1 :=
begin
  rw nat.log,
  split_ifs,
  { simp, },
  simp only [le_refl, not_true, nat.one_lt_bit0_iff, and_self]
       at h,
  cases h,
end

lemma sum_2b (a b : ℕ) : a ≤ 2 * b → a + 2 * b ≤ 4 * b :=
begin
  intro h,
  calc a + 2 * b ≤ 2 * b + 2 * b : by { refine add_le_add h _, exact rfl.ge }
       ...       = 4 * b : by linarith
end

lemma log_2_times : ∀ (a : ℕ), 2 * nat.log 2 (a + 2) ≤ a + 2
| 0       := by { rw log_2_val, norm_num, }
| (a + 1) := have (a + 1) / 2 < a + 1, from nat.div_lt_self' a 0,
begin
  rw nat.log,
  split_ifs,
  { have IH := log_2_times ((a + 1) / 2),
    rw mul_add,
    cases a,
    { norm_num, },
    cases a,
    { norm_num, rw log_2_val, simp, },
    norm_num,
    have add_one : 2 * nat.log 2 ((a.succ.succ + 1) / 2).succ ≤
                   2 * nat.log 2 ((a.succ.succ + 1) / 2 + 2), from
                      by {
                        refine mul_le_mul le_rfl _ bot_le bot_le,
                        refine log_monotonic _,
                        exact nat.le_succ ((a.succ.succ + 1) / 2 + 1),
                      },
    refine le_trans add_one _,
    refine le_trans IH _,
    have succ_succ_two : a.succ.succ + 1 = a + 3 := rfl,
    have two_div_two: ∀ {y}, (y + 2) / 2 = y / 2 + 1 :=
      by { intro, exact (y + 2).div_def 2, },
    have three_eq_one_plus_two : ∀ {y}, y + 3 = y + 1 + 2 :=
      by { intro, exact rfl, },
    rw [ succ_succ_two
       , two_div_two
       , three_eq_one_plus_two
       , ← three_eq_one_plus_two
       ],
    refine add_le_add _ (le_refl 3),
    exact nat.lt_succ_iff.mp (nat.div_lt_self' a 0),
  },
  exact bot_le,
end

lemma div_two : ∀ (b a : ℕ), 2 * a ≤ b → a ≤ b / 2
| 0       a       h := by { norm_num at h, simp only [nat.zero_div, nonpos_iff_eq_zero], exact h, }
| 1       0       h := by norm_num
| 1       (a + 1) h := by { rw mul_add at h, norm_num at h, linarith, }
| (b + 2) 0       h := bot_le
| (b + 2) (a + 1) h :=
begin
  have IH : a ≤ b / 2 := begin
                          refine div_two b a _,
                          rw mul_add at h,
                          simp only [mul_one, add_le_add_iff_right] at h,
                          exact h,
                        end,
  simp only [nat.succ_pos', nat.add_div_right],
  exact nat.succ_le_succ IH,
end
