import data.nat.parity
import tactic.ring
open nat

def sum' : ℕ → ℕ
  | 0 := 0
  | (n+1) := n + 1 + sum' n

lemma trinum_doubled :
  ∀ n : ℕ, n * n + n = 2 * sum' n :=
begin
  intro n,
  induction n with n ih,
  {
    simp,
    unfold sum',
  },
  {
    dunfold sum',
    simp [succ_eq_add_one, add_mul, mul_add, ←ih],
    ring_nf,
  }
end

lemma trinum :
  ∀ n : ℕ, n * (n + 1) / 2 = sum' n :=
begin 
  intro n,
  have h : even (n * (n + 1)) := by apply even_mul_succ_self,
  rw nat.div_eq_iff_eq_mul_left,
  rw [mul_add, mul_one, trinum_doubled, mul_comm],
  simp,
  exact even_iff_two_dvd.mp h,
end