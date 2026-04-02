import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.show false

open Nat Finset

namespace Erdos

theorem master_identity {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) := by
  have hi_le_n : i ≤ n := le_trans hij hjn
  have hji_le_ni : j - i ≤ n - i := Nat.sub_le_sub_right hjn i
  have hsub : n - i - (j - i) = n - j := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hij
  have h2 := Nat.choose_mul_factorial_mul_factorial hjn
  have h3 := Nat.choose_mul_factorial_mul_factorial hi_le_n
  have h4 := Nat.choose_mul_factorial_mul_factorial hji_le_ni
  rw [hsub] at h4
  have lhs : n.choose j * j.choose i *
      (i.factorial * (j - i).factorial * (n - j).factorial) = n.factorial := by
    calc n.choose j * j.choose i *
          (i.factorial * (j - i).factorial * (n - j).factorial)
        = n.choose j * (j.choose i * i.factorial * (j - i).factorial) *
          (n - j).factorial := by ring
      _ = n.choose j * j.factorial * (n - j).factorial := by rw [h1]
      _ = n.factorial := h2
  have rhs : n.choose i * (n - i).choose (j - i) *
      (i.factorial * (j - i).factorial * (n - j).factorial) = n.factorial := by
    calc n.choose i * (n - i).choose (j - i) *
          (i.factorial * (j - i).factorial * (n - j).factorial)
        = n.choose i * i.factorial *
          ((n - i).choose (j - i) * (j - i).factorial * (n - j).factorial) := by ring
      _ = n.choose i * i.factorial * (n - i).factorial := by rw [h4]
      _ = n.factorial := h3
  have hD : 0 < i.factorial * (j - i).factorial * (n - j).factorial := by positivity
  calc n.choose j * j.choose i
      = n.choose j * j.choose i *
        (i.factorial * (j - i).factorial * (n - j).factorial) /
        (i.factorial * (j - i).factorial * (n - j).factorial) := by
        rw [Nat.mul_div_cancel _ hD]
    _ = n.factorial /
        (i.factorial * (j - i).factorial * (n - j).factorial) := by rw [lhs]
    _ = n.choose i * (n - i).choose (j - i) *
        (i.factorial * (j - i).factorial * (n - j).factorial) /
        (i.factorial * (j - i).factorial * (n - j).factorial) := by
        rw [rhs]
    _ = n.choose i * (n - i).choose (j - i) := by rw [Nat.mul_div_cancel _ hD]

theorem carry_lemma {p V r j : ℕ} (hp : Nat.Prime p) (_hV : 2 ≤ V)
    (hr : r < p) (hj_lb : p ≤ j) (hj_ub : j < p ^ V) :
    p ∣ (r + p ^ V).choose j := by
  rw [Nat.add_choose_eq]
  apply Finset.dvd_sum
  intro ⟨s, t⟩ hst
  rw [Finset.mem_antidiagonal] at hst
  by_cases hs : r < s
  · have : r.choose s = 0 := Nat.choose_eq_zero_of_lt hs
    simp only [this, zero_mul, dvd_zero]
  · push Not at hs
    apply dvd_mul_of_dvd_right
    have ht_ne_zero : t ≠ 0 := by omega
    have ht_ne_pow : t ≠ p ^ V := by omega
    exact hp.dvd_choose_pow ht_ne_zero ht_ne_pow

theorem carry_lemma_at_p {p V r : ℕ} (hp : Nat.Prime p) (hV : 2 ≤ V)
    (hr : r < p) :
    p ∣ (r + p ^ V).choose p := by
  apply carry_lemma hp hV hr le_rfl
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ V := Nat.pow_lt_pow_right (Nat.Prime.one_lt hp) (by omega)

theorem carry_lemma_fo_resolution {p V r j : ℕ} (hp : Nat.Prime p)
    (hV : 2 ≤ V) (hr : r < p) (hj_lb : p ≤ j)
    (hj_half : 2 * j ≤ r + p ^ V) :
    p ∣ Nat.gcd ((r + p ^ V).choose p) ((r + p ^ V).choose j) := by
  apply Nat.dvd_gcd
  · exact carry_lemma_at_p hp hV hr
  · apply carry_lemma hp hV hr hj_lb
    have hpV : p ≤ p ^ V := Nat.le_self_pow (by omega) p
    omega

theorem prime_not_dvd_factorial {q m : ℕ} (hq : Nat.Prime q)
    (hm : m < q) : ¬(q ∣ m.factorial) := by
  induction m with
  | zero =>
    rw [factorial_zero]
    exact hq.not_dvd_one
  | succ k ih =>
    intro h
    rw [Nat.factorial_succ] at h
    rcases hq.dvd_mul.mp h with h1 | h1
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · exact ih (by omega) h1

theorem tame_prime {q i j : ℕ} (hq : Nat.Prime q)
    (hq_gt_ji : j - i < q) (hq_le_j : q ≤ j)
    (hq_gt_i : i < q) (hij : i ≤ j) :
    q ∣ j.choose i := by
  have hq_dvd_jfac : q ∣ j.factorial := dvd_factorial hq.pos hq_le_j
  have hq_ndvd_ifac : ¬(q ∣ i.factorial) :=
    prime_not_dvd_factorial hq hq_gt_i
  have hq_ndvd_jifac : ¬(q ∣ (j - i).factorial) :=
    prime_not_dvd_factorial hq hq_gt_ji
  have hfac := Nat.choose_mul_factorial_mul_factorial hij
  have hqdvd : q ∣ j.choose i * i.factorial * (j - i).factorial := by
    rw [hfac]; exact hq_dvd_jfac
  have hqdvd2 : q ∣ j.choose i * (i.factorial * (j - i).factorial) := by
    rwa [mul_assoc] at hqdvd
  rcases hq.dvd_mul.mp hqdvd2 with h | h
  · exact h
  · exfalso
    rcases hq.dvd_mul.mp h with h2 | h2
    · exact hq_ndvd_ifac h2
    · exact hq_ndvd_jifac h2

theorem case_B_alpha {n i j q : ℕ} (hq : Nat.Prime q)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hq_ndvd_ji : ¬(q ∣ j.choose i)) :
    q ∣ n.choose j := by
  have hmi := master_identity hij hjn
  have hq_dvd_rhs : q ∣ n.choose i * (n - i).choose (j - i) :=
    dvd_mul_of_dvd_left hq_dvd_ni _
  have hq_dvd_lhs : q ∣ n.choose j * j.choose i := hmi ▸ hq_dvd_rhs
  exact (hq.dvd_mul.mp hq_dvd_lhs).resolve_right hq_ndvd_ji

theorem case_B_alpha_gcd {n i j q : ℕ} (hq : Nat.Prime q)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hq_ndvd_ji : ¬(q ∣ j.choose i)) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) :=
  Nat.dvd_gcd hq_dvd_ni (case_B_alpha hq hij hjn hq_dvd_ni hq_ndvd_ji)

def FullyObstructed (n i j : ℕ) : Prop :=
  ∀ p, Nat.Prime p → i < p → p ∣ n.choose i → ¬(p ∣ n.choose j)

theorem fo_char {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (hfo : FullyObstructed n i j) :
    ∀ r, Nat.Prime r → i < r → r ∣ n.choose i → r ∣ j.choose i := by
  intro r hr hri hr_dvd
  by_contra hr_ndvd
  exact hfo r hr hri hr_dvd (case_B_alpha hr hij hjn hr_dvd hr_ndvd)

theorem absorption {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    j * n.choose j = n * (n - 1).choose (j - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    cases j with
    | zero => omega
    | succ j =>
      have h := Nat.succ_mul_choose_eq n j
      show (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j
      linarith

theorem dvd_choose_of_dvd_n_not_dvd_j {n j p : ℕ} (hp : Nat.Prime p)
    (hpn : p ∣ n) (hpj : ¬(p ∣ j)) (hj : 1 ≤ j) (hjn : j ≤ n) :
    p ∣ n.choose j := by
  have hab := absorption hj hjn
  have : p ∣ j * n.choose j := by
    rw [hab]; exact dvd_mul_of_dvd_left hpn _
  exact (hp.dvd_mul.mp this).resolve_left hpj

theorem fo_10_3_5 : 3 ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) := by
  native_decide
theorem fo_16_2_6 : 2 ∣ Nat.gcd (Nat.choose 16 2) (Nat.choose 16 6) := by
  native_decide
theorem fo_28_3_14 : 3 ∣ Nat.gcd (Nat.choose 28 3) (Nat.choose 28 14) := by
  native_decide
theorem fo_28_5_14 : 5 ∣ Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) := by
  native_decide
theorem fo_244_3_122 : 3 ∣ Nat.gcd (Nat.choose 244 3) (Nat.choose 244 122) := by
  native_decide
theorem fo_512_2_147 : 2 ∣ Nat.gcd (Nat.choose 512 2) (Nat.choose 512 147) := by
  native_decide
theorem fo_2048_2_713 : 2 ∣ Nat.gcd (Nat.choose 2048 2) (Nat.choose 2048 713) := by
  native_decide
theorem fo_2188_3_1094 : 3 ∣ Nat.gcd (Nat.choose 2188 3) (Nat.choose 2188 1094) := by
  native_decide

theorem fo_10_M1 : 10 % 3 = 1 ∧ 10 - 1 = 3 ^ 2 := by omega
theorem fo_16_M1 : 16 % 2 = 0 ∧ 16 = 2 ^ 4 := by omega
theorem fo_28_3_M1 : 28 % 3 = 1 ∧ 28 - 1 = 3 ^ 3 := by omega
theorem fo_28_5_M1 : 28 % 5 = 3 ∧ 28 - 3 = 5 ^ 2 := by omega
theorem fo_244_M1 : 244 % 3 = 1 ∧ 244 - 1 = 3 ^ 5 := by omega
theorem fo_512_M1 : 512 % 2 = 0 ∧ 512 = 2 ^ 9 := by omega
theorem fo_2048_M1 : 2048 % 2 = 0 ∧ 2048 = 2 ^ 11 := by omega
theorem fo_2188_M1 : 2188 % 3 = 1 ∧ 2188 - 1 = 3 ^ 7 := by omega

end Erdos