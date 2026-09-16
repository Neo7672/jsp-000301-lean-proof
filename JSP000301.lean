/-!
# JSP-000301: Consecutive powerful numbers without a perfect square

**The Justin Sun Prize problem bank, entry JSP-000301.**

Original question: *If two consecutive positive integers are powerful, must at
least one be a perfect square?*

Answer: **No.** The counterexample:

* `12167 = 23^3` — powerful: its only prime divisor is 23, and `23^2 ∣ 23^3`;
* `12168 = 2^3 · 3^2 · 13^2` — powerful: `2^2 ∣ 2^3`, `3^2 ∣ 3^2`, `13^2 ∣ 13^2`;
* `110^2 = 12100 < 12167 < 12168 < 12321 = 111^2`, so neither is a square.

The file is self-contained (bare Lean 4, no Mathlib / no Batteries).
Primality is decided by trial division; the divisor classification of
12167 / 12168 is discharged by a finite computation over `p < 12168`
(`checkAllP`, verified natively via `native_decide`).

Background: Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970)
848-855; Walsh, *Consecutive integer pairs of powerful numbers and related
Diophantine equations*, Fibonacci Quart. 14 (1976) 111-116; Guy,
*Unsolved Problems in Number Theory*, 3rd ed. (2004).
-/

/-! ## Decidable trial-division primality -/

/-- `noDivisorUpTo p k = true` iff no `d` with `2 ≤ d ≤ k+1` divides `p`. -/
def noDivisorUpTo (p k : Nat) : Bool :=
  match k with
  | 0 => true
  | k + 1 => noDivisorUpTo p k && !decide ((k + 2) ∣ p)

theorem noDivisorUpTo_true_iff {p k : Nat} :
    noDivisorUpTo p k = true ↔ ∀ d, 2 ≤ d → d ≤ k + 1 → ¬ (d ∣ p) := by
  induction k with
  | zero =>
      constructor
      · intro _ d h2 hle; omega
      · intro _; rfl
  | succ k ihk =>
      have decFalse {q : Prop} [Decidable q] (h : decide q = false) : ¬ q := by
        intro hq
        rw [decide_eq_true hq] at h
        exact Bool.noConfusion h
      constructor
      · intro h d h2 hdle hdv
        simp only [noDivisorUpTo, Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨h1, h2b⟩ := h
        by_cases hd : d ≤ k + 1
        · exact (ihk.mp h1) d h2 hd hdv
        · have hed : d = k + 2 := by omega
          subst hed
          exact decFalse h2b hdv
      · intro hall
        simp only [noDivisorUpTo, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨?_, ?_⟩
        · exact ihk.mpr fun d h2 hdle hdv => hall d h2 (by omega) hdv
        · cases hdec : decide ((k + 2) ∣ p) with
          | true =>
              exact absurd (of_decide_eq_true hdec)
                (hall (k + 2) (by omega) (by omega))
          | false => rfl

/-- Trial-division primality: `isPrime p = true` iff `p` has no divisor in `[2, p)`. -/
def isPrime (p : Nat) : Bool :=
  if p < 2 then false else noDivisorUpTo p (p - 2)

theorem isPrime_true_iff {p : Nat} (h : isPrime p = true) :
    2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → ¬ (d ∣ p) := by
  unfold isPrime at h
  split at h
  · exact absurd h (by decide)
  · rw [noDivisorUpTo_true_iff] at h
    have hp2 : p - 2 + 1 = p - 1 := by omega
    rw [hp2] at h
    refine ⟨by omega, ?_⟩
    intro d h2d hdlt hdv
    have hdle : d ≤ p - 1 := by omega
    exact h d h2d hdle hdv

/-! ## Powerful numbers and squares -/

/-- `n` is powerful when every prime divisor `p` of `n` satisfies `p * p ∣ n`. -/
def Powerful (n : Nat) : Prop :=
  ∀ p, isPrime p = true → p ∣ n → p * p ∣ n

def IsSquare (n : Nat) : Prop := ∃ r, r * r = n

/-! ## Finite witness checks -/

/-- `checkAllP target stop ok = true` iff every `p < stop` with `isPrime p`
and `p ∣ target` satisfies `ok p = true`. -/
def checkAllP (target stop : Nat) (ok : Nat → Bool) : Bool :=
  match stop with
  | 0 => true
  | stop + 1 =>
    checkAllP target stop ok &&
      (!(decide (isPrime stop)) || !(decide (stop ∣ target)) || ok stop)

theorem checkAllP_spec {target stop : Nat} {ok : Nat → Bool}
    (h : checkAllP target stop ok = true) :
    ∀ p, p < stop → isPrime p = true → p ∣ target → ok p = true := by
  induction stop with
  | zero => intro p hp; exact absurd hp (Nat.not_lt_zero p)
  | succ stop ih =>
      intro p hp hprime hdv
      simp only [checkAllP, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge p stop with hlt | hge
      · exact ih h1 p hlt hprime hdv
      · have hx : p = stop := by omega
        rw [hx] at hprime hdv
        rw [decide_eq_true hprime] at h2
        simp only [Bool.not_true, Bool.false_or] at h2
        cases hb : decide (stop ∣ target) with
        | true =>
            rw [hb] at h2
            simp only [Bool.not_true, Bool.false_or] at h2
            rw [hx]
            exact h2
        | false =>
            rw [hb] at h2
            simp only [Bool.not_false, Bool.true_or] at h2
            exact absurd (decide_eq_true hdv) (by rw [hb]; simp)

/-! ## The counterexample -/

example : 23 ^ 3 = 12167 := by decide
example : 2 ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by decide

/-- The only prime divisor of 12167 is 23. -/
theorem prime_divisor_of_12167 {p : Nat} (hprime : isPrime p = true) (hdv : p ∣ 12167) :
    p = 23 := by
  have hlt : p < 12168 := by
    have hle : p ≤ 12167 := Nat.le_of_dvd (by decide) hdv
    omega
  have h := checkAllP_spec
    (show checkAllP 12167 12168 (fun q => decide (q = 23)) = true from by
      native_decide) p hlt hprime hdv
  exact of_decide_eq_true h

theorem powerful_12167 : Powerful 12167 := by
  intro p hprime hdv
  rw [prime_divisor_of_12167 hprime hdv]
  decide

/-- The prime divisors of 12168 are exactly 2, 3 and 13. -/
theorem prime_divisor_of_12168 {p : Nat} (hprime : isPrime p = true) (hdv : p ∣ 12168) :
    p = 2 ∨ p = 3 ∨ p = 13 := by
  have hlt : p < 12169 := by
    have hle : p ≤ 12168 := Nat.le_of_dvd (by decide) hdv
    omega
  have h := checkAllP_spec
    (show checkAllP 12168 12169
        (fun q => decide (q = 2) || decide (q = 3) || decide (q = 13)) = true from by
      native_decide) p hlt hprime hdv
  cases hb2 : decide (p = 2) with
  | true => exact Or.inl (of_decide_eq_true hb2)
  | false =>
    cases hb3 : decide (p = 3) with
    | true => exact Or.inr (Or.inl (of_decide_eq_true hb3))
    | false =>
      rw [hb2, hb3] at h
      simp only [Bool.false_or] at h
      exact Or.inr (Or.inr (of_decide_eq_true h))

theorem powerful_12168 : Powerful 12168 := by
  intro p hprime hdv
  rcases prime_divisor_of_12168 hprime hdv with h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-! ## Neither 12167 nor 12168 is a square -/

/-- Squares are monotone in the base. -/
theorem sq_le_sq {r s : Nat} (h : r ≤ s) : r * r ≤ s * s := by
  have h1 : r * r ≤ s * r := Nat.mul_le_mul_right r h
  have h2 : s * r ≤ s * s := Nat.mul_le_mul_left s h
  omega

theorem not_square_12167 : ¬ IsSquare 12167 := by
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 111 with h | h
  · have hle : r * r ≤ 110 * 110 := sq_le_sq (by omega)
    rw [hr] at hle
    omega
  · have hle : 111 * 111 ≤ r * r := sq_le_sq (by omega)
    rw [hr] at hle
    omega

theorem not_square_12168 : ¬ IsSquare 12168 := by
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 111 with h | h
  · have hle : r * r ≤ 110 * 110 := sq_le_sq (by omega)
    rw [hr] at hle
    omega
  · have hle : 111 * 111 ≤ r * r := sq_le_sq (by omega)
    rw [hr] at hle
    omega

/-! ## Main theorem: the answer to JSP-000301 is "No" -/

/-- **JSP-000301.** There exist two consecutive powerful positive integers
neither of which is a perfect square: `12167 = 23^3` and
`12168 = 2^3 · 3^2 · 13^2`.  Hence the answer to the question
"If two consecutive positive integers are powerful, must at least one be a
perfect square?" is **no**. -/
theorem jsp_000301 :
    ∃ a b : Nat, a + 1 = b ∧ Powerful a ∧ Powerful b ∧ ¬ IsSquare a ∧ ¬ IsSquare b :=
  ⟨12167, 12168, rfl, powerful_12167, powerful_12168, not_square_12167, not_square_12168⟩
