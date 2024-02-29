/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Kudzo Ahegbebu, Stanislas Polu, David Renshaw, OpenAI GPT-f

! This file was ported from Lean 3 source module test and edited by Jiacheng Chen.
-/
import MiniF2F.Minif2fImport
import LeanCopilot

open LeanCopilot

set_option maxHeartbeats 0
set_option trace.aesop true
set_option trace.aesop.proof true
set_option trace.aesop.profile true


open Nat Real Rat BigOperators

theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
  rw [h₂, h₃] at h₁
  rw [h₁]
  norm_num

theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  replace h₂ : a + b = 27
  linarith
  have h₃ : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by ring
  rw [h₃, h₂, h₁]
  norm_num

theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  rw [← h₀, ← h₂]
  simp

theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  field_simp
  nlinarith

theorem mathd_numbertheory_299 : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5 := by
  norm_num

theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by
  norm_num

theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by
  rw [h₀, h₁]
  norm_num

theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  linarith

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have dvd_of_dvd_add_mul_left : ∀ a b n : ℕ, a ∣ b + a * n → a ∣ b :=
    by
    intro a b n
    refine' (Nat.dvd_add_left _).mp
    exact dvd_mul_right a n
  induction' n with k IH
  · decide
  · rw [_root_.pow_succ]
    apply dvd_of_dvd_add_mul_left 12 (4 * 4 ^ k.succ + 20) 5
    exact dvd_mul_of_dvd_right IH 4

theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  have h₁ : ↑x = (575 : ℝ); linarith
  assumption_mod_cast

theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  linarith

theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  nlinarith

theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  ring_nf

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  induction' h₀ with k h₀ IH
  · simp [factorial]
    simp [Nat.pow_succ]
  · have k_ge_one : 1 ≤ k := le_trans (by decide) h₀
    calc
      k.succ.factorial = k.succ * k.factorial := rfl
      _ < k.succ * k ^ (k - 1) := ((mul_lt_mul_left (Nat.succ_pos k)).mpr IH)
      _ ≤ k.succ * k.succ ^ (k - 1) :=
        (Nat.mul_le_mul_left _ <| Nat.pow_le_pow_of_le_left (Nat.le_succ k) (k - 1))
      _ = k.succ ^ (k - 1 + 1) := by rw [← _root_.pow_succ k.succ (k - 1)]
      _ = k.succ ^ k := by rw [Nat.sub_add_cancel k_ge_one]


theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  refine' not_forall_of_exists_not _
  use 2
  refine' not_forall_of_exists_not _
  use 4
  refine' not_iff.mpr _
  refine' Iff.symm _
  apply iff_not_comm.mpr
  refine' iff_of_true _ _
  · use 1
    use 2
    norm_num
  · norm_num
    intro k
    refine' ne_comm.mp _
    apply ne_iff_lt_or_gt.mpr
    by_cases k ≤ 2
    · left
      linarith
    · right
      linarith

theorem mathd_numbertheory_345 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by
  norm_num

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  suffices : 0 ≤ a ^ 2 - 2 * a + 1; nlinarith
  suffices : 0 ≤ (a - 1) ^ 2; nlinarith
  nlinarith

theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by
  rw [h₀]
  linarith

theorem mathd_algebra_188 (σ : Equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 := by
  simp [h]

theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  rw [h₀, h₁]
  norm_num

theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
  norm_num

theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  constructor <;> linarith

theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  linarith [h₀ 1, h₀ 2, h₀ 3, h₀ 4, h₀ 5, h₀ 6, h₀ 7]

theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
  norm_num

theorem mathd_numbertheory_342 : 54 % 6 = 0 := by
  norm_num

theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
  rw [abs_of_nonpos]
  norm_num
  norm_num

theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
  linarith

theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  linarith

theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4)) ^ (6 * x + 2) = 121 / 25 := by
  revert x h
  norm_num

theorem mathd_algebra_388 (x y z : ℝ) (h₀ : 3 * x + 4 * y - 12 * z = 10)
    (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by
  linarith

theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  revert y h₀ h₁
  intro x hx
  rw [Real.sqrt_eq_iff_sq_eq hx]
  swap
  norm_num
  intro h
  nlinarith

theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
  linarith

theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h₃ := congr (congr_arg Add.add h₀) h₁
  linarith

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  nlinarith [sq_nonneg (a - b)]

theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by
  linarith

theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  have five_to_thirty_is_one : (5 ^ 30 : ZMod 7) = 1 :=
    by
    have five_to_the_six_is_one : (5 ^ 6 : ZMod 7) = 1 := by decide
    have break_power : (5 ^ 30 : ZMod 7) = (5 ^ 6) ^ 5 := by norm_num
    rw [break_power]
    rw [five_to_the_six_is_one]
    norm_num
  change 5 ^ 30 ≡ 1 [MOD 7]
  rw [← ZMod.eq_iff_modEq_nat]
  exact_mod_cast five_to_thirty_is_one

theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  field_simp  at h₁
  linarith

theorem mathd_numbertheory_551 : 1529 % 6 = 5 := by
  norm_num

theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by
  norm_num

theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by
  nlinarith

theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  rw [h₀] at h₁
  linarith

theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  field_simp  at h₀
  linarith

theorem mathd_numbertheory_254 : (239 + 174 + 83) % 10 = 6 := by
  norm_num

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  constructor <;> linarith

theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  rw [h₀, h₁]
  norm_num

theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  linarith

theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  rw [h₀] at h₂
  simp at h₂
  rw [h₀]
  linarith

theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by
  norm_num

theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by
  rw [h₀]
  linarith

theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  rw [h₀, h₀]
  norm_num
  linarith
  rw [h₀]
  norm_num
  linarith

theorem mathd_numbertheory_66 : 194 % 11 = 7 := by
  rfl

theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  norm_num

theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
  linarith

theorem mathd_algebra_314 (n : ℕ) (h₀ : n = 11) : (1 / 4) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 := by
  rw [h₀]
  norm_num

theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  norm_num

theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ (x) (_ : x ≠ 0), ∀ (y) (_ : y ≠ 0), s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by
  norm_num [h₀]


theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  linarith

theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  linarith

theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  field_simp
  ring_nf

theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have ha : a = -4; linarith
  have hb : b = 2; linarith
  have hc : c = 7; linarith
  rw [ha, hb, hc]
  norm_num
