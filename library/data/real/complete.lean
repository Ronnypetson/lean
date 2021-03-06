/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

At this point, we no longer proceed constructively: this file makes heavy use of decidability,
excluded middle, and Hilbert choice. Two sets of definitions of Cauchy sequences, convergence,
etc are available in the libray, one with rates and one without. The definitions here, with rates,
 are amenable to be used constructively if and when that development takes place. The second set of
definitions available in /library/theories/analysis/metric_space.lean are the usual classical ones.

Here, we show that ℝ is complete. The proofs of Cauchy completeness and the supremum property
are independent of each other.
-/

import data.real.basic data.real.order data.real.division data.rat data.nat data.pnat
open rat
local postfix ⁻¹ := pnat.inv
open eq.ops pnat classical

namespace rat_seq

theorem rat_approx {s : seq} (H : regular s) :
        ∀ n : ℕ+, ∃ q : ℚ, ∃ N : ℕ+, ∀ m : ℕ+, m ≥ N → abs (s m - q) ≤ n⁻¹ :=
  begin
    intro n,
    existsi (s (2 * n)),
    existsi 2 * n,
    intro m Hm,
    apply le.trans,
    apply H,
    rewrite -(pnat.add_halves n),
    apply add_le_add_right,
    apply inv_ge_of_le Hm
  end

theorem rat_approx_seq {s : seq} (H : regular s) :
        ∀ n : ℕ+, ∃ q : ℚ, s_le (s_abs (sadd s (sneg (const q)))) (const n⁻¹) :=
  begin
    intro m,
    rewrite ↑s_le,
    cases rat_approx H m with [q, Hq],
    cases Hq with [N, HN],
    existsi q,
    apply nonneg_of_bdd_within,
    repeat (apply reg_add_reg | apply reg_neg_reg | apply abs_reg_of_reg | apply const_reg
             | assumption),
    intro n,
    existsi N,
    intro p Hp,
    rewrite ↑[sadd, sneg, s_abs, const],
    apply le.trans,
    rotate 1,
    rewrite -sub_eq_add_neg,
    apply sub_le_sub_left,
    apply HN,
    apply le.trans,
    apply Hp,
    rewrite -*pnat.mul_assoc,
    apply pnat.mul_le_mul_left,
    rewrite [sub_self, -neg_zero],
    apply neg_le_neg,
    apply rat.le_of_lt,
    apply pnat.inv_pos
  end

theorem r_rat_approx (s : reg_seq) :
        ∀ n : ℕ+, ∃ q : ℚ, r_le (r_abs (radd s (rneg (r_const q)))) (r_const n⁻¹) :=
  rat_approx_seq (reg_seq.is_reg s)

theorem const_bound {s : seq} (Hs : regular s) (n : ℕ+) :
        s_le (s_abs (sadd s (sneg (const (s n))))) (const n⁻¹) :=
  begin
    rewrite ↑[s_le, nonneg, s_abs, sadd, sneg, const],
    intro m,
    rewrite -sub_eq_add_neg,
    apply iff.mp !le_add_iff_neg_le_sub_left,
    apply le.trans,
    apply Hs,
    apply add_le_add_right,
    rewrite -*pnat.mul_assoc,
    apply inv_ge_of_le,
    apply pnat.mul_le_mul_left
  end

theorem abs_const (a : ℚ) : const (abs a) ≡ s_abs (const a) :=
  by apply equiv.refl

theorem r_abs_const (a : ℚ) : requiv (r_const (abs a) ) (r_abs (r_const a)) := abs_const a

theorem equiv_abs_of_ge_zero {s : seq} (Hs : regular s) (Hz : s_le zero s) : s_abs s ≡ s :=
  begin
    apply eq_of_bdd,
    apply abs_reg_of_reg Hs,
    apply Hs,
    intro j,
    rewrite ↑s_abs,
    let Hz' := s_nonneg_of_ge_zero Hs Hz,
    existsi 2 * j,
    intro n Hn,
    cases em (s n ≥ 0) with [Hpos, Hneg],
    rewrite [abs_of_nonneg Hpos, sub_self, abs_zero],
    apply rat.le_of_lt,
    apply pnat.inv_pos,
    let Hneg' := lt_of_not_ge Hneg,
    have Hsn : -s n - s n > 0, from add_pos (neg_pos_of_neg Hneg') (neg_pos_of_neg Hneg'),
    rewrite [abs_of_neg Hneg', abs_of_pos Hsn],
    apply le.trans,
    apply add_le_add,
    repeat (apply neg_le_neg; apply Hz'),
    rewrite neg_neg,
    apply le.trans,
    apply add_le_add,
    repeat (apply inv_ge_of_le; apply Hn),
    krewrite pnat.add_halves,
  end

theorem equiv_neg_abs_of_le_zero {s : seq} (Hs : regular s) (Hz : s_le s zero) : s_abs s ≡ sneg s :=
  begin
    apply eq_of_bdd,
    apply abs_reg_of_reg Hs,
    apply reg_neg_reg Hs,
    intro j,
    rewrite [↑s_abs, ↑s_le at Hz],
    have Hz' : nonneg (sneg s), begin
      apply nonneg_of_nonneg_equiv,
      rotate 3,
      apply Hz,
      rotate 2,
      apply s_zero_add,
      repeat (apply Hs | apply zero_is_reg | apply reg_neg_reg | apply reg_add_reg)
    end,
    existsi 2 * j,
    intro n Hn,
    cases em (s n ≥ 0) with [Hpos, Hneg],
    have Hsn : s n + s n ≥ 0, from add_nonneg Hpos Hpos,
    rewrite [abs_of_nonneg Hpos, ↑sneg, sub_neg_eq_add, abs_of_nonneg Hsn],
    rewrite [↑nonneg at Hz', ↑sneg at Hz'],
    apply le.trans,
    apply add_le_add,
    repeat apply (le_of_neg_le_neg !Hz'),
    apply le.trans,
    apply add_le_add,
    repeat (apply inv_ge_of_le; apply Hn),
    krewrite pnat.add_halves,
    let Hneg' := lt_of_not_ge Hneg,
    rewrite [abs_of_neg Hneg', ↑sneg, sub_neg_eq_add, neg_add_eq_sub, sub_self,
                abs_zero],
    apply rat.le_of_lt,
    apply pnat.inv_pos
  end

theorem r_equiv_abs_of_ge_zero {s : reg_seq} (Hz : r_le r_zero s) : requiv (r_abs s) s :=
  equiv_abs_of_ge_zero (reg_seq.is_reg s) Hz

theorem r_equiv_neg_abs_of_le_zero {s : reg_seq} (Hz : r_le s r_zero) : requiv (r_abs s) (-s) :=
  equiv_neg_abs_of_le_zero (reg_seq.is_reg s) Hz

end rat_seq

namespace real
open [class] rat_seq

private theorem rewrite_helper9 (a b c : ℝ) : b - c = (b - a) - (c - a) :=
  by rewrite [-sub_add_eq_sub_sub_swap, sub_add_cancel]

private theorem rewrite_helper10 (a b c d : ℝ) : c - d = (c - a) + (a - b) + (b - d) :=
  by rewrite [*add_sub, *sub_add_cancel]

noncomputable definition rep (x : ℝ) : rat_seq.reg_seq := some (quot.exists_rep x)

definition re_abs (x : ℝ) : ℝ :=
  quot.lift_on x (λ a, quot.mk (rat_seq.r_abs a))
    (take a b Hab, quot.sound (rat_seq.r_abs_well_defined Hab))

theorem r_abs_nonneg {x : ℝ} : zero ≤ x → re_abs x = x :=
  quot.induction_on x (λ a Ha, quot.sound  (rat_seq.r_equiv_abs_of_ge_zero Ha))

theorem r_abs_nonpos {x : ℝ} : x ≤ zero → re_abs x = -x :=
  quot.induction_on x (λ a Ha, quot.sound (rat_seq.r_equiv_neg_abs_of_le_zero Ha))

private theorem abs_const' (a : ℚ) : of_rat (abs a) = re_abs (of_rat a) :=
  quot.sound (rat_seq.r_abs_const a)

private theorem re_abs_is_abs : re_abs = abs := funext
  (begin
    intro x,
    apply eq.symm,
    cases em (zero ≤ x) with [Hor1, Hor2],
    rewrite [abs_of_nonneg Hor1, r_abs_nonneg Hor1],
    have Hor2' : x ≤ zero, from le_of_lt (lt_of_not_ge Hor2),
    rewrite [abs_of_neg (lt_of_not_ge Hor2), r_abs_nonpos Hor2']
  end)

theorem abs_const (a : ℚ) : of_rat (abs a) = abs (of_rat a) :=
  by  rewrite -re_abs_is_abs

private theorem rat_approx' (x : ℝ) : ∀ n : ℕ+, ∃ q : ℚ, re_abs (x - of_rat q) ≤ of_rat n⁻¹ :=
  quot.induction_on x (λ s n, rat_seq.r_rat_approx s n)

theorem rat_approx (x : ℝ) : ∀ n : ℕ+, ∃ q : ℚ, abs (x - of_rat q) ≤ of_rat n⁻¹ :=
  by rewrite -re_abs_is_abs; apply rat_approx'

noncomputable definition approx (x : ℝ) (n : ℕ+) := some (rat_approx x n)

theorem approx_spec (x : ℝ) (n : ℕ+) : abs (x - (of_rat (approx x n))) ≤ of_rat n⁻¹ :=
  some_spec (rat_approx x n)

theorem approx_spec' (x : ℝ) (n : ℕ+) : abs ((of_rat (approx x n)) - x) ≤ of_rat n⁻¹ :=
  by rewrite abs_sub; apply approx_spec

theorem ex_rat_pos_lower_bound_of_pos {x : ℝ} (H : x > 0) : ∃ q : ℚ, q > 0 ∧ of_rat q ≤ x :=
  if Hgeo : x ≥ 1 then
    exists.intro 1 (and.intro zero_lt_one Hgeo)
  else
    have Hdp : 1 / x > 0, from one_div_pos_of_pos H,
    begin
      cases rat_approx (1 / x) 2 with q Hq,
      have Hqp : q > 0, begin
        apply lt_of_not_ge,
        intro Hq2,
        note Hx' := one_div_lt_one_div_of_lt H (lt_of_not_ge Hgeo),
        rewrite div_one at Hx',
        have Horqn : of_rat q ≤ 0, begin
          krewrite -of_rat_zero,
          apply of_rat_le_of_rat_of_le Hq2
        end,
        have Hgt1 : 1 / x - of_rat q > 1, from calc
          1 / x - of_rat q = 1 / x + -of_rat q : sub_eq_add_neg
                       ... ≥ 1 / x             : le_add_of_nonneg_right (neg_nonneg_of_nonpos Horqn)
                       ... > 1                 : Hx',
        have Hpos : 1 / x - of_rat q > 0, from gt.trans Hgt1 zero_lt_one,
        rewrite [abs_of_pos Hpos at Hq],
        apply not_le_of_gt Hgt1,
        apply le.trans,
        apply Hq,
        krewrite -of_rat_one,
        apply of_rat_le_of_rat_of_le,
        apply inv_le_one
      end,
      existsi 1 / (2⁻¹ + q),
      split,
      apply div_pos_of_pos_of_pos,
      exact zero_lt_one,
      apply add_pos,
      apply pnat.inv_pos,
      exact Hqp,
      note Hle2 := sub_le_of_abs_sub_le_right Hq,
      note Hle3 := le_add_of_sub_left_le Hle2,
      note Hle4 := one_div_le_of_one_div_le_of_pos H Hle3,
      rewrite [of_rat_divide, of_rat_add],
      exact Hle4
    end

theorem ex_rat_neg_upper_bound_of_neg {x : ℝ} (H : x < 0) : ∃ q : ℚ, q < 0 ∧ x ≤ of_rat q :=
  have H' : -x > 0, from neg_pos_of_neg H,
  obtain q [Hq1 Hq2], from ex_rat_pos_lower_bound_of_pos H',
  exists.intro (-q) (and.intro
    (neg_neg_of_pos Hq1)
    (le_neg_of_le_neg Hq2))

notation `r_seq` := ℕ+ → ℝ

noncomputable definition converges_to_with_rate (X : r_seq) (a : ℝ) (N : ℕ+ → ℕ+) :=
  ∀ k : ℕ+, ∀ n : ℕ+, n ≥ N k → abs (X n - a) ≤ of_rat k⁻¹

noncomputable definition cauchy_with_rate (X : r_seq) (M : ℕ+ → ℕ+) :=
  ∀ k : ℕ+, ∀ m n : ℕ+, m ≥ M k → n ≥ M k → abs (X m - X n) ≤ of_rat k⁻¹

theorem cauchy_with_rate_of_converges_to_with_rate {X : r_seq} {a : ℝ} {N : ℕ+ → ℕ+}
    (Hc : converges_to_with_rate X a N) :
        cauchy_with_rate X (λ k, N (2 * k)) :=
  begin
    intro k m n Hm Hn,
    rewrite (rewrite_helper9 a),
    apply le.trans,
    apply abs_add_le_abs_add_abs,
    apply le.trans,
    apply add_le_add,
    apply Hc,
    apply Hm,
    krewrite abs_neg,
    apply Hc,
    apply Hn,
    xrewrite -of_rat_add,
    apply of_rat_le_of_rat_of_le,
    krewrite pnat.add_halves,
  end

private definition Nb (M : ℕ+ → ℕ+) := λ k, max (3 * k) (M (2 * k))

private theorem Nb_spec_right (M : ℕ+ → ℕ+) (k : ℕ+) : M (2 * k) ≤ Nb M k := !le_max_right

private theorem Nb_spec_left (M : ℕ+ → ℕ+) (k : ℕ+) : 3 * k ≤ Nb M k := !le_max_left

section lim_seq
parameter {X : r_seq}
parameter {M : ℕ+ → ℕ+}
hypothesis Hc : cauchy_with_rate X M
include Hc

noncomputable definition lim_seq : ℕ+ → ℚ :=
  λ k, approx (X (Nb M k)) (2 * k)

private theorem lim_seq_reg_helper {m n : ℕ+} (Hmn : M (2 * n) ≤M (2 * m)) :
           abs (of_rat (lim_seq m) - X (Nb M m)) + abs (X (Nb M m) - X (Nb M n)) + abs
            (X (Nb M n) - of_rat (lim_seq n)) ≤ of_rat (m⁻¹ + n⁻¹) :=
  begin
    apply le.trans,
    apply add_le_add_three,
    apply approx_spec',
    rotate 1,
    apply approx_spec,
    rotate 1,
    apply Hc,
    rotate 1,
    apply Nb_spec_right,
    rotate 1,
    apply le.trans,
    apply Hmn,
    apply Nb_spec_right,
    krewrite [-+of_rat_add],
    change of_rat ((2 * m)⁻¹ + (2 * n)⁻¹ + (2 * n)⁻¹) ≤ of_rat (m⁻¹ + n⁻¹),
    rewrite [add.assoc],
    krewrite pnat.add_halves,
    apply of_rat_le_of_rat_of_le,
    apply add_le_add_right,
    apply inv_ge_of_le,
    apply pnat.mul_le_mul_left
  end

theorem lim_seq_reg : rat_seq.regular lim_seq :=
  begin
    rewrite ↑rat_seq.regular,
    intro m n,
    apply le_of_of_rat_le_of_rat,
    rewrite [abs_const, of_rat_sub, (rewrite_helper10 (X (Nb M m)) (X (Nb M n)))],
    apply le.trans,
    apply abs_add_three,
    cases em (M (2 * m) ≥ M (2 * n)) with [Hor1, Hor2],
    apply lim_seq_reg_helper Hor1,
    let Hor2' := le_of_lt (lt_of_not_ge Hor2),
    krewrite [abs_sub (X (Nb M n)), abs_sub (X (Nb M m)), abs_sub,
             rat.add_comm, add_comm_three],
    apply lim_seq_reg_helper Hor2'
  end

theorem lim_seq_spec (k : ℕ+) :
        rat_seq.s_le (rat_seq.s_abs (rat_seq.sadd lim_seq
            (rat_seq.sneg (rat_seq.const (lim_seq k))))) (rat_seq.const k⁻¹) :=
  by apply rat_seq.const_bound; apply lim_seq_reg

private noncomputable definition r_lim_seq : rat_seq.reg_seq :=
  rat_seq.reg_seq.mk lim_seq lim_seq_reg

private theorem r_lim_seq_spec (k : ℕ+) : rat_seq.r_le
        (rat_seq.r_abs ((rat_seq.radd r_lim_seq (rat_seq.rneg
            (rat_seq.r_const ((rat_seq.reg_seq.sq r_lim_seq) k))))))
        (rat_seq.r_const k⁻¹) :=
  lim_seq_spec k

noncomputable definition lim : ℝ :=
  quot.mk r_lim_seq

theorem re_lim_spec (k : ℕ+) : re_abs (lim - (of_rat (lim_seq k))) ≤ of_rat k⁻¹ :=
  r_lim_seq_spec k

theorem lim_spec' (k : ℕ+) : abs (lim - (of_rat (lim_seq k))) ≤ of_rat k⁻¹ :=
  by rewrite -re_abs_is_abs; apply re_lim_spec

theorem lim_spec (k : ℕ+) :
        abs ((of_rat (lim_seq k)) - lim) ≤ of_rat k⁻¹ :=
  by rewrite abs_sub; apply lim_spec'

theorem converges_to_with_rate_of_cauchy_with_rate : converges_to_with_rate X lim (Nb M) :=
  begin
    intro k n Hn,
    rewrite (rewrite_helper10 (X (Nb M n)) (of_rat (lim_seq n))),
    apply le.trans,
    apply abs_add_three,
    apply le.trans,
    apply add_le_add_three,
    apply Hc,
    apply le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_right,
    have HMk : M (2 * k) ≤ Nb M n, begin
      apply le.trans,
      apply Nb_spec_right,
      apply le.trans,
      apply Hn,
      apply le.trans,
      apply pnat.mul_le_mul_left 3,
      apply Nb_spec_left
    end,
    apply HMk,
    rewrite ↑lim_seq,
    apply approx_spec,
    apply lim_spec,
    krewrite [-+of_rat_add],
    change of_rat ((2 * k)⁻¹ + (2 * n)⁻¹ + n⁻¹) ≤ of_rat k⁻¹,
    apply of_rat_le_of_rat_of_le,
    apply le.trans,
    apply add_le_add_three,
    apply rat.le_refl,
    apply inv_ge_of_le,
    apply pnat_mul_le_mul_left',
    apply le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_left,
    apply inv_ge_of_le,
    apply le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_left,
    rewrite -*pnat.mul_assoc,
    krewrite pnat.p_add_fractions,
  end

end lim_seq
-------------------------------------------
-- int embedding theorems
-- archimedean properties, integer floor and ceiling
section ints

open int

theorem archimedean_upper (x : ℝ) : ∃ z : ℤ, x ≤ of_int z :=
  begin
    apply quot.induction_on x,
    intro s,
    cases rat_seq.bdd_of_regular (rat_seq.reg_seq.is_reg s) with [b, Hb],
    existsi ubound b,
    have H : rat_seq.s_le (rat_seq.reg_seq.sq s) (rat_seq.const (rat.of_nat (ubound b))), begin
      apply rat_seq.s_le_of_le_pointwise (rat_seq.reg_seq.is_reg s),
      apply rat_seq.const_reg,
      intro n,
      apply le.trans,
      apply Hb,
      apply ubound_ge
    end,
    apply H
  end

theorem archimedean_upper_strict (x : ℝ) : ∃ z : ℤ, x < of_int z :=
  begin
    cases archimedean_upper x with [z, Hz],
    existsi z + 1,
    apply lt_of_le_of_lt,
    apply Hz,
    apply of_int_lt_of_int_of_lt,
    apply lt_add_of_pos_right,
    apply dec_trivial
  end

theorem archimedean_lower (x : ℝ) : ∃ z : ℤ, x ≥ of_int z :=
  begin
    cases archimedean_upper (-x) with [z, Hz],
    existsi -z,
    rewrite [of_int_neg],
    apply iff.mp !neg_le_iff_neg_le Hz
  end

theorem archimedean_lower_strict (x : ℝ) : ∃ z : ℤ, x > of_int z :=
  begin
    cases archimedean_upper_strict (-x) with [z, Hz],
    existsi -z,
    rewrite [of_int_neg],
    apply iff.mp !neg_lt_iff_neg_lt Hz
  end

private definition ex_floor (x : ℝ) :=
  (@exists_greatest_of_bdd (λ z, x ≥ of_int z) _
    (begin
      existsi some (archimedean_upper_strict x),
      let Har := some_spec (archimedean_upper_strict x),
      intros z Hz,
      apply not_le_of_gt,
      apply lt_of_lt_of_le,
      apply Har,
      have H : of_int (some (archimedean_upper_strict x)) ≤ of_int z, begin
        apply of_int_le_of_int_of_le,
        apply Hz
      end,
      exact H
    end)
    (by existsi some (archimedean_lower x); apply some_spec (archimedean_lower x)))

noncomputable definition floor (x : ℝ) : ℤ :=
  some (ex_floor x)

noncomputable definition ceil (x : ℝ) : ℤ := - floor (-x)

theorem floor_le (x : ℝ) : floor x ≤ x :=
  and.left (some_spec (ex_floor x))

theorem lt_of_floor_lt {x : ℝ} {z : ℤ} (Hz : floor x < z) : x < z :=
  begin
    apply lt_of_not_ge,
    cases some_spec (ex_floor x),
    apply a_1 _ Hz
  end

theorem le_ceil (x : ℝ) : x ≤ ceil x :=
  begin
    rewrite [↑ceil, of_int_neg],
    apply iff.mp !le_neg_iff_le_neg,
    apply floor_le
  end

theorem lt_of_lt_ceil {x : ℝ} {z : ℤ} (Hz : z < ceil x) : z < x :=
  begin
    rewrite ↑ceil at Hz,
    note Hz' := lt_of_floor_lt (iff.mp !lt_neg_iff_lt_neg Hz),
    rewrite [of_int_neg at Hz'],
    apply lt_of_neg_lt_neg Hz'
  end

theorem floor_succ (x : ℝ) : floor (x + 1) = floor x + 1 :=
  begin
    apply by_contradiction,
    intro H,
    cases lt_or_gt_of_ne H with [Hgt, Hlt],
    note Hl := lt_of_floor_lt Hgt,
    rewrite [of_int_add at Hl],
    apply not_le_of_gt (lt_of_add_lt_add_right Hl) !floor_le,
    note Hl := lt_of_floor_lt (iff.mp !add_lt_iff_lt_sub_right Hlt),
    rewrite [of_int_sub at Hl],
    apply not_le_of_gt (iff.mpr !add_lt_iff_lt_sub_right Hl) !floor_le
  end

theorem floor_sub_one_lt_floor (x : ℝ) : floor (x - 1) < floor x :=
  begin

    apply @lt_of_add_lt_add_right ℤ _ _ 1,
    rewrite [-floor_succ (x - 1), sub_add_cancel],
    apply lt_add_of_pos_right dec_trivial
  end

theorem ceil_lt_ceil_succ (x : ℝ) : ceil x < ceil (x + 1) :=
  begin
    rewrite [↑ceil, neg_add],
    apply neg_lt_neg,
    apply floor_sub_one_lt_floor
  end
open nat

theorem archimedean_small {ε : ℝ} (H : ε > 0) : ∃ (n : ℕ), 1 / succ n < ε :=
let n := int.nat_abs (ceil (2 / ε)) in
have int.of_nat n ≥ ceil (2 / ε),
  by rewrite of_nat_nat_abs; apply le_abs_self,
have int.of_nat (succ n) ≥ ceil (2 / ε),
  begin apply le.trans, exact this, apply int.of_nat_le_of_nat_of_le, apply le_succ end,
have H₁ : int.succ n ≥ ceil (2 / ε), from of_int_le_of_int_of_le this,
have H₂ : succ n ≥ 2 / ε, from !le.trans !le_ceil H₁,
have H₃ : 2 / ε > 0, from div_pos_of_pos_of_pos two_pos H,
have 1 / succ n < ε, from calc
  1 / succ n ≤ 1 / (2 / ε) : one_div_le_one_div_of_le H₃ H₂
    ... = ε / 2       : one_div_div
    ... < ε           : div_two_lt_of_pos H,
exists.intro n this

end ints
--------------------------------------------------
-- supremum property
-- this development roughly follows the proof of completeness done in Isabelle.
-- It does not depend on the previous proof of Cauchy completeness. Much of the same
-- machinery can be used to show that Cauchy completeness implies the supremum property.

section supremum
open prod nat
local postfix `~` := nat_of_pnat

-- The top part of this section could be refactored. What is the appropriate place to define
-- bounds, supremum, etc? In algebra/ordered_field? They potentially apply to more than just ℝ.
parameter X : ℝ → Prop

definition ub (x : ℝ) := ∀ y : ℝ, X y → y ≤ x
definition is_sup (x : ℝ) := ub x ∧ ∀ y : ℝ, ub y → x ≤ y

definition lb (x : ℝ) := ∀ y : ℝ, X y → x ≤ y
definition is_inf (x : ℝ) := lb x ∧ ∀ y : ℝ, lb y → y ≤ x

parameter elt : ℝ
hypothesis inh :  X elt
parameter bound : ℝ
hypothesis bdd : ub bound

include inh bdd

private definition avg (a b : ℚ) := a / 2 + b / 2

private noncomputable definition bisect (ab : ℚ × ℚ) :=
  if ub (avg (pr1 ab) (pr2 ab)) then
    (pr1 ab, (avg (pr1 ab) (pr2 ab)))
  else
    (avg (pr1 ab) (pr2 ab), pr2 ab)

private noncomputable definition under : ℚ := rat.of_int (floor (elt - 1))

private theorem under_spec1 : of_rat under < elt :=
  have H : of_rat under < of_int (floor elt), begin
    apply of_int_lt_of_int_of_lt,
    apply floor_sub_one_lt_floor
  end,
  lt_of_lt_of_le H !floor_le

private theorem under_spec : ¬ ub under :=
  begin
    rewrite ↑ub,
    apply not_forall_of_exists_not,
    existsi elt,
    apply iff.mpr !not_implies_iff_and_not,
    apply and.intro,
    apply inh,
    apply not_le_of_gt under_spec1
  end

private noncomputable definition over : ℚ := rat.of_int (ceil (bound + 1)) -- b

private theorem over_spec1 : bound < of_rat over :=
  have H : of_int (ceil bound) < of_rat over, begin
    apply of_int_lt_of_int_of_lt,
    apply ceil_lt_ceil_succ
  end,
  lt_of_le_of_lt !le_ceil H

private theorem over_spec : ub over :=
  begin
    rewrite ↑ub,
    intro y Hy,
    apply le_of_lt,
    apply lt_of_le_of_lt,
    apply bdd,
    apply Hy,
    apply over_spec1
  end

private noncomputable definition under_seq := λ n : ℕ, pr1 (iterate bisect n (under, over)) -- A

private noncomputable definition over_seq := λ n : ℕ, pr2 (iterate bisect n (under, over)) -- B

private noncomputable definition avg_seq := λ n : ℕ, avg (over_seq n) (under_seq n) -- C

private theorem avg_symm (n : ℕ) : avg_seq n = avg (under_seq n) (over_seq n) :=
  by rewrite [↑avg_seq, ↑avg, add.comm]

private theorem over_0 : over_seq 0 = over := rfl

private theorem under_0 : under_seq 0 = under := rfl

private theorem succ_helper (n : ℕ) :
        avg (pr1 (iterate bisect n (under, over))) (pr2 (iterate bisect n (under, over))) = avg_seq n :=
   by rewrite avg_symm

private theorem under_succ (n : ℕ) : under_seq (succ n) =
        (if ub (avg_seq n) then under_seq n else avg_seq n) :=
  begin
    cases em (ub (avg_seq n)) with [Hub, Hub],
    rewrite [if_pos Hub],
    have H :  pr1 (bisect (iterate bisect n (under, over))) = under_seq n, by
      rewrite [↑under_seq, ↑bisect at {2}, -succ_helper at Hub, if_pos Hub],
    apply H,
    rewrite [if_neg Hub],
    have H : pr1 (bisect (iterate bisect n (under, over))) = avg_seq n, by
      rewrite [↑bisect at {2}, -succ_helper at Hub, if_neg Hub, avg_symm],
    apply H
  end

private theorem over_succ (n : ℕ) : over_seq (succ n) =
        (if ub (avg_seq n) then avg_seq n else over_seq n) :=
  begin
    cases em (ub (avg_seq n)) with [Hub, Hub],
    rewrite [if_pos Hub],
    have H : pr2 (bisect (iterate bisect n (under, over))) = avg_seq n, by
      rewrite [↑bisect at {2}, -succ_helper at Hub, if_pos Hub, avg_symm],
    apply H,
    rewrite [if_neg Hub],
    have H : pr2 (bisect (iterate bisect n (under, over))) = over_seq n, by
      rewrite [↑over_seq, ↑bisect at {2}, -succ_helper at Hub, if_neg Hub],
    apply H
  end

private theorem nat.zero_eq_0 : (zero : ℕ) = 0 := rfl

private theorem width (n : ℕ) : over_seq n - under_seq n = (over - under) / ((2^n) : ℚ) :=
  nat.induction_on n
    (by xrewrite [nat.zero_eq_0, over_0, under_0, pow_zero, div_one])
    (begin
      intro a Ha,
      rewrite [over_succ, under_succ],
      let Hou := calc
        (over_seq a) / 2 - (under_seq a) / 2 = ((over - under) / 2^a) / 2 :
                                               by rewrite [div_sub_div_same, Ha]
        ... = (over - under) / ((2^a) * 2) : by rewrite div_div_eq_div_mul
        ... = (over - under) / 2^(a + 1) : by rewrite pow_add,
      cases em (ub (avg_seq a)),
      rewrite [*if_pos a_1, -add_one, -Hou, ↑avg_seq, ↑avg, sub_eq_add_neg, add.assoc, -sub_eq_add_neg, div_two_sub_self],
      rewrite [*if_neg a_1, -add_one, -Hou, ↑avg_seq, ↑avg, sub_add_eq_sub_sub,
              sub_self_div_two]
    end)

private theorem width_narrows : ∃ n : ℕ, over_seq n - under_seq n ≤ 1 :=
  begin
    cases binary_bound (over - under) with [a, Ha],
    existsi a,
    rewrite (width a),
    apply div_le_of_le_mul,
    apply pow_pos dec_trivial,
    rewrite rat.mul_one,
    apply Ha
  end

private noncomputable definition over' := over_seq (some width_narrows)

private noncomputable definition under' := under_seq (some width_narrows)

private noncomputable definition over_seq' := λ n, over_seq (n + some width_narrows)

private noncomputable definition under_seq' := λ n, under_seq (n + some width_narrows)

private theorem over_seq'0 : over_seq' 0 = over' :=
  by rewrite [↑over_seq', nat.zero_add]

private theorem under_seq'0 : under_seq' 0 = under' :=
  by rewrite [↑under_seq', nat.zero_add]

private theorem under_over' : over' - under' ≤ 1 := some_spec width_narrows

private theorem width' (n : ℕ) : over_seq' n - under_seq' n ≤ 1 / 2^n :=
  nat.induction_on n
    (begin
      xrewrite [nat.zero_eq_0, over_seq'0, under_seq'0, pow_zero, div_one],
      apply under_over'
    end)
    (begin
      intros a Ha,
      rewrite [↑over_seq' at *, ↑under_seq' at *, *succ_add at *, width at *,
              -add_one, -(add_one a), pow_add, pow_add _ a 1, *pow_one],
      apply div_mul_le_div_mul_of_div_le_div_pos' Ha dec_trivial
    end)

private theorem PA (n : ℕ) : ¬ ub (under_seq n) :=
  nat.induction_on n
    (by rewrite under_0; apply under_spec)
    (begin
      intro a Ha,
      rewrite under_succ,
      cases em (ub (avg_seq a)),
      rewrite (if_pos a_1),
      assumption,
      rewrite (if_neg a_1),
      assumption
    end)

private theorem PB (n : ℕ) : ub (over_seq n) :=
  nat.induction_on n
    (by rewrite over_0; apply over_spec)
    (begin
      intro a Ha,
      rewrite over_succ,
      cases em (ub (avg_seq a)),
      rewrite (if_pos a_1),
      assumption,
      rewrite (if_neg a_1),
      assumption
    end)

private theorem under_lt_over : under < over :=
  begin
    cases exists_not_of_not_forall under_spec with [x, Hx],
    cases and_not_of_not_implies Hx with [HXx, Hxu],
    apply lt_of_of_rat_lt_of_rat,
    apply lt_of_lt_of_le,
    apply lt_of_not_ge Hxu,
    apply over_spec _ HXx
  end

private theorem under_seq_lt_over_seq : ∀ m n : ℕ, under_seq m < over_seq n :=
  begin
    intros,
    cases exists_not_of_not_forall (PA m) with [x, Hx],
    cases iff.mp !not_implies_iff_and_not Hx with [HXx, Hxu],
    apply lt_of_of_rat_lt_of_rat,
    apply lt_of_lt_of_le,
    apply lt_of_not_ge Hxu,
    apply PB,
    apply HXx
  end

private theorem under_seq_lt_over_seq_single : ∀ n : ℕ, under_seq n < over_seq n :=
  by intros; apply under_seq_lt_over_seq

private theorem under_seq'_lt_over_seq' : ∀ m n : ℕ, under_seq' m < over_seq' n :=
  by intros; apply under_seq_lt_over_seq

private theorem under_seq'_lt_over_seq'_single : ∀ n : ℕ, under_seq' n < over_seq' n :=
  by intros; apply under_seq_lt_over_seq

private theorem under_seq_mono_helper (i k : ℕ) : under_seq i ≤ under_seq (i + k) :=
  (nat.induction_on k
    (by rewrite nat.add_zero; apply rat.le_refl)
    (begin
      intros a Ha,
      rewrite [add_succ, under_succ],
      cases em (ub (avg_seq (i + a))) with [Havg, Havg],
      rewrite (if_pos Havg),
      apply Ha,
      rewrite [if_neg Havg, ↑avg_seq, ↑avg],
      apply le.trans,
      apply Ha,
      rewrite -(add_halves (under_seq (i + a))) at {1},
      apply add_le_add_right,
      apply div_le_div_of_le_of_pos,
      apply rat.le_of_lt,
      apply under_seq_lt_over_seq,
      apply dec_trivial
    end))

private theorem under_seq_mono (i j : ℕ) (H : i ≤ j) : under_seq i ≤ under_seq j :=
  begin
    cases le.elim H with [k, Hk'],
    rewrite -Hk',
    apply under_seq_mono_helper
  end

private theorem over_seq_mono_helper (i k : ℕ) : over_seq (i + k) ≤ over_seq i :=
  nat.induction_on k
    (by rewrite nat.add_zero; apply rat.le_refl)
    (begin
      intros a Ha,
      rewrite [add_succ, over_succ],
      cases em (ub (avg_seq (i + a))) with [Havg, Havg],
      rewrite [if_pos Havg, ↑avg_seq, ↑avg],
      apply le.trans,
      rotate 1,
      apply Ha,
      rotate 1,
      apply add_le_of_le_sub_left,
      rewrite sub_self_div_two,
      apply div_le_div_of_le_of_pos,
      apply rat.le_of_lt,
      apply under_seq_lt_over_seq,
      apply dec_trivial,
      rewrite [if_neg Havg],
      apply Ha
    end)

private theorem over_seq_mono (i j : ℕ) (H : i ≤ j) : over_seq j ≤ over_seq i :=
  begin
    cases le.elim H with [k, Hk'],
    rewrite -Hk',
    apply over_seq_mono_helper
  end

private theorem rat_power_two_inv_ge (k : ℕ+) : 1 / 2^k~ ≤ k⁻¹ :=
  one_div_le_one_div_of_le !rat_of_pnat_is_pos !rat_power_two_le

open rat_seq
private theorem regular_lemma_helper {s : seq} {m n : ℕ+} (Hm : m ≤ n)
        (H : ∀ n i : ℕ+, i ≥ n → under_seq' n~ ≤ s i ∧ s i ≤ over_seq' n~) :
        abs (s m - s n) ≤ m⁻¹ + n⁻¹ :=
  begin
    cases H m n Hm with [T1under, T1over],
    cases H m m (!le.refl) with [T2under, T2over],
    apply le.trans,
    apply dist_bdd_within_interval,
    apply under_seq'_lt_over_seq'_single,
    rotate 1,
    repeat assumption,
    apply le.trans,
    apply width',
    apply le.trans,
    apply rat_power_two_inv_ge,
    apply le_add_of_nonneg_right,
    apply rat.le_of_lt (!pnat.inv_pos)
  end

private theorem regular_lemma (s : seq) (H : ∀ n i : ℕ+, i ≥ n → under_seq' n~ ≤ s i ∧ s i ≤ over_seq' n~) :
        regular s :=
  begin
    rewrite ↑regular,
    intros,
    cases em (m ≤ n) with [Hm, Hn],
    apply regular_lemma_helper Hm H,
    note T := regular_lemma_helper (le_of_lt (lt_of_not_ge Hn)) H,
    rewrite [abs_sub at T, {n⁻¹ + _}add.comm at T],
    exact T
  end

private noncomputable definition p_under_seq : seq := λ n : ℕ+, under_seq' n~

private noncomputable definition p_over_seq : seq := λ n : ℕ+, over_seq' n~

private theorem under_seq_regular : regular p_under_seq :=
  begin
    apply regular_lemma,
    intros n i Hni,
    apply and.intro,
    apply under_seq_mono,
    apply add_le_add_right,
    apply Hni,
    apply rat.le_of_lt,
    apply under_seq_lt_over_seq
  end

private theorem over_seq_regular : regular p_over_seq :=
  begin
    apply regular_lemma,
    intros n i Hni,
    apply and.intro,
    apply rat.le_of_lt,
    apply under_seq_lt_over_seq,
    apply over_seq_mono,
    apply add_le_add_right,
    apply Hni
  end

private noncomputable definition sup_over : ℝ := quot.mk (reg_seq.mk p_over_seq over_seq_regular)

private noncomputable definition sup_under : ℝ := quot.mk (reg_seq.mk p_under_seq under_seq_regular)

private theorem over_bound : ub sup_over :=
  begin
    rewrite ↑ub,
    intros y Hy,
    apply le_of_le_reprs,
    intro n,
    apply PB,
    apply Hy
  end

private theorem under_lowest_bound : ∀ y : ℝ, ub y → sup_under ≤ y :=
  begin
    intros y Hy,
    apply le_of_reprs_le,
    intro n,
    cases exists_not_of_not_forall (PA _) with [x, Hx],
    cases and_not_of_not_implies Hx with [HXx, Hxn],
    apply le.trans,
    apply le_of_lt,
    apply lt_of_not_ge Hxn,
    apply Hy,
    apply HXx
  end

private theorem under_over_equiv : p_under_seq ≡ p_over_seq :=
  begin
    intros,
    apply le.trans,
    have H : p_under_seq n < p_over_seq n, from !under_seq_lt_over_seq,
    rewrite [abs_of_neg (iff.mpr !sub_neg_iff_lt H), neg_sub],
    apply width',
    apply le.trans,
    apply rat_power_two_inv_ge,
    apply le_add_of_nonneg_left,
    apply rat.le_of_lt !pnat.inv_pos
  end

private theorem under_over_eq : sup_under = sup_over := quot.sound under_over_equiv

theorem exists_is_sup_of_inh_of_bdd : ∃ x : ℝ, is_sup x :=
  exists.intro sup_over (and.intro over_bound (under_over_eq ▸ under_lowest_bound))

end supremum
definition bounding_set (X : ℝ → Prop) (x : ℝ) : Prop := ∀ y : ℝ, X y → x ≤ y

theorem exists_is_inf_of_inh_of_bdd (X : ℝ → Prop) (elt : ℝ) (inh : X elt) (bound : ℝ)
        (bdd : lb X bound) : ∃ x : ℝ, is_inf X x :=
  begin
    have Hinh : bounding_set X bound, begin
      intros y Hy,
      apply bdd,
      apply Hy
    end,
    have Hub : ub (bounding_set X) elt, begin
      intros y Hy,
      apply Hy,
      apply inh
    end,
    cases exists_is_sup_of_inh_of_bdd _ _ Hinh _ Hub with [supr, Hsupr],
    existsi supr,
    cases Hsupr with [Hubs1, Hubs2],
    apply and.intro,
    intros,
    apply Hubs2,
    intros z Hz,
    apply Hz,
    apply a,
    intros y Hlby,
    apply Hubs1,
    intros z Hz,
    apply Hlby,
    apply Hz
  end

end real
