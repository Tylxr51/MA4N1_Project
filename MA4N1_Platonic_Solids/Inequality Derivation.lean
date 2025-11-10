import Mathlib.Tactic
import Mathlib.Data.Real.Basic


theorem platonic_inequality
  {V E F m n : ℝ}
  (hm : m > 0)
  (hn : n > 0)
  (hE : E > 0)
  (hEuler : V - E + F = 2)
  (hFaces : m * F = 2 * E)
  (hVerts : n * V = 2 * E) :
  (m - 2) * (n - 2) < 4 := by
have hm' : m ≠ 0 := by linarith [hm] --want to make this more low level
have hn' : n ≠ 0 := by linarith [hn] -- also make into seperate lemma for reuse
have hE' : E ≠ 0 := by linarith [hE]
have hF : F = 2 * E / m := by -- make lemma so can reuse
  rw[← hFaces]
  rw[mul_comm]
  rw[div_eq_mul_inv]
  rw[mul_assoc]
  rw[mul_inv_cancel₀ hm']
  rw[mul_one]
have hV : V = 2 * E / n := by
  rw[← hVerts]
  rw[mul_comm]
  rw[div_eq_mul_inv]
  rw[mul_assoc]
  rw[mul_inv_cancel₀ hn']
  rw[mul_one]
have hEuler_div_E :  n * m * (V - E + F) / E = n * m * 2 / E := by
  rw[hEuler]
rw[hF, hV] at hEuler_div_E

-- SIMPLIFYING (ADD COMMENTS)
repeat rw [div_eq_mul_inv] at hEuler_div_E
rw[sub_eq_add_neg, mul_assoc, right_distrib, right_distrib] at hEuler_div_E
rw[mul_assoc 2 E n⁻¹, mul_assoc 2 (E*n⁻¹) E⁻¹, mul_comm (E*n⁻¹), ← mul_assoc E⁻¹, mul_comm E⁻¹, mul_inv_cancel₀ hE'] at hEuler_div_E
rw[← neg_mul_eq_neg_mul, mul_inv_cancel₀ hE', ← sub_eq_add_neg] at hEuler_div_E
rw[mul_assoc 2 E m⁻¹, mul_assoc 2 (E*m⁻¹), mul_comm (E*m⁻¹), ←mul_assoc E⁻¹, mul_comm E⁻¹, mul_inv_cancel₀ hE'] at hEuler_div_E
repeat rw[one_mul] at hEuler_div_E
rw[mul_assoc, mul_comm, mul_assoc, right_distrib, sub_eq_add_neg, right_distrib] at hEuler_div_E
rw[←neg_mul_eq_neg_mul, one_mul] at hEuler_div_E
rw[mul_assoc 2, mul_comm n⁻¹, mul_inv_cancel₀ hn', mul_one] at hEuler_div_E
rw[left_distrib, left_distrib] at hEuler_div_E
rw[mul_comm, mul_comm m, neg_mul] at hEuler_div_E
rw[← mul_assoc, mul_comm 2 m⁻¹, ← mul_assoc, mul_inv_cancel₀ hm', one_mul] at hEuler_div_E
rw[mul_assoc n m 2, mul_comm m 2, ← mul_assoc, mul_comm n 2] at hEuler_div_E
rw[mul_assoc, mul_assoc] at hEuler_div_E

have h_rhs_pos : 2 * (n * (m * E⁻¹)) > 0 := by
  have mE_inv_pos : m * E⁻¹ > 0 := mul_pos (hm) (inv_pos.mpr hE)
  have nmE_inv_pos : n * (m * E⁻¹) > 0 := mul_pos (hn) (mE_inv_pos)
  exact mul_pos (by norm_num) (nmE_inv_pos)

symm at hEuler_div_E
apply gt_iff_lt.mp at h_rhs_pos

have h_lhs_pos : 2 * m + -(n * m) + 2 * n > 0 :=
  lt_of_lt_of_eq h_rhs_pos hEuler_div_E

apply gt_iff_lt.mp at h_lhs_pos
rw[← neg_neg (2*m+-(n*m)+2*n)] at h_lhs_pos

have h_neg_lhs_neg : -(2 * m + -(n * m) + 2 * n) < 0 :=
  neg_pos.mp h_lhs_pos

rw[neg_add, neg_add, neg_neg, ← neg_mul, add_comm, ← add_assoc, add_comm, ← add_assoc, neg_mul] at h_neg_lhs_neg

have h_neg_lhs_neg_add_four : n * m + -(2 * n) + -(2 * m) + 4 < 0 + 4 :=
  add_lt_add_right h_neg_lhs_neg 4

rw[zero_add] at h_neg_lhs_neg_add_four

have h_factor :
  n * m + -(2 * n) + -(2 * m) + 4 = (m - 2) * (n - 2) := by ring

symm at h_factor

apply lt_of_eq_of_lt h_factor h_neg_lhs_neg_add_four
