import Mathlib.Tactic.IntervalCases

/-- Shifting the solution set down to avoid subtraction in ℕ -/
lemma shift_classify : {(m, n) : ℕ × ℕ | (m + 1) * (n + 1)< 4}
 = {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)} := by
  ext x
  aesop
  have : fst < 3 := by
    grind
  interval_cases fst
  · grind
  · grind
  · grind

/-- Function to shift the set back up to what we desire -/
lemma shift : (· + (3,3)) '' {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4}
 = {(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} := by
  ext
  aesop
  use fst - 3, snd - 3
  obtain _|_|_|fst := fst <;> try grind
  obtain _|_|_|snd := snd <;> grind

/-- Final classification theorem for the pairs (m, n) -/
theorem classify_mn : ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
 = {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} := by
  rw [← shift, shift_classify]
  ext
  aesop

/-- Map the five pairs to their Platonic solid names. -/
inductive SolidName | tetrahedron | cube | octahedron | dodecahedron | icosahedron
deriving DecidableEq, Repr

/-- ATTEMPT TO MAKE LESS 'CHAT-GPT'-IFIED-/
def mn_solid : (ℕ × ℕ) → Option SolidName
| (3, 3) => some SolidName.tetrahedron
| (3, 4) => some SolidName.octahedron
| (3, 5) => some SolidName.icosahedron
| (4, 3) => some SolidName.cube
| (5, 3) => some SolidName.dodecahedron
| _       => none

open SolidName
#eval mn_solid (3, 4)
