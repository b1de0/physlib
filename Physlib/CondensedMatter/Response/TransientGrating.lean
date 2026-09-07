/-
Copyright (c) 2026 Marko Herkaliuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marko Herkaliuk
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!

# The transient thermal grating decay rate

## i. Overview

A transient thermal grating experiment writes a sinusoidal temperature profile of
wavevector `q` into a sample and watches its amplitude decay. Under the relaxation-time
approximation to the phonon Boltzmann equation, a single phonon mode of group velocity
`v` and relaxation time `τ` responds to a perturbation `∝ exp (I q x + s t)` as
`(ξ (y + I μ))⁻¹` in the direction cosine `μ`, with `ξ = q v τ` the mode's Knudsen number
and `y = (τ⁻¹ + s) / (q v)`. Requiring the equilibrium distribution to equal its own
angular average makes a decay rate a solution of `Phi ξ y = 1`, where

`Phi ξ y = (∫ μ in -1..1, y / (y ^ 2 + μ ^ 2)) / (2 ξ)`.

The imaginary part of the response is odd in `μ` and cancels over the symmetric interval,
so nothing is discarded by working on `ℝ`. Positivity of `y` is the
statement that `s` lies above `-τ⁻¹`; it is not assumed but proved, in `root_pos`.

The results below establish that such a solution exists exactly when `ξ < π / 2`, that it
is then unique and available in closed form as `y = (tan ξ)⁻¹ = cot ξ`, and — through
`Phi_of_neg` — why the threshold is `π / 2` rather than `π`.

## ii. Why `Phi` is defined by an integral

`Phi_eq_arctan_inv` evaluates it to `arctan y⁻¹ / ξ`, so the integral could be dispensed
with. It is kept as the definition because the closed form invites a choice that does not
exist. For `0 < y` one has `arctan y⁻¹ = π / 2 - arctan y`, and the right-hand side is the
more natural thing to write down; for `y < 0` the two differ by exactly `π`, which is
`Real.arctan_inv_of_neg` against `Real.arctan_inv_of_pos`.

Taking `(π / 2 - arctan y) / ξ` on the whole line therefore replaces the response by its
continuation across a branch cut. That continuation has a root at `y = tan (π / 2 - ξ)`
for every `ξ < π`, negative exactly when `ξ > π / 2`, so it appears to predict decay rates
below `-τ⁻¹` throughout `π / 2 < ξ < π`. `Phi_of_neg` is the reason it does not: at such a
`y` the continuation takes the value `1` while `Phi` takes `1 - π / ξ`. Defined by the
integral there is no branch to choose, and the antiderivative used in `integral_response`,
`arctan (μ / y)`, is single-valued on `ℝ`.

## iii. Key results

- `Phi` : the single-mode dispersion function, the angular average of the response.
- `Phi_eq_arctan_inv` : the closed form `arctan y⁻¹ / ξ`, with no sign condition.
- `Phi_of_pos`, `Phi_of_neg` : agreement, and disagreement by `π / ξ`, with
  `(π / 2 - arctan y) / ξ`.
- `Phi_lt` : `Phi ξ y < (π / 2) / ξ` for every `y`, which is the threshold.
- `Phi_strictAntiOn` : `Phi ξ` is strictly decreasing on `0 < y`.
- `Phi_inv_tan_eq_one` : the root in closed form, `y = (tan ξ)⁻¹`.
- `exists_root_iff` : a root exists if and only if `ξ < π / 2`.
- `root_pos` : every root is positive, i.e. the rate never lies below `-τ⁻¹`.
- `root_unique`, `root_eq` : the root is unique and equals `(tan ξ)⁻¹`.
- `criterion_physical` : the criterion restated in `q`, `v`, `τ`.

## iv. Table of contents

- A. The dispersion function
  - A.1. Definition
  - A.2. The closed form
  - A.3. Agreement and disagreement with `(π / 2 - arctan y) / ξ`
  - A.4. Bound and strict monotonicity
- B. The criterion
  - B.1. The root in closed form
  - B.2. Existence
  - B.3. Position of the root
  - B.4. Uniqueness
- C. The criterion in physical variables

## v. References

- A. A. Maznev, J. A. Johnson and K. A. Nelson, Phys. Rev. B 84, 195206 (2011).
- K. C. Collins et al., J. Appl. Phys. 114, 104302 (2013).
- C. Hua and A. J. Minnich, Phys. Rev. B 89, 094302 (2014).

-/

@[expose] public section

open Real

namespace TransientGrating

variable {ξ y : ℝ}

/-! # A. The dispersion function -/

/-! ## A.1. Definition -/

/-- The single-mode transient-thermal-grating dispersion function: the angular average over
`μ ∈ [-1, 1]` of the real part of the single-mode response `(ξ (y + I μ))⁻¹`, in the variable
`y = (τ⁻¹ + s) / (q v)` and with `ξ = q v τ` the mode's Knudsen number. A discrete decay rate
corresponds to a solution of `Phi ξ y = 1`.

It is defined by the integral rather than by a closed form on purpose; see `Phi_of_neg`. -/
noncomputable def Phi (ξ y : ℝ) : ℝ := (∫ μ in (-1 : ℝ)..1, y / (y ^ 2 + μ ^ 2)) / (2 * ξ)

/-! ## A.2. The closed form -/

/-- The closed form of the dispersion function. The angular integral is
`Real.integral_div_sq_add_sq`, whose antiderivative `arctan (μ / y)` is single-valued on `ℝ`;
that is what makes this closed form unambiguous, and it holds with no sign condition on `y`. -/
lemma Phi_eq_arctan_inv (ξ y : ℝ) : Phi ξ y = arctan y⁻¹ / ξ := by
  have h : (∫ μ in (-1 : ℝ)..1, y / (y ^ 2 + μ ^ 2)) = 2 * arctan y⁻¹ := by
    rw [integral_div_sq_add_sq, neg_div, arctan_neg, one_div]
    ring
  rw [Phi, h]
  exact mul_div_mul_left _ _ two_ne_zero

/-! ## A.3. Agreement and disagreement with `(π / 2 - arctan y) / ξ` -/

/-- On `0 < y` the dispersion function is `(π / 2 - arctan y) / ξ`. -/
lemma Phi_of_pos (hy : 0 < y) : Phi ξ y = (π / 2 - arctan y) / ξ := by
  rw [Phi_eq_arctan_inv, arctan_inv_of_pos hy]

/-- On `y < 0` the dispersion function is **not** `(π / 2 - arctan y) / ξ`: the two differ
by exactly `π / ξ`. This is why the existence threshold is `π / 2` and not `π`; see the
module docstring. -/
lemma Phi_of_neg (hξ : ξ ≠ 0) (hy : y < 0) :
    Phi ξ y = (π / 2 - arctan y) / ξ - π / ξ := by
  rw [Phi_eq_arctan_inv, arctan_inv_of_neg hy]
  field_simp
  ring

/-! ## A.4. Bound and strict monotonicity -/

/-- `Phi ξ` is bounded above by `(π / 2) / ξ`, uniformly in `y`. This single bound is the
existence threshold: a root of `Phi ξ y = 1` forces `ξ < π / 2`. -/
lemma Phi_lt (hξ : 0 < ξ) (y : ℝ) : Phi ξ y < (π / 2) / ξ := by
  rw [Phi_eq_arctan_inv]
  exact div_lt_div_of_pos_right (arctan_lt_pi_div_two _) hξ

/-- `Phi ξ` is strictly decreasing on the positive reals, which is where the physical
solutions live. -/
lemma Phi_strictAntiOn (hξ : 0 < ξ) : StrictAntiOn (Phi ξ) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha' : (0 : ℝ) < a := ha
  have hinv : b⁻¹ < a⁻¹ := by
    have hb' : (0 : ℝ) < b := ha'.trans hab
    rw [inv_lt_inv₀ hb' ha']
    exact hab
  rw [Phi_eq_arctan_inv, Phi_eq_arctan_inv]
  exact div_lt_div_of_pos_right (arctan_strictMono hinv) hξ

/-! # B. The criterion -/

/-! ## B.1. The root in closed form -/

/-- For `0 < ξ < π / 2` the root of `Phi ξ y = 1` is `y = (tan ξ)⁻¹`, that is `cot ξ`.
The proof is a direct computation and uses no intermediate value theorem. -/
lemma Phi_inv_tan_eq_one (h0 : 0 < ξ) (hpi : ξ < π / 2) : Phi ξ (tan ξ)⁻¹ = 1 := by
  rw [Phi_eq_arctan_inv, inv_inv, arctan_tan (by linarith [pi_pos]) hpi]
  exact div_self h0.ne'

/-! ## B.2. Existence -/

/-- The criterion: for `0 < ξ` a discrete decay rate exists if and only if `ξ < π / 2`.
Physically this is a Knudsen threshold on the mode's relaxation time. -/
lemma exists_root_iff (h0 : 0 < ξ) : (∃ y, Phi ξ y = 1) ↔ ξ < π / 2 := by
  constructor
  · rintro ⟨y, hy⟩
    have := Phi_lt h0 y
    rw [hy] at this
    rwa [lt_div_iff₀ h0, one_mul] at this
  · exact fun hpi => ⟨(tan ξ)⁻¹, Phi_inv_tan_eq_one h0 hpi⟩

/-! ## B.3. Position of the root -/

/-- Every root is positive, so the decay rate it describes lies strictly above the
continuum edge `s = -τ⁻¹`. This is a theorem rather than a standing hypothesis: the
dispersion relation cannot place a discrete rate below the edge. -/
lemma root_pos (h0 : 0 < ξ) (h : Phi ξ y = 1) : 0 < y := by
  have hy : arctan y⁻¹ = ξ := by
    rw [Phi_eq_arctan_inv, div_eq_one_iff_eq h0.ne'] at h
    exact h
  exact inv_pos.1 (arctan_pos.1 (hy ▸ h0))

/-! ## B.4. Uniqueness -/

/-- The root is unique, since `Phi ξ` is strictly monotone where the roots are. -/
lemma root_unique (h0 : 0 < ξ) {y₁ y₂ : ℝ} (h1 : Phi ξ y₁ = 1) (h2 : Phi ξ y₂ = 1) :
    y₁ = y₂ :=
  (Phi_strictAntiOn h0).injOn (root_pos h0 h1) (root_pos h0 h2) (h1.trans h2.symm)

/-- Any root is the closed-form one. -/
lemma root_eq (h0 : 0 < ξ) (hpi : ξ < π / 2) (h : Phi ξ y = 1) : y = (tan ξ)⁻¹ :=
  root_unique h0 h (Phi_inv_tan_eq_one h0 hpi)

/-! # C. The criterion in physical variables -/

/-- The criterion in terms of the grating wavevector `q`, the group velocity `v` and the
relaxation time `τ`: a discrete decay rate exists if and only if `q v τ < π / 2`. -/
lemma criterion_physical {q v τ : ℝ} (hq : 0 < q) (hv : 0 < v) (hτ : 0 < τ) :
    (∃ y, Phi (q * v * τ) y = 1) ↔ q * v * τ < π / 2 :=
  exists_root_iff (by positivity)

end TransientGrating
