/-
# An unconditional instance of the approximation theorem, and non-degeneracy of its conclusion

Every headline statement of this packet carries `FractionalUCP α W` as an explicit parameter,
and the packet discharges it for no proper `W`.  It is therefore worth having compiled evidence
that the approximation theorem is not an empty implication, and that its conclusion is not
satisfiable by accident.  This module supplies both, with **no hypothesis beyond `1/2 < α`,
`T > 0`, `0 < τ ≤ T`**:

* `norm_synthL2_incl_eq_zero_iff` — the quantity that is driven to zero in the conclusion is a
  *faithful* norm: it vanishes only at the zero state.  So the theorem is not trivially true
  through a degenerate norm.
* `exists_nonzero_realWiener1` — real targets of nonzero norm exist; the packet's explicit
  `finiteKernel` is one.
* `exists_nonzero_smoothSourceBefore` — the control class `smoothSourcesBefore hT W τ` is
  nontrivial for every nonempty open `W` and every `0 < τ ≤ T`.
* `terminal_zero_control` and `not_tendsto_zero_control` — the constant-zero control sequence
  fails for every nonzero target, so the conclusion is not satisfiable by a trivial choice.
* `exists_terminal_tendsto_univ` — **an unconditional instance**: for `W = 𝕋²` the UCP parameter
  is discharged by `fractionalUCP_univ`, so the approximation theorem holds outright.
* `unconditional_nontrivial_approximation` — the package: a nonzero real target, an
  unconditional approximating sequence of admissible controls switched off before `τ`, and the
  failure of the zero control for that same target.

The measured region being the whole torus is of course the degenerate case of the inverse
problem; nothing here weakens the fact that for a proper `W` the parameter is undischarged.

Part of `LiWangFormalizationTerminalControlPacket` v6.0.
-/
import LiWangFormalization.KernelSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. The conclusion's norm is faithful -/

theorem norm_synthL2_eq_zero_iff (a : Wiener) : ‖synthL2 a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    refine eq_of_synthL2_eq ?_
    rw [map_zero]
    exact norm_eq_zero.1 h
  · intro h
    rw [h, map_zero, norm_zero]

theorem norm_synthL2_incl_eq_zero_iff (u : Wiener1) : ‖synthL2 (incl u)‖ = 0 ↔ u = 0 := by
  rw [norm_synthL2_eq_zero_iff]
  constructor
  · intro h
    refine Wiener1.coeff_injective (funext fun k => ?_)
    have h2 := congrArg (fun a : Wiener => (a : Gam → ℂ) k) h
    simpa using h2
  · intro h; rw [h, map_zero]

/-! ## 2. Nonzero real targets exist -/

/-- The packet's explicit `finiteKernel`, viewed as a real first-order state. -/
noncomputable def finiteTarget : RealWiener1 :=
  RealWiener1.mk finiteKernel finiteKernel_conjSymmetric

theorem norm_finiteTarget_ne_zero : ‖synthL2 (incl finiteTarget.val)‖ ≠ 0 := by
  rw [Ne, norm_synthL2_incl_eq_zero_iff]
  exact finiteKernel_ne_zero

theorem exists_nonzero_realWiener1 : ∃ U : RealWiener1, ‖synthL2 (incl U.val)‖ ≠ 0 :=
  ⟨finiteTarget, norm_finiteTarget_ne_zero⟩

/-! ## 3. The control class is nontrivial -/

theorem exists_nonzero_smoothSourceBefore (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hne : W.Nonempty) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ V ∈ smoothSourcesBefore hT W τ, V ≠ 0 := by
  obtain ⟨a, K, hane, hsm, hKc, hKW, hvan⟩ := exists_smooth_localized_profile hW hne
  obtain ⟨χ, hbump, -, -, hone⟩ :=
    exists_smooth_time_bump_on (T := τ) (c := τ / 4) (d := 3 * τ / 4)
      (by linarith) (by linarith) (by linarith)
  have hprof : a ∈ smoothProfiles W := ⟨hsm, K, hKc, hKW, hvan⟩
  refine ⟨productSource hT.le a hbump.continuous,
    Submodule.subset_span ⟨a, χ, hbump.continuous, hprof, hbump, rfl⟩, ?_⟩
  have hmid : (τ / 4 + 3 * τ / 4) / 2 = τ / 2 := by ring
  have hmem : τ / 2 ∈ Set.Icc (0:ℝ) T := ⟨by linarith, by linarith⟩
  refine productSource_ne_zero hT.le a hbump.continuous hane
    (t₀ := ⟨τ / 2, hmem⟩) ?_
  show χ (τ / 2) ≠ 0
  rw [← hmid, hone]
  exact one_ne_zero

/-! ## 4. The zero control fails for every nonzero target -/

theorem terminal_zero_control (hα : 1 / 2 < α) (hT : 0 ≤ T) (τ : ℝ) :
    curveState hT (duhamelOp hα hT (0 : Curve0 T)) τ = 0 := by
  rw [map_zero]
  rfl

/-- The constant-zero control sequence does **not** approximate a nonzero target: the quantity
in the conclusion is then the constant `‖synthL2 (incl U.val)‖ ≠ 0`. -/
theorem not_tendsto_zero_control (hα : 1 / 2 < α) (hT : 0 ≤ T) (τ : ℝ) {U : RealWiener1}
    (hU : ‖synthL2 (incl U.val)‖ ≠ 0) :
    ¬ Tendsto
        (fun _ : ℕ => ‖synthL2 (incl (curveState hT (duhamelOp hα hT (0 : Curve0 T)) τ - U.val))‖)
        atTop (𝓝 0) := by
  have hval : ∀ _ : ℕ,
      ‖synthL2 (incl (curveState hT (duhamelOp hα hT (0 : Curve0 T)) τ - U.val))‖
        = ‖synthL2 (incl U.val)‖ := by
    intro _
    rw [terminal_zero_control hα hT τ, zero_sub, map_neg, map_neg, norm_neg]
  intro hc
  rw [tendsto_congr hval] at hc
  exact hU (tendsto_nhds_unique tendsto_const_nhds hc)

/-! ## 5. An unconditional instance -/

/-- **The approximation theorem with no undischarged hypothesis.**  For the degenerate measured
region `W = 𝕋²` the portable parameter is discharged by `fractionalUCP_univ`, so every real
first-order target is approximated at time `τ` by actual generated states of actual admissible
controls, switched off before `τ`. -/
theorem exists_terminal_tendsto_univ (hα : 1 / 2 < α) (hT : 0 < T) {τ : ℝ} (hτ0 : 0 < τ)
    (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSourcesBefore hT (Set.univ : Set Torus2) τ) ∧
      Tendsto
        (fun n => ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (𝓝 0) :=
  exists_smoothSourcesBefore_terminal_tendsto hα hT isOpen_univ (fractionalUCP_univ α) hτ0 hτT U

/-- **The packaged non-vacuity statement.**  A nonzero real target, an unconditional
approximating sequence of admissible controls switched off before `τ`, and the failure of the
zero control for that same target: the conclusion of the approximation theorem is neither
vacuous nor trivially satisfiable. -/
theorem unconditional_nontrivial_approximation (hα : 1 / 2 < α) (hT : 0 < T) {τ : ℝ}
    (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ (U : RealWiener1) (g : ℕ → Curve0 T),
      ‖synthL2 (incl U.val)‖ ≠ 0 ∧
      (∀ n, g n ∈ smoothSourcesBefore hT (Set.univ : Set Torus2) τ) ∧
      Tendsto
        (fun n => ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (𝓝 0) ∧
      ¬ Tendsto
        (fun _ : ℕ =>
          ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (0 : Curve0 T)) τ - U.val))‖)
        atTop (𝓝 0) := by
  obtain ⟨g, hg, hconv⟩ := exists_terminal_tendsto_univ hα hT hτ0 hτT finiteTarget
  exact ⟨finiteTarget, g, norm_finiteTarget_ne_zero, hg, hconv,
    not_tendsto_zero_control hα hT.le τ norm_finiteTarget_ne_zero⟩

end LiWang.Formalization
