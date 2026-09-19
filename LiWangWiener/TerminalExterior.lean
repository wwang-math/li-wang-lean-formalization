/-
# From the proved terminal approximation to exterior state and velocity convergence

Task 4 and Task 5 of the v6.0 assignment.

* `exists_exteriorStateConvergence_terminal` — the proved *global* physical `L²` convergence of
  the **full** generated states supplies, through the packet's `exteriorStateConvergence_of_global`
  (which uses `norm_synthL2_velocity_le`, the proved physical `L²` boundedness of the velocity
  multiplier), all three hypotheses of `ExteriorStateConvergence`: exterior convergence of the
  scalar states, exterior convergence of the velocities of **the full states**, and the uniform
  exterior bound.  The velocity operator is applied to the full difference state, never to an
  exterior restriction or a zero extension.
* `generatedExteriorApproximation_terminal` — `GeneratedExteriorApproximation` is therefore
  **derived**, not assumed, for every real first-order target at every positive time `τ ≤ T`.
* `tested_interaction_real_targets` — the downstream theorem: for real targets and an exterior
  test, the tested symmetrized interaction of the kernel difference vanishes.  Its hypotheses
  are only the geometric/kernel conditions, small-source measured-map agreement on the smooth
  class, and the portable `FractionalUCP α W` parameter.  The common mild neighbourhood is
  derived from `exists_bothMildOnSub` with the smaller of the two radii.

This is **not** the full paper theorem: the final operator-recovery conclusion and its carrier
compatibility are not proved here.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.TerminalControl
import LiWangWiener.ExteriorObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. Exterior state and full-state velocity convergence -/

/-- **Task 4, restated for the terminal sequence.**  The proved *global* physical `L²`
convergence of the **full** generated states at time `τ` yields, through the packet's
`exteriorStateConvergence_of_global` (which uses `norm_synthL2_velocity_le`, the proved
physical `L²` boundedness of the velocity multiplier), the exterior convergence of the states
*and* of the velocities of those **full** states.  The velocity operator is applied to
`incl (u n - U)`, the honest full difference state — never to an exterior restriction or a
zero extension. -/
theorem exists_exteriorStateConvergence_terminal (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n : ℕ, g n ∈ smoothSources hT W) ∧
      ExteriorStateConvergence W m hm
        (fun n => curveState hT.le (duhamelOp hα hT.le (g n)) τ) U.val := by
  obtain ⟨g, hg, hconv⟩ := exists_smoothSources_terminal_tendsto hα hT hW hUCP hτ0 hτT U
  exact ⟨g, hg, exteriorStateConvergence_of_global W hm hconv⟩

/-! ## 3. `GeneratedExteriorApproximation` is derived, not assumed -/

/-- **The remaining analytic input of v5.0 is now a theorem.**  For every real first-order
target and every positive time `τ ≤ T`, the actual generated states of actual smooth admissible
sources approximate it in the exterior sense, velocities included. -/
theorem generatedExteriorApproximation_terminal (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    GeneratedExteriorApproximation hα hT.le W m hm (smoothSources hT W) τ U.val :=
  exists_exteriorStateConvergence_terminal hα hT hW hUCP hm hτ0 hτT U

/-! ## 4. Radius monotonicity of the two small-source hypotheses -/

theorem MeasuredMapsAgreeOn.mono_radius (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {A : Submodule ℝ (Curve0 T)} {ε ε' : ℝ}
    (hεε' : ε ≤ ε') (h : MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε') :
    MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  fun f hf hfn => h f hf (lt_of_lt_of_le hfn hεε')

theorem BothMildOnSub.mono_radius (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {A : Submodule ℝ (Curve0 T)} {ε ε' : ℝ}
    (hεε' : ε ≤ ε') (h : BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A ε') :
    BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A ε :=
  fun f hf hfn => h f hf (lt_of_lt_of_le hfn hεε')

/-! ## 5. The downstream theorem -/

/-- **Task 5.**  For real first-order targets and an exterior test, the tested symmetrized
interaction of the kernel difference vanishes.

The hypotheses are: the geometric data (`W` open, `τ ∈ (0,T]`), the kernel conditions
(bounded, real, divergence-free difference with an explicit symbol bound), small-source
measured-map agreement on the *smooth* class, and the portable `FractionalUCP α W` parameter.
No `GeneratedExteriorApproximation`, no state or velocity convergence, no target identity and
no density conclusion is taken as input: the approximation is supplied by
`generatedExteriorApproximation_terminal`, and the common mild neighbourhood by
`exists_bothMildOnSub` at the smaller radius.

This is not the full paper theorem; the operator-recovery step is not proved here. -/
theorem tested_interaction_real_targets (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (U V : RealWiener1) :
    testedInteraction (m₁ - m₂) (hm₁.sub hm₂) ψ U.val V.val = 0 := by
  obtain ⟨ε₁, hε₁, hobs₁⟩ := hobs
  obtain ⟨ε₀, hε₀, hmild₀⟩ :=
    exists_bothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W)
  set ε : ℝ := min ε₀ ε₁ with hεdef
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
    BothMildOnSub.mono_radius hα hT.le hm₁ hr₁ hm₂ hr₂ (min_le_left ε₀ ε₁) hmild₀
  have hobs' : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
    MeasuredMapsAgreeOn.mono_radius hα hT.le W hm₁ hr₁ hm₂ hr₂ (min_le_right ε₀ ε₁) hobs₁
  exact tested_interaction_target_eq_zero hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hε hmild hobs'
    hψ τ (generatedExteriorApproximation_terminal hα hT hW hUCP (hm₁.sub hm₂) hτ0 hτT U)
    (generatedExteriorApproximation_terminal hα hT hW hUCP (hm₁.sub hm₂) hτ0 hτT V)

end LiWang.WienerModel
