/-
# Bringing the recovery theorem to the paper's kernel classes

`KernelRecovery` is stated for symbols satisfying the packet's admissibility predicates.  This
module checks that the two kernel classes actually used — genuine `A¹(𝕋²)` kernels, and kernels
satisfying the paper's ordered Fourier ellipticity — *land inside* those predicates, and
restates the recovery theorem for each so that no symbol-level hypothesis has to be supplied by
hand:

* `orderedEllipticity_admissible`, `orderedEllipticity_symbol` — the paper's ellipticity bounds
  give the packet's weighted multiplier bound, hence both symbol hypotheses, with no side
  condition (the comparison `wt k ≤ 3|k|` and the magnitude bounds are the v4.0 lemmas of
  `IntegrableKernel`);
* `kernel_determined_of_wiener1` — **two real `A¹` kernels with the same measured data have the
  same nonzero Fourier coefficients**; admissibility is automatic for `Wiener1`;
* `kernel_determined_of_orderedEllipticity` — the same for the paper's elliptic class;
* `velocity_determined_of_wiener1` — and therefore the two velocity operators are the same
  bounded operator.

This closes the *kernel-class* half of the carrier-compatibility question.  The other half —
identifying `MeasuredMapsAgreeOn` for this packet's mild source-to-solution maps with the
Li–Wang measurement operator for the actual nonlinear PDE — is untouched and remains the
standing input assumption (`STATUS.md` §1.3, §3).

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.KernelSeparation
import LiWangWiener.IntegrableKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. The paper's elliptic class is admissible for the packet

The comparison `wt k ≤ 3|k|` off the zero mode and the ellipticity bounds were already proved in
`IntegrableKernel` (`wt_le_three_absK`, `OrderedFourierEllipticity.fourierMagnitudeBounds`).
All that is needed here is the canonical instance: the zero coefficient of a kernel bounds
itself, so no extra hypothesis is required. -/

theorem orderedEllipticity_admissible {κ : Gam → ℂ} {c D : ℝ}
    (h : OrderedFourierEllipticity κ c D) : IsAdmissibleKernel κ :=
  h.isAdmissibleKernel (le_refl ‖κ 0‖)

/-- **The paper's elliptic class satisfies the packet's symbol hypotheses**, once the kernel is
also a real-valued function of the torus (`ConjSymmetric`). -/
theorem orderedEllipticity_symbol {κ : Gam → ℂ} {c D : ℝ}
    (hell : OrderedFourierEllipticity κ c D) (hcs : ConjSymmetric κ) :
    IsBddSymbol (rotatedGradientSymbol κ) ∧ IsRealSymbol (rotatedGradientSymbol κ) :=
  ⟨rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell),
    rotatedGradientSymbol_isRealSymbol hcs⟩

/-! ## 2. Recovery for genuine `A¹` kernels -/

/-- **Two real `A¹(𝕋²)` kernels with the same measured data have the same nonzero Fourier
coefficients.**  Only reality of the kernels is assumed: admissibility is automatic in `A¹`.

Conditional on the portable `FractionalUCP α W` parameter and on the measured-map agreement
being the packet's own (mild source-to-solution) one. -/
theorem kernel_determined_of_wiener1 (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : K₁.coeff k = K₂.coeff k := by
  obtain ⟨C, hC⟩ :=
    (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel).sub
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
  exact kernel_diff_eq_zero hα hT hW hE hUCP _ _ _ _ hC hτ0 hτT hobs hk

theorem velocity_congr {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (h : m₁ = m₂) (j : Fin 2) : velocity m₁ hm₁ j = velocity m₂ hm₂ j := by
  subst h; rfl

/-- **The velocity operators coincide.**  Equality of the nonzero Fourier coefficients is
exactly equality of the rotated-gradient symbols (the zero mode does not enter `∇^⊥(K * ·)`),
so the two kernels induce the *same* bounded operator on the Wiener algebra. -/
theorem velocity_determined_of_wiener1 (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    (j : Fin 2) :
    velocity (rotatedGradientSymbol K₁.coeff) (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel) j
      = velocity (rotatedGradientSymbol K₂.coeff)
          (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) j := by
  refine velocity_congr _ _ ?_ j
  obtain ⟨C, hC⟩ :=
    (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel).sub
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
  exact rotatedGradientSymbol_eq_of_measured hα hT hW hE hUCP _ _ _ _ hC hτ0 hτT hobs

/-! ## 3. Recovery for the paper's elliptic class -/

/-- **Two kernels of the paper's ordered-elliptic class with the same measured data have the
same nonzero Fourier coefficients.** -/
theorem kernel_determined_of_orderedEllipticity (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ} {c₁ D₁ c₂ D₂ : ℝ}
    (hell₁ : OrderedFourierEllipticity κ₁ c₁ D₁) (hcs₁ : ConjSymmetric κ₁)
    (hell₂ : OrderedFourierEllipticity κ₂ c₂ D₂) (hcs₂ : ConjSymmetric κ₂)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁))
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : κ₁ k = κ₂ k := by
  obtain ⟨C, hC⟩ :=
    (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁)).sub
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
  exact kernel_diff_eq_zero hα hT hW hE hUCP _ _ _ _ hC hτ0 hτT hobs hk

end LiWang.WienerModel
