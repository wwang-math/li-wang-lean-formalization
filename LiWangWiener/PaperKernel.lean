/-
# The paper kernel interface, kept separate from what is proved

The Li–Wang paper's kernel hypothesis is *stronger* than the weighted multiplier bound
`IsAdmissibleKernel` used throughout this development, and stronger than the magnitude
predicate `FourierMagnitudeBounds`.  This module states the difference explicitly and records,
as proved negative results, that neither the finite-support test kernel of the packet nor a
sign-reversed law is a witness of the paper's ordered ellipticity.

Nothing here proves punctured smoothness or the ordered ellipticity lower bound for a kernel
arising from the paper; those remain genuine input assumptions.

Part of `LiWangWienerObservationBridgePacket` v4.0.
-/
import LiWangWiener.IntegrableKernel
import LiWangWiener.HessianNonDegeneracy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

/-- **`finiteKernel` is a test of the Wiener multiplier theory, not a witness of the paper's
ordered ellipticity.**  Its Fourier coefficient vanishes at the nonzero frequency `e₁`, so its
real part is not strictly positive there and the lower bound fails for every positive `c`. -/
theorem finiteKernel_not_orderedFourierEllipticity {c D : ℝ} :
    ¬ OrderedFourierEllipticity finiteKernel.coeff c D := by
  intro h
  have hne : (unitFreq 1 : Gam) ≠ 0 := unitFreq_ne_zero 1
  have hpos := h.re_pos hne
  rw [finiteKernel_coeff_unitFreq_one] at hpos
  simp at hpos

/-- `finiteKernel` also fails the *magnitude* lower bound for every positive `c`: it is
outside the elliptic class in either formulation. -/
theorem finiteKernel_not_fourierMagnitudeBounds {c D : ℝ} (hc : 0 < c) :
    ¬ FourierMagnitudeBounds finiteKernel.coeff c D := by
  intro h
  have hne : (unitFreq 1 : Gam) ≠ 0 := unitFreq_ne_zero 1
  have hlow := (h (unitFreq 1) hne).1
  rw [finiteKernel_coeff_unitFreq_one, norm_zero] at hlow
  have : 0 < c / wt (unitFreq 1) := div_pos hc (wt_pos _)
  linarith

/-- `finiteKernel` does satisfy the weighted **upper** bound, so the Wiener multiplier theory
applies to it; only the elliptic *lower* bound fails. -/
theorem finiteKernel_nonzeroModeDecay : NonzeroModeDecay finiteKernel.coeff ‖finiteKernel‖ :=
  fun k _ => finiteKernel.kernelBound k

end LiWang.WienerModel
