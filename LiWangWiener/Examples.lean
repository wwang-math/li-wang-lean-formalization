/-
Concrete kernels, symbols and Fourier packets.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangWiener.RealCarriers

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 14. A concrete real example: kernel, symbol and Fourier packet

The showcased concrete example of the packet is the `i`-corrected rotated-gradient symbol
of an explicit admissible, conjugate-symmetric kernel, tested against an explicit nonzero
conjugate-symmetric Fourier packet (a real "cosine mode"). -/

theorem wt_neg (k : Gam) : wt (-k) = wt k := by
  have h0 : ((-k) 0 : ℤ) = -(k 0) := rfl
  have h1 : ((-k) 1 : ℤ) = -(k 1) := rfl
  simp only [wt, h0, h1, Int.cast_neg, abs_neg]

/-- A concrete admissible, conjugate-symmetric scalar kernel `κ(k) = (1 + |k₀| + |k₁|)⁻¹`. -/
noncomputable def exampleKernel : Gam → ℂ := fun k => (((wt k)⁻¹ : ℝ) : ℂ)

theorem exampleKernel_bound : KernelBound exampleKernel 1 := by
  intro k
  show wt k * ‖(((wt k)⁻¹ : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (wt_pos k)), mul_inv_cancel₀ (wt_ne_zero k)]

theorem exampleKernel_admissible : IsAdmissibleKernel exampleKernel := ⟨1, exampleKernel_bound⟩

theorem exampleKernel_conjSymmetric : ConjSymmetric exampleKernel := by
  intro k
  show (((wt (-k))⁻¹ : ℝ) : ℂ) = conj (((wt k)⁻¹ : ℝ) : ℂ)
  rw [Complex.conj_ofReal, wt_neg]

/-- The concrete (source-faithful, `i`-corrected) velocity symbol of the packet. -/
noncomputable def exampleSymbol : Fin 2 → Gam → ℂ := rotatedGradientSymbol exampleKernel

theorem exampleSymbol_bdd : IsBddSymbol exampleSymbol :=
  rotatedGradientSymbol_bdd exampleKernel_admissible

theorem exampleSymbol_real : IsRealSymbol exampleSymbol :=
  rotatedGradientSymbol_isRealSymbol exampleKernel_conjSymmetric

theorem exampleSymbol_norm_le (j : Fin 2) (k : Gam) : ‖exampleSymbol j k‖ ≤ 2 * Real.pi := by
  simpa using rotatedGradientSymbol_norm_le exampleKernel_bound j k

theorem exampleSymbol_divFree (k : Gam) :
    ((k 0 : ℤ) : ℂ) * exampleSymbol 0 k + ((k 1 : ℤ) : ℂ) * exampleSymbol 1 k = 0 :=
  rotatedGradientSymbol_divFree exampleKernel k

/-- The concrete symbol is nonzero, so the instantiation is not degenerate. -/
theorem exampleSymbol_unitFreq : exampleSymbol 1 (unitFreq 0) = twoPiI * (2 : ℂ)⁻¹ := by
  show twoPiI * (((unitFreq 0) 0 : ℤ) : ℂ) * exampleKernel (unitFreq 0) = twoPiI * (2 : ℂ)⁻¹
  rw [unitFreq_self]
  show twoPiI * ((1 : ℤ) : ℂ) * (((wt (unitFreq 0))⁻¹ : ℝ) : ℂ) = twoPiI * (2 : ℂ)⁻¹
  rw [wt_unitFreq]
  push_cast
  ring

theorem exampleSymbol_ne_zero : exampleSymbol 1 (unitFreq 0) ≠ 0 := by
  rw [exampleSymbol_unitFreq]
  have h : twoPiI ≠ 0 := by
    intro hz
    have : ‖twoPiI‖ = 0 := by rw [hz]; simp
    rw [norm_twoPiI] at this
    have := Real.pi_pos
    linarith
  simpa using h

/-! ### An explicit nonzero conjugate-symmetric Fourier packet -/

theorem diracFun_neg (k₀ k : Gam) : diracFun k₀ (-k) = diracFun (-k₀) k := by
  have h : (-k = k₀) ↔ (k = -k₀) := neg_eq_iff_eq_neg
  simp only [diracFun, h]

theorem conj_diracFun (k₀ k : Gam) : conj (diracFun k₀ k) = diracFun k₀ k := by
  by_cases h : k = k₀ <;> simp [diracFun, h]

/-- The real **cosine mode** `δ_{k₀} + δ_{-k₀}`, a nonzero conjugate-symmetric packet. -/
noncomputable def cosModeFun (k₀ : Gam) : Gam → ℂ := diracFun k₀ + diracFun (-k₀)

theorem cosModeFun_conjSymmetric (k₀ : Gam) : ConjSymmetric (cosModeFun k₀) := by
  intro k
  show diracFun k₀ (-k) + diracFun (-k₀) (-k) = conj (diracFun k₀ k + diracFun (-k₀) k)
  rw [diracFun_neg, diracFun_neg, neg_neg, map_add, conj_diracFun, conj_diracFun]
  ring

theorem cosModeFun_self (k₀ : Gam) : cosModeFun k₀ k₀ ≠ 0 := by
  have h1 : diracFun k₀ k₀ = 1 := by
    show (if k₀ = k₀ then (1 : ℂ) else 0) = 1
    exact if_pos rfl
  show diracFun k₀ k₀ + diracFun (-k₀) k₀ ≠ 0
  by_cases h : k₀ = -k₀
  · have h2 : diracFun (-k₀) k₀ = 1 := by
      show (if k₀ = -k₀ then (1 : ℂ) else 0) = 1
      exact if_pos h
    rw [h1, h2]; norm_num
  · have h2 : diracFun (-k₀) k₀ = 0 := by
      show (if k₀ = -k₀ then (1 : ℂ) else 0) = 0
      exact if_neg h
    rw [h1, h2]; norm_num

/-- The cosine mode as an element of the first-order Wiener space. -/
noncomputable def cosMode1 (k₀ : Gam) : Wiener1 := dirac1 k₀ + dirac1 (-k₀)

@[simp] theorem cosMode1_coeff (k₀ : Gam) : (cosMode1 k₀).coeff = cosModeFun k₀ := rfl

theorem cosMode1_conjSymmetric (k₀ : Gam) : ConjSymmetric (cosMode1 k₀).coeff :=
  cosModeFun_conjSymmetric k₀

theorem cosMode1_ne_zero (k₀ : Gam) : cosMode1 k₀ ≠ 0 := by
  intro h
  have : (cosMode1 k₀).coeff k₀ = 0 := by rw [h]; rfl
  exact cosModeFun_self k₀ this

/-- The concrete real Fourier packet, as an element of the real first-order carrier. -/
noncomputable def realCosMode (k₀ : Gam) : RealWiener1 :=
  RealWiener1.mk (cosMode1 k₀) (cosMode1_conjSymmetric k₀)

theorem realCosMode_ne_zero (k₀ : Gam) : realCosMode k₀ ≠ 0 := by
  intro h
  exact cosMode1_ne_zero k₀ (congrArg RealWiener1.val h)

theorem conjSymmetric_diracFun_zero : ConjSymmetric (diracFun (0 : Gam)) := by
  intro k
  rw [diracFun_neg, neg_zero, conj_diracFun]

/-- A nonzero element of the real Wiener algebra, certifying that `RealWiener` is not the
trivial space. -/
noncomputable def realDelta : RealWiener := RealWiener.mk (wdirac 0) conjSymmetric_diracFun_zero

theorem norm_realDelta : ‖realDelta‖ = 1 := norm_wdirac 0

theorem realDelta_ne_zero : realDelta ≠ 0 := by
  intro h
  have hz : ‖realDelta‖ = 0 := by rw [h]; simp
  rw [norm_realDelta] at hz
  norm_num at hz

/-! ### The kernel-level real transport and the two-kernel polarization identity -/

/-- The real transport form generated by a scalar kernel through the rotated-gradient
symbol. -/
noncomputable def kernelTransport {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) : RealWiener1 →L[ℝ] RealWiener1 →L[ℝ] RealWiener :=
  realTransport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
    (rotatedGradientSymbol_isRealSymbol hc)

/-- The real quadratic residual generated by a scalar kernel. -/
noncomputable def kernelQuadResidual {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) : RealWiener1 → RealWiener := quad (kernelTransport hb hc)

theorem kernelQuadResidual_zero {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) : kernelQuadResidual hb hc 0 = 0 := quad_zero _

theorem fderiv_kernelQuadResidual_zero {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) : fderiv ℝ (kernelQuadResidual hb hc) 0 = 0 := fderiv_quad_zero _

theorem contDiff_two_kernelQuadResidual {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) : ContDiff ℝ 2 (kernelQuadResidual hb hc) := contDiff_quad _ 2

theorem fderiv_fderiv_kernelQuadResidual_apply {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) (h₁ h₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (kernelQuadResidual hb hc)) 0 h₁ h₂
      = kernelTransport hb hc h₁ h₂ + kernelTransport hb hc h₂ h₁ := by
  have hq : kernelQuadResidual hb hc = quad (kernelTransport hb hc) := rfl
  rw [hq, fderiv_fderiv_quad]
  simp

/-- Subtraction of kernels corresponds to subtraction of the real transport forms. -/
theorem kernelTransport_sub {κ₁ κ₂ : Gam → ℂ} (hb₁ : IsAdmissibleKernel κ₁)
    (hb₂ : IsAdmissibleKernel κ₂) (hc₁ : ConjSymmetric κ₁) (hc₂ : ConjSymmetric κ₂) :
    kernelTransport hb₁ hc₁ - kernelTransport hb₂ hc₂
      = kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂) := by
  refine Eq.trans (realTransport_sub _ _ _ _) ?_
  exact realTransport_congr_symbol _ _ _ _ (rotatedGradientSymbol_sub κ₁ κ₂).symm

/-- **The two-kernel Li–Wang polarization identity over `ℝ`.**  The second real Fréchet
derivative at the origin of the difference of the two quadratic residuals is the
symmetrized real transport form of the *difference kernel*. -/
theorem realKernelPolarization {κ₁ κ₂ : Gam → ℂ} (hb₁ : IsAdmissibleKernel κ₁)
    (hb₂ : IsAdmissibleKernel κ₂) (hc₁ : ConjSymmetric κ₁) (hc₂ : ConjSymmetric κ₂)
    (g₁ g₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (fun x => kernelQuadResidual hb₁ hc₁ x
        - kernelQuadResidual hb₂ hc₂ x)) 0 g₁ g₂
      = kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂) g₁ g₂
        + kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂) g₂ g₁ := by
  have hfun : (fun x => kernelQuadResidual hb₁ hc₁ x - kernelQuadResidual hb₂ hc₂ x)
      = quad (kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂)) := by
    funext x
    rw [← kernelTransport_sub hb₁ hb₂ hc₁ hc₂]
    rfl
  rw [hfun, fderiv_fderiv_quad]
  simp

theorem realKernelPolarization_iteratedFDeriv {κ₁ κ₂ : Gam → ℂ} (hb₁ : IsAdmissibleKernel κ₁)
    (hb₂ : IsAdmissibleKernel κ₂) (hc₁ : ConjSymmetric κ₁) (hc₂ : ConjSymmetric κ₂)
    (g₁ g₂ : RealWiener1) :
    iteratedFDeriv ℝ 2 (fun x => kernelQuadResidual hb₁ hc₁ x
        - kernelQuadResidual hb₂ hc₂ x) 0 ![g₁, g₂]
      = kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂) g₁ g₂
        + kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂) g₂ g₁ := by
  have hfun : (fun x => kernelQuadResidual hb₁ hc₁ x - kernelQuadResidual hb₂ hc₂ x)
      = quad (kernelTransport (hb₁.sub hb₂) (hc₁.sub hc₂)) := by
    funext x
    rw [← kernelTransport_sub hb₁ hb₂ hc₁ hc₂]
    rfl
  rw [hfun]
  exact iteratedFDeriv_two_quad _ 0 g₁ g₂

/-- **Summary: the real (conjugate-symmetric) quadratic residual realization.** -/
theorem realQuadResidual_realization {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) :
    realQuadResidual m hm hr 0 = 0
      ∧ fderiv ℝ (realQuadResidual m hm hr) 0 = 0
      ∧ ContDiff ℝ 2 (realQuadResidual m hm hr)
      ∧ ‖realTransport m hm hr‖ ≤ 4 * Real.pi * C
      ∧ (∀ h₁ h₂ : RealWiener1, fderiv ℝ (fderiv ℝ (realQuadResidual m hm hr)) 0 h₁ h₂
          = realTransport m hm hr h₁ h₂ + realTransport m hm hr h₂ h₁) :=
  ⟨realQuadResidual_zero m hm hr, fderiv_realQuadResidual_zero m hm hr,
    contDiff_two_realQuadResidual m hm hr, norm_realTransport_le hm hr hC,
    fderiv_fderiv_realQuadResidual_apply m hm hr⟩

end LiWang.WienerModel
