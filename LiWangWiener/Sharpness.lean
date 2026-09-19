/-
# Two sharpness statements: what the measurement provably cannot see, and why the exterior
# hypothesis is necessary

The recovery theorem concludes `κ̂₁ = κ̂₂` at every *nonzero* frequency, and it requires
`((closure W)ᶜ).Nonempty`.  Both restrictions look at first like limitations of the method.
They are not: each is forced.

* `measurement_cannot_see_zero_mode` — there are two **distinct** admissible real kernels whose
  measured maps agree at *every* radius, differing only in their zero Fourier mode
  (`zeroModeShift`).  The zero mode does not enter `∇^⊥(K * ·)` at all, so no measurement of the
  flow can determine it.  The conclusion "equal off the zero mode" is therefore exactly sharp,
  and `velocity_determined_of_wiener1` recovers everything that acts.
* `exteriorTest_eq_zero_of_dense` — if the measured region is dense then the only exterior test
  is `0`, so the tested identity carries no information.  The hypothesis
  `((closure W)ᶜ).Nonempty` is thus necessary for this route, not a convenience.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.Unconditional

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. The rotated gradient ignores the zero mode -/

theorem rotatedGradientSymbol_congr_of_ne_zero {κ₁ κ₂ : Gam → ℂ}
    (h : ∀ k : Gam, k ≠ 0 → κ₁ k = κ₂ k) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ := by
  funext j k
  by_cases hk : k = 0
  · rw [hk, rotatedGradientSymbol_zero_freq, rotatedGradientSymbol_zero_freq]
  · fin_cases j
    · show -twoPiI * ((k 1 : ℤ) : ℂ) * κ₁ k = -twoPiI * ((k 1 : ℤ) : ℂ) * κ₂ k
      rw [h k hk]
    · show twoPiI * ((k 0 : ℤ) : ℂ) * κ₁ k = twoPiI * ((k 0 : ℤ) : ℂ) * κ₂ k
      rw [h k hk]

/-- Kernels that agree off the zero mode have agreeing measured maps at every radius. -/
theorem measuredMapsAgreeOn_of_eq_off_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    (h : ∀ k : Gam, k ≠ 0 → κ₁ k = κ₂ k) (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  measuredMapsAgreeOn_of_symbol_eq hα hT W hm₁ hr₁ hm₂ hr₂
    (rotatedGradientSymbol_congr_of_ne_zero h) A ε

/-! ## 2. An explicit indistinguishable pair -/

/-- The kernel `κ` with its zero Fourier mode shifted by one. -/
noncomputable def zeroModeShift (κ : Gam → ℂ) : Gam → ℂ := fun k => κ k + diracFun 0 k

theorem zeroModeShift_eq_off_zero (κ : Gam → ℂ) {k : Gam} (hk : k ≠ 0) :
    zeroModeShift κ k = κ k := by
  show κ k + diracFun 0 k = κ k
  rw [diracFun, if_neg hk, add_zero]

theorem zeroModeShift_ne (κ : Gam → ℂ) : κ ≠ zeroModeShift κ := by
  intro h
  have h0 : κ 0 = κ 0 + diracFun 0 0 := congrFun h 0
  rw [diracFun, if_pos rfl] at h0
  have h1 : (1 : ℂ) = 0 := by linear_combination -h0
  exact one_ne_zero h1

theorem wt_zero : wt (0 : Gam) = 1 := by
  show 1 + |(((0 : Gam) 0 : ℤ) : ℝ)| + |(((0 : Gam) 1 : ℤ) : ℝ)| = 1
  norm_num

theorem isAdmissibleKernel_zeroModeShift {κ : Gam → ℂ} (h : IsAdmissibleKernel κ) :
    IsAdmissibleKernel (zeroModeShift κ) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A + 1, fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    have h0 := hA 0
    rw [wt_zero, one_mul] at h0 ⊢
    have hb : ‖zeroModeShift κ 0‖ ≤ ‖κ 0‖ + 1 := by
      show ‖κ 0 + diracFun 0 0‖ ≤ _
      rw [diracFun, if_pos rfl]
      simpa using norm_add_le (κ 0) 1
    linarith
  · rw [zeroModeShift_eq_off_zero κ hk]
    linarith [hA k]

theorem conjSymmetric_zeroModeShift {κ : Gam → ℂ} (h : ConjSymmetric κ) :
    ConjSymmetric (zeroModeShift κ) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    have h0 : κ 0 = conj (κ 0) := by
      have h1 := h 0
      rwa [neg_zero] at h1
    show zeroModeShift κ (-0) = conj (zeroModeShift κ 0)
    rw [neg_zero]
    show κ 0 + diracFun 0 0 = conj (κ 0 + diracFun 0 0)
    rw [diracFun, if_pos rfl, map_add, ← h0]
    simp
  · have hnk : -k ≠ 0 := fun hc => hk (by rw [← neg_neg k, hc, neg_zero])
    rw [zeroModeShift_eq_off_zero κ hnk, zeroModeShift_eq_off_zero κ hk]
    exact h k

/-- **The measurement provably cannot see the zero Fourier mode.**  Two *distinct* admissible
real kernels — the packet's `finiteKernel` and its zero-mode shift — have agreeing measured maps
at every radius, for every measured region and every admissible source class.  So
`kernel_diff_eq_zero`'s conclusion (equality off the zero mode) is exactly sharp, and
`velocity_determined_of_wiener1` already recovers everything that acts on the flow. -/
theorem measurement_cannot_see_zero_mode (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    ∃ (κ₁ κ₂ : Gam → ℂ) (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
      (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
      (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
      (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂)),
      κ₁ ≠ κ₂ ∧ MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε := by
  refine ⟨finiteKernel.coeff, zeroModeShift finiteKernel.coeff,
    rotatedGradientSymbol_bdd finiteKernel_admissible,
    rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric,
    rotatedGradientSymbol_bdd (isAdmissibleKernel_zeroModeShift finiteKernel_admissible),
    rotatedGradientSymbol_isRealSymbol (conjSymmetric_zeroModeShift finiteKernel_conjSymmetric),
    zeroModeShift_ne _, ?_⟩
  exact measuredMapsAgreeOn_of_eq_off_zero hα hT W _ _ _ _
    (fun k hk => (zeroModeShift_eq_off_zero finiteKernel.coeff hk).symm) A ε

/-! ## 3. A dense measured region admits no exterior test -/

/-- **The exterior hypothesis is necessary for this route.**  If the measured region is dense,
the only exterior test is zero, so the tested identity — and with it the whole mode-identity
argument — carries no information. -/
theorem exteriorTest_eq_zero_of_dense {W : Set Torus2} (hWd : closure W = Set.univ)
    {ψ : Wiener1} (h : IsExteriorTest W ψ) : ψ = 0 := by
  obtain ⟨U, hU, hsub, hvan⟩ := h
  have hUuniv : U = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hWd]
    exact hsub
  have h0 : synth (incl ψ) = synth (0 : Wiener) := by
    rw [map_zero]
    exact ContinuousMap.ext (fun x => hvan x (by rw [hUuniv]; trivial))
  have h1 : incl ψ = 0 := synth_injective h0
  refine Wiener1.coeff_injective (funext fun k => ?_)
  have h2 := congrArg (fun a : Wiener => (a : Gam → ℂ) k) h1
  simpa using h2

end LiWang.WienerModel
