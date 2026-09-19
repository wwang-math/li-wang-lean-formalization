/-
The source-faithful rotated-gradient (Biot–Savart type) velocity symbol
`m₀(k) = -(2πi) k₁ κ(k)`, `m₁(k) = (2πi) k₀ κ(k)`.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangWiener.Reality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 12. The source-faithful rotated-gradient velocity symbol

For a scalar kernel `κ : Γ → ℂ` the Li–Wang velocity operator is a rotated gradient
`∇^⊥` applied to the kernel; on the Fourier side this is

  `m₀(k) = -(2πi) k₁ κ(k)`,   `m₁(k) = (2πi) k₀ κ(k)`.

The factor `i` is not decoration: it is exactly what makes the symbol satisfy the reality
condition `m j (-k) = conj (m j k)` when `κ` does.  The `i`-free symbol of Section 10 fails
that condition (`LiWang.WienerModel.testSymbolNoI_reality_failure` below). -/

/-- An **explicit weighted bound** on a scalar kernel: `∀ k, (1 + |k₀| + |k₁|) ‖κ k‖ ≤ A`. -/
def KernelBound (κ : Gam → ℂ) (A : ℝ) : Prop := ∀ k, wt k * ‖κ k‖ ≤ A

/-- A kernel is *admissible* if it satisfies some explicit weighted bound. -/
def IsAdmissibleKernel (κ : Gam → ℂ) : Prop := ∃ A : ℝ, KernelBound κ A

theorem KernelBound.nonneg {κ : Gam → ℂ} {A : ℝ} (h : KernelBound κ A) : 0 ≤ A :=
  le_trans (mul_nonneg (wt_pos 0).le (norm_nonneg _)) (h 0)

theorem KernelBound.sub {κ₁ κ₂ : Gam → ℂ} {A₁ A₂ : ℝ} (h₁ : KernelBound κ₁ A₁)
    (h₂ : KernelBound κ₂ A₂) : KernelBound (κ₁ - κ₂) (A₁ + A₂) := by
  intro k
  calc wt k * ‖(κ₁ - κ₂) k‖ ≤ wt k * (‖κ₁ k‖ + ‖κ₂ k‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (wt_pos k).le
    _ = wt k * ‖κ₁ k‖ + wt k * ‖κ₂ k‖ := by ring
    _ ≤ A₁ + A₂ := add_le_add (h₁ k) (h₂ k)

theorem IsAdmissibleKernel.sub {κ₁ κ₂ : Gam → ℂ} (h₁ : IsAdmissibleKernel κ₁)
    (h₂ : IsAdmissibleKernel κ₂) : IsAdmissibleKernel (κ₁ - κ₂) := by
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₂, hA₂⟩ := h₂
  exact ⟨A₁ + A₂, hA₁.sub hA₂⟩

/-- The **rotated-gradient (Biot–Savart type) velocity symbol** of a scalar kernel `κ`:
`m₀(k) = -(2πi) k₁ κ(k)` and `m₁(k) = (2πi) k₀ κ(k)`. -/
noncomputable def rotatedGradientSymbol (κ : Gam → ℂ) : Fin 2 → Gam → ℂ :=
  ![fun k => -twoPiI * ((k 1 : ℤ) : ℂ) * κ k, fun k => twoPiI * ((k 0 : ℤ) : ℂ) * κ k]

@[simp] theorem rotatedGradientSymbol_zero_comp (κ : Gam → ℂ) (k : Gam) :
    rotatedGradientSymbol κ 0 k = -twoPiI * ((k 1 : ℤ) : ℂ) * κ k := rfl

@[simp] theorem rotatedGradientSymbol_one_comp (κ : Gam → ℂ) (k : Gam) :
    rotatedGradientSymbol κ 1 k = twoPiI * ((k 0 : ℤ) : ℂ) * κ k := rfl

theorem rotatedGradient_aux {κ : Gam → ℂ} {A : ℝ} (h : KernelBound κ A) (i : Fin 2) (k : Gam) :
    2 * Real.pi * |((k i : ℤ) : ℝ)| * ‖κ k‖ ≤ 2 * Real.pi * A := by
  have h1 : |((k i : ℤ) : ℝ)| * ‖κ k‖ ≤ wt k * ‖κ k‖ :=
    mul_le_mul_of_nonneg_right (abs_coe_le_wt i k) (norm_nonneg _)
  calc 2 * Real.pi * |((k i : ℤ) : ℝ)| * ‖κ k‖
      = 2 * Real.pi * (|((k i : ℤ) : ℝ)| * ‖κ k‖) := by ring
    _ ≤ 2 * Real.pi * (wt k * ‖κ k‖) := mul_le_mul_of_nonneg_left h1 twoPi_nonneg
    _ ≤ 2 * Real.pi * A := mul_le_mul_of_nonneg_left (h k) twoPi_nonneg

/-- **The explicit uniform bound on the rotated-gradient symbol, derived from the weighted
bound on the kernel.** -/
theorem rotatedGradientSymbol_norm_le {κ : Gam → ℂ} {A : ℝ} (h : KernelBound κ A) (j : Fin 2)
    (k : Gam) : ‖rotatedGradientSymbol κ j k‖ ≤ 2 * Real.pi * A := by
  fin_cases j
  · show ‖-twoPiI * ((k 1 : ℤ) : ℂ) * κ k‖ ≤ 2 * Real.pi * A
    rw [norm_mul, norm_mul, norm_neg, norm_twoPiI, Complex.norm_intCast]
    exact rotatedGradient_aux h 1 k
  · show ‖twoPiI * ((k 0 : ℤ) : ℂ) * κ k‖ ≤ 2 * Real.pi * A
    rw [norm_mul, norm_mul, norm_twoPiI, Complex.norm_intCast]
    exact rotatedGradient_aux h 0 k

/-- **Derived, not assumed**: the rotated-gradient symbol of an admissible kernel is a
uniformly bounded velocity symbol. -/
theorem rotatedGradientSymbol_bdd {κ : Gam → ℂ} (h : IsAdmissibleKernel κ) :
    IsBddSymbol (rotatedGradientSymbol κ) := by
  obtain ⟨A, hA⟩ := h
  exact ⟨2 * Real.pi * A, fun j k => rotatedGradientSymbol_norm_le hA j k⟩

/-- **The symbol vanishes at zero frequency.** -/
@[simp] theorem rotatedGradientSymbol_zero_freq (κ : Gam → ℂ) (j : Fin 2) :
    rotatedGradientSymbol κ j 0 = 0 := by
  fin_cases j
  · show -twoPiI * (((0 : Gam) 1 : ℤ) : ℂ) * κ 0 = 0
    norm_num
  · show twoPiI * (((0 : Gam) 0 : ℤ) : ℂ) * κ 0 = 0
    norm_num

/-- **Conjugate symmetry of the kernel implies conjugate symmetry of the symbol.**
This is precisely where the factor `i` is needed. -/
theorem rotatedGradientSymbol_isRealSymbol {κ : Gam → ℂ} (hκ : ConjSymmetric κ) :
    IsRealSymbol (rotatedGradientSymbol κ) := by
  intro j
  fin_cases j
  · intro k
    show -twoPiI * (((-k) 1 : ℤ) : ℂ) * κ (-k) = conj (-twoPiI * ((k 1 : ℤ) : ℂ) * κ k)
    have hneg : ((-k) 1 : ℤ) = -(k 1) := rfl
    rw [hneg, hκ k]
    simp only [map_mul, map_neg, conj_twoPiI, map_intCast, Int.cast_neg]
    ring
  · intro k
    show twoPiI * (((-k) 0 : ℤ) : ℂ) * κ (-k) = conj (twoPiI * ((k 0 : ℤ) : ℂ) * κ k)
    have hneg : ((-k) 0 : ℤ) = -(k 0) := rfl
    rw [hneg, hκ k]
    simp only [map_mul, conj_twoPiI, map_intCast, Int.cast_neg]
    ring

/-- **Frequency-space divergence freedom**: `k₀ m₀(k) + k₁ m₁(k) = 0`. -/
theorem rotatedGradientSymbol_divFree (κ : Gam → ℂ) (k : Gam) :
    ((k 0 : ℤ) : ℂ) * rotatedGradientSymbol κ 0 k
      + ((k 1 : ℤ) : ℂ) * rotatedGradientSymbol κ 1 k = 0 := by
  show ((k 0 : ℤ) : ℂ) * (-twoPiI * ((k 1 : ℤ) : ℂ) * κ k)
      + ((k 1 : ℤ) : ℂ) * (twoPiI * ((k 0 : ℤ) : ℂ) * κ k) = 0
  ring

/-- **Subtraction commutes with the construction of the symbol.** -/
theorem rotatedGradientSymbol_sub (κ₁ κ₂ : Gam → ℂ) :
    rotatedGradientSymbol (κ₁ - κ₂)
      = rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂ := by
  funext j k
  have hpi : ∀ f g : Fin 2 → Gam → ℂ, (f - g) j k = f j k - g j k := fun _ _ => rfl
  rw [hpi]
  fin_cases j
  · show -twoPiI * ((k 1 : ℤ) : ℂ) * (κ₁ k - κ₂ k)
        = -twoPiI * ((k 1 : ℤ) : ℂ) * κ₁ k - -twoPiI * ((k 1 : ℤ) : ℂ) * κ₂ k
    ring
  · show twoPiI * ((k 0 : ℤ) : ℂ) * (κ₁ k - κ₂ k)
        = twoPiI * ((k 0 : ℤ) : ℂ) * κ₁ k - twoPiI * ((k 0 : ℤ) : ℂ) * κ₂ k
    ring

/-- **The rotated-gradient velocity preserves real (conjugate-symmetric) Fourier fields.** -/
theorem conjSymmetric_rotatedGradientVelocity {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) (j : Fin 2) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric
      ((velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j a : Wiener) :
        Gam → ℂ) :=
  ConjSymmetric.velocity _ (rotatedGradientSymbol_isRealSymbol hc) j ha

/-- **The rotated-gradient transport preserves real (conjugate-symmetric) Fourier fields.** -/
theorem conjSymmetric_rotatedGradientTransport {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hc : ConjSymmetric κ) {u v : Wiener1} (hu : ConjSymmetric u.coeff)
    (hv : ConjSymmetric v.coeff) :
    ConjSymmetric
      ((transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) u v : Wiener) :
        Gam → ℂ) :=
  ConjSymmetric.transport _ (rotatedGradientSymbol_isRealSymbol hc) hu hv

/-! ### Regression: the `i`-free symbol of Section 10 is not real -/

theorem testSymbolNoI_neg_unitFreq : testSymbolNoI 1 (-(unitFreq 0)) = -1 := by
  have hne : (-(unitFreq 0) : Gam) ≠ 0 := by
    intro h
    exact unitFreq_ne_zero 0 (by simpa using congrArg (fun x : Gam => -x) h)
  have hden : den (-(unitFreq 0)) = 1 := by simp [den, unitFreq]
  have hval : testSymbolNoI 1 (-(unitFreq 0))
      = (((-(unitFreq 0)) 0 : ℤ) : ℂ) / (den (-(unitFreq 0)) : ℂ) := by
    simp only [testSymbolNoI, if_neg hne, if_neg (by decide : ¬ (1 : Fin 2) = 0)]
  rw [hval, hden]
  norm_num [unitFreq]

/-- **Regression theorem.**  The `i`-free symbol of Section 10 violates the Fourier reality
condition already at a unit frequency, so it cannot be a real velocity symbol. -/
theorem testSymbolNoI_reality_failure :
    testSymbolNoI 1 (-(unitFreq 0)) ≠ conj (testSymbolNoI 1 (unitFreq 0)) := by
  rw [testSymbolNoI_neg_unitFreq, testSymbolNoI_unitFreq_one, map_one]
  intro h
  have : ((-1 : ℂ)).re = ((1 : ℂ)).re := by rw [h]
  norm_num at this

theorem not_isRealSymbol_testSymbolNoI : ¬ IsRealSymbol testSymbolNoI := by
  intro h
  exact testSymbolNoI_reality_failure (h 1 (unitFreq 0))

end LiWang.WienerModel
