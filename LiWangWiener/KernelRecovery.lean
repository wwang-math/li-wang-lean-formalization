/-
# Recovery of the kernel from the terminal tested identity

`KernelModeIdentity.symbol_mode_identity` constrains the symbol difference at every frequency
`n = −(k+l)` where the exterior test has a nonzero Fourier coefficient.  This module removes
that side condition and draws the conclusion.

* `shift1` — an exterior test may be multiplied by a Fourier mode and stays an exterior test
  (`isExteriorTest_shift1`): multiplication by `e_p` does not change the zero set.  Hence for
  **every** frequency there is an exterior test with a nonzero coefficient there
  (`exists_exteriorTest_coeff_ne_zero`), and the mode identity holds unconditionally
  (`symbol_mode_identity_all`).
* For the paper's rotated-gradient symbols this reads `Δ(k,l) · (κ̂₁ − κ̂₂)(k) = Δ(k,l) ·
  (κ̂₁ − κ̂₂)(l)` with `Δ(k,l) = k₀l₁ − k₁l₀`, so the Fourier coefficients of the kernel
  difference are **constant on all nonzero frequencies** (`kernel_fourier_eq`).
* A constant that is compatible with the boundedness of the rotated-gradient symbol must be
  zero, so `κ̂₁ = κ̂₂` off the zero mode (`kernel_diff_eq_zero`) and the two velocity operators
  coincide (`rotatedGradientSymbol_eq_of_measured`).

Everything is conditional on exactly the hypotheses of `tested_interaction_real_targets`:
geometry, kernel admissibility, small-source measured-map agreement on the smooth class, and
the portable `FractionalUCP α W` parameter.  Nothing new is assumed here.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.KernelModeIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. Shifting an exterior test in frequency -/

theorem wt_add_le (q p : Gam) : wt (q + p) ≤ wt q * wt p := by
  have e0 : (((q + p) 0 : ℤ) : ℝ) = ((q 0 : ℤ) : ℝ) + ((p 0 : ℤ) : ℝ) := by
    show (((q 0 + p 0 : ℤ)) : ℝ) = _
    push_cast; ring
  have e1 : (((q + p) 1 : ℤ) : ℝ) = ((q 1 : ℤ) : ℝ) + ((p 1 : ℤ) : ℝ) := by
    show (((q 1 + p 1 : ℤ)) : ℝ) = _
    push_cast; ring
  have hq := one_le_wt q
  have hp := one_le_wt p
  have habs : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
    intro a b
    rcases abs_cases (a + b) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
      linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]
  have habs0 := habs ((q 0 : ℤ) : ℝ) ((p 0 : ℤ) : ℝ)
  have habs1 := habs ((q 1 : ℤ) : ℝ) ((p 1 : ℤ) : ℝ)
  have hsum : wt (q + p) ≤ wt q + wt p - 1 := by
    simp only [wt, e0, e1]
    simp only [wt] at hq hp
    linarith
  nlinarith

theorem summable_wt_shift (ψ : Wiener1) (p : Gam) :
    Summable (fun k : Gam => wt k * ‖ψ.coeff (k - p)‖) := by
  have hequiv := (Equiv.addRight p).summable_iff
    (f := fun k : Gam => wt k * ‖ψ.coeff (k - p)‖)
  refine hequiv.1 ?_
  have hfun : (fun q : Gam => wt (q + p) * ‖ψ.coeff (q + p - p)‖)
      = fun q : Gam => wt (q + p) * ‖ψ.coeff q‖ := by
    funext q; rw [add_sub_cancel_right]
  have hcomp : ((fun k : Gam => wt k * ‖ψ.coeff (k - p)‖) ∘ (Equiv.addRight p))
      = fun q : Gam => wt (q + p) * ‖ψ.coeff q‖ := by
    rw [← hfun]; rfl
  rw [hcomp]
  refine Summable.of_nonneg_of_le (fun q => by have := (wt_pos (q + p)).le; positivity)
    (fun q => ?_) (ψ.summable_wt.mul_left (wt p))
  calc wt (q + p) * ‖ψ.coeff q‖
      ≤ (wt q * wt p) * ‖ψ.coeff q‖ :=
        mul_le_mul_of_nonneg_right (wt_add_le q p) (norm_nonneg _)
    _ = wt p * (wt q * ‖ψ.coeff q‖) := by ring

/-- The frequency shift of a first-order state: physically, multiplication by `e_p`. -/
noncomputable def shift1 (p : Gam) (ψ : Wiener1) : Wiener1 :=
  Wiener1.mk (fun k => ψ.coeff (k - p)) (summable_wt_shift ψ p)

@[simp] theorem coeff_shift1 (p : Gam) (ψ : Wiener1) (k : Gam) :
    (shift1 p ψ).coeff k = ψ.coeff (k - p) := rfl

theorem synth_incl_shift1 (p : Gam) (ψ : Wiener1) (x : Torus2) :
    synth (incl (shift1 p ψ)) x = emode p x * synth (incl ψ) x := by
  have he := (Equiv.addRight p).tsum_eq
    (fun k : Gam => (incl (shift1 p ψ) : Gam → ℂ) k * emode k x)
  rw [synth_apply, ← he]
  have hterm : ∀ q : Gam,
      (incl (shift1 p ψ) : Gam → ℂ) ((Equiv.addRight p) q) * emode ((Equiv.addRight p) q) x
        = emode p x * ((incl ψ : Gam → ℂ) q * emode q x) := by
    intro q
    show ψ.coeff (q + p - p) * emode (q + p) x = emode p x * (ψ.coeff q * emode q x)
    rw [add_sub_cancel_right, emode_add_apply]
    ring
  rw [tsum_congr hterm, tsum_mul_left, synth_apply]

theorem isExteriorTest_shift1 {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ) (p : Gam) :
    IsExteriorTest W (shift1 p ψ) := by
  obtain ⟨U, hU, hsub, hvan⟩ := h
  exact ⟨U, hU, hsub, fun x hx => by rw [synth_incl_shift1, hvan x hx, mul_zero]⟩

/-- **Every frequency carries an exterior test.** -/
theorem exists_exteriorTest_coeff_ne_zero {W : Set Torus2} (hE : ((closure W)ᶜ).Nonempty)
    (n : Gam) : ∃ ψ : Wiener1, IsExteriorTest W ψ ∧ ψ.coeff n ≠ 0 := by
  obtain ⟨ψ₀, hψ₀, hne⟩ := exists_exteriorTest_ne_zero hE
  obtain ⟨n₀, hn₀⟩ := exists_coeff_ne_zero hne
  refine ⟨shift1 (n - n₀) ψ₀, isExteriorTest_shift1 hψ₀ _, ?_⟩
  rw [coeff_shift1, show n - (n - n₀) = n₀ from by abel]
  exact hn₀

/-! ## 2. The mode identity at every frequency -/

/-- **The mode constraint, unconditionally in `k` and `l`.** -/
theorem symbol_mode_identity_all (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (k l : Gam) :
    ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * ((m₁ - m₂) j k + (m₁ - m₂) j l) = 0 := by
  obtain ⟨ψ, hψ, hne⟩ := exists_exteriorTest_coeff_ne_zero hE (-(k + l))
  exact symbol_mode_identity hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hτ0 hτT hobs hψ k l hne

/-! ## 3. The kernel difference has constant Fourier coefficients off zero -/

/-- **The Fourier coefficients of the kernel difference agree at any two independent
frequencies.** -/
theorem kernel_fourier_eq (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (k l : Gam) (hdet : (k 0) * (l 1) - (k 1) * (l 0) ≠ (0 : ℤ)) :
    κ₁ k - κ₂ k = κ₁ l - κ₂ l := by
  have hdiff : rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂
      = rotatedGradientSymbol (κ₁ - κ₂) := (rotatedGradientSymbol_sub κ₁ κ₂).symm
  have hdiv : IsDivFreeSymbol (rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) := by
    rw [hdiff]; exact rotatedGradientSymbol_isDivFree _
  have h := symbol_mode_identity_all hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hτ0 hτT hobs k l
  rw [hdiff] at h
  have hsplit : ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ)
        * (rotatedGradientSymbol (κ₁ - κ₂) j k + rotatedGradientSymbol (κ₁ - κ₂) j l)
      = (∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * rotatedGradientSymbol (κ₁ - κ₂) j k)
        + ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * rotatedGradientSymbol (κ₁ - κ₂) j l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, sum_rotatedGradientSymbol, sum_rotatedGradientSymbol] at h
  set Δ : ℂ := ((k 0 : ℤ) : ℂ) * ((l 1 : ℤ) : ℂ) - ((k 1 : ℤ) : ℂ) * ((l 0 : ℤ) : ℂ) with hΔ
  have hDk : (((-(k + l)) 1 : ℤ) : ℂ) * ((k 0 : ℤ) : ℂ)
        - (((-(k + l)) 0 : ℤ) : ℂ) * ((k 1 : ℤ) : ℂ) = -Δ := by
    have e0 : ((-(k + l)) 0 : ℤ) = -(k 0) - l 0 := by show -(k 0 + l 0) = _; ring
    have e1 : ((-(k + l)) 1 : ℤ) = -(k 1) - l 1 := by show -(k 1 + l 1) = _; ring
    rw [e0, e1, hΔ]
    push_cast
    ring
  have hDl : (((-(k + l)) 1 : ℤ) : ℂ) * ((l 0 : ℤ) : ℂ)
        - (((-(k + l)) 0 : ℤ) : ℂ) * ((l 1 : ℤ) : ℂ) = Δ := by
    have e0 : ((-(k + l)) 0 : ℤ) = -(k 0) - l 0 := by show -(k 0 + l 0) = _; ring
    have e1 : ((-(k + l)) 1 : ℤ) = -(k 1) - l 1 := by show -(k 1 + l 1) = _; ring
    rw [e0, e1, hΔ]
    push_cast
    ring
  rw [hDk, hDl] at h
  have hk : (κ₁ - κ₂) k = κ₁ k - κ₂ k := rfl
  have hl : (κ₁ - κ₂) l = κ₁ l - κ₂ l := rfl
  rw [hk, hl] at h
  have hΔne : Δ ≠ 0 := by
    intro hz
    refine hdet ?_
    rw [hΔ] at hz
    have hc : (((k 0) * (l 1) - (k 1) * (l 0) : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hz
    exact_mod_cast hc
  have hmain : ((κ₁ l - κ₂ l) - (κ₁ k - κ₂ k)) * (twoPiI * Δ) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hmain with h1 | h2
  · exact (sub_eq_zero.1 h1).symm
  · exact absurd h2 (mul_ne_zero twoPiI_ne_zero hΔne)

/-! ## 4. Recovery -/

/-- **The kernel difference vanishes at every nonzero frequency.** -/
theorem kernel_diff_eq_zero (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : κ₁ k = κ₂ k := by
  have heq := kernel_fourier_eq hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  -- the common value `c` at the frequencies `(N,0)`, `N ≥ 1`
  set e1 : Gam := ![0, 1] with he1
  set c : ℂ := κ₁ e1 - κ₂ e1 with hc
  have hrow : ∀ N : ℤ, N ≠ 0 → κ₁ ![N, 0] - κ₂ ![N, 0] = c := by
    intro N hN
    refine heq ![N, 0] e1 ?_
    show (![N, 0] 0) * (![(0:ℤ), 1] 1) - (![N, 0] 1) * (![(0:ℤ), 1] 0) ≠ 0
    simpa using hN
  -- boundedness of the symbol forces `c = 0`
  have hczero : c = 0 := by
    by_contra hcne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hcne
    obtain ⟨N, hN⟩ := exists_nat_gt (C / (2 * Real.pi * ‖c‖))
    have hNpos : 0 < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
    have hN0 : N ≠ 0 := by
      intro hz
      rw [hz] at hNpos
      simp at hNpos
    have hNne : ((N : ℤ)) ≠ 0 := by exact_mod_cast hN0
    have hval : (rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) 1 ![(N:ℤ), 0]
        = twoPiI * ((N : ℤ) : ℂ) * c := by
      show rotatedGradientSymbol κ₁ 1 ![(N:ℤ), 0] - rotatedGradientSymbol κ₂ 1 ![(N:ℤ), 0] = _
      rw [rotatedGradientSymbol_one_comp, rotatedGradientSymbol_one_comp,
        show (![(N:ℤ), 0] 0 : ℤ) = (N : ℤ) from rfl, ← hrow (N : ℤ) hNne]
      ring
    have hbd := hC 1 ![(N:ℤ), 0]
    rw [hval, norm_mul, norm_mul, norm_twoPiI] at hbd
    have hcast : ‖(((N : ℤ)) : ℂ)‖ = (N : ℝ) := by
      rw [Complex.norm_intCast]
      simp
    rw [hcast] at hbd
    have : C < 2 * Real.pi * (N : ℝ) * ‖c‖ := by
      have hpos : 0 < 2 * Real.pi * ‖c‖ := by positivity
      have := (div_lt_iff₀ hpos).1 hN
      nlinarith
    linarith
  -- now every nonzero frequency
  have hgen : ∀ q : Gam, q ≠ 0 → κ₁ q - κ₂ q = 0 := by
    intro q hq
    have hq' : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hq (funext fun j => by fin_cases j <;> simp [hcon.1, hcon.2])
    rcases hq' with h0 | h1
    · -- independent from `e1 = (0,1)`
      have := heq q e1 (by
        show (q 0) * (![(0:ℤ), 1] 1) - (q 1) * (![(0:ℤ), 1] 0) ≠ 0
        simpa using h0)
      rw [this, ← hc, hczero]
    · -- independent from `(1,0)`
      have hind : (q 0) * ((![(1:ℤ), 0]) 1) - (q 1) * ((![(1:ℤ), 0]) 0) ≠ 0 := by
        show (q 0) * (0 : ℤ) - (q 1) * (1 : ℤ) ≠ 0
        simpa using h1
      have h2 := heq q ![(1:ℤ), 0] hind
      rw [h2, hrow 1 one_ne_zero, hczero]
  exact sub_eq_zero.1 (hgen k hk)

/-- **Operator recovery for the rotated-gradient velocity.**  Under the measured-map agreement
on the smooth source class and the portable UCP parameter, the two velocity symbols coincide. -/
theorem rotatedGradientSymbol_eq_of_measured (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ := by
  funext j k
  by_cases hk : k = 0
  · rw [hk, rotatedGradientSymbol_zero_freq, rotatedGradientSymbol_zero_freq]
  · have := kernel_diff_eq_zero hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs hk
    fin_cases j
    · show -twoPiI * ((k 1 : ℤ) : ℂ) * κ₁ k = -twoPiI * ((k 1 : ℤ) : ℂ) * κ₂ k
      rw [this]
    · show twoPiI * ((k 0 : ℤ) : ℂ) * κ₁ k = twoPiI * ((k 0 : ℤ) : ℂ) * κ₂ k
      rw [this]

end LiWang.WienerModel
