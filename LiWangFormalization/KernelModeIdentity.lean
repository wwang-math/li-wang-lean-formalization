/-
# From the terminal identity to explicit Fourier-mode constraints on the kernel difference

`TerminalExterior.tested_interaction_real_targets` says the symmetrized tested interaction of
the kernel difference vanishes **for every real first-order target**.  Because every real target
is now reachable (that is the content of the v6.0 approximation theorem), this is no longer a
statement about a distinguished family of states: bilinearity extends it to **all** states, and
evaluating on Fourier–Dirac states turns it into an explicit algebraic identity satisfied by the
symbol difference `m₁ − m₂`.

Contents:

* `testedInteraction_eq_zero_of_real_states` — bilinear extension from real states to all of
  `Wiener1`, using the packet's existing conjugate-reflection decomposition `comb1_decomposition`;
* `testedInteraction_dirac1` — the exact value on Fourier–Dirac states:
  `2πi · ψ̂(n) · Σⱼ nⱼ (mⱼ(k) + mⱼ(l))` with `n = −(k+l)`;
* `symbol_mode_identity` — the resulting constraint, valid at every frequency where the exterior
  test has a nonzero Fourier coefficient;
* `exists_exteriorTest_ne_zero` — nonzero exterior tests exist whenever `(closure W)ᶜ` is
  nonempty, so the constraint is not vacuous;
* `exists_symbol_mode_identity` — the packaged non-vacuous statement.

This is the interface Codex's terminal-recovery / kernel-separation work consumes.  It is **not**
the paper's operator-recovery conclusion: no claim is made here that these constraints force
`m₁ = m₂`.

Part of `LiWangFormalizationTerminalControlPacket` v6.0.
-/
import LiWangFormalization.TerminalExterior
import LiWangFormalization.PrimitiveGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. Bilinearity of the tested interaction -/

theorem testedInteraction_add_left (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (ψ u u' v : Wiener1) :
    testedInteraction m hm ψ (u + u') v
      = testedInteraction m hm ψ u v + testedInteraction m hm ψ u' v := by
  rw [testedInteraction, testedInteraction, testedInteraction,
    sideInteraction_add_left, sideInteraction_add_right]
  ring

theorem testedInteraction_add_right (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (ψ u v v' : Wiener1) :
    testedInteraction m hm ψ u (v + v')
      = testedInteraction m hm ψ u v + testedInteraction m hm ψ u v' := by
  rw [testedInteraction, testedInteraction, testedInteraction,
    sideInteraction_add_right, sideInteraction_add_left]
  ring

theorem testedInteraction_smul_left (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (c : ℂ)
    (ψ u v : Wiener1) :
    testedInteraction m hm ψ (c • u) v = c * testedInteraction m hm ψ u v := by
  rw [testedInteraction, testedInteraction, sideInteraction_smul_left,
    sideInteraction_smul_right]
  ring

theorem testedInteraction_smul_right (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (c : ℂ)
    (ψ u v : Wiener1) :
    testedInteraction m hm ψ u (c • v) = c * testedInteraction m hm ψ u v := by
  rw [testedInteraction, testedInteraction, sideInteraction_smul_right,
    sideInteraction_smul_left]
  ring

/-! ## 2. From real states to all states -/

theorem conjSymmetric_comb1_re (u : Wiener1) : ConjSymmetric (comb1 (2⁻¹) 1 u).coeff :=
  conjSymmetric_comb1 conj_half (by norm_num) u

theorem conjSymmetric_comb1_im (u : Wiener1) :
    ConjSymmetric (comb1 ((2 * Complex.I)⁻¹) (-1) u).coeff :=
  conjSymmetric_comb1 conj_halfI (by norm_num) u

/-- **The tested interaction vanishes on every pair of states.**  Real targets suffice because
the real states span `Wiener1` over `ℂ` — this is the packet's `comb1_decomposition`. -/
theorem testedInteraction_eq_zero_of_real_states {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (ψ : Wiener1) (h : ∀ U V : RealWiener1, testedInteraction m hm ψ U.val V.val = 0)
    (u v : Wiener1) : testedInteraction m hm ψ u v = 0 := by
  have hreal : ∀ a b : Wiener1, ConjSymmetric a.coeff → ConjSymmetric b.coeff →
      testedInteraction m hm ψ a b = 0 := by
    intro a b ha hb
    have h2 := h (RealWiener1.mk a ha) (RealWiener1.mk b hb)
    rwa [RealWiener1.val_mk, RealWiener1.val_mk] at h2
  have hu := comb1_decomposition u
  have hv := comb1_decomposition v
  rw [← hu, ← hv]
  simp only [testedInteraction_add_left, testedInteraction_add_right,
    testedInteraction_smul_left, testedInteraction_smul_right]
  rw [hreal _ _ (conjSymmetric_comb1_re u) (conjSymmetric_comb1_re v),
    hreal _ _ (conjSymmetric_comb1_re u) (conjSymmetric_comb1_im v),
    hreal _ _ (conjSymmetric_comb1_im u) (conjSymmetric_comb1_re v),
    hreal _ _ (conjSymmetric_comb1_im u) (conjSymmetric_comb1_im v)]
  ring

/-! ## 3. Evaluation on Fourier–Dirac states -/

theorem velocity_incl_dirac1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) (k : Gam) :
    velocity m hm j (incl (dirac1 k)) = m j k • wdirac k := by
  refine lp.ext (funext fun p => ?_)
  show m j p * ((incl (dirac1 k)) p) = (m j k • wdirac k) p
  show m j p * diracFun k p = m j k * diracFun k p
  by_cases hp : p = k
  · rw [hp]
  · rw [diracFun, if_neg hp]
    ring

theorem synth_velocity_incl_dirac1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (k : Gam) (x : Torus2) :
    synth (velocity m hm j (incl (dirac1 k))) x = m j k * emode k x := by
  rw [velocity_incl_dirac1, map_smul, synth_wdirac]
  rfl

/-- **The exact value of the one-sided tested interaction on Fourier–Dirac states.** -/
theorem sideInteraction_dirac1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ : Wiener1)
    (k l : Gam) :
    sideInteraction m hm ψ (dirac1 k) (dirac1 l)
      = ∑ j : Fin 2, m j k * (twoPiI * (((-(k + l)) j : ℤ) : ℂ) * ψ.coeff (-(k + l))) := by
  rw [sideInteraction]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpt : ∀ x : Torus2,
      synth (incl (dirac1 l)) x * synth (velocity m hm j (incl (dirac1 k))) x
          * synth (fourierDeriv j ψ) x
        = m j k * (synth (fourierDeriv j ψ) x * emode (k + l) x) := by
    intro x
    rw [incl_dirac1, synth_wdirac, synth_velocity_incl_dirac1, emode_add_apply]
    ring
  have hstep : (∫ x : Torus2, synth (incl (dirac1 l)) x
        * synth (velocity m hm j (incl (dirac1 k))) x * synth (fourierDeriv j ψ) x)
      = m j k * ∫ x : Torus2, synth (fourierDeriv j ψ) x * emode (k + l) x := by
    have h1 : (∫ x : Torus2, synth (incl (dirac1 l)) x
          * synth (velocity m hm j (incl (dirac1 k))) x * synth (fourierDeriv j ψ) x)
        = ∫ x : Torus2, m j k * (synth (fourierDeriv j ψ) x * emode (k + l) x) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    have h2 : (∫ x : Torus2, m j k * (synth (fourierDeriv j ψ) x * emode (k + l) x))
        = m j k * ∫ x : Torus2, synth (fourierDeriv j ψ) x * emode (k + l) x :=
      integral_const_mul (μ := (volume : Measure Torus2)) (m j k)
        (fun x : Torus2 => synth (fourierDeriv j ψ) x * emode (k + l) x)
    rw [h1, h2]
  rw [hstep, integral_synth_mul_emode, fourierDeriv_apply]

/-- **The symmetrized tested interaction on Fourier–Dirac states.**  With `n = −(k+l)` it is
`2πi · ψ̂(n) · Σⱼ nⱼ (mⱼ(k) + mⱼ(l))`. -/
theorem testedInteraction_dirac1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ : Wiener1)
    (k l : Gam) :
    testedInteraction m hm ψ (dirac1 k) (dirac1 l)
      = twoPiI * ψ.coeff (-(k + l))
          * ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * (m j k + m j l) := by
  rw [testedInteraction, sideInteraction_dirac1, sideInteraction_dirac1,
    show l + k = k + l from add_comm l k, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem twoPiI_ne_zero : twoPiI ≠ 0 := by
  rw [twoPiI]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-! ## 4. Nonzero exterior tests exist -/

theorem exists_exteriorTest_ne_zero {W : Set Torus2} (hE : ((closure W)ᶜ).Nonempty) :
    ∃ ψ : Wiener1, IsExteriorTest W ψ ∧ ψ ≠ 0 := by
  have hEopen : IsOpen ((closure W)ᶜ) := (isClosed_closure (s := W)).isOpen_compl
  obtain ⟨u, K, hune, -, hKc, hKE, hvan⟩ := exists_smooth_localized_profile1 hEopen hE
  refine ⟨u, ⟨Kᶜ, hKc.isClosed.isOpen_compl, fun x hx hxK => ?_, fun x hx => hvan x hx⟩, hune⟩
  exact (hKE hxK) hx

theorem exists_coeff_ne_zero {ψ : Wiener1} (h : ψ ≠ 0) : ∃ n : Gam, ψ.coeff n ≠ 0 := by
  by_contra hc
  refine h (Wiener1.coeff_injective (funext fun n => ?_))
  have hn : ¬ (ψ.coeff n ≠ 0) := fun hne => hc ⟨n, hne⟩
  rw [not_not] at hn
  rw [hn]
  rfl

/-! ## 5. The mode identity -/

/-- **An explicit Fourier-mode constraint on the kernel difference**, derived — not assumed —
from the proved approximation theorem.  At every frequency `n` where the exterior test has a
nonzero Fourier coefficient, and for every splitting `k + l = −n`,

`Σⱼ nⱼ · ((m₁ − m₂)ⱼ(k) + (m₁ − m₂)ⱼ(l)) = 0`.

Hypotheses: geometry, kernel conditions, small-source measured-map agreement on the smooth
class, and the portable `FractionalUCP α W` parameter. -/
theorem symbol_mode_identity (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (k l : Gam) (hcoeff : ψ.coeff (-(k + l)) ≠ 0) :
    ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * ((m₁ - m₂) j k + (m₁ - m₂) j l) = 0 := by
  have hzero : testedInteraction (m₁ - m₂) (hm₁.sub hm₂) ψ (dirac1 k) (dirac1 l) = 0 :=
    testedInteraction_eq_zero_of_real_states (hm₁.sub hm₂) ψ
      (fun U V => tested_interaction_real_targets hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC
        hτ0 hτT hobs hψ U V) _ _
  rw [testedInteraction_dirac1] at hzero
  exact (mul_eq_zero.1 hzero).resolve_left (mul_ne_zero twoPiI_ne_zero hcoeff)

/-- **The non-vacuous packaging.**  If the exterior of the measured region is nonempty there is
a frequency `n` at which the constraint above holds for *every* splitting `k + l = −n`. -/
theorem exists_symbol_mode_identity (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε) :
    ∃ n : Gam, ∀ k : Gam,
      ∑ j : Fin 2, ((n j : ℤ) : ℂ) * ((m₁ - m₂) j k + (m₁ - m₂) j (-n - k)) = 0 := by
  obtain ⟨ψ, hψ, hψ0⟩ := exists_exteriorTest_ne_zero hE
  obtain ⟨n, hn⟩ := exists_coeff_ne_zero hψ0
  refine ⟨n, fun k => ?_⟩
  have hsum : -(k + (-n - k)) = n := by abel
  have h := symbol_mode_identity hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hτ0 hτT hobs hψ
    k (-n - k) (by rw [hsum]; exact hn)
  rwa [hsum] at h

/-! ## 6. The rotated-gradient case: a reflection identity for the kernel difference -/

theorem sum_rotatedGradientSymbol (κ : Gam → ℂ) (n k : Gam) :
    ∑ j : Fin 2, ((n j : ℤ) : ℂ) * rotatedGradientSymbol κ j k
      = twoPiI * κ k
          * (((n 1 : ℤ) : ℂ) * ((k 0 : ℤ) : ℂ) - ((n 0 : ℤ) : ℂ) * ((k 1 : ℤ) : ℂ)) := by
  rw [Fin.sum_univ_two, rotatedGradientSymbol_zero_comp, rotatedGradientSymbol_one_comp]
  ring

/-- **A reflection identity for the Fourier coefficients of the kernel difference.**

For the paper's rotated-gradient symbols `m_i = ∇^⊥(K_i * ·)` there is a frequency `n` — any
frequency at which some exterior test has a nonzero Fourier coefficient — such that the Fourier
coefficients of `K₁ − K₂` are invariant under the reflection `k ↦ −n − k`, at every `k` not
parallel to `n`.

This is derived, not assumed: it follows from the proved approximation theorem through
`symbol_mode_identity`.  It is **not** the paper's operator-recovery conclusion — no claim is
made here that it forces `K₁ = K₂`. -/
theorem kernel_reflection_identity (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε) :
    ∃ n : Gam, ∀ k : Gam,
      ((n 1 : ℤ) : ℂ) * ((k 0 : ℤ) : ℂ) - ((n 0 : ℤ) : ℂ) * ((k 1 : ℤ) : ℂ) ≠ 0 →
        κ₁ k - κ₂ k = κ₁ (-n - k) - κ₂ (-n - k) := by
  have hdiff : rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂
      = rotatedGradientSymbol (κ₁ - κ₂) := (rotatedGradientSymbol_sub κ₁ κ₂).symm
  have hdiv : IsDivFreeSymbol (rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) := by
    rw [hdiff]; exact rotatedGradientSymbol_isDivFree _
  obtain ⟨n, hn⟩ := exists_symbol_mode_identity hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC
    hτ0 hτT hobs
  refine ⟨n, fun k hD => ?_⟩
  have h := hn k
  rw [hdiff] at h
  have hsplit : ∑ j : Fin 2, ((n j : ℤ) : ℂ)
        * (rotatedGradientSymbol (κ₁ - κ₂) j k + rotatedGradientSymbol (κ₁ - κ₂) j (-n - k))
      = (∑ j : Fin 2, ((n j : ℤ) : ℂ) * rotatedGradientSymbol (κ₁ - κ₂) j k)
        + ∑ j : Fin 2, ((n j : ℤ) : ℂ) * rotatedGradientSymbol (κ₁ - κ₂) j (-n - k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, sum_rotatedGradientSymbol, sum_rotatedGradientSymbol] at h
  have hD2 : ((n 1 : ℤ) : ℂ) * (((-n - k) 0 : ℤ) : ℂ)
        - ((n 0 : ℤ) : ℂ) * (((-n - k) 1 : ℤ) : ℂ)
      = -(((n 1 : ℤ) : ℂ) * ((k 0 : ℤ) : ℂ) - ((n 0 : ℤ) : ℂ) * ((k 1 : ℤ) : ℂ)) := by
    have e0 : ((-n - k) 0 : ℤ) = -(n 0) - k 0 := rfl
    have e1 : ((-n - k) 1 : ℤ) = -(n 1) - k 1 := rfl
    rw [e0, e1]
    push_cast
    ring
  rw [hD2] at h
  have hk : (κ₁ - κ₂) k = κ₁ k - κ₂ k := rfl
  have hk' : (κ₁ - κ₂) (-n - k) = κ₁ (-n - k) - κ₂ (-n - k) := rfl
  rw [hk, hk'] at h
  have hmain : ((κ₁ k - κ₂ k) - (κ₁ (-n - k) - κ₂ (-n - k)))
      * (twoPiI * (((n 1 : ℤ) : ℂ) * ((k 0 : ℤ) : ℂ)
          - ((n 0 : ℤ) : ℂ) * ((k 1 : ℤ) : ℂ))) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 hmain with h1 | h2
  · exact sub_eq_zero.1 h1
  · exact absurd h2 (mul_ne_zero twoPiI_ne_zero hD)

end LiWang.Formalization
