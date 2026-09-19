/-
# Recovery of the Fourier coefficients, and injectivity of synthesis

The coefficient functionals `F ↦ ∫_{𝕋²} F(x) \overline{e_k(x)} dx` are bounded linear
functionals on `C(𝕋², ℂ)` which recover the Wiener coefficients from the synthesized
function.  Consequently `synth` is injective.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Lift
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

instance : IsProbabilityMeasure (volume : Measure Circ) :=
  ⟨by rw [AddCircle.measure_univ]; simp⟩

/-! ## Orthogonality of the monomials -/

/-- `∫_{𝕋} e^{2πinx} dx = δ_{n,0}`. -/
theorem integral_fourier (n : ℤ) :
    (∫ x : Circ, fourier n x) = if n = 0 then 1 else 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have hcongr : ∀ x : ℝ, fourier n ((x : ℝ) : Circ)
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ)) := by
      intro x
      rw [fourier_coe_apply]
      norm_num
    rw [intervalIntegral.integral_congr (fun x _ => hcongr x), integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (((0 : ℝ) + 1 : ℝ) : ℂ))
        = 1 := by
      rw [show ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (((0 : ℝ) + 1 : ℝ) : ℂ))
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    have h0 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [h1, h0, sub_self, zero_div]

theorem emode_eq_prod (k : Gam) (x : Torus2) :
    emode k x = ∏ i : Fin 2, fourier (k i) (x i) := by
  rw [Fin.prod_univ_two]; rfl

/-- `∫_{𝕋²} e_k(x) dx = δ_{k,0}`. -/
theorem integral_emode (k : Gam) :
    (∫ x : Torus2, emode k x) = if k = 0 then 1 else 0 := by
  have hprod : (∫ x : Torus2, ∏ i : Fin 2, fourier (k i) (x i))
      = ∏ i : Fin 2, ∫ z : Circ, fourier (k i) z := by
    rw [volume_pi]
    exact integral_fintype_prod_eq_prod (fun i (z : Circ) => fourier (k i) z)
  have hcongr : (∫ x : Torus2, emode k x) = ∫ x : Torus2, ∏ i : Fin 2, fourier (k i) (x i) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => emode_eq_prod k x)
  rw [hcongr, hprod]
  have hi : ∀ i : Fin 2, (∫ z : Circ, fourier (k i) z) = if k i = 0 then 1 else 0 :=
    fun i => integral_fourier (k i)
  rw [Fin.prod_univ_two, hi 0, hi 1]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have : ¬ (k 0 = 0 ∧ k 1 = 0) := by
      intro h
      apply hk
      funext i
      fin_cases i
      · exact h.1
      · exact h.2
    rcases not_and_or.1 this with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

/-! ## The coefficient functionals -/

theorem integrable_continuousMap (F : C(Torus2, ℂ)) : Integrable F (volume : Measure Torus2) :=
  F.continuous.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ
    isClosed_closure (Set.subset_univ _))

theorem integrable_mul_emode (F : C(Torus2, ℂ)) (k : Gam) :
    Integrable (fun x : Torus2 => F x * emode k x) (volume : Measure Torus2) := by
  have h := integrable_continuousMap (F * emode k)
  simpa only [ContinuousMap.coe_mul, Pi.mul_apply] using h

/-- The `k`-th coefficient functional on `C(𝕋², ℂ)`. -/
noncomputable def coeffLm (k : Gam) : C(Torus2, ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∫ x : Torus2, F x * emode (-k) x
  map_add' F G := by
    show (∫ x : Torus2, (F + G) x * emode (-k) x)
        = (∫ x : Torus2, F x * emode (-k) x) + ∫ x : Torus2, G x * emode (-k) x
    rw [← integral_add (integrable_mul_emode F (-k)) (integrable_mul_emode G (-k))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show (F x + G x) * emode (-k) x = F x * emode (-k) x + G x * emode (-k) x
      ring)
  map_smul' c F := by
    show (∫ x : Torus2, (c • F) x * emode (-k) x) = c • ∫ x : Torus2, F x * emode (-k) x
    have hcg : (∫ x : Torus2, (c • F) x * emode (-k) x)
        = ∫ x : Torus2, c • (F x * emode (-k) x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show (c • F x) * emode (-k) x = c • (F x * emode (-k) x)
        simp only [smul_eq_mul]; ring)
    rw [hcg]
    exact integral_smul c (fun x : Torus2 => F x * emode (-k) x)

theorem norm_coeffLm_le (k : Gam) (F : C(Torus2, ℂ)) : ‖coeffLm k F‖ ≤ ‖F‖ := by
  have hb : ∀ x : Torus2, ‖F x * emode (-k) x‖ ≤ ‖F‖ := by
    intro x
    rw [norm_mul, norm_emode_apply, mul_one]
    exact F.norm_coe_le_norm x
  have h := norm_integral_le_of_norm_le_const (C := ‖F‖) (μ := (volume : Measure Torus2))
    (f := fun x : Torus2 => F x * emode (-k) x) (Filter.Eventually.of_forall hb)
  show ‖∫ x : Torus2, F x * emode (-k) x‖ ≤ ‖F‖
  have hu : (volume : Measure Torus2).real Set.univ = 1 := by
    simp [MeasureTheory.Measure.real, measure_univ]
  rwa [hu, mul_one] at h

/-- The `k`-th coefficient functional as a bounded linear functional. -/
noncomputable def coeffCLM (k : Gam) : C(Torus2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous (coeffLm k) 1 (fun F => by rw [one_mul]; exact norm_coeffLm_le k F)

theorem coeffCLM_apply (k : Gam) (F : C(Torus2, ℂ)) :
    coeffCLM k F = ∫ x : Torus2, F x * emode (-k) x := rfl

theorem coeffCLM_emode (k l : Gam) : coeffCLM k (emode l) = if l = k then 1 else 0 := by
  rw [coeffCLM_apply]
  have hc : ∀ x : Torus2, emode l x * emode (-k) x = emode (l - k) x := by
    intro x
    rw [← emode_add_apply]
    congr 1
    try abel
  rw [integral_congr_ae (Filter.Eventually.of_forall hc), integral_emode]
  by_cases h : l = k
  · subst h; simp
  · have h' : ¬ (l - k = (0 : Gam)) := fun hc' => h (by rwa [sub_eq_zero] at hc')
    rw [if_neg h, if_neg h']

/-! ## Coefficient recovery and injectivity -/

/-- **Recovery of every Fourier coefficient.** -/
theorem coeffCLM_synth (a : Wiener) (k : Gam) : coeffCLM k (synth a) = a k := by
  rw [synth_def, ContinuousLinearMap.map_tsum _ (summable_synth a)]
  have hterm : ∀ l : Gam, coeffCLM k ((a l) • emode l) = if l = k then a k else 0 := by
    intro l
    rw [map_smul, coeffCLM_emode]
    by_cases h : l = k
    · subst h; simp
    · simp only [if_neg h, smul_zero]
  rw [tsum_congr hterm]
  exact tsum_ite_eq k (fun _ => a k)

/-- **Synthesis is injective**: a Wiener element is determined by the continuous function it
synthesizes. -/
theorem synth_injective : Function.Injective (synth : Wiener → C(Torus2, ℂ)) := by
  intro a b h
  ext k
  have := congrArg (coeffCLM k) h
  rwa [coeffCLM_synth, coeffCLM_synth] at this

theorem synth_eq_zero_iff (a : Wiener) : synth a = 0 ↔ a = 0 :=
  ⟨fun h => synth_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- **Real synthesis is injective.** -/
theorem realSynth_injective : Function.Injective (realSynth : RealWiener → C(Torus2, ℝ)) := by
  intro a b h
  apply RealWiener.val_injective
  apply synth_injective
  ext x
  have hx : realSynth a x = realSynth b x := by rw [h]
  have ha := ofReal_realSynth a x
  have hb := ofReal_realSynth b x
  rw [← ha, ← hb, hx]

end LiWang.WienerModel
