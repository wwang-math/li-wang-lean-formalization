/-
# Trigonometric-polynomial test functions on the two-torus

The coefficient functionals of `Coefficients.lean` already realise
`∫_{𝕋²} F(x) e_{-k}(x) dx` as bounded functionals recovering the Wiener coefficients.  Here we
package the *finite spatial Fourier test functions* used by the weak formulation: finite
trigonometric polynomials, their fractional Laplacians (which are again finite trigonometric
polynomials, so no regularity of the state is needed), and the exact value of the spatial
pairing of a synthesized Wiener state against such a test function.

Part of `LiWangWienerSourceResponsePacket` v3.0.
-/
import LiWangWiener.Coefficients
import LiWangWiener.FractionalHeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

/-! ## Finite trigonometric polynomials -/

/-- A finite trigonometric polynomial `∑_{k ∈ F} c_k e_k`, as a continuous function of the
torus.  These are the *finite spatial Fourier test functions*. -/
noncomputable def trigPoly (F : Finset Gam) (c : Gam → ℂ) : C(Torus2, ℂ) :=
  ∑ k ∈ F, c k • emode k

theorem trigPoly_apply (F : Finset Gam) (c : Gam → ℂ) (x : Torus2) :
    trigPoly F c x = ∑ k ∈ F, c k * emode k x := by
  rw [trigPoly]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

/-- The fractional Laplacian `(-Δ)^α` of a trigonometric polynomial is again a trigonometric
polynomial with the same finite frequency set.  Applying the dissipation to the *test
function* is what allows the weak formulation to avoid any additional regularity of the
state. -/
noncomputable def fracLapPoly (α : ℝ) (F : Finset Gam) (c : Gam → ℂ) : C(Torus2, ℂ) :=
  trigPoly F (fun k => (fracSymbol α k : ℂ) * c k)

theorem fracLapPoly_apply (α : ℝ) (F : Finset Gam) (c : Gam → ℂ) (x : Torus2) :
    fracLapPoly α F c x = ∑ k ∈ F, (fracSymbol α k : ℂ) * c k * emode k x := by
  rw [fracLapPoly, trigPoly_apply]

/-- The fractional symbol is even. -/
theorem fracSymbol_neg (α : ℝ) (k : Gam) : fracSymbol α (-k) = fracSymbol α k := by
  have h : sqNorm (-k) = sqNorm k := by
    show (((-k) 0 : ℤ) : ℝ) ^ 2 + (((-k) 1 : ℤ) : ℝ) ^ 2
        = ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2
    have h0 : ((-k) 0 : ℤ) = -(k 0) := rfl
    have h1 : ((-k) 1 : ℤ) = -(k 1) := rfl
    rw [h0, h1]
    push_cast
    ring
  rw [fracSymbol, fracSymbol, h]

/-! ## Spatial pairing of a synthesized state with a test polynomial -/

/-- Pairing a synthesized Wiener state with a single monomial. -/
theorem integral_synth_mul_emode (a : Wiener) (j : Gam) :
    (∫ x : Torus2, synth a x * emode j x) = a (-j) := by
  have h := coeffCLM_synth a (-j)
  rw [coeffCLM_apply, neg_neg] at h
  exact h

/-- **The spatial pairing against a finite Fourier test function** is an explicit finite sum of
Fourier coefficients. -/
theorem integral_synth_mul_trigPoly (a : Wiener) (F : Finset Gam) (c : Gam → ℂ) :
    (∫ x : Torus2, synth a x * trigPoly F c x) = ∑ j ∈ F, c j * a (-j) := by
  have hexp : ∀ x : Torus2, synth a x * trigPoly F c x
      = ∑ j ∈ F, c j * (synth a x * emode j x) := by
    intro x
    rw [trigPoly_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [MeasureTheory.integral_finset_sum F (fun j _ =>
    ((integrable_mul_emode (synth a) j).const_mul (c j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcm := MeasureTheory.integral_const_mul (μ := (volume : Measure Torus2)) (c j)
    (fun x : Torus2 => synth a x * emode j x)
  exact hcm.trans (congrArg (fun z : ℂ => c j * z) (integral_synth_mul_emode a j))

/-! ## Pairing against an arbitrary continuous test function -/

/-- Integration against a fixed continuous function, as a bounded linear functional on
`C(𝕋², ℂ)`.  This is what licenses exchanging the (uniformly convergent) synthesis series with
the integral against a general continuous test function. -/
noncomputable def pairCLM (P : C(Torus2, ℂ)) : C(Torus2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x : Torus2, F x * P x
      map_add' := fun F G => by
        have h : ∀ x : Torus2, (F + G) x * P x = F x * P x + G x * P x := fun x => by
          simp only [ContinuousMap.add_apply]; ring
        show (∫ x : Torus2, (F + G) x * P x) = _
        rw [integral_congr_ae (Filter.Eventually.of_forall h)]
        exact integral_add (integrable_continuousMap (F * P)) (integrable_continuousMap (G * P))
      map_smul' := fun c F => by
        have h : ∀ x : Torus2, (c • F) x * P x = c * (F x * P x) := fun x => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
        show (∫ x : Torus2, (c • F) x * P x) = c • ∫ x : Torus2, F x * P x
        rw [integral_congr_ae (Filter.Eventually.of_forall h), smul_eq_mul]
        exact integral_const_mul c (fun x : Torus2 => F x * P x) }
    ‖P‖ (fun F => by
      have h := MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := (volume : Measure Torus2)) (C := ‖F‖ * ‖P‖) (f := fun x : Torus2 => F x * P x)
        (Filter.Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul (F.norm_coe_le_norm x) (P.norm_coe_le_norm x) (norm_nonneg _)
            (norm_nonneg _))
      show ‖∫ x : Torus2, F x * P x‖ ≤ ‖P‖ * ‖F‖
      have hu : (volume : Measure Torus2).real Set.univ = 1 := by
        simp [MeasureTheory.Measure.real, measure_univ]
      rw [hu, mul_one] at h
      linarith [h, le_of_eq (mul_comm ‖F‖ ‖P‖)])

@[simp] theorem pairCLM_apply (P F : C(Torus2, ℂ)) :
    pairCLM P F = ∫ x : Torus2, F x * P x := rfl

/-- **Term-by-term pairing of a synthesized state with a continuous test function.** -/
theorem integral_synth_mul (a : Wiener) (P : C(Torus2, ℂ)) :
    (∫ x : Torus2, synth a x * P x) = ∑' k : Gam, a k * ∫ x : Torus2, emode k x * P x := by
  have h := ContinuousLinearMap.map_tsum (pairCLM P) (summable_synth a)
  calc (∫ x : Torus2, synth a x * P x)
      = pairCLM P (∑' k : Gam, (a k) • emode k) := congrArg (pairCLM P) (synth_def a)
    _ = ∑' k : Gam, pairCLM P ((a k) • emode k) := h
    _ = ∑' k : Gam, a k * ∫ x : Torus2, emode k x * P x := by
        refine tsum_congr fun k => ?_
        rw [map_smul, smul_eq_mul, pairCLM_apply]

end LiWang.WienerModel
