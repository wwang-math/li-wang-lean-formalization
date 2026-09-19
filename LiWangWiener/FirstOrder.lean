/-
The first-order Wiener space `A¹(𝕋²)` (weighted `ℓ¹`, weight `1 + |k₀| + |k₁|`), the
continuous inclusion `A¹ ↪ A`, and the Fourier derivatives `∂ⱼ a (k) = 2πi kⱼ a(k)`.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangWiener.Wiener
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 3. The first-order Wiener space -/

/-- The first-order weight `⟨k⟩₁ = 1 + |k₀| + |k₁|`. -/
noncomputable def wt (k : Gam) : ℝ := 1 + |(k 0 : ℝ)| + |(k 1 : ℝ)|

theorem one_le_wt (k : Gam) : 1 ≤ wt k := by
  have h0 := abs_nonneg ((k 0 : ℝ)); have h1 := abs_nonneg ((k 1 : ℝ))
  simp only [wt]; linarith

theorem wt_pos (k : Gam) : 0 < wt k := lt_of_lt_of_le zero_lt_one (one_le_wt k)

theorem wt_ne_zero (k : Gam) : wt k ≠ 0 := (wt_pos k).ne'

theorem abs_coe_le_wt (j : Fin 2) (k : Gam) : |(k j : ℝ)| ≤ wt k := by
  have h0 := abs_nonneg ((k 0 : ℝ)); have h1 := abs_nonneg ((k 1 : ℝ))
  fin_cases j
  · show |(k 0 : ℝ)| ≤ wt k
    simp only [wt]; linarith
  · show |(k 1 : ℝ)| ≤ wt k
    simp only [wt]; linarith

/-- The weighted-`ℓ¹` submodule of the (topology-free) ambient space `PreLp`. -/
def W1sub : Submodule ℂ (PreLp (fun _ : Gam => ℂ)) where
  carrier := {f | Summable fun k => wt k * ‖f k‖}
  zero_mem' := by
    show Summable fun k => wt k * ‖(0 : Gam → ℂ) k‖
    simp
  add_mem' := by
    intro f g hf hg
    show Summable fun k => wt k * ‖f k + g k‖
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
      (fun k => ?_) (hf.add hg)
    calc wt k * ‖f k + g k‖ ≤ wt k * (‖f k‖ + ‖g k‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (wt_pos k).le
      _ = wt k * ‖f k‖ + wt k * ‖g k‖ := by ring
  smul_mem' := by
    intro c f hf
    show Summable fun k => wt k * ‖c * f k‖
    have h : ∀ k : Gam, wt k * ‖c * f k‖ = ‖c‖ * (wt k * ‖f k‖) := by
      intro k; rw [norm_mul]; ring
    simpa only [h] using hf.mul_left ‖c‖

/-- The **first-order Wiener space** `A¹(𝕋²)`: coefficient families `f` with
`∑ₖ (1 + |k₀| + |k₁|) |f(k)| < ∞`. -/
abbrev Wiener1 : Type := W1sub

/-- The Fourier coefficient family of an element of the first-order Wiener space. -/
def Wiener1.coeff (u : Wiener1) : Gam → ℂ := (u : PreLp (fun _ : Gam => ℂ))

/-- Elements of the first-order space have weighted-summable coefficients. -/
theorem Wiener1.summable_wt (u : Wiener1) : Summable fun k => wt k * ‖u.coeff k‖ := u.2

theorem Wiener1.summable_coeff (u : Wiener1) : Summable fun k => ‖u.coeff k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (one_le_wt k)) u.summable_wt

@[simp] theorem Wiener1.coeff_add (u v : Wiener1) : (u + v).coeff = u.coeff + v.coeff := rfl
@[simp] theorem Wiener1.coeff_smul (c : ℂ) (u : Wiener1) : (c • u).coeff = c • u.coeff := rfl
@[simp] theorem Wiener1.coeff_zero : (0 : Wiener1).coeff = 0 := rfl

theorem Wiener1.coeff_injective : Function.Injective Wiener1.coeff := fun _ _ h => Subtype.ext h

/-- Build an element of the first-order space from a weighted-summable family. -/
def Wiener1.mk (f : Gam → ℂ) (hf : Summable fun k => wt k * ‖f k‖) : Wiener1 := ⟨f, hf⟩

@[simp] theorem Wiener1.coeff_mk (f : Gam → ℂ) (hf : Summable fun k => wt k * ‖f k‖) :
    (Wiener1.mk f hf).coeff = f := rfl

/-- A coefficient family arises from the first-order space exactly when it is
weighted-summable. -/
theorem Wiener1.exists_coeff_iff (f : Gam → ℂ) :
    (∃ u : Wiener1, u.coeff = f) ↔ Summable fun k => wt k * ‖f k‖ :=
  ⟨fun ⟨u, hu⟩ => hu ▸ u.summable_wt, fun hf => ⟨Wiener1.mk f hf, rfl⟩⟩

/-- The rescaling isomorphism onto the (unweighted) Wiener algebra; it is used only to
*induce* the weighted norm and to transport completeness. -/
noncomputable def Wiener1.toW (u : Wiener1) : Wiener :=
  wmk (fun k => (wt k : ℂ) * u.coeff k) (by
    have h : ∀ k : Gam, ‖(wt k : ℂ) * u.coeff k‖ = wt k * ‖u.coeff k‖ := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos k)]
    simpa only [h] using u.summable_wt)

@[simp] theorem Wiener1.toW_apply (u : Wiener1) (k : Gam) :
    (u.toW) k = (wt k : ℂ) * u.coeff k := rfl

noncomputable def Wiener1.toWHom : Wiener1 →+ Wiener where
  toFun := Wiener1.toW
  map_zero' := by
    ext k
    show (wt k : ℂ) * (0 : ℂ) = (0 : ℂ)
    exact mul_zero _
  map_add' u v := by
    ext k
    simp only [Wiener1.toW_apply, lp.coeFn_add, Pi.add_apply, Wiener1.coeff_add]
    ring

@[simp] theorem Wiener1.toWHom_apply (u : Wiener1) : Wiener1.toWHom u = u.toW := rfl

theorem Wiener1.toW_injective : Function.Injective Wiener1.toWHom := by
  intro u v h
  apply Wiener1.coeff_injective
  funext k
  have hk : (wt k : ℂ) * u.coeff k = (wt k : ℂ) * v.coeff k := by
    have := congrArg (fun (w : Wiener) => (w : Gam → ℂ) k) h
    simpa using this
  exact mul_left_cancel₀ (by simpa using (wt_ne_zero k)) hk

noncomputable instance : NormedAddCommGroup Wiener1 :=
  NormedAddCommGroup.induced Wiener1 Wiener Wiener1.toWHom Wiener1.toW_injective

theorem Wiener1.norm_def (u : Wiener1) : ‖u‖ = ‖u.toW‖ := rfl

/-- **The first-order Wiener norm is the weighted `ℓ¹` norm.** -/
theorem Wiener1.norm_eq (u : Wiener1) : ‖u‖ = ∑' k, wt k * ‖u.coeff k‖ := by
  rw [Wiener1.norm_def, wiener_norm_eq]
  refine tsum_congr fun k => ?_
  rw [Wiener1.toW_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos k)]

noncomputable instance : NormedSpace ℂ Wiener1 :=
  { (inferInstance : Module ℂ Wiener1) with
    norm_smul_le := by
      intro c u
      rw [Wiener1.norm_eq, Wiener1.norm_eq]
      have h : ∀ k : Gam, wt k * ‖(c • u).coeff k‖ = ‖c‖ * (wt k * ‖u.coeff k‖) := by
        intro k
        show wt k * ‖c * u.coeff k‖ = _
        rw [norm_mul]; ring
      rw [tsum_congr h, tsum_mul_left] }

theorem Wiener1.toW_surjective : Function.Surjective Wiener1.toWHom := by
  intro w
  have hmem : Summable fun k => wt k * ‖((wt k : ℂ))⁻¹ * w k‖ := by
    have h : ∀ k : Gam, wt k * ‖((wt k : ℂ))⁻¹ * w k‖ = ‖w k‖ := by
      intro k
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos k),
        ← mul_assoc, mul_inv_cancel₀ (wt_ne_zero k), one_mul]
    simpa only [h] using wiener_summable w
  refine ⟨⟨fun k => ((wt k : ℂ))⁻¹ * w k, hmem⟩, ?_⟩
  ext k
  show (wt k : ℂ) * (((wt k : ℂ))⁻¹ * w k) = w k
  have hne : (wt k : ℂ) ≠ 0 := by simpa using (wt_ne_zero k)
  field_simp

/-- The first-order Wiener space is a Banach space. -/
instance : CompleteSpace Wiener1 :=
  ((AddMonoidHomClass.isometry_of_norm Wiener1.toWHom
      (fun _ => rfl)).isUniformInducing.completeSpace_congr
    Wiener1.toW_surjective).mpr inferInstance

/-! ### The inclusion `A¹ ↪ A` -/

noncomputable def inclL : Wiener1 →ₗ[ℂ] Wiener where
  toFun u := wmk u.coeff u.summable_coeff
  map_add' _ _ := by ext k; rfl
  map_smul' _ _ := by ext k; rfl

theorem norm_inclL_le (u : Wiener1) : ‖inclL u‖ ≤ ‖u‖ := by
  rw [wiener_norm_eq, Wiener1.norm_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ u.summable_wt
  · show ‖u.coeff k‖ ≤ wt k * ‖u.coeff k‖
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_wt k)
  · exact u.summable_coeff

/-- The **continuous inclusion** of the first-order Wiener space into the Wiener algebra.
It preserves Fourier coefficients and is norm-nonincreasing. -/
noncomputable def incl : Wiener1 →L[ℂ] Wiener :=
  LinearMap.mkContinuous inclL 1 (fun u => by rw [one_mul]; exact norm_inclL_le u)

@[simp] theorem incl_apply (u : Wiener1) (k : Gam) : (incl u) k = u.coeff k := rfl

theorem norm_incl_apply_le (u : Wiener1) : ‖incl u‖ ≤ ‖u‖ := norm_inclL_le u

theorem norm_incl_le : ‖incl‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The first-order Wiener space really is a subspace of the Wiener algebra: the inclusion
is injective and preserves Fourier coefficients. -/
theorem incl_injective : Function.Injective (incl : Wiener1 → Wiener) := by
  intro u v h
  apply Wiener1.coeff_injective
  funext k
  have := congrArg (fun (w : Wiener) => (w : Gam → ℂ) k) h
  simpa using this

/-! ### Fourier derivatives -/

/-- The constant `2πi`. -/
noncomputable def twoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem norm_twoPiI : ‖twoPiI‖ = 2 * Real.pi := by
  simp [twoPiI, Complex.norm_I, abs_of_pos Real.pi_pos]

theorem twoPi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity

theorem summable_deriv (j : Fin 2) (u : Wiener1) :
    Summable fun k => ‖twoPiI * (k j : ℂ) * u.coeff k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (u.summable_wt.mul_left (2 * Real.pi))
  rw [norm_mul, norm_mul, norm_twoPiI, Complex.norm_intCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (abs_coe_le_wt j k) (norm_nonneg _)) twoPi_nonneg

/-- The `j`-th Fourier derivative as a linear map. -/
noncomputable def derivLm (j : Fin 2) : Wiener1 →ₗ[ℂ] Wiener where
  toFun u := wmk (fun k => twoPiI * (k j : ℂ) * u.coeff k) (summable_deriv j u)
  map_add' u v := by
    ext k
    have h : ((u + v : Wiener1).coeff) k = u.coeff k + v.coeff k := rfl
    simp only [wmk_apply, lp.coeFn_add, Pi.add_apply, h]
    ring
  map_smul' c u := by
    ext k
    have h : ((c • u : Wiener1).coeff) k = c * u.coeff k := rfl
    simp only [wmk_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h]
    ring

theorem norm_derivLm_le (j : Fin 2) (u : Wiener1) : ‖derivLm j u‖ ≤ 2 * Real.pi * ‖u‖ := by
  rw [wiener_norm_eq, Wiener1.norm_eq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_deriv j u)
    (u.summable_wt.mul_left (2 * Real.pi))
  show ‖twoPiI * (k j : ℂ) * u.coeff k‖ ≤ 2 * Real.pi * (wt k * ‖u.coeff k‖)
  rw [norm_mul, norm_mul, norm_twoPiI, Complex.norm_intCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (abs_coe_le_wt j k) (norm_nonneg _)) twoPi_nonneg

/-- **The Fourier derivative `∂ⱼ a (k) = 2πi kⱼ a(k)` is a bounded linear map from the
first-order Wiener space to the Wiener algebra**, of norm at most `2π`. -/
noncomputable def fourierDeriv (j : Fin 2) : Wiener1 →L[ℂ] Wiener :=
  LinearMap.mkContinuous (derivLm j) (2 * Real.pi) (norm_derivLm_le j)

@[simp] theorem fourierDeriv_apply (j : Fin 2) (u : Wiener1) (k : Gam) :
    (fourierDeriv j u) k = twoPiI * (k j : ℂ) * u.coeff k := rfl

theorem norm_fourierDeriv_apply_le (j : Fin 2) (u : Wiener1) :
    ‖fourierDeriv j u‖ ≤ 2 * Real.pi * ‖u‖ := norm_derivLm_le j u

theorem norm_fourierDeriv_le (j : Fin 2) : ‖fourierDeriv j‖ ≤ 2 * Real.pi :=
  LinearMap.mkContinuous_norm_le _ twoPi_nonneg _

end LiWang.WienerModel
