/-
# Physical Fourier synthesis on the two-torus

Given absolutely summable Fourier coefficients `a : Wiener` we build the continuous function

  `synth a (x) = ∑' k, a k · e_k(x)`,   `e_k(x) = exp(2πi k·x)`

on the normalised two-torus `𝕋² = ℝ²/ℤ²`, and show that `synth` is a bounded complex
linear map `Wiener →L[ℂ] C(𝕋², ℂ)` of norm at most one.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Examples
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## The normalised two-torus and its Fourier monomials -/

/-- The normalised circle `𝕋 = ℝ/ℤ`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

/-- The normalised two-torus `𝕋² = ℝ²/ℤ²`. -/
abbrev Torus2 : Type := Fin 2 → Circ

example : CompactSpace Torus2 := inferInstance
noncomputable example : NormedRing C(Torus2, ℂ) := inferInstance
example : CompleteSpace C(Torus2, ℂ) := inferInstance

theorem norm_fourier_apply (n : ℤ) (x : Circ) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- Coordinate projection `𝕋² → 𝕋` as a continuous map. -/
def torusCoord (j : Fin 2) : C(Torus2, Circ) := ⟨fun x => x j, continuous_apply j⟩

/-- The Fourier monomial `e_k(x) = exp(2πi k·x)` on the two-torus. -/
noncomputable def emode (k : Gam) : C(Torus2, ℂ) :=
  (fourier (k 0)).comp (torusCoord 0) * (fourier (k 1)).comp (torusCoord 1)

@[simp] theorem emode_apply (k : Gam) (x : Torus2) :
    emode k x = fourier (k 0) (x 0) * fourier (k 1) (x 1) := rfl

theorem norm_emode_apply (k : Gam) (x : Torus2) : ‖emode k x‖ = 1 := by
  rw [emode_apply, norm_mul, norm_fourier_apply, norm_fourier_apply, one_mul]

theorem norm_emode_le (k : Gam) : ‖emode k‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun x => (norm_emode_apply k x).le

theorem norm_emode (k : Gam) : ‖emode k‖ = 1 := by
  refine le_antisymm (norm_emode_le k) ?_
  have h := (emode k).norm_coe_le_norm (0 : Torus2)
  rwa [norm_emode_apply] at h

@[simp] theorem emode_zero : emode (0 : Gam) = 1 := by
  ext x
  show fourier ((0 : Gam) 0) (x 0) * fourier ((0 : Gam) 1) (x 1) = 1
  show fourier (0 : ℤ) (x 0) * fourier (0 : ℤ) (x 1) = 1
  rw [fourier_zero, fourier_zero, one_mul]

/-- The monomials multiply: `e_k · e_l = e_{k+l}`.  This is the algebraic heart of the
convolution–product theorem. -/
theorem emode_add_apply (k l : Gam) (x : Torus2) :
    emode (k + l) x = emode k x * emode l x := by
  show fourier ((k + l) 0) (x 0) * fourier ((k + l) 1) (x 1)
      = (fourier (k 0) (x 0) * fourier (k 1) (x 1))
        * (fourier (l 0) (x 0) * fourier (l 1) (x 1))
  have h0 : (k + l) 0 = k 0 + l 0 := rfl
  have h1 : (k + l) 1 = k 1 + l 1 := rfl
  rw [h0, h1, fourier_add, fourier_add]
  ring

theorem emode_add (k l : Gam) : emode (k + l) = emode k * emode l := by
  ext x; exact emode_add_apply k l x

theorem emode_neg_apply (k : Gam) (x : Torus2) : emode (-k) x = conj (emode k x) := by
  show fourier ((-k) 0) (x 0) * fourier ((-k) 1) (x 1)
      = conj (fourier (k 0) (x 0) * fourier (k 1) (x 1))
  have h0 : ((-k) 0 : ℤ) = -(k 0) := rfl
  have h1 : ((-k) 1 : ℤ) = -(k 1) := rfl
  rw [h0, h1, fourier_neg, fourier_neg, map_mul]

/-! ## Synthesis -/

theorem summable_synth (a : Wiener) : Summable fun k => (a k) • emode k := by
  refine Summable.of_norm_bounded (wiener_summable a) (fun k => ?_)
  rw [norm_smul]
  calc ‖a k‖ * ‖emode k‖ ≤ ‖a k‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_emode_le k) (norm_nonneg _)
    _ = ‖a k‖ := mul_one _

/-- Fourier synthesis as a linear map. -/
noncomputable def synthLm : Wiener →ₗ[ℂ] C(Torus2, ℂ) where
  toFun a := ∑' k, (a k) • emode k
  map_add' a b := by
    have h : ∀ k : Gam, ((a + b) k) • emode k = (a k) • emode k + (b k) • emode k := by
      intro k
      rw [lp.coeFn_add, Pi.add_apply]
      exact add_smul (a k) (b k) (emode k)
    rw [tsum_congr h]
    exact (summable_synth a).tsum_add (summable_synth b)
  map_smul' c a := by
    have h : ∀ k : Gam, ((c • a) k) • emode k = c • ((a k) • emode k) := by
      intro k
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
    rw [RingHom.id_apply, tsum_congr h]
    exact (summable_synth a).tsum_const_smul c

theorem norm_synthLm_le (a : Wiener) : ‖synthLm a‖ ≤ ‖a‖ := by
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (wiener_summable a)
    rw [norm_smul]
    calc ‖a k‖ * ‖emode k‖ ≤ ‖a k‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_emode_le k) (norm_nonneg _)
      _ = ‖a k‖ := mul_one _
  · rw [wiener_norm_eq]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ (wiener_summable a)
    · rw [norm_smul, norm_emode, mul_one]
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (wiener_summable a)
      rw [norm_smul, norm_emode, mul_one]

/-- **Physical Fourier synthesis** `Wiener →L[ℂ] C(𝕋², ℂ)`, of operator norm at most one. -/
noncomputable def synth : Wiener →L[ℂ] C(Torus2, ℂ) :=
  LinearMap.mkContinuous synthLm 1 (fun a => by rw [one_mul]; exact norm_synthLm_le a)

theorem synth_def (a : Wiener) : synth a = ∑' k, (a k) • emode k := rfl

/-- **The uniform norm bound** `‖synth a‖_∞ ≤ ‖a‖_{ℓ¹}`. -/
theorem norm_synth_apply_le (a : Wiener) : ‖synth a‖ ≤ ‖a‖ := norm_synthLm_le a

theorem norm_synth_le : ‖synth‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem summable_synth_pointwise (a : Wiener) (x : Torus2) :
    Summable fun k => a k * emode k x := by
  refine Summable.of_norm_bounded (wiener_summable a) (fun k => ?_)
  rw [norm_mul, norm_emode_apply, mul_one]

/-- The pointwise formula for the synthesized function. -/
theorem synth_apply (a : Wiener) (x : Torus2) : synth a x = ∑' k, a k * emode k x := by
  have h := ContinuousLinearMap.map_tsum (ContinuousMap.evalCLM ℂ x) (summable_synth a)
  show (ContinuousMap.evalCLM ℂ x) (∑' k, (a k) • emode k) = _
  rw [h]
  exact tsum_congr fun k => rfl

/-! ## Synthesis of the elementary operations -/

@[simp] theorem synth_zero : synth (0 : Wiener) = 0 := map_zero synth
theorem synth_add (a b : Wiener) : synth (a + b) = synth a + synth b := map_add synth a b
theorem synth_sub (a b : Wiener) : synth (a - b) = synth a - synth b := map_sub synth a b
theorem synth_smul (c : ℂ) (a : Wiener) : synth (c • a) = c • synth a := map_smul synth c a

/-! ## Explicit finite-mode tests -/

/-- A single Dirac coefficient synthesizes to the corresponding monomial. -/
@[simp] theorem synth_wdirac (k₀ : Gam) : synth (wdirac k₀) = emode k₀ := by
  have h : ∀ k : Gam, (wdirac k₀ k) • emode k = if k = k₀ then emode k₀ else 0 := by
    intro k
    by_cases hk : k = k₀
    · subst hk; simp [wdirac, diracFun]
    · rw [if_neg hk]
      show (if k = k₀ then (1 : ℂ) else 0) • emode k = 0
      rw [if_neg hk]
      exact zero_smul ℂ (emode k)
  rw [synth_def, tsum_congr h]
  exact tsum_ite_eq k₀ (fun _ => emode k₀)

theorem synth_wdirac_apply (k₀ : Gam) (x : Torus2) :
    synth (wdirac k₀) x = fourier (k₀ 0) (x 0) * fourier (k₀ 1) (x 1) := by
  rw [synth_wdirac]; rfl

/-- A two-mode test: the synthesis of `δ_{k₀} + δ_{k₁}` is `e_{k₀} + e_{k₁}`. -/
theorem synth_two_modes (k₀ k₁ : Gam) :
    synth (wdirac k₀ + wdirac k₁) = emode k₀ + emode k₁ := by
  rw [synth_add, synth_wdirac, synth_wdirac]

theorem synth_zero_mode : synth (wdirac (0 : Gam)) = 1 := by
  rw [synth_wdirac, emode_zero]

end LiWang.WienerModel
