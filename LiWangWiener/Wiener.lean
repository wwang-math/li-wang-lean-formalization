/-
The Wiener algebra `A(𝕋²) = ℓ¹(Γ)` on the frequency lattice `Γ = ℤ²`, and the discrete
convolution with its `ℓ¹` estimate.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 1. The frequency lattice and the Wiener algebra -/

/-- The frequency lattice `Γ = ℤ²` dual to the two–dimensional torus `𝕋² = ℝ²/ℤ²`. -/
abbrev Gam : Type := Fin 2 → ℤ

/-- The **Wiener algebra** `A(𝕋²)`, realized as the space `ℓ¹(Γ, ℂ)` of absolutely
summable complex Fourier coefficients. It is a complex Banach space. -/
abbrev Wiener : Type := lp (fun _ : Gam => ℂ) 1

example : CompleteSpace Wiener := inferInstance
noncomputable example : NormedSpace ℂ Wiener := inferInstance

/-- The Wiener norm is the sum of the absolute values of the Fourier coefficients. -/
theorem wiener_norm_eq (a : Wiener) : ‖a‖ = ∑' k, ‖a k‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]; simp

/-- Fourier coefficients of a Wiener element are absolutely summable. -/
theorem wiener_summable (a : Wiener) : Summable fun k => ‖a k‖ := by
  have := (lp.memℓp a).summable (p := 1) (by norm_num)
  simpa using this

theorem wiener_norm_apply_le (a : Wiener) (k : Gam) : ‖a k‖ ≤ ‖a‖ :=
  lp.norm_apply_le_norm one_ne_zero a k

/-- Membership in the Wiener algebra is exactly absolute summability. -/
theorem memWiener_iff (f : Gam → ℂ) : Memℓp f 1 ↔ Summable fun k => ‖f k‖ := by
  constructor
  · intro h; simpa using h.summable (p := 1) (by norm_num)
  · intro h; exact memℓp_gen (by simpa using h)

/-- Build a Wiener element out of an absolutely summable coefficient family. -/
noncomputable def wmk (f : Gam → ℂ) (hf : Summable fun k => ‖f k‖) : Wiener :=
  ⟨f, memℓp_gen (by simpa using hf)⟩

@[simp] theorem wmk_apply (f : Gam → ℂ) (hf : Summable fun k => ‖f k‖) (k : Gam) :
    (wmk f hf) k = f k := rfl

/-! ## 2. Discrete convolution -/

/-- The shear automorphism `(k, p) ↦ (p, k - p)` of `Γ × Γ`; it converts a product sum
into a convolution sum. -/
def shear : Gam × Gam ≃ Gam × Gam where
  toFun z := (z.2, z.1 - z.2)
  invFun w := (w.1 + w.2, w.1)
  left_inv z := by simp
  right_inv w := by simp

variable {a b : Gam → ℂ}

/-- Absolute summability of the two–variable convolution kernel. -/
theorem summable_shear (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable fun z : Gam × Gam => ‖a z.2 * b (z.1 - z.2)‖ := by
  have h : Summable fun z : Gam × Gam => ‖a z.1 * b z.2‖ := ha.mul_norm hb
  have h2 := (Equiv.summable_iff (f := fun z : Gam × Gam => ‖a z.1 * b z.2‖) shear).mpr h
  simpa [Function.comp, shear] using h2

theorem tsum_shear (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    ∑' z : Gam × Gam, ‖a z.2 * b (z.1 - z.2)‖ = (∑' k, ‖a k‖) * (∑' k, ‖b k‖) := by
  have e1 := Equiv.tsum_eq shear (fun z : Gam × Gam => ‖a z.1 * b z.2‖)
  have hprod : Summable fun z : Gam × Gam => ‖a z.1‖ * ‖b z.2‖ :=
    ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have e2 : (∑' k, ‖a k‖) * (∑' k, ‖b k‖) = ∑' z : Gam × Gam, ‖a z.1‖ * ‖b z.2‖ :=
    ha.tsum_mul_tsum hb hprod
  simp only [shear, Equiv.coe_fn_mk] at e1
  simp only [norm_mul] at e1 ⊢
  rw [e1, e2]

/-- The convolution of two coefficient families, `(a ⋆ b)(k) = ∑' p, a(p) b(k - p)`. -/
noncomputable def convFun (a b : Gam → ℂ) : Gam → ℂ := fun k => ∑' p, a p * b (k - p)

/-- **The defining convolution sum is absolutely summable.** -/
theorem summable_convFun_norm (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖)
    (k : Gam) : Summable fun p => ‖a p * b (k - p)‖ :=
  (summable_shear ha hb).prod_factor k

/-- **The defining convolution sum is summable.** -/
theorem summable_convFun (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖)
    (k : Gam) : Summable fun p => a p * b (k - p) :=
  (summable_convFun_norm ha hb k).of_norm

theorem summable_tsum_norm (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable fun k => ∑' p, ‖a p * b (k - p)‖ :=
  (summable_shear ha hb).prod

theorem norm_convFun_le (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) (k : Gam) :
    ‖convFun a b k‖ ≤ ∑' p, ‖a p * b (k - p)‖ :=
  norm_tsum_le_tsum_norm (summable_convFun_norm ha hb k)

/-- **The convolution belongs to the Wiener space.** -/
theorem summable_norm_convFun (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable fun k => ‖convFun a b k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_convFun_le ha hb k)
    (summable_tsum_norm ha hb)

theorem memWiener_convFun (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Memℓp (convFun a b) 1 :=
  (memWiener_iff _).2 (summable_norm_convFun ha hb)

/-- **Young's inequality for `ℓ¹`, coefficient form.** -/
theorem tsum_norm_convFun_le (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    ∑' k, ‖convFun a b k‖ ≤ (∑' k, ‖a k‖) * (∑' k, ‖b k‖) := by
  calc ∑' k, ‖convFun a b k‖
      ≤ ∑' k, ∑' p, ‖a p * b (k - p)‖ :=
        Summable.tsum_le_tsum (fun k => norm_convFun_le ha hb k) (summable_norm_convFun ha hb)
          (summable_tsum_norm ha hb)
    _ = ∑' z : Gam × Gam, ‖a z.2 * b (z.1 - z.2)‖ := ((summable_shear ha hb).tsum_prod).symm
    _ = (∑' k, ‖a k‖) * (∑' k, ‖b k‖) := tsum_shear ha hb

/-- Convolution as an operation on the Wiener algebra. -/
noncomputable def conv (a b : Wiener) : Wiener :=
  wmk (convFun a b) (summable_norm_convFun (wiener_summable a) (wiener_summable b))

@[simp] theorem conv_apply (a b : Wiener) (k : Gam) : conv a b k = ∑' p, a p * b (k - p) := rfl

/-- **The convolution norm estimate** `‖a ⋆ b‖₁ ≤ ‖a‖₁ ‖b‖₁`. -/
theorem norm_conv_le (a b : Wiener) : ‖conv a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [wiener_norm_eq, wiener_norm_eq a, wiener_norm_eq b]
  exact tsum_norm_convFun_le (wiener_summable a) (wiener_summable b)

/-! ### Bilinearity of the convolution -/

theorem conv_add_left (a₁ a₂ b : Wiener) : conv (a₁ + a₂) b = conv a₁ b + conv a₂ b := by
  ext k
  have h₁ := summable_convFun (wiener_summable a₁) (wiener_summable b) k
  have h₂ := summable_convFun (wiener_summable a₂) (wiener_summable b) k
  simp only [conv_apply, lp.coeFn_add, Pi.add_apply]
  rw [← Summable.tsum_add h₁ h₂]
  exact tsum_congr fun p => by ring

theorem conv_smul_left (c : ℂ) (a b : Wiener) : conv (c • a) b = c • conv a b := by
  ext k
  simp only [conv_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem conv_add_right (a b₁ b₂ : Wiener) : conv a (b₁ + b₂) = conv a b₁ + conv a b₂ := by
  ext k
  have h₁ := summable_convFun (wiener_summable a) (wiener_summable b₁) k
  have h₂ := summable_convFun (wiener_summable a) (wiener_summable b₂) k
  simp only [conv_apply, lp.coeFn_add, Pi.add_apply]
  rw [← Summable.tsum_add h₁ h₂]
  exact tsum_congr fun p => by ring

theorem conv_smul_right (c : ℂ) (a b : Wiener) : conv a (c • b) = c • conv a b := by
  ext k
  simp only [conv_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun p => by ring

/-- Convolution as a `ℂ`-bilinear map. -/
noncomputable def convL : Wiener →ₗ[ℂ] Wiener →ₗ[ℂ] Wiener :=
  LinearMap.mk₂ ℂ conv conv_add_left conv_smul_left conv_add_right conv_smul_right

@[simp] theorem convL_apply (a b : Wiener) : convL a b = conv a b := rfl

/-- **Convolution is represented by a continuous bilinear map** of norm at most `1`. -/
noncomputable def convCLM : Wiener →L[ℂ] Wiener →L[ℂ] Wiener :=
  LinearMap.mkContinuous₂ convL 1 (fun a b => by simpa using norm_conv_le a b)

@[simp] theorem convCLM_apply (a b : Wiener) : convCLM a b = conv a b := rfl

theorem norm_convCLM_le : ‖convCLM‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem conv_sub_left (a₁ a₂ b : Wiener) : conv (a₁ - a₂) b = conv a₁ b - conv a₂ b := by
  have h := map_sub convCLM a₁ a₂
  calc conv (a₁ - a₂) b = convCLM (a₁ - a₂) b := rfl
    _ = (convCLM a₁ - convCLM a₂) b := by rw [h]
    _ = conv a₁ b - conv a₂ b := rfl

end LiWang.WienerModel
