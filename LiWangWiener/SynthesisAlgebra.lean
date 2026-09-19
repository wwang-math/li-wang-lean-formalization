/-
# The convolution–product theorem

`synth (a ⋆ b) = synth a · synth b`: the discrete convolution of Fourier coefficients is
realized by the pointwise product of the synthesized functions on `𝕋²`.  Every interchange
and reindexing of infinite sums below is justified by absolute summability.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Synthesis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

theorem summable_norm_synth_pointwise (a : Wiener) (x : Torus2) :
    Summable fun k => ‖a k * emode k x‖ := by
  have h : ∀ k : Gam, ‖a k * emode k x‖ = ‖a k‖ := by
    intro k; rw [norm_mul, norm_emode_apply, mul_one]
  simpa only [h] using wiener_summable a

/-- The scalar heart of the convolution–product theorem: for any unimodular character
`χ : Γ → ℂ` (i.e. `χ(k+l) = χ(k)χ(l)` and `‖χ k‖ = 1`) the Wiener series multiply by
convolution.  Every interchange below is justified by absolute summability:
`tsum_mul_tsum_of_summable_norm` for the product, `Equiv.tsum_eq` along the shear
`(m,p) ↦ (p, m-p)` for the reindexing, and `Summable.tsum_prod` for the iterated sum. -/
theorem tsum_character_mul {a b : Wiener} {χ : Gam → ℂ}
    (hmul : ∀ k l : Gam, χ (k + l) = χ k * χ l) (hone : ∀ k, ‖χ k‖ = 1) :
    (∑' k, a k * χ k) * (∑' l, b l * χ l) = ∑' m, (conv a b) m * χ m := by
  have hna : Summable fun k => ‖a k * χ k‖ := by
    have h : ∀ k : Gam, ‖a k * χ k‖ = ‖a k‖ := fun k => by rw [norm_mul, hone, mul_one]
    simpa only [h] using wiener_summable a
  have hnb : Summable fun l => ‖b l * χ l‖ := by
    have h : ∀ l : Gam, ‖b l * χ l‖ = ‖b l‖ := fun l => by rw [norm_mul, hone, mul_one]
    simpa only [h] using wiener_summable b
  have hprod : Summable fun z : Gam × Gam => (a z.1 * χ z.1) * (b z.2 * χ z.2) :=
    summable_mul_of_summable_norm (f := fun k : Gam => a k * χ k)
      (g := fun l : Gam => b l * χ l) hna hnb
  have hprod' : Summable fun z : Gam × Gam =>
      (a z.2 * χ z.2) * (b (z.1 - z.2) * χ (z.1 - z.2)) := by
    have h := (Equiv.summable_iff
      (f := fun z : Gam × Gam => (a z.1 * χ z.1) * (b z.2 * χ z.2)) shear).mpr hprod
    simpa [Function.comp, shear] using h
  have hshear : (∑' z : Gam × Gam, (a z.2 * χ z.2) * (b (z.1 - z.2) * χ (z.1 - z.2)))
      = ∑' z : Gam × Gam, (a z.1 * χ z.1) * (b z.2 * χ z.2) := by
    have h := Equiv.tsum_eq shear
      (fun z : Gam × Gam => (a z.1 * χ z.1) * (b z.2 * χ z.2))
    simpa [Function.comp, shear] using h
  have hterm : ∀ m p : Gam,
      (a p * b (m - p)) * χ m = (a p * χ p) * (b (m - p) * χ (m - p)) := by
    intro m p
    have hm : χ p * χ (m - p) = χ m := by
      rw [← hmul p (m - p)]
      congr 1
      abel
    rw [← hm]; ring
  calc (∑' k, a k * χ k) * (∑' l, b l * χ l)
      = ∑' z : Gam × Gam, (a z.1 * χ z.1) * (b z.2 * χ z.2) :=
        tsum_mul_tsum_of_summable_norm (f := fun k : Gam => a k * χ k)
          (g := fun l : Gam => b l * χ l) hna hnb
    _ = ∑' z : Gam × Gam, (a z.2 * χ z.2) * (b (z.1 - z.2) * χ (z.1 - z.2)) := hshear.symm
    _ = ∑' m, ∑' p, (a p * χ p) * (b (m - p) * χ (m - p)) := hprod'.tsum_prod
    _ = ∑' m, ∑' p, (a p * b (m - p)) * χ m :=
        tsum_congr fun m => tsum_congr fun p => (hterm m p).symm
    _ = ∑' m, (conv a b) m * χ m := by
        refine tsum_congr fun m => ?_
        rw [conv_apply, tsum_mul_right]

/-- **The convolution–product theorem.**  Synthesis intertwines the discrete convolution of
Fourier coefficients with the pointwise product of functions on the torus. -/
theorem synth_conv (a b : Wiener) : synth (conv a b) = synth a * synth b := by
  ext x
  show synth (conv a b) x = synth a x * synth b x
  rw [synth_apply, synth_apply, synth_apply]
  exact (tsum_character_mul (a := a) (b := b)
    (fun k l => emode_add_apply k l x) (fun k => norm_emode_apply k x)).symm

/-- Synthesis is multiplicative, pointwise form. -/
theorem synth_conv_apply (a b : Wiener) (x : Torus2) :
    synth (conv a b) x = synth a x * synth b x := by rw [synth_conv]; rfl

/-! ## Regression: two nontrivial Dirac modes

The convolution of two Dirac coefficient families is the Dirac family at the **sum** of the
frequencies, and synthesis turns that into the product of the two monomials.  This pins down
both the frequency arithmetic and the sign convention. -/

theorem conv_wdirac_wdirac (p q : Gam) : conv (wdirac p) (wdirac q) = wdirac (p + q) := by
  ext k
  rw [conv_wdirac_left]
  show diracFun q (k - p) = diracFun (p + q) k
  have h : (k - p = q) ↔ (k = p + q) := by
    constructor
    · intro hh; rw [← hh]; abel
    · intro hh; rw [hh]; abel
  simp only [diracFun, h]

/-- Frequency addition: `e_p · e_q = e_{p+q}`, seen through synthesis. -/
theorem synth_conv_wdirac (p q : Gam) :
    synth (conv (wdirac p) (wdirac q)) = emode (p + q) := by
  rw [conv_wdirac_wdirac, synth_wdirac]

theorem synth_conv_wdirac_eq_mul (p q : Gam) :
    synth (conv (wdirac p) (wdirac q)) = synth (wdirac p) * synth (wdirac q) := by
  rw [synth_conv]

/-- Sign/cancellation regression: `e_k · e_{-k} = 1`. -/
theorem conv_wdirac_neg (p : Gam) : conv (wdirac p) (wdirac (-p)) = wdirac 0 := by
  rw [conv_wdirac_wdirac, add_neg_cancel]

theorem synth_conv_wdirac_neg (p : Gam) :
    synth (conv (wdirac p) (wdirac (-p))) = 1 := by
  rw [conv_wdirac_neg, synth_wdirac, emode_zero]

/-- A two-mode regression with explicit frequencies `(1,0)` and `(0,1)`: the product lands
at the frequency `(1,1)`. -/
theorem synth_conv_unitFreq :
    synth (conv (wdirac (unitFreq 0)) (wdirac (unitFreq 1)))
      = emode (unitFreq 0 + unitFreq 1) := synth_conv_wdirac _ _

theorem unitFreq_sum_apply :
    (unitFreq 0 + unitFreq 1 : Gam) 0 = 1 ∧ (unitFreq 0 + unitFreq 1 : Gam) 1 = 1 := by
  constructor <;> simp [unitFreq]

end LiWang.WienerModel
