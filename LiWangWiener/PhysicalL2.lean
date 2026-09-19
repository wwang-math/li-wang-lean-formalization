/-
# The physical `L²` identification and Parseval

The synthesis map is lifted to the physical Lebesgue space `L²(𝕋²)` for the **normalized**
Haar measure (the `volume` of `Fin 2 → AddCircle 1`, a probability measure), and Parseval's
identity is proved for synthesized Wiener states:

    ∫_{𝕋²} |synth a|² dx = ∑_k ‖a k‖² ,   ⟪synth a, synth b⟫_{L²} = ∑_k conj(a k) · b k .

Both are proved from the coefficient-recovery identity `∫ (synth a)·e_j = a(-j)` of
`Coefficients.lean`, i.e. from the orthogonality of the monomials for the *same* normalized
measure, so the normalization is consistent by construction.

Part of `LiWangWienerObservationBridgePacket` v4.0.
-/
import LiWangWiener.TorusIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

/-! ## Conjugate reflection of coefficients -/

theorem summable_conjRefl (a : Wiener) : Summable fun k => ‖conj (a (-k))‖ := by
  have h : (fun k : Gam => ‖conj (a (-k))‖) = fun k : Gam => ‖a (-k)‖ := by
    funext k; rw [RCLike.norm_conj]
  rw [h]
  exact (Equiv.neg Gam).summable_iff.2 (wiener_summable a)

/-- The conjugate reflection `k ↦ conj(a(-k))` of a coefficient family. -/
noncomputable def conjRefl (a : Wiener) : Wiener :=
  wmk (fun k => conj (a (-k))) (summable_conjRefl a)

@[simp] theorem conjRefl_apply (a : Wiener) (k : Gam) : (conjRefl a) k = conj (a (-k)) := rfl

/-- **Conjugation is reflection of the coefficients.** -/
theorem synth_conjRefl_apply (a : Wiener) (x : Torus2) :
    synth (conjRefl a) x = conj (synth a x) := by
  have hL : synth (conjRefl a) x = ∑' k : Gam, conj (a (-k)) * emode k x := by
    rw [synth_apply]
    exact tsum_congr fun k => by rw [conjRefl_apply]
  have hR : conj (synth a x) = ∑' k : Gam, conj (a (-k)) * emode k x := by
    rw [synth_apply, Complex.conj_tsum]
    have hterm : ∀ k : Gam, conj (a k * emode k x) = conj (a (-(-k))) * emode (-k) x := by
      intro k
      rw [map_mul, neg_neg, emode_neg_apply]
    rw [tsum_congr hterm]
    exact (Equiv.neg Gam).tsum_eq (fun j : Gam => conj (a (-j)) * emode j x)
  rw [hL, hR]

/-! ## Parseval -/

theorem summable_norm_sq (a : Wiener) : Summable fun k => ‖a k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((wiener_summable a).mul_left ‖a‖)
  have h := wiener_norm_apply_le a k
  have h0 : (0:ℝ) ≤ ‖a k‖ := norm_nonneg _
  nlinarith

/-- **Parseval's identity for a synthesized Wiener state**, for the normalized Haar measure. -/
theorem integral_norm_sq_synth (a : Wiener) :
    (∫ x : Torus2, ‖synth a x‖ ^ 2) = ∑' k : Gam, ‖a k‖ ^ 2 := by
  have hcont : Continuous fun x : Torus2 => ‖synth a x‖ ^ 2 :=
    ((synth a).continuous.norm).pow 2
  have hint : Integrable (fun x : Torus2 => ‖synth a x‖ ^ 2) (volume : Measure Torus2) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the complex form
  have hpt : ∀ x : Torus2, synth (conjRefl a) x * synth a x = ((‖synth a x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [synth_conjRefl_apply]
    rw [Complex.conj_mul']
    norm_cast
  have hcomplex : (∫ x : Torus2, synth (conjRefl a) x * synth a x)
      = ∑' k : Gam, conj (a (-k)) * a (-k) := by
    rw [integral_synth_mul (conjRefl a) (synth a)]
    refine tsum_congr fun k => ?_
    rw [conjRefl_apply]
    congr 1
    have h := integral_synth_mul_emode a k
    calc (∫ x : Torus2, emode k x * synth a x)
        = ∫ x : Torus2, synth a x * emode k x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = a (-k) := h
  have hLHS : (∫ x : Torus2, synth (conjRefl a) x * synth a x)
      = (((∫ x : Torus2, ‖synth a x‖ ^ 2) : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_ofReal
  have hRHS : (∑' k : Gam, conj (a (-k)) * a (-k)) = (((∑' k : Gam, ‖a k‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_tsum]
    have hre : ∀ k : Gam, conj (a (-k)) * a (-k) = ((‖a (-k)‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [Complex.conj_mul']
      norm_cast
    rw [tsum_congr hre]
    exact (Equiv.neg Gam).tsum_eq (fun j : Gam => ((‖a j‖ ^ 2 : ℝ) : ℂ))
  have := hLHS.symm.trans (hcomplex.trans hRHS)
  exact_mod_cast this

/-! ## The `L²(𝕋²)` carrier -/

/-- The physical `L²` space of the two-torus for the normalized Haar measure. -/
abbrev TorusL2 : Type := Lp ℂ 2 (volume : Measure Torus2)

/-- **Physical `L²` synthesis**: a Wiener state, viewed as an element of `L²(𝕋²)`. -/
noncomputable def synthL2 : Wiener →L[ℂ] TorusL2 :=
  (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ).comp synth

theorem synthL2_apply_ae (a : Wiener) :
    (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2)] fun x => synth a x :=
  ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := (volume : Measure Torus2)) (𝕜 := ℂ) (synth a)

/-- **Plancherel**: the physical `L²` inner product of two synthesized states is the
coefficient `ℓ²` inner product. -/
theorem inner_synthL2 (a b : Wiener) :
    (inner ℂ (synthL2 a) (synthL2 b) : ℂ) = ∑' k : Gam, conj (a k) * b k := by
  have hinner : (inner ℂ (synthL2 a) (synthL2 b) : ℂ)
      = ∫ x : Torus2, conj (synth a x) * synth b x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [synthL2_apply_ae a, synthL2_apply_ae b] with x hx hy
    rw [hx, hy]
    rw [RCLike.inner_apply (𝕜 := ℂ) (synth a x) (synth b x)]
    ring
  have hpt : ∀ x : Torus2, conj (synth a x) * synth b x = synth (conjRefl a) x * synth b x := by
    intro x; rw [synth_conjRefl_apply]
  rw [hinner, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_synth_mul (conjRefl a) (synth b)]
  have hterm : ∀ k : Gam, (conjRefl a) k * (∫ x : Torus2, emode k x * synth b x)
      = conj (a (-k)) * b (-k) := by
    intro k
    rw [conjRefl_apply]
    congr 1
    calc (∫ x : Torus2, emode k x * synth b x)
        = ∫ x : Torus2, synth b x * emode k x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = b (-k) := integral_synth_mul_emode b k
  rw [tsum_congr hterm]
  exact (Equiv.neg Gam).tsum_eq (fun j : Gam => conj (a j) * b j)

/-- **Parseval in the `L²` carrier.** -/
theorem norm_synthL2_sq (a : Wiener) : ‖synthL2 a‖ ^ 2 = ∑' k : Gam, ‖a k‖ ^ 2 := by
  have h := inner_synthL2 a a
  have hterm : ∀ k : Gam, conj (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
    intro k; rw [Complex.conj_mul']; norm_cast
  rw [tsum_congr hterm, ← Complex.ofReal_tsum] at h
  have hself : (inner ℂ (synthL2 a) (synthL2 a) : ℂ) = ((‖synthL2 a‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hself] at h
  exact_mod_cast h

/-- The monomials form an **orthonormal family** in the physical `L²` space. -/
theorem orthonormal_synthL2_wdirac :
    Orthonormal ℂ (fun k : Gam => synthL2 (wdirac k)) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [inner_synthL2]
  have hterm : ∀ j : Gam, conj ((wdirac k) j) * (wdirac l) j
      = if j = k then (if k = l then (1:ℂ) else 0) else 0 := by
    intro j
    show conj (if j = k then (1:ℂ) else 0) * (if j = l then (1:ℂ) else 0) = _
    by_cases hj : j = k
    · rw [if_pos hj, if_pos hj, map_one, one_mul]
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos (hj.trans hkl)]
      · rw [if_neg hkl, if_neg (fun hc : j = l => hkl (hj.symm.trans hc))]
    · rw [if_neg hj, if_neg hj, map_zero, zero_mul]
  rw [tsum_congr hterm, tsum_ite_eq]

theorem synthL2_wdirac (k : Gam) : synthL2 (wdirac k) = ContinuousMap.toLp 2 volume ℂ (emode k) := by
  show (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ) (synth (wdirac k)) = _
  rw [synth_wdirac]

end LiWang.WienerModel
