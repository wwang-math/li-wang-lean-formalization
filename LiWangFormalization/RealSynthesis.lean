/-
# Reality transfer: conjugate-symmetric coefficients synthesize to real-valued functions

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.SynthesisAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

/-- **Reality transfer.**  If the coefficient family is conjugate symmetric then the
synthesized function is fixed by complex conjugation, i.e. real valued. -/
theorem conj_synth_apply {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) (x : Torus2) :
    conj (synth a x) = synth a x := by
  have hterm : ∀ k : Gam, conj (a k * emode k x) = a (-k) * emode (-k) x := by
    intro k
    rw [map_mul, ← (ha k), ← emode_neg_apply]
  have hneg := Equiv.tsum_eq (Equiv.neg Gam) (fun k : Gam => a k * emode k x)
  rw [synth_apply, Complex.conj_tsum, tsum_congr hterm]
  simpa using hneg

theorem synth_im_eq_zero {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) (x : Torus2) :
    (synth a x).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_synth_apply ha x)

theorem ofReal_re_synth {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) (x : Torus2) :
    (((synth a x).re : ℝ) : ℂ) = synth a x :=
  Complex.conj_eq_iff_re.mp (conj_synth_apply ha x)

/-! ## The real synthesis map -/

/-- The real-valued function synthesized from a real (conjugate-symmetric) Wiener element. -/
noncomputable def realSynthMap (a : RealWiener) : C(Torus2, ℝ) :=
  ⟨fun x => (synth a.val x).re, Complex.continuous_re.comp (synth a.val).continuous⟩

@[simp] theorem realSynthMap_apply (a : RealWiener) (x : Torus2) :
    realSynthMap a x = (synth a.val x).re := rfl

/-- The real synthesis really is the complex synthesis: no information is lost. -/
theorem ofReal_realSynthMap (a : RealWiener) (x : Torus2) :
    ((realSynthMap a x : ℝ) : ℂ) = synth a.val x :=
  ofReal_re_synth a.conjSymmetric x

theorem realSynthMap_add (a b : RealWiener) :
    realSynthMap (a + b) = realSynthMap a + realSynthMap b := by
  ext x
  show (synth (a + b).val x).re = (synth a.val x).re + (synth b.val x).re
  rw [RealWiener.val_add, synth_add]
  rfl

theorem realSynthMap_smul (r : ℝ) (a : RealWiener) :
    realSynthMap (r • a) = r • realSynthMap a := by
  ext x
  show (synth (r • a).val x).re = r * (synth a.val x).re
  rw [RealWiener.val_smul, smul_real_wiener, synth_smul]
  show ((r : ℂ) • synth a.val x).re = r * (synth a.val x).re
  simp

theorem norm_realSynthMap_le (a : RealWiener) : ‖realSynthMap a‖ ≤ ‖a‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg a)).2 fun x => ?_
  calc ‖realSynthMap a x‖ = |(synth a.val x).re| := rfl
    _ ≤ ‖synth a.val x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖synth a.val‖ := (synth a.val).norm_coe_le_norm x
    _ ≤ ‖a.val‖ := norm_synth_apply_le _
    _ = ‖a‖ := rfl

/-- **Real Fourier synthesis** `RealWiener →L[ℝ] C(𝕋², ℝ)`. -/
noncomputable def realSynth : RealWiener →L[ℝ] C(Torus2, ℝ) :=
  LinearMap.mkContinuous
    { toFun := realSynthMap
      map_add' := realSynthMap_add
      map_smul' := fun r a => realSynthMap_smul r a }
    1 (fun a => by rw [one_mul]; exact norm_realSynthMap_le a)

@[simp] theorem realSynth_apply (a : RealWiener) (x : Torus2) :
    realSynth a x = (synth a.val x).re := rfl

theorem ofReal_realSynth (a : RealWiener) (x : Torus2) :
    ((realSynth a x : ℝ) : ℂ) = synth a.val x := ofReal_realSynthMap a x

theorem norm_realSynth_le : ‖realSynth‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The real synthesis of the concrete real cosine mode is a genuine real function whose
complexification is the corresponding complex synthesis. -/
theorem realSynth_realCosMode (k₀ : Gam) (x : Torus2) :
    ((realSynth (RealWiener.mk (incl (cosMode1 k₀))
        ((cosMode1_conjSymmetric k₀).incl)) x : ℝ) : ℂ)
      = synth (incl (cosMode1 k₀)) x :=
  ofReal_realSynth _ x

end LiWang.Formalization
