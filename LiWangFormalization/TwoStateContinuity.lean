/-
# Continuity of the tested interaction in the TWO state arguments

For a fixed spatial test `ψ`, the interaction that appears in the Section 6 output is

  `I_m(u,v;ψ) = ∫ [ v · R_m(u)·∇ψ + u · R_m(v)·∇ψ ]`.

This module

* builds the **bounded velocity multiplier on the physical `L²` carrier** from the uniformly
  bounded Fourier symbol, and proves it consistent with the Wiener velocity and with physical
  synthesis (`velocityW2`, `velocityW2_toWiener2`, `coeffL2_velocityW2`);
* defines `sideInteraction` and `testedInteraction` by the **actual spatial integral** of the
  actual synthesized fields, and bounds them by the **physical `L²` norms of the two states**
  times the sup-norm of the test derivative — a genuine Cauchy–Schwarz estimate, obtained by
  writing the integral as a physical `L²` inner product;
* proves that the form is complex **bilinear** (not Hermitian: no conjugation appears) in the
  two state arguments, and deduces a **quantitative two-state continuity estimate** and the
  corresponding limit statement with `ψ` fixed;
* identifies the form with the coefficient-side pairing `wpair (incl v) (transport m hm u ψ)`
  used in Section 6, so the vanishing of the symmetrized interaction transfers verbatim;
* handles the **exterior test**: with `E = (closure W)ᶜ`, an exterior test is one whose field
  vanishes on an *open neighbourhood* of `closure W`; then both the field and its first
  derivatives vanish on `closure W`, and the full-torus integral equals its restriction to `E`.
  The boundary is **not** assumed to be null and `E` is **not** replaced by `Wᶜ`.
* lifts everything to time-dependent states and to the **actual iterated space-time integral**,
  with integrability and bounds proved.

Part of `LiWangFormalizationSmoothObservationPacket` v5.0.
-/
import LiWangFormalization.Section6
import LiWangFormalization.FractionalRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. The velocity multiplier on the physical `L²` carrier -/

theorem summable_norm_sq_lp2 (c : Wiener2) : Summable fun k : Gam => ‖c k‖ ^ 2 := by
  have h := (lp.memℓp c).summable (p := 2) (by norm_num)
  refine h.congr (fun k => ?_)
  rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem norm_lp2_sq (c : Wiener2) : ‖c‖ ^ 2 = ∑' k : Gam, ‖c k‖ ^ 2 := by
  have h := norm_w2mk_sq (fun k => c k) (summable_norm_sq_lp2 c)
  have he : w2mk (fun k => c k) (summable_norm_sq_lp2 c) = c := lp.ext (funext fun _ => rfl)
  rwa [he] at h

theorem summable_norm_sq_velocity {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2)
    (c : Wiener2) : Summable fun k : Gam => ‖m j k * c k‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hm
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (m j 0)) (hC j 0)
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((summable_norm_sq_lp2 c).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC j k) 2) (sq_nonneg _)

theorem norm_w2mk_velocity_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (c : Wiener2) :
    ‖w2mk (fun k => m j k * c k) (summable_norm_sq_velocity hm j c)‖ ≤ C * ‖c‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (m j 0)) (hC j 0)
  have hsq : ‖w2mk (fun k => m j k * c k) (summable_norm_sq_velocity hm j c)‖ ^ 2
      ≤ (C * ‖c‖) ^ 2 := by
    rw [norm_w2mk_sq, mul_pow, norm_lp2_sq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_sq_velocity hm j c)
      ((summable_norm_sq_lp2 c).mul_left _)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC j k) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (w2mk (fun k => m j k * c k) (summable_norm_sq_velocity hm j c)),
    mul_nonneg hC0 (norm_nonneg c), hsq]

/-- **The velocity multiplier on the physical `L²` (coefficient `ℓ²`) carrier.** -/
noncomputable def velocityW2 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) :
    Wiener2 →L[ℂ] Wiener2 :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun c => w2mk (fun k => m j k * c k) (summable_norm_sq_velocity hm j c)
      map_add' := fun c d => lp.ext (funext fun k => by
        show m j k * ((c + d) k) = m j k * c k + m j k * d k
        rw [lp.coeFn_add, Pi.add_apply]; ring)
      map_smul' := fun r c => lp.ext (funext fun k => by
        show m j k * ((r • c) k) = r * (m j k * c k)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring) }
    ⟨Classical.choose hm, fun c =>
      norm_w2mk_velocity_le hm j (Classical.choose_spec hm) c⟩

@[simp] theorem velocityW2_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (c : Wiener2) (k : Gam) : (velocityW2 m hm j c) k = m j k * c k := rfl

theorem norm_velocityW2_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (c : Wiener2) : ‖velocityW2 m hm j c‖ ≤ C * ‖c‖ :=
  norm_w2mk_velocity_le hm j hC c

/-- **Consistency with the Wiener velocity.** -/
theorem velocityW2_toWiener2 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) (a : Wiener) :
    velocityW2 m hm j (toWiener2 a) = toWiener2 (velocity m hm j a) :=
  lp.ext (funext fun _ => rfl)

/-- **Consistency with physical synthesis.** -/
theorem coeffL2_velocityW2 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) (a : Wiener) :
    coeffL2 (velocityW2 m hm j (toWiener2 a)) = synthL2 (velocity m hm j a) := by
  rw [velocityW2_toWiener2, coeffL2_toWiener2]

/-- **Realness is preserved** by a real symbol. -/
theorem conjSymmetric_velocity {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (j : Fin 2) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((velocity m hm j a : Wiener) : Gam → ℂ) := by
  intro k
  show m j (-k) * a (-k) = conj (m j k * a k)
  rw [map_mul, ha k, hr j k]

/-- The physical `L²` norm of a Wiener state is at most its Wiener norm. -/
theorem norm_synthL2_le (a : Wiener) : ‖synthL2 a‖ ≤ ‖a‖ := by
  have h1 : ‖synthL2 a‖ ^ 2 = ∑' k : Gam, ‖a k‖ ^ 2 := norm_synthL2_sq a
  have h2 : ∑' k : Gam, ‖a k‖ ^ 2 ≤ (∑' k : Gam, ‖a k‖) ^ 2 := by
    have hs := wiener_summable a
    have hsq : Summable fun k : Gam => ‖a k‖ ^ 2 := summable_norm_sq a
    refine Summable.tsum_le_of_sum_le hsq (fun s => ?_)
    calc ∑ k ∈ s, ‖a k‖ ^ 2 ≤ (∑ k ∈ s, ‖a k‖) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => norm_nonneg _)
      _ ≤ (∑' k : Gam, ‖a k‖) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => norm_nonneg _))
            (hs.sum_le_tsum s (fun k _ => norm_nonneg _)) 2
  have h3 : ‖synthL2 a‖ ^ 2 ≤ ‖a‖ ^ 2 := by rw [h1, wiener_norm_eq a]; exact h2
  nlinarith [norm_nonneg (synthL2 a), norm_nonneg a, h3]

/-- **The velocity multiplier is bounded on the physical `L²` norm.** -/
theorem norm_synthL2_velocity_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (j : Fin 2) (a : Wiener) :
    ‖synthL2 (velocity m hm j a)‖ ≤ C * ‖synthL2 a‖ := by
  rw [← coeffL2_velocityW2, norm_coeffL2, ← coeffL2_toWiener2, norm_coeffL2]
  exact norm_velocityW2_le hm j hC (toWiener2 a)

/-! ## 2. The tested interaction as an actual spatial integral -/

theorem integrable_triple (A B C : Wiener) :
    Integrable (fun x : Torus2 => synth A x * synth B x * synth C x)
      (volume : Measure Torus2) :=
  (((synth A).continuous.mul (synth B).continuous).mul
    (synth C).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem inner_synthL2_integral (a b : Wiener) :
    (inner ℂ (synthL2 a) (synthL2 b) : ℂ) = ∫ x : Torus2, conj (synth a x) * synth b x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [synthL2_apply_ae a, synthL2_apply_ae b] with x hx hy
  rw [hx, hy]
  rw [RCLike.inner_apply (𝕜 := ℂ) (synth a x) (synth b x)]
  ring

/-- The spatial integral of a triple product is a physical `L²` inner product. -/
theorem integral_triple_eq_inner (A B C : Wiener) :
    (∫ x : Torus2, synth A x * synth B x * synth C x)
      = inner ℂ (synthL2 (conv (conjRefl A) (conjRefl C))) (synthL2 B) := by
  rw [inner_synthL2_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [synth_conv_apply, synth_conjRefl_apply, synth_conjRefl_apply, map_mul,
    Complex.conj_conj, Complex.conj_conj]
  ring

theorem norm_synthL2_conv_le (A C : Wiener) :
    ‖synthL2 (conv (conjRefl A) (conjRefl C))‖ ≤ ‖synth C‖ * ‖synthL2 A‖ := by
  have hP : ‖synthL2 (conv (conjRefl A) (conjRefl C))‖ ^ 2
      = ∫ x : Torus2, ‖synth A x‖ ^ 2 * ‖synth C x‖ ^ 2 := by
    rw [norm_synthL2_sq, ← integral_norm_sq_synth]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [synth_conv_apply, synth_conjRefl_apply, synth_conjRefl_apply, norm_mul,
      RCLike.norm_conj, RCLike.norm_conj, mul_pow]
  have hA : ‖synthL2 A‖ ^ 2 = ∫ x : Torus2, ‖synth A x‖ ^ 2 := by
    rw [norm_synthL2_sq, integral_norm_sq_synth]
  have hmono : (∫ x : Torus2, ‖synth A x‖ ^ 2 * ‖synth C x‖ ^ 2)
      ≤ ∫ x : Torus2, ‖synth C‖ ^ 2 * ‖synth A x‖ ^ 2 := by
    refine integral_mono ?_ ?_ (fun x => ?_)
    · exact (((synth A).continuous.norm.pow 2).mul
        ((synth C).continuous.norm.pow 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · exact (((synth A).continuous.norm.pow 2).const_mul
        (‖synth C‖ ^ 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) ((synth C).norm_coe_le_norm x) 2) (sq_nonneg _)
  have hsq : ‖synthL2 (conv (conjRefl A) (conjRefl C))‖ ^ 2 ≤ (‖synth C‖ * ‖synthL2 A‖) ^ 2 := by
    rw [hP, mul_pow, hA, ← integral_const_mul]
    exact hmono
  nlinarith [norm_nonneg (synthL2 (conv (conjRefl A) (conjRefl C))),
    mul_nonneg (norm_nonneg (synth C)) (norm_nonneg (synthL2 A)), hsq]

/-- **Cauchy–Schwarz for the tested triple integral**: bounded by the sup norm of the test
factor times the two physical `L²` norms. -/
theorem norm_integral_triple_le (A B C : Wiener) :
    ‖∫ x : Torus2, synth A x * synth B x * synth C x‖
      ≤ ‖synth C‖ * ‖synthL2 A‖ * ‖synthL2 B‖ := by
  rw [integral_triple_eq_inner]
  calc ‖(inner ℂ (synthL2 (conv (conjRefl A) (conjRefl C))) (synthL2 B) : ℂ)‖
      ≤ ‖synthL2 (conv (conjRefl A) (conjRefl C))‖ * ‖synthL2 B‖ := norm_inner_le_norm _ _
    _ ≤ (‖synth C‖ * ‖synthL2 A‖) * ‖synthL2 B‖ :=
        mul_le_mul_of_nonneg_right (norm_synthL2_conv_le A C) (norm_nonneg _)

/-- The one-sided tested interaction `∑ⱼ ∫ v · R_m(u) · ∂ⱼψ`, an actual spatial integral of the
actual synthesized fields.  It is **complex bilinear** in `(u,v)`: no conjugation occurs, so
this is not the Hermitian `L²` inner product. -/
noncomputable def sideInteraction (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ : Wiener1)
    (u v : Wiener1) : ℂ :=
  ∑ j : Fin 2, ∫ x : Torus2,
    synth (incl v) x * synth (velocity m hm j (incl u)) x * synth (fourierDeriv j ψ) x

/-- **The tested interaction** `I_m(u,v;ψ)`. -/
noncomputable def testedInteraction (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ : Wiener1)
    (u v : Wiener1) : ℂ :=
  sideInteraction m hm ψ u v + sideInteraction m hm ψ v u

theorem norm_synth_fourierDeriv_le (j : Fin 2) (ψ : Wiener1) :
    ‖synth (fourierDeriv j ψ)‖ ≤ 2 * Real.pi * ‖ψ‖ :=
  le_trans (norm_synth_apply_le _)
    ((fourierDeriv j).le_of_opNorm_le (norm_fourierDeriv_le j) ψ)

theorem norm_sideInteraction_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u v : Wiener1) :
    ‖sideInteraction m hm ψ u v‖
      ≤ 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖))) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (m 0 0)) (hC 0 0)
  have hterm : ∀ j : Fin 2,
      ‖∫ x : Torus2, synth (incl v) x * synth (velocity m hm j (incl u)) x
          * synth (fourierDeriv j ψ) x‖
        ≤ (2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖)) := by
    intro j
    calc ‖∫ x : Torus2, synth (incl v) x * synth (velocity m hm j (incl u)) x
              * synth (fourierDeriv j ψ) x‖
        ≤ ‖synth (fourierDeriv j ψ)‖ * ‖synthL2 (incl v)‖
            * ‖synthL2 (velocity m hm j (incl u))‖ := norm_integral_triple_le _ _ _
      _ ≤ (2 * Real.pi * ‖ψ‖) * ‖synthL2 (incl v)‖ * (C * ‖synthL2 (incl u)‖) := by
          refine mul_le_mul ?_ (norm_synthL2_velocity_le hm hC j (incl u)) (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_right (norm_synth_fourierDeriv_le j ψ) (norm_nonneg _)
          · exact mul_nonneg (by positivity) (norm_nonneg _)
      _ = (2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖)) := by ring
  calc ‖sideInteraction m hm ψ u v‖
      ≤ ∑ j : Fin 2, ‖∫ x : Torus2, synth (incl v) x * synth (velocity m hm j (incl u)) x
          * synth (fourierDeriv j ψ) x‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, (2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring


/-! ## 3. Bilinearity and the bounded bilinear form -/

theorem sideInteraction_add_left (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ u u' v : Wiener1) :
    sideInteraction m hm ψ (u + u') v
      = sideInteraction m hm ψ u v + sideInteraction m hm ψ u' v := by
  rw [sideInteraction, sideInteraction, sideInteraction, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← integral_add (integrable_triple _ _ _) (integrable_triple _ _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hv : synth (velocity m hm j (incl (u + u'))) x
      = synth (velocity m hm j (incl u)) x + synth (velocity m hm j (incl u')) x := by
    rw [map_add incl, map_add, map_add]; rfl
  rw [hv]; ring

theorem sideInteraction_smul_left (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (c : ℂ)
    (ψ u v : Wiener1) :
    sideInteraction m hm ψ (c • u) v = c * sideInteraction m hm ψ u v := by
  rw [sideInteraction, sideInteraction, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Eq.trans ?_ (integral_const_mul (μ := (volume : Measure Torus2)) c
    (fun x => synth (incl v) x * synth (velocity m hm j (incl u)) x
      * synth (fourierDeriv j ψ) x))
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hv : synth (velocity m hm j (incl (c • u))) x = c * synth (velocity m hm j (incl u)) x := by
    rw [map_smul incl, map_smul, map_smul]; rfl
  rw [hv]; ring

theorem sideInteraction_add_right (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (ψ u v v' : Wiener1) :
    sideInteraction m hm ψ u (v + v')
      = sideInteraction m hm ψ u v + sideInteraction m hm ψ u v' := by
  rw [sideInteraction, sideInteraction, sideInteraction, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← integral_add (integrable_triple _ _ _) (integrable_triple _ _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hv : synth (incl (v + v')) x = synth (incl v) x + synth (incl v') x := by
    rw [map_add incl, map_add]; rfl
  rw [hv]; ring

theorem sideInteraction_smul_right (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (c : ℂ)
    (ψ u v : Wiener1) :
    sideInteraction m hm ψ u (c • v) = c * sideInteraction m hm ψ u v := by
  rw [sideInteraction, sideInteraction, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Eq.trans ?_ (integral_const_mul (μ := (volume : Measure Torus2)) c
    (fun x => synth (incl v) x * synth (velocity m hm j (incl u)) x
      * synth (fourierDeriv j ψ) x))
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hv : synth (incl (c • v)) x = c * synth (incl v) x := by
    rw [map_smul incl, map_smul]; rfl
  rw [hv]; ring

theorem norm_sideInteraction_le_wiener {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u v : Wiener1) :
    ‖sideInteraction m hm ψ u v‖ ≤ (4 * Real.pi * ‖ψ‖ * C) * ‖u‖ * ‖v‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (m 0 0)) (hC 0 0)
  have hu : ‖synthL2 (incl u)‖ ≤ ‖u‖ :=
    le_trans (norm_synthL2_le _) (norm_incl_apply_le u)
  have hv : ‖synthL2 (incl v)‖ ≤ ‖v‖ :=
    le_trans (norm_synthL2_le _) (norm_incl_apply_le v)
  have hbase := norm_sideInteraction_le hm hC ψ u v
  have hmul : ‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖ ≤ ‖v‖ * ‖u‖ :=
    mul_le_mul hv hu (norm_nonneg _) (norm_nonneg _)
  have hpi : (0:ℝ) ≤ 2 * Real.pi * ‖ψ‖ := by positivity
  calc ‖sideInteraction m hm ψ u v‖
      ≤ 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v)‖ * ‖synthL2 (incl u)‖))) := hbase
    _ ≤ 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖v‖ * ‖u‖))) := by
        have := mul_le_mul_of_nonneg_left hmul hC0
        nlinarith [hpi, this]
    _ = (4 * Real.pi * ‖ψ‖ * C) * ‖u‖ * ‖v‖ := by ring

/-- **The tested interaction as a bounded bilinear form in the two state arguments.** -/
noncomputable def sideInteractionCLM (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ : Wiener1) : Wiener1 →L[ℂ] Wiener1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun u =>
        { toFun := fun v => sideInteraction m hm ψ u v
          map_add' := fun v v' => sideInteraction_add_right m hm ψ u v v'
          map_smul' := fun c v => sideInteraction_smul_right m hm c ψ u v }
      map_add' := fun u u' => by
        ext v; exact sideInteraction_add_left m hm ψ u u' v
      map_smul' := fun c u => by
        ext v; exact sideInteraction_smul_left m hm c ψ u v }
    (4 * Real.pi * ‖ψ‖ * C) (fun u v => norm_sideInteraction_le_wiener hm hC ψ u v)

@[simp] theorem sideInteractionCLM_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u v : Wiener1) :
    sideInteractionCLM m hm hC ψ u v = sideInteraction m hm ψ u v := rfl

theorem sideInteraction_sub_left (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u u' v : Wiener1) :
    sideInteraction m hm ψ (u - u') v
      = sideInteraction m hm ψ u v - sideInteraction m hm ψ u' v := by
  have h : sideInteractionCLM m hm hC ψ (u - u') v
      = (sideInteractionCLM m hm hC ψ u - sideInteractionCLM m hm hC ψ u') v := by
    rw [map_sub]
  rw [ContinuousLinearMap.sub_apply] at h
  exact h

theorem sideInteraction_sub_right (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u v v' : Wiener1) :
    sideInteraction m hm ψ u (v - v')
      = sideInteraction m hm ψ u v - sideInteraction m hm ψ u v' :=
  map_sub (sideInteractionCLM m hm hC ψ u) v v'

/-! ## 4. Quantitative continuity in the two state arguments, with `ψ` fixed -/

/-- The exact two-state decomposition. -/
theorem sideInteraction_decomp (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u₁ u v₁ v : Wiener1) :
    sideInteraction m hm ψ u₁ v₁ - sideInteraction m hm ψ u v
      = sideInteraction m hm ψ (u₁ - u) v₁ + sideInteraction m hm ψ u (v₁ - v) := by
  rw [sideInteraction_sub_left m hm hC, sideInteraction_sub_right m hm hC]
  ring

/-- **Quantitative two-state continuity in the physical `L²` norms.** -/
theorem norm_sideInteraction_sub_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u₁ u v₁ v : Wiener1) :
    ‖sideInteraction m hm ψ u₁ v₁ - sideInteraction m hm ψ u v‖
      ≤ 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v₁)‖ * ‖synthL2 (incl (u₁ - u))‖)))
        + 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl (v₁ - v))‖ * ‖synthL2 (incl u)‖))) := by
  rw [sideInteraction_decomp m hm hC]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact norm_sideInteraction_le hm hC ψ (u₁ - u) v₁
  · exact norm_sideInteraction_le hm hC ψ u (v₁ - v)

/-- **Quantitative two-state continuity for the symmetrized form.** -/
theorem norm_testedInteraction_sub_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ u₁ u v₁ v : Wiener1) :
    ‖testedInteraction m hm ψ u₁ v₁ - testedInteraction m hm ψ u v‖
      ≤ (2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v₁)‖ * ‖synthL2 (incl (u₁ - u))‖)))
          + 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl (v₁ - v))‖ * ‖synthL2 (incl u)‖))))
        + (2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl u₁)‖ * ‖synthL2 (incl (v₁ - v))‖)))
          + 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl (u₁ - u))‖ * ‖synthL2 (incl v)‖)))) := by
  have hsplit : testedInteraction m hm ψ u₁ v₁ - testedInteraction m hm ψ u v
      = (sideInteraction m hm ψ u₁ v₁ - sideInteraction m hm ψ u v)
        + (sideInteraction m hm ψ v₁ u₁ - sideInteraction m hm ψ v u) := by
    rw [testedInteraction, testedInteraction]; ring
  rw [hsplit]
  exact le_trans (norm_add_le _ _)
    (add_le_add (norm_sideInteraction_sub_le hm hC ψ u₁ u v₁ v)
      (norm_sideInteraction_sub_le hm hC ψ v₁ v u₁ u))


/-! ## 5. Identification with the Section 6 coefficient pairing -/

theorem wpair_add_right (A B B' : Wiener) : wpair A (B + B') = wpair A B + wpair A B' := by
  rw [wpair_comm A (B + B'), wpair_add_left, wpair_comm B A, wpair_comm B' A]

/-- **The spatial integral form is the Section 6 pairing.** -/
theorem sideInteraction_eq_wpair (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ u v : Wiener1) :
    sideInteraction m hm ψ u v = wpair (incl v) (transport m hm u ψ) := by
  rw [transport_apply, Fin.sum_univ_two, wpair_add_right, sideInteraction, Fin.sum_univ_two]
  congr 1 <;>
  · rw [wpair_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [synth_conv_apply]
    ring

/-- **The tested interaction vanishes on a generated pair.**  This is the Section 6 output
transported to the spatial-integral form. -/
theorem testedInteraction_eq_zero_of_generated {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hdiv : IsDivFreeSymbol m) {v₁ v₂ : Wiener1}
    (hgen : transport m hm v₁ v₂ + transport m hm v₂ v₁ = 0) (ψ : Wiener1) :
    testedInteraction m hm ψ v₁ v₂ = 0 := by
  rw [testedInteraction, sideInteraction_eq_wpair, sideInteraction_eq_wpair]
  exact tested_symmetrized_eq_zero hm hdiv hgen ψ

/-! ## 6. The exterior test and the restriction to `E = (closure W)ᶜ` -/

/-- **An exterior test for `W`**: a first-order state whose physical field vanishes on an *open
neighbourhood* of `closure W`.  This is what makes both the field and its first derivatives
vanish on all of `closure W`, boundary included; no null-boundary assumption is made and `E` is
never replaced by `Wᶜ`. -/
def IsExteriorTest (W : Set Torus2) (ψ : Wiener1) : Prop :=
  ∃ U : Set Torus2, IsOpen U ∧ closure W ⊆ U ∧ ∀ x ∈ U, synth (incl ψ) x = 0

theorem IsExteriorTest.field_vanishes {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ)
    {x : Torus2} (hx : x ∈ closure W) : synth (incl ψ) x = 0 := by
  obtain ⟨U, -, hsub, hvan⟩ := h
  exact hvan x (hsub hx)

/-- **The derivative support**: the first derivatives of an exterior test also vanish on the
whole of `closure W`. -/
theorem IsExteriorTest.deriv_vanishes {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ)
    (j : Fin 2) {x : Torus2} (hx : x ∈ closure W) : synth (fourierDeriv j ψ) x = 0 := by
  obtain ⟨U, hU, hsub, hvan⟩ := h
  exact synth_fourierDeriv_eq_zero_of_vanishes hU hvan j (hsub hx)

/-- **Equality of the full-torus pairing with its restriction to the exterior `E`.** -/
theorem sideInteraction_eq_exterior {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1) :
    sideInteraction m hm ψ u v
      = ∑ j : Fin 2, ∫ x in (closure W)ᶜ,
          synth (incl v) x * synth (velocity m hm j (incl u)) x * synth (fourierDeriv j ψ) x := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hzero : (∫ x in closure W,
      synth (incl v) x * synth (velocity m hm j (incl u)) x * synth (fourierDeriv j ψ) x) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
    rw [h.deriv_vanishes j hx, mul_zero]
  have hadd := integral_add_compl (μ := (volume : Measure Torus2))
    (isClosed_closure (s := W)).measurableSet (integrable_triple (incl v)
      (velocity m hm j (incl u)) (fourierDeriv j ψ))
  rw [hzero, zero_add] at hadd
  exact hadd.symm

/-! ## 7. Time-dependent states and the actual iterated space-time integral -/

/-- The tested interaction of two state *curves* at a given time. -/
noncomputable def testedInteractionTime (hT : 0 ≤ T) (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (ψ : Wiener1) (u v : Curve1 T) (t : ℝ) : ℂ :=
  testedInteraction m hm ψ (curveState hT u t) (curveState hT v t)

theorem continuous_testedInteractionTime {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (hT : 0 ≤ T) (ψ : Wiener1) (u v : Curve1 T) :
    Continuous (testedInteractionTime hT m hm ψ u v) := by
  have ha : Continuous (curveState hT u) := continuous_curveState hT u
  have hb : Continuous (curveState hT v) := continuous_curveState hT v
  have h1 : Continuous fun t : ℝ =>
      sideInteractionCLM m hm hC ψ (curveState hT u t) (curveState hT v t) :=
    ((sideInteractionCLM m hm hC ψ).continuous.comp ha).clm_apply hb
  have h2 : Continuous fun t : ℝ =>
      sideInteractionCLM m hm hC ψ (curveState hT v t) (curveState hT u t) :=
    ((sideInteractionCLM m hm hC ψ).continuous.comp hb).clm_apply ha
  exact h1.add h2

/-- **The actual iterated space-time integral**: a continuous time profile against the tested
interaction of the two state curves. -/
noncomputable def spacetimeTestedInteraction (hT : 0 ≤ T) (m : Fin 2 → Gam → ℂ)
    (hm : IsBddSymbol m) (ψ : Wiener1) (φ : ℝ → ℂ) (u v : Curve1 T) : ℂ :=
  ∫ t in (0:ℝ)..T, φ t * testedInteractionTime hT m hm ψ u v t

theorem intervalIntegrable_spacetimeTestedInteraction {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (hT : 0 ≤ T) (ψ : Wiener1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (u v : Curve1 T) :
    IntervalIntegrable (fun t => φ t * testedInteractionTime hT m hm ψ u v t)
      (volume : Measure ℝ) 0 T :=
  (hφ.mul (continuous_testedInteractionTime hm hC hT ψ u v)).intervalIntegrable 0 T

/-- **The literal iterated physical space-time integral**, with the spatial integral restricted
to the exterior `E = (closure W)ᶜ`. -/
theorem spacetimeTestedInteraction_eq_iterated {W : Set Torus2} {ψ : Wiener1}
    (hψ : IsExteriorTest W ψ) (hT : 0 ≤ T) (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (φ : ℝ → ℂ) (u v : Curve1 T) :
    spacetimeTestedInteraction hT m hm ψ φ u v
      = ∫ t in (0:ℝ)..T, φ t *
          ((∑ j : Fin 2, ∫ x in (closure W)ᶜ,
              synth (incl (curveState hT v t)) x
                * synth (velocity m hm j (incl (curveState hT u t))) x
                * synth (fourierDeriv j ψ) x)
            + (∑ j : Fin 2, ∫ x in (closure W)ᶜ,
              synth (incl (curveState hT u t)) x
                * synth (velocity m hm j (incl (curveState hT v t))) x
                * synth (fourierDeriv j ψ) x)) := by
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  dsimp only
  rw [testedInteractionTime, testedInteraction,
    sideInteraction_eq_exterior hψ m hm _ _, sideInteraction_eq_exterior hψ m hm _ _]

/-- **The space-time output vanishes.**  For two generated states whose symmetrized interaction
vanishes at every time, the actual time integral — not merely the pointwise-in-time identity —
is zero. -/
theorem spacetimeTestedInteraction_eq_zero (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (hdiv : IsDivFreeSymbol (m₁ - m₂))
    {h₁ h₂ : Curve0 T}
    (hgen : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
        + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₂) (duhamelOp hα hT h₁) = 0)
    (ψ : Wiener1) (φ : ℝ → ℂ) :
    spacetimeTestedInteraction hT (m₁ - m₂) (hm₁.sub hm₂) ψ φ
      (duhamelOp hα hT h₁) (duhamelOp hα hT h₂) = 0 := by
  have hpt : ∀ t : ℝ, φ t * testedInteractionTime hT (m₁ - m₂) (hm₁.sub hm₂) ψ
      (duhamelOp hα hT h₁) (duhamelOp hα hT h₂) t = 0 := by
    intro t
    have hval := congrArg (fun V : Curve0 T => (V (clampT hT t)).val) hgen
    have hzero : transport (m₁ - m₂) (hm₁.sub hm₂)
          (curveState hT (duhamelOp hα hT h₁) t) (curveState hT (duhamelOp hα hT h₂) t)
        + transport (m₁ - m₂) (hm₁.sub hm₂)
          (curveState hT (duhamelOp hα hT h₂) t) (curveState hT (duhamelOp hα hT h₁) t) = 0 := by
      simpa using hval
    rw [testedInteractionTime,
      testedInteraction_eq_zero_of_generated (hm₁.sub hm₂) hdiv hzero ψ, mul_zero]
  rw [spacetimeTestedInteraction, intervalIntegral.integral_congr (fun t _ => hpt t)]
  simp


end LiWang.Formalization
