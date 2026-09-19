/-
# The real-carrier interface for the time primitives, and the real-only UCP boundary

`local_cancellation` delivers, for every `t ∈ [0,T]`, an actual pair

  `v = timePrimitive hT (u₁ - u₂) t : A¹(𝕋²)`,   `F = fracTimeIntegral hα hT g t : A(𝕋²)`

with `F_k = λ_k v_k` and both physical fields vanishing on `W`.  The platform, however, proves
spatial fractional unique continuation for a **real physical-`L²` fractional graph**, while
`FractionalUCP` quantifies over complex Wiener states.  This module closes that gap:

* `memSobolev_of_coeff_rel` — explicit `H^{2α}` membership of `v` from the coefficient relation
  (`memSobolev_two_alpha` plus square summability of `incl v` and `F`);
* `synthL2_eq_fracLapRep` — the physical `L²` representative of `F` **is** the fractional graph
  element `fracLapRep`;
* `conjSymmetric_timePrimitive`, `conjSymmetric_fracTimeIntegral` — the primitives really are
  real;
* `aeRestrict_synthL2_eq_zero` — vanishing on `W` in the restricted-measure sense, proved from
  the pointwise vanishing on the open set `W`;
* `eq_of_synthL2_eq` — recovery of coefficient (hence state) equality from physical `L²`
  equality;
* `RealFractionalGraph` / `RealFractionalUCP` — the real-only UCP boundary, exactly the shape
  in which the platform theorem is available, with **every domain premise proved** here;
* `fractionalUCP_of_real` — the real/imaginary decomposition showing that the real-only
  boundary already implies the complex predicate `FractionalUCP` used by the v4.0 bridge.  So
  every conditional theorem of the bridge is available from the real hypothesis alone.

Part of `LiWangWienerSmoothObservationPacket` v5.0.
-/
import LiWangWiener.UCPBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. Sobolev membership and the physical `L²` fractional graph -/

theorem summable_norm_sq_frac_of_coeff_rel {v : Wiener1} {F : Wiener}
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) :
    Summable fun k : Gam => ‖(fracSymbol α k : ℂ) * v.coeff k‖ ^ 2 :=
  (summable_norm_sq F).congr (fun k => by rw [hrel k])

/-- **Explicit `H^{2α}` membership.**  If `v : A¹` and its fractional Laplacian `F : A` are
actual Wiener elements linked by the coefficient relation, then `v ∈ H^{2α}`. -/
theorem memSobolev_of_coeff_rel (hα : 0 < α) {v : Wiener1} {F : Wiener}
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) :
    MemSobolev (2 * α) v.coeff :=
  memSobolev_two_alpha hα (summable_norm_sq (incl v)) (summable_norm_sq_frac_of_coeff_rel hrel)

/-- **The physical `L²` fractional-graph membership.**  The `L²` synthesis of `F` is literally
the fractional-Laplacian representative built from the coefficients of `v`. -/
theorem synthL2_eq_fracLapRep {v : Wiener1} {F : Wiener}
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) :
    synthL2 F = fracLapRep (α := α) v.coeff (summable_norm_sq_frac_of_coeff_rel hrel) := by
  rw [fracLapRep, ← coeffL2_toWiener2]
  congr 1
  exact lp.ext (funext fun k => by rw [toWiener2_apply, w2mk_apply, hrel k])

/-! ## 2. Realness of the actual primitives -/

theorem conjSymmetric_curveState (hT : 0 ≤ T) (u : Curve1 T) (s : ℝ) :
    ConjSymmetric (curveState hT u s).coeff := (u (clampT hT s)).conjSymmetric

/-- **The time primitive of a real curve is real.** -/
theorem conjSymmetric_timePrimitive (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    ConjSymmetric (timePrimitive hT u t).coeff := by
  intro k
  rw [coeff_timePrimitive, coeff_timePrimitive, ← intervalIntegral_conj]
  exact intervalIntegral.integral_congr (fun s _ => conjSymmetric_curveState hT u s k)

/-- **The fractional output of the primitive is real.** -/
theorem conjSymmetric_fracTimeIntegral (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    ConjSymmetric ((fracTimeIntegral hα hT g t : Wiener) : Gam → ℂ) := by
  intro k
  have hg : Continuous (sourceFun hT g) := continuous_sourceFun hT g
  have hsplit : ∀ j : Gam, ((∫ s in (0:ℝ)..t, sourceFun hT g s) : Wiener) j
      = ∫ s in (0:ℝ)..t, (sourceFun hT g s) j :=
    fun j => ((Wiener.evalCLM j).intervalIntegral_comp_comm (hg.intervalIntegrable 0 t)).symm
  show ((∫ s in (0:ℝ)..t, sourceFun hT g s)
      - incl (curveState hT (duhamelOp hα hT g) t) : Wiener) (-k) = _
  rw [lp.coeFn_sub, Pi.sub_apply, hsplit (-k)]
  have hstate : (incl (curveState hT (duhamelOp hα hT g) t)) (-k)
      = conj ((incl (curveState hT (duhamelOp hα hT g) t)) k) :=
    conjSymmetric_curveState hT (duhamelOp hα hT g) t k
  rw [hstate]
  have hint : (∫ s in (0:ℝ)..t, (sourceFun hT g s) (-k))
      = conj (∫ s in (0:ℝ)..t, (sourceFun hT g s) k) := by
    rw [← intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun s _ => conjSymmetric_sourceFun hT g s k)
  rw [hint]
  show conj _ - conj _ = conj (((∫ s in (0:ℝ)..t, sourceFun hT g s)
      - incl (curveState hT (duhamelOp hα hT g) t) : Wiener) k)
  rw [lp.coeFn_sub, Pi.sub_apply, hsplit k, map_sub]

/-! ## 3. Vanishing on `W` in the restricted-measure sense, and recovery -/

/-- **From pointwise vanishing of the continuous field on the open set `W` to vanishing of the
physical `L²` representative in the restricted-measure sense.** -/
theorem aeRestrict_synthL2_eq_zero {W : Set Torus2} (hW : MeasurableSet W) {a : Wiener}
    (h : ∀ x ∈ W, synth a x = 0) :
    (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2).restrict W] 0 := by
  have h1 : (synthL2 a : Torus2 → ℂ)
      =ᵐ[(volume : Measure Torus2).restrict W] fun x => synth a x :=
    (synthL2_apply_ae a).filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
  refine h1.trans ?_
  refine Filter.eventually_of_mem (self_mem_ae_restrict hW) ?_
  intro x hx
  exact h x hx

/-- **Recovery**: equal physical `L²` representatives force equal Fourier coefficients. -/
theorem eq_of_synthL2_eq {a b : Wiener} (h : synthL2 a = synthL2 b) : a = b := by
  rw [← coeffL2_toWiener2, ← coeffL2_toWiener2] at h
  have h2 : toWiener2 a = toWiener2 b := coeffL2.injective h
  exact lp.ext (funext fun k => by
    have := congrArg (fun c : Wiener2 => (c : Gam → ℂ) k) h2
    simpa using this)

/-- The state is recovered as well. -/
theorem wiener1_eq_of_synthL2_incl_eq {u v : Wiener1} (h : synthL2 (incl u) = synthL2 (incl v)) :
    u = v := by
  have := eq_of_synthL2_eq h
  exact Wiener1.coeff_injective (funext fun k => congrFun (congrArg (fun a : Wiener =>
    (a : Gam → ℂ)) this) k)

/-! ## 4. The real-only UCP boundary -/

/-- **The real physical-`L²` fractional graph.**  Every field of this structure is *proved*
below for the actual time primitives; nothing here is a conclusion in disguise. -/
structure RealFractionalGraph (α : ℝ) (W : Set Torus2) (v : Wiener1) (F : Wiener) : Prop where
  stateReal : ConjSymmetric v.coeff
  fracReal : ConjSymmetric ((F : Gam → ℂ))
  coeffRel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k
  sobolev : MemSobolev (2 * α) v.coeff
  stateVanishes : (synthL2 (incl v) : Torus2 → ℂ)
    =ᵐ[(volume : Measure Torus2).restrict W] 0
  fracVanishes : (synthL2 F : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2).restrict W] 0

/-- **Spatial fractional unique continuation, real-only form.**  This is the exact shape in
which the platform proves the theorem: a *real* state whose physical `L²` field and physical
`L²` fractional Laplacian both vanish on `W` is zero.  It is strictly weaker than
`FractionalUCP`, and by `fractionalUCP_of_real` it already implies it. -/
def RealFractionalUCP (α : ℝ) (W : Set Torus2) : Prop :=
  ∀ (v : Wiener1) (F : Wiener), RealFractionalGraph α W v F → v = 0

/-- **All domain premises discharged.**  From the pointwise data produced by
`local_cancellation`, the real fractional graph of the primitive is constructed. -/
theorem realFractionalGraph_of_pointwise (hα : 0 < α) {W : Set Torus2} (hW : MeasurableSet W)
    {v : Wiener1} {F : Wiener} (hv : ConjSymmetric v.coeff) (hF : ConjSymmetric (F : Gam → ℂ))
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k)
    (hvW : ∀ x ∈ W, synth (incl v) x = 0) (hFW : ∀ x ∈ W, synth F x = 0) :
    RealFractionalGraph α W v F :=
  { stateReal := hv
    fracReal := hF
    coeffRel := hrel
    sobolev := memSobolev_of_coeff_rel hα hrel
    stateVanishes := aeRestrict_synthL2_eq_zero hW hvW
    fracVanishes := aeRestrict_synthL2_eq_zero hW hFW }

/-! ## 5. The real/imaginary decomposition: the real boundary implies the complex predicate -/

theorem Wiener1.summable_wt_conjRefl (u : Wiener1) :
    Summable fun k : Gam => wt k * ‖conj (u.coeff (-k))‖ := by
  have h : (fun k : Gam => wt k * ‖conj (u.coeff (-k))‖)
      = fun k : Gam => wt (-k) * ‖u.coeff (-k)‖ := by
    funext k; rw [RCLike.norm_conj, wt_neg]
  rw [h]
  exact (Equiv.neg Gam).summable_iff.2 u.summable_wt

/-- The conjugate reflection on the first-order Wiener space. -/
noncomputable def Wiener1.conjRefl (u : Wiener1) : Wiener1 :=
  Wiener1.mk (fun k => conj (u.coeff (-k))) (Wiener1.summable_wt_conjRefl u)

@[simp] theorem Wiener1.coeff_conjRefl (u : Wiener1) (k : Gam) :
    (Wiener1.conjRefl u).coeff k = conj (u.coeff (-k)) := rfl

theorem incl_conjRefl (u : Wiener1) : incl (Wiener1.conjRefl u) = conjRefl (incl u) :=
  lp.ext (funext fun _ => rfl)

/-- The combination `c · (u + d · (conjugate reflection of u))`. -/
noncomputable def comb1 (c d : ℂ) (u : Wiener1) : Wiener1 := c • (u + d • Wiener1.conjRefl u)

/-- The same combination on the Wiener algebra. -/
noncomputable def combW (c d : ℂ) (a : Wiener) : Wiener := c • (a + d • conjRefl a)

theorem coeff_comb1 (c d : ℂ) (u : Wiener1) (k : Gam) :
    (comb1 c d u).coeff k = c * (u.coeff k + d * conj (u.coeff (-k))) := rfl

theorem apply_combW (c d : ℂ) (a : Wiener) (k : Gam) :
    (combW c d a) k = c * (a k + d * conj (a (-k))) := rfl

theorem incl_comb1 (c d : ℂ) (u : Wiener1) : incl (comb1 c d u) = combW c d (incl u) := by
  rw [comb1, combW, map_smul, map_add, map_smul, incl_conjRefl]

theorem conjSymmetric_comb1 {c d : ℂ} (hc : conj c = c * d) (hd : d * conj d = 1) (u : Wiener1) :
    ConjSymmetric (comb1 c d u).coeff := by
  intro k
  rw [coeff_comb1, coeff_comb1, neg_neg, map_mul, map_add, map_mul, Complex.conj_conj, hc]
  linear_combination (-(c * u.coeff (-k))) * hd

theorem conjSymmetric_combW {c d : ℂ} (hc : conj c = c * d) (hd : d * conj d = 1) (a : Wiener) :
    ConjSymmetric ((combW c d a : Wiener) : Gam → ℂ) := by
  intro k
  rw [apply_combW, apply_combW, neg_neg, map_mul, map_add, map_mul, Complex.conj_conj, hc]
  linear_combination (-(c * a (-k))) * hd

theorem coeffRel_combW {v : Wiener1} {F : Wiener} (c d : ℂ)
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) (k : Gam) :
    (combW c d F) k = (fracSymbol α k : ℂ) * (comb1 c d v).coeff k := by
  rw [apply_combW, coeff_comb1, hrel k, hrel (-k), fracSymbol_neg, map_mul, Complex.conj_ofReal]
  ring

theorem synth_combW_eq_zero {W : Set Torus2} {a : Wiener} (c d : ℂ)
    (h : ∀ x ∈ W, synth a x = 0) (x : Torus2) (hx : x ∈ W) : synth (combW c d a) x = 0 := by
  rw [combW, map_smul, map_add, map_smul]
  show c * (synth a x + d * synth (conjRefl a) x) = 0
  rw [synth_conjRefl_apply, h x hx, map_zero, mul_zero, add_zero, mul_zero]

theorem comb1_decomposition (u : Wiener1) :
    comb1 (2⁻¹) 1 u + Complex.I • comb1 ((2 * Complex.I)⁻¹) (-1) u = u := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  show (2:ℂ)⁻¹ * (u.coeff k + 1 * conj (u.coeff (-k)))
      + Complex.I * ((2 * Complex.I)⁻¹ * (u.coeff k + (-1) * conj (u.coeff (-k)))) = u.coeff k
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

theorem conj_two : conj ((2:ℂ)) = 2 := by
  rw [show ((2:ℂ)) = ((2:ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem conj_half : conj ((2:ℂ)⁻¹) = (2:ℂ)⁻¹ * 1 := by
  rw [mul_one, map_inv₀, conj_two]

theorem conj_halfI : conj (((2 : ℂ) * Complex.I)⁻¹) = ((2 : ℂ) * Complex.I)⁻¹ * (-1) := by
  rw [map_inv₀, map_mul, Complex.conj_I, conj_two]
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  field_simp

/-- **The real-only UCP boundary already implies the complex predicate.**  Splitting a complex
state into its conjugate-symmetric real and imaginary parts, both parts satisfy the real
fractional-graph hypotheses, so the real theorem applies to each. -/
theorem fractionalUCP_of_real (hα : 0 < α) {W : Set Torus2} (hW : MeasurableSet W)
    (h : RealFractionalUCP α W) : FractionalUCP α W := by
  intro v F hrel hvW hFW
  have hd1 : (1 : ℂ) * conj (1 : ℂ) = 1 := by norm_num
  have hd2 : (-1 : ℂ) * conj (-1 : ℂ) = 1 := by
    rw [map_neg, map_one]; ring
  have h1 : comb1 ((2:ℂ)⁻¹) 1 v = 0 :=
    h _ (combW ((2:ℂ)⁻¹) 1 F) (realFractionalGraph_of_pointwise hα hW
      (conjSymmetric_comb1 conj_half hd1 v)
      (conjSymmetric_combW conj_half hd1 F)
      (coeffRel_combW _ _ hrel)
      (fun x hx => by rw [incl_comb1]; exact synth_combW_eq_zero _ _ hvW x hx)
      (fun x hx => synth_combW_eq_zero _ _ hFW x hx))
  have h2 : comb1 (((2:ℂ) * Complex.I)⁻¹) (-1) v = 0 :=
    h _ (combW (((2:ℂ) * Complex.I)⁻¹) (-1) F) (realFractionalGraph_of_pointwise hα hW
      (conjSymmetric_comb1 conj_halfI hd2 v)
      (conjSymmetric_combW conj_halfI hd2 F)
      (coeffRel_combW _ _ hrel)
      (fun x hx => by rw [incl_comb1]; exact synth_combW_eq_zero _ _ hvW x hx)
      (fun x hx => synth_combW_eq_zero _ _ hFW x hx))
  have hdec := comb1_decomposition v
  rw [h1, h2, smul_zero, add_zero] at hdec
  exact hdec.symm


/-! ## 6. The packaged interface for the actual primitives -/

/-- Agreement of the Wiener and physical `L²` representatives of a state. -/
theorem synthL2_eq_synth_ae (a : Wiener) :
    (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2)] fun x => synth a x :=
  synthL2_apply_ae a

/-- **The real fractional graph of the actual time primitive.**

For `1/2 < α < 1`, a nonempty open observation region `W`, and two mild solutions of the *same*
source whose measured state and velocity agree on `W`, the pair

  `(timePrimitive (u₁ - u₂) t , fracTimeIntegral g t)`

is a real physical-`L²` fractional graph for every `t ∈ [0,T]`: realness, the Fourier
coefficient relation, `H^{2α}` membership and the restricted-measure vanishing on `W` are all
proved, not assumed. -/
theorem realFractionalGraph_timePrimitive (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 ≤ T)
    {W : Set Torus2} (hW : IsOpen W) (hWne : W.Nonempty)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f)
    (hobsState : ∀ (t : TimeI T), ∀ x ∈ W,
      synth (incl (u₁ t).val) x = synth (incl (u₂ t).val) x)
    (hobsVel : ∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl (u₁ t).val)) x
        = synth (velocity m₂ hm₂ j (incl (u₂ t).val)) x)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    RealFractionalGraph α W (timePrimitive hT (u₁ - u₂) t)
      (fracTimeIntegral hα hT
        (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t) := by
  have hpos : (0:ℝ) < α := by linarith
  obtain ⟨x₀, hx₀⟩ := hWne
  refine realFractionalGraph_of_pointwise hpos hW.measurableSet
    (conjSymmetric_timePrimitive hT (u₁ - u₂) t)
    (conjSymmetric_fracTimeIntegral hα hT _ t)
    (fun k => (local_cancellation hα hT hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht
      hx₀).2.2 k)
    (fun x hx => (local_cancellation hα hT hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht hx).1)
    (fun x hx => (local_cancellation hα hT hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht hx).2.1)

/-- **Conditional on the real-only UCP boundary.**  Two mild solutions of the same source with
equal measured state and velocity on `W` coincide.  This is `curve_eq_of_ucp` with the weaker,
platform-shaped hypothesis. -/
theorem curve_eq_of_realUCP (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hWne : W.Nonempty) (hUCP : RealFractionalUCP α W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT.le m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT.le f)
    (h₂ : u₂ + sourceQuad hα hT.le m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT.le f)
    (hobsState : ∀ (t : TimeI T), ∀ x ∈ W,
      synth (incl (u₁ t).val) x = synth (incl (u₂ t).val) x)
    (hobsVel : ∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl (u₁ t).val)) x
        = synth (velocity m₂ hm₂ j (incl (u₂ t).val)) x) :
    u₁ = u₂ :=
  curve_eq_of_ucp hα hT hW
    (fractionalUCP_of_real (by linarith) hW.measurableSet hUCP) hm₁ hr₁ hm₂ hr₂ h₁ h₂
    hobsState hobsVel

/-! ## 7. What `fracTimeIntegral` is, and what it is not -/

/-- **`fracTimeIntegral` is the fractional multiplier applied to the time primitive.**

By definition `fracTimeIntegral hα hT g t = ∫₀ᵗ g(s) ds − u(t)` where `u = J_T g`; the content
of the theorem is that its Fourier coefficients are `λ_k` times those of the time primitive of
`u`.  The definition alone is **not** a construction of the Bochner integral of a pointwise
fractional-Laplacian field.  That construction — a strongly measurable `L²`-valued field
`s ↦ (-Δ)^α u(s)`, its Bochner integrability, and the identification of `synthL2` of
`fracTimeIntegral` with its time integral — is carried out separately in
`PhysicalFractionalField` (`synthL2_fracTimeIntegral`). -/
theorem fracTimeIntegral_is_frac_of_primitive (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T)
    (k : Gam) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (fracTimeIntegral hα hT g t) k
      = (fracSymbol α k : ℂ) * (timePrimitive hT (duhamelOp hα hT g) t).coeff k := by
  rw [coeff_fracTimeIntegral hα hT g k ht, coeff_timePrimitive]


end LiWang.WienerModel
