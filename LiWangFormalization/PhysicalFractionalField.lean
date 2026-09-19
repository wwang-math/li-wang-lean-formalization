/-
# The actual time-dependent fractional-Laplacian field, and the identification of
# `fracTimeIntegral` with its Bochner integral

`fracTimeIntegral hα hT g t` is *defined* as `∫₀ᵗ g(s) ds − u(t)`.  That definition alone proves
nothing about a pointwise field `s ↦ (-Δ)^α u(s)`.  This module builds the field and proves the
identification:

* `w2mult` — a bounded Fourier multiplier on the coefficient `ℓ²` carrier;
* `fracFieldW2 hα hT g t : Wiener2` — the coefficient family `λ_k u_k(t)`, defined everywhere and
  equal to that family exactly on the (co-null) set where it is square summable;
* `aestronglyMeasurable_fracFieldW2` — **strong measurability in time**, proved as an almost
  everywhere limit of the finite-rank truncations `fracTrunc α (F n)`, which are continuous;
* `lintegral_norm_sq_fracFieldW2_le`, `integrable_norm_sq_fracFieldW2` and
  `integrableOn_fracFieldW2` — the `L²`-in-time bound
  `∫₀ᵀ ‖(-Δ)^α u(s)‖² ds ≤ T‖g‖²`, obtained from the existing sum–integral estimate by
  `lintegral_tsum`, and hence Bochner integrability on a finite interval;
* `w2_fracTimeIntegral` and `synthL2_fracTimeIntegral` — **the identification theorem**:
  `synthL2 (fracTimeIntegral hα hT g t) = ∫₀ᵗ (-Δ)^α u(s) ds` in `L²(𝕋²)`.

The identification is proved through measurability, integrability and injectivity of the Fourier
coefficients — the integral is computed coordinatewise against the bounded evaluation functional
and matched with `coeff_fracTimeIntegral`.  Nothing is defined by the desired equation.

The exceptional null set is handled explicitly throughout: `ae_fracSummable` names it, and every
statement that uses the coefficient formula is either restricted to it or stated `∀ᵐ`.

Part of `LiWangFormalizationPhysicalPDEBridgePacket` v7.0.
-/
import LiWangFormalization.TerminalControl

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal NNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. A bounded Fourier multiplier on the coefficient `ℓ²` carrier -/

theorem summable_norm_sq_mult {c : Gam → ℂ} {C : ℝ} (hC : ∀ k, ‖c k‖ ≤ C) (y : Wiener2) :
    Summable fun k : Gam => ‖c k * y k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((summable_norm_sq_lp2 y).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC k) 2) (sq_nonneg _)

theorem norm_w2mk_mult_le {c : Gam → ℂ} {C : ℝ} (hC : ∀ k, ‖c k‖ ≤ C) (y : Wiener2) :
    ‖w2mk (fun k => c k * y k) (summable_norm_sq_mult hC y)‖ ≤ C * ‖y‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (c 0)) (hC 0)
  have hsq : ‖w2mk (fun k => c k * y k) (summable_norm_sq_mult hC y)‖ ^ 2 ≤ (C * ‖y‖) ^ 2 := by
    rw [norm_w2mk_sq, mul_pow, norm_lp2_sq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_sq_mult hC y)
      ((summable_norm_sq_lp2 y).mul_left _)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC k) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (w2mk (fun k => c k * y k) (summable_norm_sq_mult hC y)),
    mul_nonneg hC0 (norm_nonneg y), hsq]

/-- **A bounded Fourier multiplier** on `ℓ²(Γ)`. -/
noncomputable def w2mult (c : Gam → ℂ) {C : ℝ} (hC : ∀ k, ‖c k‖ ≤ C) : Wiener2 →L[ℂ] Wiener2 :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun y => w2mk (fun k => c k * y k) (summable_norm_sq_mult hC y)
      map_add' := fun y z => lp.ext (funext fun k => by
        show c k * ((y + z) k) = c k * y k + c k * z k
        rw [lp.coeFn_add, Pi.add_apply]; ring)
      map_smul' := fun r y => lp.ext (funext fun k => by
        show c k * ((r • y) k) = r * (c k * y k)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring) }
    ⟨C, fun y => norm_w2mk_mult_le hC y⟩

@[simp] theorem w2mult_apply (c : Gam → ℂ) {C : ℝ} (hC : ∀ k, ‖c k‖ ≤ C) (y : Wiener2) (k : Gam) :
    (w2mult c hC y) k = c k * y k := rfl

/-- The bounded evaluation functional on the coefficient `ℓ²` carrier. -/
noncomputable def Wiener2.evalCLM (k : Gam) : Wiener2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => y k
      map_add' := fun y z => by rw [lp.coeFn_add, Pi.add_apply]
      map_smul' := fun r y => by rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; rfl }
    1 (fun y => by simpa using lp.norm_apply_le_norm (by norm_num) y k)

@[simp] theorem Wiener2.evalCLM_apply (k : Gam) (y : Wiener2) : Wiener2.evalCLM k y = y k := rfl

/-! ## 2. The truncated fractional multiplier: finite rank, hence continuous in time -/

/-- The fractional symbol cut off outside a finite set of frequencies. -/
noncomputable def truncSymbol (α : ℝ) (F : Finset Gam) : Gam → ℂ :=
  fun k => if k ∈ F then ((fracSymbol α k : ℝ) : ℂ) else 0

theorem truncSymbol_bound (α : ℝ) (F : Finset Gam) (k : Gam) :
    ‖truncSymbol α F k‖ ≤ ∑ p ∈ F, fracSymbol α p := by
  have hnn : ∀ p ∈ F, 0 ≤ fracSymbol α p := fun p _ => fracSymbol_nonneg α p
  by_cases hk : k ∈ F
  · rw [truncSymbol, if_pos hk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fracSymbol_nonneg α k)]
    exact Finset.single_le_sum hnn hk
  · rw [truncSymbol, if_neg hk, norm_zero]
    exact Finset.sum_nonneg hnn

/-- The finite-rank truncation of the fractional multiplier. -/
noncomputable def fracTrunc (α : ℝ) (F : Finset Gam) : Wiener2 →L[ℂ] Wiener2 :=
  w2mult (truncSymbol α F) (truncSymbol_bound α F)

@[simp] theorem fracTrunc_apply (α : ℝ) (F : Finset Gam) (y : Wiener2) (k : Gam) :
    (fracTrunc α F y) k = truncSymbol α F k * y k := rfl

/-! ## 3. The coefficient field of the mild state, and the fractional field -/

/-- The mild state at time `t`, in the coefficient `ℓ²` carrier. -/
noncomputable def mildCoeff (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) : Wiener2 :=
  toWiener2 (incl (curveState hT (duhamelOp hα hT g) t))

@[simp] theorem mildCoeff_apply (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) (k : Gam) :
    (mildCoeff hα hT g t) k = (curveState hT (duhamelOp hα hT g) t).coeff k := rfl

theorem continuous_mildCoeff (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    Continuous (mildCoeff hα hT g) :=
  (toWiener2CLM.comp incl).continuous.comp (continuous_curveState hT _)

/-- The square-summability of the fractional multiplier of the state at time `t`.  This is the
property that holds off the exceptional null set. -/
def FracSummableAt (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) : Prop :=
  Summable fun k : Gam =>
    ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2

theorem ae_fracSummable (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)), FracSummableAt hα hT g t :=
  ae_summable_fracSymbol_sq hα hT g

open scoped Classical in
/-- **The `ℓ²`-valued fractional-Laplacian field of the mild state.**  Defined everywhere; equal
to the coefficient family `λ_k u_k(t)` exactly where that family is square summable, which is
almost every `t` (`ae_fracSummable`). -/
noncomputable def fracFieldW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) : Wiener2 :=
  if h : FracSummableAt hα hT g t then
    w2mk (fun k => (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k) h
  else 0

theorem fracFieldW2_apply {hα : 1 / 2 < α} {hT : 0 ≤ T} {g : Curve0 T} {t : ℝ}
    (h : FracSummableAt hα hT g t) (k : Gam) :
    (fracFieldW2 hα hT g t) k
      = (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k := by
  rw [fracFieldW2, dif_pos h]
  rfl

theorem norm_fracFieldW2_sq {hα : 1 / 2 < α} {hT : 0 ≤ T} {g : Curve0 T} {t : ℝ}
    (h : FracSummableAt hα hT g t) :
    ‖fracFieldW2 hα hT g t‖ ^ 2
      = ∑' k : Gam,
          ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
  rw [norm_lp2_sq]
  exact tsum_congr fun k => by rw [fracFieldW2_apply h k]

/-! ## 4. Strong measurability in time -/

/-- An exhausting sequence of finite frequency sets. -/
noncomputable def freqFinset : ℕ → Finset Gam :=
  fun n => (Finset.range n).image (Classical.choose (exists_surjective_nat Gam))

theorem freqFinset_monotone : Monotone freqFinset := by
  intro m n hmn
  refine Finset.image_subset_image (fun x hx => ?_)
  exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hmn)

theorem freqFinset_mem (k : Gam) : ∃ n, k ∈ freqFinset n := by
  obtain ⟨i, hi⟩ := Classical.choose_spec (exists_surjective_nat Gam) k
  exact ⟨i + 1, Finset.mem_image.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_self i), hi⟩⟩

theorem tendsto_freqFinset : Tendsto freqFinset atTop atTop :=
  tendsto_atTop_finset_of_monotone freqFinset_monotone freqFinset_mem

theorem tendsto_fracTrunc_mildCoeff {hα : 1 / 2 < α} {hT : 0 ≤ T} {g : Curve0 T} {t : ℝ}
    (h : FracSummableAt hα hT g t) :
    Tendsto (fun n => fracTrunc α (freqFinset n) (mildCoeff hα hT g t)) atTop
      (𝓝 (fracFieldW2 hα hT g t)) := by
  set a : Gam → ℝ := fun k =>
    ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 with ha
  have hdiff : ∀ n : ℕ,
      ‖fracFieldW2 hα hT g t - fracTrunc α (freqFinset n) (mildCoeff hα hT g t)‖ ^ 2
        = ∑' x : {k : Gam // k ∉ freqFinset n}, a x := by
    intro n
    rw [norm_lp2_sq]
    have hco : ∀ k : Gam,
        ‖(fracFieldW2 hα hT g t - fracTrunc α (freqFinset n) (mildCoeff hα hT g t)) k‖ ^ 2
          = Set.indicator {k : Gam | k ∉ freqFinset n} a k := by
      intro k
      have hval : (fracFieldW2 hα hT g t - fracTrunc α (freqFinset n) (mildCoeff hα hT g t)) k
          = (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k
            - truncSymbol α (freqFinset n) k
              * (curveState hT (duhamelOp hα hT g) t).coeff k := by
        rw [lp.coeFn_sub, Pi.sub_apply, fracFieldW2_apply h k, fracTrunc_apply, mildCoeff_apply]
      by_cases hk : k ∈ freqFinset n
      · rw [hval, truncSymbol, if_pos hk, sub_self, norm_zero,
          Set.indicator_of_notMem (by simpa using hk)]
        norm_num
      · rw [hval, truncSymbol, if_neg hk, zero_mul, sub_zero,
          Set.indicator_of_mem (by simpa using hk)]
    rw [tsum_congr hco, ← tsum_subtype]
    rfl
  have hzero : Tendsto (fun n : ℕ =>
      ‖fracFieldW2 hα hT g t - fracTrunc α (freqFinset n) (mildCoeff hα hT g t)‖ ^ 2)
      atTop (𝓝 0) := by
    have hbase := (tendsto_tsum_compl_atTop_zero a).comp tendsto_freqFinset
    exact hbase.congr (fun n => (hdiff n).symm)
  have hnorm : Tendsto (fun n : ℕ =>
      ‖fracFieldW2 hα hT g t - fracTrunc α (freqFinset n) (mildCoeff hα hT g t)‖)
      atTop (𝓝 0) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp hzero
    rw [Real.sqrt_zero] at hc
    exact hc.congr (fun n => Real.sqrt_sq (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm.congr (fun n => norm_sub_rev _ _)

theorem aestronglyMeasurable_fracFieldW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    AEStronglyMeasurable (fracFieldW2 hα hT g)
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n t => fracTrunc α (freqFinset n) (mildCoeff hα hT g t)) (fun n => ?_) ?_
  · exact (((fracTrunc α (freqFinset n)).continuous.comp
      (continuous_mildCoeff hα hT g)).stronglyMeasurable).aestronglyMeasurable
  · filter_upwards [ae_fracSummable hα hT g] with t ht
    exact tendsto_fracTrunc_mildCoeff ht

/-! ## 5. The `L²`-in-time bound and Bochner integrability -/

theorem continuous_fracCoeffSq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    Continuous (fun s : ℝ =>
      ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2) :=
  ((continuous_const.mul (continuous_coeff_curveState hT _ k)).norm).pow 2

theorem integrableOn_fracCoeffSq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    IntegrableOn (fun s : ℝ =>
        ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2)
      (Set.Ioc (0:ℝ) T) volume :=
  ((continuous_fracCoeffSq hα hT g k).integrableOn_Icc (a := (0:ℝ)) (b := T)).mono_set
    Set.Ioc_subset_Icc_self

theorem lintegral_fracCoeffSq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    ∫⁻ s in Set.Ioc (0:ℝ) T,
        ENNReal.ofReal (‖(fracSymbol α k : ℂ)
          * (curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2)
      = ENNReal.ofReal ((fracSymbol α k) ^ 2
          * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2) := by
  have hcast : ∀ s : ℝ,
      ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2
        = (fracSymbol α k) ^ 2 * ‖(curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2 := by
    intro s
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fracSymbol_nonneg α k)]
  have h1 := (ofReal_integral_eq_lintegral_ofReal (integrableOn_fracCoeffSq hα hT g k)
    (Filter.Eventually.of_forall fun s => sq_nonneg _)).symm
  rw [h1]
  congr 1
  rw [intervalIntegral.integral_of_le hT, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioc (fun s _ => hcast s)

theorem lintegral_norm_sq_fracFieldW2_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    (∫⁻ s in Set.Ioc (0:ℝ) T, ENNReal.ofReal (‖fracFieldW2 hα hT g s‖ ^ 2))
      ≤ ENNReal.ofReal (T * ‖g‖ ^ 2) := by
  set A : Gam → ℝ → ℝ≥0∞ := fun k s => ENNReal.ofReal
    (‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k‖ ^ 2) with hA
  have hstep1 : (∫⁻ s in Set.Ioc (0:ℝ) T, ENNReal.ofReal (‖fracFieldW2 hα hT g s‖ ^ 2))
      = ∫⁻ s in Set.Ioc (0:ℝ) T, ∑' k : Gam, A k s := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_fracSummable hα hT g] with s hs
    rw [norm_fracFieldW2_sq hs, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs]
  have hmeas : ∀ k : Gam, AEMeasurable (A k)
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := by
    intro k
    exact (ENNReal.measurable_ofReal.comp
      (continuous_fracCoeffSq hα hT g k).measurable).aemeasurable
  have hstep2 : (∫⁻ s in Set.Ioc (0:ℝ) T, ∑' k : Gam, A k s)
      = ∑' k : Gam, ∫⁻ s in Set.Ioc (0:ℝ) T, A k s := lintegral_tsum hmeas
  have hstep3 : ∀ k : Gam, (∫⁻ s in Set.Ioc (0:ℝ) T, A k s)
      = ENNReal.ofReal ((fracSymbol α k) ^ 2
          * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2) :=
    fun k => lintegral_fracCoeffSq hα hT g k
  have hnn : ∀ k : Gam, (0:ℝ) ≤ (fracSymbol α k) ^ 2
      * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
    intro k
    have h1 : (0:ℝ) ≤ (fracSymbol α k) ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hT]
      exact setIntegral_nonneg measurableSet_Ioc (fun s _ => sq_nonneg _)
    positivity
  rw [hstep1, hstep2, tsum_congr hstep3,
    ← ENNReal.ofReal_tsum_of_nonneg hnn (summable_integral_fracSymbol_sq hα hT g)]
  exact ENNReal.ofReal_le_ofReal (tsum_integral_fracSymbol_sq_le hα hT g)

theorem integrable_norm_sq_fracFieldW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    Integrable (fun s => ‖fracFieldW2 hα hT g s‖ ^ 2)
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := by
  refine ⟨((aestronglyMeasurable_fracFieldW2 hα hT g).norm.pow 2), ?_⟩
  have he : ∀ s : ℝ, ‖‖fracFieldW2 hα hT g s‖ ^ 2‖ₑ
      = ENNReal.ofReal (‖fracFieldW2 hα hT g s‖ ^ 2) :=
    fun s => Real.enorm_eq_ofReal (sq_nonneg _)
  have hle : (∫⁻ s in Set.Ioc (0:ℝ) T, ‖‖fracFieldW2 hα hT g s‖ ^ 2‖ₑ)
      ≤ ENNReal.ofReal (T * ‖g‖ ^ 2) := by
    rw [lintegral_congr (fun s => he s)]
    exact lintegral_norm_sq_fracFieldW2_le hα hT g
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

instance isFiniteMeasure_restrict_Ioc (a b : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩

theorem integrableOn_fracFieldW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    IntegrableOn (fracFieldW2 hα hT g) (Set.Ioc (0:ℝ) T) volume := by
  have hmem : MemLp (fracFieldW2 hα hT g) 2
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_fracFieldW2 hα hT g)).2
      (integrable_norm_sq_fracFieldW2 hα hT g)
  exact hmem.integrable (by norm_num)

theorem intervalIntegrable_fracFieldW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    IntervalIntegrable (fracFieldW2 hα hT g) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
  exact (integrableOn_fracFieldW2 hα hT g).mono_set (Set.Ioc_subset_Ioc_right ht.2)

/-! ## 6. The identification theorem -/

/-- **The physical `L²(𝕋²)`-valued fractional-Laplacian field of the mild state.** -/
noncomputable def physFracField (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) : TorusL2 :=
  coeffL2 (fracFieldW2 hα hT g t)

/-- Off the exceptional null set the physical field really is `(-Δ)^α u(t)`: its Fourier
coefficients are `λ_k u_k(t)`. -/
theorem physFracField_eq_fracLapRep {hα : 1 / 2 < α} {hT : 0 ≤ T} {g : Curve0 T} {t : ℝ}
    (h : FracSummableAt hα hT g t) :
    physFracField hα hT g t
      = fracLapRep (α := α) (curveState hT (duhamelOp hα hT g) t).coeff h := by
  rw [physFracField, fracLapRep, fracFieldW2, dif_pos h]

/-- **The identification, in the coefficient carrier.** -/
theorem w2_fracTimeIntegral (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (∫ s in (0:ℝ)..t, fracFieldW2 hα hT g s) = toWiener2 (fracTimeIntegral hα hT g t) := by
  refine lp.ext (funext fun k => ?_)
  have hcomm := (Wiener2.evalCLM k).intervalIntegral_comp_comm
    (intervalIntegrable_fracFieldW2 hα hT g ht)
  have hpt : (∫ s in (0:ℝ)..t, (fracFieldW2 hα hT g s) k)
      = ∫ s in (0:ℝ)..t,
          (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc (0:ℝ) T → FracSummableAt hα hT g s :=
      (ae_restrict_iff' measurableSet_Ioc).1 (ae_fracSummable hα hT g)
    filter_upwards [hae] with s hs hsmem
    exact fracFieldW2_apply (hs (Set.Ioc_subset_Ioc_right ht.2 hsmem)) k
  show (∫ s in (0:ℝ)..t, fracFieldW2 hα hT g s) k = (fracTimeIntegral hα hT g t) k
  rw [← Wiener2.evalCLM_apply k, ← hcomm]
  show (∫ s in (0:ℝ)..t, (fracFieldW2 hα hT g s) k) = (fracTimeIntegral hα hT g t) k
  have hconst : (∫ s in (0:ℝ)..t,
        (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) s).coeff k)
      = (fracSymbol α k : ℂ)
          * ∫ s in (0:ℝ)..t, (curveState hT (duhamelOp hα hT g) s).coeff k :=
    intervalIntegral.integral_const_mul _ _
  rw [hpt, hconst, coeff_fracTimeIntegral hα hT g k ht]

/-- **The identification theorem.**  The physical synthesis of `fracTimeIntegral` *is* the
Bochner integral of the actual time-dependent fractional-Laplacian field of the mild state.

This is proved from strong measurability, Bochner integrability and injectivity of the Fourier
coefficients — the integral is evaluated coordinatewise against the bounded evaluation
functional and matched with `coeff_fracTimeIntegral`.  Nothing here is defined by the desired
equation. -/
theorem synthL2_fracTimeIntegral (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    synthL2 (fracTimeIntegral hα hT g t) = ∫ s in (0:ℝ)..t, physFracField hα hT g s := by
  have hcomm := coeffL2.toContinuousLinearMap.intervalIntegral_comp_comm
    (intervalIntegrable_fracFieldW2 hα hT g ht)
  have hphys : (∫ s in (0:ℝ)..t, physFracField hα hT g s)
      = coeffL2 (∫ s in (0:ℝ)..t, fracFieldW2 hα hT g s) := hcomm
  rw [hphys, w2_fracTimeIntegral hα hT g ht, coeffL2_toWiener2]

end LiWang.Formalization
