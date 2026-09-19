/-
# The paper's `s = 3` forward energy package

Li–Wang, Proposition 3.1, places the solution in

```
    L^∞(0,T; L^q(𝕋²)) ∩ L^∞(0,T; H^s(𝕋²)) ∩ L²(0,T; H^{s+α}(𝕋²)),
    1/2 < α < 1,      0 < 1/q < α − 1/2,
```

for any `s > 0`; for a smooth compactly supported source we take `s = 3`.  This module proves
each of the three memberships for the packet's **constructed** small-source solution, reusing
the v8.0 tame machinery and adding exactly one more Picard bootstrap.

* `WB4_of_mild` — a uniform `wt⁴` bound, from a `wt³` bound on the source (`SmoothThirdOrder`);
  the bound is proved for the Picard iterates and transferred coefficientwise, exactly as in
  `WB_mild_of_picard`.  No convergence in a stronger norm is used.
* `sobBound_of_WB` — a `wtʳ` bound gives the `Hʳ` finite-sum bound, hence summability.
* `sobWeight_le_rho_pow` — `H⁴ ⊂ H^{3+α}` **because `α < 1`**; the paper's upper bound on `α`
  is used here and nowhere else.
* `lintegral_sobEnergy_le`, `integrableOn_sobEnergy` — the uniform `H^{3+α}` bound on `[0,T]`
  gives the genuine `L²(0,T; H^{3+α})` estimate, with measurability proved rather than assumed.
* `paperExp`, `eLpNorm_synthL2_le` — an admissible finite exponent `q` with `1/q < α − 1/2`, and
  the uniform `L^q(𝕋²)` bound of the synthesized state.

Part of `LiWangFormalizationPaperMapAlignmentPacket` v9.0.
-/
import LiWangFormalization.SmoothThirdOrder
import LiWangFormalization.SmallSourceSobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The `Hʳ` bound from a `wtʳ` bound -/

/-- **A `wtʳ` bound gives the `Hʳ` bound**, for every natural `r`. -/
theorem sobBound_of_WB {r : ℕ} {R : ℝ} {c : Gam → ℂ} (h : WB r R c) :
    ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ r * ‖c k‖ ^ 2) ≤ R ^ 2 := by
  intro F
  have hterm : ∀ k ∈ F, rho k ^ r * ‖c k‖ ^ 2 ≤ (wt k ^ r * ‖c k‖) ^ 2 := by
    intro k _
    have hρ : rho k ^ r ≤ (wt k ^ 2) ^ r :=
      pow_le_pow_left₀ (rho_pos k).le (rho_le_wt_sq k) r
    have hc2 : (0:ℝ) ≤ ‖c k‖ ^ 2 := sq_nonneg _
    have hexp : (wt k ^ r * ‖c k‖) ^ 2 = (wt k ^ 2) ^ r * ‖c k‖ ^ 2 := by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hρ hc2
  have hsq : (∑ k ∈ F, (wt k ^ r * ‖c k‖) ^ 2) ≤ (∑ k ∈ F, wt k ^ r * ‖c k‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => wt_pow_norm_nonneg r c k)
  have hR : (∑ k ∈ F, wt k ^ r * ‖c k‖) ^ 2 ≤ R ^ 2 := by
    have h0 : (0:ℝ) ≤ ∑ k ∈ F, wt k ^ r * ‖c k‖ :=
      Finset.sum_nonneg (fun k _ => wt_pow_norm_nonneg r c k)
    nlinarith [h F, h.nonneg]
  calc (∑ k ∈ F, rho k ^ r * ‖c k‖ ^ 2)
      ≤ ∑ k ∈ F, (wt k ^ r * ‖c k‖) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ (∑ k ∈ F, wt k ^ r * ‖c k‖) ^ 2 := hsq
    _ ≤ R ^ 2 := hR

theorem rho_pow_norm_sq_nonneg (r : ℕ) (c : Gam → ℂ) (k : Gam) :
    0 ≤ rho k ^ r * ‖c k‖ ^ 2 := by
  have := (rho_pos k).le; positivity

theorem summable_rho_pow_of_WB {r : ℕ} {R : ℝ} {c : Gam → ℂ} (h : WB r R c) :
    Summable fun k : Gam => rho k ^ r * ‖c k‖ ^ 2 :=
  summable_of_finset_sum_le (rho_pow_norm_sq_nonneg r c) (sobBound_of_WB h)

theorem tsum_rho_pow_le_of_WB {r : ℕ} {R : ℝ} {c : Gam → ℂ} (h : WB r R c) :
    (∑' k : Gam, rho k ^ r * ‖c k‖ ^ 2) ≤ R ^ 2 :=
  tsum_le_of_finset_sum_le (rho_pow_norm_sq_nonneg r c) (sobBound_of_WB h)

/-! ## 2. `H⁴ ⊂ H^{3+α}` — this is where `α < 1` is used -/

theorem sobWeight_eq_rho_rpow (s : ℝ) (k : Gam) : sobWeight s k = rho k ^ s := rfl

/-- The Sobolev weight of order `s` is dominated by the integer weight `ρʳ` whenever `s ≤ r`. -/
theorem sobWeight_le_rho_pow {s : ℝ} {r : ℕ} (hsr : s ≤ (r : ℝ)) (k : Gam) :
    sobWeight s k ≤ rho k ^ r := by
  rw [sobWeight_eq_rho_rpow]
  calc rho k ^ s ≤ rho k ^ ((r : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_rho k) hsr
    _ = rho k ^ r := Real.rpow_natCast _ _

theorem sobWeight_nonneg (s : ℝ) (k : Gam) : 0 ≤ sobWeight s k := (sobWeight_pos s k).le

/-- **The `H^{3+α}` bound from a `wt⁴` bound**, valid exactly because `α ≤ 1`. -/
theorem sobWeight_bound_of_WB4 (hα1 : α ≤ 1) {R : ℝ} {c : Gam → ℂ} (h : WB 4 R c) :
    ∀ F : Finset Gam, (∑ k ∈ F, sobWeight (3 + α) k * ‖c k‖ ^ 2) ≤ R ^ 2 := by
  intro F
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sobBound_of_WB h F)
  exact mul_le_mul_of_nonneg_right (sobWeight_le_rho_pow (by push_cast; linarith) k)
    (sq_nonneg _)

theorem sobWeight_norm_sq_nonneg (s : ℝ) (c : Gam → ℂ) (k : Gam) :
    0 ≤ sobWeight s k * ‖c k‖ ^ 2 :=
  mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)

/-- **Membership in the coefficient Sobolev space `H^{3+α}`.** -/
theorem memSobolev_of_WB4 (hα1 : α ≤ 1) {R : ℝ} {c : Gam → ℂ} (h : WB 4 R c) :
    MemSobolev (3 + α) c :=
  summable_of_finset_sum_le (sobWeight_norm_sq_nonneg (3 + α) c) (sobWeight_bound_of_WB4 hα1 h)

/-- The squared `H^s` norm of a coefficient family. -/
noncomputable def sobEnergy (s : ℝ) (c : Gam → ℂ) : ℝ :=
  ∑' k : Gam, sobWeight s k * ‖c k‖ ^ 2

theorem sobEnergy_nonneg (s : ℝ) (c : Gam → ℂ) : 0 ≤ sobEnergy s c :=
  tsum_nonneg (sobWeight_norm_sq_nonneg s c)

theorem sobEnergy_le_of_WB4 (hα1 : α ≤ 1) {R : ℝ} {c : Gam → ℂ} (h : WB 4 R c) :
    sobEnergy (3 + α) c ≤ R ^ 2 :=
  tsum_le_of_finset_sum_le (sobWeight_norm_sq_nonneg (3 + α) c) (sobWeight_bound_of_WB4 hα1 h)

/-! ## 3. The `L²`-in-time `H^{3+α}` estimate -/

variable {hT : 0 ≤ T}

theorem measurable_sobEnergy_ennreal (hα1 : α ≤ 1) {u : Curve1 T} {R : ℝ}
    (h4 : ∀ t : ℝ, WB 4 R (curveState hT u t).coeff) :
    Measurable fun t : ℝ =>
      ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff) := by
  have hcong : (fun t : ℝ => ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff))
      = fun t : ℝ => ∑' k : Gam,
          ENNReal.ofReal (sobWeight (3 + α) k * ‖(curveState hT u t).coeff k‖ ^ 2) := by
    funext t
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun k => sobWeight_norm_sq_nonneg (3 + α) _ k)
      (memSobolev_of_WB4 hα1 (h4 t))
  rw [hcong]
  refine Measurable.ennreal_tsum (fun k => ?_)
  refine ENNReal.measurable_ofReal.comp ?_
  exact (continuous_const.mul
    (((continuous_coeff_curveState hT u k).norm).pow 2)).measurable

theorem measurable_sobEnergy (hα1 : α ≤ 1) {u : Curve1 T} {R : ℝ}
    (h4 : ∀ t : ℝ, WB 4 R (curveState hT u t).coeff) :
    Measurable fun t : ℝ => sobEnergy (3 + α) (curveState hT u t).coeff := by
  have hre : (fun t : ℝ => sobEnergy (3 + α) (curveState hT u t).coeff)
      = fun t : ℝ =>
        (ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff)).toReal := by
    funext t
    rw [ENNReal.toReal_ofReal (sobEnergy_nonneg _ _)]
  rw [hre]
  exact ENNReal.measurable_toReal.comp (measurable_sobEnergy_ennreal hα1 h4)

/-- **The `L²(0,T; H^{3+α})` estimate.**  A uniform `wt⁴` bound on `[0,T]` gives the paper's
time-integrated `H^{3+α}` energy bound. -/
theorem lintegral_sobEnergy_le (hα1 : α ≤ 1) {u : Curve1 T} {R : ℝ}
    (h4 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 4 R (curveState hT u t).coeff) :
    (∫⁻ t in Set.Ioc (0:ℝ) T,
        ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff))
      ≤ ENNReal.ofReal (T * R ^ 2) := by
  have hpt : ∀ t ∈ Set.Ioc (0:ℝ) T,
      ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff)
        ≤ ENNReal.ofReal (R ^ 2) := by
    intro t ht
    exact ENNReal.ofReal_le_ofReal (sobEnergy_le_of_WB4 hα1 (h4 t ⟨ht.1.le, ht.2⟩))
  calc (∫⁻ t in Set.Ioc (0:ℝ) T,
          ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff))
      ≤ ∫⁻ _t in Set.Ioc (0:ℝ) T, ENNReal.ofReal (R ^ 2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := T))]
          with t ht using hpt t ht
    _ = ENNReal.ofReal (R ^ 2) * (volume : Measure ℝ) (Set.Ioc (0:ℝ) T) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (T * R ^ 2) := by
        rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The real-valued form: the `H^{3+α}` energy is integrable in time on `(0,T]`. -/
theorem integrableOn_sobEnergy (hα1 : α ≤ 1) {u : Curve1 T} {R : ℝ}
    (h4 : ∀ t : ℝ, WB 4 R (curveState hT u t).coeff) :
    IntegrableOn (fun t : ℝ => sobEnergy (3 + α) (curveState hT u t).coeff)
      (Set.Ioc (0:ℝ) T) volume := by
  have hmeas : Measurable fun t : ℝ => sobEnergy (3 + α) (curveState hT u t).coeff :=
    measurable_sobEnergy hα1 h4
  haveI hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine Integrable.mono' (g := fun _ : ℝ => R ^ 2) (integrable_const _)
    hmeas.aestronglyMeasurable ?_
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sobEnergy_nonneg _ _)]
    exact sobEnergy_le_of_WB4 hα1 (h4 t)

/-- **Almost-everywhere measurability of the `H^{3+α}` energy in time**, from continuity of the
Fourier coordinates on `[0,T]` together with genuine summability at each time.  Measurability is
proved, never assumed, and the almost-everywhere summability hypothesis is what keeps `tsum = 0`
from standing in for a convergent sum. -/
theorem aemeasurable_sobEnergy_of_continuousOn {θ : ℝ → TorusL2}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hsum : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (3 + α) (fun k => l2coeff k (θ t))) :
    AEMeasurable (fun t : ℝ => ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t))))
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := by
  have hsub : Set.Ioc (0:ℝ) T ⊆ Set.Icc (0:ℝ) T := fun t ht => ⟨ht.1.le, ht.2⟩
  have hterm : ∀ k : Gam, AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (sobWeight (3 + α) k * ‖l2coeff k (θ t)‖ ^ 2))
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := by
    intro k
    have hc : ContinuousOn (fun t : ℝ => sobWeight (3 + α) k * ‖l2coeff k (θ t)‖ ^ 2)
        (Set.Ioc (0:ℝ) T) :=
      continuousOn_const.mul (((hcont k).mono hsub).norm.pow 2)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable measurableSet_Ioc)
  have h1 : AEMeasurable (fun t : ℝ => ∑' k : Gam,
        ENNReal.ofReal (sobWeight (3 + α) k * ‖l2coeff k (θ t)‖ ^ 2))
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) := AEMeasurable.ennreal_tsum hterm
  have h2 : (fun t : ℝ => ∑' k : Gam,
        ENNReal.ofReal (sobWeight (3 + α) k * ‖l2coeff k (θ t)‖ ^ 2))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)]
      (fun t : ℝ => ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t)))) := by
    filter_upwards [hsum] with t ht
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun k => sobWeight_norm_sq_nonneg (3 + α) (fun j => l2coeff j (θ t)) k) ht).symm
  exact h1.congr h2

/-! ## 4. The admissible `L^q` exponent and the `L^q(𝕋²)` bound -/

/-- An admissible Lebesgue exponent for the paper's class: `1/q = (α − 1/2)/2 < α − 1/2`. -/
noncomputable def paperExp (α : ℝ) : ℝ := 4 / (2 * α - 1)

theorem paperExp_pos (hα : 1 / 2 < α) : 0 < paperExp α := by
  rw [paperExp]; have : 0 < 2 * α - 1 := by linarith
  positivity

theorem four_lt_paperExp (hα : 1 / 2 < α) (hα1 : α < 1) : 4 < paperExp α := by
  rw [paperExp]
  have h1 : 0 < 2 * α - 1 := by linarith
  have h2 : 2 * α - 1 < 1 := by linarith
  rw [lt_div_iff₀ h1]
  nlinarith

theorem inv_paperExp_pos (hα : 1 / 2 < α) : 0 < 1 / paperExp α :=
  one_div_pos.2 (paperExp_pos hα)

/-- **The paper's exponent inequality** `0 < 1/q < α − 1/2`. -/
theorem inv_paperExp_lt (hα : 1 / 2 < α) : 1 / paperExp α < α - 1 / 2 := by
  have h1 : 0 < 2 * α - 1 := by linarith
  rw [paperExp, one_div_div]
  linarith

theorem torus_measure_univ : (volume : Measure Torus2) Set.univ = 1 := by
  have : IsProbabilityMeasure (volume : Measure Torus2) := inferInstance
  exact measure_univ

/-- **The synthesized state is uniformly bounded in every `L^p(𝕋²)`.**  The torus has total
mass one, so the `L^p` norm is dominated by the sup norm, which is dominated by the Wiener
norm. -/
theorem eLpNorm_synthL2_le (p : ℝ≥0∞) (a : Wiener) :
    eLpNorm ((synthL2 a : Torus2 → ℂ)) p (volume : Measure Torus2) ≤ ENNReal.ofReal ‖a‖ := by
  have hae : ∀ᵐ x ∂(volume : Measure Torus2), ‖(synthL2 a : Torus2 → ℂ) x‖ ≤ ‖a‖ := by
    filter_upwards [synthL2_apply_ae a] with x hx
    rw [hx]
    exact le_trans ((synth a).norm_coe_le_norm x) (norm_synth_apply_le a)
  have hb := eLpNorm_le_of_ae_bound (μ := (volume : Measure Torus2))
    (f := (synthL2 a : Torus2 → ℂ)) (p := p) hae
  rwa [torus_measure_univ, ENNReal.one_rpow, one_mul] at hb

theorem memLp_synthL2 (p : ℝ≥0∞) (a : Wiener) :
    MemLp ((synthL2 a : Torus2 → ℂ)) p (volume : Measure Torus2) :=
  ⟨Lp.aestronglyMeasurable _,
    lt_of_le_of_lt (eLpNorm_synthL2_le p a) ENNReal.ofReal_lt_top⟩

/-! ## 5. The fourth-weight bootstrap -/

section Boot

variable {hα : 1 / 2 < α} {hm : IsBddSymbol m} {hr : IsRealSymbol m}

/-- **One more tame bootstrap.**  From `wt¹`, `wt²` and `wt³` bounds on the source and smallness
of the `A¹` norm, the constructed mild solution has a uniform `wt⁴` bound on `[0,T]`.  As in
v8.0 the bound is proved for the Picard iterates and transferred to the actual `A¹` limit
coefficientwise by `WB_mild_of_picard`. -/
theorem WB4_of_mild {f : Curve0 T} {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b) (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ)
    (hbρ : b * ρ ≤ 1 / 4) (hfsmall : ‖duhamelOp hα hT f‖ ≤ ρ / 2)
    {S1 S2 S3 : ℝ} (hS10 : 0 ≤ S1) (hS20 : 0 ≤ S2) (hS30 : 0 ≤ S3)
    (hS1 : ∀ s : ℝ, WB 1 S1 (fun k => (sourceFun hT f s) k))
    (hS2 : ∀ s : ℝ, WB 2 S2 (fun k => (sourceFun hT f s) k))
    (hS3 : ∀ s : ℝ, WB 3 S3 (fun k => (sourceFun hT f s) k))
    (habs1 : duhamelConst α T * (transportConst 1 C * ρ) ≤ 1 / 2)
    (habs2 : duhamelConst α T * (transportConst 2 C * ρ) ≤ 1 / 2)
    (habs3 : duhamelConst α T * (transportConst 3 C * ρ) ≤ 1 / 2)
    {u : Curve1 T} (hu : ‖u‖ ≤ ρ)
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    ∃ R4 : ℝ, 0 ≤ R4 ∧ ∀ t ∈ Set.Icc (0:ℝ) T, WB 4 R4 (curveState hT u t).coeff := by
  have hK0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  have hcc : ∀ r : ℕ, (0:ℝ) ≤ transportConst r C := by
    intro r; rw [transportConst]; have := Real.pi_pos; positivity
  have hball : ∀ n : ℕ, ∀ s : ℝ, ‖curveState hT (picard hα hT hm hr f n) s‖ ≤ ρ := by
    intro n s
    exact le_trans (norm_curveState_le hT _ s) (picard_norm_le hb hb0 hρ0 hbρ hfsmall n)
  have hR1 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 1 ρ (curveState hT (picard hα hT hm hr f n) t).coeff :=
    fun n t _ => (WB.wiener1 (curveState hT (picard hα hT hm hr f n) t)).mono (hball n t)
  set R2 : ℝ := 2 * ((S1 + transportConst 1 C * (ρ * ρ)) * duhamelConst α T) with hR2def
  have hR2 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 2 R2 (curveState hT (picard hα hT hm hr f n) t).coeff :=
    fun n => WB_picard_uniform hC hb hb0 hρ0 hbρ hfsmall hS10 hρ0 hS1 hR1 habs1 n
  have hR20 : 0 ≤ R2 := by
    rw [hR2def]
    have h : (0:ℝ) ≤ transportConst 1 C * (ρ * ρ) := mul_nonneg (hcc 1) (by positivity)
    nlinarith
  set R3 : ℝ := 2 * ((S2 + transportConst 2 C * (R2 * ρ)) * duhamelConst α T) with hR3def
  have hR3 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 3 R3 (curveState hT (picard hα hT hm hr f n) t).coeff :=
    fun n => WB_picard_uniform hC hb hb0 hρ0 hbρ hfsmall hS20 hR20 hS2 hR2 habs2 n
  have hR30 : 0 ≤ R3 := by
    rw [hR3def]
    have h : (0:ℝ) ≤ transportConst 2 C * (R2 * ρ) := mul_nonneg (hcc 2) (by positivity)
    nlinarith
  set R4 : ℝ := 2 * ((S3 + transportConst 3 C * (R3 * ρ)) * duhamelConst α T) with hR4def
  have hR4 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 4 R4 (curveState hT (picard hα hT hm hr f n) t).coeff :=
    fun n => WB_picard_uniform hC hb hb0 hρ0 hbρ hfsmall hS30 hR30 hS3 hR3 habs3 n
  have hR40 : 0 ≤ R4 := by
    rw [hR4def]
    have h : (0:ℝ) ≤ transportConst 3 C * (R3 * ρ) := mul_nonneg (hcc 3) (by positivity)
    nlinarith
  refine ⟨R4, hR40, fun t ht => ?_⟩
  exact WB_mild_of_picard hb hb0 hρ0 hbρ hfsmall hu hmild (fun n => hR4 n t ht)

end Boot

end LiWang.Formalization
