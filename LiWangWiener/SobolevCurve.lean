/-
# From `H³`-bounded coefficients to a continuous `A¹` curve

Step 1b of the v8.0 Sobolev-compatibility bridge.

`SobolevEmbedding.lean` produces, at each fixed time, an `A¹` element from an `H³` coefficient
family.  That alone does **not** give a `Curve1 T`: continuity in the `A¹` norm does not follow
from `L^∞_t H³` by abstract nonsense.  This file supplies the missing analysis.

* `tsum_compl_wt_le` — the **uniform tail estimate**: for every `δ > 0` and every finite set `F`,

      ∑_{k ∉ F} wt(k)|a_k| ≤ (2δ)⁻¹ ∑_{k ∉ F} wt(k)²/ρ(k)³ + (δ/2) E,

  where `E` bounds the `H³` energy.  The second term is small by choosing `δ`, the first by
  choosing `F`, and **neither choice depends on time**.
* `continuous_sobToWiener1_curve` — with continuity of each Fourier coefficient and a *uniform*
  `H³` bound, the `A¹`-valued curve is continuous.  The finitely many coefficients in `F` are
  handled by their continuity; the tail by the uniform estimate.
* `forall_le_of_ae_le` — an `H³` bound holding only almost everywhere is upgraded to *every*
  time of `[0,T]` for the continuous coefficient representative.  The upgrade is proved, with
  the endpoints handled explicitly: a relatively open nonempty subset of `[0,T]` has positive
  Lebesgue measure when `T > 0`, so a closed full-measure subset of `[0,T]` is all of `[0,T]`.
* `sobCurve` — the resulting **bounded continuous real `A¹` curve**, an actual element of
  `Curve1 T`, together with `sobCurve_coeff` and `synthL2_sobCurve` identifying its
  coefficients and its physical synthesis with the input data.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.SobolevEmbedding
import LiWangWiener.Spacetime

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.WienerModel

/-! ## 1. Summability and the energy bound from finite partial sums -/

/-- A nonnegative family with uniformly bounded partial sums is summable. -/
theorem summable_of_finset_sum_le {f : Gam → ℝ} (hf : ∀ k, 0 ≤ f k) {M : ℝ}
    (h : ∀ F : Finset Gam, (∑ k ∈ F, f k) ≤ M) : Summable f :=
  summable_of_sum_le (fun k => hf k) h

theorem tsum_le_of_finset_sum_le {f : Gam → ℝ} (hf : ∀ k, 0 ≤ f k) {M : ℝ}
    (h : ∀ F : Finset Gam, (∑ k ∈ F, f k) ≤ M) : (∑' k, f k) ≤ M :=
  Real.tsum_le_of_sum_le (fun k => hf k) h

/-- The two spellings of a complement-indexed sum agree definitionally. -/
theorem tsum_compl_spelling {f : Gam → ℝ} (F : Finset Gam) :
    (∑' k : {x : Gam // x ∉ F}, f (k : Gam))
      = ∑' k : ((F : Set Gam)ᶜ : Set Gam), f (k : Gam) := rfl

theorem sob_nonneg (c : Gam → ℂ) (k : Gam) : 0 ≤ rho k ^ 3 * ‖c k‖ ^ 2 := by
  have := (rho_pos k).le
  positivity

/-! ## 2. The uniform tail estimate -/

/-- **The uniform tail estimate.**  Only the energy bound `E` enters, so the estimate is
uniform over any family of states with that bound — in particular uniform in time. -/
theorem tsum_compl_wt_le {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2)
    {δ E : ℝ} (hδ : 0 < δ) (hE : (∑' k : Gam, rho k ^ 3 * ‖c k‖ ^ 2) ≤ E) (F : Finset Gam) :
    (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) * ‖c (k : Gam)‖)
      ≤ (1 / (2 * δ)) * (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
        + (δ / 2) * E := by
  have hws : Summable fun k : {x : Gam // x ∉ F} => wt (k : Gam) * ‖c (k : Gam)‖ :=
    (summable_wt_mul_norm h).subtype _
  have hks : Summable fun k : {x : Gam // x ∉ F} => wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3 :=
    summable_wtsq_div_rho3.subtype _
  have hes : Summable fun k : {x : Gam // x ∉ F} => rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2 :=
    h.subtype _
  have hmaj : Summable fun k : {x : Gam // x ∉ F} =>
      (1 / (2 * δ)) * (wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
        + (δ / 2) * (rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2) :=
    (hks.mul_left _).add (hes.mul_left _)
  have hstep : (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) * ‖c (k : Gam)‖)
      ≤ ∑' k : {x : Gam // x ∉ F},
          ((1 / (2 * δ)) * (wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
            + (δ / 2) * (rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2)) :=
    Summable.tsum_le_tsum (fun k => wt_mul_norm_le c hδ (k : Gam)) hws hmaj
  have hsplit : (∑' k : {x : Gam // x ∉ F},
        ((1 / (2 * δ)) * (wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
          + (δ / 2) * (rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2)))
      = (1 / (2 * δ)) * (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
        + (δ / 2) * ∑' k : {x : Gam // x ∉ F}, rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2 := by
    rw [Summable.tsum_add (hks.mul_left _) (hes.mul_left _), tsum_mul_left, tsum_mul_left]
  rw [hsplit] at hstep
  refine le_trans hstep ?_
  have htail : (∑' k : {x : Gam // x ∉ F}, rho (k : Gam) ^ 3 * ‖c (k : Gam)‖ ^ 2) ≤ E := by
    have hadd := h.sum_add_tsum_compl (s := F)
    have hnn : (0:ℝ) ≤ ∑ k ∈ F, rho k ^ 3 * ‖c k‖ ^ 2 :=
      Finset.sum_nonneg (fun k _ => sob_nonneg c k)
    rw [tsum_compl_spelling (f := fun k => rho k ^ 3 * ‖c k‖ ^ 2) F]
    linarith [hadd, hE]
  have hδ2 : (0:ℝ) ≤ δ / 2 := by linarith
  have := mul_le_mul_of_nonneg_left htail hδ2
  linarith

/-! ## 3. Continuity of the `A¹`-valued curve -/

theorem sob_diff_le {c d : Gam → ℂ} (k : Gam) :
    rho k ^ 3 * ‖c k - d k‖ ^ 2
      ≤ 2 * (rho k ^ 3 * ‖c k‖ ^ 2) + 2 * (rho k ^ 3 * ‖d k‖ ^ 2) := by
  have hρ : (0:ℝ) ≤ rho k ^ 3 := by have := (rho_pos k).le; positivity
  have htri : ‖c k - d k‖ ≤ ‖c k‖ + ‖d k‖ := norm_sub_le _ _
  have h0 : (0:ℝ) ≤ ‖c k - d k‖ := norm_nonneg _
  have hsq : ‖c k - d k‖ ^ 2 ≤ 2 * ‖c k‖ ^ 2 + 2 * ‖d k‖ ^ 2 := by
    nlinarith [norm_nonneg (c k), norm_nonneg (d k), sq_nonneg (‖c k‖ - ‖d k‖)]
  nlinarith

/-- **The time-continuity bridge.**  Continuity of every Fourier coefficient together with a
*uniform* `H³` bound gives continuity of the `A¹`-valued curve.  `L^∞_t H³` alone would not. -/
theorem continuous_sobToWiener1_curve {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k)
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) :
    Continuous fun t => sobToWiener1 (hsum t) := by
  have hM0 : 0 ≤ M := le_trans (tsum_nonneg (fun k => sob_nonneg (a 0) k)) (hM 0)
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- the energy of the difference
  set E : ℝ := 4 * M + 1 with hEdef
  have hE0 : (0:ℝ) < E := by rw [hEdef]; linarith
  have hdsum : ∀ t : ℝ, Summable fun k => rho k ^ 3 * ‖a t k - a t₀ k‖ ^ 2 := by
    intro t
    refine Summable.of_nonneg_of_le (fun k => sob_nonneg (fun j => a t j - a t₀ j) k)
      (fun k => sob_diff_le k) ?_
    exact ((hsum t).mul_left 2).add ((hsum t₀).mul_left 2)
  have hdE : ∀ t : ℝ, (∑' k : Gam, rho k ^ 3 * ‖a t k - a t₀ k‖ ^ 2) ≤ E := by
    intro t
    have hle := Summable.tsum_le_tsum (fun k => sob_diff_le (c := a t) (d := a t₀) k)
      (hdsum t) (((hsum t).mul_left 2).add ((hsum t₀).mul_left 2))
    rw [Summable.tsum_add ((hsum t).mul_left 2) ((hsum t₀).mul_left 2),
      tsum_mul_left, tsum_mul_left] at hle
    have h1 := hM t
    have h2 := hM t₀
    rw [hEdef]
    linarith
  -- choose `δ` so that the energy term is small
  obtain ⟨δ, hδ0, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ (δ / 2) * E < ε / 3 := by
    refine ⟨ε / (3 * E), by positivity, ?_⟩
    have hEne : E ≠ 0 := ne_of_gt hE0
    have hval : ε / (3 * E) / 2 * E = ε / 6 := by field_simp; ring
    rw [hval]
    linarith
  -- choose the finite set `F` so that the kernel tail is small
  obtain ⟨F, hF⟩ : ∃ F : Finset Gam,
      (1 / (2 * δ)) * (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3)
        < ε / 3 := by
    have htend := tendsto_tsum_compl_atTop_zero (fun k : Gam => wt k ^ 2 / rho k ^ 3)
    have hmul : Tendsto (fun F : Finset Gam =>
        (1 / (2 * δ)) * (∑' k : {x : Gam // x ∉ F}, wt (k : Gam) ^ 2 / rho (k : Gam) ^ 3))
        atTop (nhds ((1 / (2 * δ)) * 0)) := htend.const_mul _
    rw [mul_zero] at hmul
    exact (hmul.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 3))).exists
  -- the finitely many coefficients
  have hfincont : Continuous fun t : ℝ => ∑ k ∈ F, wt k * ‖a t k - a t₀ k‖ :=
    continuous_finset_sum F (fun k _ => continuous_const.mul
      (((hcont k).sub continuous_const).norm))
  have hfin0 : (∑ k ∈ F, wt k * ‖a t₀ k - a t₀ k‖) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp
  have hfin : ∀ᶠ t in nhds t₀, (∑ k ∈ F, wt k * ‖a t k - a t₀ k‖) < ε / 3 := by
    have := (hfincont.tendsto t₀)
    rw [hfin0] at this
    exact this.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 3))
  filter_upwards [hfin] with t ht
  -- assemble
  have hnormeq : dist (sobToWiener1 (hsum t)) (sobToWiener1 (hsum t₀))
      = ∑' k : Gam, wt k * ‖a t k - a t₀ k‖ := by
    rw [dist_eq_norm, Wiener1.norm_eq, Wiener1.coeff_sub]
    rfl
  rw [hnormeq]
  have hwsum : Summable fun k : Gam => wt k * ‖a t k - a t₀ k‖ :=
    summable_wt_mul_norm (hdsum t)
  have hsplit := hwsum.sum_add_tsum_compl (s := F)
  have htail := tsum_compl_wt_le (c := fun k => a t k - a t₀ k) (hdsum t) hδ0 (hdE t) F
  rw [tsum_compl_spelling (f := fun k => wt k * ‖a t k - a t₀ k‖) F] at htail
  linarith [hsplit, htail, hF, hδsmall, ht]


/-! ## 4. From an almost-everywhere bound to an everywhere bound -/

/-- **A closed full-measure condition on `[0,T]` holds at every point, endpoints included.**
The proof is the only place where the endpoints matter: around any `t ∈ [0,T]` the set
`Ioo (max 0 (t-η)) (min T (t+η))` is a nonempty open subset of `[0,T]`, hence of positive
Lebesgue measure, so the exceptional null set cannot contain it. -/
theorem forall_le_of_ae_le {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T → g t ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, g t ≤ M := by
  intro t ht
  by_contra hcon
  push Not at hcon
  have hopen : IsOpen {s : ℝ | M < g s} := isOpen_lt continuous_const hg
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen t hcon
  set A : ℝ := max 0 (t - η) with hA
  set B : ℝ := min T (t + η) with hB
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hAB : A < B := by
    refine max_lt (lt_min hT (by linarith)) (lt_min (by linarith) (by linarith))
  have hA0 : 0 ≤ A := le_max_left _ _
  have hAt : t - η ≤ A := le_max_right _ _
  have hBT : B ≤ T := min_le_left _ _
  have hBt : B ≤ t + η := min_le_right _ _
  have hsub : Set.Ioo A B ⊆ {s : ℝ | ¬ (s ∈ Set.Icc (0:ℝ) T → g s ≤ M)} := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hA0 hs.1.le
    have hsT : s ≤ T := le_trans hs.2.le hBT
    have hdist : dist s t < η := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hs.1, hAt]; linarith [hs.2, hBt]]
    have hgs : M < g s := hball (by rwa [Metric.mem_ball])
    intro hmem
    exact absurd (hmem ⟨hs0, hsT⟩) (not_le.2 hgs)
  have hnull : (volume : Measure ℝ) {s : ℝ | ¬ (s ∈ Set.Icc (0:ℝ) T → g s ≤ M)} = 0 :=
    MeasureTheory.ae_iff.1 hae
  have hzero : (volume : Measure ℝ) (Set.Ioo A B) = 0 := measure_mono_null hsub hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  linarith

/-- **The `H³` bound, given only almost everywhere, holds at every time** for the continuous
coefficient representative.  The bound is stated on finite partial sums, which is what makes the
upgrade a statement about continuous real functions; `summable_of_finset_sum_le` and
`tsum_le_of_finset_sum_le` then pass to the full sum. -/
theorem forall_finset_sum_le_of_ae {T : ℝ} (hT : 0 < T) {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) {M : ℝ}
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M := by
  intro t ht F
  refine forall_le_of_ae_le hT (g := fun s => ∑ k ∈ F, rho k ^ 3 * ‖a s k‖ ^ 2) ?_ ?_ t ht
  · exact continuous_finset_sum F (fun k _ => continuous_const.mul ((hcont k).norm.pow 2))
  · filter_upwards [hae] with s hs hsmem
    exact hs hsmem F

/-! ## 5. The bounded continuous real `A¹` curve -/

/-- **The `A¹` curve of an `H³`-bounded, coefficientwise continuous, real family.**  This is an
actual element of `Curve1 T`: bounded, continuous, and real. -/
noncomputable def sobCurve {T : ℝ} {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) : Curve1 T :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : TimeI T => sobToRealWiener1 (hsum (t : ℝ)) (hreal (t : ℝ)),
      by
        refine (RealWiener1.isometry_val.comp_continuous_iff).1 ?_
        exact (continuous_sobToWiener1_curve hcont hsum hM).comp continuous_subtype_val⟩

@[simp] theorem sobCurve_apply {T : ℝ} {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) (t : TimeI T) :
    (sobCurve (T := T) hcont hreal hsum hM) t
      = sobToRealWiener1 (hsum (t : ℝ)) (hreal (t : ℝ)) := rfl

/-- **Coefficient agreement**: the curve's Fourier coefficients are the input coefficients. -/
theorem sobCurve_coeff {T : ℝ} {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) (t : TimeI T) (k : Gam) :
    ((sobCurve (T := T) hcont hreal hsum hM) t).val.coeff k = a (t : ℝ) k := rfl

/-- The clamped state of the curve. -/
theorem curveState_sobCurve {T : ℝ} (hT : 0 ≤ T) {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) (s : ℝ) (k : Gam) :
    (curveState hT (sobCurve (T := T) hcont hreal hsum hM) s).coeff k
      = a ((clampT hT s : TimeI T) : ℝ) k := rfl

/-- At a time of `[0,T]` the clamp is the identity, so the curve's state has exactly the input
coefficients. -/
theorem curveState_sobCurve_mem {T : ℝ} (hT : 0 ≤ T) {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) (k : Gam) :
    (curveState hT (sobCurve (T := T) hcont hreal hsum hM) s).coeff k = a s k := by
  have hclamp : ((clampT hT s : TimeI T) : ℝ) = s := clampT_coe hT hs.1 hs.2
  rw [curveState_sobCurve hT hcont hreal hsum hM s k, hclamp]

/-- **Physical agreement**: the synthesis of the constructed curve is the given `L²(𝕋²)` state,
at every time of `[0,T]`.  No representative is modified: the equality is in `L²(𝕋²)`. -/
theorem synthL2_sobCurve {T : ℝ} (hT : 0 ≤ T) {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) (hreal : ∀ t, ConjSymmetric (a t))
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M)
    {θ : ℝ → TorusL2} (hθ : ∀ t k, l2coeff k (θ t) = a t k)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT (sobCurve (T := T) hcont hreal hsum hM) s)) = θ s := by
  refine synthL2_incl_eq_of_coeff (w := curveState hT _ s) (fun k => ?_)
  rw [hθ s k, curveState_sobCurve_mem hT hcont hreal hsum hM hs k]

end LiWang.WienerModel
