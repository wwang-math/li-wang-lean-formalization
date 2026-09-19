/-
# Fixed positive-time approximate controllability by smooth admissible sources

This module proves the **approximation theorem for the actual generated states**:

> for `1/2 < α`, `T > 0`, open `W`, `0 < τ ≤ T`, and every real target `U : RealWiener1`,
> there are admissible smooth sources `gₙ`, switched off before `τ`, with
> `‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le gₙ) τ − U.val))‖ → 0`.

It is not a definition named "approximation certificate": the conclusion is the actual
physical `L²` convergence of the actual Duhamel states at the actual time `τ`.

The proof is the duality route:

1.  `pairY_terminal_productSource` — the terminal response of a product source is the honest
    time integral `∫₀^τ χ(s) ⟪y, e^{-(τ-s)(-Δ)^α} a⟫ ds` (Bochner integral commuted through a
    bounded functional; no formal manipulation).
2.  `eq_zero_of_orthogonal_terminal` — if `y ∈ ℓ²` annihilates every terminal response, then
    the time separation lemma (bumps supported in `(0,τ)`) kills the `s`-integral, the spatial
    separation lemma (smooth profiles in `W`) makes `e^{-r(-Δ)^α}y` vanish on `W`,
    differentiating in `r` makes `(-Δ)^α e^{-r(-Δ)^α}y` vanish on `W` too, and the portable
    parameter `FractionalUCP α W` then forces `y = 0` (heat injectivity, zero mode included).
3.  `mem_closure_of_orthogonal_trivial` — Hilbert-space duality in the *complex* space
    `Wiener2`, followed by the **real projection** `reW2 = (1 + C)/2` (`C` = conjugate
    reflection), which is norm-nonincreasing, fixes real states, and sends the complex span of
    the real response space back into it.  This is what keeps real controls with real targets:
    no density is claimed in the unrestricted complex `L²`.
4.  `exists_smoothSources_terminal_tendsto` — the statement above.

Time `0` is genuinely excluded: `curveState hT.le (duhamelOp …) 0 = 0` for every source, so no
nonzero target is reachable there (`duhamelOp_zero_time` in `DuhamelOperator`).

Part of `LiWangFormalizationTerminalControlPacket` v6.0.
-/
import LiWangFormalization.HeatSemigroupL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology
open scoped ENNReal

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. The `ℓ²` view of a Wiener state, and the duality functional -/

theorem toWiener2_add (a b : Wiener) : toWiener2 (a + b) = toWiener2 a + toWiener2 b := by
  refine lp.ext (funext fun k => ?_)
  show (a + b) k = (toWiener2 a) k + (toWiener2 b) k
  rw [toWiener2_apply, toWiener2_apply, lp.coeFn_add]
  rfl

theorem toWiener2_smul (c : ℂ) (a : Wiener) : toWiener2 (c • a) = c • toWiener2 a := by
  refine lp.ext (funext fun k => ?_)
  show (c • a : Wiener) k = c * (toWiener2 a) k
  rw [toWiener2_apply]
  rfl

theorem toWiener2_sub (a b : Wiener) : toWiener2 (a - b) = toWiener2 a - toWiener2 b := by
  refine lp.ext (funext fun k => ?_)
  show (a - b) k = (toWiener2 a) k - (toWiener2 b) k
  rw [toWiener2_apply, toWiener2_apply, lp.coeFn_sub]
  rfl

theorem norm_toWiener2_le (a : Wiener) : ‖toWiener2 a‖ ≤ ‖a‖ := by
  rw [← norm_coeffL2, coeffL2_toWiener2]
  exact norm_synthL2_le a

/-- The physical `L²` norm of a first-order state is the `ℓ²` norm of its coefficients. -/
theorem norm_synthL2_eq_norm_toWiener2 (a : Wiener) : ‖synthL2 a‖ = ‖toWiener2 a‖ := by
  rw [← coeffL2_toWiener2, norm_coeffL2]

noncomputable def toWiener2CLM : Wiener →L[ℂ] Wiener2 :=
  LinearMap.mkContinuous
    { toFun := toWiener2
      map_add' := toWiener2_add
      map_smul' := fun c a => toWiener2_smul c a } 1
    (fun a => by simpa using norm_toWiener2_le a)

@[simp] theorem toWiener2CLM_apply (a : Wiener) : toWiener2CLM a = toWiener2 a := rfl

/-- The bounded `ℂ`-linear functional `u ↦ ⟪y, u⟫_{ℓ²}` on the first-order space. -/
noncomputable def pairY (y : Wiener2) : Wiener1 →L[ℂ] ℂ :=
  (innerSL ℂ y).comp (toWiener2CLM.comp incl)

@[simp] theorem pairY_apply (y : Wiener2) (u : Wiener1) :
    pairY y u = inner ℂ y (toWiener2 (incl u)) := rfl

/-! ## 2. The terminal response map -/

theorem curveState_duhamelOp_add (hα : 1 / 2 < α) (hT : 0 ≤ T) (g g' : Curve0 T) (τ : ℝ) :
    curveState hT (duhamelOp hα hT (g + g')) τ
      = curveState hT (duhamelOp hα hT g) τ + curveState hT (duhamelOp hα hT g') τ := by
  show ((duhamelOp hα hT (g + g')) (clampT hT τ)).val = _
  rw [map_add]
  rfl

theorem curveState_duhamelOp_smul (hα : 1 / 2 < α) (hT : 0 ≤ T) (r : ℝ) (g : Curve0 T) (τ : ℝ) :
    curveState hT (duhamelOp hα hT (r • g)) τ = r • curveState hT (duhamelOp hα hT g) τ := by
  show ((duhamelOp hα hT (r • g)) (clampT hT τ)).val = _
  rw [map_smul]
  rfl

/-- **The terminal response**, as an `ℝ`-linear map into the coefficient `ℓ²` space. -/
noncomputable def terminalW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (τ : ℝ) : Curve0 T →ₗ[ℝ] Wiener2 where
  toFun g := toWiener2 (incl (curveState hT (duhamelOp hα hT g) τ))
  map_add' g g' := by
    rw [curveState_duhamelOp_add hα hT, map_add, toWiener2_add]
  map_smul' r g := by
    rw [curveState_duhamelOp_smul hα hT, smul_real_wiener1, map_smul, toWiener2_smul]
    rfl

@[simp] theorem terminalW2_apply (hα : 1 / 2 < α) (hT : 0 ≤ T) (τ : ℝ) (g : Curve0 T) :
    terminalW2 hα hT τ g = toWiener2 (incl (curveState hT (duhamelOp hα hT g) τ)) := rfl

/-! ## 3. The terminal response of a product source as a genuine time integral -/

theorem pairY_terminal_productSource (hα : 1 / 2 < α) (hT : 0 < T) {τ : ℝ} (hτ0 : 0 < τ)
    (hτT : τ ≤ T) (y : Wiener2) (a : RealWiener) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump τ χ) :
    pairY y (curveState hT.le (duhamelOp hα hT.le (productSource hT.le a hχ.continuous)) τ)
      = ∫ s in (0:ℝ)..τ, (χ s : ℂ) * heatPair α y a.val (τ - s) := by
  obtain ⟨t₀, t₁, ht₀, ht01, ht1, hvan⟩ := hχ.supp
  have hχτ : χ τ = 0 := hvan τ (fun hc => absurd hc.2 (not_le.2 ht1))
  set g : Curve0 T := productSource hT.le a hχ.continuous with hgdef
  have hcoe : ((clampT hT.le τ : TimeI T) : ℝ) = τ := clampT_coe hT.le hτ0.le hτT
  have hstate : curveState hT.le (duhamelOp hα hT.le g) τ
      = duhamelIntegral hα.le τ (sourceFun hT.le g) := by
    show ((duhamelOp hα hT.le g) (clampT hT.le τ)).val = _
    rw [duhamelOp_apply_val, hcoe]
  rw [hstate, duhamelIntegral,
    ← ContinuousLinearMap.intervalIntegral_comp_comm (pairY y)
      (intervalIntegrable_duhamelIntegrand hα hτ0.le (continuous_sourceFun hT.le g)
        (fun s => norm_sourceFun_le hT.le g s))]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le hτ0.le] at hs
  have hclamp : ((clampT hT.le s : TimeI T) : ℝ) = s :=
    clampT_coe hT.le hs.1 (le_trans hs.2 hτT)
  have hsrc : sourceFun hT.le g s = χ s • a.val := by
    rw [hgdef, sourceFun_productSource, hclamp]
  show pairY y (heatSmoothFun hα.le (τ - s) (sourceFun hT.le g s))
    = (χ s : ℂ) * heatPair α y a.val (τ - s)
  rcases lt_or_eq_of_le hs.2 with hlt | heq
  · have hpos : 0 < τ - s := by linarith
    rw [hsrc, heatSmoothFun_real_smul hα.le, smul_real_wiener1, map_smul,
      heatPair_eq_inner hα.le hpos y a.val]
    rfl
  · have hz : τ - s = 0 := by rw [heq, sub_self]
    rw [hz, heatSmoothFun_of_nonpos hα.le le_rfl, map_zero, heq, hχτ]
    simp

/-! ## 3b. The sources that are switched off before the terminal time -/

/-- The admissible sources whose time profile is a `C^∞` bump supported in a compact
subinterval of `(0,τ)`: they are switched off *before* the terminal time. -/
noncomputable def smoothSourcesBefore (hT : 0 < T) (W : Set Torus2) (τ : ℝ) :
    Submodule ℝ (Curve0 T) :=
  Submodule.span ℝ {V | ∃ (a : RealWiener) (χ : ℝ → ℝ) (hχ : Continuous χ),
      a ∈ smoothProfiles W ∧ IsSmoothTimeBump τ χ ∧ V = productSource hT.le a hχ}

theorem smoothSourcesBefore_le (hT : 0 < T) (W : Set Torus2) {τ : ℝ} (hτT : τ ≤ T) :
    smoothSourcesBefore hT W τ ≤ smoothSources hT W := by
  refine Submodule.span_le.2 ?_
  rintro V ⟨a, χ, hχc, ha, hbump, rfl⟩
  exact Submodule.subset_span ⟨a, χ, hχc, ha, hbump.mono hτT, rfl⟩

/-- **Every source switched off before `τ` really is**: its Wiener-valued profile vanishes
outside a compact subinterval of `(0,τ)`. -/
theorem smoothSourcesBefore_timeSupport (hT : 0 < T) (W : Set Torus2) {τ : ℝ} (hτ : 0 < τ)
    (hτT : τ ≤ T) {V : Curve0 T} (hV : V ∈ smoothSourcesBefore hT W τ) :
    ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < τ ∧
      ∀ t ∉ Set.Icc t₀ t₁, sourceFun hT.le V t = 0 := by
  refine Submodule.span_induction
    (p := fun V _ => ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < τ ∧
      ∀ t ∉ Set.Icc t₀ t₁, sourceFun hT.le V t = 0) ?_ ?_ ?_ ?_ hV
  · rintro V ⟨a, χ, hχc, -, hbump, rfl⟩
    obtain ⟨t₀, t₁, ht₀, ht01, ht1, hvan⟩ := hbump.supp
    refine ⟨t₀, t₁, ht₀, ht01, ht1, fun t ht => ?_⟩
    rw [sourceFun_productSource]
    have hnot : ((clampT hT.le t : TimeI T) : ℝ) ∉ Set.Icc t₀ t₁ := by
      show min (max t 0) T ∉ Set.Icc t₀ t₁
      rcases not_and_or.1 (fun h : t₀ ≤ t ∧ t ≤ t₁ => ht ⟨h.1, h.2⟩) with h | h
      · have h2 : max t 0 < t₀ := max_lt (not_le.1 h) ht₀
        have h1 : min (max t 0) T ≤ max t 0 := min_le_left _ _
        exact fun hmem => absurd hmem.1 (by linarith)
      · have h1 : t₁ < max t 0 := lt_of_lt_of_le (not_le.1 h) (le_max_left _ _)
        have h3 : t₁ < min (max t 0) T := lt_min h1 (lt_of_lt_of_le ht1 hτT)
        exact fun hmem => absurd hmem.2 (by linarith)
    rw [hvan _ hnot, zero_smul]
  · exact ⟨τ / 4, τ / 2, by linarith, by linarith, by linarith, fun t _ => rfl⟩
  · rintro V V' - - ⟨a₀, a₁, ha₀, ha, ha₁, hva⟩ ⟨b₀, b₁, hb₀, hb, hb₁, hvb⟩
    refine ⟨min a₀ b₀, max a₁ b₁, lt_min ha₀ hb₀,
      le_trans (min_le_left _ _) (le_trans ha (le_max_left _ _)), max_lt ha₁ hb₁, fun t ht => ?_⟩
    rw [sourceFun_add, hva t (fun hc => ht ⟨le_trans (min_le_left _ _) hc.1,
        le_trans hc.2 (le_max_left _ _)⟩),
      hvb t (fun hc => ht ⟨le_trans (min_le_right _ _) hc.1,
        le_trans hc.2 (le_max_right _ _)⟩), add_zero]
  · rintro r V - ⟨a₀, a₁, ha₀, ha, ha₁, hva⟩
    exact ⟨a₀, a₁, ha₀, ha, ha₁, fun t ht => by rw [sourceFun_smul, hva t ht, smul_zero]⟩

/-! ## 4. Orthogonality to every terminal response forces `y = 0` -/

/-- **The duality step.**  An `ℓ²` state orthogonal to every state generated at time `τ` by an
admissible smooth source supported in `W × (0,τ)` is zero.  `FractionalUCP α W` is the
portable parameter; nothing else is assumed. -/
theorem eq_zero_of_orthogonal_terminal (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    {y : Wiener2}
    (hy : ∀ g ∈ smoothSourcesBefore hT W τ,
      pairY y (curveState hT.le (duhamelOp hα hT.le g) τ) = 0) :
    y = 0 := by
  refine eq_zero_of_heatPair_vanishes hα.le hW hUCP hτ0 ?_
  intro a ha r hr
  set f : ℝ → ℂ := fun s => heatPair α y a.val (τ - s) with hf
  have hfc : Continuous f :=
    (continuous_heatPair α y a.val).comp (continuous_const.sub continuous_id)
  have hzero : ∀ χ : ℝ → ℝ, IsSmoothTimeBump τ χ → (∫ s in (0:ℝ)..τ, (χ s : ℂ) * f s) = 0 := by
    intro χ hχ
    rw [hf, ← pairY_terminal_productSource hα hT hτ0 hτT y a hχ]
    refine hy _ (Submodule.subset_span ⟨a, χ, hχ.continuous, ha, hχ, rfl⟩)
  have hall := eq_zero_of_forall_time_bump_complex hτ0 hfc hzero
  have hmem : τ - r ∈ Set.Icc (0:ℝ) τ := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h2 : heatPair α y a.val (τ - (τ - r)) = 0 := hall (τ - r) hmem
  have h3 : τ - (τ - r) = r := by ring
  rw [h3] at h2
  exact h2

/-! ## 5. The conjugate reflection on `ℓ²` and the real projection -/

theorem summable_norm_sq_w2 (y : Wiener2) : Summable fun k : Gam => ‖y k‖ ^ 2 := by
  have h := (lp.memℓp y).summable (p := 2) (by norm_num)
  have hcast : ∀ k : Gam, ‖y k‖ ^ (2 : ENNReal).toReal = ‖y k‖ ^ (2:ℕ) := by
    intro k
    rw [show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa only [hcast] using h

theorem norm_w2_sq (y : Wiener2) : ‖y‖ ^ 2 = ∑' k : Gam, ‖y k‖ ^ 2 := by
  have h := norm_w2mk_sq (fun k => y k) (summable_norm_sq_w2 y)
  have hy : w2mk (fun k => y k) (summable_norm_sq_w2 y) = y := lp.ext rfl
  rw [hy] at h
  exact h

theorem summable_norm_sq_crefl (y : Wiener2) :
    Summable fun k : Gam => ‖conj (y (-k))‖ ^ 2 := by
  have h1 : (fun k : Gam => ‖conj (y (-k))‖ ^ 2) = fun k : Gam => ‖y (-k)‖ ^ 2 := by
    funext k; rw [RCLike.norm_conj]
  rw [h1]
  exact (Equiv.neg Gam).summable_iff.2 (summable_norm_sq_w2 y)

/-- The **conjugate reflection** `(Cy)_k = conj(y_{-k})`: a conjugate-linear involutive
isometry of `ℓ²` whose fixed points are exactly the real (conjugate-symmetric) states. -/
noncomputable def creflW2 (y : Wiener2) : Wiener2 :=
  w2mk (fun k => conj (y (-k))) (summable_norm_sq_crefl y)

@[simp] theorem creflW2_apply (y : Wiener2) (k : Gam) : (creflW2 y) k = conj (y (-k)) := rfl

theorem creflW2_add (y z : Wiener2) : creflW2 (y + z) = creflW2 y + creflW2 z := by
  refine lp.ext (funext fun k => ?_)
  show conj ((y + z : Wiener2) (-k)) = conj (y (-k)) + conj (z (-k))
  show conj (y (-k) + z (-k)) = conj (y (-k)) + conj (z (-k))
  rw [map_add]

theorem creflW2_smul (c : ℂ) (y : Wiener2) : creflW2 (c • y) = conj c • creflW2 y := by
  refine lp.ext (funext fun k => ?_)
  show conj ((c • y : Wiener2) (-k)) = conj c * conj (y (-k))
  show conj (c * y (-k)) = conj c * conj (y (-k))
  rw [map_mul]

theorem norm_creflW2 (y : Wiener2) : ‖creflW2 y‖ = ‖y‖ := by
  have h1 : ‖creflW2 y‖ ^ 2 = ∑' k : Gam, ‖conj (y (-k))‖ ^ 2 :=
    norm_w2mk_sq _ (summable_norm_sq_crefl y)
  have h2 : ‖y‖ ^ 2 = ∑' k : Gam, ‖y k‖ ^ 2 := norm_w2_sq y
  have h3 : (∑' k : Gam, ‖conj (y (-k))‖ ^ 2) = ∑' k : Gam, ‖y k‖ ^ 2 := by
    have he : ∀ k : Gam, ‖conj (y (-k))‖ ^ 2 = ‖y (-k)‖ ^ 2 := fun k => by rw [RCLike.norm_conj]
    rw [tsum_congr he]
    exact (Equiv.neg Gam).tsum_eq (fun j : Gam => ‖y j‖ ^ 2)
  have h4 : ‖creflW2 y‖ ^ 2 = ‖y‖ ^ 2 := by rw [h1, h3, ← h2]
  nlinarith [norm_nonneg (creflW2 y), norm_nonneg y]

/-- The **real projection** on `ℓ²`. -/
noncomputable def reW2 (y : Wiener2) : Wiener2 := (2⁻¹ : ℂ) • (y + creflW2 y)

theorem reW2_apply (y : Wiener2) (k : Gam) :
    (reW2 y) k = 2⁻¹ * (y k + conj (y (-k))) := rfl

theorem reW2_add (y z : Wiener2) : reW2 (y + z) = reW2 y + reW2 z := by
  refine lp.ext (funext fun k => ?_)
  show (reW2 (y + z)) k = (reW2 y) k + (reW2 z) k
  rw [reW2_apply, reW2_apply, reW2_apply]
  have h1 : ((y + z : Wiener2)) k = y k + z k := rfl
  have h2 : ((y + z : Wiener2)) (-k) = y (-k) + z (-k) := rfl
  rw [h1, h2, map_add]
  ring

theorem reW2_sub (y z : Wiener2) : reW2 (y - z) = reW2 y - reW2 z := by
  refine lp.ext (funext fun k => ?_)
  show (reW2 (y - z)) k = (reW2 y) k - (reW2 z) k
  rw [reW2_apply, reW2_apply, reW2_apply]
  have h1 : ((y - z : Wiener2)) k = y k - z k := rfl
  have h2 : ((y - z : Wiener2)) (-k) = y (-k) - z (-k) := rfl
  rw [h1, h2, map_sub]
  ring

@[simp] theorem reW2_zero : reW2 (0 : Wiener2) = 0 := by
  refine lp.ext (funext fun k => ?_)
  show (reW2 (0 : Wiener2)) k = (0 : Wiener2) k
  rw [reW2_apply]
  have h1 : ((0 : Wiener2)) k = 0 := rfl
  have h2 : ((0 : Wiener2)) (-k) = 0 := rfl
  rw [h1, h2, map_zero]
  ring

theorem norm_reW2_le (y : Wiener2) : ‖reW2 y‖ ≤ ‖y‖ := by
  rw [reW2, norm_smul]
  have h1 : ‖(2⁻¹ : ℂ)‖ = 2⁻¹ := by norm_num
  rw [h1]
  have h2 : ‖y + creflW2 y‖ ≤ ‖y‖ + ‖creflW2 y‖ := norm_add_le _ _
  rw [norm_creflW2] at h2
  linarith

/-- The key algebraic identity making the real projection compatible with complex scalars. -/
theorem reW2_smul_complex (c : ℂ) (y : Wiener2) :
    reW2 (c • y) = c.re • reW2 y + c.im • reW2 (Complex.I • y) := by
  refine lp.ext (funext fun k => ?_)
  have hgen : ∀ p q : ℝ, ∀ Z Z' : ℂ,
      2⁻¹ * (((p:ℂ) + (q:ℂ) * Complex.I) * Z + conj ((p:ℂ) + (q:ℂ) * Complex.I) * Z')
        = (p:ℂ) * (2⁻¹ * (Z + Z')) + (q:ℂ) * (2⁻¹ * (Complex.I * Z + conj Complex.I * Z')) := by
    intro p q Z Z'
    have hc1 : conj ((p:ℂ) + (q:ℂ) * Complex.I) = (p:ℂ) - (q:ℂ) * Complex.I := by
      simp [Complex.ext_iff]
    have hc2 : conj Complex.I = -Complex.I := by simp
    rw [hc1, hc2]
    ring
  have hc : ((c.re : ℂ) + (c.im : ℂ) * Complex.I) = c := Complex.re_add_im c
  have hL : ((reW2 (c • y)) : Gam → ℂ) k
      = 2⁻¹ * (((c.re:ℂ) + (c.im:ℂ) * Complex.I) * (y k)
          + conj ((c.re:ℂ) + (c.im:ℂ) * Complex.I) * conj (y (-k))) := by
    rw [reW2_apply, hc]
    have e1 : ((c • y : Wiener2)) k = c * y k := rfl
    have e2 : ((c • y : Wiener2)) (-k) = c * y (-k) := rfl
    rw [e1, e2, map_mul]
  have hR : ((c.re • reW2 y + c.im • reW2 (Complex.I • y) : Wiener2)) k
      = (c.re:ℂ) * (2⁻¹ * (y k + conj (y (-k))))
        + (c.im:ℂ) * (2⁻¹ * (Complex.I * y k + conj Complex.I * conj (y (-k)))) := by
    have e1 : ((c.re • reW2 y + c.im • reW2 (Complex.I • y) : Wiener2)) k
        = (c.re : ℝ) • ((reW2 y) k) + (c.im : ℝ) • ((reW2 (Complex.I • y)) k) := rfl
    rw [e1, Complex.real_smul, Complex.real_smul, reW2_apply, reW2_apply]
    have h1 : ((Complex.I • y : Wiener2)) k = Complex.I * y k := rfl
    have h2 : ((Complex.I • y : Wiener2)) (-k) = Complex.I * y (-k) := rfl
    rw [h1, h2, map_mul]
  rw [hL, hR]
  exact hgen c.re c.im (y k) (conj (y (-k)))

theorem reW2_of_real {y : Wiener2} (h : creflW2 y = y) : reW2 y = y := by
  rw [reW2, h]
  have : (y + y) = (2 : ℂ) • y := by
    refine lp.ext (funext fun k => ?_)
    simp [two_smul]
  rw [this, smul_smul]
  norm_num

theorem reW2_I_of_real {y : Wiener2} (h : creflW2 y = y) : reW2 (Complex.I • y) = 0 := by
  rw [reW2, creflW2_smul, h]
  have hI : conj Complex.I = -Complex.I := by simp
  rw [hI]
  have : (Complex.I • y + (-Complex.I) • y) = (0 : Wiener2) := by
    rw [← add_smul]
    simp
  rw [this, smul_zero]

/-! ## 6. Density of a real response space from triviality of its annihilator -/

/-- The set of complex vectors whose real projection (and that of their `i`-multiple) lands
back in the real subspace `A`; it is a **complex** subspace containing `A`. -/
noncomputable def realizableSub (A : Submodule ℝ Wiener2) : Submodule ℂ Wiener2 where
  carrier := {z | reW2 z ∈ A ∧ reW2 (Complex.I • z) ∈ A}
  zero_mem' := by
    refine ⟨by rw [reW2_zero]; exact A.zero_mem, ?_⟩
    rw [smul_zero, reW2_zero]; exact A.zero_mem
  add_mem' := by
    rintro z w ⟨hz1, hz2⟩ ⟨hw1, hw2⟩
    refine ⟨by rw [reW2_add]; exact A.add_mem hz1 hw1, ?_⟩
    rw [smul_add, reW2_add]
    exact A.add_mem hz2 hw2
  smul_mem' := by
    rintro c z ⟨hz1, hz2⟩
    constructor
    · rw [reW2_smul_complex]
      exact A.add_mem (A.smul_mem _ hz1) (A.smul_mem _ hz2)
    · rw [smul_smul, reW2_smul_complex]
      exact A.add_mem (A.smul_mem _ hz1) (A.smul_mem _ hz2)

theorem le_realizableSub {A : Submodule ℝ Wiener2} (hreal : ∀ z ∈ A, creflW2 z = z) :
    (A : Set Wiener2) ⊆ (realizableSub A : Set Wiener2) := by
  intro z hz
  exact ⟨by rw [reW2_of_real (hreal z hz)]; exact hz,
    by rw [reW2_I_of_real (hreal z hz)]; exact A.zero_mem⟩

/-- **Real density from a trivial annihilator.**  If every element of the real subspace `A` is
a real state, and the only `ℓ²` state orthogonal to all of `A` is zero, then every real state
lies in the closure of `A` — *not* merely in the closure of its complex span. -/
theorem mem_closure_of_orthogonal_trivial {A : Submodule ℝ Wiener2}
    (hreal : ∀ z ∈ A, creflW2 z = z)
    (hann : ∀ y : Wiener2, (∀ w ∈ A, inner ℂ y w = (0:ℂ)) → y = 0)
    {w₀ : Wiener2} (hw₀ : creflW2 w₀ = w₀) :
    w₀ ∈ closure (A : Set Wiener2) := by
  set B : Submodule ℂ Wiener2 := Submodule.span ℂ (A : Set Wiener2) with hB
  have hBperp : Bᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 (fun y hy => ?_)
    refine hann y (fun w hw => ?_)
    exact (Submodule.mem_orthogonal' B y).1 hy w (Submodule.subset_span hw)
  have htop : B.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hBperp
  have hw₀B : w₀ ∈ closure (B : Set Wiener2) := by
    have h1 : w₀ ∈ B.topologicalClosure := by rw [htop]; exact Submodule.mem_top
    have h2 : (B.topologicalClosure : Set Wiener2) = closure (B : Set Wiener2) :=
      Submodule.topologicalClosure_coe B
    exact h2 ▸ h1
  obtain ⟨z, hzB, hzlim⟩ := mem_closure_iff_seq_limit.1 hw₀B
  have hzA : ∀ n, reW2 (z n) ∈ A := by
    intro n
    have hle : (B : Set Wiener2) ⊆ (realizableSub A : Set Wiener2) :=
      Submodule.span_le.2 (le_realizableSub hreal)
    exact (hle (hzB n)).1
  refine mem_closure_iff_seq_limit.2 ⟨fun n => reW2 (z n), hzA, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n, ‖reW2 (z n) - w₀‖ ≤ ‖z n - w₀‖ := by
    intro n
    have e : reW2 (z n) - w₀ = reW2 (z n - w₀) := by rw [reW2_sub, reW2_of_real hw₀]
    rw [e]
    exact norm_reW2_le _
  exact squeeze_zero (fun n => norm_nonneg _) hbound
    (tendsto_iff_norm_sub_tendsto_zero.1 hzlim)

/-! ## 7. Reality of the terminal responses -/

theorem creflW2_toWiener2_incl {u : Wiener1} (hu : ConjSymmetric u.coeff) :
    creflW2 (toWiener2 (incl u)) = toWiener2 (incl u) := by
  refine lp.ext (funext fun k => ?_)
  show conj ((toWiener2 (incl u)) (-k)) = (toWiener2 (incl u)) k
  show conj (u.coeff (-k)) = u.coeff k
  rw [hu k, Complex.conj_conj]

theorem creflW2_terminalW2 (hα : 1 / 2 < α) (hT : 0 ≤ T) (τ : ℝ) (g : Curve0 T) :
    creflW2 (terminalW2 hα hT τ g) = terminalW2 hα hT τ g :=
  creflW2_toWiener2_incl ((duhamelOp hα hT g) (clampT hT τ)).conjSymmetric

/-! ## 8. The approximation theorem for the actual generated states -/

/-- **Fixed positive-time approximate controllability.**  For every real first-order target
`U : RealWiener1` there are *actual* admissible smooth sources `gₙ`, compactly supported in
`W × (0,τ)` (`smoothSourcesBefore_timeSupport`), whose generated states at time `τ` converge to
`U` in the physical `L²(𝕋²)` norm.

Scope, stated precisely: the targets are the *real first-order* states `RealWiener1 = A¹_ℝ(𝕋²)`,
not all of real `L²(𝕋²)`; no uniform bound on `gₙ` is asserted (and none is available); no
density is claimed in the unrestricted complex `L²`; and `FractionalUCP α W` is carried as the
portable parameter, never proved here for a proper `W`. -/
theorem exists_smoothSourcesBefore_terminal_tendsto (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ)
    (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSourcesBefore hT W τ) ∧
      Tendsto
        (fun n => ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (𝓝 0) := by
  set A : Submodule ℝ Wiener2 :=
    Submodule.map (terminalW2 hα hT.le τ) (smoothSourcesBefore hT W τ) with hA
  set w₀ : Wiener2 := toWiener2 (incl U.val) with hw₀def
  have hreal : ∀ z ∈ A, creflW2 z = z := by
    intro z hz
    obtain ⟨g, -, rfl⟩ := Submodule.mem_map.1 hz
    exact creflW2_terminalW2 hα hT.le τ g
  have hann : ∀ y : Wiener2, (∀ w ∈ A, inner ℂ y w = (0:ℂ)) → y = 0 := by
    intro y hy
    refine eq_zero_of_orthogonal_terminal hα hT hW hUCP hτ0 hτT (fun g hg => ?_)
    exact hy (terminalW2 hα hT.le τ g) (Submodule.mem_map_of_mem hg)
  have hw₀ : creflW2 w₀ = w₀ := creflW2_toWiener2_incl U.conjSymmetric
  have hmem := mem_closure_of_orthogonal_trivial hreal hann hw₀
  obtain ⟨x, hxA, hxlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose g hg hgeq using fun n => Submodule.mem_map.1 (hxA n)
  refine ⟨g, hg, ?_⟩
  have hrw : ∀ n, ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖
      = ‖x n - w₀‖ := by
    intro n
    rw [norm_synthL2_eq_norm_toWiener2, map_sub, toWiener2_sub, hw₀def]
    congr 2
    exact hgeq n
  simp only [hrw]
  exact tendsto_iff_norm_sub_tendsto_zero.1 hxlim

/-- **Fixed positive-time approximate controllability**, stated for the full admissible family.
The controls produced are in fact switched off before `τ`
(`exists_smoothSourcesBefore_terminal_tendsto`). -/
theorem exists_smoothSources_terminal_tendsto (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSources hT W) ∧
      Tendsto
        (fun n => ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (𝓝 0) := by
  obtain ⟨g, hg, hconv⟩ :=
    exists_smoothSourcesBefore_terminal_tendsto hα hT hW hUCP hτ0 hτT U
  exact ⟨g, fun n => smoothSourcesBefore_le hT W hτT (hg n), hconv⟩

/-! ## 9. The zero-time limitation -/

/-- **Time zero is genuinely excluded**: every generated state vanishes at `t = 0`, so no
nonzero target is approximable there. -/
theorem terminal_zero_time (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    curveState hT (duhamelOp hα hT g) 0 = 0 := by
  show ((duhamelOp hα hT g) (clampT hT 0)).val = _
  rw [duhamelOp_apply_val]
  have h0 : ((clampT hT (0:ℝ) : TimeI T) : ℝ) = 0 := clampT_coe hT le_rfl hT
  rw [h0, duhamelIntegral, intervalIntegral.integral_same]

end LiWang.Formalization
