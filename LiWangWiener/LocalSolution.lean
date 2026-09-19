/-
# A local mild solution of the fractional active-scalar equation

With the Duhamel term proved continuous in time (`MildSolution.lean`), the mild map becomes a
self-map of a closed ball of curves on a short time interval, and it is a contraction there.
Banach's fixed-point theorem then produces a genuine local mild solution of

    ∂_t θ + N_m(θ, θ) + (-Δ)^α θ = 0,   θ(0) = θ₀,

in the Wiener algebra, for `1/2 < α`.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.AffineFixedPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.WienerModel

/-! ## Estimates for the corrected mild map -/

theorem norm_mildMap1_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u : ℝ → Wiener1} {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    ‖mildMap1 hα.le hm u₀ u t‖ ≤ ‖u₀‖ + (4 * Real.pi * C * R * R) * duhamelConst α t := by
  refine le_trans (norm_sub_le _ _) (add_le_add (norm_heatFlow1_le α t u₀) ?_)
  exact norm_duhamelIntegral_le hα ht (fun s => norm_quadCurve_le hm hC hR s)

theorem norm_mildMap1_sub_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u v : ℝ → Wiener1}
    (hu : Continuous u) (hv : Continuous v) {R : ℝ}
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R) {D : ℝ} (hD : ∀ s, ‖u s - v s‖ ≤ D)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖mildMap1 hα.le hm u₀ u t - mildMap1 hα.le hm u₀ v t‖
      ≤ (8 * Real.pi * C * R * D) * duhamelConst α t := by
  have hcancel : mildMap1 hα.le hm u₀ u t - mildMap1 hα.le hm u₀ v t
      = -(duhamelIntegral hα.le t (quadCurve hm u)
          - duhamelIntegral hα.le t (quadCurve hm v)) := by
    simp only [mildMap1]
    abel
  rw [hcancel, norm_neg]
  refine norm_duhamelIntegral_sub_le hα ht (continuous_quadCurve hm hu)
    (continuous_quadCurve hm hv) (fun s => norm_quadCurve_le hm hC hRu s)
    (fun s => norm_quadCurve_le hm hC hRv s) (fun s => ?_)
  exact le_trans (norm_quadCurve_sub_le hm hC hRu hRv s)
    (mul_le_mul_of_nonneg_left (hD s) (by
      have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
      have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRu 0)
      have hpi := Real.pi_pos
      positivity))

/-! ## The mild map as a self-map of curves -/

/-- The mild map, as a map of bounded continuous curves on `[0,T]`. -/
noncomputable def mildCurveMap {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {T : ℝ}
    (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) : TimeI T →ᵇ Wiener1 :=
  affineCurveMap hα hm hC (fun t => heatFlow1 α t u₀) (continuous_heatFlow1 α u₀) hT U

@[simp] theorem mildCurveMap_apply {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {T : ℝ}
    (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) (t : TimeI T) :
    mildCurveMap hα hm hC u₀ hT U t = mildMap1 hα.le hm u₀ (extendCurve hT U) (t : ℝ) := rfl

/-! ## The local mild solution -/

/-- **The fixed-point construction.**  On a short enough interval the mild map is a self-map
of the closed ball of radius `2‖θ₀‖+1` in the space of bounded continuous curves and a
`1/2`-contraction there, so Banach's theorem gives a fixed curve, together with the
approximating iterates (used later to transport reality). -/
theorem exists_mildCurve_fixedPoint {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ (T : ℝ) (hT : 0 < T),
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * C * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      (∀ V : TimeI T →ᵇ Wiener1, ‖V‖ ≤ 2 * ‖u₀‖ + 1 →
        ‖mildCurveMap hα hm hC u₀ hT.le V‖ ≤ 2 * ‖u₀‖ + 1) ∧
      ∃ U : TimeI T →ᵇ Wiener1,
        ‖U‖ ≤ 2 * ‖u₀‖ + 1 ∧
        mildCurveMap hα hm hC u₀ hT.le U = U ∧
        Tendsto (fun n : ℕ => (mildCurveMap hα hm hC u₀ hT.le)^[n] 0) atTop (𝓝 U) := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hpi := Real.pi_pos
  have hu₀ : (0:ℝ) ≤ ‖u₀‖ := norm_nonneg _
  have hR0 : (0:ℝ) < 2 * ‖u₀‖ + 1 := by linarith
  set L : ℝ := 8 * Real.pi * C * (2 * ‖u₀‖ + 1)
      + 4 * Real.pi * C * (2 * ‖u₀‖ + 1) * (2 * ‖u₀‖ + 1) + 1 with hLdef
  have hL0 : (0:ℝ) < L := by simp only [hLdef]; positivity
  have h2L : (0:ℝ) < 2 * L := by linarith
  obtain ⟨T, hT, hsm⟩ := exists_duhamelConst_lt hα (ε := 1 / (2 * L)) (by positivity)
  have hcomb : ∀ t ∈ Set.Icc (0:ℝ) T,
      (8 * Real.pi * C * (2 * ‖u₀‖ + 1)
        + 4 * Real.pi * C * (2 * ‖u₀‖ + 1) * (2 * ‖u₀‖ + 1)) * duhamelConst α t ≤ 1 / 2 := by
    intro t ht
    have hg := (hsm t ht).le
    have hcoef : (0:ℝ) ≤ 8 * Real.pi * C * (2 * ‖u₀‖ + 1)
        + 4 * Real.pi * C * (2 * ‖u₀‖ + 1) * (2 * ‖u₀‖ + 1) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hg hcoef) ?_
    rw [mul_one_div, div_le_iff₀ h2L]
    have hexp : (1:ℝ) / 2 * (2 * L) = L := by ring
    rw [hexp, hLdef]
    linarith
  obtain ⟨hballmaps, U, hUmem, hfix, htend⟩ :=
    exists_affineCurve_fixedPoint hα hm hC (fun t => heatFlow1 α t u₀)
      (continuous_heatFlow1 α u₀) (fun t => norm_heatFlow1_le α t u₀) hT.le hcomb
  refine ⟨T, hT, ?_, hballmaps, U, hUmem, hfix, htend⟩
  intro t ht
  have hg := (hsm t ht).le
  have hcoef : (0:ℝ) ≤ 8 * Real.pi * C * (2 * ‖u₀‖ + 1) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hg hcoef) ?_
  rw [mul_one_div, div_le_iff₀ h2L]
  have hexp : (1:ℝ) / 2 * (2 * L) = L := by ring
  rw [hexp, hLdef]
  have h4 : (0:ℝ) ≤ 4 * Real.pi * C * (2 * ‖u₀‖ + 1) * (2 * ‖u₀‖ + 1) := by positivity
  linarith

/-- **Local existence of a mild solution.**  For every datum `θ₀` in the first-order Wiener
space `A¹` and every `α > 1/2` there is a positive time `T` and a bounded continuous curve
`θ : ℝ → A¹` with `θ(0) = θ₀` which satisfies the mild (Duhamel) formulation

    θ(t) = e^{-t(-Δ)^α} θ₀ - ∫₀^t e^{-(t-s)(-Δ)^α} N_m(θ(s), θ(s)) ds

for every `t ∈ [0,T]`.  The proof is Banach's fixed-point theorem on the closed ball of
radius `2‖θ₀‖+1` in the space of bounded continuous curves; the smallness of `T` comes from
`duhamelConst α t → 0`, which is where `1/2 < α` is used. -/
theorem exists_local_mild_solution {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * C * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u) := by
  obtain ⟨T, hT, hsmall, -, U, hUmem, hfix, -⟩ := exists_mildCurve_fixedPoint hα hm hC u₀
  refine ⟨T, hT, hsmall, extendCurve hT.le U, continuous_extendCurve hT.le U, ?_, ?_, ?_⟩
  · calc extendCurve hT.le U 0 = U (clampT hT.le 0) := rfl
      _ = mildCurveMap hα hm hC u₀ hT.le U (clampT hT.le 0) := by rw [hfix]
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) ((clampT hT.le 0 : ℝ)) := rfl
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) 0 := by
            rw [clampT_coe hT.le le_rfl hT.le]
      _ = u₀ := mildMap1_zero hα.le hm u₀ _
  · intro t
    exact le_trans (norm_extendCurve_le hT.le U t) hUmem
  · intro t ht
    calc extendCurve hT.le U t = U (clampT hT.le t) := rfl
      _ = mildCurveMap hα hm hC u₀ hT.le U (clampT hT.le t) := by rw [hfix]
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) ((clampT hT.le t : ℝ)) := rfl
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) t := by
            rw [clampT_coe hT.le ht.1 ht.2]
      _ = heatFlow1 α t u₀
            - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT.le U)) := rfl

/-- **Local existence for the source-faithful rotated-gradient velocity.**  Specialization of
`exists_local_mild_solution` to the symbol `m = ∇^⊥(κ · )` of the Li–Wang velocity operator,
with the symbol bound *derived* from the weighted kernel bound. -/
theorem exists_local_mild_solution_rotatedGradient {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ}
    {A : ℝ} (hb : KernelBound κ A) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀
          - duhamelIntegral hα.le t
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) :=
  exists_local_mild_solution hα (rotatedGradientSymbol_bdd ⟨A, hb⟩)
    (fun j k => rotatedGradientSymbol_norm_le hb j k) u₀

/-! ## Uniqueness of the mild solution -/

/-- **Uniqueness of the mild solution** on a time interval where the contraction factor is at
most `1/2`: two bounded continuous curves that both satisfy the mild equation with the same
datum coincide on `[0,T]`.  This is `affine_solution_unique` with the affine part
`A(t) = e^{-t(-Δ)^α}θ₀`. -/
theorem mild_solution_unique {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {R T : ℝ}
    (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t :=
  affine_solution_unique hα hm hC (fun t => heatFlow1 α t u₀) hT hsmall hu hv hRu hRv heu hev

/-- **Local well-posedness of the mild formulation**: existence *and* uniqueness on a common
short time interval. -/
theorem exists_local_mild_solution_unique {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
        (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) := by
  obtain ⟨T, hT, hsmall, hex⟩ := exists_local_mild_solution hα hm hC u₀
  exact ⟨T, hT, hex, fun u v hu hv hRu hRv heu hev =>
    mild_solution_unique hα hm hC u₀ hT.le hsmall hu hv hRu hRv heu hev⟩

/-! ## Continuous dependence on the datum -/

theorem heatFlow1_sub (α t : ℝ) (u v : Wiener1) :
    heatFlow1 α t u - heatFlow1 α t v = heatFlow1 α t (u - v) := by
  apply Wiener1.coeff_injective
  funext k
  show (heatFlow1 α t u).coeff k - (heatFlow1 α t v).coeff k
    = heatSymbol α (max t 0) k * (u - v).coeff k
  rw [heatFlow1_coeff, heatFlow1_coeff, Wiener1.coeff_sub]
  show heatSymbol α (max t 0) k * u.coeff k - heatSymbol α (max t 0) k * v.coeff k
    = heatSymbol α (max t 0) k * (u.coeff k - v.coeff k)
  ring

/-- **Continuous dependence on the initial datum.**  On a time interval where the contraction
factor is at most `1/2`, two mild solutions bounded by `R` differ by at most twice the
distance of their data.  Together with `exists_local_mild_solution` and
`mild_solution_unique` this is Hadamard local well-posedness of the mild formulation. -/
theorem mild_solution_stability {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ v₀ : Wiener1) {R T : ℝ}
    (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatFlow1 α t v₀ - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ 2 * ‖u₀ - v₀‖ := by
  have hUc : Continuous fun t : TimeI T => u (t : ℝ) := hu.comp continuous_subtype_val
  have hVc : Continuous fun t : TimeI T => v (t : ℝ) := hv.comp continuous_subtype_val
  set Ur : TimeI T →ᵇ Wiener1 := mkOfCompact ⟨fun t : TimeI T => u (t : ℝ), hUc⟩ with hUrdef
  set Vr : TimeI T →ᵇ Wiener1 := mkOfCompact ⟨fun t : TimeI T => v (t : ℝ), hVc⟩ with hVrdef
  have hD0 : (0:ℝ) ≤ dist Ur Vr := dist_nonneg
  have hd0 : (0:ℝ) ≤ ‖u₀ - v₀‖ := norm_nonneg _
  have hextu : ∀ s : ℝ, extendCurve hT Ur s = u ((clampT hT s : ℝ)) := fun _ => rfl
  have hextv : ∀ s : ℝ, extendCurve hT Vr s = v ((clampT hT s : ℝ)) := fun _ => rfl
  have hagree_u : ∀ s ∈ Set.Icc (0:ℝ) T, extendCurve hT Ur s = u s := by
    intro s hs; rw [hextu, clampT_coe hT hs.1 hs.2]
  have hagree_v : ∀ s ∈ Set.Icc (0:ℝ) T, extendCurve hT Vr s = v s := by
    intro s hs; rw [hextv, clampT_coe hT hs.1 hs.2]
  have hRU : ∀ s : ℝ, ‖extendCurve hT Ur s‖ ≤ R := fun s => by rw [hextu]; exact hRu _
  have hRV : ∀ s : ℝ, ‖extendCurve hT Vr s‖ ≤ R := fun s => by rw [hextv]; exact hRv _
  have hdiff : ∀ s : ℝ, ‖extendCurve hT Ur s - extendCurve hT Vr s‖ ≤ dist Ur Vr :=
    fun s => dist_extendCurve_le hT Ur Vr s
  have hkey : ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖u t - v t‖ ≤ ‖u₀ - v₀‖ + dist Ur Vr / 2 := by
    intro t ht
    have hsub : ∀ s ∈ Set.Icc (0:ℝ) t, u s = extendCurve hT Ur s := fun s hs =>
      (hagree_u s ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hsubv : ∀ s ∈ Set.Icc (0:ℝ) t, v s = extendCurve hT Vr s := fun s hs =>
      (hagree_v s ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hequ : u t = heatFlow1 α t u₀
        - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT Ur)) := by
      rw [heu t ht, duhamelIntegral_quadCurve_congr hα.le hm ht.1 hsub]
    have heqv : v t = heatFlow1 α t v₀
        - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT Vr)) := by
      rw [hev t ht, duhamelIntegral_quadCurve_congr hα.le hm ht.1 hsubv]
    have hsplit : u t - v t = heatFlow1 α t (u₀ - v₀)
        - (duhamelIntegral hα.le t (quadCurve hm (extendCurve hT Ur))
            - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT Vr))) := by
      rw [hequ, heqv, ← heatFlow1_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) (add_le_add (norm_heatFlow1_le α t (u₀ - v₀)) ?_)
    have hb := norm_duhamelIntegral_sub_le hα ht.1
      (continuous_quadCurve hm (continuous_extendCurve hT Ur))
      (continuous_quadCurve hm (continuous_extendCurve hT Vr))
      (fun s => norm_quadCurve_le hm hC hRU s) (fun s => norm_quadCurve_le hm hC hRV s)
      (fun s => le_trans (norm_quadCurve_sub_le hm hC hRU hRV s)
        (mul_le_mul_of_nonneg_left (hdiff s) (by
          have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
          have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRU 0)
          have hpi := Real.pi_pos
          positivity)))
    refine le_trans hb ?_
    have hs := hsmall t ht
    calc (8 * Real.pi * C * R * dist Ur Vr) * duhamelConst α t
        = dist Ur Vr * ((8 * Real.pi * C * R) * duhamelConst α t) := by ring
      _ ≤ dist Ur Vr * (1 / 2) := mul_le_mul_of_nonneg_left hs hD0
      _ = dist Ur Vr / 2 := by ring
  have hDle : dist Ur Vr ≤ ‖u₀ - v₀‖ + dist Ur Vr / 2 := by
    refine (dist_le (by linarith : (0:ℝ) ≤ ‖u₀ - v₀‖ + dist Ur Vr / 2)).2 (fun t => ?_)
    rw [dist_eq_norm]
    exact hkey (t : ℝ) t.2
  intro t ht
  have h := hkey t ht
  linarith

/-- **Hadamard local well-posedness of the mild formulation**: on one and the same time
interval there is a solution, it is unique among curves in the ball, and solutions depend
Lipschitz-continuously on their data. -/
theorem exists_local_well_posed {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
        (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) ∧
      (∀ (v₀ : Wiener1) (u v : ℝ → Wiener1), Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t v₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ 2 * ‖u₀ - v₀‖) := by
  obtain ⟨T, hT, hsmall, hex⟩ := exists_local_mild_solution hα hm hC u₀
  refine ⟨T, hT, hex, ?_, ?_⟩
  · exact fun u v hu hv hRu hRv heu hev =>
      mild_solution_unique hα hm hC u₀ hT.le hsmall hu hv hRu hRv heu hev
  · exact fun v₀ u v hu hv hRu hRv heu hev =>
      mild_solution_stability hα hm hC u₀ v₀ hT.le hsmall hu hv hRu hRv heu hev

end LiWang.WienerModel
