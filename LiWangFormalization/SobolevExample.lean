/-
# The forward interface, and a constructed nontrivial Sobolev solution

Step 3 (interface and example) of the v8.0 Sobolev-compatibility bridge.

* `HasHigherBound` isolates what the bootstrap of `SmallSourceSobolev.lean` needs of a source:
  bounded `wt¹` and `wt²` coefficient sums, uniformly in time.  It is closed under sums and
  real scalings, so it passes to finite spans.  It is **per source**: a `Curve0` ball cannot
  supply it, because a highly oscillatory smooth source is small in `Curve0` and large in every
  higher norm.
* `exists_sobolevExistence_of_higherBound` discharges `SobolevExistence` on any admissible class
  all of whose members have a higher bound — the radius is uniform and positive; its
  absorption constants are explicit, while two of its three components are obtained
  existentially from neighbourhood statements.
* `meanSource` / `meanSolution` is an **actual constructed solution**, not a theorem about an
  assumed one: the spatially constant unit-mean control, whose mild solution is the plain
  Duhamel response (the transport term vanishes identically because the state has only the zero
  mode), is a Sobolev solution, and its terminal mean is exactly `T ≠ 0`.

Part of `LiWangFormalizationSobolevCompatibilityPacket` v8.0.
-/
import LiWangFormalization.SmallSourceSobolev
import LiWangFormalization.SobolevObservation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The forward interface -/

/-- **The higher-order source bound** required by the tame bootstrap. -/
def HasHigherBound (hT : 0 ≤ T) (f : Curve0 T) : Prop :=
  ∃ S : ℝ, 0 ≤ S ∧ (∀ s : ℝ, WB 1 S (fun k => (sourceFun hT f s) k))
    ∧ ∀ s : ℝ, WB 2 S (fun k => (sourceFun hT f s) k)

theorem HasHigherBound.add {hT : 0 ≤ T} {f g : Curve0 T} (hf : HasHigherBound hT f)
    (hg : HasHigherBound hT g) : HasHigherBound hT (f + g) := by
  obtain ⟨S₁, hS₁0, h₁a, h₁b⟩ := hf
  obtain ⟨S₂, hS₂0, h₂a, h₂b⟩ := hg
  refine ⟨S₁ + S₂, by linarith, fun s => ?_, fun s => ?_⟩
  · exact (WB.add (h₁a s) (h₂a s)).of_norm_le (fun k => le_of_eq (by rfl))
  · exact (WB.add (h₁b s) (h₂b s)).of_norm_le (fun k => le_of_eq (by rfl))

theorem HasHigherBound.smul {hT : 0 ≤ T} {f : Curve0 T} (c : ℝ) (hf : HasHigherBound hT f) :
    HasHigherBound hT (c • f) := by
  obtain ⟨S, hS0, ha, hb⟩ := hf
  refine ⟨|c| * S, by positivity, fun s => ?_, fun s => ?_⟩
  · refine WB.of_norm_le_mul (abs_nonneg c) (ha s) (fun k => ?_)
    show ‖(c : ℂ) • (sourceFun hT f s) k‖ ≤ |c| * ‖(sourceFun hT f s) k‖
    rw [norm_smul]
    simp
  · refine WB.of_norm_le_mul (abs_nonneg c) (hb s) (fun k => ?_)
    show ‖(c : ℂ) • (sourceFun hT f s) k‖ ≤ |c| * ‖(sourceFun hT f s) k‖
    rw [norm_smul]
    simp

/-- **`SobolevExistence` from the higher-order source bound.**  The smallness radius is uniform
and positive.  The absorption constants are explicit; two of the three radii combined into it
come from `nhds` statements and are therefore existential, not formulas.  The `H³` bound `M` is
produced per source, as the definition allows. -/
theorem exists_sobolevExistence_of_higherBound (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (A : Submodule ℝ (Curve0 T)) (hA : ∀ f ∈ A, HasHigherBound hT f) :
    ∃ ε > 0, SobolevExistence hα hT hm A ε := by
  classical
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, ‖sourceQuad hα hT m hm hr‖ ≤ b := ⟨_, le_rfl⟩
  have hb0 : (0:ℝ) ≤ b :=
    le_trans (ContinuousLinearMap.opNorm_nonneg (sourceQuad hα hT m hm hr)) hbdef
  have hK0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  set D : ℝ := duhamelConst α T * (transportConst 1 C + transportConst 2 C) + b + 1 with hD
  have hcc1 : (0:ℝ) ≤ transportConst 1 C := by
    rw [transportConst]; have := Real.pi_pos; positivity
  have hcc2 : (0:ℝ) ≤ transportConst 2 C := by
    rw [transportConst]; have := Real.pi_pos; positivity
  have hD1 : (1:ℝ) ≤ D := by rw [hD]; nlinarith
  have hD0 : (0:ℝ) < D := by linarith
  set ρ : ℝ := 1 / (4 * D) with hρdef
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; positivity
  have hbρ : b * ρ ≤ 1 / 4 := by
    rw [hρdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have habs1 : duhamelConst α T * (transportConst 1 C * ρ) ≤ 1 / 2 := by
    rw [hρdef]
    rw [show duhamelConst α T * (transportConst 1 C * (1 / (4 * D)))
        = (duhamelConst α T * transportConst 1 C) / (4 * D) from by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have habs2 : duhamelConst α T * (transportConst 2 C * ρ) ≤ 1 / 2 := by
    rw [hρdef]
    rw [show duhamelConst α T * (transportConst 2 C * (1 / (4 * D)))
        = (duhamelConst α T * transportConst 2 C) / (4 * D) from by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- a radius on which the implicit-function solution exists, solves the equation and is small
  obtain ⟨ε₁, hε₁0, h1⟩ := Metric.eventually_nhds_iff.1
    (eventually_sourceSolution_eq hα hT hm hr)
  obtain ⟨ε₂, hε₂0, h2⟩ := Metric.eventually_nhds_iff.1
    (eventually_norm_sourceSolution_le hα hT hm hr (r := ρ) hρ0)
  obtain ⟨ε₃, hε₃0, h3⟩ : ∃ ε > 0, ∀ f : Curve0 T, ‖f‖ < ε →
      ‖duhamelOp hα hT f‖ ≤ ρ / 2 := by
    refine ⟨ρ / (2 * (duhamelConst α T + 1)), by positivity, fun f hf => ?_⟩
    refine le_trans ((duhamelOp hα hT).le_opNorm f) ?_
    have hop : ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ ≤ duhamelConst α T :=
      norm_duhamelOp_le hα hT
    have hfn : (0:ℝ) ≤ ‖f‖ := norm_nonneg _
    have : ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ * ‖f‖
        ≤ duhamelConst α T * (ρ / (2 * (duhamelConst α T + 1))) :=
      mul_le_mul hop hf.le hfn hK0
    refine le_trans this ?_
    have hKp : (0:ℝ) < duhamelConst α T + 1 := by linarith
    have hrw : duhamelConst α T * (ρ / (2 * (duhamelConst α T + 1)))
        = (duhamelConst α T / (duhamelConst α T + 1)) * (ρ / 2) := by
      field_simp
    rw [hrw]
    have hfrac : duhamelConst α T / (duhamelConst α T + 1) ≤ 1 := by
      rw [div_le_one hKp]; linarith
    nlinarith [hρ0.le]
  refine ⟨min (min ε₁ ε₂) ε₃, by positivity, ?_⟩
  intro f hfA hfn
  have hf1 : ‖f‖ < ε₁ := lt_of_lt_of_le hfn (le_trans (min_le_left _ _) (min_le_left _ _))
  have hf2 : ‖f‖ < ε₂ := lt_of_lt_of_le hfn (le_trans (min_le_left _ _) (min_le_right _ _))
  have hf3 : ‖f‖ < ε₃ := lt_of_lt_of_le hfn (min_le_right _ _)
  have hmild := h1 (by rwa [dist_zero_right])
  have hsmall := h2 (by rwa [dist_zero_right])
  obtain ⟨S, hS0, hS1, hS2⟩ := hA f hfA
  obtain ⟨R3, hR30, h3b⟩ := WB3_of_mild (hα := hα) (hT := hT) (hm := hm) (hr := hr) hC hbdef
    hb0 hρ0.le hbρ (h3 f hf3) hS0 hS0 hS1 hS2 habs1 habs2 hsmall hmild
  exact ⟨R3 ^ 2, mildPhysState hT (sourceSolution hα hT hm hr f),
    isSobolevSolution_mild hmild h3b⟩

/-! ## 2. A constructed nontrivial Sobolev solution -/

theorem conjSymmetric_wdirac0 : ConjSymmetric ((wdirac (0 : Gam) : Wiener) : Gam → ℂ) := by
  intro k
  by_cases hk : k = 0
  · subst hk; simp [diracFun]
  · have hnk : -k ≠ 0 := fun h => hk (neg_eq_zero.1 h)
    simp [diracFun, hk, hnk]

/-- The constant real profile `1` on the torus: a state with **mean one**. -/
noncomputable def meanProfile : RealWiener := RealWiener.mk (wdirac (0 : Gam)) conjSymmetric_wdirac0

/-- A concrete nonzero-mean control: constant in space and in time. -/
noncomputable def meanSource (hT : 0 ≤ T) : Curve0 T :=
  productSource hT meanProfile (continuous_const (y := (1:ℝ)))

theorem sourceFun_meanSource (hT : 0 ≤ T) (s : ℝ) (k : Gam) :
    (sourceFun hT (meanSource hT) s) k = diracFun 0 k := by
  show (1 : ℝ) • (wdirac (0 : Gam)) k = _
  simp

/-- The constructed solution: the plain Duhamel response of the mean source. -/
noncomputable def meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) : Curve1 T :=
  duhamelOp hα hT (meanSource hT)

/-- Its coefficients are supported at the zero mode. -/
theorem meanSolution_coeff_eq_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) {k : Gam} (hk : k ≠ 0) :
    (curveState hT (meanSolution hα hT) t).coeff k = 0 := by
  rw [meanSolution, coeff_duhamelOp_eq_scalarDuhamel hα hT _ k ht, scalarDuhamel]
  have hz : ∀ s : ℝ, ((Real.exp (-((t - s) * fracSymbol α k)) : ℝ) : ℂ)
      * (sourceFun hT (meanSource hT) s) k = 0 := by
    intro s
    rw [sourceFun_meanSource hT s k, diracFun, if_neg hk, mul_zero]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℂ)) (fun s _ => hz s)]
  simp

/-- **The zero mode is exactly the time primitive of the mean**: `θ̂₀(t) = t`. -/
theorem meanSolution_zero_mode (hα : 1 / 2 < α) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT (meanSolution hα hT) t).coeff 0 = (t : ℂ) := by
  have hα0 : (0:ℝ) < α := by linarith
  rw [meanSolution, coeff_duhamelOp_eq_scalarDuhamel hα hT _ 0 ht, scalarDuhamel,
    fracSymbol_zero_eq hα0]
  have hone : ∀ s : ℝ, ((Real.exp (-((t - s) * (0:ℝ))) : ℝ) : ℂ)
      * (sourceFun hT (meanSource hT) s) 0 = 1 := by
    intro s
    rw [sourceFun_meanSource hT s 0, diracFun, if_pos rfl]
    norm_num
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℂ)) (fun s _ => hone s),
    intervalIntegral.integral_const, sub_zero]
  exact (Complex.real_smul (x := t) (z := 1)).trans (mul_one _)


/-- The coefficient vanishing, at every real time (the curve is clamped outside `[0,T]`). -/
theorem meanSolution_coeff_eq_zero' (hα : 1 / 2 < α) (hT : 0 ≤ T) (s : ℝ) {k : Gam}
    (hk : k ≠ 0) : (curveState hT (meanSolution hα hT) s).coeff k = 0 := by
  have heq : curveState hT (meanSolution hα hT) s
      = curveState hT (meanSolution hα hT) ((clampT hT s : TimeI T) : ℝ) := by
    rw [curveState_coe hT _ (clampT hT s)]
    rfl
  rw [heq]
  exact meanSolution_coeff_eq_zero hα hT (clampT hT s).2 hk

/-- **The transport term vanishes identically** for the mean-mode state: the gradient of a
constant-in-space field is zero. -/
theorem fourierDeriv_meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (j : Fin 2) (s : ℝ) :
    fourierDeriv j (curveState hT (meanSolution hα hT) s) = 0 := by
  refine lp.ext (funext fun k => ?_)
  show twoPiI * ((k j : ℤ) : ℂ) * (curveState hT (meanSolution hα hT) s).coeff k = (0 : Wiener) k
  by_cases hk : k = 0
  · subst hk
    show twoPiI * (((0 : Gam) j : ℤ) : ℂ) * _ = _
    have hz : ((0 : Gam) j : ℤ) = 0 := rfl
    rw [hz]
    rw [show ((0 : Wiener) (0 : Gam)) = 0 from rfl]
    simp
  · rw [meanSolution_coeff_eq_zero' hα hT s hk]
    rw [show ((0 : Wiener) k) = 0 from rfl]
    simp

theorem transport_meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (s : ℝ) :
    transport m hm (curveState hT (meanSolution hα hT) s)
        (curveState hT (meanSolution hα hT) s) = 0 := by
  rw [transport_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [fourierDeriv_meanSolution hα hT j s]
  refine lp.ext (funext fun k => ?_)
  show (∑' p : Gam,
      (velocity m hm j (incl (curveState hT (meanSolution hα hT) s)) : Wiener) p
        * (0 : Wiener) (k - p)) = (0 : Wiener) k
  have hz : ∀ p : Gam,
      (velocity m hm j (incl (curveState hT (meanSolution hα hT) s)) : Wiener) p
        * (0 : Wiener) (k - p) = 0 := by
    intro p
    rw [show ((0 : Wiener) (k - p)) = 0 from rfl, mul_zero]
  rw [tsum_congr hz, tsum_zero]
  rw [show ((0 : Wiener) k) = 0 from rfl]

theorem spacetimeTransport_meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    spacetimeTransport m hm hr (meanSolution hα hT) (meanSolution hα hT) = (0 : Curve0 T) := by
  refine DFunLike.ext _ _ (fun t => RealWiener.val_injective ?_)
  show transport m hm ((meanSolution hα hT) t).val ((meanSolution hα hT) t).val = (0 : Wiener)
  have hval : ((meanSolution hα hT) t).val = curveState hT (meanSolution hα hT) (t : ℝ) :=
    (curveState_coe hT _ t).symm
  rw [hval]
  exact transport_meanSolution hα hT hm (t : ℝ)

/-- **The constructed mean-mode state is a mild solution**, for every source size — no smallness
is needed, because the nonlinearity vanishes on it identically. -/
theorem meanSolution_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    meanSolution hα hT + sourceQuad hα hT m hm hr (meanSolution hα hT) (meanSolution hα hT)
      = duhamelOp hα hT (meanSource hT) := by
  have hq : sourceQuad hα hT m hm hr (meanSolution hα hT) (meanSolution hα hT) = 0 := by
    show duhamelOp hα hT (spacetimeTransport m hm hr (meanSolution hα hT) (meanSolution hα hT))
        = 0
    rw [spacetimeTransport_meanSolution hα hT hm hr, map_zero]
  rw [hq, add_zero, meanSolution]

/-- Every weighted coefficient sum of the constructed state is controlled by its `A¹` norm,
because only the zero mode is present and `wt 0 = 1`. -/
theorem WB_meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (r : ℕ) (t : ℝ) :
    WB r ‖meanSolution hα hT‖ (curveState hT (meanSolution hα hT) t).coeff := by
  intro F
  have hwt0 : wt (0 : Gam) = 1 := by
    show 1 + |(((0 : Gam) 0 : ℤ) : ℝ)| + |(((0 : Gam) 1 : ℤ) : ℝ)| = 1
    norm_num
  have hterm : ∀ k ∈ F, wt k ^ r * ‖(curveState hT (meanSolution hα hT) t).coeff k‖
      ≤ if k = 0 then ‖meanSolution hα hT‖ else 0 := by
    intro k _
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, hwt0, one_pow, one_mul]
      refine le_trans ?_ (norm_curveState_le hT (meanSolution hα hT) t)
      refine le_trans ?_ (le_of_eq (Wiener1.norm_eq _).symm)
      have hsum := (Wiener1.summable_wt (curveState hT (meanSolution hα hT) t)).sum_le_tsum
        ({0} : Finset Gam) (fun j _ => mul_nonneg (wt_pos j).le (norm_nonneg _))
      simpa [hwt0] using hsum
    · rw [if_neg hk, meanSolution_coeff_eq_zero' hα hT t hk, norm_zero, mul_zero]
  calc (∑ k ∈ F, wt k ^ r * ‖(curveState hT (meanSolution hα hT) t).coeff k‖)
      ≤ ∑ k ∈ F, (if k = 0 then ‖meanSolution hα hT‖ else 0) := Finset.sum_le_sum hterm
    _ = if (0 : Gam) ∈ F then ‖meanSolution hα hT‖ else 0 :=
        Finset.sum_ite_eq' F (0 : Gam) (fun _ => ‖meanSolution hα hT‖)
    _ ≤ ‖meanSolution hα hT‖ := by
        by_cases h0 : (0 : Gam) ∈ F
        · rw [if_pos h0]
        · rw [if_neg h0]; exact norm_nonneg _

/-- **The constructed solution is a Sobolev solution.**  This is an actual constructed object:
the source, the state and every hypothesis of `IsSobolevSolution` are produced, not assumed. -/
theorem isSobolevSolution_meanSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    IsSobolevSolution hα hT hm (‖meanSolution hα hT‖ ^ 2) (meanSource hT)
      (mildPhysState hT (meanSolution hα hT)) :=
  isSobolevSolution_mild (hα := hα) (hT := hT) (hm := hm) (hr := hr)
    (meanSolution_mild hα hT hm hr) (fun t _ => WB_meanSolution hα hT 3 t)

/-- **The constructed solution has nonzero terminal mean** when `T ≠ 0`: its zero Fourier mode
at time `T` is exactly `T`.  Nothing here imposes a mean-zero control. -/
theorem meanSolution_terminal_mean (hα : 1 / 2 < α) (hT : 0 ≤ T) :
    l2coeff 0 (mildPhysState hT (meanSolution hα hT) T) = (T : ℂ) := by
  rw [l2coeff_mildPhysState]
  exact meanSolution_zero_mode hα hT ⟨hT, le_rfl⟩

theorem meanSolution_terminal_mean_ne_zero (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) :
    l2coeff 0 (mildPhysState hT.le (meanSolution hα hT.le) T) ≠ 0 := by
  rw [meanSolution_terminal_mean hα hT.le]
  exact_mod_cast ne_of_gt hT

end LiWang.Formalization
