/-
# Aligning the packet's source family and observations with the paper's

Two things are proved here.

**Existence of paper solutions.**  `exists_paperExistence_of_higherBound3` runs the v9.0
fourth-weight bootstrap on the same Picard construction as v8.0 and produces a *paper* solution
(Proposition 3.1 at `s = 3`) for every admissible source in an explicit small ball;
`exists_paperExistence_smoothSources` discharges its hypothesis for the whole smooth source
family, using `hasHigherBound3_of_mem_smoothSources`.  The smallness is in the `Curve0 T` norm
throughout — the higher-order information enters only through the per-source `HasHigherBound3`,
never as a ball in a stronger norm.

**The source family.**  The paper's input is `C_c^∞(W × (0,T))`.  The packet's
`smoothSources hT W` is the span of separated products, which is a **subspace** of that, and the
inclusion is what the recovery argument needs: equality of the paper maps on all of
`C_c^∞(W × (0,T))` restricts to equality on this subfamily.  `isPaperSource_of_mem_smoothSources`
proves the inclusion by exhibiting, for each member, the jointly smooth real physical
representative of `SpacetimeRepresentative.lean`, compactly supported in `W × (0,T)`.  Nothing
here claims the converse; see `STATUS.md`.

Part of `LiWangWienerPaperMapAlignmentPacket` v9.0.
-/
import LiWangWiener.PaperMap
import LiWangWiener.SmoothThirdOrder
import LiWangWiener.SpacetimeRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. Existence of paper solutions on a small ball -/

/-- **Paper solutions exist on an explicit small ball.**  Same Picard construction as v8.0; the
only new input is the `wt³` source bound, which buys the `wt⁴` solution bound and hence the
`L²(0,T;H^{3+α})` membership. -/
theorem exists_paperExistence_of_higherBound3 (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (A : Submodule ℝ (Curve0 T)) (hA : ∀ f ∈ A, HasHigherBound3 hT.le f) :
    ∃ ε > 0, PaperExistence hα hT hm A ε := by
  classical
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, ‖sourceQuad hα hT.le m hm hr‖ ≤ b := ⟨_, le_rfl⟩
  have hb0 : (0:ℝ) ≤ b :=
    le_trans (ContinuousLinearMap.opNorm_nonneg (sourceQuad hα hT.le m hm hr)) hbdef
  have hK0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT.le
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  have hcc : ∀ r : ℕ, (0:ℝ) ≤ transportConst r C := by
    intro r; rw [transportConst]; have := Real.pi_pos; positivity
  have hcc1 : (0:ℝ) ≤ transportConst 1 C := hcc 1
  have hcc2 : (0:ℝ) ≤ transportConst 2 C := hcc 2
  have hcc3 : (0:ℝ) ≤ transportConst 3 C := hcc 3
  have hsum0 : (0:ℝ) ≤ transportConst 1 C + transportConst 2 C + transportConst 3 C := by
    linarith
  have hprodD : (0:ℝ) ≤ duhamelConst α T
      * (transportConst 1 C + transportConst 2 C + transportConst 3 C) := mul_nonneg hK0 hsum0
  set D : ℝ := duhamelConst α T * (transportConst 1 C + transportConst 2 C
    + transportConst 3 C) + b + 1 with hD
  have hD1 : (1:ℝ) ≤ D := by rw [hD]; linarith
  have hD0 : (0:ℝ) < D := by linarith
  have hbD : b ≤ D := by rw [hD]; linarith
  set ρ : ℝ := 1 / (4 * D) with hρdef
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; positivity
  have hbρ : b * ρ ≤ 1 / 4 := by
    rw [hρdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have habs : ∀ r : ℕ, transportConst r C ≤ transportConst 1 C + transportConst 2 C
      + transportConst 3 C → duhamelConst α T * (transportConst r C * ρ) ≤ 1 / 2 := by
    intro r hle
    have hmono : duhamelConst α T * transportConst r C
        ≤ duhamelConst α T * (transportConst 1 C + transportConst 2 C + transportConst 3 C) :=
      mul_le_mul_of_nonneg_left hle hK0
    have hleD : duhamelConst α T * transportConst r C ≤ D := by rw [hD]; linarith
    rw [hρdef]
    rw [show duhamelConst α T * (transportConst r C * (1 / (4 * D)))
        = (duhamelConst α T * transportConst r C) / (4 * D) from by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have habs1 := habs 1 (by linarith)
  have habs2 := habs 2 (by linarith)
  have habs3 := habs 3 (by linarith)
  obtain ⟨ε₁, hε₁0, h1⟩ := Metric.eventually_nhds_iff.1
    (eventually_sourceSolution_eq hα hT.le hm hr)
  obtain ⟨ε₂, hε₂0, h2⟩ := Metric.eventually_nhds_iff.1
    (eventually_norm_sourceSolution_le hα hT.le hm hr (r := ρ) hρ0)
  obtain ⟨ε₃, hε₃0, h3⟩ : ∃ ε > 0, ∀ f : Curve0 T, ‖f‖ < ε →
      ‖duhamelOp hα hT.le f‖ ≤ ρ / 2 := by
    refine ⟨ρ / (2 * (duhamelConst α T + 1)), by positivity, fun f hf => ?_⟩
    refine le_trans ((duhamelOp hα hT.le).le_opNorm f) ?_
    have hop : ‖(duhamelOp hα hT.le : Curve0 T →L[ℝ] Curve1 T)‖ ≤ duhamelConst α T :=
      norm_duhamelOp_le hα hT.le
    have hfn : (0:ℝ) ≤ ‖f‖ := norm_nonneg _
    have hmul : ‖(duhamelOp hα hT.le : Curve0 T →L[ℝ] Curve1 T)‖ * ‖f‖
        ≤ duhamelConst α T * (ρ / (2 * (duhamelConst α T + 1))) :=
      mul_le_mul hop hf.le hfn hK0
    refine le_trans hmul ?_
    have hKp : (0:ℝ) < duhamelConst α T + 1 := by linarith
    have hrw : duhamelConst α T * (ρ / (2 * (duhamelConst α T + 1)))
        = (duhamelConst α T / (duhamelConst α T + 1)) * (ρ / 2) := by field_simp
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
  obtain ⟨S, hS0, hS1, hS2, hS3⟩ := hA f hfA
  obtain ⟨R4, hR40, h4b⟩ := WB4_of_mild (hα := hα) (hT := hT.le) (hm := hm) (hr := hr) hC
    hbdef hb0 hρ0.le hbρ (h3 f hf3) hS0 hS0 hS0 hS1 hS2 hS3 habs1 habs2 habs3 hsmall hmild
  exact ⟨(mildPhysState hT.le (sourceSolution hα hT.le hm hr f), R4 ^ 2, T * R4 ^ 2,
      ‖sourceSolution hα hT.le hm hr f‖),
    isPaperSolution_mild hα1 hT hmild h4b⟩

/-- **Paper existence on the smooth source family is proved, not assumed.** -/
theorem exists_paperExistence_smoothSources (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) :
    ∃ ε > 0, PaperExistence hα hT hm (smoothSources hT W) ε :=
  exists_paperExistence_of_higherBound3 hα hα1 hT hm hr hC (smoothSources hT W)
    (fun _ hf => hasHigherBound3_of_mem_smoothSources hT W hf)

/-! ## 2. The packet's sources are paper sources -/

/-- **An admissible paper source**: a source curve whose physical spacetime field is a genuine
real `C^∞` function, doubly periodic and compactly supported in `W × (0,T)` — the datum of
Li–Wang (1.6). -/
def IsPaperSource (hT : 0 < T) (W : Set Torus2) (V : Curve0 T) : Prop :=
  ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, SmoothSpacetimeRep hT W V Φ

/-- **Every smooth source of the packet is an admissible paper source.** -/
theorem isPaperSource_of_mem_smoothSources (hT : 0 < T) {W : Set Torus2} {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) : IsPaperSource hT W V :=
  exists_smoothSpacetimeRep hT hV

/-- The physical field of a paper source is a **real** field, reproduced by the representative
at every time of `[0,T]`, and **compactly supported in `W × (0,T)`**.  (Smoothness is the
`smooth` field of `SmoothSpacetimeRep`, carried by `IsPaperSource` itself.) -/
theorem sourcePhys_eq_of_isPaperSource {hT : 0 < T} {W : Set Torus2} {V : Curve0 T}
    (h : IsPaperSource hT W V) :
    ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, (∀ q, conj (Φ q) = Φ q) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ y : Fin 2 → ℝ,
        sourcePhys hT.le V t (torusProj y) = Φ (t, (y 0, y 1)))
      ∧ (∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧
          ∀ (t : ℝ) (y : Fin 2 → ℝ), torusProj y ∉ K → Φ (t, (y 0, y 1)) = 0)
      ∧ (∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < T ∧ ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0) := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ, hΦ.real, hΦ.agrees, hΦ.spaceSupp, hΦ.timeSupp⟩

/-! ## 3. The paper observations are the packet observations -/

variable {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {A : Submodule ℝ (Curve0 T)} {ε : ℝ}

/-- The canonical paper state observation is represented by the packet's pointwise state
observation. -/
theorem paperObsState_ae_packet (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    ((paperObsState hex hf hs t : Torus2 → ℂ))
      =ᵐ[(volume : Measure Torus2)]
        fun x => (isPaperSolution_paperSol hex hf hs).isSobolevSolution.obsState t x := by
  have hae := (isPaperSolution_paperSol hex hf hs).isSobolevSolution.obsState_ae ht
  rw [sobClamp_of_mem hT.le _ ht] at hae
  exact hae.symm

/-- The canonical paper velocity observation is represented by the packet's pointwise velocity
observation. -/
theorem paperObsVel_ae_packet (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (hex : PaperExistence hα hT hm A ε) {f : Curve0 T} (hf : f ∈ A) (hs : ‖f‖ < ε)
    (j : Fin 2) (t : ℝ) :
    ((paperObsVel hex hf hs j t : Torus2 → ℂ))
      =ᵐ[(volume : Measure Torus2)]
        fun x => (isPaperSolution_paperSol hex hf hs).isSobolevSolution.obsVel j t x :=
  paperObsVel_ae hr hC hex hf hs (isPaperSolution_paperSol hex hf hs) j t

/-- **The paper solution class is inhabited over the class the recovery theorem uses.**  For a
nonempty open `W` there is a **nonzero** smooth source in `smoothSources hT W` admitting a
Li–Wang `s = 3` solution. -/
theorem exists_nonzero_smoothSource_paperSolution (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ}
    (hT : 0 < T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (f : Curve0 T) (M N K : ℝ) (θ : ℝ → TorusL2),
      f ∈ smoothSources hT W ∧ f ≠ 0 ∧ IsPaperSolution hα hT hm M N K f θ := by
  obtain ⟨ε, hε0, hex⟩ := exists_paperExistence_smoothSources hα hα1 hT hm hr hC W
  obtain ⟨V, hV, hV0, -⟩ := exists_nonzero_smoothSource hT hW hne
  have hVn : (0:ℝ) < ‖V‖ := norm_pos_iff.2 hV0
  set c : ℝ := ε / (2 * ‖V‖) with hc
  have hc0 : (0:ℝ) < c := by rw [hc]; positivity
  have hnorm : ‖c • V‖ = ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hc]
    field_simp
  have hsmall : ‖c • V‖ < ε := by rw [hnorm]; linarith
  have hne0 : c • V ≠ 0 := by
    refine norm_ne_zero_iff.1 ?_
    rw [hnorm]; positivity
  obtain ⟨p, hp⟩ := hex (c • V) (Submodule.smul_mem _ c hV) hsmall
  exact ⟨c • V, p.2.1, p.2.2.1, p.2.2.2, p.1, Submodule.smul_mem _ c hV, hne0, hp⟩

end LiWang.WienerModel
