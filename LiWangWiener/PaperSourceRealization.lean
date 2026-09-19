/-
# Realizing an arbitrary `C_c^∞(W × (0,T))` datum as a `Curve0 T` source

Li–Wang's input in (1.6) is a real `C^∞` function on the space-time cylinder, compactly
supported in `W × (0,T)`.  The packet's sources are elements of `Curve0 T`, i.e. bounded
continuous maps `[0,T] → A_ℝ(𝕋²)`.  v9.0 proved the inclusion in one direction — every smooth
source of the packet has such a physical field.  This module proves the **converse
realization**: every such field *is* the physical field of an actual `Curve0 T` source, and the
round trip is exact.

The only analytic content is time continuity in the Wiener norm, which is `SpacetimeCalculus`:
the fourth-order Fourier decay of the slices holds with a constant independent of time, so the
tail of the `ℓ¹` series is uniformly small and the finitely many remaining coefficients are
continuous by the parametric interval-integral theorem.

Part of `LiWangWienerPaperSourceRealizationPacket` v10.0.
-/
import LiWangWiener.SpacetimeCalculus
import LiWangWiener.PaperAlignment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.WienerModel

variable {T : ℝ}

/-! ## 1. The paper's space-time datum -/

/-- **The datum of Li–Wang (1.6)**: a real `C^∞` doubly periodic function on `ℝ × ℝ²`,
compactly supported in `W` in space and in a compact subinterval of `(0,T)` in time. -/
structure IsPaperField (hT : 0 < T) (W : Set Torus2) (Φ : ℝ × (ℝ × ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  per0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y))
  per1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))
  real : ∀ q, conj (Φ q) = Φ q
  spaceSupp : ∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧
    ∀ (t : ℝ) (y : Fin 2 → ℝ), torusProj y ∉ K → Φ (t, (y 0, y 1)) = 0
  timeSupp : ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < T ∧ ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0

/-- Every field of a `SmoothSpacetimeRep` is a paper field. -/
theorem isPaperField_of_rep {hT : 0 < T} {W : Set Torus2} {V : Curve0 T}
    {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : SmoothSpacetimeRep hT W V Φ) : IsPaperField hT W Φ where
  smooth := h.smooth
  per0 := h.per0
  per1 := h.per1
  real := h.real
  spaceSupp := h.spaceSupp
  timeSupp := h.timeSupp

/-! ## 2. The realization -/

/-- **The `Curve0 T` source realized by a paper field.**  Its value at time `t` is the real
Wiener element of the spatial slice `Φ(t, ·)`. -/
noncomputable def paperCurve {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) : Curve0 T :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : TimeI T => realWienerOfSmooth (slice Φ (t : ℝ))
        (isSmoothPeriodic_slice h.smooth h.per0 h.per1 (t : ℝ))
        (fun p => h.real ((t : ℝ), p)),
      by
        obtain ⟨a₀, a₁, -, ha01, -, hav⟩ := h.timeSupp
        refine (RealWiener.isometry_val.comp_continuous_iff).1 ?_
        exact (continuous_wienerSlice h.smooth h.per0 h.per1 ha01 hav).comp
          continuous_subtype_val⟩

@[simp] theorem paperCurve_apply {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) (t : TimeI T) :
    (paperCurve h) t = realWienerOfSmooth (slice Φ (t : ℝ))
      (isSmoothPeriodic_slice h.smooth h.per0 h.per1 (t : ℝ))
      (fun p => h.real ((t : ℝ), p)) := rfl

/-- On `[0,T]` the instantaneous source of the realization is the Wiener element of the slice. -/
theorem sourceFun_paperCurve {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    sourceFun hT.le (paperCurve h) t
      = wienerOfSmooth (slice Φ t) (isSmoothPeriodic_slice h.smooth h.per0 h.per1 t) := by
  have hcl : clampT hT.le t = (⟨t, ht⟩ : TimeI T) := Subtype.ext (clampT_coe hT.le ht.1 ht.2)
  rw [sourceFun, hcl]
  rfl

/-- **The round trip is exact**: the physical field of the realized source is the given paper
field, at every time of `[0,T]` and every point of the torus. -/
theorem sourcePhys_paperCurve {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (y : Fin 2 → ℝ) :
    sourcePhys hT.le (paperCurve h) t (torusProj y) = Φ (t, (y 0, y 1)) := by
  rw [sourcePhys, sourceFun_paperCurve h ht]
  show lift (wienerOfSmooth (slice Φ t) _) y = Φ (t, (y 0, y 1))
  exact lift_wienerOfSmooth _ y

/-- **The realized source has the given paper field as its space-time representative.** -/
theorem smoothSpacetimeRep_paperCurve {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) : SmoothSpacetimeRep hT W (paperCurve h) Φ where
  smooth := h.smooth
  per0 := h.per0
  per1 := h.per1
  real := h.real
  agrees := fun _ ht y => sourcePhys_paperCurve h ht y
  spaceSupp := h.spaceSupp
  timeSupp := h.timeSupp

/-- **Every paper datum is realized by an admissible paper source.** -/
theorem isPaperSource_paperCurve {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) : IsPaperSource hT W (paperCurve h) :=
  ⟨Φ, smoothSpacetimeRep_paperCurve h⟩

/-- **The two source descriptions match**: a source curve is an admissible paper source exactly
when its physical field is a paper datum realized by it. -/
theorem isPaperSource_iff_exists_paperField {hT : 0 < T} {W : Set Torus2} {V : Curve0 T} :
    IsPaperSource hT W V ↔ ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, IsPaperField hT W Φ ∧
      SmoothSpacetimeRep hT W V Φ := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    exact ⟨Φ, isPaperField_of_rep hΦ, hΦ⟩
  · rintro ⟨Φ, -, hΦ⟩
    exact ⟨Φ, hΦ⟩

end LiWang.WienerModel
