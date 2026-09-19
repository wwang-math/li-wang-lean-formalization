/-
# Every admissible smooth source has a jointly smooth real physical representative

`smoothSources hT W` is, by construction, the algebraic **span** of separated products of a
smooth compactly supported spatial profile with a `C^∞` time bump.  It is *not* claimed to be
the space of all jointly smooth compactly supported sources.  What is proved here is the
inclusion that duality actually needs:

> every element of `smoothSources hT W` has a **jointly smooth**, doubly periodic, **real**
> physical representative `Φ(t, y)`, compactly supported in `W × (0,T)`, which reproduces
> `sourcePhys` at every time of `[0,T]`.

The proof is a span induction on `SmoothSpacetimeRep`, whose closure under sums and real scalars
is proved directly (union of the spatial supports, min/max of the time supports).

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.TestSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.WienerModel

variable {T : ℝ}

/-- **A jointly smooth real physical representative** of a source curve, compactly supported
in `W × (0,T)`. -/
structure SmoothSpacetimeRep (hT : 0 < T) (W : Set Torus2) (V : Curve0 T)
    (Φ : ℝ × (ℝ × ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  per0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y))
  per1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))
  real : ∀ q, conj (Φ q) = Φ q
  agrees : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ y : Fin 2 → ℝ,
    sourcePhys hT.le V t (torusProj y) = Φ (t, (y 0, y 1))
  spaceSupp : ∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧
    ∀ (t : ℝ) (y : Fin 2 → ℝ), torusProj y ∉ K → Φ (t, (y 0, y 1)) = 0
  timeSupp : ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < T ∧ ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0

namespace SmoothSpacetimeRep

theorem zero (hT : 0 < T) (W : Set Torus2) :
    SmoothSpacetimeRep hT W (0 : Curve0 T) (fun _ => (0:ℂ)) where
  smooth := contDiff_const
  per0 _ _ _ := rfl
  per1 _ _ _ := rfl
  real _ := map_zero _
  agrees t _ y := by
    show sourcePhys hT.le (0 : Curve0 T) t (torusProj y) = 0
    rw [sourcePhys_zero]
    rfl
  spaceSupp := ⟨∅, isCompact_empty, Set.empty_subset _, fun _ _ _ => rfl⟩
  timeSupp := ⟨T / 4, 3 * T / 4, by linarith, by linarith, by linarith, fun _ _ _ => rfl⟩

theorem add {hT : 0 < T} {W : Set Torus2} {V V' : Curve0 T} {Φ Φ' : ℝ × (ℝ × ℝ) → ℂ}
    (h : SmoothSpacetimeRep hT W V Φ) (h' : SmoothSpacetimeRep hT W V' Φ') :
    SmoothSpacetimeRep hT W (V + V') (fun q => Φ q + Φ' q) := by
  obtain ⟨K, hKc, hKW, hKv⟩ := h.spaceSupp
  obtain ⟨K', hKc', hKW', hKv'⟩ := h'.spaceSupp
  obtain ⟨t₀, t₁, ht₀, ht01, ht1, htv⟩ := h.timeSupp
  obtain ⟨t₀', t₁', ht₀', ht01', ht1', htv'⟩ := h'.timeSupp
  refine ⟨h.smooth.add h'.smooth, fun t x y => by rw [h.per0, h'.per0],
    fun t x y => by rw [h.per1, h'.per1], fun q => by rw [map_add, h.real, h'.real], ?_,
    ⟨K ∪ K', hKc.union hKc', Set.union_subset hKW hKW', fun t y hy => ?_⟩,
    ⟨min t₀ t₀', max t₁ t₁', lt_min ht₀ ht₀',
      le_trans (min_le_left _ _) (le_trans ht01 (le_max_left _ _)), max_lt ht1 ht1',
      fun t ht p => ?_⟩⟩
  · intro t ht y
    have he : sourcePhys hT.le (V + V') t = sourcePhys hT.le V t + sourcePhys hT.le V' t :=
      sourcePhys_add hT.le V V' t
    rw [he]
    show sourcePhys hT.le V t (torusProj y) + sourcePhys hT.le V' t (torusProj y) = _
    rw [h.agrees t ht y, h'.agrees t ht y]
  · rw [hKv t y (fun hc => hy (Or.inl hc)), hKv' t y (fun hc => hy (Or.inr hc)), add_zero]
  · rw [htv t (fun hc => ht ⟨le_trans (min_le_left _ _) hc.1,
      le_trans hc.2 (le_max_left _ _)⟩) p,
      htv' t (fun hc => ht ⟨le_trans (min_le_right _ _) hc.1,
      le_trans hc.2 (le_max_right _ _)⟩) p, add_zero]

theorem smul {hT : 0 < T} {W : Set Torus2} {V : Curve0 T} {Φ : ℝ × (ℝ × ℝ) → ℂ} (r : ℝ)
    (h : SmoothSpacetimeRep hT W V Φ) :
    SmoothSpacetimeRep hT W (r • V) (fun q => ((r : ℝ) : ℂ) * Φ q) := by
  obtain ⟨K, hKc, hKW, hKv⟩ := h.spaceSupp
  obtain ⟨t₀, t₁, ht₀, ht01, ht1, htv⟩ := h.timeSupp
  refine ⟨contDiff_const.mul h.smooth, fun t x y => by rw [h.per0],
    fun t x y => by rw [h.per1], fun q => by rw [map_mul, Complex.conj_ofReal, h.real], ?_,
    ⟨K, hKc, hKW, fun t y hy => by rw [hKv t y hy, mul_zero]⟩,
    ⟨t₀, t₁, ht₀, ht01, ht1, fun t ht p => by rw [htv t ht p, mul_zero]⟩⟩
  intro t ht y
  have he : sourcePhys hT.le (r • V) t = r • sourcePhys hT.le V t := sourcePhys_smul hT.le r V t
  rw [he]
  show ((r : ℝ) : ℂ) * sourcePhys hT.le V t (torusProj y) = _
  rw [h.agrees t ht y]

end SmoothSpacetimeRep

/-- The representative of a generator: a `C^∞` time bump times a smooth localized profile. -/
theorem smoothSpacetimeRep_productSource (hT : 0 < T) {W : Set Torus2} {a : RealWiener}
    (ha : a ∈ smoothProfiles W) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) :
    SmoothSpacetimeRep hT W (productSource hT.le a hχ.continuous)
      (fun q => ((χ q.1 : ℝ) : ℂ) * planeLift a.val q.2) := by
  obtain ⟨hsm, K, hKc, hKW, hKv⟩ := ha
  obtain ⟨t₀, t₁, ht₀, ht01, ht1, htv⟩ := hχ.supp
  have hper : IsSmoothPeriodic (planeLift a.val) := isSmoothPeriodic_planeLift hsm
  have hlift : ∀ y : Fin 2 → ℝ, planeLift a.val (y 0, y 1) = synth a.val (torusProj y) := by
    intro y
    show lift a.val ![y 0, y 1] = synth a.val (torusProj y)
    rw [lift_def, vecPair_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨K, hKc, hKW, fun t y hy => ?_⟩,
    ⟨t₀, t₁, ht₀, ht01, ht1, fun t ht p => by rw [htv t ht]; simp⟩⟩
  · exact (Complex.ofRealCLM.contDiff.comp (hχ.smooth.comp contDiff_fst)).mul
      (hper.smooth.comp contDiff_snd)
  · intro t x y
    show ((χ t : ℝ) : ℂ) * planeLift a.val (x + 1, y) = ((χ t : ℝ) : ℂ) * planeLift a.val (x, y)
    rw [hper.per0 (x, y)]
  · intro t x y
    show ((χ t : ℝ) : ℂ) * planeLift a.val (x, y + 1) = ((χ t : ℝ) : ℂ) * planeLift a.val (x, y)
    rw [hper.per1 (x, y)]
  · intro q
    show conj (((χ q.1 : ℝ) : ℂ) * planeLift a.val q.2) = _
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    obtain ⟨y0, y1⟩ := q.2
    show conj (lift a.val ![y0, y1]) = lift a.val ![y0, y1]
    rw [lift_def]
    exact conj_synth_apply a.conjSymmetric _
  · intro t ht y
    rw [sourcePhys_productSource, clampT_coe hT.le ht.1 ht.2, hlift y]
  · show ((χ t : ℝ) : ℂ) * planeLift a.val (y 0, y 1) = 0
    rw [hlift y, hKv (torusProj y) hy, mul_zero]

/-- **Task 2.**  Every element of the admissible smooth source family has a jointly smooth,
doubly periodic, real physical representative compactly supported in `W × (0,T)`. -/
theorem exists_smoothSpacetimeRep (hT : 0 < T) {W : Set Torus2} {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) :
    ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, SmoothSpacetimeRep hT W V Φ := by
  refine Submodule.span_induction (p := fun V _ => ∃ Φ, SmoothSpacetimeRep hT W V Φ)
    ?_ ?_ ?_ ?_ hV
  · rintro V ⟨a, χ, hχc, ha, hbump, rfl⟩
    exact ⟨_, smoothSpacetimeRep_productSource hT ha hbump⟩
  · exact ⟨_, SmoothSpacetimeRep.zero hT W⟩
  · rintro V V' - - ⟨Φ, hΦ⟩ ⟨Φ', hΦ'⟩
    exact ⟨_, hΦ.add hΦ'⟩
  · rintro r V - ⟨Φ, hΦ⟩
    exact ⟨_, SmoothSpacetimeRep.smul r hΦ⟩

end LiWang.WienerModel
