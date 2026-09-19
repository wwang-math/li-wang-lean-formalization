/-
# The real vector space of smooth sources compactly supported in `W × (0,T)`

This module assembles the spatial profiles of `SmoothSource` and a genuine `C^∞` time bump
into an honest `ℝ`-submodule `smoothSources hT W` of the packet's source space `Curve0 T`,
and proves:

* every element is compactly supported strictly inside `W × (0,T)` (`CompactlySupportedIn`),
  hence in particular lies in `localizedSources`;
* the curve is continuous **in the Wiener norm** — it is literally a bounded continuous map
  into `RealWiener` — and its physical field at time `t` is `χ(t)` times the synthesized
  spatial profile;
* the construction is inverse to the Euclidean smooth periodic lift (`synthesis recovers the
  prescribed physical source`);
* the space is nontrivial for every nonempty open `W` and every `T > 0`.

Part of `LiWangFormalizationSmoothObservationPacket` v5.0.
-/
import LiWangFormalization.SmoothSource
import LiWangFormalization.LocalizedSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.Formalization

variable {T : ℝ}

/-! ## 1. Compactly supported sources form a submodule -/

@[simp] theorem sourceFun_zero' (hT : 0 ≤ T) (s : ℝ) :
    sourceFun hT (0 : Curve0 T) s = 0 := rfl

/-- **Compactly supported sources form an `ℝ`-submodule** of `Curve0 T`. -/
noncomputable def compactlySupportedSources (hT : 0 < T) (W : Set Torus2) :
    Submodule ℝ (Curve0 T) where
  carrier := {V | CompactlySupportedIn hT.le W V}
  add_mem' := by
    rintro V V' ⟨⟨Ka, hKa, hKaW, hva⟩, ⟨a₀, a₁, ha₀, ha, ha₁, hta⟩⟩
      ⟨⟨Kb, hKb, hKbW, hvb⟩, ⟨b₀, b₁, hb₀, hb, hb₁, htb⟩⟩
    refine ⟨⟨Ka ∪ Kb, hKa.union hKb, Set.union_subset hKaW hKbW, fun t x hx => ?_⟩,
      ⟨min a₀ b₀, max a₁ b₁, lt_min ha₀ hb₀, le_trans (min_le_left _ _)
        (le_trans ha (le_max_left _ _)), max_lt ha₁ hb₁, fun t ht => ?_⟩⟩
    · rw [sourcePhys_add]
      show sourcePhys hT.le V t x + sourcePhys hT.le V' t x = 0
      rw [hva t x (fun h => hx (Or.inl h)), hvb t x (fun h => hx (Or.inr h)), add_zero]
    · rw [sourceFun_add, hta t (fun hc => ht ⟨le_trans (min_le_left _ _) hc.1,
        le_trans hc.2 (le_max_left _ _)⟩), htb t (fun hc => ht ⟨le_trans (min_le_right _ _) hc.1,
        le_trans hc.2 (le_max_right _ _)⟩), add_zero]
  zero_mem' := by
    refine ⟨⟨∅, isCompact_empty, Set.empty_subset _, fun t x _ => ?_⟩,
      ⟨T / 4, 3 * T / 4, by linarith, by linarith, by linarith, fun t _ => ?_⟩⟩
    · rw [sourcePhys_zero]; rfl
    · rw [sourceFun_zero']
  smul_mem' := by
    rintro r V ⟨⟨Ka, hKa, hKaW, hva⟩, ⟨a₀, a₁, ha₀, ha, ha₁, hta⟩⟩
    refine ⟨⟨Ka, hKa, hKaW, fun t x hx => ?_⟩, ⟨a₀, a₁, ha₀, ha, ha₁, fun t ht => ?_⟩⟩
    · rw [sourcePhys_smul]
      show (r : ℂ) • sourcePhys hT.le V t x = 0
      rw [hva t x hx, smul_zero]
    · rw [sourceFun_smul, hta t ht, smul_zero]

@[simp] theorem mem_compactlySupportedSources (hT : 0 < T) (W : Set Torus2) (V : Curve0 T) :
    V ∈ compactlySupportedSources hT W ↔ CompactlySupportedIn hT.le W V := Iff.rfl

/-! ## 2. The smooth source space -/

/-- The generators: a smooth compactly supported spatial profile times a `C^∞` time bump. -/
def smoothSourceGens (hT : 0 < T) (W : Set Torus2) : Set (Curve0 T) :=
  {V | ∃ (a : RealWiener) (χ : ℝ → ℝ) (hχ : Continuous χ),
      a ∈ smoothProfiles W ∧ IsSmoothTimeBump T χ ∧ V = productSource hT.le a hχ}

/-- **The real vector space of smooth sources compactly supported in `W × (0,T)`.** -/
noncomputable def smoothSources (hT : 0 < T) (W : Set Torus2) : Submodule ℝ (Curve0 T) :=
  Submodule.span ℝ (smoothSourceGens hT W)

theorem smoothSourceGens_compactlySupported (hT : 0 < T) (W : Set Torus2)
    {V : Curve0 T} (hV : V ∈ smoothSourceGens hT W) : CompactlySupportedIn hT.le W V := by
  obtain ⟨a, χ, hχ, ⟨-, K, hKc, hKW, hvan⟩, hbump, rfl⟩ := hV
  obtain ⟨t₀, t₁, ht₀, ht, ht₁, hsupp⟩ := hbump.supp
  exact productSource_compactlySupported hT.le a hχ hKc hKW hvan ht₀ ht ht₁ hsupp

/-- Every smooth source is compactly supported strictly inside `W × (0,T)`. -/
theorem smoothSources_le_compactlySupported (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ compactlySupportedSources hT W :=
  Submodule.span_le.2 (fun V hV => smoothSourceGens_compactlySupported hT W hV)

/-- Every smooth source is a localized source. -/
theorem smoothSources_le_localizedSources (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ localizedSources hT.le W := by
  intro V hV
  exact (smoothSources_le_compactlySupported hT W hV).supportedIn

theorem compactlySupportedIn_of_mem_smoothSources (hT : 0 < T) (W : Set Torus2)
    {V : Curve0 T} (hV : V ∈ smoothSources hT W) : CompactlySupportedIn hT.le W V :=
  smoothSources_le_compactlySupported hT W hV

/-! ## 3. The smooth source curve attached to smooth space-time data -/

/-- The source curve of a smooth real spatial profile and a `C^∞` time bump. -/
noncomputable def smoothSourceCurve (hT : 0 < T) {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) : Curve0 T :=
  productSource hT.le (realWienerOfSmooth G hG hre) hχ.continuous

/-- **The source curve is continuous in the Wiener norm** — it is literally a bounded
continuous map into the real Wiener algebra. -/
theorem continuous_smoothSourceCurve (hT : 0 < T) {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) :
    Continuous fun t : TimeI T => smoothSourceCurve hT hG hre hχ t :=
  (smoothSourceCurve hT hG hre hχ).continuous

/-- **Synthesis recovers the prescribed physical source**: at every time the physical field of
the smooth source curve is `χ(t)` times the given smooth periodic profile. -/
theorem smoothSourceCurve_physical (hT : 0 < T) {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) (s : ℝ)
    (y : Fin 2 → ℝ) :
    sourcePhys hT.le (smoothSourceCurve hT hG hre hχ) s (torusProj y)
      = ((χ ((clampT hT.le s : TimeI T) : ℝ) : ℝ) : ℂ) * G (y 0, y 1) := by
  rw [smoothSourceCurve, sourcePhys_productSource]
  congr 1
  have e := congrFun (planeLift_wienerOfSmooth hG) (y 0, y 1)
  rw [planeLift_apply, vecPair_eq] at e
  exact e

/-- The inverse property: the Wiener element of a smooth periodic function has that function
as its own physical representative. -/
theorem wienerOfSmooth_planeLift {a : Wiener} (h : SmoothWiener a) :
    wienerOfSmooth (planeLift a) (isSmoothPeriodic_planeLift h) = a :=
  planeLift_injective (planeLift_wienerOfSmooth _)

/-! ## 4. Non-vacuity -/

/-- **The smooth source space is nontrivial** for every `T > 0` and every nonempty open `W`. -/
theorem exists_nonzero_smoothSource (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hne : W.Nonempty) :
    ∃ V ∈ smoothSources hT W, V ≠ 0 ∧ CompactlySupportedIn hT.le W V := by
  obtain ⟨a, K, hane, hsm, hKc, hKW, hvan⟩ := exists_smooth_localized_profile hW hne
  obtain ⟨χ, hbump, hχmid⟩ := exists_smooth_time_bump hT
  have hprof : a ∈ smoothProfiles W := ⟨hsm, K, hKc, hKW, hvan⟩
  set V := productSource hT.le a hbump.continuous with hVdef
  have hgen : V ∈ smoothSourceGens hT W := ⟨a, χ, hbump.continuous, hprof, hbump, rfl⟩
  refine ⟨V, Submodule.subset_span hgen, ?_, smoothSourceGens_compactlySupported hT W hgen⟩
  have hmem : T / 2 ∈ Set.Icc (0:ℝ) T := ⟨by linarith, by linarith⟩
  exact productSource_ne_zero hT.le a hbump.continuous hane (t₀ := ⟨T / 2, hmem⟩)
    (by rw [show ((⟨T / 2, hmem⟩ : TimeI T) : ℝ) = T / 2 from rfl, hχmid]; exact one_ne_zero)

end LiWang.Formalization
