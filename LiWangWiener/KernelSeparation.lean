/-
# Non-vacuity of the recovery theorem, and the separation it provides

`KernelRecovery.rotatedGradientSymbol_eq_of_measured` is an implication.  This module checks
that it has content and records its contrapositive in usable form.

* `exists_open_nonempty_with_exterior` — the geometric hypotheses are satisfiable: the torus
  carries a nonempty open `W` whose closure is not everything (two distinct points, Hausdorff
  separation).
* `rotatedGradientSymbol_eq_of_measured_bdd` — the same recovery theorem without an explicit
  symbol bound: the bound is extracted from `IsBddSymbol.sub`.
* `measuredMapsAgreeOn_of_symbol_eq` — the converse direction, proved: equal velocity symbols
  give agreeing measured maps at every radius.  Together with the recovery theorem this makes
  the measured map a **faithful** invariant of the velocity symbol (`measuredMapsAgreeOn_iff`).
* `measured_maps_differ_of_symbol_ne` — the contrapositive: distinct velocity symbols cannot
  have agreeing measured maps on the smooth class at any positive radius.
* `finiteKernel_vs_zero_measured_differ` — an explicit witness pair (`finiteKernel` against the
  zero kernel), so the separation statement is not vacuous.

Conditional, as everywhere, on `FractionalUCP α W`.  Nothing here weakens the caveats of
`STATUS.md` §1.3: `MeasuredMapsAgreeOn` is a hypothesis about *this packet's* mild
source-to-solution maps.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.KernelRecovery
import LiWangWiener.PhysicalTransport
import LiWangWiener.RotatedNonDegeneracy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. The geometric hypotheses are satisfiable -/

theorem half_ne_zero_circ : ((1/2 : ℝ) : Circ) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hn' : (n : ℝ) = 1/2 := by simpa using hn
  have h2 : (2 * n : ℤ) = 1 := by
    have h3 : (2 * (n:ℝ)) = 1 := by rw [hn']; ring
    exact_mod_cast h3
  omega

theorem exists_two_points_torus2 :
    (torusProj (fun _ => (1/2 : ℝ)) : Torus2) ≠ torusProj (fun _ => (0 : ℝ)) := by
  intro hc
  have h0 := congrFun hc 0
  rw [torusProj_apply, torusProj_apply] at h0
  have hz : ((0:ℝ) : Circ) = 0 := by
    simpa using (AddCircle.coe_eq_zero_iff (p := (1:ℝ)) (x := (0:ℝ))).2 ⟨0, by simp⟩
  rw [hz] at h0
  exact half_ne_zero_circ h0

/-- **The geometry is non-vacuous**: there is a nonempty open region of the torus whose
closure is not the whole torus, so both `W.Nonempty` and `((closure W)ᶜ).Nonempty` hold. -/
theorem exists_open_nonempty_with_exterior :
    ∃ W : Set Torus2, IsOpen W ∧ W.Nonempty ∧ ((closure W)ᶜ).Nonempty := by
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := t2_separation exists_two_points_torus2
  refine ⟨u, hu, ⟨torusProj (fun _ => (1/2 : ℝ)), hpu⟩,
    ⟨torusProj (fun _ => (0 : ℝ)), ?_⟩⟩
  have hsub : u ⊆ vᶜ := by
    intro x hx hxv
    exact (Set.disjoint_left.1 huv hx) hxv
  have hcl : closure u ⊆ vᶜ := closure_minimal hsub hv.isClosed_compl
  intro hmem
  exact (hcl hmem) hqv

/-! ## 1b. The portable UCP parameter is neither trivially true nor trivially false -/

/-- **`FractionalUCP` is satisfiable.**  On the whole torus it holds outright, because synthesis
is injective.  (This is the degenerate case `W = 𝕋²`, where the measured region is everything; it
is recorded only to show the parameter is not an unsatisfiable hypothesis.) -/
theorem fractionalUCP_univ (α : ℝ) : FractionalUCP α (Set.univ : Set Torus2) := by
  intro v F _ hv _
  have h0 : synth (incl v) = synth (0 : Wiener) := by
    rw [map_zero]
    exact ContinuousMap.ext (fun x => hv x (Set.mem_univ x))
  have h1 : incl v = 0 := synth_injective h0
  refine Wiener1.coeff_injective (funext fun k => ?_)
  have h2 := congrArg (fun a : Wiener => (a : Gam → ℂ) k) h1
  simpa using h2

/-- **`FractionalUCP` is not trivially true.**  It fails for the empty region, which is exactly
the degenerate case in which `smoothSources hT ∅ = ⊥` and the measurement hypothesis would carry
no information.  So a recovery theorem carrying `FractionalUCP α W` is never reading `W = ∅`. -/
theorem not_fractionalUCP_empty (α : ℝ) : ¬ FractionalUCP α (∅ : Set Torus2) := by
  intro h
  have hrel : ∀ k : Gam,
      ((((fracSymbol α (unitFreq 0) : ℝ) : ℂ) • wdirac (unitFreq 0) : Wiener)) k
        = ((fracSymbol α k : ℝ) : ℂ) * (dirac1 (unitFreq 0)).coeff k := by
    intro k
    show ((fracSymbol α (unitFreq 0) : ℝ) : ℂ) * diracFun (unitFreq 0) k
      = ((fracSymbol α k : ℝ) : ℂ) * diracFun (unitFreq 0) k
    by_cases hk : k = unitFreq 0
    · rw [hk]
    · rw [diracFun, if_neg hk]; ring
  have hz := h (dirac1 (unitFreq 0)) _ hrel
    (fun x hx => absurd hx (Set.notMem_empty x)) (fun x hx => absurd hx (Set.notMem_empty x))
  have hc : (dirac1 (unitFreq 0)).coeff (unitFreq 0) = 0 := by rw [hz]; rfl
  rw [dirac1_coeff, diracFun, if_pos rfl] at hc
  exact one_ne_zero hc

/-- **The measurement hypothesis quantifies over a nonzero family at every radius.**  For every
`ε > 0` the admissible class contains a nonzero source of norm below `ε`, so
`MeasuredMapsAgreeOn … ε` is never satisfied by default for lack of test sources. -/
theorem exists_nonzero_smoothSource_norm_lt (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hne : W.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ smoothSources hT W, V ≠ 0 ∧ ‖V‖ < ε := by
  obtain ⟨V₀, hV₀, hV₀ne, -⟩ := exists_nonzero_smoothSource hT hW hne
  have hpos : 0 < ‖V₀‖ := norm_pos_iff.2 hV₀ne
  have hδ : (0:ℝ) < ε / (2 * ‖V₀‖) := by positivity
  refine ⟨(ε / (2 * ‖V₀‖)) • V₀, Submodule.smul_mem _ _ hV₀,
    smul_ne_zero hδ.ne' hV₀ne, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hval : (ε / (2 * ‖V₀‖)) * ‖V₀‖ = ε / 2 := by field_simp
  rw [hval]
  linarith

/-! ## 2. Recovery without an explicit symbol bound -/

theorem rotatedGradientSymbol_eq_of_measured_bdd (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ := by
  obtain ⟨C, hC⟩ := hm₁.sub hm₂
  exact rotatedGradientSymbol_eq_of_measured hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs

/-! ## 3. The converse, and faithfulness -/

/-- **Equal symbols give agreeing measured maps.**  Definitional proof irrelevance makes the two
source-to-solution maps literally the same object once the symbols coincide. -/
theorem measuredMapsAgreeOn_of_symbol_eq (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (hm : m₁ = m₂)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε := by
  subst hm
  intro f _ _
  exact ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **Faithfulness.**  Under the portable UCP parameter and the geometric hypotheses, agreement
of the measured maps on the smooth source class is *equivalent* to equality of the velocity
symbols. -/
theorem measuredMapsAgreeOn_iff (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    (∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
      ↔ rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ := by
  constructor
  · intro hobs
    exact rotatedGradientSymbol_eq_of_measured_bdd hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hτ0 hτT hobs
  · intro hsym
    exact ⟨1, one_pos, measuredMapsAgreeOn_of_symbol_eq hα hT.le W hm₁ hr₁ hm₂ hr₂ hsym _ 1⟩

/-- **The contrapositive.**  Distinct velocity symbols are distinguished by the measured map on
the smooth source class, at every positive radius. -/
theorem measured_maps_differ_of_symbol_ne (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hne : rotatedGradientSymbol κ₁ ≠ rotatedGradientSymbol κ₂) :
    ¬ ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
  fun hobs => hne ((measuredMapsAgreeOn_iff hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hτ0 hτT).1 hobs)

/-! ## 4. An explicit witness pair -/

theorem zeroKernel_admissible : IsAdmissibleKernel (0 : Gam → ℂ) :=
  ⟨0, fun k => by simp⟩

theorem rotatedGradientSymbol_zero_kernel : rotatedGradientSymbol (0 : Gam → ℂ) = 0 := by
  funext j k
  fin_cases j
  · show -twoPiI * ((k 1 : ℤ) : ℂ) * (0 : ℂ) = 0
    ring
  · show twoPiI * ((k 0 : ℤ) : ℂ) * (0 : ℂ) = 0
    ring

theorem rotatedGradientSymbol_finiteKernel_ne_zero :
    rotatedGradientSymbol finiteKernel.coeff ≠ rotatedGradientSymbol (0 : Gam → ℂ) := by
  intro hc
  have h := congrFun (congrFun hc 1) (unitFreq 0)
  rw [rotatedGradientSymbol_zero_kernel] at h
  have hval : rotatedGradientSymbol finiteKernel.coeff 1 (unitFreq 0) = twoPiI := by
    rw [rotatedGradientSymbol_one_comp, finiteKernel_coeff_unitFreq,
      show ((unitFreq 0) 0 : ℤ) = 1 from unitFreq_self 0]
    norm_num
  rw [hval] at h
  exact twoPiI_ne_zero h

/-- **The separation statement is not vacuous.**  The packet's explicit `finiteKernel` and the
zero kernel are both admissible and real, their velocity symbols differ, and therefore their
measured maps on the smooth source class differ at every positive radius. -/
theorem finiteKernel_vs_zero_measured_differ (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hm₁ : IsBddSymbol (rotatedGradientSymbol finiteKernel.coeff))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol finiteKernel.coeff))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol (0 : Gam → ℂ)))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol (0 : Gam → ℂ))) :
    ¬ ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
  measured_maps_differ_of_symbol_ne hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hτ0 hτT
    rotatedGradientSymbol_finiteKernel_ne_zero

/-- Both members of the witness pair really are admissible and real. -/
theorem finiteKernel_symbol_admissible :
    IsBddSymbol (rotatedGradientSymbol finiteKernel.coeff)
      ∧ IsRealSymbol (rotatedGradientSymbol finiteKernel.coeff)
      ∧ IsBddSymbol (rotatedGradientSymbol (0 : Gam → ℂ))
      ∧ IsRealSymbol (rotatedGradientSymbol (0 : Gam → ℂ)) :=
  ⟨rotatedGradientSymbol_bdd finiteKernel_admissible,
    rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric,
    rotatedGradientSymbol_bdd zeroKernel_admissible,
    rotatedGradientSymbol_isRealSymbol ConjSymmetric.zero⟩

end LiWang.WienerModel
