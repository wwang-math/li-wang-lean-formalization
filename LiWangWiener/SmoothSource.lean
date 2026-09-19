/-
# Actual smooth compactly supported sources

Building on `SmoothPeriodic`, this module produces the objects the v4.0 development was
missing:

* `planeLift a` — the Euclidean periodic lift of a Wiener state, viewed on `ℝ × ℝ`; `SmoothWiener a`
  says that this **actual physical representative** is `C^∞`;
* the inverse construction `wienerOfSmooth` is shown to be additive and real-homogeneous, to
  preserve realness (conjugate symmetry), and to be inverse to `planeLift`;
* a genuine **smooth circle bump**: for any integer-translation-invariant open `V ⊆ ℝ` and any
  `c ∈ V`, a `C^∞` `1`-periodic real function which is nonzero at `c` and vanishes off `V`.
  The radius is produced by a compactness argument, not assumed;
* consequently, for any nonempty open `W ⊆ 𝕋²`, a **nonzero real smooth profile in the Wiener
  algebra whose physical field is supported in a compact subset of `W`** — the existence input
  that v4.0 had to isolate as the hypothesis `HasLocalizedProfile`;
* `smoothProfiles W`, the real vector space of such profiles.

Part of `LiWangWienerSmoothObservationPacket` v5.0.
-/
import LiWangWiener.SmoothPeriodic
import LiWangWiener.RealSynthesis
import LiWangWiener.SolutionReality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.WienerModel

/-! ## 1. The Euclidean lift of a Wiener state, on `ℝ × ℝ` -/

/-- The periodic lift of a Wiener state, read as a function of two real variables. -/
noncomputable def planeLift (a : Wiener) : ℝ × ℝ → ℂ := fun p => lift a ![p.1, p.2]

theorem planeLift_apply (a : Wiener) (p : ℝ × ℝ) : planeLift a p = lift a ![p.1, p.2] := rfl

theorem torusProj_surjective : Function.Surjective (torusProj : (Fin 2 → ℝ) → Torus2) := by
  intro x
  refine ⟨fun j => ((AddCircle.equivIoc (1:ℝ) 0 (x j) : ℝ)), ?_⟩
  funext j
  exact (AddCircle.equivIoc (1:ℝ) 0).symm_apply_apply (x j)

theorem lift_injective : Function.Injective (lift : Wiener → (Fin 2 → ℝ) → ℂ) := by
  intro a b hab
  refine synth_injective ?_
  ext x
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  exact congrFun hab y

theorem planeLift_injective : Function.Injective planeLift := by
  intro a b hab
  refine lift_injective ?_
  funext y
  have h := congrFun hab (y 0, y 1)
  have e : (![(y 0), (y 1)] : Fin 2 → ℝ) = y := by
    funext j; fin_cases j <;> rfl
  rw [planeLift_apply, planeLift_apply, e] at h
  exact h

@[simp] theorem planeLift_add (a b : Wiener) : planeLift (a + b) = planeLift a + planeLift b := by
  funext p
  show lift (a + b) _ = lift a _ + lift b _
  rw [lift_def, lift_def, lift_def, map_add]
  rfl

@[simp] theorem planeLift_smul (r : ℝ) (a : Wiener) :
    planeLift ((r : ℂ) • a) = (r : ℂ) • planeLift a := by
  funext p
  show lift ((r : ℂ) • a) _ = (r : ℂ) * lift a _
  rw [lift_def, lift_def, map_smul]
  rfl

@[simp] theorem planeLift_zero : planeLift (0 : Wiener) = 0 := by
  funext p
  show lift (0 : Wiener) _ = 0
  rw [lift_def, map_zero]
  rfl

/-- `a` has a **smooth physical representative**: its Euclidean periodic lift is `C^∞`. -/
def SmoothWiener (a : Wiener) : Prop := ContDiff ℝ ∞ (planeLift a)

theorem isSmoothPeriodic_planeLift {a : Wiener} (h : SmoothWiener a) :
    IsSmoothPeriodic (planeLift a) := by
  refine ⟨h, ?_, ?_⟩
  · intro p
    show lift a ![p.1 + 1, p.2] = lift a ![p.1, p.2]
    have e : (![p.1 + 1, p.2] : Fin 2 → ℝ)
        = fun j => (![p.1, p.2] : Fin 2 → ℝ) j + ((((![1, 0] : Gam) j : ℤ)) : ℝ) := by
      funext j; fin_cases j <;> norm_num
    rw [e, lift_periodic]
  · intro p
    show lift a ![p.1, p.2 + 1] = lift a ![p.1, p.2]
    have e : (![p.1, p.2 + 1] : Fin 2 → ℝ)
        = fun j => (![p.1, p.2] : Fin 2 → ℝ) j + ((((![0, 1] : Gam) j : ℤ)) : ℝ) := by
      funext j; fin_cases j <;> norm_num
    rw [e, lift_periodic]

theorem planeLift_wienerOfSmooth {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    planeLift (wienerOfSmooth G h) = G := by
  funext p
  rw [planeLift_apply, lift_wienerOfSmooth h]
  rfl

theorem smoothWiener_wienerOfSmooth {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    SmoothWiener (wienerOfSmooth G h) := by
  rw [SmoothWiener, planeLift_wienerOfSmooth h]
  exact h.smooth

/-- The Fourier coefficient map on smooth doubly periodic functions is **additive**. -/
theorem wienerOfSmooth_add {G H : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G) (hH : IsSmoothPeriodic H)
    (hGH : IsSmoothPeriodic (G + H)) :
    wienerOfSmooth (G + H) hGH = wienerOfSmooth G hG + wienerOfSmooth H hH := by
  refine planeLift_injective ?_
  rw [planeLift_add, planeLift_wienerOfSmooth, planeLift_wienerOfSmooth,
    planeLift_wienerOfSmooth]

/-- ... and **real homogeneous**. -/
theorem wienerOfSmooth_smul {G : ℝ × ℝ → ℂ} (r : ℝ) (hG : IsSmoothPeriodic G)
    (hrG : IsSmoothPeriodic ((r : ℂ) • G)) :
    wienerOfSmooth ((r : ℂ) • G) hrG = (r : ℂ) • wienerOfSmooth G hG := by
  refine planeLift_injective ?_
  rw [planeLift_smul, planeLift_wienerOfSmooth, planeLift_wienerOfSmooth]

theorem wienerOfSmooth_eq_zero_iff {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G) :
    wienerOfSmooth G hG = 0 ↔ ∀ p, G p = 0 := by
  constructor
  · intro h p
    have := planeLift_wienerOfSmooth hG
    rw [h, planeLift_zero] at this
    exact congrFun this.symm p
  · intro h
    refine planeLift_injective ?_
    rw [planeLift_wienerOfSmooth, planeLift_zero]
    funext p; exact h p

/-! ## 2. Realness -/

theorem conj_chi (n : ℤ) (y : ℝ) : conj (chi n y) = chi (-n) y := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  simp only [twoPiI, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
    map_intCast]
  push_cast
  ring

theorem percoeff_conj (ψ : ℝ → ℂ) (n : ℤ) :
    percoeff (fun y => conj (ψ y)) (-n) = conj (percoeff ψ n) := by
  rw [percoeff, percoeff, ← intervalIntegral_conj]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  rw [map_mul, conj_chi]

theorem conjSymmetric_pcoeff {G : ℝ × ℝ → ℂ} (hre : ∀ p, conj (G p) = G p) :
    ConjSymmetric (pcoeff G) := by
  intro k
  have hinner : ∀ y0 : ℝ, percoeff (fun y1 => G (y0, y1)) ((-k) 1)
      = conj (percoeff (fun y1 => G (y0, y1)) (k 1)) := by
    intro y0
    have h1 : ((-k) 1) = -(k 1) := rfl
    rw [h1, ← percoeff_conj]
    exact percoeff_congr (fun y1 => (hre (y0, y1)).symm) _
  have h0 : ((-k) 0) = -(k 0) := rfl
  rw [pcoeff, pcoeff, h0, percoeff_congr hinner, percoeff_conj]

/-- The real Wiener element of a real-valued smooth doubly periodic function. -/
noncomputable def realWienerOfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) : RealWiener :=
  RealWiener.mk (wienerOfSmooth G h) (conjSymmetric_pcoeff hre)

@[simp] theorem val_realWienerOfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) :
    (realWienerOfSmooth G h hre).val = wienerOfSmooth G h := rfl

/-! ## 3. A genuine smooth circle bump -/

theorem contDiff_chi (n : ℤ) : ContDiff ℝ ∞ (chi n) := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => twoPiI * (n : ℂ) * (t : ℂ)) := contDiff_const.mul h1
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp h2

theorem chi_periodic (n : ℤ) (t : ℝ) : chi n (t + 1) = chi n t := by
  rw [chi, chi]
  have e : twoPiI * (n : ℂ) * ((t + 1 : ℝ) : ℂ)
      = twoPiI * (n : ℂ) * (t : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [twoPiI]; push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem chi_int_shift (n : ℤ) (t : ℝ) (m : ℤ) : chi n (t + (m : ℝ)) = chi n t :=
  periodic_int_add (chi_periodic n) t m

theorem chi_one_eq_iff {s t : ℝ} : chi 1 s = chi 1 t ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  rw [chi, chi, Complex.exp_eq_exp_iff_exists_int]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have h1 : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hc : (2 * (Real.pi : ℂ) * Complex.I) * ((s : ℂ) - (t : ℂ) - (n : ℂ)) = 0 := by
      simp only [twoPiI] at hn
      linear_combination hn
    have h0 : (s : ℂ) - (t : ℂ) - (n : ℂ) = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · exact absurd h hne
      · exact h
    have hcast : ((s : ℝ) : ℂ) = (((t + (n : ℝ)) : ℝ) : ℂ) := by push_cast; linear_combination h0
    exact_mod_cast hcast
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp only [twoPiI]; push_cast; ring⟩

theorem exists_box_shift (c t : ℝ) : ∃ n : ℤ, t - (n : ℝ) ∈ Set.Icc (c - 1/2) (c + 1/2) := by
  refine ⟨⌊t - c + 1/2⌋, ?_, ?_⟩
  · have h := Int.floor_le (t - c + 1/2); linarith
  · have h := Int.lt_floor_add_one (t - c + 1/2); linarith

/-- **The separation radius.**  For an open set `V ⊆ ℝ` invariant under integer translations and
containing `c`, there is `δ > 0` with: the `e^{2πi·}`-image of any `t` within `δ` of that of `c`
forces `t ∈ V`.  The radius is produced by a compactness argument on one period. -/
theorem exists_circle_radius {V : Set ℝ} (hV : IsOpen V)
    (hinv : ∀ (t : ℝ) (n : ℤ), (t + (n : ℝ)) ∈ V ↔ t ∈ V) {c : ℝ} (hc : c ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, dist (chi 1 t) (chi 1 c) ≤ δ → t ∈ V := by
  have hshift : ∀ t : ℝ, ∀ n : ℤ, chi 1 (t - (n : ℝ)) = chi 1 t := by
    intro t n
    have e : t - (n : ℝ) = t + (((-n : ℤ)) : ℝ) := by push_cast; ring
    rw [e, chi_int_shift]
  have hback : ∀ (t : ℝ) (n : ℤ), t - (n : ℝ) ∈ V → t ∈ V := by
    intro t n ht
    have h := (hinv (t - (n : ℝ)) n).2 ht
    rwa [sub_add_cancel] at h
  set K : Set ℝ := Set.Icc (c - 1/2) (c + 1/2) \ V with hKdef
  have hKc : IsCompact K := isCompact_Icc.diff hV
  by_cases hKe : K.Nonempty
  · obtain ⟨s₀, hs₀K, hmin⟩ := hKc.exists_isMinOn hKe
      (Continuous.continuousOn ((continuous_chi 1).dist continuous_const))
    have hpos : 0 < dist (chi 1 s₀) (chi 1 c) := by
      rcases eq_or_lt_of_le (dist_nonneg (x := chi 1 s₀) (y := chi 1 c)) with h | h
      · exfalso
        have heq : chi 1 s₀ = chi 1 c := by rwa [eq_comm, dist_eq_zero] at h
        obtain ⟨n, hn⟩ := chi_one_eq_iff.1 heq
        exact hs₀K.2 (by rw [hn]; exact (hinv c n).2 hc)
      · exact h
    refine ⟨dist (chi 1 s₀) (chi 1 c) / 2, by linarith, fun t ht => ?_⟩
    obtain ⟨n, hn⟩ := exists_box_shift c t
    refine hback t n ?_
    by_contra hcon
    have hmem : t - (n : ℝ) ∈ K := ⟨hn, hcon⟩
    have hle := isMinOn_iff.1 hmin _ hmem
    rw [hshift t n] at hle
    linarith
  · refine ⟨1, one_pos, fun t _ => ?_⟩
    obtain ⟨n, hn⟩ := exists_box_shift c t
    refine hback t n ?_
    by_contra hcon
    exact hKe ⟨t - (n : ℝ), hn, hcon⟩

/-- The smooth circle bump attached to a separation radius. -/
noncomputable def circBump (δ : ℝ) (hδ : 0 < δ) (c : ℝ) : ContDiffBump (chi 1 c) :=
  ⟨δ / 2, δ, by linarith, by linarith⟩

/-- Its `1`-periodic `C^∞` real profile on the line. -/
noncomputable def circProfile (δ : ℝ) (hδ : 0 < δ) (c : ℝ) : ℝ → ℝ :=
  fun t => circBump δ hδ c (chi 1 t)

theorem contDiff_circProfile (δ : ℝ) (hδ : 0 < δ) (c : ℝ) :
    ContDiff ℝ ∞ (circProfile δ hδ c) :=
  (circBump δ hδ c).contDiff.comp (contDiff_chi 1)

theorem circProfile_periodic (δ : ℝ) (hδ : 0 < δ) (c t : ℝ) :
    circProfile δ hδ c (t + 1) = circProfile δ hδ c t := by
  rw [circProfile, circProfile, chi_periodic]

theorem circProfile_center (δ : ℝ) (hδ : 0 < δ) (c : ℝ) : circProfile δ hδ c c = 1 :=
  (circBump δ hδ c).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_self]
    exact le_of_lt (circBump δ hδ c).rIn_pos)

theorem circProfile_nonneg (δ : ℝ) (hδ : 0 < δ) (c t : ℝ) : 0 ≤ circProfile δ hδ c t :=
  (circBump δ hδ c).nonneg

theorem circProfile_ne_zero_dist {δ : ℝ} (hδ : 0 < δ) {c t : ℝ}
    (ht : circProfile δ hδ c t ≠ 0) : dist (chi 1 t) (chi 1 c) ≤ δ := by
  by_contra hcon
  exact ht ((circBump δ hδ c).zero_of_le_dist (le_of_lt (not_le.1 hcon)))


/-! ## 4. A nonzero smooth profile localized in any nonempty open region -/

/-- The product of two circle bumps: a `C^∞`, `ℤ²`-periodic, real-valued function of the
plane, localized near `(c₀, c₁)` modulo `ℤ²`. -/
noncomputable def bumpProfile (δ0 δ1 : ℝ) (h0 : 0 < δ0) (h1 : 0 < δ1) (c0 c1 : ℝ) :
    ℝ × ℝ → ℂ :=
  fun p => ((circProfile δ0 h0 c0 p.1 : ℝ) : ℂ) * ((circProfile δ1 h1 c1 p.2 : ℝ) : ℂ)

theorem isSmoothPeriodic_bumpProfile (δ0 δ1 : ℝ) (h0 : 0 < δ0) (h1 : 0 < δ1) (c0 c1 : ℝ) :
    IsSmoothPeriodic (bumpProfile δ0 δ1 h0 h1 c0 c1) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ContDiff.mul ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp ((contDiff_circProfile δ0 h0 c0).comp contDiff_fst)
    · exact Complex.ofRealCLM.contDiff.comp ((contDiff_circProfile δ1 h1 c1).comp contDiff_snd)
  · intro p; rw [bumpProfile, bumpProfile, circProfile_periodic]
  · intro p; rw [bumpProfile, bumpProfile, circProfile_periodic]

theorem bumpProfile_real (δ0 δ1 : ℝ) (h0 : 0 < δ0) (h1 : 0 < δ1) (c0 c1 : ℝ) (p : ℝ × ℝ) :
    conj (bumpProfile δ0 δ1 h0 h1 c0 c1 p) = bumpProfile δ0 δ1 h0 h1 c0 c1 p := by
  rw [bumpProfile, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

theorem bumpProfile_nonneg (δ0 δ1 : ℝ) (h0 : 0 < δ0) (h1 : 0 < δ1) (c0 c1 : ℝ) (p : ℝ × ℝ) :
    (bumpProfile δ0 δ1 h0 h1 c0 c1 p).im = 0
      ∧ 0 ≤ (bumpProfile δ0 δ1 h0 h1 c0 c1 p).re := by
  have he : bumpProfile δ0 δ1 h0 h1 c0 c1 p
      = ((circProfile δ0 h0 c0 p.1 * circProfile δ1 h1 c1 p.2 : ℝ) : ℂ) := by
    rw [bumpProfile, Complex.ofReal_mul]
  rw [he]
  exact ⟨Complex.ofReal_im _, by
    rw [Complex.ofReal_re]
    exact mul_nonneg (circProfile_nonneg δ0 h0 c0 p.1) (circProfile_nonneg δ1 h1 c1 p.2)⟩

theorem bumpProfile_center (δ0 δ1 : ℝ) (h0 : 0 < δ0) (h1 : 0 < δ1) (c0 c1 : ℝ) :
    bumpProfile δ0 δ1 h0 h1 c0 c1 (c0, c1) = 1 := by
  rw [bumpProfile, circProfile_center, circProfile_center]
  norm_num

theorem bumpProfile_dist_of_ne_zero {δ0 δ1 : ℝ} (h0 : 0 < δ0) (h1 : 0 < δ1) {c0 c1 : ℝ}
    {p : ℝ × ℝ} (hp : bumpProfile δ0 δ1 h0 h1 c0 c1 p ≠ 0) :
    dist (chi 1 p.1) (chi 1 c0) ≤ δ0 ∧ dist (chi 1 p.2) (chi 1 c1) ≤ δ1 := by
  rw [bumpProfile] at hp
  have h := mul_ne_zero_iff.1 hp
  refine ⟨circProfile_ne_zero_dist h0 ?_, circProfile_ne_zero_dist h1 ?_⟩
  · exact fun hz => h.1 (by rw [hz]; norm_num)
  · exact fun hz => h.2 (by rw [hz]; norm_num)

theorem continuous_circCoe : Continuous (fun s : ℝ => ((s : ℝ) : Circ)) :=
  AddCircle.continuous_mk' (1:ℝ)

theorem vecPair_eq (y : Fin 2 → ℝ) : (![(y 0), (y 1)] : Fin 2 → ℝ) = y := by
  funext j; fin_cases j <;> rfl

/-- **The missing existence input of v4.0, now proved.**  For every nonempty open `W ⊆ 𝕋²`
there is a *nonzero* real element of the Wiener algebra whose physical field is `C^∞` and
vanishes outside a compact subset of `W`. -/
theorem exists_smooth_bump_at {W : Set Torus2} (hW : IsOpen W) {w : Torus2} (hw : w ∈ W) :
    ∃ (a : RealWiener) (K : Set Torus2),
      SmoothWiener a.val ∧ IsCompact K ∧ K ⊆ W ∧ (∀ x ∉ K, synth a.val x = 0) ∧
      (∀ x : Torus2, (synth a.val x).im = 0 ∧ 0 ≤ (synth a.val x).re) ∧
      synth a.val w = 1 := by
  obtain ⟨c, rfl⟩ := torusProj_surjective w
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hW (torusProj c) hw
  set u' : Fin 2 → Set Circ := fun j => if j ∈ I then u j else Set.univ with hu'def
  have hu'open : ∀ j, IsOpen (u' j) := by
    intro j
    by_cases hj : j ∈ I
    · rw [hu'def]; simp only [if_pos hj]; exact (hu j hj).1
    · rw [hu'def]; simp only [if_neg hj]; exact isOpen_univ
  have hu'mem : ∀ j, torusProj c j ∈ u' j := by
    intro j
    by_cases hj : j ∈ I
    · rw [hu'def]; simp only [if_pos hj]; exact (hu j hj).2
    · rw [hu'def]; simp only [if_neg hj]; trivial
  have hu'sub : Set.univ.pi u' ⊆ W := by
    intro x hx
    refine hsub (fun a ha => ?_)
    have hxa := hx a (Set.mem_univ a)
    rw [hu'def] at hxa
    simp only [if_pos (Finset.mem_coe.1 ha)] at hxa
    exact hxa
  set V : Fin 2 → Set ℝ := fun j => (fun s : ℝ => ((s : ℝ) : Circ)) ⁻¹' (u' j) with hVdef
  have hVopen : ∀ j, IsOpen (V j) := fun j => (hu'open j).preimage continuous_circCoe
  have hVmem : ∀ j, c j ∈ V j := fun j => hu'mem j
  have hVinv : ∀ (j : Fin 2) (t : ℝ) (n : ℤ), (t + (n : ℝ)) ∈ V j ↔ t ∈ V j := by
    intro j t n
    show ((t + (n : ℝ) : ℝ) : Circ) ∈ u' j ↔ ((t : ℝ) : Circ) ∈ u' j
    rw [coe_add_intCast]
  have hrad : ∀ j : Fin 2, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, dist (chi 1 t) (chi 1 (c j)) ≤ δ → t ∈ V j :=
    fun j => exists_circle_radius (hVopen j) (hVinv j) (hVmem j)
  choose δ hδpos hδV using hrad
  set G := bumpProfile (δ 0) (δ 1) (hδpos 0) (hδpos 1) (c 0) (c 1) with hGdef
  have hGsm : IsSmoothPeriodic G := isSmoothPeriodic_bumpProfile _ _ _ _ _ _
  have hGre : ∀ p, conj (G p) = G p := bumpProfile_real _ _ _ _ _ _
  set a : RealWiener := realWienerOfSmooth G hGsm hGre with hadef
  set S : Fin 2 → Set ℝ := fun j =>
    {t : ℝ | dist (chi 1 t) (chi 1 (c j)) ≤ δ j} ∩ Set.Icc (c j - 1/2) (c j + 1/2) with hSdef
  have hScompact : ∀ j, IsCompact (S j) := fun j =>
    IsCompact.inter_left isCompact_Icc
      (isClosed_le ((continuous_chi 1).dist continuous_const) continuous_const)
  set K : Set Torus2 := torusProj '' (Set.univ.pi S) with hKdef
  have hLift : ∀ y : Fin 2 → ℝ, synth a.val (torusProj y) = G (y 0, y 1) := by
    intro y
    have e := congrFun (planeLift_wienerOfSmooth hGsm) (y 0, y 1)
    rw [planeLift_apply, vecPair_eq] at e
    exact e
  refine ⟨a, K, ?_, ((isCompact_univ_pi hScompact).image torusProj.continuous), ?_, ?_, ?_, ?_⟩
  · show SmoothWiener (wienerOfSmooth G hGsm)
    exact smoothWiener_wienerOfSmooth hGsm
  · rintro _ ⟨y, hy, rfl⟩
    refine hu'sub (fun j _ => ?_)
    exact hδV j (y j) (hy j (Set.mem_univ j)).1
  · intro x hx
    by_contra hne0
    apply hx
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    have hGy : G (y 0, y 1) ≠ 0 := by rw [← hLift y]; exact hne0
    have hdist := bumpProfile_dist_of_ne_zero (hδpos 0) (hδpos 1) (by rw [← hGdef]; exact hGy)
    choose n hn using fun j : Fin 2 => exists_box_shift (c j) (y j)
    refine ⟨fun j => y j - (n j : ℝ), fun j _ => ⟨?_, hn j⟩, ?_⟩
    · have hshift : chi 1 (y j - (n j : ℝ)) = chi 1 (y j) := by
        have e : y j - (n j : ℝ) = y j + (((-(n j) : ℤ)) : ℝ) := by push_cast; ring
        rw [e, chi_int_shift]
      show dist (chi 1 (y j - (n j : ℝ))) (chi 1 (c j)) ≤ δ j
      rw [hshift]
      fin_cases j
      · exact hdist.1
      · exact hdist.2
    · funext j
      show ((y j - (n j : ℝ) : ℝ) : Circ) = ((y j : ℝ) : Circ)
      have e : y j - (n j : ℝ) = y j + (((-(n j) : ℤ)) : ℝ) := by push_cast; ring
      rw [e, coe_add_intCast]
  · intro x
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    rw [hLift y, hGdef]
    exact bumpProfile_nonneg _ _ _ _ _ _ _
  · rw [hLift c, hGdef, bumpProfile_center]

/-- The v5.0 form: a *nonzero* smooth profile supported in a compact subset of `W`. -/
theorem exists_smooth_localized_profile {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (a : RealWiener) (K : Set Torus2),
      a ≠ 0 ∧ SmoothWiener a.val ∧ IsCompact K ∧ K ⊆ W ∧ ∀ x ∉ K, synth a.val x = 0 := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨a, K, hsm, hKc, hKW, hvan, -, hone⟩ := exists_smooth_bump_at hW hw
  refine ⟨a, K, ?_, hsm, hKc, hKW, hvan⟩
  intro hz
  rw [hz, show (0 : RealWiener).val = (0 : Wiener) from rfl, map_zero] at hone
  exact one_ne_zero hone.symm


/-! ## 5. The real vector space of smooth compactly supported profiles -/

theorem smoothWiener_add {a b : Wiener} (ha : SmoothWiener a) (hb : SmoothWiener b) :
    SmoothWiener (a + b) := by
  rw [SmoothWiener, planeLift_add]
  exact ha.add hb

theorem smoothWiener_smul (r : ℝ) {a : Wiener} (ha : SmoothWiener a) :
    SmoothWiener ((r : ℂ) • a) := by
  rw [SmoothWiener, planeLift_smul]
  exact ha.const_smul ((r : ℂ))

theorem smoothWiener_zero : SmoothWiener (0 : Wiener) := by
  rw [SmoothWiener, planeLift_zero]
  exact contDiff_const

/-- **The real vector space of smooth profiles compactly supported inside `W`.** -/
noncomputable def smoothProfiles (W : Set Torus2) : Submodule ℝ RealWiener where
  carrier := {a | SmoothWiener a.val ∧
    ∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧ ∀ x ∉ K, synth a.val x = 0}
  add_mem' := by
    rintro a b ⟨hsa, Ka, hKa, hKaW, hva⟩ ⟨hsb, Kb, hKb, hKbW, hvb⟩
    refine ⟨?_, Ka ∪ Kb, hKa.union hKb, Set.union_subset hKaW hKbW, ?_⟩
    · rw [RealWiener.val_add]; exact smoothWiener_add hsa hsb
    · intro x hx
      rw [RealWiener.val_add, map_add]
      show synth a.val x + synth b.val x = 0
      rw [hva x (fun h => hx (Or.inl h)), hvb x (fun h => hx (Or.inr h)), add_zero]
  zero_mem' := by
    refine ⟨?_, ∅, isCompact_empty, Set.empty_subset _, ?_⟩
    · rw [RealWiener.val_zero]; exact smoothWiener_zero
    · intro x _
      rw [RealWiener.val_zero, map_zero]
      rfl
  smul_mem' := by
    rintro r a ⟨hsa, Ka, hKa, hKaW, hva⟩
    refine ⟨?_, Ka, hKa, hKaW, ?_⟩
    · rw [RealWiener.val_smul, smul_real_wiener]; exact smoothWiener_smul r hsa
    · intro x hx
      rw [RealWiener.val_smul, smul_real_wiener, map_smul]
      show (r : ℂ) * synth a.val x = 0
      rw [hva x hx, mul_zero]

@[simp] theorem mem_smoothProfiles (W : Set Torus2) (a : RealWiener) :
    a ∈ smoothProfiles W ↔ SmoothWiener a.val ∧
      ∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧ ∀ x ∉ K, synth a.val x = 0 := Iff.rfl

/-- Every smooth profile in `smoothProfiles W` has physical field vanishing outside `W`. -/
theorem smoothProfiles_vanishes {W : Set Torus2} {a : RealWiener} (ha : a ∈ smoothProfiles W)
    {x : Torus2} (hx : x ∉ W) : synth a.val x = 0 := by
  obtain ⟨-, K, -, hKW, hv⟩ := ha
  exact hv x (fun h => hx (hKW h))

/-- **Non-vacuity**: for a nonempty open `W`, the space `smoothProfiles W` is nontrivial. -/
theorem exists_nonzero_smoothProfile {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a ∈ smoothProfiles W, a ≠ 0 := by
  obtain ⟨a, K, hane, hsm, hKc, hKW, hvan⟩ := exists_smooth_localized_profile hW hne
  exact ⟨a, ⟨hsm, K, hKc, hKW, hvan⟩, hane⟩

/-! ## 6. A genuine `C^∞` compactly supported time profile -/

/-- A `C^∞` time profile whose support is a compact subinterval of `(0,T)`. -/
structure IsSmoothTimeBump (T : ℝ) (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  supp : ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < T ∧ ∀ t ∉ Set.Icc t₀ t₁, χ t = 0

theorem IsSmoothTimeBump.continuous {T : ℝ} {χ : ℝ → ℝ} (h : IsSmoothTimeBump T χ) :
    Continuous χ := h.smooth.continuous

/-- The explicit smooth time bump supported in `[T/4, 3T/4] ⊂ (0,T)` and equal to `1` at
`T/2`.  Unlike `timeProfile`, this one is genuinely `C^∞`. -/
noncomputable def smoothTimeBump (T : ℝ) (hT : 0 < T) : ContDiffBump (T / 2 : ℝ) :=
  ⟨T / 8, T / 4, by linarith, by linarith⟩

theorem exists_smooth_time_bump {T : ℝ} (hT : 0 < T) :
    ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ χ (T / 2) = 1 := by
  refine ⟨smoothTimeBump T hT, ⟨(smoothTimeBump T hT).contDiff, ⟨T / 4, 3 * T / 4,
    by linarith, by linarith, by linarith, fun t ht => ?_⟩⟩, ?_⟩
  · refine (smoothTimeBump T hT).zero_of_le_dist ?_
    show (smoothTimeBump T hT).rOut ≤ dist t (T / 2)
    show T / 4 ≤ |t - T / 2|
    rcases not_and_or.1 (fun h : T / 4 ≤ t ∧ t ≤ 3 * T / 4 => ht ⟨h.1, h.2⟩) with h | h
    · rw [abs_of_nonpos (by have := not_le.1 h; linarith)]
      have := not_le.1 h; linarith
    · rw [abs_of_nonneg (by have := not_le.1 h; linarith)]
      have := not_le.1 h; linarith
  · refine (smoothTimeBump T hT).one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_self]
    exact le_of_lt (smoothTimeBump T hT).rIn_pos


end LiWang.WienerModel
