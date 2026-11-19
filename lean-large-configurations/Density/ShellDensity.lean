module

public import Density.SliceDensity
public import Density.Annular
public import Density.PowerBand

/-! # Density of the annular witnesses in §2 -/

public section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Density.Annular

/-- Every single signed shell has actual centered-cube density 1−ε. -/
theorem hasDensity_shell {d p : ℕ} {ε : ℝ} (hd : 1 ≤ d) (hp : 1 ≤ p)
    (s : Fin d → Bool) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    HasDensity (shell p (fun i => directionSign (s i)) ε) (1-ε) := by
  cases d with
  | zero => omega
  | succ d =>
    apply hasDensity_of_uniform_slices (C := 16) (isOpen_shell ..).measurableSet
      (by linarith) (by norm_num)
    intro R hR y
    let c := ∑ i : Fin d, directionSign (s i.succ) * y i ^ p
    have he (t : ℝ) : Fin.cons t y ∈ shell p (fun i => directionSign (s i)) ε ↔
        directionSign (s 0) * t ^ p + c ∈ Band ε := by
      simp [shell, phase, c, Fin.sum_univ_succ]
    simpa only [he] using
      Density.PowerSlices.centered_band_estimate hp hε₀ hε₁ hR.le c (s 0)

private theorem cubeRatio_union_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (E : ι → Set (Point d)) (hE : ∀ i, MeasurableSet (E i)) {R : ℝ} (hR : 0 < R) :
    1 - ∑ i, (1 - cubeRatio (E i) R) ≤ cubeRatio (⋂ i, E i) R := by
  classical
  let B := centeredCube d R
  have hfin : volume B ≠ ⊤ := by dsimp [B]; rw [volume_centeredCube]; finiteness
  have hB : volume.real B = R^d := by
    rw [measureReal_def, volume_centeredCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
  have hdiff (S : Set (Point d)) (hS : MeasurableSet S) :
      volume.real (B \ S) = R^d - volume.real (S ∩ B) := by
    have h := measureReal_sdiff_add_inter (μ := volume) hS hfin
    rw [hB, inter_comm B S] at h
    linarith
  have h := measureReal_iUnion_fintype_le (μ := volume) (fun i => B \ E i)
  rw [← sdiff_iInter, hdiff _ (.iInter hE)] at h
  simp_rw [hdiff _ (hE _)] at h
  have hd := pow_pos hR d
  have hpoint (i) : 1 - cubeRatio (E i) R = (R^d - volume.real (E i ∩ B)) / R^d := by
    change 1 - volume.real _ / R^d = _
    rw [sub_div, div_self hd.ne']
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  change 1 - _ / R^d ≤ volume.real _ / R^d
  calc
    _ = (R^d - ∑ i, (R^d - volume.real (E i ∩ B))) / R^d := by
      rw [sub_div, div_self hd.ne']
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_comm.mp h) hd.le

private theorem cubeRatio_le_one {d : ℕ} (E : Set (Point d)) {R : ℝ} (hR : 0 < R) :
    cubeRatio E R ≤ 1 := by
  have hfin : volume (centeredCube d R) ≠ ⊤ := by rw [volume_centeredCube]; finiteness
  have h := measureReal_mono (μ := volume) (Set.inter_subset_right (s := E)) hfin
  simp only [measureReal_def, volume_centeredCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le] at h
  exact (div_le_one (pow_pos hR _)).mpr h

/-- Taking complements and summing their measures over the 2ᵈ sign vectors
gives the asserted lower density, with explicit dimension dependence. -/
theorem oddShell_lowerDensity {d p : ℕ} {ε : ℝ} (hd : 1 ≤ d) (hp : 1 ≤ p)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    1 - (2:ℝ)^d*ε ≤ lowerDensity (oddShell (d:=d) p ε) := by
  classical
  let S (s : Fin d → Bool) := shell p (fun i => directionSign (s i)) ε
  let F (R : ℝ) := 1 - ∑ s : Fin d → Bool, (1 - cubeRatio (S s) R)
  have hlim : Tendsto F atTop (𝓝 (1-(2:ℝ)^d*ε)) := by
    have ht (s : Fin d → Bool) : Tendsto (fun R => 1 - cubeRatio (S s) R) atTop (𝓝 (1-(1-ε))) :=
      tendsto_const_nhds.sub (hasDensity_shell hd hp s hε₀ hε₁)
    have hh := tendsto_const_nhds (x := (1:ℝ)) |>.sub
      (tendsto_finsetSum Finset.univ (fun s _ => ht s))
    simpa [F, Fintype.card_fun, nsmul_eq_mul] using hh
  have hle : ∀ᶠ R : ℝ in atTop, F R ≤ cubeRatio (oddShell (d:=d) p ε) R := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact cubeRatio_union_bound S (fun s => (isOpen_shell ..).measurableSet) hR
  rw [← hlim.liminf_eq]
  refine Filter.liminf_le_liminf hle hlim.isBoundedUnder_ge ?_
  have hub : atTop.IsBoundedUnder (· ≤ ·) (cubeRatio (oddShell (d:=d) p ε)) :=
    ⟨1, (eventually_gt_atTop (0:ℝ)).mono fun _ hR => cubeRatio_le_one _ hR⟩
  exact hub.isCobounded_flip

end Density.Annular
