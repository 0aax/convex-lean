import ConvexStarLib.Defs

/-!
# `brunn_minkowski_1d`

Source: BrunnMinkowski.

Statement from the `convex-eval-v28-2h/brunn_minkowski_1d` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace brunn_minkowski_1d`, so the main result is `brunn_minkowski_1d.brunn_minkowski_1d`.
-/

namespace brunn_minkowski_1d

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem brunn_minkowski_1d
    (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty) :
    volume (A + B) ≥ volume A + volume B := by
  -- compact case
  have key : ∀ K L : Set ℝ, IsCompact K → IsCompact L → K.Nonempty → L.Nonempty →
      volume K + volume L ≤ volume (K + L) := by
    intro K L hK hL hKne hLne
    set a := sSup K with ha_def
    set b := sInf L with hb_def
    have haK : a ∈ K := hK.sSup_mem hKne
    have hbL : b ∈ L := hL.sInf_mem hLne
    have h1 : volume (K + {b}) = volume K := by
      rw [Set.add_singleton]
      simp
    have h2 : volume ({a} + L) = volume L := by
      rw [Set.singleton_add]
      simp
    have hsub1 : K + {b} ⊆ K + L := Set.add_subset_add_left (Set.singleton_subset_iff.mpr hbL)
    have hsub2 : {a} + L ⊆ K + L := Set.add_subset_add_right (Set.singleton_subset_iff.mpr haK)
    have hinter : (K + {b}) ∩ ({a} + L) ⊆ {a + b} := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.add_singleton] at hx1
      rw [Set.singleton_add] at hx2
      obtain ⟨k, hk, rfl⟩ := hx1
      obtain ⟨l, hl, hkl⟩ := hx2
      have hka : k ≤ a := le_csSup hK.bddAbove hk
      have hbl : b ≤ l := csInf_le hL.bddBelow hl
      simp only [Set.mem_singleton_iff]
      linarith
    have hmeas : MeasurableSet ({a} + L) := (isCompact_singleton.add hL).measurableSet
    calc volume K + volume L = volume (K + {b}) + volume ({a} + L) := by rw [h1, h2]
      _ = volume ((K + {b}) ∪ ({a} + L)) + volume ((K + {b}) ∩ ({a} + L)) :=
          (measure_union_add_inter _ hmeas).symm
      _ = volume ((K + {b}) ∪ ({a} + L)) := by
          rw [measure_mono_null hinter (measure_singleton _), add_zero]
      _ ≤ volume (K + L) := measure_mono (Set.union_subset hsub1 hsub2)
  -- general case
  obtain ⟨a₀, ha₀⟩ := hA_ne
  obtain ⟨b₀, hb₀⟩ := hB_ne
  rw [ge_iff_le]
  refine le_of_forall_lt fun c hc => ?_
  by_cases hA0 : volume A = 0
  · rw [hA0, zero_add] at hc
    calc c < volume B := hc
      _ = volume ({a₀} + B) := by rw [Set.singleton_add]; simp
      _ ≤ volume (A + B) :=
          measure_mono (Set.add_subset_add_right (Set.singleton_subset_iff.mpr ha₀))
  by_cases hB0 : volume B = 0
  · rw [hB0, add_zero] at hc
    calc c < volume A := hc
      _ = volume (A + {b₀}) := by rw [Set.add_singleton]; simp
      _ ≤ volume (A + B) :=
          measure_mono (Set.add_subset_add_left (Set.singleton_subset_iff.mpr hb₀))
  obtain ⟨y, hy, z, hz, hcyz⟩ := ENNReal.exists_lt_add_of_lt_add hc hA0 hB0
  obtain ⟨K, hKA, hK, hyK⟩ := hA.exists_lt_isCompact hy
  obtain ⟨L, hLB, hL, hzL⟩ := hB.exists_lt_isCompact hz
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hyK
  have hLne : L.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hzL
  calc c < y + z := hcyz
    _ ≤ volume K + volume L := add_le_add hyK.le hzL.le
    _ ≤ volume (K + L) := key K L hK hL hKne hLne
    _ ≤ volume (A + B) := measure_mono (Set.add_subset_add hKA hLB)

end brunn_minkowski_1d
