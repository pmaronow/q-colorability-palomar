import ThLean.W.S541S.RootKernel

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S541S
open ThresholdFoundations ThLean.BP.S5

/-- The short-root estimate, using only the indicated frozen dependency contracts. -/
theorem S5_32Statement_of_deps
    (h06 : S5_06Statement) (h09B : S5_09BStatement)
    (hRelabel : PreRelabelStatement.{0, 0}) (hE01 : S5_E01Statement) :
    ThLean.BP.S5.S5_32Statement := by
  intro q n D hq hn a t ht
  cases n with
  | zero => omega
  | succ N =>
    have hN : 2 ≤ N := by omega
    have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    have : Nonempty (Pair (Fin N)) := by
      let u : Fin N := ⟨0, by omega⟩
      let v : Fin N := ⟨1, by omega⟩
      refine ⟨⟨s(u, v), ?_⟩⟩
      intro w he
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        have := h1.trans h2.symm <;> simp [u, v, Fin.ext_iff] at this
    let e : Option (Fin N) ≃ Fin (N + 1) := (finSuccEquiv' a).symm
    have he : e none = a := finSuccEquiv'_symm_none a
    have hroot : rootProbability q D a t =
        rootProbability (V := Option (Fin N)) q D none t := by
      unfold rootProbability
      calc
        _ = poissonGraphMean t (fun G : MGraph (Option (Fin N)) =>
            indicator (rootEvent q D a (relabel e G))) :=
          (poissonGraphMean_relabel hRelabel e q t _).symm
        _ = _ := by
          congr 1
          funext G
          have hiff := rootEvent_relabel hRelabel e q D G none
          rw [he] at hiff
          exact congrArg indicator (propext hiff)
    have hsplit := rootProbability_option_le h09B hE01
      (V := Fin N) (by simpa using hN) q D hq t ht
    have htime : (((N + 1 : ℕ) : ℝ) - 2) / ((N + 1 : ℕ) : ℝ) * t =
        (((N : ℝ) - 1) / ((N : ℝ) + 1)) * t := by
      push_cast
      congr 2
      ring
    have hs : 0 ≤ ((((N : ℝ) - 1) / ((N : ℝ) + 1)) * t) := by
      have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
      exact mul_nonneg (div_nonneg (by linarith) (by positivity)) ht
    constructor
    · rw [htime]
      simpa only [hroot, Fintype.card_fin, Nat.succ_sub_one, Nat.cast_succ, nmTime]
        using hsplit
    · rw [htime]
      simpa only [Nat.succ_sub_one, Nat.cast_succ] using
        truncated_nmTime_le h06 hE01 q N D hq hN
          (z := 2 * t / ((N : ℝ) + 1)) (s := (((N : ℝ) - 1) / ((N : ℝ) + 1)) * t)
          (by positivity) hs

example (h06 : S5_06Statement) (h09B : S5_09BStatement)
    (hRelabel : PreRelabelStatement.{0, 0}) (hE01 : S5_E01Statement) :
    ThLean.BP.S5.S5_32Statement := S5_32Statement_of_deps h06 h09B hRelabel hE01

end ThLean.W.S541S
