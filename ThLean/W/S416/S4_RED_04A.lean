import ThLean.BP.S4.Deletion

/-!
The finite-average helpers `uniformMean_mul_left`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S416
open ThresholdFoundations
open ThLean.BP.S4

private theorem deletedPrefix_eq_tupleGraph_omitBlock
    {E : Type} [Fintype E] {T m : ℕ} (x : Fin T → Pair E)
    (i : Fin T) (hi : i.val < m) (hm : m ≤ T) :
    deletedPrefix x i m = tupleGraph (omitBlock x i m hi hm) := by
  classical
  ext e
  simp only [deletedPrefix, tupleGraph]
  let f : Fin (m - 1) → Fin T := fun j =>
    ⟨if j.val < i.val then j.val else j.val + 1, by
      by_cases hji : j.val < i.val
      · simp [hji, lt_trans hji hi |>.trans_le hm]
      · have hlt : j.val + 1 < m := by omega
        simp [hji, hlt.trans_le hm]⟩
  symm
  apply Finset.card_bij (s := Finset.univ.filter (fun j : Fin (m - 1) => (omitBlock x i m hi hm j).val = e))
    (t := Finset.univ.filter (fun j : Fin T => j.val < m ∧ j ≠ i ∧ (x j).val = e))
    (fun j _ => f j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_, ?_⟩
    · change (if j.val < i.val then j.val else j.val + 1) < m
      split_ifs with hji
      · exact lt_trans hji hi
      · omega
    · intro hji
      have hv := congrArg Fin.val hji
      by_cases hlt : j.val < i.val
      · simp [f, hlt] at hv
        omega
      · simp [f, hlt] at hv
        omega
    · simpa [f, omitBlock] using hj
  · intro a ha b hb hab
    apply Fin.ext
    have hval := congrArg Fin.val hab
    simp only [f] at hval
    by_cases ha' : a.val < i.val <;> by_cases hb' : b.val < i.val <;> simp [ha',hb'] at hval <;> omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hbm, hbi, hbe⟩ := hb
    have hbi' : b.val ≠ i.val := by
      intro h
      apply hbi
      exact Fin.ext h
    let k : Fin (m - 1) := ⟨if b.val < i.val then b.val else b.val - 1, by
      by_cases hlt : b.val < i.val
      · rw [if_pos hlt]
        have hbi : b.val + 1 ≤ i.val := Nat.succ_le_of_lt hlt
        have him : i.val ≤ m - 1 := Nat.le_pred_of_lt hi
        exact Nat.lt_of_succ_le (le_trans hbi him)
      · rw [if_neg hlt]
        have hgt : i.val < b.val := by
          rcases lt_or_eq_of_le (Nat.le_of_not_gt hlt) with hlt' | heq
          · exact hlt'
          · exact False.elim (hbi' heq.symm)
        have hbpos : 1 ≤ b.val := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hgt)
        have hble : b.val ≤ m - 1 := Nat.le_pred_of_lt hbm
        have hsub : b.val - 1 + 1 = b.val := Nat.sub_add_cancel hbpos
        apply Nat.lt_of_succ_le
        change b.val - 1 + 1 ≤ m - 1
        rw [hsub]
        exact hble⟩
    have hfk : f k = b := by
      apply Fin.ext
      dsimp [f, k]
      by_cases hlt : b.val < i.val
      · simp [hlt]
      · have hgt : i.val < b.val := by
          rcases lt_or_eq_of_le (Nat.le_of_not_gt hlt) with hlt' | heq
          · exact hlt'
          · exact False.elim (hbi' heq.symm)
        have hble : i.val ≤ b.val - 1 := Nat.le_pred_of_lt hgt
        have hnot : ¬ b.val - 1 < i.val := Nat.not_lt_of_ge hble
        have hbpos : 1 ≤ b.val := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hgt)
        have hsub : b.val - 1 + 1 = b.val := Nat.sub_add_cancel hbpos
        simp [hlt, hnot, hsub]
    refine ⟨k, ?_, hfk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (x (f k)).val = e
    rw [hfk]
    exact hbe


private theorem tuplePrefix_eq_addPair_deletedPrefix
    {E : Type} [Fintype E] {T m : ℕ} (x : Fin T → Pair E)
    (i : Fin T) (hi : i.val < m) (hm : m ≤ T) :
    tuplePrefix x m = addPair (deletedPrefix x i m) (x i) := by
  classical
  ext e
  let s : Finset (Fin T) := Finset.univ.filter
    (fun j => j.val < m ∧ j ≠ i ∧ (x j).val = e)
  let t : Finset (Fin T) := Finset.univ.filter
    (fun j => j.val < m ∧ (x j).val = e)
  by_cases hxe : (x i).val = e
  · have hnot : i ∉ s := by simp [s]
    have hsplit : t = insert i s := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [s, t, hi, hxe]
      · simp [s, t, hji]
    change t.card = addPair (deletedPrefix x i m) (x i) e
    rw [hsplit, Finset.card_insert_of_notMem hnot]
    simp [addPair, addEdge, tuplePrefix, deletedPrefix, s, t, hxe]
  · have hsplit : t = s := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [s, t, hxe]
      · simp [s, t, hji]
    change t.card = addPair (deletedPrefix x i m) (x i) e
    rw [hsplit]
    have hxe' : e ≠ (x i).val := Ne.symm hxe
    simp [addPair, addEdge, tuplePrefix, deletedPrefix, s, t, hxe']


private theorem tupleGraph_futureSlice
    {E : Type} [Fintype E] {T m l : ℕ} (x : Fin T → Pair E)
    (hm : m ≤ l) (hl : l ≤ T) :
    tupleGraph (futureBlock x m l hm hl) = fun e =>
      (Finset.univ.filter (fun j : Fin T => m ≤ j.val ∧ j.val < l ∧ (x j).val = e)).card := by
  classical
  ext e
  simp only [tupleGraph]
  let f : Fin (l - m) → Fin T := fun j =>
    ⟨m + j.val, by
      have hjlt : j.val < l - m := j.isLt
      have hlt' := Nat.add_lt_add_left hjlt m
      rw [Nat.add_comm m (l - m), Nat.sub_add_cancel hm] at hlt'
      exact (lt_of_lt_of_le hlt' hl)⟩
  apply Finset.card_bij (s := Finset.univ.filter
      (fun j : Fin (l - m) => (futureBlock x m l hm hl j).val = e))
    (t := Finset.univ.filter
      (fun j : Fin T => m ≤ j.val ∧ j.val < l ∧ (x j).val = e))
    (fun j _ => f j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_, ?_⟩
    · change m ≤ m + j.val
      omega
    · change m + j.val < l
      have hjlt : j.val < l - m := j.isLt
      have hlt' := Nat.add_lt_add_left hjlt m
      rw [Nat.add_comm m (l - m), Nat.sub_add_cancel hm] at hlt'
      exact hlt'
    · simpa [f, futureBlock] using hj
  · intro a ha b hb hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simp only [f] at hv
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hbm, hbl, hbe⟩ := hb
    let k : Fin (l - m) := ⟨b.val - m, by omega⟩
    have hfk : f k = b := by
      apply Fin.ext
      dsimp [f, k]
      omega
    refine ⟨k, ?_, hfk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (x (f k)).val = e
    rw [hfk]
    exact hbe

private theorem deletedPrefix_eq_deletedPrefix_add_future
    {E : Type} [Fintype E] {T m l : ℕ} (x : Fin T → Pair E)
    (i : Fin T) (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T) :
    deletedPrefix x i l =
      deletedPrefix x i m + tupleGraph (futureBlock x m l hm hl) := by
  classical
  ext e
  let old : Finset (Fin T) := Finset.univ.filter
    (fun j => j.val < m ∧ j ≠ i ∧ (x j).val = e)
  let fut : Finset (Fin T) := Finset.univ.filter
    (fun j => m ≤ j.val ∧ j.val < l ∧ (x j).val = e)
  let all : Finset (Fin T) := Finset.univ.filter
    (fun j => j.val < l ∧ j ≠ i ∧ (x j).val = e)
  have hsplit : all = old ∪ fut := by
    ext j
    by_cases hjm : j.val < m
    · have hjl : j.val < l := lt_of_lt_of_le hjm hm
      simp only [all, old, fut, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hjm, hjl]
    · have hmj : m ≤ j.val := Nat.le_of_not_gt hjm
      have hji : j ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        omega
      simp only [all, old, fut, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hjm, hmj, hji]
  have hdisj : Disjoint old fut := by
    apply Finset.disjoint_left.mpr
    intro j hjold hjfut
    simp only [old, fut, Finset.mem_filter, Finset.mem_univ, true_and] at hjold hjfut
    exact (not_lt_of_ge hjfut.1) hjold.1
  change all.card = deletedPrefix x i m e + tupleGraph (futureBlock x m l hm hl) e
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hfuture := congrFun (tupleGraph_futureSlice x hm hl) e
  rw [hfuture]
  simp [old, fut, deletedPrefix]


private theorem uniformMean_mul_left {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

private theorem uniformMean_two_scales {A : Type} [Fintype A]
    (c d : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c * f x * d) = (c * d) * uniformMean f := by
  calc
    uniformMean (fun x => c * f x * d) =
        uniformMean (fun x => (c * d) * f x) := by
          apply congrArg uniformMean
          funext x
          ring
    _ = (c * d) * uniformMean f := uniformMean_mul_left (c * d) f


private theorem uniformMean_fintype_congr {A : Type} (I J : Fintype A)
    (f : A → ℝ) : @uniformMean A I f = @uniformMean A J f := by
  unfold uniformMean
  have hs : (@Finset.univ A I).sum f = (@Finset.univ A J).sum f := by
    exact @Fintype.sum_equiv A A ℝ I J inferInstance
      (Equiv.refl A) f f (by intro x; rfl)
  have hc : @Fintype.card A I = @Fintype.card A J :=
    @Fintype.card_congr A A I J (Equiv.refl A)
  rw [hs, hc]

private theorem uniformMean_congr_fintype {A : Type} (I J : Fintype A)
    (f g : A → ℝ)
    (h : @uniformMean A I f = @uniformMean A I g) :
    @uniformMean A J f = @uniformMean A J g := by
  rw [uniformMean_fintype_congr J I f, h, uniformMean_fintype_congr I J g]

private theorem uniformMean_eq_of_exists {A : Type} (J : Fintype A)
    (f : A → ℝ) (c : ℝ)
    (h : ∃ I : Fintype A, @uniformMean A I f = c) :
    @uniformMean A J f = c := by
  rcases h with ⟨I, hI⟩
  exact (uniformMean_fintype_congr J I f).trans hI

set_option maxHeartbeats 1000000 in
theorem S4_RED_04AStatement_of_deps
    (h03 : ThLean.BP.S4.S4_RED_03Statement)
    (hFrozen : ThresholdFoundations.PreFrozenStatement.{0}) :
    ThLean.BP.S4.S4_RED_04AStatement := by
  intro q n hq hn T m l i hi hm hl a
  have hnN : 2 ≤ n := by omega
  have hn2 : 2 ≤ Fintype.card (Fin n) := by simpa using hnN
  let vertexZero : Fin n := ⟨0, by omega⟩
  let vertexOne : Fin n := ⟨1, by omega⟩
  have h01 : vertexZero ≠ vertexOne := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  let pairWitness : Pair (Fin n) := ⟨s(vertexZero, vertexOne), by
    intro v hv
    rcases Sym2.eq_iff.mp hv with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact h01 (h0.trans h1.symm)
    · exact h01 (h0.trans h1.symm)⟩
  letI : Nonempty (Pair (Fin n)) := ⟨pairWitness⟩
  letI : Fintype (Pair (Fin n)) := Subtype.fintype _
  let F : (Fin (m - 1) → Pair (Fin n)) → Pair (Fin n) →
      (Fin (l - m) → Pair (Fin n)) → ℝ := fun u e b =>
    a (tupleGraph u) *
      indicator (Colorable q (tupleGraph u) ∧
        ¬ Colorable q (addPair (tupleGraph u) e)) *
      indicator (Colorable q (tupleGraph u + tupleGraph b))
  have hfactor := h03 (Pair (Fin n)) T m l i hi hm hl F
  have hleft : uniformMean (fun x : EdgeTuple (Fin n) T =>
      a (deletedPrefix x i m) * indicator (deletionDisagreement q x i m) *
        indicator (Colorable q (deletedPrefix x i l))) =
      uniformMean (fun x : EdgeTuple (Fin n) T =>
        F (omitBlock x i m hi (le_trans hm hl)) (x i)
          (futureBlock x m l hm hl)) := by
    apply congrArg uniformMean
    funext x
    simp only [F, deletionDisagreement]
    rw [deletedPrefix_eq_tupleGraph_omitBlock x i hi (le_trans hm hl)]
    rw [tuplePrefix_eq_addPair_deletedPrefix x i hi (le_trans hm hl)]
    rw [deletedPrefix_eq_deletedPrefix_add_future x i hi hm hl]
    rw [deletedPrefix_eq_tupleGraph_omitBlock x i hi (le_trans hm hl)]
  have hk (G : MGraph (Fin n)) :
      uniformMean (fun e : Pair (Fin n) =>
        indicator (Colorable q G ∧ ¬ Colorable q (addPair G e))) = kappa q G := by
    apply uniformMean_eq_of_exists (J := (inferInstance : Fintype (Pair (Fin n))))
    exact ⟨_, (hFrozen (Fin n) q hq hn2).2.1 G⟩
  have hsurvival (G : MGraph (Fin n)) (k : ℕ) :
      uniformMean (fun b : EdgeTuple (Fin n) k =>
        indicator (Colorable q (G + tupleGraph b))) = survival q G k := by
    apply uniformMean_eq_of_exists (J := (inferInstance : Fintype (EdgeTuple (Fin n) k)))
    exact ⟨_, rfl⟩
  have hCurrent : uniformMean (fun x : EdgeTuple (Fin n) T =>
      a (deletedPrefix x i m) * indicator (deletionDisagreement q x i m) *
        indicator (Colorable q (deletedPrefix x i l))) =
      uniformMean (fun x : EdgeTuple (Fin n) (m - 1) =>
        a (tupleGraph x) * kappa q (tupleGraph x) * survival q (tupleGraph x) (l - m)) := by
    calc
      uniformMean (fun x : EdgeTuple (Fin n) T =>
          a (deletedPrefix x i m) * indicator (deletionDisagreement q x i m) *
            indicator (Colorable q (deletedPrefix x i l))) =
          uniformMean (fun x : EdgeTuple (Fin n) T =>
            F (omitBlock x i m hi (le_trans hm hl)) (x i)
              (futureBlock x m l hm hl)) := hleft
      _ = uniformMean (fun u : Fin (m - 1) → Pair (Fin n) =>
            uniformMean (fun e : Pair (Fin n) =>
              uniformMean (fun b : Fin (l - m) → Pair (Fin n) => F u e b))) := hfactor
      _ = uniformMean (fun u : Fin (m - 1) → Pair (Fin n) =>
            a (tupleGraph u) * kappa q (tupleGraph u) *
              survival q (tupleGraph u) (l - m)) := by
        apply congrArg uniformMean
        funext u
        have hfutureMean (e : Pair (Fin n)) :
            uniformMean (fun b : Fin (l - m) → Pair (Fin n) => F u e b) =
              (a (tupleGraph u) * indicator
                (Colorable q (tupleGraph u) ∧
                  ¬ Colorable q (addPair (tupleGraph u) e))) *
                survival q (tupleGraph u) (l - m) := by
          calc
            uniformMean (fun b : Fin (l - m) → Pair (Fin n) =>
                (a (tupleGraph u) * indicator
                  (Colorable q (tupleGraph u) ∧
                    ¬ Colorable q (addPair (tupleGraph u) e))) *
                  indicator (Colorable q (tupleGraph u + tupleGraph b))) =
                (a (tupleGraph u) * indicator
                  (Colorable q (tupleGraph u) ∧
                    ¬ Colorable q (addPair (tupleGraph u) e))) *
                  uniformMean (fun b : Fin (l - m) → Pair (Fin n) =>
                    indicator (Colorable q (tupleGraph u + tupleGraph b))) :=
                      uniformMean_mul_left _ _
            _ = _ := by rw [hsurvival]
        calc
          uniformMean (fun e : Pair (Fin n) =>
              uniformMean (fun b : Fin (l - m) → Pair (Fin n) => F u e b)) =
              uniformMean (fun e : Pair (Fin n) =>
                (a (tupleGraph u) * indicator
                  (Colorable q (tupleGraph u) ∧
                    ¬ Colorable q (addPair (tupleGraph u) e))) *
                  survival q (tupleGraph u) (l - m)) := by
                    apply congrArg uniformMean
                    funext e
                    exact hfutureMean e
          _ = a (tupleGraph u) * kappa q (tupleGraph u) *
                survival q (tupleGraph u) (l - m) := by
                  rw [uniformMean_two_scales]
                  rw [hk (tupleGraph u)]
                  ring
  exact hCurrent

end ThLean.W.S416
